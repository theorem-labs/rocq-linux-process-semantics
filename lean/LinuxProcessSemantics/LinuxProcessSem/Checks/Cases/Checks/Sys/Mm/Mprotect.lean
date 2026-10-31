import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mprotect
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.Mprotect

/-! # Checks.Cases.Checks.Sys.Mm.Mprotect — what the mprotect checker answers, read off against Linux

Pins over `Checks.Sys.Mm.Mprotect`'s `check_mprotect` and
`mprotect_witness`.  Restates the checker-level half of
`theories/LinuxProcessSem/Checks/Cases/Mm/Mprotect.v`: every checker
`Example` there is stated on `check_syscall`, and each is restated here on
`check_mprotect` at the same register values, with the same offered
effect and the same fixture.  The spec-level half of that file is
`Checks/Cases/Mm/Mprotect.lean`'s.  No ledger reads this file's mapping
today: `tools/check_lean_cases_parity.py` pairs a Cases file with the Rocq
file at its mirrored path, none sits at this one, and the S file's
`covers:` lines may name only its own theorems — so this file is listed
`unmirrored`, and the `Rocq:` name in each twin's docstring is the
mapping.  Not part of the trusted
specification: this file is QA on the definitions, written to be READ,
and every claim in it is a claim about what the kernel does, with the
citation beside it.  Line numbers are Linux v6.18.46 (commit
1f99e9ab748f) throughout.

WHY THE CHECKER AND NOT `check_syscall`.  Rocq's examples go through the
dispatcher, so that a wrong argument order in the arm is caught where
the registers are named.  The pins down to the ledger section apply
`check_mprotect` to the register values directly, in
`SYSCALL_DEFINE3(mprotect, start, len, prot)`'s order.  They were written
before `checked_table` had a row for 226, and they cannot see a
transposed register in the arm.  The last section is the registration's:
it restates each Rocq example stated through `check_syscall` the same
way, over the real table, and says there which pins carry the register
order.

HOW THESE CLOSE.  Not by `rfl`.  `Meta.isDefEq` on `check_mprotect` at
concrete arguments unfolds through the containment tests and exceeds
`maxRecDepth`, and raising the limit to 8192 does not change that;
`decide` is not available, since `check_result` carries a `Model` and
`Model` has no `DecidableEq`.  What does close each pin, in
milliseconds, is `sys_norm` after one `unfold` of the checker and of
`check_ret_only`, whose match on the
effect's shape is what the offered effect has to pass: the `sys_simp`
set reads the fixture and the
post-state builder, `+decide` settles each closed `Bool` gate and
`+ground` evaluates the rest.  The macros below are that sequence, so
that a pin's proof says what kind of claim it is.

WHAT THE PROBE EVIDENCE IS.  No probe under `testing/syscall-check/`
evaluates the Lean checker: the harness runs the extracted Rocq model.
Where a pin cites a probe case, the case states the same fact of the
Rocq checker against the pinned kernel, and this file states it of the
Lean one.  A probe's grant is placed by the kernel, so its address is a
run-time value; the pin uses the fixture's address and the probe's own
length and prot word, which are constants in the probe's source.

WHAT MEASURES THESE PINS.  Nothing in the tree: `tools/lean_mutate.py`
builds a spec mutant and elaborates `Checks/Cases/Mm/Mprotect.lean`
against it, so no mutant of `Sys/Mm/Mprotect.lean` or of the checker is
ever compiled against this file, and its kill-rate is unmeasured by
anything checked in.  The deep review of #1065 ran a hand-rolled sweep of
the checker and the witness against it and added the pins for the
survivors it found, each saying so in its docstring; that sweep is not in
the tree.  This paragraph stops being true when that tool lists a
checker's pins beside the spec's, and is deleted then. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Mm.Mprotect

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mprotect
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.Mprotect
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! ## The fixtures and the closers -/

/-- One reserved page with backed capacity to spare: the PROT_NONE grant
of one page that `errno_mprotect.c`'s `mprotect-noaccess` mode and
`noaccess_vm.c`'s `len0-noaccess` mode build. -/
def noaccess_one_page : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [(65536, 4096)] 0 0 16384 0 demo_sp)

/-- Two reserved pages with backed capacity to spare: `noaccess_vm.c`'s
`fresh` mode reserves 8192 bytes PROT_NONE and exposes the first page. -/
def noaccess_two_pages : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [(65536, 8192)] 0 0 16384 0 demo_sp)

/-- The same page once exposed: the grant stays, the no-access interval is
gone. -/
def rw_one_page : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 16384 0 demo_sp)

/-- The same-page brk-shrink state the spec twin describes: `vm_maps` owns
the page eight bytes short while `vm_noaccess` holds the whole of it, the
one reachable shape where `vm_noaccess ⊆ vm_maps` fails. -/
def noaccess_owned_short : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4088)] [(65536, 4096)] 0 0 16384 0 demo_sp)

/-- The rw counterpart: `vm_maps` owns the page eight bytes short and
`vm_noaccess` is empty, the byte-granular ledger a brk grow of 4088 bytes
from a page boundary leaves once its tail is exposed. -/
def rw_owned_short : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 4088)] [] 0 0 16384 0 demo_sp)

/-- `noaccess_two_pages` under a budget of exactly one page, the
`--alloc-limit 4096` the probe's `fresh` case runs under… -/
def fresh_exact_budget : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [(65536, 8192)] 0 0 4096 0 demo_sp)

/-- …and one byte short of it. -/
def fresh_one_byte_short : Model :=
  fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [(65536, 8192)] 0 0 4095 0 demo_sp)

/-- Read a concrete `check_mprotect` off and close the equation the pin
states.

`scoped`, because `Kernel/Groups.lean` declares a `check_norm` and a
`witness_norm` too, unscoped and with bodies that unfold ITS checkers.  A
tactic macro is not namespaced: two declarations of one name become a
`choice` node, and Lean tries the alternatives in the order the parser
lists them and stops at the first that ERRORS rather than the first that
fails to apply (`evalChoiceAux` advances only on an unsupported-syntax
exception), so in a file importing both pin modules one file's body ran
on every goal and the other file's pins stopped closing — reproduced in
both import orders by the deep review of #1065.  `Witness/Prelude.lean`
records the same hazard for `srw`, kept identical by hand; here the bodies
cannot be.  Scoping keeps these three inside `open` of this namespace,
which every pin here is under; the Groups pair is outside this PR's diff
and stays unscoped. -/
scoped macro "check_norm" : tactic =>
  `(tactic| (unfold check_mprotect check_ret_only; sys_norm))

/-- Read a concrete `check_mprotect` off and refute the acceptance the pin
denies. -/
scoped macro "check_refute" : tactic =>
  `(tactic| (unfold check_mprotect check_ret_only; sys_refute))

/-- Read a concrete `mprotect_witness` off. -/
scoped macro "witness_norm" : tactic =>
  `(tactic| (unfold mprotect_witness; sys_norm))

/-! ## Gate 1: PROT_GROWSDOWN with PROT_GROWSUP is -EINVAL, before anything else

`if (grows == (PROT_GROWSDOWN|PROT_GROWSUP)) return -EINVAL;`
(mm/mprotect.c:876-877, Linux v6.18.46) is the first test of
`do_mprotect_pkey`; one grow bit alone is masked off at :875 and never
validated on a zero length, which takes its 0 at :881-882.

NOT LINUX ALONE.  The lone-grows-bit pins below (`growsdown_alone_*`,
`growsup_alone_*`) refuse -EINVAL, and that is a real answer of a
supported implementation: qemu-user's `target_mprotect` validates the
prot word BEFORE its zero-length return (linux-user/mmap.c:188-197,
QEMU 11.1.1), so `mprotect(x, 0, PROT_GROWSDOWN|rw)` outside the guest
stack window and `mprotect(x, 0, PROT_GROWSUP|rw)` anywhere are -EINVAL
there and 0 under Linux.  The checker mirrors the spec twin's arm, which proves
Linux's order as certain; the divergence, its scope and the list of
everything that states it are
`bugs/mprotect-zero-length-prot-admits-linux-alone.md`'s, and these six
pins move with the arm when it does. -/

/-- Both grow bits with rw: -EINVAL is admitted, on a zero length.  Rocq:
`mprotect_grows_conflict_is_einval`.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem grows_conflict_is_einval :
    check_mprotect 65536 0 50331651 (mkEffect (errno_ret EINVAL) [] [])
        noaccess_three_pages = CheckOk noaccess_three_pages [] := by
  check_norm

/-- The probe's own word, the two grow bits alone: still -EINVAL.
probe: testing/syscall-check/tests/mprotect_exec.c#conform -- len0-growboth -/
theorem grows_conflict_alone_is_einval :
    check_mprotect 65536 0 50331648 (mkEffect (errno_ret EINVAL) [] [])
        rw_two_pages = CheckOk rw_two_pages [] := by
  check_norm

/-- …and the zero length does not rescue a success: the pair test comes first.
probe: testing/syscall-check/tests/mprotect_exec.c#reject --mutate mprotect:ret=0 -- len0-growboth -/
theorem grows_conflict_success_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 0 50331648 (mkEffect 0 [] []) rw_two_pages
      ≠ CheckOk m' evs := by
  check_refute

/-- …nor is any other errno admitted.
probe: testing/syscall-check/tests/mprotect_exec.c#reject --mutate mprotect:ret=-ENOMEM -- len0-growboth -/
theorem grows_conflict_enomem_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 0 50331648 (mkEffect (errno_ret ENOMEM) [] [])
        rw_two_pages ≠ CheckOk m' evs := by
  check_refute

/-- PROT_GROWSDOWN alone with rw on a zero length is 0.  Rocq:
`mprotect_growsdown_alone_is_not_a_conflict`.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem growsdown_alone_is_not_a_conflict :
    check_mprotect 65536 0 16777219 (mkEffect 0 [] [])
        noaccess_three_pages = CheckOk noaccess_three_pages [] := by
  check_norm

/-- The same call as the probe issues it, on the probe's rw grant.
probe: testing/syscall-check/tests/mprotect_exec.c#conform -- len0-growdown -/
theorem growsdown_alone_is_zero_on_rw :
    check_mprotect 65536 0 16777219 (mkEffect 0 [] []) rw_two_pages =
      CheckOk rw_two_pages [] := by
  check_norm

/-- PROT_GROWSUP alone likewise.  Rocq: `mprotect_growsup_alone_is_not_a_conflict`.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem growsup_alone_is_not_a_conflict :
    check_mprotect 65536 0 33554435 (mkEffect 0 [] [])
        noaccess_three_pages = CheckOk noaccess_three_pages [] := by
  check_norm

/-- A kernel that validated the lone bit before the zero-length return
would answer -EINVAL — qemu-user does, see the section note — and the
checker, following the spec twin's arm, refuses it.  Rocq:
`mprotect_growsdown_alone_einval_is_rejected`.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem growsdown_alone_einval_is_rejected :
    check_mprotect 65536 0 16777219 (mkEffect (errno_ret EINVAL) [] [])
        noaccess_three_pages = CheckReject := by
  check_norm

/-- …the probe's reject twin: a kernel that validated the lone bit before
the zero-length return.
probe: testing/syscall-check/tests/mprotect_exec.c#reject --mutate mprotect:ret=-EINVAL -- len0-growdown -/
theorem growsdown_alone_einval_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 0 16777219 (mkEffect (errno_ret EINVAL) [] [])
        rw_two_pages ≠ CheckOk m' evs := by
  check_refute

/-- Rocq: `mprotect_growsup_alone_einval_is_rejected`.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem growsup_alone_einval_is_rejected :
    check_mprotect 65536 0 33554435 (mkEffect (errno_ret EINVAL) [] [])
        noaccess_three_pages = CheckReject := by
  check_norm


/-- The pair test precedes the wrap test: both grow bits on a range whose
end wraps is -EINVAL (:876-877), not the -ENOMEM of :885-886.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem grows_conflict_precedes_wrap :
    check_mprotect 9223372036854775808 9223372036854775808 50331651
        (mkEffect (errno_ret EINVAL) [] []) rw_two_pages = CheckOk rw_two_pages [] := by
  check_norm

/-- …and the wrap's errno is refused there.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem grows_conflict_precedes_wrap_enomem_is_rejected :
    check_mprotect 9223372036854775808 9223372036854775808 50331651
        (mkEffect (errno_ret ENOMEM) [] []) rw_two_pages = CheckReject := by
  check_norm

/-- The two grow bits alone on a NONZERO length: still -EINVAL, still before
anything else.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem grows_conflict_nonzero_length_is_einval :
    check_mprotect 65536 4096 50331648 (mkEffect (errno_ret EINVAL) [] [])
        rw_two_pages = CheckOk rw_two_pages [] := by
  check_norm

/-- …and not a 0.  Without this gate the word would reach the prot test,
which declines any grow bit, so what the pin separates the -EINVAL from is
a `CheckUnmodeled`, not the no-op's 0.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem grows_conflict_nonzero_length_success_is_rejected :
    check_mprotect 65536 4096 50331648 (mkEffect 0 [] []) rw_two_pages =
      CheckReject := by
  check_norm

/-! ## Gate 2: an unaligned start is -EINVAL, before the zero length

`if (start & ~PAGE_MASK) return -EINVAL;` (mm/mprotect.c:879-880, Linux
v6.18.46) sits between the grow test and `if (!len) return 0;` (:881-882). -/

/-- `mprotect(65537, 0, rw)`: -EINVAL, not the zero-length 0.  Rocq:
`mprotect_unaligned_precedes_zero_length`.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem unaligned_precedes_zero_length :
    check_mprotect 65537 0 3 (mkEffect (errno_ret EINVAL) [] [])
        noaccess_three_pages = CheckOk noaccess_three_pages [] := by
  check_norm

/-- The probe's `p + 1, 0, rw` on its rw grant.
probe: testing/syscall-check/tests/mprotect_exec.c#conform -- unaligned-len0 -/
theorem unaligned_zero_length_is_einval_on_rw :
    check_mprotect 65537 0 3 (mkEffect (errno_ret EINVAL) [] []) rw_two_pages =
      CheckOk rw_two_pages [] := by
  check_norm

/-- The alignment gate admits no success…
probe: testing/syscall-check/tests/mprotect_exec.c#reject --mutate mprotect:ret=0 -- unaligned-len0 -/
theorem unaligned_zero_length_success_refused (m' : Model) (evs : List event) :
    check_mprotect 65537 0 3 (mkEffect 0 [] []) rw_two_pages ≠ CheckOk m' evs := by
  check_refute

/-- …and no other errno.
probe: testing/syscall-check/tests/mprotect_exec.c#reject --mutate mprotect:ret=-ENOMEM -- unaligned-len0 -/
theorem unaligned_zero_length_enomem_refused (m' : Model) (evs : List event) :
    check_mprotect 65537 0 3 (mkEffect (errno_ret ENOMEM) [] []) rw_two_pages
      ≠ CheckOk m' evs := by
  check_refute

/-- `mprotect(3, 4096, PROT_EXEC)`: the unaligned start answers before the
prot word is read, so a prot the model declines is still -EINVAL here.
probe: testing/syscall-check/tests/mprotect_exec.c#conform -- addr-as-prot -/
theorem unaligned_precedes_unsupported_prot :
    check_mprotect 3 4096 4 (mkEffect (errno_ret EINVAL) [] []) rw_two_pages =
      CheckOk rw_two_pages [] := by
  check_norm

/-- …and not a success.
probe: testing/syscall-check/tests/mprotect_exec.c#reject --mutate mprotect:ret=0 -- addr-as-prot -/
theorem unaligned_unsupported_prot_success_refused (m' : Model) (evs : List event) :
    check_mprotect 3 4096 4 (mkEffect 0 [] []) rw_two_pages ≠ CheckOk m' evs := by
  check_refute


/-- The alignment test precedes the wrap test: an odd start on a wrapping
range is -EINVAL (:879-880), not -ENOMEM (:885-886).
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem unaligned_precedes_wrap :
    check_mprotect 9223372036854775809 9223372036854775808 3
        (mkEffect (errno_ret EINVAL) [] []) rw_two_pages = CheckOk rw_two_pages [] := by
  check_norm

/-- …and the wrap's errno is refused there.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem unaligned_precedes_wrap_enomem_is_rejected :
    check_mprotect 9223372036854775809 9223372036854775808 3
        (mkEffect (errno_ret ENOMEM) [] []) rw_two_pages = CheckReject := by
  check_norm

/-- An unaligned start on a NONZERO length over a live rw mapping: -EINVAL,
where the aligned call is the no-op's 0.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem unaligned_nonzero_length_is_einval :
    check_mprotect 65537 4096 3 (mkEffect (errno_ret EINVAL) [] []) rw_two_pages =
      CheckOk rw_two_pages [] := by
  check_norm

/-- …and that 0 is refused.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem unaligned_nonzero_length_success_is_rejected :
    check_mprotect 65537 4096 3 (mkEffect 0 [] []) rw_two_pages = CheckReject := by
  check_norm

/-- `start & ~PAGE_MASK` (:879-880) fires on ANY start that is not a page
multiple, however finely aligned: eight bytes into the page, half a page in,
and one byte short of the next page are all -EINVAL.  Every other unaligned
start in this file is odd (65537, 3, 2^63 + 1), so a checker testing the low
three bits instead of the low twelve passed them all; the mutation sweep of
the deep review of #1065 found that survivor, and this pin is what kills it.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem unaligned_inside_the_page_is_einval :
    check_mprotect 65544 4096 3 (mkEffect (errno_ret EINVAL) [] []) rw_two_pages =
        CheckOk rw_two_pages [] ∧
    check_mprotect 67584 4096 3 (mkEffect (errno_ret EINVAL) [] []) rw_two_pages =
        CheckOk rw_two_pages [] ∧
    check_mprotect 69631 4096 3 (mkEffect (errno_ret EINVAL) [] []) rw_two_pages =
        CheckOk rw_two_pages [] := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- …and 0 is refused at each of them.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem unaligned_inside_the_page_success_is_rejected :
    check_mprotect 65544 4096 3 (mkEffect 0 [] []) rw_two_pages = CheckReject ∧
    check_mprotect 67584 4096 3 (mkEffect 0 [] []) rw_two_pages = CheckReject ∧
    check_mprotect 69631 4096 3 (mkEffect 0 [] []) rw_two_pages = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-! ## Gate 3: a zero length is 0, before the prot is validated

`if (!len) return 0;` (mm/mprotect.c:881-882, Linux v6.18.46) precedes
`arch_validate_prot` (:887-888), so every prot word answers 0 at length
zero — including the ones
the model declines at any other length. -/

/-- `mprotect(p, 0, rw)` on the probe's grant.
probe: testing/syscall-check/tests/mprotect_exec.c#conform -- len0 -/
theorem zero_length_is_zero :
    check_mprotect 65536 0 3 (mkEffect 0 [] []) rw_two_pages =
      CheckOk rw_two_pages [] := by
  check_norm

/-- …and 0 alone.
probe: testing/syscall-check/tests/mprotect_exec.c#reject --mutate mprotect:ret=-ENOMEM -- len0 -/
theorem zero_length_enomem_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 0 3 (mkEffect (errno_ret ENOMEM) [] []) rw_two_pages
      ≠ CheckOk m' evs := by
  check_refute

/-- PROT_READ|PROT_EXEC at length zero: 0, where the same prot at any
other length is declined below.
probe: testing/syscall-check/tests/mprotect_exec.c#conform -- len0-exec -/
theorem exec_zero_length_is_zero :
    check_mprotect 65536 0 5 (mkEffect 0 [] []) rw_two_pages =
      CheckOk rw_two_pages [] := by
  check_norm

/-- PROT_NONE at length zero likewise.
probe: testing/syscall-check/tests/mprotect_exec.c#conform -- len0-none -/
theorem none_zero_length_is_zero :
    check_mprotect 65536 0 0 (mkEffect 0 [] []) rw_two_pages =
      CheckOk rw_two_pages [] := by
  check_norm

/-- PROT_READ at length zero on a live rw mapping.  Rocq:
`mprotect_read_only_zero_length_is_zero`.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem read_only_zero_length_is_zero :
    check_mprotect 65536 0 1 (mkEffect 0 [] []) rw_two_pages =
      CheckOk rw_two_pages [] := by
  check_norm

/-- …and a zero-length call admits 0 and nothing else.  Rocq:
`mprotect_read_only_zero_length_errno_is_rejected`.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem read_only_zero_length_errno_is_rejected :
    check_mprotect 65536 0 1 (mkEffect (errno_ret ENOMEM) [] []) rw_two_pages =
      CheckReject := by
  check_norm


/-- A zero length over a page still PROT_NONE: 0, and the page stays
reserved — nothing is exposed at length zero.
probe: testing/syscall-check/tests/noaccess_vm.c#conform -- len0-noaccess -/
theorem zero_length_over_noaccess_is_zero :
    check_mprotect 65536 0 3 (mkEffect 0 [] []) noaccess_one_page =
      CheckOk noaccess_one_page [] := by
  check_norm

/-- …so an empty zero range in the effect is still a range too many…
probe: testing/syscall-check/tests/noaccess_vm.c#reject --mutate mprotect:smuggle-zeros:a0:0 -- len0-noaccess -/
theorem zero_length_over_noaccess_empty_zeros_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 0 3 (mkEffect 0 [] [(65536, 0)]) noaccess_one_page
      ≠ CheckOk m' evs := by
  check_refute

/-- …and so is the page's.
probe: testing/syscall-check/tests/noaccess_vm.c#reject --mutate mprotect:smuggle-zeros:a0:4096 -- len0-noaccess -/
theorem zero_length_over_noaccess_zeros_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 0 3 (mkEffect 0 [] [(65536, 4096)]) noaccess_one_page
      ≠ CheckOk m' evs := by
  check_refute

/-- A copy-in beside a gate's answer: `SYSCALL_DEFINE3(mprotect)` takes
three registers (:1008-1009) and reads no user memory on any path.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem zero_length_copyin_is_rejected :
    check_mprotect 65536 0 3 (SyscallEffect.mkEffectU 0 [] [] [] [] [(65536, 8)])
        rw_two_pages = CheckReject := by
  check_norm

/-! ## Gate 4: a range whose end wraps is -ENOMEM, before the prot is read

`len = PAGE_ALIGN(len); end = start + len; if (end <= start) return
-ENOMEM;` (mm/mprotect.c:883-886, Linux v6.18.46), in `unsigned long`
arithmetic, and before `arch_validate_prot` at :887-888. -/

/-- `mprotect(2^63, 2^63, rw)`: `end` wraps to exactly 0.  Rocq:
`mprotect_wrapping_end_is_enomem`.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem wrapping_end_is_enomem :
    check_mprotect 9223372036854775808 9223372036854775808 3
        (mkEffect (errno_ret ENOMEM) [] []) noaccess_three_pages =
      CheckOk noaccess_three_pages [] := by
  check_norm

/-- A wrapping range admits -ENOMEM and nothing else.  Rocq:
`mprotect_wrapping_end_success_is_rejected`.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem wrapping_end_success_is_rejected :
    check_mprotect 9223372036854775808 9223372036854775808 3
        (mkEffect 0 [] []) noaccess_three_pages = CheckReject := by
  check_norm

/-- …and it is -ENOMEM for PROT_EXEC as well, which the model would
otherwise decline: the wrap test precedes the prot.  Rocq:
`mprotect_wrapping_end_precedes_unsupported_prot`.
kernel: mm/mprotect.c:do_mprotect_pkey; include/linux/mman.h:arch_validate_prot@v6.18.46 -/
theorem wrapping_end_precedes_unsupported_prot :
    check_mprotect 9223372036854775808 9223372036854775808 4
        (mkEffect (errno_ret ENOMEM) [] []) noaccess_three_pages =
      CheckOk noaccess_three_pages [] := by
  check_norm

/-- The probe's `mprotect(p, -1, rw)`: `PAGE_ALIGN` of `2^64 - 1` is 0
in `unsigned long`, so the end is the start.
probe: testing/syscall-check/tests/mprotect_exec.c#conform -- huge-len -/
theorem huge_length_is_enomem :
    check_mprotect 65536 18446744073709551615 3
        (mkEffect (errno_ret ENOMEM) [] []) rw_two_pages = CheckOk rw_two_pages [] := by
  check_norm

/-- …deterministically: no success…
probe: testing/syscall-check/tests/mprotect_exec.c#reject --mutate mprotect:ret=0 -- huge-len -/
theorem huge_length_success_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 18446744073709551615 3 (mkEffect 0 [] []) rw_two_pages
      ≠ CheckOk m' evs := by
  check_refute

/-- …and no other errno.
probe: testing/syscall-check/tests/mprotect_exec.c#reject --mutate mprotect:ret=-EINVAL -- huge-len -/
theorem huge_length_einval_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 18446744073709551615 3 (mkEffect (errno_ret EINVAL) [] [])
        rw_two_pages ≠ CheckOk m' evs := by
  check_refute

/-- The same wrapping range with PROT_EXEC.
probe: testing/syscall-check/tests/mprotect_exec.c#conform -- huge-len-exec -/
theorem huge_length_exec_is_enomem :
    check_mprotect 65536 18446744073709551615 4
        (mkEffect (errno_ret ENOMEM) [] []) rw_two_pages = CheckOk rw_two_pages [] := by
  check_norm

/-- …where prot validation cannot replace the earlier errno.
probe: testing/syscall-check/tests/mprotect_exec.c#reject --mutate mprotect:ret=-EINVAL -- huge-len-exec -/
theorem huge_length_exec_einval_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 18446744073709551615 4 (mkEffect (errno_ret EINVAL) [] [])
        rw_two_pages ≠ CheckOk m' evs := by
  check_refute


/-- A wrap by the sum alone: `PAGE_ALIGN(2^64 - 4096)` is itself, and
`start + len` (:884) carries past the word.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem wrap_by_sum_is_enomem :
    check_mprotect 65536 18446744073709547520 3 (mkEffect (errno_ret ENOMEM) [] [])
        rw_two_pages = CheckOk rw_two_pages [] := by
  check_norm

/-- …and admits no success.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem wrap_by_sum_success_is_rejected :
    check_mprotect 65536 18446744073709547520 3 (mkEffect 0 [] []) rw_two_pages =
      CheckReject := by
  check_norm

/-- The last page of the word: `end` is exactly 0, which `end <= start`
(:885) catches.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem top_page_is_enomem :
    check_mprotect 18446744073709547520 4096 3 (mkEffect (errno_ret ENOMEM) [] [])
        rw_two_pages = CheckOk rw_two_pages [] := by
  check_norm

/-- …and a one-byte length there rounds up to that same page first (:883).
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem top_page_short_length_is_enomem :
    check_mprotect 18446744073709547520 1 3 (mkEffect (errno_ret ENOMEM) [] [])
        rw_two_pages = CheckOk rw_two_pages [] := by
  check_norm

/-- The first page above the Sv48 user range does not wrap; Linux's
-ENOMEM there is `vma_find`'s (:904-907), and the model, with no grant
under the range, declines rather than admits it.  There is no `TASK_SIZE`
gate in `mprotect_spec`, and this pin is the record of that.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem sv48_top_is_unmodeled :
    check_mprotect 140737488355328 4096 3 (mkEffect (errno_ret ENOMEM) [] [])
        rw_two_pages = CheckUnmodeled := by
  check_norm

/-- The wrap test is `2^64 <= start + PAGE_ALIGN(len)` and nothing lower: a
sum in `[2^63, 2^64)` has not carried past the word, so `end <= start`
(:884-886) is false and Linux walks on to `vma_find` (:904-907), answering
-ENOMEM only because no VMA sits there — a range the ledger does not
cover, which the model declines.  A gate reading `2^63` for `2^64` would
accept that -ENOMEM as the wrap's; the mutation sweep of the deep review of
#1065 found that mutant survived every pin, and this is what kills it.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem non_wrapping_high_sum_is_unmodeled :
    check_mprotect 9223372036854775808 4096 3 (mkEffect (errno_ret ENOMEM) [] [])
        rw_two_pages = CheckUnmodeled ∧
    check_mprotect 18446744073709543424 4096 3 (mkEffect (errno_ret ENOMEM) [] [])
        rw_two_pages = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- `start = 0` is aligned and not special: with `len = 2^64 - 4095`,
`PAGE_ALIGN` (:883) carries to 0 and `end <= start` (:884-886) is -ENOMEM
at the lowest start there is; one page less and the sum stands at
`2^64 - 4096` with no wrap, a range no grant covers.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem zero_start_wraps_like_any_other :
    check_mprotect 0 18446744073709547521 3 (mkEffect (errno_ret ENOMEM) [] [])
        rw_two_pages = CheckOk rw_two_pages [] ∧
    check_mprotect 0 18446744073709547520 3 (mkEffect (errno_ret ENOMEM) [] [])
        rw_two_pages = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-! ## The exposure: PROT_NONE to rw over a reserved range

Past the four gates, `mprotect_fixup` (mm/mprotect.c, Linux v6.18.46)
either fails with -ENOMEM — the budget checks at :801-803 and :807-808
refuse the new writable pages, or a split inside `vma_modify_flags`
(:816) cannot be made — or succeeds and, through
`vma_modify_flags` (:816) and `__split_vma` (mm/vma.c, Linux v6.18.46),
leaves exactly the
asked-for range readable and writable with its fresh anonymous pages
reading as zeroes. -/

/-- The middle page of a three-page reservation: the success splits the
no-access interval into two remnants and zero-fills exactly that page.
Rocq: `mprotect_middle_splits_noaccess_and_zeros_exactly`.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup; mm/vma.c:__split_vma@v6.18.46 -/
theorem middle_splits_noaccess_and_zeros_exactly :
    check_mprotect 69632 4096 3 (mkEffect 0 [] [(69632, 4096)])
        noaccess_three_pages =
      CheckOk (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [(65536, 4096), (73728, 4096)]
                          0 0 16384 0 demo_sp)) [] := by
  check_norm

/-- The errno preserves the ledger.  Whether the -ENOMEM is the budget's
(:801-803, :807-808) or a split's that `vma_modify_flags` (:816) could not
make — `split_vma` and `__split_vma` in mm/vma.c (Linux v6.18.46) both
answer -ENOMEM — no protection has changed, and a VMA split at the same
protection is nothing the ledger records.  Rocq:
`mprotect_noaccess_errno_preserves_ledger`.
kernel: mm/mprotect.c:mprotect_fixup; mm/vma.c:vma_modify_flags@v6.18.46 -/
theorem noaccess_errno_preserves_ledger :
    check_mprotect 69632 4096 3 (mkEffect (errno_ret ENOMEM) [] [])
        noaccess_three_pages = CheckOk noaccess_three_pages [] := by
  check_norm

/-- A success that zero-fills MORE than the page asked for is a lie.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem wider_zeros_are_rejected :
    check_mprotect 69632 4096 3 (mkEffect 0 [] [(65536, 12288)])
        noaccess_three_pages = CheckReject := by
  check_norm

/-- The probe's transition: the first page of a two-page reservation made
rw and zero-filled, the second still reserved — which is exactly
`mixed_two_pages`, the fixture the mixed-protection declines below run on.
probe: testing/syscall-check/tests/noaccess_vm.c#conform -- fresh -/
theorem fresh_first_page_exposed :
    check_mprotect 65536 4096 3 (mkEffect 0 [] [(65536, 4096)]) noaccess_two_pages =
      CheckOk mixed_two_pages [] := by
  check_norm

/-- …and so is a success that exposes the page without its zero-fill: the
fresh anonymous pages of a range made writable read as zeroes.
probe: testing/syscall-check/tests/noaccess_vm.c#reject --mutate mprotect:drop-zeros -- fresh -/
theorem exposure_without_zeros_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 3 (mkEffect 0 [] []) noaccess_two_pages
      ≠ CheckOk m' evs := by
  check_refute

/-- …or with an unmap in the effect: mprotect leaves nothing unmapped.
probe: testing/syscall-check/tests/noaccess_vm.c#reject --mutate mprotect:smuggle-unmap:a0:4096 -- fresh -/
theorem exposure_with_unmap_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 3
        (SyscallEffect.mkEffectU 0 [] [(65536, 4096)] [(65536, 4096)] [] []) noaccess_two_pages
      ≠ CheckOk m' evs := by
  check_refute

/-- The whole of a one-page reservation exposed: the no-access interval
is gone and the grant stays.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem one_page_exposure_clears_noaccess :
    check_mprotect 65536 4096 3 (mkEffect 0 [] [(65536, 4096)])
        noaccess_one_page = CheckOk rw_one_page [] := by
  check_norm

/-- The probe's transition failing with -ENOMEM, its zero-fill dropped with it.
probe: testing/syscall-check/tests/errno_mprotect.c#conform --mutate mprotect:ret=-ENOMEM,drop-zeros -- mprotect-noaccess -/
theorem exposure_enomem_is_admitted :
    check_mprotect 65536 4096 3 (mkEffect (errno_ret ENOMEM) [] [])
        noaccess_one_page = CheckOk noaccess_one_page [] := by
  check_norm

/-- -EINVAL past the four gates is unreachable; the checker refuses it.
probe: testing/syscall-check/tests/errno_mprotect.c#reject --mutate mprotect:ret=-EINVAL,drop-zeros -- mprotect-noaccess -/
theorem exposure_einval_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 3 (mkEffect (errno_ret EINVAL) [] [])
        noaccess_one_page ≠ CheckOk m' evs := by
  check_refute

/-- …and -EBADF names an fd where mprotect has none.
probe: testing/syscall-check/tests/errno_mprotect.c#reject --mutate mprotect:ret=-EBADF,drop-zeros -- mprotect-noaccess -/
theorem exposure_ebadf_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 3 (mkEffect (errno_ret EBADF) [] [])
        noaccess_one_page ≠ CheckOk m' evs := by
  check_refute

/-- -EPERM and -EACCES are refused on this arm, each for a reason of its
own.  -EPERM is `mprotect_fixup`'s answer for a sealed VMA (:766-767); the
sealed VMAs a riscv64 process can hold are `mseal`'s (462, outside the
modeled surface) and, under CONFIG_MSEAL_SYSTEM_MAPPINGS — off by default,
and unselectable on the pinned VM kernel, whose config is
`testing/vm/kernel.fragment` merged over the riscv defconfig: the
defconfig sets CONFIG_CHECKPOINT_RESTORE=y (arch/riscv/configs/defconfig:22),
the fragment does not unset it, and the option `depends on
!CHECKPOINT_RESTORE` (security/Kconfig:54-58); a configuration all the
same — the vdso text (arch/riscv/kernel/vdso.c:139, Linux v6.18.46), its
data pages (lib/vdso/datastore.c:101-103; these also lack VM_MAYWRITE, so
rw over them is the VM_MAY* -EACCES of :960-963 before the seal is ever
consulted) and the uprobes XOL area (security/Kconfig:61-62, installed
by `xol_add_vma`, kernel/events/uprobes.c:1725-1728); none is an entry of
`vm_maps`, which this arm requires — so the vdso's real -EPERM and the
vvar's real -EACCES are declined (`sealed_system_mapping_eperm_is_unmodeled`,
`sealed_system_mapping_eacces_is_unmodeled`), never refused.  The spec
twin's own sentence rests the refusal on `mseal` being unmodeled alone,
which the vdso shows is not enough; the `vm_maps` conjunct is what
carries it.
-EACCES is the VM_MAY* test (:960-963) and `map_deny_write_exec`
(:965-968), which the spec twin argues cannot fire for rw over a grant
`vm_maps` holds.
kernel: mm/mprotect.c:mprotect_fixup,do_mprotect_pkey@v6.18.46 -/
theorem exposure_eperm_and_eacces_refused :
    check_mprotect 65536 4096 3 (mkEffect (errno_ret EPERM) [] []) noaccess_one_page =
      CheckReject ∧
    check_mprotect 65536 4096 3 (mkEffect (errno_ret EACCES) [] []) noaccess_one_page =
      CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- An errno with a zero-fill beside it: a failed mprotect exposes nothing.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem exposure_errno_with_zeros_is_rejected :
    check_mprotect 65536 4096 3 (mkEffect (errno_ret ENOMEM) [] [(65536, 4096)])
        noaccess_one_page = CheckReject := by
  check_norm


/-! ### The length is rounded, the zero range is the rounded one

`len = PAGE_ALIGN(len)` (mm/mprotect.c:883, Linux v6.18.46) before the
range is walked, so the pages exposed and zero-filled are the rounded
range's, never the byte count's. -/

/-- A one-byte length exposes the page.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem short_length_rounds_to_the_page :
    check_mprotect 65536 1 3 (mkEffect 0 [] [(65536, 4096)]) noaccess_one_page =
      CheckOk rw_one_page [] := by
  check_norm

/-- …and a zero range of one byte is not the page's.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem short_length_unrounded_zeros_are_rejected :
    check_mprotect 65536 1 3 (mkEffect 0 [] [(65536, 1)]) noaccess_one_page =
      CheckReject := by
  check_norm

/-- Two pages less a byte over a three-page reservation: two pages are
exposed, one remnant stays.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup; mm/vma.c:__split_vma@v6.18.46 -/
theorem two_pages_less_a_byte_round_up :
    check_mprotect 65536 8191 3 (mkEffect 0 [] [(65536, 8192)])
        noaccess_three_pages =
      CheckOk (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [(73728, 4096)] 0 0 16384 0 demo_sp))
        [] := by
  check_norm

/-- …and the byte count is not a zero range.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem two_pages_less_a_byte_unrounded_zeros_are_rejected :
    check_mprotect 65536 8191 3 (mkEffect 0 [] [(65536, 8191)])
        noaccess_three_pages = CheckReject := by
  check_norm

/-- A page and a byte over a one-page reservation rounds past the grant:
Linux walks on into whatever follows (:934-997) or answers -ENOMEM where
nothing does (:1000-1001); the model declines.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem rounded_range_past_the_grant_is_unmodeled :
    check_mprotect 65536 4097 3 (mkEffect 0 [] []) noaccess_one_page =
      CheckUnmodeled := by
  check_norm

/-- The containment tests read the ROUNDED length.  On `noaccess_owned_short`
an rw `mprotect` of the 4088 bytes `vm_maps` owns rounds to the page
(:883), which `vm_maps` does not contain, and the checker declines — a
checker testing the raw length would find both ledgers containing 4088
bytes and accept 0 with a zero-fill of eight bytes the model does not own
(and Linux does: the page's VMA stands, mm/mmap.c:153-158, so Linux
answers 0 here, which the model cannot name from its ledger).  The mutation
sweep of the deep review of #1065 found the raw-length mutant survived
every pin, every fixture being page-granular; this kills it.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem containment_reads_the_rounded_length :
    check_mprotect 65536 4088 3 (mkEffect 0 [] [(65536, 4096)]) noaccess_owned_short =
      CheckUnmodeled ∧
    check_mprotect 65536 4088 3 (mkEffect 0 [] [(65536, 4088)]) noaccess_owned_short =
      CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- The no-op arm's containment reads the rounded length too.  On
`rw_owned_short` the same call rounds to a page `vm_maps` does not own,
and the checker declines rather than accept the 0 Linux answers over the
standing VMA — page-granular because the grow extends the VMA to
`newbrk = PAGE_ALIGN(brk)` (mm/mmap.c:153, the grow of :194 spanning
`oldbrk` to `newbrk`), not to the byte asked for.  The exposure twin
above does not cover this: the sweep's mutant of the NO-OP arm's
`map_contains` alone
survived every pin after the twin landed, the exposure pin reaching only
the first arm; this one reaches the second.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem noop_containment_reads_the_rounded_length :
    check_mprotect 65536 4088 3 (mkEffect 0 [] []) rw_owned_short = CheckUnmodeled := by
  check_norm

/-! ### Where the split falls

`vma_modify` (mm/vma.c:1642, Linux v6.18.46), reached from
`vma_modify_flags` (:1693), splits a preceding portion (:1664-1668), a
trailing portion (:1672-1676), both, or neither when the VMA is the range
(:1679).  The middle-page pin above is "both";
these are the other three. -/

/-- The left page: one remnant, to the right.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup; mm/vma.c:vma_modify_flags,vma_modify,__split_vma@v6.18.46 -/
theorem left_page_split_leaves_the_right :
    check_mprotect 65536 4096 3 (mkEffect 0 [] [(65536, 4096)])
        noaccess_three_pages =
      CheckOk (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [(69632, 8192)] 0 0 16384 0 demo_sp))
        [] := by
  check_norm

/-- The right page: one remnant, to the left.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup; mm/vma.c:vma_modify_flags,vma_modify,__split_vma@v6.18.46 -/
theorem right_page_split_leaves_the_left :
    check_mprotect 73728 4096 3 (mkEffect 0 [] [(73728, 4096)])
        noaccess_three_pages =
      CheckOk (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [(65536, 8192)] 0 0 16384 0 demo_sp))
        [] := by
  check_norm

/-- The whole reservation: no split, no remnant.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup; mm/vma.c:vma_modify_flags,vma_modify@v6.18.46 -/
theorem whole_reservation_exposed_leaves_nothing :
    check_mprotect 65536 12288 3 (mkEffect 0 [] [(65536, 12288)])
        noaccess_three_pages =
      CheckOk (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [] 0 0 16384 0 demo_sp)) [] := by
  check_norm

/-! ### The effect of an exposure is one zero range and nothing else

The kernel changes one contiguous `[nstart, tmp)` per VMA (:980-990) and
writes, unmaps and copies nothing. -/

/-- The zero range shifted by a page is not the page exposed.
probe: testing/syscall-check/tests/noaccess_vm.c#reject --mutate mprotect:drop-zeros,smuggle-zeros:a0+4096:4096 -- fresh -/
theorem exposure_shifted_zeros_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 3 (mkEffect 0 [] [(69632, 4096)]) noaccess_two_pages
      ≠ CheckOk m' evs := by
  check_refute

/-- A zero range twice the page is not it either.
probe: testing/syscall-check/tests/noaccess_vm.c#reject --mutate mprotect:drop-zeros,smuggle-zeros:a0:8192 -- fresh -/
theorem exposure_doubled_zeros_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 3 (mkEffect 0 [] [(65536, 8192)]) noaccess_two_pages
      ≠ CheckOk m' evs := by
  check_refute

/-- Half the page…
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem middle_partial_zeros_are_rejected :
    check_mprotect 69632 4096 3 (mkEffect 0 [] [(69632, 2048)])
        noaccess_three_pages = CheckReject := by
  check_norm

/-- …and the page in two halves: the effect names one range.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem middle_split_zeros_are_rejected :
    check_mprotect 69632 4096 3 (mkEffect 0 [] [(69632, 2048), (71680, 2048)])
        noaccess_three_pages = CheckReject := by
  check_norm

/-- The right zero range with a positive return: `do_mprotect_pkey` returns
`error`, 0 or negative (:1005).
probe: testing/syscall-check/tests/noaccess_vm.c#reject --mutate mprotect:ret=1 -- fresh -/
theorem exposure_positive_return_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 3 (mkEffect 1 [] [(65536, 4096)]) noaccess_two_pages
      ≠ CheckOk m' evs := by
  check_refute

/-- A positive 12 is neither 0 nor -ENOMEM.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem exposure_positive_errno_refused :
    check_mprotect 65536 4096 3 (mkEffect 12 [] []) noaccess_one_page = CheckReject := by
  check_norm

/-- The return is compared at the full width of the register, on both
arms: a word whose LOW 32 bits are 0 is not a 0, and the zero-extended
-ENOMEM `0xfffffff4` is not -ENOMEM.  `do_mprotect_pkey`'s `int` comes back
through `SYSCALL_DEFINE3`'s `long` (:1008-1012) sign-extended, so the
register holds 0 or `2^64 - 12` and never these.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem return_is_compared_at_full_width :
    check_mprotect 65536 4096 3 (mkEffect 4294967296 [] [(65536, 4096)]) noaccess_one_page =
      CheckReject ∧
    check_mprotect 65536 4096 3 (mkEffect 4294967284 [] []) noaccess_one_page =
      CheckReject ∧
    check_mprotect 65536 4096 3 (mkEffect 4294967296 [] []) rw_two_pages = CheckReject ∧
    check_mprotect 65536 4096 3 (mkEffect 4294967284 [] []) rw_two_pages = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- A write beside the zero range: mm/mprotect.c copies nothing to user
memory.
probe: testing/syscall-check/tests/noaccess_vm.c#reject --mutate mprotect:smuggle-write:a0:1 -- fresh -/
theorem exposure_write_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 3 (mkEffect 0 [(65536, [0])] [(65536, 4096)])
        noaccess_two_pages ≠ CheckOk m' evs := by
  check_refute

/-- An errno with an unmap: the -ENOMEM returns (:803, :808) before any VMA
is touched, and the failure path only unaccounts (:853-855).
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem exposure_errno_with_unmap_refused :
    check_mprotect 65536 4096 3
        (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(65536, 4096)] [] []) noaccess_one_page
      = CheckReject := by
  check_norm

/-- A copy-in beside the exposure: `do_mprotect_pkey` takes three registers
and reads no user memory.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem exposure_copyin_refused :
    check_mprotect 65536 4096 3
        (SyscallEffect.mkEffectU 0 [] [(65536, 4096)] [] [] [(65536, 8)]) noaccess_one_page
      = CheckReject := by
  check_norm

/-- A memory copy beside the exposure: `do_mprotect_pkey` moves no user
memory either; the one thing an exposure does to user memory is the
zero-fill of the pages it makes accessible.  The copies ledger was the one
of the five that no pin on this arm refused (mutation sweep, deep review of
#1065).
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem exposure_copy_refused :
    check_mprotect 65536 4096 3
        (SyscallEffect.mkEffectU 0 [] [(65536, 4096)] [] [MemCopy.mkCopy 65536 69632 4096] [])
        noaccess_one_page = CheckReject := by
  check_norm

/-- …and beside the -ENOMEM, which returns at :803 or :808 before any page
is touched.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem exposure_errno_with_copy_refused :
    check_mprotect 65536 4096 3
        (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [] [MemCopy.mkCopy 65536 69632 4096] [])
        noaccess_one_page = CheckReject := by
  check_norm

/-! ### The backed budget

Exposing a reserved page consumes backed capacity at the permission
transition, mm/mprotect.c:799-810 (Linux v6.18.46): `may_expand_vm`
(mm/mmap.c, Linux v6.18.46) against the address-space limit, then
`security_vm_enough_memory_mm` (security/security.c, Linux v6.18.46)
against the commit charge.  With a zero-byte budget the success is
refused
while the -ENOMEM outcome remains available. -/

/-- Rocq: `mprotect_over_backed_budget_rejects_success`.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem over_backed_budget_rejects_success :
    check_mprotect 65536 4096 3 (mkEffect 0 [] [(65536, 4096)])
        noaccess_zero_backing = CheckReject := by
  check_norm

/-- Rocq: `mprotect_over_backed_budget_allows_enomem`.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem over_backed_budget_allows_enomem :
    check_mprotect 65536 4096 3 (mkEffect (errno_ret ENOMEM) [] [])
        noaccess_zero_backing = CheckOk noaccess_zero_backing [] := by
  check_norm

/-- The budget is tested to the byte at the post-state: exposing one page
of the probe's two-page reservation charges 4096, which a limit of exactly
4096 admits…
probe: testing/syscall-check/tests/noaccess_vm.c#conform --alloc-limit 4096 -- fresh -/
theorem exact_budget_admits_the_exposure :
    check_mprotect 65536 4096 3 (mkEffect 0 [] [(65536, 4096)]) fresh_exact_budget =
      CheckOk (fixture (VmMaps.mkVmMapsFull [] [(65536, 8192)] [(69632, 4096)] 0 0 4096 0 demo_sp))
        [] := by
  check_norm

/-- …and a limit one byte short refuses: the kernel's 0 is not accepted…
probe: testing/syscall-check/tests/noaccess_vm.c#reject --alloc-limit 4095 -- fresh -/
theorem one_byte_short_budget_success_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 3 (mkEffect 0 [] [(65536, 4096)]) fresh_one_byte_short
      ≠ CheckOk m' evs := by
  check_refute

/-- …while the -ENOMEM the charge answers (:807-808) stays admitted there.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem one_byte_short_budget_enomem_admitted :
    check_mprotect 65536 4096 3 (mkEffect (errno_ret ENOMEM) [] []) fresh_one_byte_short =
      CheckOk fresh_one_byte_short [] := by
  check_norm

/-- Exposing a MAP_NORESERVE guard keeps its lazy provenance: the post-state
is the spec's own `mprotect_model_next`, which `Checks/Cases/Mm/Mprotect.lean`
pins does not charge the second page eagerly — the charge is taken only
when `oldflags` lacks VM_ACCOUNT|VM_WRITE|VM_HUGETLB|VM_SHARED|VM_NORESERVE
(:804-810).  Rocq:
`mprotect_lazy_guard_preserves_backing_provenance`.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem lazy_guard_preserves_backing_provenance :
    check_mprotect 69632 4096 3 (mkEffect 0 [] [(69632, 4096)])
        mprotect_lazy_guard =
      CheckOk (mprotect_model_next mprotect_lazy_guard 69632 4096) [] := by
  check_norm

/-! ## The no-op: rw over a live rw mapping

`mprotect_fixup` returns 0 at mm/mprotect.c:769-772 (Linux v6.18.46) when
`newflags == oldflags`, before any accounting; nothing is split, zeroed or
charged. -/

/-- The probe's `mprotect(p, 4096, rw)` on its rw grant: 0, nothing else in
the effect.
probe: testing/syscall-check/tests/mprotect_exec.c#conform -- rw -/
theorem already_rw_is_zero :
    check_mprotect 65536 4096 3 (mkEffect 0 [] []) rw_two_pages =
      CheckOk rw_two_pages [] := by
  check_norm

/-- A positive return: mprotect answers 0 or -errno.
probe: testing/syscall-check/tests/mprotect_exec.c#reject --mutate mprotect:ret=1 -- rw -/
theorem already_rw_positive_return_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 3 (mkEffect 1 [] []) rw_two_pages
      ≠ CheckOk m' evs := by
  check_refute

/-- …not the length it protected either.
probe: testing/syscall-check/tests/mprotect_exec.c#reject --mutate mprotect:ret=4096 -- rw -/
theorem already_rw_length_return_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 3 (mkEffect 4096 [] []) rw_two_pages
      ≠ CheckOk m' evs := by
  check_refute

/-- An already-rw mprotect exposes no zero range.
probe: testing/syscall-check/tests/mprotect_exec.c#reject --mutate mprotect:smuggle-zeros:a0:4096 -- rw -/
theorem already_rw_zeros_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 3 (mkEffect 0 [] [(65536, 4096)]) rw_two_pages
      ≠ CheckOk m' evs := by
  check_refute

/-- …and cannot fail with -ENOMEM: `mprotect_fixup` returns 0 before any
allocation.  Rocq: `mprotect_already_rw_errno_is_rejected`.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem already_rw_errno_is_rejected :
    check_mprotect 65536 4096 3 (mkEffect (errno_ret ENOMEM) [] []) rw_two_pages =
      CheckReject := by
  check_norm

/-- The same refusal as the probe states it.
probe: testing/syscall-check/tests/mprotect_exec.c#reject --mutate mprotect:ret=-ENOMEM -- rw -/
theorem already_rw_enomem_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 3 (mkEffect (errno_ret ENOMEM) [] []) rw_two_pages
      ≠ CheckOk m' evs := by
  check_refute

/-- …nor with -EINVAL: aligned start, nonzero length, permitted prot.
probe: testing/syscall-check/tests/mprotect_exec.c#reject --mutate mprotect:ret=-EINVAL -- rw -/
theorem already_rw_einval_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 3 (mkEffect (errno_ret EINVAL) [] []) rw_two_pages
      ≠ CheckOk m' evs := by
  check_refute

/-- A failed mprotect exposes nothing.
probe: testing/syscall-check/tests/mprotect_exec.c#reject --mutate mprotect:ret=-ENOMEM,smuggle-zeros:a0:4096 -- rw -/
theorem already_rw_errno_with_zeros_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 3 (mkEffect (errno_ret ENOMEM) [] [(65536, 4096)])
        rw_two_pages ≠ CheckOk m' evs := by
  check_refute

/-- A write in the effect: mprotect copies nothing to user memory, so no
accepting arm carries one.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem already_rw_write_refused :
    check_mprotect 65536 4096 3 (mkEffect 0 [(65536, [0])] []) rw_two_pages = CheckReject := by
  check_norm

/-- Two heap pages grown by one brk call, then rw over both: inside one
record, so modeled.
probe: testing/syscall-check/tests/mprotect_exec.c#conform -- onerecord -/
theorem already_rw_whole_record_is_zero :
    check_mprotect 65536 8192 3 (mkEffect 0 [] []) rw_two_pages =
      CheckOk rw_two_pages [] := by
  check_norm

/-- …exposing nothing…
probe: testing/syscall-check/tests/mprotect_exec.c#reject --mutate mprotect:smuggle-zeros:a0:8192 -- onerecord -/
theorem already_rw_whole_record_zeros_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 8192 3 (mkEffect 0 [] [(65536, 8192)]) rw_two_pages
      ≠ CheckOk m' evs := by
  check_refute

/-- …and not -EINVAL on a brk record either.
probe: testing/syscall-check/tests/mprotect_exec.c#reject --mutate mprotect:ret=-EINVAL -- onerecord -/
theorem already_rw_whole_record_einval_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 8192 3 (mkEffect (errno_ret EINVAL) [] []) rw_two_pages
      ≠ CheckOk m' evs := by
  check_refute


/-- The no-op with an unmap in the effect: `mprotect_fixup` returns at
:769-772 before anything is touched.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem already_rw_unmap_refused :
    check_mprotect 65536 4096 3
        (SyscallEffect.mkEffectU 0 [] [] [(65536, 4096)] [] []) rw_two_pages = CheckReject := by
  check_norm

/-- The no-op with a memory copy, and with a copy-in: `do_mprotect_pkey`
neither moves nor reads user memory, and `mprotect_fixup` has returned at
:769-772 before it could.  These two ledgers were the ones no pin on this
arm refused (mutation sweep, deep review of #1065).
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem already_rw_copy_and_copyin_refused :
    check_mprotect 65536 4096 3
        (SyscallEffect.mkEffectU 0 [] [] [] [MemCopy.mkCopy 65536 69632 4096] []) rw_two_pages
      = CheckReject ∧
    check_mprotect 65536 4096 3
        (SyscallEffect.mkEffectU 0 [] [] [] [] [(65536, 8)]) rw_two_pages = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- …and -EBADF names an fd where the no-op has none either.
probe: testing/syscall-check/tests/errno_mprotect.c#reject --mutate mprotect:ret=-EBADF -- mprotect -/
theorem already_rw_ebadf_refused (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 3 (mkEffect (errno_ret EBADF) [] []) rw_two_pages
      ≠ CheckOk m' evs := by
  check_refute

/-- A one-byte length over a live rw mapping rounds to its page (:883) and
is the same no-op.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem already_rw_short_length_is_zero :
    check_mprotect 65536 1 3 (mkEffect 0 [] []) rw_two_pages =
      CheckOk rw_two_pages [] := by
  check_norm

/-! ## What the checker declines

Each of these is reached on the ARGUMENT SHAPE, so no offered effect
rescues it: the arm answers `CheckUnmodeled`, never `CheckReject`, and a
conformance run stops rather than reporting a failure the model has not
earned.  `Sys/Mm/Mprotect.lean` argues each decline; this file pins that
the checker takes it.  The probe's `fail-closed` cases are cited on the
NEGATIVE twins below, not on the `= CheckUnmodeled` pins:
`tools/check_lean_pin_evidence.py` reads a polarity off the statement,
and `CheckUnmodeled` is not the word `Unmodeled` it looks for, so a
decline stated as an equation is read as a positive claim wanting a
`conform` case.  The kernel line on each decline says what Linux does
where the model stops. -/

/-- A range no grant covers: Linux's `vma_find` answers -ENOMEM at :904-907,
and the model, which tracks only the grants it saw, declines rather than
guesses.  Rocq: `mprotect_unmapped_forged_success_is_unmodeled`.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem unmapped_forged_success_is_unmodeled :
    check_mprotect 131072 4096 3 (mkEffect 0 [] []) noaccess_three_pages =
      CheckUnmodeled := by
  check_norm

/-- …which is the probe's fail-closed stop with the kernel's real -ENOMEM…
probe: testing/syscall-check/tests/noaccess_vm.c#fail-closed -- unmapped -/
theorem unmapped_enomem_accepts_nothing (m' : Model) (evs : List event) :
    check_mprotect 131072 4096 3 (mkEffect (errno_ret ENOMEM) [] []) noaccess_three_pages
      ≠ CheckOk m' evs := by
  check_refute

/-- …and with a forged 0: the state gate wins over the effect.
probe: testing/syscall-check/tests/noaccess_vm.c#fail-closed --mutate mprotect:ret=0 -- unmapped -/
theorem unmapped_forged_success_accepts_nothing (m' : Model) (evs : List event) :
    check_mprotect 131072 4096 3 (mkEffect 0 [] []) noaccess_three_pages
      ≠ CheckOk m' evs := by
  check_refute

/-- A no-access interval with no grant under it is a ledger the model
cannot answer for: Linux answers 0 where the page's VMA still stands (the
same-page brk shrink, mm/mmap.c:153-158) and -ENOMEM where none does
(:905-907), and the ledger cannot tell the two apart.  Rocq:
`mprotect_noaccess_outside_vm_maps_is_unmodeled`.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem noaccess_outside_vm_maps_is_unmodeled :
    check_mprotect 65536 4096 3 (mkEffect 0 [] [(65536, 4096)]) noaccess_unowned =
      CheckUnmodeled := by
  check_norm

/-- …the probe's shrink-then-enable: Linux's 0 is not accepted.
probe: testing/syscall-check/tests/noaccess_vm.c#fail-closed -- brk-samepage-protect -/
theorem noaccess_outside_vm_maps_accepts_nothing (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 3 (mkEffect 0 [] [(65536, 4096)]) noaccess_unowned
      ≠ CheckOk m' evs := by
  check_refute

/-- A range across two adjacent grants: Linux walks every VMA of the
range (:934-997) and answers 0 when the walk reaches `end` (:1000-1001);
the rw arm asks for ONE record and declines.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem spanning_two_records_is_unmodeled :
    check_mprotect 65536 8192 3 (mkEffect 0 [] []) two_adjacent_pages =
      CheckUnmodeled := by
  check_norm

/-- …so the harness stops there: Linux's 0 is not accepted, and neither is
anything else.
probe: testing/syscall-check/tests/mprotect_exec.c#fail-closed -- span -/
theorem spanning_two_records_accepts_nothing (m' : Model) (evs : List event) :
    check_mprotect 65536 8192 3 (mkEffect 0 [] []) two_adjacent_pages
      ≠ CheckOk m' evs := by
  check_refute

/-- A page of the image, which `vm_maps` does not record: Linux finds the
VMA and answers, the model has no grant to answer with.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem image_range_is_unmodeled :
    check_mprotect 65536 4096 3 (mkEffect 0 [] []) noaccess_base =
      CheckUnmodeled := by
  check_norm

/-- …and an errno on it rescues nothing: the decline is on the range.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem image_range_errno_is_unmodeled :
    check_mprotect 65536 4096 3 (mkEffect (errno_ret ENOMEM) [] []) noaccess_base =
      CheckUnmodeled := by
  check_norm

/-- The harness's view of the image page: nothing is accepted, with the
kernel's 0…
probe: testing/syscall-check/tests/mprotect_exec.c#fail-closed -- image -/
theorem image_range_accepts_nothing (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 3 (mkEffect 0 [] []) noaccess_base
      ≠ CheckOk m' evs := by
  check_refute

/-- …or with a lying kernel's -ENOMEM.
probe: testing/syscall-check/tests/mprotect_exec.c#fail-closed --mutate mprotect:ret=-ENOMEM -- image -/
theorem image_range_errno_accepts_nothing (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 3 (mkEffect (errno_ret ENOMEM) [] []) noaccess_base
      ≠ CheckOk m' evs := by
  check_refute

/-- The vdso's page is another the ledger does not hold — `vm_maps` records
the grants a run saw, `vm_reserved` the image, and the vdso is neither —
and under CONFIG_MSEAL_SYSTEM_MAPPINGS it is sealed at exec
(arch/riscv/kernel/vdso.c:139, Linux v6.18.46), so rw over it is a real
-EPERM (`mprotect_fixup`, :766-767): declined on the range, as every
unheld range is — the `vm_maps` gate, the ledger's stand-in for the VMA
walk `do_mprotect_pkey` starts at `vma_find` (:904-907), which here finds
the vdso the ledger never held — and never contradicted.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem sealed_system_mapping_eperm_is_unmodeled :
    check_mprotect 65536 4096 3 (mkEffect (errno_ret EPERM) [] []) noaccess_base =
      CheckUnmodeled := by
  check_norm

/-- The vvar's real answer is the other errno: its data pages lack
VM_MAYWRITE (lib/vdso/datastore.c:101-103), so rw over them is the VM_MAY*
-EACCES of :960-963, reached before the seal is consulted — declined on the
same gate, never refused.  The refusal of -EACCES above
(`exposure_eperm_and_eacces_refused`) is for a grant `vm_maps` holds; this
range it does not.
kernel: mm/mprotect.c:do_mprotect_pkey; lib/vdso/datastore.c:vdso_install_vvar_mapping@v6.18.46 -/
theorem sealed_system_mapping_eacces_is_unmodeled :
    check_mprotect 65536 4096 3 (mkEffect (errno_ret EACCES) [] []) noaccess_base =
      CheckUnmodeled := by
  check_norm

/-- PROT_READ over a live rw mapping: Linux answers 0 — `newflags` drops
VM_WRITE (:953-957), `mprotect_fixup` applies it (:829, :834) and returns
0 (:851) — the model declines, and offering the checker Linux's answer
yields `CheckUnmodeled`, not `CheckOk`.  Rocq:
`mprotect_read_only_downgrade_is_unmodeled`.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup; include/uapi/asm-generic/mman-common.h:PROT_READ@v6.18.46 -/
theorem read_only_downgrade_is_unmodeled :
    check_mprotect 65536 4096 1 (mkEffect 0 [] []) rw_two_pages =
      CheckUnmodeled := by
  check_norm

/-- …which is the probe's fail-closed stop: the kernel's 0 is not accepted.
probe: testing/syscall-check/tests/mprotect_exec.c#fail-closed -- ro -/
theorem read_only_downgrade_accepts_nothing (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 1 (mkEffect 0 [] []) rw_two_pages
      ≠ CheckOk m' evs := by
  check_refute

/-- …with a zero-fill offered as well: the decline is on the prot, not on
the effect.  Rocq: `mprotect_read_only_downgrade_with_zeros_is_unmodeled`.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem read_only_downgrade_with_zeros_is_unmodeled :
    check_mprotect 65536 4096 1 (mkEffect 0 [] [(65536, 4096)]) rw_two_pages =
      CheckUnmodeled := by
  check_norm

/-- PROT_READ over a range still PROT_NONE: that range IS in `vm_noaccess`,
so the exposure's own gate matches on everything but the prot word.  Rocq:
`mprotect_read_only_over_noaccess_is_unmodeled`.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem read_only_over_noaccess_is_unmodeled :
    check_mprotect 69632 4096 1 (mkEffect 0 [] [(69632, 4096)]) noaccess_three_pages =
      CheckUnmodeled := by
  check_norm

/-- PROT_READ|PROT_EXEC over an anonymous rw grant: Linux answers 0 —
`newflags` gains VM_EXEC (:953-957) and `mprotect_fixup` applies it
(:829-851) — on a run that has not enabled MDWE, whose
`map_deny_write_exec` (:965-968) refuses the gain with -EACCES; the model
has no mutable page permissions and declines either way.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem exec_is_unmodeled :
    check_mprotect 65536 4096 5 (mkEffect 0 [] []) rw_two_pages =
      CheckUnmodeled := by
  check_norm

/-- …so the probe's fail-closed stop accepts nothing, Linux's 0 included.
probe: testing/syscall-check/tests/mprotect_exec.c#fail-closed -- exec -/
theorem exec_accepts_nothing (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 5 (mkEffect 0 [] []) rw_two_pages ≠ CheckOk m' evs := by
  check_refute

/-- PROT_READ|PROT_WRITE|PROT_EXEC: Linux's 0 by the same lines, and under
MDWE the -EACCES of a writable mapping made executable; declined.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem rwx_is_unmodeled :
    check_mprotect 65536 4096 7 (mkEffect 0 [] []) rw_two_pages =
      CheckUnmodeled := by
  check_norm

/-- The MDWE -EACCES of a writable mapping made executable
(`map_deny_write_exec`, include/linux/mman.h:212-213, reached at :965-968),
offered: declined by the same prot gate.
kernel: mm/mprotect.c:do_mprotect_pkey; include/linux/mman.h:map_deny_write_exec@v6.18.46 -/
theorem rwx_eacces_is_unmodeled :
    check_mprotect 65536 4096 7 (mkEffect (errno_ret EACCES) [] []) rw_two_pages =
      CheckUnmodeled := by
  check_norm

/-- probe: testing/syscall-check/tests/mprotect_exec.c#fail-closed -- rwx -/
theorem rwx_accepts_nothing (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 7 (mkEffect 0 [] []) rw_two_pages ≠ CheckOk m' evs := by
  check_refute

/-- PROT_EXEC alone: Linux answers 0, dropping VM_READ|VM_WRITE and adding
VM_EXEC (:953-957) — or, with MDWE armed, the -EACCES of a non-executable
mapping becoming executable (`map_deny_write_exec`,
include/linux/mman.h:201-220, whose `!(old & VM_EXEC)` test denies at its
own :216-217; reached at :965-968); declined either way, like every word
that is not rw.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup; include/linux/mman.h:map_deny_write_exec@v6.18.46 -/
theorem exec_only_is_unmodeled :
    check_mprotect 65536 4096 4 (mkEffect 0 [] []) rw_two_pages = CheckUnmodeled := by
  check_norm

/-- The MDWE -EACCES named above, offered: the prot gate declines before
the effect is read, so "either way" holds on both sides.
kernel: mm/mprotect.c:do_mprotect_pkey; include/linux/mman.h:map_deny_write_exec@v6.18.46 -/
theorem exec_only_eacces_is_unmodeled :
    check_mprotect 65536 4096 4 (mkEffect (errno_ret EACCES) [] []) rw_two_pages =
      CheckUnmodeled := by
  check_norm

/-- probe: testing/syscall-check/tests/mprotect_exec.c#fail-closed -- exec-only -/
theorem exec_only_accepts_nothing (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 4 (mkEffect 0 [] []) rw_two_pages ≠ CheckOk m' evs := by
  check_refute

/-- PROT_NONE over a live mapping: Linux answers 0, `newflags` dropping
VM_READ|VM_WRITE (:953-957); the model, whose only inaccessible interval
is a reservation's, would keep reading the page, and declines.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem none_is_unmodeled :
    check_mprotect 65536 4096 0 (mkEffect 0 [] []) rw_two_pages =
      CheckUnmodeled := by
  check_norm

/-- probe: testing/syscall-check/tests/mprotect_exec.c#fail-closed -- none -/
theorem none_accepts_nothing (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 0 (mkEffect 0 [] []) rw_two_pages ≠ CheckOk m' evs := by
  check_refute

/-- PROT_SEM|rw: Linux permits PROT_SEM and answers 0; the model compares
the whole word and declines, so a masking spec would conform where this
one stops.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup; include/linux/mman.h:arch_validate_prot@v6.18.46 -/
theorem sem_rw_is_unmodeled :
    check_mprotect 65536 4096 11 (mkEffect 0 [] []) rw_two_pages =
      CheckUnmodeled := by
  check_norm

/-- probe: testing/syscall-check/tests/mprotect_exec.c#fail-closed -- sem-rw -/
theorem sem_rw_accepts_nothing (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 11 (mkEffect 0 [] []) rw_two_pages ≠ CheckOk m' evs := by
  check_refute

/-- `prot = 0x80000003`: `arch_validate_prot`'s -EINVAL; the model declines
the word rather than answer it.
kernel: mm/mprotect.c:do_mprotect_pkey; include/linux/mman.h:arch_validate_prot@v6.18.46 -/
theorem bit31_is_unmodeled :
    check_mprotect 65536 4096 2147483651 (mkEffect (errno_ret EINVAL) [] [])
        rw_two_pages = CheckUnmodeled := by
  check_norm

/-- …so the kernel's -EINVAL is not accepted either.
probe: testing/syscall-check/tests/mprotect_exec.c#fail-closed -- bit31 -/
theorem bit31_accepts_nothing (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 2147483651 (mkEffect (errno_ret EINVAL) [] []) rw_two_pages
      ≠ CheckOk m' evs := by
  check_refute

/-- `(1 << 32) | rw`: the full `unsigned long` reaches `arch_validate_prot`.
kernel: mm/mprotect.c:do_mprotect_pkey; include/linux/mman.h:arch_validate_prot@v6.18.46 -/
theorem highbits_is_unmodeled :
    check_mprotect 65536 4096 4294967299 (mkEffect (errno_ret EINVAL) [] [])
        rw_two_pages = CheckUnmodeled := by
  check_norm

/-- probe: testing/syscall-check/tests/mprotect_exec.c#fail-closed -- highbits -/
theorem highbits_accepts_nothing (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 4294967299 (mkEffect (errno_ret EINVAL) [] []) rw_two_pages
      ≠ CheckOk m' evs := by
  check_refute

/-- `len` and `prot` swapped: a length of 3 rounds to a page and a prot of
4096 is declined.
kernel: mm/mprotect.c:do_mprotect_pkey; include/linux/mman.h:arch_validate_prot@v6.18.46 -/
theorem swapped_len_and_prot_is_unmodeled :
    check_mprotect 65536 3 4096 (mkEffect (errno_ret EINVAL) [] []) rw_two_pages =
      CheckUnmodeled := by
  check_norm

/-- probe: testing/syscall-check/tests/mprotect_exec.c#fail-closed -- wrong-order -/
theorem swapped_len_and_prot_accepts_nothing (m' : Model) (evs : List event) :
    check_mprotect 65536 3 4096 (mkEffect (errno_ret EINVAL) [] []) rw_two_pages
      ≠ CheckOk m' evs := by
  check_refute


/-- PROT_GROWSDOWN with rw on a NONZERO length over an mmap grant: Linux
answers -EINVAL, since the VMA is not `VM_GROWSDOWN` (:909-915); the model
declines the word rather than answer for the flag.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem growsdown_nonzero_length_is_unmodeled :
    check_mprotect 65536 4096 16777219 (mkEffect (errno_ret EINVAL) [] [])
        rw_two_pages = CheckUnmodeled := by
  check_norm

/-- …so the kernel's answer is not accepted, and neither is a 0.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem growsdown_nonzero_length_accepts_nothing (m' : Model) (evs : List event) :
    check_mprotect 65536 4096 16777219 (mkEffect 0 [] []) rw_two_pages
      ≠ CheckOk m' evs := by
  check_refute

/-- PROT_GROWSUP likewise (:919-923).
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem growsup_nonzero_length_is_unmodeled :
    check_mprotect 65536 4096 33554435 (mkEffect (errno_ret EINVAL) [] [])
        rw_two_pages = CheckUnmodeled := by
  check_norm

/-! ### The mixed-protection range

The one ledger decline that is not an uncontained range.  `mixed_two_pages`
(`Checks/Cases/Mm/Mprotect.lean`) is a two-page grant whose second page
alone is inaccessible; a request over both is inside `vm_maps` and
neither inside nor clear of `vm_noaccess`. -/

/-- A grant whose pages differ in protection: Linux walks the range's
VMAs at :934-997, both present, and answers 0 for the whole of it; the
model, which knows a protection interval only as wholly inaccessible or
wholly not, declines rather than pretend the suffix was already writable.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem mixed_protection_success_is_unmodeled :
    check_mprotect 65536 8192 3 (mkEffect 0 [] []) mixed_two_pages =
      CheckUnmodeled := by
  check_norm

/-- …and the zero-fill of the page that was inaccessible, the honest
effect of Linux's answer, does not make the call modeled: the decline is
on the range, not on the effect offered.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem mixed_protection_zeroed_suffix_is_unmodeled :
    check_mprotect 65536 8192 3 (mkEffect 0 [] [(69632, 4096)]) mixed_two_pages =
      CheckUnmodeled := by
  check_norm

/-- The harness's view: nothing is accepted on a mixed range, with the 0
Linux answered…
probe: testing/syscall-check/tests/noaccess_vm.c#fail-closed -- partial -/
theorem mixed_protection_accepts_nothing (m' : Model) (evs : List event) :
    check_mprotect 65536 8192 3 (mkEffect 0 [] []) mixed_two_pages
      ≠ CheckOk m' evs := by
  check_refute

/-- `region_free` is exclusive at the top: the rw first page of the mixed
fixture ends where its PROT_NONE page begins, and rw over it alone is the
no-op's 0 (`mprotect_fixup`, :769-772 — the first page's VMA already
carries the flags), nothing exposed and no -ENOMEM, where the same call
over both pages is declined above.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem mixed_rw_page_alone_is_the_noop :
    check_mprotect 65536 4096 3 (mkEffect 0 [] []) mixed_two_pages =
      CheckOk mixed_two_pages [] ∧
    check_mprotect 65536 4096 3 (mkEffect (errno_ret ENOMEM) [] []) mixed_two_pages =
      CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- …and exposing its PROT_NONE page alone completes the reservation: the
post-state is `rw_two_pages`, the fixture every no-op pin runs on.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem mixed_noaccess_page_alone_completes_the_reservation :
    check_mprotect 69632 4096 3 (mkEffect 0 [] [(69632, 4096)]) mixed_two_pages =
      CheckOk rw_two_pages [] := by
  check_norm

/-! ## The witness

`mprotect_witness` names one admitted outcome per input, and
`mprotect_witness_ok` proves it admitted; these read the choice off. -/

/-- The gates' answers, in order: the grow conflict…
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem witness_grows_conflict :
    mprotect_witness 65536 0 50331651 rw_two_pages =
      ret_outcome (errno_ret EINVAL) rw_two_pages := by
  witness_norm

/-- …the unaligned start…
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem witness_unaligned :
    mprotect_witness 65537 0 3 rw_two_pages =
      ret_outcome (errno_ret EINVAL) rw_two_pages := by
  witness_norm

/-- …the zero length…
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem witness_zero_length :
    mprotect_witness 65536 0 5 rw_two_pages = ret_outcome 0 rw_two_pages := by
  witness_norm

/-- …and the wrapped end, for a prot the model would otherwise decline.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem witness_wrapping_end :
    mprotect_witness 9223372036854775808 9223372036854775808 4 noaccess_three_pages =
      ret_outcome (errno_ret ENOMEM) noaccess_three_pages := by
  witness_norm

/-- On the exposure the witness takes the errno arm: -ENOMEM is admitted
whatever the budget, where the success depends on it.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem witness_exposure_is_the_errno :
    mprotect_witness 69632 4096 3 noaccess_three_pages =
      ret_outcome (errno_ret ENOMEM) noaccess_three_pages := by
  witness_norm

/-- On a live rw mapping the witness is the no-op's 0.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem witness_already_rw :
    mprotect_witness 65536 4096 3 rw_two_pages = ret_outcome 0 rw_two_pages := by
  witness_norm

/-- Where the checker declines, so does the witness: the read-only downgrade…
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem witness_read_only_is_unmodeled :
    mprotect_witness 65536 4096 1 rw_two_pages = Unmodeled := by
  witness_norm

/-- …and a range no grant covers.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem witness_unmapped_is_unmodeled :
    mprotect_witness 131072 4096 3 noaccess_three_pages = Unmodeled := by
  witness_norm

/-- …a no-access interval no grant holds, the exposure gate's `vm_maps`
conjunct…
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem witness_noaccess_unowned_is_unmodeled :
    mprotect_witness 65536 4096 3 noaccess_unowned = Unmodeled := by
  witness_norm

/-- …and the mixed range, the no-op gate's `region_free` conjunct.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem witness_mixed_is_unmodeled :
    mprotect_witness 65536 8192 3 mixed_two_pages = Unmodeled := by
  witness_norm

/-! ## The ledger

Rocq's `check_mprotect_preserves` (`Checks/VmMapsDisjoint.v`) turns on one
fact — an accepting `check_mprotect` leaves `vm_maps` as it was — which
the checker file states for every accepting run as `check_mprotect_vm_maps`
(its header says why not in Rocq's `vm_wf` shape).  This reads that fact
off the concrete split above: the post-state
`middle_splits_noaccess_and_zeros_exactly` names has the grant whole. -/

/-- The split of the middle page moves a page out of `vm_noaccess` and
leaves the grant in `vm_maps` whole — `check_mprotect_vm_maps` at the
split's own answer.
model: `vm_maps` records grants and `vm_noaccess` protection intervals; a protection change moves no grant -/
theorem middle_split_keeps_vm_maps :
    (m_vmmaps (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [(65536, 4096), (73728, 4096)]
                          0 0 16384 0 demo_sp))).vm_maps =
      (m_vmmaps noaccess_three_pages).vm_maps := by
  decide

/-! ## The Rocq examples, through `check_syscall` over the real table

The registration's half.  Every example
`theories/LinuxProcessSem/Checks/Cases/Mm/Mprotect.v` states on the
checker — twenty-two, each stated there through `check_syscall` at
`mkInput 226 [addr; len; prot; 0; 0; 0]` and closed by `check_eq` — is
restated here through the Lean `check_syscall`, over `checked_table`
itself, at the Rocq input.  Each takes its Rocq name with
`_over_the_real_table` after it, K6b's convention for the pins at which
the real table first answers a call (`Checks/Cases/Checks/Sys/Mm/Mmap.lean`
states brk's and munmap's so), and its evidence line is the twin's above.

What such a pin adds to its twin is the ARM's claim, which this file's
header set aside for the registration: that the lookup at 226 finds
`arm_mprotect` and not the dispatcher's own decline, and that `start`,
`len` and `prot` are read from `a0`, `a1` and `a2`.  A refusal at a
transposed register can coincide with the refusal at the right one.
`middle_splits_noaccess_and_zeros_exactly_over_the_real_table` is an
acceptance, and the three pins after it state what `check_mprotect`
answers at its registers with any two of them swapped: none of the three
is that acceptance.

POLARITY is the file's: a pin stated `= CheckReject` or `= CheckUnmodeled`
is positive to `tools/check_lean_pin_evidence.py` and cites the kernel
function whose answer the refused lie contradicts. -/

/-- An `mprotect` input: `a7 = 226`, with `start`, `len` and `prot` in
`a0`, `a1` and `a2`, the order
`SYSCALL_DEFINE3(mprotect, unsigned long, start, size_t, len, unsigned long, prot)`
(mm/mprotect.c:1008-1012, Linux v6.18.46) declares and
`SC_RISCV_REGS_TO_ARGS` (arch/riscv/include/asm/syscall_wrapper.h:21-24)
reads off `orig_a0`, `a1` and `a2`; no memory.  It is defined here rather
than imported from `Checks/Cases/Run.lean` (whose `mprotect_in` is the
same term) for two reasons.  That import would pull the run layer into a
checker pin file.  And `tools/check_lean_pin_evidence.py` reads a pin's
syscall number off a numeral in the statement or in a definition in the
SAME file. -/
def mprotect_in (addr len prot : word) : SyscallInput :=
  SyscallInput.mkInput 226 [addr, len, prot, 0, 0, 0] (fun _ => none) (fun _ => none)

set_option maxRecDepth 4096 in
/-- The lookup the dispatcher performs on an `mprotect_in`, computed once:
`in_sysno` is `226` whatever the three registers hold.
model: `lookup_ca` over `checked_table` at a closed number; the table's own
contents, not a kernel claim. -/
theorem lookup_mprotect_in (addr len prot : word) :
    lookup_ca checked_table (bv_unsigned (mprotect_in addr len prot).in_sysno)
      = some arm_mprotect :=
  lookup_ca_checked_table_mprotect

/-- Read a concrete `check_syscall` at an `mprotect_in` off.  The steps are
the lookup, the arm's `arm_unfold` and then `check_norm`.  `scoped`, for
the reason `check_norm` gives. -/
scoped macro "dispatch_norm" : tactic =>
  `(tactic| (unfold check_syscall check_syscall_in; rw [lookup_mprotect_in];
             simp only [arm_unfold]; check_norm))

/-! ### Gate 1 and the zero length -/

/-- `grows_conflict_is_einval` over the real table.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem mprotect_grows_conflict_is_einval_over_the_real_table :
    check_syscall (mprotect_in 65536 0 50331651) (mkEffect (errno_ret EINVAL) [] [])
        noaccess_three_pages = CheckOk noaccess_three_pages [] := by
  dispatch_norm

/-- `growsdown_alone_is_not_a_conflict` over the real table.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem mprotect_growsdown_alone_is_not_a_conflict_over_the_real_table :
    check_syscall (mprotect_in 65536 0 16777219) (mkEffect 0 [] [])
        noaccess_three_pages = CheckOk noaccess_three_pages [] := by
  dispatch_norm

/-- `growsup_alone_is_not_a_conflict` over the real table.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem mprotect_growsup_alone_is_not_a_conflict_over_the_real_table :
    check_syscall (mprotect_in 65536 0 33554435) (mkEffect 0 [] [])
        noaccess_three_pages = CheckOk noaccess_three_pages [] := by
  dispatch_norm

/-- `growsdown_alone_einval_is_rejected` over the real table.  The
qemu-user divergence recorded at Gate 1 above applies to this pin too.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem mprotect_growsdown_alone_einval_is_rejected_over_the_real_table :
    check_syscall (mprotect_in 65536 0 16777219) (mkEffect (errno_ret EINVAL) [] [])
        noaccess_three_pages = CheckReject := by
  dispatch_norm

/-- `growsup_alone_einval_is_rejected` over the real table (the same
qemu-user caveat applies).
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem mprotect_growsup_alone_einval_is_rejected_over_the_real_table :
    check_syscall (mprotect_in 65536 0 33554435) (mkEffect (errno_ret EINVAL) [] [])
        noaccess_three_pages = CheckReject := by
  dispatch_norm

/-- `unaligned_precedes_zero_length` over the real table.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem mprotect_unaligned_precedes_zero_length_over_the_real_table :
    check_syscall (mprotect_in 65537 0 3) (mkEffect (errno_ret EINVAL) [] [])
        noaccess_three_pages = CheckOk noaccess_three_pages [] := by
  dispatch_norm

/-- `read_only_zero_length_is_zero` over the real table.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem mprotect_read_only_zero_length_is_zero_over_the_real_table :
    check_syscall (mprotect_in 65536 0 1) (mkEffect 0 [] []) rw_two_pages =
      CheckOk rw_two_pages [] := by
  dispatch_norm

/-- `read_only_zero_length_errno_is_rejected` over the real table.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem mprotect_read_only_zero_length_errno_is_rejected_over_the_real_table :
    check_syscall (mprotect_in 65536 0 1) (mkEffect (errno_ret ENOMEM) [] []) rw_two_pages =
      CheckReject := by
  dispatch_norm

/-! ### The wrapping end -/

/-- `wrapping_end_is_enomem` over the real table.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem mprotect_wrapping_end_is_enomem_over_the_real_table :
    check_syscall (mprotect_in 9223372036854775808 9223372036854775808 3)
        (mkEffect (errno_ret ENOMEM) [] []) noaccess_three_pages =
      CheckOk noaccess_three_pages [] := by
  dispatch_norm

/-- `wrapping_end_success_is_rejected` over the real table.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem mprotect_wrapping_end_success_is_rejected_over_the_real_table :
    check_syscall (mprotect_in 9223372036854775808 9223372036854775808 3)
        (mkEffect 0 [] []) noaccess_three_pages = CheckReject := by
  dispatch_norm

/-- `wrapping_end_precedes_unsupported_prot` over the real table.
kernel: mm/mprotect.c:do_mprotect_pkey; include/linux/mman.h:arch_validate_prot@v6.18.46 -/
theorem mprotect_wrapping_end_precedes_unsupported_prot_over_the_real_table :
    check_syscall (mprotect_in 9223372036854775808 9223372036854775808 4)
        (mkEffect (errno_ret ENOMEM) [] []) noaccess_three_pages =
      CheckOk noaccess_three_pages [] := by
  dispatch_norm

/-! ### Exposure and the budget -/

/-- `middle_splits_noaccess_and_zeros_exactly` over the real table.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup; mm/vma.c:__split_vma@v6.18.46 -/
theorem mprotect_middle_splits_noaccess_and_zeros_exactly_over_the_real_table :
    check_syscall (mprotect_in 69632 4096 3) (mkEffect 0 [] [(69632, 4096)])
        noaccess_three_pages =
      CheckOk (fixture (VmMaps.mkVmMapsFull [] [(65536, 12288)] [(65536, 4096), (73728, 4096)]
                          0 0 16384 0 demo_sp)) [] := by
  dispatch_norm

/-- `middle_splits_noaccess_and_zeros_exactly_over_the_real_table`'s
registers with `len` and `prot` swapped: prot 4096 carries a bit outside
`PROT_READ | PROT_WRITE | PROT_EXEC | PROT_SEM`, which the generic
`arch_validate_prot` (include/linux/mman.h:106-109, Linux v6.18.46;
arch/riscv defines none of its own) refuses with `-EINVAL` at
mm/mprotect.c:887-888, and the checker declines that prot word.
kernel: mm/mprotect.c:do_mprotect_pkey; include/linux/mman.h:arch_validate_prot@v6.18.46 -/
theorem middle_splits_with_len_and_prot_swapped_is_unmodeled :
    check_mprotect 69632 3 4096 (mkEffect 0 [] [(69632, 4096)]) noaccess_three_pages =
      CheckUnmodeled := by
  check_norm

/-- The same registers with `start` and `len` swapped: the range is
`[4096, 73728)`, which `noaccess_three_pages` does not own; Linux answers
`-ENOMEM` there when the first mapping it finds starts above `start`
(mm/mprotect.c:917-918, Linux v6.18.46), and the checker declines.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem middle_splits_with_start_and_len_swapped_is_unmodeled :
    check_mprotect 4096 69632 3 (mkEffect 0 [] [(69632, 4096)]) noaccess_three_pages =
      CheckUnmodeled := by
  check_norm

/-- The same registers with `start` and `prot` swapped: `start` 3 is not
page-aligned, which is `-EINVAL` at mm/mprotect.c:879-880 (Linux
v6.18.46), so the offered 0 is refused.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem middle_splits_with_start_and_prot_swapped_is_rejected :
    check_mprotect 3 4096 69632 (mkEffect 0 [] [(69632, 4096)]) noaccess_three_pages =
      CheckReject := by
  check_norm

/-- `noaccess_errno_preserves_ledger` over the real table.
kernel: mm/mprotect.c:mprotect_fixup; mm/vma.c:vma_modify_flags@v6.18.46 -/
theorem mprotect_noaccess_errno_preserves_ledger_over_the_real_table :
    check_syscall (mprotect_in 69632 4096 3) (mkEffect (errno_ret ENOMEM) [] [])
        noaccess_three_pages = CheckOk noaccess_three_pages [] := by
  dispatch_norm

/-- `over_backed_budget_rejects_success` over the real table.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem mprotect_over_backed_budget_rejects_success_over_the_real_table :
    check_syscall (mprotect_in 65536 4096 3) (mkEffect 0 [] [(65536, 4096)])
        noaccess_zero_backing = CheckReject := by
  dispatch_norm

/-- `over_backed_budget_allows_enomem` over the real table.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem mprotect_over_backed_budget_allows_enomem_over_the_real_table :
    check_syscall (mprotect_in 65536 4096 3) (mkEffect (errno_ret ENOMEM) [] [])
        noaccess_zero_backing = CheckOk noaccess_zero_backing [] := by
  dispatch_norm

/-- `lazy_guard_preserves_backing_provenance` over the real table.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem mprotect_lazy_guard_preserves_backing_provenance_over_the_real_table :
    check_syscall (mprotect_in 69632 4096 3) (mkEffect 0 [] [(69632, 4096)])
        mprotect_lazy_guard =
      CheckOk (mprotect_model_next mprotect_lazy_guard 69632 4096) [] := by
  dispatch_norm

/-- `already_rw_errno_is_rejected` over the real table.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem mprotect_already_rw_errno_is_rejected_over_the_real_table :
    check_syscall (mprotect_in 65536 4096 3) (mkEffect (errno_ret ENOMEM) [] []) rw_two_pages =
      CheckReject := by
  dispatch_norm

/-! ### The declines -/

/-- `unmapped_forged_success_is_unmodeled` over the real table.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem mprotect_unmapped_forged_success_is_unmodeled_over_the_real_table :
    check_syscall (mprotect_in 131072 4096 3) (mkEffect 0 [] []) noaccess_three_pages =
      CheckUnmodeled := by
  dispatch_norm

/-- `noaccess_outside_vm_maps_is_unmodeled` over the real table.
kernel: mm/mprotect.c:do_mprotect_pkey@v6.18.46 -/
theorem mprotect_noaccess_outside_vm_maps_is_unmodeled_over_the_real_table :
    check_syscall (mprotect_in 65536 4096 3) (mkEffect 0 [] [(65536, 4096)]) noaccess_unowned =
      CheckUnmodeled := by
  dispatch_norm

/-- `read_only_downgrade_is_unmodeled` over the real table: Linux's own 0
for the downgrade is declined, not accepted.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup; include/uapi/asm-generic/mman-common.h:PROT_READ@v6.18.46 -/
theorem mprotect_read_only_downgrade_is_unmodeled_over_the_real_table :
    check_syscall (mprotect_in 65536 4096 1) (mkEffect 0 [] []) rw_two_pages =
      CheckUnmodeled := by
  dispatch_norm

/-- `read_only_downgrade_with_zeros_is_unmodeled` over the real table.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem mprotect_read_only_downgrade_with_zeros_is_unmodeled_over_the_real_table :
    check_syscall (mprotect_in 65536 4096 1) (mkEffect 0 [] [(65536, 4096)]) rw_two_pages =
      CheckUnmodeled := by
  dispatch_norm

/-- `read_only_over_noaccess_is_unmodeled` over the real table.
kernel: mm/mprotect.c:do_mprotect_pkey,mprotect_fixup@v6.18.46 -/
theorem mprotect_read_only_over_noaccess_is_unmodeled_over_the_real_table :
    check_syscall (mprotect_in 69632 4096 1) (mkEffect 0 [] [(69632, 4096)])
        noaccess_three_pages = CheckUnmodeled := by
  dispatch_norm

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Mm.Mprotect
