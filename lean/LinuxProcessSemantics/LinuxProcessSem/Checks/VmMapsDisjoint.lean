import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Run
import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap
import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect
import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise
import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mremap
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Uaccess

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.VmMapsDisjoint — what `vm_maps` really guarantees

Mirrors `theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`: the witness
states of its PART 1, the ownership invariant of its PART 2 with the
interval and counting lemmas that carry it, the setter frame facts and
the generic frame tactics of its PRESERVATION section, and the two facts
the dispatcher-level theorem rests on (`init_model_vm_wf`,
`lookup_ca_In`).  Not part of the trusted specification: like the Rocq
file this is QA on the definitions, and the invariant it proves is
consumed by proofs about the checker, never by a spec.

THE SPLIT TWIN.  The Rocq file ends with `checked_table_preserves_vm`, a
`first [...]` alternation with one alternative per dispatcher arm, and
every C ticket of the port adds one.  That alternation is the generated
module `Checks/VmMapsDisjoint/Arms.lean`, which `tools/gen_lean_checked.py`
renders from the arm files under `Checks/Arms/` and which imports this
file; the invariant never changes when an arm lands, so this file does
not either.  The split runs the way `Checks/Sys/Dispatch.lean` and the
generated `Checks/Sys/Table.lean` do — the part imports the whole — for the reason
that file gives, and the same reader's note applies: `arm_preserves_vm`
and everything an arm's frame lemma needs are here, and the theorem over
the table is in the part.  THE IMPORT DISCIPLINE follows from it: this
file imports `Checks/Sys/Dispatch.lean` and never `Checks/Sys/Table.lean`,
because `Table.lean` imports every checker, and a checker's file has to
import THIS one — its `check_<name>_frame` lemma is closed by the
`vm_frame` tactics below — without a cycle.  The arms themselves live in
the arm files, which import the checkers, so the arm-level facts
`arm_<name>_preserves_vm` cannot be stated in a checker's file either;
each is stated in its arm's file under `Checks/Arms/`, beside the
`CheckedArm` it is about, and the generated alternation consumes it.

WHAT IS NOT HERE, AND WHY.  Lemmas are not registered `unported:` (the
header takes definitions only), so the Rocq lemmas this file does not
carry are accounted for by kind, each with the file it lands in; the
names are the Rocq file's to list, and the list below is read against it
at the baseline named further down:
- the per-arm `check_*_frame` and `check_*_preserves` lemmas wait on the
  arm's checker: each arrives with its C ticket, in the checker's own
  file, and its arm-level fact is written in the arm's file under
  `Checks/Arms/`, from which the alternative is rendered.  The three brk lemmas beside them in Rocq's PART 2 —
  `brk_r_ok_grow`, `brk_grant_wf`, `brk_model_next_wf` — are spec-side
  and wait on nothing: every name they state is in `Sys/Mm/Mmap.lean`,
  and the one `State.v` fact their proofs lean on, `alloc_top_page_lt`,
  is a line of `omega` over `State/Vm.lean`'s `alloc_top_room`.  They are
  the one part of PART 2 this file leaves out, to land with
  C-Mm-Mmap-brk-munmap beside `check_brk_preserves`, their only consumer;
- PART 1's step examples are stated through `check_syscall` on the brk,
  munmap and mmap checkers and are ticket K9's, in a `Witness` part
  beside `Arms`.  The three PART 1 examples that are closed computations
  over the ledgers alone — `wit_overlap_holds`, `wit_duplicate_base`,
  `wit_duplicate_base_is_unaligned` — are here, beside the states they
  read.  Rocq's `check_eq`, the tactic the step examples close by, has
  no twin: `decide +kernel` is that comparison;
- `check_readv_gap_frame` and `check_open_result_frame`, the frame facts
  about the wrappers of `Checks/Sys/Fs/ReadWrite.v` and
  `Checks/Sys/Fs/Open.v`, wait on those checker twins and register at
  `vm_done` below, where `check_efault_or_frame` — whose wrapper
  `Checks/Sys/Uaccess.lean` carries — is the first rule and the worked
  example;
- `check_syscall_preserves_vm_wf`, `syscall_spec_preserves_vm_wf` and
  `base_unique_after_syscall` rest on `check_syscall`, the
  `Checks/ExecutableSpecs.v` twin, and so live in
  `Checks/Invariants.lean` — as `check_syscall_preserves`,
  `syscall_spec_preserves` and `base_unique_after_syscall`, the first two
  generalised over every registered invariant — where the generated
  `Checks/VmMapsDisjoint/Arms.lean` states
  the dispatcher-level fact over the lookup that `check_syscall` is a
  `match` on;
- `vmm_vmmaps` and `vmm_backing` are `State.lean`'s
  `m_vmmaps_with_vmmaps` and `m_vmmaps_with_vm_backing` and are not
  repeated.  `region_free_In` and `region_free_intro` are `State.v`
  lemmas `State/Vm.lean` does not carry; their twins are here, under
  their Rocq names, because `State/` is a frozen base part and an edit to
  it lands every open port PR on a rebuild (`docs/lean-port/BRIEF.md`,
  "Frozen files"), which two four-line lemmas do not buy.  The
  `lean: base:` PR that adds them to `State/Vm.lean` deletes these two in
  the same change: a file that opens both namespaces would otherwise see
  an ambiguous name.

THE HEADER'S BASELINE is the day-branch commit the Rocq file was read
at, a71fd38a (the squash of the 2026-09-11 work, #794), not the port's
common baseline f44244ad.  The two differ only in per-arm frame proofs
that are C tickets' lemmas and not here: `check_read_frame`,
`check_pread64_frame`, `check_openat_frame` and `check_unlinkat_frame`
grew the `/dev/urandom` arms of #712 and the `/tmp` arms of #827, and
`check_fstat_chrdev_frame` and `check_fstat_urandom_frame` were added
beside `check_fstat_devnull_frame`.  Every definition and every lemma of
PART 1 and PART 2 reads the same at both commits; `wit_s0`'s
`mkProcInput` is the thirteen-place form at both, which the Lean
`ProcInput.mkProcInput` keeps as a wrapper over the wider record.

SPELLINGS.  Rocq's `Forall P maps` is `∀ e ∈ maps, P e` (its
`Forall_forall` reading); `Z.leb`/`Z.ltb` on `bv_unsigned` are the
decidable `≤`/`<` on `Int`; `nat` is `Nat`, `lia` is `omega`, and
`Local Open Scope Z_scope` has no counterpart because `Int` needs no
scope.  Rocq's `dif`/`difn` (destruct the `if` a hypothesis sits on) are
`split at h`, which `vm_step` runs.  The `2 ^ 64` bounds are written as
the literal `18446744073709551616` so that `omega` reads them.  Rocq's
`vm_compute; reflexivity` on the PART 2b examples is `decide +kernel`:
the same closed computation, evaluated by the kernel rather than the
elaborator, whose `whnf` runs out of recursion depth on `owned_bytes`
over 4196 bytes; it adds no axiom (`Checks/Axioms.lean`'s walk lists
none for these).  Three helpers have no Rocq twin and say so in place:
`owns_b_iff`, the reading of `owns_b` the interval lemmas share;
`vm_wf_of_frame`, Rocq's `erewrite check_X_frame; exact Hwf` step as a
lemma; and `arm_preserves_of_frame`, which turns a frame lemma into the
arm-level fact an arm file under `Checks/Arms/` names.

THE KERNEL FACT the file turns on is argued on the Rocq header and not
repeated.  Its anchor, read at the pinned commit: `SYSCALL_DEFINE1(brk)`
(mm/mmap.c:153-158, Linux v6.18.46, commit 1f99e9ab748f) takes the exit
`if (oldbrk == newbrk) { mm->brk = brk; goto success; }` on the
page-rounded breaks before any VMA is consulted, so a brk move within one
page reaches `mm->brk = brk` with no address-space test.  One exit sits
above it that does not return a break at all: the killable acquisition
of the mmap lock (mm/mmap.c:125-126, Linux v6.18.46) answers -EINTR when
the task has a fatal signal pending, a path the model, which has no
signals, never takes; the Rocq header's "each returns `origbrk`" for the
gates above the exit is short by that case, and the two gates that do
`goto out` return `origbrk` as it says.  Byte-level
disjointness of `vm_maps` is therefore not an invariant of reachable
states; page-aligned ownership is what survives, and why that is enough
for `munmap`'s `map_has`/`map_remove` pair is the Rocq header's argument
too. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/-! ## PART 1 — the witness process

The start state the eight-step counterexample runs from, and the ledgers
it passes through.  The steps themselves need the brk and munmap checkers
and are ticket K9's; what is here is every state they name, so that the
PART 2b examples below, which read two of those ledgers, can be stated
now, and the three PART 1 examples that read the ledgers alone.  The
shape — the image at `[4096, 8192)`, the break base at `0x10000` — is the
one `Checks/Examples.v`'s brk section uses; the Rocq
definitions carry the argument for each choice. -/

/-- Rocq: `VmMapsDisjoint.wit_reserved`. -/
def wit_reserved : List (word × word) := [(4096, 4096)]

/-- Rocq: `VmMapsDisjoint.wit_brk_base`. -/
def wit_brk_base : word := 65536

/-- Rocq: `VmMapsDisjoint.wit_limit`. -/
def wit_limit : Int := 0x40000000

/-- `mm->mmap_base`, pinned to an admissible value so that the start state
is one `execve` can hand out; nothing in either tier reads it (the Rocq
definition says why that is the only reason).  Rocq:
`VmMapsDisjoint.wit_mmap_base`. -/
def wit_mmap_base : word := Z_to_bv 64 mmap_base_min

/-- The witness ledger: `State.mkVmMaps` with `vm_mmap_base` at the
admissible value instead of zero.  Rocq: `VmMapsDisjoint.wit_vm`. -/
def wit_vm (maps : List (word × word)) (start_brk brk : word) (limit : Int) : VmMaps :=
  VmMaps.mkVmMapsFull wit_reserved maps [] start_brk brk limit wit_mmap_base
    (Z_to_bv 64 sp_window_lo)

/-- Rocq: `VmMapsDisjoint.wit_s0`. -/
def wit_s0 : Model :=
  init_model wit_reserved wit_brk_base wit_mmap_base (Z_to_bv 64 sp_window_lo) wit_limit
    (ProcInput.mkProcInput [] [] [] IEof (Z_to_bv 64 1000) (Z_to_bv 64 1002) []
      net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc false .Sv48)

/-- `Run.valid_mmap_base`'s three conjuncts on the witness, spelled out for
the reason `wit_brk_base_admissible` gives.  Rocq:
`VmMapsDisjoint.wit_mmap_base_admissible`. -/
theorem wit_mmap_base_admissible :
    mmap_base_min ≤ bv_unsigned wit_mmap_base
    ∧ bv_unsigned wit_mmap_base ≤ mmap_base_max
    ∧ bv_unsigned wit_mmap_base % page_size = 0 := by
  decide

/-- The start state is one `execve` really can hand a process: exactly
`Run.valid_brk`'s three conjuncts, spelled on the reservation list so that
the statement mentions no `Segment`.  Rocq:
`VmMapsDisjoint.wit_brk_base_admissible`. -/
theorem wit_brk_base_admissible :
    reserved_top wit_reserved ≤ bv_unsigned wit_brk_base
    ∧ bv_unsigned wit_brk_base ≤ reserved_top wit_reserved + brk_aslr_max
    ∧ bv_unsigned wit_brk_base % page_size = 0 := by
  decide

/-- …and that really is `Run.valid_brk` for any image whose LOAD
reservations are `wit_reserved`.  Rocq: `VmMapsDisjoint.wit_valid_brk`. -/
theorem wit_valid_brk (segs : List Segment) (hs : segments_reserved segs = wit_reserved) :
    valid_brk segs wit_brk_base := by
  unfold valid_brk
  rw [hs]
  exact wit_brk_base_admissible

/-- A brk call's input.  Rocq: `VmMapsDisjoint.brk_in`. -/
def brk_in (req : word) : SyscallInput :=
  SyscallInput.mkInput 214 [req, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- After step 1, brk(0x11000): an ordinary page-crossing grow.  Rocq:
`VmMapsDisjoint.wit_s1`. -/
def wit_s1 : Model := with_vmmaps (wit_vm [(65536, 4096)] 65536 69632 wit_limit) wit_s0

/-- After step 2, brk(0x11064): the gate checks the rounded range, the
ledger records the logical one, and the break is mid-page.  Rocq:
`VmMapsDisjoint.wit_s2`. -/
def wit_s2 : Model :=
  with_vmmaps (wit_vm [(69632, 100), (65536, 4096)] 65536 69732 wit_limit) wit_s0

/-- After step 3, munmap(0x10000, 4096): the first heap grant dropped, the
break untouched.  Rocq: `VmMapsDisjoint.wit_s3`. -/
def wit_s3 : Model := with_vmmaps (wit_vm [(69632, 100)] 65536 69732 wit_limit) wit_s0

/-- After step 4, brk(0x107d0): a shrink into the hole, the ledger empty,
the break mid-page with nothing below it owned.  Rocq:
`VmMapsDisjoint.wit_s4`. -/
def wit_s4 : Model := with_vmmaps (wit_vm [] 65536 67536 wit_limit) wit_s0

/-- After step 5, an mmap of one page at the hint 0x10000: the break now
points inside a fresh mapping.  Rocq: `VmMapsDisjoint.wit_s5`. -/
def wit_s5 : Model := with_vmmaps (wit_vm [(65536, 4096)] 65536 67536 wit_limit) wit_s0

/-- THE OVERLAP: brk(0x10834) grows by 100 bytes within one page, so no
address-space test runs and the grant lands inside the step-5 mapping.
Rocq: `VmMapsDisjoint.wit_overlap`. -/
def wit_overlap : Model :=
  with_vmmaps (wit_vm [(67536, 100), (65536, 4096)] 65536 67636 wit_limit) wit_s0

/-- …and the entries really do overlap.  The grant's OWN entry is dropped
before the query, because every nonempty interval overlaps itself: what
is checked is that the step-5 mapping alone already covers the range the
brk grant just took.  Rocq: `VmMapsDisjoint.wit_overlap_holds`. -/
theorem wit_overlap_holds :
    region_free (map_remove (m_vmmaps wit_overlap).vm_maps 67536) 67536 100 = false := by
  decide

/-- After step 6, brk(0x107c6) run FROM `wit_s5` (break 67536), not from
`wit_overlap`: a ten-byte shrink that splits the step-5 LEDGER ENTRY, its
right remnant based at the old break.  The split is the model's
(`brk_maps_next` subtracts `[67526, 67536)`); Linux rounds both breaks to
the same page, takes the exit the header names and leaves the step-5 VMA
whole.  Rocq: `VmMapsDisjoint.wit_s6`. -/
def wit_s6 : Model :=
  with_vmmaps (wit_vm [(65536, 1990), (67536, 2096)] 65536 67526 wit_limit) wit_s0

/-- After step 7, brk(0x107d0): the ten bytes grown back, same page.  Rocq:
`VmMapsDisjoint.wit_s7`. -/
def wit_s7 : Model :=
  with_vmmaps (wit_vm [(67526, 10), (65536, 1990), (67536, 2096)] 65536 67536 wit_limit) wit_s0

/-- After step 8, brk(0x10834): two entries based at 67536, of different
sizes.  Rocq: `VmMapsDisjoint.wit_s8`. -/
def wit_s8 : Model :=
  with_vmmaps
    (wit_vm [(67536, 100), (67526, 10), (65536, 1990), (67536, 2096)] 65536 67636 wit_limit)
    wit_s0

/-- THE VERDICT.  Two DIFFERENT sizes are both "exactly the mapping at
67536", so `map_has` does not determine the entry `map_remove` would
drop.  Byte-level base uniqueness is therefore not an invariant of
reachable states, and no proof of it can exist as the model stands.
Rocq: `VmMapsDisjoint.wit_duplicate_base`. -/
theorem wit_duplicate_base :
    map_has (m_vmmaps wit_s8).vm_maps 67536 100 = true
    ∧ map_has (m_vmmaps wit_s8).vm_maps 67536 2096 = true := by
  decide

/-- The duplicated base is NOT page aligned, and PART 2 shows that is no
accident: a page-aligned break makes `brk_grow_ok` compute `lo < hi` and
the `region_free` test does run.  Rocq:
`VmMapsDisjoint.wit_duplicate_base_is_unaligned`. -/
theorem wit_duplicate_base_is_unaligned : (67536 : Int) % page_size ≠ 0 := by decide

/-! ## PART 2 — the invariant that IS maintained

`owners maps p` counts the live entries that own byte `p`.  The invariant
is that no PAGE-ALIGNED byte has two owners; PART 1 shows the same
statement is false for an arbitrary byte. -/

/-- Does the ledger entry `e` own the byte at address `p`?  Rocq:
`VmMapsDisjoint.owns_b`. -/
def owns_b (e : word × word) (p : Int) : Bool :=
  bv_unsigned e.1 ≤ p && p < bv_unsigned e.1 + bv_unsigned e.2

/-- Rocq: `VmMapsDisjoint.owners`. -/
def owners (maps : List (word × word)) (p : Int) : Nat :=
  match maps with
  | [] => 0
  | e :: r => (if owns_b e p then 1 else 0) + owners r p

/-- THE INVARIANT.  Every page-aligned address is owned by at most one
live mapping.  Rocq: `VmMapsDisjoint.page_owner_unique`. -/
def page_owner_unique (maps : List (word × word)) : Prop :=
  ∀ p : Int, p % page_size = 0 → owners maps p ≤ 1

/-- The companion well-formedness the ledger's writers also maintain: no
entry is empty.  An empty entry would own nothing, so it would slip past
`region_free` and past `page_owner_unique` while still answering
`map_has`.  Rocq: `VmMapsDisjoint.sizes_nonzero`. -/
def sizes_nonzero (maps : List (word × word)) : Prop :=
  ∀ e ∈ maps, bv_unsigned e.2 ≠ 0

/-- Rocq: `VmMapsDisjoint.maps_wf`. -/
def maps_wf (maps : List (word × word)) : Prop := sizes_nonzero maps ∧ page_owner_unique maps

/-- Rocq: `VmMapsDisjoint.vm_wf`. -/
def vm_wf (h : VmMaps) : Prop := maps_wf h.vm_maps

/-! ### PART 2b — what the overlap does to the byte total

`State.live_bytes` was once documented as the distinct-byte count of the
granted-and-not-freed memory, on the strength of the disjointness PART 1
refutes.  The definition below is the distinct-byte measure computed the
slow honest way over a bounded window, and the examples pin the failure
so that neither sentence can come back while the overlap is reachable.
Recorded in bugs/live-bytes-double-counts-overlapping-entries.md. -/

/-- How many of the `n` bytes from `lo` are owned by at least one live
entry.  Rocq: `VmMapsDisjoint.owned_bytes`. -/
def owned_bytes (maps : List (word × word)) (lo : Int) (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => (if 0 < owners maps lo then 1 else 0) + owned_bytes maps (lo + 1) k

/-- THE DOUBLE COUNT: the brk grant lies wholly inside the step-5 mapping,
so 4096 distinct bytes are granted and `live_bytes` reports 4196 — exactly
the contained entry's size is charged twice.  Rocq:
`VmMapsDisjoint.live_bytes_over_counts_the_overlap`. -/
theorem live_bytes_over_counts_the_overlap :
    live_bytes (m_vmmaps wit_overlap).vm_maps = 4196
    ∧ owned_bytes (m_vmmaps wit_overlap).vm_maps 65536 4196 = 4096 := by
  decide +kernel

/-- THE CONTROL: the same two sizes placed end to end.  Rocq:
`VmMapsDisjoint.disjoint_ledger`. -/
def disjoint_ledger : List (word × word) :=
  [(Z_to_bv 64 69632, Z_to_bv 64 100), (Z_to_bv 64 65536, Z_to_bv 64 4096)]

/-- …on which `live_bytes` IS the distinct-byte count; without this pair the
example above would pass against an `owned_bytes` that always answered
4096.  Rocq: `VmMapsDisjoint.live_bytes_is_exact_when_the_entries_are_disjoint`. -/
theorem live_bytes_is_exact_when_the_entries_are_disjoint :
    live_bytes disjoint_ledger = 4196 ∧ owned_bytes disjoint_ledger 65536 4196 = 4196 := by
  decide +kernel

/-- SO PLACEMENT PLAYS A PART: the two ledgers hold the same multiset of
sizes, `live_bytes` cannot tell them apart, and the number of bytes really
granted differs by 100.  Rocq:
`VmMapsDisjoint.placement_changes_the_granted_byte_count`. -/
theorem placement_changes_the_granted_byte_count :
    live_bytes (m_vmmaps wit_overlap).vm_maps = live_bytes disjoint_ledger
    ∧ owned_bytes (m_vmmaps wit_overlap).vm_maps 65536 4196
      ≠ owned_bytes disjoint_ledger 65536 4196 := by
  decide +kernel

/-- THE DIRECTION: the sum is never below the distinct count, so a budget
gate built on it fires no later than the truth.  Rocq:
`VmMapsDisjoint.live_bytes_over_counts_never_under`. -/
theorem live_bytes_over_counts_never_under :
    ((owned_bytes (m_vmmaps wit_overlap).vm_maps 65536 4196 : Nat) : Int)
      ≤ live_bytes (m_vmmaps wit_overlap).vm_maps := by
  decide +kernel

/-- The duplicate-base state double counts too, by the smaller of the two
entries sharing base 67536.  Rocq:
`VmMapsDisjoint.live_bytes_over_counts_the_duplicate_base`. -/
theorem live_bytes_over_counts_the_duplicate_base :
    live_bytes (m_vmmaps wit_s8).vm_maps = 4196
    ∧ owned_bytes (m_vmmaps wit_s8).vm_maps 65536 4196 = 4096 := by
  decide +kernel

/-! ### Arithmetic and counting lemmas -/

/-- `BvBase.bv_unsigned_Z_to_bv_small` with the bound as a literal, so that
`omega` reads it; the round trip is proved once, there.  Rocq:
`VmMapsDisjoint.u64`. -/
theorem u64 (z : Int) (h0 : 0 ≤ z) (h1 : z < 18446744073709551616) :
    bv_unsigned (Z_to_bv 64 z) = z :=
  bv_unsigned_Z_to_bv_small z h0 (by omega)

/-- `Prelude.word_unsigned_range` with the bound as a literal, so that
`omega` reads it.  Rocq: `VmMapsDisjoint.word_range`. -/
theorem word_range (w : word) : 0 ≤ bv_unsigned w ∧ bv_unsigned w < 18446744073709551616 := by
  have h := word_unsigned_range w
  unfold two_pow_64 at h
  omega

/-- Rocq: `VmMapsDisjoint.page_round_up_Z_ge`.  The bound is kept for the callers'
shape and is redundant on both sides: for the positive divisor `page_size`,
Rocq's floor division and Lean's Euclidean `/` agree, and the statement
holds for every `z`, so `omega` does not read it. -/
theorem page_round_up_Z_ge (z : Int) (_hz : 0 ≤ z) : z ≤ page_round_up_Z z := by
  unfold page_round_up_Z page_size
  omega

/-- The step PART 1 turns on: a PAGE-ALIGNED address at or above `z` is at
or above `z` rounded up.  This is why the rounded gate covers every
page-aligned byte of the range it fails to cover byte for byte.  Rocq:
`VmMapsDisjoint.page_round_up_Z_le_aligned`. -/
theorem page_round_up_Z_le_aligned (z p : Int) (hp : p % page_size = 0) (hzp : z ≤ p) :
    page_round_up_Z z ≤ p := by
  simp only [page_round_up_Z, page_size] at hp ⊢
  omega

/-- The reading of `owns_b` every lemma below goes through. -/
theorem owns_b_iff (a n : word) (p : Int) :
    owns_b (a, n) p = true ↔ bv_unsigned a ≤ p ∧ p < bv_unsigned a + bv_unsigned n := by
  simp only [owns_b, Bool.and_eq_true, decide_eq_true_eq]

/-- Rocq: `VmMapsDisjoint.owns_true`. -/
theorem owns_true (a n : word) (p : Int) (h : owns_b (a, n) p = true) :
    bv_unsigned a ≤ p ∧ p < bv_unsigned a + bv_unsigned n :=
  (owns_b_iff a n p).mp h

/-- Rocq: `VmMapsDisjoint.owns_false`. -/
theorem owns_false (a n : word) (p : Int) (h : owns_b (a, n) p = false) :
    p < bv_unsigned a ∨ bv_unsigned a + bv_unsigned n ≤ p := by
  have hiff := owns_b_iff a n p
  rw [h] at hiff
  simp only [Bool.false_eq_true, false_iff] at hiff
  omega

/-- Rocq: `VmMapsDisjoint.owns_intro`. -/
theorem owns_intro (a n : word) (p : Int) (h1 : bv_unsigned a ≤ p)
    (h2 : p < bv_unsigned a + bv_unsigned n) : owns_b (a, n) p = true :=
  (owns_b_iff a n p).mpr ⟨h1, h2⟩

/-- Two entries that own the same byte overlap — the bridge from `owners`
to `region_free`.  Rocq: `VmMapsDisjoint.owns_overlap`. -/
theorem owns_overlap (a n b s : word) (p : Int) (h1 : owns_b (a, n) p = true)
    (h2 : owns_b (b, s) p = true) : iv_overlap a n b s = true := by
  have ha := owns_true a n p h1
  have hb := owns_true b s p h2
  simp only [iv_overlap, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- `State.v`'s `region_free_In`, here because `State.lean` is frozen. -/
theorem region_free_In (maps : List (word × word)) (lo n a sz : word)
    (hfree : region_free maps lo n = true) (hin : (a, sz) ∈ maps) :
    iv_overlap lo n a sz = false := by
  induction maps with
  | nil => cases hin
  | cons e r ih =>
    obtain ⟨b, s⟩ := e
    simp only [region_free, Bool.and_eq_true, Bool.not_eq_true'] at hfree
    rcases List.mem_cons.mp hin with heq | hin'
    · cases heq
      exact hfree.1
    · exact ih hfree.2 hin'

/-- `State.v`'s `region_free_intro`, here because `State.lean` is frozen. -/
theorem region_free_intro (maps : List (word × word)) (lo n : word)
    (h : ∀ a sz, (a, sz) ∈ maps → iv_overlap lo n a sz = false) :
    region_free maps lo n = true := by
  induction maps with
  | nil => rfl
  | cons e r ih =>
    obtain ⟨b, s⟩ := e
    simp only [region_free, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨h b s List.mem_cons_self, ih (fun a sz hin => h a sz (List.mem_cons_of_mem _ hin))⟩

/-- Rocq: `VmMapsDisjoint.region_free_no_owner`. -/
theorem region_free_no_owner (maps : List (word × word)) (a n : word) (p : Int)
    (hfree : region_free maps a n = true) (hown : owns_b (a, n) p = true) :
    owners maps p = 0 := by
  induction maps with
  | nil => rfl
  | cons e r ih =>
    obtain ⟨b, s⟩ := e
    simp only [region_free, Bool.and_eq_true, Bool.not_eq_true'] at hfree
    simp only [owners]
    cases ho : owns_b (b, s) p with
    | true =>
      rw [owns_overlap a n b s p hown ho] at hfree
      simp only [Bool.true_eq_false, false_and] at hfree
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      exact ih hfree.2

/-- Rocq: `VmMapsDisjoint.region_free_app_r`. -/
theorem region_free_app_r (l1 l2 : List (word × word)) (lo n : word)
    (h : region_free (l1 ++ l2) lo n = true) : region_free l2 lo n = true := by
  induction l1 with
  | nil => exact h
  | cons e r ih =>
    obtain ⟨b, s⟩ := e
    simp only [List.cons_append, region_free, Bool.and_eq_true] at h
    exact ih h.2

/-- Rocq: `VmMapsDisjoint.owners_app`. -/
theorem owners_app (l1 l2 : List (word × word)) (p : Int) :
    owners (l1 ++ l2) p = owners l1 p + owners l2 p := by
  induction l1 with
  | nil => simp only [List.nil_append, owners, Nat.zero_add]
  | cons e r ih => simp only [List.cons_append, owners, ih, Nat.add_assoc]

/-- Rocq: `VmMapsDisjoint.owners_filter_split`. -/
theorem owners_filter_split (f : word × word → Bool) (maps : List (word × word)) (p : Int) :
    owners (maps.filter f) p + owners (maps.filter (fun e => !f e)) p = owners maps p := by
  induction maps with
  | nil => rfl
  | cons e r ih =>
    cases hf : f e <;>
      simp only [List.filter_cons, hf, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        ↓reduceIte, owners] <;>
      cases owns_b e p <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;>
      omega

/-- Rocq: `VmMapsDisjoint.owners_filter_le`. -/
theorem owners_filter_le (f : word × word → Bool) (maps : List (word × word)) (p : Int) :
    owners (maps.filter f) p ≤ owners maps p := by
  have := owners_filter_split f maps p
  omega

/-- Rocq: `VmMapsDisjoint.sizes_nonzero_filter`. -/
theorem sizes_nonzero_filter (f : word × word → Bool) (maps : List (word × word))
    (h : sizes_nonzero maps) : sizes_nonzero (maps.filter f) :=
  fun e he => h e (List.mem_filter.mp he).1

/-- Rocq: `VmMapsDisjoint.owners_ge1`. -/
theorem owners_ge1 (maps : List (word × word)) (e : word × word) (p : Int) (hin : e ∈ maps)
    (ho : owns_b e p = true) : 1 ≤ owners maps p := by
  induction maps with
  | nil => cases hin
  | cons e' r ih =>
    simp only [owners]
    rcases List.mem_cons.mp hin with heq | hin'
    · subst heq
      simp only [ho, ↓reduceIte]
      omega
    · have := ih hin'
      cases owns_b e' p <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- Rocq: `VmMapsDisjoint.owners_all_own`. -/
theorem owners_all_own (l : List (word × word)) (p : Int) (h : ∀ e ∈ l, owns_b e p = true) :
    owners l p = l.length := by
  induction l with
  | nil => rfl
  | cons e r ih =>
    simp only [owners, List.length_cons, h e List.mem_cons_self, ↓reduceIte]
    rw [ih (fun e' he' => h e' (List.mem_cons_of_mem e he'))]
    omega

/-- Rocq: `VmMapsDisjoint.owners_map_remove_lt`. -/
theorem owners_map_remove_lt (maps : List (word × word)) (b s : word) (p : Int)
    (hin : (b, s) ∈ maps) (ho : owns_b (b, s) p = true) :
    owners (map_remove maps b) p + 1 ≤ owners maps p := by
  induction maps with
  | nil => cases hin
  | cons e r ih =>
    simp only [map_remove] at ih ⊢
    rcases List.mem_cons.mp hin with heq | hin'
    · subst heq
      simp only [List.filter_cons, bv_eqb_refl, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        owners, ho]
      have := owners_filter_le (fun q => !bv_eqb q.1 b) r p
      omega
    · have hih := ih hin'
      cases hb : bv_eqb e.1 b <;>
        simp only [List.filter_cons, hb, Bool.not_true, Bool.not_false, Bool.false_eq_true,
          ↓reduceIte, owners] <;>
        cases owns_b e p <;>
        simp only [Bool.false_eq_true, ↓reduceIte] <;>
        omega

/-! ### The two ways the ledger grows: a fresh `region_free` grant, and a
`maps_subtract` that can only shrink coverage -/

/-- A grant checked by `region_free` against the very list it is prepended
to keeps the invariant, for EVERY address, page aligned or not.  Rocq:
`VmMapsDisjoint.maps_wf_cons_free`. -/
theorem maps_wf_cons_free (maps : List (word × word)) (a n : word) (hwf : maps_wf maps)
    (hn : bv_unsigned n ≠ 0) (hfree : region_free maps a n = true) :
    maps_wf ((a, n) :: maps) := by
  obtain ⟨hnz, hun⟩ := hwf
  refine ⟨?_, ?_⟩
  · intro e he
    rcases List.mem_cons.mp he with heq | he'
    · subst heq
      exact hn
    · exact hnz e he'
  · intro p hp
    simp only [owners]
    cases ho : owns_b (a, n) p with
    | true =>
      rw [region_free_no_owner maps a n p hfree ho]
      simp only [↓reduceIte, Nat.add_zero, Nat.le_refl]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      exact hun p hp

/-- One entry cut by `[lo, hi)`: the remnants own only bytes the entry
owned, at most one of them owns any byte, and both are nonempty.  Rocq:
`VmMapsDisjoint.iv_subtract_ok`. -/
theorem iv_subtract_ok (a sz : word) (lo hi p : Int) (hlo : 0 ≤ lo) (hlohi : lo ≤ hi)
    (hhi : hi < 18446744073709551616) (hsz : bv_unsigned sz ≠ 0) :
    owners (iv_subtract a sz lo hi) p ≤ (if owns_b (a, sz) p then 1 else 0)
    ∧ sizes_nonzero (iv_subtract a sz lo hi) := by
  have ha := word_range a
  have hs := word_range sz
  have iffS := owns_b_iff a sz p
  unfold iv_subtract
  by_cases h1 : bv_unsigned a < lo <;> by_cases h2 : hi < bv_unsigned a + bv_unsigned sz <;>
    simp only [h1, h2, ↓reduceIte, List.nil_append, List.append_nil, List.cons_append]
  · -- both remnants
    have eL : bv_unsigned (Z_to_bv 64 (min (bv_unsigned sz) (lo - bv_unsigned a)))
        = min (bv_unsigned sz) (lo - bv_unsigned a) := u64 _ (by omega) (by omega)
    have eR1 : bv_unsigned (Z_to_bv 64 (max (bv_unsigned a) hi)) = max (bv_unsigned a) hi :=
      u64 _ (by omega) (by omega)
    have eR2 : bv_unsigned (Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - max (bv_unsigned a) hi))
        = bv_unsigned a + bv_unsigned sz - max (bv_unsigned a) hi := u64 _ (by omega) (by omega)
    have iffL := owns_b_iff a (Z_to_bv 64 (min (bv_unsigned sz) (lo - bv_unsigned a))) p
    have iffR := owns_b_iff (Z_to_bv 64 (max (bv_unsigned a) hi))
      (Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - max (bv_unsigned a) hi)) p
    rw [eL] at iffL
    rw [eR1, eR2] at iffR
    refine ⟨?_, ?_⟩
    · simp only [owners]
      cases hL : owns_b (a, Z_to_bv 64 (min (bv_unsigned sz) (lo - bv_unsigned a))) p <;>
      cases hR : owns_b (Z_to_bv 64 (max (bv_unsigned a) hi),
        Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - max (bv_unsigned a) hi)) p <;>
      cases hS : owns_b (a, sz) p <;>
      simp only [hL, hR, hS, Bool.false_eq_true, ↓reduceIte, false_iff, true_iff, Nat.add_zero,
        Nat.zero_add] at iffL iffR iffS ⊢ <;>
      omega
    · intro e he
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with heq | heq <;> subst heq
      · simp only [eL]
        omega
      · simp only [eR2]
        omega
  · -- the left remnant alone
    have eL : bv_unsigned (Z_to_bv 64 (min (bv_unsigned sz) (lo - bv_unsigned a)))
        = min (bv_unsigned sz) (lo - bv_unsigned a) := u64 _ (by omega) (by omega)
    have iffL := owns_b_iff a (Z_to_bv 64 (min (bv_unsigned sz) (lo - bv_unsigned a))) p
    rw [eL] at iffL
    refine ⟨?_, ?_⟩
    · simp only [owners]
      cases hL : owns_b (a, Z_to_bv 64 (min (bv_unsigned sz) (lo - bv_unsigned a))) p <;>
      cases hS : owns_b (a, sz) p <;>
      simp only [hL, hS, Bool.false_eq_true, ↓reduceIte, false_iff, true_iff, Nat.add_zero]
        at iffL iffS ⊢ <;>
      omega
    · intro e he
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
      subst he
      simp only [eL]
      omega
  · -- the right remnant alone
    have eR1 : bv_unsigned (Z_to_bv 64 (max (bv_unsigned a) hi)) = max (bv_unsigned a) hi :=
      u64 _ (by omega) (by omega)
    have eR2 : bv_unsigned (Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - max (bv_unsigned a) hi))
        = bv_unsigned a + bv_unsigned sz - max (bv_unsigned a) hi := u64 _ (by omega) (by omega)
    have iffR := owns_b_iff (Z_to_bv 64 (max (bv_unsigned a) hi))
      (Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - max (bv_unsigned a) hi)) p
    rw [eR1, eR2] at iffR
    refine ⟨?_, ?_⟩
    · simp only [owners]
      cases hR : owns_b (Z_to_bv 64 (max (bv_unsigned a) hi),
        Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - max (bv_unsigned a) hi)) p <;>
      cases hS : owns_b (a, sz) p <;>
      simp only [hR, hS, Bool.false_eq_true, ↓reduceIte, false_iff, true_iff, Nat.add_zero]
        at iffR iffS ⊢ <;>
      omega
    · intro e he
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
      subst he
      simp only [eR2]
      omega
  · -- the entry lies inside the cut: nothing survives
    exact ⟨Nat.zero_le _, fun e he => nomatch he⟩

/-- Rocq: `VmMapsDisjoint.maps_subtract_ok`. -/
theorem maps_subtract_ok (maps : List (word × word)) (lo hi : Int) (hlo : 0 ≤ lo)
    (hlohi : lo ≤ hi) (hhi : hi < 18446744073709551616) (hnz : sizes_nonzero maps) :
    sizes_nonzero (maps_subtract maps lo hi)
    ∧ ∀ p, owners (maps_subtract maps lo hi) p ≤ owners maps p := by
  induction maps with
  | nil =>
    simp only [maps_subtract]
    exact ⟨fun _ he => (List.not_mem_nil he).elim, fun p => Nat.le_refl _⟩
  | cons e r ih =>
    obtain ⟨a, sz⟩ := e
    have hhd : bv_unsigned sz ≠ 0 := hnz (a, sz) List.mem_cons_self
    have htl : sizes_nonzero r := fun e he => hnz e (List.mem_cons_of_mem _ he)
    obtain ⟨ihnz, ihle⟩ := ih htl
    refine ⟨?_, ?_⟩
    · intro e he
      simp only [maps_subtract, List.mem_append] at he
      rcases he with he | he
      · exact (iv_subtract_ok a sz lo hi 0 hlo hlohi hhi hhd).2 e he
      · exact ihnz e he
    · intro p
      simp only [maps_subtract, owners_app, owners]
      have hiv := (iv_subtract_ok a sz lo hi p hlo hlohi hhi hhd).1
      have hle := ihle p
      cases ho : owns_b (a, sz) p <;>
        simp only [ho, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hiv ⊢ <;>
        omega

/-- Rocq: `VmMapsDisjoint.maps_wf_subtract`. -/
theorem maps_wf_subtract (maps : List (word × word)) (lo hi : Int) (h1 : 0 ≤ lo) (h2 : lo ≤ hi)
    (h3 : hi < 18446744073709551616) (hwf : maps_wf maps) : maps_wf (maps_subtract maps lo hi) := by
  obtain ⟨hnz, hun⟩ := hwf
  obtain ⟨ha, hb⟩ := maps_subtract_ok maps lo hi h1 h2 h3 hnz
  exact ⟨ha, fun p hp => Nat.le_trans (hb p) (hun p hp)⟩

/-- Nothing survives a subtraction INSIDE the range subtracted: the cut is
free of what `iv_subtract` keeps, which is what makes the spanning
MAP_FIXED post-state well formed.  The `2 ^ 64` bound is the right
remnant's; every caller has it from the `alloc_top` gate (the argument is
on the Rocq lemma).  Rocq: `VmMapsDisjoint.iv_subtract_region_free`. -/
theorem iv_subtract_region_free (c sz a n : word)
    (hhi : bv_unsigned a + bv_unsigned n < 18446744073709551616) (b s : word)
    (hin : (b, s) ∈ iv_subtract c sz (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) :
    iv_overlap a n b s = false := by
  have ha := word_range a
  have hn := word_range n
  have hc := word_range c
  have hsz := word_range sz
  unfold iv_subtract at hin
  simp only [List.mem_append] at hin
  rcases hin with hin | hin
  · by_cases h1 : bv_unsigned c < bv_unsigned a
    · simp only [h1, ↓reduceIte, List.mem_singleton, Prod.mk.injEq] at hin
      obtain ⟨rfl, rfl⟩ := hin
      simp only [iv_overlap, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      rw [u64 _ (by omega) (by omega)]
      omega
    · simp only [h1, ↓reduceIte, List.mem_nil_iff] at hin
  · by_cases h2 : bv_unsigned a + bv_unsigned n < bv_unsigned c + bv_unsigned sz
    · simp only [h2, ↓reduceIte, List.mem_singleton, Prod.mk.injEq] at hin
      obtain ⟨rfl, rfl⟩ := hin
      simp only [iv_overlap, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      rw [u64 _ (by omega) (by omega), u64 _ (by omega) (by omega)]
      omega
    · simp only [h2, ↓reduceIte, List.mem_nil_iff] at hin

/-- Rocq: `VmMapsDisjoint.maps_subtract_region_free`. -/
theorem maps_subtract_region_free (maps : List (word × word)) (a n : word)
    (hhi : bv_unsigned a + bv_unsigned n < 18446744073709551616) :
    region_free (maps_subtract maps (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) a n
      = true := by
  apply region_free_intro
  induction maps with
  | nil =>
    intro b s hin
    simp only [maps_subtract, List.mem_nil_iff] at hin
  | cons e r ih =>
    obtain ⟨c, sz⟩ := e
    intro b s hin
    simp only [maps_subtract, List.mem_append] at hin
    rcases hin with hin | hin
    · exact iv_subtract_region_free c sz a n hhi b s hin
    · exact ih b s hin

/-- Rocq: `VmMapsDisjoint.maps_wf_filter`. -/
theorem maps_wf_filter (f : word × word → Bool) (maps : List (word × word))
    (hwf : maps_wf maps) : maps_wf (maps.filter f) := by
  obtain ⟨hnz, hun⟩ := hwf
  exact ⟨sizes_nonzero_filter f maps hnz,
    fun p hp => Nat.le_trans (owners_filter_le f maps p) (hun p hp)⟩

/-- Rocq: `VmMapsDisjoint.region_free_filter`. -/
theorem region_free_filter (f : word × word → Bool) (maps : List (word × word)) (lo n : word)
    (h : region_free maps lo n = true) : region_free (maps.filter f) lo n = true := by
  apply region_free_intro
  intro a sz hin
  exact region_free_In maps lo n a sz h (List.mem_filter.mp hin).1

/-- Rocq: `VmMapsDisjoint.maps_wf_cons_sub`. -/
theorem maps_wf_cons_sub (maps : List (word × word)) (a n0 n : word) (hwf : maps_wf maps)
    (hn : bv_unsigned n ≠ 0) (hin : (a, n0) ∈ maps) (hle : bv_unsigned n ≤ bv_unsigned n0) :
    maps_wf ((a, n) :: map_remove maps a) := by
  obtain ⟨hnz, hun⟩ := hwf
  refine ⟨?_, ?_⟩
  · intro e he
    rcases List.mem_cons.mp he with heq | he'
    · subst heq
      exact hn
    · exact sizes_nonzero_filter _ maps hnz e he'
  · intro p hp
    simp only [owners]
    cases ho : owns_b (a, n) p with
    | true =>
      have ho' := owns_true a n p ho
      have ho0 : owns_b (a, n0) p = true := owns_intro a n0 p ho'.1 (by omega)
      have hlt := owners_map_remove_lt maps a n0 p hin ho0
      have hu := hun p hp
      simp only [↓reduceIte]
      omega
    | false =>
      have hf := owners_filter_le (fun q => !bv_eqb q.1 a) maps p
      have hu := hun p hp
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      unfold map_remove
      omega

/-! ### What the invariant buys: base uniqueness where a syscall can name a
base, and the `map_has`/`map_remove` agreement munmap needs -/

/-- Rocq: `VmMapsDisjoint.map_has_In`. -/
theorem map_has_In (maps : List (word × word)) (a n : word) (h : map_has maps a n = true) :
    (a, n) ∈ maps := by
  unfold map_has at h
  rw [List.any_eq_true] at h
  obtain ⟨⟨b, s⟩, hin, hb⟩ := h
  simp only [Bool.and_eq_true, bv_eqb_eq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  exact hin

/-- THE NARROW FORM the downstream `munmap` argument asks for: at a
PAGE-ALIGNED base — the only kind `munmap`, `mremap`, `mprotect` and
`mmap` can produce or accept — the ledger holds exactly one entry, and it
is the one `map_has` matched.  So `map_has`'s `(base, size)` test and
`map_remove`'s base-only removal name the same mapping.  Rocq:
`VmMapsDisjoint.base_entry_unique`. -/
theorem base_entry_unique (maps : List (word × word)) (a n : word) (hwf : maps_wf maps)
    (ha : bv_unsigned a % page_size = 0) (hhas : map_has maps a n = true) :
    maps.filter (fun q => bv_eqb q.1 a) = [(a, n)] := by
  obtain ⟨hnz, hun⟩ := hwf
  have hin := map_has_In maps a n hhas
  have hinF : (a, n) ∈ maps.filter (fun q => bv_eqb q.1 a) :=
    List.mem_filter.mpr ⟨hin, bv_eqb_refl a⟩
  have hown : ∀ e ∈ maps.filter (fun q => bv_eqb q.1 a), owns_b e (bv_unsigned a) = true := by
    intro e he
    obtain ⟨b, s⟩ := e
    obtain ⟨he', hb⟩ := List.mem_filter.mp he
    simp only [bv_eqb_eq] at hb
    subst hb
    have hs : bv_unsigned s ≠ 0 := hnz (b, s) he'
    have := word_range s
    exact owns_intro b s (bv_unsigned b) (Int.le_refl _) (by omega)
  have hall := owners_all_own _ (bv_unsigned a) hown
  have hle := owners_filter_le (fun q => bv_eqb q.1 a) maps (bv_unsigned a)
  have hun' := hun (bv_unsigned a) ha
  have hlen : (maps.filter (fun q => bv_eqb q.1 a)).length ≤ 1 := by omega
  generalize hF : maps.filter (fun q => bv_eqb q.1 a) = F at hinF hlen ⊢
  match F, hinF, hlen with
  | [], hinF, _ => exact absurd hinF List.not_mem_nil
  | [x], hinF, _ =>
    rw [List.mem_singleton] at hinF
    rw [hinF]
  | _ :: _ :: _, _, hlen =>
    simp only [List.length_cons] at hlen
    omega

/-- …hence the size in a `map_has` hit is unique.  Rocq:
`VmMapsDisjoint.map_has_pins_size`. -/
theorem map_has_pins_size (maps : List (word × word)) (a n1 n2 : word) (hwf : maps_wf maps)
    (ha : bv_unsigned a % page_size = 0) (h1 : map_has maps a n1 = true)
    (h2 : map_has maps a n2 = true) : n1 = n2 := by
  have e1 := base_entry_unique maps a n1 hwf ha h1
  have hinF : (a, n2) ∈ maps.filter (fun q => bv_eqb q.1 a) :=
    List.mem_filter.mpr ⟨map_has_In maps a n2 h2, bv_eqb_refl a⟩
  rw [e1, List.mem_singleton, Prod.mk.injEq] at hinF
  exact hinF.2.symm

/-- Rocq: `VmMapsDisjoint.live_bytes_filter_split`. -/
theorem live_bytes_filter_split (f : word × word → Bool) (maps : List (word × word)) :
    live_bytes maps = live_bytes (maps.filter f) + live_bytes (maps.filter (fun e => !f e)) := by
  induction maps with
  | nil => rfl
  | cons e r ih =>
    obtain ⟨a, s⟩ := e
    cases hf : f (a, s) <;>
      simp only [List.filter_cons, hf, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        ↓reduceIte, live_bytes, ih] <;>
      omega

/-- The budget reading of the same fact: an exact `munmap` gives back
exactly the bytes `map_has` matched.  Rocq:
`VmMapsDisjoint.munmap_returns_matched_bytes`. -/
theorem munmap_returns_matched_bytes (maps : List (word × word)) (a n : word) (hwf : maps_wf maps)
    (ha : bv_unsigned a % page_size = 0) (hhas : map_has maps a n = true) :
    live_bytes maps = bv_unsigned n + live_bytes (map_remove maps a) := by
  have hs := live_bytes_filter_split (fun q => bv_eqb q.1 a) maps
  rw [base_entry_unique maps a n hwf ha hhas] at hs
  simp only [live_bytes, Int.add_zero] at hs
  unfold map_remove
  exact hs

/-! ## PRESERVATION — the setters, the wrappers, and the frame tactics

Every setter builds its own subsystem record and carries the rest
across, so `m_vmmaps` of a stack of them is `m_vmmaps` of the base BY
CONVERSION, and each fact below is `rfl` where the Rocq one is
`reflexivity`.  They exist to give a rewrite a handle where a proof
cannot unfold, exactly as Rocq's `vmm_*` do. -/

/-- Rocq: `VmMapsDisjoint.vmm_forget_range`. -/
theorem vmm_forget_range (lo hi : Int) (m : Model) :
    m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m := rfl

/-- Rocq: `VmMapsDisjoint.vmm_forget_ranges`.  The one setter fact that is
not `rfl`: `forget_vm_ranges` recurses on a list a hypothesis leaves open. -/
theorem vmm_forget_ranges (rs : List (word × word)) (m : Model) :
    m_vmmaps (forget_vm_ranges rs m) = m_vmmaps m := by
  induction rs generalizing m with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨a, n⟩ := p
    exact ih (vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) m)

/-- Rocq: `VmMapsDisjoint.vmm_mmap_backing`. -/
theorem vmm_mmap_backing (flags a n : word) (m : Model) :
    m_vmmaps (with_mmap_backing flags a n m) = m_vmmaps m := by
  unfold with_mmap_backing
  by_cases hf : mmap_noreserve_b flags = true
  · simp only [hf, ↓reduceIte]
    exact m_vmmaps_with_vm_backing _ _ _
  · simp only [hf, Bool.false_eq_true, ↓reduceIte]

/-- Rocq: `VmMapsDisjoint.vmm_mmap_replacement`. -/
theorem vmm_mmap_replacement (flags a n : word) (m : Model) :
    m_vmmaps (with_mmap_replacement flags a n m) = m_vmmaps m := by
  unfold with_mmap_replacement
  rw [vmm_mmap_backing, vmm_forget_range]

/-- Rocq: `VmMapsDisjoint.vmm_mmap_destroyed`. -/
theorem vmm_mmap_destroyed (a n : word) (h : VmMaps) (m : Model) :
    m_vmmaps (with_mmap_destroyed a n h m) = h := rfl

/-- Rocq: `VmMapsDisjoint.vmm_brk_next`. -/
theorem vmm_brk_next (m : Model) (req r : word) :
    m_vmmaps (with_brk_next m req r) = brk_model_next (m_vmmaps m) req r := by
  simp only [with_brk_next, vmm_forget_ranges, m_vmmaps_with_vmmaps]

/-- Rocq: `VmMapsDisjoint.vmm_mprotect_next`. -/
theorem vmm_mprotect_next (m : Model) (addr n : word) :
    m_vmmaps (mprotect_model_next m addr n)
      = VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved (m_vmmaps m).vm_maps
          (maps_subtract (m_vmmaps m).vm_noaccess (bv_unsigned addr)
            (bv_unsigned addr + bv_unsigned n))
          (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk (m_vmmaps m).vm_limit
          (m_vmmaps m).vm_mmap_base (m_vmmaps m).vm_init_sp := rfl

/-- Rocq: `VmMapsDisjoint.vmm_madvise_next`. -/
theorem vmm_madvise_next (m : Model) (addr n : word) :
    m_vmmaps (madvise_dontneed_next m addr n) = m_vmmaps m := rfl

/-- Rocq: `VmMapsDisjoint.vmm_resize_backing`. -/
theorem vmm_resize_backing (b : Bool) (old old_n dst new_n : word) (m : Model) :
    m_vmmaps (vm_resize_backing b old old_n dst new_n m) = m_vmmaps m := rfl

open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mremap in
/-- Rocq: `VmMapsDisjoint.vmm_mremap_next`. -/
theorem vmm_mremap_next (m : Model) (old old_n dst new_n : word) :
    m_vmmaps (mremap_model_next m old old_n dst new_n)
      = mremap_maps_next (m_vmmaps m) old dst new_n := by
  simp only [mremap_model_next, vmm_resize_backing, m_vmmaps_with_vmmaps]

/-- Rocq: `VmMapsDisjoint.vmm_fixed_rw_next`. -/
theorem vmm_fixed_rw_next (m : Model) (addr n : word) :
    (mmap_fixed_rw_next (m_vmmaps m) addr n).vm_maps = (m_vmmaps m).vm_maps := rfl

/-- Rocq: `VmMapsDisjoint.w_is0_false`. -/
theorem w_is0_false (w : word) (h : w_is0 w = false) : bv_unsigned w ≠ 0 := by
  intro hc
  have h0 : (Z_to_bv 64 0).toNat = 0 := by decide
  have hw : w = Z_to_bv 64 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [h0]
    unfold bv_unsigned at hc
    omega
  rw [hw, w_is0, bv_eqb_refl] at h
  exact absurd h (by simp only [Bool.true_eq_false, not_false_eq_true])

/-- Rocq: `VmMapsDisjoint.page_round_up_pos`. -/
theorem page_round_up_pos (z : Int) (h : 0 < z) : 0 < page_round_up_Z z := by
  unfold page_round_up_Z page_size
  omega

/-! ### The checkers' shared wrappers hand the model straight back

Rocq states these as forward lemmas an `apply … in H` consumes; here the
arguments other than the hypothesis are implicit, so that `vm_step` can
apply each one to a hypothesis it knows only by name. -/

/-- Rocq: `VmMapsDisjoint.check_ret_only_model`. -/
theorem check_ret_only_model {eff : SyscallEffect} {r : word} {mm : Model} {evs0 : List event}
    {m' : Model} {evs : List event} (h : check_ret_only eff r mm evs0 = CheckOk m' evs) :
    m' = mm :=
  ((check_ret_only_ok_iff eff r mm evs0 m' evs).mp h).2.1

/-- Rocq: `VmMapsDisjoint.check_ret_only_copyins_model`. -/
theorem check_ret_only_copyins_model {reads : List (word × Nat)} {eff : SyscallEffect} {r : word}
    {mm : Model} {evs0 : List event} {m' : Model} {evs : List event}
    (h : check_ret_only_copyins reads eff r mm evs0 = CheckOk m' evs) : m' = mm :=
  ((check_ret_only_copyins_ok_iff reads eff r mm evs0 m' evs).mp h).2.1

/-- Rocq: `VmMapsDisjoint.check_copyins_model`. -/
theorem check_copyins_model {reads : List (word × Nat)} {eff : SyscallEffect} {res : check_result}
    {m' : Model} {evs : List event} (h : check_copyins reads eff res = CheckOk m' evs) :
    res = CheckOk m' evs := by
  unfold check_copyins at h
  split at h
  · exact h
  · cases h

/-- Rocq: `VmMapsDisjoint.check_copyin_prefix_model`. -/
theorem check_copyin_prefix_model {reads : List (word × Nat)} {eff : SyscallEffect}
    {res : check_result} {m' : Model} {evs : List event}
    (h : check_copyin_prefix reads eff res = CheckOk m' evs) : res = CheckOk m' evs := by
  unfold check_copyin_prefix at h
  split at h
  · cases h
  · split at h
    · exact h
    · cases h

/-- Rocq: `VmMapsDisjoint.check_copyins_after_model`. -/
theorem check_copyins_after_model {reads : List (word × Nat)} {eff : SyscallEffect}
    {res : check_result} {m' : Model} {evs : List event}
    (h : check_copyins_after reads eff res = CheckOk m' evs) : res = CheckOk m' evs :=
  ((check_copyins_after_ok_iff reads eff res m' evs).mp h).2

/-! ### The frame tactics

Rocq's `vm_step H` reads the shape of `H` with `match type of`; Lean's
macros cannot, so each arm is tried in turn under `first` and the
hypothesis is passed by name.  Arm for arm with Rocq's list:

- `CheckReject = CheckOk _ _`, `CheckUnmodeled = CheckOk _ _` and
  `CheckOk _ _ = CheckOk _ _` (`discriminate` and `injection H as <- <-`)
  are one `cases h`, which closes a constructor mismatch and substitutes
  the components of a match;
- the five wrapper arms are the `*_model` lemmas above, applied with
  `replace` and, where they yield an equation on the model, `subst`;
- `if ?b then _ else _` and `match ?x with _ end` (`destruct … eqn:?`)
  are `split at h`, which keeps the hypothesis's name in both branches;
- `dsimp only at h` is the `cbv zeta` the per-arm Rocq proofs run before
  `vm_frame2`, folded in here so that a `let` in a checker does not stop
  the loop.

`vm_frame h` is Rocq's `repeat vm_step H; reflexivity`: `repeat'` because
Ltac's `repeat` recurses into every subgoal a step opens, and `<;> rfl`
because Ltac's `;` runs the closer on all of them.  `vm_frame2 h` adds
`vm_done h` to the loop and closes with `try rfl`, as Rocq's does. -/

/-- One step of the frame argument on hypothesis `h`. -/
macro "vm_step " h:ident : tactic => `(tactic| first
  | cases $h:ident
  | (replace $h:ident := check_ret_only_model $h:ident; subst $h:ident)
  | (replace $h:ident := check_ret_only_copyins_model $h:ident; subst $h:ident)
  | (replace $h:ident := check_copyins_after_model $h:ident)
  | (replace $h:ident := check_copyin_prefix_model $h:ident)
  | (replace $h:ident := check_copyins_model $h:ident)
  | split at $h:ident
  | dsimp only at $h:ident)

/-- Rocq's `vm_frame H`. -/
macro "vm_frame " h:ident : tactic => `(tactic| (repeat' vm_step $h:ident) <;> rfl)

/-- Rocq's `vm_done H`: close a frame goal through a wrapper lemma that
does not fit `vm_step`'s shapes — `check_efault_or_frame`,
`check_readv_gap_frame` and `check_open_result_frame` in the Rocq file.
The syntax is declared here with one rule that fails, and each wrapper's
frame lemma adds its own `macro_rules` for `vm_done` beside itself:
`check_efault_or_frame` below is the first and the worked example, and
the checker twins of `Checks/Sys/Fs/ReadWrite.v` and
`Checks/Sys/Fs/Open.v` register the other two the same way, from their
own files.  Lean tries the most recently declared rule first and falls
through to the older ones when it fails, and reports the LAST rule tried
when all fail — the one below, whose message therefore names the case —
which is what makes the point extensible without an edit here.  A rule
that succeeds without closing the goal would make `vm_frame2`'s loop
spin to its iteration cap: every rule must be an `exact`. -/
syntax "vm_done " ident : tactic

macro_rules
  | `(tactic| vm_done $_h:ident) =>
    `(tactic| fail "vm_done: no wrapper frame lemma applies to this hypothesis")

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Uaccess in
/-- Rocq: `VmMapsDisjoint.check_efault_or_frame`.  The -EFAULT-or-fallback
acceptor hands the model straight back on both of its answers; `vm_frame`
closes it once the definition is opened, and it is a `vm_done` rule
because a checker that CALLS it leaves it closed. -/
theorem check_efault_or_frame (fb : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_efault_or fb eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_efault_or at h
  vm_frame h

/-- The first `vm_done` rule.  Declared after the failing default so that
it is tried first; the arguments other than the hypothesis are found by
unification FROM THE HYPOTHESIS, which is what the `.trans rfl` is for: a
checker calls the acceptor on a model it has already rebuilt
(`with_halted … m`, say), so the lemma's right-hand side is `m_vmmaps` of
that model, and the goal's is `m_vmmaps m`.  Elaborated against the goal
directly, the lemma's model argument would be fixed to `m` first and the
hypothesis would then fail to fit; through `Eq.trans` it is fixed by the
hypothesis and the remaining step is the setter conversion `rfl` reads. -/
macro_rules
  | `(tactic| vm_done $h:ident) =>
    `(tactic| exact (check_efault_or_frame _ _ _ _ _ $h:ident).trans rfl)

/-- Rocq's `vm_frame2 H`. -/
macro "vm_frame2 " h:ident : tactic =>
  `(tactic| (repeat' first | vm_step $h:ident | vm_done $h:ident) <;> (try rfl))

/-! ## The invariant, over the whole dispatcher -/

/-- `execve` establishes it: the ledger starts empty.  Rocq:
`VmMapsDisjoint.init_model_vm_wf`. -/
theorem init_model_vm_wf (reserved : List (word × word)) (brk0 mbase sp : word) (lim : Int)
    (inp : ProcInput) : vm_wf (m_vmmaps (init_model reserved brk0 mbase sp lim inp)) := by
  have hm : (m_vmmaps (init_model reserved brk0 mbase sp lim inp)).vm_maps = [] := rfl
  unfold vm_wf maps_wf sizes_nonzero page_owner_unique
  rw [hm]
  exact ⟨fun _ he => (List.not_mem_nil he).elim, fun p _ => Nat.zero_le 1⟩

/-- `lookup_ca` answers with an arm OF the table it searched.  Rocq:
`VmMapsDisjoint.lookup_ca_In`. -/
theorem lookup_ca_In (t : List CheckedArm) (n : Int) (c : CheckedArm)
    (h : lookup_ca t n = some c) : c ∈ t := by
  induction t with
  | nil => simp only [lookup_ca, reduceCtorEq] at h
  | cons a r ih =>
    simp only [lookup_ca] at h
    by_cases hn : ca_no a = n
    · simp only [hn, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · simp only [hn, ↓reduceIte] at h
      exact List.mem_cons_of_mem a (ih h)

/-- What one dispatcher arm owes the ledger, as a property of the table
entry rather than of a syscall number.  Rocq:
`VmMapsDisjoint.arm_preserves_vm`. -/
def arm_preserves_vm (c : CheckedArm) : Prop :=
  ∀ i eff m m' evs, c.ca_check i eff m = CheckOk m' evs →
    vm_wf (m_vmmaps m) → vm_wf (m_vmmaps m')

/-- The frame reading of the invariant: a checker that hands the VM
subsystem back untouched preserves whatever held of it.  Rocq closes each
frame alternative with `erewrite check_X_frame by eassumption; exact Hwf`;
this is that step as a lemma. -/
theorem vm_wf_of_frame {m m' : Model} (hf : m_vmmaps m' = m_vmmaps m) (hwf : vm_wf (m_vmmaps m)) :
    vm_wf (m_vmmaps m') := by
  rw [hf]
  exact hwf

/-- An arm whose checker never moves `m_vmmaps` preserves the invariant.
This is how a `check_*_frame` lemma becomes the arm-level fact
an arm file states and the generated alternation consumes: the rewrite to the plain
checker is `simp only [arm_unfold] at h`, and the frame lemma closes the
rest. -/
theorem arm_preserves_of_frame (c : CheckedArm)
    (hf : ∀ i eff m m' evs, c.ca_check i eff m = CheckOk m' evs → m_vmmaps m' = m_vmmaps m) :
    arm_preserves_vm c :=
  fun i eff m m' evs h hwf => vm_wf_of_frame (hf i eff m m' evs h) hwf

/-! ### The table split and the fallback

`vm_arms_split t` turns `∀ c ∈ t, arm_preserves_vm c` into one goal per
arm of the table `t`, in table order — Rocq's `unfold checked_table;
repeat apply Forall_cons` — and closes it outright when `t` is empty.
`vm_arm_uncovered` is Rocq's `fail 1 "…"`, with one difference of shape
that Lean forces.  Rocq's `fail 1` escapes the enclosing `first` by its
level, so the fallback can be the alternation's last alternative and
still fail the proof.  Lean's `first` catches every ordinary error
(`Tactic.orElse` is a `try … catch`, and only interrupts and resource
limits pass through it), so a fallback INSIDE the `first` would be caught
and the alternatives behind it would run.  The fallback is therefore a
separate step after the alternation, `all_goals vm_arm_uncovered`, and the
alternation itself closes with `| skip`: `skip` always succeeds, so an
alternative appended behind it never runs, the arm it names stays open,
and the step below fails naming that arm — which is the Rocq rule "an
alternative listed behind the fail never runs", kept by construction
instead of by convention.  It is an `elab` rather than a `fail` because
`fail` prints the goal WITH the case tag `constructor` attaches, which
varies with the arm's position in the table; the elab prints the goal's
type alone, so the message a test pins does not. -/

/-- One goal per arm of the table `t`. -/
macro "vm_arms_split " t:ident : tactic =>
  `(tactic| (simp only [$t:ident, List.forall_mem_cons, List.mem_nil_iff, false_implies,
      implies_true, and_true]
             repeat' constructor))

open Lean Elab Tactic in
/-- The fallback that names the arm.  Its message is the whole reason the
alternation has a last alternative; Rocq's `fail 1` gives the same
instruction in its own words, and the wording here differs because the
edit it asks for is in the arm's file under `Checks/Arms/`, not beside a
`fail`. -/
elab "vm_arm_uncovered" : tactic => do
  let g ← getMainGoal
  -- The goal's TYPE, not the goal: the split leaves no hypotheses, and the
  -- case tag `constructor` attaches would otherwise vary with the arm's
  -- position in the table, which the pinned message must not.
  let ty ← g.withContext do instantiateMVars (← g.getType)
  let msg : String :=
    "checked_table_preserves_vm has no case for this dispatcher arm.\n" ++
    "Give the new checker a *_frame lemma (it leaves m_vmmaps alone) or a *_preserves one\n" ++
    "(it writes vm_maps), state `arm_<name>_preserves_vm : arm_preserves_vm arm_<name>` from\n" ++
    "it in the arm's file under Checks/Arms/, and let tools/gen_lean_checked.py render\n" ++
    "`| exact arm_<name>_preserves_vm` ABOVE the alternation's closing `| skip`;\n" ++
    "an alternative listed behind that line never runs.  The uncovered goal, which names\n" ++
    "the arm:"
  throwError m!"{msg}\n⊢ {ty}"

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint
