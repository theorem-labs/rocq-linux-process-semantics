(** * LinuxProcessSem.Checks.Cases.Mm.Mmap — worked examples over brk (214), mmap (222), munmap (215)

    Mirrors [Sys/Mm/Mmap.v], which answers to Linux [mm/mmap.c]: this
    file holds the worked examples for the syscalls defined there, and
    no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Decode DecodeC.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude Fs.ReadWrite.

Example munmap_unaligned_einval :
  check_syscall (mkInput 215 [65537; 4096; 0; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) one_map_model
  = CheckOk one_map_model [].
Proof. check_eq. Qed.

Example munmap_len_zero_einval :
  check_syscall (mkInput 215 [65536; 0; 0; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) one_map_model
  = CheckOk one_map_model [].
Proof. check_eq. Qed.

(** An effect that keeps the memory mapped (no [eff_unmaps]) is rejected
    — a successful unmap must DECLARE the range it made inaccessible, and
    a stays-readable answer is not admissible. *)

Example munmap_without_unmap_rejected :
  check_syscall (mkInput 215 [65536; 4096; 0; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) one_map_model
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** munmap of a range containing no mapped pages is a no-op success,
    as on Linux. *)

Example munmap_free_range_noop :
  check_syscall (mkInput 215 [131072; 4096; 0; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) one_map_model
  = CheckOk one_map_model [].
Proof. check_eq. Qed.

(** The free-range arm's bound is this run's [State.alloc_top],
    INCLUSIVE: a free page ending exactly at it is the no-op 0, and the
    page above it is inside the stack band the ledger does not describe,
    so the arm declines.  [one_map_model]'s stack pointer is [demo_sp],
    so its [alloc_top] is [demo_top]; a [<?] in place of the [<=?] turns
    the first of these red. *)

Example munmap_free_range_ending_at_alloc_top_is_noop :
  check_syscall (mkInput 215 [Z_to_bv 64 (demo_top - 4096); 4096; 0; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) one_map_model
  = CheckOk one_map_model [].
Proof. check_eq. Qed.

Example munmap_free_range_in_the_stack_band_is_unmodeled :
  check_syscall (mkInput 215 [Z_to_bv 64 demo_top; 4096; 0; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) one_map_model
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** A PARTIAL unmap (Linux would split the mapping) is unmodeled and
    fails closed. *)

Example munmap_partial_is_error :
  check_syscall (mkInput 215 [65536; 4096; 0; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect 0 [] [])
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 demo_limit)
                 (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)))
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** Reason 3.  [check_munmap]'s gate bounds the SUM [addr + nZ] by
    [State.TASK_SIZE] (see [Mmap.munmap_spec]); pin that an ordinary
    munmap of a live low-address mapping still takes the exact-match arm
    and succeeds. *)

Example munmap_ordinary_still_succeeds :
  check_syscall (mkInput 215 [65536; 4096; 0; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffectU 0 [] [] [(65536, 4096)] [] []) one_map_model
  = CheckOk (with_vmmaps (mkVmMaps [] [] 0 0 demo_limit) one_map_model) [].
Proof. check_eq. Qed.

(** A mapping the MODEL holds just under 2^64 — which no riscv64 kernel
    can hand out, the model admits it only because no Rocq-side
    invariant bounds a segment's address — is refused by [munmap] with
    Linux's own -EINVAL, because the range test precedes the ledger:
    [start > TASK_SIZE] fails first.  An unmap reported here is
    rejected. *)
Example munmap_near_max_is_einval :
  check_syscall
    (mkInput 215 [Z_to_bv 64 (two_pow_64 - 8192); 4096; 0; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] [])
    near_ceiling_sum_model
  = CheckOk near_ceiling_sum_model []
  /\ check_syscall
    (mkInput 215 [Z_to_bv 64 (two_pow_64 - 8192); 4096; 0; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU 0 [] [] [(Z_to_bv 64 (two_pow_64 - 8192), 4096)] [] [])
    near_ceiling_sum_model
  = CheckReject.
Proof. split; check_eq. Qed.

(** Reason 3 (a model constant, [State.TASK_SIZE]) and Reason 4 (no
    real kernel hands back a mapping up here): a range whose end reaches
    2^64 exactly.  [addr = 2^63], [len = 2^63]: [nZ = page_round_up_Z
    len = 2^63] unchanged (already page-sized), and [addr + nZ = 2^64].
    Linux's [do_vmi_munmap] answers -EINVAL from [start > TASK_SIZE]
    before it forms [end = start + PAGE_ALIGN(len)], and so does the
    model's gate, which compares the [Z] sum against [TASK_SIZE] before
    the ledger is consulted.  A bound on [nZ] alone would have missed
    it — [nZ = 2^63] is a perfectly good page count — and an adversarial
    model carrying an exact mapping at this address would then have
    reported success for a range whose end no [word] can name.  The
    gate answers before [m] is consulted, and the 0 is rejected. *)

Example munmap_high_addr_sum_wraps_is_einval :
  check_syscall
    (mkInput 215 [Z_to_bv 64 (2 ^ 63); Z_to_bv 64 (2 ^ 63); 0; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) one_map_model
  = CheckOk one_map_model []
  /\ check_syscall
    (mkInput 215 [Z_to_bv 64 (2 ^ 63); Z_to_bv 64 (2 ^ 63); 0; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) one_map_model
  = CheckReject.
Proof. split; check_eq. Qed.

(* -------------------------------------------------------------------------
   mremap(MREMAP_MAYMOVE): exact ownership, final-budget accounting, and
   snapshot-copy semantics.  Placement and allocation-ledger facts are
   model-internal.
   ------------------------------------------------------------------------- *)

(** On a RESIZING call the one admitted runtime failure is ENOMEM, with a
    canonical empty effect and the allocation ledger unchanged.  This one
    shrinks, and the shrink path really can fail: [do_vmi_munmap]
    (mm/mremap.c:1096, v6.12) splits the VMA, and the split can fail to
    allocate (mm/vma.c:384-405) or trip [sysctl_max_map_count]
    (mm/vma.c:1197).  The equal-size arm is different — see
    [mremap_equal_size_enomem_rejected]. *)

(** Shrinking in place replaces the exact mapping and refunds its tail. *)

(** The refunded page is spendable once by another allocator grant. *)

(** A successful grow is inadmissible when its FINAL live-byte total exceeds
    the limit; mremap charges only [new-old], not a transient second mapping. *)

(** A moved result cannot alias another live mapping, even when its copy,
    unmap, and size fields otherwise have the canonical shape. *)

(** [apply_effect] reads the moved prefix from the immutable PRE-effect
    snapshot: although the same effect unmaps the source first, sentinel
    bytes arrive at the destination, the source becomes [None], the grown
    tail is zero, and an unrelated byte is untouched. *)

(** An equal-size call is deterministic and succeeds with an EMPTY effect:
    Linux returns [addr] at mm/mremap.c:1092 (v6.12) having done no
    allocation, no VMA split and no accounting, so nothing is unmapped,
    zeroed or copied.  Reason 3: what is pinned here is the resulting
    LEDGER — [vm_maps] and the live-byte total come out byte-identical, so
    the call is a no-op for the allocator too, which no trace reveals. *)

(** And that arm carries NO injectable failure.  Walking mm/mremap.c:1041-1093
    (v6.12) for [flags = MREMAP_MAYMOVE], a non-hugetlb VMA that exists and
    is unsealed, and [old_len = new_len], the only exits are -EINTR (:1042),
    -EFAULT (:1045), -EPERM (:1051), the hugetlb -EINVALs (:1062-1072) and
    [ret = addr] (:1092) — and all four errnos are excluded by the modeled
    shape (see [Mremap.mremap_errnos]).  No allocation, no split, no
    accounting, hence no -ENOMEM: a trace reporting one on a modeled source
    is rejected.  Reason 4: no kernel can be made to produce it; this
    asks the checker directly, with the source's exact ledger fixed by
    hand. *)

(** Growing IN PLACE.  Linux takes this branch when [old_len == vma->vm_end
    - addr] and [vma_expandable] holds ([vrm_can_expand_in_place],
    mm/mremap.c:1430-1444, Linux v6.18.46, testing [vma_expandable],
    :1415-1427); the grown delta gets no page tables from
    [vma_merge_extend] ([expand_vma_in_place], :1470), so it faults in as
    zeroes through [do_anonymous_page] (mm/memory.c:5149-5262) — which is
    the declared zero range.  Reason 3: the assertion pins the post-state
    ledger, where the
    single [vm_maps] entry is REPLACED by a longer one at the same base
    rather than a second entry being added — invisible in any trace. *)

(** The same call on the same budget is rejected once the neighbouring page
    is owned by another mapping: [vma_expandable] (mm/mremap.c:1415-1427,
    Linux v6.18.46) would fail and Linux would have to move, so staying at
    [addr] is not an admissible answer.  The budget still allows the growth
    (limit 16384,
    final live bytes 12288), so the rejection is attributable to the
    placement conjunct alone.  Reason 4: it takes a kernel that expanded
    over a live mapping, which no kernel does. *)

(** The BINARY IMAGE blocks an in-place grow the same way a live mapping
    does, which is what the [vm_reserved] half of
    [Mremap.mremap_inplace_grow_b] decides.  This model is
    [mremap_one_page_model] with ONE field changed — a reserved page at
    69632, where [mremap_inplace_grow_accepts] has none — so the flipped
    verdict is attributable to that conjunct and nothing else: the
    [vm_maps] half still passes ([map_remove] takes the source out and
    leaves the ledger empty), and so does the budget (limit 8192, final
    live bytes 8192).  Deleting the conjunct would turn this [CheckReject]
    back into the [CheckOk] above.

    Reason 4: no live run can reach it.  Two things would have to line up —
    a tracked rw mapping sitting within [new_len] BELOW a LOAD segment, and
    a trace claiming Linux grew it in place over that segment.  The first is
    unobtainable: the only modeled way to choose an address for an anonymous
    mapping is MAP_FIXED, and [Mmap.mmap_fixed_noaccess_b] admits it solely
    as a PROT_NONE guard inside a mapping the process already owns, while a
    plain [mmap] takes whatever the kernel picks — never the image. *)

(** And the conjunct closes the in-place ARM, not the call: from the same
    ledger a move to free space is still admissible, which is also what
    Linux does once [vma_expandable] (mm/mremap.c:1415-1427, Linux
    v6.18.46) reports the neighbouring address space taken. *)

(** The THIRD conjunct of [Mremap.mremap_inplace_grow_b],
    [addr + new_len <= alloc_top h], is what keeps a grown mapping clear
    of the dynamic stack: the stack is not in [vm_reserved], so nothing
    else in the predicate notices a grow that climbs into it.  It needs a
    source address the other mremap examples cannot supply — [mremap_in]
    bakes 65536 — so the two below name theirs.

    [demo_top] = 0x7fff7f800000 = 140735332483072: the [State.alloc_top]
    of every ledger these cases build, [sp_window_lo] - [stack_max_size],
    since [demo_sp] seeds the stack pointer at the bottom of the SP
    window. *)

(** A source at [demo_top - 8192] whose grown extent ends exactly ON
    the ceiling, which the conjunct's [<=?] admits — the same inclusive
    boundary [mmap_modeled_at_ceiling_boundary_grants] reads off for
    [mmap]. *)

(** The same call one page higher, so the grown extent ends one page PAST
    the ceiling.  The model differs from the one above in the source's base
    address and nothing else, and every other conjunct is as permissive
    here as it is there: the source still fits under the ceiling
    ([addr + old_len = demo_top] exactly, so [Mremap.mremap_source_b]
    passes), [region_free] still sees an empty ledger once [map_remove]
    takes the source out, and the budget is still met (limit 8192, final
    live bytes 8192).  So the flip is attributable to
    [addr + new_len <= alloc_top h] alone, and deleting that conjunct
    would turn this [CheckReject] back into the [CheckOk] above.

    Reason 4: no live run can reach it.  A trace would have to grow a tracked
    mapping in place across its run's [alloc_top].  Linux's top-down
    [mmap_base] sits at least [stack_guard_gap] below the deepest legal
    stack, or [MAX_GAP] below [STACK_TOP] when a large guard makes the gap
    clamp (mm/util.c:456-461, [mmap_base], Linux v6.18.46).  The other
    case is a guard within one stack pad plus the stack rlimit of 2^64:
    the pad wraps (mm/util.c:450), or the sum wraps and the test at :453
    keeps the rlimit alone.  The gap is then at most 0x407fe000 and can
    clamp up to [MIN_GAP], so under [PF_RANDOMIZE] the base can be from
    one page to 0x387ff000 bytes above the deepest stack bottom, up to
    [STACK_TOP - MIN_GAP].  So with any smaller guard a live run's grants
    end under the stack's bottom.  With a guard in that range Linux can
    place a mapping above [alloc_top], which the model refuses: there the
    model's stack-disjointness rule ([State.alloc_top]) is narrower than
    Linux.  The other exception is an argv image over 1 MiB, a known
    limitation of the model. *)

(** And, as with the image conjunct, it closes the in-place ARM rather than
    the call: from the same ledger a move down to free space is still
    admissible. *)

(** [PAGE_ALIGN(new_len)] at mm/mremap.c:1918 ([do_mremap], Linux v6.18.46)
    is [(len + 4095) & ~4095] on an [unsigned long] — include/linux/mm.h:222
    -> include/vdso/align.h:8 -> include/uapi/linux/const.h:48-49 — and it
    WRAPS.  At [new_len = 2^64-1] it yields 0, so the [!new_len] test at
    mm/mremap.c:1771-1772 ([check_mremap_params]) answers -EINVAL, exactly
    as for [new_len = 0].  Reason
    3: what is pinned is the BOUNDARY of [Mremap.page_align_is0_b], read off
    from the two adjacent lengths below — a model predicate, where any one
    trace shows only a single point.  The rejecting halves are also reason
    4: they need a kernel that ignored the wrap, or applied it one page too
    far. *)

(** The boundary the wrap does NOT reach: [2^64-4096] is already page
    aligned, so [PAGE_ALIGN] returns it unchanged and nonzero and
    mm/mremap.c:1038 does not fire.  It is an enormous grow instead, and
    every placement conjunct — [addr + new_len <= alloc_top h] in both
    [Mremap.mremap_inplace_grow_b] and [Mremap.mremap_fresh_b] — fails, so
    the only outcome the model still admits is the injected -ENOMEM, and
    -EINVAL is rejected. *)

(** Gate ORDER for [old_len = 0].  Linux validates the flag word, then
    [offset_in_page(addr)] ([check_mremap_params], mm/mremap.c:1759-1764,
    Linux v6.18.46); the "duplicate a mapping" shape that [old_len = 0]
    selects is only examined much later, inside [check_prep_vma]
    (mm/mremap.c:1690-1693; v6.12's [vma_to_resize]), after [vma_lookup]
    (:1931) and the seal check (:1662-1663).  So a MISALIGNED address with
    [old_len = 0] is a plain -EINVAL, and the model must not fail closed on
    the clone shape first.  Reason 3: which gate fires first is
    model-internal, and a trace that only ever sees -EINVAL cannot
    distinguish the two orders. *)

(** With an ALIGNED address the same [old_len = 0] does reach the clone
    shape, whose -EINVAL preconditions (mm/mremap.c:839-842) the model does
    not track, so it fails closed.  This pins the ANSWER; the pair below
    pins the GATE that produces it, which on this ledger cannot be seen
    apart from [Mremap.mremap_source_b]. *)

(** A ledger entry of size ZERO, which no run can produce (every [vm_maps]
    writer emits a nonzero size — [mmap_spec]'s [w_is0 len] gate, [brk_grants]'
    [old < r], [mremap_model_next]'s already-gated [new_n], and [maps_subtract]
    preserves nonzero-ness), but which the [VmMaps] TYPE admits: the record is
    a bare list of pairs with no well-formedness predicate.  On such a ledger
    [mremap_source_b] ACCEPTS a zero-rounded source, so the [page_align_is0_b
    old_size] gate is the only thing standing between this call and a verdict.
    No live run can see that, and it is
    why [mremap_old_size_zero_aligned_is_unmodeled] above does not pin the gate:
    on its two-page ledger the source gate declines anyway. *)

(** The WRAP half of [Mremap.page_align_is0_b] on the OLD size is redundant
    against [Mremap.mremap_source_b], and this is why: a wrapped round gives
    [old_nZ = 2^64], and the source gate's [alloc_top] bound (under 2^64
    for every ledger, [State.alloc_top_lt]) then fails for EVERY
    [old] and every ledger.  So no trace and no hand-built state can tell
    the two spellings apart — the disjunct is kept because the gate must
    answer for the argument Linux actually rounds, not because the answer
    changes.  Reason 1: a [forall] over every ledger and every address. *)

(** ...and the hypothesis is the wrap: [2^64-1] is the top-partial-page
    argument Linux's [PAGE_ALIGN] sends to zero (mm/mremap.c:1030, v6.12). *)

(** The end-to-end answer, for the record. *)

(** What BOUNDS the one approximation mremap makes on its SUCCESS path
    (see [Mremap.mremap_spec], BOUNDED APPROXIMATION).  A move unmaps the source
    with [do_vmi_munmap] at mm/mremap.c:792 (v6.12), and when that call fails
    Linux SWALLOWS its error (:793-797, "OOM: unable to split vma, just get
    accounts right") and still returns [new_addr] (:817).  So a successful
    Linux mremap can leave the source mapped, while [Mremap.mremap_model_next]
    always drops it.  Such a kernel's address space is therefore the model's
    ledger plus one retained entry [(old, old_n)]; [region_free] does not care
    where in the list it sits, so putting it in front is that kernel's ledger.

    Two things follow, and together they are why the gap costs precision
    and not soundness.  The model really does claim the source gone, so no
    later call can be answered out of it — [Mremap.mremap_source_b] and
    [Mmap.munmap_spec] both go through [map_has], which now fails, i.e.
    fail closed. And the two free sets
    differ EXACTLY on the regions that meet the retained source: everything
    the divergent kernel still considers free the model considers free too,
    so no placement a real kernel makes is ever refused, and the model's
    extra freedom reaches no further than the source range itself.

    Reason 1: a [forall] over every ledger and every candidate region, which
    no finite set of traces can establish — and the divergent kernel it
    quantifies over is one no live run can summon on demand anyway. *)

(* -------------------------------------------------------------------------
   [Run.apply_effect] stage order.

   [apply_effect] (Run.v:172-185) runs four memory stages in a fixed order
   — unmaps, then zeros, then copies, then writes — and every copy source
   is read from the PRE-effect snapshot taken at Run.v:180.
   [mremap_copy_reads_pre_effect_snapshot] above has pairwise-disjoint
   zero, unmap and destination ranges, so it pins the snapshot against the
   unmaps and nothing else: the three remaining adjacencies never show.

   The effects below are HAND-BUILT to overlap one adjacency each; no
   modeled syscall emits them (no spec declares a zero range inside its own
   unmap range, or a write on top of its own copy destination), which is
   why they belong here under reason 3 — model-internal ordering that no
   real execution reveals.  Each states which pair it discriminates, and
   each was chosen so that swapping that pair changes the answer.
   ------------------------------------------------------------------------- *)

(** unmaps BEFORE zeros.  The zero range covers the unmapped range, so the
    byte reads [Some 0]; running zeros first would let the unmap erase them
    and the answer would be [None]. *)

(** zeros BEFORE copies.  The copy destination covers the zero range, so
    the byte reads the copied sentinel; running copies first would leave
    [Some 0]. *)

(** copies BEFORE writes.  The write lands on the copy destination, so the
    byte reads the written value; running writes first would leave the
    copied sentinel [Some 90]. *)

(** unmaps and zeros versus the COPY SOURCE.  The source lies inside both
    a zero range and an unmap range, and the destination outside both, so
    the destination still receives the PRE-effect byte while the source
    itself reads [Some 0].  This is strictly stronger than
    [mremap_copy_reads_pre_effect_snapshot], where the source is only
    unmapped: there, a copy reading live memory would show [None] at the
    destination, whereas here it would show [Some 0], the same value a
    correct zero-fill produces one page away. *)

(* -------------------------------------------------------------------------
   Anonymous PROT_NONE reservations and contained permission transitions.
   [vm_maps] owns/budgets the whole allocation; [vm_noaccess] records only
   the subranges whose machine overlay is absent.

   Reason 3 (MODEL-INTERNAL STATE) covers this whole block, and it is not a
   formality: every example below names the resulting ledger LITERALLY —
   [(65536, 4096); (73728, 4096)] and the like.  A live run cannot do that.
   Placement is environment-chosen ([choose] in [Mmap.mmap_spec], the
   kernel's [get_unmapped_area] on Linux), so a live run
   can only observe that a later call behaves consistently with SOME split,
   never that the split produced exactly these two intervals in this order.
   ------------------------------------------------------------------------- *)

Example mmap_fresh_noaccess_records_both_ledgers :
  check_syscall
    (mkInput 222 [0; 4096; 0; 34; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU 65536 [] [] [(65536, 4096)] [] []) noaccess_base
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull [] [(65536, 4096)] [(65536, 4096)] 0 0 16384 0 demo_sp)
        noaccess_base) [].
Proof. check_eq. Qed.

(** Reason 3.  The fresh no-access effect also erases any old
    writable-overlay byte at a reused address.  Without that erasure, the VM
    ledger would say PROT_NONE while the machine could still load stale
    data left by an earlier allocation.  This is a direct computation on
    [Run.apply_unmaps] over a synthetic overlay — the overlay is model state,
    and no execution exposes it. *)

Example mmap_fresh_noaccess_erases_stale_overlay :
  apply_unmaps stale_overlay [(65536, 4096)] 65536 = None.
Proof. check_eq. Qed.

(** Reason 3.  A contained MAP_FIXED guard changes only [vm_noaccess]:
    [vm_maps] keeps the whole 8192-byte owner and virtual occupancy is
    unchanged, while the protected page stops consuming backed capacity. *)

Example mmap_fixed_noaccess_preserves_owner_and_frees_backing :
  check_syscall
    (mkInput 222 [65536; 4096; 0; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU 65536 [] [] [(65536, 4096)] [] [])
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 8192) noaccess_base)
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull [] [(65536, 8192)] [(65536, 4096)] 0 0 8192 0 demo_sp)
        noaccess_base) [].
Proof. check_eq. Qed.

(* -------------------------------------------------------------------------
   MAP_NORESERVE, and the rw MAP_FIXED COMMIT that completes the
   reserve-then-commit idiom.

   Two claims are load-bearing and neither is reachable from a live run.  The
   first is UNIVERSALLY QUANTIFIED (reason 1): masking MAP_NORESERVE is
   inert for every call that does not set the bit, which is the whole
   argument that programs not using the idiom see an unchanged model.  The
   second is MODEL-INTERNAL STATE (reason 3): the commit must leave
   [vm_maps] untouched while removing exactly its own range from
   [vm_noaccess].  Ordinary backing increases immediately; MAP_NORESERVE keeps
   the slice lazy so [vm_backing_used] grows only as its pages are first
   accessed.  A live run sees usable memory either way; only the ledger
   distinguishes "commit inside what you already own" from "acquire more".
   ------------------------------------------------------------------------- *)

(** The shape tests WITHOUT the MAP_NORESERVE mask:
    an exact equality on the whole flags word.  Kept here, in the QA file,
    so the inertness claim below compares against something rather than
    asserting itself. *)
Definition mmap_modeled_exact_b (prot flags off : word) : bool :=
  Z.eqb (bv_unsigned prot) (PROT_READ + PROT_WRITE)
  && Z.eqb (bv_unsigned flags) (MAP_PRIVATE + MAP_ANONYMOUS)
  && w_is0 off.
Definition mmap_noaccess_exact_b (prot flags off : word) : bool :=
  Z.eqb (bv_unsigned prot) PROT_NONE
  && Z.eqb (bv_unsigned flags) (MAP_PRIVATE + MAP_ANONYMOUS)
  && w_is0 off.
Definition mmap_fixed_noaccess_exact_b (prot flags off : word) : bool :=
  Z.eqb (bv_unsigned prot) PROT_NONE
  && Z.eqb (bv_unsigned flags) (MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED)
  && w_is0 off.

(** Reason 1.  For every [flags] without MAP_NORESERVE set, all three
    masked shape tests answer exactly what the unmasked ones above answer.
    This is the "does the mask alter any binary that does not use the
    pattern" question, settled for the flags half; the other half is
    structural (the commit branch is reached only through
    [Mmap.mmap_fixed_rw_b], which no call of the other shapes matches). *)
Lemma mmap_noreserve_masking_is_inert : forall prot flags off,
  Z.land (bv_unsigned flags) MAP_NORESERVE = 0%Z ->
  mmap_modeled_b prot flags off = mmap_modeled_exact_b prot flags off
  /\ mmap_noaccess_b prot flags off
     = mmap_noaccess_exact_b prot flags off
  /\ mmap_fixed_noaccess_b prot flags off
     = mmap_fixed_noaccess_exact_b prot flags off.
Proof.
  intros prot flags off H.
  unfold mmap_modeled_b, mmap_noaccess_b, mmap_fixed_noaccess_b,
         mmap_modeled_exact_b, mmap_noaccess_exact_b,
         mmap_fixed_noaccess_exact_b.
  rewrite (mmap_flags_core_id flags H). repeat split.
Qed.

(** Reason 4.  ONE bit is masked, not "unknown bits".  MAP_POPULATE
    (0x8000) on the otherwise-modeled rw shape still leaves the modeled
    surface — it asks the kernel to prefault the mapping, which is a
    request about memory the model does not represent. *)
Example mmap_populate_bit_still_unmodeled :
  check_syscall
    (mkInput 222 [0; 4096; 3; 32802; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] [(65536, 4096)]) noaccess_base
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** A PROT_NONE|MAP_NORESERVE reservation occupies virtual space without
    consuming backed capacity.  Its size may therefore exceed [vm_limit]. *)
Example mmap_noreserve_reservation_ignores_backed_budget :
  check_syscall
    (mkInput 222 [0; 8192; 0; 16418; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU 65536 [] [] [(65536, 8192)] [] [])
    (with_vmmaps (mkVmMaps [] [] 0 0 4096) noaccess_base)
  = CheckOk
      (vm_add_lazy 65536 8192
        (with_vmmaps
          (mkVmMapsFull [] [(65536, 8192)] [(65536, 8192)] 0 0 4096 0 demo_sp)
          noaccess_base)) [].
Proof. check_eq. Qed.

(** Reason 3.  …and the same call inside its budget is the ordinary
    reservation, in both ledgers, spelled with the MAP_NORESERVE bit set. *)
Example mmap_noreserve_reservation_within_budget :
  check_syscall
    (mkInput 222 [0; 8192; 0; 16418; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU 65536 [] [] [(65536, 8192)] [] [])
    (with_vmmaps (mkVmMaps [] [] 0 0 8192) noaccess_base)
  = CheckOk
      (vm_add_lazy 65536 8192
        (with_vmmaps
          (mkVmMapsFull [] [(65536, 8192)] [(65536, 8192)] 0 0 8192 0 demo_sp)
          noaccess_base)) [].
Proof. check_eq. Qed.

(** Reason 3.  THE COMMIT.  An rw MAP_FIXED over the first page of an
    8192-byte PROT_NONE reservation: [vm_maps] keeps the whole owner
    INTACT — so virtual occupancy remains 8192 — while [vm_noaccess]
    loses exactly the committed range and backed memory rises by 4096.
    range and keeps the uncommitted tail as [(69632, 4096)].  The bytes
    come back as zeroes ([eff_zeros]), which is what makes the range
    readable to the machine. *)
Example mmap_fixed_rw_commits_inside_reservation :
  check_syscall
    (mkInput 222 [65536; 4096; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] [(65536, 4096)])
    (with_vmmaps
       (mkVmMapsFull [] [(65536, 8192)] [(65536, 8192)] 0 0 8192 0 demo_sp)
       noaccess_base)
  = CheckOk
      (with_mmap_replacement 50 65536 4096
        (with_vmmaps
          (mkVmMapsFull [] [(65536, 8192)] [(69632, 4096)] 0 0 8192 0 demo_sp)
          noaccess_base)) [].
Proof. check_eq. Qed.

(** The commit's two accounts stated directly: virtual occupancy is
    unchanged, while the exposed page consumes backed capacity. *)
Example mmap_fixed_rw_commit_preserves_virtual_bytes :
  vm_live_bytes (mkVmMapsFull [] [(65536, 8192)] [(65536, 8192)] 0 0 8192 0 demo_sp)
  = vm_live_bytes (mkVmMapsFull [] [(65536, 8192)] [(69632, 4096)] 0 0 8192 0 demo_sp).
Proof. check_eq. Qed.

Example mmap_fixed_rw_commit_adds_backed_bytes :
  vm_backed_bytes (mkVmMapsFull [] [(65536, 8192)] [(65536, 8192)] 0 0 8192 0 demo_sp)
  = 0%Z /\
  vm_backed_bytes (mkVmMapsFull [] [(65536, 8192)] [(69632, 4096)] 0 0 8192 0 demo_sp)
  = 4096%Z.
Proof. split; check_eq. Qed.

(** A contained commit is atomic with its backed-budget charge: when the
    newly exposed page would cross the limit, the success is rejected and
    the unchanged errno resolution remains available. *)
Example mmap_fixed_rw_commit_over_backed_budget_rejected :
  check_syscall
    (mkInput 222 [65536; 4096; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] [(65536, 4096)])
    (with_vmmaps
       (mkVmMapsFull [] [(65536, 8192)] [(65536, 8192)] 0 0 2048 0 demo_sp)
       noaccess_base)
  = CheckReject.
Proof. check_eq. Qed.

(** Mixed ranges charge only the newly exposed portion.  The first page is
    already accessible and the second is reserved; replacing both under an
    8192-byte limit succeeds because the resulting state, not the request
    length added to the old total, is what the gate measures. *)
Example mmap_fixed_rw_mixed_commit_charges_exact_delta :
  check_syscall
    (mkInput 222 [65536; 8192; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] [(65536, 8192)])
    (with_vmmaps
       (mkVmMapsFull [] [(65536, 8192)] [(69632, 4096)] 0 0 8192 0 demo_sp)
       noaccess_base)
  = CheckOk
      (with_mmap_replacement 50 65536 8192
        (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 8192)
          noaccess_base)) [].
Proof. check_eq. Qed.

(** Reason 3.  The same call with MAP_NORESERVE also set (flags 16434) is
    the same transition — this is the spelling a runtime that reserved
    with MAP_NORESERVE actually uses when it commits. *)
Example mmap_fixed_rw_noreserve_commits_the_same :
  check_syscall
    (mkInput 222 [65536; 4096; 3; 16434; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] [(65536, 4096)])
    (with_vmmaps
       (mkVmMapsFull [] [(65536, 8192)] [(65536, 8192)] 0 0 8192 0 demo_sp)
       noaccess_base)
  = CheckOk
      (with_mmap_replacement 16434 65536 4096
        (with_vmmaps
          (mkVmMapsFull [] [(65536, 8192)] [(69632, 4096)] 0 0 8192 0 demo_sp)
          noaccess_base)) [].
Proof. check_eq. Qed.

(** Reason 3.  A commit over an ALREADY LIVE rw range is modeled too, and
    it is not a no-op: Linux tears the old mapping down and installs
    fresh anonymous pages, so the range reads back as zeroes.  The
    [eff_zeros] here is what destroys whatever the program had written
    there — the one place this shape differs from [mprotect_spec], which
    short-circuits on an already-rw range and exposes nothing. *)
Example mmap_fixed_rw_over_live_range_rezeroes :
  check_syscall
    (mkInput 222 [65536; 4096; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] [(65536, 4096)])
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 8192) noaccess_base)
  = CheckOk
      (with_mmap_replacement 50 65536 4096
        (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 8192)
          noaccess_base)) [].
Proof. check_eq. Qed.

(** Reason 3.  A range that SPANS two adjacent tracked mappings is
    contained in neither, and Linux replaces both: [vms_gather_munmap_vmas]
    detaches every VMA the request meets and one new mapping goes in over
    the whole of it (mm/vma.c, Linux v6.18.46).  So the two entries
    collapse into the request's one.  Declining here would refute every
    equivalence statement about a program that reaches it. *)
Example mmap_fixed_rw_spanning_two_mappings_replaces_both :
  check_syscall
    (mkInput 222 [65536; 8192; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] [(65536, 8192)])
    (with_vmmaps (mkVmMaps [] [(65536, 4096); (69632, 4096)] 0 0 16384)
       noaccess_base)
  = CheckOk
      (with_mmap_replacement 50 65536 8192
        (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 16384)
          noaccess_base)) [].
Proof. check_eq. Qed.

(** Reason 3.  …and a range that merely OVERLAPS a tracked mapping — the
    last page of an owned range plus one page past its end — keeps the
    part of the entry the request does not reach.  That remnant is
    [__split_vma]'s work, read on the model's intervals as
    [maps_subtract]: [(65536, 8192)] loses its second page and the
    request's own [(69632, 8192)] covers it instead. *)
Example mmap_fixed_rw_partial_overlap_keeps_the_remnant :
  check_syscall
    (mkInput 222 [69632; 8192; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 69632 [] [(69632, 8192)])
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 16384) noaccess_base)
  = CheckOk
      (with_mmap_replacement 50 69632 8192
        (with_vmmaps
          (mkVmMaps [] [(69632, 8192); (65536, 4096)] 0 0 16384)
          noaccess_base)) [].
Proof. check_eq. Qed.

(* -------------------------------------------------------------------------
   MAP_FIXED THAT SPANS — the rest of the arm, both ways

   The two accepts above are the spanning shape.  What follows
   pins the rest of it: the other two resolutions, the answers that are
   NOT admitted, the budget, the PROT_NONE twin, and the one sub-case
   that still declines.

   Reason 3 (model-internal state) for the accepts — every one names the
   resulting ledger literally, and placement is the caller's here so
   there is nothing environment-chosen to observe — and reason 4 for the
   image decline, whose ledger no live run can build.
   ------------------------------------------------------------------------- *)

(** The ledger the spanning cases run against: one 8192-byte mapping at
    65536, and a request that covers its second page and one page past
    its end. *)
Definition span_model : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 16384) noaccess_base.

(** Resolution 1 of 3: the NON-DESTRUCTIVE failure.  [may_expand_vm] gets
    a strictly positive delta here — the request is not wholly mapped
    already — so RLIMIT_AS can refuse this call where it could not refuse
    a contained one (mm/vma.c:2418, Linux v6.18.46).  The gather has
    already set [vms->clear_ptes] (:1497), so the abort reattaches
    (:2357-2358) and the ledger is untouched. *)
Example mmap_fixed_rw_span_errno_preserves_the_range :
  check_syscall
    (mkInput 222 [69632; 8192; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOMEM) [] [])
    span_model
  = CheckOk span_model [].
Proof. check_eq. Qed.

(** Resolution 3 of 3: the DESTRUCTIVE failure.  Past
    [vms_clean_up_area] the abort cannot reattach, so it writes a hole
    over exactly [[addr, addr + len)] (mm/vma.c:2365-2366) — and only
    over that: the remnant at 65536 the split produced is outside the
    request and survives, which is why this is [maps_subtract] and not
    the removal of a whole entry. *)
Example mmap_fixed_rw_span_errno_destroys_only_the_request :
  check_syscall
    (mkInput 222 [69632; 8192; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU (errno_ret ENOMEM) [] [] [(69632, 8192)] [] [])
    span_model
  = CheckOk
      (with_mmap_destroyed 69632 8192
        (mkVmMaps [] [(65536, 4096)] 0 0 16384) span_model) [].
Proof. check_eq. Qed.

(** NEGATIVE, and the one the ABORT path most needs.  A failure may
    leave the range intact or leave it as a hole, and nothing between:
    [vms_abort_munmap_vmas] either reattaches every VMA the gather
    detached (mm/vma.c:2357-2358, calling [reattach_vmas],
    mm/vma.c:1351-1360) or writes NULL over exactly
    [[vms->start, vms->end)] in one store (:2365-2366).  A
    failure announcing an unmap of PART of the request is describing a
    half-replaced ledger no kernel reaches — the state the model would
    have if it applied the gather's tear-down without the abort's
    all-or-nothing restore. *)
Example mmap_fixed_rw_span_errno_partial_unmap_rejected :
  check_syscall
    (mkInput 222 [69632; 8192; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU (errno_ret ENOMEM) [] [] [(69632, 4096)] [] [])
    span_model
  = CheckReject.
Proof. check_eq. Qed.

(** …and the mistake in the other direction, which is the one a model
    that forgot the SPLITS would make: the abort's store covers the
    request, not everything the gather touched, so the remnant at 65536
    is not part of the hole.  A failure claiming it is, is rejected. *)
Example mmap_fixed_rw_span_errno_unmapping_the_remnant_rejected :
  check_syscall
    (mkInput 222 [69632; 8192; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU (errno_ret ENOMEM) [] [] [(65536, 12288)] [] [])
    span_model
  = CheckReject.
Proof. check_eq. Qed.

(** NEGATIVE: no failure exposes bytes.  The same errno with a zero-fill
    attached is rejected, whichever way the range resolved — the
    destructive abort leaves a hole, it does not hand back zeroes. *)
Example mmap_fixed_rw_span_errno_with_zeros_rejected :
  check_syscall
    (mkInput 222 [69632; 8192; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOMEM) [] [(69632, 8192)])
    span_model
  = CheckReject.
Proof. check_eq. Qed.

(** NEGATIVE: the success zeroes the WHOLE request, not just the part
    that was already mapped.  A kernel that exposed only the overlap
    would be leaving the rest of its own new mapping unwritten. *)
Example mmap_fixed_rw_span_partial_zero_fill_rejected :
  check_syscall
    (mkInput 222 [69632; 8192; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 69632 [] [(69632, 4096)])
    span_model
  = CheckReject.
Proof. check_eq. Qed.

(** NEGATIVE: and it unmaps nothing.  [eff_zeros] over the whole request
    already subsumes the tear-down — [Run.apply_effect] materializes
    every byte of it as a defined zero — so a success that ALSO announces
    an unmap is describing a state transition the model does not have. *)
Example mmap_fixed_rw_span_success_with_unmaps_rejected :
  check_syscall
    (mkInput 222 [69632; 8192; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU 69632 [] [(69632, 8192)] [(69632, 8192)] [] [])
    span_model
  = CheckReject.
Proof. check_eq. Qed.

(** The BUDGET, both ways.  The part of the request that met nothing is
    newly owned and Linux charges it
    ([map->charged = map->pglen - vms->nr_accounted], mm/vma.c:2422-2429),
    so the success is available only while the resulting state fits.
    Here the request needs 12288 backed bytes against a 8192-byte
    budget: the success is refused… *)
Definition span_tight_model : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 4096)] 0 0 8192) noaccess_base.

Example mmap_fixed_rw_span_over_budget_rejected :
  check_syscall
    (mkInput 222 [65536; 12288; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] [(65536, 12288)])
    span_tight_model
  = CheckReject.
Proof. check_eq. Qed.

(** …and the errno resolution is what remains, which is the forced
    out-of-memory point rather than a decline. *)
Example mmap_fixed_rw_span_over_budget_errno_admitted :
  check_syscall
    (mkInput 222 [65536; 12288; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOMEM) [] [])
    span_tight_model
  = CheckOk span_tight_model [].
Proof. check_eq. Qed.

(** THE PROT_NONE TWIN.  Same ledger, same request, prot 0: the request
    is owned and inaccessible, the remnant survives, and the effect is
    an unmap rather than a zero-fill. *)
Example mmap_fixed_noaccess_span_reserves_the_request :
  check_syscall
    (mkInput 222 [69632; 8192; 0; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU 69632 [] [] [(69632, 8192)] [] [])
    span_model
  = CheckOk
      (with_mmap_replacement 50 69632 8192
        (with_vmmaps
          (mkVmMapsFull [] [(69632, 8192); (65536, 4096)]
            [(69632, 8192)] 0 0 16384 0 demo_sp)
          span_model)) [].
Proof. check_eq. Qed.

(** …with no budget gate, and this is why: the request lands in
    [vm_noaccess] whole, so [State.vm_backed_maps] cuts it out and the
    backed total can only FALL.  Ownership grows by the page that met
    nothing; backing drops by the page that was accessible. *)
Example mmap_fixed_noaccess_span_owns_more_and_backs_less :
  vm_live_bytes (mkVmMaps [] [(65536, 8192)] 0 0 16384) = 8192%Z
  /\ vm_live_bytes
       (mkVmMapsFull [] [(69632, 8192); (65536, 4096)]
          [(69632, 8192)] 0 0 16384 0 demo_sp) = 12288%Z
  /\ vm_backed_bytes (mkVmMaps [] [(65536, 8192)] 0 0 16384) = 8192%Z
  /\ vm_backed_bytes
       (mkVmMapsFull [] [(69632, 8192); (65536, 4096)]
          [(69632, 8192)] 0 0 16384 0 demo_sp) = 4096%Z.
Proof. repeat split; check_eq. Qed.

(** …and its destructive failure, which drops the request from BOTH
    ledgers. *)
Example mmap_fixed_noaccess_span_errno_destroys_only_the_request :
  check_syscall
    (mkInput 222 [69632; 8192; 0; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU (errno_ret ENOMEM) [] [] [(69632, 8192)] [] [])
    span_model
  = CheckOk
      (with_mmap_destroyed 69632 8192
        (mkVmMaps [] [(65536, 4096)] 0 0 16384) span_model) [].
Proof. check_eq. Qed.

(** …and its abort is all-or-nothing in the same way: a PROT_NONE
    failure that unmaps only part of the request is rejected too, so the
    pin is on the arm rather than on [prot]. *)
Example mmap_fixed_noaccess_span_errno_partial_unmap_rejected :
  check_syscall
    (mkInput 222 [69632; 8192; 0; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU (errno_ret ENOMEM) [] [] [(69632, 4096)] [] [])
    span_model
  = CheckReject.
Proof. check_eq. Qed.

(** NEGATIVE for the PROT_NONE twin: it exposes nothing, so a success
    carrying a zero-fill is rejected. *)
Example mmap_fixed_noaccess_span_success_with_zeros_rejected :
  check_syscall
    (mkInput 222 [69632; 8192; 0; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 69632 [] [(69632, 8192)])
    span_model
  = CheckReject.
Proof. check_eq. Qed.

(* ---- what the contained arm keeps that the spanning arm does not ---- *)

(** A contained request is NOT re-cut, and that is deliberate: Linux
    leaves such a VMA whole apart from the splits, and
    [State.map_contains] — which [Mprotect.mprotect_spec] and the
    contained MAP_FIXED shapes all gate on — asks whether ONE entry
    covers a range.  Fragmenting here would narrow their modeled surface
    on a later call for no gain.  This pins that the contained arm is
    the one that runs: [vm_maps] still holds the single [(65536, 8192)]
    entry afterwards. *)
Definition contained_h : VmMaps :=
  mkVmMapsFull [] [(65536, 8192)] [(65536, 8192)] 0 0 16384 0 demo_sp.

Example mmap_fixed_contained_stays_unfragmented :
  check_syscall
    (mkInput 222 [65536; 4096; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] [(65536, 4096)])
    (with_vmmaps contained_h noaccess_base)
  = CheckOk
      (with_mmap_replacement 50 65536 4096
        (with_vmmaps
          (mkVmMapsFull [] [(65536, 8192)] [(69632, 4096)] 0 0 16384 0 demo_sp)
          noaccess_base)) [].
Proof. check_eq. Qed.

(** …and the two forms are the same claim about memory, which is what
    makes keeping both honest rather than a second answer: on the same
    pre-state and request the spanning post-state owns the same number
    of bytes and backs the same number of bytes as the contained one.
    Only the cut differs. *)
Example mmap_fixed_span_agrees_with_contained_on_backing :
  live_bytes (vm_maps (mmap_fixed_rw_span_next contained_h 65536 4096))
    = live_bytes (vm_maps (mmap_fixed_rw_next contained_h 65536 4096))
  /\ live_bytes (vm_backed_maps (mmap_fixed_rw_span_next contained_h 65536 4096))
    = live_bytes (vm_backed_maps (mmap_fixed_rw_next contained_h 65536 4096))
  /\ vm_maps (mmap_fixed_rw_span_next contained_h 65536 4096)
    <> vm_maps (mmap_fixed_rw_next contained_h 65536 4096).
Proof.
  split; [check_eq|]. split; [check_eq|]. cbn. discriminate.
Qed.

(* ---- the one sub-case that still declines ---- *)

(** Reason 4.  A MAP_FIXED that reaches the image's LOAD reservations is
    [unmodeled], and stays that way.  Linux would replace those pages
    like any others; the model cannot, because its image bytes are not
    in this ledger — they are the [State.Image] segments the fetch and
    the memory overlay read — so replacing part of one here would leave
    the ledger and the machine disagreeing about what the process can
    execute.  The [vm_reserved] arm of [Mmap.mmap_spec] carries the
    argument and what the decline costs. *)
Definition image_span_model : Model :=
  with_vmmaps
    (mkVmMapsFull [(65536, 4096)] [(69632, 4096)] [] 0 0 16384 0 demo_sp)
    noaccess_base.

Example mmap_fixed_rw_over_the_image_is_unmodeled :
  check_syscall
    (mkInput 222 [65536; 8192; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] [(65536, 8192)])
    image_span_model
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** …and the PROT_NONE spelling of the same request declines too, so the
    gate is on the ledger rather than on [prot]. *)
Example mmap_fixed_noaccess_over_the_image_is_unmodeled :
  check_syscall
    (mkInput 222 [65536; 8192; 0; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU 65536 [] [] [(65536, 8192)] [] [])
    image_span_model
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** Reason 4.  The decline is on the ARM, not on the resolution.  Both
    declines above offer a success; this one offers a plain errno with
    the range untouched — the answer the spanning arm's FIRST resolution
    gives for any other ledger, and the one a model that gated the
    reservation test on the success path alone would wave through.  The
    guard sits above the [alt], so there is no resolution to reach and
    the answer is [CheckUnmodeled] rather than [CheckOk]. *)
Example mmap_fixed_rw_over_the_image_errno_is_unmodeled :
  check_syscall
    (mkInput 222 [65536; 8192; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOMEM) [] [])
    image_span_model
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** THE TIGHT ANCHOR that keeps those two declines from being
    reject-everything: the same ledger, the same shape, one page higher
    so the request clears the reservation — and it is answered. *)
Example mmap_fixed_rw_clear_of_the_image_replaces :
  check_syscall
    (mkInput 222 [69632; 8192; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 69632 [] [(69632, 8192)])
    image_span_model
  = CheckOk
      (with_mmap_replacement 50 69632 8192
        (with_vmmaps
          (mkVmMapsFull [(65536, 4096)] [(69632, 8192)] [] 0 0 16384 0 demo_sp)
          image_span_model)) [].
Proof. check_eq. Qed.

(** Reason 4.  The commit exposes EXACTLY the range it was asked for.  A
    kernel claiming to have zeroed the whole 8192-byte owner in answer to
    a 4096-byte request is rejected, not accepted as an over-delivery. *)
Example mmap_fixed_rw_wider_zero_fill_rejected :
  check_syscall
    (mkInput 222 [65536; 4096; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] [(65536, 8192)])
    (with_vmmaps
       (mkVmMapsFull [] [(65536, 8192)] [(65536, 8192)] 0 0 8192 0 demo_sp)
       noaccess_base)
  = CheckReject.
Proof. check_eq. Qed.

(** Reason 4.  The SUCCESS unmaps nothing.  [eff_zeros] already makes
    every covered byte defined, so a success that also announced an unmap
    would be describing a different transition — rejected. *)
Example mmap_fixed_rw_success_with_unmap_rejected :
  check_syscall
    (mkInput 222 [65536; 4096; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU 65536 [] [(65536, 4096)] [(65536, 4096)] [] [])
    (with_vmmaps
       (mkVmMapsFull [] [(65536, 8192)] [(65536, 8192)] 0 0 8192 0 demo_sp)
       noaccess_base)
  = CheckReject.
Proof. check_eq. Qed.

(** Reason 3.  THE DESTRUCTIVE FAILURE, which is the resolution a
    MAP_FIXED has and an [mprotect] does not: an allocation failure past
    [vms_clean_up_area] returns an errno AND leaves a hole.  The range
    goes from both ledgers — so its bytes return to the budget, the owner
    splitting into the two remnants — and the effect announces the unmap,
    which is what makes a later load from the hole fault. *)
Example mmap_fixed_rw_destructive_failure_leaves_a_hole :
  check_syscall
    (mkInput 222 [69632; 4096; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU (errno_ret ENOMEM) [] [] [(69632, 4096)] [] [])
    (with_vmmaps (mkVmMaps [] [(65536, 12288)] 0 0 16384) noaccess_base)
  = CheckOk
      (with_mmap_destroyed 69632 4096
        (mkVmMaps [] [(65536, 4096); (73728, 4096)] 0 0 16384)
        noaccess_base) [].
Proof. check_eq. Qed.

(** Reason 1.  THE FRESH MAP_FIXED SUB-CASE ADDS NO REACHABLE TRANSITION.
    Under the guards that sub-case tests, the effect and post-state it
    produces are ones the HINT-PLACED rw shape already produces from the
    same pre-state — for any hint at all, since without MAP_FIXED an
    address argument is only a hint and the model's placement [choose]
    is always free to land on [addr].  So the widening is in which
    argument words reach the transition, never in the set of transitions:
    no state becomes reachable that the hint-placed shape does not reach,
    and every invariant that holds of that shape's post-states holds of
    these unchanged.

    This is the strongest soundness argument any of the four shapes has,
    and it is why the sub-case is here rather than left fail-closed: it
    is a [forall] over admissible outcomes, which is reason 1's whole
    category and which no trace can establish. *)
Lemma mmap_fixed_fresh_adds_no_transition :
  forall hint addr len i m,
    w_is0 hint = false ->
    w_is0 len = false ->
    (bv_unsigned addr mod page_size = 0)%Z ->
    (0 < bv_unsigned addr)%Z ->
    (bv_unsigned addr + page_round_up_Z (bv_unsigned len) <= alloc_top (m_vmmaps m))%Z ->
    region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr
      (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true ->
    mmap_noreserve_backed_ok 34 m (page_round_up_Z (bv_unsigned len)) = true ->
    mmap_spec hint len 3 34 mmap_fd_none 0 i m
      (Ok (mkEffect addr []
             [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])
          (with_mmap_backing 34 addr
             (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
           (with_vmmaps
             (mkVmMapsFull (vm_reserved (m_vmmaps m))
                ((addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
                   :: vm_maps (m_vmmaps m))
                (vm_noaccess (m_vmmaps m)) (vm_start_brk (m_vmmaps m))
                (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m))
                (vm_init_sp (m_vmmaps m))) m)) []).
Proof.
  intros hint addr len i m Hhint Hl Halign Hpos Hceil Hfree Hbud.
  unfold mmap_spec. rewrite Hl. cbn [mmap_modeled_b].
  apply alt_r.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
  eapply bind_ok0.
  { apply (choose_ok _ addr). cbv beta. repeat split; assumption. }
  eapply bind_ok0; [apply modify_ok|].
  apply pure_ok.
Qed.

(** Reason 1.  The PROT_NONE MAP_FIXED branch carries the same free-range
    sub-case, and it is the same argument again: under those guards the
    effect and post-state are ones [mmap_noaccess_b] already produces from
    the same pre-state, for any hint.  Leaving this out would be an
    asymmetry rather than a decision — a sanitizer runtime fills the gap
    between its two shadow regions with exactly this call. *)
Lemma mmap_fixed_noaccess_fresh_adds_no_transition :
  forall hint addr len i m,
    w_is0 hint = false ->
    w_is0 len = false ->
    (bv_unsigned addr mod page_size = 0)%Z ->
    (0 < bv_unsigned addr)%Z ->
    (bv_unsigned addr + page_round_up_Z (bv_unsigned len) <= alloc_top (m_vmmaps m))%Z ->
    region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr
      (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true ->
    mmap_spec hint len 0 34 mmap_fd_none 0 i m
      (Ok (mkEffectU addr [] []
             [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))] [] [])
          (with_vmmaps
             (mkVmMapsFull (vm_reserved (m_vmmaps m))
                ((addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
                   :: vm_maps (m_vmmaps m))
                ((addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
                   :: vm_noaccess (m_vmmaps m))
                (vm_start_brk (m_vmmaps m))
                (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m))
                (vm_init_sp (m_vmmaps m))) m) []).
Proof.
  intros hint addr len i m Hhint Hl Halign Hpos Hceil Hfree.
  unfold mmap_spec. rewrite Hl. cbn [mmap_modeled_b mmap_noaccess_b].
  apply alt_r.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
  eapply bind_ok0.
  { apply (choose_ok _ addr). cbv beta. repeat split; assumption. }
  eapply bind_ok0; [apply modify_ok|].
  apply pure_ok.
Qed.

(** Reason 3.  …and the transition on a concrete ledger: a PROT_NONE
    MAP_FIXED whose range meets nothing lands in BOTH ledgers, exactly as
    a hint-placed reservation does. *)
Example mmap_fixed_noaccess_fresh_reserves :
  check_syscall
    (mkInput 222 [65536; 8192; 0; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU 65536 [] [] [(65536, 8192)] [] [])
    (with_vmmaps (mkVmMaps [] [] 0 0 8192) noaccess_base)
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull [] [(65536, 8192)] [(65536, 8192)] 0 0 8192 0 demo_sp)
        noaccess_base) [].
Proof. check_eq. Qed.

(** A fresh fixed PROT_NONE reservation also consumes no backed budget. *)
Example mmap_fixed_noaccess_fresh_ignores_backed_budget :
  check_syscall
    (mkInput 222 [65536; 8192; 0; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU 65536 [] [] [(65536, 8192)] [] [])
    (with_vmmaps (mkVmMaps [] [] 0 0 4096) noaccess_base)
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull [] [(65536, 8192)] [(65536, 8192)] 0 0 4096 0 demo_sp)
        noaccess_base) [].
Proof. check_eq. Qed.

(** Reason 3.  …and the transition itself, on a concrete ledger: a
    fresh read-write MAP_FIXED is recorded and charged like any other
    accessible grant. *)
Example mmap_fixed_rw_fresh_grants_and_charges :
  check_syscall
    (mkInput 222 [65536; 4096; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] [(65536, 4096)])
    (with_vmmaps (mkVmMaps [] [] 0 0 8192) noaccess_base)
  = CheckOk
      (with_vmmaps (mkVmMaps [] [(65536, 4096)] 0 0 8192) noaccess_base) [].
Proof. check_eq. Qed.

(** Reason 4.  …and it is metered: the same call against a budget that
    cannot take it admits only the errno branch. *)
Example mmap_fixed_rw_fresh_over_budget_rejected :
  check_syscall
    (mkInput 222 [65536; 4096; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] [(65536, 4096)])
    (with_vmmaps (mkVmMaps [] [] 0 0 2048) noaccess_base)
  = CheckReject.
Proof. check_eq. Qed.

(** Reason 4.  Address 0 is NOT a fresh grant.  It is page-aligned, so
    the argument gate lets it through, and Linux answers -EPERM there
    ([cap_mmap_addr] below [dac_mmap_min_addr]).  The model does not
    model -EPERM, so the call fails closed rather than being granted. *)
Example mmap_fixed_rw_fresh_at_zero_is_unmodeled :
  check_syscall
    (mkInput 222 [0; 4096; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] [(0, 4096)])
    (with_vmmaps (mkVmMaps [] [] 0 0 8192) noaccess_base)
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** Reason 4.  …AND NEITHER IS A COMMIT AT 0.  Linux's -EPERM comes from
    [security_mmap_addr] on the address it is about to return, which does
    not consult the ledger at all, so a MAP_FIXED at 0 over a range the
    model DOES own is refused exactly as one over free space is.  That is
    why the gate sits above the containment test rather than inside the
    fresh sub-case: were it inside, a state owning address 0 would let the
    model answer a success no kernel produces. *)
Example mmap_fixed_rw_commit_at_zero_is_unmodeled :
  check_syscall
    (mkInput 222 [0; 4096; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] [(0, 4096)])
    (with_vmmaps (mkVmMaps [] [(0, 8192)] 0 0 8192) noaccess_base)
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** Reason 4.  The PROT_NONE half answers the same, through the same
    gate. *)
Example mmap_fixed_noaccess_at_zero_is_unmodeled :
  check_syscall
    (mkInput 222 [0; 4096; 0; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU 0 [] [] [(0, 4096)] [] [])
    (with_vmmaps (mkVmMaps [] [(0, 8192)] 0 0 8192) noaccess_base)
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** 0xdfff0001000 = 15392894357504 bytes (14.00 TiB) is
    AddressSanitizer's shadow reservation on a 48-bit address space, and
    it arrives as exactly the PROT_NONE|MAP_NORESERVE shape the masking
    above matches.  It occupies virtual address space but consumes no
    backed budget, so the Sv48-sized reservation is admissible even with
    the ordinary target backed-memory limit. *)
Example asan_sized_reservation_is_admitted :
  check_syscall
    (mkInput 222 [0; 15392894357504; 0; 16418; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU 65536 [] [] [(65536, 15392894357504)] [] [])
    (with_vmmaps (mkVmMaps [] [] 0 0 target_alloc_limit) noaccess_base)
  = CheckOk
      (vm_add_lazy 65536 15392894357504
        (with_vmmaps
          (mkVmMapsFull [] [(65536, 15392894357504)]
            [(65536, 15392894357504)] 0 0 target_alloc_limit 0 demo_sp)
          noaccess_base)) [].
Proof. check_eq. Qed.

(** Reason 4.  …and the outcome that IS admissible for it is the errno,
    which is the same answer the machine gives. *)
Example asan_sized_reservation_admits_enomem :
  check_syscall
    (mkInput 222 [0; 15392894357504; 0; 16418; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU (errno_ret ENOMEM) [] [] [] [] [])
    (with_vmmaps (mkVmMaps [] [] 0 0 target_alloc_limit) noaccess_base)
  = CheckOk
      (with_vmmaps (mkVmMaps [] [] 0 0 target_alloc_limit) noaccess_base) [].
Proof. check_eq. Qed.

(** Reason 4.  A FAILURE never exposes bytes: the same errno with a
    zero-fill attached is rejected, whichever way the range resolved. *)
Example mmap_fixed_rw_failure_with_zeros_rejected :
  check_syscall
    (mkInput 222 [65536; 4096; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOMEM) [] [(65536, 4096)])
    (with_vmmaps
       (mkVmMapsFull [] [(65536, 8192)] [(65536, 8192)] 0 0 8192 0 demo_sp)
       noaccess_base)
  = CheckReject.
Proof. check_eq. Qed.

(* -------------------------------------------------------------------------
   mmap's ARGUMENT GATE and its FAILURE SHAPES.

   None of this is reachable from a live run: a real kernel cannot be made
   to fail a MAP_FIXED (the last reason listed at the top of
   [Checks/Examples.v] — the environment cannot be made to produce the
   outcome), and an argument combination the model declines has no
   verdict to check.  Line numbers are Linux v6.12.
   ------------------------------------------------------------------------- *)

(** A length whose page round-up leaves the address space is -ENOMEM, and
    that -ENOMEM BEATS the -EINVAL an unaligned addr would otherwise earn:
    [do_mmap] rounds the length and answers -ENOMEM on the wrap
    (mm/mmap.c:315-317) before [__get_unmapped_area] ever reaches
    [offset_in_page] (mm/mmap.c:917-918). *)

Example mmap_fixed_overflowing_len_is_enomem :
  check_syscall
    (mkInput 222 [4097; 18446744073709551615; 0; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOMEM) [] []) noaccess_base
  = CheckOk noaccess_base [].
Proof. check_eq. Qed.

(** The negative: -EINVAL on that same call is the wrong errno, and the
    model must say so rather than accept it. *)

Example mmap_fixed_overflowing_len_rejects_einval :
  check_syscall
    (mkInput 222 [4097; 18446744073709551615; 0; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) noaccess_base
  = CheckReject.
Proof. check_eq. Qed.

(** Below the model's ceiling an unaligned MAP_FIXED addr IS -EINVAL. *)

Example mmap_fixed_unaligned_below_ceiling_is_einval :
  check_syscall
    (mkInput 222 [4097; 4096; 0; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) noaccess_base
  = CheckOk noaccess_base [].
Proof. check_eq. Qed.

(** Above it — [demo_sp + 1], a stack's width past [demo_top] and still
    far under [State.TASK_SIZE], so Linux's own answer is this same
    -EINVAL — the arm declines: its range ends past this run's
    [alloc_top], inside the stack band the ledger does not describe, and
    the arm fails closed there rather than answer for it. *)

Example mmap_fixed_unaligned_above_ceiling_is_unmodeled :
  check_syscall
    (mkInput 222 [140735340871681; 4096; 0; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) noaccess_base
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** A zero length is -EINVAL only once the call is plainly anonymous.
    [ksys_mmap_pgoff] inspects the FLAGS first (mm/mmap.c:511-515,
    :522-540); [do_mmap]'s [if (!len)] is downstream of both arms
    (mm/mmap.c:294-295). *)

Example mmap_zero_len_anonymous_is_einval :
  check_syscall
    (mkInput 222 [0; 0; 3; 34; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) noaccess_base
  = CheckOk noaccess_base [].
Proof. check_eq. Qed.

(** A base model holding a REGULAR file open read-only at fd 3, for the
    file-backed cases below.  Nothing else about it differs from
    [noaccess_base]: the point is only that [fd_lookup] resolves, so a
    decline cannot be mistaken for the model simply not knowing the fd. *)

Definition mmap_file_model : Model :=
  with_fs [([102], [104; 105; 106; 107])]
    (with_fds
      ((Z_to_bv 64 3, FdFile [102] (Z_to_bv 64 0)) :: m_fds noaccess_base)
      noaccess_base).

(** The negative, twice.  MAP_ANONYMOUS clear is the file-backed path and
    every call on it declines, so no errno presented there conforms --
    not the -EINVAL of a zero length, and not the -EBADF Linux really
    gives for a closed fd (mm/mmap.c:511-515), which [Mmap.mmap_spec]'s
    file-backed branch explains why it does not claim. *)

Example mmap_zero_len_file_backed_is_unmodeled :
  check_syscall
    (mkInput 222 [0; 0; 3; 2; 999; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) noaccess_base
  = CheckUnmodeled.
Proof. check_eq. Qed.

Example mmap_file_backed_closed_fd_ebadf_is_unmodeled :
  check_syscall
    (mkInput 222 [0; 4096; 1; 2; 999; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EBADF) [] []) noaccess_base
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** A LIVE fd is the same decline, at the two prots that matter.  fd 3
    holds a regular file here, so the arm is reached with everything a
    real private file mapping has; PROT_READ is the shape the machine
    model cannot encode at all, and PROT_READ|PROT_WRITE is the one it
    could encode and still declines, because nothing ties the mapping to
    [m_fs] (see [Mmap.mmap_spec]). *)

Example mmap_private_file_read_is_unmodeled :
  check_syscall
    (mkInput 222 [0; 4096; 1; 2; 3; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] [(65536, 4096)]) mmap_file_model
  = CheckUnmodeled.
Proof. check_eq. Qed.

Example mmap_private_file_rw_is_unmodeled :
  check_syscall
    (mkInput 222 [0; 4096; 3; 2; 3; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] [(65536, 4096)]) mmap_file_model
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** The offset gate runs ahead of all of it, so a MISALIGNED offset is
    -EINVAL even on the file-backed path riscv never lets reach generic
    mm (arch/riscv/kernel/sys_riscv.c, [riscv_sys_mmap]). *)

Example mmap_misaligned_offset_is_einval :
  check_syscall
    (mkInput 222 [0; 4096; 1; 2; 999; 1]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) noaccess_base
  = CheckOk noaccess_base [].
Proof. check_eq. Qed.

(** Its negative: -EBADF is the answer one page-offset later, and is not
    admissible here. *)

Example mmap_misaligned_offset_ebadf_is_rejected :
  check_syscall
    (mkInput 222 [0; 4096; 1; 2; 999; 1]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EBADF) [] []) noaccess_base
  = CheckReject.
Proof. check_eq. Qed.

(** The same gate on the ordinary anonymous rw shape, which the length
    and shape tests would otherwise have admitted. *)

Example mmap_anonymous_misaligned_offset_is_einval :
  check_syscall
    (mkInput 222 [0; 4096; 3; 34; mmap_fd_none; 2048]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) noaccess_base
  = CheckOk noaccess_base [].
Proof. check_eq. Qed.

(** And the one misaligned-offset shape the gate does NOT answer: a
    length within a page of 2^64 rounds to zero in the kernel's own
    arithmetic, and qemu-user reaches the call in the other order --
    -ENOMEM from [target_mmap]'s length check, measured on
    qemu-riscv64, against the kernel's -EINVAL.  The model declines;
    [Mmap.mmap_pglen_ok_b] carries the argument.  2^64 - 1 is the
    length here; 2^64 - 4096 rounds to itself and is answered by the
    case above it. *)

Example mmap_misaligned_offset_wrapping_len_is_unmodeled :
  check_syscall
    (mkInput 222 [0; 18446744073709551615; 1; 2; 999; 1]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) noaccess_base
  = CheckUnmodeled.
Proof. check_eq. Qed.

Example mmap_misaligned_offset_page_len_is_einval :
  check_syscall
    (mkInput 222 [0; 18446744073709547520; 1; 2; 999; 1]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) noaccess_base
  = CheckOk noaccess_base [].
Proof. check_eq. Qed.

(** ...and with MAP_HUGETLB the hugetlbfs setup answers first
    (mm/mmap.c:522-540). *)

Example mmap_zero_len_hugetlb_is_unmodeled :
  check_syscall
    (mkInput 222 [0; 0; 3; 262178; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) noaccess_base
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** Linux ignores [fd] entirely for an anonymous mapping (mm/mmap.c:511),
    and so does the model: the shape predicates do not read it, so the
    grant is admitted for any [fd], open or not.  This is the widening
    [Mmap.mmap_fd_none] describes; the value 3 here is an fd the base
    model does not hold, and 0 below is one it does. *)

Example mmap_anonymous_other_fd_grants :
  check_syscall
    (mkInput 222 [0; 4096; 3; 34; 3; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] [(65536, 4096)]) noaccess_base
  = CheckOk
      (with_vmmaps (mkVmMapsFull [] [(65536, 4096)] [] 0 0 16384 0 demo_sp)
        noaccess_base) [].
Proof. check_eq. Qed.

Example mmap_anonymous_live_fd_grants :
  check_syscall
    (mkInput 222 [0; 4096; 3; 34; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] [(65536, 4096)]) noaccess_base
  = CheckOk
      (with_vmmaps (mkVmMapsFull [] [(65536, 4096)] [] 0 0 16384 0 demo_sp)
        noaccess_base) [].
Proof. check_eq. Qed.

(** The negative that keeps the widening from being a hole: it widens
    the SHAPE match and nothing else, so a grant that lands somewhere the
    placement guard refuses is still rejected with a stray fd, exactly as
    it is with -1.  65536 is free here; 0 is not a legal placement. *)

Example mmap_anonymous_other_fd_bad_placement_is_rejected :
  check_syscall
    (mkInput 222 [0; 4096; 3; 34; 3; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 0 [] [(0, 4096)]) noaccess_base
  = CheckReject.
Proof. check_eq. Qed.

(** Same for the offset: Linux requires only page alignment
    (arch/riscv/kernel/sys_riscv.c:16-17) and then ignores the page offset
    for anonymous memory (mm/mmap.c:897-899, :471-476). *)

Example mmap_anonymous_page_aligned_offset_is_unmodeled :
  check_syscall
    (mkInput 222 [0; 4096; 3; 34; mmap_fd_none; 4096]
      (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] [(65536, 4096)]) noaccess_base
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** A failed MAP_FIXED has TWO shapes.  Past [vms_clean_up_area]
    (mm/vma.c:1281-1293, called from [__mmap_prepare] at :2441, Linux
    v6.18.46) the old range is already torn down, so the abort at
    mm/vma.c:2729-2730 takes the destructive branch and deliberately
    leaves a gap ([vms_abort_munmap_vmas], mm/vma.c:2365-2366): the errno
    comes back with the range UNMAPPED and carved out of both ledgers,
    leaving the tail of the enclosing mapping behind. *)

Example mmap_fixed_errno_may_destroy_the_range :
  check_syscall
    (mkInput 222 [65536; 4096; 0; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU (errno_ret ENOMEM) [] [] [(65536, 4096)] [] [])
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 8192) noaccess_base)
  = CheckOk
      (with_vmmaps (mkVmMapsFull [] [(69632, 4096)] [] 0 0 8192 0 demo_sp)
        noaccess_base) [].
Proof. check_eq. Qed.

(** The same call may equally preserve the range — that is the -ENOMEM of
    [vms_gather_munmap_vmas] (mm/vma.c:1389-1393, Linux v6.18.46), which
    is tested before any split and returns through [__mmap_prepare]
    (mm/vma.c:2436-2440), whose gather-error arm zeroes [vms->nr_pages]
    so that [vms_abort_munmap_vmas] (:2354-2355) tears nothing down. *)

Example mmap_fixed_errno_may_preserve_the_range :
  check_syscall
    (mkInput 222 [65536; 4096; 0; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOMEM) [] [])
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 8192) noaccess_base)
  = CheckOk (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 8192)
              noaccess_base) [].
Proof. check_eq. Qed.

(** The negative: the gap Linux leaves is exactly the requested range.  An
    errno that unmaps the whole enclosing mapping is not a failure shape
    the abort path can produce. *)

Example mmap_fixed_errno_unmap_must_be_the_request :
  check_syscall
    (mkInput 222 [65536; 4096; 0; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU (errno_ret ENOMEM) [] [] [(65536, 8192)] [] [])
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 8192) noaccess_base)
  = CheckReject.
Proof. check_eq. Qed.

(** Reason 3.  Enabling the MIDDLE page of a three-page reservation splits
    the no-access interval into exactly two remnants, in this order.
    The shape of [maps_subtract]'s output is reachable only
    here, because a live run cannot name the kernel's chosen base. *)

(** Reason 3.  A failed enable leaves BOTH ledgers exactly as they were, so
    the allocator's retry sees the same state.  The observable
    consequence is that a second mprotect still succeeds;
    the claim here is the stronger one — the model state is IDENTICAL, not
    merely compatible — and identity of a literal ledger is not observable. *)

(** Reason 3, and reason 4 in the direction that matters.  A forged 0 over a
    range in NEITHER ledger is [CheckUnmodeled]: the state gate is consulted
    before the return value, so no answer rescues an untracked range.  Linux
    would say -ENOMEM here (v6.12 [mm/mprotect.c] [do_mprotect_pkey], L753
    `error = -ENOMEM;` and L765-766 `if (vma->vm_start > start) goto out;`),
    which is why the model declining is fail-closed rather than wrong.
    This states it at a ledger a live run cannot build. *)

(** Reason: the environment cannot produce it.  Re-protecting an
    already-rw range CANNOT fail on Linux — [mprotect_fixup] returns 0 at
    [newflags == oldflags] before any allocation, split or accounting
    (Linux v6.12, mm/mprotect.c:617-620) — so a kernel answering -ENOMEM
    here is behaving inadmissibly and the model must say so.  This is the
    negative half of that branch having no errno alternative: with such an
    alternative in [Mprotect.mprotect_spec] the verdict would be
    [CheckOk] and the lie would go unnoticed. *)

(** Reason: it pins model-internal state no execution reveals.  Outside the
    documented final-page tail of a byte-granular brk shrink, [State.v]
    purpose (c) says [vm_noaccess] is owned by [vm_maps]; that holds on
    every reachable state ([Checks.NoaccessOwned.star_preserves_sys_inv]),
    but this state is built by hand.  A ledger with no owner at all must not let mprotect return
    0 and zero-fill a range the model does
    not own — Linux answers -ENOMEM for a range starting outside every VMA
    (Linux v6.12, mm/mprotect.c:753, :765-766) — so the exposure branch
    tests both ledgers and this state falls through to fail-closed. *)

(** Reason: the environment cannot produce a verdict on it.  [addr] = 2^63
    with [len] = 2^63 page-rounds to 2^63, so the sum reaches exactly 2^64
    and Linux's [end = start + len] wraps to 0: [end <= start] holds and
    the answer is -ENOMEM (v6.12 [mm/mprotect.c] [do_mprotect_pkey],
    L731-734).  This Rocq pair
    pins the exact 2^63 + 2^63 boundary and rejects a forged
    success.

    The pair also pins that the gate is a GATE.  A test of only whether
    the page rounding alone overflowed ([2^64 <= nZ]) does not fire at
    2^63, so this call would fall through to the containment check and
    be answered [CheckUnmodeled] — weaker than the -ENOMEM Linux
    guarantees, and it would not reject a kernel returning 0. *)

(** Gate ordering against an unsupported permission: the wrapping-range
    -ENOMEM is decided before [PROT_EXEC] is validated, so this remains a
    modeled deterministic error rather than falling through to fail-closed. *)

(** Alignment precedes the zero-length fast return: even though no page
    would change, an unaligned start deterministically returns -EINVAL. *)

(** The grows conflict fires on BOTH stack-extension bits together, never
    on either one alone: Linux v6.12 mm/mprotect.c [do_mprotect_pkey] latches
    [grows = prot & (PROT_GROWSDOWN|PROT_GROWSUP)] (:715) and returns
    -EINVAL only for [grows == (PROT_GROWSDOWN|PROT_GROWSUP)] (:724-725).
    A single bit survives that gate, is masked out of [prot] (:723), and
    at zero length reaches the `if (!len) return 0` at :729-730.

    The three calls below differ in NOTHING but the grow bits — same
    page-aligned start, same zero length, same PROT_READ|PROT_WRITE
    underneath — so each one is decided by the conflict gate alone.  They
    are what makes [Mprotect.mprotect_grows_conflict_b] a conjunction rather
    than a nonzero test on the two-bit mask: a predicate firing on either
    bit would answer -EINVAL for the first two, where Linux answers 0.
    The three are pinned side by side
    here so the conjunction shape stays visible. *)

(** The negative half, and the one an either-bit predicate would accept: a
    kernel reporting -EINVAL for a lone PROT_GROWSDOWN is behaving
    inadmissibly and the model must say so. *)

(** Both bits together, at the same aligned start and zero length: the
    conflict gate precedes the zero-length fast return, so an aligned
    zero-length call is not 0 after all.  (Alignment is the other gate
    ahead of that return — see [mprotect_unaligned_precedes_zero_length]
    above.)  The pair with the two calls above is what
    makes the conjunction load-bearing here. *)

(** Reason 3.  An exact munmap of a wholly-inaccessible mapping empties both
    ledgers together — the no-access record must not outlive the mapping it
    describes, or a later grant at the same address would be born hidden.
    This shows [vm_noaccess] reaching [], which no trace shows. *)

Example munmap_exact_noaccess_removes_both_ledgers :
  check_syscall
    (mkInput 215 [65536; 12288; 0; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU 0 [] [] [(65536, 12288)] [] []) noaccess_three_pages
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull [] [] [] 0 0 16384 0 demo_sp)
        noaccess_three_pages) [].
Proof. check_eq. Qed.

Definition noaccess_brk_model : Model :=
  with_vmmaps
    (mkVmMapsFull [(4096, 4096)] [(65536, 4096)] [(65536, 4096)]
      65536 69632 demo_limit 0 demo_sp)
    (init_model [(4096, 4096)] 65536 0 demo_sp demo_limit (demo_input [] IEof)).

(** Reason 3.  A brk QUERY resolves to the unchanged break and must leave
    the no-access ledger alone — [brk_model_next]'s subtraction is gated on
    a strict shrink, and a query is not one.  The break base is ASLR-placed,
    so a live run cannot name the model state a query has to preserve. *)

Example brk_query_preserves_noaccess :
  check_syscall
    (mkInput 214 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 69632 [] []) noaccess_brk_model
  = CheckOk noaccess_brk_model [].
Proof. check_eq. Qed.

(** Reason 4: no kernel produces this effect.  A fresh PROT_NONE grant
    declares its range in [eff_unmaps] — the bytes go AWAY — so an effect
    that ALSO declares [eff_zeros] over the same range claims the pages
    are simultaneously unmapped and zero-filled.  [Run.apply_effect]
    erases before it zeroes, so honouring it would leave a readable zero
    page where the ledger says PROT_NONE: the stale-overlay class this
    branch exists to close, in its most direct form.  The shape is not
    reachable from a real trace at all, which is why the
    rejecting direction has to be stated here. *)

Example mmap_fresh_noaccess_zeros_are_rejected :
  check_syscall
    (mkInput 222 [0; 4096; 0; 34; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU 65536 [] [(65536, 4096)] [(65536, 4096)] [] []) noaccess_base
  = CheckReject.
Proof. check_eq. Qed.

(** Reason 3, and the only place this can be stated at all.  The
    MAP_FIXED gate tests [region_free (vm_reserved h) addr n] AND
    [map_contains (vm_maps h) addr n].  The first LOOKS redundant — the
    two ledgers are disjoint on every reachable state — but definitionally
    there is no implication, and that conjunct is the whole reason a guard
    page cannot be installed over the loaded image.

    That disjointness is NOT "[region_free] gates every grant", which is
    false: a brk grow inside one page enters [vm_maps] with no
    address-space test at all ([Sys/Mm/Mmap.brk_grow_ok]'s [else true],
    and [Checks/VmMapsDisjoint] Part 1 for a checked execution reaching
    it).  It holds for two separate reasons — [mmap] and [mremap] place
    only where [region_free] accepts against [vm_reserved ++ vm_maps], and
    brk grants cannot reach the image because [Run.valid_brk] puts the
    break base at or above the page-rounded image top and the break never
    goes below [min_brk].  Remove it and the call below
    becomes a modeled SUCCESS returning [addr] and declaring
    [eff_unmaps] across the image, erasing loaded code and data from the
    machine overlay.

    No live run can pin it.  A run that aims a real image address at
    this gate starts from [init_model], whose [vm_maps] is EMPTY,
    so that call fails [map_contains] as well and would still decline
    with the [vm_reserved] conjunct deleted.  Separating the two
    conjuncts needs a ledger that violates the disjointness prose, which
    only a hand-built state can be. *)

Example mmap_fixed_over_image_is_unmodeled :
  check_syscall
    (mkInput 222 [4096; 4096; 0; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU 4096 [] [] [(4096, 4096)] [] []) noaccess_image_overlap
  = CheckUnmodeled.
Proof. check_eq. Qed.

(* -------------------------------------------------------------------------
   brk (214).  A concrete process: the image occupies [4096, 8192) and
   the break base sits ASLR-plausibly at 0x10000 = 65536 ([vm_start_brk]
   = [vm_brk] = 65536 at execve) — so [min_brk] = [start_brk] = 65536,
   and the ASLR gap [8192, 65536) between image and base is INVALID
   territory, as on Linux.

   The break base is ASLR-placed, so a live run cannot name it in a literal
   expected return; that is what puts the rejecting cases and the
   blocked-grow branch here.
   ------------------------------------------------------------------------- *)

Definition brk_reserved : list (word * word) := [(4096, 4096)].

Definition m_est : Model := init_model brk_reserved 65536 0 demo_sp demo_limit (demo_input [] IEof).

Definition brk_in (req : word) : SyscallInput :=
  mkInput 214 [req; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None).

(** brk(0) on an ESTABLISHED break returns the CURRENT break UNCHANGED,
    with NO state change — the Linux [addr < min_brk] path libc uses to
    query (sbrk(0)) — and does NOT return an arbitrary value. *)

Example brk_zero_returns_current_break :
  check_syscall (brk_in 0) (mkEffect 65536 [] []) m_est = CheckOk m_est [].
Proof. check_eq. Qed.

Example brk_zero_rejects_arbitrary :
  check_syscall (brk_in 0) (mkEffect 123456 [] []) m_est = CheckReject.
Proof. check_eq. Qed.

(** A request in the ASLR GAP between the image top (8192) and the base
    (65536) is invalid — Linux's [min_brk] is [mm->start_brk], the base
    itself, NOT the image top — so it returns the break unchanged and
    cannot move it. *)

Example brk_in_aslr_gap_returns_break :
  check_syscall (brk_in 16384) (mkEffect 65536 [] []) m_est = CheckOk m_est [].
Proof. check_eq. Qed.

Example brk_in_aslr_gap_rejects_moving :
  check_syscall (brk_in 16384) (mkEffect 16384 [] []) m_est = CheckReject.
Proof. check_eq. Qed.

(** A blocked GROW may always take the failure branch: the break is
    unchanged (and no memory is granted).  Linux always grants here, so
    no honest trace exhibits this branch. *)

Example brk_grow_may_fail :
  check_syscall (brk_in 131072) (mkEffect 65536 [] []) m_est = CheckOk m_est [].
Proof. check_eq. Qed.

(** ONE FREE PAGE ABOVE THE NEW BREAK.  [SYSCALL_DEFINE1(brk)] (mm/mmap.c,
    commit 1f99e9ab748fc5c32120de9c4eca31abfe54a4d5) refuses a grow when
    a VMA meets [[oldbrk, newbrk + PAGE_SIZE)] — [vma_find(&vmi, newbrk +
    PAGE_SIZE + stack_guard_gap)] then [newbrk + PAGE_SIZE >
    vm_start_gap(next)] — and answers the OLD break.  So with a mapping
    at 69632, a grow from 65536 to exactly 69632 installs a free page
    but lands flush against the mapping: the grant is inadmissible and
    the unchanged break is the only answer.  Move the mapping one page
    up, to 73728, and the same grow is granted.  The first lemma is the
    negative a predicate over [[lo, hi)] alone would answer
    [CheckOk]; the third pins that the lookahead is one page and not
    more. *)

Definition m_neighbour_flush : Model :=
  with_vmmaps (mkVmMaps brk_reserved [(69632, 4096)] 65536 65536 demo_limit) m_est.

Example brk_grow_flush_against_neighbour_rejected :
  check_syscall (brk_in 69632) (mkEffect 69632 [] [(65536, 4096)])
    m_neighbour_flush
  = CheckReject.
Proof. check_eq. Qed.

Example brk_grow_flush_against_neighbour_returns_break :
  check_syscall (brk_in 69632) (mkEffect 65536 [] []) m_neighbour_flush
  = CheckOk m_neighbour_flush [].
Proof. check_eq. Qed.

Definition m_neighbour_gap : Model :=
  with_vmmaps (mkVmMaps brk_reserved [(73728, 4096)] 65536 65536 demo_limit) m_est.

Example brk_grow_one_page_below_neighbour_grants :
  check_syscall (brk_in 69632) (mkEffect 69632 [] [(65536, 4096)])
    m_neighbour_gap
  = CheckOk (with_vmmaps (mkVmMaps brk_reserved [(65536, 4096); (73728, 4096)]
                            65536 69632 demo_limit) m_neighbour_gap) [].
Proof. check_eq. Qed.

(** A SHRINK unmaps the freed heap tail.  From a grown process (break
    0x20000, heap grant [65536, 131072)), brk back down to 65536 removes
    the grant FROM THE LEDGER — so the freed space can be re-granted
    later — AND declares [65536, 131072) in [eff_unmaps], which erases
    the machine overlay so a load through a dangling heap pointer
    faults.  Without that declaration the freed bytes would survive in
    the overlay and a re-grow would read them back, which no real Linux
    execution does. *)

Definition m_grown : Model :=
  with_vmmaps (mkVmMaps brk_reserved [(65536, 65536)] 65536 131072 demo_limit)
              (init_model brk_reserved 65536 0 demo_sp demo_limit (demo_input [] IEof)).

Example brk_shrink_unmaps_freed_tail :
  check_syscall (brk_in 65536)
    (mkEffectU 65536 [] [] [(65536, 65536)] [] []) m_grown
  = CheckOk (with_vmmaps (mkVmMaps brk_reserved [] 65536 65536 demo_limit) m_grown) [].
Proof. check_eq. Qed.

(** …and a shrink that declares NO unmap is inadmissible: the freed
    pages really go on Linux. *)

Example brk_shrink_must_declare_unmaps :
  check_syscall (brk_in 65536) (mkEffect 65536 [] []) m_grown = CheckReject.
Proof. check_eq. Qed.

(** The alignment boundary: a SUB-PAGE shrink frees NOTHING.  Linux
    page-aligns both breaks and takes the [newbrk == oldbrk] early exit
    (mm/mmap.c:156-161), so brk from 131072 down to 129024 (0x1f800,
    inside the same page) moves [mm->brk] and unmaps not one byte — the
    written heap survives, and [eff_unmaps] is empty.  ([vm_maps] still
    tracks the break itself, at byte granularity, so the ledger entry
    shrinks; that only bounds where a later grant may be placed and is
    not visible to the running program.) *)

Example brk_subpage_shrink_frees_nothing :
  check_syscall (brk_in 129024) (mkEffect 129024 [] []) m_grown
  = CheckOk (with_vmmaps (mkVmMaps brk_reserved [(65536, 63488)] 65536 129024
                            demo_limit) m_grown) [].
Proof. check_eq. Qed.

(** The mirror image on GROW: moving the logical break forward inside an
    already mapped page installs no page and therefore zero-fills nothing.
    In particular, a shrink-and-regrow within one page must not overwrite
    bytes above the temporary break. *)

Example brk_same_page_regrow_zeros_nothing :
  brk_zeros 69624 69624 69620 = [].
Proof. check_eq. Qed.

(** The no-access overlay follows the same physical boundary.  Start eight
    bytes below the end of a guarded page, shrink four bytes, then regrow the
    four: both transitions preserve the guard.  [vm_maps] still records the
    two logical pieces and charges their exact byte count. *)

Definition m_brk_same_page : Model :=
  with_vmmaps
    (mkVmMapsFull brk_reserved [(65536, 4088)] [(65536, 4096)]
      65536 69624 demo_limit 0 demo_sp) m_grown.

Definition m_brk_same_page_shrunk : Model :=
  with_vmmaps
    (mkVmMapsFull brk_reserved [(65536, 4084)] [(65536, 4096)]
      65536 69620 demo_limit 0 demo_sp) m_brk_same_page.

Example brk_same_page_shrink_preserves_noaccess :
  check_syscall (brk_in 69620) (mkEffect 69620 [] []) m_brk_same_page
  = CheckOk m_brk_same_page_shrunk [].
Proof. check_eq. Qed.

Example brk_same_page_regrow_preserves_noaccess :
  check_syscall (brk_in 69624) (mkEffect 69624 [] []) m_brk_same_page_shrunk
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull brk_reserved [(69620, 4); (65536, 4084)]
          [(65536, 4096)] 65536 69624 demo_limit 0 demo_sp)
        m_brk_same_page_shrunk) [].
Proof. check_eq. Qed.

(** That same-page shrink is the one documented case where a protected
    range outlives the [vm_maps] entry that owned it: [m_brk_same_page_shrunk]
    leaves [[69620, 69632)] in [vm_noaccess] and in no [vm_maps] entry.
    [Mremap.mremap_fresh_b] never consults [vm_noaccess], so what keeps a
    moved destination off that orphan is the residual entry
    [(65536, 4084)] — the shrink truncates the brk entry, it does not
    remove it, and a page-aligned destination low enough to touch the
    orphan must cross the residual first.  The pair below differs only in
    the destination, one page apart across the orphan's end (69632); the
    source at 131072 is an unrelated clean mapping to move. *)

Definition m_brk_orphan_with_source : Model :=
  with_vmmaps
    (mkVmMapsFull brk_reserved [(65536, 4084); (131072, 4096)]
      [(65536, 4096)] 65536 69620 demo_limit 0 demo_sp)
    m_brk_same_page_shrunk.

(** The counterfactual, on a state that is UNREACHABLE: the same-page brk
    shrink TRUNCATES the owning entry rather than removing it, and a
    nonempty orphan forces the protected base [a] to satisfy
    [a <= page_floor r < r], so [[page_floor r, r)] is always still in
    [vm_maps].  Take the residual out anyway and the move onto the orphan
    page is ACCEPTED — the model would place a mapping onto protected
    memory.  So the property [Mremap.mremap_fresh_b] actually leans on is
    "truncated, not removed", not the containment prose: the orphan's
    presence in [vm_noaccess] does none of the work, because the
    predicate never reads it. *)

Definition m_brk_orphan_without_residual : Model :=
  with_vmmaps
    (mkVmMapsFull brk_reserved [(131072, 4096)]
      [(65536, 4096)] 65536 69620 demo_limit 0 demo_sp)
    m_brk_same_page_shrunk.

(** The two states above, measured against the ledger invariant that
    [Mremap.mremap_fresh_avoids_noaccess] assumes.
    [State.noaccess_pages_owned] says every protected byte lies on a page
    some live [vm_maps] entry still touches — strictly weaker than
    [vm_noaccess] being a subset of [vm_maps], which the same-page brk
    shrink genuinely breaks.

    It HOLDS on the real shrunken state: the orphan [[69620, 69632)] is on
    page [[65536, 69632)], and the truncated brk entry [(65536, 4084)]
    still reaches into that page.  Nothing about the orphan being
    unowned bytewise matters, which is the point. *)

Example noaccess_pages_owned_brk_orphan :
  noaccess_pages_owned (m_vmmaps m_brk_same_page_shrunk).
Proof.
  unfold noaccess_pages_owned, m_brk_same_page_shrunk, with_vmmaps.
  cbn [m_vmmaps vm_noaccess vm_maps]; autorewrite with model.
  intros a n Hin. destruct Hin as [Heq|[]]. inversion Heq; subst; clear Heq.
  assert (E65536 : bv_unsigned (65536 : word) = 65536%Z) by reflexivity.
  assert (E4096 : bv_unsigned (4096 : word) = 4096%Z) by reflexivity.
  assert (E4084 : bv_unsigned (4084 : word) = 4084%Z) by reflexivity.
  split; [rewrite E4096; lia|].
  intros x Hx. rewrite E65536, E4096 in Hx.
  exists (65536 : word), (4084 : word). split; [now left|].
  rewrite E65536, E4084.
  destruct (page_round_down_Z_within 65536 69632 x
              ltac:(reflexivity) ltac:(reflexivity) ltac:(lia)) as [H1 H2].
  unfold page_size in *. lia.
Qed.

(** And it FAILS on the counterfactual state, the one where the residual
    entry was taken away and the move onto protected memory was accepted
    just above.  So the invariant is exactly what separates the reachable
    state from the unreachable one: it is not vacuous, and it is not
    trivially true of anything with a nonempty [vm_noaccess]. *)

Example noaccess_pages_owned_fails_without_residual :
  ~ noaccess_pages_owned (m_vmmaps m_brk_orphan_without_residual).
Proof.
  unfold noaccess_pages_owned, m_brk_orphan_without_residual, with_vmmaps.
  cbn [m_vmmaps vm_noaccess vm_maps]; autorewrite with model.
  intros H.
  assert (E65536 : bv_unsigned (65536 : word) = 65536%Z) by reflexivity.
  assert (E4096 : bv_unsigned (4096 : word) = 4096%Z) by reflexivity.
  assert (E131072 : bv_unsigned (131072 : word) = 131072%Z) by reflexivity.
  destruct (H (65536 : word) (4096 : word) ltac:(now left)) as [_ Hpage].
  destruct (Hpage 65536%Z ltac:(lia)) as [b [s [Hin [Hb1 _]]]].
  destruct Hin as [Heq|[]]. inversion Heq; subst; clear Heq.
  rewrite E131072 in Hb1.
  replace (page_round_down_Z 65536) with 65536%Z in Hb1 by reflexivity.
  unfold page_size in Hb1. lia.
Qed.

(** Crossing that boundary is exact in both directions: an unaligned old
    break at 0x10ff8 grown sixteen bytes maps and zeroes precisely the next
    page [0x11000,0x12000), while the logical ledger records only sixteen
    newly requested bytes. *)

Example brk_unaligned_cross_page_zeros_exact_new_page :
  check_syscall (brk_in 69640)
    (mkEffect 69640 [] [(69632, 4096)]) m_brk_same_page
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull brk_reserved [(69624, 16); (65536, 4088)]
          [(65536, 4096)] 65536 69640 demo_limit 0 demo_sp)
        m_brk_same_page) [].
Proof. check_eq. Qed.

(* -------------------------------------------------------------------------
   The allocation budget ([State.vm_limit]).  These are the
   model-level statement that the budget BITES — a live run can
   exhibit the forced failure, but only the checks here can state that the
   over-budget GRANT is inadmissible.

   A tight process: budget 8192, one live 4096-byte grant at 65536 —
   4096 bytes of budget left. *)

Definition mmap_in (len : word) : SyscallInput :=
  mkInput 222 [0; len; 3; 34; mmap_fd_none; 0] (fun _ => None) (fun _ => None).

(** Within the remaining budget the grant is admissible, and is metered
    at the PAGE-ROUNDED length the ledger records. *)

Example mmap_within_budget_grants :
  check_syscall (mmap_in 4096) (mkEffect 131072 [] [(131072, 4096)]) tight_model
  = CheckOk (with_vmmaps (mkVmMaps [] [(131072, 4096); (65536, 4096)] 0 0 8192)
               tight_model) [].
Proof. check_eq. Qed.

(** Beyond it the grant is REJECTED — address space is plentiful (the
    ceiling is nowhere near), the budget alone forces failure… *)

Example mmap_beyond_budget_rejected :
  check_syscall (mmap_in 8192) (mkEffect 131072 [] [(131072, 8192)]) tight_model
  = CheckReject.
Proof. check_eq. Qed.

(** …and the failure the kernel then reports is admissible: ENOMEM with
    no grant.  This pair is the deterministic out-of-memory point. *)

Example mmap_beyond_budget_fails_enomem :
  check_syscall (mmap_in 8192) (mkEffect (errno_ret ENOMEM) [] []) tight_model
  = CheckOk tight_model [].
Proof. check_eq. Qed.

(** Freeing returns bytes to the budget: after unmapping the live grant,
    the 8192-byte request that was over budget above is grantable. *)

Example freed_budget_is_regrantable :
  check_syscall (mmap_in 8192) (mkEffect 131072 [] [(131072, 8192)])
    (with_vmmaps (mkVmMaps [] [] 0 0 8192) tight_model)
  = CheckOk (with_vmmaps (mkVmMaps [] [(131072, 8192)] 0 0 8192) tight_model) [].
Proof. check_eq. Qed.

(* -------------------------------------------------------------------------
   The [check_mmap] placement/budget conjunction.  The
   five-way read-write test — page alignment, positivity, the
   [alloc_top] bound, [region_free] against
   [vm_reserved ++ vm_maps], and [vm_limit] — differs deliberately from
   the four-way PROT_NONE test, which has no backed-memory charge.
   [check_mmap_sound_ok]
   destructs each conjunction against its matching
   [mmap_spec]'s [choose], so a copy that drifts out of sync fails to
   build. That guarantees SOME fix gets made, not the RIGHT one: the
   quickest way to turn a failing [check_mmap_sound_ok] green again is to
   weaken [mmap_spec]'s [choose] to match whatever [check_mmap] drifted
   to, which silences the proof without restoring the intended placement
   rule. These examples exist to make that move visibly wrong — a
   weakened [choose] would still admit the [CheckOk] cases below but
   would also make the paired [CheckReject] pin false, so a drift that
   the build lets through cannot also pass these.

   Reason 3 (MODEL-INTERNAL STATE, [State.alloc_top]) and Reason 4
   (the environment cannot be made to produce these — placement is
   ASLR-chosen, so no live run can name a literal address at the ceiling or
   overlapping a specific live mapping): every example below pins ONE
   conjunct as independently load-bearing, in BOTH [mmap_modeled_b] and
   [mmap_noaccess_b], by holding a boundary value just inside admissible
   and just outside it.  [vm_limit] is pinned for [mmap_modeled_b] by
   [mmap_within_budget_grants] / [mmap_beyond_budget_rejected] above.
   The bound is per run
   ([State.alloc_top]); these examples pin it at [demo_top], the top a
   run started at the bottom of the SP window has, and the
   [grant_at_demo_top_*] pair below is what separates a bound read from
   the ledger from a constant. *)

Definition mmap_noaccess_in (len : word) : SyscallInput :=
  mkInput 222 [0; len; 0; 34; mmap_fd_none; 0] (fun _ => None) (fun _ => None).

(** A zero placement is page-aligned, below the ceiling, disjoint, and
    within budget.  Positivity is the only placement conjunct that can
    reject these otherwise exact fresh-grant effects. *)

Example mmap_modeled_zero_placement_is_rejected :
  check_syscall (mmap_in 4096) (mkEffect 0 [] [(0, 4096)]) ceiling_room_model
  = CheckReject.
Proof. check_eq. Qed.

Example mmap_noaccess_zero_placement_is_rejected :
  check_syscall (mmap_noaccess_in 4096) (mkEffectU 0 [] [] [(0, 4096)] [] [])
    ceiling_room_model
  = CheckReject.
Proof. check_eq. Qed.

(** Address 65537 is positive, below the ceiling, disjoint, and within
    budget.  It is one byte past a page boundary, so page alignment is
    the only placement conjunct that rejects these exact effects. *)

Example mmap_modeled_unaligned_placement_is_rejected :
  check_syscall (mmap_in 4096) (mkEffect 65537 [] [(65537, 4096)])
    ceiling_room_model
  = CheckReject.
Proof. check_eq. Qed.

Example mmap_noaccess_unaligned_placement_is_rejected :
  check_syscall (mmap_noaccess_in 4096)
    (mkEffectU 65537 [] [] [(65537, 4096)] [] []) ceiling_room_model
  = CheckReject.
Proof. check_eq. Qed.

(** [demo_top] = 0x7fff7f800000 = 140735332483072.  The last
    page-aligned start admitting a 4096-byte grant is
    [demo_top - 4096] = 140735332478976: [r + n = demo_top]
    exactly, satisfying the conjunct's [<=?]. Budget and placement are
    otherwise unconstrained ([ceiling_room_model] carries no live map
    and [demo_limit] of budget), so only [alloc_top] can be doing
    the work here. *)

Example mmap_modeled_at_ceiling_boundary_grants :
  check_syscall (mmap_in 4096)
    (mkEffect 140735332478976 [] [(140735332478976, 4096)])
    ceiling_room_model
  = CheckOk
      (with_vmmaps (mkVmMaps [] [(140735332478976, 4096)] 0 0 demo_limit)
        ceiling_room_model) [].
Proof. check_eq. Qed.

(** One page past the boundary — [r = demo_top] itself, so
    [r + n = demo_top + 4096] — fails the SAME conjunct and only
    that conjunct: region and budget are exactly as permissive as
    above. *)

Example mmap_modeled_past_ceiling_is_rejected :
  check_syscall (mmap_in 4096)
    (mkEffect 140735332483072 [] [(140735332483072, 4096)])
    ceiling_room_model
  = CheckReject.
Proof. check_eq. Qed.

(** The same boundary, in the PROT_NONE branch: the grant also lands in
    [vm_noaccess]. *)

Example mmap_noaccess_at_ceiling_boundary_grants :
  check_syscall (mmap_noaccess_in 4096)
    (mkEffectU 140735332478976 [] [] [(140735332478976, 4096)] [] [])
    ceiling_room_model
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull [] [(140735332478976, 4096)] [(140735332478976, 4096)]
          0 0 demo_limit 0 demo_sp)
        ceiling_room_model) [].
Proof. check_eq. Qed.

Example mmap_noaccess_past_ceiling_is_rejected :
  check_syscall (mmap_noaccess_in 4096)
    (mkEffectU 140735332483072 [] [] [(140735332483072, 4096)] [] [])
    ceiling_room_model
  = CheckReject.
Proof. check_eq. Qed.

Example mmap_modeled_adjacent_to_live_map_grants :
  check_syscall (mmap_in 4096) (mkEffect 135168 [] [(135168, 4096)])
    region_live_model
  = CheckOk
      (with_vmmaps (mkVmMaps [] [(135168, 4096); (131072, 4096)] 0 0 demo_limit)
        region_live_model) [].
Proof. check_eq. Qed.

(** …while a grant AT the live mapping's own start overlaps it exactly
    and [region_free] alone rejects it. *)

Example mmap_modeled_overlapping_live_map_is_rejected :
  check_syscall (mmap_in 4096) (mkEffect 131072 [] [(131072, 4096)])
    region_live_model
  = CheckReject.
Proof. check_eq. Qed.

Example mmap_noaccess_adjacent_to_live_map_grants :
  check_syscall (mmap_noaccess_in 4096) (mkEffectU 135168 [] [] [(135168, 4096)] [] [])
    region_live_model
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull [] [(135168, 4096); (131072, 4096)] [(135168, 4096)]
          0 0 demo_limit 0 demo_sp)
        region_live_model) [].
Proof. check_eq. Qed.

Example mmap_noaccess_overlapping_live_map_is_rejected :
  check_syscall (mmap_noaccess_in 4096) (mkEffectU 131072 [] [] [(131072, 4096)] [] [])
    region_live_model
  = CheckReject.
Proof. check_eq. Qed.

(** PROT_NONE reservations occupy virtual space without consuming the
    backed-memory budget.  Same [tight_model] (budget 8192, one accessible
    4096-byte grant), same addresses and lengths: the reservation is
    admissible whether or not its full length would fit [vm_limit]. *)

Example mmap_noaccess_within_budget_grants :
  check_syscall (mmap_noaccess_in 4096) (mkEffectU 131072 [] [] [(131072, 4096)] [] [])
    tight_model
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull [] [(131072, 4096); (65536, 4096)] [(131072, 4096)]
          0 0 8192 0 demo_sp)
        tight_model) [].
Proof. check_eq. Qed.

(** The two ledgers make the distinction explicit: all 12288 bytes occupy
    virtual addresses, while only the original read-write page is backed. *)

Example mmap_noaccess_ignores_backed_budget :
  check_syscall (mmap_noaccess_in 8192) (mkEffectU 131072 [] [] [(131072, 8192)] [] [])
    tight_model
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull [] [(131072, 8192); (65536, 4096)] [(131072, 8192)]
          0 0 8192 0 demo_sp)
        tight_model) [].
Proof. check_eq. Qed.

Example mmap_noaccess_virtual_bytes :
  vm_live_bytes
    (mkVmMapsFull [] [(131072, 8192); (65536, 4096)] [(131072, 8192)]
      0 0 8192 0 demo_sp) = 12288%Z.
Proof. reflexivity. Qed.

Example mmap_noaccess_backed_bytes :
  vm_backed_bytes
    (mkVmMapsFull [] [(131072, 8192); (65536, 4096)] [(131072, 8192)]
      0 0 8192 0 demo_sp) = 4096%Z.
Proof. reflexivity. Qed.

(** brk meters against the same budget: a fresh process with budget
    4096.  A one-page grow fits; a two-page grow can only fail (the
    break comes back unchanged), never move the break. *)

Definition m_tight_brk : Model := init_model brk_reserved 65536 0 demo_sp 4096 (demo_input [] IEof).

Example brk_grow_within_budget_grants :
  check_syscall (brk_in 69632) (mkEffect 69632 [] [(65536, 4096)]) m_tight_brk
  = CheckOk (with_vmmaps (mkVmMaps brk_reserved [(65536, 4096)] 65536 69632 4096)
               m_tight_brk) [].
Proof. check_eq. Qed.

Example brk_grow_beyond_budget_rejects_moving :
  check_syscall (brk_in 73728) (mkEffect 73728 [] [(65536, 8192)]) m_tight_brk
  = CheckReject.
Proof. check_eq. Qed.

Example brk_grow_beyond_budget_returns_break :
  check_syscall (brk_in 73728) (mkEffect 65536 [] []) m_tight_brk
  = CheckOk m_tight_brk [].
Proof. check_eq. Qed.

(** Sparse-backing lifecycle regressions.  These states are intentionally
    small so the budget edge is visible without a large allocation. *)
Definition mmap_lazy_rw_base : Model :=
  with_vmmaps (mkVmMaps [] [] 0 0 4096) noaccess_base.

Example mmap_rw_noreserve_bypasses_eager_backing :
  check_syscall
    (mkInput 222 [0; 8192; 3; 16418; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] [(65536, 8192)]) mmap_lazy_rw_base
  = CheckOk
      (vm_add_lazy 65536 8192
        (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 4096)
          mmap_lazy_rw_base)) [].
Proof. check_eq. Qed.

Definition mmap_lazy_materialized : Model :=
  with_vm_backing [(65536, 8192)] [65536; 69632]
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 8192) noaccess_base).

Example mmap_fixed_noaccess_replacement_forgets_replaced_backing :
  check_syscall
    (mkInput 222 [65536; 4096; 0; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU 65536 [] [] [(65536, 4096)] [] []) mmap_lazy_materialized
  = CheckOk
      (with_mmap_replacement 50 65536 4096
        (with_vmmaps
          (mkVmMapsFull [] [(65536, 8192)] [(65536, 4096)] 0 0 8192 0 demo_sp)
          mmap_lazy_materialized)) [].
Proof. check_eq. Qed.

Example mmap_fixed_noaccess_replacement_keeps_only_the_tail :
  let post := with_mmap_replacement 50 65536 4096
    (with_vmmaps
      (mkVmMapsFull [] [(65536, 8192)] [(65536, 4096)] 0 0 8192 0 demo_sp)
      mmap_lazy_materialized) in
  m_vm_lazy post = [(69632, 4096)] /\
  m_vm_materialized post = [69632].
Proof. cbv zeta. split; check_eq. Qed.

Example mmap_fixed_destructive_failure_forgets_backing :
  check_syscall
    (mkInput 222 [65536; 8192; 3; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU (errno_ret ENOMEM) [] [] [(65536, 8192)] [] [])
    mmap_lazy_materialized
  = CheckOk
      (with_mmap_destroyed 65536 8192 (mkVmMaps [] [] 0 0 8192)
        mmap_lazy_materialized) [].
Proof. check_eq. Qed.

Example munmap_forgets_lazy_and_materialized_metadata :
  check_syscall
    (mkInput 215 [65536; 8192; 0; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU 0 [] [] [(65536, 8192)] [] []) mmap_lazy_materialized
  = CheckOk
      (with_mmap_destroyed 65536 8192 (mkVmMaps [] [] 0 0 8192)
        mmap_lazy_materialized) [].
Proof. check_eq. Qed.

Example munmap_metadata_cannot_be_recharged_after_removal :
  let post := with_mmap_destroyed 65536 8192 (mkVmMaps [] [] 0 0 8192)
                mmap_lazy_materialized in
  m_vm_lazy post = [] /\ m_vm_materialized post = [] /\
  vm_backing_used post = 0%Z.
Proof. cbv zeta. repeat split; check_eq. Qed.

(** A lazy reservation may not make memory FREE.

    [vm_backing_used] subtracts a lazy range by its whole byte extent,
    while a first touch charges a page back only when ONE lazy range
    contains that whole page.  On an UNALIGNED range those two disagree,
    and the gap is backing that leaves the budget and can never be put
    back: an UNDER-charge, the direction that lets the model grant an
    allocation the kernel would refuse.  [State.vm_add_lazy] closes it by
    recording only a reservation's page-aligned interior, so the bytes it
    subtracts are exactly the bytes a touch can restore.

    Asked for [67584, 73728) -- a base 2048 into a page -- it records
    [69632, 73728), the one whole page the range covers.  Without the
    interior it would record the request, subtract 6144, and leave 2048
    bytes recoverable by nothing.

    The pin is at the model level because no syscall can reach this state:
    [mmap] places on a page boundary and rounds the length up, so every
    reservation the syscall layer builds is aligned already.  That is what
    makes the hole invisible to a trace test, and why it is pinned here --
    an obligation discharged because it was unreachable is not a test. *)
Definition lazy_align_base : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 8192)
    (init_model [] 0 0 demo_sp 8192 (demo_input [] IEof)).

Example lazy_unaligned_reservation_frees_no_backing :
  let m := vm_add_lazy 67584 6144 lazy_align_base in
  let touched := with_vm_backing (m_vm_lazy m) [69632] m in
  vm_backing_used lazy_align_base = 8192%Z /\
  m_vm_lazy m = [(69632, 4096)] /\
  vm_backing_used m = 4096%Z /\
  materialize_model_accesses m [(69632, 1%nat)] = Some touched /\
  vm_backing_used touched = 8192%Z.
Proof. cbv zeta. repeat split; check_eq. Qed.

(** A brk shrink is also a sparse-lifecycle boundary.  Start with a one-page
    heap, replace it by MAP_FIXED|MAP_NORESERVE, touch the page, then shrink
    the heap away.  Both sparse ledgers must be empty before an ordinary eager
    mmap spends the released page's budget. *)
Definition brk_sparse_grown : Model :=
  with_vmmaps (mkVmMaps brk_reserved [(65536, 4096)] 65536 69632 4096)
    (init_model brk_reserved 65536 0 demo_sp 4096 (demo_input [] IEof)).

Definition brk_sparse_fixed : Model :=
  with_mmap_replacement 16434 65536 4096 brk_sparse_grown.

Definition brk_sparse_touched : Model :=
  with_vm_backing (m_vm_lazy brk_sparse_fixed) [65536] brk_sparse_fixed.

Example brk_heap_fixed_noreserve_replacement :
  check_syscall
    (mkInput 222 [65536; 4096; 3; 16434; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] [(65536, 4096)]) brk_sparse_grown
  = CheckOk brk_sparse_fixed [].
Proof. check_eq. Qed.

Example brk_heap_fixed_noreserve_first_touch :
  materialize_model_accesses brk_sparse_fixed [(65536, 1%nat)] =
    Some brk_sparse_touched.
Proof. check_eq. Qed.

Example brk_shrink_forgets_fixed_noreserve_touch :
  check_syscall (brk_in 65536)
    (mkEffectU 65536 [] [] [(65536, 4096)] [] []) brk_sparse_touched
  = CheckOk (with_brk_next brk_sparse_touched 65536 65536) [].
Proof. check_eq. Qed.

Example brk_shrink_clears_sparse_ledgers :
  let post := with_brk_next brk_sparse_touched 65536 65536 in
  m_vm_lazy post = [] /\ m_vm_materialized post = [] /\
  vm_backing_used post = 0%Z.
Proof. cbv zeta. repeat split; check_eq. Qed.

Example eager_mmap_reuses_budget_after_sparse_brk_shrink :
  let post := with_brk_next brk_sparse_touched 65536 65536 in
  check_syscall
    (mkInput 222 [0; 4096; 3; 34; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 131072 [] [(131072, 4096)]) post
  = CheckOk
      (with_vmmaps
        (mkVmMaps brk_reserved [(131072, 4096)] 65536 65536 4096) post) [].
Proof. check_eq. Qed.

(* -------------------------------------------------------------------------
   lseek on a CHANNEL, and the ordering of its checks.

   The model treats fds 0-2 as streams.  When they are pipes, Linux's
   [vfs_llseek] answers the same -ESPIPE (fs/read_write.c, v6.18.46);
   when standard input is a regular file, the kernel disagrees with this
   stream idealization.  These examples state what the model means for
   a channel.
   ------------------------------------------------------------------------- *)

(** stdin (channel) at fd 0 and file "f" = "hi" open read-only at fd 3
    with offset 0. *)

(* -------------------------------------------------------------------------
   PREFERENCE-FREE PLACEMENT: what the spec says, and what it does not say

   The fresh-grant arms say three things about a placement the model
   chooses and nothing else — page-aligned, inside the user address
   space (nonzero, ending at or below the run's [State.alloc_top]), and
   disjoint from every mapping the ledger records.  The section note in
   [Sys/Mm/Mmap.v] carries the argument; these cases carry both halves
   of it, and the first three are low placements the spec admits.

   The spec does not pin the SEARCH as well — at or above a bottom-up
   floor, or leaving no fitting free gap up to the run's
   [mm->mmap_base] — because such a conjunct excludes placements Linux
   makes: its highest-fit half would read a ledger that does not carry
   the kernel's own vdso/vvar VMAs, so a real top-down descent would
   look impossible to the model.  Leaving it out costs provability and
   buys soundness, and these cases are where that trade is visible.

   Reason 4 (the environment cannot produce it) for all of them: the
   kernel allocates top-down from an [mmap_base] just under the stack
   (mm/util.c [mmap_base], v6.18.46), far above any of these addresses,
   so no live run can put the checker in front of a low placement to accept
   or reject.
   ------------------------------------------------------------------------- *)

Definition placement_model : Model :=
  init_model [] 0 (Z_to_bv 64 mmap_base_max) demo_sp demo_limit (demo_input [] IEof).

(** A LOW FIRST GRANT, admitted.  A first NULL-hint
    grant at 0x80000000 is page-aligned, positive, below the ceiling and
    free, so the spec admits it.

    The OTHER end of the run is where this matters: a runtime that later
    reserves a low absolute range with MAP_FIXED meets a partial
    overlap.  [Mmap.mmap_spec]'s spanning arm performs the replacement
    Linux performs, so a low placement is an ordinary resolution rather
    than a refutation.  What remains is that a program whose OBSERVABLE
    behaviour changes under such a replacement has a false equivalence
    statement, which is the right answer for a program that is
    placement-sensitive under ASLR. *)
Example mmap_null_hint_low_grant_admitted :
  check_syscall (mmap_in 4096)
    (mkEffect (Z_to_bv 64 0x80000000) [] [(Z_to_bv 64 0x80000000, 4096)])
    placement_model
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull [] [(Z_to_bv 64 0x80000000, 4096)] [] 0 0 demo_limit
          (Z_to_bv 64 mmap_base_max) demo_sp) placement_model) [].
Proof. check_eq. Qed.

(** …and the PROT_NONE arm admits the same placement through the same
    three conditions, so the freedom is in the placement rule rather than
    in either arm. *)
Example mmap_null_hint_low_reservation_admitted :
  check_syscall (mmap_noaccess_in 4096)
    (mkEffectU (Z_to_bv 64 0x80000000) [] []
       [(Z_to_bv 64 0x80000000, 4096)] [] [])
    placement_model
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull [] [(Z_to_bv 64 0x80000000, 4096)]
          [(Z_to_bv 64 0x80000000, 4096)] 0 0 demo_limit
          (Z_to_bv 64 mmap_base_max) demo_sp) placement_model) [].
Proof. check_eq. Qed.

(** A NON-NULL hint is just as free — the kernel honors a free
    page-aligned hint anywhere ([generic_get_unmapped_area] returns
    [addr] when the gap fits, mm/mmap.c:703-710, Linux v6.18.46) — and
    the pair with the case above is what says the spec treats the
    two alike. *)
Example mmap_nonnull_hint_low_grant_admitted :
  check_syscall
    (mkInput 222 [Z_to_bv 64 0x80000000; 4096; 3; 34; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (Z_to_bv 64 0x80000000) [] [(Z_to_bv 64 0x80000000, 4096)])
    placement_model
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull [] [(Z_to_bv 64 0x80000000, 4096)] [] 0 0 demo_limit
          (Z_to_bv 64 mmap_base_max) demo_sp) placement_model) [].
Proof. check_eq. Qed.

(** THE THIRD CASE, and the one easiest to miss: SKIPPING A FITTING
    FREE GAP is not a refusal.

    The ledger below is saturated from 0x2aaaaab000 up to the ceiling
    except for one free page-sized hole.  A placement below 0x2aaaaab000
    therefore has a fitting gap above it, and a search conjunct would
    refuse it on exactly that ground — no kernel descends past free
    space.

    It is admitted, and nothing in the spec looks at what is above a
    placement.  That is the sharpest single statement of what the spec
    gives up: not merely that low addresses are allowed, but that the
    ORDER a search would impose is not checked at all.  The trade is
    the one the section note argues — the same quantifier would also
    refuse real descents across VMAs the ledger does not carry — and
    this case is where a reader can see both sides of it at once. *)
Definition holed_reservation : list (word * word) :=
  [(Z_to_bv 64 0x2aaaaab000, Z_to_bv 64 0x1000000000);
   (Z_to_bv 64 0x3aaaaac000, Z_to_bv 64 (demo_top - 0x3aaaaac000))].

Definition holed_model : Model :=
  with_vmmaps
    (mkVmMapsFull [] holed_reservation holed_reservation 0 0
      demo_limit (Z_to_bv 64 mmap_base_max) demo_sp) placement_model.

Example mmap_null_hint_skipping_a_free_gap_admitted :
  check_syscall (mmap_in 4096)
    (mkEffect (Z_to_bv 64 0x2aaaaaa000) []
       [(Z_to_bv 64 0x2aaaaaa000, 4096)])
    holed_model
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull []
          ((Z_to_bv 64 0x2aaaaaa000, 4096) :: holed_reservation)
          holed_reservation 0 0 demo_limit
          (Z_to_bv 64 mmap_base_max) demo_sp) holed_model) [].
Proof. check_eq. Qed.

(** …and the hole itself is still refused for the reason the spec keeps:
    it is not free.  The gap the case above skips is at
    [0x3aaaaab000]; a grant claiming the page BELOW it lands inside the
    first reservation and is rejected by disjointness, which is the only
    thing saying anything about where a placement may go. *)
Example mmap_null_hint_inside_the_reservation_rejected :
  check_syscall (mmap_in 4096)
    (mkEffect (Z_to_bv 64 0x3aaaaaa000) []
       [(Z_to_bv 64 0x3aaaaaa000, 4096)])
    holed_model
  = CheckReject.
Proof. check_eq. Qed.

(* ---- the conditions that DO still refuse, one case each ---- *)

(** NEGATIVE: page alignment.  One byte off, everything else identical. *)
Example mmap_null_hint_unaligned_rejected :
  check_syscall (mmap_in 4096)
    (mkEffect (Z_to_bv 64 0x80000001) [] [(Z_to_bv 64 0x80000001, 4096)])
    placement_model
  = CheckReject.
Proof. check_eq. Qed.

(** NEGATIVE: address 0.  What Linux enforces is
    [mmap_min_addr <= a] — [security_mmap_addr] consults
    [dac_mmap_min_addr], whose default is 4096 (security/min_addr.c:11
    defines it from CONFIG_DEFAULT_MMAP_MIN_ADDR, mm/Kconfig:726 and
    :729, Linux v6.18.46) — and what the spec enforces is [0 < a], which
    is WIDER.  The sysctl is settable to 0, so [0 < a] is the
    loosest-legal envelope over every configuration of it rather than a
    kernel rule.

    HOW MUCH WIDER, exactly, because "wider" alone reads as a live gap
    and mostly is not one.  On a STOCK kernel the over-admission is
    EMPTY at page granularity: the default is 4096, riscv64 does not
    override it, and the only page-aligned address below 4096 is 0 —
    which this negative pins as refused.  The window is non-empty only
    where the sysctl has been RAISED, which most distributions do (to
    65536).  So the model admits page-aligned addresses in
    [(0, mmap_min_addr)] on a configured-up kernel and none on a
    default one.
    Over-admission, in the direction that costs provability rather than
    soundness.  Address 0 itself is refused under EVERY setting, which
    is what this case pins. *)
Example mmap_null_hint_zero_rejected :
  check_syscall (mmap_in 4096)
    (mkEffect 0 [] [(0, 4096)]) placement_model
  = CheckReject.
Proof. check_eq. Qed.

(** NEGATIVE: the grant top.  A grant whose end passes this run's
    [alloc_top] would not be disjoint from its stack. *)
Example mmap_null_hint_above_ceiling_rejected :
  check_syscall (mmap_in 4096)
    (mkEffect (Z_to_bv 64 demo_top) []
       [(Z_to_bv 64 demo_top, 4096)])
    placement_model
  = CheckReject.
Proof. check_eq. Qed.

(** NEGATIVE, and the essence of the rule:
    DISJOINTNESS from every live mapping.  [get_unmapped_area] never
    silently overlaps a live VMA for a preference-free request — both
    generic searches ask [vm_unmapped_area] for a gap (mm/mmap.c:712-718,
    :763-770), and a gap is free of every VMA in the interval searched
    (mm/vma.c:2885-2930, :2942-2982, Linux v6.18.46).  Here the request
    lands on a page the ledger already owns. *)
Definition placement_model_1 : Model :=
  with_vmmaps
    (mkVmMapsFull [] [(Z_to_bv 64 0x7fff7f7ff000, 4096)] [] 0 0 demo_limit
      (Z_to_bv 64 mmap_base_max) demo_sp) placement_model.

Example mmap_null_hint_overlapping_live_rejected :
  check_syscall (mmap_in 4096)
    (mkEffect (Z_to_bv 64 0x7fff7f7ff000) []
       [(Z_to_bv 64 0x7fff7f7ff000, 4096)])
    placement_model_1
  = CheckReject.
Proof. check_eq. Qed.

(** …and the anchor that keeps it tight: one page lower, where nothing
    is mapped, is admitted. *)
Example mmap_null_hint_beside_live_admitted :
  check_syscall (mmap_in 4096)
    (mkEffect (Z_to_bv 64 0x7fff7f7fe000) []
       [(Z_to_bv 64 0x7fff7f7fe000, 4096)])
    placement_model_1
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull []
          [(Z_to_bv 64 0x7fff7f7fe000, 4096);
           (Z_to_bv 64 0x7fff7f7ff000, 4096)] [] 0 0 demo_limit
          (Z_to_bv 64 mmap_base_max) demo_sp) placement_model_1) [].
Proof. check_eq. Qed.

(** NEGATIVE: disjointness covers the IMAGE too, and separately.  A
    grant over the binary's LOAD reservation is refused even though
    [vm_maps] is empty — [region_free] is checked against
    [vm_reserved ++ vm_maps], not against [vm_maps] alone. *)
Definition placement_model_img : Model :=
  with_vmmaps
    (mkVmMapsFull [(Z_to_bv 64 0x10000, 8192)] [] [] 0 0 demo_limit
      (Z_to_bv 64 mmap_base_max) demo_sp) placement_model.

Example mmap_null_hint_over_image_rejected :
  check_syscall (mmap_in 4096)
    (mkEffect (Z_to_bv 64 0x11000) [] [(Z_to_bv 64 0x11000, 4096)])
    placement_model_img
  = CheckReject.
Proof. check_eq. Qed.

(** THE SANITIZER SHAPE, on a witness run: after two
    admissible NULL-hint grants, AddressSanitizer's high-shadow
    MAP_FIXED|MAP_NORESERVE reservation at [0x7fff7000, 0x8fff7000)
    finds its range free and is admitted through the fresh-range
    MAP_FIXED arm.

    When the range is NOT free — when a floating grant did land inside
    the future shadow — that call is not [unmodeled]: it is
    the spanning replacement, and the statement survives it unless the
    program can observe the difference. *)
Definition placement_model_2 : Model :=
  with_vmmaps
    (mkVmMapsFull []
      [(Z_to_bv 64 0x7fff7f7fe000, 4096);
       (Z_to_bv 64 0x7fff7f7ff000, 4096)] [] 0 0 demo_limit
      (Z_to_bv 64 mmap_base_max) demo_sp) placement_model_1.

Example asan_shadow_fixed_after_null_grants_admitted :
  check_syscall
    (mkInput 222 [Z_to_bv 64 0x7fff7000; 268435456; 0; 16434;
                  mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU (Z_to_bv 64 0x7fff7000) [] []
       [(Z_to_bv 64 0x7fff7000, 268435456)] [] [])
    placement_model_2
  = CheckOk
      (vm_add_lazy (Z_to_bv 64 0x7fff7000) 268435456
        (with_vmmaps
          (mkVmMapsFull []
            [(Z_to_bv 64 0x7fff7000, 268435456);
             (Z_to_bv 64 0x7fff7f7fe000, 4096);
             (Z_to_bv 64 0x7fff7f7ff000, 4096)]
            [(Z_to_bv 64 0x7fff7000, 268435456)] 0 0 demo_limit
            (Z_to_bv 64 mmap_base_max) demo_sp) placement_model_2)) [].
Proof. check_eq. Qed.

(** Reason 1: the universal half, quantified over the placement rather
    than computed, which no finite set of checks can say.  EVERY
    admissible resolution of a NULL-hint grant satisfies the three
    conditions — that is the whole content of the rule, and stating it
    is what makes the accepts above evidence about a SPEC rather than
    about seven addresses.

    No lemma says the grant lands at or above a floor, and none should:
    such a floor excludes placements Linux makes.

    IT IS SHALLOW, and the difference is worth
    naming rather than leaving for a reader to notice.  It is
    stated over [check_mmap] and concludes exactly the conjuncts it
    destructs, so on its own it says little more than that the checker's
    guard is the conjunction it is written as.  What makes it a
    statement about the SPEC rather than about the checker is the pair
    [Checks.Sys.Mm.Mmap.check_mmap_sound_ok] and
    [check_mmap_complete_ok], which relate the two in both directions;
    read with them, every resolution [mmap_spec] admits for this shape
    satisfies the three conditions.  Without them it is a lemma about an
    executable function. *)
Lemma first_null_grant_admissible :
  forall (mb sp : word) inp (len a : word) m' evs,
    w_is0 len = false ->
    check_mmap 0 len 3 34 mmap_fd_none 0
      (mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])
      (init_model [] 0 mb sp demo_limit inp) = CheckOk m' evs ->
    (bv_unsigned a mod page_size = 0)%Z
    /\ (0 < bv_unsigned a)%Z
    /\ (bv_unsigned a + page_round_up_Z (bv_unsigned len)
        <= alloc_top (m_vmmaps (init_model [] 0 mb sp demo_limit inp)))%Z
    /\ region_free
         (vm_reserved (m_vmmaps (init_model [] 0 mb sp demo_limit inp))
          ++ vm_maps (m_vmmaps (init_model [] 0 mb sp demo_limit inp)))
         a (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true.
Proof.
  intros mb sp inp len a m' evs Hlen H.
  unfold check_mmap in H. rewrite Hlen in H.
  cbn [mmap_modeled_b] in H. cbv zeta in H.
  destruct (errno_ret_in mmap_errnos a) eqn:He; [discriminate|].
  destruct ((bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
            && (bv_unsigned a + page_round_up_Z (bv_unsigned len)
                <=? alloc_top (m_vmmaps (init_model [] 0 mb sp demo_limit inp)))%Z
            && region_free
                 (vm_reserved (m_vmmaps (init_model [] 0 mb sp demo_limit inp))
                  ++ vm_maps (m_vmmaps (init_model [] 0 mb sp demo_limit inp)))
                 a (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
            && mmap_noreserve_backed_ok 34 (init_model [] 0 mb sp demo_limit inp)
                 (page_round_up_Z (bv_unsigned len))
            && listNN_eqb
                 [(a, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]
                 [(a, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])
    eqn:HC; [|discriminate].
  apply andb_true_iff in HC as [HC _].
  apply andb_true_iff in HC as [HC _].
  apply andb_true_iff in HC as [HC Hfree].
  apply andb_true_iff in HC as [HC Hceil].
  apply andb_true_iff in HC as [Halign Hpos].
  apply Z.eqb_eq in Halign. apply Z.ltb_lt in Hpos.
  apply Z.leb_le in Hceil.
  repeat split; assumption.
Qed.

(** Reason 1, the negative half of the same [forall]: no resolution whose
    end passes the RUN'S top is accepted, whatever the stack pointer.  The
    bound the conclusion names is [State.alloc_top] of the very ledger the
    check ran on, so a checker comparing against a constant instead
    could not prove it: at a stack pointer
    above the constant the constant would admit what the ledger refuses. *)
Lemma mmap_null_hint_above_top_never_accepted :
  forall (mb sp : word) inp (len a : word) m' evs,
    w_is0 len = false ->
    (alloc_top (m_vmmaps (init_model [] 0 mb sp demo_limit inp))
     < bv_unsigned a + page_round_up_Z (bv_unsigned len))%Z ->
    check_mmap 0 len 3 34 mmap_fd_none 0
      (mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])
      (init_model [] 0 mb sp demo_limit inp) <> CheckOk m' evs.
Proof.
  intros mb sp inp len a m' evs Hlen Habove H.
  destruct (first_null_grant_admissible mb sp inp len a m' evs Hlen H)
    as (_ & _ & Hle & _).
  lia.
Qed.


(* -------------------------------------------------------------------------
   THE BOUND IS READ FROM THE LEDGER, NOT FROM A CONSTANT

   [State.alloc_top] is [vm_init_sp - stack_max_size]: the grant top of a
   run is its own stack's bottom.  The biconditional proofs in
   [Checks/Sys/Mm/Mmap.v] cannot see a constant creeping into both the
   spec and the checker at once, so each pair below runs THE SAME effect
   against two ledgers that differ only in the stack pointer they were
   started with, and asks for opposite verdicts.  [demo_sp] is the bottom
   of the SP window, so its top is [demo_top]; [hi_sp] is 256 MiB above
   it.  A grant ending one page past [demo_top] is exactly the lie a run
   started at [demo_sp] must refuse and a run started at [hi_sp] must
   admit.  Reason 3: the stack pointer is model-internal state fixed
   when the run starts, so no trace can vary it.
   ------------------------------------------------------------------------- *)

Definition hi_sp : word := Z_to_bv 64 (sp_window_lo + 0x10000000).

Definition top_lo_model : Model :=
  init_model [] 0 (Z_to_bv 64 mmap_base_max) demo_sp demo_limit (demo_input [] IEof).
Definition top_hi_model : Model :=
  init_model [] 0 (Z_to_bv 64 mmap_base_max) hi_sp demo_limit (demo_input [] IEof).

Example grant_at_demo_top_rejected_under_low_sp :
  check_syscall (mmap_in 4096)
    (mkEffect (Z_to_bv 64 demo_top) [] [(Z_to_bv 64 demo_top, 4096)])
    top_lo_model
  = CheckReject.
Proof. check_eq. Qed.

Example grant_at_demo_top_admitted_under_high_sp :
  check_syscall (mmap_in 4096)
    (mkEffect (Z_to_bv 64 demo_top) [] [(Z_to_bv 64 demo_top, 4096)])
    top_hi_model
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull [] [(Z_to_bv 64 demo_top, 4096)] [] 0 0 demo_limit
          (Z_to_bv 64 mmap_base_max) hi_sp) top_hi_model) [].
Proof. check_eq. Qed.

(** The PROT_NONE arm reads the same field. *)
Example noaccess_grant_at_demo_top_rejected_under_low_sp :
  check_syscall (mmap_noaccess_in 4096)
    (mkEffectU (Z_to_bv 64 demo_top) [] [] [(Z_to_bv 64 demo_top, 4096)] [] [])
    top_lo_model
  = CheckReject.
Proof. check_eq. Qed.

Example noaccess_grant_at_demo_top_admitted_under_high_sp :
  check_syscall (mmap_noaccess_in 4096)
    (mkEffectU (Z_to_bv 64 demo_top) [] [] [(Z_to_bv 64 demo_top, 4096)] [] [])
    top_hi_model
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull [] [(Z_to_bv 64 demo_top, 4096)]
          [(Z_to_bv 64 demo_top, 4096)] 0 0 demo_limit
          (Z_to_bv 64 mmap_base_max) hi_sp) top_hi_model) [].
Proof. check_eq. Qed.

(** And so does a growing [brk]: an established break one page under
    [demo_top] asked to grow two pages crosses the top. *)
Definition brk_top_lo_model : Model :=
  init_model [] (Z_to_bv 64 (demo_top - 4096)) (Z_to_bv 64 mmap_base_max)
    demo_sp demo_limit (demo_input [] IEof).
Definition brk_top_hi_model : Model :=
  init_model [] (Z_to_bv 64 (demo_top - 4096)) (Z_to_bv 64 mmap_base_max)
    hi_sp demo_limit (demo_input [] IEof).

Example brk_grow_across_demo_top_rejected_under_low_sp :
  check_syscall (brk_in (Z_to_bv 64 (demo_top + 4096)))
    (mkEffect (Z_to_bv 64 (demo_top + 4096)) []
       [(Z_to_bv 64 (demo_top - 4096), 8192)])
    brk_top_lo_model
  = CheckReject.
Proof. check_eq. Qed.

Example brk_grow_across_demo_top_admitted_under_high_sp :
  check_syscall (brk_in (Z_to_bv 64 (demo_top + 4096)))
    (mkEffect (Z_to_bv 64 (demo_top + 4096)) []
       [(Z_to_bv 64 (demo_top - 4096), 8192)])
    brk_top_hi_model
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 8192)] []
          (Z_to_bv 64 (demo_top - 4096)) (Z_to_bv 64 (demo_top + 4096))
          demo_limit (Z_to_bv 64 mmap_base_max) hi_sp) brk_top_hi_model) [].
Proof. check_eq. Qed.

(* -------------------------------------------------------------------------
   MAP_FIXED_NOREPLACE: placed exactly, refused rather than replaced.

   [Mmap.mmap_spec]'s two NOREPLACE shapes take the MAP_FIXED argument
   gate and then split ONCE on the ledger: a range meeting nothing in
   [vm_reserved ++ vm_maps] is the free-range MAP_FIXED sub-case, and a
   range meeting anything is -EEXIST with nothing changed ([do_mmap],
   mm/mmap.c:361-362 and :410-412, Linux v6.18.46; the section in
   [Sys/Mm/Mmap.v] carries the reading).  Every example below is one
   a live run cannot state on its own, for one of the four reasons at
   the top of [Checks/Examples.v]: the LEDGER after each call is named
   literally (reason 3), the -EEXIST over the image needs an image a
   live run cannot map over
   (reason 4), and the two [forall]s at the end are quantified over
   every ledger and every address (reason 1).
   ------------------------------------------------------------------------- *)

(** The four spellings the shapes accept: the bit alone, the bit with
    MAP_FIXED beside it, and each with MAP_NORESERVE.  The last is the
    one a sealed sanitizer runtime issues. *)
Definition noreplace_flags : word := Z_to_bv 64 0x100022.
Definition noreplace_fixed_flags : word := Z_to_bv 64 0x100032.
Definition noreplace_noreserve_flags : word := Z_to_bv 64 0x104022.
Definition noreplace_fixed_noreserve_flags : word := Z_to_bv 64 0x104032.

(** THE RUNTIME'S START-UP SEQUENCE, on the ledger of
    [asan_shadow_fixed_after_null_grants_admitted]: two floating
    NULL-hint grants have landed under the stack, and the sealed
    runtime now reserves its low shadow (rw), the gap between the
    shadows (PROT_NONE) and its high shadow (rw), each
    MAP_NORESERVE|MAP_FIXED_NOREPLACE at the address AddressSanitizer
    derives from its 0x7fff8000 shadow offset on a 47-bit address
    space.  All three ranges are free, so all three are admitted, and
    each lands in the ledger exactly where it was asked for, with lazy
    backing (reason 3: the ledger after each call is the claim). *)
Definition asan_low_shadow_in : SyscallInput :=
  mkInput 222 [Z_to_bv 64 0x7fff7000; Z_to_bv 64 0x10000000; 3;
               noreplace_noreserve_flags; mmap_fd_none; 0]
    (fun _ => None) (fun _ => None).
Definition asan_gap_in : SyscallInput :=
  mkInput 222 [Z_to_bv 64 0x8fff7000; Z_to_bv 64 0x20000000000; 0;
               noreplace_noreserve_flags; mmap_fd_none; 0]
    (fun _ => None) (fun _ => None).
Definition asan_high_shadow_in : SyscallInput :=
  mkInput 222 [Z_to_bv 64 0x2008fff7000; Z_to_bv 64 0xdfff0001000; 3;
               noreplace_noreserve_flags; mmap_fd_none; 0]
    (fun _ => None) (fun _ => None).

Definition asan_after_low_shadow : Model :=
  vm_add_lazy (Z_to_bv 64 0x7fff7000) (Z_to_bv 64 0x10000000)
    (with_vmmaps
      (mkVmMapsFull []
        [(Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000);
         (Z_to_bv 64 0x7fff7f7fe000, 4096);
         (Z_to_bv 64 0x7fff7f7ff000, 4096)] [] 0 0 demo_limit
        (Z_to_bv 64 mmap_base_max) demo_sp) placement_model_2).
Definition asan_after_gap : Model :=
  vm_add_lazy (Z_to_bv 64 0x8fff7000) (Z_to_bv 64 0x20000000000)
    (with_vmmaps
      (mkVmMapsFull []
        [(Z_to_bv 64 0x8fff7000, Z_to_bv 64 0x20000000000);
         (Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000);
         (Z_to_bv 64 0x7fff7f7fe000, 4096);
         (Z_to_bv 64 0x7fff7f7ff000, 4096)]
        [(Z_to_bv 64 0x8fff7000, Z_to_bv 64 0x20000000000)] 0 0 demo_limit
        (Z_to_bv 64 mmap_base_max) demo_sp) asan_after_low_shadow).
Definition asan_after_high_shadow : Model :=
  vm_add_lazy (Z_to_bv 64 0x2008fff7000) (Z_to_bv 64 0xdfff0001000)
    (with_vmmaps
      (mkVmMapsFull []
        [(Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000);
         (Z_to_bv 64 0x8fff7000, Z_to_bv 64 0x20000000000);
         (Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000);
         (Z_to_bv 64 0x7fff7f7fe000, 4096);
         (Z_to_bv 64 0x7fff7f7ff000, 4096)]
        [(Z_to_bv 64 0x8fff7000, Z_to_bv 64 0x20000000000)] 0 0 demo_limit
        (Z_to_bv 64 mmap_base_max) demo_sp) asan_after_gap).

Example asan_sealed_startup_is_admitted :
  check_syscall asan_low_shadow_in
    (mkEffect (Z_to_bv 64 0x7fff7000) []
       [(Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000)])
    placement_model_2
  = CheckOk asan_after_low_shadow []
  /\ check_syscall asan_gap_in
    (mkEffectU (Z_to_bv 64 0x8fff7000) [] []
       [(Z_to_bv 64 0x8fff7000, Z_to_bv 64 0x20000000000)] [] [])
    asan_after_low_shadow
  = CheckOk asan_after_gap []
  /\ check_syscall asan_high_shadow_in
    (mkEffect (Z_to_bv 64 0x2008fff7000) []
       [(Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000)])
    asan_after_gap
  = CheckOk asan_after_high_shadow [].
Proof. split; [check_eq | split; check_eq]. Qed.

(** THE COLLISION the bit exists for.  A floating grant has landed at
    0x80000000, inside the future low shadow.  Under MAP_FIXED that call
    is the spanning replacement (the grant is silently overwritten,
    which is what [asan_shadow_fixed_after_null_grants_admitted]'s
    comment describes); under MAP_FIXED_NOREPLACE it is -EEXIST, and the
    ledger is untouched — pinned as the post-state being the pre-state,
    which is reason 3.  The forged success is the answer MAP_FIXED
    would have given, and it is rejected — as the hint arm would reject
    it too, the range not being free, so the reject on its own does not
    pin that the bit is matched rather than stripped; the -EEXIST twin
    above and [mmap_noreplace_with_fixed_over_live_is_eexist] are what
    pin that. *)
Definition noreplace_collide_model : Model :=
  with_vmmaps
    (mkVmMapsFull [] [(Z_to_bv 64 0x80000000, 4096)] [] 0 0 demo_limit
      (Z_to_bv 64 mmap_base_max) demo_sp) placement_model.

Example asan_sealed_low_shadow_over_a_grant_is_eexist :
  check_syscall asan_low_shadow_in
    (mkEffect (errno_ret EEXIST) [] []) noreplace_collide_model
  = CheckOk noreplace_collide_model [].
Proof. check_eq. Qed.

Example asan_sealed_low_shadow_over_a_grant_success_rejected :
  check_syscall asan_low_shadow_in
    (mkEffect (Z_to_bv 64 0x7fff7000) []
       [(Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000)])
    noreplace_collide_model
  = CheckReject.
Proof. check_eq. Qed.

(** …and the same request spelled MAP_FIXED over the same ledger IS the
    replacement: the grant inside the request is cut out of [vm_maps]
    and the request takes its place.  The bit is what separates the two
    answers, and both are Linux's. *)
Example asan_shadow_fixed_over_a_grant_replaces_where_noreplace_refuses :
  check_syscall
    (mkInput 222 [Z_to_bv 64 0x7fff7000; Z_to_bv 64 0x10000000; 3; 16434;
                  mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (Z_to_bv 64 0x7fff7000) []
       [(Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000)])
    noreplace_collide_model
  = CheckOk
      (with_mmap_replacement 16434 (Z_to_bv 64 0x7fff7000)
         (Z_to_bv 64 0x10000000)
        (with_vmmaps
          (mkVmMapsFull [] [(Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000)]
            [] 0 0 demo_limit (Z_to_bv 64 mmap_base_max) demo_sp)
          noreplace_collide_model)) [].
Proof. check_eq. Qed.

(* ---- the occupied range, on a one-page ledger ---- *)

Definition noreplace_over_live_in (prot flags : word) : SyscallInput :=
  mkInput 222 [65536; 4096; prot; flags; mmap_fd_none; 0]
    (fun _ => None) (fun _ => None).
Definition noreplace_free_in (prot flags : word) : SyscallInput :=
  mkInput 222 [69632; 4096; prot; flags; mmap_fd_none; 0]
    (fun _ => None) (fun _ => None).

(** A request over a live page is -EEXIST, with the ledger unchanged,
    for both prot words. *)
Example mmap_noreplace_over_live_is_eexist :
  check_syscall (noreplace_over_live_in 3 noreplace_flags)
    (mkEffect (errno_ret EEXIST) [] []) one_map_model
  = CheckOk one_map_model []
  /\ check_syscall (noreplace_over_live_in 0 noreplace_flags)
    (mkEffect (errno_ret EEXIST) [] []) one_map_model
  = CheckOk one_map_model [].
Proof. split; check_eq. Qed.

(** ANY page of the request: a two-page request whose second page is the
    live one is refused, although its first page is free. *)
Example mmap_noreplace_partial_overlap_is_eexist :
  check_syscall
    (mkInput 222 [61440; 8192; 3; noreplace_flags; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EEXIST) [] []) one_map_model
  = CheckOk one_map_model [].
Proof. check_eq. Qed.

(** Reason 4: a forged SUCCESS over a live page is rejected, with or
    without the zero-fill a real grant carries — this is the lie the bit
    exists to refuse.  It is NOT what pins the bit being matched rather
    than stripped: stripped, the bit-alone word is the floating hint
    shape, which refuses a placement over a live page just the same.
    The strip is pinned by the -EEXIST twin above, which a stripped
    checker rejects, and by [mmap_noreplace_with_fixed_over_live_is_eexist],
    whose stripped word is MAP_FIXED and accepts the replacement. *)
Example mmap_noreplace_over_live_success_rejected :
  check_syscall (noreplace_over_live_in 3 noreplace_flags)
    (mkEffect 65536 [] [(65536, 4096)]) one_map_model
  = CheckReject
  /\ check_syscall (noreplace_over_live_in 3 noreplace_flags)
    (mkEffect 65536 [] []) one_map_model
  = CheckReject
  /\ check_syscall (noreplace_over_live_in 0 noreplace_flags)
    (mkEffectU 65536 [] [] [(65536, 4096)] [] []) one_map_model
  = CheckReject.
Proof. split; [check_eq | split; check_eq]. Qed.

(** Reason 4: -EEXIST is the errno, not just an errno.  -EINVAL — the
    argument gate's errno, which a model that ran the refusal FIRST
    could confuse it with — is rejected on an aligned request. *)
Example mmap_noreplace_over_live_einval_rejected :
  check_syscall (noreplace_over_live_in 3 noreplace_flags)
    (mkEffect (errno_ret EINVAL) [] []) one_map_model
  = CheckReject.
Proof. check_eq. Qed.

(** …while -ENOMEM is admitted beside it: [mm->map_count >
    sysctl_max_map_count] (mm/mmap.c:377-378, Linux v6.18.46) is tested
    before the intersection, and the model tracks no map count, so the
    environment failure every mmap arm admits stays admitted here. *)
Example mmap_noreplace_over_live_enomem_admitted :
  check_syscall (noreplace_over_live_in 3 noreplace_flags)
    (mkEffect (errno_ret ENOMEM) [] []) one_map_model
  = CheckOk one_map_model [].
Proof. check_eq. Qed.

(** Reason 4: a refusal changes nothing, so an -EEXIST that also claims
    a zero-fill or an unmap is rejected. *)
Example mmap_noreplace_eexist_with_an_effect_rejected :
  check_syscall (noreplace_over_live_in 3 noreplace_flags)
    (mkEffect (errno_ret EEXIST) [] [(65536, 4096)]) one_map_model
  = CheckReject
  /\ check_syscall (noreplace_over_live_in 0 noreplace_flags)
    (mkEffectU (errno_ret EEXIST) [] [] [(65536, 4096)] [] []) one_map_model
  = CheckReject.
Proof. split; check_eq. Qed.

(* ---- the free range: the MAP_FIXED free-range sub-case again ---- *)

(** A request over a free page is an ordinary grant naming its own
    address — recorded, and (rw) zero-filled, exactly as the free-range
    MAP_FIXED sub-case records it.  Reason 3: the ledger is the claim. *)
Example mmap_noreplace_free_range_grants :
  check_syscall (noreplace_free_in 3 noreplace_flags)
    (mkEffect 69632 [] [(69632, 4096)]) one_map_model
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull [] [(69632, 4096); (65536, 4096)] [] 0 0 demo_limit
          0 demo_sp) one_map_model) []
  /\ check_syscall (noreplace_free_in 0 noreplace_flags)
    (mkEffectU 69632 [] [] [(69632, 4096)] [] []) one_map_model
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull [] [(69632, 4096); (65536, 4096)] [(69632, 4096)] 0 0
          demo_limit 0 demo_sp) one_map_model) [].
Proof. split; check_eq. Qed.

(** Reason 4: on a free range -EEXIST is NOT an answer.  Nothing the
    ledger records meets the request, so [find_vma_intersection] finds
    nothing and Linux grants; a kernel refusing it is rejected.  (What
    the ledger does not record — the vdso/vvar pair — is a known
    residual gap of the model.) *)
Example mmap_noreplace_free_range_eexist_rejected :
  check_syscall (noreplace_free_in 3 noreplace_flags)
    (mkEffect (errno_ret EEXIST) [] []) one_map_model
  = CheckReject
  /\ check_syscall (noreplace_free_in 0 noreplace_flags)
    (mkEffect (errno_ret EEXIST) [] []) one_map_model
  = CheckReject.
Proof. split; check_eq. Qed.

(** …and the free-range grant keeps the environment errno, like every
    grant. *)
Example mmap_noreplace_free_range_enomem_admitted :
  check_syscall (noreplace_free_in 3 noreplace_flags)
    (mkEffect (errno_ret ENOMEM) [] []) one_map_model
  = CheckOk one_map_model [].
Proof. check_eq. Qed.

(* ---- both bits ---- *)

(** MAP_FIXED | MAP_FIXED_NOREPLACE is MAP_FIXED_NOREPLACE.  [do_mmap]
    folds the NOREPLACE bit into MAP_FIXED at mm/mmap.c:361-362 and
    tests the NOREPLACE bit alone at :410, so the combined word answers
    -EEXIST on a live page, and the replacement MAP_FIXED alone would
    perform is rejected.  Reason 4: a kernel that let MAP_FIXED win
    would be the wrong kernel. *)
Example mmap_noreplace_with_fixed_over_live_is_eexist :
  check_syscall (noreplace_over_live_in 3 noreplace_fixed_flags)
    (mkEffect (errno_ret EEXIST) [] []) one_map_model
  = CheckOk one_map_model []
  /\ check_syscall (noreplace_over_live_in 3 noreplace_fixed_flags)
    (mkEffect 65536 [] [(65536, 4096)]) one_map_model
  = CheckReject.
Proof. split; check_eq. Qed.

(** THE ANCHOR: MAP_FIXED alone over the same page IS that replacement —
    the contained commit — so the bit, and only the bit, is what turns
    the answer. *)
Example mmap_fixed_alone_over_live_replaces :
  check_syscall (noreplace_over_live_in 3 50)
    (mkEffect 65536 [] [(65536, 4096)]) one_map_model
  = CheckOk
      (with_mmap_replacement 50 65536 4096
        (with_vmmaps
          (mkVmMapsFull [] [(65536, 4096)] [] 0 0 demo_limit 0 demo_sp)
          one_map_model)) [].
Proof. check_eq. Qed.

(** …and on a free page the combined word grants, as the bit alone does. *)
Example mmap_noreplace_with_fixed_free_range_grants :
  check_syscall (noreplace_free_in 3 noreplace_fixed_flags)
    (mkEffect 69632 [] [(69632, 4096)]) one_map_model
  = CheckOk
      (with_vmmaps
        (mkVmMapsFull [] [(69632, 4096); (65536, 4096)] [] 0 0 demo_limit
          0 demo_sp) one_map_model) [].
Proof. check_eq. Qed.

(* ---- the image: an answer here, a decline under MAP_FIXED ---- *)

(** Reason 4.  Over the image's LOAD reservation the MAP_FIXED spelling
    declines ([mmap_fixed_rw_over_the_image_is_unmodeled] above), because
    the replacement it would perform has no representation.  The
    NOREPLACE spelling performs no replacement: those pages are mapped,
    so the answer is -EEXIST and the ledger can give it.  Both the
    request that meets the image and a live mapping and the one that
    meets the image alone are answered; the forged success over the
    image is rejected. *)
Example mmap_noreplace_over_the_image_is_eexist :
  check_syscall
    (mkInput 222 [65536; 8192; 3; noreplace_flags; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EEXIST) [] []) image_span_model
  = CheckOk image_span_model []
  /\ check_syscall
    (mkInput 222 [65536; 4096; 3; noreplace_flags; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EEXIST) [] []) image_span_model
  = CheckOk image_span_model []
  /\ check_syscall
    (mkInput 222 [65536; 4096; 3; noreplace_flags; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] [(65536, 4096)]) image_span_model
  = CheckReject.
Proof. split; [check_eq | split; check_eq]. Qed.

(* ---- the argument gate, and the flag bits that still decline ---- *)

(** Order is behavior: the alignment -EINVAL of [__get_unmapped_area]
    (mm/mmap.c:859) is decided before the intersection test at :410, so
    an unaligned address INSIDE the live page is -EINVAL, and -EEXIST for
    it is rejected. *)
Example mmap_noreplace_unaligned_inside_live_is_einval :
  check_syscall
    (mkInput 222 [65537; 4096; 3; noreplace_flags; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) one_map_model
  = CheckOk one_map_model []
  /\ check_syscall
    (mkInput 222 [65537; 4096; 3; noreplace_flags; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EEXIST) [] []) one_map_model
  = CheckReject.
Proof. split; check_eq. Qed.

(** The rest of the gate, as the MAP_FIXED arms have it: a page-rounded
    end past 2^64 is -ENOMEM, address 0 declines, a range reaching the
    stack band declines, and a zero length is the plain anonymous
    -EINVAL decided before any shape. *)
Example mmap_noreplace_gate_matches_map_fixed :
  check_syscall
    (mkInput 222 [4096; Z_to_bv 64 (two_pow_64 - 1); 3; noreplace_flags;
                  mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOMEM) [] []) one_map_model
  = CheckOk one_map_model []
  /\ check_syscall
    (mkInput 222 [0; 4096; 3; noreplace_flags; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EEXIST) [] []) one_map_model
  = CheckUnmodeled
  /\ check_syscall
    (mkInput 222 [Z_to_bv 64 demo_top; 4096; 3; noreplace_flags;
                  mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EEXIST) [] []) one_map_model
  = CheckUnmodeled
  /\ check_syscall
    (mkInput 222 [65536; 0; 3; noreplace_flags; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) one_map_model
  = CheckOk one_map_model [].
Proof. split; [check_eq | split; [check_eq | split; check_eq]]. Qed.

(** The bit is matched, not stripped, so every other unmodeled shape
    stays unmodeled with it: an extra flag bit (MAP_POPULATE),
    MAP_SHARED, MAP_HUGETLB, an executable prot, a nonzero offset, and a
    file-backed request (MAP_ANONYMOUS clear) all decline, whatever the
    ledger holds at the address. *)
Example mmap_noreplace_other_shapes_stay_unmodeled :
  check_syscall
    (mkInput 222 [69632; 4096; 3; Z_to_bv 64 0x108022; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 69632 [] [(69632, 4096)]) one_map_model
  = CheckUnmodeled
  /\ check_syscall
    (mkInput 222 [69632; 4096; 3; Z_to_bv 64 0x100021; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 69632 [] [(69632, 4096)]) one_map_model
  = CheckUnmodeled
  /\ check_syscall
    (mkInput 222 [69632; 4096; 3; Z_to_bv 64 0x140022; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 69632 [] [(69632, 4096)]) one_map_model
  = CheckUnmodeled
  /\ check_syscall
    (mkInput 222 [69632; 4096; 7; noreplace_flags; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 69632 [] [(69632, 4096)]) one_map_model
  = CheckUnmodeled
  /\ check_syscall
    (mkInput 222 [69632; 4096; 3; noreplace_flags; mmap_fd_none; 4096]
      (fun _ => None) (fun _ => None))
    (mkEffect 69632 [] [(69632, 4096)]) one_map_model
  = CheckUnmodeled
  /\ check_syscall
    (mkInput 222 [69632; 4096; 3; Z_to_bv 64 0x100002; 3; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 69632 [] [(69632, 4096)]) one_map_model
  = CheckUnmodeled.
Proof.
  split; [check_eq | split; [check_eq | split; [check_eq | split;
    [check_eq | split; check_eq]]]].
Qed.

(* ---- the two universal halves ---- *)

(** Reason 1.  OVER AN OCCUPIED RANGE NOTHING BUT AN ERRNO IS ACCEPTED,
    for every ledger, every address and every length: whatever the
    checker accepts leaves the model unchanged, carries no zero-fill
    and no unmap, and returns one of the argument gate's two errnos or
    -EEXIST.  Stated over the checker, with
    [Checks.Sys.Mm.Mmap.check_mmap_sound_ok] and [check_mmap_complete_ok]
    carrying it to [Mmap.mmap_spec] in both directions.  The flags word
    is the runtime's. *)
Lemma mmap_noreplace_occupied_answers_only_errnos :
  forall addr len fd r zs us m m' evs,
    region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr
      (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = false ->
    check_mmap addr len 3 noreplace_noreserve_flags fd 0
      (mkEffectU r [] zs us [] []) m = CheckOk m' evs ->
    m' = m /\ evs = [] /\ zs = [] /\ us = []
    /\ (r = errno_ret ENOMEM \/ r = errno_ret EINVAL \/ r = errno_ret EEXIST).
Proof.
  intros addr len fd r zs us m m' evs Hocc H.
  unfold check_mmap in H.
  assert (E1 : mmap_off_aligned_b 0 = true) by (vm_compute; reflexivity).
  assert (E2 : mmap_anon_b noreplace_noreserve_flags = true)
    by (vm_compute; reflexivity).
  assert (E3 : mmap_plain_anon_b noreplace_noreserve_flags = true)
    by (vm_compute; reflexivity).
  assert (E4 : mmap_modeled_b 3 noreplace_noreserve_flags 0 = false)
    by (vm_compute; reflexivity).
  assert (E5 : mmap_noaccess_b 3 noreplace_noreserve_flags 0 = false)
    by (vm_compute; reflexivity).
  assert (E6 : mmap_fixed_noaccess_b 3 noreplace_noreserve_flags 0 = false)
    by (vm_compute; reflexivity).
  assert (E7 : mmap_fixed_rw_b 3 noreplace_noreserve_flags 0 = false)
    by (vm_compute; reflexivity).
  assert (E8 : mmap_noreplace_noaccess_b 3 noreplace_noreserve_flags 0 = false)
    by (vm_compute; reflexivity).
  assert (E9 : mmap_noreplace_rw_b 3 noreplace_noreserve_flags 0 = true)
    by (vm_compute; reflexivity).
  rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9 in H. cbn [negb] in H.
  destruct (w_is0 len) eqn:Hl.
  { apply check_ret_only_ok_iff in H. destruct H as (Heff & -> & ->).
    injection Heff as -> -> ->.
    repeat split; try reflexivity. right; left; reflexivity. }
  cbv zeta in H.
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hovf.
  { apply check_ret_only_ok_iff in H. destruct H as (Heff & -> & ->).
    injection Heff as -> -> ->.
    repeat split; try reflexivity. left; reflexivity. }
  destruct (negb (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
                    <=? alloc_top (m_vmmaps m))%Z) eqn:Hceil; [discriminate|].
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
  { apply check_ret_only_ok_iff in H. destruct H as (Heff & -> & ->).
    injection Heff as -> -> ->.
    repeat split; try reflexivity. right; left; reflexivity. }
  destruct (negb (0 <? bv_unsigned addr)%Z) eqn:Hpos; [discriminate|].
  rewrite Hocc in H.
  destruct zs; [|discriminate]. destruct us; [|discriminate].
  destruct (errno_ret_in mmap_errnos r || bv_eqb r (errno_ret EEXIST))
    eqn:He; [|discriminate].
  injection H as <- <-.
  apply orb_true_iff in He as [He | He].
  - apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
    destruct HIn as [<- | []].
    repeat split; try reflexivity. left; reflexivity.
  - apply bv_eqb_eq in He. subst r.
    repeat split; try reflexivity. right; right; reflexivity.
Qed.

(** Reason 1, the other half.  OVER A FREE RANGE -EEXIST IS NEVER
    ACCEPTED, for every ledger, every address and every length.  Nothing
    the ledger records meets the request, so no kernel reading only its
    VMA tree could refuse it; the one kernel that would — one holding a
    VMA the ledger does not carry — is the model's known residual
    gap. *)
Lemma mmap_noreplace_free_range_never_eexist :
  forall addr len fd zs us m m' evs,
    region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr
      (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true ->
    check_mmap addr len 3 noreplace_noreserve_flags fd 0
      (mkEffectU (errno_ret EEXIST) [] zs us [] []) m <> CheckOk m' evs.
Proof.
  intros addr len fd zs us m m' evs Hfree H.
  unfold check_mmap in H.
  assert (E1 : mmap_off_aligned_b 0 = true) by (vm_compute; reflexivity).
  assert (E2 : mmap_anon_b noreplace_noreserve_flags = true)
    by (vm_compute; reflexivity).
  assert (E3 : mmap_plain_anon_b noreplace_noreserve_flags = true)
    by (vm_compute; reflexivity).
  assert (E4 : mmap_modeled_b 3 noreplace_noreserve_flags 0 = false)
    by (vm_compute; reflexivity).
  assert (E5 : mmap_noaccess_b 3 noreplace_noreserve_flags 0 = false)
    by (vm_compute; reflexivity).
  assert (E6 : mmap_fixed_noaccess_b 3 noreplace_noreserve_flags 0 = false)
    by (vm_compute; reflexivity).
  assert (E7 : mmap_fixed_rw_b 3 noreplace_noreserve_flags 0 = false)
    by (vm_compute; reflexivity).
  assert (E8 : mmap_noreplace_noaccess_b 3 noreplace_noreserve_flags 0 = false)
    by (vm_compute; reflexivity).
  assert (E9 : mmap_noreplace_rw_b 3 noreplace_noreserve_flags 0 = true)
    by (vm_compute; reflexivity).
  rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9 in H. cbn [negb] in H.
  destruct (w_is0 len) eqn:Hl.
  { apply check_ret_only_ok_iff in H. destruct H as (Heff & _ & _).
    apply (f_equal (fun e => bv_unsigned (eff_ret e))) in Heff.
    vm_compute in Heff. discriminate. }
  cbv zeta in H.
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hovf.
  { apply check_ret_only_ok_iff in H. destruct H as (Heff & _ & _).
    apply (f_equal (fun e => bv_unsigned (eff_ret e))) in Heff.
    vm_compute in Heff. discriminate. }
  destruct (negb (bv_unsigned addr + page_round_up_Z (bv_unsigned len)
                    <=? alloc_top (m_vmmaps m))%Z) eqn:Hceil; [discriminate|].
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
  { apply check_ret_only_ok_iff in H. destruct H as (Heff & _ & _).
    apply (f_equal (fun e => bv_unsigned (eff_ret e))) in Heff.
    vm_compute in Heff. discriminate. }
  destruct (negb (0 <? bv_unsigned addr)%Z) eqn:Hpos; [discriminate|].
  rewrite Hfree in H.
  destruct us; [|discriminate].
  assert (Enot : errno_ret_in mmap_errnos (errno_ret EEXIST) = false)
    by (vm_compute; reflexivity).
  rewrite Enot in H.
  destruct (bv_eqb (errno_ret EEXIST) addr
            && listNN_eqb zs
                 [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]
            && mmap_noreserve_backed_ok noreplace_noreserve_flags m
                 (page_round_up_Z (bv_unsigned len))) eqn:HC;
    [|discriminate].
  apply andb_true_iff in HC as [HC _].
  apply andb_true_iff in HC as [Hr _].
  apply bv_eqb_eq in Hr.
  (* the refused address would be an errno encoding, above every
     ledger's grant top *)
  apply negb_false_iff, Z.leb_le in Hceil.
  rewrite <- Hr in Hceil.
  rewrite errno_ret_unsigned in Hceil by (unfold EEXIST; lia).
  pose proof (word_unsigned_range len) as Hlen.
  pose proof (page_round_up_Z_nonneg (bv_unsigned len) ltac:(lia)) as Hn.
  alloc_top_bounds. unfold two_pow_64, stack_max_size, EEXIST in *. lia.
Qed.
