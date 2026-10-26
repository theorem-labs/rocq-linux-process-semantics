(** * LinuxProcessSem.Sys.Mm.Mremap — mremap (216)

    This file answers to Linux [mm/mremap.c]: it holds what the kernel
    defines there, and nothing else.  Which file a spec belongs in is
    therefore not a judgement call — look up where the kernel defines
    the syscall.  [Specs.v] carries the whole map.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export
  Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** mremap's modeled private-anonymous shape has no externally tracked
    failure condition beyond address-space exhaustion.  Bad arguments and
    unsupported VMA shapes are handled deterministically/fail-closed below.

    Traced through [SYSCALL_DEFINE5(mremap, ...)] (mm/mremap.c:1961-1994,
    Linux v6.18.46; the walk is its body [do_mremap], :1911-1952, and the
    helpers it calls, in mm/mremap.c unless another file is named) for
    exactly that shape — flags exactly MREMAP_MAYMOVE, [old] page
    aligned, both sizes nonzero, the source one tracked private anonymous
    rw mapping.  Every errno the call can still reach at RUN time is
    ENOMEM, and only on a RESIZING call:

    - equal size: NONE.  [check_prep_vma] returns at :1676-1677 before
      any allocation, split or accounting, and [mremap_at] answers [addr]
      at :1559, so nothing on that branch can fail — see [mremap_spec],
      which is why the equal-size arm sits outside the [alt] that offers
      this list;
    - shrink: a failed [do_vmi_munmap] ([shrink_vma], :1337-1338), which
      has to split the vma, so it can fail to allocate ([__split_vma],
      mm/vma.c:510-512, 523-524, 530-532) and, when the kernel's vma
      extends past the modeled entry, exceed [sysctl_max_map_count]
      ([vms_gather_munmap_vmas], mm/vma.c:1389-1393);
    - grow in place: [security_vm_enough_memory_mm] ([vrm_calc_charge],
      :990, overcommit) and a failed [vma_merge_extend]
      ([expand_vma_in_place], :1470, answered at :1471-1473);
    - grow by moving: [may_expand_vm] (mm/mmap.c:1326-1330 —
      RLIMIT_AS / RLIMIT_DATA) reached through [check_prep_vma] at
      :1742-1743, a failed [get_unmapped_area] ([vrm_set_new_addr],
      :957-960), and [move_vma]'s map-count check ([prep_move_vma],
      :1043-1044), its overcommit check (:1281-1282), a failed [copy_vma]
      ([copy_vma_and_data], :1193-1198), and a short [move_page_tables]
      (:1208-1209).

    Every other errno the function can return is a GATE this shape has
    already passed, or one the spec answers itself — not a runtime
    failure, so none of them is injectable:

    - EINVAL: unknown flag bits ([check_mremap_params], :1759-1760),
      FIXED without MAYMOVE (:1791-1792) and DONTUNMAP resizing
      (:1795-1796) are all excluded by the exact-flags test;
      [offset_in_page(addr)] (:1763-1764) and a zero [new_len]
      (:1771-1772) are the deterministic -EINVAL the spec returns itself;
      a rounded [new_len] above TASK_SIZE (:1775-1776) is a gate v6.12
      did not have on the
      MAYMOVE-only path, where the request went on to -ENOMEM from
      [get_unmapped_area], and [mremap_spec] answers it that way;
      a zero [old_len] on a private vma ([check_prep_vma], :1690-1693) is
      excluded by the clone gate; DONTUNMAP over a VM_DONTEXPAND /
      VM_PFNMAP vma (:1696-1698) is excluded for the same reason as :1795,
      the exact-flags test never lets DONTUNMAP through;
      the pgoff-overflow check (:1733-1734) needs [pgoff + (new_len >> 12)]
      to wrap 64 bits, and for an anonymous vma [do_mmap] sets
      [pgoff = addr >> PAGE_SHIFT] (mm/mmap.c [do_mmap]), so [alloc_top]
      ([State.alloc_top_lt]) caps it under 2^52 against a
      [new_len >> 12] below 2^52.
    - EFAULT: no vma at [addr] ([check_prep_vma], :1658-1659, after
      [vma_lookup] at :1931) and [old_len] running past the vma end
      (:1720-1721) are both excluded by [mremap_source_b], which demands
      the source be exactly one tracked mapping; VM_DONTEXPAND /
      VM_PFNMAP (:1736-1737) is never set on an anonymous mmap grant —
      their only setters are [remap_pfn_range_internal]
      (mm/memory.c:2953), [remap_vmalloc_range_partial]
      (mm/vmalloc.c:4615) and [__install_special_mapping]
      (mm/mmap.c:1440, flags at :1454-1455), and the anonymous leg of
      [do_mmap] reaches none of them: the driver hook sits behind
      [if (map->file)] at mm/vma.c:2520 ([__mmap_new_vma]), and the
      anonymous path is [vma_set_anonymous] at :2525.
    - EAGAIN: [mlock_future_ok] (:1739-1740) returns true immediately
      unless VM_LOCKED (mm/mmap.c:233-234), which can only arrive via
      MAP_LOCKED or [mlockall] (mm/mlock.c:747) — both outside the modeled
      surface, so no vma here is ever locked.

    Two errnos a real kernel CAN still return are deliberately outside the
    modeled surface, rather than silently absorbed:

    - EINTR from [mmap_write_lock_killable] ([do_mremap],
      mm/mremap.c:1924-1925) cannot be observed by any program.  That
      helper (include/linux/mmap_lock.h:325-332) is a thin wrapper around
      [down_write_killable] (kernel/locking/rwsem.c:1598-1610), whose wait
      state is TASK_KILLABLE (:1331, :1496), and
      [signal_pending_state] aborts a TASK_KILLABLE wait only on a FATAL
      signal (include/linux/sched/signal.h:408-416: TASK_KILLABLE lacks
      TASK_INTERRUPTIBLE, so the result is [__fatal_signal_pending]).  A
      fatal signal kills the task before it returns to userspace, so the
      -EINTR never reaches a register the program can read.  This is the
      same argument [Mprotect.mprotect_errnos] makes for its own killable lock.

    - EPERM for an mseal'd VMA ([vma_is_sealed] in [check_prep_vma],
      mm/mremap.c:1662-1663, testing VM_SEALED, include/linux/mm.h:447-448;
      v6.12's [can_modify_vma]) is unreachable because
      [mseal] (__NR_mseal, 462) is not in [syscall_spec]'s modeled surface
      (mm/mseal.c:71-78 is its only setter), so VM_SEALED is never set
      on a modeled run. *)
Definition mremap_errnos : list Z := [ENOMEM].

(** Replace the one mapping based at [old] with [(dst,new_n)].  The source
    is required below to have no [vm_noaccess] overlap, while a moved
    destination is fresh, so the no-access ledger is preserved verbatim. *)
Definition mremap_maps_next (h : VmMaps) (old dst new_n : word) : VmMaps :=
  mkVmMapsFull (vm_reserved h) ((dst, new_n) :: map_remove (vm_maps h) old)
    (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h)
    (vm_mmap_base h) (vm_init_sp h).

(** A source is either uniformly lazy or wholly eager.  A MAP_FIXED inside
    it can split the backing provenance without splitting [vm_maps]; mremap
    fails closed on that mixed representation rather than guessing which
    provenance a grown tail inherits. *)
Definition mremap_backing_uniform_b (m : Model) (old old_n : word) : bool :=
  map_contains (m_vm_lazy m) old old_n
  || region_free (m_vm_lazy m) old old_n.

Definition mremap_source_lazy_b (m : Model) (old old_n : word) : bool :=
  map_contains (m_vm_lazy m) old old_n.

(** Update ownership and sparse-backing ledgers as one state transition.
    Materialized pages move with their source-relative offsets; a shrink
    releases pages beyond the new end, and a lazy grow extends the lazy range
    without eagerly charging its tail. *)
Definition mremap_model_next (m : Model) (old old_n dst new_n : word) : Model :=
  vm_resize_backing (mremap_source_lazy_b m old old_n) old old_n dst new_n
    (with_vmmaps (mremap_maps_next (m_vmmaps m) old dst new_n) m).

(** The grown delta reads as fresh zeroes.  Neither [vma_merge_extend]
    ([expand_vma_in_place], mm/mremap.c:1470, Linux v6.18.46) on the
    in-place path nor [copy_vma] ([copy_vma_and_data], mm/mremap.c:1193)
    on the move path installs page tables for it, and a [pte_none] fault
    on a PRIVATE|ANONYMOUS VMA is served by [do_anonymous_page]
    (mm/memory.c:5149-5262) — a read from the shared zero page
    (mm/memory.c:5170-5172), a write from a zeroed folio
    ([alloc_anon_folio], mm/memory.c:5059, called at :5198).

    The [old_nZ < new_nZ] guard never fires false where this is used:
    [mremap_spec] answers the equal case before [mremap_inplace_effect] is
    built, and the shrink case takes that function's other branch, so both
    call sites have already established growth.  It is kept because the
    function is total in its arguments and its name promises the tail of a
    grow; no trace can distinguish dropping it. *)
Definition mremap_tail (base old_n : word) (old_nZ new_nZ : Z)
    : list (word * word) :=
  if (old_nZ <? new_nZ)%Z
  then [(base + old_n, Z_to_bv 64 (new_nZ - old_nZ))]
  else [].

(** Linux's [PAGE_ALIGN(len)] ([do_mremap], mm/mremap.c:1917-1918, Linux
    v6.18.46) expands to [(len + 4095) & ~4095] on an [unsigned long]
    (include/linux/mm.h:222 -> include/vdso/align.h:8 ->
    include/uapi/linux/const.h:48-49), which
    WRAPS.  It yields zero on exactly two kinds of input: [len = 0], and
    [len] in the top partial page [[2^64-4095, 2^64-1]].  (Not the whole
    top page: [2^64-4096] is already aligned and survives.)  Computing the
    round in [Z], that is [page_round_up_Z len = 0 \/ = 2^64], which is
    what this decides — so the two arms of Linux's [!new_len] test at
    mm/mremap.c:1771-1772 ([check_mremap_params]) need no separate
    treatment. *)
Definition page_align_is0_b (len : word) : bool :=
  w_is0 len || (two_pow_64 <=? page_round_up_Z (bv_unsigned len))%Z.

(** The modeled source.  Linux needs only [vma_lookup(mm, addr)] to
    succeed (mm/mremap.c:1043, v6.12); requiring an EXACT tracked entry is
    stricter, hence fail closed, and it is what lets [mremap_model_next]
    carry [vm_noaccess] over untouched.  The [vm_reserved] and
    [vm_noaccess] conjuncts keep the image and PROT_NONE guards out: the
    model has no ledger shape for remapping either.

    Two of the four conjuncts pull their weight only jointly.
    [region_free (vm_reserved h) old old_n] is implied by
    [map_has (vm_maps h) old old_n] whenever the two ledgers are disjoint —
    which they are, but NOT because [region_free] gates every grant: a brk
    grow inside one page enters [vm_maps] with no address-space test at all
    ([Mmap.brk_grow_ok]'s [else true], and [Checks/VmMapsDisjoint] Part 1
    for a checked execution reaching it).  It holds for two separate
    reasons — [Mmap.mmap_spec] and [mremap_spec] place only where
    [region_free] accepts against [vm_reserved ++ vm_maps], and brk grants
    cannot reach the image because [Run.valid_brk] puts the break base at
    or above the page-rounded image top and the break never goes below
    [min_brk].  So no trace can distinguish dropping it; it is kept because
    the disjointness is an invariant of the other specs rather than
    something stated here.  The [alloc_top]
    bound is what [mremap_source_ret_not_errno] needs to know that a
    successful in-place return cannot be mistaken for an encoded errno. *)
Definition mremap_source_b (h : VmMaps) (old old_n : word)
    (old_nZ : Z) : bool :=
  (bv_unsigned old + old_nZ <=? alloc_top h)%Z
  && region_free (vm_reserved h) old old_n
  && map_has (vm_maps h) old old_n
  && region_free (vm_noaccess h) old old_n.

(** The budget analogue of [may_expand_vm] (mm/mmap.c:1324-1346, Linux
    v6.18.46), which mremap reaches from [check_prep_vma] at
    mm/mremap.c:1742-1743 (v6.12's [vma_to_resize]) with
    [npages = delta >> PAGE_SHIFT] — i.e. Linux charges the
    NET DELTA, never a transient peak of both mappings.  The model checks the
    complete post-state instead: that is the same delta for eager mappings,
    while a MAP_NORESERVE tail remains lazy and costs nothing until touched.
    Since [check_prep_vma] runs from [do_mremap] at mm/mremap.c:1932, before
    [mremap_at] (:1937) picks the in-place or the move branch
    ([expand_vma], :1512), the same gate applies to both
    paths; the model does the same. *)
Definition mremap_final_budget_b (m : Model)
    (old old_n dst new_n : word) : bool :=
  vm_backing_within_limit (mremap_model_next m old old_n dst new_n).

(** Linux grows in place when [old_len == vma->vm_end - addr]
    (mm/mremap.c:1116, v6.12) and [vma_expandable] holds (:1120, defined at
    :966-978).  This is a coarser predicate in both directions — see
    [mremap_spec] for why the resulting over-admission is presented as an
    [alt] rather than a claim.

    Both halves of the [region_free] conjunct are LIVE.  The [vm_maps] half
    is the ordinary case; the [vm_reserved]
    half — an in-place grow running into the binary image — no trace reaches,
    because the only modeled way to choose an anonymous mapping's address is
    the PROT_NONE MAP_FIXED guard ([Mmap.mmap_fixed_noaccess_b]), which must land
    inside a mapping the process already owns, so no trace can put a tracked
    mapping below a LOAD segment.  It is not dead either:
    [Checks/Examples.v]'s [mremap_inplace_grow_into_image_rejected] flips
    [mremap_inplace_grow_accepts] to [CheckReject] by adding one reserved
    entry and changing nothing else.

    The [alloc_top] conjunct is LIVE too, and it is the only thing
    keeping a grown mapping clear of the dynamic stack — the stack is in
    neither [vm_reserved] nor [vm_maps], so [region_free] cannot see it.
    No
    kernel places an ordinary anonymous mapping near this address for the
    in-place arm to grow from.  [Checks/Examples.v]'s
    [mremap_inplace_grow_past_ceiling_rejected] pins it, against
    [mremap_inplace_grow_to_ceiling_accepts] one page below: the pair
    differs only in the source's base address, so the flipped verdict is
    attributable to this conjunct alone. *)
Definition mremap_inplace_grow_b (m : Model) (old old_n new_n : word)
    (old_nZ new_nZ : Z) : bool :=
  let h := m_vmmaps m in
  (bv_unsigned old + new_nZ <=? alloc_top h)%Z
  && region_free (vm_reserved h ++ map_remove (vm_maps h) old) old new_n
  && mremap_final_budget_b m old old_n old new_n.

(** A moved destination, and the argument for what this guard says is
    mremap's own rather than a loan from [Mmap.mmap_spec].

    A MAYMOVE destination IS a preference-free placement: Linux picks it
    with [get_unmapped_area] at [addr = 0] and no MAP_FIXED
    ([vrm_set_new_addr], mm/mremap.c:957-960, Linux v6.18.46; some line
    citations in this file are against v6.12 instead).
    So the conditions that hold of one
    hold of the other — page-aligned, nonzero, below
    [State.alloc_top], disjoint from every recorded mapping — and
    the conditions that do NOT are the same conditions, for the same
    reason.  This guard carries no search-order conjunct, for the
    reason its mmap twin carries none: a highest-fit conjunct would be
    read on the model's ledger, and the ledger does not carry the
    kernel's own vdso/vvar VMAs, so a real move destination the kernel
    reached by descending past them would be one the model called impossible.
    Excluding a destination Linux produces costs the theorem, exactly as
    it does for a fresh grant.

    DISJOINTNESS DOES MORE WORK HERE than in an ordinary grant, and that
    is the mremap-specific half.  [dst] can never overlap the source:
    Linux picks it
    with [get_unmapped_area] in [vrm_set_new_addr] (mm/mremap.c:957-960,
    Linux v6.18.46), passing [addr = 0] and no
    MAP_FIXED, so the search runs over the maple tree while the source VMA
    is still live (it is not unmapped until [move_vma] reaches
    [unmap_source_vma], mm/mremap.c:1122).  The model gets the same
    exclusion for free, because
    [old] is still in [vm_maps h] when [region_free] is evaluated.

    [dst <> old] is therefore redundant against a well-formed ledger, and
    [check_mremap] never evaluates it (it dispatches on [r = old] first).
    It is load-bearing in the SPEC: without it the [choose] would let the
    move arm produce move-shaped effects at [old], which the checker would
    classify as the in-place arm and reject — i.e. completeness would fail.
    [mremap_fresh_neq_old] is what discharges that.

    [vm_noaccess] is deliberately ABSENT from the [region_free] list, and
    that is not an oversight this predicate gets away with.  [State.v]'s
    purpose (c) says protected ranges are ORDINARILY subranges of
    [vm_maps], which the [vm_maps] half already excludes.  It names ONE
    exception, and it is a real one: a brk shrink inside its final page
    drops the byte-granular tail from [vm_maps] while [Mmap.brk_unmaps]
    (page-rounded) removes nothing from [vm_noaccess], so a strict
    sub-page slice [[r, PAGE_ALIGN r)] is left protected and owned by no
    [vm_maps] entry.  [Checks/Examples.v]'s [m_brk_same_page_shrunk] is a
    checked-in state in exactly that shape.

    No destination can reach such a slice, for a reason this predicate
    does check.  [dst] is page aligned, and the entry that owned the
    protected range is TRUNCATED to [[e0, r)], never removed — a nonempty
    orphan forces the protected base [a] to satisfy
    [a <= page_floor r < r], so [[page_floor r, r)] is still in
    [vm_maps].  A page-aligned [dst] overlapping the orphan needs
    [dst <= page_floor r] and [dst + new_n > r], which puts it across
    [[e0, r)], and [region_free] refuses it.  The pair
    [mremap_move_onto_brk_orphan_page_rejected] /
    [mremap_move_above_brk_orphan_accepts] in [Checks/Examples.v] pins
    that boundary: the two differ only in the destination, one page apart
    across the orphan's end.

    Note WHICH half of that does the work.
    [mremap_move_onto_orphan_without_residual_accepts] takes the residual
    entry out of the same state, and the move onto the orphan page is
    then ACCEPTED — so the property this predicate leans on is "the
    shrink TRUNCATES the owning entry rather than removing it", not the
    containment prose itself.  The orphan's presence in [vm_noaccess]
    contributes nothing here, because the predicate never reads it.  That
    state is unreachable, for the [a <= page_floor r < r] reason above;
    the example is checked in so the load-bearing property is visible
    rather than inferred.

    Adding [region_free (vm_noaccess h) dst new_n] here would be
    redundant on every reachable state by the argument above, and it
    would be a conjunct no example or test could ever flip — which is
    the opposite of how every other conjunct in this file is justified.
    The consumer half of that argument is mechanized:
    [mremap_fresh_avoids_noaccess] below derives the missing conjunct
    from [State.noaccess_pages_owned], the page-granular weakening of the
    containment that survives the brk-shrink exception.  The other half
    is mechanized too: [Checks/NoaccessOwned.v] proves a stronger ledger
    invariant ([sys_inv]) true of [init_model] and kept by every modeled
    system call, and derives [noaccess_pages_owned] from it
    ([sys_inv_noaccess_pages_owned]). *)
Definition mremap_fresh_b (m : Model) (old_nZ new_nZ : Z)
    (old old_n dst new_n : word) : bool :=
  let h := m_vmmaps m in
  negb (bv_eqb dst old)
  && (bv_unsigned dst mod page_size =? 0)%Z
  && (0 <? bv_unsigned dst)%Z
  && (bv_unsigned dst + new_nZ <=? alloc_top h)%Z
  && region_free (vm_reserved h ++ vm_maps h) dst new_n
  && mremap_final_budget_b m old old_n dst new_n.

(** Half of the argument above, mechanized: GIVEN the ledger invariant
    [State.noaccess_pages_owned], a destination this predicate accepts is
    disjoint from [vm_noaccess] — exactly the conjunct the definition
    leaves out.  So what the predicate leaves to the state is one named
    invariant rather than prose about a syscall.

    The proof is the page-granularity argument, with no appeal to the brk
    shrink's shape: [dst] is page aligned and [new_n] is a whole number of
    pages, so any protected byte the request touches drags its WHOLE page
    inside [[dst, dst+new_n)]; the invariant hands back a [vm_maps] entry
    meeting that page, and [region_free] against [vm_reserved ++ vm_maps]
    has already excluded every such entry.

    The two side conditions on [new_n] are what [mremap_spec] supplies at
    the call site: it passes [new_n = Z_to_bv 64 (page_round_up_Z
    (bv_unsigned new_size))] under [page_align_is0_b new_size = false],
    which is precisely "page-sized and nonzero".  Both are load-bearing
    rather than convenient — [iv_overlap] treats an empty interval on
    either side as overlapping anything that straddles it, so a zero-length
    request has no protected BYTE to reason about while [region_free] can
    still answer false.

    That [noaccess_pages_owned] holds of every reachable state is
    [Checks/NoaccessOwned.v]'s: [init_model_sys_inv],
    [star_preserves_sys_inv] and [sys_inv_noaccess_pages_owned]. *)
Lemma mremap_fresh_avoids_noaccess :
  forall m old_nZ new_nZ old old_n dst new_n,
    noaccess_pages_owned (m_vmmaps m) ->
    (0 < bv_unsigned new_n)%Z ->
    (bv_unsigned new_n mod page_size = 0)%Z ->
    mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true ->
    region_free (vm_noaccess (m_vmmaps m)) dst new_n = true.
Proof.
  intros m old_nZ new_nZ old old_n dst new_n Hown Hpos Hmod Hfresh.
  unfold mremap_fresh_b in Hfresh.
  cbv zeta in Hfresh.
  apply andb_true_iff in Hfresh as [Hfresh _].
  apply andb_true_iff in Hfresh as [Hfresh Hrf].
  apply andb_true_iff in Hfresh as [Hfresh _].
  apply andb_true_iff in Hfresh as [Hfresh _].
  apply andb_true_iff in Hfresh as [_ Halign].
  apply Z.eqb_eq in Halign.
  assert (Hhi : ((bv_unsigned dst + bv_unsigned new_n) mod page_size = 0)%Z).
  { rewrite Z.add_mod by (unfold page_size; lia).
    rewrite Halign, Hmod. reflexivity. }
  apply region_free_intro. intros a n Hin.
  destruct (Hown a n Hin) as [Hn Hpage].
  destruct (iv_overlap dst new_n a n) eqn:Hov; [exfalso|reflexivity].
  unfold iv_overlap in Hov.
  apply andb_true_iff in Hov as [Hov1 Hov2].
  apply Z.ltb_lt in Hov1. apply Z.ltb_lt in Hov2.
  remember (Z.max (bv_unsigned dst) (bv_unsigned a)) as x eqn:Hx.
  destruct (Hpage x ltac:(lia)) as [b [s [Hinm [Hb1 Hb2]]]].
  destruct (page_round_down_Z_within (bv_unsigned dst)
              (bv_unsigned dst + bv_unsigned new_n) x Halign Hhi ltac:(lia))
    as [Hf1 Hf2].
  pose proof (region_free_In _ _ _ b s Hrf
                (in_or_app _ _ _ (or_intror Hinm))) as Hno.
  unfold iv_overlap in Hno.
  apply andb_false_iff in Hno as [Hc|Hc]; apply Z.ltb_ge in Hc; lia.
Qed.

(** Staying at [old]: a shrink drops exactly the tail
    [[addr+new_len, addr+old_len)] — the range [do_vmi_munmap] is given at
    mm/mremap.c:1096, v6.12 — and a grow zero-fills exactly the delta. *)
Definition mremap_inplace_effect (old old_n new_n : word)
    (old_nZ new_nZ : Z) : SyscallEffect :=
  if (new_nZ <? old_nZ)%Z
  then mkEffectU old [] []
         [(old + new_n,
           Z_to_bv 64 (old_nZ - new_nZ))] [] []
  else mkEffect old [] (mremap_tail old old_n old_nZ new_nZ).

(** A move relocates the whole source: [move_ptes] (mm/mremap.c:193-315,
    Linux v6.18.46) clears each source PTE with [get_and_clear_ptes]
    (:287) and installs it at the destination with [set_ptes] (:300), so
    the same physical pages appear at [dst]; untouched [pte_none] entries
    are skipped (:268-269) and refault as zeroes through
    [do_anonymous_page] (mm/memory.c:5149-5262) for a PRIVATE|ANONYMOUS
    VMA.  Hence the copy length
    is the WHOLE source, [old_n] — not [min old_n new_n].  A move only
    happens on growth ([mremap_spec] reaches [mremap_move_effect] only
    under [old_nZ < new_nZ], because Linux serves [old_len >= new_len] in
    place at mm/mremap.c:1088-1103), so the two agree and the [min] was
    dead generality.

    The source is then unmapped by [do_vmi_munmap] at mm/mremap.c:792,
    which is why the copy source is inside [eff_unmaps]: [Run.apply_copies]
    reads the PRE-EFFECT snapshot (Run.v:180), matching the kernel's order.
    The grown tail carries no page tables — neither [copy_vma] nor
    [vma_merge_extend] installs any for the delta — so it reads as fresh
    zeroes, which is [mremap_tail]. *)
Definition mremap_move_effect (old old_n dst : word) (old_nZ new_nZ : Z)
    : SyscallEffect :=
  mkEffectU dst [] (mremap_tail dst old_n old_nZ new_nZ) [(old, old_n)]
    [mkCopy old dst old_n] [].

(** The bounded [mremap(old,old_size,new_size,MREMAP_MAYMOVE)] shape used
    by musl realloc.  The source must be exactly one tracked readable/writable
    anonymous mapping.  Equal-size calls are no-ops; shrink removes/refunds
    the tail; grow may extend into a free adjacent range; and MAYMOVE permits
    a fresh disjoint placement that symbolically copies the preserved prefix,
    unmaps the old range, and zero-fills only a grown tail.

    ORDER, against [SYSCALL_DEFINE5(mremap)] (mm/mremap.c:1961-1994, Linux
    v6.18.46, whose body is [do_mremap], :1911-1952; the line numbers in
    this ORDER and RESULTS walk are v6.12's, when the whole walk sat in the
    syscall body, except where a citation names v6.18.46).  Which
    gate fires first is as much a part of the syscall as its result, so the
    branches below are in the kernel's order:

    - mm/mremap.c:1012, 1015, 1022 validate [flags] before any other
      argument is inspected.  One read does precede them — :1010,
      [addr = untagged_addr(addr)] — but on riscv64 it cannot change an
      answer: RISC-V pointer masking (Supm) postdates v6.12, so the arch
      defines no override and [untagged_addr] is the generic identity
      (include/linux/uaccess.h:25-26, v6.12).  A tagged [old] therefore
      keeps its tag through [offset_in_page] (:1027) and into [vma_lookup]
      (:1043), where arm64 would have stripped it at :1010, so Linux
      answers EFAULT for such an address while the model fails closed at
      [mremap_source_b] — the safe direction, and the reason the flag test
      really is the first gate that can decide the answer.  The model's
      narrower shape (exactly MREMAP_MAYMOVE) therefore fails closed
      first, ahead of the deterministic EINVAL below.  Linux answers a deterministic
      EINVAL for a flag word outside {FIXED, MAYMOVE, DONTUNMAP} (:1013) and
      serves [flags = 0] on exactly the same path as MAYMOVE (which nothing
      between :1080 and :1103 consults; its next read is :1165); modeling
      neither is a deliberate narrowing, not a fidelity claim.
    - mm/mremap.c:1027, [offset_in_page(addr)] -> EINVAL.
    - mm/mremap.c:1030-1031 round BOTH lengths with the wrapping
      [PAGE_ALIGN] (see [page_align_is0_b]) — before the
      [old_len == new_len] test at :1091, which is why a 4095-byte new size
      against a one-page source is an equal-size no-op and not a shrink —
      and then :1038 answers EINVAL when the rounded NEW length is zero.
      So a [new_size] in the top partial page is EINVAL, exactly like
      [new_size = 0]; the model says so rather than failing closed on the
      wrap.
    - a rounded OLD length of zero is the "duplicate a mapping" shape, which
      Linux refuses with EINVAL for a private mapping in [check_prep_vma]
      (mm/mremap.c:1690-1693, Linux v6.18.46; v6.12's [vma_to_resize] at
      :839-842) — but only after [vma_lookup] (:1043) and the
      seal check (:1050), and only on the growth path (:1108).  The model
      does not track enough to reproduce that EINVAL's preconditions, so it
      fails closed; it does so HERE, after the two EINVAL gates above, so
      that a misaligned address or a zero new size still gets Linux's answer.
      (An unmodeled answer need not precede a modeled one: being unmodeled
      says nothing about position, and Linux's position is :839, below both.
      [PAGE_ALIGN] at :1030 wraps a near-2^64 [old_size] to 0, so the wrap
      and the literal zero are the same case and share this gate.)
      The gate's two halves are NOT equally observable, and a trace pins
      neither, because both are
      fail-closed and any fail-closed route gives the same answer.  Delete the
      ZERO half and control reaches [mremap_source_b], whose
      [map_has] then needs a ledger entry of size exactly 0 — nothing a
      run can produce, but the [VmMaps] record carries no
      well-formedness predicate, so such a ledger is writable by hand.
      [Checks/Examples.v]'s [mremap_zero_entry_passes_the_source_gate] /
      [mremap_old_size_zero_gate_precedes_the_source_gate] is that pair:
      the first shows the fall-through would ACCEPT, the second that the
      answer is [Unmodeled] anyway, so the flip is attributable to this
      gate alone.  Delete the WRAP half and there is no such state:
      [old_nZ = 2^64] fails [mremap_source_b]'s [alloc_top] conjunct
      for EVERY address and every ledger, so no trace and no hand-built
      state can tell the two spellings apart.  It is kept because the
      gate must answer for the argument Linux actually rounds, and the
      honest pin is the redundancy itself —
      [mremap_wrapping_old_size_cannot_pass_the_source_gate], a [forall]
      over both.
    - mm/mremap.c:1043 requires a VMA at [addr], and nothing more on the
      equal-size and shrink paths: they never call [vma_to_resize], so
      [old_len] is never compared against [vma->vm_end - addr] (:849).  An
      equal-size call therefore succeeds and returns [addr] even when
      [[addr, addr+old_len)] spans a hole, several VMAs, or runs off the end
      of the mapping — the only other requirement is that the VMA is
      unsealed (:1050).  The model instead demands an exact tracked entry,
      which is a much larger narrowing than "not an exact entry" reads as;
      it is the safe direction (fail closed).

    RESULTS.  For [old_len >= new_len] Linux never moves: nothing between
    mm/mremap.c:1080 and :1103 reads MREMAP_MAYMOVE (its next read is
    :1165, the one place the flag decides whether a mapping may move; the
    earlier reads at :1015 and :1023 only reject FIXED and DONTUNMAP
    combinations), and the :1088 block returns [addr] outright — at :1092
    for the equal case, at :1101 once [do_vmi_munmap] has dropped the tail
    at :1096.  The two use different exits: the equal case leaves through
    [goto out] (:1093), which unlocks mmap_lock on the way out, while the
    shrink leaves through [goto out_unlocked] (:1102), because
    [do_vmi_munmap] was passed [unlock = true] (:1097) and has already
    dropped the lock.  Growth is the only case that can move, and it
    reaches :1165 only after the in-place expansion guarded by
    [vma_expandable] at :1120 has failed to return [addr] at :1155.

    The equal-size arm carries NO injectable failure.  Walking
    mm/mremap.c:1041-1093 for [flags = MREMAP_MAYMOVE], a non-hugetlb VMA
    that exists and is unsealed, and [old_len = new_len], the only exits are
    EINTR (:1042), EFAULT (:1045), EPERM (:1051), the hugetlb EINVALs
    (:1062-1072) and [ret = addr] (:1092) — all four errnos excluded by the
    modeled shape (see [mremap_errnos]).  There is no allocation, no VMA
    split and no accounting on that branch, so ENOMEM is unreachable and the
    [alt] with [Syscall.errno_from] must not cover it.  The shrink arm is different:
    [do_vmi_munmap] (:1096) splits the VMA and can fail to allocate
    (mm/vma.c:384-405) or exceed [sysctl_max_map_count] (mm/vma.c:1197).

    The choice between growing in place and moving is a genuine [alt],
    because Linux's in-place test reads state the model's ledger does not
    have: [vma_expandable] (mm/mremap.c:1415-1427, Linux v6.18.46) consults
    the next VMA in the maple tree, plus [TASK_SIZE], [mmap_min_addr] and
    the LSM hook through [get_unmapped_area] under MAP_FIXED
    ([__get_unmapped_area], mm/mmap.c:824, 857, 862, and
    [generic_get_unmapped_area], :697, or its topdown twin, :747);
    and :1116 requires [old_len == vma->vm_end - addr], which a kernel-side
    VMA merge can defeat.  Any of those can send Linux to the move path
    where the model sees free space, so the model admits both.  That
    argument does NOT apply to the equal-size and shrink arms — they never
    reach [vma_expandable] — which is why those two are deterministic.

    An injected ENOMEM leaves no memory effects: [move_vma] moves the page
    tables back (mm/mremap.c:730-737), swaps its bookkeeping (:738-741) and
    unmaps the NEW area at :792, i.e. it rolls back.  The argument is
    specific to MAYMOVE: under MREMAP_FIXED the destination is destroyed at
    :918 before the source is validated at :930, so THAT errno does have
    memory effects.  FIXED is unmodeled.

    BOUNDED APPROXIMATION, and it is on the SUCCESS path, not only the
    failure one.  The unmap at mm/mremap.c:792 is the same call site for
    both, and when it fails its error is SWALLOWED (:793-797, "OOM: unable
    to split vma, just get accounts right"): [move_vma] carries on and
    returns [new_addr] at :817.  So a successful Linux mremap can leave the
    source range still mapped, at an address the program knows.  The model
    always emits [eff_unmaps [(old, old_n)]] and always drops [old] from the
    ledger, so it says that range is gone when a doubly-unlucky kernel would
    still serve its bytes.

    What makes it reachable is the same thing named for the shrink path in
    [mremap_errnos]: Linux only requires [old_len <= vma->vm_end - addr]
    (mm/mremap.c:849), so the model's exact ledger entry can be a strict
    prefix of a merged kernel VMA; [do_vmi_munmap] then has to split, and a
    split can fail on allocation (mm/vma.c:384, 394, 399, 403) or on
    [sysctl_max_map_count] (mm/vma.c:1197).  The model has no shape for
    "mapped at both addresses" and does not attempt one.  The cost is a
    fidelity gap in the modeled semantics, not a checker unsoundness: what
    the model's ledger claims is FREE stays a superset of what is really
    free, so no real placement is ever refused because of it.  That is the
    claim [Checks/Examples.v]'s [mremap_move_gap_is_the_retained_source]
    proves, together with the bound — the two free sets differ only over the
    retained source.

    The fifth syscall argument is ignored, and the reason is not that only
    MREMAP_FIXED reads it.  Linux reads [new_addr] in three places:
    mm/mremap.c:1064 unconditionally inside the hugetlb block, and
    mm/mremap.c:1075 for FIXED *or* DONTUNMAP (both routed into
    [mremap_to]).  Under this shape the hugetlb block is unreachable (the
    source is one tracked PRIVATE|ANONYMOUS mapping) and both flags are
    unmodeled, so the only remaining use is :1170, where
    [get_unmapped_area] OVERWRITES [new_addr] before it is read.

    Size rounding is done in [Z] and checked before conversion back to
    [word].  Protected/mixed/non-exact sources, FIXED, DONTUNMAP, and every
    other flag combination fail closed. *)
Definition mremap_spec (old old_size new_size flags : word)
    : Sys SyscallEffect :=
  (* This gate declines TWO different kernel answers, and only one of them
     is a refusal.  Linux rejects a flag word outside
     {FIXED, MAYMOVE, DONTUNMAP} with a deterministic EINVAL
     (mm/mremap.c:1012-1024), but it ACCEPTS [flags = 0]: nothing between
     :1088 and :1103 reads MREMAP_MAYMOVE, so equal-size, shrink and
     in-place grow all succeed exactly as they do under MAYMOVE, and the
     flag first matters at :1165, where a call that must MOVE gets the
     -ENOMEM parked at :1164.  Declining [flags = 0] is therefore a
     deliberate narrowing of the modeled surface -- announced here and in
     the ORDER note above -- not a claim that Linux fails.  It is the safe
     direction: [unmodeled] never asserts a wrong result. *)
  if negb (Z.eqb (bv_unsigned flags) MREMAP_MAYMOVE)
  then unmodeled
  else if negb (Z.eqb (bv_unsigned old mod page_size) 0)
  then err_ret EINVAL                              (* mm/mremap.c:1027 *)
  else if page_align_is0_b new_size
  then err_ret EINVAL                              (* mm/mremap.c:1031, 1038 *)
  else if page_align_is0_b old_size
  then unmodeled                                   (* clone: mm/mremap.c:839 *)
  else
    m <- get_model ;;
    let h := m_vmmaps m in
    let old_nZ := page_round_up_Z (bv_unsigned old_size) in
    let new_nZ := page_round_up_Z (bv_unsigned new_size) in
    let old_n := Z_to_bv 64 old_nZ in
    let new_n := Z_to_bv 64 new_nZ in
    if negb (mremap_source_b h old old_n old_nZ
             && mremap_backing_uniform_b m old old_n)
    then unmodeled                                 (* mm/mremap.c:1043 *)
    else if Z.eqb old_nZ new_nZ
    then ret_only old                              (* mm/mremap.c:1091-1093 *)
    else
      alt
        (e <- errno_from mremap_errnos ;; err_ret e)
        (if (new_nZ <? old_nZ)%Z then
           modify (fun _ => mremap_model_next m old old_n old new_n) ;;
           pure (mremap_inplace_effect old old_n new_n old_nZ new_nZ)
         else
           let move :=
             dst <- choose (fun dst =>
                mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true) ;;
             modify (fun _ => mremap_model_next m old old_n dst new_n) ;;
             pure (mremap_move_effect old old_n dst old_nZ new_nZ) in
           if mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ
           then alt
             (modify (fun _ => mremap_model_next m old old_n old new_n) ;;
              pure (mremap_inplace_effect old old_n new_n old_nZ new_nZ))
             move
           else move).

(* =========================================================================
   THE BUDGET MARK for mremap (see [Mmap.brk_budget_refused_b] for what
   a mark is)
   ========================================================================= *)

(** THE MOVE'S CHARGE, WITH THE DESTINATION FACTORED OUT.

    A grow's budget gate is [mremap_final_budget_b] on the complete
    post-state, and the moved resolution's post-state depends on the
    destination [dst] the [choose] picks — which the mark, reading only
    the request and the state, does not have.  It does not need it.  At
    a destination that is FRESH — disjoint from every live mapping and
    carrying no protected bytes, no lazy reservation and no materialized
    page — the re-created mapping is charged in full when the source is
    eager and not at all when it is lazy (its materialized pages move
    with it and are charged by count), and nothing else in the
    post-state mentions [dst]: [mremap_maps_next] drops [old] and conses
    the destination, [State.vm_resize_backing] cuts the source's own
    reservation and pages out of the two backing ledgers and re-records
    the moved pages at destination-relative offsets, whose COUNT is what
    [State.vm_backing_used] reads.  So the charge is one number for every
    fresh destination, and this is that number, written out of the same
    pieces [vm_resize_backing] assembles: what is left of the ledger once
    [old] is gone, the re-created mapping's own charge, and the page
    count.  [mremap_move_charge_at_fresh] proves it equal to the gate's
    reading at any destination of that shape; [mremap_fresh_b] supplies
    the live-mapping half of "fresh" and [State.noaccess_pages_owned]
    (through [mremap_fresh_avoids_noaccess]) the protected half; the
    lazy and materialized halves are the ledger invariant the writers of
    [vm_lazy] keep — every reservation lies under a live mapping — which
    is not yet a proved invariant and is taken as a hypothesis where
    the lemma is used. *)
Definition mremap_move_charge (m : Model) (old old_n new_n : word) : Z :=
  let h := m_vmmaps m in
  let old_lo := bv_unsigned old in
  let old_hi := (old_lo + bv_unsigned old_n)%Z in
  let source_lazy := mremap_source_lazy_b m old old_n in
  let kept_lazy := maps_subtract (m_vm_lazy m) old_lo old_hi in
  let kept_pages :=
    List.filter (page_outside_range old_lo old_hi) (m_vm_materialized m) in
  let moved_pages :=
    if source_lazy then
      List.filter
        (fun p => page_in_half_open old_lo old_hi p
                  && (bv_unsigned p - old_lo <? bv_unsigned new_n)%Z)
        (m_vm_materialized m)
    else [] in
  (live_bytes
     (maps_subtract_all
        (maps_subtract_all (map_remove (vm_maps h) old) (vm_noaccess h))
        kept_lazy)
   + (if source_lazy then 0 else bv_unsigned new_n)
   + Z.of_nat (List.length moved_pages + List.length kept_pages) * page_size)%Z.

(** The move's budget gate, destination-free: the same comparison
    [State.vm_backing_within_limit] makes, on the charge above. *)
Definition mremap_move_budget_b (m : Model) (old old_n new_n : word) : bool :=
  (mremap_move_charge m old old_n new_n <=? vm_limit (m_vmmaps m))%Z.

(** Only a GROW charges, and a grow has two non-errno resolutions, each
    behind its own reading of [mremap_final_budget_b]: in place, on the
    mapping grown at [old], admitted when [mremap_inplace_grow_b] holds
    (room above the source AND its budget gate passing); and moved, on
    the mapping re-created at a fresh [dst], whose gate reads the same
    charge at every fresh destination, [mremap_move_budget_b].

    THE MARK FIRES WHEN NO PLACEMENT FITS THE BUDGET: the in-place
    resolution is not admitted AND the move's budget gate refuses.  That
    is the request Linux refuses for want of memory: where the in-place
    resolution is unavailable and a move fits, Linux moves the mapping
    ([expand_vma], mm/mremap.c:1520-1543, Linux v6.18.46, which picks
    the new address in [vrm_set_new_addr], :957-960) and the call
    succeeds.  Neither gate alone is the right test, because
    neither post-state is charged at least as much as the other on
    every state:

    - the in-place post-state can be charged MORE.  The grown tail may
      lie over a lazy neighbour; the in-place evaluation clears that
      neighbour's reservation under the tail and charges its bytes
      eagerly, where a move leaves the neighbour alone.  On such a state
      the in-place gate refuses while a move fits, and the mark is
      silent ([Checks/BudgetPremise.v]'s [ov_mark_silent_while_a_move_fits]);
    - the in-place post-state can be charged LESS.  The charge is
      [State.live_bytes] of [State.vm_backed_maps], which subtracts
      [vm_noaccess] — NOT of [vm_maps].  A PROT_NONE mapping directly
      above the source leaves the grown tail's bytes uncharged in place,
      while a move re-creates the whole mapping at a fresh destination
      and is charged every byte of it.  In-place growth is unavailable
      there (the tail meets a live mapping), so the move is the only
      non-errno resolution, it is budget-refused, and the mark fires
      although the in-place gate alone passes
      ([Checks/BudgetPremise.v]'s [un_mark_fires_on_the_move_refusal]).

    The mark stays placement-independent: it reads neither which
    resolution the [alt] takes nor the destination the [choose] picks,
    only whether in-place growth is admitted and the destination-free
    charge of a move.  It does not ask whether a fresh destination
    EXISTS: an address space with no free range is a refusal of its own
    kind, not of the budget, and is not marked unless the move's charge
    is also over the budget.

    An earlier version fired when EITHER gate refused, and so over-marked
    the first case above: an execution Linux completes by moving counted
    as budget-refused, and [Run.source_within_budget] dropped the input.
    The present mark implies that one and not conversely
    ([Checks/BudgetPremise.v]'s
    [mremap_budget_refused_implies_two_gate] and
    [ov_two_gate_fires_where_the_mark_is_silent]).

    [Checks/BudgetPremise.v] pins the rule: [mremap_budget_refused_iff]
    (the mark, on a grow past the argument gates, is exactly "not
    admitted in place and the move's gate refuses");
    [mremap_budget_refused_refuses_inplace] (where the mark fires, the
    in-place resolution is not admitted) and
    [mremap_budget_refused_refuses_move] (where the mark fires, no fresh
    destination that carries no backing metadata is admitted) —
    together, a marked request has no non-errno resolution on a state
    keeping the ledger invariants;
    [mremap_budget_refused_fires_on_move_refusal] (in-place unavailable
    and the move refused at one fresh destination that carries no
    backing metadata fires the mark); and the concrete states above.
    Shrinks, the equal-size answer, and every shape the arm declines or
    answers -EINVAL are not budget refusals. *)
Definition mremap_budget_refused_b (old old_size new_size flags : word)
    (m : Model) : bool :=
  if negb (Z.eqb (bv_unsigned flags) MREMAP_MAYMOVE) then false
  else if negb (Z.eqb (bv_unsigned old mod page_size) 0) then false
  else if page_align_is0_b new_size then false
  else if page_align_is0_b old_size then false
  else
    let h := m_vmmaps m in
    let old_nZ := page_round_up_Z (bv_unsigned old_size) in
    let new_nZ := page_round_up_Z (bv_unsigned new_size) in
    let old_n := Z_to_bv 64 old_nZ in
    let new_n := Z_to_bv 64 new_nZ in
    if negb (mremap_source_b h old old_n old_nZ
             && mremap_backing_uniform_b m old old_n)
    then false
    else if (new_nZ <=? old_nZ)%Z then false
    else negb (mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ
               || mremap_move_budget_b m old old_n new_n).

(* -------------------------------------------------------------------------
   Destination independence of the move's charge
   ------------------------------------------------------------------------- *)

(** The list arithmetic behind [mremap_move_charge_at_fresh].  Every
    lemma here is about [State.maps_subtract] and its iteration
    [State.maps_subtract_all], read as a byte count through
    [State.live_bytes]; none of them is specific to mremap, and none is
    stated elsewhere, so they live beside their one consumer. *)

Lemma mremap_word_range : forall w : word,
  (0 <= bv_unsigned w < two_pow_64)%Z.
Proof.
  intro w. pose proof (bv_unsigned_in_range 64 w) as H.
  change (bv_modulus 64) with two_pow_64 in H. exact H.
Qed.

Lemma mremap_u64 : forall z,
  (0 <= z < two_pow_64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. apply Z_to_bv_small. change (bv_modulus 64) with two_pow_64.
  exact Hz.
Qed.

Lemma live_bytes_app : forall l1 l2,
  live_bytes (l1 ++ l2) = (live_bytes l1 + live_bytes l2)%Z.
Proof.
  induction l1 as [|[a sz] r IH]; intros l2; cbn [live_bytes app];
    [reflexivity | rewrite IH; lia].
Qed.

Lemma live_bytes_nonneg : forall l, (0 <= live_bytes l)%Z.
Proof.
  induction l as [|[a sz] r IH]; cbn [live_bytes]; [lia |].
  pose proof (mremap_word_range sz). lia.
Qed.

Lemma maps_subtract_app : forall l1 l2 lo hi,
  maps_subtract (l1 ++ l2) lo hi
  = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi.
Proof.
  induction l1 as [|[a sz] r IH]; intros l2 lo hi; cbn [maps_subtract app];
    [reflexivity | rewrite IH, app_assoc; reflexivity].
Qed.

Lemma maps_subtract_all_app : forall cuts l1 l2,
  maps_subtract_all (l1 ++ l2) cuts
  = maps_subtract_all l1 cuts ++ maps_subtract_all l2 cuts.
Proof.
  induction cuts as [|[a n] r IH]; intros l1 l2; cbn [maps_subtract_all];
    [reflexivity | rewrite maps_subtract_app; apply IH].
Qed.

(** A cut that misses an entry leaves it exactly as it was.  The entry
    must be nonempty: [iv_subtract] drops an empty entry sitting at the
    cut's base, and an empty entry is not something the two [region_free]
    readings agree about either. *)
Lemma iv_subtract_disjoint : forall (a sz : word) lo hi,
  (0 < bv_unsigned sz)%Z ->
  (lo <= hi)%Z ->
  (bv_unsigned a + bv_unsigned sz <= lo \/ hi <= bv_unsigned a)%Z ->
  iv_subtract a sz lo hi = [(a, sz)].
Proof.
  intros a sz lo hi Hpos Hlohi Hdisj. unfold iv_subtract. cbv zeta.
  destruct (bv_unsigned a <? lo)%Z eqn:E1;
    [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1];
  destruct (hi <? bv_unsigned a + bv_unsigned sz)%Z eqn:E2;
    [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2
    | apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2];
  cbn [app].
  - exfalso. lia.
  - rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite Z.max_l by lia.
    replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a)%Z
      with (bv_unsigned sz) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
  - exfalso. lia.
Qed.

(** ...so a nonempty entry that is [region_free] of a cut list survives
    the whole list. *)
Lemma maps_subtract_all_disjoint_entry : forall cuts (a sz : word),
  (0 < bv_unsigned sz)%Z ->
  region_free cuts a sz = true ->
  maps_subtract_all [(a, sz)] cuts = [(a, sz)].
Proof.
  induction cuts as [|[lo n] r IH]; intros a sz Hpos Hfree; [reflexivity |].
  cbn [region_free] in Hfree.
  apply andb_true_iff in Hfree as [Hov Hfree]. apply negb_true_iff in Hov.
  unfold iv_overlap in Hov. apply andb_false_iff in Hov.
  pose proof (mremap_word_range n).
  cbn [maps_subtract_all maps_subtract].
  rewrite iv_subtract_disjoint;
    [cbn [app]; apply IH; assumption | exact Hpos | lia |].
  destruct Hov as [Hov | Hov]; apply Z.ltb_ge in Hov; lia.
Qed.

(** Cuts only remove bytes. *)
Lemma live_bytes_iv_subtract_le : forall (a sz : word) lo hi,
  (lo <= hi)%Z ->
  (live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz)%Z.
Proof.
  intros a sz lo hi Hlohi. unfold iv_subtract. cbv zeta.
  pose proof (mremap_word_range a). pose proof (mremap_word_range sz).
  destruct (bv_unsigned a <? lo)%Z eqn:E1;
    [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1];
  destruct (hi <? bv_unsigned a + bv_unsigned sz)%Z eqn:E2;
    [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2
    | apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2];
  cbn [app live_bytes].
  - rewrite mremap_u64 by (pose proof (Z.min_spec (bv_unsigned sz) (lo - bv_unsigned a)); lia).
    rewrite mremap_u64 by (pose proof (Z.max_spec (bv_unsigned a) hi); lia).
    pose proof (Z.min_spec (bv_unsigned sz) (lo - bv_unsigned a)).
    pose proof (Z.max_spec (bv_unsigned a) hi). lia.
  - rewrite mremap_u64 by (pose proof (Z.min_spec (bv_unsigned sz) (lo - bv_unsigned a)); lia).
    pose proof (Z.min_spec (bv_unsigned sz) (lo - bv_unsigned a)). lia.
  - rewrite mremap_u64 by (pose proof (Z.max_spec (bv_unsigned a) hi); lia).
    pose proof (Z.max_spec (bv_unsigned a) hi). lia.
  - lia.
Qed.

Lemma live_bytes_maps_subtract_le : forall l lo hi,
  (lo <= hi)%Z ->
  (live_bytes (maps_subtract l lo hi) <= live_bytes l)%Z.
Proof.
  induction l as [|[a sz] r IH]; intros lo hi Hlohi; cbn [maps_subtract live_bytes];
    [lia |].
  rewrite live_bytes_app.
  pose proof (live_bytes_iv_subtract_le a sz lo hi Hlohi).
  pose proof (IH lo hi Hlohi). lia.
Qed.

Lemma live_bytes_maps_subtract_all_le : forall cuts l,
  (live_bytes (maps_subtract_all l cuts) <= live_bytes l)%Z.
Proof.
  induction cuts as [|[a n] r IH]; intros l; cbn [maps_subtract_all]; [lia |].
  pose proof (mremap_word_range n).
  pose proof (live_bytes_maps_subtract_le l (bv_unsigned a)
                (bv_unsigned a + bv_unsigned n) ltac:(lia)).
  pose proof (IH (maps_subtract l (bv_unsigned a) (bv_unsigned a + bv_unsigned n))).
  lia.
Qed.

(** A cut that misses every entry of a ledger changes no byte count,
    whatever cuts follow it.  Stated on the count rather than the list
    because an EMPTY entry at the cut's base is dropped by [iv_subtract]
    and kept by the identity — a difference no byte count can see. *)
Lemma live_bytes_subtract_free : forall cuts l lo hi,
  (lo <= hi)%Z ->
  (forall (b s : word), In (b, s) l ->
     (bv_unsigned b + bv_unsigned s <= lo \/ hi <= bv_unsigned b)%Z) ->
  live_bytes (maps_subtract_all (maps_subtract l lo hi) cuts)
  = live_bytes (maps_subtract_all l cuts).
Proof.
  intros cuts l lo hi Hlohi.
  induction l as [|[a sz] r IH]; intros Hfree; [reflexivity |].
  cbn [maps_subtract].
  change ((a, sz) :: r) with ([(a, sz)] ++ r).
  rewrite !maps_subtract_all_app, !live_bytes_app.
  rewrite IH by (intros b s Hin; apply Hfree; right; exact Hin).
  f_equal.
  destruct (Z.eq_dec (bv_unsigned sz) 0) as [Hz | Hz].
  - (* an empty entry is weightless on both sides *)
    pose proof (live_bytes_maps_subtract_all_le cuts (iv_subtract a sz lo hi)) as H1.
    pose proof (live_bytes_maps_subtract_all_le cuts [(a, sz)]) as H2.
    pose proof (live_bytes_nonneg (maps_subtract_all (iv_subtract a sz lo hi) cuts)).
    pose proof (live_bytes_nonneg (maps_subtract_all [(a, sz)] cuts)).
    pose proof (live_bytes_iv_subtract_le a sz lo hi Hlohi).
    cbn [live_bytes] in H2. lia.
  - pose proof (mremap_word_range sz).
    rewrite iv_subtract_disjoint;
      [reflexivity | lia | exact Hlohi | apply Hfree; left; reflexivity].
Qed.

(** Each remnant of a cut lies inside the entry it came from, provided
    the entry lies inside the address space (a right remnant's base is
    re-wrapped through [Z_to_bv]). *)
Lemma iv_subtract_within : forall (a sz : word) lo hi (b s : word),
  (bv_unsigned a + bv_unsigned sz <= two_pow_64)%Z ->
  In (b, s) (iv_subtract a sz lo hi) ->
  (bv_unsigned a <= bv_unsigned b
   /\ bv_unsigned b + bv_unsigned s <= bv_unsigned a + bv_unsigned sz)%Z.
Proof.
  intros a sz lo hi b s Hfit Hin. unfold iv_subtract in Hin. cbv zeta in Hin.
  pose proof (mremap_word_range a). pose proof (mremap_word_range sz).
  apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - destruct (bv_unsigned a <? lo)%Z eqn:E1; cbn in Hin; [| contradiction].
    apply Z.ltb_lt in E1. destruct Hin as [Heq | []]. inversion Heq; subst b s.
    pose proof (Z.min_spec (bv_unsigned sz) (lo - bv_unsigned a)).
    rewrite mremap_u64 by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz)%Z eqn:E2; cbn in Hin;
      [| contradiction].
    apply Z.ltb_lt in E2. destruct Hin as [Heq | []]. inversion Heq; subst b s.
    pose proof (Z.max_spec (bv_unsigned a) hi).
    rewrite !mremap_u64 by lia. lia.
Qed.

Lemma maps_subtract_In : forall l lo hi (b s : word),
  In (b, s) (maps_subtract l lo hi) ->
  exists (a sz : word), In (a, sz) l /\ In (b, s) (iv_subtract a sz lo hi).
Proof.
  induction l as [|[a sz] r IH]; intros lo hi b s Hin; [contradiction |].
  cbn [maps_subtract] in Hin. apply in_app_or in Hin.
  destruct Hin as [Hin | Hin].
  - exists a, sz. split; [left; reflexivity | exact Hin].
  - destruct (IH lo hi b s Hin) as [a' [sz' [Hin' Hiv]]].
    exists a', sz'. split; [right; exact Hin' | exact Hiv].
Qed.

Lemma maps_subtract_all_within : forall cuts l (b s : word),
  (forall (a sz : word), In (a, sz) l ->
     (bv_unsigned a + bv_unsigned sz <= two_pow_64)%Z) ->
  In (b, s) (maps_subtract_all l cuts) ->
  exists (a sz : word),
    In (a, sz) l
    /\ (bv_unsigned a <= bv_unsigned b
        /\ bv_unsigned b + bv_unsigned s <= bv_unsigned a + bv_unsigned sz)%Z.
Proof.
  induction cuts as [|[c n] r IH]; intros l b s Hfit Hin.
  - exists b, s. split; [exact Hin | lia].
  - cbn [maps_subtract_all] in Hin.
    assert (Hfit' : forall (a sz : word),
              In (a, sz) (maps_subtract l (bv_unsigned c)
                            (bv_unsigned c + bv_unsigned n)) ->
              (bv_unsigned a + bv_unsigned sz <= two_pow_64)%Z).
    { intros a sz Hin'.
      destruct (maps_subtract_In _ _ _ _ _ Hin') as [a0 [sz0 [Hin0 Hiv]]].
      pose proof (Hfit a0 sz0 Hin0).
      pose proof (iv_subtract_within _ _ _ _ _ _ (Hfit a0 sz0 Hin0) Hiv). lia. }
    destruct (IH (maps_subtract l (bv_unsigned c) (bv_unsigned c + bv_unsigned n))
                b s Hfit' Hin) as [a' [sz' [Hin' Hw']]].
    destruct (maps_subtract_In _ _ _ _ _ Hin') as [a0 [sz0 [Hin0 Hiv]]].
    pose proof (Hfit a0 sz0 Hin0).
    pose proof (iv_subtract_within _ _ _ _ _ _ (Hfit a0 sz0 Hin0) Hiv).
    exists a0, sz0. split; [exact Hin0 | lia].
Qed.

(** The remnants of a cut miss the cut: what [iv_subtract] keeps is the
    part of the entry BELOW the cut's base and the part AT OR ABOVE its
    end.  The end must be an address, since the right remnant's base is
    re-wrapped through [Z_to_bv]. *)
Lemma iv_subtract_misses_cut : forall (c sz : word) lo hi (b s : word),
  (0 <= lo)%Z -> (hi < two_pow_64)%Z ->
  In (b, s) (iv_subtract c sz lo hi) ->
  (bv_unsigned b + bv_unsigned s <= lo \/ hi <= bv_unsigned b)%Z.
Proof.
  intros c sz lo hi b s Hlo Hhi Hin. unfold iv_subtract in Hin. cbv zeta in Hin.
  pose proof (mremap_word_range c). pose proof (mremap_word_range sz).
  apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - destruct (bv_unsigned c <? lo)%Z eqn:E1; cbn in Hin; [| contradiction].
    apply Z.ltb_lt in E1. destruct Hin as [Heq | []]. inversion Heq; subst b s.
    pose proof (Z.min_spec (bv_unsigned sz) (lo - bv_unsigned c)).
    rewrite mremap_u64 by lia. lia.
  - destruct (hi <? bv_unsigned c + bv_unsigned sz)%Z eqn:E2; cbn in Hin;
      [| contradiction].
    apply Z.ltb_lt in E2. destruct Hin as [Heq | []]. inversion Heq; subst b s.
    pose proof (Z.max_spec (bv_unsigned c) hi).
    rewrite (mremap_u64 (Z.max (bv_unsigned c) hi)) by lia. lia.
Qed.

Lemma maps_subtract_misses_cut : forall l lo hi (b s : word),
  (0 <= lo)%Z -> (hi < two_pow_64)%Z ->
  In (b, s) (maps_subtract l lo hi) ->
  (bv_unsigned b + bv_unsigned s <= lo \/ hi <= bv_unsigned b)%Z.
Proof.
  intros l lo hi b s Hlo Hhi Hin.
  destruct (maps_subtract_In l lo hi b s Hin) as [a [sz [_ Hiv]]].
  exact (iv_subtract_misses_cut a sz lo hi b s Hlo Hhi Hiv).
Qed.

(** Cutting an entry out of itself leaves nothing, and nothing stays
    nothing under further cuts. *)
Lemma iv_subtract_self : forall (a n : word),
  iv_subtract a n (bv_unsigned a) (bv_unsigned a + bv_unsigned n) = [].
Proof.
  intros a n. unfold iv_subtract. cbv zeta.
  rewrite (proj2 (Z.ltb_ge _ _) (Z.le_refl (bv_unsigned a))).
  rewrite (proj2 (Z.ltb_ge _ _) (Z.le_refl (bv_unsigned a + bv_unsigned n))).
  reflexivity.
Qed.

Lemma maps_subtract_all_nil : forall cuts, maps_subtract_all [] cuts = [].
Proof. induction cuts as [|[a n] r IH]; [reflexivity | exact IH]. Qed.

(** A page-aligned, page-sized, nonempty reservation is its own
    interior. *)
Lemma lazy_interior_aligned : forall (a n : word),
  (bv_unsigned a mod page_size = 0)%Z ->
  (bv_unsigned n mod page_size = 0)%Z ->
  (0 < bv_unsigned n)%Z ->
  lazy_interior a n = [(a, n)].
Proof.
  intros a n Ha Hn Hpos. unfold lazy_interior. cbv zeta.
  pose proof (mremap_word_range a). pose proof (mremap_word_range n).
  assert (Hps : page_size <> 0%Z) by (unfold page_size; lia).
  assert (Hqa : bv_unsigned a = (page_size * (bv_unsigned a / page_size))%Z)
    by (apply (Z.div_exact (bv_unsigned a) page_size Hps); exact Ha).
  assert (Hqn : bv_unsigned n = (page_size * (bv_unsigned n / page_size))%Z)
    by (apply (Z.div_exact (bv_unsigned n) page_size Hps); exact Hn).
  set (qa := (bv_unsigned a / page_size)%Z) in *.
  set (qn := (bv_unsigned n / page_size)%Z) in *.
  assert (Hlo : ((bv_unsigned a + page_size - 1) / page_size * page_size)%Z
                = bv_unsigned a).
  { rewrite Hqa. unfold page_size.
    replace (4096 * qa + 4096 - 1)%Z with (qa * 4096 + 4095)%Z by lia.
    rewrite Z.div_add_l by lia. rewrite (Z.div_small 4095 4096) by lia. lia. }
  assert (Hhi : ((bv_unsigned a + bv_unsigned n) / page_size * page_size)%Z
                = (bv_unsigned a + bv_unsigned n)%Z).
  { rewrite Hqa, Hqn. unfold page_size.
    replace (4096 * qa + 4096 * qn)%Z with ((qa + qn) * 4096)%Z by lia.
    rewrite Z.div_mul by lia. lia. }
  rewrite Hlo, Hhi.
  destruct (bv_unsigned a <? bv_unsigned a + bv_unsigned n)%Z eqn:E;
    [| apply Z.ltb_ge in E; lia].
  replace (bv_unsigned a + bv_unsigned n - bv_unsigned a)%Z
    with (bv_unsigned n) by lia.
  rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

(** THE LEMMA: at any destination that is fresh and carries no backing
    metadata, the moved post-state's charge is [mremap_move_charge].

    The hypotheses are the "fresh" of the header, spelled ledger by
    ledger: [dst] is page aligned and the request page-sized and
    nonempty (so the lazy interior a lazy source re-records is exactly
    the destination); the request ends inside the address space (so a
    remnant's re-wrapped base is its base); every live mapping other than
    the source lies inside the address space and misses the destination;
    so does every protected range; cutting the destination out of the
    lazy ledger — after the source's own reservation is gone — changes
    nothing; and no materialized page outside the source lies under the
    destination.  The last two are the identity form of "the destination
    carries no lazy reservation and no materialized page", taken on the
    ledgers [State.vm_resize_backing] actually reads. *)
Lemma mremap_move_charge_at_fresh : forall m old old_n dst new_n,
  (bv_unsigned dst mod page_size = 0)%Z ->
  (bv_unsigned new_n mod page_size = 0)%Z ->
  (0 < bv_unsigned new_n)%Z ->
  (bv_unsigned dst + bv_unsigned new_n < two_pow_64)%Z ->
  (forall (a sz : word), In (a, sz) (map_remove (vm_maps (m_vmmaps m)) old) ->
     (bv_unsigned a + bv_unsigned sz <= two_pow_64)%Z) ->
  region_free (map_remove (vm_maps (m_vmmaps m)) old) dst new_n = true ->
  region_free (vm_noaccess (m_vmmaps m)) dst new_n = true ->
  maps_subtract
    (maps_subtract (m_vm_lazy m) (bv_unsigned old)
       (bv_unsigned old + bv_unsigned old_n))
    (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n)
  = maps_subtract (m_vm_lazy m) (bv_unsigned old)
      (bv_unsigned old + bv_unsigned old_n) ->
  List.filter (page_outside_range (bv_unsigned dst)
                 (bv_unsigned dst + bv_unsigned new_n))
    (List.filter (page_outside_range (bv_unsigned old)
                    (bv_unsigned old + bv_unsigned old_n))
       (m_vm_materialized m))
  = List.filter (page_outside_range (bv_unsigned old)
                   (bv_unsigned old + bv_unsigned old_n))
      (m_vm_materialized m) ->
  vm_backing_used (mremap_model_next m old old_n dst new_n)
  = mremap_move_charge m old old_n new_n.
Proof.
  intros m old old_n dst new_n Halign Hnalign Hpos Hend Hfit Hmaps Hnoacc
    Hlazy Hpages.
  (* the post-state's projections, by conversion: the accessors are
     [simpl never] *)
  assert (P1 : forall L P m', m_vmmaps (with_vm_backing L P m') = m_vmmaps m')
    by reflexivity.
  assert (P2 : forall L P m', m_vm_lazy (with_vm_backing L P m') = L)
    by reflexivity.
  assert (P3 : forall L P m', m_vm_materialized (with_vm_backing L P m') = P)
    by reflexivity.
  assert (P4 : forall h m', m_vmmaps (with_vmmaps h m') = h) by reflexivity.
  assert (P5 : forall h m', m_vm_lazy (with_vmmaps h m') = m_vm_lazy m')
    by reflexivity.
  assert (P6 : forall h m', m_vm_materialized (with_vmmaps h m')
                            = m_vm_materialized m') by reflexivity.
  unfold vm_backing_used, mremap_move_charge, mremap_model_next,
    vm_resize_backing, mremap_maps_next.
  cbv zeta.
  rewrite !P1, !P2, !P3, !P4, !P5, !P6.
  unfold vm_backed_maps. cbn [vm_maps vm_noaccess vm_limit].
  set (KL := maps_subtract (m_vm_lazy m) (bv_unsigned old)
               (bv_unsigned old + bv_unsigned old_n)) in *.
  set (KP := List.filter (page_outside_range (bv_unsigned old)
                            (bv_unsigned old + bv_unsigned old_n))
               (m_vm_materialized m)) in *.
  set (R0 := map_remove (vm_maps (m_vmmaps m)) old) in *.
  set (NA := vm_noaccess (m_vmmaps m)) in *.
  (* KL misses the destination: by the identity, every entry of KL is a
     remnant of cutting the destination out of it *)
  assert (HKL : region_free KL dst new_n = true).
  { apply region_free_intro. intros a n Hin.
    rewrite <- Hlazy in Hin.
    pose proof (mremap_word_range dst).
    pose proof (maps_subtract_misses_cut KL (bv_unsigned dst)
                  (bv_unsigned dst + bv_unsigned new_n) a n ltac:(lia) Hend Hin)
      as Hm.
    unfold iv_overlap. apply andb_false_iff.
    destruct Hm as [Hm | Hm]; [left | right]; apply Z.ltb_ge; lia. }
  rewrite Hlazy, Hpages.
  rewrite length_app.
  change ((dst, new_n) :: R0) with ([(dst, new_n)] ++ R0).
  rewrite maps_subtract_all_app.
  rewrite (maps_subtract_all_disjoint_entry NA dst new_n Hpos Hnoacc).
  (* remnants of R0 miss the destination *)
  assert (HR : forall (b s : word), In (b, s) (maps_subtract_all R0 NA) ->
            (bv_unsigned b + bv_unsigned s <= bv_unsigned dst
             \/ bv_unsigned dst + bv_unsigned new_n <= bv_unsigned b)%Z).
  { intros b s Hin.
    destruct (maps_subtract_all_within NA R0 b s Hfit Hin) as [a [sz [Hin0 Hw]]].
    pose proof (region_free_In R0 dst new_n a sz Hmaps Hin0) as Hov.
    unfold iv_overlap in Hov. apply andb_false_iff in Hov.
    destruct Hov as [Hov | Hov]; apply Z.ltb_ge in Hov; lia. }
  destruct (mremap_source_lazy_b m old old_n) eqn:Hsrc.
  - (* lazy source: the re-created mapping is its own lazy interior *)
    rewrite (lazy_interior_aligned dst new_n Halign Hnalign Hpos).
    rewrite length_map.
    rewrite maps_subtract_all_app, live_bytes_app.
    cbn [app].
    cbn [maps_subtract_all maps_subtract].
    rewrite iv_subtract_self. cbn [app]. rewrite maps_subtract_all_nil.
    cbn [live_bytes].
    rewrite (live_bytes_subtract_free KL (maps_subtract_all R0 NA)
               (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n)
               ltac:(lia) HR).
    lia.
  - (* eager source: the re-created mapping is charged whole *)
    rewrite maps_subtract_all_app, live_bytes_app.
    rewrite (maps_subtract_all_disjoint_entry KL dst new_n Hpos HKL).
    cbn [live_bytes]. lia.
Qed.
