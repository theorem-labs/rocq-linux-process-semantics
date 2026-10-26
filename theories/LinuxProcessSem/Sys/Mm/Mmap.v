(** * LinuxProcessSem.Sys.Mm.Mmap — brk (214), mmap (222), munmap (215)

    This file answers to Linux [mm/mmap.c]: it holds what the kernel
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
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(* =========================================================================
   Anonymous memory grants

   Granted anonymous memory is ZERO-BACKED, as on Linux: a successful
   mmap and a successful brk grow carry the granted region in
   [eff_zeros], which [Run.apply_effect] materializes as zeros in the
   writable overlay.  (Without this, a load from granted-but-unwritten
   memory would fail — a vacuity trap for any source that reads zeroed
   pages.)

   DISJOINTNESS, AND WHAT IT IS NOT.  Every grant (and its zero-fill)
   is disjoint from the binary image and the stack.  It is NOT disjoint
   from every other live allocation: a brk grow inside one page enters
   [vm_maps] with no address-space test at all (see [brk_grants] and
   [brk_grow_ok] below), so the ledger can hold entries that overlap
   byte for byte, and [Checks/VmMapsDisjoint] carries a checked
   execution reaching exactly that.  What IS invariant is PAGE-GRANULAR:
   no page-aligned address is owned by two entries, which is what every
   consumer of the ledger actually needs.  Linux behaves the same way
   ([SYSCALL_DEFINE1(brk)] exits before consulting any VMA when the
   rounded breaks agree), so this is faithful, not a modelling slip.
   Placement stays non-deterministic (covering ASLR); only occupied
   space is excluded:
   - below this run's [State.alloc_top], hence disjoint from the dynamic
     stack and the argv/envp block of the stack pointer the run was
     started with;
   - [region_free] against [vm_reserved] (the page-rounded LOAD
     segments, fixed at [execve] — the kernel maps whole pages, so a
     grant sharing a partial page with a segment is as impossible as a
     full overlap) and against [vm_maps] (live anonymous mappings AND
     recorded brk grows, so an MMAP can never alias the live heap — the
     converse does not hold, because a same-page brk grow is not gated
     on [vm_maps] at all).
   This is what allocator-frame reasoning needs downstream: every
   mmap/brk effect's [eff_zeros] is disjoint from the stack and the
   image by constant-interval arithmetic, with no dependence on SP.

   PLACEMENT within the free space is nondeterministic (covering ASLR
   and both kernel layouts), with no floor or highest-fit invariant laid
   on top: a fresh grant's [choose] guard asks only for page alignment,
   an address below [alloc_top], and disjointness from [vm_reserved]
   and [vm_maps] through [region_free].  A first grant can therefore
   land as low as 0x80000000, the placement
   [mmap_null_hint_low_grant_admitted] checks.  That is safe for a
   program whose runtime later reserves a low fixed range, because such
   a later MAP_FIXED reservation is the spanning
   replacement ([mmap_fixed_rw_span_next] and
   [mmap_fixed_noaccess_span_next], both built on [maps_subtract])
   rather than a decline, as [asan_shadow_fixed_after_null_grants_admitted]
   checks.

   BUDGET: every accessible grant is additionally metered against the
   run's backed-memory budget ([State.vm_limit], seeded per role by
   [Equivalence.strong_equiv]): a grant may not push [vm_backing_used]
   above it.  PROT_NONE reservations still occupy [vm_maps] and exclude
   overlapping placement.  Ordinary mappings are charged when they become
   readable; MAP_NORESERVE mappings are charged page by page on first access.
   Once the budget is spent only the failure resolutions remain, so a
   program with unbounded allocation runs out of memory at a FORCED
   point — forced by a fixed budget, not by a quantified draw — which is
   what obliges a target to reproduce the source's out-of-memory
   behavior.  The point is not a function of the grant/free
   history alone: overlapping [vm_maps] entries make [State.live_bytes]
   depend on placement as well, and [Equivalence.equiv] compares whole
   trace SETS, so the target must reproduce every point the source can
   reach.

   All bound and rounding arithmetic is in [Z] over unsigned values (a
   page round-up near 2^64 must not wrap into a small number).
   ========================================================================= *)

(** [brk req] models the raw Linux [SYSCALL_DEFINE1(brk)] (riscv64), which
    NEVER returns [-errno]: it returns the NEW break on success, and the
    CURRENT break UNCHANGED on any failure.  Three execution paths,
    clearly separated below by [brk_r_ok] and [brk_model_next]:

    - QUERY / INVALID ([req = 0], or [req < min_brk]): [req < min_brk] hits
      the kernel's [if (brk < min_brk) goto out;] path, which restores and
      returns the current break with ZERO state change.  [brk(0)] is exactly
      this path (0 is always below the heap), and is how musl/glibc query
      the current break ([sbrk(0)]).

    - GROW ([req > break]): the kernel maps the added anonymous, zero-filled
      pages and returns [req] — but only if the region is free (below
      [alloc_top] and disjoint from the image and every live mapping)
      and the page above it is disjoint too — Linux keeps it clear of the
      break ([brk_grow_ok]); otherwise it [goto out]s and returns the
      break unchanged.  Both
      resolutions are admissible (a real grow can be blocked, and musl then
      falls back to mmap).

    - SHRINK ([min_brk <= req < break]): the kernel lowers the logical break
      to [req] and unmaps the page tail
      [[PAGE_ALIGN(req), PAGE_ALIGN(break))] ([do_vmi_align_munmap] on the
      brk VMA).  Those pages really go: the logical ledger drops
      [[req, break)] ([brk_maps_next])
      AND the effect declares them in [eff_unmaps] ([brk_unmaps]), so a
      load through a dangling heap pointer faults instead of reading the
      bytes that were there — as on Linux, where a re-grow of pages actually
      released reads back zeros.  A same-page shrink releases nothing and
      preserves its bytes.  A shrink can also fail (intersecting VMA /
      ENOMEM), returning the break unchanged — so both resolutions are
      admissible.

    ASLR / the initial break.  On riscv64 [start_brk = brk] is ASLR-placed
    at [execve]: [PAGE_ALIGN(end_bss) + PAGE_SIZE + rand], [rand]
    page-aligned in [0, 1 GiB) ([arch_randomize_brk ->
    randomize_page(_, SZ_1G)], gated on [randomize_va_space > 1]);
    qemu-user placed it at exactly the page-rounded image top.  The model
    mirrors the initial SP: the break base is a QUANTIFIED PARAMETER of
    the run ([Run.mi_init_brk], any [Run.valid_brk] value, independent
    per binary), seeded into [vm_brk] by [State.init_model].  So the
    break is ALWAYS ESTABLISHED, from the first instruction on — exactly
    as on Linux — and [brk(0)] simply reports it. *)

(** The lowest legal break — Linux's [min_brk], which is [mm->start_brk]:
    the ASLR-placed heap base itself ([vm_start_brk], set at execve).  A
    request below it — including one in the ASLR gap between the image
    top and the base — is INVALID: the kernel returns the break
    unchanged, with no state change. *)
Definition min_brk (h : VmMaps) : word := vm_start_brk h.

(** Whether a brk resolution actually GREW the break: request [req] was a
    real move (not a query), the break [old] was already established, and
    the resolution [r] is strictly above it.  Every other case
    (query/invalid keeps [r = old]; shrink and grow-failure have
    [r <= old]) is not a grow.  Both grow effects — the grant ledger
    [brk_grants] and the zero-fill [brk_zeros] — are gated on this one
    test so they cannot drift apart.

    The [req <> 0] and [0 < old] conjuncts are redundant given [brk_r_ok]
    (queries resolve to [r = old], and [old >= min_brk > 0] for any real
    image), but keep both effects gated on the path that may grow. *)
Definition brk_is_grow (req r old : word) : bool :=
  negb (w_is0 req) && Z.ltb 0 (bv_unsigned old)
  && Z.ltb (bv_unsigned old) (bv_unsigned r).

(** The byte-granular grant ledger of a brk transition: exactly a GROW
    SUCCESS from break [old] up to [r] owns [old, r); every other case
    owns nothing.  This deliberately differs from [brk_zeros]: Linux
    changes [mm->brk] byte-granularly but only installs page-rounded memory.
    Keeping the logical range here makes [vm_backing_used] charge exactly the
    requested growth.
    [r - old] cannot wrap: [brk_is_grow] ensures [old < r] unsigned. *)
Definition brk_grants (req r old : word) : list (word * word) :=
  if brk_is_grow req r old then [(old, r - old)] else [].

(** Turn a nonempty half-open interval [[lo, hi)] expressed in unbounded
    integer address arithmetic into the effect/ledger range spelling.  Both
    brk directions use this helper so their page rounding cannot drift apart.
    Admissible brk transitions keep the endpoints below [alloc_top], so
    the conversion back to 64-bit words is lossless. *)
Definition brk_page_range (lo hi : Z) : list (word * word) :=
  if Z.ltb lo hi
  then [(Z_to_bv 64 lo, Z_to_bv 64 (hi - lo))]
  else [].

(** The zero-fill VISIBLE to the process after a brk GROW SUCCESS.  Linux
    installs only the newly covered pages, exactly
    [[PAGE_ALIGN(old), PAGE_ALIGN(r))].  A grow within the already mapped
    final page therefore exposes no new bytes and has an empty effect; in
    particular, shrinking and regrowing inside one page preserves its old
    contents.  Arithmetic and page rounding stay in [Z], so a round-up near
    2^64 cannot wrap into a small grant. *)
Definition brk_zeros (req r old : word) : list (word * word) :=
  if brk_is_grow req r old
  then brk_page_range (page_round_up_Z (bv_unsigned old))
                      (page_round_up_Z (bv_unsigned r))
  else [].

(** The pages a brk transition FREES: a SHRINK from break [old] down to
    [r] releases exactly [PAGE_ALIGN(r), PAGE_ALIGN(old))
    ([do_vmi_align_munmap] on the brk VMA, mm/mmap.c:164-181 in v6.12,
    which tears the PTEs down for real — a later re-grow of the same
    addresses hands back FRESH ZEROES, not the old bytes).  That range
    is EMPTY when the two breaks round to the same page: Linux takes the
    [newbrk == oldbrk] early exit (mm/mmap.c:156-161) and a SUB-PAGE
    shrink frees nothing at all.  Every other resolution (query/invalid,
    and grow, which keep [old <= r]) frees nothing either.

    Mirror image of [brk_zeros]: one guarded singleton interval, with
    all arithmetic in [Z] over unsigned values (a page round-up near
    2^64 must not wrap into a small number).  Under the guard the base
    [lo] is below 2^64 and the size is [hi - lo <= 2^64 - lo], so both
    re-enter [word] losslessly; the one corner that would not ([lo = 0]
    with [hi = 2^64]) needs [r = 0], which no [brk_r_ok] resolution
    admits once the break is established. *)
Definition brk_unmaps (r old : word) : list (word * word) :=
  let lo := page_round_up_Z (bv_unsigned r) in
  let hi := page_round_up_Z (bv_unsigned old) in
  if Z.ltb 0 (bv_unsigned old)
  then brk_page_range lo hi else [].

(** The GROW gate: when [r] is strictly above the break, the PHYSICAL pages
    newly installed — [[PAGE_ALIGN(old), PAGE_ALIGN(r))] — must lie below
    [alloc_top], and they and the one page above them must be disjoint
    from the image and every live mapping (ONE FREE PAGE ABOVE THE NEW
    BREAK, below).
    A same-page grow has no physical interval, so those address-space tests
    are vacuous.  The allocation budget is deliberately LOGICAL:
    [r - old] added bytes must fit next to the live byte-granular grants, so
    the deterministic OOM point does not depend on page rounding.  All page
    arithmetic is in [Z] and the ceiling test precedes conversion to words.

    THE GRANT AND THE GATE COVER DIFFERENT RANGES, ON PURPOSE.
    [brk_grants] records the LOGICAL interval [[old, r)] while this gate
    tests the PHYSICAL one [[PAGE_ALIGN(old), PAGE_ALIGN(r))] plus the page
    above it (next paragraph), and tests nothing at all when the physical
    interval is EMPTY, as it is for a grow inside one page.  So a same-page grow enters
    [vm_maps] with no address-space test at all, and the ledger can end
    up holding overlapping — even identically based — entries.  That is
    not a hole to be plugged; it is what Linux does.
    [SYSCALL_DEFINE1(brk)] (mm/mmap.c) computes

      newbrk = PAGE_ALIGN(brk);
      oldbrk = PAGE_ALIGN(mm->brk);
      if (oldbrk == newbrk) {
              mm->brk = brk;
              goto success;
      }

    and every VMA test on both directions — the shrink block's
    [vma_find], [check_brk_limits], the stack-guard-gap [vma_find], and
    [do_brk_flags] — sits BELOW that early exit.  Read at the kernel of
    record, stable v6.18.46 (commit
    1f99e9ab748fc5c32120de9c4eca31abfe54a4d5), where the syscall is
    still in mm/mmap.c: no statement between function entry and
    [goto success] reads the VMA tree, and all four VMA users above are
    below the exit — [do_brk_flags] itself having moved to mm/vma.c
    without taking the syscall or its exit with it.  The exit block
    quoted above is byte-identical from v5.18 through v6.18.46.  The
    surrounding PROLOGUE is not: commit e001ef9652c2 ("mm: simplify
    min_brk handling in brk()", first released in v6.17) hoisted
    [min_brk = mm->start_brk] above the [CONFIG_COMPAT_BRK] ifdef and
    inverted the test inside it, so the prologue text is constant only
    over v6.5-v6.16.  That commit is a no-functional-change refactor of
    a gate that already sat above the exit and was already not an
    address-space test, so it does not reach this argument; neither does
    the v6.12 change of the shrink call to [do_vmi_align_munmap], which
    is below the exit.  Window figures sample mainline tags; the
    v6.18.46 statement is read from that commit itself.  A within-page move of
    the break therefore reaches [mm->brk = brk] with NO ADDRESS-SPACE
    TEST APPLIED, even over bytes another mapping owns; a process
    reaches such a state by unmapping the brk VMA and mapping over it.
    It is not unconditional: the killable [mmap_write_lock], the
    [brk < min_brk] floor and [check_data_rlimit] sit above the exit and
    can each refuse it, returning [origbrk].  None is an address-space
    test, so none touches the argument here; and [brk_r_ok] admits
    [r = vm_brk h] on every grow, so those refusals are already
    admissible outcomes of the model.  Adding
    [region_free (vm_reserved h ++ vm_maps h) (vm_brk h) (r - vm_brk h)]
    here would decline exactly that call,
    and declining it is not fail-closed.  [brk_r_ok] evaluates this gate
    at the resolution it is being shown, and the tightening reaches only
    the SUCCESS resolution [r = req]: at the failure resolution
    [r = vm_brk h] the outer guard degenerates to
    [vm_brk h < vm_brk h], so the gate answers [true] without entering
    the branch at all.  The tightened checker would therefore still
    admit the no-op answer while rejecting [r = req] — which is the
    break Linux hands back for this call, its [oldbrk == newbrk] early
    exit returning the request.

    ONE FREE PAGE ABOVE THE NEW BREAK.  The range [region_free] tests runs
    to [PAGE_ALIGN(r) + PAGE_SIZE], one page past the pages the grow
    installs, because the kernel refuses a grow that would leave the new
    break flush against the next mapping.  [SYSCALL_DEFINE1(brk)]
    (mm/mmap.c, commit 1f99e9ab748fc5c32120de9c4eca31abfe54a4d5), after
    [check_brk_limits] and before [do_brk_flags]:

      vma_iter_init(&vmi, mm, oldbrk);
      next = vma_find(&vmi, newbrk + PAGE_SIZE + stack_guard_gap);
      if (next && newbrk + PAGE_SIZE > vm_start_gap(next))
              goto out;

    [vma_find(&vmi, max)] is [mas_find(&vmi->mas, max - 1)]
    (include/linux/mm.h), the first VMA meeting [[oldbrk, max)], and
    [vm_start_gap] (same file) is [vm_start] itself for a VMA that is
    neither VM_GROWSDOWN nor VM_SHADOW_STACK.  So for an ordinary mapping
    the test refuses exactly when the mapping meets
    [[oldbrk, newbrk + PAGE_SIZE)]: the pages being installed, and one
    more.  [check_brk_limits], ahead of it, tests nothing against other
    mappings: its [get_unmapped_area(NULL, oldbrk, len, 0, MAP_FIXED)]
    hands [oldbrk] straight back unless [newbrk > TASK_SIZE] or
    [security_mmap_addr(oldbrk)] objects ([__get_unmapped_area], same
    file), and [mlock_future_ok] adds an [-EAGAIN] only with [VM_LOCKED]
    in [def_flags] ([mlockall(MCL_FUTURE)], unmodeled); each of those
    refusals returns [origbrk] like the one below.  The refusal here
    returns [origbrk] — the [r = vm_brk h] resolution
    [brk_r_ok] admits on every grow — so a mapping that starts at
    [PAGE_ALIGN(r)] leaves the failure resolution and makes the success
    one inadmissible.  The [oldbrk == newbrk] exit quoted above sits
    before this test, which is why a grow that installs no page is not
    subject to it.  [Checks/Cases/Mm/Mmap.v] pins the boundary from both
    sides: [brk_grow_flush_against_neighbour_rejected] and
    [brk_grow_one_page_below_neighbour_grants].

    For a VM_GROWSDOWN VMA — the stack — [vm_start_gap] subtracts
    [stack_guard_gap] (256 pages unless the command line says otherwise,
    mm/mmap.c), so Linux also refuses a grow to within a page and that gap
    of the stack's current start.  The model has no stack VMA to test
    against: [alloc_top] keeps every grow at least [stack_max_size] below
    the run's [sp], which stands in for that refusal only while the stack
    has not grown to within [stack_guard_gap + PAGE_SIZE] of that bound.
    That is a premise of the model.

    What holds instead is PAGE-granular: no page-aligned address is ever
    owned by two [vm_maps] entries, because a page-aligned byte of
    [[old, r)] is necessarily inside [[PAGE_ALIGN(old), PAGE_ALIGN(r))],
    a range this gate does test.  Since every base a syscall can name
    is page aligned, that is what makes a base determine its entry.  See
    [Checks/VmMapsDisjoint] for the statement, the preservation proof
    over the whole dispatcher, and a checked execution reaching the
    byte-level overlap. *)
(** The budget conjunct of a brk grow, named so that [brk_grow_ok]
    and the budget mark [brk_budget_refused_b] below read ONE
    definition rather than two spellings of it: the grow's byte delta
    [r - vm_brk] must fit the backing still unspent.  Byte-granular,
    like the ledger entry a grow records. *)
Definition brk_budget_ok (m : Model) (r : word) : bool :=
  let h := m_vmmaps m in
  Z.leb (vm_backing_used m + bv_unsigned (r - vm_brk h)) (vm_limit h).

Definition brk_grow_ok (m : Model) (req r : word) : bool :=
  let h := m_vmmaps m in
  if Z.ltb 0 (bv_unsigned (vm_brk h))
     && Z.ltb (bv_unsigned (vm_brk h)) (bv_unsigned r)
  then let lo := page_round_up_Z (bv_unsigned (vm_brk h)) in
       let hi := page_round_up_Z (bv_unsigned r) in
       (if Z.ltb lo hi
        then Z.leb hi (alloc_top h)
             && region_free (vm_reserved h ++ vm_maps h)
                            (Z_to_bv 64 lo) (Z_to_bv 64 (hi + page_size - lo))
        else true)
       && brk_budget_ok m r
  else true.

(** May the kernel report resolved break [r] for [brk req] under ledger [h]?
    The three Linux paths, keyed on the request against [min_brk] and the
    tracked break [b = vm_brk h]: *)
Definition brk_r_ok (m : Model) (req r : word) : bool :=
  let h := m_vmmaps m in
  let b := vm_brk h in
  if w_is0 req || Z.ltb (bv_unsigned req) (bv_unsigned (min_brk h)) then
    bv_eqb r b                                (* QUERY / INVALID: unchanged *)
  else if Z.ltb (bv_unsigned req) (bv_unsigned b) then
    bv_eqb r req || bv_eqb r b                 (* SHRINK: to [req], or fail *)
  else
    (bv_eqb r req || bv_eqb r b) && brk_grow_ok m req r.  (* GROW: to [req], or fail *)

(** The [vm_maps] ledger after resolving to break [r].  A GROW SUCCESS
    records the granted interval, so a later mmap can never alias the
    live heap; the CONVERSE fails, because a grow inside one page is
    gated on neither [vm_maps] nor anything else in the address space,
    and so can land inside a live mapping.  A SHRINK drops the logical
    tail [r, b) via
    [maps_subtract] (dropping heap grants inside it while sparing higher
    anonymous mmaps); every other resolution leaves [vm_maps] untouched
    ([brk_grants] is [] and no interval is freed).  This ledger stays
    byte-granular on purpose even though [brk_zeros]/[brk_unmaps] describe
    the page-rounded memory effects. *)
Definition brk_maps_next (h : VmMaps) (req r : word) : list (word * word) :=
  if Z.ltb 0 (bv_unsigned (vm_brk h))
     && Z.ltb (bv_unsigned r) (bv_unsigned (vm_brk h))
  then (* SHRINK: free [r, b) *)
       maps_subtract (vm_maps h) (bv_unsigned r) (bv_unsigned (vm_brk h))
  else (* GROW success records; else no-op *)
       brk_grants req r (vm_brk h) ++ vm_maps h.

(** Apply exactly the page ranges named by a brk unmap effect to a mapping
    overlay.  [brk_unmaps] is empty or a singleton today; spelling this as a
    fold keeps [vm_noaccess] subtraction tied to the effect if that changes.
    Each range is stored as a (base, length) pair, so the end is recovered
    in [Z] — the same shape the munmap and mprotect gates use.  A [word]
    sum here could wrap at 2^64 and hand [maps_subtract] a range ending at
    0, which subtracts nothing instead of the tail the effect announced. *)
Definition maps_subtract_ranges (maps ranges : list (word * word))
    : list (word * word) :=
  fold_left (fun acc p =>
               maps_subtract acc (bv_unsigned (fst p))
                             (bv_unsigned (fst p) + bv_unsigned (snd p)))
            ranges maps.

Definition brk_model_next (h : VmMaps) (req r : word) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (brk_maps_next h req r)
               (maps_subtract_ranges (vm_noaccess h)
                                     (brk_unmaps r (vm_brk h)))
               (vm_start_brk h) r (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

(* =========================================================================
   THE PROTECTED LEDGER NAMES REAL BYTES

   [State.entries_nonzero] says why a ledger list would want to promise
   this and proves it closed under the three ways one is built; what is
   left is to apply it at each writer of [vm_noaccess], and that is what
   this section and its twin in [Mm/Mprotect.v] do.  Read together with
   [State.vm_noaccess_entries_nonzero], [State.init_model_noaccess_nonzero]
   (the empty base case) and
   [Madvise.madvise_noaccess_decline_names_a_protected_byte] (the
   consumer).

   THE WRITERS, BY NAME.  They are what a grep for [vm_noaccess] in this
   file and in [Mm/Mprotect.v] finds on the left of a [mkVmMapsFull],
   and each has a lemma below or beside its definition.

     GROWS THE LIST — the only shape that can add an entry, so the only
     one whose lemma needs a length to be nonzero:

       [mmap_fixed_noaccess_span_next]  — named; cons over a
                                          [maps_subtract]
       the chosen-address PROT_NONE anonymous grant, the free-range
       sub-case of PROT_NONE MAP_FIXED, and PROT_NONE
       MAP_FIXED_NOREPLACE — inline, and all of them writing the SAME
                                          record; cons
       the PROT_NONE MAP_FIXED CONTAINED arm — inline; cons over a
                                          [maps_subtract]

     SHRINKS THE LIST — nothing is added, so the lemma is unconditional
     and [State.maps_subtract_nonzero] is the whole of it:

       [brk_model_next]                 — named; [maps_subtract_ranges]
       [mmap_fixed_rw_next]             — named; [maps_subtract]
       [mmap_fixed_destroyed_next]      — named; [maps_subtract]
       [mmap_fixed_rw_span_next]        — named; [maps_subtract]
       [Mprotect.mprotect_model_next]   — named; [maps_subtract]
       [munmap_spec]'s whole-mapping removal — inline; [maps_subtract]

     LEAVES THE LIST ALONE — [vm_noaccess h] carried over verbatim, so
     there is nothing to state: [Mremap.mremap_maps_next], and the rw
     anonymous grant, the rw MAP_FIXED free-range sub-case and the rw
     MAP_FIXED_NOREPLACE arm of this file.

   [theories/Common/MmapSim.v]'s [munmap_model] and [mmap_model] build
   [VmMaps] values too, for the proof library rather than for a spec
   arm.  They are a [maps_subtract] and a carry-over, so neither can add
   an entry; they are named here so the lists above are not read as the
   whole tree.

   THE COMPOSITION is in [Checks/NoaccessOwned.v]: "every reachable
   model satisfies [State.vm_noaccess_entries_nonzero]" follows from
   [init_model_sys_inv], [star_preserves_sys_inv] and
   [sys_inv_noaccess_pages_owned] with
   [State.noaccess_pages_owned_nonzero].
   ========================================================================= *)

(** [maps_subtract_ranges] is a fold of [State.maps_subtract], so it
    inherits the closure. *)
Lemma maps_subtract_ranges_nonzero : forall ranges maps,
  entries_nonzero maps ->
  entries_nonzero (maps_subtract_ranges maps ranges).
Proof.
  unfold maps_subtract_ranges.
  induction ranges as [|[a n] rest IH]; intros maps H; cbn [fold_left];
    [exact H |].
  apply IH. cbn [fst snd]. now apply maps_subtract_nonzero.
Qed.

(** The length every [cons] writer records: the request's page-rounded
    size, positive because the arm has already refused a zero length and
    bounded the rounded end below 2^64 (so the [Z_to_bv] round trip is
    lossless and cannot wrap a whole page to nothing). *)
Lemma mmap_request_len_nonzero : forall len : word,
  w_is0 len = false ->
  (page_round_up_Z (bv_unsigned len) < two_pow_64)%Z ->
  (0 < bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))%Z.
Proof.
  intros len H0 Hfit.
  pose proof (w_is0_false_pos len H0) as Hpos.
  pose proof (page_round_up_Z_pos (bv_unsigned len) Hpos) as Hpage.
  rewrite bv_unsigned_Z_to_bv_u64 by (unfold page_size in Hpage; lia).
  unfold page_size in Hpage. lia.
Qed.

(* ---- the writers that have no name -------------------------------------

   THREE post-states are written out inside [mmap_spec] and
   [munmap_spec] rather than defined, and a lemma cannot be ABOUT an
   expression with no name.  So each of the three below RESTATES the
   record its arms write, and takes as hypotheses the GATES those arms
   have already passed — which is what makes them the arm's own facts
   rather than facts about an arbitrary record: an arm past [w_is0 len]
   with its rounded end under 2^64, binding [n] to that rounded length,
   has every hypothesis to hand.

   WHAT THE RESTATEMENT COSTS, plainly: it is a second copy.  Re-shape
   an arm's post-state and the lemma below goes on being true of the
   shape that is gone, with nothing failing; add a PROT_NONE arm with a
   fourth shape and it is covered by none of them.  The durable fix is
   to give those arms named post-state functions the way
   [mmap_fixed_rw_next] and its siblings have, so each lemma is about
   the definition the arm uses.
   ------------------------------------------------------------------- *)

(** The record the three PROT_NONE grant arms write — the chosen-address
    anonymous grant, the free-range sub-case of MAP_FIXED, and
    MAP_FIXED_NOREPLACE.  The request is newly owned AND newly
    protected, so this is a [cons] onto both lists and the request must
    name a byte. *)
Lemma mmap_noaccess_grant_inline_nonzero : forall (h : VmMaps) (a len n : word),
  w_is0 len = false ->
  (page_round_up_Z (bv_unsigned len) < two_pow_64)%Z ->
  n = Z_to_bv 64 (page_round_up_Z (bv_unsigned len)) ->
  vm_noaccess_entries_nonzero h ->
  vm_noaccess_entries_nonzero
    (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
       ((a, n) :: vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h)
       (vm_mmap_base h) (vm_init_sp h)).
Proof.
  intros h a len n H0 Hfit -> H.
  unfold vm_noaccess_entries_nonzero. cbn [vm_noaccess].
  apply entries_nonzero_cons; [now apply mmap_request_len_nonzero | exact H].
Qed.

(** The record the PROT_NONE MAP_FIXED CONTAINED arm writes: the range
    is already owned, so [vm_maps] does not move; the protected list is
    re-cut around the request and the request added whole, so the cut
    cannot leave a vacuous remnant and the addition names a byte. *)
Lemma mmap_fixed_noaccess_inline_nonzero :
  forall (h : VmMaps) (addr len n : word),
  w_is0 len = false ->
  (page_round_up_Z (bv_unsigned len) < two_pow_64)%Z ->
  n = Z_to_bv 64 (page_round_up_Z (bv_unsigned len)) ->
  vm_noaccess_entries_nonzero h ->
  vm_noaccess_entries_nonzero
    (mkVmMapsFull (vm_reserved h) (vm_maps h)
       ((addr, n) :: maps_subtract (vm_noaccess h)
                       (bv_unsigned addr)
                       (bv_unsigned addr + bv_unsigned n))
       (vm_start_brk h) (vm_brk h) (vm_limit h)
       (vm_mmap_base h) (vm_init_sp h)).
Proof.
  intros h addr len n H0 Hfit -> H.
  unfold vm_noaccess_entries_nonzero. cbn [vm_noaccess].
  apply entries_nonzero_cons;
    [now apply mmap_request_len_nonzero | now apply maps_subtract_nonzero].
Qed.

(** The record [munmap_spec]'s whole-mapping removal writes.  Nothing is
    added to the protected list — the removal cuts it by the request's
    range, [maps_subtract] rather than [map_remove] because a protected
    entry need not coincide with the mapping — so no length fact is
    needed and no gate is a hypothesis. *)
Lemma munmap_inline_nonzero : forall (h : VmMaps) (addr n : word),
  vm_noaccess_entries_nonzero h ->
  vm_noaccess_entries_nonzero
    (mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) addr)
       (maps_subtract (vm_noaccess h)
          (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
       (vm_start_brk h) (vm_brk h) (vm_limit h)
       (vm_mmap_base h) (vm_init_sp h)).
Proof.
  intros h addr n H. unfold vm_noaccess_entries_nonzero.
  cbn [vm_noaccess]. now apply maps_subtract_nonzero.
Qed.

(** A [brk] shrink cuts the page-rounded unmapped range out of the
    protected list and adds nothing. *)
Lemma brk_model_next_noaccess_nonzero : forall h req r,
  vm_noaccess_entries_nonzero h ->
  vm_noaccess_entries_nonzero (brk_model_next h req r).
Proof.
  intros h req r H. unfold vm_noaccess_entries_nonzero, brk_model_next.
  cbn [vm_noaccess]. now apply maps_subtract_ranges_nonzero.
Qed.

Fixpoint forget_vm_ranges (ranges : list (word * word)) (m : Model) : Model :=
  match ranges with
  | [] => m
  | (a, n) :: rest =>
      forget_vm_ranges rest
        (vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) m)
  end.

Definition with_brk_next (m : Model) (req r : word) : Model :=
  let h := m_vmmaps m in
  forget_vm_ranges (brk_unmaps r (vm_brk h))
    (with_vmmaps (brk_model_next h req r) m).

Definition brk_spec (req : word) : Sys SyscallEffect :=
  m <- get_model ;;
  let h := m_vmmaps m in
  r <- choose (fun r => brk_r_ok m req r = true) ;;
  modify (fun _ => with_brk_next m req r) ;;
  pure (mkEffectU r [] (brk_zeros req r (vm_brk h))
                    (brk_unmaps r (vm_brk h)) [] []).

(* =========================================================================
   THE BUDGET MARK for brk: is this request refused for exceeding
   [vm_limit]?
   =========================================================================

   [Run.budget_refused_at] asks, at every configuration a run reaches,
   whether the pending request is one the BUDGET declines — as opposed
   to one the environment may decline anyway (every arm here keeps an
   [alt] onto its errno list, so a refusal is always admissible) or one
   an argument gate declines (an errno the state determines).  The
   premise of the budget-parameterised statements
   ([Equivalence.strong_universal_T_budgets] and its siblings) is that
   the SOURCE run never reaches such a configuration.

   The mark is a function of the PRE-state and the request, never of
   the answer chosen: it is the negation of the arm's own budget gate
   after the arm's own shape gates, so it fires exactly where the
   success resolution's budget conjunct is false and nothing but a
   refusal remains.  It is deliberately NOT a state flag the spec sets
   — the arms have no distinct "forced" branch to set it in, and the
   lazy first-touch refusal ([Run.sstep_instr_fault]) has no successor
   state at all — and NOT an event, which would enter trace equality
   and change what every existing statement means.

   For brk: a real request ([req <> 0], at or above [min_brk]) that
   GROWS the break from an established one, whose byte delta does not
   fit.  Everything else — the query, the invalid address, a shrink, a
   grow from an unestablished break (which [brk_grow_ok] does not gate),
   a grow that fits — is not a budget refusal, whatever the answer.
   [brk_r_ok] then admits only [r = vm_brk]: the mark's soundness is
   pinned in [Checks/BudgetPremise.v]. *)
Definition brk_budget_refused_b (m : Model) (req : word) : bool :=
  let h := m_vmmaps m in
  negb (w_is0 req || Z.ltb (bv_unsigned req) (bv_unsigned (min_brk h)))
  && Z.ltb 0 (bv_unsigned (vm_brk h))
  && Z.ltb (bv_unsigned (vm_brk h)) (bv_unsigned req)
  && negb (brk_budget_ok m req).

(** Anonymous mmap fails only for lack of memory / address space. *)
Definition mmap_errnos : list Z := [ENOMEM].

(** MAP_NORESERVE lives in the arch-generic half riscv64 inherits
    (include/uapi/asm-generic/mman.h:11, Linux v6.12).  It changes only
    Linux's commit accounting; it does not affect placement, contents,
    permissions, or a successful return value.

    It changes that accounting CONDITIONALLY, which matters for what the
    model is entitled to claim.  [do_mmap] (mm/mmap.c, Linux v6.12)
    translates the bit to VM_NORESERVE only outside strict overcommit:

      if (flags & MAP_NORESERVE) {
              /- We honor MAP_NORESERVE if allowed to overcommit -/
              if (sysctl_overcommit_memory != OVERCOMMIT_NEVER)
                      vm_flags |= VM_NORESERVE;

    Under [vm.overcommit_memory = 2] Linux ignores the bit,
    [accountable_mapping] is true again, and a private read-write mapping
    past the commit limit is -ENOMEM.  The model always honors it, so it
    describes overcommit modes 0 and 1.  That is part of the same
    environment obligation the backed-memory ceiling already carries,
    not a claim about mode 2.

    The model records the mapping as lazy: it occupies virtual space
    immediately, but each page consumes [vm_limit] only on its first
    successful instruction or syscall access.  That per-page charging is a
    MODEL abstraction rather than a Linux mechanism: Linux commits a
    VM_NORESERVE range at no point, and runs no per-fault
    [__vm_enough_memory].  It bounds a budget the model enforces and Linux
    does not.  Ordinary read-write mappings remain eagerly backed. *)
Definition MAP_NORESERVE : Z := 16384%Z.          (* 0x4000 *)

(** Remove only MAP_NORESERVE before matching an anonymous mmap shape;
    every other flag bit must still match exactly.

    Masking the bit out of the SHAPE match is the conservative direction
    because it can only widen what the model must account for, never what
    it lets through: the two spellings match the same shape, and the bit
    is then read back by [mmap_noreserve_b] at the one place it changes an
    answer, the backing charge.  A masked-out bit that instead selected a
    laxer gate would be the unsafe direction; this one selects the lazy
    LEDGER while leaving every errno, placement and effect gate identical. *)
Definition mmap_flags_core (flags : word) : Z :=
  Z.ldiff (bv_unsigned flags) MAP_NORESERVE.

Definition mmap_noreserve_b (flags : word) : bool :=
  negb (Z.eqb (Z.land (bv_unsigned flags) MAP_NORESERVE) 0).

Definition with_mmap_backing (flags a n : word) (m : Model) : Model :=
  if mmap_noreserve_b flags then vm_add_lazy a n m else m.

Definition with_mmap_replacement (flags a n : word) (m : Model) : Model :=
  with_mmap_backing flags a n
    (vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) m).

(** A fixed mapping's destructive failure and [munmap] share the same
    lifecycle transition: the ownership/no-access ledgers change and every
    lazy or materialized entry in the removed range is forgotten. *)
Definition with_mmap_destroyed (a n : word) (h' : VmMaps)
    (m : Model) : Model :=
   vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)
     (with_vmmaps h' m).

Lemma mmap_flags_core_id : forall flags : word,
  Z.land (bv_unsigned flags) MAP_NORESERVE = 0%Z ->
  mmap_flags_core flags = bv_unsigned flags.
Proof.
  intros flags H. unfold mmap_flags_core.
  apply Z.bits_inj'. intros k Hk. rewrite Z.ldiff_spec.
  destruct (Z.testbit MAP_NORESERVE k) eqn:Hn;
    [|now rewrite Bool.andb_true_r].
  destruct (Z.testbit (bv_unsigned flags) k) eqn:Hb; [|reflexivity].
  exfalso.
  assert (Z.testbit (Z.land (bv_unsigned flags) MAP_NORESERVE) k = true)
    as Hc by (rewrite Z.land_spec, Hb, Hn; reflexivity).
  rewrite H, Z.bits_0 in Hc. discriminate.
Qed.

(** -1 in two's complement: the [fd] a caller conventionally passes
    with MAP_ANONYMOUS.

    The anonymous shapes below do not require it, because Linux does
    not look at [fd] there.  [ksys_mmap_pgoff] resolves a file only inside
    [if (!(flags & MAP_ANONYMOUS))], and returns -EBADF from inside that
    branch when [fget] finds nothing; the MAP_ANONYMOUS arm beside it
    never mentions [fd] and does not pass it on to [vm_mmap_pgoff]
    (mm/mmap.c, [ksys_mmap_pgoff], Linux v6.18.46).  So
    [mmap(NULL, 4096, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS,
    3, 0)] succeeds on Linux for ANY [fd] — valid, closed, or garbage —
    and each shape predicate below takes [prot], [flags] and [off]
    only.  Ignoring [fd] admits no new
    answer: the arms it opens are the ones the model produces
    for the same call spelled with -1, and the placement, effect and
    errno gates are the same.

    The constant is here because the worked examples in
    [Checks/Cases/Mm/Mmap.v] name it, and because it is what a reader
    expects to see beside
    [mmap_anon_b], which is where the [fd] question actually lives. *)
Definition mmap_fd_none  : word := Z_to_bv 64 (-1).

(** Is MAP_ANONYMOUS set?  This is the ONE bit that decides whether
    Linux resolves [fd] at all, so it is the gate on the file-backed
    branch of [mmap_spec] below.  [ksys_mmap_pgoff] (mm/mmap.c, Linux
    v6.18.46) opens with

      if (!(flags & MAP_ANONYMOUS)) {
              audit_mmap_fd(fd, flags);
              file = fget(fd);
              if (!file)
                      return -EBADF;

    and nothing in the syscall runs before that except riscv's offset
    check ([mmap_off_aligned_b]).  MAP_HUGETLB is irrelevant to the
    test: with MAP_ANONYMOUS clear the [fget] happens first whatever
    else the flags word carries. *)
Definition mmap_anon_b (flags : word) : bool :=
  negb (Z.eqb (Z.land (bv_unsigned flags) MAP_ANONYMOUS) 0).

(** Is [off] page-aligned?  riscv answers -EINVAL when it is not, and
    answers it BEFORE any generic mm code runs — before the flags are
    read, before [fget], before [do_mmap]'s zero-length check:

      static long riscv_sys_mmap(..., off_t offset,
                                 unsigned long page_shift_offset)
      {
              if (unlikely(offset & (~PAGE_MASK >> page_shift_offset)))
                      return -EINVAL;

    (arch/riscv/kernel/sys_riscv.c, [riscv_sys_mmap], Linux v6.18.46).
    __NR_mmap (222) enters it with [page_shift_offset] zero -- the
    [SYSCALL_DEFINE6] for mmap immediately below passes 0 -- so the mask
    is exactly [PAGE_SIZE - 1] and the test is this one.  Deterministic
    and argument-only: no model state is consulted, which is why
    [mmap_spec] can answer it first. *)
Definition mmap_off_aligned_b (off : word) : bool :=
  Z.eqb (bv_unsigned off mod page_size) 0.

(** Does [PAGE_ALIGN(len)] stay inside an [unsigned long]?  The kernel
    rounds the length in machine arithmetic, so a [len] within a page of
    2^64 rounds to ZERO there, and [do_mmap] answers -ENOMEM for it
    (mm/mmap.c, [do_mmap]: [len = PAGE_ALIGN(len); if (!len) return
    -ENOMEM;]).  This model computes the rounding in [Z], where nothing
    wraps, so the condition has to be spelled out; the MAP_FIXED arms
    below already test the same quantity through
    [two_pow_64 <=? addr + nZ].

    It guards the -EINVAL above, and the reason is not about Linux.  On
    Linux v6.18.46 the -EINVAL is certain for every [len]: riscv's
    offset test runs before [do_mmap] reads the length at all.  QEMU's
    user-mode emulation reaches the same call the other way round --
    [target_mmap] (linux-user/mmap.c) validates the request itself
    before it performs any mapping, and its length check comes first,
    [len = TARGET_PAGE_ALIGN(len); if (len == 0 || len >
    (abi_ulong)-start)] answering -ENOMEM.  Measured on qemu-riscv64:
    [mmap(0, (size_t)-1, PROT_READ, MAP_PRIVATE, 999, 1)] answers
    -ENOMEM there against -EINVAL on Linux.  Every other
    misaligned-offset shape measured on the same binary -- zero length,
    huge non-wrapping lengths, an invalid MAP_TYPE, an unknown prot bit,
    MAP_FIXED at an unaligned address, MAP_HUGETLB, an address hint --
    answers -EINVAL on both.

    WHOSE RULE THIS FOLLOWS, since the answer differs by implementation
    and this file should not pretend otherwise.  README.md's design-priorities
    section counts QEMU's user-mode emulation of the syscall interface
    among the supported implementations, so priority 1 forbids proving
    -EINVAL as certain here: doing so would prove a behaviour outside
    the intersection of what the supported implementations produce,
    since qemu-riscv64 answers -ENOMEM for the case measured above.
    The decline costs coverage, never soundness -- it is what this
    guard takes. *)
Definition mmap_pglen_ok_b (len : word) : bool :=
  (page_round_up_Z (bv_unsigned len) <? two_pow_64)%Z.

(** The offset the model's anonymous shapes pin: 0.  This is a
    narrowing: a MISALIGNED offset is
    answered ([mmap_off_aligned_b] and the -EINVAL branch that opens
    [mmap_spec]), and what is pinned here is the page-ALIGNED nonzero
    offset.

    Linux requires only page ALIGNMENT of [off], and requires it first:
    [riscv_sys_mmap] rejects [offset & (~PAGE_MASK >> page_shift_offset)]
    with -EINVAL before any generic code runs
    (arch/riscv/kernel/sys_riscv.c, [riscv_sys_mmap], Linux v6.18.46),
    and __NR_mmap (222) enters it with [page_shift_offset] zero (the
    [SYSCALL_DEFINE6] for mmap in the same file), so the mask is just
    [PAGE_SIZE - 1].  A page-aligned offset is then IGNORED for an
    anonymous mapping: [__get_unmapped_area] zeroes the page offset it
    places with ([if (!file) pgoff = 0], mm/mmap.c:897-899) and
    [do_mmap] resets the one the VMA records to [addr >> PAGE_SHIFT]
    (mm/mmap.c:471-476).  A page-aligned nonzero [off] is therefore an
    ordinary success on Linux, and [unmodeled] here.

    One consequence of that path is genuinely surprising and worth
    naming.  [riscv_sys_mmap] declares [offset] as [off_t], i.e.
    SIGNED (arch/riscv/kernel/sys_riscv.c:13; [off_t] ->
    [__kernel_off_t] -> [__kernel_long_t], include/linux/types.h:26 and
    include/uapi/asm-generic/posix_types.h:87), while both the syscall
    prototype above it (arch/riscv/kernel/sys_riscv.c:24-26) and
    [ksys_mmap_pgoff] below it (mm/mmap.c:506) say [unsigned long].  The
    [offset >> (PAGE_SHIFT - page_shift_offset)] at
    arch/riscv/kernel/sys_riscv.c:19-20 is thus an ARITHMETIC shift: a
    page-aligned [off] at or above 2^63 becomes a page offset with its
    top 12 bits set rather than [off / 4096].  That is large enough for
    [do_mmap]'s [(pgoff + (len >> PAGE_SHIFT)) < pgoff] to wrap and
    return -EOVERFLOW (mm/mmap.c:319-321) once [len] is large enough —
    even under MAP_ANONYMOUS, because that check runs before the
    [pgoff = 0] of mm/mmap.c:897-899. *)

(** Is this the PLAIN anonymous shape — MAP_ANONYMOUS set, MAP_HUGETLB
    clear?  This is the gate on the zero-length -EINVAL below, because
    it is the only flag combination that reaches it.

    [ksys_mmap_pgoff] (mm/mmap.c:566-609, Linux v6.18.46) inspects the
    flags before the length is ever examined, and only its fall-through
    reaches [do_mmap]'s [if (!len) return -EINVAL] (mm/mmap.c:347-348):

    - MAP_ANONYMOUS clear: [file = fget(fd)] and -EBADF on failure
      (mm/mmap.c:575-577).  So [mmap(NULL, 0, PROT_READ, MAP_PRIVATE,
      999, 0)] with 999 closed is -EBADF on Linux, not -EINVAL.
    - MAP_ANONYMOUS and MAP_HUGETLB both set: [hstate_sizelog] (-EINVAL
      when the requested huge-page size has no hstate) and
      [hugetlb_file_setup], whose error is returned as-is
      (mm/mmap.c:584-602).

    Both are unmodeled here — the model maps no files and has no huge
    pages — so a zero-length mmap outside the plain anonymous shape
    fails closed instead of guessing -EINVAL.  The first of the two is
    declined EARLIER, by [mmap_spec]'s file-backed branch, which
    takes every MAP_ANONYMOUS-clear call whatever its length; so by the
    time this test is reached MAP_ANONYMOUS is already known to be set,
    and the only thing this predicate separates out is the
    huge-page arm.  The conjunct on MAP_ANONYMOUS is kept anyway,
    because it is what makes the predicate say on its own which flag
    class it names.

    INSIDE the plain anonymous shape the -EINVAL holds for every other
    argument, which is why the branch below tests nothing else.  Nothing
    between [ksys_mmap_pgoff]'s fall-through and mm/mmap.c:294 looks at
    [addr], [prot] or [off]: [do_mmap] validates MAP_TYPE only at
    mm/mmap.c:477-478, well after the length.  And the one argument
    check that DOES precede all of this — riscv's
    [offset & (~PAGE_MASK >> page_shift_offset)]
    (arch/riscv/kernel/sys_riscv.c:16-17) — answers -EINVAL as well, so
    a misaligned [off] agrees with this branch rather than escaping it. *)
Definition mmap_plain_anon_b (flags : word) : bool :=
  negb (Z.eqb (Z.land (bv_unsigned flags) MAP_ANONYMOUS) 0)
  && Z.eqb (Z.land (bv_unsigned flags) MAP_HUGETLB) 0.

(* =========================================================================
   PLACEMENT — what the two fresh-grant arms may choose, and why the
   spec says no more than it does

   When the caller expresses no preference the kernel picks the address,
   and the model lets it: the placement flows through the
   nondeterminism monad, exactly as the initial stack pointer and the
   program break already do ([Run.valid_sp], [Run.valid_brk],
   [Equivalence.strong_universal_T]).  The [choose] guards below say
   three things about the address and nothing else:

   - it is PAGE-ALIGNED;
   - it is inside the user address space this model describes — nonzero,
     and ending at or below this run's [State.alloc_top];
   - it is DISJOINT from every mapping the ledger records, [vm_reserved]
     and [vm_maps] both.  [get_unmapped_area] never silently overlaps a
     live VMA for a preference-free request: both generic searches ask
     [vm_unmapped_area] for a gap (mm/mmap.c:712-718 and :763-770, Linux
     v6.18.46), and a gap is by construction free of every VMA in the
     interval it was searched (mm/vma.c:2885-2930, :2942-2982).

   WHY NOT MORE.  A fourth conjunct could also pin the
   SEARCH: a placement would have to sit at or above a bottom-up floor derived
   from riscv64's [TASK_UNMAPPED_BASE], or else leave no fitting free
   gap between its end and the run's [mm->mmap_base].  Three things are
   wrong with that, in increasing order of importance.

   It would EXCLUDE PLACEMENTS LINUX MAKES.  The highest-fit half would
   be read on
   the model's ledger, and the kernel's search walks VMAs the ledger
   does not carry — the vdso/vvar pair [execve] installs, among others.
   A real top-down descent below the floor is justified by "everything
   above me is occupied", occupied in part by mappings the model never
   recorded, so the model would call a real placement inadmissible.  That is
   the direction that costs the THEOREM rather than coverage: a
   statement proved against it would not cover the run the kernel
   performs.  The ledger's missing kernel VMAs have other costs, which
   are a known limitation of the model.

   It would ENCODE A LAYOUT.  The floor is a constant, and no constant of
   that kind belongs in a model of the kernel: riscv64's own is one,
   but the same slot invites one chosen to clear whatever
   the runtime in front of us happens to reserve, which would be a fact
   about a corpus wearing a kernel citation.  Nor could the floor be
   RAISED to steer placements clear of a runtime's absolute
   reservations: on riscv64 [TASK_UNMAPPED_BASE] is
   [PAGE_ALIGN((UL(1) << MMAP_MIN_VA_BITS) / 3)] with [MMAP_MIN_VA_BITS]
   fixed at [VA_BITS_SV39] whatever paging mode the guest boots
   (arch/riscv/include/asm/processor.h:52, pgtable.h:138-140, Linux
   v6.18.46), so every riscv64 kernel allocates bottom-up from
   0x2aaaaab000 and a higher floor would call a real placement
   inadmissible.  A collision with such a reservation is answered by
   the spanning MAP_FIXED arm below, unless the reservation reaches the
   image, which is the one MAP_FIXED shape that still declines.

   And it would describe a KERNEL THAT DOES NOT DEPLOY.  Placement is
   randomized per exec ([arch_mmap_rnd], mm/util.c:399-411), so no
   deterministic rule is the rule; what is true of every run is the
   admissibility above.  Quantifying over the whole admissible set is
   also what makes the certified property the right one — that
   observable behaviour is INSENSITIVE to placement, which is what an
   equivalence statement about a sanitizer build should mean.  A program
   whose output really does depend on where a mapping landed is
   nondeterministic under ASLR, and its statement should be false.

   ANTI-VACUITY is a behaviour here, not a side condition.  Each arm is
   [alt (errno_from mmap_errnos) (choose ...)]: when no address
   satisfies the guard the [choose] is unsatisfiable, the [alt] collapses
   onto its errno arm, and the model MUST answer -ENOMEM.  So an
   exhausted address space is modeled rather than a gap, and no
   totality obligation is needed to keep statements from going vacuous
   (this is the same collapse the backed-memory budget uses to force
   its out-of-memory point).

   A KERNEL-LIKE SEARCH BELONGS IN THE UNTRUSTED TIER, beside the proof
   library in theories/Common/, for proof strategies that want one
   concrete address rather than a quantifier.
   theories/Common/PlacementSearch.v holds it: the free-gap decision
   procedure, and the executable
   placement function with its soundness lemma against these very
   conditions.  What is NOT there is an unconditional nonemptiness
   lemma, and that is a fact rather than a gap: over an ARBITRARY ledger
   the admissible set really can be empty, so the honest unconditional
   statement is a counting argument, which is not written.  Nothing
   above depends on any of it -- the anti-vacuity paragraph is what
   keeps statements non-vacuous, and it holds whatever that tier
   contains.  The spec does not name that file, and determinism claims
   are welcome there and unnecessary here.
   ========================================================================= *)

(** The ordinary rw mmap shape: PRIVATE ANONYMOUS READ+WRITE at offset
    0, with any [fd].  Fresh PROT_NONE and the two bounded contained
    MAP_FIXED shapes are recognized separately below.  A NON-NULL [addr]
    is not constrained: without MAP_FIXED it is only a hint the kernel
    may honor or ignore, and the model's nondeterministic placement
    covers both.  A NULL [addr] leaves the kernel to place, and the
    address the model may then choose is bounded by the [choose] guard's
    admissibility conditions — see the placement section above.
    Everything else — file-backed mappings, MAP_SHARED, executable
    permissions, and unknown flag bits other than MAP_NORESERVE
    ([mmap_flags_core]) — is unmodeled and
    must yield [unmodeled] (fail closed): the machine model has no mutable page
    permissions and no file-backed memory, so honoring those calls
    with zero-filled rw memory would invent behavior no real kernel
    produces. *)
Definition mmap_modeled_b (prot flags off : word) : bool :=
  Z.eqb (bv_unsigned prot) (PROT_READ + PROT_WRITE)
  && Z.eqb (mmap_flags_core flags) (MAP_PRIVATE + MAP_ANONYMOUS)
  && w_is0 off.

(** A fresh inaccessible anonymous reservation.  musl's mallocng uses
    this after a failed brk, then enables one metadata page with mprotect;
    an allocator or sanitizer runtime that reserves a large region up
    front and commits slices of it later opens with the same call, which
    is why the MAP_NORESERVE spelling of it is matched here too. *)
Definition mmap_noaccess_b (prot flags off : word) : bool :=
  Z.eqb (bv_unsigned prot) PROT_NONE
  && Z.eqb (mmap_flags_core flags) (MAP_PRIVATE + MAP_ANONYMOUS)
  && w_is0 off.

(** The contained MAP_FIXED guard-page overwrite used by musl after a
    successful brk reservation.  The spec below supports only a range
    wholly covered by one tracked anonymous mapping. *)
Definition mmap_fixed_noaccess_b (prot flags off : word) : bool :=
  Z.eqb (bv_unsigned prot) PROT_NONE
  && Z.eqb (mmap_flags_core flags) (MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED)
  && w_is0 off.

(** The contained MAP_FIXED rw COMMIT: the mirror image of the shape
    above, and the second half of the reserve-then-commit idiom.  A
    program reserves a region PROT_NONE and later turns slices of it into
    usable memory in place; musl reaches that state through [mprotect]
    ([mprotect_spec]), allocators and sanitizer runtimes reach it through
    an rw MAP_FIXED over the same reservation.

    Like its PROT_NONE twin, the spec below supports only a range wholly
    covered by ONE tracked anonymous mapping.  That containment is doing
    more work here than it does there, and it is worth saying why.  The
    PROT_NONE shape only ever makes memory LESS reachable; the effect it
    emits is an unmap, so a containment mistake costs the model a fault
    it should not have produced.  This shape makes memory MORE reachable
    — it hands back a page of readable zeroes — so a containment mistake
    would have the model invent memory the process does not own.  The
    gate is therefore the same one [mprotect_spec] uses before it exposes
    zeroes ([map_contains] on [vm_maps]), and for the same reason.

    What it does NOT need is [mprotect_spec]'s second conjunct.  That
    spec must additionally see the range as wholly protected or wholly
    unprotected, because it can only describe a uniform permission
    transition.  MAP_FIXED has no such restriction: it REPLACES the range
    whatever was there, so a range that is part protected and part live
    is as ordinary as either pure case, and [maps_subtract] removes
    exactly the covered part of each [vm_noaccess] interval.

    Ownership is untouched, but backed accounting changes exactly with
    accessibility.  Removing the committed slice from [vm_noaccess]
    increases [vm_backing_used] by the newly exposed portion for ordinary
    mappings; MAP_NORESERVE retains lazy first-touch accounting.  The success
    is available only when that resulting state stays within [vm_limit].
    Replacing an already-accessible slice therefore costs nothing, while
    committing a reserved slice consumes its page-rounded size.

    This shape has two FURTHER sub-cases, split on the ledger rather
    than on the arguments.  A range that meets no live mapping at all is
    not a commit but an ordinary anonymous grant naming its own address,
    and it is charged and recorded like one; the branch documents why
    that adds nothing the model did not already admit.  A range that
    meets live mappings without being contained in one is the SPANNING
    replacement — see the section that introduces
    [mmap_fixed_rw_span_next] for what Linux does there and why the
    contained arm keeps its own post-state. *)
Definition mmap_fixed_rw_b (prot flags off : word) : bool :=
  Z.eqb (bv_unsigned prot) (PROT_READ + PROT_WRITE)
  && Z.eqb (mmap_flags_core flags) (MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED)
  && w_is0 off.

(** State after a successful contained rw MAP_FIXED replacement.  Naming
    this once keeps the relational spec and executable checker on the same
    exact backed-memory calculation, including mixed accessible/PROT_NONE
    ranges where only the newly exposed pages add to the budget. *)
Definition mmap_fixed_rw_next (h : VmMaps) (addr n : word) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (vm_maps h)
    (maps_subtract (vm_noaccess h)
       (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

(** The contained rw MAP_FIXED exposes part of the protected list and
    adds nothing to it. *)
Lemma mmap_fixed_rw_next_noaccess_nonzero : forall h addr n,
  vm_noaccess_entries_nonzero h ->
  vm_noaccess_entries_nonzero (mmap_fixed_rw_next h addr n).
Proof.
  intros h addr n H. unfold vm_noaccess_entries_nonzero, mmap_fixed_rw_next.
  cbn [vm_noaccess]. now apply maps_subtract_nonzero.
Qed.

(* =========================================================================
   MAP_FIXED THAT SPANS — the case that is neither contained nor free

   The two contained shapes above cover a MAP_FIXED wholly inside one
   tracked mapping, and their free-range twins cover one that meets
   nothing.  Everything between — a partial overlap, a range covering
   two mappings, a range covering one whole mapping and part of another
   — is what Linux calls replacement and this section models.

   [__mmap_prepare] (mm/vma.c:2386, Linux v6.18.46) hands every VMA
   overlapping [addr, addr + len) to [vms_gather_munmap_vmas] (:2404,
   defined at :1372), which SPLITS the first at [addr] when the range
   starts inside it (:1401) and the last at the end when the range ends
   inside it (:1422), then detaches everything between.  The splits are
   why the bytes OUTSIDE the request survive: those remnants were never
   detached.  [__mmap_region] (:2682) then installs one new mapping over
   the whole request, merging it with its neighbours where it can
   ([vma_merge_new_range], :2708).

   So the ledger after a success is: every entry re-cut by
   [maps_subtract] over the request, plus one entry for the request
   itself.  [maps_subtract] is exactly [__split_vma]'s effect on the
   model's intervals — it keeps the parts of each entry outside the cut,
   splitting a straddling entry into a left and a right remnant.

   WHY THE CONTAINED ARMS DO NOT USE THIS FORM, though it would give the
   same bytes: a contained request leaves Linux's VMA whole apart from
   the splits, and re-cutting the model's entry into [left; right; new]
   would FRAGMENT a tracked allocation that is still one allocation.
   [State.map_contains] asks whether ONE entry covers a range, and
   [Mprotect.mprotect_spec] and the contained MAP_FIXED shapes above all
   gate on it, so fragmenting here would silently narrow their modeled
   surface on a later call.  The two forms agree on the byte set and on
   [State.live_bytes]; [Checks/Cases/Mm/Mmap.v]'s
   [mmap_fixed_span_agrees_with_contained_on_backing] pins that on a
   witness, and [mmap_fixed_contained_stays_unfragmented] pins that the
   contained arm is the one that runs.

   WHAT MERGING COSTS, since the model does not do it: a real kernel may
   fold the new mapping into an adjacent one, so its single VMA can be
   larger than the model's single entry.  That makes the model's
   [map_contains] NARROWER than the kernel's, which declines where Linux
   would answer — the safe direction, and the same direction the split
   remnants already push.
   ========================================================================= *)

(** The ledger a destructive MAP_FIXED failure leaves: the request's
    range is gone from both ledgers and nothing replaces it.
    [vms_abort_munmap_vmas] writes NULL over exactly
    [[vms->start, vms->end)] (mm/vma.c:2365-2366, Linux v6.18.46), so the
    split remnants outside the request survive here too — which is why
    this is [maps_subtract] over the request rather than the removal of
    whole entries. *)
Definition mmap_fixed_destroyed_next (h : VmMaps) (addr n : word) : VmMaps :=
  mkVmMapsFull (vm_reserved h)
    (maps_subtract (vm_maps h)
       (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    (maps_subtract (vm_noaccess h)
       (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

(** A destructive MAP_FIXED failure leaves the request as a hole in both
    ledgers; the protected list only loses entries. *)
Lemma mmap_fixed_destroyed_next_noaccess_nonzero : forall h addr n,
  vm_noaccess_entries_nonzero h ->
  vm_noaccess_entries_nonzero (mmap_fixed_destroyed_next h addr n).
Proof.
  intros h addr n H.
  unfold vm_noaccess_entries_nonzero, mmap_fixed_destroyed_next.
  cbn [vm_noaccess]. now apply maps_subtract_nonzero.
Qed.

(** The ledger after a successful rw MAP_FIXED that spans: the request
    is owned and accessible, every entry it meets is re-cut around it. *)
Definition mmap_fixed_rw_span_next (h : VmMaps) (addr n : word) : VmMaps :=
  mkVmMapsFull (vm_reserved h)
    ((addr, n) :: maps_subtract (vm_maps h)
                    (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    (maps_subtract (vm_noaccess h)
       (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

(** The spanning rw MAP_FIXED conses the request onto [vm_maps] only;
    the protected list is cut, not grown. *)
Lemma mmap_fixed_rw_span_next_noaccess_nonzero : forall h addr n,
  vm_noaccess_entries_nonzero h ->
  vm_noaccess_entries_nonzero (mmap_fixed_rw_span_next h addr n).
Proof.
  intros h addr n H.
  unfold vm_noaccess_entries_nonzero, mmap_fixed_rw_span_next.
  cbn [vm_noaccess]. now apply maps_subtract_nonzero.
Qed.

(** …and after a PROT_NONE one: owned and inaccessible.  Ownership can
    GROW here where it cannot in the contained arm — the part of the
    request that met nothing is newly owned — but backed accounting
    cannot: the request lands in [vm_noaccess] whole, so
    [State.vm_backed_maps] cuts it out and [State.vm_backing_used] can
    only fall.  That is why this shape carries no budget guard and its
    rw twin does. *)
Definition mmap_fixed_noaccess_span_next (h : VmMaps) (addr n : word)
    : VmMaps :=
  mkVmMapsFull (vm_reserved h)
    ((addr, n) :: maps_subtract (vm_maps h)
                    (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    ((addr, n) :: maps_subtract (vm_noaccess h)
                    (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

(** The spanning PROT_NONE MAP_FIXED is the one named post-state that
    GROWS the protected list, so it is the one with a side condition:
    the request it conses must name a byte.  [mmap_spec] supplies that
    at the call site through [mmap_request_len_nonzero], the length
    having passed a [w_is0] gate and the rounded-end bound. *)
Lemma mmap_fixed_noaccess_span_next_noaccess_nonzero : forall h addr n,
  (0 < bv_unsigned n)%Z ->
  vm_noaccess_entries_nonzero h ->
  vm_noaccess_entries_nonzero (mmap_fixed_noaccess_span_next h addr n).
Proof.
  intros h addr n Hn H.
  unfold vm_noaccess_entries_nonzero, mmap_fixed_noaccess_span_next.
  cbn [vm_noaccess]. apply entries_nonzero_cons; [exact Hn |].
  now apply maps_subtract_nonzero.
Qed.

(** …and the same from the GATES the arm has already passed rather than
    from the size it computed, which is the form a call site can cite.
    [mmap_spec] binds [n] to the page-rounded length past a [w_is0]
    refusal and a bound on the rounded end, and those two are exactly
    what [mmap_request_len_nonzero] consumes. *)
Lemma mmap_fixed_noaccess_span_next_noaccess_nonzero_of_len :
  forall h addr len n,
  w_is0 len = false ->
  (page_round_up_Z (bv_unsigned len) < two_pow_64)%Z ->
  n = Z_to_bv 64 (page_round_up_Z (bv_unsigned len)) ->
  vm_noaccess_entries_nonzero h ->
  vm_noaccess_entries_nonzero (mmap_fixed_noaccess_span_next h addr n).
Proof.
  intros h addr len n H0 Hfit -> H.
  apply mmap_fixed_noaccess_span_next_noaccess_nonzero;
    [now apply mmap_request_len_nonzero | exact H].
Qed.

Definition mmap_noreserve_backed_ok (flags : word) (m : Model)
    (nZ : Z) : bool :=
  if mmap_noreserve_b flags then true
  else (vm_backing_used m + nZ <=? vm_limit (m_vmmaps m))%Z.

Definition mmap_fixed_rw_budget_ok (flags : word) (m : Model)
    (addr n : word) : bool :=
  vm_backing_within_limit
    (with_mmap_replacement flags addr n
      (with_vmmaps (mmap_fixed_rw_next (m_vmmaps m) addr n) m)).

(** The same gate on the spanning post-state, and it is doing more work
    than its contained twin.  There the request was already owned, so
    the only budget movement was the newly EXPOSED part; here the part
    of the request that met nothing is newly OWNED as well, and Linux
    charges it: [__mmap_prepare] takes the commit charge
    [map->charged = map->pglen - vms->nr_accounted] and calls
    [security_vm_enough_memory_mm] when that delta is nonzero
    (mm/vma.c:2422-2429, Linux v6.18.46), where [nr_accounted] counts
    only the VM_ACCOUNT pages the gather detached (:1439-1440) — that
    is, only the pages already inside the request.  Testing the whole
    post-state is the same delta read on the model's ledger. *)
Definition mmap_fixed_rw_span_budget_ok (flags : word) (m : Model)
    (addr n : word) : bool :=
  vm_backing_within_limit
    (with_mmap_replacement flags addr n
      (with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps m) addr n) m)).

(* =========================================================================
   MAP_FIXED_NOREPLACE — placed exactly, refused rather than replaced

   MAP_FIXED_NOREPLACE (0x100000, include/uapi/asm-generic/mman-common.h:31,
   Linux v6.18.46) asks for what MAP_FIXED asks for — placement at
   [addr] exactly — with one difference: where MAP_FIXED tears down
   whatever the range holds and installs the new mapping over it, this
   bit makes the kernel REFUSE the call when any page of the range is
   mapped already.  [do_mmap] (mm/mmap.c, Linux v6.18.46) decides both
   halves:

     mm/mmap.c:361-362   if (flags & MAP_FIXED_NOREPLACE)
                                 flags |= MAP_FIXED;
     ...
     mm/mmap.c:406       addr = __get_unmapped_area(file, addr, len, pgoff,
                                                    flags, vm_flags);
     mm/mmap.c:410-413   if (flags & MAP_FIXED_NOREPLACE) {
                                 if (find_vma_intersection(mm, addr, addr + len))
                                         return -EEXIST;
                         }

   The first is PLACEMENT.  From :362 on the request carries MAP_FIXED,
   so [__get_unmapped_area] hands [addr] back unchanged — both generic
   searches return it at their [if (flags & MAP_FIXED) return addr;]
   (mm/mmap.c:700 and :750) — and runs the bounds and alignment tests
   the MAP_FIXED arms above cite: [len > TASK_SIZE] at :824, [addr >
   TASK_SIZE - len] at :857, [offset_in_page(addr)] at :859,
   [security_mmap_addr] at :862.  The argument gate of the two shapes
   below is therefore the MAP_FIXED arms' gate verbatim, in the same
   order, and it PRECEDES the refusal: an unaligned [addr] inside a live
   mapping is -EINVAL, not -EEXIST.

   The second is the REFUSAL.  [find_vma_intersection] (mm/mmap.c:885-893)
   is [mt_find(&mm->mm_mt, &index, end_addr - 1)] from [start_addr]: the
   first VMA meeting the half-open interval [[addr, addr + len)].  So
   ANY mapped page of the request, whatever else in it is free, answers
   -EEXIST — before [mmap_region] runs, with nothing changed.  The model
   asks the same question of its ledger: [region_free] against
   [vm_reserved ++ vm_maps], the disjointness test every fresh grant
   already passes.  A range that meets nothing is exactly the free-range
   MAP_FIXED sub-case and is answered as that sub-case is, lazy
   MAP_NORESERVE backing included; a range that meets anything is
   -EEXIST.

   THE IMAGE IS AN ANSWER HERE WHERE MAP_FIXED DECLINES.  A MAP_FIXED
   over the image's LOAD reservations stays [unmodeled], because the
   replacement it performs has no representation: the image bytes are
   [State.Image] segments, not entries of this ledger.  This bit
   performs no replacement.  Those pages are mapped — the VMAs
   [load_elf_binary] installed for them — so [find_vma_intersection]
   finds one and the answer is -EEXIST with nothing changed, which the
   ledger CAN say; [vm_reserved] is in the test for that reason.

   BOTH BITS TOGETHER is not "MAP_FIXED wins".  :361-362 is the only
   place [do_mmap] reads the NOREPLACE bit before placement, and it only
   ADDS MAP_FIXED to the word; :410 then tests the NOREPLACE bit alone,
   whatever else is set.  So MAP_FIXED | MAP_FIXED_NOREPLACE reaches
   every test MAP_FIXED_NOREPLACE alone reaches, with the same flags
   word from :362 on, and [calc_vm_flag_bits] (include/linux/mman.h:153-162,
   Linux v6.18.46) translates neither bit into a VM_ flag, so the
   mapping installed on success is the same one.  [mmap_noreplace_flags_b]
   accepts both spellings and the arms answer them alike: -EEXIST on an
   occupied range.  A model that let MAP_FIXED win would admit a
   replacement Linux refuses.

   WHAT ELSE LINUX CAN ANSWER on the occupied path, and which of it the
   arms carry.  Three -ENOMEMs sit before :410.  The wrapped
   page-rounding at :368-370 and :857's bound are the argument gate's,
   answered as the MAP_FIXED arms answer them; [mm->map_count >
   sysctl_max_map_count] at :377-378 is the environment failure every
   arm in this file admits through [errno_from mmap_errnos], because the
   model tracks no map count.  So the occupied sub-case is
   [alt (errno_from mmap_errnos) (err_ret EEXIST)]: -EEXIST is the
   answer, and the -ENOMEM beside it is the one every other mmap arm
   already admits.  Nothing else reaches it: MAP_LOCKED's -EPERM
   (:415-417) needs a bit outside the shape, and [mlock_future_ok]'s
   -EAGAIN (:419-420) needs VM_LOCKED in [def_flags], which only
   [mlockall(MCL_FUTURE)] sets and no modeled call does.  The free-range
   sub-case's answers are the MAP_FIXED free-range sub-case's, for the
   reasons given there.

   WHY -EEXIST IS FORCED, under the scope README.md states.  The target
   is any variant of Linux, and the variants differ on this bit in one
   way only: a kernel from before the bit existed ignores it, treats
   [addr] as a hint and answers a placement (the bit reached Linux in
   v4.17).  Every supported kernel has it — README.md's scope section
   states the floor this relies on, stable kernels from v4.17 on — and
   on every one of them an occupied range answers -EEXIST
   (or the map-count -ENOMEM above), whatever the layout, address-space
   size or randomisation: [find_vma_intersection] reads the VMA tree and
   nothing else.  QEMU's user-mode emulation agrees: [target_mmap]
   (linux-user/mmap.c, read at QEMU 8.2.2) answers EEXIST for a
   MAP_FIXED_NOREPLACE request whose guest range is not empty.  (It can
   also answer EEXIST on a range the GUEST has free: without
   [reserved_va] it keeps the bit on the host mmap and a host-side
   collision comes back as EEXIST, linux-user/mmap.c:655-659 and
   :738-745 at the same version — a second free-range residual beside
   the vdso one below.)  The
   refusal is therefore not a placement choice the statement quantifies
   over but a point every admitted implementation reaches, so a
   statement over a program that meets it must reproduce it on the
   target side: [Equivalence.equiv] compares whole trace sets, and the
   source's set contains the -EEXIST trace.

   WHAT THE LEDGER CANNOT SEE, since -EEXIST is rejected on a range the
   ledger calls free.  The kernel's own VMAs — the vdso/vvar pair
   [execve] installs — are in neither ledger, so a request that lands
   on them answers -EEXIST on Linux and is rejected here; the stack is
   kept out by [alloc_top], which declines the band above it.  That is
   a known limitation of the model, the same absence [munmap]'s
   free-range arm has.
   ========================================================================= *)

(** Does [flags] spell a MAP_FIXED_NOREPLACE request over the plain
    anonymous shape?  Two spellings, deliberately both: the bit alone,
    and the bit beside MAP_FIXED, which [do_mmap] folds into the same
    flags word at mm/mmap.c:361-362 before anything else reads it (the
    section above).  MAP_NORESERVE is masked as everywhere else
    ([mmap_flags_core]); every other bit must be absent, so MAP_SHARED,
    MAP_HUGETLB, MAP_POPULATE and the rest still leave the modeled
    surface.  The bit is MATCHED, not stripped: stripping it would send
    an occupied-range request into the MAP_FIXED arms, which replace
    where Linux refuses. *)
Definition mmap_noreplace_flags_b (flags : word) : bool :=
  Z.eqb (mmap_flags_core flags)
        (MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED_NOREPLACE)
  || Z.eqb (mmap_flags_core flags)
           (MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED + MAP_FIXED_NOREPLACE).

(** The rw and PROT_NONE NOREPLACE shapes: the two MAP_FIXED shapes'
    prot words over [mmap_noreplace_flags_b], at offset 0.  A sealed
    sanitizer runtime opens with three of these — its low shadow (rw),
    the gap between the shadows (PROT_NONE) and its high shadow (rw),
    all MAP_NORESERVE — before any other mapping, so that a range some
    layout already occupies is refused rather than overwritten. *)
Definition mmap_noreplace_rw_b (prot flags off : word) : bool :=
  Z.eqb (bv_unsigned prot) (PROT_READ + PROT_WRITE)
  && mmap_noreplace_flags_b flags && w_is0 off.

Definition mmap_noreplace_noaccess_b (prot flags off : word) : bool :=
  Z.eqb (bv_unsigned prot) PROT_NONE
  && mmap_noreplace_flags_b flags && w_is0 off.

(** [mmap addr len prot flags fd off].  Three things are decided before
    any shape is matched, in the kernel's own order.

    A MISALIGNED [off] is -EINVAL, whatever else the call says: riscv's
    [riscv_sys_mmap] tests it before it calls into generic mm at all
    ([mmap_off_aligned_b]).  The one exception is a [len] whose
    page-rounding wraps, which is declined rather than answered because
    qemu-user reaches the call in the other order -- see
    [mmap_pglen_ok_b], which also says which policy that follows.

    Then MAP_ANONYMOUS.  With the bit CLEAR the request is FILE-BACKED,
    and the whole path is [unmodeled]; the branch below says why in
    full, and which real answer it declines to give.  The short version
    is that the model can neither hold a readable-but-not-writable page
    nor tie a mapping to the file it came from.

    Then len = 0, which is -EINVAL for the plain anonymous shape
    ([mmap_plain_anon_b]) and [unmodeled] for the huge-page one, because
    Linux looks at the FLAGS first and the length second — see
    [mmap_plain_anon_b] for the citations.  For the modeled shape
    ([mmap_modeled_b]): either fails
    with an errno from [mmap_errnos], or the kernel grants ANY
    page-aligned, nonzero
    region below [alloc_top] (hence disjoint from the stack) that
    is disjoint from the binary image and from every live allocation
    (see the disjointness note above, and the placement section for why
    the guard says that and no more) and that fits the run's remaining
    backed-memory budget (the complete post-state [vm_backing_used] within
    [vm_limit] — a spent budget leaves only the errno branch, the
    forced out-of-memory point); the region is recorded
    so later grants cannot alias it, and the grant is zero-filled
    ([eff_zeros]) as Linux zero-fills anonymous pages.  The fresh
    PROT_NONE branch uses the same placement rules but consumes no backed
    budget; it records the reservation in both ledgers and erases any stale
    mutable overlay bytes through [eff_unmaps] so the inaccessible range
    cannot be read by the machine.  The two MAP_FIXED
    branches share one argument gate and then split on the LEDGER.  A range
    wholly inside one live anonymous mapping is replaced in place,
    preserving ownership and budget — the PROT_NONE branch installing
    fresh inaccessible pages and emitting the exact [eff_unmaps] range,
    the rw one installing fresh zeroed pages and emitting the same range
    as [eff_zeros] — with THREE resolutions, because a MAP_FIXED over
    live memory can fail after it has already torn that memory down.  A
    range that meets NO live mapping is an ordinary anonymous grant
    naming its own address: the rw branch charges and records it like any
    grant, with TWO resolutions, since a MAP_FIXED over a gap destroys
    nothing on the way out.  Everything between the two — a partial
    overlap, a range covering several mappings — is the SPANNING case,
    which replaces every anonymous mapping the request meets and keeps
    the parts of them that fall outside it, with three resolutions like
    the contained case.  A range reaching the image's LOAD reservations
    is the one that still stays unmodeled.  The two
    MAP_FIXED_NOREPLACE branches take the same argument gate and split
    ONCE on the ledger: a range meeting nothing is the free-range
    sub-case again, and a range meeting anything — the image included —
    is -EEXIST with nothing changed (see the MAP_FIXED_NOREPLACE
    section).  Each branch
    documents its own resolutions.  Any other
    prot/flags/off combination is unmodeled: [unmodeled] (fail
    closed).  [fd] is not part of any shape: under MAP_ANONYMOUS Linux
    never reads it (see [mmap_fd_none]).  MAP_NORESERVE is the one flag
    bit removed before a shape is matched, and only that bit — see [mmap_flags_core] for what the
    kernel does with it and why ignoring it is the conservative
    direction.  The rounded length is computed in [Z]; it re-enters
    [word] only when the bound check already confines it below
    [alloc_top]. *)
Definition mmap_spec (addr len prot flags fd off : word) : Sys SyscallEffect :=
  if negb (mmap_off_aligned_b off) then
    (if mmap_pglen_ok_b len then err_ret EINVAL else unmodeled)
  else if negb (mmap_anon_b flags) then
    (* FILE-BACKED: MAP_ANONYMOUS is clear, so Linux resolves [fd] and
       maps a file's pages.  Everything here is [unmodeled], and there
       are two independent reasons, either of which alone would force it.

       (1) THE MACHINE MODEL HAS NO READ-ONLY PAGE.  A private file
       mapping's usual prot is PROT_READ, and
       [RiscvSemantics.machine_state]'s writable overlay [ms_mem] is
       simultaneously the only source of readable bytes outside the
       loaded segments ([RiscvSemantics.ov_read_bytes] falls back to
       [memory_read], never to [ms_rom]) and the whole of the writable
       view ([RiscvSemantics.wview], hence [State.in_wmem] and every
       output-buffer gate).  Bytes put there are writable; bytes kept
       out of it are unreadable.  A readable-not-writable page therefore
       has no encoding, and answering the call either admits a store
       Linux answers with SIGSEGV or faults a load Linux serves.  That
       is the same wall [Mprotect.mprotect_spec] records for
       [mprotect(PROT_READ)], reached from the other side,
       and it takes the same core change to close: a channel from a
       [SyscallEffect] to a read-only view.

       (2) THE MODEL CANNOT TIE A MAPPING TO ITS FILE.  Even at
       PROT_READ|PROT_WRITE, where [ms_mem] does describe the
       permissions exactly (a MAP_PRIVATE mapping is copy-on-write, so
       stores stay out of the file), the bytes would have to be read
       from [m_fs] and installed as [eff_writes] AT MMAP TIME, and Linux
       populates the mapping from the page cache LATER.  A [write]
       through a second fd, an [ftruncate] or an [unlinkat] between the
       mmap and the first touch is visible through a private mapping
       that has not been written to yet, so a snapshot would be stale
       and the model would be claiming, as certain, bytes no supported
       implementation produces.  [State.VmMaps] records ranges and
       nothing else, so there is no ledger to consult; giving it one
       means declining at the five specs that mutate [m_fs] as well
       ([write], [writev], [ftruncate], [openat] with O_TRUNC,
       [unlinkat]).

       ONE ANSWER ON THIS PATH IS DELIBERATELY NOT TAKEN, and it is
       worth saying which and why.  [ksys_mmap_pgoff] opens the
       file-backed path with

         if (!(flags & MAP_ANONYMOUS)) {
                 audit_mmap_fd(fd, flags);
                 file = fget(fd);
                 if (!file)
                         return -EBADF;

       (mm/mmap.c, [ksys_mmap_pgoff], Linux v6.18.46), decided before
       the length and before [do_mmap] runs at all, so an [fd] the
       process does not hold is -EBADF on Linux whatever the other
       arguments say -- and the model holds the fd table that would
       answer it.  QEMU's user-mode emulation never resolves the fd at
       all: [target_mmap] (linux-user/mmap.c) validates the request
       itself and lets the host mmap discover the descriptor, so it
       answers its own -EINVAL or -ENOMEM wherever one of its checks
       fires first.  Measured on qemu-riscv64, against the -EBADF
       Linux v6.18.46 gives for each: a zero length, a length within a
       page of 2^64, an invalid MAP_TYPE, an unknown prot bit, and
       MAP_FIXED at an unaligned address.  The two walls above already
       force the decline for every LIVE fd, so what this paragraph
       settles is only the closed-fd corner.  README.md's design-priorities
       section counts QEMU's user-mode emulation among the supported
       implementations, and it made each of those five qemu-user answers
       a real behaviour, so an unconditional -EBADF would claim a
       behaviour outside the intersection.  An -EBADF hedged by a list of
       argument shapes would be the only sound version, and it would sit
       in front of a path that declines for two other reasons anyway, so
       this arm declines outright instead.  Reconsidering it is a
       decision about whether those answers are QEMU's bugs or its
       behaviour, not a decision about this arm. *)
    unmodeled
  else if w_is0 len then
    (if mmap_plain_anon_b flags then err_ret EINVAL else unmodeled)
  else if mmap_modeled_b prot flags off then
    alt
      (e <- errno_from mmap_errnos ;; err_ret e)
      (m <- get_model ;;
       let h := m_vmmaps m in
       let nZ := page_round_up_Z (bv_unsigned len) in
       let n := Z_to_bv 64 nZ in
       a <- choose (fun a => (bv_unsigned a mod page_size = 0)%Z
                             /\ (0 < bv_unsigned a)%Z
                             /\ (bv_unsigned a + nZ <= alloc_top h)%Z
                             /\ region_free (vm_reserved h ++ vm_maps h) a n = true
                              /\ mmap_noreserve_backed_ok flags m nZ = true) ;;
       modify (fun _ =>
         with_mmap_backing flags a n
           (with_vmmaps
              (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
                (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h)
                (vm_mmap_base h) (vm_init_sp h)) m)) ;;
       pure (mkEffect a [] [(a, n)]))
  else if mmap_noaccess_b prot flags off then
    alt
      (e <- errno_from mmap_errnos ;; err_ret e)
      (m <- get_model ;;
       let h := m_vmmaps m in
       let nZ := page_round_up_Z (bv_unsigned len) in
       let n := Z_to_bv 64 nZ in
       a <- choose (fun a => (bv_unsigned a mod page_size = 0)%Z
                             /\ (0 < bv_unsigned a)%Z
                             /\ (bv_unsigned a + nZ <= alloc_top h)%Z
                             /\ region_free (vm_reserved h ++ vm_maps h) a n = true) ;;
       modify (fun _ =>
         with_mmap_backing flags a n
           (with_vmmaps
             (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
               ((a, n) :: vm_noaccess h) (vm_start_brk h)
               (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)) ;;
       pure (mkEffectU a [] [] [(a, n)] [] []))
  else if mmap_fixed_noaccess_b prot flags off then
    (* ARGUMENT GATE, in Linux's order (Linux v6.12).  [do_mmap] rounds
       the length and runs its bounds — all -ENOMEM — before any address
       is looked at, and [__get_unmapped_area] runs two more -ENOMEM
       bounds BEFORE the alignment -EINVAL:

         mm/mmap.c:315-317   len = PAGE_ALIGN(len); if (!len)  -ENOMEM
         mm/mmap.c:323-325   map_count > sysctl_max_map_count  -ENOMEM
         mm/mmap.c:883-884   len > TASK_SIZE                   -ENOMEM
         mm/mmap.c:915-916   addr > TASK_SIZE - len            -ENOMEM
         mm/mmap.c:917-918   offset_in_page(addr)              -EINVAL

       [generic_get_unmapped_area] hands MAP_FIXED's [addr] straight
       back, before any rounding (mm/mmap.c:763-764), so the alignment
       test at :917 sees the caller's address unchanged.

       Hence the first test.  [addr + PAGE_ALIGN(len) >= 2^64] covers
       both the wrapped round-up of :316 (which forces
       [addr + nZ >= 2^64] as well, [addr] being unsigned) and the bound
       at :915: the [len] live at :915 is the PAGE-ALIGNED length
       ([do_mmap] assigned it at :315 and [__get_unmapped_area] never
       reassigns its parameter), and :883 already guarantees
       [len <= TASK_SIZE] there, so :915 reads [addr + len > TASK_SIZE]
       — which [addr + len >= 2^64] implies for every
       [TASK_SIZE < 2^64], with no knowledge of the actual TASK_SIZE
       needed.  -ENOMEM, deterministically.
       [mmap(0x1001, (size_t)-1, PROT_NONE,
       MAP_PRIVATE|MAP_ANONYMOUS|MAP_FIXED, -1, 0)] is that case.

       This also removes a disagreement between the three branches: an
       overflowing length already yields -ENOMEM in the two fresh-grant
       branches above, where it makes their [choose] guard
       ([a + nZ <= alloc_top h]) unsatisfiable and collapses the [alt]
       onto [mmap_errnos = [ENOMEM]].  Only this branch answered
       [unmodeled].

       The residual of :915 — [addr + nZ < 2^64] but still
       [addr > TASK_SIZE - len] — is what the second test fails closed
       on.  This arm does not consult [State.TASK_SIZE]; it commits to
       the -EINVAL of :917 only below [State.alloc_top], the run's
       stack-derived grant top, with its own justification.  For a
       [Run.valid_sp] stack pointer the top is under [sp_window_hi -
       stack_max_size], hence under [State.TASK_SIZE] = 0x800000000000,
       the Sv48 [TASK_SIZE_64 = PGDIR_SIZE * PTRS_PER_PGD / 2]
       (arch/riscv/include/asm/pgtable.h at v6.18.46) that this
       development's whole address-space layout assumes (see
       [State.sp_window_lo]); a ledger whose stack pointer is outside
       that window is outside the theorem.  At or above the top:
       [unmodeled].

       -EPERM is deliberately NOT modeled.  [security_mmap_addr]
       ([__get_unmapped_area], mm/mmap.c:862-863) runs after the
       alignment test, and its baseline hook [cap_mmap_addr]
       (security/commoncap.c:1459-1471) only fires below
       [dac_mmap_min_addr], whose default is 4096
       (security/min_addr.c:11 defines it from
       CONFIG_DEFAULT_MMAP_MIN_ADDR, mm/Kconfig:726 declares that symbol
       and :729 gives it that default, Linux v6.18.46).  The only
       page-aligned address it can reject is therefore 0, and the fourth
       gate below declines it — for BOTH MAP_FIXED shapes and BOTH of
       each shape's sub-cases, so no sub-case has to re-derive it. *)
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (two_pow_64 <=? bv_unsigned addr + nZ)%Z then err_ret ENOMEM
    else
      m <- get_model ;;
      let h := m_vmmaps m in
      if negb (bv_unsigned addr + nZ <=? alloc_top h)%Z then unmodeled
      else if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then err_ret EINVAL
      else if negb (0 <? bv_unsigned addr)%Z then unmodeled
      else
      let n := Z_to_bv 64 nZ in
      if region_free (vm_reserved h) addr n
         && map_contains (vm_maps h) addr n
      then
      (* THREE RESOLUTIONS, because Linux produces three.  A MAP_FIXED
         over a live mapping tears the old range down in
         [vms_clean_up_area] (mm/vma.c:1281-1293, called from
         [__mmap_prepare] at :2441, Linux v6.18.46) — [vms_clear_ptes]
         runs [unmap_vmas] and [free_pgtables] and then clears
         [vms->clear_ptes] (mm/vma.c:1255-1280) — and it does so BEFORE
         the two allocations that can still fail, [vm_area_alloc] and
         [vma_iter_prealloc], both -ENOMEM ([__mmap_new_vma],
         mm/vma.c:2506-2508 and :2515-2518).  Either reaches
         [abort_munmap:] (mm/vma.c:2729-2730), and with [clear_ptes]
         false [vms_abort_munmap_vmas] (mm/vma.c:2349-2369) takes the
         destructive path:

           /* Aborting cannot just call the vm_ops open() because they
              are often not symmetrical and state data has been lost.
              Resort to the old failure method of leaving a gap where
              the MAP_FIXED mapping failed. */
           mas_set_range(mas, vms->start, vms->end - 1);
           mas_store_gfp(mas, NULL, GFP_KERNEL|__GFP_NOFAIL);

         The syscall returns an errno and the range comes back
         UNMAPPED, old contents gone.

         For exactly the shape this branch models — PROT_NONE, wholly
         inside one live anonymous mapping — the failures that are
         still NON-destructive are narrow.  [accountable_mapping]
         (mm/vma.c:2326-2336) is false without VM_WRITE, so
         [security_vm_enough_memory_mm] ([__mmap_prepare],
         mm/vma.c:2422-2432) never
         runs; [may_expand_vm] gets the delta [pglen - vms.nr_pages]
         (mm/vma.c:2418-2419), which is 0 when the whole requested
         range was already mapped; and [__mmap_region] has no
         [map_count] check of its own (the only increment is in
         [__mmap_new_vma], mm/vma.c:2543).  That leaves
         [vms_gather_munmap_vmas] (mm/vma.c:1389-1393) testing
         [mm->map_count >= sysctl_max_map_count],
         which fires only for the strictly-interior two-split case and
         is tested before any [__split_vma], so it returns -ENOMEM
         through [__mmap_prepare]'s gather-error arm (:2436-2440), which
         zeroes [vms->nr_pages] so that the abort at :2730 does nothing.

         So: an errno with the range preserved, the success, and an
         errno with the range destroyed.  [alt] composes, so this is
         [alt A (alt B C)].  The destructive resolution drops the range
         from BOTH ledgers and emits it in [eff_unmaps], which is what
         makes a later access to it fault instead of reading stale
         bytes.

         A separate, deliberate gap: even the non-destructive abort
         [reattach_vmas] (mm/vma.c:1351-1360) only clears each VMA's
         detached flag and destroys the side tree — it never re-merges,
         so the two [__split_vma] calls in [vms_gather_munmap_vmas]
         (mm/vma.c:1401, 1422) survive
         and a failed interior MAP_FIXED permanently costs up to two
         [map_count].  The model tracks no [map_count] at all, so this
         is not modeled here. *)
      alt
        (e <- errno_from mmap_errnos ;; err_ret e)
        (alt
          (modify (fun _ =>
             with_mmap_replacement flags addr n
              (with_vmmaps (mkVmMapsFull (vm_reserved h) (vm_maps h)
               ((addr, n) :: maps_subtract (vm_noaccess h)
                               (bv_unsigned addr)
                               (bv_unsigned addr + bv_unsigned n))
               (vm_start_brk h) (vm_brk h) (vm_limit h)
               (vm_mmap_base h) (vm_init_sp h)) m)) ;;
           pure (mkEffectU addr [] [] [(addr, n)] [] []))
          (e <- errno_from mmap_errnos ;;
           modify (fun _ => with_mmap_destroyed addr n
             (mmap_fixed_destroyed_next h addr n) m) ;;
           pure (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])))
      (* The same free-range sub-case the rw branch below carries, and for the
         same reason.  A PROT_NONE MAP_FIXED whose range meets no live mapping
         is not a guard page punched into something owned; it is a fresh
         inaccessible reservation that names its own address.  Its guards are
         [mmap_noaccess_b]'s [choose] guard conjunct for conjunct, and its
         post-state and effect are that branch's with [addr] where it writes
         the chosen [a], so like its rw twin it adds NO reachable transition —
         see [Checks/Cases/Mm/Mmap.v]'s
         [mmap_fixed_noaccess_fresh_adds_no_transition].
         Two resolutions, not three: with [vms.nr_pages] zero there is nothing
         to tear down and [vms_abort_munmap_vmas] returns at its first line
         (mm/vma.h:244-245), so the destructive one cannot arise.

         Leaving it out was an asymmetry rather than a decision, and a MEASURED
         one: a sealed sanitizer runtime fills the gap between its two shadow
         regions with exactly this call, and it was the single call the rest of
         this file still declined. *)
      else if region_free (vm_reserved h ++ vm_maps h) addr n
      then
      alt
        (e <- errno_from mmap_errnos ;; err_ret e)
        (a <- choose (fun a => a = addr) ;;
         modify (fun _ => with_mmap_backing flags a n
           (with_vmmaps (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
             ((a, n) :: vm_noaccess h) (vm_start_brk h)
             (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)) ;;
         pure (mkEffectU a [] [] [(a, n)] [] []))
      (* THE SPANNING SUB-CASE: the request meets live mappings without
         being contained in one.  See the MAP_FIXED-that-spans section
         above for the split-and-replace argument and for why the
         contained arm keeps its own post-state.

         THREE RESOLUTIONS, and the same three the contained arm has,
         for the same reason — the destructive boundary is
         [vms_clean_up_area] (mm/vma.c:1281-1293, called at :2441, Linux
         v6.18.46), the allocations that can still fail are past it, and
         [vms_abort_munmap_vmas] (:2349, taken at :2730) then leaves the
         request's range as a hole (:2365-2366) while the split remnants
         outside it survive.  What CAN be wider here than in the
         contained arm is the non-destructive half: [may_expand_vm] gets
         the delta [map->pglen - vms->nr_pages] (:2418), which is
         nonzero exactly when the request is not wholly covered by live
         mappings, so RLIMIT_AS can refuse such a call where it could
         not refuse a contained one.  NOT every spanning request,
         though: this arm is selected by [map_contains] failing, which
         asks whether ONE entry covers the range, so a request covered
         by two ADJACENT entries lands here with a delta of zero and
         RLIMIT_AS cannot refuse it either.  Nothing turns on which:
         the non-destructive resolution is an unguarded [errno_from
         mmap_errnos] superset in both cases.  Non-destructive because
         [vms->clear_ptes] is still set at that point (:1497), so the
         abort takes [reattach_vmas] (:2357-2358) and the range comes
         back.

         Two Linux answers this arm does not carry, both narrow.

         [vma_is_sealed] gives -EPERM (:1396-1398, :1416-1418).  Two
         things set VM_SEALED (include/linux/mm.h:447-448) and neither
         can reach a ledger entry this arm meets.  [mseal_apply]
         (mm/mseal.c:72, :78, the only setters in that file, reached
         only from [do_mseal] at :139 and its [SYSCALL_DEFINE3] at
         :187) needs the [mseal] syscall, 462, which is not in
         [Specs.syscall_spec]'s modeled surface — the same argument
         [Mremap.mremap_errnos] makes, there against v6.12.  And
         [VM_SEALED_SYSMAP] (include/linux/mm.h:4402-4405) aliases
         VM_SEALED under CONFIG_MSEAL_SYSTEM_MAPPINGS.  What carries
         that half is not a list of its users but a property of all of
         them: it is applied only by kernel-installed special mappings,
         and this model tracks NO special mapping in either ledger.
         Grepping VM_SEALED_SYSMAP over v6.18.46 gives eleven sites
         across seven architectures; the three a riscv64 task can meet
         are the arch vdso text (arch/riscv/kernel/vdso.c:139), the vvar
         datastore (lib/vdso/datastore.c:103), and the uprobes
         execute-out-of-line area (kernel/events/uprobes.c:1727) — the
         last installed at
         uprobe registration rather than by [execve], which is why the
         argument is phrased over the property and not over what
         [execve] does (the placement search has the same
         absence).  That second half is
         vacuous while those VMAs are absent, but this
         arm widens the class of requests that reach the question, so
         it is written down rather than left implicit.

         [max_map_count] gives -ENOMEM (:1389-1393) but only before any
         split, hence non-destructively, and the errno arm already
         admits it. *)
      else if region_free (vm_reserved h) addr n
      then
      alt
        (e <- errno_from mmap_errnos ;; err_ret e)
        (alt
          (modify (fun _ =>
             with_mmap_replacement flags addr n
               (with_vmmaps (mmap_fixed_noaccess_span_next h addr n) m)) ;;
           pure (mkEffectU addr [] [] [(addr, n)] [] []))
          (e <- errno_from mmap_errnos ;;
           modify (fun _ => with_mmap_destroyed addr n
             (mmap_fixed_destroyed_next h addr n) m) ;;
           pure (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])))
      (* WHAT STILL DECLINES, and it is one shape: a request that meets
         [vm_reserved], the image's LOAD reservations.  Linux would
         replace those pages like any others, but the model's image
         bytes do not live in this ledger — they are the [State.Image]
         segments the fetch and the memory overlay read — so replacing
         part of one here would leave the ledger and the machine
         disagreeing about what the process can execute.  A real answer
         has to move the image into the same replaceable representation
         the anonymous ledger uses, which is a change to [State.Image]
         and to every consumer of [vm_reserved], not to this arm.

         What it costs: a program that maps over its own text or data
         leaves the modeled surface on that call, and the [unmodeled]
         reaches the error transition, so one such call refutes the
         equivalence statement for that binary.  No modeled program
         shape does it — the runtimes the spanning
         arm serves reserve shadow memory well away from the image, and the
         shape that would meet this gate is a self-modifying or
         self-patching program, which the machine model has its own
         reasons not to describe.  The gate is on the ledger and not on
         [prot], so both MAP_FIXED spellings decline the same request;
         [Checks/Cases/Mm/Mmap.v] pins that as
         [mmap_fixed_rw_over_the_image_is_unmodeled] and
         [mmap_fixed_noaccess_over_the_image_is_unmodeled], with
         [mmap_fixed_rw_clear_of_the_image_replaces] — the same request
         one page clear of the image — as the anchor that keeps the
         decline from being reject-everything. *)
      else unmodeled
  else if mmap_fixed_rw_b prot flags off then
    (* THE ARGUMENT GATE IS THE ONE ABOVE, VERBATIM, and it has to be:
       every citation on it is about [do_mmap] and [__get_unmapped_area]
       reading the length and the address (mm/mmap.c:315-317, :323-325,
       :883-884, :915-918, Linux v6.12), and none of those four gates
       branches on [prot].  [do_mmap] does READ [prot] before them, at
       mm/mmap.c:303-305, but only to fold in PROT_EXEC under
       [READ_IMPLIES_EXEC]; that cannot change which of these four errnos
       is produced, so the gate is genuinely shared.  A shape that
       answered a different errno for the same [addr]/[len] would be
       claiming Linux branches on a register none of these gates reads. *)
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (two_pow_64 <=? bv_unsigned addr + nZ)%Z then err_ret ENOMEM
    else
      m <- get_model ;;
      let h := m_vmmaps m in
      if negb (bv_unsigned addr + nZ <=? alloc_top h)%Z then unmodeled
      else if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then err_ret EINVAL
      else if negb (0 <? bv_unsigned addr)%Z then unmodeled
      else
      let n := Z_to_bv 64 nZ in
      if region_free (vm_reserved h) addr n
         && map_contains (vm_maps h) addr n
      then
      (* THE SAME THREE RESOLUTIONS, for the same reason: the destructive
         boundary is [vms_clean_up_area] (mm/vma.c:1281-1293, called from
         [__mmap_prepare] at :2441, Linux v6.18.46), everything
         that can fail before it leaves the range intact, everything
         after it leaves a hole.  Asking for rw rather than PROT_NONE
         moves one failure across that boundary in the SAFE direction and
         adds none:

         - [accountable_mapping] is now TRUE (VM_WRITE, private, and —
           for the plain spelling — no VM_NORESERVE, mm/vma.c:2326-2336),
           so [__mmap_prepare] takes the commit charge this time.  It
           charges the DELTA, [charged = pglen; charged -=
           vms.nr_accounted], and calls [security_vm_enough_memory_mm]
           only when that is nonzero — which is why
           [mmap_fixed_rw_budget_ok] tests the whole post-state rather
           than adding [pglen]: over a range already accounted the delta,
           and the charge, are zero.  It is
           at mm/vma.c:2422-2432, which is BEFORE :2441, so its -ENOMEM
           reaches [abort_munmap:] with [vms->clear_ptes] still set and
           [vms_abort_munmap_vmas] (mm/vma.c:2357-2358) takes
           [reattach_vmas] (:1351-1360): the range is put
           back.  A NON-destructive errno, already among the three.
         - [may_expand_vm] (:2418-2419) still gets the delta
           [pglen - vms.nr_pages], which is 0 for a range already wholly
           mapped, and [vms_gather_munmap_vmas]'s [max_map_count]
           (mm/vma.c:1389-1393) still fires only for the interior
           two-split case, before any [__split_vma].  Both
           non-destructive, both unchanged.
         - [vm_area_alloc] and [vma_iter_prealloc] ([__mmap_new_vma],
           mm/vma.c:2506-2508 and :2515-2518) are still the two past
           :2441, and still the destructive pair.

         The SUCCESS is where the two shapes part.  Linux tears the old
         range down and installs fresh anonymous rw pages, so the process
         reads ZEROES back from every byte of it — including bytes it had
         written a moment earlier through a live rw mapping, and
         including bytes that were unreadable under PROT_NONE.  That is
         [eff_zeros], the same effect [mprotect_spec] emits when it
         exposes a protected range, and it subsumes an unmap:
         [Run.apply_effect] materializes the whole range as defined
         zeroes, so nothing stale can survive it and no separate
         [eff_unmaps] is needed.

         Both bounds the zero-fill needs are already discharged by the
         gate above — [addr + n <= alloc_top h] and [region_free]
         against [vm_reserved] — so this branch's exposed bytes are
         disjoint from the image and from the stack of the stack pointer
         this run was started with, like every other grant in this
         file. *)
      alt
        (e <- errno_from mmap_errnos ;; err_ret e)
        (alt
          (_ <- choose (fun _ : unit =>
                 mmap_fixed_rw_budget_ok flags m addr n = true) ;;
           modify (fun _ => with_mmap_replacement flags addr n
             (with_vmmaps (mmap_fixed_rw_next h addr n) m)) ;;
           pure (mkEffect addr [] [(addr, n)]))
          (e <- errno_from mmap_errnos ;;
           modify (fun _ => with_mmap_destroyed addr n
             (mmap_fixed_destroyed_next h addr n) m) ;;
           pure (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])))
      (* THE OTHER HALF OF MAP_FIXED, and the one that adds the least.  A
         MAP_FIXED whose range meets NO live mapping is not a commit
         inside something the process owns — it is an ordinary anonymous
         grant that names its own address instead of letting the kernel
         pick one.  Linux treats it as exactly that: with [vms.nr_pages]
         zero there is nothing to tear down, [vms_abort_munmap_vmas]
         returns at its first line (mm/vma.h:244-245), and the
         destructive resolution above cannot arise — which is why this
         sub-case has TWO resolutions where the commit has three.

         IT ADDS NO REACHABLE TRANSITION.  The guards below are the
         [choose] guard of the hint-placed rw branch, conjunct for
         conjunct — page alignment, nonzero base, [alloc_top],
         [region_free] against [vm_reserved ++ vm_maps], and the budget
         — and the post-state and effect are that branch's, spelled
         the same way with [addr] where it writes the chosen [a].  So
         every (pre-state, effect, post-state) triple this admits is one
         the model already admitted for the SAME program at the same
         length, hinting its own (nonzero) [addr] without MAP_FIXED: the
         kernel honors a free hint, and the model's nondeterministic
         placement covers it.  [Checks/Cases/Mm/Mmap.v]'s
         [mmap_fixed_fresh_adds_no_transition] states exactly that and
         proves it.

         The four-way split is on the LEDGER, not on the flags: wholly
         inside one tracked mapping is a commit, meeting nothing at all
         is a grant, meeting live mappings without being inside one is
         the SPANNING replacement below, and a range that reaches the
         image's LOAD reservations is the one shape that still declines.

         [0 < addr] is NOT re-derived here.  Linux answers -EPERM at
         address 0 whether or not anything is mapped there — the check is
         [security_mmap_addr] on the returned address, above the ledger
         entirely — so the gate that declines it belongs above the
         containment test, not inside one sub-case of it, and that is
         where it sits. *)
      else if region_free (vm_reserved h ++ vm_maps h) addr n
      then
      (* THE BUDGET SITS INSIDE THE RESOLUTION, NOT IN THE GUARD ABOVE,
         and the difference is behavior.  A grant the budget cannot take
         is a real -ENOMEM on Linux, and it is the forced out-of-memory
         point; testing it in the branch-selection guard
         would answer [unmodeled] instead, losing that forcing for this
         shape alone.  Spelling it as a [choose] pinned to [addr] is what
         makes the collapse happen the same way it does for the
         hint-placed branch: over budget the guard is unsatisfiable, the
         [alt] has only its errno arm left, and the model MUST fail. *)
      alt
        (e <- errno_from mmap_errnos ;; err_ret e)
        (a <- choose (fun a => a = addr
                               /\ mmap_noreserve_backed_ok flags m nZ = true) ;;
         modify (fun _ => with_mmap_backing flags a n
           (with_vmmaps (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
             (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h)
                (vm_mmap_base h) (vm_init_sp h)) m)) ;;
         pure (mkEffect a [] [(a, n)]))
      (* THE SPANNING SUB-CASE, the rw half.  Its PROT_NONE twin above
         carries the argument for the three resolutions, for what the
         non-destructive half admits that the contained arm's does
         not, and for the two Linux answers this arm does not carry.
         Three things differ here, all of them the same differences the
         contained pair already has:

         - the SUCCESS exposes bytes, so it emits [eff_zeros] over the
           whole request rather than an unmap.  Every byte of it reads
           back as zero on Linux — the pages are fresh anonymous pages,
           including the bytes the process wrote a moment ago through a
           mapping this call replaced;
         - it is therefore gated on the budget, through
           [mmap_fixed_rw_span_budget_ok], which is where the newly
           OWNED part of the request gets charged;
         - the budget sits inside the resolution rather than in the
           branch guard, for the reason the free-range arm above gives:
           over budget the [choose] is unsatisfiable, the [alt] collapses
           onto its errno arm, and the model MUST fail rather than
           answering [unmodeled]. *)
      else if region_free (vm_reserved h) addr n
      then
      alt
        (e <- errno_from mmap_errnos ;; err_ret e)
        (alt
          (_ <- choose (fun _ : unit =>
                 mmap_fixed_rw_span_budget_ok flags m addr n = true) ;;
           modify (fun _ => with_mmap_replacement flags addr n
             (with_vmmaps (mmap_fixed_rw_span_next h addr n) m)) ;;
           pure (mkEffect addr [] [(addr, n)]))
          (e <- errno_from mmap_errnos ;;
           modify (fun _ => with_mmap_destroyed addr n
             (mmap_fixed_destroyed_next h addr n) m) ;;
           pure (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])))
      else unmodeled
  else if mmap_noreplace_noaccess_b prot flags off then
    (* THE MAP_FIXED ARGUMENT GATE, VERBATIM: from mm/mmap.c:362 on the
       request carries MAP_FIXED, so the four tests above are the tests
       it meets, in that order, and they precede the -EEXIST of :410-412
       (the MAP_FIXED_NOREPLACE section above).  Then ONE split on the
       ledger, not four: a range that meets nothing in [vm_reserved ++
       vm_maps] is the free-range MAP_FIXED sub-case, resolution for
       resolution; a range that meets anything — a live mapping, a brk
       grant, or the image's LOAD reservations — is -EEXIST with nothing
       changed, beside the environment -ENOMEM every arm admits. *)
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (two_pow_64 <=? bv_unsigned addr + nZ)%Z then err_ret ENOMEM
    else
      m <- get_model ;;
      let h := m_vmmaps m in
      if negb (bv_unsigned addr + nZ <=? alloc_top h)%Z then unmodeled
      else if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then err_ret EINVAL
      else if negb (0 <? bv_unsigned addr)%Z then unmodeled
      else
      let n := Z_to_bv 64 nZ in
      if region_free (vm_reserved h ++ vm_maps h) addr n
      then
      alt
        (e <- errno_from mmap_errnos ;; err_ret e)
        (a <- choose (fun a => a = addr) ;;
         modify (fun _ => with_mmap_backing flags a n
           (with_vmmaps (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
             ((a, n) :: vm_noaccess h) (vm_start_brk h)
             (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)) ;;
         pure (mkEffectU a [] [] [(a, n)] [] []))
      else
      alt
        (e <- errno_from mmap_errnos ;; err_ret e)
        (err_ret EEXIST)
  else if mmap_noreplace_rw_b prot flags off then
    (* The rw spelling: the same gate, the same split, and the free-range
       sub-case of the rw MAP_FIXED arm — with its budget inside the
       resolution, so that over budget the [alt] collapses onto -ENOMEM
       rather than declining (the argument is on that arm). *)
    let nZ := page_round_up_Z (bv_unsigned len) in
    if (two_pow_64 <=? bv_unsigned addr + nZ)%Z then err_ret ENOMEM
    else
      m <- get_model ;;
      let h := m_vmmaps m in
      if negb (bv_unsigned addr + nZ <=? alloc_top h)%Z then unmodeled
      else if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then err_ret EINVAL
      else if negb (0 <? bv_unsigned addr)%Z then unmodeled
      else
      let n := Z_to_bv 64 nZ in
      if region_free (vm_reserved h ++ vm_maps h) addr n
      then
      alt
        (e <- errno_from mmap_errnos ;; err_ret e)
        (a <- choose (fun a => a = addr
                               /\ mmap_noreserve_backed_ok flags m nZ = true) ;;
         modify (fun _ => with_mmap_backing flags a n
           (with_vmmaps (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
             (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h)
                (vm_mmap_base h) (vm_init_sp h)) m)) ;;
         pure (mkEffect a [] [(a, n)]))
      else
      alt
        (e <- errno_from mmap_errnos ;; err_ret e)
        (err_ret EEXIST)
  else unmodeled.

(* =========================================================================
   THE BUDGET MARK for mmap (see the brk mark above for what a mark is)
   ========================================================================= *)

(** The shape gates are [mmap_spec]'s, in [mmap_spec]'s order, and each
    charging branch's budget gate is the function that branch's
    [choose] carries — [mmap_noreserve_backed_ok] for a hint-placed
    grant, for the free-range MAP_FIXED grant and for the
    MAP_FIXED_NOREPLACE rw grant (a MAP_NORESERVE request is free at
    grant time and so never budget-refused), [mmap_fixed_rw_budget_ok]
    for the contained rw replacement, [mmap_fixed_rw_span_budget_ok]
    for the spanning one.  The branches that consume no backing
    (PROT_NONE, MAP_FIXED PROT_NONE, MAP_FIXED_NOREPLACE PROT_NONE)
    never fire, and neither does anything an argument gate answers: the
    -EINVALs, the overflowing length's -ENOMEM, the NOREPLACE -EEXIST,
    and the unmodeled shapes.  All three budget gates read the request
    and the pre-state and not the placement, so the mark is exact for
    this arm: it is [true] iff no success resolution exists for want of
    budget.  Pinned in [Checks/BudgetPremise.v].  That pin does not see
    a NEW charging branch on a gate the mark already names (the mark
    falls to [false] there). *)
Definition mmap_budget_refused_b (addr len prot flags fd off : word)
    (m : Model) : bool :=
  if negb (mmap_off_aligned_b off) then false
  else if negb (mmap_anon_b flags) then false
  else if w_is0 len then false
  else
    let h := m_vmmaps m in
    let nZ := page_round_up_Z (bv_unsigned len) in
    let n := Z_to_bv 64 nZ in
    if mmap_modeled_b prot flags off then
      negb (mmap_noreserve_backed_ok flags m nZ)
    else if mmap_noaccess_b prot flags off then false
    else if mmap_fixed_noaccess_b prot flags off then false
    else if mmap_fixed_rw_b prot flags off then
      if (two_pow_64 <=? bv_unsigned addr + nZ)%Z then false
      else if negb (bv_unsigned addr + nZ <=? alloc_top h)%Z then false
      else if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then false
      else if negb (0 <? bv_unsigned addr)%Z then false
      else if region_free (vm_reserved h) addr n
              && map_contains (vm_maps h) addr n
      then negb (mmap_fixed_rw_budget_ok flags m addr n)
      else if region_free (vm_reserved h ++ vm_maps h) addr n
      then negb (mmap_noreserve_backed_ok flags m nZ)
      else if region_free (vm_reserved h) addr n
      then negb (mmap_fixed_rw_span_budget_ok flags m addr n)
      else false
    else if mmap_noreplace_noaccess_b prot flags off then false
    else if mmap_noreplace_rw_b prot flags off then
      if (two_pow_64 <=? bv_unsigned addr + nZ)%Z then false
      else if negb (bv_unsigned addr + nZ <=? alloc_top h)%Z then false
      else if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then false
      else if negb (0 <? bv_unsigned addr)%Z then false
      else if region_free (vm_reserved h ++ vm_maps h) addr n
      then negb (mmap_noreserve_backed_ok flags m nZ)
      else false
    else false.

(** [munmap addr len].  Linux checks the arguments first, all -EINVAL
    and deterministic (mm/vma.c [do_vmi_munmap], v6.18.46):

      if ((offset_in_page(start)) || start > TASK_SIZE || len > TASK_SIZE-start)
              return -EINVAL;
      end = start + PAGE_ALIGN(len);
      if (end == start)
              return -EINVAL;

    So an unaligned [addr], a [len] of 0, and a range leaving the user
    address space are each -EINVAL before any mapping is looked at.  For
    a page-aligned [start] and a nonzero [len], the disjunction
    [start > TASK_SIZE || len > TASK_SIZE - start] is exactly
    [start + PAGE_ALIGN(len) > TASK_SIZE] (the first disjunct covers the
    [start] for which the unsigned subtraction would wrap), since
    [TASK_SIZE - start] is a multiple of the page size and [PAGE_ALIGN]
    is the least multiple at or above [len]; that is the [nZ] test below,
    in [Z], with [State.TASK_SIZE] the Sv48 top.  The [end == start]
    guard's only reachable case is [len = 0], which the first test has
    already answered, and no nonzero range under [TASK_SIZE] can wrap, so
    nothing here ever hands a wrapped end to the word-level map
    operations.

    Then, with [n] = the page-rounded [len]:

    - [addr, addr+n) EXACTLY a recorded mapping (an anonymous mmap
      grant or a recorded brk grow): the mapping is dropped from the
      ledger and the range is UNMAPPED in the machine ([eff_unmaps]) —
      a later access faults instead of reading stale bytes, as on
      Linux.  (Unmapping a brk-grow record this way is faithful too:
      Linux unmaps the pages, the break pointer is unchanged, and a
      later grow continues above the old break — the hole stays a
      hole.)
    - [addr, addr+n) disjoint from the image and every recorded
      mapping, and ending at or below this run's [State.alloc_top]: 0, a no-op
      — Linux does not fail when the range contains no mapped pages.
      Below that line the only mappings the ledger does not carry are
      the ones the KERNEL installs without being asked — the vdso/vvar
      pair, which ends at [mm->mmap_base] and so sits BELOW this line on
      essentially every exec ([mmap_base] pads its gap by the largest
      stack randomisation, mm/util.c at v6.18.46, so it is at least
      1 MiB under [sp - 8 MiB] unless the argv/envp block is larger than
      that) — and a free-range unmap that lands on those is answered 0
      here where Linux unmaps them (or, with
      [CONFIG_MSEAL_SYSTEM_MAPPINGS], refuses with -EPERM); that is a
      premise of the model.
    - anything else — a PARTIAL/interior/spanning unmap (Linux would
      split the mapping), a range touching the binary image
      ([vm_reserved] can never be unreserved), or a free range reaching
      into the STACK BAND [[alloc_top h, TASK_SIZE)] — is unmodeled and
      yields [unmodeled] (fail closed).  The band is the one region the
      ledger does not describe: [Run.init_machine_state] zero-maps the
      stack below the entry [sp] and records it in no [VmMaps] list, so a
      range that is free by the ledger may be the stack, which Linux
      would split and unmap where a no-op 0 would leave it mapped.
      [alloc_top h] is [vm_init_sp h - stack_max_size], the lowest
      address this run's stack can occupy, which is why it is the bound
      here.

    With the kernel and boot fixed ([State.TASK_SIZE]), the
    address-space test is Linux's own -EINVAL. *)

(** The free-range no-op arm's guard: nothing recorded in the range,
    and the range below the stack band (see [munmap_spec]). *)
Definition munmap_free_ok (h : VmMaps) (addr : word) (nZ : Z) : bool :=
  (region_free (vm_reserved h ++ vm_maps h) addr (Z_to_bv 64 nZ)
   && (bv_unsigned addr + nZ <=? alloc_top h)%Z)%bool.

Definition munmap_spec (addr len : word) : Sys SyscallEffect :=
  if negb (Z.eqb (bv_unsigned addr mod page_size) 0) || w_is0 len then err_ret EINVAL
  else
    h <- get_vmmaps ;;
    let nZ := page_round_up_Z (bv_unsigned len) in
    (* [start > TASK_SIZE || len > TASK_SIZE-start], as one [Z] test on
       the rounded end (see the header).  It is also what keeps [n] a
       faithful [word] rendering of the rounded length in the [(addr, n)]
       unmap effect and in the range handed to [maps_subtract] below:
       every range that passes has [addr + nZ <= 2^47], so the word
       never wraps.  Errno choice is behavior — this is -EINVAL and not
       [Mprotect.mprotect_spec]'s -ENOMEM, although the two gates have
       the same shape. *)
    if (TASK_SIZE <? bv_unsigned addr + nZ)%Z then err_ret EINVAL
    else
    let n := Z_to_bv 64 nZ in
    if map_has (vm_maps h) addr n then
      set_vmmaps (mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) addr)
                    (maps_subtract (vm_noaccess h)
                       (bv_unsigned addr)
                       (bv_unsigned addr + bv_unsigned n))
                    (vm_start_brk h) (vm_brk h) (vm_limit h)
                    (vm_mmap_base h) (vm_init_sp h)) ;;
      forget_vm_range (bv_unsigned addr)
                      (bv_unsigned addr + bv_unsigned n) ;;
      pure (mkEffectU (Z_to_bv 64 0) [] [] [(addr, n)] [] [])
    else if munmap_free_ok h addr nZ
    then ret_only (Z_to_bv 64 0)
    else unmodeled.
