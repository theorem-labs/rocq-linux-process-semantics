(** * LinuxProcessSem.Sys.Mm.Madvise — madvise (233)

    This file answers to Linux [mm/madvise.c]: it holds what the kernel
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

(** [madvise addr len advice].  ONE advice value is answered, MADV_DONTNEED,
    over a range the ledger describes completely; every other advice value
    declines.  What the arm exists for is the backed-memory budget: a
    MAP_NORESERVE page is charged to [State.vm_limit] on its first touch
    ([State.materialize_model_accesses]), and without this arm only an
    unmap of the whole mapping would give that charge back.  A runtime
    that returns its shadow pages with MADV_DONTNEED when large chunks are
    freed keeps the mapping and reuses the same pages, so under heavy
    alloc/free traffic it stays inside its memory on Linux, while without
    this arm the model would spend its budget on every page ever touched.

    THE KERNEL'S ORDER, which the spec follows because the order is
    behavior.  [do_madvise] (mm/madvise.c, Linux v6.18.46) opens with
    [madvise_should_skip], which is [is_valid_madvise] and then the
    zero-length exit:

      static bool is_valid_madvise(unsigned long start, size_t len_in,
                                   int behavior)
      {
              if (!madvise_behavior_valid(behavior)) return false;
              if (!PAGE_ALIGNED(start)) return false;
              len = PAGE_ALIGN(len_in);
              if (len_in && !len) return false;
              if (start + len < start) return false;
              return true;
      }
      ...
              if (!is_valid_madvise(start, len_in, behavior)) {
                      *err = -EINVAL; return true; }
              if (start + PAGE_ALIGN(len_in) == start) {
                      *err = 0; return true; }

    Every refusal in [is_valid_madvise] is -EINVAL, so the order AMONG
    them is unobservable, and the arm tests alignment first: a misaligned
    [addr] is -EINVAL for every advice value, known or not, before the
    advice is read — [madvise_behavior_valid] is a pure switch on the
    value, and a value it rejects is -EINVAL just the same.  What IS
    observable is that all four precede the zero-length exit: [len = 0]
    answers 0 only for a valid advice value at an aligned address, which
    is why the [w_is0 len] branch below sits behind both gates.  The
    advice gate declines rather than answering -EINVAL for an unknown
    value because [madvise_behavior_valid]'s list depends on the kernel
    configuration (MADV_MERGEABLE needs CONFIG_KSM, MADV_HUGEPAGE
    CONFIG_TRANSPARENT_HUGEPAGE, MADV_HWPOISON CONFIG_MEMORY_FAILURE), so
    which values are "unknown" is not a fact about the source alone.

    The last two refusals are one test in [Z]: [PAGE_ALIGN(len_in)] wraps
    to 0 exactly when [page_round_up_Z len = 2^64], and [start + len]
    wraps exactly when [addr + nZ >= 2^64] for an [nZ] below it; both are
    [two_pow_64 <= addr + nZ].  That test is [Mprotect.mprotect_spec]'s
    fourth gate with -EINVAL in place of -ENOMEM — errno choice is
    behavior, and [do_mprotect_pkey] and [is_valid_madvise] pick
    different ones for the same shape.  QEMU's user-mode emulation agrees
    on both refusals ([target_madvise], linux-user/mmap.c, 8.2.2: a
    misaligned start and a [TARGET_PAGE_ALIGN] that wraps to zero or a
    range [guest_range_valid_untagged] refuses are each -EINVAL, and a
    zero [len_in] is 0), so the two argument errnos and the zero-length
    success are inside the intersection the design priorities (README.md) require.

    THE ANSWERED SHAPE.  Past the gates the kernel walks the VMAs the
    range meets ([madvise_walk_vmas]), applying [madvise_vma_behavior] to
    each; for MADV_DONTNEED that is [madvise_dontneed_free] and, unless
    the VMA is VM_LOCKED, VM_PFNMAP or hugetlb (-EINVAL,
    [madvise_dontneed_free_valid_vma]), [madvise_dontneed_single_vma],
    which zaps the page range and returns 0.  A zapped anonymous private
    page reads back as zeros and is faulted in fresh on the next touch.
    None of the three refusing VMA kinds can arise on a modeled run:
    mlock (228) and mlockall (230) are outside the modeled surface, so no
    VMA is VM_LOCKED; the model maps no device memory, so none is
    VM_PFNMAP; and [Mmap.mmap_spec] declines MAP_HUGETLB.  Nor can the
    -EPERM of [can_madvise_modify] (a sealed VMA) — mseal (462) is
    unmodeled, as [Mprotect.mprotect_errnos] already argues for its
    twin — nor the userfaultfd retry, since no modeled call arms one.

    So over a range that lies inside ONE live anonymous mapping of the
    ledger, every page of it read-write, the answer is forced: 0, the
    range reads back as zeros, and no event.  That is the
    [madvise_dontneed_ok] gate below, one conjunct per way the ledger's
    picture could fall short of the kernel's:

    - [map_contains (vm_maps h)]: inside one recorded anonymous mapping
      — an mmap grant, a MAP_FIXED commit, or a recorded brk grow (the
      heap is an anonymous private VMA to Linux, and zapping its pages
      is what a brk shrink-and-regrow already models: fresh zeros).  The
      model never merges adjacent entries, so a range one kernel VMA
      covers can lie across two entries here and decline — the safe
      direction, as [State.map_contains] says.  A range with a page the
      ledger does not own declines rather than answering the -ENOMEM
      [madvise_walk_vmas] reports, and the reason is the SHAPE of that
      answer: the walk applies the advice to every mapped part it meets
      and only then returns [unmapped_error], so a hole means a state
      change AND an errno at once, and the ledger — which carries neither
      the stack nor the kernel's own vdso/vvar pair — cannot say which
      parts Linux zapped.
    - [region_free (vm_reserved h)]: never the image's LOAD pages.  The
      file-backed private ones read back FILE CONTENTS after a zap, not
      zeros, and the model cannot state them; the anonymous BSS ones are
      not in the ledger's replaceable representation either
      ([Mmap.mmap_spec]'s MAP_FIXED arms give the same reason).  No
      reachable state has an image page in [vm_maps], so the conjunct is
      documentary there and load-bearing only for a hand-built ledger;
      [Checks/Cases/Mm/Madvise.v] pins it on one.
    - [region_free (vm_noaccess h)]: every page read-write.  Linux zaps a
      PROT_NONE anonymous page just the same and answers 0, but the
      machine overlay holds no bytes for a protected page, and the
      zero-fill that re-exposes one belongs to [Mprotect.mprotect_spec];
      declaring [eff_zeros] over a range the process cannot read would
      claim bytes the machine cannot serve.  A decline, not a wrong
      answer, and one no modeled runtime reaches.

    THE EFFECT is [eff_zeros] over the whole page-rounded range, as the
    rw MAP_FIXED replacement and the mprotect exposure emit: every byte
    of it reads back as zero on Linux, including bytes written a moment
    ago.  [Run.apply_effect] materializes it in the overlay, and
    [State.syscall_effect_accesses] deliberately omits zero ranges, so
    the zero-fill charges nothing — the pages are lazy again, not touched.

    THE LEDGER.  [madvise_dontneed_next] drops every materialized page in
    the range and changes nothing else: the mapping stays in [vm_maps]
    with its size, its lazy provenance stays in [m_vm_lazy], and the
    budget falls by exactly the charges those pages took, so the next
    access re-charges them through [State.materialize_model_accesses]
    as a first touch does.  An EAGERLY charged mapping keeps its charge:
    Linux keeps the commit charge of a VM_ACCOUNT VMA across a zap too
    ([madvise_dontneed_single_vma] touches no accounting), and the
    model's eager charge is that commit-time guarantee, not the pages'
    residency.  Only [m_vm_materialized] shrinks; [m_vm_lazy] is passed
    through unchanged, so the page-alignment invariant
    [State.vm_backing_used] rests on is untouched — this is a reader of
    the lazy ledger, not a third writer.

    Nothing here is nondeterministic and no errno is injectable: the
    only failures [do_madvise] can report on the answered shape are the
    -EINTR of a killable write lock, which DONTNEED does not take
    ([get_lock_mode] gives it MADVISE_VMA_READ_LOCK), and the walk's
    -ENOMEM, which the containment gate excludes.  A forged nonzero
    return, a forged 0 on a misaligned address, and a 0 without the
    zero-fill are each rejected; [Checks/Cases/Mm/Madvise.v] pins all
    three. *)

(** Is the advice MADV_DONTNEED?  [advice] arrives narrowed by
    [Syscall.int32]: the kernel declares it [int]
    ([SYSCALL_DEFINE3(madvise, unsigned long, start, size_t, len_in,
    int, behavior)], mm/madvise.c, Linux v6.18.46), so the register's
    high half is discarded before the switch reads it. *)
Definition madvise_dontneed_b (advice : word) : bool :=
  Z.eqb (bv_unsigned advice) MADV_DONTNEED.

(** The answered shape's ledger gate (see the header): inside one live
    anonymous mapping, clear of the image, every page read-write. *)
Definition madvise_dontneed_ok (h : VmMaps) (addr n : word) : bool :=
  region_free (vm_reserved h) addr n
  && map_contains (vm_maps h) addr n
  && region_free (vm_noaccess h) addr n.

(** THE THIRD CONJUNCT DECLINES ONLY OVER A REAL PROTECTED BYTE.

    [region_free] folds [State.iv_overlap], which reports an overlap
    against a ZERO-SIZE interval strictly inside the queried range:
    [iv_overlap addr n a 0] is [addr < a && a < addr + n], true for any
    [a] strictly between.  So an entry of [vm_noaccess] naming no byte
    would close this gate over a range the process can read and write
    throughout, and the call would decline where the header says it
    answers.  Fail closed rather than wrong, which is why no example or
    test would catch it.

    No writer can make one. [State.vm_noaccess_entries_nonzero] is the
    property, [State.init_model_noaccess_nonzero] its base case, and
    every writer of the list carries a preservation lemma —
    [Mm/Mmap.v]'s section "the protected ledger names real bytes" lists
    the writers by name and holds the lemmas, [Mm/Mprotect.v] the one
    writer outside that file.  One thing that section says and this
    must not overstate: the lemmas for the arms that write their
    post-state inline RESTATE the record rather than naming it, so a
    re-shaped arm would not break them.  The composition into "every
    reachable model satisfies it" is [Checks/NoaccessOwned.v]'s
    ([init_model_sys_inv], [star_preserves_sys_inv],
    [sys_inv_noaccess_pages_owned], then
    [State.noaccess_pages_owned_nonzero]), which this file cannot
    import, so the lemma below takes the property as a HYPOTHESIS; a
    caller discharges it from those lemmas, or from the writer that
    produced the state, as the worked example in
    [Checks/Cases/Mm/Madvise.v] does.

    Under it, a decline attributed to [vm_noaccess] exhibits an address
    the request covers and the process cannot touch — which is exactly
    the situation the conjunct is here to keep the model out of.

    THE SIDE CONDITION on [n] is supplied by [madvise_spec] at the call
    site: it passes [n = Z_to_bv 64 (page_round_up_Z (bv_unsigned len))]
    past a [w_is0 len] gate and the [two_pow_64] bound on the rounded
    end, which is [Mmap.mmap_request_len_nonzero]'s exact shape. It is
    load-bearing rather than tidy: with [n = 0] the request covers no
    address at all, while [region_free] can still answer false. *)
Lemma madvise_noaccess_decline_names_a_protected_byte :
  forall h addr n,
    vm_noaccess_entries_nonzero h ->
    (0 < bv_unsigned n)%Z ->
    region_free (vm_noaccess h) addr n = false ->
    exists a sz x,
      In (a, sz) (vm_noaccess h)
      /\ (0 < bv_unsigned sz)%Z
      /\ (bv_unsigned a <= x < bv_unsigned a + bv_unsigned sz)%Z
      /\ (bv_unsigned addr <= x < bv_unsigned addr + bv_unsigned n)%Z.
Proof.
  intros h addr n Hnz Hn Hfree.
  destruct (region_free_false _ _ _ Hfree) as [a [sz [Hin Hov]]].
  pose proof (Hnz a sz Hin) as Hsz.
  unfold iv_overlap in Hov.
  apply andb_true_iff in Hov as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
  exists a, sz, (Z.max (bv_unsigned a) (bv_unsigned addr)).
  pose proof (Z.max_spec (bv_unsigned a) (bv_unsigned addr)).
  split; [exact Hin | split; [exact Hsz | lia]].
Qed.

(** The post-state: the range's first-touch charges are given back and
    nothing else moves.  The bounds are taken in [Z], as every ledger
    range is; the gate above has already bounded [addr + n] below 2^64. *)
Definition madvise_dontneed_next (m : Model) (addr n : word) : Model :=
  with_vm_backing (m_vm_lazy m)
    (List.filter
       (page_outside_range (bv_unsigned addr)
                           (bv_unsigned addr + bv_unsigned n))
       (m_vm_materialized m)) m.

Definition madvise_spec (addr len advice : word) : Sys SyscallEffect :=
  if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then err_ret EINVAL
  else if negb (madvise_dontneed_b advice) then unmodeled
  else if w_is0 len then ret_only (Z_to_bv 64 0)
  else if (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z
  then err_ret EINVAL
  else
    m <- get_model ;;
    let h := m_vmmaps m in
    let nZ := page_round_up_Z (bv_unsigned len) in
    let n := Z_to_bv 64 nZ in
    if madvise_dontneed_ok h addr n then
      modify (fun _ => madvise_dontneed_next m addr n) ;;
      pure (mkEffect (Z_to_bv 64 0) [] [(addr, n)])
    else unmodeled.
