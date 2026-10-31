(** * LinuxProcessSem.Checks.Cases.Mm.PlacementHoles — the placement rule, checked

    NOT part of the trusted specification: worked cases.

    Two things are pinned here, both by computation on the checker.

    THE ADDRESS IS LINUX'S.  [Sys/Mm/Mmap.linux_place] says where a
    fresh anonymous mapping goes, and [Checks/Placement.linux_place_b]
    computes it.  The cases below are the five the OSSV-231 plan's
    "Review Focus" names: a hint of 1 to 4095, a hint that is not page
    aligned, the hint 2^64-1, a transparent-huge-page kernel, and the
    same kernel without it.  Each one is a place where a reader's
    first guess is wrong, so each is written with the kernel's own
    reason beside it.

    THE vdso/vvar PAIR IS IN THE LEDGER, and the four calls that can
    meet it are answered.  [execve] maps the pair below the mmap base
    ([State.init_model], through [State.vdso_reserved]); before this
    change the model did not carry it, and SCOPE.md carried a premise
    that no call ever touched it instead.

    Every Linux claim is at v6.18.46, commit 1f99e9ab748f, and every
    file and line cited is readable at /home/sami/src/linux-6.18.46 at
    that commit. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs Placement Cases.Prelude.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   The fixture: a launch with a real layout
   ========================================================================= *)

(** A model [execve] can really hand a process: the mmap base at the
    bottom of the band [Run.valid_mmap_base] admits, the stack pointer
    at the bottom of its window, an empty image, and the default kernel
    build (no transparent huge pages, vDSO image 1, which is two text
    pages).  [place_thp] is the same launch on a kernel built WITH
    transparent huge pages, and the only field that differs is
    [kb_thp]: the point of several cases below is that the two give
    different addresses for the same call. *)
Definition place_model : Model :=
  init_model [] (Z_to_bv 64 0x11000) (Z_to_bv 64 mmap_base_min)
    (Z_to_bv 64 sp_window_lo) target_alloc_limit (demo_input [] IEof).

(** The SAME launch with transparent huge pages, and the only field
    that differs is [kb_thp]: written as a projection-wise copy of
    [default_kernel] so that a field added to [State.KernelBuild]
    changes this fixture in one place and not in its meaning. *)
Definition place_thp : Model :=
  with_kernel (mkKernelBuild true (kb_vdso default_kernel)
                 (kb_aslr default_kernel) (kb_guard default_kernel)
                 (kb_rnd_bits default_kernel) (kb_rseq default_kernel)
                 (kb_vlenb default_kernel) (kb_cache default_kernel))
    place_model.

(** The three addresses every case below is written against, as the
    model computes them.  [mmap_top] is the mmap base rather than
    [alloc_top], because this launch's base is far below its stack:
    the search is bounded by the base, as Linux's is
    (mm/mmap.c:766, [info.high_limit = arch_get_mmap_base(addr,
    mm->mmap_base)]). *)
Example place_mmap_top : mmap_top (m_vmmaps place_model) = 23387528589312%Z.
Proof. vm_compute. reflexivity. Qed.

Example place_alloc_top : alloc_top (m_vmmaps place_model) = 140735332483072%Z.
Proof. vm_compute. reflexivity. Qed.

(** THE PAIR IS THERE, and it is the top of the search window: the vvar
    part of four pages at [mmap_top - 24576], then the two text pages
    directly above it, ending exactly at [mmap_top].
    [__setup_additional_pages] (arch/riscv/kernel/vdso.c:110) asks
    [get_unmapped_area] for the two parts in one span (:120-124) with a
    NULL hint, and at that point in [load_elf_binary] nothing is mapped
    below [mm->mmap_base]; it then installs vvar at the result and the
    text above it (:130-138). *)
Example place_vdso_pair_is_reserved :
  vm_reserved (m_vmmaps place_model)
  = [ (Z_to_bv 64 23387528564736, Z_to_bv 64 16384);
      (Z_to_bv 64 23387528581120, Z_to_bv 64 8192) ].
Proof. vm_compute. reflexivity. Qed.

Example place_vdso_pair_ends_at_the_search_top :
  (23387528564736 + 24576)%Z = mmap_top (m_vmmaps place_model).
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   Where the search puts a mapping
   ========================================================================= *)

(** THE FIRST GRANT OF THE RUN lands ONE PAGE UNDER THE PAIR, not at
    the top of the address space and not at a low address.  This is the
    highest page that fits below [mmap_top] once the pair is counted
    (mm/vma.c, [unmapped_area_topdown], which returns the end of the
    highest large enough gap minus the length).

    Before this change the model admitted any free page-aligned address
    below [alloc_top], which is what let it refuse a mapping the same
    Linux launch grants — the holes of OSSV-210. *)
Example place_first_grant_is_under_the_vdso :
  linux_place_b (m_vmmaps place_model) false (Z_to_bv 64 0) 4096
  = Some 23387528560640%Z.
Proof. vm_compute. reflexivity. Qed.

Example place_first_grant_is_one_page_under_the_pair :
  (23387528560640 + 4096)%Z = 23387528564736%Z.
Proof. reflexivity. Qed.

(** AND AN ADDRESS LINUX WOULD NOT CHOOSE IS NOT REACHABLE.  0x10000 is
    page aligned, positive, below [alloc_top] and free: it met every
    condition the old guard asked for.  The search does not stop there,
    so the checker refuses the grant. *)
Example place_low_address_rejected :
  check_syscall
    (mkInput 222 [0; 4096; 3; 34; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] [(65536, 4096)]) place_model
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** One page either side of Linux's answer is refused too, so the
    acceptance above is an equality and not a band. *)
Example place_one_page_high_rejected :
  check_syscall
    (mkInput 222 [0; 4096; 3; 34; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (Z_to_bv 64 23387528564736) [] [(Z_to_bv 64 23387528564736, 4096)])
    place_model
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

Example place_one_page_low_rejected :
  check_syscall
    (mkInput 222 [0; 4096; 3; 34; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (Z_to_bv 64 23387528556544) [] [(Z_to_bv 64 23387528556544, 4096)])
    place_model
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** …and Linux's own address IS admitted, which is the other half of
    the pair: a test that only shows the refusal does not show the
    checker still works. *)
Example place_linux_address_accepted :
  exists m' evs,
    check_syscall
      (mkInput 222 [0; 4096; 3; 34; mmap_fd_none; 0]
        (fun _ => None) (fun _ => None))
      (mkEffect (Z_to_bv 64 23387528560640) [] [(Z_to_bv 64 23387528560640, 4096)])
      place_model
    = CheckOk m' evs.
Proof. vm_compute. eexists; eexists; reflexivity. Qed.

(* =========================================================================
   Review Focus: the five cases where the first guess is wrong
   ========================================================================= *)

(** (1) A TRANSPARENT-HUGE-PAGE KERNEL PLACES THE SAME REQUEST LOWER.
    For a length that is a multiple of PMD_SIZE and no hint,
    [__get_unmapped_area] (mm/mmap.c:844-849) goes to
    [thp_get_unmapped_area_vmflags], which searches for [len +
    PMD_SIZE] and then aligns UP to the next 2 MiB boundary
    (mm/huge_memory.c, [__thp_get_unmapped_area]).  The padded search
    starts lower, so the answer is lower than the plain one even though
    the alignment moves it up again. *)
Example place_4m_without_thp :
  linux_place_b (m_vmmaps place_model) false (Z_to_bv 64 0) 0x400000
  = Some 23387524370432%Z.
Proof. vm_compute. reflexivity. Qed.

Example place_4m_with_thp :
  linux_place_b (m_vmmaps place_thp) true (Z_to_bv 64 0) 0x400000
  = Some 23387522990080%Z.
Proof. vm_compute. reflexivity. Qed.

Example place_thp_answer_is_pmd_aligned :
  (23387522990080 mod pmd_size)%Z = 0%Z.
Proof. vm_compute. reflexivity. Qed.

Example place_plain_answer_is_not_pmd_aligned :
  (23387524370432 mod pmd_size)%Z <> 0%Z.
Proof. vm_compute. discriminate. Qed.

(** (2) A HINT OF 1 TO 4095 IS NO HINT AT ALL.  [round_hint_to_min]
    (mm/mmap.c:219-226) is [hint &= PAGE_MASK] before anything else
    looks at the address, so 1 becomes 0 and the request takes the
    no-hint path — including the transparent-huge-page path, which
    [__get_unmapped_area] gates on [!addr]. *)
Example place_hint_one_is_no_hint :
  linux_place_b (m_vmmaps place_thp) true (Z_to_bv 64 1) 0x400000
  = linux_place_b (m_vmmaps place_thp) true (Z_to_bv 64 0) 0x400000.
Proof. vm_compute. reflexivity. Qed.

(** (3) A HINT THAT IS NOT PAGE ALIGNED IS ROUNDED DOWN AND HONOURED.
    0x1001 becomes 0x1000, the range is free, and
    [generic_get_unmapped_area_topdown]'s hint test (mm/mmap.c:753-761)
    returns it.  So a hinted grant CAN land at a low address, where a
    preference-free one cannot. *)
Example place_hint_rounded_down_and_honoured :
  linux_place_b (m_vmmaps place_model) false (Z_to_bv 64 0x1001) 4096
  = Some 4096%Z.
Proof. vm_compute. reflexivity. Qed.

(** (4) THE HINT 2^64-1 FAILS THE SEARCH'S OWN BOUND, so the plain
    search runs — and NOT the transparent-huge-page one, because the
    hint was nonzero.  The address is the plain answer of case (1),
    on a kernel that would otherwise have aligned it.  This is the case
    a reader is most likely to get wrong: a hint that cannot be
    honoured is not the same as no hint. *)
Example place_hint_max_searches_without_thp :
  linux_place_b (m_vmmaps place_thp) true (Z_to_bv 64 0xffffffffffffffff) 0x400000
  = Some 23387524370432%Z.
Proof. vm_compute. reflexivity. Qed.

Example place_hint_max_differs_from_no_hint :
  linux_place_b (m_vmmaps place_thp) true (Z_to_bv 64 0xffffffffffffffff) 0x400000
  <> linux_place_b (m_vmmaps place_thp) true (Z_to_bv 64 0) 0x400000.
Proof. vm_compute. discriminate. Qed.

(** (5) THE PLACEMENT IS A FUNCTION, and that is the property the whole
    change exists for: given the ledger, the kernel build and the hint,
    the model has no freedom left in the address. *)
Example place_is_a_function : forall h thp hint nZ a a',
  linux_place h thp hint nZ a -> linux_place h thp hint nZ a' -> a = a'.
Proof. exact linux_place_unique. Qed.

(* =========================================================================
   The vdso/vvar pair: the four calls that can meet it
   ========================================================================= *)

(** (a) AN munmap OF PART OF THE PAIR.  The model answers [unmodeled],
    which is its fail-closed answer: Linux unmaps the vvar page and the
    process then faults in the vDSO, and this model has no term for
    that.  Before the change the ledger did not carry the pair at all,
    so the same call looked like an unmap of nothing and SUCCEEDED; the
    premise in SCOPE.md that no [munmap] range meets the pair is what
    stood in for this answer, and it is gone. *)
Example vdso_partial_munmap_unmodeled :
  check_syscall
    (mkInput 215 [Z_to_bv 64 23387528564736; 4096; 0; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU 0 [] [] [(Z_to_bv 64 23387528564736, 4096)] [] [])
    place_model
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** (b) AN munmap OF THE WHOLE PAIR — the call a kernel with the vDSO
    sealed (mm/mseal.c) refuses outright.  Same answer, same reason. *)
Example vdso_whole_munmap_unmodeled :
  check_syscall
    (mkInput 215 [Z_to_bv 64 23387528564736; 24576; 0; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU 0 [] [] [(Z_to_bv 64 23387528564736, 24576)] [] [])
    place_model
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** (c) A MAP_FIXED OVER THE vDSO TEXT.  Linux replaces the mapping and
    the process loses its vDSO; the model declines rather than invent
    the result. *)
Example vdso_map_fixed_over_text_unmodeled :
  check_syscall
    (mkInput 222 [Z_to_bv 64 23387528581120; 4096; 0; 50; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU (Z_to_bv 64 23387528581120) [] []
       [(Z_to_bv 64 23387528581120, 4096)] [] [])
    place_model
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** (d) MAP_FIXED_NOREPLACE OVER THE vvar START IS ANSWERED, and it is
    answered as Linux answers it: -EEXIST.  [do_mmap] forces MAP_FIXED
    for MAP_FIXED_NOREPLACE and then checks
    [find_vma_intersection(mm, addr, addr + len)] (mm/mmap.c:410-413).
    This is the one of the four that the model does not decline, and it
    is the one that shows the pair is really in the ledger: with an
    empty [vm_reserved] there would be no intersection and no -EEXIST.
    Its neighbour, the same call one page BELOW the pair, is a grant,
    not an -EEXIST — see [vdso_noreplace_below_the_pair_is_not_eexist]. *)
Example vdso_noreplace_over_vvar_is_eexist :
  exists m' evs,
    check_syscall
      (mkInput 222 [Z_to_bv 64 23387528564736; 4096; 3; 1048610; mmap_fd_none; 0]
        (fun _ => None) (fun _ => None))
      (mkEffect (errno_ret EEXIST) [] []) place_model
    = CheckOk m' evs.
Proof. vm_compute. eexists; eexists; reflexivity. Qed.

Example vdso_noreplace_below_the_pair_is_not_eexist :
  check_syscall
    (mkInput 222 [Z_to_bv 64 23387528560640; 4096; 3; 1048610; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EEXIST) [] []) place_model
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** (e) A brk GROWTH THAT MEETS THE PAIR IS REFUSED, and refused the
    way Linux refuses it: [SYSCALL_DEFINE1(brk)] returns the OLD break
    when the next VMA starts before [newbrk + PAGE_SIZE]
    (mm/mmap.c:183-190), it does not return an errno.  So the pair of
    answers below is the test: the grow is rejected, and the same call
    answered with the old break is admitted. *)
Definition place_brk_model : Model :=
  init_model [] (Z_to_bv 64 23387528560640) (Z_to_bv 64 mmap_base_min)
    (Z_to_bv 64 sp_window_lo) target_alloc_limit (demo_input [] IEof).

Example vdso_brk_grow_into_the_pair_rejected :
  check_syscall
    (mkInput 214 [Z_to_bv 64 23387528564736; 0; 0; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffectU (Z_to_bv 64 23387528564736) []
       [(Z_to_bv 64 23387528560640, 4096)] [] [] [])
    place_brk_model
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

Example vdso_brk_grow_into_the_pair_keeps_the_old_break :
  exists m' evs,
    check_syscall
      (mkInput 214 [Z_to_bv 64 23387528564736; 0; 0; 0; 0; 0]
        (fun _ => None) (fun _ => None))
      (mkEffectU (Z_to_bv 64 23387528560640) [] [] [] [] [])
      place_brk_model
    = CheckOk m' evs.
Proof. vm_compute. eexists; eexists; reflexivity. Qed.
