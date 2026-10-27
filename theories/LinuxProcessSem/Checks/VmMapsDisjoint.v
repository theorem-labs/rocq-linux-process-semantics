(** * LinuxProcessSem.Checks.VmMapsDisjoint — what [vm_maps] really guarantees

    Not part of the trusted specification: QA on the definitions, in the
    style of [Checks/Examples.v], plus the ledger invariant those
    definitions DO maintain.

    One might expect the [vm_maps] intervals to be "pairwise disjoint
    by construction ([region_free] gates every grant)".  PART 1 below is
    a machine-checked execution that refutes that: six modeled syscalls
    from an [execve]-shaped [init_model] state leave the ledger holding
    two OVERLAPPING entries, and eight leave it holding two entries with
    the SAME BASE and different sizes.  So neither byte-level pairwise
    disjointness nor byte-level base uniqueness is an invariant of
    reachable states, and no proof of either can exist.

    PART 2 states and proves what IS invariant, which is the property
    every consumer of the ledger actually needs: no PAGE-ALIGNED address
    is owned by two entries.  Every address a syscall can name as a
    mapping base is page aligned ([munmap], [mremap] and [mprotect]
    answer -EINVAL otherwise, and [mmap] only ever places on a page
    boundary), so this yields base uniqueness exactly where it is used,
    and in particular makes [munmap]'s [map_has]/[map_remove] pair agree.

    WHY THE WEAKER PROPERTY IS THE RIGHT ONE.  The gap Part 1 exploits is
    real Linux behaviour, not a modelling slip: [SYSCALL_DEFINE1(brk)]
    (mm/mmap.c) rounds both breaks and takes

      newbrk = PAGE_ALIGN(brk);
      oldbrk = PAGE_ALIGN(mm->brk);
      if (oldbrk == newbrk) {
              mm->brk = brk;
              goto success;
      }

    BEFORE any VMA is consulted — the shrink block's [vma_find], the
    grow path's [check_brk_limits], its stack-guard-gap [vma_find] and
    [do_brk_flags] are all BELOW this exit.  Read at the kernel of
    record, stable v6.18.46 (commit
    1f99e9ab748fc5c32120de9c4eca31abfe54a4d5): [SYSCALL_DEFINE1(brk)] is
    still in mm/mmap.c — the v6.12-era VMA split moved [do_brk_flags] out
    to mm/vma.c but left the syscall and this exit where they were — and
    no statement between function entry and [goto success] reads the VMA
    tree.  The exit block quoted above is byte-identical from v5.18
    through v6.18.46.  The PROLOGUE is not byte-identical that far:
    commit e001ef9652c2 ("mm: simplify min_brk handling in brk()", first
    released in v6.17) hoisted [min_brk = mm->start_brk] above the
    [CONFIG_COMPAT_BRK] ifdef and inverted the test inside it, holding
    the prologue text constant only over v6.5-v6.16.  That is a
    no-functional-change refactor of a gate already above the exit and
    already not an address-space test, so nothing argued here moves with
    it; and neither does the v6.12 change of the shrink call from
    [do_vma_munmap] to [do_vmi_align_munmap], which is below the exit.
    Window figures sample mainline tags; the v6.18.46 statement is read
    from that commit itself.  A brk move
    within one page therefore reaches [mm->brk = brk] with NO
    ADDRESS-SPACE TEST APPLIED,
    even when the bytes it walks over belong to some other mapping — a
    state a real process reaches by unmapping the brk VMA and mapping
    over it.  Not unconditionally, though: three gates sit ABOVE the
    exit, none of them about the address space — the killable
    [mmap_write_lock], the [brk < min_brk] floor, and
    [check_data_rlimit(rlimit(RLIMIT_DATA), brk, ...)], which is passed
    the RAW unaligned break precisely so a non-page-aligned limit cannot
    be escaped by a within-page grow.  Each returns [origbrk], the break
    unchanged.  The model does not carry [RLIMIT_DATA], and does not need
    to: [brk_r_ok] admits [r = vm_brk h] on every grow, which is that
    same unchanged break, so a refusal it does not model is already an
    admissible outcome.  The model reproduces
    that faithfully with [brk_grow_ok]'s [else true], and a gate that
    required the unrounded range [[old, r)] to be [region_free] would
    make the model REJECT a call Linux serves.  [brk_r_ok] evaluates the
    gate at the resolution it is shown, so the tightening would decline
    the SUCCESS resolution [r = req] — the break Linux hands back —
    while leaving the no-op resolution [r = old] admissible, its outer
    guard having degenerated to [old < old].  The byte-level overlap is
    the honest ledger reading of a real kernel state; page-granular
    ownership is what survives it. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run MemImageType StackLayout.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
Import ListNotations.
Open Scope bv_scope.

(** [vm_compute]-normalized results can differ from literal expected
    values only in the (opaque, proof-irrelevant) [BvWf] proofs inside
    [bv] leaves; descend to those leaves and compare unsigned values. *)
Ltac check_eq :=
  vm_compute;
  repeat first [reflexivity | (apply bv_eq; reflexivity) | progress f_equal].

(* =========================================================================
   PART 1 — the counterexample, as a chain of modeled syscalls

   Reason 3 of [Checks/Examples.v]'s taxonomy: this pins MODEL-INTERNAL
   STATE (the [vm_maps] list) that no observation of a real execution
   reveals, and it is a statement about a WHOLE RUN rather than one call.

   The process: the image occupies [4096, 8192) and the ASLR-placed break
   base sits at 0x10000 = 65536, exactly the shape [Checks/Examples.v]'s
   brk section uses.  [wit_valid_brk] below records that this really is an
   [execve]-admissible placement.
   ========================================================================= *)

Definition wit_reserved : list (word * word) := [(4096, 4096)].
Definition wit_brk_base : word := 65536.
Definition wit_limit : Z := 0x40000000%Z.

(** [mm->mmap_base].  Nothing in the spec reads this field, so no
    step below depends on the value.  It is
    pinned to an admissible one ([wit_mmap_base_admissible]) so that the
    whole start state is one [execve] can hand out, which is what makes
    the overlap below reachable rather than hypothetical.  That is the
    only reason: no spec arm reads the value (the ASan plan checker's
    placement gate does, outside the spec; see [State]'s [vm_mmap_base]
    field note). *)
Definition wit_mmap_base : word := Z_to_bv 64 mmap_base_min.

(** The witness ledger.  [State.mkVmMaps] would default [vm_mmap_base] to
    zero, which is below [State.mmap_base_min]; this fixes it at the
    admissible value instead and is otherwise that same constructor. *)
Definition wit_vm (maps : list (word * word)) (start_brk brk : word)
    (limit : Z) : VmMaps :=
  mkVmMapsFull wit_reserved maps [] start_brk brk limit wit_mmap_base
    (Z_to_bv 64 sp_window_lo).

Definition wit_s0 : Model :=
  init_model wit_reserved wit_brk_base wit_mmap_base (Z_to_bv 64 sp_window_lo)
    wit_limit
    (mkProcInput [] [] [] IEof (Z_to_bv 64 1000) (Z_to_bv 64 1002) []
                 net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc false Sv48).

(** The starting state is one [execve] really can hand a process: the
    break base is page aligned and sits at or above the page-rounded
    image top, within the brk ASLR window.  These are exactly
    [Run.valid_brk]'s three conjuncts, spelled on the reservation list so
    that the statement mentions no [MemImageType.Segment] — whose
    primitive-string payload field would otherwise show up under
    [Print Assumptions] as the kernel constant [PrimString.string]. *)
(** [Run.valid_mmap_base]'s three conjuncts, spelled out for the same
    reason the brk ones are below. *)
Lemma wit_mmap_base_admissible :
  (mmap_base_min <= bv_unsigned wit_mmap_base)%Z
  /\ (bv_unsigned wit_mmap_base <= mmap_base_max)%Z
  /\ (bv_unsigned wit_mmap_base mod page_size = 0)%Z.
Proof.
  unfold wit_mmap_base, mmap_base_min, mmap_base_max, sp_window_hi,
    page_size.
  repeat split; vm_compute; try discriminate; reflexivity.
Qed.

Lemma wit_brk_base_admissible :
  (reserved_top wit_reserved <= bv_unsigned wit_brk_base)%Z
  /\ (bv_unsigned wit_brk_base <= reserved_top wit_reserved + brk_aslr_max)%Z
  /\ (bv_unsigned wit_brk_base mod page_size = 0)%Z.
Proof.
  unfold wit_reserved, wit_brk_base, brk_aslr_max, page_size.
  cbn [reserved_top]. repeat split; vm_compute; try discriminate; reflexivity.
Qed.

(** …and that really is [Run.valid_brk] for any image whose LOAD
    reservations are [wit_reserved]. *)
Lemma wit_valid_brk : forall segs,
  segments_reserved segs = wit_reserved -> valid_brk segs wit_brk_base.
Proof.
  intros segs Hs. unfold valid_brk. rewrite Hs.
  exact wit_brk_base_admissible.
Qed.

Definition brk_in (req : word) : SyscallInput :=
  mkInput 214 [req; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None).

(** STEP 1 — brk(0x11000): an ordinary page-crossing grow.  The gate
    checks [[65536, 69632)] and grants it. *)
Definition wit_s1 : Model :=
  with_vmmaps (wit_vm [(65536, 4096)] 65536 69632 wit_limit) wit_s0.

Example wit_step1 :
  check_syscall (brk_in 69632) (mkEffect 69632 [] [(65536, 4096)]) wit_s0
  = CheckOk wit_s1 [].
Proof. check_eq. Qed.

(** STEP 2 — brk(0x11064): grow 100 bytes past the page boundary.  The
    gate checks the ROUNDED range [[69632, 73728)]; the ledger records
    the LOGICAL range [[69632, 69732)].  The break is now mid-page. *)
Definition wit_s2 : Model :=
  with_vmmaps
    (wit_vm [(69632, 100); (65536, 4096)] 65536 69732 wit_limit)
    wit_s0.

Example wit_step2 :
  check_syscall (brk_in 69732) (mkEffect 69732 [] [(69632, 4096)]) wit_s1
  = CheckOk wit_s2 [].
Proof. check_eq. Qed.

(** STEP 3 — munmap(0x10000, 4096): drop the FIRST heap grant.  Linux
    unmaps those pages and leaves [mm->brk] alone; so does the model. *)
Definition wit_s3 : Model :=
  with_vmmaps
    (wit_vm [(69632, 100)] 65536 69732 wit_limit) wit_s0.

Example wit_step3 :
  check_syscall
    (mkInput 215 [65536; 4096; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffectU 0 [] [] [(65536, 4096)] [] []) wit_s2
  = CheckOk wit_s3 [].
Proof. check_eq. Qed.

(** STEP 4 — brk(0x107d0): shrink down into the hole step 3 opened.  The
    remaining grant is above the new break, so the ledger empties; the
    break lands mid-page at 67536, with NOTHING below it owned. *)
Definition wit_s4 : Model :=
  with_vmmaps (wit_vm [] 65536 67536 wit_limit) wit_s0.

Example wit_step4 :
  check_syscall (brk_in 67536)
    (mkEffectU 67536 [] [] [(69632, 4096)] [] []) wit_s3
  = CheckOk wit_s4 [].
Proof. check_eq. Qed.

(** STEP 5 — mmap of one page AT AN EXPLICIT HINT of 0x10000, which the
    kernel honors because the range is free of the image and of every
    live mapping, so [region_free] accepts.  The break now points INSIDE
    this fresh mapping — the model's reading of "the brk VMA was
    unmapped and something else was mapped over it", which a real kernel
    permits. *)
Definition wit_s5 : Model :=
  with_vmmaps (wit_vm [(65536, 4096)] 65536 67536 wit_limit) wit_s0.

Example wit_step5 :
  check_syscall
    (mkInput 222 [65536; 4096; 3; 34; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] [(65536, 4096)]) wit_s4
  = CheckOk wit_s5 [].
Proof. check_eq. Qed.

(** THE HINT IS NOT LOAD-BEARING.
    The identical grant with a NULL hint is admitted, because the spec
    says only three things about a preference-free placement — page
    alignment, the user range, and disjointness from every recorded
    mapping — and 0x10000 satisfies all three on this ledger.

    The spec does not pin the search further — at or above a bottom-up
    floor derived from riscv64's [TASK_UNMAPPED_BASE], or else leaving
    no fitting free gap up to the run's [mm->mmap_base] — because such a
    conjunct EXCLUDES placements Linux makes: its highest-fit half would
    be read on a ledger that does not carry the kernel's own vdso/vvar
    VMAs, so a real top-down descent would look impossible to the
    model.  The cost is exactly this: a low placement no ORDINARY
    kernel run produces is admissible.

    That is a provability cost and not a soundness one, and it is
    bounded.  It cannot refute a statement by colliding with a runtime's
    later MAP_FIXED reservation, because [Mmap.mmap_spec] models that
    MAP_FIXED as the replacement Linux performs rather than declining it;
    what remains is that a program whose observable behaviour depends on
    where a mapping landed has a false equivalence statement, which is
    the correct answer under ASLR.  The pair is kept — the hinted step 5
    above and this one — because the two together say what the spec does
    and does not constrain, which is what a reader needs. *)
Example wit_step5_null_hint_also_admitted :
  check_syscall
    (mkInput 222 [0; 4096; 3; 34; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] [(65536, 4096)]) wit_s4
  = CheckOk wit_s5 [].
Proof. check_eq. Qed.

(** …and the conditions that DO still refuse are pinned here, so the
    accept above is not read as "anything goes": the same NULL-hint
    grant at an unaligned address, and at one that overlaps the live
    mapping step 5 placed, are both rejected. *)
Example wit_step5_null_hint_unaligned_refused :
  check_syscall
    (mkInput 222 [0; 4096; 3; 34; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 65537 [] [(65537, 4096)]) wit_s4
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

Example wit_step5_null_hint_overlapping_refused :
  check_syscall
    (mkInput 222 [0; 4096; 3; 34; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 65536 [] [(65536, 4096)]) wit_s5
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** THE OVERLAP, in one more step.  brk(0x10834) grows the break by 100
    bytes without crossing a page boundary, so [brk_grow_ok] computes
    [lo = hi = 69632] and runs NO address-space test at all; the grant
    [[67536, 67636)] lands inside the mapping step 5 placed.  Two live
    [vm_maps] entries now overlap. *)
Definition wit_overlap : Model :=
  with_vmmaps
    (wit_vm [(67536, 100); (65536, 4096)] 65536 67636 wit_limit)
    wit_s0.

Example wit_overlap_step :
  check_syscall (brk_in 67636) (mkEffect 67636 [] []) wit_s5
  = CheckOk wit_overlap [].
Proof. check_eq. Qed.

(** …and the entries really do overlap.  The grant's OWN entry is
    dropped before the query, because every nonempty interval overlaps
    itself: what is checked is that the step-5 mapping alone already
    covers the range the brk grant just took. *)
Example wit_overlap_holds :
  region_free (map_remove (vm_maps (m_vmmaps wit_overlap)) 67536) 67536 100
  = false.
Proof. vm_compute. reflexivity. Qed.

(** STEP 6 — brk(0x107c6): a ten-byte shrink, still inside one page.  It
    SPLITS the step-5 mapping, and the right-hand remnant is based at the
    OLD break, 67536. *)
Definition wit_s6 : Model :=
  with_vmmaps
    (wit_vm [(65536, 1990); (67536, 2096)] 65536 67526 wit_limit)
    wit_s0.

Example wit_step6 :
  check_syscall (brk_in 67526) (mkEffect 67526 [] []) wit_s5
  = CheckOk wit_s6 [].
Proof. check_eq. Qed.

(** STEP 7 — brk(0x107d0): grow the ten bytes back.  Same page, so again
    no address-space test. *)
Definition wit_s7 : Model :=
  with_vmmaps
    (wit_vm [(67526, 10); (65536, 1990); (67536, 2096)]
              65536 67536 wit_limit)
    wit_s0.

Example wit_step7 :
  check_syscall (brk_in 67536) (mkEffect 67536 [] []) wit_s6
  = CheckOk wit_s7 [].
Proof. check_eq. Qed.

(** STEP 8 — brk(0x10834): one more same-page grow, from a break that is
    now the base of the step-6 remnant.  [brk_grants] records
    [[67536, 67636)] and the ledger ends up with TWO entries based at
    67536. *)
Definition wit_s8 : Model :=
  with_vmmaps
    (wit_vm
      [(67536, 100); (67526, 10); (65536, 1990); (67536, 2096)]
      65536 67636 wit_limit)
    wit_s0.

Example wit_step8 :
  check_syscall (brk_in 67636) (mkEffect 67636 [] []) wit_s7
  = CheckOk wit_s8 [].
Proof. check_eq. Qed.

(** THE VERDICT.  Two DIFFERENT sizes are both "exactly the mapping at
    67536", so [map_has] does not determine the entry [map_remove] would
    drop.  Byte-level base uniqueness is therefore not an invariant of
    reachable states, and no proof of it can exist as the model stands. *)
Example wit_duplicate_base :
  map_has (vm_maps (m_vmmaps wit_s8)) 67536 100 = true
  /\ map_has (vm_maps (m_vmmaps wit_s8)) 67536 2096 = true.
Proof. split; vm_compute; reflexivity. Qed.

(** The duplicated base is NOT page aligned, and Part 2 shows that is no
    accident: a page-aligned break makes [brk_grow_ok] compute
    [lo < hi] and the [region_free] test does run. *)
Example wit_duplicate_base_is_unaligned :
  (67536 mod page_size <> 0)%Z.
Proof. vm_compute. discriminate. Qed.

(** A simpler route — [mmap] choosing the mid-page break
    itself as its base — cannot happen, and this is the gate that stops
    it: [mmap]'s placement is page aligned in every branch that grants,
    so the route above (a munmap that opens a hole, then a shrink INTO
    it) is the shorter one that works.  Asked for that base DIRECTLY, by
    the same hinted request step 5 uses and differing only in the
    address, so the refusal is the alignment test and nothing else. *)
Example mmap_cannot_place_at_the_midpage_break :
  check_syscall
    (mkInput 222 [67536; 4096; 3; 34; mmap_fd_none; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect 67536 [] [(67536, 4096)]) wit_s4
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   PART 2 — the invariant that IS maintained

   [owners maps p] counts the live entries that own byte [p].  The
   invariant is that no PAGE-ALIGNED byte has two owners.  Part 1 shows
   the same statement is false for an arbitrary byte.
   ========================================================================= *)

Local Open Scope Z_scope.

(** Does the ledger entry [e] own the byte at address [p]? *)
Definition owns_b (e : word * word) (p : Z) : bool :=
  (bv_unsigned (fst e) <=? p)
  && (p <? bv_unsigned (fst e) + bv_unsigned (snd e)).

Fixpoint owners (maps : list (word * word)) (p : Z) : nat :=
  match maps with
  | [] => 0%nat
  | e :: r => ((if owns_b e p then 1 else 0) + owners r p)%nat
  end.

(** THE INVARIANT.  Every page-aligned address is owned by at most one
    live mapping. *)
Definition page_owner_unique (maps : list (word * word)) : Prop :=
  forall p, p mod page_size = 0 -> (owners maps p <= 1)%nat.

(** The companion well-formedness the ledger's writers also maintain, and
    which the corollaries need: no entry is empty.  An empty entry would
    own nothing, so it would slip past [region_free] and past
    [page_owner_unique] while still answering [map_has]. *)
Definition sizes_nonzero (maps : list (word * word)) : Prop :=
  Forall (fun e => bv_unsigned (snd e) <> 0) maps.

Definition maps_wf (maps : list (word * word)) : Prop :=
  sizes_nonzero maps /\ page_owner_unique maps.

Definition vm_wf (h : VmMaps) : Prop := maps_wf (vm_maps h).


(* -------------------------------------------------------------------------
   PART 2b — what the overlap does to the byte total

   Two readings of [State.live_bytes] — "exactly the number of
   granted-and-not-freed bytes", and metering "BYTES, not addresses —
   which is what makes the forced out-of-memory point deterministic" —
   follow from the disjointness Part 1 refutes, and both fail without
   it.  These cases pin the failure so
   that neither sentence can be claimed while the overlap is still
   reachable, and so that closing the gap in [brk_grow_ok] would have to
   break a case here rather than silently re-truth a comment.

   It sits after [owners] rather than beside Part 1's counterexample
   because the distinct-byte measure below is built from it.

   This is a known limitation of the model.
   ------------------------------------------------------------------------- *)

(** How many of the [n] bytes from [lo] are owned by at least one live
    entry.  [owners] is Part 2's per-address ownership count; this is the
    DISTINCT-byte measure [live_bytes] claims to be, computed the slow
    honest way over a bounded window so the two can be compared. *)
Fixpoint owned_bytes (maps : list (word * word)) (lo : Z) (n : nat) : nat :=
  match n with
  | O => O
  | S k => ((if Nat.ltb 0 (owners maps lo) then 1 else 0)
            + owned_bytes maps (lo + 1) k)%nat
  end.

(** THE DOUBLE COUNT.  [wit_overlap]'s ledger is
    [[(67536, 100); (65536, 4096)]]: the brk grant lies wholly inside the
    mapping step 5 placed, so 4096 distinct bytes are granted and
    [live_bytes] reports 4196.  Exactly 100 bytes are charged twice —
    the size of the contained entry. *)
Example live_bytes_over_counts_the_overlap :
  live_bytes (vm_maps (m_vmmaps wit_overlap)) = 4196%Z
  /\ owned_bytes (vm_maps (m_vmmaps wit_overlap)) 65536 4196 = 4096%nat.
Proof. split; vm_compute; reflexivity. Qed.

(** THE CONTROL, and the case that makes the one above mean something.
    The same two SIZES placed end to end instead of nested: [live_bytes]
    reports 4196 again, and now that IS the distinct-byte count.  Without
    this pair the case above would pass just as well against an
    [owned_bytes] that always answered 4096. *)
Definition disjoint_ledger : list (word * word) :=
  [(Z_to_bv 64 69632, Z_to_bv 64 100); (Z_to_bv 64 65536, Z_to_bv 64 4096)].

Example live_bytes_is_exact_when_the_entries_are_disjoint :
  live_bytes disjoint_ledger = 4196%Z
  /\ owned_bytes disjoint_ledger 65536 4196 = 4196%nat.
Proof. split; vm_compute; reflexivity. Qed.

(** SO PLACEMENT PLAYS A PART.  The two ledgers hold the same multiset of
    sizes and [live_bytes] cannot tell them apart, while the number of
    bytes actually granted differs by 100.  One number cannot be the
    distinct-byte count of both, so the budget total is a function of
    WHERE the grants landed and not only of which sizes were granted and
    freed — which is what the second reading above denies, and the
    reason the forced out-of-memory point is not determined
    by the grant-and-free history alone. *)
Example placement_changes_the_granted_byte_count :
  live_bytes (vm_maps (m_vmmaps wit_overlap)) = live_bytes disjoint_ledger
  /\ owned_bytes (vm_maps (m_vmmaps wit_overlap)) 65536 4196
     <> owned_bytes disjoint_ledger 65536 4196.
Proof. split; [vm_compute; reflexivity | vm_compute; discriminate]. Qed.

(** THE DIRECTION, pinned rather than left to the prose: the sum is never
    below the distinct count, so every [used + delta <=? limit] gate
    built on it fires no later than the truth and can fire EARLIER.  The
    model refuses a call Linux serves; it never grants one Linux would
    refuse on this account. *)
Example live_bytes_over_counts_never_under :
  (Z.of_nat (owned_bytes (vm_maps (m_vmmaps wit_overlap)) 65536 4196)
   <= live_bytes (vm_maps (m_vmmaps wit_overlap)))%Z.
Proof. vm_compute. discriminate. Qed.

(** And the duplicate-base state double counts too, by the size of the
    smaller of the two entries sharing base 67536. *)
Example live_bytes_over_counts_the_duplicate_base :
  live_bytes (vm_maps (m_vmmaps wit_s8)) = 4196%Z
  /\ owned_bytes (vm_maps (m_vmmaps wit_s8)) 65536 4196 = 4096%nat.
Proof. split; vm_compute; reflexivity. Qed.

(* -------------------------------------------------------------------------
   Arithmetic and counting lemmas
   ------------------------------------------------------------------------- *)

Lemma u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

Lemma word_range : forall (w : word), 0 <= bv_unsigned w < 2 ^ 64.
Proof.
  intro w. pose proof (bv_unsigned_in_range 64 w) as H.
  change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.

Lemma page_round_up_Z_ge : forall z, 0 <= z -> z <= page_round_up_Z z.
Proof.
  intros z Hz. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4095) 4096 ltac:(lia)) as Hd.
  pose proof (Z.mod_pos_bound (z + 4095) 4096 ltac:(lia)) as Hm.
  lia.
Qed.

(** The step Part 1 turns on: a PAGE-ALIGNED address at or above [z] is
    at or above [z] ROUNDED UP.  This is exactly why the rounded gate
    covers every page-aligned byte of the range it fails to cover
    byte-for-byte. *)
Lemma page_round_up_Z_le_aligned : forall z p,
  p mod page_size = 0 -> z <= p -> page_round_up_Z z <= p.
Proof.
  intros z p Hp Hzp. unfold page_round_up_Z, page_size in *.
  remember (p / 4096) as q eqn:Hqdef.
  assert (Hq : p = 4096 * q).
  { subst q. pose proof (Z.div_mod p 4096 ltac:(lia)). lia. }
  assert (Hle : (z + 4095) / 4096 < q + 1)
    by (apply Z.div_lt_upper_bound; lia).
  remember ((z + 4095) / 4096) as k eqn:Hkdef.
  nia.
Qed.

Lemma owns_true : forall a n p,
  owns_b (a, n) p = true -> bv_unsigned a <= p < bv_unsigned a + bv_unsigned n.
Proof.
  intros a n p H. unfold owns_b in H. cbn [fst snd] in H.
  apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma owns_false : forall a n p,
  owns_b (a, n) p = false ->
  p < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= p.
Proof.
  intros a n p H. unfold owns_b in H. cbn [fst snd] in H.
  apply andb_false_iff in H as [H|H].
  - apply Z.leb_gt in H. lia.
  - apply Z.ltb_ge in H. lia.
Qed.

Lemma owns_intro : forall a n p,
  bv_unsigned a <= p -> p < bv_unsigned a + bv_unsigned n -> owns_b (a, n) p = true.
Proof.
  intros a n p H1 H2. unfold owns_b. cbn [fst snd].
  apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.

(** Two entries that own the same byte overlap — the bridge from
    [owners] to [region_free]. *)
Lemma owns_overlap : forall a n b s p,
  owns_b (a, n) p = true -> owns_b (b, s) p = true -> iv_overlap a n b s = true.
Proof.
  intros a n b s p H1 H2.
  apply owns_true in H1. apply owns_true in H2.
  unfold iv_overlap. apply andb_true_iff.
  split; apply Z.ltb_lt; lia.
Qed.

Lemma region_free_no_owner : forall maps a n p,
  region_free maps a n = true -> owns_b (a, n) p = true -> owners maps p = 0%nat.
Proof.
  induction maps as [|[b s] r IH]; intros a n p Hfree Hown; [reflexivity|].
  cbn in Hfree. apply andb_true_iff in Hfree as [Hhd Htl].
  cbn [owners]. destruct (owns_b (b, s) p) eqn:Ho.
  - rewrite (owns_overlap a n b s p Hown Ho) in Hhd. discriminate.
  - cbn. exact (IH a n p Htl Hown).
Qed.

Lemma region_free_app_r : forall l1 l2 lo n,
  region_free (l1 ++ l2) lo n = true -> region_free l2 lo n = true.
Proof.
  induction l1 as [|[b s] r IH]; intros l2 lo n H; [exact H|].
  cbn in H. apply andb_true_iff in H as [_ H]. exact (IH l2 lo n H).
Qed.

Lemma owners_app : forall l1 l2 p,
  owners (l1 ++ l2) p = (owners l1 p + owners l2 p)%nat.
Proof.
  induction l1 as [|e r IH]; intros l2 p; cbn; [reflexivity|].
  rewrite IH. lia.
Qed.

Lemma owners_filter_split : forall f maps p,
  (owners (List.filter f maps) p
   + owners (List.filter (fun e => negb (f e)) maps) p
   = owners maps p)%nat.
Proof.
  induction maps as [|e r IH]; intros p; cbn; [reflexivity|].
  specialize (IH p). destruct (f e); cbn; destruct (owns_b e p); lia.
Qed.

Lemma owners_filter_le : forall f maps p,
  (owners (List.filter f maps) p <= owners maps p)%nat.
Proof.
  intros f maps p. pose proof (owners_filter_split f maps p). lia.
Qed.

Lemma sizes_nonzero_filter : forall f maps,
  sizes_nonzero maps -> sizes_nonzero (List.filter f maps).
Proof.
  unfold sizes_nonzero. induction maps as [|e r IH]; intros H; cbn; [constructor|].
  inversion H as [|? ? Hhd Htl]; subst.
  destruct (f e); [constructor; [exact Hhd|]|]; now apply IH.
Qed.

Lemma owners_ge1 : forall maps e p,
  In e maps -> owns_b e p = true -> (1 <= owners maps p)%nat.
Proof.
  induction maps as [|e' r IH]; intros e p Hin Ho; [contradiction|].
  cbn [owners]. destruct Hin as [->|Hin].
  - rewrite Ho. lia.
  - specialize (IH e p Hin Ho). destruct (owns_b e' p); lia.
Qed.

Lemma owners_all_own : forall l p,
  (forall e, In e l -> owns_b e p = true) -> owners l p = length l.
Proof.
  induction l as [|e r IH]; intros p H; cbn; [reflexivity|].
  rewrite (H e ltac:(now left)). rewrite (IH p); [lia|].
  intros e' Hin. apply H. now right.
Qed.

Lemma owners_map_remove_lt : forall maps b s p,
  In (b, s) maps -> owns_b (b, s) p = true ->
  (owners (map_remove maps b) p + 1 <= owners maps p)%nat.
Proof.
  induction maps as [|e r IH]; intros b s p Hin Ho; [contradiction|].
  unfold map_remove in *. cbn [List.filter].
  destruct (negb (bv_eqb (fst e) b)) eqn:Hf.
  - assert (Hin' : In (b, s) r).
    { destruct Hin as [He|Hin]; [|exact Hin].
      subst e. cbn in Hf. rewrite bv_eqb_refl in Hf. discriminate. }
    specialize (IH b s p Hin' Ho). cbn [owners].
    destruct (owns_b e p); lia.
  - destruct Hin as [He|Hin].
    + subst e. cbn [owners]. rewrite Ho.
      pose proof (owners_filter_le (fun q => negb (bv_eqb (fst q) b)) r p). lia.
    + specialize (IH b s p Hin Ho). cbn [owners].
      destruct (owns_b e p); lia.
Qed.

(* -------------------------------------------------------------------------
   The two ways the ledger grows: a fresh [region_free] grant, and a
   [maps_subtract] that can only shrink coverage
   ------------------------------------------------------------------------- *)

(** A grant checked by [region_free] against the very list it is
    prepended to keeps the invariant, for EVERY address — page aligned
    or not. *)
Lemma maps_wf_cons_free : forall maps a n,
  maps_wf maps -> bv_unsigned n <> 0 ->
  region_free maps a n = true ->
  maps_wf ((a, n) :: maps).
Proof.
  intros maps a n [Hnz Hun] Hn Hfree. split.
  - constructor; [exact Hn|exact Hnz].
  - intros p Hp. cbn [owners]. destruct (owns_b (a, n) p) eqn:Ho.
    + rewrite (region_free_no_owner maps a n p Hfree Ho). lia.
    + specialize (Hun p Hp). lia.
Qed.

Lemma iv_subtract_ok : forall a sz lo hi p,
  0 <= lo -> lo <= hi -> hi < 2 ^ 64 -> bv_unsigned sz <> 0 ->
  (owners (iv_subtract a sz lo hi) p
     <= if owns_b (a, sz) p then 1 else 0)%nat
  /\ sizes_nonzero (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi p Hlo0 Hlohi Hhi Hsz.
  pose proof (word_range a) as Ha. pose proof (word_range sz) as Hs.
  unfold iv_subtract.
  destruct (bv_unsigned a <? lo) eqn:E1; [apply Z.ltb_lt in E1|apply Z.ltb_ge in E1];
  destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2;
    [apply Z.ltb_lt in E2|apply Z.ltb_ge in E2| apply Z.ltb_lt in E2|apply Z.ltb_ge in E2];
  cbn [app];
  repeat match goal with
  | |- context [ owners (?x :: ?y) p ] => cbn [owners]
  end;
  repeat rewrite u64 by lia;
  repeat match goal with
  | |- context [ owns_b ?e p ] => destruct (owns_b e p) eqn:?
  end;
  repeat match goal with
  | H : owns_b (?x, ?y) p = true |- _ => apply owns_true in H
  | H : owns_b (?x, ?y) p = false |- _ => apply owns_false in H
  end;
  repeat rewrite u64 in * by lia;
  split; try (cbn; lia);
  repeat constructor; cbn [snd]; rewrite u64 by lia; lia.
Qed.

Lemma maps_subtract_ok : forall maps lo hi,
  0 <= lo -> lo <= hi -> hi < 2 ^ 64 -> sizes_nonzero maps ->
  sizes_nonzero (maps_subtract maps lo hi)
  /\ forall p, (owners (maps_subtract maps lo hi) p <= owners maps p)%nat.
Proof.
  induction maps as [|[a sz] r IH]; intros lo hi Hlo Hlohi Hhi Hnz.
  - split; [constructor|intro p; cbn; lia].
  - inversion Hnz as [|? ? Hhd Htl]; subst.
    destruct (IH lo hi Hlo Hlohi Hhi Htl) as [IHnz IHle].
    cbn [maps_subtract]. split.
    + apply Forall_app. split; [|exact IHnz].
      cbn [snd] in Hhd.
      destruct (iv_subtract_ok a sz lo hi 0 Hlo Hlohi Hhi Hhd) as [_ Hw].
      exact Hw.
    + intro p. rewrite owners_app. cbn [owners].
      cbn [snd] in Hhd.
      destruct (iv_subtract_ok a sz lo hi p Hlo Hlohi Hhi Hhd) as [Hc _].
      specialize (IHle p). destruct (owns_b (a, sz) p); lia.
Qed.

Lemma maps_wf_subtract : forall maps lo hi,
  0 <= lo -> lo <= hi -> hi < 2 ^ 64 ->
  maps_wf maps -> maps_wf (maps_subtract maps lo hi).
Proof.
  intros maps lo hi H1 H2 H3 [Hnz Hun].
  destruct (maps_subtract_ok maps lo hi H1 H2 H3 Hnz) as [Ha Hb].
  split; [exact Ha|]. intros p Hp. specialize (Hb p). specialize (Hun p Hp). lia.
Qed.

(** Nothing survives a subtraction INSIDE the range subtracted.
    [iv_subtract] keeps only the parts of an entry that fall outside the
    cut — a left remnant ending at the cut's base and a right remnant
    starting at its end — so the cut itself is free of the result.

    This is what makes the spanning MAP_FIXED post-state well formed:
    that arm's ledger is the request consed onto the subtraction, and
    [maps_wf_cons_free] wants the new entry disjoint from what is left.
    The [2 ^ 64] bound is the right remnant's: its base is
    [Z.max a (addr + n)], which only round-trips through [Z_to_bv 64]
    while the request's end fits in a word.  Every caller has that from
    the [alloc_top] gate. *)
Lemma iv_subtract_region_free : forall c sz (a n : word),
  bv_unsigned a + bv_unsigned n < 2 ^ 64 ->
  forall b s,
    In (b, s)
      (iv_subtract c sz (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) ->
    iv_overlap a n b s = false.
Proof.
  intros c sz a n Hhi b s Hin.
  pose proof (word_range a) as Ha. pose proof (word_range n) as Hn.
  pose proof (word_range c) as Hc. pose proof (word_range sz) as Hsz.
  unfold iv_subtract in Hin. apply in_app_or in Hin.
  destruct Hin as [Hin|Hin].
  - destruct (bv_unsigned c <? bv_unsigned a) eqn:E1; cbn in Hin;
      [|contradiction].
    apply Z.ltb_lt in E1.
    destruct Hin as [Heq|[]]. inversion Heq; subst b s.
    unfold iv_overlap. rewrite u64 by lia.
    apply andb_false_iff. left. apply Z.ltb_ge. lia.
  - destruct (bv_unsigned a + bv_unsigned n
              <? bv_unsigned c + bv_unsigned sz) eqn:E2; cbn in Hin;
      [|contradiction].
    apply Z.ltb_lt in E2.
    destruct Hin as [Heq|[]]. inversion Heq; subst b s.
    unfold iv_overlap.
    rewrite (u64 (Z.max (bv_unsigned c) (bv_unsigned a + bv_unsigned n)))
      by lia.
    apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.

Lemma maps_subtract_region_free : forall maps (a n : word),
  bv_unsigned a + bv_unsigned n < 2 ^ 64 ->
  region_free
    (maps_subtract maps (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
    a n = true.
Proof.
  intros maps a n Hhi. apply region_free_intro.
  induction maps as [|[c sz] r IH]; intros b s Hin; [contradiction|].
  cbn [maps_subtract] in Hin. apply in_app_or in Hin.
  destruct Hin as [Hin|Hin].
  - exact (iv_subtract_region_free c sz a n Hhi b s Hin).
  - exact (IH b s Hin).
Qed.

Lemma maps_wf_filter : forall f maps,
  maps_wf maps -> maps_wf (List.filter f maps).
Proof.
  intros f maps [Hnz Hun]. split; [now apply sizes_nonzero_filter|].
  intros p Hp. pose proof (owners_filter_le f maps p). specialize (Hun p Hp). lia.
Qed.

Lemma region_free_filter : forall f maps lo n,
  region_free maps lo n = true -> region_free (List.filter f maps) lo n = true.
Proof.
  intros f maps lo n H. apply region_free_intro. intros a sz Hin.
  apply List.filter_In in Hin as [Hin _].
  exact (region_free_In maps lo n a sz H Hin).
Qed.

Lemma maps_wf_cons_sub : forall maps a n0 n,
  maps_wf maps -> bv_unsigned n <> 0 ->
  In (a, n0) maps -> bv_unsigned n <= bv_unsigned n0 ->
  maps_wf ((a, n) :: map_remove maps a).
Proof.
  intros maps a n0 n [Hnz Hun] Hn Hin Hle. split.
  - constructor; [exact Hn|now apply sizes_nonzero_filter].
  - intros p Hp. cbn [owners]. destruct (owns_b (a, n) p) eqn:Ho.
    + apply owns_true in Ho.
      assert (Ho0 : owns_b (a, n0) p = true) by (apply owns_intro; lia).
      pose proof (owners_map_remove_lt maps a n0 p Hin Ho0).
      specialize (Hun p Hp). lia.
    + pose proof (owners_filter_le (fun q => negb (bv_eqb (fst q) a)) maps p).
      specialize (Hun p Hp). unfold map_remove. lia.
Qed.

(* -------------------------------------------------------------------------
   What the invariant buys: base uniqueness where a syscall can name a
   base, and the [map_has]/[map_remove] agreement munmap needs
   ------------------------------------------------------------------------- *)

Lemma map_has_In : forall maps a n,
  map_has maps a n = true -> In (a, n) maps.
Proof.
  intros maps a n H. unfold map_has in H.
  apply existsb_exists in H as [[b s] [Hin Hb]].
  apply andb_true_iff in Hb as [H1 H2]. cbn [fst snd] in *.
  apply bv_eqb_eq in H1. apply bv_eqb_eq in H2. subst. exact Hin.
Qed.

(** THE NARROW FORM the downstream [munmap] argument asks for: at a
    PAGE-ALIGNED base — the only kind [munmap], [mremap], [mprotect] and
    [mmap] can produce or accept — the ledger holds exactly one entry,
    and it is the one [map_has] matched.  So [map_has]'s [(base, size)]
    test and [map_remove]'s base-only removal name the same mapping. *)
Theorem base_entry_unique : forall maps a n,
  maps_wf maps -> bv_unsigned a mod page_size = 0 ->
  map_has maps a n = true ->
  List.filter (fun q => bv_eqb (fst q) a) maps = [(a, n)].
Proof.
  intros maps a n [Hnz Hun] Ha Hhas.
  pose proof (map_has_In maps a n Hhas) as Hin.
  assert (HinF : In (a, n) (List.filter (fun q => bv_eqb (fst q) a) maps)).
  { apply List.filter_In. split; [exact Hin|].
    cbn [fst]. apply bv_eqb_refl. }
  assert (Hown : forall e, In e (List.filter (fun q => bv_eqb (fst q) a) maps) ->
                           owns_b e (bv_unsigned a) = true).
  { intros [b s] He.
    apply List.filter_In in He as [He Hb]. cbn [fst] in Hb.
    apply bv_eqb_eq in Hb. subst b.
    unfold sizes_nonzero in Hnz. rewrite Forall_forall in Hnz.
    specialize (Hnz _ He). cbn [snd] in Hnz.
    apply owns_intro; [lia|].
    pose proof (word_range s). lia. }
  pose proof (owners_all_own (List.filter (fun q => bv_eqb (fst q) a) maps)
                (bv_unsigned a) Hown) as Hall.
  pose proof (owners_filter_le (fun q => bv_eqb (fst q) a) maps
                (bv_unsigned a)) as Hsplit.
  specialize (Hun (bv_unsigned a) Ha).
  assert (Hlen : (length (List.filter (fun q => bv_eqb (fst q) a) maps) <= 1)%nat).
  { rewrite <- Hall. exact (Nat.le_trans _ _ _ Hsplit Hun). }
  destruct (List.filter (fun q => bv_eqb (fst q) a) maps) as [|x [|y r]];
    cbn in Hlen; try lia.
  - contradiction.
  - destruct HinF as [->|[]]. reflexivity.
Qed.

(** …hence the size in a [map_has] hit is unique. *)
Corollary map_has_pins_size : forall maps a n1 n2,
  maps_wf maps -> bv_unsigned a mod page_size = 0 ->
  map_has maps a n1 = true -> map_has maps a n2 = true -> n1 = n2.
Proof.
  intros maps a n1 n2 Hwf Ha H1 H2.
  pose proof (base_entry_unique maps a n1 Hwf Ha H1) as E1.
  pose proof (map_has_In maps a n2 H2) as Hin2.
  assert (HinF : In (a, n2) (List.filter (fun q => bv_eqb (fst q) a) maps)).
  { apply List.filter_In. split; [exact Hin2|]. cbn [fst]. apply bv_eqb_refl. }
  rewrite E1 in HinF. destruct HinF as [Heq|[]].
  injection Heq. auto.
Qed.

Lemma live_bytes_filter_split : forall f maps,
  live_bytes maps
  = live_bytes (List.filter f maps)
    + live_bytes (List.filter (fun e => negb (f e)) maps).
Proof.
  induction maps as [|[a s] r IH]; cbn; [reflexivity|].
  destruct (f (a, s)); cbn; lia.
Qed.

(** The budget reading of the same fact: an exact [munmap] gives back
    exactly the bytes [map_has] matched, no more and no less. *)
Corollary munmap_returns_matched_bytes : forall maps a n,
  maps_wf maps -> bv_unsigned a mod page_size = 0 ->
  map_has maps a n = true ->
  live_bytes maps = bv_unsigned n + live_bytes (map_remove maps a).
Proof.
  intros maps a n Hwf Ha Hhas.
  pose proof (live_bytes_filter_split (fun q => bv_eqb (fst q) a) maps) as Hs.
  rewrite (base_entry_unique maps a n Hwf Ha Hhas) in Hs.
  cbn in Hs. unfold map_remove. lia.
Qed.

(* -------------------------------------------------------------------------
   PRESERVATION.  Every syscall that writes [vm_maps] keeps the invariant.
   ------------------------------------------------------------------------- *)

(** [m_vmmaps] and the setters are [simpl never] ([State.v]), so [cbn]
    has no handle on them; every one of these is [reflexivity] — the
    subsystem record is exactly what the setter builds — and they give
    [rewrite] one.  The backing wrappers matter here because the
    memory syscalls update the sparse-backing ledgers in the same
    step as [vm_maps], and none of those wrappers touches [vm_maps]. *)
Lemma vmm_vmmaps : forall h m, m_vmmaps (with_vmmaps h m) = h.
Proof. reflexivity. Qed.

Lemma vmm_backing : forall lz mt m,
  m_vmmaps (with_vm_backing lz mt m) = m_vmmaps m.
Proof. reflexivity. Qed.

Lemma vmm_forget_range : forall lo hi m,
  m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m.
Proof. reflexivity. Qed.

Lemma vmm_forget_ranges : forall rs m,
  m_vmmaps (forget_vm_ranges rs m) = m_vmmaps m.
Proof.
  induction rs as [|[a n] rs IH]; intros m; [reflexivity|].
  cbn [forget_vm_ranges]. rewrite IH. reflexivity.
Qed.

Lemma vmm_mmap_backing : forall flags a n m,
  m_vmmaps (with_mmap_backing flags a n m) = m_vmmaps m.
Proof.
  intros flags a n m. unfold with_mmap_backing.
  destruct (mmap_noreserve_b flags); reflexivity.
Qed.

Lemma vmm_mmap_replacement : forall flags a n m,
  m_vmmaps (with_mmap_replacement flags a n m) = m_vmmaps m.
Proof.
  intros flags a n m. unfold with_mmap_replacement.
  now rewrite vmm_mmap_backing.
Qed.

Lemma vmm_mmap_destroyed : forall a n h m,
  m_vmmaps (with_mmap_destroyed a n h m) = h.
Proof. reflexivity. Qed.

Lemma vmm_brk_next : forall m req r,
  m_vmmaps (with_brk_next m req r) = brk_model_next (m_vmmaps m) req r.
Proof.
  intros m req r. unfold with_brk_next.
  now rewrite vmm_forget_ranges, vmm_vmmaps.
Qed.

Lemma vmm_mprotect_next : forall m addr n,
  m_vmmaps (mprotect_model_next m addr n)
  = mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
      (maps_subtract (vm_noaccess (m_vmmaps m))
         (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
      (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m))
      (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m))
      (vm_init_sp (m_vmmaps m)).
Proof. reflexivity. Qed.

Lemma vmm_madvise_next : forall m addr n,
  m_vmmaps (madvise_dontneed_next m addr n) = m_vmmaps m.
Proof. reflexivity. Qed.

Lemma vmm_resize_backing : forall b old old_n dst new_n m,
  m_vmmaps (vm_resize_backing b old old_n dst new_n m) = m_vmmaps m.
Proof. reflexivity. Qed.

Lemma vmm_mremap_next : forall m old old_n dst new_n,
  m_vmmaps (mremap_model_next m old old_n dst new_n)
  = mremap_maps_next (m_vmmaps m) old dst new_n.
Proof.
  intros. unfold mremap_model_next.
  now rewrite vmm_resize_backing, vmm_vmmaps.
Qed.

Lemma vmm_fixed_rw_next : forall m addr n,
  vm_maps (mmap_fixed_rw_next (m_vmmaps m) addr n) = vm_maps (m_vmmaps m).
Proof. reflexivity. Qed.
Lemma w_is0_false : forall w, w_is0 w = false -> bv_unsigned w <> 0.
Proof.
  intros w H Hc. unfold w_is0 in H.
  assert (w = Z_to_bv 64 0) as ->.
  { apply bv_eq. rewrite Hc, u64 by lia. reflexivity. }
  rewrite bv_eqb_refl in H. discriminate.
Qed.

Lemma page_round_up_pos : forall z, 0 < z -> 0 < page_round_up_Z z.
Proof. intros z H. pose proof (page_round_up_Z_ge z ltac:(lia)). lia. Qed.

(** A grow resolution is gated: [brk_r_ok] can only admit a strictly
    higher break through the branch that evaluates [brk_grow_ok]. *)
Lemma brk_r_ok_grow : forall m req r,
  brk_r_ok m req r = true ->
  brk_is_grow req r (vm_brk (m_vmmaps m)) = true ->
  brk_grow_ok m req r = true.
Proof.
  intros m req r Hok Hgrow.
  unfold brk_is_grow in Hgrow.
  apply andb_true_iff in Hgrow as [Hgrow Hlt].
  apply andb_true_iff in Hgrow as [Hreq Hpos].
  apply Z.ltb_lt in Hlt. apply Z.ltb_lt in Hpos.
  apply negb_true_iff in Hreq.
  unfold brk_r_ok in Hok. cbv zeta in Hok.
  rewrite Hreq in Hok. cbn [orb] in Hok.
  destruct (bv_unsigned req <? bv_unsigned (min_brk (m_vmmaps m))) eqn:Emin.
  - apply bv_eqb_eq in Hok. subst r. lia.
  - destruct (bv_unsigned req <? bv_unsigned (vm_brk (m_vmmaps m))) eqn:Eshrink.
    + apply Z.ltb_lt in Eshrink.
      apply orb_true_iff in Hok as [Hok|Hok]; apply bv_eqb_eq in Hok; subst r; lia.
    + apply andb_true_iff in Hok as [_ Hok]. exact Hok.
Qed.

(** The heart of PART 2, and the exact mirror of PART 1: a brk grant may
    cover bytes the gate never tested, but every PAGE-ALIGNED byte it
    covers lies inside the range [region_free] did test. *)
Lemma brk_grant_wf : forall m req r,
  brk_r_ok m req r = true ->
  brk_is_grow req r (vm_brk (m_vmmaps m)) = true ->
  vm_wf (m_vmmaps m) ->
  maps_wf ((vm_brk (m_vmmaps m), (r - vm_brk (m_vmmaps m))%bv)
           :: vm_maps (m_vmmaps m)).
Proof.
  intros m req r Hok Hgrow Hwf. set (h := m_vmmaps m) in *.
  pose proof (brk_r_ok_grow m req r Hok Hgrow) as Hgok.
  unfold brk_is_grow in Hgrow.
  apply andb_true_iff in Hgrow as [Hgrow Hlt].
  apply andb_true_iff in Hgrow as [_ Hpos].
  apply Z.ltb_lt in Hlt. apply Z.ltb_lt in Hpos.
  pose proof (word_range r) as Hr. pose proof (word_range (vm_brk h)) as Hb.
  assert (Hsz : bv_unsigned (r - vm_brk h)%bv
                = bv_unsigned r - bv_unsigned (vm_brk h)).
  { rewrite bv_sub_unsigned. apply bv_wrap_small.
    change (bv_modulus 64) with (2 ^ 64). lia. }
  destruct Hwf as [Hnz Hun]. split.
  - constructor; [cbn [snd]; lia|exact Hnz].
  - intros p Hp. cbn [owners]. destruct (owns_b (vm_brk h, (r - vm_brk h)%bv) p) eqn:Ho.
    2:{ specialize (Hun p Hp). lia. }
    apply owns_true in Ho. cbn [fst snd] in Ho. rewrite Hsz in Ho.
    (* the gate ran, because a page-aligned byte of the grant is inside
       the ROUNDED range *)
    unfold brk_grow_ok in Hgok. cbv zeta in Hgok. fold h in Hgok.
    rewrite (proj2 (Z.ltb_lt 0 (bv_unsigned (vm_brk h))) Hpos) in Hgok.
    rewrite (proj2 (Z.ltb_lt (bv_unsigned (vm_brk h)) (bv_unsigned r)) Hlt)
      in Hgok.
    cbn [andb] in Hgok. apply andb_true_iff in Hgok as [Hgok _].
    set (lo := page_round_up_Z (bv_unsigned (vm_brk h))) in *.
    set (hi := page_round_up_Z (bv_unsigned r)) in *.
    assert (Hlop : lo <= p)
      by (apply page_round_up_Z_le_aligned; [exact Hp|lia]).
    assert (Hphi : p < hi).
    { pose proof (page_round_up_Z_ge (bv_unsigned r) ltac:(lia)). lia. }
    rewrite (proj2 (Z.ltb_lt lo hi) ltac:(lia)) in Hgok.
    apply andb_true_iff in Hgok as [Hceil Hfree].
    apply Z.leb_le in Hceil.
    alloc_top_bounds. unfold two_pow_64 in *.
    assert (Hlo0 : 0 <= lo) by (apply page_round_up_Z_nonneg; lia).
    assert (Hps : 0 < page_size) by (unfold page_size; lia).
    pose proof (alloc_top_page_lt h) as Hacp. unfold two_pow_64 in Hacp.
    assert (Hown : owns_b (Z_to_bv 64 lo, Z_to_bv 64 (hi + page_size - lo)) p
                   = true).
    { apply owns_intro; rewrite !u64 by lia; lia. }
    rewrite (region_free_no_owner (vm_maps h) _ _ p
               (region_free_app_r _ _ _ _ Hfree) Hown).
    lia.
Qed.

Lemma brk_model_next_wf : forall m req r,
  brk_r_ok m req r = true -> vm_wf (m_vmmaps m) ->
  vm_wf (brk_model_next (m_vmmaps m) req r).
Proof.
  intros m req r Hok Hwf. set (h := m_vmmaps m) in *.
  unfold vm_wf, brk_model_next, brk_maps_next. cbn [vm_maps].
  destruct (Z.ltb 0 (bv_unsigned (vm_brk h))
            && Z.ltb (bv_unsigned r) (bv_unsigned (vm_brk h))) eqn:Eshrink.
  - apply andb_true_iff in Eshrink as [_ Hlt]. apply Z.ltb_lt in Hlt.
    pose proof (word_range r). pose proof (word_range (vm_brk h)).
    apply maps_wf_subtract; try lia. exact Hwf.
  - unfold brk_grants. destruct (brk_is_grow req r (vm_brk h)) eqn:Egrow.
    + cbn [app]. now apply (brk_grant_wf m req r).
    + cbn [app]. exact Hwf.
Qed.

Lemma check_brk_preserves : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs ->
  vm_wf (m_vmmaps m) -> vm_wf (m_vmmaps m').
Proof.
  intros req [ret ws zs us cs ci] m m' evs H Hwf.
  unfold check_brk in H.
  destruct ws as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct ci as [|? ?]; [|discriminate].
  destruct (brk_r_ok m req ret
            && listNN_eqb zs (brk_zeros req ret (vm_brk (m_vmmaps m)))
            && listNN_eqb us (brk_unmaps ret (vm_brk (m_vmmaps m)))) eqn:E;
    [|discriminate].
  injection H as <- <-.
  apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E _].
  rewrite vmm_brk_next. now apply brk_model_next_wf.
Qed.

Lemma check_ret_only_model : forall eff r mm evs0 m' evs,
  check_ret_only eff r mm evs0 = CheckOk m' evs -> m' = mm.
Proof.
  intros [ret ws zs us cs ci] r mm evs0 m' evs H. unfold check_ret_only in H.
  destruct ws, zs, us, cs, ci; try discriminate.
  destruct (bv_eqb ret r); [|discriminate]. injection H as <- <-. reflexivity.
Qed.

(** The copyin wrappers ([Checks/Sys/Prelude.v]) sit between an arm and
    its answer.  Neither changes the model: [check_ret_only_copyins]
    hands back the model [check_ret_only] was given, and the other two
    pass a result through unchanged. *)
Lemma check_ret_only_copyins_model : forall reads eff r mm evs0 m' evs,
  check_ret_only_copyins reads eff r mm evs0 = CheckOk m' evs -> m' = mm.
Proof.
  intros reads eff r mm evs0 m' evs H.
  unfold check_ret_only_copyins in H.
  destruct (check_ret_only (clear_copyins eff) r mm evs0) eqn:E;
    try discriminate.
  destruct (access_ranges_eqb (eff_copyins eff) reads); [|discriminate].
  inversion H; subst. eapply check_ret_only_model. exact E.
Qed.

(** Three wrappers hand a result straight back once the copy-in ranges
    the arm declared match the ones observed: [check_copyins],
    [check_copyin_prefix] and [check_copyins_after], all three in
    [Checks/Sys/Prelude.v].  None of them touches the model, so a
    success under one is a success under what it wraps. *)
Lemma check_copyins_model : forall reads eff res m' evs,
  check_copyins reads eff res = CheckOk m' evs -> res = CheckOk m' evs.
Proof.
  intros reads eff res m' evs H. unfold check_copyins in H.
  destruct (access_ranges_eqb (eff_copyins eff) reads); [exact H|discriminate].
Qed.

Lemma check_copyin_prefix_model : forall reads eff res m' evs,
  check_copyin_prefix reads eff res = CheckOk m' evs -> res = CheckOk m' evs.
Proof.
  intros reads eff res m' evs H. unfold check_copyin_prefix in H.
  destruct res as [m0 evs0| |];
    destruct (access_ranges_eqb (firstn (length reads) (eff_copyins eff)) reads);
    solve [exact H | discriminate].
Qed.

Lemma check_copyins_after_model : forall reads eff res m' evs,
  Prelude.check_copyins_after reads eff res = CheckOk m' evs ->
  res = CheckOk m' evs.
Proof.
  intros reads eff res m' evs H.
  unfold Prelude.check_copyins_after, check_copyins in H.
  destruct res as [m0 evs0| |];
    destruct (access_ranges_eqb (eff_copyins eff) reads);
    solve [exact H | discriminate].
Qed.

(** Pull the [if] the checker is sitting on out of a hypothesis, with a
    generated name ([dif]) or a chosen one ([difn]). *)
Ltac dif H := match type of H with
              | context [ if ?b then _ else _ ] =>
                  let E := fresh "E" in destruct b eqn:E
              end.
Ltac difn H E := match type of H with
                 | context [ if ?b then _ else _ ] => destruct b eqn:E
                 end.

Lemma check_munmap_preserves : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs ->
  vm_wf (m_vmmaps m) -> vm_wf (m_vmmaps m').
Proof.
  intros addr len [ret ws zs us cs ci] m m' evs H Hwf.
  unfold check_munmap in H. cbv zeta in H.
  dif H; [apply check_ret_only_model in H; subst m'; exact Hwf|].
  dif H; [apply check_ret_only_model in H; subst m'; exact Hwf|].
  dif H.
  - destruct ws, zs, cs, ci; try discriminate.
    dif H; [|discriminate]. injection H as <- <-.
    unfold vm_wf. rewrite vmm_mmap_destroyed. cbn [vm_maps].
    now apply maps_wf_filter.
  - dif H; [apply check_ret_only_model in H; subst m'; exact Hwf|discriminate].
Qed.

Lemma check_mprotect_preserves : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs ->
  vm_wf (m_vmmaps m) -> vm_wf (m_vmmaps m').
Proof.
  intros addr len prot [ret ws zs us cs ci] m m' evs H Hwf.
  unfold check_mprotect in H. cbv zeta in H.
  dif H; [apply check_ret_only_model in H; subst m'; exact Hwf|].
  dif H; [apply check_ret_only_model in H; subst m'; exact Hwf|].
  dif H; [apply check_ret_only_model in H; subst m'; exact Hwf|].
  dif H; [apply check_ret_only_model in H; subst m'; exact Hwf|].
  dif H; [discriminate|].
  dif H.
  - destruct ws, us, cs, ci; try discriminate.
    dif H.
    + destruct zs; [|discriminate]. injection H as <- <-. exact Hwf.
    + dif H; [|discriminate]. injection H as <- <-.
      unfold vm_wf. rewrite vmm_mprotect_next. cbn [vm_maps]. exact Hwf.
  - dif H; [|discriminate].
    destruct ws, zs, us, cs, ci; try discriminate.
    dif H; [|discriminate]. injection H as <- <-. exact Hwf.
Qed.

(** [madvise] never touches [vm_maps]: its one state change is to the
    materialized-page ledger ([Madvise.madvise_dontneed_next]), so the
    frame form is the whole statement. *)
Lemma check_madvise_frame : forall addr len advice eff m m' evs,
  check_madvise addr len advice eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros addr len advice [ret ws zs us cs ci] m m' evs H.
  unfold check_madvise in H. cbv zeta in H.
  dif H; [apply check_ret_only_model in H; subst m'; reflexivity|].
  dif H; [discriminate|].
  dif H; [apply check_ret_only_model in H; subst m'; reflexivity|].
  dif H; [apply check_ret_only_model in H; subst m'; reflexivity|].
  dif H; [|discriminate].
  destruct ws, us, cs, ci; try discriminate.
  dif H; [|discriminate]. injection H as <- <-. apply vmm_madvise_next.
Qed.

Lemma check_mmap_preserves : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs ->
  vm_wf (m_vmmaps m) -> vm_wf (m_vmmaps m').
Proof.
  intros addr len prot flags fd off [ret ws zs us cs ci] m m' evs H Hwf.
  unfold check_mmap in H. cbv zeta in H.
  pose proof (alloc_top_lt (m_vmmaps m)) as Hac. unfold two_pow_64 in Hac.
  pose proof (word_range len) as Hlenr.
  pose proof (word_range addr) as Haddrr.
  destruct (negb (mmap_off_aligned_b off)) eqn:Eoff.
  { destruct (mmap_pglen_ok_b len); [|discriminate].
    apply check_ret_only_model in H; subst m'; exact Hwf. }
  destruct (negb (mmap_anon_b flags)) eqn:Eanon; [discriminate|].
  destruct (w_is0 len) eqn:Elen.
  { destruct (mmap_plain_anon_b flags); [|discriminate].
    apply check_ret_only_model in H; subst m'; exact Hwf. }
  pose proof (w_is0_false len Elen) as Hlen0.
  assert (HnZ : 0 < page_round_up_Z (bv_unsigned len))
    by (apply page_round_up_pos; lia).
  (* the placed shapes: the grant is exactly what [region_free] accepted *)
  destruct (mmap_modeled_b prot flags off) eqn:Emod.
  { destruct ws, us, cs, ci; try discriminate.
    destruct (errno_ret_in mmap_errnos ret).
    { destruct zs; [|discriminate]. injection H as <- <-. exact Hwf. }
    (* SIX conjuncts, left associated: alignment, positivity, the
       ceiling, [region_free], [mmap_noreserve_backed_ok] and the
       [listNN_eqb] on the grant list.  Only [region_free] and the
       ceiling are used below; the rest are peeled to reach them. *)
    difn H E; [|discriminate]. injection H as <- <-.
    unfold vm_wf. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
    apply andb_true_iff in E as [E Hzs].
    apply andb_true_iff in E as [E Hbud].
    apply andb_true_iff in E as [E Hfree].
    apply andb_true_iff in E as [E Hceil].
    apply andb_true_iff in E as [Halign Hpos].
    apply Z.leb_le in Hceil. apply Z.ltb_lt in Hpos.
    apply maps_wf_cons_free.
    - exact Hwf.
    - rewrite u64 by lia. lia.
    - exact (region_free_app_r _ _ _ _ Hfree). }
  destruct (mmap_noaccess_b prot flags off) eqn:Enoa.
  { destruct ws, zs, cs, ci; try discriminate.
    destruct (errno_ret_in mmap_errnos ret).
    { destruct us; [|discriminate]. injection H as <- <-. exact Hwf. }
    (* FIVE here: the noaccess grant carries no
       [mmap_noreserve_backed_ok] conjunct, because it reserves no
       backing. *)
    difn H E; [|discriminate]. injection H as <- <-.
    unfold vm_wf. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
    apply andb_true_iff in E as [E Hus].
    apply andb_true_iff in E as [E Hfree].
    apply andb_true_iff in E as [E Hceil].
    apply andb_true_iff in E as [Halign Hpos].
    apply Z.leb_le in Hceil. apply Z.ltb_lt in Hpos.
    apply maps_wf_cons_free.
    - exact Hwf.
    - rewrite u64 by lia. lia.
    - exact (region_free_app_r _ _ _ _ Hfree). }
  (* the two MAP_FIXED shapes.  Each takes the same four early exits and
     then splits on whether the request names a live mapping (which it
     replaces, leaving [vm_maps] alone or subtracting from it) or free
     address space (which it grants, exactly where [region_free]
     accepted). *)
  destruct (mmap_fixed_noaccess_b prot flags off) eqn:Efix.
  { difn H Enomem; [apply check_ret_only_model in H; subst m'; exact Hwf|].
    difn H Eceil; [discriminate|].
    difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hwf|].
    difn H Epos; [discriminate|].
    apply negb_false_iff, Z.leb_le in Eceil.
    difn H Elive.
    - destruct ws, zs, cs, ci; try discriminate.
      destruct (errno_ret_in mmap_errnos ret).
      + destruct us.
        * injection H as <- <-. exact Hwf.
        * difn H Eus; [|discriminate]. injection H as <- <-.
          unfold vm_wf. rewrite vmm_mmap_destroyed. cbn [vm_maps].
          apply maps_wf_subtract; try (rewrite u64 by lia); try lia. exact Hwf.
      + difn H Eok; [|discriminate]. injection H as <- <-.
        unfold vm_wf. rewrite vmm_mmap_replacement, vmm_vmmaps. cbn [vm_maps].
        exact Hwf.
    - difn H Efree.
      + destruct ws, zs, cs, ci; try discriminate.
        destruct (errno_ret_in mmap_errnos ret).
        * destruct us; [|discriminate]. injection H as <- <-. exact Hwf.
        * difn H Eok; [|discriminate]. injection H as <- <-.
          unfold vm_wf. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
          apply maps_wf_cons_free.
          -- exact Hwf.
          -- rewrite u64 by lia. lia.
          -- exact (region_free_app_r _ _ _ _ Efree).
      (* SPANNING: the success conses the request onto the subtraction,
         which [maps_subtract_region_free] says it is disjoint from. *)
      + difn H Espan; [|discriminate].
        destruct ws, zs, cs, ci; try discriminate.
        destruct (errno_ret_in mmap_errnos ret).
        * destruct us.
          -- injection H as <- <-. exact Hwf.
          -- difn H Eus; [|discriminate]. injection H as <- <-.
             unfold vm_wf. rewrite vmm_mmap_destroyed. cbn [vm_maps].
             apply maps_wf_subtract; try (rewrite u64 by lia); try lia.
             exact Hwf.
        * difn H Eok; [|discriminate]. injection H as <- <-.
          unfold vm_wf. rewrite vmm_mmap_replacement, vmm_vmmaps.
          cbn [vm_maps mmap_fixed_noaccess_span_next].
          apply maps_wf_cons_free.
          -- apply maps_wf_subtract; try (rewrite u64 by lia); try lia.
             exact Hwf.
          -- rewrite u64 by lia. lia.
          -- apply maps_subtract_region_free. rewrite u64 by lia. lia. }
  destruct (mmap_fixed_rw_b prot flags off) eqn:Efixrw.
  2: {
    (* the two MAP_FIXED_NOREPLACE shapes: the same four early exits,
       then ONE split on the ledger — a free range is granted exactly
       where [region_free] accepted, an occupied one is refused with
       [vm_maps] untouched. *)
    destruct (mmap_noreplace_noaccess_b prot flags off) eqn:Enrn.
    { difn H Enomem; [apply check_ret_only_model in H; subst m'; exact Hwf|].
      difn H Eceil; [discriminate|].
      difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hwf|].
      difn H Epos; [discriminate|].
      apply negb_false_iff, Z.leb_le in Eceil.
      difn H Efree.
      - destruct ws, zs, cs, ci; try discriminate.
        destruct (errno_ret_in mmap_errnos ret).
        + destruct us; [|discriminate]. injection H as <- <-. exact Hwf.
        + difn H Eok; [|discriminate]. injection H as <- <-.
          unfold vm_wf. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
          apply maps_wf_cons_free.
          * exact Hwf.
          * rewrite u64 by lia. lia.
          * exact (region_free_app_r _ _ _ _ Efree).
      - destruct ws, zs, us, cs, ci; try discriminate.
        difn H Eerr; [|discriminate]. injection H as <- <-. exact Hwf. }
    destruct (mmap_noreplace_rw_b prot flags off) eqn:Enrr; [|discriminate].
    difn H Enomem; [apply check_ret_only_model in H; subst m'; exact Hwf|].
    difn H Eceil; [discriminate|].
    difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hwf|].
    difn H Epos; [discriminate|].
    apply negb_false_iff, Z.leb_le in Eceil.
    difn H Efree.
    - destruct ws, us, cs, ci; try discriminate.
      destruct (errno_ret_in mmap_errnos ret).
      + destruct zs; [|discriminate]. injection H as <- <-. exact Hwf.
      + difn H Eok; [|discriminate]. injection H as <- <-.
        unfold vm_wf. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
        apply maps_wf_cons_free.
        * exact Hwf.
        * rewrite u64 by lia. lia.
        * exact (region_free_app_r _ _ _ _ Efree).
    - destruct ws, zs, us, cs, ci; try discriminate.
      difn H Eerr; [|discriminate]. injection H as <- <-. exact Hwf. }
  difn H Enomem; [apply check_ret_only_model in H; subst m'; exact Hwf|].
  difn H Eceil; [discriminate|].
  difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hwf|].
  difn H Epos; [discriminate|].
  apply negb_false_iff, Z.leb_le in Eceil.
  difn H Elive.
  - destruct ws, cs, ci; try discriminate.
    destruct (errno_ret_in mmap_errnos ret).
    + destruct zs; [|discriminate]. destruct us.
      * injection H as <- <-. exact Hwf.
      * difn H Eus; [|discriminate]. injection H as <- <-.
        unfold vm_wf. rewrite vmm_mmap_destroyed. cbn [vm_maps].
        apply maps_wf_subtract; try (rewrite u64 by lia); try lia. exact Hwf.
    + destruct us; [|discriminate].
      difn H Eok; [|discriminate]. injection H as <- <-.
      unfold vm_wf. rewrite vmm_mmap_replacement, vmm_vmmaps.
      rewrite vmm_fixed_rw_next. exact Hwf.
  - difn H Efree.
    + destruct ws, us, cs, ci; try discriminate.
      destruct (errno_ret_in mmap_errnos ret).
      * destruct zs; [|discriminate]. injection H as <- <-. exact Hwf.
      * difn H Eok; [|discriminate]. injection H as <- <-.
        unfold vm_wf. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
        apply maps_wf_cons_free.
        -- exact Hwf.
        -- rewrite u64 by lia. lia.
        -- exact (region_free_app_r _ _ _ _ Efree).
    (* SPANNING, the rw half: same shape as its PROT_NONE twin above. *)
    + difn H Espan; [|discriminate].
      destruct ws, cs, ci; try discriminate.
      destruct (errno_ret_in mmap_errnos ret).
      * destruct zs; [|discriminate]. destruct us.
        -- injection H as <- <-. exact Hwf.
        -- difn H Eus; [|discriminate]. injection H as <- <-.
           unfold vm_wf. rewrite vmm_mmap_destroyed. cbn [vm_maps].
           apply maps_wf_subtract; try (rewrite u64 by lia); try lia.
           exact Hwf.
      * destruct us; [|discriminate].
        difn H Eok; [|discriminate]. injection H as <- <-.
        unfold vm_wf. rewrite vmm_mmap_replacement, vmm_vmmaps.
        cbn [vm_maps mmap_fixed_rw_span_next].
        apply maps_wf_cons_free.
        -- apply maps_wf_subtract; try (rewrite u64 by lia); try lia.
           exact Hwf.
        -- rewrite u64 by lia. lia.
        -- apply maps_subtract_region_free. rewrite u64 by lia. lia.
Qed.

Lemma check_mremap_preserves : forall old old_size new_size flags eff m m' evs,
  check_mremap old old_size new_size flags eff m = CheckOk m' evs ->
  vm_wf (m_vmmaps m) -> vm_wf (m_vmmaps m').
Proof.
  intros old old_size new_size flags [ret ws zs us cs ci] m m' evs H Hwf.
  unfold check_mremap in H. cbv zeta in H.
  pose proof (alloc_top_lt (m_vmmaps m)) as Hac. unfold two_pow_64 in Hac.
  pose proof (word_range old) as Hor.
  pose proof (word_range old_size) as Hos.
  pose proof (word_range new_size) as Hns.
  difn H Eflag; [discriminate|].
  difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hwf|].
  difn H Enew; [apply check_ret_only_model in H; subst m'; exact Hwf|].
  difn H Etask; [apply check_ret_only_model in H; subst m'; exact Hwf|].
  difn H Eold; [discriminate|].
  difn H Esrc; [discriminate|].
  difn H Eeq; [apply check_ret_only_model in H; subst m'; exact Hwf|].
  destruct ws; [|discriminate]. destruct ci; [|discriminate].
  (* the new length is a nonzero number of pages *)
  unfold page_align_is0_b in Enew. apply orb_false_iff in Enew as [Enew0 EnewB].
  apply Z.leb_gt in EnewB.
  pose proof (w_is0_false new_size Enew0) as Hnew0.
  assert (HnewZ : 0 < page_round_up_Z (bv_unsigned new_size))
    by (apply page_round_up_pos; lia).
  (* the source is a live entry, and its size fits in a word *)
  apply negb_false_iff in Esrc.
  (* the backing-uniformity conjunct is about the sparse ledgers, not
     about [vm_maps]; the ownership conjuncts are what this needs *)
  apply andb_true_iff in Esrc as [Esrc _].
  unfold mremap_source_b in Esrc.
  apply andb_true_iff in Esrc as [Esrc _].
  apply andb_true_iff in Esrc as [Esrc Hhas].
  apply andb_true_iff in Esrc as [Hoceil _].
  apply Z.leb_le in Hoceil.
  assert (HoldZ : 0 <= page_round_up_Z (bv_unsigned old_size))
    by (apply page_round_up_Z_nonneg; lia).
  destruct (errno_ret_in mremap_errnos ret).
  { destruct zs, us, cs; try discriminate. injection H as <- <-. exact Hwf. }
  destruct (bv_eqb ret old).
  - difn H Eshrink.
    + difn H Eok; [|discriminate]. injection H as <- <-.
      apply Z.ltb_lt in Eshrink.
      unfold vm_wf. rewrite vmm_mremap_next.
      unfold mremap_maps_next. cbn [vm_maps].
      apply (maps_wf_cons_sub _ _ (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))).
      * exact Hwf.
      * rewrite u64 by lia. lia.
      * apply map_has_In. exact Hhas.
      * rewrite !u64 by lia. lia.
    + difn H Egrow; [|discriminate].
      difn H Eok; [|discriminate]. injection H as <- <-.
      unfold vm_wf. rewrite vmm_mremap_next.
      unfold mremap_maps_next. cbn [vm_maps].
      unfold mremap_inplace_grow_b in Egrow. cbv zeta in Egrow.
      apply andb_true_iff in Egrow as [Egrow _].
      apply andb_true_iff in Egrow as [Hgceil Hgfree].
      apply Z.leb_le in Hgceil.
      apply maps_wf_cons_free.
      * now apply maps_wf_filter.
      * rewrite u64 by lia. lia.
      * exact (region_free_app_r _ _ _ _ Hgfree).
  - difn H Emove; [|discriminate]. injection H as <- <-.
    unfold vm_wf. rewrite vmm_mremap_next.
    unfold mremap_maps_next. cbn [vm_maps].
    apply andb_true_iff in Emove as [Emove _].
    apply andb_true_iff in Emove as [Emove _].
    apply andb_true_iff in Emove as [Emove _].
    apply andb_true_iff in Emove as [_ Hfresh].
    (* SIX conjuncts: destination distinct from the source, aligned,
       positive, under the ceiling, [region_free] and the final budget.
       Peeled from the right down to the ceiling and [region_free],
       which are the two this proof uses.  The count is the predicate's,
       not this comment's: peel one too many and the [Z.leb_le] below
       lands on the positivity conjunct and the proof stops. *)
    unfold mremap_fresh_b in Hfresh. cbv zeta in Hfresh.
    apply andb_true_iff in Hfresh as [Hfresh _].
    apply andb_true_iff in Hfresh as [Hfresh Hffree].
    apply andb_true_iff in Hfresh as [Hfresh Hfceil].
    apply andb_true_iff in Hfresh as [_ Hfpos].
    apply Z.leb_le in Hfceil. apply Z.ltb_lt in Hfpos.
    apply maps_wf_cons_free.
    + now apply maps_wf_filter.
    + rewrite u64 by lia. lia.
    + apply region_free_filter. exact (region_free_app_r _ _ _ _ Hffree).
Qed.

(* -------------------------------------------------------------------------
   FRAME.  Every other modeled syscall leaves [vm_maps] alone, so the
   invariant survives the whole dispatcher rather than five of its arms.
   ------------------------------------------------------------------------- *)

Ltac vm_step H :=
  match type of H with
  | CheckReject = CheckOk _ _ => discriminate H
  | CheckUnmodeled = CheckOk _ _ => discriminate H
  | CheckOk _ _ = CheckOk _ _ => injection H as <- <-
  | check_ret_only _ _ _ _ = CheckOk _ _ =>
      apply check_ret_only_model in H; subst
  | check_ret_only_copyins _ _ _ _ _ = CheckOk _ _ =>
      apply check_ret_only_copyins_model in H; subst
  | Prelude.check_copyins_after _ _ _ = CheckOk _ _ =>
      apply check_copyins_after_model in H
  | check_copyin_prefix _ _ _ = CheckOk _ _ =>
      apply check_copyin_prefix_model in H
  | check_copyins _ _ _ = CheckOk _ _ => apply check_copyins_model in H
  | context [ if ?b then _ else _ ] => destruct b eqn:?
  | context [ match ?x with _ => _ end ] => destruct x eqn:?
  end.

(** Every setter builds its own subsystem record and carries the rest
    across, so [m_vmmaps] of any stack of them is [m_vmmaps] of the base
    BY CONVERSION.  [reflexivity] therefore closes these where [cbn]
    cannot: [State.v] declares the accessors and setters [simpl never]. *)
Ltac vm_frame H := repeat vm_step H; reflexivity.

Lemma check_efault_or_frame : forall fb eff m m' evs,
  check_efault_or fb eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof. intros fb eff m m' evs H. unfold check_efault_or in H. vm_frame H. Qed.

Lemma check_readv_gap_frame : forall m' evs,
  check_readv_gap = CheckOk m' evs -> False.
Proof. intros m' evs H. unfold check_readv_gap in H. discriminate. Qed.

Lemma check_open_result_frame : forall eff m mk m' evs,
  (forall fd, m_vmmaps (mk fd) = m_vmmaps m) ->
  check_open_result eff m mk = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof.
  intros eff m mk m' evs Hmk H.
  unfold check_open_result, check_new_fd_result in H.
  repeat vm_step H; try apply Hmk; reflexivity.
Qed.

Ltac vm_done H :=
  first
  [ apply check_efault_or_frame in H; exact H
  | elim (check_readv_gap_frame _ _ H)
  | (eapply check_open_result_frame in H;
     [exact H | intros; reflexivity]) ].

Ltac vm_frame2 H :=
  repeat (vm_step H || vm_done H); try reflexivity.

Lemma check_read_frame : forall i fd buf count eff m m' evs,
  check_read i fd buf count eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof.
  intros i fd buf count eff m m' evs H.
  unfold check_read, check_read_urandom, check_socket_pending_error,
    check_access_ok_zero in H.
  cbv zeta in H. vm_frame2 H.
Qed.

Lemma check_write_frame : forall i fd buf count eff m m' evs,
  check_write i fd buf count eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof.
  intros i fd buf count eff m m' evs H.
  unfold check_write, check_access_ok_zero in H. vm_frame2 H.
Qed.

(** A positional transfer touches no mapping.  [check_pread64] returns
    the model it was given — a pread advances no offset — and
    [check_pwrite64] returns [with_fs] over it, which carries the VM
    subsystem across untouched. *)
Lemma check_pread64_frame : forall i fd buf count pos eff m m' evs,
  check_pread64 i fd buf count pos eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i fd buf count pos eff m m' evs H.
  unfold check_pread64, check_read_urandom in H. cbv zeta in H. vm_frame2 H.
Qed.

Lemma check_pwrite64_frame : forall i fd buf count pos eff m m' evs,
  check_pwrite64 i fd buf count pos eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i fd buf count pos eff m m' evs H.
  unfold check_pwrite64 in H. vm_frame2 H.
Qed.

Lemma check_openat_frame : forall i dirfd pathp flags eff m m' evs,
  check_openat i dirfd pathp flags eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  (* openat's body and its copy-in wrapper are [Local] to
     [Checks/Sys/Fs/Open.v]; nothing they do reaches the address
     space, and naming them here is what lets [vm_frame2] see that. *)
  unfold check_openat, Open.check_openat_body, Open.check_openat_resolved,
    Open.check_openat_sep, Open.check_openat_localtime,
    Open.check_openat_devnull, Open.check_open_devnull,
    Open.check_openat_urandom, Open.check_open_urandom,
    Open.check_openat_tmp,
    Open.check_openat_read, Open.check_openat_create, Open.check_openat_excl,
    Open.check_openat_dir, Open.check_openat_append,
    Open.check_openat_rdwr, Open.check_openat_rdwr_excl,
    check_create_wronly, check_open_append, check_open_rdwr in H.
  vm_frame2 H.
Qed.

Lemma check_close_frame : forall fd eff m m' evs,
  check_close fd eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof. intros fd eff m m' evs H. unfold check_close in H. vm_frame2 H. Qed.

Lemma check_lseek_frame : forall fd off whence eff m m' evs,
  check_lseek fd off whence eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof.
  intros fd off whence eff m m' evs H. unfold check_lseek in H. vm_frame2 H.
Qed.

Lemma check_getcwd_frame : forall size eff m m' evs,
  check_getcwd size eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof.
  intros size eff m m' evs H. unfold check_getcwd in H. vm_frame2 H.
Qed.

Lemma check_getrandom_frame : forall i buf cap flags eff m m' evs,
  check_getrandom i buf cap flags eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i buf cap flags eff m m' evs H.
  unfold check_getrandom, check_getrandom_zero in H. vm_frame2 H.
Qed.

Lemma check_readlinkat_frame : forall dirfd eff m m' evs,
  check_readlinkat dirfd eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof.
  intros dirfd eff m m' evs H. unfold check_readlinkat in H. vm_frame2 H.
Qed.

Lemma check_exit_frame : forall code eff m m' evs,
  check_exit code eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof. intros code eff m m' evs H. unfold check_exit in H. vm_frame2 H. Qed.

Lemma check_set_tid_address_frame : forall eff m m' evs,
  check_set_tid_address eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof.
  intros eff m m' evs H. unfold check_set_tid_address in H. vm_frame2 H.
Qed.

Lemma check_ioctl_frame : forall fd req eff m m' evs,
  check_ioctl fd req eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof. intros fd req eff m m' evs H. unfold check_ioctl in H. vm_frame2 H. Qed.

Lemma check_writev_frame : forall i fd iov iovcnt eff m m' evs,
  check_writev i fd iov iovcnt eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i fd iov iovcnt eff m m' evs H.
  unfold check_writev in H. vm_frame2 H.
Qed.

Lemma check_readv_imported_frame : forall i fd r iovs0 eff m m' evs,
  check_readv_imported i fd r iovs0 eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i fd r iovs0 eff m m' evs H.
  unfold check_readv_imported in H.
  vm_frame2 H.
Qed.

Lemma check_readv_frame : forall i fd iov iovcnt eff m m' evs,
  check_readv i fd iov iovcnt eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i fd iov iovcnt eff m m' evs H.
  unfold check_readv in H.
  repeat (vm_step H || vm_done H
          || (apply check_readv_imported_frame in H; exact H));
  try reflexivity.
Qed.

(** The rest of the dispatcher.  These arms touch fds, the file system
    or the core-limit pin, never the address space, so each one is the
    same mechanical [vm_frame2]. *)

Lemma check_wait4_frame : forall i upid stat_addr options rusage eff m m' evs,
  check_wait4 i upid stat_addr options rusage eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i upid stat_addr options rusage eff m m' evs H.
  unfold check_wait4 in H. vm_frame2 H.
Qed.

Lemma check_epoll_create1_frame : forall flags32 eff m m' evs,
  check_epoll_create1 flags32 eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof.
  intros flags32 eff m m' evs H. unfold check_epoll_create1 in H. vm_frame2 H.
Qed.

Lemma check_epoll_ctl_frame : forall i epfd op32 tfd event eff m m' evs,
  check_epoll_ctl i epfd op32 tfd event eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i epfd op32 tfd event eff m m' evs H.
  unfold check_epoll_ctl in H. vm_frame2 H.
Qed.

Lemma check_epoll_pwait_frame :
  forall i epfd events maxevents32 sigmask sigsetsize eff m m' evs,
  check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m
    = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i epfd events maxevents32 sigmask sigsetsize eff m m' evs H.
  unfold check_epoll_pwait in H. vm_frame2 H.
Qed.

Lemma check_fsync_frame : forall fd eff m m' evs,
  check_fsync fd eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof. intros fd eff m m' evs H. unfold check_fsync in H. vm_frame2 H. Qed.

Lemma check_getdents64_frame : forall fd count eff m m' evs,
  check_getdents64 fd count eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof.
  intros fd count eff m m' evs H. unfold check_getdents64 in H. vm_frame2 H.
Qed.

(** [flock] records nothing: every answered arm is a bare return, and
    the arms that would need state decline.  So a [*_frame] rather than
    a [*_preserves], and the same mechanical [vm_frame2]. *)
Lemma check_flock_frame : forall fd cmd eff m m' evs,
  check_flock fd cmd eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof.
  intros fd cmd eff m m' evs H. unfold check_flock in H. vm_frame2 H.
Qed.

(** [timerfd_create] allocates no descriptor here -- its only answer is
    the -EINVAL it decides from its two arguments -- so it touches no
    field of the model at all, [m_vmmaps] included.  A [*_frame] rather
    than a [*_preserves]: nothing is written for [vm_wf] to be
    re-established over.  This stops being the right shape if the arm
    ever grows the success branch [Sys/Fs/Timerfd] declines, but not
    because of memory: a descriptor lands in [m_fds], which this theorem
    does not quantify over. *)
Lemma check_timerfd_create_frame : forall clkid flags eff m m' evs,
  check_timerfd_create clkid flags eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros clkid flags eff m m' evs H.
  unfold check_timerfd_create in H. vm_frame2 H.
Qed.

(** [eventfd2] is [timerfd_create]'s twin here for the same reason: its
    only answer is the -EINVAL it decides from the flag word alone, and
    Linux decides it before the [kmalloc], so the arm touches no field
    of the model, [m_vmmaps] included.  A [*_frame] rather than a
    [*_preserves]: nothing is written for [vm_wf] to be re-established
    over. *)
Lemma check_eventfd2_frame : forall flags eff m m' evs,
  check_eventfd2 flags eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros flags eff m m' evs H.
  unfold check_eventfd2 in H. vm_frame2 H.
Qed.

(** uname writes only the UTS-name pin, which lives in [ProcState]:
    [State.with_utsname] rebuilds that record and carries the VM
    subsystem across untouched. *)
Lemma check_uname_frame : forall i name eff m m' evs,
  check_uname i name eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i name eff m m' evs H.
  unfold check_uname, check_uname_copy in H. vm_frame2 H.
Qed.

Lemma check_prlimit64_frame :
  forall i pid resource new_rlim old_rlim eff m m' evs,
  check_prlimit64 i pid resource new_rlim old_rlim eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i pid resource new_rlim old_rlim eff m m' evs H.
  unfold check_prlimit64, check_rlim64_read in H. vm_frame2 H.
Qed.

Lemma check_ftruncate_frame : forall fd len eff m m' evs,
  check_ftruncate fd len eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof.
  intros fd len eff m m' evs H. unfold check_ftruncate in H. vm_frame2 H.
Qed.

(** [check_getpid] IS [check_set_tid_address] ([Checks/Sys/Kernel/Sys.v]:
    both accept only the bare return).  Named separately so the
    enumeration below stays one line per dispatcher arm. *)
Lemma check_getpid_frame : forall eff m m' evs,
  check_getpid eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof. exact check_set_tid_address_frame. Qed.

(** ...and so is [check_gettid].  Named separately for the same reason:
    the enumeration below stays one line per dispatcher arm, so a new
    arm that forgot its frame lemma is a missing line rather than a
    silent reuse of another syscall's. *)
Lemma check_gettid_frame : forall eff m m' evs,
  check_gettid eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof. exact check_set_tid_address_frame. Qed.

(** [setsid] takes no arguments and writes no memory, so neither arm can
    touch [vm_maps]: the -EPERM arm hands back [m] itself, and the
    success arm hands back [with_setsid_succeeded (with_tid ret m)],
    two setters that rebuild only [ProcState]. *)
Lemma check_setsid_frame : forall eff m m' evs,
  check_setsid eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof. intros eff m m' evs H. unfold check_setsid in H. vm_frame2 H. Qed.

(** [prctl] answers [PR_CAPBSET_READ] out of a constant and declines
    every other option, so no arm of it touches the model at all: both
    accepting branches hand back [m] itself. *)
Lemma check_prctl_frame : forall option_ arg2 eff m m' evs,
  check_prctl option_ arg2 eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof.
  intros option_ arg2 eff m m' evs H. unfold check_prctl in H. vm_frame2 H.
Qed.

(** The three clock arms.  [gettimeofday] and [clock_gettime] hand back
    the model untouched; [nanosleep] advances [m_clock] and nothing else,
    and [with_clock] leaves [m_vmmaps] alone BY CONVERSION. *)

Lemma check_gettimeofday_frame : forall i tv tz eff m m' evs,
  check_gettimeofday i tv tz eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i tv tz eff m m' evs H.
  unfold check_gettimeofday in H. vm_frame2 H.
Qed.

Lemma check_clock_gettime_frame : forall i clkid tp eff m m' evs,
  check_clock_gettime i clkid tp eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i clkid tp eff m m' evs H.
  unfold check_clock_gettime in H. vm_frame2 H.
Qed.

Lemma check_nanosleep_frame : forall i rqtp rmtp eff m m' evs,
  check_nanosleep i rqtp rmtp eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i rqtp rmtp eff m m' evs H.
  unfold check_nanosleep in H. vm_frame2 H.
Qed.

(* -------------------------------------------------------------------------
   The invariant, over the whole dispatcher
   ------------------------------------------------------------------------- *)

(** [execve] establishes it: the ledger starts empty. *)
Lemma init_model_vm_wf : forall reserved brk0 mbase sp lim inp,
  vm_wf (m_vmmaps (init_model reserved brk0 mbase sp lim inp)).
Proof.
  intros reserved brk0 mbase sp lim inp.
  (* [m_vmmaps] and [init_model] are [simpl never] ([State.v]), so [cbn]
     has no handle on them; the ledger is [[]] BY CONVERSION, which is
     what [reflexivity] here establishes and [rewrite] then uses. *)
  assert (Hm : vm_maps (m_vmmaps (init_model reserved brk0 mbase sp lim inp)) = [])
    by reflexivity.
  unfold vm_wf, maps_wf, sizes_nonzero, page_owner_unique. rewrite Hm.
  split; [constructor|intros p _; cbn [owners]; lia].
Qed.

(** …and every modeled syscall preserves it.

    The dispatcher is one lookup in [Checks/Sys/Dispatch.checked_table],
    so the case split here is over the ARMS OF THAT TABLE rather than
    over syscall numbers: [lookup_ca_In] turns the lookup into
    membership, and [arm_unfold] turns each member back into the plain
    [check_*] the lemma below it was written against.  Adding an arm to
    the table therefore adds a goal here, and the last alternative says
    what to write.

    THE LIST IS A HAND-MAINTAINED ENUMERATION, deliberately, and that is
    a judgement rather than an oversight.  A computed coverage check
    needs both sides to be DATA — a list of arms and a decidable test —
    so that agreement is a [vm_compute].  The alternatives below are
    TACTICS, not data, and reifying them into a second list would move
    the staleness rather than remove it.  What this needs is not
    detection but a NAME: an uncovered arm already fails the build, but
    without one it fails opaquely, as an exhausted [first] with no
    indication of what is missing. *)

(** [lookup_ca] answers with an arm OF the table it searched. *)
Lemma lookup_ca_In : forall t n c, lookup_ca t n = Some c -> In c t.
Proof.
  induction t as [|a t IH]; intros n c H; cbn [lookup_ca] in H;
    [discriminate|].
  cbn [In]. destruct (Z.eqb (ca_no a) n).
  - left. injection H as <-. reflexivity.
  - right. exact (IH n c H).
Qed.

(** The arms below neither read nor write [vm_maps].  They change fds,
    credentials, the file system or the socket table, or nothing at all,
    and every setter that does so rebuilds only its own subsystem record
    — so [m_vmmaps] comes across by conversion and each proof is the
    same mechanical [vm_frame2]. *)

Lemma check_dup_frame : forall oldfd eff m m' evs,
  check_dup oldfd eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof.
  intros oldfd eff m m' evs H.
  unfold check_dup, check_dup_result in H. vm_frame2 H.
Qed.

Lemma check_dup3_frame : forall oldfd newfd flags eff m m' evs,
  check_dup3 oldfd newfd flags eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros oldfd newfd flags eff m m' evs H. unfold check_dup3 in H. vm_frame2 H.
Qed.

Lemma check_unlinkat_frame : forall i dirfd pathp flags eff m m' evs,
  check_unlinkat i dirfd pathp flags eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold check_unlinkat, Namei.check_unlinkat_body, Namei.check_unlinkat_tmp,
    Namei.check_unlink_found, check_unlink_result in H.
  vm_frame2 H.
Qed.

Lemma check_faccessat_frame : forall i dirfd pathp mode eff m m' evs,
  check_faccessat i dirfd pathp mode eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i dirfd pathp mode eff m m' evs H.
  unfold check_faccessat, Open.check_faccessat_body, check_access_exists in H.
  vm_frame2 H.
Qed.

Lemma check_faccessat2_frame : forall i dirfd pathp mode flags eff m m' evs,
  check_faccessat2 i dirfd pathp mode flags eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i dirfd pathp mode flags eff m m' evs H.
  unfold check_faccessat2, Open.check_faccessat_body, check_access_exists in H.
  vm_frame2 H.
Qed.

Lemma check_pselect6_frame : forall i n32 inp outp exp tsp sig eff m m' evs,
  check_pselect6 i n32 inp outp exp tsp sig eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i n32 inp outp exp tsp sig eff m m' evs H.
  unfold check_pselect6 in H. vm_frame2 H.
Qed.

Lemma check_ppoll_frame : forall i ufds nfds tsp sig sigsetsize eff m m' evs,
  check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i ufds nfds tsp sig sigsetsize eff m m' evs H.
  unfold check_ppoll in H. vm_frame2 H.
Qed.

Lemma check_newfstatat_frame : forall i dirfd pathp flag eff m m' evs,
  check_newfstatat i dirfd pathp flag eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i dirfd pathp flag eff m m' evs H.
  unfold check_newfstatat in H. vm_frame2 H.
Qed.

(** fstat's success arm changes the model
    on a call that also writes user memory: it records the file's stat
    pin ([State.with_statpin]).  That setter rebuilds [ProcState] and
    carries [m_vmmaps] across untouched, which is what the [model]
    rewrite database's [m_vmmaps_with_statpin] says, so the frame
    holds -- but not because nothing moved. *)
Lemma check_fstat_file_frame : forall i p statbuf eff m m' evs,
  check_fstat_file i p statbuf eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i p statbuf eff m m' evs H.
  unfold check_fstat_file in H.
  destruct (fs_lookup (m_fs m) p) as [data|]; [|discriminate].
  destruct (negb (access_okb statbuf STAT_SIZE)); [vm_frame2 H|].
  destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE)) as [w|];
    [|discriminate].
  assert (Hdel : exists pin,
             check_fstat_deliver statbuf (length data) p pin eff m
             = CheckOk m' evs).
  { destruct (statpin_lookup (m_statpins m) p) as [b0|]; [|eauto].
    destruct (negb (stat_buf_wf b0)); [discriminate|eauto]. }
  destruct Hdel as (pin & Hd).
  apply check_fstat_deliver_ok in Hd
    as (bs & _ & _ & _ & _ & [(b1 & _ & _ & ->)|(_ & ->)]);
    [reflexivity|autorewrite with model; reflexivity].
Qed.

Lemma check_fstat_chrdev_frame : forall ok p i statbuf eff m m' evs,
  check_fstat_chrdev ok p i statbuf eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros ok p i statbuf eff m m' evs H.
  unfold check_fstat_chrdev in H.
  destruct (negb (access_okb statbuf STAT_SIZE)); [vm_frame2 H|].
  destruct (read_bytes_map (in_wmem i) statbuf (Z_to_bv 64 STAT_SIZE)) as [w|];
    [|discriminate].
  assert (Hdel : exists pin,
             check_fstat_deliver_by ok statbuf p pin eff m
             = CheckOk m' evs).
  { destruct (statpin_lookup (m_statpins m) p) as [b0|]; [|eauto].
    destruct (negb (stat_buf_wf b0 && ok b0)%bool); [discriminate|eauto]. }
  destruct Hdel as (pin & Hd).
  apply check_fstat_deliver_by_ok in Hd
    as (bs & _ & _ & _ & _ & [(b1 & _ & _ & ->)|(_ & ->)]);
    [reflexivity|autorewrite with model; reflexivity].
Qed.

Lemma check_fstat_devnull_frame : forall i statbuf eff m m' evs,
  check_fstat_devnull i statbuf eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof. intros. eapply check_fstat_chrdev_frame. exact H. Qed.

Lemma check_fstat_urandom_frame : forall i statbuf eff m m' evs,
  check_fstat_urandom i statbuf eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof. intros. eapply check_fstat_chrdev_frame. exact H. Qed.

Lemma check_fstat_frame : forall i fd statbuf eff m m' evs,
  check_fstat i fd statbuf eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof.
  intros i fd statbuf eff m m' evs H. unfold check_fstat in H.
  destruct (fd_lookup (m_fds m) fd) as [e|]; [|vm_frame2 H].
  destruct e; try discriminate;
    first [eapply check_fstat_file_frame; exact H
          |eapply check_fstat_devnull_frame; exact H
          |eapply check_fstat_urandom_frame; exact H].
Qed.

Lemma check_getid_frame : forall sel eff m m' evs,
  check_getid sel eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof. intros sel eff m m' evs H. unfold check_getid in H. vm_frame2 H. Qed.

Lemma check_setid_frame : forall get put user v eff m m' evs,
  check_setid get put user v eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros get put user v eff m m' evs H.
  unfold check_setid, check_setid_result in H. vm_frame2 H.
Qed.

Lemma check_setresid_frame : forall get put user r e sv eff m m' evs,
  check_setresid get put user r e sv eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros get put user r e sv eff m m' evs H.
  unfold check_setresid, check_setid_result in H. vm_frame2 H.
Qed.

Lemma check_getgroups_frame : forall gidsetsize eff m m' evs,
  check_getgroups gidsetsize eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof.
  intros gidsetsize eff m m' evs H. unfold check_getgroups in H. vm_frame2 H.
Qed.

Lemma check_setgroups_frame : forall eff m m' evs,
  check_setgroups eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof.
  intros eff m m' evs H. unfold check_setgroups in H. vm_frame2 H.
Qed.

Lemma check_socket_frame : forall domain type protocol eff m m' evs,
  check_socket domain type protocol eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros domain type protocol eff m m' evs H.
  unfold check_socket, check_new_fd_result in H. vm_frame2 H.
Qed.

Lemma check_bind_frame : forall i fd addrp addrlen eff m m' evs,
  check_bind i fd addrp addrlen eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i fd addrp addrlen eff m m' evs H.
  unfold check_bind, check_errno_or_success in H. vm_frame2 H.
Qed.

Lemma check_listen_frame : forall fd backlog eff m m' evs,
  check_listen fd backlog eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof.
  intros fd backlog eff m m' evs H.
  unfold check_listen, check_errno_or_success, check_errno_only in H.
  vm_frame2 H.
Qed.

(* connect answers every arm through [check_ret_only]/[check_ret_only_copyins]
   at the model it was given, or declines; it never writes vm_maps. *)
Lemma check_connect_frame : forall i fd addrp addrlen eff m m' evs,
  check_connect i fd addrp addrlen eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i fd addrp addrlen eff m m' evs H.
  unfold check_connect in H. vm_frame2 H.
Qed.

Lemma check_accept4_frame : forall fd addrp addrlenp flags eff m m' evs,
  check_accept4 fd addrp addrlenp flags eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros fd addrp addrlenp flags eff m m' evs H.
  (* [check_errno_only] is unfolded alongside, the way
     [check_read_frame] unfolds [check_access_ok_zero]: it is the arm
     [check_accept4] takes once [Net.Socket.conn_ix_exhausted] holds, and
     [vm_step] sees no [if] or [match] through a folded definition, so
     without the unfold that branch leaves an open goal. *)
  unfold check_accept4, check_new_fd_result, check_errno_or_success,
    check_errno_only in H. vm_frame2 H.
Qed.

Lemma check_fcntl_frame : forall fd cmd arg eff m m' evs,
  check_fcntl fd cmd arg eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof.
  intros fd cmd arg eff m m' evs H. unfold check_fcntl in H. vm_frame2 H.
Qed.

(** sched_setscheduler answers an errno or a 0 that changes no model
    state at all, or declines.  It READS four bytes of user memory and
    writes none, so it cannot reach the mappings either. *)
Lemma check_sched_setscheduler_frame : forall i pid policy param eff m m' evs,
  check_sched_setscheduler i pid policy param eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i pid policy param eff m m' evs H.
  unfold check_sched_setscheduler in H. vm_frame2 H.
Qed.

(** sched_getaffinity answers an errno or declines; it never reaches
    user memory, let alone the mappings. *)
Lemma check_sched_getaffinity_frame : forall len eff m m' evs,
  check_sched_getaffinity len eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof.
  intros len eff m m' evs H. unfold check_sched_getaffinity in H. vm_frame2 H.
Qed.

(** sched_yield answers 0 and hands back the model it was given, so the
    mappings are the same list. *)
Lemma check_sched_yield_frame : forall eff m m' evs,
  check_sched_yield eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof.
  intros eff m m' evs H. unfold check_sched_yield in H. vm_frame2 H.
Qed.

(** sigaltstack answers a bare return on every arm, and the one arm that
    moves the model hands back [with_sigaltstack_installed m], which
    rebuilds the process state alone. *)
Lemma check_sigaltstack_frame : forall i uss uoss eff m m' evs,
  check_sigaltstack i uss uoss eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i uss uoss eff m m' evs H.
  unfold check_sigaltstack in H. vm_frame2 H.
Qed.

Lemma check_rt_sigaction_frame : forall i sig act oact ss eff m m' evs,
  check_rt_sigaction i sig act oact ss eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i sig act oact ss eff m m' evs H.
  unfold check_rt_sigaction in H. vm_frame2 H.
Qed.

Lemma check_clone_frame : forall flags eff m m' evs,
  check_clone flags eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof.
  intros flags eff m m' evs H.
  unfold check_clone, check_clone_resolve, check_clone_answer in H.
  vm_frame2 H.
Qed.

Lemma check_clone3_frame : forall i uargs size eff m m' evs,
  check_clone3 i uargs size eff m = CheckOk m' evs -> m_vmmaps m' = m_vmmaps m.
Proof.
  intros i uargs size eff m m' evs H.
  unfold check_clone3, check_clone3_resolve, check_clone_answer in H.
  vm_frame2 H.
Qed.

(* -------------------------------------------------------------------------
   THE FORCING MECHANISM

   [Checks.Sys.Dispatch] made the dispatcher DATA: [check_syscall] is a
   [lookup_ca] into [checked_table], not a hand-written [if] chain.  So
   "every arm preserves the ledger" is literally a [Forall] over that
   list, and the coverage obligation lands where the arm is declared —
   add a [CheckedArm] to [checked_table] and a goal appears here, with no
   edit to any statement below.
   ------------------------------------------------------------------------- *)

(** What one dispatcher arm owes the ledger, as a property of the table
    entry rather than of a syscall number. *)
Definition arm_preserves_vm (c : CheckedArm) : Prop :=
  forall i eff m m' evs,
    ca_check c i eff m = CheckOk m' evs ->
    vm_wf (m_vmmaps m) -> vm_wf (m_vmmaps m').

(** Every arm discharges it.

    THE FALLBACK IS THE POINT.  The alternatives are a hand-maintained
    enumeration, and they are deliberately NOT reified into a second
    list: a computed coverage check needs both sides to be data, and
    these are tactics, so a second list would move the staleness rather
    than remove it.  What the enumeration needs instead is a name for its
    own failure.  An arm nobody covered already fails the build —
    [repeat apply Forall_cons] hands it its own goal and [first] runs out
    of alternatives — and without a fallback it fails opaquely, as an
    exhausted [first] naming nothing.  The last alternative says which
    lemma to write.

    Order matters: [first] takes the earliest alternative that applies,
    so the [fail 1] has to stay last.  An arm listed behind it is an arm
    that never runs.

    [autorewrite with arm_unfold] is what gets from [ca_check arm_read]
    to [check_read]: [refine] built each arm, so [cbn] will not unfold
    it, and [Checks.Sys.Dispatch] exports a [reflexivity] lemma per arm
    for exactly this. *)
(** The five socket option/address calls.  Each resolves the fd and
    answers from the socket state; none has an address-space effect, so
    each leaves [m_vmmaps] exactly as it found it. *)
Lemma check_getsockname_frame : forall fd eff m m' evs,
  check_getsockname fd eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros fd eff m m' evs H.
  unfold check_getsockname in H. vm_frame2 H.
Qed.

Lemma check_getpeername_frame : forall fd eff m m' evs,
  check_getpeername fd eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros fd eff m m' evs H.
  unfold check_getpeername in H. vm_frame2 H.
Qed.

Lemma check_setsockopt_frame : forall fd level optlen eff m m' evs,
  check_setsockopt fd level optlen eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros fd level optlen eff m m' evs H.
  unfold check_setsockopt in H. vm_frame2 H.
Qed.

Lemma check_getsockopt_frame : forall i fd level optlenp eff m m' evs,
  check_getsockopt i fd level optlenp eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i fd level optlenp eff m m' evs H.
  unfold check_getsockopt in H. vm_frame2 H.
Qed.

Lemma check_shutdown_frame : forall fd how eff m m' evs,
  check_shutdown fd how eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros fd how eff m m' evs H.
  unfold check_shutdown in H. vm_frame2 H.
Qed.

(** The send path.  [check_send_on_socket] is the shared body
    both entry points funnel through, and it is the only place either
    touches the model: the delivering arm returns the model it was
    handed and the [SendErr] arm rewrites the descriptor with [with_fds].
    Neither moves a mapping.  Its [pre]/[acc] parameters carry the
    copy-in ledger. *)
Lemma check_send_on_socket_frame :
  forall pre acc fd sk total bs eff m m' evs,
  check_send_on_socket pre acc fd sk total bs eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros pre acc fd sk total bs eff m m' evs H.
  unfold check_send_on_socket in H. vm_frame2 H.
Qed.

(** The three socket arms that need no socket.  None of them touches the
    address space: [check_socketpair] answers out of [socketpair_fds] and
    the destination's own range, and both recv entry points answer out of
    the fd table alone.  Written out per arm rather than folded together
    because the cascade below applies them by name. *)
Lemma check_recv_fd_answer_frame : forall fds fd eff m m' evs,
  check_recv_fd_answer fds fd eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros fds fd eff m m' evs H.
  unfold check_recv_fd_answer in H. vm_frame2 H.
Qed.


Lemma check_socketpair_frame : forall i family type protocol sv eff m m' evs,
  check_socketpair i family type protocol sv eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i family type protocol sv eff m m' evs H.
  unfold check_socketpair, check_socketpair_written, check_socketpair_faulted
    in H. vm_frame2 H.
Qed.


Lemma check_recvfrom_frame : forall i fd buf size eff m m' evs,
  check_recvfrom i fd buf size eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i fd buf size eff m m' evs H.
  unfold check_recvfrom, check_access_ok_zero, check_recv_fd_answer in H.
  vm_frame2 H.
Qed.


Lemma check_recvmsg_frame : forall fd flags eff m m' evs,
  check_recvmsg fd flags eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros fd flags eff m m' evs H.
  unfold check_recvmsg, check_recv_fd_answer in H. vm_frame2 H.
Qed.

Lemma check_sendto_frame : forall i fd buf count flags addrp eff m m' evs,
  check_sendto i fd buf count flags addrp eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i fd buf count flags addrp eff m m' evs H.
  unfold check_sendto, check_access_ok_zero, check_send_on_socket in H.
  vm_frame2 H.
Qed.

Lemma check_sendmsg_frame : forall i fd msgp flags eff m m' evs,
  check_sendmsg i fd msgp flags eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i fd msgp flags eff m m' evs H.
  unfold check_sendmsg, check_send_on_socket in H. vm_frame2 H.
Qed.

(** pipe2 writes the descriptor pair into guest memory and installs two
    fd-table entries plus a pipe-table entry.  None of that is [vm_maps]:
    [pipe2_model] is [with_pipes] over [with_fds], and both carry the VM
    subsystem across untouched. *)
Lemma check_pipe2_frame : forall i fildes flags eff m m' evs,
  check_pipe2 i fildes flags eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i fildes flags eff m m' evs H.
  unfold check_pipe2, pipe2_model in H. vm_frame2 H.
Qed.

(** [futex] answers only from its arguments and the four bytes it reads:
    every arm hands back [m] itself, so nothing of the model changes and
    [m_vmmaps] with it.  A [*_frame] rather than a [*_preserves], for the
    reason [check_timerfd_create_frame] gives.  The wait arm's copy-in
    ledger is a claim about what was READ; the pages it charges are
    accounted by [Run.sstep_syscall] over the effect, outside this
    theorem. *)
Lemma check_futex_frame : forall i uaddr op val utime eff m m' evs,
  check_futex i uaddr op val utime eff m = CheckOk m' evs ->
  m_vmmaps m' = m_vmmaps m.
Proof.
  intros i uaddr op val utime eff m m' evs H.
  unfold check_futex, check_futex_wake_private, check_futex_wait_private in H.
  vm_frame2 H.
Qed.

Lemma checked_table_preserves_vm : Forall arm_preserves_vm checked_table.
Proof.
  unfold checked_table.
  repeat apply Forall_cons.
  all: try exact (Forall_nil arm_preserves_vm).
  all: unfold arm_preserves_vm; intros i eff m m' evs H Hwf;
       autorewrite with arm_unfold in H.
  all: first
    [ eapply check_brk_preserves; eassumption
    | eapply check_mmap_preserves; eassumption
    | eapply check_munmap_preserves; eassumption
    | eapply check_mremap_preserves; eassumption
    | eapply check_mprotect_preserves; eassumption
    | erewrite check_madvise_frame by eassumption; exact Hwf
    | erewrite check_read_frame by eassumption; exact Hwf
    | erewrite check_write_frame by eassumption; exact Hwf
    | erewrite check_pread64_frame by eassumption; exact Hwf
    | erewrite check_pwrite64_frame by eassumption; exact Hwf
    | erewrite check_readv_frame by eassumption; exact Hwf
    | erewrite check_writev_frame by eassumption; exact Hwf
    | erewrite check_openat_frame by eassumption; exact Hwf
    | erewrite check_close_frame by eassumption; exact Hwf
    | erewrite check_lseek_frame by eassumption; exact Hwf
    | erewrite check_ftruncate_frame by eassumption; exact Hwf
    | erewrite check_ioctl_frame by eassumption; exact Hwf
    | erewrite check_readlinkat_frame by eassumption; exact Hwf
    | erewrite check_wait4_frame by eassumption; exact Hwf
    | erewrite check_fsync_frame by eassumption; exact Hwf
    | erewrite check_getdents64_frame by eassumption; exact Hwf
    | erewrite check_flock_frame by eassumption; exact Hwf
    | erewrite check_exit_frame by eassumption; exact Hwf
    | erewrite check_set_tid_address_frame by eassumption; exact Hwf
    | erewrite check_getpid_frame by eassumption; exact Hwf
    | erewrite check_gettid_frame by eassumption; exact Hwf
    | erewrite check_setsid_frame by eassumption; exact Hwf
    | erewrite check_uname_frame by eassumption; exact Hwf
    | erewrite check_prctl_frame by eassumption; exact Hwf
    | erewrite check_prlimit64_frame by eassumption; exact Hwf
    | erewrite check_getrandom_frame by eassumption; exact Hwf
    | erewrite check_gettimeofday_frame by eassumption; exact Hwf
    | erewrite check_clock_gettime_frame by eassumption; exact Hwf
    | erewrite check_nanosleep_frame by eassumption; exact Hwf
    | erewrite check_dup_frame by eassumption; exact Hwf
    | erewrite check_dup3_frame by eassumption; exact Hwf
    | erewrite check_unlinkat_frame by eassumption; exact Hwf
    | erewrite check_faccessat_frame by eassumption; exact Hwf
    | erewrite check_faccessat2_frame by eassumption; exact Hwf
    | erewrite check_pselect6_frame by eassumption; exact Hwf
    | erewrite check_ppoll_frame by eassumption; exact Hwf
    | erewrite check_newfstatat_frame by eassumption; exact Hwf
    | erewrite check_fstat_frame by eassumption; exact Hwf
    | erewrite check_getid_frame by eassumption; exact Hwf
    | erewrite check_setid_frame by eassumption; exact Hwf
    | erewrite check_setresid_frame by eassumption; exact Hwf
    | erewrite check_getgroups_frame by eassumption; exact Hwf
    | erewrite check_setgroups_frame by eassumption; exact Hwf
    | erewrite check_socket_frame by eassumption; exact Hwf
    | erewrite check_bind_frame by eassumption; exact Hwf
    | erewrite check_listen_frame by eassumption; exact Hwf
    | erewrite check_accept4_frame by eassumption; exact Hwf
    | erewrite check_fcntl_frame by eassumption; exact Hwf
    | erewrite check_sched_setscheduler_frame by eassumption; exact Hwf
    | erewrite check_sched_getaffinity_frame by eassumption; exact Hwf
    | erewrite check_sched_yield_frame by eassumption; exact Hwf
    | erewrite check_sigaltstack_frame by eassumption; exact Hwf
    | erewrite check_rt_sigaction_frame by eassumption; exact Hwf
    | erewrite check_tkill_frame by eassumption; exact Hwf
    | erewrite check_tgkill_frame by eassumption; exact Hwf
    | erewrite check_rt_sigprocmask_frame by eassumption; exact Hwf
    | erewrite check_futex_frame by eassumption; exact Hwf
    | erewrite check_clone_frame by eassumption; exact Hwf
    | erewrite check_clone3_frame by eassumption; exact Hwf
    | erewrite check_getsockname_frame by eassumption; exact Hwf
    | erewrite check_getpeername_frame by eassumption; exact Hwf
    | erewrite check_setsockopt_frame by eassumption; exact Hwf
    | erewrite check_getsockopt_frame by eassumption; exact Hwf
    | erewrite check_shutdown_frame by eassumption; exact Hwf
    | erewrite check_sendto_frame by eassumption; exact Hwf
    | erewrite check_sendmsg_frame by eassumption; exact Hwf
    | erewrite check_socketpair_frame by eassumption; exact Hwf
    | erewrite check_recvfrom_frame by eassumption; exact Hwf
    | erewrite check_recvmsg_frame by eassumption; exact Hwf
    | erewrite check_connect_frame by eassumption; exact Hwf
    | erewrite check_timerfd_create_frame by eassumption; exact Hwf
    | erewrite check_eventfd2_frame by eassumption; exact Hwf
    | erewrite check_pipe2_frame by eassumption; exact Hwf
    | erewrite check_getcwd_frame by eassumption; exact Hwf
    | erewrite check_epoll_create1_frame by eassumption; exact Hwf
    | erewrite check_epoll_ctl_frame by eassumption; exact Hwf
    | erewrite check_epoll_pwait_frame by eassumption; exact Hwf
    | fail 1 "check_syscall_preserves_vm_wf has no case for this dispatcher arm: give the new checker a *_frame lemma (it leaves m_vmmaps alone) or a *_preserves one (it writes vm_maps), and add it to the list above" ].
Qed.

(** …and therefore so does the dispatcher.  No syscall is named here, and
    nothing in this proof grows when one is added: the lookup is resolved
    abstractly and [checked_table_preserves_vm] carries the arms. *)
Theorem check_syscall_preserves_vm_wf : forall i eff m m' evs,
  check_syscall i eff m = CheckOk m' evs ->
  vm_wf (m_vmmaps m) -> vm_wf (m_vmmaps m').
Proof.
  intros i eff m m' evs H Hwf. unfold check_syscall in H.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk;
    [|discriminate H].
  pose proof checked_table_preserves_vm as Hall.
  rewrite Forall_forall in Hall.
  exact (Hall c (lookup_ca_In _ _ _ Elk) i eff m m' evs H Hwf).
Qed.

(** The same statement against the RELATIONAL spec, which is what a
    downstream proof steps through. *)
Corollary syscall_spec_preserves_vm_wf : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  vm_wf (m_vmmaps m) -> vm_wf (m_vmmaps m').
Proof.
  intros i m eff m' evs H Hwf.
  eapply check_syscall_preserves_vm_wf; [|exact Hwf].
  apply check_syscall_ok_iff. exact H.
Qed.

(** Put together: in any state satisfying [vm_wf] — which the
    corollary below takes as a HYPOTHESIS rather than establishing by
    induction over a run — a [map_has] hit at a
    page-aligned base names exactly one ledger entry.  This is the fact
    the downstream [munmap] argument needs — [map_has]'s
    [(base, size)] test and [map_remove]'s base-only removal cannot
    disagree. *)
Corollary base_unique_after_syscall : forall i eff m m' evs a n,
  check_syscall i eff m = CheckOk m' evs ->
  vm_wf (m_vmmaps m) ->
  bv_unsigned a mod page_size = 0 ->
  map_has (vm_maps (m_vmmaps m')) a n = true ->
  List.filter (fun q => bv_eqb (fst q) a) (vm_maps (m_vmmaps m')) = [(a, n)].
Proof.
  intros i eff m m' evs a n H Hwf Ha Hhas.
  apply base_entry_unique; [|exact Ha|exact Hhas].
  exact (check_syscall_preserves_vm_wf i eff m m' evs H Hwf).
Qed.
