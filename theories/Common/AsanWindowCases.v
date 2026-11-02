(* Written by the OSS-Fuzz proof collaborators. *)
(** * AsanWindowCases — the placement window, checked on concrete ledgers

    NOT part of the trusted specification: worked cases for
    [AsanWindow.family_place_in_window], in the style of
    [Checks.Cases.Mm.PlacementHoles].  Every address below is computed
    by Linux's search as [Checks.Placement.linux_place_b] runs it, and
    every premise is decided by [AsanWindow.window_premises_b].  The
    file is here and not under [Checks/Cases/] because it uses
    [Common.AsanWindow], and [Checks/] may not import [Common/]
    ([Checks.Placement]'s header).

    The sizes are the ASan secondary maps of the cURL fuzz target
    fuzz_bufq: 69,632 bytes (17 pages, the smallest) and 270,336 bytes
    (66 pages, the largest).  Both are below 2 MiB, so the THP path
    never runs for them, whatever the kernel build.

    The cases, and what each one pins:

    - A, ON A LAUNCH LEDGER: the ledger [execve] gives a process (the
      vdso/vvar pair at the top of the search window), then four family
      maps of both sizes.  Every premise holds, with the bufq sizes, so
      the lemma is not vacuous there.  The first map is also checked
      against [check_syscall], the checker of the whole mmap call.
    - B, A HIGHER GAP: an munmap opens a hole between two maps.  The
      next small map goes into the hole, so its address is not the one
      the same request gets on ledger A, and it is still in the window.
    - C, NEXT TO A FIXED RESERVATION: a start-up PROT_NONE reservation
      under the vdso pair, re-cut into three entries by a MAP_FIXED
      inside it, and one cover interval for all three.  A family map
      next to it is unmapped; the next map lands directly under the
      reservation.
    - D, NEXT TO [mmap_top]: a hole that ends at the window's top.  The
      next map lands directly under [mmap_top].
    - E, THE TOO-STRONG BOUND IS FALSE: the counterexample to the bound
      [W = M + s_max] ("the family never fragments").  The same ledger
      meets [fam_window].
    - F, THE COVER PREMISE IS NEEDED: one map that is not in the family
      and not in the cover.  Every other premise holds, and the grant
      lands below the window. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs Placement Cases.Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require MmapTopFrame.
From LinuxProcessSemantics.Common Require Import AsanPlacement AsanWindow.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* =========================================================================
   Fixtures
   ========================================================================= *)

(** The two bufq secondary map sizes. *)
Definition s_small : Z := 69632.
Definition s_large : Z := 270336.

(** The ledger after a NULL-hint, rw, anonymous grant of [n] bytes: the
    address Linux's search gives, consed onto [vm_maps], as the modeled
    arm of [Mmap.mmap_spec] writes it. *)
Definition grant (h : VmMaps) (n : Z) : VmMaps :=
  match linux_place_b h false (Z_to_bv 64 0) n with
  | Some a =>
      mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 n) :: vm_maps h)
        (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h)
        (vm_mmap_base h) (vm_init_sp h)
  | None => h
  end.

(** The same for a PROT_NONE grant: it lands in both ledgers. *)
Definition grant_none (h : VmMaps) (n : Z) : VmMaps :=
  match linux_place_b h false (Z_to_bv 64 0) n with
  | Some a =>
      mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 n) :: vm_maps h)
        ((Z_to_bv 64 a, Z_to_bv 64 n) :: vm_noaccess h)
        (vm_start_brk h) (vm_brk h) (vm_limit h)
        (vm_mmap_base h) (vm_init_sp h)
  | None => h
  end.

(** munmap of [[a, a + n)], the ledger [Mmap.munmap_spec] writes. *)
Definition unmap (h : VmMaps) (a n : Z) : VmMaps :=
  mmap_fixed_destroyed_next h (Z_to_bv 64 a) (Z_to_bv 64 n).

(** The family classifier of a case: the entries based at [bs]. *)
Definition fam_bases (bs : list Z) (p : word * word) : bool :=
  existsb (Z.eqb (bv_unsigned (fst p))) bs.

Definition no_hint : word := Z_to_bv 64 0.

Lemma no_hint_address : hint_address no_hint = 0.
Proof. vm_compute. reflexivity. Qed.

(** A launch [execve] can really hand a process, the one
    [Checks.Cases.Mm.PlacementHoles] uses: the mmap base at the bottom
    of the band [Run.valid_mmap_base] admits, the stack pointer at the
    bottom of its window, an empty image, the default kernel build (no
    transparent huge pages). *)
Definition launch_model : Model :=
  init_model [] (Z_to_bv 64 0x11000) (Z_to_bv 64 mmap_base_min)
    (Z_to_bv 64 sp_window_lo) target_alloc_limit (demo_input [] IEof).

Definition h0 : VmMaps := m_vmmaps launch_model.

(** The top of the search window for every case: [mmap_base_min]. *)
Definition T0 : Z := 23387528589312.

Example h0_top : mmap_top h0 = T0.
Proof. vm_compute. reflexivity. Qed.

(** The vdso/vvar pair is the only start-up entry, and it ends at the
    window's top. *)
Example h0_ledger :
  vm_reserved h0 = [ (Z_to_bv 64 (T0 - 24576), Z_to_bv 64 16384);
                     (Z_to_bv 64 (T0 - 8192), Z_to_bv 64 8192) ]
  /\ vm_maps h0 = [].
Proof. split; vm_compute; reflexivity. Qed.

(** The pair's cover weight for the larger request. *)
Definition W_vdso : Z := 573438.

Example W_vdso_val : gap_weight s_large (vm_reserved h0) = W_vdso.
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   A. A launch ledger with an ASan-like family
   ========================================================================= *)

(** Four secondary maps in a row: large, small, small, large.  The first
    lands directly under the vdso pair, next to that fixed reservation;
    each next one directly under the one before. *)
Definition hA1 : VmMaps := grant h0 s_large.
Definition hA : VmMaps := grant (grant (grant hA1 s_small) s_small) s_large.

Example caseA_ledger :
  vm_maps hA = [ (Z_to_bv 64 (T0 - 704512), Z_to_bv 64 s_large);
                 (Z_to_bv 64 (T0 - 434176), Z_to_bv 64 s_small);
                 (Z_to_bv 64 (T0 - 364544), Z_to_bv 64 s_small);
                 (Z_to_bv 64 (T0 - 294912), Z_to_bv 64 s_large) ].
Proof. vm_compute. reflexivity. Qed.

(** THE FIRST MAP IS THE CHECKER'S.  The whole mmap call
    [mmap(NULL, 270336, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS,
    -1, 0)] on the launch model, answered at the address [grant] uses,
    is accepted, and its post-state has the ledger [hA1]. *)
Example caseA_first_map_is_the_checkers :
  match check_syscall
          (mkInput (Z_to_bv 64 222)
             [Z_to_bv 64 0; Z_to_bv 64 s_large; Z_to_bv 64 3; Z_to_bv 64 34;
              mmap_fd_none; Z_to_bv 64 0]
             (fun _ => None) (fun _ => None))
          (mkEffect (Z_to_bv 64 (T0 - 294912)) []
             [(Z_to_bv 64 (T0 - 294912), Z_to_bv 64 s_large)])
          launch_model with
  | CheckOk m' _ => vm_maps (m_vmmaps m') = vm_maps hA1
                    /\ vm_reserved (m_vmmaps m') = vm_reserved hA1
  | _ => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

Definition famA : word * word -> bool :=
  fam_bases [T0 - 294912; T0 - 364544; T0 - 434176; T0 - 704512].

(** The family's bytes on ledger A; [M] for cases A and B. *)
Definition M_AB : Z := 679936.

Example caseA_family_bytes :
  gw_sizes (List.filter famA (vm_reserved hA ++ vm_maps hA)) = M_AB.
Proof. vm_compute. reflexivity. Qed.

(** The window for A and B: 3,997,684 bytes. *)
Example caseAB_window : fam_window M_AB s_small s_large W_vdso = 3997684.
Proof. vm_compute. reflexivity. Qed.

(** EVERY PREMISE HOLDS, for both request sizes: the lemma is not
    vacuous on a launch ledger with the bufq sizes. *)
Example caseA_premises_large :
  window_premises_b hA s_large famA (vm_reserved h0) M_AB s_small s_large W_vdso = true.
Proof. vm_compute. reflexivity. Qed.

Example caseA_premises_small :
  window_premises_b hA s_small famA (vm_reserved h0) M_AB s_small s_large W_vdso = true.
Proof. vm_compute. reflexivity. Qed.

Example caseA_place_large :
  linux_place_b hA false no_hint s_large = Some (T0 - 974848).
Proof. vm_compute. reflexivity. Qed.

Example caseA_place_small :
  linux_place_b hA false no_hint s_small = Some (T0 - 774144).
Proof. vm_compute. reflexivity. Qed.

(** The lemma's conclusion for the two grants. *)
Lemma caseA_in_window :
  mmap_top hA - fam_window M_AB s_small s_large W_vdso <= T0 - 974848
  /\ mmap_top hA - fam_window M_AB s_small s_large W_vdso <= T0 - 774144.
Proof.
  split.
  - apply (proj1 (family_place_in_window_b hA false no_hint s_large (T0 - 974848)
                   famA (vm_reserved h0) M_AB s_small s_large W_vdso
                   caseA_premises_large no_hint_address eq_refl caseA_place_large)).
  - apply (proj1 (family_place_in_window_b hA false no_hint s_small (T0 - 774144)
                   famA (vm_reserved h0) M_AB s_small s_large W_vdso
                   caseA_premises_small no_hint_address eq_refl caseA_place_small)).
Qed.

(* =========================================================================
   B. A higher gap opens between two maps
   ========================================================================= *)

(** munmap of the first small map: a 17-page hole between the first
    large map and the second small one. *)
Definition hB : VmMaps := unmap hA (T0 - 364544) s_small.

Example caseB_ledger :
  vm_maps hB = [ (Z_to_bv 64 (T0 - 704512), Z_to_bv 64 s_large);
                 (Z_to_bv 64 (T0 - 434176), Z_to_bv 64 s_small);
                 (Z_to_bv 64 (T0 - 294912), Z_to_bv 64 s_large) ].
Proof. vm_compute. reflexivity. Qed.

Definition famB : word * word -> bool :=
  fam_bases [T0 - 294912; T0 - 434176; T0 - 704512].

Example caseB_premises :
  window_premises_b hB s_small famB (vm_reserved h0) M_AB s_small s_large W_vdso = true.
Proof. vm_compute. reflexivity. Qed.

(** THE ANSWER MOVES UP into the hole... *)
Example caseB_place_small :
  linux_place_b hB false no_hint s_small = Some (T0 - 364544).
Proof. vm_compute. reflexivity. Qed.

(** ...so it differs from the answer to the same request on ledger A... *)
Example caseB_answer_differs : T0 - 364544 <> T0 - 774144.
Proof. unfold T0. lia. Qed.

(** ...and it is in the same window. *)
Lemma caseB_in_window :
  mmap_top hB - fam_window M_AB s_small s_large W_vdso <= T0 - 364544
  /\ T0 - 364544 + s_small <= mmap_top hB.
Proof.
  exact (family_place_in_window_b hB false no_hint s_small (T0 - 364544)
           famB (vm_reserved h0) M_AB s_small s_large W_vdso
           caseB_premises no_hint_address eq_refl caseB_place_small).
Qed.

(* =========================================================================
   C. A gap next to a fixed reservation
   ========================================================================= *)

(** A 64-page PROT_NONE reservation lands directly under the vdso pair,
    then a 16-page MAP_FIXED rw map inside it re-cuts it into three
    ledger entries. *)
Definition res_base : Z := T0 - 286720.
Definition res_len : Z := 262144.

Definition hC2 : VmMaps :=
  mmap_fixed_rw_span_next (grant_none h0 res_len)
    (Z_to_bv 64 (res_base + 65536)) (Z_to_bv 64 65536).

Example caseC_reservation_recut :
  vm_maps hC2 = [ (Z_to_bv 64 (T0 - 221184), Z_to_bv 64 65536);
                  (Z_to_bv 64 (T0 - 286720), Z_to_bv 64 65536);
                  (Z_to_bv 64 (T0 - 155648), Z_to_bv 64 131072) ].
Proof. vm_compute. reflexivity. Qed.

(** A large then a small family map below the reservation; the large
    one, next to the reservation, is unmapped. *)
Definition hC : VmMaps :=
  unmap (grant (grant hC2 s_large) s_small) (T0 - 557056) s_large.

Example caseC_ledger :
  vm_maps hC = [ (Z_to_bv 64 (T0 - 626688), Z_to_bv 64 s_small);
                 (Z_to_bv 64 (T0 - 221184), Z_to_bv 64 65536);
                 (Z_to_bv 64 (T0 - 286720), Z_to_bv 64 65536);
                 (Z_to_bv 64 (T0 - 155648), Z_to_bv 64 131072) ].
Proof. vm_compute. reflexivity. Qed.

Definition famC : word * word -> bool := fam_bases [T0 - 626688].

(** ONE cover interval for the whole reservation, whatever MAP_FIXED did
    inside it. *)
Definition covC : list (word * word) :=
  vm_reserved h0 ++ [(Z_to_bv 64 res_base, Z_to_bv 64 res_len)].

Definition M_C : Z := 339968.
Definition W_O_C : Z := 1110013.

Example caseC_cover_weight : gap_weight s_large covC = W_O_C.
Proof. vm_compute. reflexivity. Qed.

Example caseC_premises :
  window_premises_b hC s_small famC covC M_C s_small s_large W_O_C = true.
Proof. vm_compute. reflexivity. Qed.

(** THE MAP LANDS DIRECTLY UNDER THE RESERVATION. *)
Example caseC_place_small :
  linux_place_b hC false no_hint s_small = Some (res_base - s_small).
Proof. vm_compute. reflexivity. Qed.

Lemma caseC_in_window :
  mmap_top hC - fam_window M_C s_small s_large W_O_C <= res_base - s_small
  /\ res_base - s_small + s_small <= mmap_top hC.
Proof.
  exact (family_place_in_window_b hC false no_hint s_small (res_base - s_small)
           famC covC M_C s_small s_large W_O_C
           caseC_premises no_hint_address eq_refl caseC_place_small).
Qed.

(* =========================================================================
   D. A gap that ends at mmap_top
   ========================================================================= *)

(** The same window top with no vdso pair, so a family map can sit
    directly under [mmap_top].  This ledger is not one a launch gives
    (every launch has the pair at the top); it pins the scan's top
    boundary. *)
Definition hD0 : VmMaps :=
  mkVmMapsFull [] [] [] (Z_to_bv 64 0) (Z_to_bv 64 0) target_alloc_limit
    (vm_mmap_base h0) (vm_init_sp h0).

Example hD0_top : mmap_top hD0 = T0.
Proof. vm_compute. reflexivity. Qed.

(** A large map directly under [mmap_top], a small one under it; the
    large one is unmapped. *)
Definition hD : VmMaps := unmap (grant (grant hD0 s_large) s_small) (T0 - s_large) s_large.

Example caseD_ledger :
  vm_maps hD = [ (Z_to_bv 64 (T0 - 339968), Z_to_bv 64 s_small) ].
Proof. vm_compute. reflexivity. Qed.

Definition famD : word * word -> bool := fam_bases [T0 - 339968].

Example caseD_premises :
  window_premises_b hD s_small famD [] M_C s_small s_large 0 = true.
Proof. vm_compute. reflexivity. Qed.

(** THE MAP LANDS DIRECTLY UNDER [mmap_top]. *)
Example caseD_place_small :
  linux_place_b hD false no_hint s_small = Some (T0 - s_small).
Proof. vm_compute. reflexivity. Qed.

Lemma caseD_in_window :
  mmap_top hD - fam_window M_C s_small s_large 0 <= T0 - s_small
  /\ T0 - s_small + s_small <= mmap_top hD.
Proof.
  exact (family_place_in_window_b hD false no_hint s_small (T0 - s_small)
           famD [] M_C s_small s_large 0
           caseD_premises no_hint_address eq_refl caseD_place_small).
Qed.

(* =========================================================================
   E. The bound W = M + s_max is false
   ========================================================================= *)

Fixpoint grant_n (h : VmMaps) (n : Z) (k : nat) : VmMaps :=
  match k with O => h | Datatypes.S k' => grant_n (grant h n) n k' end.

(** Sixteen small maps from the top: map [i] (1 to 16) is based at
    [T0 - i * s_small]. *)
Definition hE16 : VmMaps := grant_n hD0 s_small 16.

Example caseE_sixteen_maps :
  vm_maps hE16 = List.map (fun i => (Z_to_bv 64 (T0 - i * s_small), Z_to_bv 64 s_small))
                   [16; 15; 14; 13; 12; 11; 10; 9; 8; 7; 6; 5; 4; 3; 2; 1].
Proof. vm_compute. reflexivity. Qed.

(** Twelve of them are unmapped (all but 4, 8, 12 and 16): every hole is
    51 pages, smaller than a large map's 66. *)
Definition hE12 : VmMaps :=
  fold_left (fun h i => unmap h (T0 - i * s_small) s_small)
    [1; 2; 3; 5; 6; 7; 9; 10; 11; 13; 14; 15] hE16.

(** Two large maps; neither fits in a hole, so both land below map 16. *)
Definition hE : VmMaps := grant (grant hE12 s_large) s_large.

Example caseE_ledger :
  vm_maps hE = [ (Z_to_bv 64 (T0 - 1654784), Z_to_bv 64 s_large);
                 (Z_to_bv 64 (T0 - 1384448), Z_to_bv 64 s_large);
                 (Z_to_bv 64 (T0 - 16 * s_small), Z_to_bv 64 s_small);
                 (Z_to_bv 64 (T0 - 12 * s_small), Z_to_bv 64 s_small);
                 (Z_to_bv 64 (T0 - 8 * s_small), Z_to_bv 64 s_small);
                 (Z_to_bv 64 (T0 - 4 * s_small), Z_to_bv 64 s_small) ].
Proof. vm_compute. reflexivity. Qed.

(** [M] is the bytes of the sixteen small maps; the family at the third
    large map's call holds 819,200 of them. *)
Definition M_E : Z := 1114112.

Example caseE_family_bytes :
  gw_sizes (List.filter (fun _ => true) (vm_reserved hE ++ vm_maps hE)) = 819200.
Proof. vm_compute. reflexivity. Qed.

(** The third large map lands at [T0 - 1925120]. *)
Example caseE_place_large :
  linux_place_b hE false no_hint s_large = Some (T0 - 1925120).
Proof. vm_compute. reflexivity. Qed.

(** THE TOO-STRONG CLAIM.  "The family never fragments": a grant of a
    family whose bytes are at most [M], with nothing else in the
    ledger, lands within [M + s_max] of the top. *)
Definition tight_window_claim : Prop :=
  forall (h : VmMaps) (a : Z) (is_fam : word * word -> bool) (M : Z),
    (forall p, In p (vm_reserved h ++ vm_maps h) -> is_fam p = true) ->
    gw_sizes (List.filter is_fam (vm_reserved h ++ vm_maps h)) <= M ->
    (forall p, In p (List.filter is_fam (vm_reserved h ++ vm_maps h)) ->
       s_small <= bv_unsigned (snd p)) ->
    linux_place h false no_hint s_large a ->
    mmap_top h - (M + s_large) <= a.

(** IT IS FALSE: on ledger E it misses by 540,672 bytes. *)
Lemma tight_window_claim_false : ~ tight_window_claim.
Proof.
  intros Hc.
  assert (Hpl : linux_place hE false no_hint s_large (T0 - 1925120)).
  { apply (proj1 (proj1 (linux_place_b_spec hE false no_hint s_large
                           ltac:(unfold s_large; lia) eq_refl) (T0 - 1925120))).
    exact caseE_place_large. }
  pose proof (Hc hE (T0 - 1925120) (fun _ => true) M_E
                (fun _ _ => eq_refl)
                ltac:(rewrite caseE_family_bytes; unfold M_E; lia)) as H.
  assert (Hall : forallb (fun p => s_small <=? bv_unsigned (snd p))
                   (List.filter (fun _ => true) (vm_reserved hE ++ vm_maps hE)) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall.
  assert (Hsz : forall p, In p (List.filter (fun _ => true) (vm_reserved hE ++ vm_maps hE)) ->
                  s_small <= bv_unsigned (snd p)).
  { intros p Hp. apply Z.leb_le. exact (Hall p Hp). }
  specialize (H Hsz Hpl).
  assert (Htop : mmap_top hE = T0) by (vm_compute; reflexivity).
  rewrite Htop in H. unfold M_E, s_large, T0 in H. lia.
Qed.

(** The SAME ledger meets [fam_window]: all its premises hold (with no
    other map, [W_O = 0]), and the grant is in the window. *)
Example caseE_premises :
  window_premises_b hE s_large (fun _ => true) [] M_E s_small s_large 0 = true.
Proof. vm_compute. reflexivity. Qed.

Example caseE_window : fam_window M_E s_small s_large 0 = 5779439.
Proof. vm_compute. reflexivity. Qed.

Lemma caseE_in_window :
  mmap_top hE - fam_window M_E s_small s_large 0 <= T0 - 1925120
  /\ T0 - 1925120 + s_large <= mmap_top hE.
Proof.
  exact (family_place_in_window_b hE false no_hint s_large (T0 - 1925120)
           (fun _ => true) [] M_E s_small s_large 0
           caseE_premises no_hint_address eq_refl caseE_place_large).
Qed.

(* =========================================================================
   F. Without the cover premise the grant escapes
   ========================================================================= *)

(** One 1 MiB rw map on the launch ledger that is neither in the family
    (the family is empty) nor in the cover (the cover is the vdso pair
    only). *)
Definition hF : VmMaps := grant h0 1048576.

Example caseF_ledger :
  vm_maps hF = [ (Z_to_bv 64 (T0 - 1073152), Z_to_bv 64 1048576) ].
Proof. vm_compute. reflexivity. Qed.

Definition famF : word * word -> bool := fun _ => false.

(** With [M = 0] the window is 847,869 bytes. *)
Example caseF_window : fam_window 0 s_small s_large W_vdso = 847869.
Proof. vm_compute. reflexivity. Qed.

(** EVERY PREMISE BUT THE COVER HOLDS... *)
Example caseF_other_premises :
  let L := vm_reserved hF ++ vm_maps hF in
  let T := mmap_top hF in
  let W := fam_window 0 s_small s_large W_vdso in
  ((0 <? s_large) && (s_large <=? s_large) && (s_large mod page_size =? 0)
   && (0 <? s_small) && (gw_sizes (List.filter famF L) <=? 0)
   && forallb (fun p => s_small <=? bv_unsigned (snd p)) (List.filter famF L)
   && (gap_weight s_large (vm_reserved h0) <=? W_vdso)
   && (page_size <=? T - W))%bool = true.
Proof. vm_compute. reflexivity. Qed.

(** ...and the cover premise fails: the 1 MiB map meets the window and
    no cover interval holds it. *)
Example caseF_cover_fails :
  others_covered_b (vm_reserved hF ++ vm_maps hF) famF
    (mmap_top hF - fam_window 0 s_small s_large W_vdso) (mmap_top hF)
    (vm_reserved h0) = false.
Proof. vm_compute. reflexivity. Qed.

Example caseF_place_large :
  linux_place_b hF false no_hint s_large = Some (T0 - 1343488).
Proof. vm_compute. reflexivity. Qed.

(** THE GRANT ESCAPES: the cover premise is false, the grant is Linux's,
    and it lands below the window. *)
Lemma caseF_escapes :
  let W := fam_window 0 s_small s_large W_vdso in
  ~ (forall p, In p (vm_reserved hF ++ vm_maps hF) -> famF p = false ->
       live_at (mmap_top hF - W) p = true ->
       bv_unsigned (fst p) < mmap_top hF ->
       covered_by (vm_reserved h0) p)
  /\ linux_place hF false no_hint s_large (T0 - 1343488)
  /\ T0 - 1343488 < mmap_top hF - W.
Proof.
  cbv zeta. split; [|split].
  - intros Hcov.
    pose proof (proj2 (others_covered_b_iff (vm_reserved hF ++ vm_maps hF) famF
                         (mmap_top hF - fam_window 0 s_small s_large W_vdso) (mmap_top hF)
                         (vm_reserved h0)) Hcov) as Hb.
    rewrite caseF_cover_fails in Hb. discriminate.
  - apply (proj1 (proj1 (linux_place_b_spec hF false no_hint s_large
                           ltac:(unfold s_large; lia) eq_refl) (T0 - 1343488))).
    exact caseF_place_large.
  - vm_compute. reflexivity.
Qed.

(** With the map in the cover, the premises hold again and the window
    grows to hold the grant: the cover's weight is what pays for it. *)
Definition covF : list (word * word) := vm_reserved h0 ++ vm_maps hF.
Definition W_O_F : Z := 1896445.

Example caseF_cover_weight : gap_weight s_large covF = W_O_F.
Proof. vm_compute. reflexivity. Qed.

Example caseF_premises_with_cover :
  window_premises_b hF s_large famF covF 0 s_small s_large W_O_F = true.
Proof. vm_compute. reflexivity. Qed.

Lemma caseF_in_window_with_cover :
  mmap_top hF - fam_window 0 s_small s_large W_O_F <= T0 - 1343488
  /\ T0 - 1343488 + s_large <= mmap_top hF.
Proof.
  exact (family_place_in_window_b hF false no_hint s_large (T0 - 1343488)
           famF covF 0 s_small s_large W_O_F
           caseF_premises_with_cover no_hint_address eq_refl caseF_place_large).
Qed.

(* =========================================================================
   Assumptions
   ========================================================================= *)

(** The baseline: the lemma of [AsanPlacement] this file's argument
    extends. *)
Print Assumptions AsanPlacement.null_hint_grant_above.
Print Assumptions topdown_place_above_cover.
Print Assumptions family_place_in_window.
Print Assumptions family_place_in_window_single.
Print Assumptions family_place_in_window_b.
Print Assumptions tight_window_claim_false.
Print Assumptions caseF_escapes.
Print Assumptions caseA_first_map_is_the_checkers.
Print Assumptions MmapTopFrame.mm_ok_keeps_mmap_top.
