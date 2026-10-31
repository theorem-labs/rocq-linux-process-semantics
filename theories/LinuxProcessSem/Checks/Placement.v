(** * LinuxProcessSem.Checks.Placement — Linux's search, as a function

    NOT part of the trusted specification.  [Sys/Mm/Mmap.v] says WHERE a
    fresh mapping goes, relationally, in the words Linux's own comments
    use: the highest fitting page base below [mmap_top], else the lowest
    from [task_unmapped_base] up, with the hint and the transparent
    huge-page rules in front (Linux v6.18.46, commit 1f99e9ab748f,
    mm/mmap.c, [generic_get_unmapped_area_topdown]; mm/vma.c,
    [unmapped_area_topdown] and [unmapped_area]).  This file computes
    that address and proves the computation is the relation.

    WHY BOTH FORMS.  The trusted text has to be read against the kernel
    by a person, so it says "the highest one" rather than walking a
    candidate list.  The checker has to DECIDE whether an address a
    trace reports is the one Linux gives, and a proof that builds an
    execution needs an address in hand.  [linux_place_b] is that
    function and [linux_place_b_spec] is the bridge; nothing else in the
    tree may re-derive either.

    WHY THE CANDIDATE LIST IS COMPLETE.  A fitting base can be slid
    until it meets something.  Slide DOWN and it stops at the window's
    floor or at the page-rounded END of a ledger entry; slide UP and it
    stops at the window's ceiling minus the length, or at the
    page-rounded START of a ledger entry minus the length.  Those are
    the two candidate lists.  [lowest_gap_b_complete] and
    [highest_gap_b_complete] are the two slides.

    The same argument is in [theories/Common/PlacementSearch.v]
    ([higher_fit_b_complete]) for the untrusted proof library.  It is
    written again here because [Checks/] may not import [Common/]: the
    checker is built and extracted without the proof library. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.

(** EVERY ORDER GOAL IN THIS FILE DROPS THE ALIGNMENT HYPOTHESES FIRST.

    Micromega's div/mod preprocessing turns each [_ mod page_size = 0]
    in the context into a product with a fresh quotient, and the
    certificate search then goes nonlinear.
    [theories/Common/PlacementSearch.v] measured 231 s, 100 s and 90 s
    on three such goals, each of which is one [Z.le_trans].  The
    context here carries up to five of them at once.

    So: [plia] for an order goal, [lia] only where an alignment fact is
    part of the argument.  Do not put a bare [lia] back. *)
Ltac plia :=
  repeat match goal with
  | H : (_ mod page_size = 0)%Z |- _ => clear H
  | H : (_ mod pmd_size = 0)%Z |- _ => clear H
  | H : (_ mod 4096 = 0)%Z |- _ => clear H
  | H : (_ mod 2097152 = 0)%Z |- _ => clear H
  end;
  lia.

(* =========================================================================
   Page arithmetic the two slides need
   ========================================================================= *)

Lemma page_round_up_Z_aligned : forall z,
  (page_round_up_Z z mod page_size = 0)%Z.
Proof. intro z. unfold page_round_up_Z. apply Z_mod_mult. Qed.

Lemma page_round_up_Z_ge : forall z, (z <= page_round_up_Z z)%Z.
Proof.
  intro z. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as H.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)). lia.
Qed.

(** The round-up is the LEAST page multiple at or above its argument. *)
Lemma page_round_up_Z_least : forall z b,
  (z <= b)%Z -> (b mod page_size = 0)%Z -> (page_round_up_Z z <= b)%Z.
Proof.
  intros z b Hzb Hb. unfold page_round_up_Z, page_size in *.
  pose proof (Z.div_mod b 4096 ltac:(lia)) as Hd.
  assert (H : ((z + 4096 - 1) / 4096 < b / 4096 + 1)%Z)
    by (apply Z.div_lt_upper_bound; lia).
  lia.
Qed.

Lemma page_round_down_Z_aligned : forall z,
  (page_round_down_Z z mod page_size = 0)%Z.
Proof. intro z. unfold page_round_down_Z. apply Z_mod_mult. Qed.

(** The round-down is the GREATEST page multiple at or below its
    argument — the mirror of [page_round_up_Z_least]. *)
Lemma page_round_down_Z_greatest : forall z b,
  (b <= z)%Z -> (b mod page_size = 0)%Z -> (b <= page_round_down_Z z)%Z.
Proof.
  intros z b Hbz Hb. unfold page_round_down_Z, page_size in *.
  pose proof (Z.div_mod b 4096 ltac:(lia)) as Hd.
  assert (H : (b / 4096 <= z / 4096)%Z)
    by (apply Z.div_le_mono; lia).
  lia.
Qed.

(* =========================================================================
   Folds over a candidate list
   ========================================================================= *)

Lemma fold_max_ge_seed : forall l s, (s <= fold_left Z.max l s)%Z.
Proof.
  induction l as [|x l IH]; intro s; cbn; [lia|].
  pose proof (IH (Z.max s x)). lia.
Qed.

Lemma fold_max_ge_in : forall l s x,
  In x l -> (x <= fold_left Z.max l s)%Z.
Proof.
  induction l as [|y l IH]; intros s x Hin; [contradiction|].
  cbn. destruct Hin as [->|Hin].
  - pose proof (fold_max_ge_seed l (Z.max s x)). lia.
  - now apply IH.
Qed.

Lemma fold_max_le : forall l s b,
  (s <= b)%Z -> (forall x, In x l -> (x <= b)%Z) ->
  (fold_left Z.max l s <= b)%Z.
Proof.
  induction l as [|y l IH]; intros s b Hs Hl; cbn; [exact Hs|].
  apply IH; [|intros x Hx; apply Hl; now right].
  pose proof (Hl y ltac:(now left)). lia.
Qed.

Lemma fold_max_in_or_seed : forall l s,
  fold_left Z.max l s = s \/ In (fold_left Z.max l s) l.
Proof.
  induction l as [|y l IH]; intro s; cbn; [now left|].
  destruct (IH (Z.max s y)) as [Heq|Hin].
  - rewrite Heq. destruct (Z.max_spec s y) as [[_ ->]|[_ ->]];
      [right; now left | now left].
  - right. now right.
Qed.

Lemma fold_min_le_seed : forall l s, (fold_left Z.min l s <= s)%Z.
Proof.
  induction l as [|x l IH]; intro s; cbn; [lia|].
  pose proof (IH (Z.min s x)). lia.
Qed.

Lemma fold_min_le_in : forall l s x,
  In x l -> (fold_left Z.min l s <= x)%Z.
Proof.
  induction l as [|y l IH]; intros s x Hin; [contradiction|].
  cbn. destruct Hin as [->|Hin].
  - pose proof (fold_min_le_seed l (Z.min s x)). lia.
  - now apply IH.
Qed.

Lemma fold_min_ge : forall l s b,
  (b <= s)%Z -> (forall x, In x l -> (b <= x)%Z) ->
  (b <= fold_left Z.min l s)%Z.
Proof.
  induction l as [|y l IH]; intros s b Hs Hl; cbn; [exact Hs|].
  apply IH; [|intros x Hx; apply Hl; now right].
  pose proof (Hl y ltac:(now left)). lia.
Qed.

Lemma fold_min_in_or_seed : forall l s,
  fold_left Z.min l s = s \/ In (fold_left Z.min l s) l.
Proof.
  induction l as [|y l IH]; intro s; cbn; [now left|].
  destruct (IH (Z.min s y)) as [Heq|Hin].
  - rewrite Heq. destruct (Z.min_spec s y) as [[_ ->]|[_ ->]];
      [now left | right; now left].
  - right. now right.
Qed.

(* =========================================================================
   The two candidate lists and the decision procedure over them
   ========================================================================= *)

(** Does a request of [nZ] bytes fit at [g] inside [[lo, hi)]?  The
    boolean twin of [Sys/Mm/Mmap.gap_fits]. *)
Definition gap_fits_b (maps : list (word * word)) (lo hi nZ g : Z) : bool :=
  (g mod page_size =? 0)%Z && (lo <=? g)%Z && (g + nZ <=? hi)%Z
  && region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ).

Lemma gap_fits_b_iff : forall maps lo hi nZ g,
  gap_fits_b maps lo hi nZ g = true <-> gap_fits maps lo hi nZ g.
Proof.
  intros maps lo hi nZ g. unfold gap_fits_b, gap_fits. split.
  - intro H. apply andb_true_iff in H as [H Hfree].
    apply andb_true_iff in H as [H Hhi].
    apply andb_true_iff in H as [Hal Hlo].
    repeat split;
      [now apply Z.eqb_eq | now apply Z.leb_le | now apply Z.leb_le
       | exact Hfree].
  - intros (Hal & Hlo & Hhi & Hfree).
    rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.leb_le _ _) Hlo),
      (proj2 (Z.leb_le _ _) Hhi), Hfree.
    reflexivity.
Qed.

(** Sliding DOWN stops at the floor or at a page-rounded entry end. *)
Definition gap_candidates_lo (maps : list (word * word)) (lo : Z) : list Z :=
  lo :: map (fun p => page_round_up_Z (bv_unsigned (fst p)
                                       + bv_unsigned (snd p))%Z) maps.

(** Sliding UP stops at the ceiling less the length, or at a
    page-rounded entry start less the length. *)
Definition gap_candidates_hi (maps : list (word * word)) (hi nZ : Z)
    : list Z :=
  page_round_down_Z (hi - nZ)
    :: map (fun p => (page_round_down_Z (bv_unsigned (fst p)) - nZ)%Z) maps.

(** The LOWEST fitting base, or [None].  [Z.min] over the fitting
    candidates, seeded with the first one. *)
Definition lowest_gap_b (maps : list (word * word)) (lo hi nZ : Z)
    : option Z :=
  match List.filter (gap_fits_b maps lo hi nZ) (gap_candidates_lo maps lo) with
  | [] => None
  | c :: cs => Some (fold_left Z.min cs c)
  end.

(** The HIGHEST fitting base, or [None]. *)
Definition highest_gap_b (maps : list (word * word)) (lo hi nZ : Z)
    : option Z :=
  match List.filter (gap_fits_b maps lo hi nZ)
          (gap_candidates_hi maps hi nZ) with
  | [] => None
  | c :: cs => Some (fold_left Z.max cs c)
  end.

(** A filtered list's fold stays inside the list, so the answer is a
    candidate that passed the filter. *)
Lemma filter_fold_min_in : forall f l c cs,
  List.filter f l = c :: cs ->
  In (fold_left Z.min cs c) (c :: cs).
Proof.
  intros f l c cs _.
  destruct (fold_min_in_or_seed cs c) as [Heq|Hin]; [rewrite Heq; now left|].
  now right.
Qed.

Lemma filter_fold_max_in : forall f l c cs,
  List.filter f l = c :: cs ->
  In (fold_left Z.max cs c) (c :: cs).
Proof.
  intros f l c cs _.
  destruct (fold_max_in_or_seed cs c) as [Heq|Hin]; [rewrite Heq; now left|].
  now right.
Qed.

(** SOUNDNESS of the lowest search: the answer fits. *)
Lemma lowest_gap_b_fits : forall maps lo hi nZ a,
  lowest_gap_b maps lo hi nZ = Some a -> gap_fits maps lo hi nZ a.
Proof.
  intros maps lo hi nZ a H. unfold lowest_gap_b in H.
  destruct (List.filter (gap_fits_b maps lo hi nZ) (gap_candidates_lo maps lo))
    as [|c cs] eqn:Hf; [discriminate|].
  injection H as <-.
  assert (Hin : In (fold_left Z.min cs c) (c :: cs))
    by (eapply filter_fold_min_in; exact Hf).
  rewrite <- Hf in Hin. apply filter_In in Hin as [_ Hb].
  now apply gap_fits_b_iff.
Qed.

Lemma highest_gap_b_fits : forall maps lo hi nZ a,
  highest_gap_b maps lo hi nZ = Some a -> gap_fits maps lo hi nZ a.
Proof.
  intros maps lo hi nZ a H. unfold highest_gap_b in H.
  destruct (List.filter (gap_fits_b maps lo hi nZ)
              (gap_candidates_hi maps hi nZ)) as [|c cs] eqn:Hf;
    [discriminate|].
  injection H as <-.
  assert (Hin : In (fold_left Z.max cs c) (c :: cs))
    by (eapply filter_fold_max_in; exact Hf).
  rewrite <- Hf in Hin. apply filter_In in Hin as [_ Hb].
  now apply gap_fits_b_iff.
Qed.

(** THE SLIDE DOWN.  Given any fitting base [g], some candidate at or
    below [g] fits too: the greatest candidate that is at or below [g].
    Every entry ending at or below [g] has its page-rounded end among
    the candidates, so it cannot reach past the chosen one; every entry
    ending above [g] starts at or above [g + nZ], else it would have
    met [g]'s own free range. *)
Lemma slide_down : forall maps lo hi nZ g,
  (0 <= lo)%Z -> (0 < nZ)%Z ->
  (lo mod page_size = 0)%Z -> (nZ mod page_size = 0)%Z ->
  (hi < two_pow_64)%Z ->
  gap_fits maps lo hi nZ g ->
  exists c, In c (gap_candidates_lo maps lo)
            /\ gap_fits maps lo hi nZ c /\ (c <= g)%Z.
Proof.
  intros maps lo hi nZ g Hlo0 HnPos HloAl HnAl Hhi64 Hg.
  destruct Hg as (HgAl & Hglo & Hghi & Hgfree).
  assert (HgW : bv_unsigned (Z_to_bv 64 g) = g)
    by (apply bv_unsigned_Z_to_bv_u64; lia).
  assert (HnW : bv_unsigned (Z_to_bv 64 nZ) = nZ)
    by (apply bv_unsigned_Z_to_bv_u64; lia).
  set (cs := List.filter (fun c => (c <=? g)%Z) (gap_candidates_lo maps lo)).
  set (c := fold_left Z.max cs lo).
  assert (Hcs : forall x, In x cs <->
            In x (gap_candidates_lo maps lo) /\ (x <=? g)%Z = true)
    by (intro x; unfold cs; exact (filter_In _ x _)).
  assert (Hclo : (lo <= c)%Z) by (unfold c; apply fold_max_ge_seed).
  assert (Hcg : (c <= g)%Z).
  { unfold c. apply fold_max_le; [plia|]. intros x Hx.
    apply Hcs in Hx. destruct Hx as [_ Hx]. now apply Z.leb_le. }
  assert (Hcand : In c (gap_candidates_lo maps lo)).
  { destruct (fold_max_in_or_seed cs lo) as [Heq|Hin].
    - assert (Heq' : c = lo) by exact Heq. rewrite Heq'. now left.
    - apply Hcs in Hin. exact (proj1 Hin). }
  assert (HcW : bv_unsigned (Z_to_bv 64 c) = c)
    by (apply bv_unsigned_Z_to_bv_u64; plia).
  assert (HcAl : (c mod page_size = 0)%Z).
  { destruct Hcand as [Heq|Hin].
    - rewrite <- Heq. exact HloAl.
    - apply in_map_iff in Hin. destruct Hin as (p & Heq & _).
      rewrite <- Heq. apply page_round_up_Z_aligned. }
  assert (Hcfree : region_free maps (Z_to_bv 64 c) (Z_to_bv 64 nZ) = true).
  { apply region_free_intro. intros b s Hin.
    pose proof (region_free_In _ _ _ _ _ Hgfree Hin) as Hno.
    unfold iv_overlap in *. rewrite HgW, HnW in Hno. rewrite HcW, HnW.
    apply andb_false_iff in Hno.
    set (B := bv_unsigned b) in *. set (S := bv_unsigned s) in *.
    destruct (Z.le_gt_cases (B + S) g) as [Hend|Hend].
    - assert (Hc : In (page_round_up_Z (B + S)) (gap_candidates_lo maps lo)).
      { right. apply in_map_iff. exists (b, s). split; [reflexivity|assumption]. }
      assert (Hcle : (page_round_up_Z (B + S) <= g)%Z)
        by (apply page_round_up_Z_least; assumption).
      assert (Hcc : (page_round_up_Z (B + S) <= c)%Z).
      { unfold c. apply fold_max_ge_in. apply Hcs. split; [assumption|].
        now apply Z.leb_le. }
      pose proof (page_round_up_Z_ge (B + S)) as Hround.
      apply andb_false_iff. left. apply Z.ltb_ge. plia.
    - destruct Hno as [Hno|Hno].
      + apply Z.ltb_ge in Hno. plia.
      + apply Z.ltb_ge in Hno.
        apply andb_false_iff. right. apply Z.ltb_ge. plia. }
  exists c. split; [exact Hcand|]. split; [|exact Hcg].
  repeat split; [exact HcAl | exact Hclo | plia | exact Hcfree].
Qed.

(** THE SLIDE UP, the mirror.  The chosen candidate is the LEAST one at
    or above [g]: the ceiling candidate is one such, and every entry
    starting at or above [g + nZ] offers another.  An entry starting
    below [g + nZ] ends at or below [g], so it cannot meet a range that
    starts at or above [g]. *)
Lemma slide_up : forall maps lo hi nZ g,
  (0 <= lo)%Z -> (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  (hi < two_pow_64)%Z ->
  gap_fits maps lo hi nZ g ->
  exists c, In c (gap_candidates_hi maps hi nZ)
            /\ gap_fits maps lo hi nZ c /\ (g <= c)%Z.
Proof.
  intros maps lo hi nZ g Hlo0 HnPos HnAl Hhi64 Hg.
  destruct Hg as (HgAl & Hglo & Hghi & Hgfree).
  assert (HgW : bv_unsigned (Z_to_bv 64 g) = g)
    by (apply bv_unsigned_Z_to_bv_u64; plia).
  assert (HnW : bv_unsigned (Z_to_bv 64 nZ) = nZ)
    by (apply bv_unsigned_Z_to_bv_u64; plia).
  set (T := page_round_down_Z (hi - nZ)).
  assert (HTAl : (T mod page_size = 0)%Z)
    by (unfold T; apply page_round_down_Z_aligned).
  assert (HgT : (g <= T)%Z)
    by (unfold T; apply page_round_down_Z_greatest; [plia|exact HgAl]).
  set (cs := List.filter (fun c => (g <=? c)%Z) (gap_candidates_hi maps hi nZ)).
  set (c := fold_left Z.min cs T).
  assert (Hcs : forall x, In x cs <->
            In x (gap_candidates_hi maps hi nZ) /\ (g <=? x)%Z = true)
    by (intro x; unfold cs; exact (filter_In _ x _)).
  assert (Hchi : (c <= T)%Z) by (unfold c; apply fold_min_le_seed).
  assert (Hgc : (g <= c)%Z).
  { unfold c. apply fold_min_ge; [exact HgT|]. intros x Hx.
    apply Hcs in Hx. destruct Hx as [_ Hx]. now apply Z.leb_le. }
  assert (Hcand : In c (gap_candidates_hi maps hi nZ)).
  { destruct (fold_min_in_or_seed cs T) as [Heq|Hin].
    - assert (Heq' : c = T) by exact Heq. rewrite Heq'. now left.
    - apply Hcs in Hin. exact (proj1 Hin). }
  assert (HTend : (T + nZ <= hi)%Z).
  { unfold T, page_round_down_Z, page_size.
    pose proof (Z.mul_div_le (hi - nZ) 4096 ltac:(lia)). plia. }
  assert (Hcend : (c + nZ <= hi)%Z) by plia.
  assert (HcW : bv_unsigned (Z_to_bv 64 c) = c)
    by (apply bv_unsigned_Z_to_bv_u64; plia).
  assert (HcAl : (c mod page_size = 0)%Z).
  { destruct Hcand as [Heq|Hin].
    - rewrite <- Heq. exact HTAl.
    - apply in_map_iff in Hin. destruct Hin as (p & Heq & _).
      rewrite <- Heq.
      pose proof (page_round_down_Z_aligned (bv_unsigned (fst p))) as Ha.
      unfold page_size in *.
      rewrite Zminus_mod, Ha, HnAl. reflexivity. }
  assert (Hcfree : region_free maps (Z_to_bv 64 c) (Z_to_bv 64 nZ) = true).
  { apply region_free_intro. intros b s Hin.
    pose proof (region_free_In _ _ _ _ _ Hgfree Hin) as Hno.
    unfold iv_overlap in *. rewrite HgW, HnW in Hno. rewrite HcW, HnW.
    apply andb_false_iff in Hno.
    set (B := bv_unsigned b) in *. set (S := bv_unsigned s) in *.
    destruct (Z.le_gt_cases (g + nZ) B) as [Hstart|Hstart].
    - (* the entry starts above g's range: its rounded start is a
         candidate at or above g, so c cannot reach it *)
      assert (Hc : In (page_round_down_Z B - nZ)%Z
                     (gap_candidates_hi maps hi nZ)).
      { right. apply in_map_iff. exists (b, s). split; [reflexivity|assumption]. }
      assert (HBr : (g + nZ <= page_round_down_Z B)%Z).
      { apply page_round_down_Z_greatest; [exact Hstart|].
        unfold page_size in *. rewrite Zplus_mod, HgAl, HnAl. reflexivity. }
      assert (Hcc : (c <= page_round_down_Z B - nZ)%Z).
      { unfold c. apply fold_min_le_in. apply Hcs. split; [exact Hc|].
        apply Z.leb_le. plia. }
      pose proof (page_round_down_Z_le B) as Hround.
      apply andb_false_iff. right. apply Z.ltb_ge. plia.
    - (* the entry starts below g's end, so it ends at or below g *)
      destruct Hno as [Hno|Hno].
      + apply Z.ltb_ge in Hno.
        apply andb_false_iff. left. apply Z.ltb_ge. plia.
      + apply Z.ltb_ge in Hno. plia. }
  exists c. split; [exact Hcand|]. split; [|exact Hgc].
  repeat split; [exact HcAl | plia | exact Hcend | exact Hcfree].
Qed.

(** COMPLETENESS and EXACTNESS of the lowest search. *)
Lemma lowest_gap_b_spec : forall maps lo hi nZ,
  (0 <= lo)%Z -> (0 < nZ)%Z ->
  (lo mod page_size = 0)%Z -> (nZ mod page_size = 0)%Z ->
  (hi < two_pow_64)%Z ->
  (forall a, lowest_gap_b maps lo hi nZ = Some a <-> lowest_gap maps lo hi nZ a)
  /\ (lowest_gap_b maps lo hi nZ = None
      <-> forall a, ~ gap_fits maps lo hi nZ a).
Proof.
  intros maps lo hi nZ Hlo0 HnPos HloAl HnAl Hhi64.
  assert (Hnone : lowest_gap_b maps lo hi nZ = None
                  <-> forall a, ~ gap_fits maps lo hi nZ a).
  { unfold lowest_gap_b. split.
    - intros H a Ha.
      destruct (List.filter (gap_fits_b maps lo hi nZ)
                  (gap_candidates_lo maps lo)) as [|c cs] eqn:Hf;
        [|discriminate].
      destruct (slide_down maps lo hi nZ a Hlo0 HnPos HloAl HnAl Hhi64 Ha)
        as (c & Hin & Hfit & _).
      assert (Hin' : In c (List.filter (gap_fits_b maps lo hi nZ)
                             (gap_candidates_lo maps lo)))
        by (apply filter_In; split; [exact Hin | now apply gap_fits_b_iff]).
      rewrite Hf in Hin'. contradiction.
    - intro H.
      destruct (List.filter (gap_fits_b maps lo hi nZ)
                  (gap_candidates_lo maps lo)) as [|c cs] eqn:Hf;
        [reflexivity|].
      exfalso.
      assert (Hin : In c (List.filter (gap_fits_b maps lo hi nZ)
                            (gap_candidates_lo maps lo)))
        by (rewrite Hf; now left).
      apply filter_In in Hin as [_ Hb].
      exact (H c (proj1 (gap_fits_b_iff _ _ _ _ _) Hb)). }
  split; [|exact Hnone].
  intro a. split.
  - intro H. split; [now apply lowest_gap_b_fits|].
    intros a' Ha'.
    destruct (slide_down maps lo hi nZ a' Hlo0 HnPos HloAl HnAl Hhi64 Ha')
      as (c & Hin & Hfit & Hle).
    unfold lowest_gap_b in H.
    destruct (List.filter (gap_fits_b maps lo hi nZ)
                (gap_candidates_lo maps lo)) as [|c0 cs] eqn:Hf;
      [discriminate|].
    injection H as <-.
    assert (Hin' : In c (c0 :: cs))
      by (rewrite <- Hf; apply filter_In; split;
          [exact Hin | now apply gap_fits_b_iff]).
    destruct Hin' as [->|Hin'].
    + pose proof (fold_min_le_seed cs c). plia.
    + pose proof (fold_min_le_in cs c0 c Hin'). plia.
  - intros [Hfit Hmin].
    destruct (lowest_gap_b maps lo hi nZ) as [a'|] eqn:Hb.
    + f_equal. pose proof (lowest_gap_b_fits _ _ _ _ _ Hb) as Ha'.
      pose proof (Hmin a' Ha') as H1.
      (* a' is lowest too, by the same argument applied to a *)
      assert (H2 : (a' <= a)%Z).
      { unfold lowest_gap_b in Hb.
        destruct (List.filter (gap_fits_b maps lo hi nZ)
                    (gap_candidates_lo maps lo)) as [|c0 cs] eqn:Hf;
          [discriminate|].
        injection Hb as <-.
        destruct (slide_down maps lo hi nZ a Hlo0 HnPos HloAl HnAl Hhi64 Hfit)
          as (c & Hin & Hcfit & Hle).
        assert (Hin' : In c (c0 :: cs))
          by (rewrite <- Hf; apply filter_In; split;
              [exact Hin | now apply gap_fits_b_iff]).
        destruct Hin' as [->|Hin'].
        - pose proof (fold_min_le_seed cs c). plia.
        - pose proof (fold_min_le_in cs c0 c Hin'). plia. }
      plia.
    + exfalso. exact (proj1 Hnone eq_refl a Hfit).
Qed.

Lemma highest_gap_b_spec : forall maps lo hi nZ,
  (0 <= lo)%Z -> (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  (hi < two_pow_64)%Z ->
  (forall a, highest_gap_b maps lo hi nZ = Some a
             <-> highest_gap maps lo hi nZ a)
  /\ (highest_gap_b maps lo hi nZ = None
      <-> forall a, ~ gap_fits maps lo hi nZ a).
Proof.
  intros maps lo hi nZ Hlo0 HnPos HnAl Hhi64.
  assert (Hnone : highest_gap_b maps lo hi nZ = None
                  <-> forall a, ~ gap_fits maps lo hi nZ a).
  { unfold highest_gap_b. split.
    - intros H a Ha.
      destruct (List.filter (gap_fits_b maps lo hi nZ)
                  (gap_candidates_hi maps hi nZ)) as [|c cs] eqn:Hf;
        [|discriminate].
      destruct (slide_up maps lo hi nZ a Hlo0 HnPos HnAl Hhi64 Ha)
        as (c & Hin & Hfit & _).
      assert (Hin' : In c (List.filter (gap_fits_b maps lo hi nZ)
                             (gap_candidates_hi maps hi nZ)))
        by (apply filter_In; split; [exact Hin | now apply gap_fits_b_iff]).
      rewrite Hf in Hin'. contradiction.
    - intro H.
      destruct (List.filter (gap_fits_b maps lo hi nZ)
                  (gap_candidates_hi maps hi nZ)) as [|c cs] eqn:Hf;
        [reflexivity|].
      exfalso.
      assert (Hin : In c (List.filter (gap_fits_b maps lo hi nZ)
                            (gap_candidates_hi maps hi nZ)))
        by (rewrite Hf; now left).
      apply filter_In in Hin as [_ Hb].
      exact (H c (proj1 (gap_fits_b_iff _ _ _ _ _) Hb)). }
  split; [|exact Hnone].
  intro a. split.
  - intro H. split; [now apply highest_gap_b_fits|].
    intros a' Ha'.
    destruct (slide_up maps lo hi nZ a' Hlo0 HnPos HnAl Hhi64 Ha')
      as (c & Hin & Hfit & Hle).
    unfold highest_gap_b in H.
    destruct (List.filter (gap_fits_b maps lo hi nZ)
                (gap_candidates_hi maps hi nZ)) as [|c0 cs] eqn:Hf;
      [discriminate|].
    injection H as <-.
    assert (Hin' : In c (c0 :: cs))
      by (rewrite <- Hf; apply filter_In; split;
          [exact Hin | now apply gap_fits_b_iff]).
    destruct Hin' as [->|Hin'].
    + pose proof (fold_max_ge_seed cs c). plia.
    + pose proof (fold_max_ge_in cs c0 c Hin'). plia.
  - intros [Hfit Hmax].
    destruct (highest_gap_b maps lo hi nZ) as [a'|] eqn:Hb.
    + f_equal. pose proof (highest_gap_b_fits _ _ _ _ _ Hb) as Ha'.
      pose proof (Hmax a' Ha') as H1.
      assert (H2 : (a <= a')%Z).
      { unfold highest_gap_b in Hb.
        destruct (List.filter (gap_fits_b maps lo hi nZ)
                    (gap_candidates_hi maps hi nZ)) as [|c0 cs] eqn:Hf;
          [discriminate|].
        injection Hb as <-.
        destruct (slide_up maps lo hi nZ a Hlo0 HnPos HnAl Hhi64 Hfit)
          as (c & Hin & Hcfit & Hle).
        assert (Hin' : In c (c0 :: cs))
          by (rewrite <- Hf; apply filter_In; split;
              [exact Hin | now apply gap_fits_b_iff]).
        destruct Hin' as [->|Hin'].
        - pose proof (fold_max_ge_seed cs c). plia.
        - pose proof (fold_max_ge_in cs c0 c Hin'). plia. }
      plia.
    + exfalso. exact (proj1 Hnone eq_refl a Hfit).
Qed.

(** Each of the two searches has at most one answer. *)
Lemma highest_gap_unique : forall maps lo hi nZ a a',
  highest_gap maps lo hi nZ a -> highest_gap maps lo hi nZ a' -> a = a'.
Proof.
  intros maps lo hi nZ a a' [Ha Hmax] [Ha' Hmax'].
  pose proof (Hmax a' Ha'). pose proof (Hmax' a Ha). lia.
Qed.

Lemma lowest_gap_unique : forall maps lo hi nZ a a',
  lowest_gap maps lo hi nZ a -> lowest_gap maps lo hi nZ a' -> a = a'.
Proof.
  intros maps lo hi nZ a a' [Ha Hmin] [Ha' Hmin'].
  pose proof (Hmin a' Ha'). pose proof (Hmin' a Ha). lia.
Qed.

(* =========================================================================
   The ledger's two windows, and the bounds that make them usable
   ========================================================================= *)

(** The search top is below 2^64 and at or above nothing in particular;
    these are the two facts every call of the two [_spec] lemmas needs
    about a real ledger. *)
Lemma mmap_top_lt_two_pow_64 : forall h, (mmap_top h < two_pow_64)%Z.
Proof.
  intro h. unfold mmap_top.
  pose proof (bv_unsigned_in_range 64 (vm_mmap_base h)) as [_ Hhi].
  change (bv_modulus 64) with two_pow_64 in Hhi. lia.
Qed.

Lemma alloc_top_lt_two_pow_64 : forall h, (alloc_top h < two_pow_64)%Z.
Proof.
  intro h. pose proof (alloc_top_room h).
  unfold stack_max_size in *. lia.
Qed.

Lemma page_size_aligned : (page_size mod page_size = 0)%Z.
Proof. reflexivity. Qed.

Lemma task_unmapped_base_aligned : (task_unmapped_base mod page_size = 0)%Z.
Proof. reflexivity. Qed.

Lemma task_unmapped_base_nonneg : (0 <= task_unmapped_base)%Z.
Proof. unfold task_unmapped_base. lia. Qed.

(* =========================================================================
   [topdown_search] and [linux_place], computed
   ========================================================================= *)

(** [generic_get_unmapped_area_topdown] with no hint, as a function. *)
Definition topdown_search_b (h : VmMaps) (nZ : Z) : option Z :=
  let maps := vm_reserved h ++ vm_maps h in
  match highest_gap_b maps page_size (mmap_top h) nZ with
  | Some a => Some a
  | None => lowest_gap_b maps task_unmapped_base (alloc_top h) nZ
  end.

Lemma topdown_search_b_spec : forall h nZ,
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  (forall a, topdown_search_b h nZ = Some a <-> topdown_search h nZ a)
  /\ (topdown_search_b h nZ = None <-> forall a, ~ topdown_search h nZ a).
Proof.
  intros h nZ HnPos HnAl.
  set (maps := vm_reserved h ++ vm_maps h).
  destruct (highest_gap_b_spec maps page_size (mmap_top h) nZ
              ltac:(unfold page_size; lia) HnPos HnAl
              (mmap_top_lt_two_pow_64 h)) as [Hhi1 Hhi2].
  destruct (lowest_gap_b_spec maps task_unmapped_base (alloc_top h) nZ
              task_unmapped_base_nonneg HnPos task_unmapped_base_aligned HnAl
              (alloc_top_lt_two_pow_64 h)) as [Hlo1 Hlo2].
  unfold topdown_search_b, topdown_search. fold maps.
  destruct (highest_gap_b maps page_size (mmap_top h) nZ) as [t|] eqn:Ht.
  - split.
    + intro a. split.
      * intro H. injection H as <-. left. now apply Hhi1.
      * intros [H|[Hno _]].
        -- f_equal.
           exact (highest_gap_unique _ _ _ _ _ _ (proj1 (Hhi1 t) eq_refl) H).
        -- exfalso.
           pose proof (proj1 (Hhi1 t) eq_refl) as [Hfit _].
           exact (Hno t Hfit).
    + split; [discriminate|]. intro H. exfalso.
      exact (H t (or_introl (proj1 (Hhi1 t) eq_refl))).
  - assert (Hno : forall a, ~ gap_fits maps page_size (mmap_top h) nZ a)
      by (exact (proj1 Hhi2 eq_refl)).
    split.
    + intro a. split.
      * intro H. right. split; [exact Hno|]. now apply Hlo1.
      * intros [H|[_ H]].
        -- exfalso. destruct H as [Hfit _]. exact (Hno a Hfit).
        -- now apply Hlo1.
    + split.
      * intros H a [Ha|[_ Ha]].
        -- destruct Ha as [Hfit _]. exact (Hno a Hfit).
        -- exact (proj1 Hlo2 H a (proj1 Ha)).
      * intro H.
        destruct (lowest_gap_b maps task_unmapped_base (alloc_top h) nZ)
          as [a0|] eqn:Hl; [exfalso|reflexivity].
        exact (H a0 (or_intror (conj Hno (proj1 (Hlo1 a0) eq_refl)))).
Qed.

(** WHERE LINUX PUTS IT, computed.  [Sys/Mm/Mmap.linux_place]'s three
    branches, in the same order. *)
Definition linux_place_b (h : VmMaps) (thp : bool) (hint : word) (nZ : Z)
    : option Z :=
  let g := hint_address hint in
  let maps := vm_reserved h ++ vm_maps h in
  if (g =? 0)%Z then
    if thp && (nZ mod pmd_size =? 0)%Z then
      match topdown_search_b h (nZ + pmd_size) with
      | Some ret => Some (thp_align ret)
      | None => topdown_search_b h nZ
      end
    else topdown_search_b h nZ
  else
    if gap_fits_b maps page_size (alloc_top h) nZ g then Some g
    else topdown_search_b h nZ.

(* =========================================================================
   [linux_place_b] is [linux_place]
   ========================================================================= *)

Lemma pmd_size_pos : (0 < pmd_size)%Z.
Proof. unfold pmd_size. lia. Qed.

Lemma mod_pmd_mod_page : forall x,
  (x mod pmd_size = 0)%Z -> (x mod page_size = 0)%Z.
Proof.
  intros x H. apply Z.mod_divide in H; [|unfold pmd_size; lia].
  apply Z.mod_divide; [unfold page_size; lia|].
  apply (Z.divide_trans _ pmd_size); [|exact H].
  exists 512%Z. reflexivity.
Qed.

Lemma thp_align_bounds : forall ret,
  (ret < thp_align ret)%Z /\ (thp_align ret <= ret + pmd_size)%Z.
Proof.
  intro ret. unfold thp_align.
  pose proof (Z.mod_pos_bound ret pmd_size pmd_size_pos).
  destruct (Z.eqb_spec (ret mod pmd_size) 0); lia.
Qed.

Lemma thp_align_pmd : forall ret, (thp_align ret mod pmd_size = 0)%Z.
Proof.
  intro ret. unfold thp_align.
  destruct (Z.eqb_spec (ret mod pmd_size) 0) as [Heq|Hne].
  - rewrite Zplus_mod, Heq, Z_mod_same_full. reflexivity.
  - replace (ret + (pmd_size - ret mod pmd_size))%Z
      with (ret - ret mod pmd_size + pmd_size)%Z by lia.
    rewrite Zplus_mod, Z_mod_same_full, Zminus_mod, Zmod_mod,
      Z.sub_diag. reflexivity.
Qed.

Lemma thp_align_page : forall ret, (thp_align ret mod page_size = 0)%Z.
Proof. intro ret. apply mod_pmd_mod_page, thp_align_pmd. Qed.

(** A free range stays free when it shrinks inside itself.  The THP
    branch needs exactly this: the padded search cleared
    [[ret, ret + nZ + PMD_SIZE)], and the mapping takes the subrange
    [[thp_align ret, thp_align ret + nZ)] of it. *)
Lemma region_free_shrink : forall maps a n a' n',
  region_free maps a n = true ->
  (bv_unsigned a <= bv_unsigned a')%Z ->
  (bv_unsigned a' + bv_unsigned n' <= bv_unsigned a + bv_unsigned n)%Z ->
  region_free maps a' n' = true.
Proof.
  intros maps a n a' n' Hfree Hlo Hhi.
  apply region_free_intro. intros b s Hin.
  pose proof (region_free_In _ _ _ _ _ Hfree Hin) as Hno.
  unfold iv_overlap in *. apply andb_false_iff in Hno.
  apply andb_false_iff.
  destruct Hno as [Hno|Hno]; apply Z.ltb_ge in Hno.
  - left. apply Z.ltb_ge. lia.
  - right. apply Z.ltb_ge. lia.
Qed.

(** The search's answer, read as the old [choose] guard read its
    address.  [page_size <= a] rather than [0 < a] because both windows
    start at or above one page. *)
Lemma topdown_search_admissible : forall h nZ a,
  (0 < nZ)%Z -> topdown_search h nZ a ->
  (a mod page_size = 0)%Z /\ (page_size <= a)%Z
  /\ (a + nZ <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h)
       (Z_to_bv 64 a) (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ a HnPos Hts.
  pose proof (page_round_down_Z_le (alloc_top h)) as Hrd.
  assert (Htop : (mmap_top h <= alloc_top h)%Z)
    by (unfold mmap_top; plia).
  destruct Hts as [[Hfit _]|[_ [Hfit _]]];
    destruct Hfit as (Hal & Hlo & Hhi & Hfree).
  - split; [exact Hal|]. split; [exact Hlo|]. split; [plia|exact Hfree].
  - split; [exact Hal|].
    split; [unfold task_unmapped_base, page_size in *; plia|].
    split; [exact Hhi|exact Hfree].
Qed.

(** THE SEARCH IS A FUNCTION. *)
Lemma topdown_search_unique : forall h nZ a a',
  topdown_search h nZ a -> topdown_search h nZ a' -> a = a'.
Proof.
  intros h nZ a a' Ha Ha'.
  destruct Ha as [Ha|[Hno Ha]]; destruct Ha' as [Ha'|[Hno' Ha']].
  - exact (highest_gap_unique _ _ _ _ _ _ Ha Ha').
  - exfalso. exact (Hno' a (proj1 Ha)).
  - exfalso. exact (Hno a' (proj1 Ha')).
  - exact (lowest_gap_unique _ _ _ _ _ _ Ha Ha').
Qed.

(** THE PLACEMENT IS A FUNCTION, which is the whole point of the
    change: given the ledger, the kernel build and the hint, the model
    has no freedom left in the address. *)
Lemma linux_place_unique : forall h thp hint nZ a a',
  linux_place h thp hint nZ a -> linux_place h thp hint nZ a' -> a = a'.
Proof.
  intros h thp hint nZ a a' Ha Ha'. unfold linux_place in Ha, Ha'.
  cbv zeta in Ha, Ha'.
  destruct (Z.eqb (hint_address hint) 0) eqn:Hg.
  - destruct (thp && (nZ mod pmd_size =? 0)%Z)%bool.
    + destruct Ha as [(ret & Hret & ->)|[Hno Hts]];
        destruct Ha' as [(ret' & Hret' & ->)|[Hno' Hts']].
      * f_equal. exact (topdown_search_unique _ _ _ _ Hret Hret').
      * exfalso. exact (Hno' ret Hret).
      * exfalso. exact (Hno ret' Hret').
      * exact (topdown_search_unique _ _ _ _ Hts Hts').
    + exact (topdown_search_unique _ _ _ _ Ha Ha').
  - destruct Ha as [[Hfit ->]|[Hno Hts]];
      destruct Ha' as [[Hfit' ->]|[Hno' Hts']].
    + reflexivity.
    + exfalso. exact (Hno' Hfit).
    + exfalso. exact (Hno Hfit').
    + exact (topdown_search_unique _ _ _ _ Hts Hts').
Qed.

(** WHAT THE OLD GUARD ASKED FOR, from the new one.  A proof that
    destructed the four conjuncts of the old [choose] applies this and
    goes on unchanged. *)
Lemma linux_place_admissible : forall h thp hint nZ a,
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  linux_place h thp hint nZ a ->
  (a mod page_size = 0)%Z /\ (0 < a)%Z /\ (a + nZ <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h)
       (Z_to_bv 64 a) (Z_to_bv 64 nZ) = true.
Proof.
  intros h thp hint nZ a HnPos HnAl Hpl.
  pose proof (alloc_top_lt_two_pow_64 h) as Hat.
  unfold linux_place in Hpl. cbv zeta in Hpl.
  destruct (Z.eqb (hint_address hint) 0) eqn:Hg.
  - destruct (thp && (nZ mod pmd_size =? 0)%Z)%bool.
    + destruct Hpl as [(ret & Hret & ->)|[_ Hts]].
      * destruct (topdown_search_admissible h (nZ + pmd_size) ret
                    ltac:(pose proof pmd_size_pos; plia) Hret)
          as (Hal & Hlo & Hhi & Hfree).
        pose proof (thp_align_bounds ret) as [Hb1 Hb2].
        pose proof pmd_size_pos as Hpmd.
        assert (HretW : bv_unsigned (Z_to_bv 64 ret) = ret)
          by (apply bv_unsigned_Z_to_bv_u64;
              unfold page_size in Hlo; plia).
        assert (HbigW : bv_unsigned (Z_to_bv 64 (nZ + pmd_size))
                        = (nZ + pmd_size)%Z)
          by (apply bv_unsigned_Z_to_bv_u64;
              unfold page_size in Hlo; plia).
        assert (HaW : bv_unsigned (Z_to_bv 64 (thp_align ret))
                      = thp_align ret)
          by (apply bv_unsigned_Z_to_bv_u64;
              unfold page_size in Hlo; plia).
        assert (HnW : bv_unsigned (Z_to_bv 64 nZ) = nZ)
          by (apply bv_unsigned_Z_to_bv_u64;
              unfold page_size in Hlo; plia).
        repeat split.
        -- apply thp_align_page.
        -- unfold page_size in Hlo. plia.
        -- plia.
        -- apply (region_free_shrink _ (Z_to_bv 64 ret)
                    (Z_to_bv 64 (nZ + pmd_size))); rewrite ?HretW, ?HbigW,
             ?HaW, ?HnW; [exact Hfree|plia|plia].
      * destruct (topdown_search_admissible h nZ a HnPos Hts)
          as (Hal & Hlo & Hhi & Hfree).
        unfold page_size in Hlo.
        repeat split; [exact Hal | plia | exact Hhi | exact Hfree].
    + destruct (topdown_search_admissible h nZ a HnPos Hpl)
        as (Hal & Hlo & Hhi & Hfree).
      unfold page_size in Hlo.
      repeat split; [exact Hal | plia | exact Hhi | exact Hfree].
  - destruct Hpl as [[Hfit ->]|[_ Hts]].
    + destruct Hfit as (Hal & Hlo & Hhi & Hfree).
      unfold page_size in Hlo.
      repeat split; [exact Hal | plia | exact Hhi | exact Hfree].
    + destruct (topdown_search_admissible h nZ a HnPos Hts)
        as (Hal & Hlo & Hhi & Hfree).
      unfold page_size in Hlo.
      repeat split; [exact Hal | lia | exact Hhi | exact Hfree].
Qed.

(** THE RULE HAS AN ANSWER whenever a range of the requested size is
    free in either of Linux's two windows.  This is what a proof that
    has to BUILD an execution needs, and it is why the model refuses
    only where the kernel refuses: a refusal is now exhaustion.

    The OSSV-231 plan states this with [task_unmapped_base <= mmap_top h]
    as a further premise.  It is not needed — the argument never
    compares the two windows — so it is not asked for here, and a
    caller that holds it simply does not have to pass it. *)
Lemma linux_place_exists : forall h thp hint nZ,
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  (exists g, gap_fits (vm_reserved h ++ vm_maps h) page_size (mmap_top h) nZ g
             \/ gap_fits (vm_reserved h ++ vm_maps h) task_unmapped_base
                  (alloc_top h) nZ g) ->
  exists a, linux_place h thp hint nZ a.
Proof.
  intros h thp hint nZ HnPos HnAl Hex.
  (* The plain search has an answer. *)
  assert (Hts : exists a, topdown_search h nZ a).
  { destruct (topdown_search_b_spec h nZ HnPos HnAl) as [Hsome Hnone].
    destruct (topdown_search_b h nZ) as [a|] eqn:Hb;
      [exists a; now apply Hsome|].
    exfalso. destruct Hex as (g & [Hg|Hg]).
    - destruct (highest_gap_b_spec (vm_reserved h ++ vm_maps h) page_size
                  (mmap_top h) nZ ltac:(unfold page_size; lia) HnPos HnAl
                  (mmap_top_lt_two_pow_64 h)) as [Hh1 Hh2].
      destruct (highest_gap_b (vm_reserved h ++ vm_maps h) page_size
                  (mmap_top h) nZ) as [t|] eqn:Ht.
      + apply (proj1 Hnone eq_refl t). left. now apply Hh1.
      + exact (proj1 Hh2 eq_refl g Hg).
    - destruct (lowest_gap_b_spec (vm_reserved h ++ vm_maps h)
                  task_unmapped_base (alloc_top h) nZ
                  task_unmapped_base_nonneg HnPos task_unmapped_base_aligned
                  HnAl (alloc_top_lt_two_pow_64 h)) as [Hl1 Hl2].
      destruct (lowest_gap_b (vm_reserved h ++ vm_maps h) task_unmapped_base
                  (alloc_top h) nZ) as [t|] eqn:Ht.
      + destruct (highest_gap_b_spec (vm_reserved h ++ vm_maps h) page_size
                    (mmap_top h) nZ ltac:(unfold page_size; lia) HnPos HnAl
                    (mmap_top_lt_two_pow_64 h)) as [Hh1 Hh2].
        destruct (highest_gap_b (vm_reserved h ++ vm_maps h) page_size
                    (mmap_top h) nZ) as [u|] eqn:Hu.
        * apply (proj1 Hnone eq_refl u). left. now apply Hh1.
        * apply (proj1 Hnone eq_refl t). right.
          split; [now apply Hh2 | now apply Hl1].
      + exact (proj1 Hl2 eq_refl g Hg). }
  unfold linux_place. cbv zeta.
  destruct (Z.eqb (hint_address hint) 0) eqn:Hg.
  - destruct (thp && (nZ mod pmd_size =? 0)%Z)%bool.
    + assert (HpadPos : (0 < nZ + pmd_size)%Z)
        by (pose proof pmd_size_pos; lia).
      assert (HpadAl : ((nZ + pmd_size) mod page_size = 0)%Z).
      { rewrite Zplus_mod, HnAl.
        rewrite (mod_pmd_mod_page pmd_size (Z_mod_same_full pmd_size)).
        reflexivity. }
      destruct (topdown_search_b_spec h (nZ + pmd_size) HpadPos HpadAl)
        as [Hq1 Hq2].
      destruct (topdown_search_b h (nZ + pmd_size)) as [ret|] eqn:Hq.
      * exists (thp_align ret). left. exists ret.
        split; [now apply Hq1 | reflexivity].
      * destruct Hts as (a & Ha). exists a. right.
        split; [now apply Hq2 | exact Ha].
    + exact Hts.
  - destruct (gap_fits_b (vm_reserved h ++ vm_maps h) page_size (alloc_top h)
                nZ (hint_address hint)) eqn:Hf.
    + exists (hint_address hint). left.
      split; [now apply gap_fits_b_iff | reflexivity].
    + destruct Hts as (a & Ha). exists a. right. split; [|exact Ha].
      intro Hc. rewrite (proj2 (gap_fits_b_iff _ _ _ _ _) Hc) in Hf.
      discriminate.
Qed.

(* =========================================================================
   The checker's view: computing the answer decides the question
   ========================================================================= *)

Lemma linux_place_b_spec : forall h thp hint nZ,
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  (forall a, linux_place_b h thp hint nZ = Some a
             <-> linux_place h thp hint nZ a)
  /\ (linux_place_b h thp hint nZ = None
      <-> forall a, ~ linux_place h thp hint nZ a).
Proof.
  intros h thp hint nZ HnPos HnAl.
  pose proof pmd_size_pos as Hpmd.
  assert (HpadPos : (0 < nZ + pmd_size)%Z) by lia.
  assert (HpadAl : ((nZ + pmd_size) mod page_size = 0)%Z).
  { rewrite Zplus_mod, HnAl.
    rewrite (mod_pmd_mod_page pmd_size (Z_mod_same_full pmd_size)).
    reflexivity. }
  destruct (topdown_search_b_spec h nZ HnPos HnAl) as [Hp1 Hp2].
  destruct (topdown_search_b_spec h (nZ + pmd_size) HpadPos HpadAl)
    as [Hq1 Hq2].
  unfold linux_place_b, linux_place. cbv zeta.
  destruct (Z.eqb (hint_address hint) 0) eqn:Hg.
  - destruct (thp && (nZ mod pmd_size =? 0)%Z)%bool.
    + destruct (topdown_search_b h (nZ + pmd_size)) as [ret|] eqn:Hq.
      * assert (Hret : topdown_search h (nZ + pmd_size) ret)
          by (now apply Hq1).
        split.
        -- intro a. split.
           ++ intro H. injection H as <-. left. exists ret.
              split; [exact Hret|reflexivity].
           ++ intros [(ret' & Hret' & ->)|[Hno _]].
              ** f_equal. f_equal.
                 exact (topdown_search_unique _ _ _ _ Hret Hret').
              ** exfalso. exact (Hno ret Hret).
        -- split; [discriminate|]. intro H. exfalso.
           exact (H (thp_align ret)
                    (or_introl (ex_intro _ ret (conj Hret eq_refl)))).
      * assert (Hno : forall ret, ~ topdown_search h (nZ + pmd_size) ret)
          by (now apply Hq2).
        split.
        -- intro a. split.
           ++ intro H. right. split; [exact Hno|]. now apply Hp1.
           ++ intros [(ret' & Hret' & _)|[_ H]].
              ** exfalso. exact (Hno ret' Hret').
              ** now apply Hp1.
        -- split.
           ++ intros H a [(ret' & Hret' & _)|[_ Ha]].
              ** exact (Hno ret' Hret').
              ** exact (proj1 Hp2 H a Ha).
           ++ intro H. apply Hp2. intros a Ha.
              exact (H a (or_intror (conj Hno Ha))).
    + exact (conj Hp1 Hp2).
  - destruct (gap_fits_b (vm_reserved h ++ vm_maps h) page_size (alloc_top h)
                nZ (hint_address hint)) eqn:Hf.
    + assert (Hfit : gap_fits (vm_reserved h ++ vm_maps h) page_size
                       (alloc_top h) nZ (hint_address hint))
        by (now apply gap_fits_b_iff).
      split.
      * intro a. split.
        -- intro H. injection H as <-. left. split; [exact Hfit|reflexivity].
        -- intros [[_ ->]|[Hno _]]; [reflexivity|exfalso; exact (Hno Hfit)].
      * split; [discriminate|]. intro H. exfalso.
        exact (H (hint_address hint) (or_introl (conj Hfit eq_refl))).
    + assert (Hno : ~ gap_fits (vm_reserved h ++ vm_maps h) page_size
                      (alloc_top h) nZ (hint_address hint)).
      { intro Hc. rewrite (proj2 (gap_fits_b_iff _ _ _ _ _) Hc) in Hf.
        discriminate. }
      split.
      * intro a. split.
        -- intro H. right. split; [exact Hno|]. now apply Hp1.
        -- intros [[Hc _]|[_ H]]; [exfalso; exact (Hno Hc)|now apply Hp1].
      * split.
        -- intros H a [[Hc _]|[_ Ha]];
             [exact (Hno Hc) | exact (proj1 Hp2 H a Ha)].
        -- intro H. apply Hp2. intros a Ha.
           exact (H a (or_intror (conj Hno Ha))).
Qed.

(** THE CHECKER'S ONE TEST: is the address a trace reports the address
    Linux gives?  Written over the returned [word] so that
    [Checks.Sys.Mm.Mmap] and [Checks.Sys.Mm.Mremap] carry no [option]
    plumbing. *)
Definition linux_place_is (h : VmMaps) (thp : bool) (hint : word) (nZ : Z)
    (r : word) : bool :=
  match linux_place_b h thp hint nZ with
  | Some a => (a =? bv_unsigned r)%Z
  | None => false
  end.

Lemma linux_place_is_iff : forall h thp hint nZ r,
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  (linux_place_is h thp hint nZ r = true
   <-> linux_place h thp hint nZ (bv_unsigned r)).
Proof.
  intros h thp hint nZ r HnPos HnAl.
  destruct (linux_place_b_spec h thp hint nZ HnPos HnAl) as [Hsome Hnone].
  unfold linux_place_is.
  destruct (linux_place_b h thp hint nZ) as [a|] eqn:Hb.
  - split.
    + intro H. apply Z.eqb_eq in H. subst a. now apply Hsome.
    + intro H. apply Z.eqb_eq.
      exact (linux_place_unique _ _ _ _ _ _ (proj1 (Hsome a) eq_refl) H).
  - split; [discriminate|]. intro H. exfalso.
    exact (proj1 Hnone eq_refl _ H).
Qed.

(** The checker's test implies the four facts the old guard asked for,
    in one step, for the proofs in [Checks/Sys/Mm/]. *)
Lemma linux_place_is_admissible : forall h thp hint nZ r,
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  linux_place_is h thp hint nZ r = true ->
  (bv_unsigned r mod page_size = 0)%Z /\ (0 < bv_unsigned r)%Z
  /\ (bv_unsigned r + nZ <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h) r (Z_to_bv 64 nZ) = true.
Proof.
  intros h thp hint nZ r HnPos HnAl H.
  apply (linux_place_is_iff h thp hint nZ r HnPos HnAl) in H.
  destruct (linux_place_admissible h thp hint nZ (bv_unsigned r) HnPos HnAl H)
    as (Hal & Hpos & Hhi & Hfree).
  assert (Hr : Z_to_bv 64 (bv_unsigned r) = r)
    by (apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small;
        apply bv_unsigned_in_range).
  rewrite Hr in Hfree.
  repeat split; assumption.
Qed.

(** * THE vDSO PAIR UNDER LOAD

    [State] proves four general facts about the pair that [execve]
    installs ([State.vdso_reserved]; arch/riscv/kernel/vdso.c,
    [arch_setup_additional_pages], Linux v6.18.46, commit
    1f99e9ab748f): [vdso_reserved_above], [vdso_reserved_nonzero],
    [vdso_len_page] and [vdso_reserved_entry_ok].  Until this section
    NOTHING IN THE MODEL USED ANY OF THEM.  The vDSO proofs that exist
    reach the same facts by inline argument: [Common.AsanInit]'s
    [resx_eq] unfolds [State.vdso_reserved] and computes the pair for
    [State.default_kernel], and the fixtures in
    [Checks.Cases.Mm.PlacementHoles] are concrete.

    A lemma nothing uses is not merely dead weight.  It has never had
    to discharge an obligation, and an obligation is the one test that
    exposes a statement too weak to use — a premise no caller can
    produce, or a conclusion that stops just short of the fact a caller
    needs.  The four below are the obligations, one for each, and they
    are general in the kernel build where the fixtures are not. *)

(** A rounded address is a page base.  [page_round_down_Z_le],
    [_mono], [_idem] and [_min_r] above say where rounding puts an
    address; this says what it leaves. *)
Lemma page_round_down_Z_mod : forall x,
  (page_round_down_Z x mod page_size = 0)%Z.
Proof.
  intro x. unfold page_round_down_Z, page_size. apply Z_mod_mult.
Qed.

(** The pair's hull starts on a page when its top is a page base,
    because the pair's width is a whole number of pages
    ([State.vdso_len_page]).  A port that has to place something below
    the pair needs the base, not the top. *)
Lemma vdso_hull_base_page : forall kb top,
  (top mod page_size = 0)%Z ->
  ((top - vdso_len kb) mod page_size = 0)%Z.
Proof.
  intros kb top Htop.
  rewrite Zminus_mod, Htop, (vdso_len_page kb). reflexivity.
Qed.

(** WHERE THE PAIR'S TOP IS FOR A LAUNCH, written once.  This is the
    expression [State.init_reserved] uses — the model it is building
    does not exist yet, so [State.vdso_top] cannot be called on it —
    and [State.vdso_top_init_model] is the proof that the finished
    model agrees.  Named rather than written out at each premise so
    that a caller may [apply] these lemmas without a [zeta] step. *)
Definition launch_vdso_top (mbase sp : word) : Z :=
  page_round_down_Z
    (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)).

(** THE LAUNCH'S LEDGER HAS NO ZERO-WIDTH ENTRY when the image's own
    reservations have none.  [State.entries_nonzero] is what stops an
    entry closing a [region_free] gate over a range it holds no byte
    of, and [State.init_reserved] appends the pair to the image's list,
    so the pair has to carry its half: [State.vdso_reserved_nonzero].

    The only premise about the top is the 64-bit bound, which is why
    this is the form a fixture can use — it needs no alignment and no
    room hypothesis. *)
Lemma init_reserved_nonzero : forall reserved mbase sp kb,
  entries_nonzero reserved ->
  (launch_vdso_top mbase sp < two_pow_64)%Z ->
  entries_nonzero (init_reserved reserved mbase sp kb).
Proof.
  intros reserved mbase sp kb Hres Htop a n Hin.
  unfold init_reserved in Hin. apply in_app_or in Hin as [Hin | Hin].
  - exact (Hres a n Hin).
  - exact (vdso_reserved_nonzero _ _ _ _ Htop Hin).
Qed.

(** EVERY ENTRY OF THE LAUNCH'S LEDGER IS THE IMAGE'S OR LIES IN THE
    PAIR'S HULL.  [State.vdso_reserved_above] is the second half.  A
    proof that a range misses the whole ledger splits here: it argues
    about the image's segments, and about one interval for the pair. *)
Lemma init_reserved_entry_place : forall reserved mbase sp kb a n,
  (launch_vdso_top mbase sp < two_pow_64)%Z ->
  In (a, n) (init_reserved reserved mbase sp kb) ->
  In (a, n) reserved
  \/ ((launch_vdso_top mbase sp - vdso_len kb <= bv_unsigned a)%Z
      /\ (bv_unsigned a + bv_unsigned n <= launch_vdso_top mbase sp)%Z).
Proof.
  intros reserved mbase sp kb a n Htop Hin.
  unfold init_reserved in Hin. apply in_app_or in Hin as [Hin | Hin].
  - left. exact Hin.
  - right. exact (vdso_reserved_above _ _ _ _ Htop Hin).
Qed.

(** EVERYTHING AN ENTRY OF THE LAUNCH'S LEDGER PROMISES, in one
    lemma: it names at least one byte, it starts and ends on a page,
    and the pair's hull starts on a page too.  This is
    [State.vdso_reserved_entry_ok] put under the obligation it was
    written for, with the alignment premise discharged rather than
    assumed — [page_round_down_Z_mod] supplies it, because
    [State.init_reserved] rounds the top itself.

    The room premise is the condition under which
    [State.vdso_reserved] emits anything at all, and it is the one
    premise a caller must carry.  Say so here rather than letting a
    port discover it. *)
Lemma init_reserved_entry_ok : forall reserved mbase sp kb a n,
  (page_size + vdso_len kb <= launch_vdso_top mbase sp)%Z ->
  (launch_vdso_top mbase sp < two_pow_64)%Z ->
  (forall b m, In (b, m) reserved ->
     (0 < bv_unsigned m)%Z /\ (bv_unsigned b mod page_size = 0)%Z
     /\ (bv_unsigned m mod page_size = 0)%Z) ->
  In (a, n) (init_reserved reserved mbase sp kb) ->
  (0 < bv_unsigned n)%Z
  /\ (bv_unsigned a mod page_size = 0)%Z
  /\ (bv_unsigned n mod page_size = 0)%Z
  /\ ((launch_vdso_top mbase sp - vdso_len kb) mod page_size = 0)%Z.
Proof.
  intros reserved mbase sp kb a n Hroom Htop Hres Hin.
  assert (Hal : (launch_vdso_top mbase sp mod page_size = 0)%Z)
    by apply page_round_down_Z_mod.
  pose proof (vdso_hull_base_page kb _ Hal) as Hhull.
  unfold init_reserved in Hin. apply in_app_or in Hin as [Hin | Hin].
  - destruct (Hres a n Hin) as (H1 & H2 & H3). repeat split; assumption.
  - destruct (vdso_reserved_entry_ok kb _ a n Hroom Htop Hal Hin)
      as (H1 & H2 & H3 & _ & _).
    repeat split; assumption.
Qed.

(** THE ADDRESS THE RULE CHOOSES MISSES THE PAIR, for EVERY kernel
    build.  The fixtures in [Checks.Cases.Mm.PlacementHoles] show this
    for [State.default_kernel] by computation; this is the general
    statement, and it is the one a port needs, because a port's build
    is not the fixture's.

    The ledger is split as the image's entries and the pair, which is
    the shape [State.vm_reserved_init_model] gives for a launch and
    which every later state keeps: no step of the model removes a
    reservation. *)
Lemma linux_place_misses_vdso : forall h thp hint nZ r kb rest a n,
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z -> (nZ < two_pow_64)%Z ->
  vm_reserved h = rest ++ vdso_reserved kb (vdso_top h) ->
  linux_place_is h thp hint nZ r = true ->
  In (a, n) (vdso_reserved kb (vdso_top h)) ->
  (bv_unsigned r + nZ <= bv_unsigned a)%Z
  \/ (bv_unsigned a + bv_unsigned n <= bv_unsigned r)%Z.
Proof.
  intros h thp hint nZ r kb rest a n HnPos HnAl HnB Hres H Hin.
  destruct (linux_place_is_admissible h thp hint nZ r HnPos HnAl H)
    as (_ & _ & _ & Hfree).
  assert (Hin' : In (a, n) (vm_reserved h ++ vm_maps h)).
  { apply in_or_app. left. rewrite Hres. apply in_or_app. right. exact Hin. }
  pose proof (region_free_In _ _ _ _ _ Hfree Hin') as Hov.
  unfold iv_overlap in Hov.
  rewrite bv_unsigned_Z_to_bv_u64 in Hov by (unfold two_pow_64 in *; lia).
  apply andb_false_iff in Hov as [Hf | Hf]; apply Z.ltb_ge in Hf.
  - right. exact Hf.
  - left. exact Hf.
Qed.
