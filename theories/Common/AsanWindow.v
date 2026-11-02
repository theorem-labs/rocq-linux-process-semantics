(* Written by the OSS-Fuzz proof collaborators. *)
(** * AsanWindow — where a NULL-hint grant of a mapping family can land

    [AsanPlacement.null_hint_grant_above] gives a LOWER BOUND on a
    NULL-hint grant, but its high mark only falls: each grant can lower
    it by up to twice its size, so the bound grows with the total size
    of every grant the run makes.  A run that maps and unmaps the same
    family again and again (the ASan secondary allocator's large
    chunks, which the quarantine unmaps in bursts) makes that total grow
    without limit.

    This file bounds the grant by the family's CURRENT size instead.
    The result is a WINDOW below [mmap_top h] whose depth depends only
    on what the ledger holds at the call:

      W = s_max + 4095 + M + (M / s_min) * (s_max + 4095) + W_O

    where [M] bounds the family's mapped bytes, [s_min] bounds each
    family entry from below, [s_max] bounds the request, and [W_O] is
    the [gap_weight] of a cover of everything else in the window.

    ONE LEDGER, ONE CALL.  [linux_place] is called once per mmap, inside
    the [choose] of [Mmap.mmap_spec]'s modeled anonymous arm, on the
    ledger of the model at that step.  So every premise is about the one
    ledger [h] at that one call, and the result holds for any order of
    maps and unmaps that led to it.  The "at every step" content (the
    family's byte bound, the start-up layout) is a reachable-state
    invariant of the consumer, which discharges these premises from it
    at each grant.  [Checks.MmapTopFrame.mm_ok_keeps_mmap_top] shows the
    window's top [mmap_top] does not move across the memory calls, so
    the windows of all the grants of a run are one window.

    THE PROOF reuses [AsanPlacement]'s upward scan ([Section Gap]):
    the scan runs from the window floor [x] to [mmap_top h] instead of
    from [bottomup_floor] to [alloc_ceiling], and a blocked candidate
    jumps past the COVER interval of the entry that blocks it, not past
    the entry.  Then [highest_gap]'s maximality puts Linux's answer at
    or above the fit the scan found, as in [null_hint_grant_above].

    Image-INDEPENDENT; depends only on the specification. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
From LinuxProcessSemantics.Common Require Import AsanPlacement.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(** [lia] slows down by orders of magnitude when the context holds
    [_ mod _ = 0] facts it does not need ([AsanPlacement],
    [Checks.Placement.plia]).  Order goals here drop them first. *)
Local Ltac pagelia :=
  repeat match goal with
  | H : (_ mod page_size = 0)%Z |- _ => clear H
  | H : (_ mod pmd_size = 0)%Z |- _ => clear H
  | H : (_ mod 4096 = 0)%Z |- _ => clear H
  end;
  lia.

(* ========================================================================= *)
(* Covers                                                                     *)
(* ========================================================================= *)

(** A ledger entry [p] lies inside one interval of [cov].  A cover may
    hold one interval for many ledger entries: the start-up PROT_NONE
    reservations are re-cut into several [vm_maps] entries by the
    spanning MAP_FIXED arms ([Mmap.mmap_fixed_rw_span_next],
    [Mmap.mmap_fixed_noaccess_span_next]), and the whole reservation is
    one interval of the cover. *)
Definition covered_by (cov : list (word * word)) (p : word * word) : Prop :=
  exists c t, In (c, t) cov
    /\ bv_unsigned c <= bv_unsigned (fst p)
    /\ bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned c + bv_unsigned t.

Lemma covered_by_app_l : forall c1 c2 p, covered_by c1 p -> covered_by (c1 ++ c2) p.
Proof.
  intros c1 c2 p (c & t & Hin & H1 & H2). exists c, t.
  split; [apply in_or_app; left; exact Hin|]. split; assumption.
Qed.

Lemma covered_by_app_r : forall c1 c2 p, covered_by c2 p -> covered_by (c1 ++ c2) p.
Proof.
  intros c1 c2 p (c & t & Hin & H1 & H2). exists c, t.
  split; [apply in_or_app; right; exact Hin|]. split; assumption.
Qed.

(** Every entry covers itself. *)
Lemma covered_by_self : forall cov p, In p cov -> covered_by cov p.
Proof.
  intros cov [b s] Hin. exists b, s. split; [exact Hin|]. cbn. lia.
Qed.

(* ========================================================================= *)
(* Weights                                                                    *)
(* ========================================================================= *)

(** [gap_weight] grows with the request size. *)
Lemma gap_weight_mono : forall n1 n2 l,
  n1 <= n2 -> gap_weight n1 l <= gap_weight n2 l.
Proof.
  intros n1 n2 l Hn. induction l as [|[b s] l IH]; cbn; lia.
Qed.

(** Entries of at least [s_min] bytes each: their count times [s_min]
    is at most their total size. *)
Lemma count_mul_le_sizes : forall s_min l,
  (forall p, In p l -> s_min <= bv_unsigned (snd p)) ->
  Z.of_nat (length l) * s_min <= gw_sizes l.
Proof.
  intros s_min l. induction l as [|p l IH]; intros H; cbn -[Z.of_nat]; [lia|].
  rewrite Nat2Z.inj_succ.
  pose proof (H p (or_introl eq_refl)) as Hp.
  pose proof (IH (fun q Hq => H q (or_intror Hq))) as Hl. nia.
Qed.

(* ========================================================================= *)
(* The upward scan from an arbitrary floor, stepping on cover intervals       *)
(* ========================================================================= *)

(** The scan invariant at candidate [c] for the ledger [L], the cover
    [cov], the request [nZ], the floor [x] and the ceiling [T]: [c] is a
    page at or above [x], and the weight of the cover intervals still
    live at [c] leaves room for a window of [nZ] below [T]. *)
Definition wscan_inv (cov : list (word * word)) (nZ x T c : Z) : Prop :=
  c mod page_size = 0 /\ x <= c
  /\ c + nZ + gap_weight nZ (List.filter (live_at c) cov) <= T.

(** A fit at [c]: [[c, c + nZ)] is between [x] and [T] and meets no
    entry of [L]. *)
Definition wgap_at (L : list (word * word)) (nZ x T c : Z) : Prop :=
  c mod page_size = 0 /\ x <= c /\ c + nZ <= T
  /\ region_free L (Z_to_bv 64 c) (Z_to_bv 64 nZ) = true.

(** The cover premise: every entry of [L] that is live at [x] (ends
    above [x]) and starts below [T] lies inside an interval of [cov].
    These are exactly the entries that can block a candidate in
    [[x, T)]. *)
Definition covers_window (L cov : list (word * word)) (x T : Z) : Prop :=
  forall p, In p L -> live_at x p = true -> bv_unsigned (fst p) < T ->
    covered_by cov p.

(** One step: [c] is a fit, or some entry of [L] blocks it.  That entry
    is live at [x] and starts below [c + nZ <= T], so a cover interval
    [(ct, tt)] holds it; the next candidate is the page above that
    interval's end, and the interval's own weight pays for the jump. *)
Lemma wscan_ok_or_step : forall L cov nZ x T c,
  0 <= nZ -> T < 2 ^ 64 -> 0 <= x ->
  covers_window L cov x T ->
  wscan_inv cov nZ x T c ->
  wgap_at L nZ x T c
  \/ exists c', wscan_inv cov nZ x T c'
       /\ (length (List.filter (live_at c') cov) < length (List.filter (live_at c) cov))%nat.
Proof.
  intros L cov nZ x T c HnZ HT64 Hx0 Hcov (Hal & Hxc & Hw).
  pose proof (gap_weight_nonneg nZ (List.filter (live_at c) cov) HnZ) as Hw0.
  assert (Hcu : bv_unsigned (Z_to_bv 64 c) = c) by (apply fg_u64_lit; pagelia).
  assert (Hnu : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply fg_u64_lit; pagelia).
  destruct (region_free L (Z_to_bv 64 c) (Z_to_bv 64 nZ)) eqn:Hfree.
  - left. split; [exact Hal|]. split; [exact Hxc|]. split; [pagelia|exact Hfree].
  - right.
    destruct (fg_region_free_false _ _ _ Hfree) as (b & s & Hin & Hov).
    unfold iv_overlap in Hov. rewrite Hcu, Hnu in Hov.
    apply andb_true_iff in Hov as [H1 H2].
    apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
    assert (Hlx : live_at x (b, s) = true)
      by (unfold live_at; cbn; apply Z.ltb_lt; pagelia).
    destruct (Hcov (b, s) Hin Hlx ltac:(cbn; pagelia)) as (ct & tt & Hcin & Hc1 & Hc2).
    cbn in Hc1, Hc2.
    pose proof (page_round_up_Z_ge (bv_unsigned ct + bv_unsigned tt)) as Hge.
    pose proof (page_round_up_Z_aligned (bv_unsigned ct + bv_unsigned tt)) as Hal'.
    assert (Hle : page_round_up_Z (bv_unsigned ct + bv_unsigned tt)
                  <= bv_unsigned ct + bv_unsigned tt + 4095).
    { unfold page_round_up_Z, page_size.
      pose proof (Z.mul_div_le (bv_unsigned ct + bv_unsigned tt + 4096 - 1) 4096
                    ltac:(pagelia)). pagelia. }
    set (c' := page_round_up_Z (bv_unsigned ct + bv_unsigned tt)) in *.
    clearbody c'.
    assert (Hlive : live_at c (ct, tt) = true)
      by (unfold live_at; cbn; apply Z.ltb_lt; pagelia).
    assert (Hdead : live_at c' (ct, tt) = false)
      by (unfold live_at; cbn; apply Z.ltb_ge; pagelia).
    destruct (live_weight_step nZ cov c c' ct tt HnZ ltac:(pagelia) Hcin Hlive Hdead)
      as [Hws Hlen].
    exists c'. split; [|exact Hlen].
    split; [exact Hal'|]. split; pagelia.
Qed.

Lemma wscan : forall L cov nZ x T k c,
  0 <= nZ -> T < 2 ^ 64 -> 0 <= x ->
  covers_window L cov x T ->
  (length (List.filter (live_at c) cov) <= k)%nat ->
  wscan_inv cov nZ x T c ->
  exists g, wgap_at L nZ x T g.
Proof.
  intros L cov nZ x T k. induction k as [|k IH]; intros c HnZ HT64 Hx0 Hcov Hk Hinv.
  - destruct (wscan_ok_or_step L cov nZ x T c HnZ HT64 Hx0 Hcov Hinv)
      as [Hok|(c' & _ & Hlt)]; [|lia].
    exists c. exact Hok.
  - destruct (wscan_ok_or_step L cov nZ x T c HnZ HT64 Hx0 Hcov Hinv)
      as [Hok|(c' & Hinv' & Hlt)].
    + exists c. exact Hok.
    + apply (IH c' HnZ HT64 Hx0 Hcov); [lia|exact Hinv'].
Qed.

(** THE GAP LEMMA ABOVE A FLOOR: a cover with slack [gap_weight] above
    a page-aligned [x] leaves a fit of [nZ] in [[x, T)]. *)
Theorem free_gap_above_cover : forall L cov nZ x T,
  0 <= nZ -> T < 2 ^ 64 -> 0 <= x -> x mod page_size = 0 ->
  covers_window L cov x T ->
  x + nZ + gap_weight nZ cov <= T ->
  exists g, wgap_at L nZ x T g.
Proof.
  intros L cov nZ x T HnZ HT64 Hx0 HxAl Hcov Hslack.
  apply (wscan L cov nZ x T _ x HnZ HT64 Hx0 Hcov (le_n _)).
  split; [exact HxAl|]. split; [apply Z.le_refl|].
  pose proof (gap_weight_filter_le nZ (live_at x) cov HnZ). pagelia.
Qed.

(* ========================================================================= *)
(* The core: a cover with slack above x keeps the top-down answer above x    *)
(* ========================================================================= *)

(** [linux_place] with no hint and the THP guard false is
    [topdown_search] (Mmap.v, [linux_place]: the [g =? 0] branch, then
    the [else] of the THP test). *)
Lemma linux_place_nohint_topdown : forall h thp hint nZ a,
  hint_address hint = 0 ->
  (thp && (nZ mod pmd_size =? 0))%bool = false ->
  linux_place h thp hint nZ a -> topdown_search h nZ a.
Proof.
  intros h thp hint nZ a Hg Hthp Hpl.
  unfold linux_place in Hpl. cbv zeta in Hpl.
  rewrite Hg, Z.eqb_refl in Hpl. cbv iota in Hpl.
  rewrite Hthp in Hpl. exact Hpl.
Qed.

(** A top-down fit [g] puts the top-down answer at or above [g], and in
    the window: the answer is the HIGHEST fit, and the bottom-up
    fallback runs only when there is no fit at all. *)
Lemma topdown_search_above_fit : forall h nZ g a,
  gap_fits (vm_reserved h ++ vm_maps h) page_size (mmap_top h) nZ g ->
  topdown_search h nZ a ->
  g <= a /\ a + nZ <= mmap_top h.
Proof.
  intros h nZ g a Hfit Hts. unfold topdown_search in Hts. cbv zeta in Hts.
  destruct Hts as [[Ha Hmax]|[Hno _]].
  - split; [exact (Hmax g Hfit)|]. destruct Ha as (_ & _ & Hhi & _). exact Hhi.
  - exfalso. exact (Hno g Hfit).
Qed.

(** THE CORE LEMMA.  If every ledger entry that can block a candidate
    in [[x, mmap_top h)] lies inside an interval of [cov], and the
    cover's [gap_weight] leaves room for one more window of [nZ] below
    [mmap_top h], then a NULL-hint, non-THP request of [nZ] bytes lands
    at or above [x], and inside Linux's top-down window. *)
Lemma topdown_place_above_cover : forall (h : VmMaps) (thp : bool) (hint : word)
    (nZ a : Z) (cov : list (word * word)) (x : Z),
  0 < nZ -> nZ mod page_size = 0 ->
  hint_address hint = 0 ->
  (thp && (nZ mod pmd_size =? 0))%bool = false ->
  x mod page_size = 0 -> page_size <= x ->
  (forall p, In p (vm_reserved h ++ vm_maps h) ->
     live_at x p = true -> bv_unsigned (fst p) < mmap_top h ->
     covered_by cov p) ->
  x + nZ + gap_weight nZ cov <= mmap_top h ->
  linux_place h thp hint nZ a ->
  x <= a /\ a + nZ <= mmap_top h.
Proof.
  intros h thp hint nZ a cov x HnZ HnAl Hg Hthp HxAl Hxp Hcov Hslack Hpl.
  pose proof (mmap_top_lt_two_pow_64 h) as Htop64. unfold two_pow_64 in Htop64.
  destruct (free_gap_above_cover (vm_reserved h ++ vm_maps h) cov nZ x (mmap_top h)
              ltac:(pagelia) Htop64 ltac:(unfold page_size in Hxp; pagelia) HxAl Hcov Hslack)
    as (g & HgAl & Hxg & HgT & Hfree).
  assert (Hfit : gap_fits (vm_reserved h ++ vm_maps h) page_size (mmap_top h) nZ g).
  { unfold gap_fits. split; [exact HgAl|]. split; [pagelia|]. split; [exact HgT|exact Hfree]. }
  destruct (topdown_search_above_fit h nZ g a Hfit
              (linux_place_nohint_topdown h thp hint nZ a Hg Hthp Hpl)) as [Hga HaT].
  split; pagelia.
Qed.

(* ========================================================================= *)
(* The window                                                                 *)
(* ========================================================================= *)

(** The window depth for a family whose mapped bytes are at most [M]
    and whose entries are each at least [s_min] bytes, for a request of
    at most [s_max] bytes, with the rest of the window held by a cover
    of gap weight at most [W_O].

    The per-entry slack [s_max + 4095] is [gap_weight]'s own: each
    interval can push the scan past itself, past one spoiled window of
    the request's size, and up to the next page boundary.  [M / s_min]
    bounds the NUMBER of family entries.  The first [s_max + 4095] is
    the request itself and the round-up of the floor to a page. *)
Definition fam_window (M s_min s_max W_O : Z) : Z :=
  s_max + 4095 + M + (M / s_min) * (s_max + 4095) + W_O.

(** THE WINDOW LEMMA.

    - The FAMILY is [is_fam], a classifier the caller supplies: a ledger
      entry is a bare [(word * word)] with no kind field
      ([State.VmMaps]), so membership is the caller's knowledge, not the
      ledger's.
    - [M] COUNTS EVERY FAMILY ENTRY THE LEDGER HOLDS, not only the live
      allocations: [List.filter is_fam L] runs over the whole ledger, so
      an ASan secondary chunk that is quarantined but still mapped is in
      it, and so are its redzones and its guard page.  A consumer must
      bound the quarantined-but-mapped bytes in [M] too.
    - The family premises are about the ledger AT THIS CALL: total bytes
      at most [M], each entry at least [s_min] bytes.  No upper size
      premise on family entries is needed; [s_max] bounds only the
      REQUEST.
    - Everything else that meets the window lies inside [oth_cov].  The
      cover can hold one interval for a whole start-up reservation that
      MAP_FIXED re-cut into many entries.  An entry next to a fixed
      reservation, or a gap that ends at [mmap_top h], needs nothing
      more: the scan steps over the reservation's cover interval, and
      it stops at [mmap_top h].
    - Holds for ANY map/unmap order: the premises are about one ledger,
      and the argument never looks at history. *)
Theorem family_place_in_window :
  forall (h : VmMaps) (thp : bool) (hint : word) (nZ a : Z)
         (is_fam : word * word -> bool) (oth_cov : list (word * word))
         (M s_min s_max W_O : Z),
  let L := vm_reserved h ++ vm_maps h in
  let W := fam_window M s_min s_max W_O in
  (* the request: page-rounded, at most s_max, NULL hint, not the THP path *)
  0 < nZ <= s_max -> nZ mod page_size = 0 ->
  hint_address hint = 0 ->
  (thp && (nZ mod pmd_size =? 0))%bool = false ->
  (* the family, at this call *)
  0 < s_min ->
  gw_sizes (List.filter is_fam L) <= M ->
  (forall p, In p (List.filter is_fam L) -> s_min <= bv_unsigned (snd p)) ->
  (* everything else that meets the window is covered *)
  (forall p, In p L -> is_fam p = false ->
     live_at (mmap_top h - W) p = true ->
     bv_unsigned (fst p) < mmap_top h ->
     covered_by oth_cov p) ->
  gap_weight s_max oth_cov <= W_O ->
  (* the window's floor is a real top-down base *)
  page_size <= mmap_top h - W ->
  linux_place h thp hint nZ a ->
  mmap_top h - W <= a /\ a + nZ <= mmap_top h.
Proof.
  intros h thp hint nZ a is_fam oth_cov M s_min s_max W_O L W
    HnZ HnAl Hg Hthp Hsmin HM Hsz Hoth HWO Hfloor Hpl.
  set (T := mmap_top h) in *.
  set (F := List.filter is_fam L) in *.
  set (q := M / s_min) in *.
  assert (HW : W = s_max + 4095 + M + q * (s_max + 4095) + W_O) by reflexivity.
  clearbody W.
  set (x := page_round_up_Z (T - W)).
  assert (Hx1 : T - W <= x) by (unfold x; apply page_round_up_Z_ge).
  assert (Hx2 : x <= T - W + 4095).
  { unfold x, page_round_up_Z, page_size.
    pose proof (Z.mul_div_le (T - W + 4096 - 1) 4096 ltac:(pagelia)). pagelia. }
  assert (HxAl : x mod page_size = 0) by (unfold x; apply page_round_up_Z_aligned).
  clearbody x.
  (* the family's weight: at most [q] entries, each charged [s_max + 4095] *)
  pose proof (count_mul_le_sizes s_min F Hsz) as Hcnt.
  assert (HcntM : Z.of_nat (length F) <= q).
  { unfold q. apply Z.div_le_lower_bound; [exact Hsmin|]. pagelia. }
  clearbody q.
  assert (Hm1 : Z.of_nat (length F) * (nZ + 4095) <= Z.of_nat (length F) * (s_max + 4095))
    by (apply Z.mul_le_mono_nonneg_l; pagelia).
  assert (Hm2 : Z.of_nat (length F) * (s_max + 4095) <= q * (s_max + 4095))
    by (apply Z.mul_le_mono_nonneg_r; pagelia).
  pose proof (gap_weight_sizes nZ F) as HgF.
  pose proof (gap_weight_mono nZ s_max oth_cov ltac:(pagelia)) as HgO.
  (* the cover: the family covers itself, [oth_cov] holds the rest *)
  assert (Hcov : forall p, In p L -> live_at x p = true -> bv_unsigned (fst p) < T ->
                   covered_by (F ++ oth_cov) p).
  { intros p Hin Hlx Hlt. destruct (is_fam p) eqn:Hf.
    - apply covered_by_app_l, covered_by_self. unfold F. apply filter_In. split; assumption.
    - apply covered_by_app_r. apply (Hoth p Hin Hf); [|exact Hlt].
      unfold live_at in *. apply Z.ltb_lt in Hlx. apply Z.ltb_lt. pagelia. }
  assert (Hxp : page_size <= x) by (unfold page_size in *; pagelia).
  assert (Hslack : x + nZ + gap_weight nZ (F ++ oth_cov) <= T).
  { rewrite gap_weight_app. clear Hcov. pagelia. }
  destruct (topdown_place_above_cover h thp hint nZ a (F ++ oth_cov) x
              ltac:(pagelia) HnAl Hg Hthp HxAl Hxp Hcov Hslack Hpl) as [Hxa HaT].
  change (mmap_top h) with T in HaT.
  split; pagelia.
Qed.

(** ** The single-size instance ([s_min = s_max = n])

    An instance of [family_place_in_window], not a separate argument.  It
    is about 2M, not M: the snapshot argument charges every family entry
    one spoiled window of [n] bytes, which a single-size family never
    actually leaves (a freed slot is exactly refillable).  A tight
    [W = M] needs an invariant over the run, not one ledger. *)
Corollary family_place_in_window_single :
  forall (h : VmMaps) (thp : bool) (hint : word) (n a : Z)
         (is_fam : word * word -> bool) (oth_cov : list (word * word))
         (M W_O : Z),
  let L := vm_reserved h ++ vm_maps h in
  let W := fam_window M n n W_O in
  0 < n -> n mod page_size = 0 ->
  hint_address hint = 0 ->
  (thp && (n mod pmd_size =? 0))%bool = false ->
  gw_sizes (List.filter is_fam L) <= M ->
  (forall p, In p (List.filter is_fam L) -> bv_unsigned (snd p) = n) ->
  (forall p, In p L -> is_fam p = false ->
     live_at (mmap_top h - W) p = true ->
     bv_unsigned (fst p) < mmap_top h ->
     covered_by oth_cov p) ->
  gap_weight n oth_cov <= W_O ->
  page_size <= mmap_top h - W ->
  linux_place h thp hint n a ->
  mmap_top h - W <= a /\ a + n <= mmap_top h.
Proof.
  intros h thp hint n a is_fam oth_cov M W_O L W
    Hn HnAl Hg Hthp HM Hsz Hoth HWO Hfloor Hpl.
  apply (family_place_in_window h thp hint n a is_fam oth_cov M n n W_O);
    try assumption.
  - pagelia.
  - intros p Hp. rewrite (Hsz p Hp). pagelia.
Qed.

(* ========================================================================= *)
(* The premises, decided                                                      *)
(* ========================================================================= *)

(** A boolean twin of [covered_by]. *)
Definition covered_by_b (cov : list (word * word)) (p : word * word) : bool :=
  existsb (fun q => (bv_unsigned (fst q) <=? bv_unsigned (fst p))
                    && (bv_unsigned (fst p) + bv_unsigned (snd p)
                        <=? bv_unsigned (fst q) + bv_unsigned (snd q))) cov.

Lemma covered_by_b_iff : forall cov p,
  covered_by_b cov p = true <-> covered_by cov p.
Proof.
  intros cov p. unfold covered_by_b, covered_by. rewrite existsb_exists. split.
  - intros ([c t] & Hin & H). cbv beta in H. cbn [fst snd] in H.
    apply andb_true_iff in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2.
    exists c, t. split; [exact Hin|]. split; assumption.
  - intros (c & t & Hin & H1 & H2). exists (c, t). split; [exact Hin|].
    cbv beta. cbn [fst snd]. apply andb_true_iff. split; apply Z.leb_le; assumption.
Qed.

(** A boolean twin of the non-family cover premise of
    [family_place_in_window], with the window floor [y] and the top [T]
    as parameters. *)
Definition others_covered_b (L : list (word * word)) (is_fam : word * word -> bool)
    (y T : Z) (cov : list (word * word)) : bool :=
  forallb (fun p => is_fam p || negb (live_at y p) || negb (bv_unsigned (fst p) <? T)
                    || covered_by_b cov p) L.

Lemma others_covered_b_iff : forall L is_fam y T cov,
  others_covered_b L is_fam y T cov = true <->
  (forall p, In p L -> is_fam p = false -> live_at y p = true ->
     bv_unsigned (fst p) < T -> covered_by cov p).
Proof.
  intros L is_fam y T cov. unfold others_covered_b. rewrite forallb_forall. split.
  - intros H p Hin Hf Hl Hlt. specialize (H p Hin). cbv beta in H.
    rewrite <- Z.ltb_lt in Hlt. rewrite Hf, Hl, Hlt in H. cbn [orb negb] in H.
    apply covered_by_b_iff. exact H.
  - intros H p Hin. cbv beta.
    destruct (is_fam p) eqn:Hf; [reflexivity|].
    destruct (live_at y p) eqn:Hl; [|reflexivity].
    destruct (bv_unsigned (fst p) <? T) eqn:Hlt; [|reflexivity].
    cbn [orb negb]. apply covered_by_b_iff.
    apply (H p Hin Hf Hl). apply Z.ltb_lt. exact Hlt.
Qed.

(** Every premise of [family_place_in_window] that is about the ledger
    and the request size, as one boolean.  A caller with a concrete
    ledger decides it by computation. *)
Definition window_premises_b (h : VmMaps) (nZ : Z) (is_fam : word * word -> bool)
    (oth_cov : list (word * word)) (M s_min s_max W_O : Z) : bool :=
  let L := vm_reserved h ++ vm_maps h in
  let T := mmap_top h in
  let W := fam_window M s_min s_max W_O in
  (0 <? nZ) && (nZ <=? s_max) && (nZ mod page_size =? 0) && (0 <? s_min)
  && (gw_sizes (List.filter is_fam L) <=? M)
  && forallb (fun p => s_min <=? bv_unsigned (snd p)) (List.filter is_fam L)
  && others_covered_b L is_fam (T - W) T oth_cov
  && (gap_weight s_max oth_cov <=? W_O)
  && (page_size <=? T - W).

(** [family_place_in_window] for a decided premise set and the
    executable placement [Checks.Placement.linux_place_b]. *)
Theorem family_place_in_window_b :
  forall (h : VmMaps) (thp : bool) (hint : word) (nZ a : Z)
         (is_fam : word * word -> bool) (oth_cov : list (word * word))
         (M s_min s_max W_O : Z),
  window_premises_b h nZ is_fam oth_cov M s_min s_max W_O = true ->
  hint_address hint = 0 ->
  (thp && (nZ mod pmd_size =? 0))%bool = false ->
  linux_place_b h thp hint nZ = Some a ->
  mmap_top h - fam_window M s_min s_max W_O <= a /\ a + nZ <= mmap_top h.
Proof.
  intros h thp hint nZ a is_fam oth_cov M s_min s_max W_O Hb Hg Hthp Hpl.
  unfold window_premises_b in Hb. cbv zeta in Hb.
  repeat rewrite andb_true_iff in Hb.
  destruct Hb as [[[[[[[[H0 H1] H2] H3] H4] H5] H6] H7] H8].
  apply Z.ltb_lt in H0. apply Z.leb_le in H1. apply Z.eqb_eq in H2.
  apply Z.ltb_lt in H3. apply Z.leb_le in H4. rewrite forallb_forall in H5.
  pose proof (proj1 (others_covered_b_iff _ _ _ _ _) H6) as H6'. clear H6.
  apply Z.leb_le in H7. apply Z.leb_le in H8.
  apply (proj1 (linux_place_b_spec h thp hint nZ H0 H2) a) in Hpl.
  apply (family_place_in_window h thp hint nZ a is_fam oth_cov M s_min s_max W_O);
    try assumption.
  - pagelia.
  - intros p Hp. apply Z.leb_le. exact (H5 p Hp).
Qed.

(* ========================================================================= *)
(* The window's top                                                           *)
(* ========================================================================= *)

(** [mmap_top] reads only [vm_mmap_base] and [vm_init_sp]; every
    ledger writer of the memory calls copies both from the ledger it
    rewrites.  [Checks.MmapTopFrame.mm_ok_keeps_mmap_top] is the same
    fact for the calls themselves. *)
Lemma mmap_top_frame : forall h h',
  vm_mmap_base h' = vm_mmap_base h -> vm_init_sp h' = vm_init_sp h ->
  mmap_top h' = mmap_top h.
Proof.
  intros h h' Hb Hs. unfold mmap_top, alloc_top. rewrite Hb, Hs. reflexivity.
Qed.

(** A NULL-hint grant's ledger ([Mmap.mmap_spec]'s modeled arms cons
    [(a, n)] onto [vm_maps]). *)
Lemma mmap_top_grant : forall h a n na,
  mmap_top (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) na
              (vm_start_brk h) (vm_brk h) (vm_limit h)
              (vm_mmap_base h) (vm_init_sp h)) = mmap_top h.
Proof. reflexivity. Qed.

(** The munmap ledger, which is also a destructive MAP_FIXED failure's. *)
Lemma mmap_top_munmap : forall h addr n,
  mmap_top (mmap_fixed_destroyed_next h addr n) = mmap_top h.
Proof. reflexivity. Qed.

Lemma mmap_top_fixed_rw_span : forall h addr n,
  mmap_top (mmap_fixed_rw_span_next h addr n) = mmap_top h.
Proof. reflexivity. Qed.

Lemma mmap_top_fixed_noaccess_span : forall h addr n,
  mmap_top (mmap_fixed_noaccess_span_next h addr n) = mmap_top h.
Proof. reflexivity. Qed.

Lemma mmap_top_fixed_rw : forall h addr n,
  mmap_top (mmap_fixed_rw_next h addr n) = mmap_top h.
Proof. reflexivity. Qed.

Lemma mmap_top_brk : forall h req r,
  mmap_top (brk_model_next h req r) = mmap_top h.
Proof. reflexivity. Qed.

(** WHY A FAILED MUNMAP DOES NOT BREAK A CONSUMER'S SNAPSHOT.  The
    -ENOMEM arm of [Mmap.munmap_spec] returns before any ledger write
    ([e <- errno_from munmap_errnos ;; err_ret e]), so the ledger after
    the call is the ledger before it
    ([Checks.SpuriousCfg.munmap_whole_enomem_admitted] shows the model
    unchanged).  A consumer whose program does not continue past a
    failed munmap (the ASan runtime reports the failure and dies) never
    reaches a later grant from that state, so the family's byte bound
    at the next grant is not affected by it. *)
