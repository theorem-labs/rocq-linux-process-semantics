(** * LinuxProcessSem.Checks.VdsoDisjoint — no recorded mapping meets the vDSO pair

    The pair section at the top of [Sys/Mm/Mmap.v] lets an arm whose
    range lies inside one recorded mapping skip the pair test: the exact
    munmap, the contained MAP_FIXED, and the mprotect, madvise and mremap
    sources.  That is sound only if no [vm_maps] entry meets a mapped
    range of [State.m_vdso].  This file proves it of every configuration
    a run reaches ([init_config_star_vdso_maps_disjoint]).

    THE INVARIANT HAS A SECOND HALF.  A brk grow records [[old, r)] but
    tests only the whole pages it installs, [[PAGE_ALIGN old, PAGE_ALIGN
    r)], and the page above them ([Mmap.brk_grow_ok]); a grow inside one
    page is tested by neither Linux nor the model.  So the invariant also
    says that the heap, [[start_brk, PAGE_ALIGN brk)], misses the pair
    ([vdso_heap_clear]), and that [0 < start_brk <= brk]: [brk_grow_ok]
    tests nothing while the break is 0, so a run that started there could
    move its break into the pair and then grow inside that page.

    THE START OF A RUN satisfies it when the initial break is page
    aligned ([Run.valid_brk]) and nonzero: the ledger is empty and the
    heap range is [[brk0, brk0)].  The break is nonzero when the image
    loads a byte, since [valid_brk] puts it at or above
    [reserved_top]. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run MemImageType StackLayout.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs VmMapsDisjoint MapsFit NoaccessOwned.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* -------------------------------------------------------------------------
   Ranges against the pair, byte by byte
   ------------------------------------------------------------------------- *)

(** One range of the pair against [[lo, hi)]: the [z_ranges_meet] test is
    false exactly when no byte of [[lo, hi)] is a byte of the range. *)
Lemma range_meets_false_bytes : forall (b : bool) lo hi p q,
  (b && z_ranges_meet lo hi p q)%bool = false <->
  (forall x, lo <= x < hi -> (b && (p <=? x) && (x <? q))%bool = false).
Proof.
  intros b lo hi p q. destruct b; cbn [andb]; [|split; intros; reflexivity].
  unfold z_ranges_meet. split.
  - intros H x Hx. apply Z.ltb_ge in H.
    destruct (p <=? x) eqn:E1; [|reflexivity]. apply Z.leb_le in E1.
    cbn [andb]. apply Z.ltb_ge. lia.
  - intros H. apply Z.ltb_ge.
    destruct (Z.le_gt_cases (Z.min hi q) (Z.max lo p)) as [Hle|Hgt]; [exact Hle|].
    exfalso. specialize (H (Z.max lo p) ltac:(lia)).
    rewrite (proj2 (Z.leb_le p (Z.max lo p)) ltac:(lia)) in H. cbn [andb] in H.
    apply Z.ltb_ge in H. lia.
Qed.

Lemma vdso_meets_false_bytes : forall v lo hi,
  vdso_meets v lo hi = false <->
  (forall x, lo <= x < hi -> vdso_byte v x = false).
Proof.
  intros v lo hi. unfold vdso_meets, vdso_byte. split.
  - intros H x Hx. apply orb_false_iff in H as [H1 H2]. apply orb_false_iff. split.
    + exact (proj1 (range_meets_false_bytes _ _ _ _ _) H1 x Hx).
    + exact (proj1 (range_meets_false_bytes _ _ _ _ _) H2 x Hx).
  - intros H. apply orb_false_iff. split.
    + apply (proj2 (range_meets_false_bytes _ _ _ _ _)). intros x Hx.
      exact (proj1 (proj1 (orb_false_iff _ _) (H x Hx))).
    + apply (proj2 (range_meets_false_bytes _ _ _ _ _)). intros x Hx.
      exact (proj2 (proj1 (orb_false_iff _ _) (H x Hx))).
Qed.

Lemma vdso_meets_empty : forall v lo hi, hi <= lo -> vdso_meets v lo hi = false.
Proof. intros v lo hi H. apply vdso_meets_false_bytes. intros x Hx. lia. Qed.

(** Two ranges that miss the pair, end to start, make one. *)
Lemma vdso_meets_union : forall v lo mid hi,
  vdso_meets v lo mid = false -> vdso_meets v mid hi = false ->
  vdso_meets v lo hi = false.
Proof.
  intros v lo mid hi H1 H2. apply vdso_meets_false_bytes. intros x Hx.
  destruct (Z.lt_ge_cases x mid).
  - exact (proj1 (vdso_meets_false_bytes _ _ _) H1 x ltac:(lia)).
  - exact (proj1 (vdso_meets_false_bytes _ _ _) H2 x ltac:(lia)).
Qed.

(** [Mmap.vdso_meets_narrow] with the known range first, so the bounds
    are plain goals. *)
Lemma vdso_meets_within : forall v lo' hi' lo hi,
  vdso_meets v lo' hi' = false -> lo' <= lo -> hi <= hi' ->
  vdso_meets v lo hi = false.
Proof. intros v lo' hi' lo hi H H1 H2. exact (vdso_meets_narrow v lo hi lo' hi' H1 H2 H). Qed.

Lemma bool_cut4 : forall p c l u q d l' u' : bool,
  (p && c && l && u || q && d && l' && u')%bool = true ->
  (p && l && u || q && l' && u')%bool = true.
Proof.
  intros p c l u q d l' u'.
  destruct p, c, l, u, q, d, l', u'; cbn; intros H; solve [reflexivity | discriminate H].
Qed.

(** [vdso_cut] only clears bits. *)
Lemma vdso_byte_cut : forall v a b x,
  vdso_byte (vdso_cut v a b) x = true -> vdso_byte v x = true.
Proof. intros v a b x H. exact (bool_cut4 _ _ _ _ _ _ _ _ H). Qed.

Lemma vdso_meets_cut_mono : forall v a b lo hi,
  vdso_meets v lo hi = false -> vdso_meets (vdso_cut v a b) lo hi = false.
Proof.
  intros v a b lo hi H. apply vdso_meets_false_bytes. intros x Hx.
  destruct (vdso_byte (vdso_cut v a b) x) eqn:E; [|reflexivity].
  apply vdso_byte_cut in E.
  rewrite (proj1 (vdso_meets_false_bytes _ _ _) H x Hx) in E. discriminate E.
Qed.

Ltac zb_hyps :=
  repeat match goal with
  | H : (_ <? _)%Z = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _)%Z = false |- _ => apply Z.ltb_ge in H
  | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _)%Z = false |- _ => apply Z.leb_gt in H
  end.

Lemma range_cut_self : forall (b : bool) lo hi p q x,
  (b && z_ranges_meet lo hi p q && negb (z_range_covers lo hi p q))%bool = false ->
  lo <= x < hi ->
  (b && negb (z_range_covers lo hi p q) && (p <=? x) && (x <? q))%bool = false.
Proof.
  intros b lo hi p q x H Hx. destruct b; [|reflexivity]. cbn [andb] in *.
  unfold z_ranges_meet, z_range_covers in *.
  destruct (Z.max lo p <? Z.min hi q) eqn:E1;
    destruct (lo <=? p) eqn:E2; destruct (q <=? hi) eqn:E3;
    destruct (p <=? x) eqn:E4; destruct (x <? q) eqn:E5;
    cbn [andb negb] in *; try reflexivity; try discriminate H;
    zb_hyps; lia.
Qed.

(** A request that splits no range of the pair misses what is left of
    the pair once the ranges it covers are cut. *)
Lemma vdso_meets_cut_self : forall v lo hi,
  vdso_split v lo hi = false -> vdso_meets (vdso_cut v lo hi) lo hi = false.
Proof.
  intros v lo hi Hs. apply vdso_meets_false_bytes. intros x Hx.
  unfold vdso_split in Hs. apply orb_false_iff in Hs as [H1 H2].
  unfold vdso_byte. apply orb_false_iff. split.
  - exact (range_cut_self _ _ _ _ _ x H1 Hx).
  - exact (range_cut_self _ _ _ _ _ x H2 Hx).
Qed.

Lemma pu_mono : forall a b, a <= b -> page_round_up_Z a <= page_round_up_Z b.
Proof.
  intros a b H. unfold page_round_up_Z, page_size.
  apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia.
Qed.

(* -------------------------------------------------------------------------
   The invariant
   ------------------------------------------------------------------------- *)

(** Every entry of [maps] misses the mapped ranges of [v]. *)
Definition vd_maps (v : VdsoState) (maps : list (word * word)) : Prop :=
  forall a sz, In (a, sz) maps ->
    vdso_meets v (bv_unsigned a) (bv_unsigned a + bv_unsigned sz) = false.

(** The heap [[sb, PAGE_ALIGN b)] misses them, above a nonzero base. *)
Definition vd_heap (v : VdsoState) (sb b : word) : Prop :=
  (0 < bv_unsigned sb <= bv_unsigned b)%Z
  /\ vdso_meets v (bv_unsigned sb) (page_round_up_Z (bv_unsigned b)) = false.

Definition vd_inv (v : VdsoState) (h : VmMaps) : Prop :=
  vd_maps v (vm_maps h) /\ vd_heap v (vm_start_brk h) (vm_brk h).

(** The inductive invariant. *)
Definition vdso_inv (m : Model) : Prop := vd_inv (m_vdso m) (m_vmmaps m).

(** What the Mm arms rely on: no recorded mapping meets a mapped range of
    the pair. *)
Definition vdso_maps_disjoint (m : Model) : Prop :=
  forall a sz, In (a, sz) (vm_maps (m_vmmaps m)) ->
    vdso_meets (m_vdso m) (bv_unsigned a) (bv_unsigned a + bv_unsigned sz) = false.

(** [vdso_heap_clear] is the other half of [vdso_inv], by name. *)
Definition vdso_heap_clear (m : Model) : Prop :=
  (0 < bv_unsigned (vm_start_brk (m_vmmaps m)) <= bv_unsigned (vm_brk (m_vmmaps m)))%Z
  /\ vdso_meets (m_vdso m) (bv_unsigned (vm_start_brk (m_vmmaps m)))
       (page_round_up_Z (bv_unsigned (vm_brk (m_vmmaps m)))) = false.

Lemma vdso_inv_iff : forall m,
  vdso_inv m <-> vdso_maps_disjoint m /\ vdso_heap_clear m.
Proof. intros m. split; intros H; exact H. Qed.

Lemma vdso_inv_maps_disjoint : forall m, vdso_inv m -> vdso_maps_disjoint m.
Proof. intros m [H _]. exact H. Qed.

Lemma vd_maps_cons : forall v maps a n,
  vdso_meets v (bv_unsigned a) (bv_unsigned a + bv_unsigned n) = false ->
  vd_maps v maps -> vd_maps v ((a, n) :: maps).
Proof.
  intros v maps a n Ha H b s [Heq|Hin];
    [injection Heq as <- <-; exact Ha | exact (H b s Hin)].
Qed.

Lemma vd_maps_filter : forall v f maps, vd_maps v maps -> vd_maps v (List.filter f maps).
Proof. intros v f maps H a s Hin. apply filter_In in Hin as [Hin _]. exact (H a s Hin). Qed.

(** A remnant of [maps_subtract] lies inside the entry it was cut from. *)
Lemma vd_maps_subtract : forall v maps lo hi,
  maps_fit maps -> vd_maps v maps -> vd_maps v (maps_subtract maps lo hi).
Proof.
  intros v maps lo hi Hfit H a' s' Hin.
  apply vdso_meets_false_bytes. intros x Hx.
  destruct (maps_subtract_bytes maps lo hi a' s' x Hfit Hin Hx) as (a & s & Hin0 & Hx0 & _).
  exact (proj1 (vdso_meets_false_bytes _ _ _) (H a s Hin0) x Hx0).
Qed.

Lemma vd_maps_cut : forall v lo hi maps, vd_maps v maps -> vd_maps (vdso_cut v lo hi) maps.
Proof. intros v lo hi maps H a s Hin. apply vdso_meets_cut_mono. exact (H a s Hin). Qed.

Lemma vd_inv_ext : forall v h h',
  vm_maps h' = vm_maps h -> vm_start_brk h' = vm_start_brk h -> vm_brk h' = vm_brk h ->
  vd_inv v h -> vd_inv v h'.
Proof. intros v h h' H1 H2 H3 H. unfold vd_inv in *. rewrite H1, H2, H3. exact H. Qed.

(** The step every Mm leaf but brk takes: the break is carried, the pair
    only loses bits, and the new ledger misses what is left of it. *)
Lemma vd_inv_step : forall v v' h h',
  vm_start_brk h' = vm_start_brk h -> vm_brk h' = vm_brk h ->
  (forall x, vdso_byte v' x = true -> vdso_byte v x = true) ->
  vd_maps v' (vm_maps h') ->
  vd_inv v h -> vd_inv v' h'.
Proof.
  intros v v' h h' Hsb Hb Hmono Hmaps' (_ & Hlim & Hheap).
  unfold vd_inv, vd_heap. rewrite Hsb, Hb.
  split; [exact Hmaps'|]. split; [exact Hlim|].
  apply vdso_meets_false_bytes. intros x Hx.
  destruct (vdso_byte v' x) eqn:E; [|reflexivity].
  apply Hmono in E. rewrite (proj1 (vdso_meets_false_bytes _ _ _) Hheap x Hx) in E.
  discriminate E.
Qed.

(* -------------------------------------------------------------------------
   The pair through the Mm post-states
   ------------------------------------------------------------------------- *)

Lemma vdso_mmap_backing : forall flags a n m,
  m_vdso (with_mmap_backing flags a n m) = m_vdso m.
Proof.
  intros flags a n m. unfold with_mmap_backing.
  destruct (mmap_noreserve_b flags); reflexivity.
Qed.

Lemma vdso_mmap_replacement : forall flags a n m,
  m_vdso (with_mmap_replacement flags a n m) = m_vdso m.
Proof.
  intros flags a n m. unfold with_mmap_replacement. rewrite vdso_mmap_backing.
  reflexivity.
Qed.

Lemma vdso_mmap_destroyed : forall a n h m,
  m_vdso (with_mmap_destroyed a n h m) = m_vdso m.
Proof. reflexivity. Qed.

Lemma vdso_forget_ranges : forall rs m, m_vdso (forget_vm_ranges rs m) = m_vdso m.
Proof.
  induction rs as [|[a n] rs IH]; intros m; [reflexivity|].
  cbn [forget_vm_ranges]. rewrite IH. reflexivity.
Qed.

Lemma vdso_brk_next : forall m req r, m_vdso (with_brk_next m req r) = m_vdso m.
Proof. intros m req r. unfold with_brk_next. rewrite vdso_forget_ranges. reflexivity. Qed.

Lemma vdso_mremap_next : forall m old old_n dst new_n,
  m_vdso (mremap_model_next m old old_n dst new_n) = m_vdso m.
Proof. reflexivity. Qed.

Lemma vdso_mprotect_next : forall m addr n,
  m_vdso (mprotect_model_next m addr n) = m_vdso m.
Proof. reflexivity. Qed.

#[local] Hint Rewrite vdso_mmap_backing vdso_mmap_replacement vdso_mmap_destroyed
  vdso_brk_next vdso_mremap_next vdso_mprotect_next m_vdso_with_vdso m_vdso_with_vmmaps
  vmm_mmap_backing vmm_mmap_replacement vmm_mmap_destroyed vmm_vmmaps vmm_brk_next
  vmm_mremap_next vmm_mprotect_next m_vmmaps_with_vdso : vdpost.

(** A success leaf: rewrite the post-state's pair and ledger, then
    [vd_inv_step], leaving the bit goal and the ledger goal. *)
Ltac vd_leaf Hinv :=
  autorewrite with vdpost;
  lazymatch type of Hinv with
  | vd_inv ?v ?h =>
      apply (vd_inv_step v _ h); [reflexivity | reflexivity | | | exact Hinv]
  end.

(* -------------------------------------------------------------------------
   The five writers
   ------------------------------------------------------------------------- *)

(** What [brk_r_ok] admits: the old break, a shrink to the request at or
    above [start_brk], or a gated grow to the request. *)
Lemma brk_r_ok_shape : forall m req r,
  brk_r_ok m req r = true ->
  r = vm_brk (m_vmmaps m)
  \/ (r = req /\ bv_unsigned (vm_start_brk (m_vmmaps m)) <= bv_unsigned req
               < bv_unsigned (vm_brk (m_vmmaps m)))
  \/ (r = req /\ bv_unsigned (vm_brk (m_vmmaps m)) < bv_unsigned req
      /\ w_is0 req = false /\ brk_grow_ok m req r = true).
Proof.
  intros m req r Hok. unfold brk_r_ok, min_brk in Hok. cbv zeta in Hok.
  destruct (w_is0 req) eqn:E0; cbn [orb] in Hok.
  { left. apply bv_eqb_eq in Hok. exact Hok. }
  destruct (bv_unsigned req <? bv_unsigned (vm_start_brk (m_vmmaps m)))%Z eqn:E1.
  { left. apply bv_eqb_eq in Hok. exact Hok. }
  apply Z.ltb_ge in E1.
  destruct (bv_unsigned req <? bv_unsigned (vm_brk (m_vmmaps m)))%Z eqn:E2.
  - apply Z.ltb_lt in E2. apply orb_true_iff in Hok as [Hok|Hok]; apply bv_eqb_eq in Hok.
    + right; left. split; [exact Hok | lia].
    + left. exact Hok.
  - apply Z.ltb_ge in E2. apply andb_true_iff in Hok as [Hok Hg].
    apply orb_true_iff in Hok as [Hok|Hok]; apply bv_eqb_eq in Hok.
    + destruct (Z.eq_dec (bv_unsigned req) (bv_unsigned (vm_brk (m_vmmaps m)))) as [Heq|Hne].
      * left. subst r. apply bv_eq. exact Heq.
      * right; right. subst r.
        split; [reflexivity|]. split; [lia|]. split; [reflexivity | exact Hg].
    + left. exact Hok.
Qed.

(** THE brk ARGUMENT.  A shrink cuts entries and lowers the break within
    the heap.  A grow from [b] to [r] records [[b, r)]: its part below
    [PAGE_ALIGN b] is heap the invariant already clears, and the rest lies
    inside the range [brk_grow_ok] tested, [[PAGE_ALIGN b, PAGE_ALIGN r +
    PAGE_SIZE)].  A grow inside one page records only bytes below
    [PAGE_ALIGN b]. *)
Lemma brk_vd_inv : forall m req r,
  brk_r_ok m req r = true ->
  maps_fit (vm_maps (m_vmmaps m)) ->
  vd_inv (m_vdso m) (m_vmmaps m) ->
  vd_inv (m_vdso m) (brk_model_next (m_vmmaps m) req r).
Proof.
  intros m req r Hok Hfit Hinv.
  pose proof Hinv as (Hmaps & (Hsb0 & Hsbb) & Hheap).
  pose proof (word_range req) as Hreqr.
  pose proof (word_range (vm_brk (m_vmmaps m))) as Hbr.
  destruct (brk_r_ok_shape m req r Hok)
    as [Hr | [(Hr & Hlo & Hhi) | (Hr & Hgt & Hreq0 & Hg)]]; subst r.
  - apply (vd_inv_ext _ (m_vmmaps m)); [| reflexivity | reflexivity | exact Hinv].
    unfold brk_model_next, brk_maps_next, brk_grants, brk_is_grow. cbn [vm_maps].
    rewrite Z.ltb_irrefl, !andb_false_r. reflexivity.
  - unfold vd_inv, vd_heap, brk_model_next, brk_maps_next. cbn [vm_maps vm_start_brk vm_brk].
    rewrite (proj2 (Z.ltb_lt 0 (bv_unsigned (vm_brk (m_vmmaps m)))) ltac:(lia)),
      (proj2 (Z.ltb_lt _ _) Hhi).
    cbn [andb].
    split; [apply vd_maps_subtract; assumption|]. split; [lia|].
    apply (vdso_meets_within _ _ _ _ _ Hheap); [lia | apply pu_mono; lia].
  - unfold brk_grow_ok in Hg. cbv zeta in Hg.
    rewrite (proj2 (Z.ltb_lt 0 (bv_unsigned (vm_brk (m_vmmaps m)))) ltac:(lia)),
      (proj2 (Z.ltb_lt _ _) Hgt) in Hg.
    cbn [andb] in Hg. apply andb_true_iff in Hg as [Hg _].
    assert (Hsz : bv_unsigned (req - vm_brk (m_vmmaps m))%bv
                  = bv_unsigned req - bv_unsigned (vm_brk (m_vmmaps m))).
    { rewrite bv_sub_unsigned. apply bv_wrap_small.
      change (bv_modulus 64) with (2 ^ 64). lia. }
    pose proof (pu_ge (bv_unsigned req)) as Hpu.
    unfold vd_inv, vd_heap, brk_model_next, brk_maps_next, brk_grants, brk_is_grow.
    cbn [vm_maps vm_start_brk vm_brk].
    rewrite (proj2 (Z.ltb_ge _ _) (Z.lt_le_incl _ _ Hgt)), andb_false_r.
    rewrite (proj2 (Z.ltb_lt 0 (bv_unsigned (vm_brk (m_vmmaps m)))) ltac:(lia)),
      (proj2 (Z.ltb_lt _ _) Hgt), Hreq0.
    cbn [andb negb app].
    destruct (page_round_up_Z (bv_unsigned (vm_brk (m_vmmaps m)))
              <? page_round_up_Z (bv_unsigned req)) eqn:Elh.
    + apply andb_true_iff in Hg as [_ Hvd]. apply negb_true_iff in Hvd.
      pose proof (vdso_meets_union _ _ _ _ Hheap Hvd) as U.
      split; [apply vd_maps_cons; [rewrite Hsz | exact Hmaps] | split; [lia|]].
      * apply (vdso_meets_within _ _ _ _ _ U); unfold page_size; lia.
      * apply (vdso_meets_within _ _ _ _ _ U); unfold page_size; lia.
    + apply Z.ltb_ge in Elh.
      split; [apply vd_maps_cons; [rewrite Hsz | exact Hmaps] | split; [lia|]].
      * apply (vdso_meets_within _ _ _ _ _ Hheap); lia.
      * apply (vdso_meets_within _ _ _ _ _ Hheap); lia.
Qed.

Lemma check_brk_preserves_vdso : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs ->
  vm_fit (m_vmmaps m) -> vdso_inv m -> vdso_inv m'.
Proof.
  intros req [ret ws zs us cs ci] m m' evs H Hfit Hinv.
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
  unfold vdso_inv in *. rewrite vdso_brk_next, vmm_brk_next.
  exact (brk_vd_inv m req ret E Hfit Hinv).
Qed.

Lemma check_munmap_preserves_vdso : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs ->
  vm_fit (m_vmmaps m) -> vdso_inv m -> vdso_inv m'.
Proof.
  intros addr len [ret ws zs us cs ci] m m' evs H Hfit Hinv.
  unfold vdso_inv in *. pose proof (proj1 Hinv) as Hmaps.
  unfold check_munmap in H. cbv zeta in H.
  dif H; [apply check_ret_only_model in H; subst m'; exact Hinv|].
  dif H; [apply check_ret_only_model in H; subst m'; exact Hinv|].
  dif H.
  - destruct ws, zs, cs, ci; try discriminate.
    dif H; [|discriminate]. injection H as <- <-.
    vd_leaf Hinv; [exact (fun x Hx => Hx) |].
    cbn [vm_maps]. unfold map_remove. apply vd_maps_filter. exact Hmaps.
  - dif H; [apply check_ret_only_model in H; subst m'; exact Hinv|].
    dif H.
    + dif H; [|discriminate]. apply check_ret_only_model in H; subst m'.
      vd_leaf Hinv; [intros x; apply vdso_byte_cut |].
      apply vd_maps_cut. exact Hmaps.
    + dif H; [apply check_ret_only_model in H; subst m'; exact Hinv|discriminate].
Qed.

Lemma check_mprotect_preserves_vdso : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs ->
  vm_fit (m_vmmaps m) -> vdso_inv m -> vdso_inv m'.
Proof.
  intros addr len prot [ret ws zs us cs ci] m m' evs H Hfit Hinv.
  unfold vdso_inv in *. pose proof (proj1 Hinv) as Hmaps.
  unfold check_mprotect in H. cbv zeta in H.
  dif H; [apply check_ret_only_model in H; subst m'; exact Hinv|].
  dif H; [apply check_ret_only_model in H; subst m'; exact Hinv|].
  dif H; [apply check_ret_only_model in H; subst m'; exact Hinv|].
  dif H; [apply check_ret_only_model in H; subst m'; exact Hinv|].
  dif H; [discriminate|].
  dif H.
  - destruct ws, us, cs, ci; try discriminate.
    dif H.
    + destruct zs; [|discriminate]. injection H as <- <-. exact Hinv.
    + dif H; [|discriminate]. injection H as <- <-.
      vd_leaf Hinv; [exact (fun x Hx => Hx) |]. cbn [vm_maps]. exact Hmaps.
  - dif H.
    + destruct ws, zs, us, cs, ci; try discriminate.
      dif H; [|discriminate]. injection H as <- <-. exact Hinv.
    + dif H; [|discriminate].
      apply check_mprotect_vdso_model in H. subst m'. exact Hinv.
Qed.

(** The MAP_FIXED arms over the pair: each success clears the ranges the
    request covers, and the request, which splits none, misses what is
    left ([vdso_meets_cut_self]). *)
Lemma check_mmap_fixed_noaccess_vdso_preserves_vdso :
  forall flags addr nZ eff m m' evs,
  0 < nZ -> bv_unsigned addr + nZ <= alloc_top (m_vmmaps m) ->
  check_mmap_fixed_noaccess_vdso flags addr nZ eff m = CheckOk m' evs ->
  vm_fit (m_vmmaps m) -> vdso_inv m -> vdso_inv m'.
Proof.
  intros flags addr nZ [ret ws zs us cs ci] m m' evs HnZ Eceil H Hfit Hinv.
  unfold vdso_inv in *. pose proof (proj1 Hinv) as Hmaps.
  pose proof (alloc_top_lt (m_vmmaps m)) as Hac. unfold two_pow_64 in Hac.
  pose proof (word_range addr) as Haddrr.
  assert (Hn : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply u64; lia).
  unfold check_mmap_fixed_noaccess_vdso in H. cbv zeta in H.
  difn H Esp.
  { destruct ws, zs, us, cs, ci; try discriminate.
    dif H; [|discriminate]. injection H as <- <-. exact Hinv. }
  difn H Efree; [|difn H Espan; [|discriminate]].
  all: destruct ws, zs, cs, ci; try discriminate.
  all: destruct (errno_ret_in mmap_errnos ret).
  all: try (destruct us;
            [ injection H as <- <-; exact Hinv
            | difn H Eus; [|discriminate]; injection H as <- <-;
              vd_leaf Hinv; [intros x; apply vdso_byte_cut |];
              cbn [vm_maps mmap_fixed_destroyed_next];
              apply vd_maps_cut, vd_maps_subtract; [exact Hfit | exact Hmaps] ]).
  - difn H Eok; [|discriminate]. injection H as <- <-.
    vd_leaf Hinv; [intros x; apply vdso_byte_cut |]. cbn [vm_maps].
    apply vd_maps_cons; [rewrite Hn; apply vdso_meets_cut_self; exact Esp |].
    apply vd_maps_cut. exact Hmaps.
  - difn H Eok; [|discriminate]. injection H as <- <-.
    vd_leaf Hinv; [intros x; apply vdso_byte_cut |].
    cbn [vm_maps mmap_fixed_noaccess_span_next].
    apply vd_maps_cons; [rewrite Hn; apply vdso_meets_cut_self; exact Esp |].
    apply vd_maps_cut, vd_maps_subtract; [exact Hfit | exact Hmaps].
Qed.

Lemma check_mmap_fixed_rw_vdso_preserves_vdso :
  forall flags addr nZ eff m m' evs,
  0 < nZ -> bv_unsigned addr + nZ <= alloc_top (m_vmmaps m) ->
  check_mmap_fixed_rw_vdso flags addr nZ eff m = CheckOk m' evs ->
  vm_fit (m_vmmaps m) -> vdso_inv m -> vdso_inv m'.
Proof.
  intros flags addr nZ [ret ws zs us cs ci] m m' evs HnZ Eceil H Hfit Hinv.
  unfold vdso_inv in *. pose proof (proj1 Hinv) as Hmaps.
  pose proof (alloc_top_lt (m_vmmaps m)) as Hac. unfold two_pow_64 in Hac.
  pose proof (word_range addr) as Haddrr.
  assert (Hn : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply u64; lia).
  unfold check_mmap_fixed_rw_vdso in H. cbv zeta in H.
  difn H Esp.
  { destruct ws, zs, us, cs, ci; try discriminate.
    dif H; [|discriminate]. injection H as <- <-. exact Hinv. }
  difn H Efree; [|difn H Espan; [|discriminate]].
  all: destruct ws, cs, ci; try discriminate.
  all: destruct (errno_ret_in mmap_errnos ret).
  all: try (destruct zs; [|discriminate]; destruct us;
            [ injection H as <- <-; exact Hinv
            | difn H Eus; [|discriminate]; injection H as <- <-;
              vd_leaf Hinv; [intros x; apply vdso_byte_cut |];
              cbn [vm_maps mmap_fixed_destroyed_next];
              apply vd_maps_cut, vd_maps_subtract; [exact Hfit | exact Hmaps] ]).
  - destruct us; [|discriminate].
    difn H Eok; [|discriminate]. injection H as <- <-.
    vd_leaf Hinv; [intros x; apply vdso_byte_cut |]. cbn [vm_maps].
    apply vd_maps_cons; [rewrite Hn; apply vdso_meets_cut_self; exact Esp |].
    apply vd_maps_cut. exact Hmaps.
  - destruct us; [|discriminate].
    difn H Eok; [|discriminate]. injection H as <- <-.
    vd_leaf Hinv; [intros x; apply vdso_byte_cut |].
    cbn [vm_maps mmap_fixed_rw_span_next].
    apply vd_maps_cons; [rewrite Hn; apply vdso_meets_cut_self; exact Esp |].
    apply vd_maps_cut, vd_maps_subtract; [exact Hfit | exact Hmaps].
Qed.

Lemma check_mmap_preserves_vdso : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs ->
  vm_fit (m_vmmaps m) -> vdso_inv m -> vdso_inv m'.
Proof.
  intros addr len prot flags fd off [ret ws zs us cs ci] m m' evs H Hfit Hinv.
  unfold vdso_inv in *. pose proof (proj1 Hinv) as Hmaps.
  unfold check_mmap in H. cbv zeta in H.
  pose proof (alloc_top_lt (m_vmmaps m)) as Hac. unfold two_pow_64 in Hac.
  pose proof (word_range len) as Hlenr.
  pose proof (word_range addr) as Haddrr.
  pose proof (word_range ret) as Hretr.
  destruct (negb (mmap_off_aligned_b off)) eqn:Eoff.
  { destruct (mmap_pglen_ok_b len); [|discriminate].
    apply check_ret_only_model in H; subst m'; exact Hinv. }
  destruct (negb (mmap_anon_b flags)) eqn:Eanon; [discriminate|].
  destruct (w_is0 len) eqn:Elen.
  { destruct (mmap_plain_anon_b flags); [|discriminate].
    apply check_ret_only_model in H; subst m'; exact Hinv. }
  pose proof (w_is0_false len Elen) as Hlen0.
  assert (HnZ : 0 < page_round_up_Z (bv_unsigned len))
    by (apply page_round_up_pos; lia).
  (* the placed shapes: the [choose] guard's pair conjunct *)
  destruct (mmap_modeled_b prot flags off) eqn:Emod.
  { destruct ws, us, cs, ci; try discriminate.
    destruct (errno_ret_in mmap_errnos ret).
    { destruct zs; [|discriminate]. injection H as <- <-. exact Hinv. }
    difn H E; [|discriminate]. injection H as <- <-.
    apply andb_true_iff in E as [E _].
    apply andb_true_iff in E as [E _].
    apply andb_true_iff in E as [E Hvd].
    apply andb_true_iff in E as [E _].
    apply andb_true_iff in E as [_ Hceil].
    apply Z.leb_le in Hceil. apply negb_true_iff in Hvd.
    vd_leaf Hinv; [exact (fun x Hx => Hx) |]. cbn [vm_maps].
    apply vd_maps_cons; [rewrite u64 by lia; exact Hvd | exact Hmaps]. }
  destruct (mmap_noaccess_b prot flags off) eqn:Enoa.
  { destruct ws, zs, cs, ci; try discriminate.
    destruct (errno_ret_in mmap_errnos ret).
    { destruct us; [|discriminate]. injection H as <- <-. exact Hinv. }
    difn H E; [|discriminate]. injection H as <- <-.
    apply andb_true_iff in E as [E _].
    apply andb_true_iff in E as [E Hvd].
    apply andb_true_iff in E as [E _].
    apply andb_true_iff in E as [_ Hceil].
    apply Z.leb_le in Hceil. apply negb_true_iff in Hvd.
    vd_leaf Hinv; [exact (fun x Hx => Hx) |]. cbn [vm_maps].
    apply vd_maps_cons; [rewrite u64 by lia; exact Hvd | exact Hmaps]. }
  (* MAP_FIXED, PROT_NONE: contained (the ledger only loses bytes), over
     the pair ([check_mmap_fixed_noaccess_vdso_preserves_vdso]), or past
     the pair test (a free range or a spanning request that misses it). *)
  destruct (mmap_fixed_noaccess_b prot flags off) eqn:Efix.
  { difn H Enomem; [apply check_ret_only_model in H; subst m'; exact Hinv|].
    difn H Eceil; [discriminate|].
    difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hinv|].
    difn H Epos; [discriminate|].
    apply negb_false_iff, Z.leb_le in Eceil.
    difn H Elive.
    - destruct ws, zs, cs, ci; try discriminate.
      destruct (errno_ret_in mmap_errnos ret).
      + destruct us.
        * injection H as <- <-. exact Hinv.
        * difn H Eus; [|discriminate]. injection H as <- <-.
          vd_leaf Hinv; [exact (fun x Hx => Hx) |].
          cbn [vm_maps mmap_fixed_destroyed_next].
          apply vd_maps_subtract; [exact Hfit | exact Hmaps].
      + difn H Eok; [|discriminate]. injection H as <- <-.
        vd_leaf Hinv; [exact (fun x Hx => Hx) |]. cbn [vm_maps]. exact Hmaps.
    - difn H Evd.
      { eapply check_mmap_fixed_noaccess_vdso_preserves_vdso;
          [exact HnZ | exact Eceil | exact H | exact Hfit | exact Hinv]. }
      difn H Efree.
      + destruct ws, zs, cs, ci; try discriminate.
        destruct (errno_ret_in mmap_errnos ret).
        * destruct us; [|discriminate]. injection H as <- <-. exact Hinv.
        * difn H Eok; [|discriminate]. injection H as <- <-.
          vd_leaf Hinv; [exact (fun x Hx => Hx) |]. cbn [vm_maps].
          apply vd_maps_cons; [rewrite u64 by lia; exact Evd | exact Hmaps].
      + difn H Espan; [|discriminate].
        destruct ws, zs, cs, ci; try discriminate.
        destruct (errno_ret_in mmap_errnos ret).
        * destruct us.
          -- injection H as <- <-. exact Hinv.
          -- difn H Eus; [|discriminate]. injection H as <- <-.
             vd_leaf Hinv; [exact (fun x Hx => Hx) |].
             cbn [vm_maps mmap_fixed_destroyed_next].
             apply vd_maps_subtract; [exact Hfit | exact Hmaps].
        * difn H Eok; [|discriminate]. injection H as <- <-.
          vd_leaf Hinv; [exact (fun x Hx => Hx) |].
          cbn [vm_maps mmap_fixed_noaccess_span_next].
          apply vd_maps_cons; [rewrite u64 by lia; exact Evd |].
          apply vd_maps_subtract; [exact Hfit | exact Hmaps]. }
  destruct (mmap_fixed_rw_b prot flags off) eqn:Efixrw.
  2: {
    (* MAP_FIXED_NOREPLACE: a grant only where the pair conjunct holds. *)
    destruct (mmap_noreplace_noaccess_b prot flags off) eqn:Enrn.
    { difn H Enomem; [apply check_ret_only_model in H; subst m'; exact Hinv|].
      difn H Eceil; [discriminate|].
      difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hinv|].
      difn H Epos; [discriminate|].
      apply negb_false_iff, Z.leb_le in Eceil.
      difn H Efree.
      - destruct ws, zs, cs, ci; try discriminate.
        destruct (errno_ret_in mmap_errnos ret).
        + destruct us; [|discriminate]. injection H as <- <-. exact Hinv.
        + difn H Eok; [|discriminate]. injection H as <- <-.
          apply andb_true_iff in Efree as [_ Hvd]. apply negb_true_iff in Hvd.
          vd_leaf Hinv; [exact (fun x Hx => Hx) |]. cbn [vm_maps].
          apply vd_maps_cons; [rewrite u64 by lia; exact Hvd | exact Hmaps].
      - destruct ws, zs, us, cs, ci; try discriminate.
        difn H Eerr; [|discriminate]. injection H as <- <-. exact Hinv. }
    destruct (mmap_noreplace_rw_b prot flags off) eqn:Enrr; [|discriminate].
    difn H Enomem; [apply check_ret_only_model in H; subst m'; exact Hinv|].
    difn H Eceil; [discriminate|].
    difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hinv|].
    difn H Epos; [discriminate|].
    apply negb_false_iff, Z.leb_le in Eceil.
    difn H Efree.
    - destruct ws, us, cs, ci; try discriminate.
      destruct (errno_ret_in mmap_errnos ret).
      + destruct zs; [|discriminate]. injection H as <- <-. exact Hinv.
      + difn H Eok; [|discriminate]. injection H as <- <-.
        apply andb_true_iff in Efree as [_ Hvd]. apply negb_true_iff in Hvd.
        vd_leaf Hinv; [exact (fun x Hx => Hx) |]. cbn [vm_maps].
        apply vd_maps_cons; [rewrite u64 by lia; exact Hvd | exact Hmaps].
    - destruct ws, zs, us, cs, ci; try discriminate.
      difn H Eerr; [|discriminate]. injection H as <- <-. exact Hinv. }
  (* MAP_FIXED, rw: the PROT_NONE shape's three cases. *)
  difn H Enomem; [apply check_ret_only_model in H; subst m'; exact Hinv|].
  difn H Eceil; [discriminate|].
  difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hinv|].
  difn H Epos; [discriminate|].
  apply negb_false_iff, Z.leb_le in Eceil.
  difn H Elive.
  - destruct ws, cs, ci; try discriminate.
    destruct (errno_ret_in mmap_errnos ret).
    + destruct zs; [|discriminate]. destruct us.
      * injection H as <- <-. exact Hinv.
      * difn H Eus; [|discriminate]. injection H as <- <-.
        vd_leaf Hinv; [exact (fun x Hx => Hx) |].
        cbn [vm_maps mmap_fixed_destroyed_next].
        apply vd_maps_subtract; [exact Hfit | exact Hmaps].
    + destruct us; [|discriminate].
      difn H Eok; [|discriminate]. injection H as <- <-.
      vd_leaf Hinv; [exact (fun x Hx => Hx) |].
      cbn [vm_maps mmap_fixed_rw_next]. exact Hmaps.
  - difn H Evd.
    { eapply check_mmap_fixed_rw_vdso_preserves_vdso;
        [exact HnZ | exact Eceil | exact H | exact Hfit | exact Hinv]. }
    difn H Efree.
    + destruct ws, us, cs, ci; try discriminate.
      destruct (errno_ret_in mmap_errnos ret).
      * destruct zs; [|discriminate]. injection H as <- <-. exact Hinv.
      * difn H Eok; [|discriminate]. injection H as <- <-.
        vd_leaf Hinv; [exact (fun x Hx => Hx) |]. cbn [vm_maps].
        apply vd_maps_cons; [rewrite u64 by lia; exact Evd | exact Hmaps].
    + difn H Espan; [|discriminate].
      destruct ws, cs, ci; try discriminate.
      destruct (errno_ret_in mmap_errnos ret).
      * destruct zs; [|discriminate]. destruct us.
        -- injection H as <- <-. exact Hinv.
        -- difn H Eus; [|discriminate]. injection H as <- <-.
           vd_leaf Hinv; [exact (fun x Hx => Hx) |].
           cbn [vm_maps mmap_fixed_destroyed_next].
           apply vd_maps_subtract; [exact Hfit | exact Hmaps].
      * destruct us; [|discriminate].
        difn H Eok; [|discriminate]. injection H as <- <-.
        vd_leaf Hinv; [exact (fun x Hx => Hx) |].
        cbn [vm_maps mmap_fixed_rw_span_next].
        apply vd_maps_cons; [rewrite u64 by lia; exact Evd |].
        apply vd_maps_subtract; [exact Hfit | exact Hmaps].
Qed.

(** mremap re-records its source: smaller in place (inside the old
    entry), grown in place (the old entry, then a tail the arm tests), or
    moved (to a destination the arm tests). *)
Lemma check_mremap_preserves_vdso :
  forall old old_size new_size flags eff m m' evs,
  check_mremap old old_size new_size flags eff m = CheckOk m' evs ->
  vm_fit (m_vmmaps m) -> vdso_inv m -> vdso_inv m'.
Proof.
  intros old old_size new_size flags [ret ws zs us cs ci] m m' evs H Hfit Hinv.
  unfold vdso_inv in *. pose proof (proj1 Hinv) as Hmaps.
  unfold check_mremap in H. cbv zeta in H.
  pose proof (alloc_top_lt (m_vmmaps m)) as Hac. unfold two_pow_64 in Hac.
  pose proof (word_range old) as Hor.
  pose proof (word_range old_size) as Hos.
  pose proof (word_range new_size) as Hns.
  pose proof (word_range ret) as Hretr.
  difn H Eflag; [discriminate|].
  difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hinv|].
  difn H Enew; [apply check_ret_only_model in H; subst m'; exact Hinv|].
  difn H Eold; [discriminate|].
  difn H Esrc.
  { difn H Evb; [|discriminate].
    apply check_mremap_vdso_source_model in H. subst m'. exact Hinv. }
  difn H Eeq; [apply check_ret_only_model in H; subst m'; exact Hinv|].
  destruct ws; [|discriminate]. destruct ci; [|discriminate].
  unfold page_align_is0_b in Enew. apply orb_false_iff in Enew as [Enew0 _].
  pose proof (w_is0_false new_size Enew0) as Hnew0.
  assert (HnewZ : 0 < page_round_up_Z (bv_unsigned new_size))
    by (apply page_round_up_pos; lia).
  apply negb_false_iff in Esrc.
  apply andb_true_iff in Esrc as [Esrc _].
  unfold mremap_source_b in Esrc.
  apply andb_true_iff in Esrc as [Esrc _].
  apply andb_true_iff in Esrc as [Esrc Hhas].
  apply andb_true_iff in Esrc as [Hoceil _].
  apply Z.leb_le in Hoceil.
  assert (HoldZ : 0 <= page_round_up_Z (bv_unsigned old_size))
    by (apply page_round_up_Z_nonneg; lia).
  pose proof (Hmaps _ _ (map_has_In _ _ _ Hhas)) as Hold.
  rewrite u64 in Hold by lia.
  destruct (errno_ret_in mremap_errnos ret).
  { destruct zs, us, cs; try discriminate. injection H as <- <-. exact Hinv. }
  destruct (bv_eqb ret old).
  - difn H Eshrink.
    + difn H Eok; [|discriminate]. injection H as <- <-.
      apply Z.ltb_lt in Eshrink.
      vd_leaf Hinv; [exact (fun x Hx => Hx) |].
      cbn [vm_maps mremap_maps_next].
      apply vd_maps_cons; [| unfold map_remove; apply vd_maps_filter; exact Hmaps].
      rewrite u64 by lia.
      apply (vdso_meets_within _ _ _ _ _ Hold); lia.
    + difn H Egrow; [|discriminate].
      difn H Eok; [|discriminate]. injection H as <- <-.
      unfold mremap_inplace_grow_b in Egrow. cbv zeta in Egrow.
      apply andb_true_iff in Egrow as [Egrow _].
      apply andb_true_iff in Egrow as [Egrow Hvd].
      apply andb_true_iff in Egrow as [Hgceil _].
      apply Z.leb_le in Hgceil. apply negb_true_iff in Hvd.
      vd_leaf Hinv; [exact (fun x Hx => Hx) |].
      cbn [vm_maps mremap_maps_next].
      apply vd_maps_cons; [| unfold map_remove; apply vd_maps_filter; exact Hmaps].
      rewrite u64 by lia.
      exact (vdso_meets_union _ _ _ _ Hold Hvd).
  - difn H Emove; [|discriminate]. injection H as <- <-.
    apply andb_true_iff in Emove as [Emove _].
    apply andb_true_iff in Emove as [Emove _].
    apply andb_true_iff in Emove as [Emove _].
    apply andb_true_iff in Emove as [Emove Hvd].
    apply andb_true_iff in Emove as [_ Hfresh].
    apply negb_true_iff in Hvd.
    unfold mremap_fresh_b in Hfresh. cbv zeta in Hfresh.
    apply andb_true_iff in Hfresh as [Hfresh _].
    apply andb_true_iff in Hfresh as [Hfresh _].
    apply andb_true_iff in Hfresh as [_ Hfceil].
    apply Z.leb_le in Hfceil.
    vd_leaf Hinv; [exact (fun x Hx => Hx) |].
    cbn [vm_maps mremap_maps_next].
    apply vd_maps_cons; [| unfold map_remove; apply vd_maps_filter; exact Hmaps].
    rewrite u64 by lia. exact Hvd.
Qed.

(* -------------------------------------------------------------------------
   FRAME.  Every other arm leaves the pair alone: [with_vdso] is written
   only by the Mm arms above, and every other setter carries
   [procst_vdso] across ([State]'s [m_vdso_with_*] rewrites, database
   [model]).  The lemmas below are [VmMapsDisjoint]'s [check_*_frame]
   lemmas with [m_vdso] for [m_vmmaps], proof for proof; with those, an
   arm that keeps both halves keeps [vdso_inv] ([vdso_inv_frame]).
   ------------------------------------------------------------------------- *)

Lemma vdso_inv_frame : forall m m',
  m_vmmaps m' = m_vmmaps m -> m_vdso m' = m_vdso m -> vdso_inv m -> vdso_inv m'.
Proof. intros m m' H1 H2 H. unfold vdso_inv in *. rewrite H1, H2. exact H. Qed.

Lemma check_efault_or_vdso_frame : forall fb eff m m' evs,
  check_efault_or fb eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros fb eff m m' evs H. unfold check_efault_or in H. repeat vm_step H; reflexivity.
Qed.

Lemma check_open_result_vdso_frame : forall eff m mk m' evs,
  (forall fd, m_vdso (mk fd) = m_vdso m) ->
  check_open_result eff m mk = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros eff m mk m' evs Hmk H.
  unfold check_open_result, check_new_fd_result in H.
  repeat vm_step H; try apply Hmk; reflexivity.
Qed.

Ltac vd_done H :=
  first
  [ apply check_efault_or_vdso_frame in H; exact H
  | elim (check_readv_gap_frame _ _ H)
  | (eapply check_open_result_vdso_frame in H;
     [exact H | intros; reflexivity]) ].

(** THE ONE FRAME TACTIC: walk the checker's branches ([VmMapsDisjoint.vm_step],
    which reads only the hypothesis), then close [m_vdso m' = m_vdso m]
    by conversion or through the [model] rewrites. *)
Ltac vd_frame2 H :=
  repeat (vm_step H || vd_done H);
  try solve [ reflexivity | autorewrite with model; reflexivity ].

Lemma check_madvise_vdso_frame : forall addr len advice eff m m' evs,
  check_madvise addr len advice eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros addr len advice [ret ws zs us cs ci] m m' evs H.
  unfold check_madvise in H. cbv zeta in H.
  dif H; [apply check_ret_only_model in H; subst m'; reflexivity|].
  dif H; [discriminate|].
  dif H; [apply check_ret_only_model in H; subst m'; reflexivity|].
  dif H; [apply check_ret_only_model in H; subst m'; reflexivity|].
  dif H; [|discriminate].
  destruct ws, us, cs, ci; try discriminate.
  dif H; [|discriminate]. injection H as <- <-. reflexivity.
Qed.

Lemma check_read_vdso_frame : forall i fd buf count eff m m' evs,
  check_read i fd buf count eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros i fd buf count eff m m' evs H.
  unfold check_read, check_read_urandom, check_socket_pending_error,
    check_access_ok_zero in H.
  cbv zeta in H. vd_frame2 H.
Qed.

Lemma check_write_vdso_frame : forall i fd buf count eff m m' evs,
  check_write i fd buf count eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros i fd buf count eff m m' evs H.
  unfold check_write, check_access_ok_zero in H. vd_frame2 H.
Qed.

Lemma check_pread64_vdso_frame : forall i fd buf count pos eff m m' evs,
  check_pread64 i fd buf count pos eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i fd buf count pos eff m m' evs H.
  unfold check_pread64, check_read_urandom in H. cbv zeta in H. vd_frame2 H.
Qed.

Lemma check_pwrite64_vdso_frame : forall i fd buf count pos eff m m' evs,
  check_pwrite64 i fd buf count pos eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i fd buf count pos eff m m' evs H.
  unfold check_pwrite64 in H. vd_frame2 H.
Qed.

Lemma check_openat_vdso_frame : forall i dirfd pathp flags eff m m' evs,
  check_openat i dirfd pathp flags eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold check_openat, Open.check_openat_body, Open.check_openat_resolved,
    Open.check_openat_sep, Open.check_openat_localtime,
    Open.check_openat_devnull, Open.check_open_devnull,
    Open.check_openat_urandom, Open.check_open_urandom,
    Open.check_openat_tmp,
    Open.check_openat_read, Open.check_openat_create, Open.check_openat_excl,
    Open.check_openat_dir, Open.check_openat_append,
    Open.check_openat_rdwr, Open.check_openat_rdwr_excl,
    check_create_wronly, check_open_append, check_open_rdwr in H.
  vd_frame2 H.
Qed.

Lemma check_close_vdso_frame : forall fd eff m m' evs,
  check_close fd eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof. intros fd eff m m' evs H. unfold check_close in H. vd_frame2 H. Qed.

Lemma check_lseek_vdso_frame : forall fd off whence eff m m' evs,
  check_lseek fd off whence eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros fd off whence eff m m' evs H. unfold check_lseek in H. vd_frame2 H.
Qed.

Lemma check_getcwd_vdso_frame : forall size eff m m' evs,
  check_getcwd size eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros size eff m m' evs H. unfold check_getcwd in H. vd_frame2 H.
Qed.

Lemma check_getrandom_vdso_frame : forall i buf cap flags eff m m' evs,
  check_getrandom i buf cap flags eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i buf cap flags eff m m' evs H.
  unfold check_getrandom, check_getrandom_zero in H. vd_frame2 H.
Qed.

Lemma check_readlinkat_vdso_frame : forall dirfd eff m m' evs,
  check_readlinkat dirfd eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros dirfd eff m m' evs H. unfold check_readlinkat in H. vd_frame2 H.
Qed.

Lemma check_exit_vdso_frame : forall code eff m m' evs,
  check_exit code eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof. intros code eff m m' evs H. unfold check_exit in H. vd_frame2 H. Qed.

Lemma check_set_tid_address_vdso_frame : forall eff m m' evs,
  check_set_tid_address eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros eff m m' evs H. unfold check_set_tid_address in H. vd_frame2 H.
Qed.

Lemma check_ioctl_vdso_frame : forall fd req eff m m' evs,
  check_ioctl fd req eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof. intros fd req eff m m' evs H. unfold check_ioctl in H. vd_frame2 H. Qed.

Lemma check_writev_vdso_frame : forall i fd iov iovcnt eff m m' evs,
  check_writev i fd iov iovcnt eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i fd iov iovcnt eff m m' evs H.
  unfold check_writev in H. vd_frame2 H.
Qed.

Lemma check_readv_imported_vdso_frame : forall i fd r iovs0 eff m m' evs,
  check_readv_imported i fd r iovs0 eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i fd r iovs0 eff m m' evs H.
  unfold check_readv_imported in H.
  vd_frame2 H.
Qed.

Lemma check_readv_vdso_frame : forall i fd iov iovcnt eff m m' evs,
  check_readv i fd iov iovcnt eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i fd iov iovcnt eff m m' evs H.
  unfold check_readv in H.
  repeat (vm_step H || vd_done H
          || (apply check_readv_imported_vdso_frame in H; exact H));
  try reflexivity.
Qed.

Lemma check_wait4_vdso_frame : forall i upid stat_addr options rusage eff m m' evs,
  check_wait4 i upid stat_addr options rusage eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i upid stat_addr options rusage eff m m' evs H.
  unfold check_wait4 in H. vd_frame2 H.
Qed.

Lemma check_epoll_create1_vdso_frame : forall flags32 eff m m' evs,
  check_epoll_create1 flags32 eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros flags32 eff m m' evs H. unfold check_epoll_create1 in H. vd_frame2 H.
Qed.

Lemma check_epoll_ctl_vdso_frame : forall i epfd op32 tfd event eff m m' evs,
  check_epoll_ctl i epfd op32 tfd event eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i epfd op32 tfd event eff m m' evs H.
  unfold check_epoll_ctl in H. vd_frame2 H.
Qed.

Lemma check_epoll_pwait_vdso_frame :
  forall i epfd events maxevents32 sigmask sigsetsize eff m m' evs,
  check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m
    = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i epfd events maxevents32 sigmask sigsetsize eff m m' evs H.
  unfold check_epoll_pwait in H. vd_frame2 H.
Qed.

Lemma check_fsync_vdso_frame : forall fd eff m m' evs,
  check_fsync fd eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof. intros fd eff m m' evs H. unfold check_fsync in H. vd_frame2 H. Qed.

Lemma check_getdents64_vdso_frame : forall fd count eff m m' evs,
  check_getdents64 fd count eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros fd count eff m m' evs H. unfold check_getdents64 in H. vd_frame2 H.
Qed.

Lemma check_flock_vdso_frame : forall fd cmd eff m m' evs,
  check_flock fd cmd eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros fd cmd eff m m' evs H. unfold check_flock in H. vd_frame2 H.
Qed.

Lemma check_timerfd_create_vdso_frame : forall clkid flags eff m m' evs,
  check_timerfd_create clkid flags eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros clkid flags eff m m' evs H.
  unfold check_timerfd_create in H. vd_frame2 H.
Qed.

Lemma check_eventfd2_vdso_frame : forall flags eff m m' evs,
  check_eventfd2 flags eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros flags eff m m' evs H.
  unfold check_eventfd2 in H. vd_frame2 H.
Qed.

Lemma check_uname_vdso_frame : forall i name eff m m' evs,
  check_uname i name eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i name eff m m' evs H.
  unfold check_uname, check_uname_copy in H. vd_frame2 H.
Qed.

Lemma check_prlimit64_vdso_frame :
  forall i pid resource new_rlim old_rlim eff m m' evs,
  check_prlimit64 i pid resource new_rlim old_rlim eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i pid resource new_rlim old_rlim eff m m' evs H.
  unfold check_prlimit64, check_rlim64_read in H. vd_frame2 H.
Qed.

Lemma check_ftruncate_vdso_frame : forall fd len eff m m' evs,
  check_ftruncate fd len eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros fd len eff m m' evs H. unfold check_ftruncate in H. vd_frame2 H.
Qed.

Lemma check_getpid_vdso_frame : forall eff m m' evs,
  check_getpid eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof. exact check_set_tid_address_vdso_frame. Qed.

Lemma check_gettid_vdso_frame : forall eff m m' evs,
  check_gettid eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof. exact check_set_tid_address_vdso_frame. Qed.

Lemma check_setsid_vdso_frame : forall eff m m' evs,
  check_setsid eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof. intros eff m m' evs H. unfold check_setsid in H. vd_frame2 H. Qed.

Lemma check_prctl_vdso_frame : forall option_ arg2 eff m m' evs,
  check_prctl option_ arg2 eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros option_ arg2 eff m m' evs H. unfold check_prctl in H. vd_frame2 H.
Qed.

Lemma check_gettimeofday_vdso_frame : forall i tv tz eff m m' evs,
  check_gettimeofday i tv tz eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i tv tz eff m m' evs H.
  unfold check_gettimeofday in H. vd_frame2 H.
Qed.

Lemma check_clock_gettime_vdso_frame : forall i clkid tp eff m m' evs,
  check_clock_gettime i clkid tp eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i clkid tp eff m m' evs H.
  unfold check_clock_gettime in H. vd_frame2 H.
Qed.

Lemma check_nanosleep_vdso_frame : forall i rqtp rmtp eff m m' evs,
  check_nanosleep i rqtp rmtp eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i rqtp rmtp eff m m' evs H.
  unfold check_nanosleep in H. vd_frame2 H.
Qed.

Lemma check_dup_vdso_frame : forall oldfd eff m m' evs,
  check_dup oldfd eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros oldfd eff m m' evs H.
  unfold check_dup, check_dup_result in H. vd_frame2 H.
Qed.

Lemma check_dup3_vdso_frame : forall oldfd newfd flags eff m m' evs,
  check_dup3 oldfd newfd flags eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros oldfd newfd flags eff m m' evs H. unfold check_dup3 in H. vd_frame2 H.
Qed.

Lemma check_unlinkat_vdso_frame : forall i dirfd pathp flags eff m m' evs,
  check_unlinkat i dirfd pathp flags eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i dirfd pathp flags eff m m' evs H.
  unfold check_unlinkat, Namei.check_unlinkat_body, Namei.check_unlinkat_tmp,
    Namei.check_unlink_found, check_unlink_result in H.
  vd_frame2 H.
Qed.

Lemma check_faccessat_vdso_frame : forall i dirfd pathp mode eff m m' evs,
  check_faccessat i dirfd pathp mode eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i dirfd pathp mode eff m m' evs H.
  unfold check_faccessat, Open.check_faccessat_body, check_access_exists in H.
  vd_frame2 H.
Qed.

Lemma check_faccessat2_vdso_frame : forall i dirfd pathp mode flags eff m m' evs,
  check_faccessat2 i dirfd pathp mode flags eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i dirfd pathp mode flags eff m m' evs H.
  unfold check_faccessat2, Open.check_faccessat_body, check_access_exists in H.
  vd_frame2 H.
Qed.

Lemma check_pselect6_vdso_frame : forall i n32 inp outp exp tsp sig eff m m' evs,
  check_pselect6 i n32 inp outp exp tsp sig eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i n32 inp outp exp tsp sig eff m m' evs H.
  unfold check_pselect6 in H. vd_frame2 H.
Qed.

Lemma check_ppoll_vdso_frame : forall i ufds nfds tsp sig sigsetsize eff m m' evs,
  check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i ufds nfds tsp sig sigsetsize eff m m' evs H.
  unfold check_ppoll in H. vd_frame2 H.
Qed.

Lemma check_newfstatat_vdso_frame : forall i dirfd pathp flag eff m m' evs,
  check_newfstatat i dirfd pathp flag eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i dirfd pathp flag eff m m' evs H.
  unfold check_newfstatat in H. vd_frame2 H.
Qed.

Lemma check_fstat_file_vdso_frame : forall i p statbuf eff m m' evs,
  check_fstat_file i p statbuf eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i p statbuf eff m m' evs H.
  unfold check_fstat_file in H.
  destruct (fs_lookup (m_fs m) p) as [data|]; [|discriminate].
  destruct (negb (access_okb statbuf STAT_SIZE)); [vd_frame2 H|].
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

Lemma check_fstat_chrdev_vdso_frame : forall ok p i statbuf eff m m' evs,
  check_fstat_chrdev ok p i statbuf eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros ok p i statbuf eff m m' evs H.
  unfold check_fstat_chrdev in H.
  destruct (negb (access_okb statbuf STAT_SIZE)); [vd_frame2 H|].
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

Lemma check_fstat_devnull_vdso_frame : forall i statbuf eff m m' evs,
  check_fstat_devnull i statbuf eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof. intros. eapply check_fstat_chrdev_vdso_frame. exact H. Qed.

Lemma check_fstat_urandom_vdso_frame : forall i statbuf eff m m' evs,
  check_fstat_urandom i statbuf eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof. intros. eapply check_fstat_chrdev_vdso_frame. exact H. Qed.

Lemma check_fstat_vdso_frame : forall i fd statbuf eff m m' evs,
  check_fstat i fd statbuf eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros i fd statbuf eff m m' evs H. unfold check_fstat in H.
  destruct (fd_lookup (m_fds m) fd) as [e|]; [|vd_frame2 H].
  destruct e; try discriminate;
    first [eapply check_fstat_file_vdso_frame; exact H
          |eapply check_fstat_devnull_vdso_frame; exact H
          |eapply check_fstat_urandom_vdso_frame; exact H].
Qed.

Lemma check_getid_vdso_frame : forall sel eff m m' evs,
  check_getid sel eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof. intros sel eff m m' evs H. unfold check_getid in H. vd_frame2 H. Qed.

Lemma check_setid_vdso_frame : forall get put user v eff m m' evs,
  check_setid get put user v eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros get put user v eff m m' evs H.
  unfold check_setid, check_setid_result in H. vd_frame2 H.
Qed.

Lemma check_setresid_vdso_frame : forall get put user r e sv eff m m' evs,
  check_setresid get put user r e sv eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros get put user r e sv eff m m' evs H.
  unfold check_setresid, check_setid_result in H. vd_frame2 H.
Qed.

Lemma check_getgroups_vdso_frame : forall gidsetsize eff m m' evs,
  check_getgroups gidsetsize eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros gidsetsize eff m m' evs H. unfold check_getgroups in H. vd_frame2 H.
Qed.

Lemma check_setgroups_vdso_frame : forall eff m m' evs,
  check_setgroups eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros eff m m' evs H. unfold check_setgroups in H. vd_frame2 H.
Qed.

Lemma check_socket_vdso_frame : forall domain type protocol eff m m' evs,
  check_socket domain type protocol eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros domain type protocol eff m m' evs H.
  unfold check_socket, check_new_fd_result in H. vd_frame2 H.
Qed.

Lemma check_bind_vdso_frame : forall i fd addrp addrlen eff m m' evs,
  check_bind i fd addrp addrlen eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i fd addrp addrlen eff m m' evs H.
  unfold check_bind, check_errno_or_success in H. vd_frame2 H.
Qed.

Lemma check_listen_vdso_frame : forall fd backlog eff m m' evs,
  check_listen fd backlog eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros fd backlog eff m m' evs H.
  unfold check_listen, check_errno_or_success, check_errno_only in H.
  vd_frame2 H.
Qed.

Lemma check_connect_vdso_frame : forall i fd addrp addrlen eff m m' evs,
  check_connect i fd addrp addrlen eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i fd addrp addrlen eff m m' evs H.
  unfold check_connect in H. vd_frame2 H.
Qed.

Lemma check_accept4_vdso_frame : forall fd addrp addrlenp flags eff m m' evs,
  check_accept4 fd addrp addrlenp flags eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros fd addrp addrlenp flags eff m m' evs H.
  unfold check_accept4, check_new_fd_result, check_errno_or_success,
    check_errno_only in H. vd_frame2 H.
Qed.

Lemma check_fcntl_vdso_frame : forall fd cmd arg eff m m' evs,
  check_fcntl fd cmd arg eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros fd cmd arg eff m m' evs H. unfold check_fcntl in H. vd_frame2 H.
Qed.

Lemma check_sched_setscheduler_vdso_frame : forall i pid policy param eff m m' evs,
  check_sched_setscheduler i pid policy param eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i pid policy param eff m m' evs H.
  unfold check_sched_setscheduler in H. vd_frame2 H.
Qed.

Lemma check_sched_getaffinity_vdso_frame : forall len eff m m' evs,
  check_sched_getaffinity len eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros len eff m m' evs H. unfold check_sched_getaffinity in H. vd_frame2 H.
Qed.

Lemma check_sched_yield_vdso_frame : forall eff m m' evs,
  check_sched_yield eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros eff m m' evs H. unfold check_sched_yield in H. vd_frame2 H.
Qed.

Lemma check_sigaltstack_vdso_frame : forall i uss uoss eff m m' evs,
  check_sigaltstack i uss uoss eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i uss uoss eff m m' evs H.
  unfold check_sigaltstack in H. vd_frame2 H.
Qed.

Lemma check_rt_sigaction_vdso_frame : forall i sig act oact ss eff m m' evs,
  check_rt_sigaction i sig act oact ss eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i sig act oact ss eff m m' evs H.
  unfold check_rt_sigaction in H. vd_frame2 H.
Qed.

Lemma check_clone_vdso_frame : forall flags eff m m' evs,
  check_clone flags eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros flags eff m m' evs H.
  unfold check_clone, check_clone_resolve, check_clone_answer in H.
  vd_frame2 H.
Qed.

Lemma check_clone3_vdso_frame : forall i uargs size eff m m' evs,
  check_clone3 i uargs size eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros i uargs size eff m m' evs H.
  unfold check_clone3, check_clone3_resolve, check_clone_answer in H.
  vd_frame2 H.
Qed.

Lemma check_getsockname_vdso_frame : forall fd eff m m' evs,
  check_getsockname fd eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros fd eff m m' evs H.
  unfold check_getsockname in H. vd_frame2 H.
Qed.

Lemma check_getpeername_vdso_frame : forall fd eff m m' evs,
  check_getpeername fd eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros fd eff m m' evs H.
  unfold check_getpeername in H. vd_frame2 H.
Qed.

Lemma check_setsockopt_vdso_frame : forall fd level optlen eff m m' evs,
  check_setsockopt fd level optlen eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros fd level optlen eff m m' evs H.
  unfold check_setsockopt in H. vd_frame2 H.
Qed.

Lemma check_getsockopt_vdso_frame : forall i fd level optlenp eff m m' evs,
  check_getsockopt i fd level optlenp eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i fd level optlenp eff m m' evs H.
  unfold check_getsockopt in H. vd_frame2 H.
Qed.

Lemma check_shutdown_vdso_frame : forall fd how eff m m' evs,
  check_shutdown fd how eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros fd how eff m m' evs H.
  unfold check_shutdown in H. vd_frame2 H.
Qed.

Lemma check_send_on_socket_vdso_frame :
  forall pre acc fd sk total bs eff m m' evs,
  check_send_on_socket pre acc fd sk total bs eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros pre acc fd sk total bs eff m m' evs H.
  unfold check_send_on_socket in H. vd_frame2 H.
Qed.

Lemma check_recv_fd_answer_vdso_frame : forall fds fd eff m m' evs,
  check_recv_fd_answer fds fd eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros fds fd eff m m' evs H.
  unfold check_recv_fd_answer in H. vd_frame2 H.
Qed.

Lemma check_socketpair_vdso_frame : forall i family type protocol sv eff m m' evs,
  check_socketpair i family type protocol sv eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i family type protocol sv eff m m' evs H.
  unfold check_socketpair, check_socketpair_written, check_socketpair_faulted
    in H. vd_frame2 H.
Qed.

Lemma check_recvfrom_vdso_frame : forall i fd buf size eff m m' evs,
  check_recvfrom i fd buf size eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i fd buf size eff m m' evs H.
  unfold check_recvfrom, check_access_ok_zero, check_recv_fd_answer in H.
  vd_frame2 H.
Qed.

Lemma check_recvmsg_vdso_frame : forall fd flags eff m m' evs,
  check_recvmsg fd flags eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros fd flags eff m m' evs H.
  unfold check_recvmsg, check_recv_fd_answer in H. vd_frame2 H.
Qed.

Lemma check_sendto_vdso_frame : forall i fd buf count flags addrp eff m m' evs,
  check_sendto i fd buf count flags addrp eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i fd buf count flags addrp eff m m' evs H.
  unfold check_sendto, check_access_ok_zero, check_send_on_socket in H.
  vd_frame2 H.
Qed.

Lemma check_sendmsg_vdso_frame : forall i fd msgp flags eff m m' evs,
  check_sendmsg i fd msgp flags eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i fd msgp flags eff m m' evs H.
  unfold check_sendmsg, check_send_on_socket in H. vd_frame2 H.
Qed.

Lemma check_pipe2_vdso_frame : forall i fildes flags eff m m' evs,
  check_pipe2 i fildes flags eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i fildes flags eff m m' evs H.
  unfold check_pipe2, pipe2_model in H. vd_frame2 H.
Qed.

Lemma check_futex_vdso_frame : forall i uaddr op val utime eff m m' evs,
  check_futex i uaddr op val utime eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i uaddr op val utime eff m m' evs H.
  unfold check_futex, check_futex_wake_private, check_futex_wait_private in H.
  vd_frame2 H.
Qed.

(** The three signal arms whose [*_frame] lemmas live in
    [Checks/Sys/Kernel/Signal.v], with the same proofs. *)
Lemma m_vdso_sigmask_deliver_model : forall new m,
  m_vdso (sigmask_deliver_model new m) = m_vdso m.
Proof.
  intros new m. unfold sigmask_deliver_model.
  destruct (m_sigabrt_pending m && negb (sigabrt_blocked new))%bool;
    autorewrite with model; reflexivity.
Qed.

Lemma check_rt_sigprocmask_vdso_frame : forall i how nset oset ss eff m m' evs,
  check_rt_sigprocmask i how nset oset ss eff m = CheckOk m' evs ->
  m_vdso m' = m_vdso m.
Proof.
  intros i how nset oset ss eff m m' evs H.
  unfold check_rt_sigprocmask in H.
  destruct (negb (bv_eqb ss (Z_to_bv 64 NSIG_BYTES))) eqn:Hss;
    cbv beta iota zeta in H.
  { apply check_ret_only_ok_iff in H. now destruct H as (_ & -> & _). }
  destruct (w_is0 nset) eqn:Hn; cbv beta iota in H.
  { destruct (w_is0 oset) eqn:Ho; cbv beta iota in H.
    - apply check_ret_only_ok_iff in H. now destruct H as (_ & -> & _).
    - apply check_write_oset_ok_iff in H. now destruct H as (-> & _ & _ & _). }
  destruct (user_read i m nset (Z_to_bv 64 NSIG_BYTES)) as [bs| |] eqn:Hr;
    cbv beta iota in H.
  3:{ discriminate. }
  2:{ apply check_ret_only_ok_iff in H. now destruct H as (_ & -> & _). }
  destruct (negb (how_valid how)) eqn:Hh; cbv beta iota zeta in H.
  { apply check_ret_only_copyins_ok_iff in H. now destruct H as (_ & -> & _). }
  destruct (w_is0 oset) eqn:Ho; cbv beta iota in H.
  { apply check_ret_only_copyins_ok_iff in H. destruct H as (_ & -> & _).
    now rewrite m_vdso_sigmask_deliver_model. }
  unfold check_write_oset_copyins in H.
  destruct (check_write_oset i oset (m_sigmask m) (clear_copyins eff)
              (sigmask_deliver_model (sigmask_apply how (m_sigmask m)
                               (sigmask_strip (sigset_of bs))) m))
    as [m2 evs2| |] eqn:Hcw; [|discriminate|discriminate].
  destruct (access_ranges_eqb (eff_copyins eff)
              [(nset, Z.to_nat NSIG_BYTES)]); [|discriminate].
  apply check_write_oset_ok_iff in Hcw. destruct Hcw as (-> & _ & _ & _).
  inversion H; subst. now rewrite m_vdso_sigmask_deliver_model.
Qed.

Lemma check_tkill_vdso_frame : forall pid sig eff m m' evs,
  check_tkill pid sig eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros pid sig eff m m' evs H.
  unfold check_tkill, check_tkill_self, check_send_sigabrt in H.
  repeat match type of H with
         | (if ?b then _ else _) = _ => destruct b; cbv beta iota in H
         | match ?x with _ => _ end = _ => destruct x; cbv beta iota in H
         end;
    try discriminate;
    try (apply check_ret_only_ok_iff in H; destruct H as (_ & -> & _);
         reflexivity);
    inversion H; subst; autorewrite with model; reflexivity.
Qed.

Lemma check_tgkill_vdso_frame : forall tgid pid sig eff m m' evs,
  check_tgkill tgid pid sig eff m = CheckOk m' evs -> m_vdso m' = m_vdso m.
Proof.
  intros tgid pid sig eff m m' evs H.
  unfold check_tgkill, check_tkill_self, check_send_sigabrt in H.
  repeat match type of H with
         | (if ?b then _ else _) = _ => destruct b; cbv beta iota in H
         | match ?x with _ => _ end = _ => destruct x; cbv beta iota in H
         end;
    try discriminate;
    try (apply check_ret_only_ok_iff in H; destruct H as (_ & -> & _);
         reflexivity);
    inversion H; subst; autorewrite with model; reflexivity.
Qed.


(* -------------------------------------------------------------------------
   The invariant, over the whole dispatcher
   ------------------------------------------------------------------------- *)

(** [execve] establishes it: the ledger starts empty, and with a page
    aligned, nonzero break the heap range [[brk0, PAGE_ALIGN brk0)] is
    empty.  Where [init_model] places the pair does not matter. *)
Lemma init_model_vdso_inv : forall reserved brk0 mbase sp lim inp,
  0 < bv_unsigned brk0 -> bv_unsigned brk0 mod page_size = 0 ->
  vdso_inv (init_model reserved brk0 mbase sp lim inp).
Proof.
  intros reserved brk0 mbase sp lim inp Hpos Hal. unfold vdso_inv.
  assert (Hm : m_vmmaps (init_model reserved brk0 mbase sp lim inp)
               = mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp) by reflexivity.
  rewrite Hm. unfold vd_inv, vd_maps, vd_heap. cbn [vm_maps vm_start_brk vm_brk].
  split; [intros a sz []|]. split; [lia|].
  apply vdso_meets_empty. apply page_round_up_Z_le_aligned; [exact Hal | lia].
Qed.

Ltac vd_arm L1 L2 :=
  lazymatch goal with
  | Hinv : vdso_inv ?m |- vdso_inv ?m' =>
      apply (vdso_inv_frame m m');
      [ eapply L1; eassumption | eapply L2; eassumption | exact Hinv ]
  end.

Definition arm_preserves_vdso (c : CheckedArm) : Prop :=
  forall i eff m m' evs,
    ca_check c i eff m = CheckOk m' evs ->
    vm_fit (m_vmmaps m) -> vdso_inv m -> vdso_inv m'.

(** The enumeration is [VmMapsDisjoint.checked_table_preserves_vm]'s, arm
    for arm: the five writers by their own lemmas, every other arm by its
    two frame lemmas. *)
Lemma checked_table_preserves_vdso : Forall arm_preserves_vdso checked_table.
Proof.
  unfold checked_table.
  repeat apply Forall_cons.
  all: try exact (Forall_nil arm_preserves_vdso).
  all: unfold arm_preserves_vdso; intros i eff m m' evs H Hfit Hinv;
       autorewrite with arm_unfold in H.
  all: first
    [ eapply check_brk_preserves_vdso; eassumption
    | eapply check_mmap_preserves_vdso; eassumption
    | eapply check_munmap_preserves_vdso; eassumption
    | eapply check_mremap_preserves_vdso; eassumption
    | eapply check_mprotect_preserves_vdso; eassumption
    | vd_arm check_madvise_frame check_madvise_vdso_frame
    | vd_arm check_read_frame check_read_vdso_frame
    | vd_arm check_write_frame check_write_vdso_frame
    | vd_arm check_pread64_frame check_pread64_vdso_frame
    | vd_arm check_pwrite64_frame check_pwrite64_vdso_frame
    | vd_arm check_readv_frame check_readv_vdso_frame
    | vd_arm check_writev_frame check_writev_vdso_frame
    | vd_arm check_openat_frame check_openat_vdso_frame
    | vd_arm check_close_frame check_close_vdso_frame
    | vd_arm check_lseek_frame check_lseek_vdso_frame
    | vd_arm check_ftruncate_frame check_ftruncate_vdso_frame
    | vd_arm check_ioctl_frame check_ioctl_vdso_frame
    | vd_arm check_readlinkat_frame check_readlinkat_vdso_frame
    | vd_arm check_wait4_frame check_wait4_vdso_frame
    | vd_arm check_fsync_frame check_fsync_vdso_frame
    | vd_arm check_getdents64_frame check_getdents64_vdso_frame
    | vd_arm check_flock_frame check_flock_vdso_frame
    | vd_arm check_exit_frame check_exit_vdso_frame
    | vd_arm check_set_tid_address_frame check_set_tid_address_vdso_frame
    | vd_arm check_getpid_frame check_getpid_vdso_frame
    | vd_arm check_gettid_frame check_gettid_vdso_frame
    | vd_arm check_setsid_frame check_setsid_vdso_frame
    | vd_arm check_uname_frame check_uname_vdso_frame
    | vd_arm check_prctl_frame check_prctl_vdso_frame
    | vd_arm check_prlimit64_frame check_prlimit64_vdso_frame
    | vd_arm check_getrandom_frame check_getrandom_vdso_frame
    | vd_arm check_gettimeofday_frame check_gettimeofday_vdso_frame
    | vd_arm check_clock_gettime_frame check_clock_gettime_vdso_frame
    | vd_arm check_nanosleep_frame check_nanosleep_vdso_frame
    | vd_arm check_dup_frame check_dup_vdso_frame
    | vd_arm check_dup3_frame check_dup3_vdso_frame
    | vd_arm check_unlinkat_frame check_unlinkat_vdso_frame
    | vd_arm check_faccessat_frame check_faccessat_vdso_frame
    | vd_arm check_faccessat2_frame check_faccessat2_vdso_frame
    | vd_arm check_pselect6_frame check_pselect6_vdso_frame
    | vd_arm check_ppoll_frame check_ppoll_vdso_frame
    | vd_arm check_newfstatat_frame check_newfstatat_vdso_frame
    | vd_arm check_fstat_frame check_fstat_vdso_frame
    | vd_arm check_getid_frame check_getid_vdso_frame
    | vd_arm check_setid_frame check_setid_vdso_frame
    | vd_arm check_setresid_frame check_setresid_vdso_frame
    | vd_arm check_getgroups_frame check_getgroups_vdso_frame
    | vd_arm check_setgroups_frame check_setgroups_vdso_frame
    | vd_arm check_socket_frame check_socket_vdso_frame
    | vd_arm check_bind_frame check_bind_vdso_frame
    | vd_arm check_listen_frame check_listen_vdso_frame
    | vd_arm check_accept4_frame check_accept4_vdso_frame
    | vd_arm check_fcntl_frame check_fcntl_vdso_frame
    | vd_arm check_sched_setscheduler_frame check_sched_setscheduler_vdso_frame
    | vd_arm check_sched_getaffinity_frame check_sched_getaffinity_vdso_frame
    | vd_arm check_sched_yield_frame check_sched_yield_vdso_frame
    | vd_arm check_sigaltstack_frame check_sigaltstack_vdso_frame
    | vd_arm check_rt_sigaction_frame check_rt_sigaction_vdso_frame
    | vd_arm check_tkill_frame check_tkill_vdso_frame
    | vd_arm check_tgkill_frame check_tgkill_vdso_frame
    | vd_arm check_rt_sigprocmask_frame check_rt_sigprocmask_vdso_frame
    | vd_arm check_futex_frame check_futex_vdso_frame
    | vd_arm check_clone_frame check_clone_vdso_frame
    | vd_arm check_clone3_frame check_clone3_vdso_frame
    | vd_arm check_getsockname_frame check_getsockname_vdso_frame
    | vd_arm check_getpeername_frame check_getpeername_vdso_frame
    | vd_arm check_setsockopt_frame check_setsockopt_vdso_frame
    | vd_arm check_getsockopt_frame check_getsockopt_vdso_frame
    | vd_arm check_shutdown_frame check_shutdown_vdso_frame
    | vd_arm check_sendto_frame check_sendto_vdso_frame
    | vd_arm check_sendmsg_frame check_sendmsg_vdso_frame
    | vd_arm check_socketpair_frame check_socketpair_vdso_frame
    | vd_arm check_recvfrom_frame check_recvfrom_vdso_frame
    | vd_arm check_recvmsg_frame check_recvmsg_vdso_frame
    | vd_arm check_connect_frame check_connect_vdso_frame
    | vd_arm check_timerfd_create_frame check_timerfd_create_vdso_frame
    | vd_arm check_eventfd2_frame check_eventfd2_vdso_frame
    | vd_arm check_pipe2_frame check_pipe2_vdso_frame
    | vd_arm check_getcwd_frame check_getcwd_vdso_frame
    | vd_arm check_epoll_create1_frame check_epoll_create1_vdso_frame
    | vd_arm check_epoll_ctl_frame check_epoll_ctl_vdso_frame
    | vd_arm check_epoll_pwait_frame check_epoll_pwait_vdso_frame
    | fail 1 "checked_table_preserves_vdso has no case for this dispatcher arm: give the new checker a *_vdso_frame lemma (it leaves m_vdso alone; vd_frame2) beside its *_frame one, or a *_preserves_vdso one (it writes vm_maps, the break or m_vdso), and add it to the list above" ].
Qed.

Theorem check_syscall_preserves_vdso_inv : forall i eff m m' evs,
  check_syscall i eff m = CheckOk m' evs ->
  vm_fit (m_vmmaps m) -> vdso_inv m -> vdso_inv m'.
Proof.
  intros i eff m m' evs H Hfit Hinv. unfold check_syscall in H.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk;
    [|discriminate H].
  pose proof checked_table_preserves_vdso as Hall.
  rewrite Forall_forall in Hall.
  exact (Hall c (lookup_ca_In _ _ _ Elk) i eff m m' evs H Hfit Hinv).
Qed.

(** The same statement against the RELATIONAL spec. *)
Corollary syscall_spec_preserves_vdso_inv : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  vm_fit (m_vmmaps m) -> vdso_inv m -> vdso_inv m'.
Proof.
  intros i m eff m' evs H Hfit Hinv.
  eapply check_syscall_preserves_vdso_inv; [| exact Hfit | exact Hinv].
  apply check_syscall_ok_iff. exact H.
Qed.

(** The shrink arms of brk, munmap and MAP_FIXED read [MapsFit.vm_fit],
    so the invariant a run carries is the pair. *)
Definition vdso_sys_inv (m : Model) : Prop := vm_fit (m_vmmaps m) /\ vdso_inv m.

Theorem check_syscall_preserves_vdso_sys_inv : forall i eff m m' evs,
  check_syscall i eff m = CheckOk m' evs -> vdso_sys_inv m -> vdso_sys_inv m'.
Proof.
  intros i eff m m' evs H [Hfit Hinv]. split.
  - exact (check_syscall_preserves_vm_fit i eff m m' evs H Hfit).
  - exact (check_syscall_preserves_vdso_inv i eff m m' evs H Hfit Hinv).
Qed.

Corollary syscall_spec_preserves_vdso_sys_inv : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) -> vdso_sys_inv m -> vdso_sys_inv m'.
Proof.
  intros i m eff m' evs H Hinv.
  eapply check_syscall_preserves_vdso_sys_inv; [|exact Hinv].
  apply check_syscall_ok_iff. exact H.
Qed.

(* -------------------------------------------------------------------------
   On every reachable configuration
   ------------------------------------------------------------------------- *)

(** A model with the same ledger and the same [ProcState] (which holds
    [m_vdso]) keeps the invariant. *)
Lemma vdso_sys_inv_frame : forall m m',
  m_vmmaps m' = m_vmmaps m -> m_proc m' = m_proc m ->
  vdso_sys_inv m -> vdso_sys_inv m'.
Proof.
  intros m m' Hvm Hp [Hfit Hinv]. split.
  - unfold vm_fit in *. rewrite Hvm. exact Hfit.
  - apply (vdso_inv_frame m m'); [exact Hvm | | exact Hinv].
    unfold m_vdso. rewrite Hp. reflexivity.
Qed.

(** One transition keeps [vdso_sys_inv]: an instruction step leaves the
    ledger and [ProcState] alone ([Run.mi_account_step_model_frame]); a
    system call moves them as its spec says
    ([syscall_spec_preserves_vdso_sys_inv]) and the materialization that
    follows leaves them alone ([State.materialize_model_accesses_frame]);
    an exit or a kill keeps the spec's own post-model. *)
Lemma sstep_preserves_vdso_sys_inv : forall segs c evs c',
  sstep segs c evs (SNext c') ->
  vdso_sys_inv (cfg_model c) -> vdso_sys_inv (cfg_model c').
Proof.
  intros segs [ms model] evs c' Hstep Hinv. cbn [cfg_model] in Hinv.
  inversion Hstep; subst; cbn [cfg_model].
  - match goal with
    | [ H : mi_account_step _ _ _ = RiscvSemantics.MachineOk (_, _) |- _ ] =>
        destruct (mi_account_step_model_frame _ _ _ _ _ H) as (_&Hvm&_&_&_&Hp&_)
    end.
    exact (vdso_sys_inv_frame _ _ Hvm Hp Hinv).
  - match goal with
    | [ Hs : syscall_spec _ _ (Ok _ ?m1 _),
        Hm : materialize_model_accesses ?m1 _ = Some _ |- _ ] =>
        destruct (materialize_model_accesses_frame _ _ _ Hm) as (_&Hvm&_&_&_&Hp&_);
        exact (vdso_sys_inv_frame _ _ Hvm Hp
                 (syscall_spec_preserves_vdso_sys_inv _ _ _ _ _ Hs Hinv))
    end.
  - match goal with
    | [ Hs : syscall_spec _ _ (Ok _ _ _) |- _ ] =>
        exact (syscall_spec_preserves_vdso_sys_inv _ _ _ _ _ Hs Hinv)
    end.
  - match goal with
    | [ Hs : syscall_spec _ _ (Ok _ _ _) |- _ ] =>
        exact (syscall_spec_preserves_vdso_sys_inv _ _ _ _ _ Hs Hinv)
    end.
Qed.

Lemma star_preserves_vdso_sys_inv : forall segs c tr c',
  star segs c tr c' ->
  vdso_sys_inv (cfg_model c) -> vdso_sys_inv (cfg_model c').
Proof.
  intros segs c tr c' Hstar.
  induction Hstar as [c | c1 evs c2 tr c3 Hstep Hstar IH]; intros Hinv;
    [exact Hinv|].
  exact (IH (sstep_preserves_vdso_sys_inv _ _ _ _ Hstep Hinv)).
Qed.

(** The same under a spurious-failure configuration, whose executions are
    executions of the unfiltered run ([Run.star_cfg_sub]). *)
Corollary star_cfg_preserves_vdso_sys_inv : forall segs cfg c tr c',
  star_cfg segs cfg c tr c' ->
  vdso_sys_inv (cfg_model c) -> vdso_sys_inv (cfg_model c').
Proof.
  intros segs cfg c tr c' Hstar.
  exact (star_preserves_vdso_sys_inv _ _ _ _ (star_cfg_sub _ _ _ _ _ Hstar)).
Qed.

(** The start of a run: [Run.init_config]'s model is [State.init_model].
    [Run.valid_brk] makes the break page aligned and at least the image
    top, so an image that loads a byte starts with a nonzero break. *)
Lemma init_config_vdso_sys_inv : forall segs pc ph sp brk0 mb rnd lim inp,
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  vdso_sys_inv (cfg_model (init_config segs pc ph sp brk0 mb rnd lim inp)).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp (Hlo & _ & Hal) Htop.
  unfold init_config. cbn [cfg_model]. split.
  - apply init_model_vm_fit.
  - apply init_model_vdso_inv; [lia | exact Hal].
Qed.

Corollary init_config_star_vdso_sys_inv :
  forall segs pc ph sp brk0 mb rnd lim inp tr c,
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  star segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr c ->
  vdso_sys_inv (cfg_model c).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp tr c Hbrk Htop Hstar.
  exact (star_preserves_vdso_sys_inv _ _ _ _ Hstar
           (init_config_vdso_sys_inv _ _ _ _ _ _ _ _ _ Hbrk Htop)).
Qed.

Corollary init_config_star_cfg_vdso_sys_inv :
  forall segs cfg pc ph sp brk0 mb rnd lim inp tr c,
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  star_cfg segs cfg (init_config segs pc ph sp brk0 mb rnd lim inp) tr c ->
  vdso_sys_inv (cfg_model c).
Proof.
  intros segs cfg pc ph sp brk0 mb rnd lim inp tr c Hbrk Htop Hstar.
  exact (star_cfg_preserves_vdso_sys_inv _ _ _ _ _ Hstar
           (init_config_vdso_sys_inv _ _ _ _ _ _ _ _ _ Hbrk Htop)).
Qed.

(** What the pair section of [Sys/Mm/Mmap.v] cites: on every configuration
    a run reaches, no recorded mapping meets a mapped range of the pair. *)
Corollary init_config_star_vdso_maps_disjoint :
  forall segs pc ph sp brk0 mb rnd lim inp tr c,
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  star segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr c ->
  vdso_maps_disjoint (cfg_model c).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp tr c Hbrk Htop Hstar.
  apply vdso_inv_maps_disjoint.
  exact (proj2 (init_config_star_vdso_sys_inv _ _ _ _ _ _ _ _ _ _ _ Hbrk Htop Hstar)).
Qed.

Corollary init_config_star_cfg_vdso_maps_disjoint :
  forall segs cfg pc ph sp brk0 mb rnd lim inp tr c,
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  star_cfg segs cfg (init_config segs pc ph sp brk0 mb rnd lim inp) tr c ->
  vdso_maps_disjoint (cfg_model c).
Proof.
  intros segs cfg pc ph sp brk0 mb rnd lim inp tr c Hbrk Htop Hstar.
  apply vdso_inv_maps_disjoint.
  exact (proj2 (init_config_star_cfg_vdso_sys_inv _ _ _ _ _ _ _ _ _ _ _ _
                  Hbrk Htop Hstar)).
Qed.
