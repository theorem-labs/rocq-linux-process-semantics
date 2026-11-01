(** * LinuxProcessSem.Checks.MunmapCut — what a partial [munmap] leaves

    Not part of the trusted specification.  When [Mmap.munmap_spec]
    answers 0 to an unmap that unmaps — the exact arm or a partial one —
    it cuts both ledgers with [maps_subtract] over the page-rounded range
    ([Mmap.mmap_fixed_destroyed_next]).  This file states what that cut
    does:

    - [check_munmap_zero_owned]: after a 0 answer that is not the exact
      arm, the bytes [vm_maps] owns are the old ones outside the range;
      [check_munmap_zero_pages] says the same of whole pages;
    - [check_munmap_unmap_backing]: every answer that unmaps, whole or
      partial, cuts the lazy and materialized ledgers by the same range,
      so the backing charge of the range is released the same way.

    The ledger invariants are [NoaccessOwned.sys_inv], and
    [NoaccessOwned.check_syscall_preserves_sys_inv] covers the partial
    arm. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run MemImageType StackLayout.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs VmMapsDisjoint MapsFit NoaccessOwned.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* -------------------------------------------------------------------------
   The cut, as a set of bytes
   ------------------------------------------------------------------------- *)

(** A byte of an entry outside the cut is in one of its remnants. *)
Lemma iv_subtract_keeps : forall a s lo hi x,
  bv_unsigned a + bv_unsigned s <= two_pow_64 ->
  bv_unsigned a <= x < bv_unsigned a + bv_unsigned s ->
  ~ (lo <= x < hi) ->
  exists a' s', In (a', s') (iv_subtract a s lo hi)
    /\ bv_unsigned a' <= x < bv_unsigned a' + bv_unsigned s'.
Proof.
  intros a s lo hi x Hf Hx Hc. unfold two_pow_64 in Hf.
  pose proof (word_range a). pose proof (word_range s).
  unfold iv_subtract. cbv zeta.
  destruct (Z_lt_ge_dec x lo) as [Hlt|Hge].
  - exists a, (Z_to_bv 64 (Z.min (bv_unsigned s) (lo - bv_unsigned a))).
    assert (E : (bv_unsigned a <? lo) = true) by (apply Z.ltb_lt; lia).
    rewrite E. split; [apply in_or_app; left; left; reflexivity|].
    pose proof (Z.min_spec (bv_unsigned s) (lo - bv_unsigned a)).
    rewrite u64 by lia. lia.
  - exists (Z_to_bv 64 (Z.max (bv_unsigned a) hi)),
      (Z_to_bv 64 (bv_unsigned a + bv_unsigned s - Z.max (bv_unsigned a) hi)).
    assert (E : (hi <? bv_unsigned a + bv_unsigned s) = true)
      by (apply Z.ltb_lt; lia).
    rewrite E. split.
    + apply in_or_app. right. left. reflexivity.
    + pose proof (Z.max_spec (bv_unsigned a) hi).
      rewrite !u64 by lia. lia.
Qed.

Lemma maps_subtract_keeps : forall l lo hi x,
  maps_fit l -> owned l x -> ~ (lo <= x < hi) ->
  owned (maps_subtract l lo hi) x.
Proof.
  induction l as [|[a s] r IH]; intros lo hi x Hf (b & t & Hin & Hx) Hc;
    [destruct Hin|].
  cbn [maps_subtract]. destruct Hin as [Heq|Hin].
  - inversion Heq; subst b t.
    destruct (iv_subtract_keeps a s lo hi x (Hf a s (or_introl eq_refl)) Hx Hc)
      as (a' & s' & Hin' & Hx').
    exists a', s'. split; [apply in_or_app; left; exact Hin' | exact Hx'].
  - assert (Ho : owned r x) by (exists b, t; split; assumption).
    destruct (IH lo hi x (fun c u H => Hf c u (or_intror H)) Ho Hc)
      as (a' & s' & Hin' & Hx').
    exists a', s'. split; [apply in_or_app; right; exact Hin' | exact Hx'].
Qed.

(** [maps_subtract] leaves exactly the bytes outside the cut. *)
Theorem maps_subtract_owned : forall l lo hi x,
  maps_fit l ->
  owned (maps_subtract l lo hi) x <-> owned l x /\ ~ (lo <= x < hi).
Proof.
  intros l lo hi x Hf. split.
  - intros (a' & s' & Hin & Hx).
    destruct (maps_subtract_bytes l lo hi a' s' x Hf Hin Hx)
      as (a & s & Hin0 & Hx0 & Hc).
    split; [exists a, s; split; assumption | exact Hc].
  - intros [Ho Hc]. exact (maps_subtract_keeps l lo hi x Hf Ho Hc).
Qed.

(* -------------------------------------------------------------------------
   The checker's 0 answers
   ------------------------------------------------------------------------- *)

Lemma zero_ne_einval : Z_to_bv 64 0 <> errno_ret EINVAL.
Proof. intro H. apply (f_equal bv_unsigned) in H. vm_compute in H. discriminate. Qed.

(** A 0 answer passed both argument gates. *)
Lemma check_munmap_zero_args : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs ->
  eff_ret eff = Z_to_bv 64 0 ->
  bv_unsigned addr mod page_size = 0
  /\ bv_unsigned addr + page_round_up_Z (bv_unsigned len) <= TASK_SIZE.
Proof.
  intros addr len [ret ws zs us cs ci] m m' evs H Hr.
  cbn [eff_ret] in Hr. subst ret.
  unfold check_munmap in H. cbv zeta in H.
  difn H Eargs.
  { apply check_ret_only_ok_iff in H as [Heff _].
    apply (f_equal eff_ret) in Heff. exfalso. exact (zero_ne_einval Heff). }
  difn H Etask.
  { apply check_ret_only_ok_iff in H as [Heff _].
    apply (f_equal eff_ret) in Heff. exfalso. exact (zero_ne_einval Heff). }
  apply orb_false_iff in Eargs as [Ealign _].
  apply negb_false_iff, Z.eqb_eq in Ealign.
  apply Z.ltb_ge in Etask. split; assumption.
Qed.

(** After a 0 answer that is not the exact arm — the free-range no-op or
    the cut — [vm_maps] owns exactly the bytes it owned outside the
    page-rounded range. *)
Theorem check_munmap_zero_owned : forall addr len eff m m' evs,
  vm_fit (m_vmmaps m) ->
  map_has (vm_maps (m_vmmaps m)) addr
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = false ->
  check_munmap addr len eff m = CheckOk m' evs ->
  eff_ret eff = Z_to_bv 64 0 ->
  forall x,
    owned (vm_maps (m_vmmaps m')) x
    <-> owned (vm_maps (m_vmmaps m)) x
        /\ ~ (bv_unsigned addr <= x
              < bv_unsigned addr + page_round_up_Z (bv_unsigned len)).
Proof.
  intros addr len eff m m' evs Hfit Hhas H Hr x.
  destruct (check_munmap_zero_args addr len eff m m' evs H Hr) as [_ Hb].
  unfold TASK_SIZE in Hb.
  pose proof (word_range addr) as Har. pose proof (word_range len) as Hlr.
  pose proof (page_round_up_Z_ge (bv_unsigned len) ltac:(lia)) as HnZ.
  assert (Hn : bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
               = page_round_up_Z (bv_unsigned len)) by (rewrite u64 by lia; reflexivity).
  destruct eff as [ret ws zs us cs ci]. cbn [eff_ret] in Hr. subst ret.
  unfold check_munmap in H. cbv zeta in H.
  difn H Eargs.
  { apply check_ret_only_ok_iff in H as [Heff _].
    apply (f_equal eff_ret) in Heff. exfalso. exact (zero_ne_einval Heff). }
  difn H Etask.
  { apply check_ret_only_ok_iff in H as [Heff _].
    apply (f_equal eff_ret) in Heff. exfalso. exact (zero_ne_einval Heff). }
  rewrite Hhas in H. cbv iota in H.
  difn H Efree.
  - (* the free range: nothing owned in it, nothing changes *)
    apply check_ret_only_model in H. subst m'.
    unfold munmap_free_ok in Efree. apply andb_true_iff in Efree as [Efree _].
    split; [|intros [Ho _]; exact Ho].
    intros Ho. split; [exact Ho|]. intros Hin.
    destruct Ho as (b & s & Hbs & Hx).
    pose proof (region_free_In _ _ _ _ _ Efree (in_or_app _ _ _ (or_intror Hbs)))
      as Hov.
    unfold iv_overlap in Hov. rewrite Hn in Hov.
    apply andb_false_iff in Hov as [Hov|Hov]; apply Z.ltb_ge in Hov; lia.
  - (* the cut *)
    difn H Ecut; [|discriminate].
    destruct ws, zs, cs, ci; try discriminate.
    replace (errno_ret_in munmap_errnos (Z_to_bv 64 0)) with false in H
      by reflexivity.
    cbv iota in H.
    dif H; [|discriminate]. injection H as <- <-.
    rewrite vmm_mmap_destroyed. unfold mmap_fixed_destroyed_next.
    cbn [vm_maps]. rewrite Hn. apply maps_subtract_owned. exact Hfit.
Qed.

(** Every byte of the page at [p] is owned. *)
Definition page_owned (maps : list (word * word)) (p : Z) : Prop :=
  forall x, p <= x < p + page_size -> owned maps x.

(** The same, page by page: the range is page aligned, so a page is in
    it whole or not at all. *)
Corollary check_munmap_zero_pages : forall addr len eff m m' evs p,
  vm_fit (m_vmmaps m) ->
  map_has (vm_maps (m_vmmaps m)) addr
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = false ->
  check_munmap addr len eff m = CheckOk m' evs ->
  eff_ret eff = Z_to_bv 64 0 ->
  p mod page_size = 0 ->
  page_owned (vm_maps (m_vmmaps m')) p
  <-> page_owned (vm_maps (m_vmmaps m)) p
      /\ ~ (bv_unsigned addr <= p
            < bv_unsigned addr + page_round_up_Z (bv_unsigned len)).
Proof.
  intros addr len eff m m' evs p Hfit Hhas H Hr Hp.
  destruct (check_munmap_zero_args addr len eff m m' evs H Hr) as [Ha _].
  pose proof (check_munmap_zero_owned addr len eff m m' evs Hfit Hhas H Hr)
    as Hx.
  unfold page_owned, page_size in *.
  pose proof (Z.div_mod (bv_unsigned addr) 4096 ltac:(lia)) as Hda.
  pose proof (Z.div_mod p 4096 ltac:(lia)) as Hdp.
  split.
  - intros Hall. split.
    + intros y Hy. exact (proj1 (proj1 (Hx y) (Hall y Hy))).
    + exact (proj2 (proj1 (Hx p) (Hall p ltac:(lia)))).
  - intros [Hall Hc] y Hy. apply (proj2 (Hx y)).
    split; [exact (Hall y Hy)|].
    intros Hin. apply Hc. rewrite Ha in Hda. rewrite Hp in Hdp. lia.
Qed.

(* -------------------------------------------------------------------------
   The backing charge
   ------------------------------------------------------------------------- *)

(** An answer that unmaps — the exact arm or the cut — forgets the lazy
    and materialized ledgers over the page-rounded range, by the one
    transition [Mmap.with_mmap_destroyed]. *)
Theorem check_munmap_unmap_backing : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs ->
  eff_unmaps eff <> [] ->
  let lo := bv_unsigned addr in
  let hi := (bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z in
  m_vm_lazy m' = maps_subtract (m_vm_lazy m) lo hi
  /\ m_vm_materialized m'
     = List.filter (page_outside_range lo hi) (m_vm_materialized m).
Proof.
  intros addr len [ret ws zs us cs ci] m m' evs H Hus lo hi.
  cbn [eff_unmaps] in Hus. unfold lo, hi. clear lo hi.
  pose proof (word_range addr) as Har. pose proof (word_range len) as Hlr.
  pose proof (page_round_up_Z_ge (bv_unsigned len) ltac:(lia)) as HnZ.
  unfold check_munmap in H. cbv zeta in H.
  difn H Eargs.
  { apply check_ret_only_ok_iff in H as [Heff _].
    inversion Heff; subst; contradiction. }
  difn H Etask.
  { apply check_ret_only_ok_iff in H as [Heff _].
    inversion Heff; subst; contradiction. }
  apply Z.ltb_ge in Etask. unfold TASK_SIZE in Etask.
  assert (Hn : bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
               = page_round_up_Z (bv_unsigned len)) by (rewrite u64 by lia; reflexivity).
  dif H.
  - destruct ws, zs, cs, ci; try discriminate.
    dif H.
    + destruct us; [contradiction|discriminate].
    + dif H; [|discriminate]. injection H as <- <-.
      unfold with_mmap_destroyed, vm_forget_range. rewrite Hn.
      split; reflexivity.
  - dif H.
    { apply check_ret_only_ok_iff in H as [Heff _].
      inversion Heff; subst; contradiction. }
    dif H; [|discriminate].
    destruct ws, zs, cs, ci; try discriminate.
    dif H.
    + destruct us; [contradiction|discriminate].
    + dif H; [|discriminate]. injection H as <- <-.
      unfold with_mmap_destroyed, vm_forget_range. rewrite Hn.
      split; reflexivity.
Qed.
