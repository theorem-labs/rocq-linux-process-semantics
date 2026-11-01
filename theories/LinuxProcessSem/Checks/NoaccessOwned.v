(** * LinuxProcessSem.Checks.NoaccessOwned — [State.noaccess_pages_owned] on every modeled step

    Not part of the trusted specification: the preservation half of the
    ledger invariant [State.noaccess_pages_owned], which
    [Mremap.mremap_fresh_avoids_noaccess] and
    [Checks.BudgetPremise.fresh_dst_avoids_noaccess] take as a hypothesis.

    ** Why the invariant is not proved on its own

    [noaccess_pages_owned] is not inductive.  A state can satisfy it with
    the only witness of a protected page being a mapping that starts in
    the middle of that page, and a later cut can take that mapping away
    while the protection stays whole.  Such a state is not reachable, and
    what makes it unreachable is a stronger statement, [na_inv] below:

    - every protected entry is page aligned, a whole number of pages,
      nonempty, and ends inside the address space ([na_shape]); and
    - every protected byte is OWNED, byte for byte, by a live mapping
      ([na_cover]).

    THE SECOND CONJUNCT HAD AN EXCEPTION UNTIL THIS REVISION, and losing
    it is a consequence of the brk ledger becoming page-granular.  While
    [Mmap.brk_maps_next] cut the LOGICAL tail [[r, b)] out of [vm_maps]
    on a shrink, and [Mmap.brk_unmaps] (page-rounded, empty for a
    same-page shrink) removed nothing from [vm_noaccess], a shrink to a
    break that is not page aligned left the slice
    [[vm_brk, PAGE_ALIGN vm_brk)] protected and owned by nothing — so
    [na_cover] had to allow it, asking only that the first byte of the
    break's page be owned.  [Mmap.brk_maps_next] no longer makes that
    cut: it takes out exactly the pages [Mmap.brk_unmaps] names.  The two
    lists lose the same interval, no step strands a protected byte, and
    the exception is gone — which is also why this file no longer needs
    the break at all except to keep [na_inv']'s shape.

    [na_inv_noaccess_pages_owned] derives [noaccess_pages_owned] from it.
    [na_inv] is preserved together with [VmMapsDisjoint.vm_wf] and
    [MapsFit.vm_fit] (a cut leaves remnants that re-enter [word]
    losslessly, so a byte outside the cut keeps an owner); [sys_inv] is the three
    together, [init_model_sys_inv] the base case,
    [check_syscall_preserves_sys_inv] / [syscall_spec_preserves_sys_inv]
    the system-call step, and [sstep_preserves_sys_inv] /
    [star_preserves_sys_inv] / [star_cfg_preserves_sys_inv] the whole
    run. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run MemImageType StackLayout.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs VmMapsDisjoint MapsFit.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* -------------------------------------------------------------------------
   The strengthened invariant
   ------------------------------------------------------------------------- *)

(** Byte [x] lies inside some entry of [maps]. *)
Definition owned (maps : list (word * word)) (x : Z) : Prop :=
  exists b s, In (b, s) maps
    /\ (bv_unsigned b <= x < bv_unsigned b + bv_unsigned s)%Z.

Definition na_shape (na : list (word * word)) : Prop :=
  forall a n, In (a, n) na ->
    (bv_unsigned a mod page_size = 0 /\ bv_unsigned n mod page_size = 0
     /\ 0 < bv_unsigned n /\ bv_unsigned a + bv_unsigned n <= two_pow_64)%Z.

(** [brk] is kept as a parameter, unread: it is what [na_inv'] and every
    lemma below are indexed by, and the exception that needed it is gone
    (see the header). *)
Definition na_cover (maps na : list (word * word)) (brk : Z) : Prop :=
  forall a n x, In (a, n) na ->
    (bv_unsigned a <= x < bv_unsigned a + bv_unsigned n)%Z ->
    owned maps x.

Definition na_inv' (maps na : list (word * word)) (brk : Z) : Prop :=
  na_shape na /\ na_cover maps na brk.

Definition na_inv (h : VmMaps) : Prop :=
  na_inv' (vm_maps h) (vm_noaccess h) (bv_unsigned (vm_brk h)).

Definition sys_inv (h : VmMaps) : Prop := vm_wf h /\ vm_fit h /\ na_inv h.

(* -------------------------------------------------------------------------
   Page arithmetic
   ------------------------------------------------------------------------- *)

Ltac pgf z :=
  pose proof (Z.div_mod z 4096 ltac:(lia));
  pose proof (Z.mod_pos_bound z 4096 ltac:(lia)).

Lemma pu_aligned : forall z, (page_round_up_Z z mod page_size = 0)%Z.
Proof. intro z. unfold page_round_up_Z. apply Z_mod_mult. Qed.

Lemma pu_ge : forall z, (z <= page_round_up_Z z)%Z.
Proof.
  intro z. unfold page_round_up_Z, page_size.
  pgf (z + 4096 - 1). lia.
Qed.

Lemma pd_le : forall z, (page_round_down_Z z <= z)%Z.
Proof. intro z. unfold page_round_down_Z, page_size. pgf z. lia. Qed.

(** A byte in the orphan slice of a break is on the break's page, and
    that page starts strictly below the break. *)
Lemma zone_floor : forall brk x,
  (brk <= x < page_round_up_Z brk)%Z ->
  page_round_down_Z x = page_round_down_Z brk
  /\ (page_round_down_Z brk < brk)%Z.
Proof.
  intros brk x Hx. unfold page_round_up_Z, page_round_down_Z, page_size in *.
  pgf x. pgf brk. pgf (brk + 4096 - 1).
  assert (Hq : (x / 4096 = brk / 4096)%Z) by lia.
  rewrite Hq. lia.
Qed.

(** A page-aligned window holding the first byte of the break's page
    holds every byte of the orphan slice. *)
Lemma zone_same_page : forall lo hi brk x,
  (lo mod page_size = 0)%Z -> (hi mod page_size = 0)%Z ->
  (brk <= x < page_round_up_Z brk)%Z ->
  (lo <= page_round_down_Z brk < hi)%Z ->
  (lo <= x < hi)%Z.
Proof.
  intros lo hi brk x Hlo Hhi Hx HP.
  destruct (zone_floor brk x Hx) as [Hfx _].
  rewrite <- Hfx in HP.
  destruct (page_round_down_Z_within lo hi (page_round_down_Z x) Hlo Hhi HP)
    as [_ H2].
  unfold page_round_down_Z, page_size in *.
  pgf x. pgf (x / 4096 * 4096). lia.
Qed.

Lemma aligned_add : forall x y,
  (x mod page_size = 0)%Z -> (y mod page_size = 0)%Z ->
  ((x + y) mod page_size = 0)%Z.
Proof.
  intros x y Hx Hy. rewrite Z.add_mod by (unfold page_size; lia).
  rewrite Hx, Hy. reflexivity.
Qed.

(* -------------------------------------------------------------------------
   [owned] under the ways a writer builds [vm_maps]
   ------------------------------------------------------------------------- *)

Lemma owned_cons : forall maps e x, owned maps x -> owned (e :: maps) x.
Proof.
  intros maps e x (b & s & Hin & Hx). exists b, s. split; [right; exact Hin | exact Hx].
Qed.

Lemma owned_app_l : forall l1 l2 x, owned l1 x -> owned (l1 ++ l2) x.
Proof.
  intros l1 l2 x (b & s & Hin & Hx). exists b, s.
  split; [apply in_or_app; left; exact Hin | exact Hx].
Qed.

Lemma owned_app_r : forall l1 l2 x, owned l2 x -> owned (l1 ++ l2) x.
Proof.
  intros l1 l2 x (b & s & Hin & Hx). exists b, s.
  split; [apply in_or_app; right; exact Hin | exact Hx].
Qed.

(** A byte outside a cut keeps its owner's remnant. *)
Lemma iv_subtract_owned : forall a s lo hi x,
  (bv_unsigned a + bv_unsigned s <= two_pow_64)%Z ->
  (bv_unsigned a <= x < bv_unsigned a + bv_unsigned s)%Z ->
  ~ (lo <= x < hi)%Z ->
  owned (iv_subtract a s lo hi) x.
Proof.
  intros a s lo hi x Hf Hx Hc. unfold two_pow_64 in Hf.
  pose proof (word_range a). pose proof (word_range s).
  unfold iv_subtract. cbv zeta.
  destruct (Z_lt_le_dec x lo) as [Hlo|Hlo].
  - apply owned_app_l.
    rewrite (proj2 (Z.ltb_lt (bv_unsigned a) lo) ltac:(lia)).
    exists a, (Z_to_bv 64 (Z.min (bv_unsigned s) (lo - bv_unsigned a))).
    split; [left; reflexivity|]. rewrite u64 by lia. lia.
  - apply owned_app_r.
    rewrite (proj2 (Z.ltb_lt hi (bv_unsigned a + bv_unsigned s)) ltac:(lia)).
    exists (Z_to_bv 64 (Z.max (bv_unsigned a) hi)),
      (Z_to_bv 64 (bv_unsigned a + bv_unsigned s - Z.max (bv_unsigned a) hi)).
    split; [left; reflexivity|]. rewrite !u64 by lia. lia.
Qed.

Lemma owned_subtract : forall maps lo hi x,
  maps_fit maps -> owned maps x -> ~ (lo <= x < hi)%Z ->
  owned (maps_subtract maps lo hi) x.
Proof.
  induction maps as [|[a s] r IH]; intros lo hi x Hf (b & t & Hin & Hx) Hc;
    [destruct Hin|].
  cbn [maps_subtract].
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. apply owned_app_l.
    apply iv_subtract_owned; [apply Hf; left; reflexivity | exact Hx | exact Hc].
  - apply owned_app_r. apply IH; [| exists b, t; split; [exact Hin | exact Hx] | exact Hc].
    intros c u Hcu. apply Hf. right. exact Hcu.
Qed.

Lemma map_contains_owned : forall maps lo n x,
  map_contains maps lo n = true ->
  (bv_unsigned lo <= x < bv_unsigned lo + bv_unsigned n)%Z ->
  owned maps x.
Proof.
  intros maps lo n x H Hx. unfold map_contains in H.
  apply existsb_exists in H as [[b s] [Hin H]]. cbv zeta in H. cbn [fst snd] in H.
  apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists b, s. split; [exact Hin | lia].
Qed.

(* -------------------------------------------------------------------------
   The protected list under a cut
   ------------------------------------------------------------------------- *)

Lemma na_shape_fit : forall na, na_shape na -> maps_fit na.
Proof. intros na H a n Hin. exact (proj2 (proj2 (proj2 (H a n Hin)))). Qed.

Lemma iv_subtract_bytes : forall a s lo hi a' s' x,
  (bv_unsigned a + bv_unsigned s <= two_pow_64)%Z ->
  In (a', s') (iv_subtract a s lo hi) ->
  (bv_unsigned a' <= x < bv_unsigned a' + bv_unsigned s')%Z ->
  (bv_unsigned a <= x < bv_unsigned a + bv_unsigned s)%Z /\ ~ (lo <= x < hi)%Z.
Proof.
  intros a s lo hi a' s' x Hf Hin Hx. unfold two_pow_64 in Hf.
  pose proof (word_range a). pose proof (word_range s).
  unfold iv_subtract in Hin. cbv zeta in Hin.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo)%Z eqn:E; [|destruct Hin].
    apply Z.ltb_lt in E.
    destruct Hin as [Heq|[]]. injection Heq as <- <-.
    rewrite u64 in Hx by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned s)%Z eqn:E; [|destruct Hin].
    apply Z.ltb_lt in E.
    destruct Hin as [Heq|[]]. injection Heq as <- <-.
    rewrite !u64 in Hx by lia. lia.
Qed.

Lemma maps_subtract_bytes : forall l lo hi a' s' x,
  maps_fit l -> In (a', s') (maps_subtract l lo hi) ->
  (bv_unsigned a' <= x < bv_unsigned a' + bv_unsigned s')%Z ->
  exists a s, In (a, s) l
    /\ (bv_unsigned a <= x < bv_unsigned a + bv_unsigned s)%Z
    /\ ~ (lo <= x < hi)%Z.
Proof.
  induction l as [|[a s] r IH]; intros lo hi a' s' x Hf Hin Hx;
    cbn [maps_subtract] in Hin; [destruct Hin|].
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (iv_subtract_bytes a s lo hi a' s' x
                (Hf a s (or_introl eq_refl)) Hin Hx) as [H1 H2].
    exists a, s. split; [left; reflexivity | split; assumption].
  - destruct (IH lo hi a' s' x (fun b t H => Hf b t (or_intror H)) Hin Hx)
      as (b & t & H1 & H2 & H3).
    exists b, t. split; [right; exact H1 | split; assumption].
Qed.

Lemma iv_subtract_shape : forall a s lo hi a' s',
  (bv_unsigned a mod page_size = 0)%Z -> (bv_unsigned s mod page_size = 0)%Z ->
  (0 < bv_unsigned s)%Z -> (bv_unsigned a + bv_unsigned s <= two_pow_64)%Z ->
  (lo mod page_size = 0)%Z -> (hi mod page_size = 0)%Z ->
  In (a', s') (iv_subtract a s lo hi) ->
  (bv_unsigned a' mod page_size = 0 /\ bv_unsigned s' mod page_size = 0
   /\ 0 < bv_unsigned s' /\ bv_unsigned a' + bv_unsigned s' <= two_pow_64)%Z.
Proof.
  intros a s lo hi a' s' Ha Hs Hpos Hf Hlo Hhi Hin.
  unfold two_pow_64 in *. unfold page_size in *.
  pose proof (word_range a). pose proof (word_range s).
  unfold iv_subtract in Hin. cbv zeta in Hin.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo)%Z eqn:E; [|destruct Hin].
    apply Z.ltb_lt in E.
    destruct Hin as [Heq|[]]. injection Heq as <- <-.
    rewrite u64 by lia.
    pgf (bv_unsigned a). pgf (bv_unsigned s). pgf lo.
    pgf (Z.min (bv_unsigned s) (lo - bv_unsigned a)).
    repeat split; lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned s)%Z eqn:E; [|destruct Hin].
    apply Z.ltb_lt in E.
    destruct Hin as [Heq|[]]. injection Heq as <- <-.
    rewrite !u64 by lia.
    pgf (bv_unsigned a). pgf (bv_unsigned s). pgf hi.
    pgf (Z.max (bv_unsigned a) hi).
    pgf (bv_unsigned a + bv_unsigned s - Z.max (bv_unsigned a) hi).
    repeat split; lia.
Qed.

Lemma maps_subtract_shape : forall na lo hi,
  na_shape na -> (lo mod page_size = 0)%Z -> (hi mod page_size = 0)%Z ->
  na_shape (maps_subtract na lo hi).
Proof.
  induction na as [|[a s] r IH]; intros lo hi Hsh Hlo Hhi;
    cbn [maps_subtract]; [intros b t []|].
  intros b t Hin. apply in_app_or in Hin as [Hin|Hin].
  - destruct (Hsh a s (or_introl eq_refl)) as (Ha & Hs & Hpos & Hf).
    exact (iv_subtract_shape a s lo hi b t Ha Hs Hpos Hf Hlo Hhi Hin).
  - apply (IH lo hi (fun c u H => Hsh c u (or_intror H)) Hlo Hhi b t Hin).
Qed.

(* -------------------------------------------------------------------------
   [na_inv'] under each shape of writer
   ------------------------------------------------------------------------- *)

(** [vm_maps] only grows: every grant that adds no protection. *)
Lemma na_inv_mono : forall maps maps' na brk,
  (forall x, owned maps x -> owned maps' x) ->
  na_inv' maps na brk -> na_inv' maps' na brk.
Proof.
  intros maps maps' na brk Hm [Hsh Hcov]. split; [exact Hsh|].
  intros a n x Hin Hx.
  exact (Hm x (Hcov a n x Hin Hx)).
Qed.

Lemma na_inv_cons_maps : forall maps na brk e,
  na_inv' maps na brk -> na_inv' (e :: maps) na brk.
Proof. intros maps na brk e. apply na_inv_mono. intros x. apply owned_cons. Qed.

(** A page-aligned cut of the protected list alone: [mprotect] and the
    contained rw MAP_FIXED. *)
Lemma na_inv_cut_na : forall maps na brk lo hi,
  (lo mod page_size = 0)%Z -> (hi mod page_size = 0)%Z ->
  na_inv' maps na brk -> na_inv' maps (maps_subtract na lo hi) brk.
Proof.
  intros maps na brk lo hi Hlo Hhi [Hsh Hcov]. split.
  - apply maps_subtract_shape; assumption.
  - intros a' n' x Hin Hx.
    destruct (maps_subtract_bytes na lo hi a' n' x (na_shape_fit _ Hsh) Hin Hx)
      as (a & n & Hin0 & Hx0 & _).
    exact (Hcov a n x Hin0 Hx0).
Qed.

(** The same page-aligned cut of both lists: the destructive MAP_FIXED
    failure and the cut half of a spanning MAP_FIXED. *)
Lemma na_inv_cut_both : forall maps na brk lo hi,
  maps_fit maps -> (lo mod page_size = 0)%Z -> (hi mod page_size = 0)%Z ->
  na_inv' maps na brk ->
  na_inv' (maps_subtract maps lo hi) (maps_subtract na lo hi) brk.
Proof.
  intros maps na brk lo hi Hmf Hlo Hhi [Hsh Hcov]. split.
  - apply maps_subtract_shape; assumption.
  - intros a' n' x Hin Hx.
    destruct (maps_subtract_bytes na lo hi a' n' x (na_shape_fit _ Hsh) Hin Hx)
      as (a & n & Hin0 & Hx0 & Hcut).
    apply owned_subtract; [exact Hmf | exact (Hcov a n x Hin0 Hx0) | exact Hcut].
Qed.

(** A request newly owned and newly protected: the PROT_NONE grants. *)
Lemma na_inv_cons_both : forall maps na brk a n,
  (bv_unsigned a mod page_size = 0)%Z -> (bv_unsigned n mod page_size = 0)%Z ->
  (0 < bv_unsigned n)%Z -> (bv_unsigned a + bv_unsigned n <= two_pow_64)%Z ->
  na_inv' maps na brk -> na_inv' ((a, n) :: maps) ((a, n) :: na) brk.
Proof.
  intros maps na brk a n Ha Hn Hpos Hf Hinv.
  destruct (na_inv_cons_maps maps na brk (a, n) Hinv) as [Hsh Hcov].
  split.
  - intros b s [Heq|Hin].
    + injection Heq as <- <-. repeat split; assumption.
    + exact (Hsh b s Hin).
  - intros b s x [Heq|Hin] Hx.
    + injection Heq as <- <-. exists a, n. split; [left; reflexivity | exact Hx].
    + exact (Hcov b s x Hin Hx).
Qed.

(** A request newly protected whose every byte is already owned: the
    contained PROT_NONE MAP_FIXED. *)
Lemma na_inv_add_owned : forall maps na brk a n,
  (bv_unsigned a mod page_size = 0)%Z -> (bv_unsigned n mod page_size = 0)%Z ->
  (0 < bv_unsigned n)%Z -> (bv_unsigned a + bv_unsigned n <= two_pow_64)%Z ->
  (forall x, (bv_unsigned a <= x < bv_unsigned a + bv_unsigned n)%Z -> owned maps x) ->
  na_inv' maps na brk -> na_inv' maps ((a, n) :: na) brk.
Proof.
  intros maps na brk a n Ha Hn Hpos Hf Hown [Hsh Hcov]. split.
  - intros b s [Heq|Hin].
    + injection Heq as <- <-. repeat split; assumption.
    + exact (Hsh b s Hin).
  - intros b s x [Heq|Hin] Hx.
    + injection Heq as <- <-. exact (Hown x Hx).
    + exact (Hcov b s x Hin Hx).
Qed.

(** [mremap] cuts its source range out of the ledger and records one
    entry; no protected byte meets the source. *)
Lemma na_inv_mremap : forall maps na brk old old_n d k,
  maps_fit maps ->
  (bv_unsigned old mod page_size = 0)%Z -> (bv_unsigned old_n mod page_size = 0)%Z ->
  region_free na old old_n = true ->
  na_inv' maps na brk ->
  na_inv' ((d, k) :: maps_subtract maps (bv_unsigned old)
                       (bv_unsigned old + bv_unsigned old_n)) na brk.
Proof.
  intros maps na brk old old_n d k Hmf Ha Hn Hfree [Hsh Hcov].
  assert (Hhi : ((bv_unsigned old + bv_unsigned old_n) mod page_size = 0)%Z)
    by (apply aligned_add; assumption).
  split; [exact Hsh|].
  intros a n x Hin Hx.
  assert (Hxs : ~ (bv_unsigned old <= x < bv_unsigned old + bv_unsigned old_n)%Z).
  { intro Hxs. pose proof (region_free_In _ _ _ a n Hfree Hin) as Hno.
    unfold iv_overlap in Hno.
    apply andb_false_iff in Hno as [Hc|Hc]; apply Z.ltb_ge in Hc; lia. }
  apply owned_cons.
  exact (owned_subtract maps _ _ x Hmf (Hcov a n x Hin Hx) Hxs).
Qed.

(* -------------------------------------------------------------------------
   brk
   ------------------------------------------------------------------------- *)

(** What a resolution other than "unchanged" says about the request. *)
Lemma brk_r_ok_cases : forall m req r,
  brk_r_ok m req r = true ->
  r = vm_brk (m_vmmaps m) \/ (r = req /\ w_is0 req = false).
Proof.
  intros m req r H. unfold brk_r_ok in H. cbv zeta in H.
  destruct (w_is0 req || (bv_unsigned req <? bv_unsigned (min_brk (m_vmmaps m)))%Z)
    eqn:E1.
  - left. apply bv_eqb_eq in H. exact H.
  - apply orb_false_iff in E1 as [E1 _].
    destruct (bv_unsigned req <? bv_unsigned (vm_brk (m_vmmaps m)))%Z.
    + apply orb_true_iff in H as [H|H]; apply bv_eqb_eq in H;
        [right; split; assumption | left; exact H].
    + apply andb_true_iff in H as [H _].
      apply orb_true_iff in H as [H|H]; apply bv_eqb_eq in H;
        [right; split; assumption | left; exact H].
Qed.

(** The shrink, one protected byte at a time, and it is now one lemma
    rather than three.  The shrink's ONLY cut of [vm_maps] is the range
    [Mmap.brk_unmap_cut] takes, inside [[PAGE_ALIGN r, PAGE_ALIGN b)];
    the protected list loses exactly that range too, so a protected byte
    that survives is outside it and keeps the owner it had.  A same-page
    shrink is the degenerate case: both ranges are empty and nothing is
    cut at all. *)
Lemma brk_shrink_cover_cut : forall maps na b r a n x lo hi,
  maps_fit maps -> na_cover maps na b ->
  In (a, n) na -> (bv_unsigned a <= x < bv_unsigned a + bv_unsigned n)%Z ->
  ~ (page_round_up_Z r <= x < page_round_up_Z b)%Z ->
  (page_round_up_Z r <= lo)%Z -> (hi <= page_round_up_Z b)%Z ->
  owned (maps_subtract maps lo hi) x.
Proof.
  intros maps na b r a n x lo hi Hmf Hcov Hin Hx Hcut Hlo Hhi.
  apply owned_subtract; [exact Hmf | exact (Hcov a n x Hin Hx) | lia].
Qed.

Lemma brk_model_next_na_inv : forall m req r,
  brk_r_ok m req r = true ->
  vm_fit (m_vmmaps m) -> na_inv (m_vmmaps m) ->
  na_inv (brk_model_next (m_vmmaps m) req r).
Proof.
  intros m req r Hok Hfit Hna.
  pose proof (brk_r_ok_cases m req r Hok) as Hr.
  set (h := m_vmmaps m) in *.
  destruct Hna as [Hsh Hcov].
  unfold na_inv, brk_model_next, brk_maps_next, brk_unmap_cut, brk_unmaps,
    brk_grants, brk_is_grow.
  cbv zeta. cbn [vm_maps vm_noaccess vm_brk].
  pose proof (word_range r) as Hrr. pose proof (word_range (vm_brk h)) as Hbr.
  set (b := vm_brk h) in *.
  destruct (Z.lt_total (bv_unsigned r) (bv_unsigned b)) as [Hlt|[Heq|Hgt]].
  - (* SHRINK *)
    destruct Hr as [Hr|[-> Hreq]]; [subst r; lia|].
    pose proof (w_is0_false req Hreq) as Hreq0.
    assert (Hb0 : (0 < bv_unsigned b)%Z) by lia.
    rewrite (proj2 (Z.ltb_lt 0 (bv_unsigned b)) Hb0).
    rewrite (proj2 (Z.ltb_lt (bv_unsigned req) (bv_unsigned b)) Hlt).
    cbn [andb].
    pose proof (page_round_up_Z_pos (bv_unsigned req) ltac:(lia)) as Hpur.
    assert (Hpub : (page_round_up_Z (bv_unsigned b) <= 2 ^ 64)%Z).
    { unfold page_round_up_Z, page_size. pgf (bv_unsigned b + 4096 - 1). lia. }
    unfold brk_page_range.
    destruct (page_round_up_Z (bv_unsigned req)
              <? page_round_up_Z (bv_unsigned b))%Z eqn:Ecut.
    + apply Z.ltb_lt in Ecut.
      unfold maps_subtract_ranges. cbn [fold_left fst snd].
      unfold page_size in Hpur.
      rewrite !u64 by lia.
      replace (page_round_up_Z (bv_unsigned req)
               + (page_round_up_Z (bv_unsigned b) - page_round_up_Z (bv_unsigned req)))%Z
        with (page_round_up_Z (bv_unsigned b)) by lia.
      split.
      * apply maps_subtract_shape; [exact Hsh | apply pu_aligned | apply pu_aligned].
      * intros a' n' x Hin Hx.
        destruct (maps_subtract_bytes _ _ _ a' n' x (na_shape_fit _ Hsh) Hin Hx)
          as (a & n & Hin0 & Hx0 & Hc).
        apply (brk_shrink_cover_cut _ _ _ _ a n x _ _ Hfit Hcov Hin0 Hx0 Hc);
          lia.
    + apply Z.ltb_ge in Ecut.
      unfold maps_subtract_ranges. cbn [fold_left].
      split; [exact Hsh|].
      intros a n x Hin Hx.
      exact (Hcov a n x Hin Hx).
  - (* UNCHANGED *)
    assert (Erb : r = b) by (apply bv_eq; exact Heq). subst r.
    rewrite Z.ltb_irrefl, !andb_false_r. cbn [app].
    destruct (0 <? bv_unsigned b)%Z;
      unfold brk_page_range; rewrite ?Z.ltb_irrefl;
      unfold maps_subtract_ranges; cbn [fold_left]; split; assumption.
  - (* GROW *)
    destruct Hr as [Hr|[-> Hreq]]; [subst r; lia|].
    rewrite Hreq. cbn [negb andb].
    rewrite (proj2 (Z.ltb_ge (bv_unsigned req) (bv_unsigned b)) ltac:(lia)),
      andb_false_r.
    rewrite (proj2 (Z.ltb_lt (bv_unsigned b) (bv_unsigned req)) Hgt), andb_true_r.
    assert (Hpu : (page_round_up_Z (bv_unsigned b)
                   <= page_round_up_Z (bv_unsigned req))%Z).
    { unfold page_round_up_Z, page_size.
      pgf (bv_unsigned b + 4096 - 1). pgf (bv_unsigned req + 4096 - 1). lia. }
    assert (Hna' : maps_subtract_ranges (vm_noaccess h)
                     (if (0 <? bv_unsigned b)%Z
                      then brk_page_range (page_round_up_Z (bv_unsigned req))
                             (page_round_up_Z (bv_unsigned b))
                      else []) = vm_noaccess h).
    { destruct (0 <? bv_unsigned b)%Z; [|reflexivity].
      unfold brk_page_range.
      rewrite (proj2 (Z.ltb_ge _ _) Hpu). reflexivity. }
    rewrite Hna'.
    destruct (0 <? bv_unsigned b)%Z eqn:Eb.
    + apply Z.ltb_lt in Eb.
      split; [exact Hsh|].
      intros a n x Hin Hx.
      unfold brk_page_range.
      destruct (Z.ltb (page_round_up_Z (bv_unsigned b))
                      (page_round_up_Z (bv_unsigned req)));
        cbn [app]; [apply owned_cons | idtac]; exact (Hcov a n x Hin Hx).
    + apply Z.ltb_ge in Eb. cbn [app].
      split; [exact Hsh|].
      intros a n x Hin Hx. exact (Hcov a n x Hin Hx).
Qed.

(** The invariant gives the page-ownership statement. *)
Theorem na_inv_noaccess_pages_owned : forall h,
  na_inv h -> noaccess_pages_owned h.
Proof.
  intros h [Hsh Hcov] a n Hin.
  destruct (Hsh a n Hin) as (_ & _ & Hpos & _).
  split; [exact Hpos|].
  intros x Hx.
  destruct (Hcov a n x Hin Hx) as (b & s & Hb & Hbx).
  exists b, s. split; [exact Hb|].
  unfold page_round_down_Z, page_size. pgf x. lia.
Qed.

(* -------------------------------------------------------------------------
   The five writers of the two lists, walked as [VmMapsDisjoint] walks
   them for [vm_wf]; each leaf is one of the shapes above.
   ------------------------------------------------------------------------- *)

Lemma check_brk_preserves_na : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs ->
  vm_wf (m_vmmaps m) -> vm_fit (m_vmmaps m) ->
  na_inv (m_vmmaps m) -> na_inv (m_vmmaps m').
Proof.
  intros req [ret ws zs us cs ci] m m' evs H Hwf Hfit Hna.
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
  rewrite vmm_brk_next. now apply brk_model_next_na_inv.
Qed.

Lemma check_munmap_preserves_na : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs ->
  vm_wf (m_vmmaps m) -> vm_fit (m_vmmaps m) ->
  na_inv (m_vmmaps m) -> na_inv (m_vmmaps m').
Proof.
  intros addr len [ret ws zs us cs ci] m m' evs H Hwf Hfit Hna.
  unfold check_munmap in H. cbv zeta in H.
  difn H Eargs; [apply check_ret_only_model in H; subst m'; exact Hna|].
  difn H Etask; [apply check_ret_only_model in H; subst m'; exact Hna|].
  difn H Ehas.
  - destruct ws, zs, cs, ci; try discriminate.
    dif H.
    + destruct us; [|discriminate]. injection H as <- <-. exact Hna.
    + dif H; [|discriminate]. injection H as <- <-.
      apply orb_false_iff in Eargs as [Ealign Elen].
      apply negb_false_iff, Z.eqb_eq in Ealign.
      apply Z.ltb_ge in Etask. unfold TASK_SIZE in Etask.
      pose proof (word_range addr) as Har. pose proof (word_range len) as Hlr.
      pose proof (page_round_up_Z_ge (bv_unsigned len) ltac:(lia)) as HnZ.
      unfold na_inv. rewrite vmm_mmap_destroyed. unfold mmap_fixed_destroyed_next.
      cbn [vm_maps vm_noaccess vm_brk].
      apply na_inv_cut_both; [exact Hfit | exact Ealign | | exact Hna].
      rewrite u64 by lia. apply aligned_add; [exact Ealign | apply pu_aligned].
  - dif H; [apply check_ret_only_model in H; subst m'; exact Hna|].
    dif H; [|discriminate].
    destruct ws, zs, cs, ci; try discriminate.
    dif H.
    + destruct us; [|discriminate]. injection H as <- <-. exact Hna.
    + dif H; [|discriminate]. injection H as <- <-.
      apply orb_false_iff in Eargs as [Ealign Elen].
      apply negb_false_iff, Z.eqb_eq in Ealign.
      apply Z.ltb_ge in Etask. unfold TASK_SIZE in Etask.
      pose proof (word_range addr) as Har. pose proof (word_range len) as Hlr.
      pose proof (page_round_up_Z_ge (bv_unsigned len) ltac:(lia)) as HnZ.
      unfold na_inv. rewrite vmm_mmap_destroyed. unfold mmap_fixed_destroyed_next.
      cbn [vm_maps vm_noaccess vm_brk].
      apply na_inv_cut_both; [exact Hfit | exact Ealign | | exact Hna].
      rewrite u64 by lia. apply aligned_add; [exact Ealign | apply pu_aligned].
Qed.

Lemma check_mprotect_preserves_na : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs ->
  vm_wf (m_vmmaps m) -> vm_fit (m_vmmaps m) ->
  na_inv (m_vmmaps m) -> na_inv (m_vmmaps m').
Proof.
  intros addr len prot [ret ws zs us cs ci] m m' evs H Hwf Hfit Hna.
  unfold check_mprotect in H. cbv zeta in H.
  dif H; [apply check_ret_only_model in H; subst m'; exact Hna|].
  difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hna|].
  difn H Elen; [apply check_ret_only_model in H; subst m'; exact Hna|].
  difn H Ebig; [apply check_ret_only_model in H; subst m'; exact Hna|].
  dif H; [discriminate|].
  dif H.
  - destruct ws, us, cs, ci; try discriminate.
    dif H.
    + destruct zs; [|discriminate]. injection H as <- <-. exact Hna.
    + dif H; [|discriminate]. injection H as <- <-.
      apply negb_false_iff, Z.eqb_eq in Ealign.
      apply Z.leb_gt in Ebig. unfold two_pow_64 in Ebig.
      pose proof (word_range addr) as Har. pose proof (word_range len) as Hlr.
      pose proof (w_is0_false len Elen) as Hlen0.
      assert (HnZ : (0 < page_round_up_Z (bv_unsigned len))%Z)
        by (apply page_round_up_pos; lia).
      unfold na_inv. rewrite vmm_mprotect_next. cbn [vm_maps vm_noaccess vm_brk].
      apply na_inv_cut_na; [exact Ealign | | exact Hna].
      rewrite u64 by lia. apply aligned_add; [exact Ealign | apply pu_aligned].
  - dif H; [|discriminate].
    destruct ws, zs, us, cs, ci; try discriminate.
    dif H; [|discriminate]. injection H as <- <-. exact Hna.
Qed.

Lemma check_mmap_preserves_na : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs ->
  vm_wf (m_vmmaps m) -> vm_fit (m_vmmaps m) ->
  na_inv (m_vmmaps m) -> na_inv (m_vmmaps m').
Proof.
  intros addr len prot flags fd off [ret ws zs us cs ci] m m' evs H Hwf Hfit Hna.
  unfold check_mmap in H. cbv zeta in H.
  pose proof (alloc_top_lt (m_vmmaps m)) as Hac. unfold two_pow_64 in Hac.
  pose proof (word_range len) as Hlenr.
  pose proof (word_range addr) as Haddrr.
  pose proof (word_range ret) as Hretr.
  destruct (negb (mmap_off_aligned_b off)) eqn:Eoff.
  { apply check_ret_only_model in H; subst m'; exact Hna. }
  destruct (negb (mmap_anon_b flags)) eqn:Eanon.
  { destruct (fd_lookup (m_fds m) (fd32 fd)); [discriminate|].
    apply check_ret_only_model in H; subst m'; exact Hna. }
  destruct (w_is0 len) eqn:Elen.
  { destruct (mmap_plain_anon_b flags); [|discriminate].
    apply check_ret_only_model in H; subst m'; exact Hna. }
  pose proof (w_is0_false len Elen) as Hlen0.
  assert (HnZ : (0 < page_round_up_Z (bv_unsigned len))%Z)
    by (apply page_round_up_pos; lia).
  pose proof (pu_aligned (bv_unsigned len)) as Hnal.
  destruct (mmap_modeled_b prot flags off) eqn:Emod.
  { destruct ws, us, cs, ci; try discriminate.
    destruct (errno_ret_in mmap_errnos ret).
    { destruct zs; [|discriminate]. injection H as <- <-. exact Hna. }
    difn H E; [|discriminate]. injection H as <- <-.
    unfold na_inv. rewrite vmm_mmap_backing, vmm_vmmaps.
    cbn [vm_maps vm_noaccess vm_brk].
    apply na_inv_cons_maps. exact Hna. }
  destruct (mmap_noaccess_b prot flags off) eqn:Enoa.
  { destruct ws, zs, cs, ci; try discriminate.
    destruct (errno_ret_in mmap_errnos ret).
    { destruct us; [|discriminate]. injection H as <- <-. exact Hna. }
    difn H E; [|discriminate]. injection H as <- <-.
    unfold na_inv. rewrite vmm_mmap_backing, vmm_vmmaps.
    cbn [vm_maps vm_noaccess vm_brk].
    apply andb_true_iff in E as [Hplace Hus].
    destruct (Placement.linux_place_is_admissible _ _ _ _ _ HnZ Hnal Hplace)
      as (Halign & Hpos & Hceil & Hfree).
    apply na_inv_cons_both;
      [exact Halign | rewrite u64 by lia; exact Hnal | rewrite u64 by lia; exact HnZ
      | rewrite u64 by lia; unfold two_pow_64; lia | exact Hna]. }
  destruct (mmap_fixed_noaccess_b prot flags off) eqn:Efix.
  { difn H Enomem; [apply check_ret_only_model in H; subst m'; exact Hna|].
    difn H Eceil; [discriminate|].
    difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hna|].
    difn H Epos; [discriminate|].
    apply negb_false_iff, Z.leb_le in Eceil.
    apply negb_false_iff, Z.eqb_eq in Ealign.
    assert (Hn64 : bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
                   = page_round_up_Z (bv_unsigned len)) by (rewrite u64 by lia; reflexivity).
    assert (Hhial : ((bv_unsigned addr
                      + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
                     mod page_size = 0)%Z)
      by (rewrite Hn64; apply aligned_add; assumption).
    difn H Elive.
    - destruct ws, zs, cs, ci; try discriminate.
      destruct (errno_ret_in mmap_errnos ret).
      + destruct us.
        * injection H as <- <-. exact Hna.
        * difn H Eus; [|discriminate]. injection H as <- <-.
          unfold na_inv. rewrite vmm_mmap_destroyed. unfold mmap_fixed_destroyed_next.
          cbn [vm_maps vm_noaccess vm_brk].
          apply na_inv_cut_both; [exact Hfit | exact Ealign | exact Hhial | exact Hna].
      + difn H Eok; [|discriminate]. injection H as <- <-.
        unfold na_inv. rewrite vmm_mmap_replacement, vmm_vmmaps.
        cbn [vm_maps vm_noaccess vm_brk].
        apply andb_true_iff in Elive as [_ Hcont].
        apply na_inv_add_owned;
          [exact Ealign | rewrite Hn64; exact Hnal | rewrite Hn64; exact HnZ
          | rewrite Hn64; unfold two_pow_64; lia
          | intros x Hx; exact (map_contains_owned _ _ _ x Hcont Hx) | ].
        apply na_inv_cut_na; [exact Ealign | exact Hhial | exact Hna].
    - difn H Efree.
      + destruct ws, zs, cs, ci; try discriminate.
        destruct (errno_ret_in mmap_errnos ret).
        * destruct us; [|discriminate]. injection H as <- <-. exact Hna.
        * difn H Eok; [|discriminate]. injection H as <- <-.
          unfold na_inv. rewrite vmm_mmap_backing, vmm_vmmaps.
          cbn [vm_maps vm_noaccess vm_brk].
          apply na_inv_cons_both;
            [exact Ealign | rewrite Hn64; exact Hnal | rewrite Hn64; exact HnZ
            | rewrite Hn64; unfold two_pow_64; lia | exact Hna].
      + difn H Espan; [|discriminate].
        destruct ws, zs, cs, ci; try discriminate.
        destruct (errno_ret_in mmap_errnos ret).
        * destruct us.
          -- injection H as <- <-. exact Hna.
          -- difn H Eus; [|discriminate]. injection H as <- <-.
             unfold na_inv. rewrite vmm_mmap_destroyed.
             unfold mmap_fixed_destroyed_next. cbn [vm_maps vm_noaccess vm_brk].
             apply na_inv_cut_both; [exact Hfit | exact Ealign | exact Hhial | exact Hna].
        * difn H Eok; [|discriminate]. injection H as <- <-.
          unfold na_inv. rewrite vmm_mmap_replacement, vmm_vmmaps.
          unfold mmap_fixed_noaccess_span_next. cbn [vm_maps vm_noaccess vm_brk].
          apply na_inv_cons_both;
            [exact Ealign | rewrite Hn64; exact Hnal | rewrite Hn64; exact HnZ
            | rewrite Hn64; unfold two_pow_64; lia | ].
          apply na_inv_cut_both; [exact Hfit | exact Ealign | exact Hhial | exact Hna]. }
  destruct (mmap_fixed_rw_b prot flags off) eqn:Efixrw.
  2: {
    destruct (mmap_noreplace_noaccess_b prot flags off) eqn:Enrn.
    { difn H Enomem; [apply check_ret_only_model in H; subst m'; exact Hna|].
      difn H Eceil; [discriminate|].
      difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hna|].
      difn H Epos; [discriminate|].
      apply negb_false_iff, Z.leb_le in Eceil.
      apply negb_false_iff, Z.eqb_eq in Ealign.
      difn H Efree.
      - destruct ws, zs, cs, ci; try discriminate.
        destruct (errno_ret_in mmap_errnos ret).
        + destruct us; [|discriminate]. injection H as <- <-. exact Hna.
        + difn H Eok; [|discriminate]. injection H as <- <-.
          unfold na_inv. rewrite vmm_mmap_backing, vmm_vmmaps.
          cbn [vm_maps vm_noaccess vm_brk].
          apply na_inv_cons_both;
            [exact Ealign | rewrite u64 by lia; exact Hnal
            | rewrite u64 by lia; exact HnZ
            | rewrite u64 by lia; unfold two_pow_64; lia | exact Hna].
      - destruct ws, zs, us, cs, ci; try discriminate.
        difn H Eerr; [|discriminate]. injection H as <- <-. exact Hna. }
    destruct (mmap_noreplace_rw_b prot flags off) eqn:Enrr; [|discriminate].
    difn H Enomem; [apply check_ret_only_model in H; subst m'; exact Hna|].
    difn H Eceil; [discriminate|].
    difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hna|].
    difn H Epos; [discriminate|].
    difn H Efree.
    - destruct ws, us, cs, ci; try discriminate.
      destruct (errno_ret_in mmap_errnos ret).
      + destruct zs; [|discriminate]. injection H as <- <-. exact Hna.
      + difn H Eok; [|discriminate]. injection H as <- <-.
        unfold na_inv. rewrite vmm_mmap_backing, vmm_vmmaps.
        cbn [vm_maps vm_noaccess vm_brk].
        apply na_inv_cons_maps. exact Hna.
    - destruct ws, zs, us, cs, ci; try discriminate.
      difn H Eerr; [|discriminate]. injection H as <- <-. exact Hna. }
  difn H Enomem; [apply check_ret_only_model in H; subst m'; exact Hna|].
  difn H Eceil; [discriminate|].
  difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hna|].
  difn H Epos; [discriminate|].
  apply negb_false_iff, Z.leb_le in Eceil.
  apply negb_false_iff, Z.eqb_eq in Ealign.
  assert (Hn64 : bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
                 = page_round_up_Z (bv_unsigned len)) by (rewrite u64 by lia; reflexivity).
  assert (Hhial : ((bv_unsigned addr
                    + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
                   mod page_size = 0)%Z)
    by (rewrite Hn64; apply aligned_add; assumption).
  difn H Elive.
  - destruct ws, cs, ci; try discriminate.
    destruct (errno_ret_in mmap_errnos ret).
    + destruct zs; [|discriminate]. destruct us.
      * injection H as <- <-. exact Hna.
      * difn H Eus; [|discriminate]. injection H as <- <-.
        unfold na_inv. rewrite vmm_mmap_destroyed. unfold mmap_fixed_destroyed_next.
        cbn [vm_maps vm_noaccess vm_brk].
        apply na_inv_cut_both; [exact Hfit | exact Ealign | exact Hhial | exact Hna].
    + destruct us; [|discriminate].
      difn H Eok; [|discriminate]. injection H as <- <-.
      unfold na_inv. rewrite vmm_mmap_replacement, vmm_vmmaps.
      unfold mmap_fixed_rw_next. cbn [vm_maps vm_noaccess vm_brk].
      apply na_inv_cut_na; [exact Ealign | exact Hhial | exact Hna].
  - difn H Efree.
    + destruct ws, us, cs, ci; try discriminate.
      destruct (errno_ret_in mmap_errnos ret).
      * destruct zs; [|discriminate]. injection H as <- <-. exact Hna.
      * difn H Eok; [|discriminate]. injection H as <- <-.
        unfold na_inv. rewrite vmm_mmap_backing, vmm_vmmaps.
        cbn [vm_maps vm_noaccess vm_brk].
        apply na_inv_cons_maps. exact Hna.
    + difn H Espan; [|discriminate].
      destruct ws, cs, ci; try discriminate.
      destruct (errno_ret_in mmap_errnos ret).
      * destruct zs; [|discriminate]. destruct us.
        -- injection H as <- <-. exact Hna.
        -- difn H Eus; [|discriminate]. injection H as <- <-.
           unfold na_inv. rewrite vmm_mmap_destroyed.
           unfold mmap_fixed_destroyed_next. cbn [vm_maps vm_noaccess vm_brk].
           apply na_inv_cut_both; [exact Hfit | exact Ealign | exact Hhial | exact Hna].
      * destruct us; [|discriminate].
        difn H Eok; [|discriminate]. injection H as <- <-.
        unfold na_inv. rewrite vmm_mmap_replacement, vmm_vmmaps.
        unfold mmap_fixed_rw_span_next. cbn [vm_maps vm_noaccess vm_brk].
        apply na_inv_cons_maps.
        apply na_inv_cut_both; [exact Hfit | exact Ealign | exact Hhial | exact Hna].
Qed.

Lemma check_mremap_preserves_na :
  forall old old_size new_size flags eff m m' evs,
  check_mremap old old_size new_size flags eff m = CheckOk m' evs ->
  vm_wf (m_vmmaps m) -> vm_fit (m_vmmaps m) ->
  na_inv (m_vmmaps m) -> na_inv (m_vmmaps m').
Proof.
  intros old old_size new_size flags [ret ws zs us cs ci] m m' evs H Hwf Hfit Hna.
  unfold check_mremap in H. cbv zeta in H.
  pose proof (alloc_top_lt (m_vmmaps m)) as Hac. unfold two_pow_64 in Hac.
  pose proof (word_range old) as Hor.
  pose proof (word_range old_size) as Hos.
  difn H Eflag; [discriminate|].
  difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hna|].
  difn H Enew; [apply check_ret_only_model in H; subst m'; exact Hna|].
  difn H Etask; [apply check_ret_only_model in H; subst m'; exact Hna|].
  difn H Eold; [discriminate|].
  difn H Esrc; [discriminate|].
  difn H Eeq; [apply check_ret_only_model in H; subst m'; exact Hna|].
  destruct ws; [|discriminate]. destruct ci; [|discriminate].
  apply negb_false_iff, Z.eqb_eq in Ealign.
  apply negb_false_iff in Esrc.
  apply andb_true_iff in Esrc as [Esrc _].
  unfold mremap_source_b in Esrc.
  apply andb_true_iff in Esrc as [Esrc Hsna].
  apply andb_true_iff in Esrc as [Esrc Hhas].
  apply andb_true_iff in Esrc as [Hoceil _].
  apply Z.leb_le in Hoceil.
  assert (HoldZ : (0 <= page_round_up_Z (bv_unsigned old_size))%Z)
    by (apply page_round_up_Z_nonneg; lia).
  assert (Hoal : (bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
                  mod page_size = 0)%Z)
    by (rewrite u64 by lia; apply pu_aligned).
  destruct (errno_ret_in mremap_errnos ret).
  { destruct zs, us, cs; try discriminate. injection H as <- <-. exact Hna. }
  destruct (bv_eqb ret old).
  - difn H Eshrink.
    + difn H Eok; [|discriminate]. injection H as <- <-.
      unfold na_inv. rewrite vmm_mremap_next.
      unfold mremap_maps_next. cbn [vm_maps vm_noaccess vm_brk].
      exact (na_inv_mremap _ _ _ _ _ _ _ Hfit Ealign Hoal Hsna Hna).
    + difn H Egrow; [|discriminate].
      difn H Eok; [|discriminate]. injection H as <- <-.
      unfold na_inv. rewrite vmm_mremap_next.
      unfold mremap_maps_next. cbn [vm_maps vm_noaccess vm_brk].
      exact (na_inv_mremap _ _ _ _ _ _ _ Hfit Ealign Hoal Hsna Hna).
  - difn H Emove; [|discriminate]. injection H as <- <-.
    unfold na_inv. rewrite vmm_mremap_next.
    unfold mremap_maps_next. cbn [vm_maps vm_noaccess vm_brk].
    exact (na_inv_mremap _ _ _ _ _ _ _ Hfit Ealign Hoal Hsna Hna).
Qed.

(* -------------------------------------------------------------------------
   The invariant, over the whole dispatcher
   ------------------------------------------------------------------------- *)

(** [execve] establishes it: both lists start empty. *)
Lemma init_model_na_inv : forall reserved brk0 mbase sp lim inp,
  na_inv (m_vmmaps (init_model reserved brk0 mbase sp lim inp)).
Proof.
  intros reserved brk0 mbase sp lim inp.
  assert (Hn : vm_noaccess (m_vmmaps (init_model reserved brk0 mbase sp lim inp)) = [])
    by reflexivity.
  unfold na_inv. rewrite Hn. split; [intros a n [] | intros a n x []].
Qed.

Lemma init_model_sys_inv : forall reserved brk0 mbase sp lim inp,
  sys_inv (m_vmmaps (init_model reserved brk0 mbase sp lim inp)).
Proof.
  intros reserved brk0 mbase sp lim inp.
  split; [apply init_model_vm_wf|].
  split; [apply init_model_vm_fit | apply init_model_na_inv].
Qed.

Definition arm_preserves_na (c : CheckedArm) : Prop :=
  forall i eff m m' evs,
    ca_check c i eff m = CheckOk m' evs ->
    vm_wf (m_vmmaps m) -> vm_fit (m_vmmaps m) ->
    na_inv (m_vmmaps m) -> na_inv (m_vmmaps m').

(** The enumeration is [VmMapsDisjoint.checked_table_preserves_vm]'s,
    arm for arm. *)
Lemma checked_table_preserves_na : Forall arm_preserves_na checked_table.
Proof.
  unfold checked_table.
  repeat apply Forall_cons.
  all: try exact (Forall_nil arm_preserves_na).
  all: unfold arm_preserves_na; intros i eff m m' evs H Hwf Hfit Hna;
       autorewrite with arm_unfold in H.
  all: first
    [ eapply check_brk_preserves_na; eassumption
    | eapply check_mmap_preserves_na; eassumption
    | eapply check_munmap_preserves_na; eassumption
    | eapply check_mremap_preserves_na; eassumption
    | eapply check_mprotect_preserves_na; eassumption
    | erewrite check_madvise_frame by eassumption; exact Hna
    | erewrite check_read_frame by eassumption; exact Hna
    | erewrite check_write_frame by eassumption; exact Hna
    | erewrite check_pread64_frame by eassumption; exact Hna
    | erewrite check_pwrite64_frame by eassumption; exact Hna
    | erewrite check_readv_frame by eassumption; exact Hna
    | erewrite check_writev_frame by eassumption; exact Hna
    | erewrite check_pwritev2_frame by eassumption; exact Hna
    | erewrite check_openat_frame by eassumption; exact Hna
    | erewrite check_close_frame by eassumption; exact Hna
    | erewrite check_lseek_frame by eassumption; exact Hna
    | erewrite check_ftruncate_frame by eassumption; exact Hna
    | erewrite check_ioctl_frame by eassumption; exact Hna
    | erewrite check_readlinkat_frame by eassumption; exact Hna
    | erewrite check_wait4_frame by eassumption; exact Hna
    | erewrite check_fsync_frame by eassumption; exact Hna
    | erewrite check_getdents64_frame by eassumption; exact Hna
    | erewrite check_flock_frame by eassumption; exact Hna
    | erewrite check_exit_frame by eassumption; exact Hna
    | erewrite check_set_tid_address_frame by eassumption; exact Hna
    | erewrite check_getpid_frame by eassumption; exact Hna
    | erewrite check_gettid_frame by eassumption; exact Hna
    | erewrite check_setsid_frame by eassumption; exact Hna
    | erewrite check_uname_frame by eassumption; exact Hna
    | erewrite check_prctl_frame by eassumption; exact Hna
    | erewrite check_prlimit64_frame by eassumption; exact Hna
    | erewrite check_getrandom_frame by eassumption; exact Hna
    | erewrite check_gettimeofday_frame by eassumption; exact Hna
    | erewrite check_clock_gettime_frame by eassumption; exact Hna
    | erewrite check_clock_getres_frame by eassumption; exact Hna
    | erewrite check_nanosleep_frame by eassumption; exact Hna
    | erewrite check_dup_frame by eassumption; exact Hna
    | erewrite check_dup3_frame by eassumption; exact Hna
    | erewrite check_unlinkat_frame by eassumption; exact Hna
    | erewrite check_faccessat_frame by eassumption; exact Hna
    | erewrite check_faccessat2_frame by eassumption; exact Hna
    | erewrite check_pselect6_frame by eassumption; exact Hna
    | erewrite check_ppoll_frame by eassumption; exact Hna
    | erewrite check_newfstatat_frame by eassumption; exact Hna
    | erewrite check_fstat_frame by eassumption; exact Hna
    | erewrite check_getid_frame by eassumption; exact Hna
    | erewrite check_setid_frame by eassumption; exact Hna
    | erewrite check_setresid_frame by eassumption; exact Hna
    | erewrite check_getgroups_frame by eassumption; exact Hna
    | erewrite check_setgroups_frame by eassumption; exact Hna
    | erewrite check_socket_frame by eassumption; exact Hna
    | erewrite check_bind_frame by eassumption; exact Hna
    | erewrite check_listen_frame by eassumption; exact Hna
    | erewrite check_accept4_frame by eassumption; exact Hna
    | erewrite check_fcntl_frame by eassumption; exact Hna
    | erewrite check_sched_setscheduler_frame by eassumption; exact Hna
    | erewrite check_sched_getaffinity_frame by eassumption; exact Hna
    | erewrite check_sched_yield_frame by eassumption; exact Hna
    | erewrite check_sigaltstack_frame by eassumption; exact Hna
    | erewrite check_rt_sigaction_frame by eassumption; exact Hna
    | erewrite check_tkill_frame by eassumption; exact Hna
    | erewrite check_tgkill_frame by eassumption; exact Hna
    | erewrite check_rt_sigprocmask_frame by eassumption; exact Hna
    | erewrite check_futex_frame by eassumption; exact Hna
    | erewrite check_set_robust_list_frame by eassumption; exact Hna
    | erewrite check_clone_frame by eassumption; exact Hna
    | erewrite check_clone3_frame by eassumption; exact Hna
    | erewrite check_getsockname_frame by eassumption; exact Hna
    | erewrite check_getpeername_frame by eassumption; exact Hna
    | erewrite check_setsockopt_frame by eassumption; exact Hna
    | erewrite check_getsockopt_frame by eassumption; exact Hna
    | erewrite check_shutdown_frame by eassumption; exact Hna
    | erewrite check_sendto_frame by eassumption; exact Hna
    | erewrite check_sendmsg_frame by eassumption; exact Hna
    | erewrite check_socketpair_frame by eassumption; exact Hna
    | erewrite check_recvfrom_frame by eassumption; exact Hna
    | erewrite check_recvmsg_frame by eassumption; exact Hna
    | erewrite check_connect_frame by eassumption; exact Hna
    | erewrite check_timerfd_create_frame by eassumption; exact Hna
    | erewrite check_eventfd2_frame by eassumption; exact Hna
    | erewrite check_pipe2_frame by eassumption; exact Hna
    | erewrite check_getcwd_frame by eassumption; exact Hna
    | erewrite check_epoll_create1_frame by eassumption; exact Hna
    | erewrite check_epoll_ctl_frame by eassumption; exact Hna
    | erewrite check_epoll_pwait_frame by eassumption; exact Hna
    | fail 1 "checked_table_preserves_na has no case for this dispatcher arm: give the new checker a *_frame lemma (it leaves m_vmmaps alone) or a *_preserves_na one (it writes vm_maps or vm_noaccess), and add it to the list above" ].
Qed.

Theorem check_syscall_preserves_sys_inv : forall i eff m m' evs,
  check_syscall i eff m = CheckOk m' evs ->
  sys_inv (m_vmmaps m) -> sys_inv (m_vmmaps m').
Proof.
  intros i eff m m' evs H (Hwf & Hfit & Hna).
  split; [exact (check_syscall_preserves_vm_wf i eff m m' evs H Hwf)|].
  split; [exact (check_syscall_preserves_vm_fit i eff m m' evs H Hfit)|].
  unfold check_syscall in H.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk;
    [|discriminate H].
  pose proof checked_table_preserves_na as Hall.
  rewrite Forall_forall in Hall.
  exact (Hall c (lookup_ca_In _ _ _ Elk) i eff m m' evs H Hwf Hfit Hna).
Qed.

(** The same statement against the RELATIONAL spec. *)
Corollary syscall_spec_preserves_sys_inv : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  sys_inv (m_vmmaps m) -> sys_inv (m_vmmaps m').
Proof.
  intros i m eff m' evs H Hinv.
  eapply check_syscall_preserves_sys_inv; [|exact Hinv].
  apply check_syscall_ok_iff. exact H.
Qed.

(** What a consumer cites: [sys_inv] gives [State.noaccess_pages_owned]. *)
Corollary sys_inv_noaccess_pages_owned : forall h,
  sys_inv h -> noaccess_pages_owned h.
Proof. intros h (_ & _ & Hna). exact (na_inv_noaccess_pages_owned h Hna). Qed.

(* -------------------------------------------------------------------------
   On every reachable configuration
   ------------------------------------------------------------------------- *)

(** One transition keeps [sys_inv]: an instruction step leaves the ledger
    alone ([Run.mi_account_step_model_frame]); a system call moves it as
    its spec says ([syscall_spec_preserves_sys_inv]) and the
    materialization that follows leaves it alone
    ([State.materialize_model_accesses_frame]); an exit or a kill keeps
    the spec's own post-model. *)
Lemma sstep_preserves_sys_inv : forall segs c evs c',
  sstep segs c evs (SNext c') ->
  sys_inv (m_vmmaps (cfg_model c)) -> sys_inv (m_vmmaps (cfg_model c')).
Proof.
  intros segs [ms model] evs c' Hstep Hinv. cbn [cfg_model] in Hinv.
  inversion Hstep; subst; cbn [cfg_model].
  - match goal with
    | [ H : mi_account_step _ _ _ = RiscvSemantics.MachineOk (_, _) |- _ ] =>
        destruct (mi_account_step_model_frame _ _ _ _ _ H) as (_&Hvm&_)
    end.
    rewrite Hvm. exact Hinv.
  - match goal with
    | [ Hs : syscall_spec _ _ (Ok _ ?m1 _),
        Hm : materialize_model_accesses ?m1 _ = Some _ |- _ ] =>
        destruct (materialize_model_accesses_frame _ _ _ Hm) as (_&Hvm&_);
        rewrite Hvm; exact (syscall_spec_preserves_sys_inv _ _ _ _ _ Hs Hinv)
    end.
  - match goal with
    | [ Hs : syscall_spec _ _ (Ok _ _ _) |- _ ] =>
        exact (syscall_spec_preserves_sys_inv _ _ _ _ _ Hs Hinv)
    end.
  - match goal with
    | [ Hs : syscall_spec _ _ (Ok _ _ _) |- _ ] =>
        exact (syscall_spec_preserves_sys_inv _ _ _ _ _ Hs Hinv)
    end.
Qed.

(** A whole execution keeps it.  [Run.init_config]'s model is
    [State.init_model], where [init_model_sys_inv] holds, so every
    configuration a run reaches satisfies [sys_inv], and with it
    [State.noaccess_pages_owned] ([sys_inv_noaccess_pages_owned]) and
    [MapsFit.vm_fit]. *)
Lemma star_preserves_sys_inv : forall segs c tr c',
  star segs c tr c' ->
  sys_inv (m_vmmaps (cfg_model c)) -> sys_inv (m_vmmaps (cfg_model c')).
Proof.
  intros segs c tr c' Hstar.
  induction Hstar as [c | c1 evs c2 tr c3 Hstep Hstar IH]; intros Hinv;
    [exact Hinv|].
  exact (IH (sstep_preserves_sys_inv _ _ _ _ Hstep Hinv)).
Qed.

(** The same under a spurious-failure configuration, whose executions are
    executions of the unfiltered run ([Run.star_cfg_sub]). *)
Corollary star_cfg_preserves_sys_inv : forall segs cfg c tr c',
  star_cfg segs cfg c tr c' ->
  sys_inv (m_vmmaps (cfg_model c)) -> sys_inv (m_vmmaps (cfg_model c')).
Proof.
  intros segs cfg c tr c' Hstar.
  exact (star_preserves_sys_inv _ _ _ _ (star_cfg_sub _ _ _ _ _ Hstar)).
Qed.

(** The start of every run: [Run.init_config]'s model is
    [State.init_model], so [init_model_sys_inv] applies. *)
Lemma init_config_sys_inv : forall segs pc ph sp brk0 mb rnd lim inp,
  sys_inv (m_vmmaps (cfg_model (init_config segs pc ph sp brk0 mb rnd lim inp))).
Proof. intros. unfold init_config. cbn [cfg_model]. apply init_model_sys_inv. Qed.

(** Every configuration a run of an image reaches from its initial
    configuration satisfies [sys_inv], so [State.noaccess_pages_owned]
    ([sys_inv_noaccess_pages_owned]) and [MapsFit.vm_fit] hold there. *)
Corollary init_config_star_sys_inv : forall segs pc ph sp brk0 mb rnd lim inp tr c,
  star segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr c ->
  sys_inv (m_vmmaps (cfg_model c)).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp tr c Hstar.
  exact (star_preserves_sys_inv _ _ _ _ Hstar (init_config_sys_inv _ _ _ _ _ _ _ _ _)).
Qed.

(** The same under a spurious-failure configuration. *)
Corollary init_config_star_cfg_sys_inv :
  forall segs cfg pc ph sp brk0 mb rnd lim inp tr c,
  star_cfg segs cfg (init_config segs pc ph sp brk0 mb rnd lim inp) tr c ->
  sys_inv (m_vmmaps (cfg_model c)).
Proof.
  intros segs cfg pc ph sp brk0 mb rnd lim inp tr c Hstar.
  exact (star_cfg_preserves_sys_inv _ _ _ _ _ Hstar (init_config_sys_inv _ _ _ _ _ _ _ _ _)).
Qed.
