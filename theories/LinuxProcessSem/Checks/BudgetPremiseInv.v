(** * LinuxProcessSem.Checks.BudgetPremiseInv — the move's budget gate on invariant states

    Not part of the trusted specification.  [BudgetPremise]'s
    [mremap_move_budget_admits_fresh_lazyfree] takes two ledger
    hypotheses, [State.noaccess_pages_owned] and the fit of the live
    mappings.  Both follow from [NoaccessOwned.sys_inv], which holds on
    every configuration a run reaches
    ([NoaccessOwned.init_config_star_sys_inv]); this file states the
    gate fact with that one hypothesis in their place.

    THE ONE LEDGER HYPOTHESIS LEFT is that the lazy ledgers are empty
    ([m_vm_lazy m = []] and [m_vm_materialized m = []]): at that state
    the run holds no MAP_NORESERVE reservation and no first-touched page
    of one.  It is not a run invariant: it fails from a run's first
    successful MAP_NORESERVE reservation on, for as long as the
    reservation lives (an ASan runtime keeps its for the whole run;
    [Common/LazyFrame.v]), so a consumer discharges it from its own
    program; the general
    [BudgetPremise.mremap_move_budget_admits_fresh] takes the two
    lazy-ledger identities at the destination instead.

    The last two lemmas are in [mremap_spec]'s own terms: it passes
    [new_n] as the word of [new_nZ = page_round_up_Z (bv_unsigned
    new_size)] after [page_align_is0_b new_size = false], and
    [Mremap.mremap_fresh_b] states its bound on [new_nZ].
    [mremap_fresh_b_intro_sys_inv] concludes [mremap_fresh_b = true]
    from the move's budget gate and the destination's own guards. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs BudgetPremise MapsFit NoaccessOwned.
Import ListNotations.
Open Scope bv_scope.

Corollary mremap_move_budget_admits_fresh_sys_inv :
  forall m old old_n dst new_n,
  sys_inv (m_vmmaps m) ->
  m_vm_lazy m = [] ->
  m_vm_materialized m = [] ->
  (bv_unsigned dst mod page_size = 0)%Z ->
  (bv_unsigned new_n mod page_size = 0)%Z ->
  (0 < bv_unsigned new_n)%Z ->
  (bv_unsigned dst + bv_unsigned new_n <= alloc_top (m_vmmaps m))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) dst new_n
  = true ->
  mremap_move_budget_b m old old_n new_n = true ->
  mremap_final_budget_b m old old_n dst new_n = true.
Proof.
  intros m old old_n dst new_n Hinv Hlz Hmat Hdalign Hnmod Hpos Hdtop Hdfree Hmv.
  destruct Hinv as (Hwf & Hfit & Hna).
  exact (mremap_move_budget_admits_fresh_lazyfree m old old_n dst new_n
           Hlz Hmat Hdalign Hnmod Hpos Hdtop Hdfree
           (sys_inv_noaccess_pages_owned _ (conj Hwf (conj Hfit Hna)))
           (vm_fit_map_remove _ old Hfit) Hmv).
Qed.

(** [mremap_spec]'s [new_n] is a positive whole number of pages, and its
    word is its [Z] value.  The first conjunct is
    [BudgetPremise.page_align_is0_b_false_word]; this lemma adds the two
    side conditions the gate lemmas take on [bv_unsigned new_n]. *)
Lemma mremap_new_n_shape : forall new_size,
  page_align_is0_b new_size = false ->
  let new_n := Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)) in
  bv_unsigned new_n = page_round_up_Z (bv_unsigned new_size)
  /\ (bv_unsigned new_n mod page_size = 0)%Z
  /\ (0 < bv_unsigned new_n)%Z.
Proof.
  intros new_size H new_n.
  assert (Hw : bv_unsigned new_n = page_round_up_Z (bv_unsigned new_size))
    by exact (page_align_is0_b_false_word new_size H).
  rewrite Hw. split; [reflexivity|].
  split; [apply page_round_up_Z_mod|].
  unfold page_align_is0_b in H. apply orb_false_iff in H as [H0 _].
  assert (Hpos : (0 < bv_unsigned new_size)%Z).
  { pose proof (bv_unsigned_in_range 64 new_size) as Hr.
    destruct (Z.eq_dec (bv_unsigned new_size) 0) as [E|E]; [|lia].
    exfalso. unfold w_is0 in H0.
    assert (Heq : new_size = Z_to_bv 64 0)
      by (apply bv_eq; rewrite E; reflexivity).
    rewrite Heq, bv_eqb_refl in H0. discriminate H0. }
  unfold page_round_up_Z, page_size.
  assert (Hq : (1 <= (bv_unsigned new_size + 4096 - 1) / 4096)%Z)
    by (apply Z.div_le_lower_bound; lia).
  lia.
Qed.

(** THE MOVE IS ADMITTED.  In [mremap_spec]'s own terms
    ([new_n] the word of [new_nZ = page_round_up_Z (bv_unsigned
    new_size)], after [page_align_is0_b new_size = false]): on a state
    satisfying [sys_inv] with empty lazy ledgers, a destination that is
    not [old], nonzero, page aligned, ends at or below [alloc_top] and is
    free against [vm_reserved ++ vm_maps] passes [mremap_fresh_b]
    whenever the move's budget gate [mremap_move_budget_b] passes. *)
Lemma mremap_fresh_b_intro_sys_inv :
  forall m old_nZ new_size old old_n dst,
  let new_nZ := page_round_up_Z (bv_unsigned new_size) in
  let new_n := Z_to_bv 64 new_nZ in
  page_align_is0_b new_size = false ->
  sys_inv (m_vmmaps m) ->
  m_vm_lazy m = [] ->
  m_vm_materialized m = [] ->
  bv_eqb dst old = false ->
  (0 < bv_unsigned dst)%Z ->
  (bv_unsigned dst mod page_size = 0)%Z ->
  (bv_unsigned dst + new_nZ <= alloc_top (m_vmmaps m))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) dst new_n
  = true ->
  mremap_move_budget_b m old old_n new_n = true ->
  mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true.
Proof.
  intros m old_nZ new_size old old_n dst new_nZ new_n
    Hal Hinv Hlz Hmat Hne Hdpos Hdalign Hdtop Hdfree Hmv.
  destruct (mremap_new_n_shape new_size Hal) as (Hw & Hnmod & Hnpos).
  fold new_nZ new_n in Hw, Hnmod, Hnpos.
  assert (Hfin : mremap_final_budget_b m old old_n dst new_n = true).
  { apply (mremap_move_budget_admits_fresh_sys_inv m old old_n dst new_n
             Hinv Hlz Hmat Hdalign Hnmod Hnpos); [|exact Hdfree|exact Hmv].
    rewrite Hw. exact Hdtop. }
  unfold mremap_fresh_b. cbv zeta.
  rewrite Hne, Hdfree, Hfin.
  rewrite (proj2 (Z.eqb_eq _ _) Hdalign), (proj2 (Z.ltb_lt _ _) Hdpos),
    (proj2 (Z.leb_le _ _) Hdtop).
  reflexivity.
Qed.
