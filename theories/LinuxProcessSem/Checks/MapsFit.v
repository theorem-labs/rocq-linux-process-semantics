(** * LinuxProcessSem.Checks.MapsFit — every live mapping ends inside the address space

    Not part of the trusted specification: a ledger invariant, proved
    over the same dispatcher [Checks.VmMapsDisjoint] walks for [vm_wf].

    [vm_fit h] says every [vm_maps] entry ends at or below [two_pow_64].
    It is NOT a consequence of [VmMapsDisjoint.vm_wf]: that invariant
    bounds how many entries own a page-aligned address and that no size
    is zero, and an entry [(2^64 - 4096, 8192)] meets both.  It is the
    hypothesis [Mremap.mremap_move_charge_at_fresh] and the
    [BudgetPremise] lemmas built on it take on [map_remove (vm_maps h)
    old]; [vm_fit_map_remove] discharges it from [vm_fit].

    What every writer of [vm_maps] does to the list, and why each keeps
    the invariant:

    - a fresh grant ([mmap], [brk] grow, [mremap] grow in place and
      move) conses one entry whose end the writer has bounded — by
      [alloc_top] for [mmap] and [mremap], by a [word] break for [brk];
    - a cut ([munmap], [mremap] move's source, [brk] shrink, MAP_FIXED
      over live mappings) filters the list or subtracts a range from it,
      and every remnant of [State.iv_subtract] ends no later than the
      entry it came from;
    - [mremap] shrink re-records the source at a smaller size.

    As with [vm_wf], the statement is the base case ([init_model_vm_fit])
    and preservation by every modeled syscall
    ([check_syscall_preserves_vm_fit], [syscall_spec_preserves_vm_fit]);
    [NoaccessOwned.star_preserves_sys_inv] carries it, inside [sys_inv],
    along a whole run. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run MemImageType StackLayout.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs VmMapsDisjoint.
Import ListNotations.
Open Scope bv_scope.

Definition maps_fit (maps : list (word * word)) : Prop :=
  forall a sz, In (a, sz) maps ->
    (bv_unsigned a + bv_unsigned sz <= two_pow_64)%Z.

Definition vm_fit (h : VmMaps) : Prop := maps_fit (vm_maps h).

(** The form [Mremap.mremap_move_charge_at_fresh] takes. *)
Lemma vm_fit_map_remove : forall h old,
  vm_fit h ->
  forall (a sz : word), In (a, sz) (map_remove (vm_maps h) old) ->
    (bv_unsigned a + bv_unsigned sz <= two_pow_64)%Z.
Proof.
  intros h old Hf a sz Hin. unfold map_remove in Hin.
  apply List.filter_In in Hin as [Hin _]. exact (Hf a sz Hin).
Qed.

(* -------------------------------------------------------------------------
   Closure of [maps_fit] under the ways a writer builds [vm_maps]
   ------------------------------------------------------------------------- *)

Lemma maps_fit_nil : maps_fit [].
Proof. intros a sz []. Qed.

Lemma maps_fit_cons : forall maps a n,
  maps_fit maps -> (bv_unsigned a + bv_unsigned n <= two_pow_64)%Z ->
  maps_fit ((a, n) :: maps).
Proof.
  intros maps a n Hf Hb b s [Heq|Hin].
  - injection Heq as <- <-. exact Hb.
  - exact (Hf b s Hin).
Qed.

Lemma maps_fit_app : forall l1 l2,
  maps_fit l1 -> maps_fit l2 -> maps_fit (l1 ++ l2).
Proof.
  intros l1 l2 H1 H2 a sz Hin. apply in_app_or in Hin as [Hin|Hin].
  - exact (H1 a sz Hin).
  - exact (H2 a sz Hin).
Qed.

Lemma maps_fit_filter : forall f maps,
  maps_fit maps -> maps_fit (List.filter f maps).
Proof.
  intros f maps Hf a sz Hin. apply List.filter_In in Hin as [Hin _].
  exact (Hf a sz Hin).
Qed.

(** Each remnant of a cut ends no later than the entry it came from, at
    any cut: the right remnant exists only when the cut ends inside the
    entry, so its re-wrapped base is its base. *)
Lemma iv_subtract_fit : forall a sz lo hi,
  (bv_unsigned a + bv_unsigned sz <= two_pow_64)%Z ->
  maps_fit (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi Hfit. unfold two_pow_64 in Hfit.
  pose proof (word_range a) as Ha. pose proof (word_range sz) as Hs.
  unfold iv_subtract. cbv zeta.
  apply maps_fit_app.
  - destruct (bv_unsigned a <? lo)%Z eqn:E; [|exact maps_fit_nil].
    apply Z.ltb_lt in E.
    apply maps_fit_cons; [exact maps_fit_nil|].
    unfold two_pow_64. rewrite u64 by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz)%Z eqn:E;
      [|exact maps_fit_nil].
    apply Z.ltb_lt in E.
    apply maps_fit_cons; [exact maps_fit_nil|].
    unfold two_pow_64. rewrite !u64 by lia. lia.
Qed.

Lemma maps_subtract_fit : forall maps lo hi,
  maps_fit maps -> maps_fit (maps_subtract maps lo hi).
Proof.
  induction maps as [|[a sz] r IH]; intros lo hi Hf; cbn [maps_subtract].
  - exact maps_fit_nil.
  - apply maps_fit_app.
    + apply iv_subtract_fit. apply Hf. left. reflexivity.
    + apply IH. intros b s Hin. apply Hf. right. exact Hin.
Qed.

(** [mremap]'s in-place shrink: the source, re-recorded smaller. *)
Lemma maps_fit_cons_sub : forall maps a n0 n,
  maps_fit maps -> In (a, n0) maps -> (bv_unsigned n <= bv_unsigned n0)%Z ->
  maps_fit ((a, n) :: map_remove maps a).
Proof.
  intros maps a n0 n Hf Hin Hle. apply maps_fit_cons.
  - unfold map_remove. apply maps_fit_filter. exact Hf.
  - pose proof (Hf a n0 Hin). lia.
Qed.

(** The bound a fresh grant needs, from the writer's own ceiling. *)
Ltac fit_bound := unfold two_pow_64; rewrite ?u64 by lia; lia.

(* -------------------------------------------------------------------------
   The five writers of [vm_maps].  Each proof walks the checker exactly as
   its [VmMapsDisjoint] twin does for [vm_wf]; only the closure lemma at
   each leaf differs.
   ------------------------------------------------------------------------- *)

(** A brk grant [[old, r)] with [old < r] ends at the word [r]. *)
Lemma brk_model_next_fit : forall h req r,
  vm_fit h -> vm_fit (brk_model_next h req r).
Proof.
  intros h req r Hf.
  unfold vm_fit, brk_model_next, brk_maps_next. cbn [vm_maps].
  destruct (Z.ltb 0 (bv_unsigned (vm_brk h))
            && Z.ltb (bv_unsigned r) (bv_unsigned (vm_brk h))).
  - apply maps_subtract_fit. exact Hf.
  - apply maps_fit_app; [|exact Hf].
    unfold brk_grants. destruct (brk_is_grow req r (vm_brk h)) eqn:Egrow;
      [|exact maps_fit_nil].
    unfold brk_is_grow in Egrow.
    apply andb_true_iff in Egrow as [_ Hlt]. apply Z.ltb_lt in Hlt.
    apply maps_fit_cons; [exact maps_fit_nil|].
    pose proof (word_range r) as Hr. pose proof (word_range (vm_brk h)) as Hb.
    assert (Hsz : bv_unsigned (r - vm_brk h)%bv
                  = (bv_unsigned r - bv_unsigned (vm_brk h))%Z).
    { rewrite bv_sub_unsigned. apply bv_wrap_small.
      change (bv_modulus 64) with (2 ^ 64)%Z. lia. }
    rewrite Hsz. unfold two_pow_64. lia.
Qed.

Lemma check_brk_preserves_fit : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs ->
  vm_fit (m_vmmaps m) -> vm_fit (m_vmmaps m').
Proof.
  intros req [ret ws zs us cs ci] m m' evs H Hfit.
  unfold check_brk in H.
  destruct ws as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct ci as [|? ?]; [|discriminate].
  destruct (brk_r_ok m req ret
            && listNN_eqb zs (brk_zeros req ret (vm_brk (m_vmmaps m)))
            && listNN_eqb us (brk_unmaps ret (vm_brk (m_vmmaps m)))) eqn:E;
    [|discriminate].
  injection H as <- <-.
  rewrite vmm_brk_next. now apply brk_model_next_fit.
Qed.

Lemma check_munmap_preserves_fit : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs ->
  vm_fit (m_vmmaps m) -> vm_fit (m_vmmaps m').
Proof.
  intros addr len [ret ws zs us cs ci] m m' evs H Hfit.
  unfold check_munmap in H. cbv zeta in H.
  dif H; [apply check_ret_only_model in H; subst m'; exact Hfit|].
  dif H; [apply check_ret_only_model in H; subst m'; exact Hfit|].
  dif H.
  - destruct ws, zs, cs, ci; try discriminate.
    dif H; [|discriminate]. injection H as <- <-.
    unfold vm_fit. rewrite vmm_mmap_destroyed. cbn [vm_maps].
    now apply maps_fit_filter.
  - dif H; [apply check_ret_only_model in H; subst m'; exact Hfit|discriminate].
Qed.

Lemma check_mprotect_preserves_fit : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs ->
  vm_fit (m_vmmaps m) -> vm_fit (m_vmmaps m').
Proof.
  intros addr len prot [ret ws zs us cs ci] m m' evs H Hfit.
  unfold check_mprotect in H. cbv zeta in H.
  dif H; [apply check_ret_only_model in H; subst m'; exact Hfit|].
  dif H; [apply check_ret_only_model in H; subst m'; exact Hfit|].
  dif H; [apply check_ret_only_model in H; subst m'; exact Hfit|].
  dif H; [apply check_ret_only_model in H; subst m'; exact Hfit|].
  dif H; [discriminate|].
  dif H.
  - destruct ws, us, cs, ci; try discriminate.
    dif H.
    + destruct zs; [|discriminate]. injection H as <- <-. exact Hfit.
    + dif H; [|discriminate]. injection H as <- <-.
      unfold vm_fit. rewrite vmm_mprotect_next. cbn [vm_maps]. exact Hfit.
  - dif H; [|discriminate].
    destruct ws, zs, us, cs, ci; try discriminate.
    dif H; [|discriminate]. injection H as <- <-. exact Hfit.
Qed.

Lemma check_mmap_preserves_fit : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs ->
  vm_fit (m_vmmaps m) -> vm_fit (m_vmmaps m').
Proof.
  intros addr len prot flags fd off [ret ws zs us cs ci] m m' evs H Hfit.
  unfold check_mmap in H. cbv zeta in H.
  pose proof (alloc_top_lt (m_vmmaps m)) as Hac. unfold two_pow_64 in Hac.
  pose proof (word_range len) as Hlenr.
  pose proof (word_range addr) as Haddrr.
  pose proof (word_range ret) as Hretr.
  destruct (negb (mmap_off_aligned_b off)) eqn:Eoff.
  { destruct (mmap_pglen_ok_b len); [|discriminate].
    apply check_ret_only_model in H; subst m'; exact Hfit. }
  destruct (negb (mmap_anon_b flags)) eqn:Eanon; [discriminate|].
  destruct (w_is0 len) eqn:Elen.
  { destruct (mmap_plain_anon_b flags); [|discriminate].
    apply check_ret_only_model in H; subst m'; exact Hfit. }
  pose proof (w_is0_false len Elen) as Hlen0.
  assert (HnZ : (0 < page_round_up_Z (bv_unsigned len))%Z)
    by (apply page_round_up_pos; lia).
  destruct (mmap_modeled_b prot flags off) eqn:Emod.
  { destruct ws, us, cs, ci; try discriminate.
    destruct (errno_ret_in mmap_errnos ret).
    { destruct zs; [|discriminate]. injection H as <- <-. exact Hfit. }
    difn H E; [|discriminate]. injection H as <- <-.
    unfold vm_fit. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
    apply andb_true_iff in E as [E Hzs].
    apply andb_true_iff in E as [E Hbud].
    apply andb_true_iff in E as [E Hfree].
    apply andb_true_iff in E as [E Hceil].
    apply andb_true_iff in E as [Halign Hpos].
    apply Z.leb_le in Hceil. apply Z.ltb_lt in Hpos.
    apply maps_fit_cons; [exact Hfit | fit_bound]. }
  destruct (mmap_noaccess_b prot flags off) eqn:Enoa.
  { destruct ws, zs, cs, ci; try discriminate.
    destruct (errno_ret_in mmap_errnos ret).
    { destruct us; [|discriminate]. injection H as <- <-. exact Hfit. }
    difn H E; [|discriminate]. injection H as <- <-.
    unfold vm_fit. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
    apply andb_true_iff in E as [E Hus].
    apply andb_true_iff in E as [E Hfree].
    apply andb_true_iff in E as [E Hceil].
    apply andb_true_iff in E as [Halign Hpos].
    apply Z.leb_le in Hceil. apply Z.ltb_lt in Hpos.
    apply maps_fit_cons; [exact Hfit | fit_bound]. }
  destruct (mmap_fixed_noaccess_b prot flags off) eqn:Efix.
  { difn H Enomem; [apply check_ret_only_model in H; subst m'; exact Hfit|].
    difn H Eceil; [discriminate|].
    difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hfit|].
    difn H Epos; [discriminate|].
    apply negb_false_iff, Z.leb_le in Eceil.
    difn H Elive.
    - destruct ws, zs, cs, ci; try discriminate.
      destruct (errno_ret_in mmap_errnos ret).
      + destruct us.
        * injection H as <- <-. exact Hfit.
        * difn H Eus; [|discriminate]. injection H as <- <-.
          unfold vm_fit. rewrite vmm_mmap_destroyed. cbn [vm_maps].
          apply maps_subtract_fit. exact Hfit.
      + difn H Eok; [|discriminate]. injection H as <- <-.
        unfold vm_fit. rewrite vmm_mmap_replacement, vmm_vmmaps. cbn [vm_maps].
        exact Hfit.
    - difn H Efree.
      + destruct ws, zs, cs, ci; try discriminate.
        destruct (errno_ret_in mmap_errnos ret).
        * destruct us; [|discriminate]. injection H as <- <-. exact Hfit.
        * difn H Eok; [|discriminate]. injection H as <- <-.
          unfold vm_fit. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
          apply maps_fit_cons; [exact Hfit | fit_bound].
      + difn H Espan; [|discriminate].
        destruct ws, zs, cs, ci; try discriminate.
        destruct (errno_ret_in mmap_errnos ret).
        * destruct us.
          -- injection H as <- <-. exact Hfit.
          -- difn H Eus; [|discriminate]. injection H as <- <-.
             unfold vm_fit. rewrite vmm_mmap_destroyed. cbn [vm_maps].
             apply maps_subtract_fit. exact Hfit.
        * difn H Eok; [|discriminate]. injection H as <- <-.
          unfold vm_fit. rewrite vmm_mmap_replacement, vmm_vmmaps.
          cbn [vm_maps mmap_fixed_noaccess_span_next].
          apply maps_fit_cons;
            [apply maps_subtract_fit; exact Hfit | fit_bound]. }
  destruct (mmap_fixed_rw_b prot flags off) eqn:Efixrw.
  2: {
    destruct (mmap_noreplace_noaccess_b prot flags off) eqn:Enrn.
    { difn H Enomem; [apply check_ret_only_model in H; subst m'; exact Hfit|].
      difn H Eceil; [discriminate|].
      difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hfit|].
      difn H Epos; [discriminate|].
      apply negb_false_iff, Z.leb_le in Eceil.
      difn H Efree.
      - destruct ws, zs, cs, ci; try discriminate.
        destruct (errno_ret_in mmap_errnos ret).
        + destruct us; [|discriminate]. injection H as <- <-. exact Hfit.
        + difn H Eok; [|discriminate]. injection H as <- <-.
          unfold vm_fit. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
          apply maps_fit_cons; [exact Hfit | fit_bound].
      - destruct ws, zs, us, cs, ci; try discriminate.
        difn H Eerr; [|discriminate]. injection H as <- <-. exact Hfit. }
    destruct (mmap_noreplace_rw_b prot flags off) eqn:Enrr; [|discriminate].
    difn H Enomem; [apply check_ret_only_model in H; subst m'; exact Hfit|].
    difn H Eceil; [discriminate|].
    difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hfit|].
    difn H Epos; [discriminate|].
    apply negb_false_iff, Z.leb_le in Eceil.
    difn H Efree.
    - destruct ws, us, cs, ci; try discriminate.
      destruct (errno_ret_in mmap_errnos ret).
      + destruct zs; [|discriminate]. injection H as <- <-. exact Hfit.
      + difn H Eok; [|discriminate]. injection H as <- <-.
        unfold vm_fit. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
        apply maps_fit_cons; [exact Hfit | fit_bound].
    - destruct ws, zs, us, cs, ci; try discriminate.
      difn H Eerr; [|discriminate]. injection H as <- <-. exact Hfit. }
  difn H Enomem; [apply check_ret_only_model in H; subst m'; exact Hfit|].
  difn H Eceil; [discriminate|].
  difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hfit|].
  difn H Epos; [discriminate|].
  apply negb_false_iff, Z.leb_le in Eceil.
  difn H Elive.
  - destruct ws, cs, ci; try discriminate.
    destruct (errno_ret_in mmap_errnos ret).
    + destruct zs; [|discriminate]. destruct us.
      * injection H as <- <-. exact Hfit.
      * difn H Eus; [|discriminate]. injection H as <- <-.
        unfold vm_fit. rewrite vmm_mmap_destroyed. cbn [vm_maps].
        apply maps_subtract_fit. exact Hfit.
    + destruct us; [|discriminate].
      difn H Eok; [|discriminate]. injection H as <- <-.
      unfold vm_fit. rewrite vmm_mmap_replacement, vmm_vmmaps.
      rewrite vmm_fixed_rw_next. exact Hfit.
  - difn H Efree.
    + destruct ws, us, cs, ci; try discriminate.
      destruct (errno_ret_in mmap_errnos ret).
      * destruct zs; [|discriminate]. injection H as <- <-. exact Hfit.
      * difn H Eok; [|discriminate]. injection H as <- <-.
        unfold vm_fit. rewrite vmm_mmap_backing, vmm_vmmaps. cbn [vm_maps].
        apply maps_fit_cons; [exact Hfit | fit_bound].
    + difn H Espan; [|discriminate].
      destruct ws, cs, ci; try discriminate.
      destruct (errno_ret_in mmap_errnos ret).
      * destruct zs; [|discriminate]. destruct us.
        -- injection H as <- <-. exact Hfit.
        -- difn H Eus; [|discriminate]. injection H as <- <-.
           unfold vm_fit. rewrite vmm_mmap_destroyed. cbn [vm_maps].
           apply maps_subtract_fit. exact Hfit.
      * destruct us; [|discriminate].
        difn H Eok; [|discriminate]. injection H as <- <-.
        unfold vm_fit. rewrite vmm_mmap_replacement, vmm_vmmaps.
        cbn [vm_maps mmap_fixed_rw_span_next].
        apply maps_fit_cons;
          [apply maps_subtract_fit; exact Hfit | fit_bound].
Qed.

Lemma check_mremap_preserves_fit :
  forall old old_size new_size flags eff m m' evs,
  check_mremap old old_size new_size flags eff m = CheckOk m' evs ->
  vm_fit (m_vmmaps m) -> vm_fit (m_vmmaps m').
Proof.
  intros old old_size new_size flags [ret ws zs us cs ci] m m' evs H Hfit.
  unfold check_mremap in H. cbv zeta in H.
  pose proof (alloc_top_lt (m_vmmaps m)) as Hac. unfold two_pow_64 in Hac.
  pose proof (word_range old) as Hor.
  pose proof (word_range old_size) as Hos.
  pose proof (word_range new_size) as Hns.
  pose proof (word_range ret) as Hretr.
  difn H Eflag; [discriminate|].
  difn H Ealign; [apply check_ret_only_model in H; subst m'; exact Hfit|].
  difn H Enew; [apply check_ret_only_model in H; subst m'; exact Hfit|].
  difn H Etask; [apply check_ret_only_model in H; subst m'; exact Hfit|].
  difn H Eold; [discriminate|].
  difn H Esrc; [discriminate|].
  difn H Eeq; [apply check_ret_only_model in H; subst m'; exact Hfit|].
  destruct ws; [|discriminate]. destruct ci; [|discriminate].
  unfold page_align_is0_b in Enew. apply orb_false_iff in Enew as [Enew0 EnewB].
  apply Z.leb_gt in EnewB.
  pose proof (w_is0_false new_size Enew0) as Hnew0.
  assert (HnewZ : (0 < page_round_up_Z (bv_unsigned new_size))%Z)
    by (apply page_round_up_pos; lia).
  apply negb_false_iff in Esrc.
  apply andb_true_iff in Esrc as [Esrc _].
  unfold mremap_source_b in Esrc.
  apply andb_true_iff in Esrc as [Esrc _].
  apply andb_true_iff in Esrc as [Esrc Hhas].
  apply andb_true_iff in Esrc as [Hoceil _].
  apply Z.leb_le in Hoceil.
  assert (HoldZ : (0 <= page_round_up_Z (bv_unsigned old_size))%Z)
    by (apply page_round_up_Z_nonneg; lia).
  destruct (errno_ret_in mremap_errnos ret).
  { destruct zs, us, cs; try discriminate. injection H as <- <-. exact Hfit. }
  destruct (bv_eqb ret old).
  - difn H Eshrink.
    + difn H Eok; [|discriminate]. injection H as <- <-.
      apply Z.ltb_lt in Eshrink.
      unfold vm_fit. rewrite vmm_mremap_next.
      unfold mremap_maps_next. cbn [vm_maps].
      apply (maps_fit_cons_sub _ _
               (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))).
      * exact Hfit.
      * apply map_has_In. exact Hhas.
      * rewrite !u64 by lia. lia.
    + difn H Egrow; [|discriminate].
      difn H Eok; [|discriminate]. injection H as <- <-.
      unfold vm_fit. rewrite vmm_mremap_next.
      unfold mremap_maps_next. cbn [vm_maps].
      unfold mremap_inplace_grow_b in Egrow. cbv zeta in Egrow.
      apply andb_true_iff in Egrow as [Egrow _].
      apply andb_true_iff in Egrow as [Hgceil Hgfree].
      apply Z.leb_le in Hgceil.
      apply maps_fit_cons; [now apply maps_fit_filter | fit_bound].
  - difn H Emove; [|discriminate]. injection H as <- <-.
    unfold vm_fit. rewrite vmm_mremap_next.
    unfold mremap_maps_next. cbn [vm_maps].
    apply andb_true_iff in Emove as [Emove _].
    apply andb_true_iff in Emove as [Emove _].
    apply andb_true_iff in Emove as [Emove _].
    apply andb_true_iff in Emove as [_ Hfresh].
    unfold mremap_fresh_b in Hfresh. cbv zeta in Hfresh.
    apply andb_true_iff in Hfresh as [Hfresh _].
    apply andb_true_iff in Hfresh as [Hfresh Hffree].
    apply andb_true_iff in Hfresh as [Hfresh Hfceil].
    apply andb_true_iff in Hfresh as [_ Hfpos].
    apply Z.leb_le in Hfceil. apply Z.ltb_lt in Hfpos.
    apply maps_fit_cons; [now apply maps_fit_filter | fit_bound].
Qed.

(* -------------------------------------------------------------------------
   The invariant, over the whole dispatcher
   ------------------------------------------------------------------------- *)

(** [execve] establishes it: the ledger starts empty. *)
Lemma init_model_vm_fit : forall reserved brk0 mbase sp lim inp,
  vm_fit (m_vmmaps (init_model reserved brk0 mbase sp lim inp)).
Proof.
  intros reserved brk0 mbase sp lim inp.
  assert (Hm : vm_maps (m_vmmaps (init_model reserved brk0 mbase sp lim inp)) = [])
    by reflexivity.
  unfold vm_fit. rewrite Hm. exact maps_fit_nil.
Qed.

Definition arm_preserves_fit (c : CheckedArm) : Prop :=
  forall i eff m m' evs,
    ca_check c i eff m = CheckOk m' evs ->
    vm_fit (m_vmmaps m) -> vm_fit (m_vmmaps m').

(** The enumeration is [VmMapsDisjoint.checked_table_preserves_vm]'s,
    arm for arm: the five writers by their [*_preserves_fit] lemma, every
    other arm by its [*_frame] lemma ([VmMapsDisjoint], or the checker's
    own file, as [check_rt_sigprocmask_frame] in
    [Checks/Sys/Kernel/Signal.v]). *)
Lemma checked_table_preserves_fit : Forall arm_preserves_fit checked_table.
Proof.
  unfold checked_table.
  repeat apply Forall_cons.
  all: try exact (Forall_nil arm_preserves_fit).
  all: unfold arm_preserves_fit; intros i eff m m' evs H Hfit;
       autorewrite with arm_unfold in H.
  all: first
    [ eapply check_brk_preserves_fit; eassumption
    | eapply check_mmap_preserves_fit; eassumption
    | eapply check_munmap_preserves_fit; eassumption
    | eapply check_mremap_preserves_fit; eassumption
    | eapply check_mprotect_preserves_fit; eassumption
    | erewrite check_madvise_frame by eassumption; exact Hfit
    | erewrite check_read_frame by eassumption; exact Hfit
    | erewrite check_write_frame by eassumption; exact Hfit
    | erewrite check_pread64_frame by eassumption; exact Hfit
    | erewrite check_pwrite64_frame by eassumption; exact Hfit
    | erewrite check_readv_frame by eassumption; exact Hfit
    | erewrite check_writev_frame by eassumption; exact Hfit
    | erewrite check_openat_frame by eassumption; exact Hfit
    | erewrite check_close_frame by eassumption; exact Hfit
    | erewrite check_lseek_frame by eassumption; exact Hfit
    | erewrite check_ftruncate_frame by eassumption; exact Hfit
    | erewrite check_ioctl_frame by eassumption; exact Hfit
    | erewrite check_readlinkat_frame by eassumption; exact Hfit
    | erewrite check_wait4_frame by eassumption; exact Hfit
    | erewrite check_fsync_frame by eassumption; exact Hfit
    | erewrite check_getdents64_frame by eassumption; exact Hfit
    | erewrite check_flock_frame by eassumption; exact Hfit
    | erewrite check_exit_frame by eassumption; exact Hfit
    | erewrite check_set_tid_address_frame by eassumption; exact Hfit
    | erewrite check_getpid_frame by eassumption; exact Hfit
    | erewrite check_gettid_frame by eassumption; exact Hfit
    | erewrite check_setsid_frame by eassumption; exact Hfit
    | erewrite check_uname_frame by eassumption; exact Hfit
    | erewrite check_prctl_frame by eassumption; exact Hfit
    | erewrite check_prlimit64_frame by eassumption; exact Hfit
    | erewrite check_getrandom_frame by eassumption; exact Hfit
    | erewrite check_gettimeofday_frame by eassumption; exact Hfit
    | erewrite check_clock_gettime_frame by eassumption; exact Hfit
    | erewrite check_nanosleep_frame by eassumption; exact Hfit
    | erewrite check_dup_frame by eassumption; exact Hfit
    | erewrite check_dup3_frame by eassumption; exact Hfit
    | erewrite check_unlinkat_frame by eassumption; exact Hfit
    | erewrite check_faccessat_frame by eassumption; exact Hfit
    | erewrite check_faccessat2_frame by eassumption; exact Hfit
    | erewrite check_pselect6_frame by eassumption; exact Hfit
    | erewrite check_ppoll_frame by eassumption; exact Hfit
    | erewrite check_newfstatat_frame by eassumption; exact Hfit
    | erewrite check_fstat_frame by eassumption; exact Hfit
    | erewrite check_getid_frame by eassumption; exact Hfit
    | erewrite check_setid_frame by eassumption; exact Hfit
    | erewrite check_setresid_frame by eassumption; exact Hfit
    | erewrite check_getgroups_frame by eassumption; exact Hfit
    | erewrite check_setgroups_frame by eassumption; exact Hfit
    | erewrite check_socket_frame by eassumption; exact Hfit
    | erewrite check_bind_frame by eassumption; exact Hfit
    | erewrite check_listen_frame by eassumption; exact Hfit
    | erewrite check_accept4_frame by eassumption; exact Hfit
    | erewrite check_fcntl_frame by eassumption; exact Hfit
    | erewrite check_sched_setscheduler_frame by eassumption; exact Hfit
    | erewrite check_sched_getaffinity_frame by eassumption; exact Hfit
    | erewrite check_sched_yield_frame by eassumption; exact Hfit
    | erewrite check_sigaltstack_frame by eassumption; exact Hfit
    | erewrite check_rt_sigaction_frame by eassumption; exact Hfit
    | erewrite check_tkill_frame by eassumption; exact Hfit
    | erewrite check_tgkill_frame by eassumption; exact Hfit
    | erewrite check_rt_sigprocmask_frame by eassumption; exact Hfit
    | erewrite check_futex_frame by eassumption; exact Hfit
    | erewrite check_clone_frame by eassumption; exact Hfit
    | erewrite check_clone3_frame by eassumption; exact Hfit
    | erewrite check_getsockname_frame by eassumption; exact Hfit
    | erewrite check_getpeername_frame by eassumption; exact Hfit
    | erewrite check_setsockopt_frame by eassumption; exact Hfit
    | erewrite check_getsockopt_frame by eassumption; exact Hfit
    | erewrite check_shutdown_frame by eassumption; exact Hfit
    | erewrite check_sendto_frame by eassumption; exact Hfit
    | erewrite check_sendmsg_frame by eassumption; exact Hfit
    | erewrite check_socketpair_frame by eassumption; exact Hfit
    | erewrite check_recvfrom_frame by eassumption; exact Hfit
    | erewrite check_recvmsg_frame by eassumption; exact Hfit
    | erewrite check_connect_frame by eassumption; exact Hfit
    | erewrite check_timerfd_create_frame by eassumption; exact Hfit
    | erewrite check_eventfd2_frame by eassumption; exact Hfit
    | erewrite check_pipe2_frame by eassumption; exact Hfit
    | erewrite check_getcwd_frame by eassumption; exact Hfit
    | erewrite check_epoll_create1_frame by eassumption; exact Hfit
    | erewrite check_epoll_ctl_frame by eassumption; exact Hfit
    | erewrite check_epoll_pwait_frame by eassumption; exact Hfit
    | fail 1 "checked_table_preserves_fit has no case for this dispatcher arm: give the new checker a *_frame lemma (it leaves m_vmmaps alone) or a *_preserves_fit one (it writes vm_maps), and add it to the list above" ].
Qed.

Theorem check_syscall_preserves_vm_fit : forall i eff m m' evs,
  check_syscall i eff m = CheckOk m' evs ->
  vm_fit (m_vmmaps m) -> vm_fit (m_vmmaps m').
Proof.
  intros i eff m m' evs H Hfit. unfold check_syscall in H.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk;
    [|discriminate H].
  pose proof checked_table_preserves_fit as Hall.
  rewrite Forall_forall in Hall.
  exact (Hall c (lookup_ca_In _ _ _ Elk) i eff m m' evs H Hfit).
Qed.

(** The same statement against the RELATIONAL spec. *)
Corollary syscall_spec_preserves_vm_fit : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  vm_fit (m_vmmaps m) -> vm_fit (m_vmmaps m').
Proof.
  intros i m eff m' evs H Hfit.
  eapply check_syscall_preserves_vm_fit; [|exact Hfit].
  apply check_syscall_ok_iff. exact H.
Qed.
