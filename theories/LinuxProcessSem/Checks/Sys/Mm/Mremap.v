(** * LinuxProcessSem.Checks.Sys.Mm.Mremap — the mremap (216) checkers, and their proofs

    Mirrors [Sys/Mm/Mremap.v], which answers to Linux [mm/mremap.c]:
    this file holds the checkers for the syscalls defined there, and no
    others.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export
  Prelude Fs.ReadWrite Mm.Mmap.

Definition check_mremap (old old_size new_size flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (Z.eqb (bv_unsigned flags) MREMAP_MAYMOVE)
  then CheckUnmodeled
  else if negb (Z.eqb (bv_unsigned old mod page_size) 0)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if page_align_is0_b new_size
  then check_ret_only eff (errno_ret EINVAL) m []
  else if (TASK_SIZE <? page_round_up_Z (bv_unsigned new_size))%Z
  then check_ret_only eff (errno_ret EINVAL) m []
  else if page_align_is0_b old_size
  then CheckUnmodeled
  else
    let old_nZ := page_round_up_Z (bv_unsigned old_size) in
    let new_nZ := page_round_up_Z (bv_unsigned new_size) in
    let old_n := Z_to_bv 64 old_nZ in
    let new_n := Z_to_bv 64 new_nZ in
    if negb (mremap_source_b (m_vmmaps m) old old_n old_nZ
             && mremap_backing_uniform_b m old old_n)
    then CheckUnmodeled
    else if Z.eqb old_nZ new_nZ
    then check_ret_only eff old m []
    else
    match eff with
    | mkEffectU r [] zs us cs [] =>
        if errno_ret_in mremap_errnos r then
          match zs, us, cs with
          | [], [], [] => CheckOk m []
          | _, _, _ => CheckReject
          end
        else if bv_eqb r old then
          if (new_nZ <? old_nZ)%Z then
            if listNN_eqb zs []
               && listNN_eqb us
                    [(old + new_n,
                      Z_to_bv 64 (old_nZ - new_nZ))]
               && listCopy_eqb cs []
            then CheckOk
              (mremap_model_next m old old_n old new_n) []
            else CheckReject
          else if mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ
          then if listNN_eqb zs (mremap_tail old old_n old_nZ new_nZ)
                  && listNN_eqb us [] && listCopy_eqb cs []
               then CheckOk
                 (mremap_model_next m old old_n old new_n) []
               else CheckReject
          else CheckReject
        else if (old_nZ <? new_nZ)%Z
                  && mremap_fresh_b m old_nZ new_nZ old old_n r new_n
                  && listNN_eqb zs (mremap_tail r old_n old_nZ new_nZ)
                  && listNN_eqb us [(old, old_n)]
                  && listCopy_eqb cs [mkCopy old r old_n]
             then CheckOk
               (mremap_model_next m old old_n r new_n) []
             else CheckReject
    | _ => CheckReject
    end.

Lemma mremap_source_ret_not_errno : forall h old old_n old_nZ,
  (0 <= old_nZ)%Z -> mremap_source_b h old old_n old_nZ = true ->
  errno_ret_in mremap_errnos old = false.
Proof.
  intros h old old_n old_nZ Hn Hsrc.
  unfold mremap_source_b in Hsrc. rewrite !Bool.andb_true_iff in Hsrc.
  destruct Hsrc as (((Hbound & _) & _) & _). apply Z.leb_le in Hbound.
  apply errno_ret_in_below; [reflexivity|].
  alloc_top_bounds. unfold two_pow_64 in *; lia.
Qed.

Lemma mremap_fresh_ret_not_errno : forall m old_nZ new_nZ old old_n dst new_n,
  (0 <= new_nZ)%Z ->
  mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true ->
  errno_ret_in mremap_errnos dst = false.
Proof.
  intros m old_nZ new_nZ old old_n dst new_n Hn Hfresh.
  unfold mremap_fresh_b in Hfresh. cbv zeta in Hfresh.
  rewrite !Bool.andb_true_iff in Hfresh.
  destruct Hfresh as (((((_ & _) & _) & Hbound) & _) & _).
  apply Z.leb_le in Hbound.
  apply errno_ret_in_below; [reflexivity|].
  alloc_top_bounds. unfold two_pow_64 in *; lia.
Qed.

Lemma mremap_fresh_neq_old : forall m old_nZ new_nZ old old_n dst new_n,
  mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true ->
  bv_eqb dst old = false.
Proof.
  intros m old_nZ new_nZ old old_n dst new_n H.
  unfold mremap_fresh_b in H. cbv zeta in H.
  rewrite !Bool.andb_true_iff in H.
  destruct H as (((((Hneq & _) & _) & _) & _) & _).
  now apply negb_true_iff in Hneq.
Qed.

Lemma check_mremap_sound_ok : forall old old_size new_size flags eff m m' evs i,
  check_mremap old old_size new_size flags eff m = CheckOk m' evs ->
  mremap_spec old old_size new_size flags i m (Ok eff m' evs).
Proof.
  intros old old_size new_size flags eff m m' evs i H.
  unfold check_mremap in H. unfold mremap_spec.
  destruct (negb (Z.eqb (bv_unsigned flags) MREMAP_MAYMOVE)) eqn:Hshape;
    [discriminate|].
  destruct (negb (Z.eqb (bv_unsigned old mod page_size) 0)) eqn:Halign.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct (page_align_is0_b new_size) eqn:Hnew.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct (TASK_SIZE <? page_round_up_Z (bv_unsigned new_size))%Z eqn:Htask.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct (page_align_is0_b old_size) eqn:Hold; [discriminate|].
  cbv zeta in H.
  destruct (negb (mremap_source_b (m_vmmaps m) old
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
              (page_round_up_Z (bv_unsigned old_size))
            && mremap_backing_uniform_b m old
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))))) eqn:Hsrc;
    [discriminate|].
  destruct (Z.eqb (page_round_up_Z (bv_unsigned old_size))
                   (page_round_up_Z (bv_unsigned new_size))) eqn:Heq.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
    try rewrite Hsrc. try rewrite Heq. apply pure_ok. }
  destruct eff as [r ws zs us cs copyins]. destruct ws as [|w ws]; [|discriminate].
  destruct (errno_ret_in mremap_errnos r) eqn:Herr.
  - destruct zs as [|z zs]; destruct us as [|u us]; destruct cs as [|c cs];
      destruct copyins as [|? ?];
      try discriminate.
    inversion H; clear H; subst.
    apply errno_ret_in_true in Herr. destruct Herr as (e & HIn & ->).
    eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
    try rewrite Hsrc. try rewrite Heq. apply alt_l.
    eapply bind_ok0; [apply (choose_ok _ e); exact HIn|]. apply pure_ok.
  - destruct (bv_eqb r old) eqn:Hret.
    + apply bv_eqb_eq in Hret; subst r.
      destruct ((page_round_up_Z (bv_unsigned new_size)
                  <? page_round_up_Z (bv_unsigned old_size))%Z) eqn:Hlt.
      * destruct (listNN_eqb zs []) eqn:Hzs;
          [|destruct copyins; discriminate].
        destruct (listNN_eqb us
          [(old + Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)),
            Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)
                         - page_round_up_Z (bv_unsigned new_size)))]) eqn:Hus;
          [|destruct copyins; discriminate].
        destruct (listCopy_eqb cs []) eqn:Hcs;
          [|destruct copyins; discriminate].
        destruct copyins as [|? ?]; [|discriminate].
        inversion H; clear H; subst.
        apply listNN_eqb_eq in Hzs; subst zs.
        apply listNN_eqb_eq in Hus; subst us.
        apply listCopy_eqb_eq in Hcs; subst cs.
        eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
        try rewrite Hsrc. try rewrite Heq. apply alt_r. try rewrite Hlt.
        eapply bind_ok0; [apply modify_ok|].
        unfold mremap_inplace_effect. rewrite Hlt. apply pure_ok.
      * destruct (mremap_inplace_grow_b m old
             (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
             (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))
             (page_round_up_Z (bv_unsigned old_size))
             (page_round_up_Z (bv_unsigned new_size))) eqn:Hgrow;
          [|destruct copyins; discriminate].
        destruct (listNN_eqb zs
          (mremap_tail old
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
            (page_round_up_Z (bv_unsigned old_size))
            (page_round_up_Z (bv_unsigned new_size)))) eqn:Hzs;
          [|destruct copyins; discriminate].
        destruct (listNN_eqb us []) eqn:Hus;
          [|destruct copyins; discriminate].
        destruct (listCopy_eqb cs []) eqn:Hcs;
          [|destruct copyins; discriminate].
        destruct copyins as [|? ?]; [|discriminate].
        inversion H; clear H; subst.
        apply listNN_eqb_eq in Hzs; subst zs.
        apply listNN_eqb_eq in Hus; subst us.
        apply listCopy_eqb_eq in Hcs; subst cs.
        eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
        try rewrite Hsrc. try rewrite Heq. apply alt_r.
        try rewrite Hlt. try rewrite Hgrow.
        apply alt_l. eapply bind_ok0; [apply modify_ok|].
        unfold mremap_inplace_effect. rewrite Hlt. apply pure_ok.
    + destruct ((page_round_up_Z (bv_unsigned old_size)
                   <? page_round_up_Z (bv_unsigned new_size))%Z)
                eqn:Hmove; [|destruct copyins; discriminate].
      destruct (mremap_fresh_b m
                  (page_round_up_Z (bv_unsigned old_size))
                  (page_round_up_Z (bv_unsigned new_size)) old
                  (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) r
                  (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))))
        eqn:Hfresh; [|destruct copyins; discriminate].
      destruct (listNN_eqb zs
        (mremap_tail r
          (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
          (page_round_up_Z (bv_unsigned old_size))
          (page_round_up_Z (bv_unsigned new_size)))) eqn:Hzs;
        [|destruct copyins; discriminate].
      destruct (listNN_eqb us
        [(old, Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))]) eqn:Hus;
        [|destruct copyins; discriminate].
      destruct (listCopy_eqb cs
        [mkCopy old r
          (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))]) eqn:Hcs;
        [|destruct copyins; discriminate].
      destruct copyins as [|? ?]; [|discriminate].
      inversion H; clear H; subst.
      apply listNN_eqb_eq in Hzs; subst zs.
      apply listNN_eqb_eq in Hus; subst us.
      apply listCopy_eqb_eq in Hcs; subst cs.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
      try rewrite Hsrc. try rewrite Heq. apply alt_r.
      destruct ((page_round_up_Z (bv_unsigned new_size)
                   <? page_round_up_Z (bv_unsigned old_size))%Z) eqn:Hlt.
      * apply Z.ltb_lt in Hmove. apply Z.ltb_lt in Hlt. lia.
      * destruct (mremap_inplace_grow_b m old
             (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
             (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))
             (page_round_up_Z (bv_unsigned old_size))
             (page_round_up_Z (bv_unsigned new_size))) eqn:Hgrow.
        -- apply alt_r. eapply bind_ok0; [apply (choose_ok _ r); exact Hfresh|].
           eapply bind_ok0; [apply modify_ok|].
           unfold mremap_move_effect. apply pure_ok.
        -- eapply bind_ok0; [apply (choose_ok _ r); exact Hfresh|].
           eapply bind_ok0; [apply modify_ok|].
           unfold mremap_move_effect. apply pure_ok.
Qed.

Lemma check_mremap_sound_unmodeled : forall old old_size new_size flags eff m i,
  check_mremap old old_size new_size flags eff m = CheckUnmodeled ->
  mremap_spec old old_size new_size flags i m Unmodeled.
Proof.
  intros old old_size new_size flags eff m i H.
  unfold check_mremap in H. unfold mremap_spec.
  destruct (negb (Z.eqb (bv_unsigned flags) MREMAP_MAYMOVE)) eqn:Hshape.
  { apply unmodeled_intro. }
  destruct (negb (Z.eqb (bv_unsigned old mod page_size) 0)) eqn:Halign.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (page_align_is0_b new_size) eqn:Hnew.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (TASK_SIZE <? page_round_up_Z (bv_unsigned new_size))%Z eqn:Htask.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (page_align_is0_b old_size) eqn:Hold.
  { apply unmodeled_intro. }
  cbv zeta in H.
  destruct (negb (mremap_source_b (m_vmmaps m) old
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
              (page_round_up_Z (bv_unsigned old_size))
            && mremap_backing_uniform_b m old
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))))) eqn:Hsrc.
  { eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta zeta.
    rewrite Hsrc. apply unmodeled_intro. }
  destruct (Z.eqb (page_round_up_Z (bv_unsigned old_size))
                   (page_round_up_Z (bv_unsigned new_size))) eqn:Heq.
  { now apply check_ret_only_no_unmodeled in H. }
  exfalso.
  destruct eff as [r ws zs us cs copyins]. destruct ws as [|w ws]; [|discriminate].
  destruct (errno_ret_in mremap_errnos r).
  { destruct zs; destruct us; destruct cs; destruct copyins; discriminate. }
  destruct (bv_eqb r old).
  - destruct ((page_round_up_Z (bv_unsigned new_size)
                 <? page_round_up_Z (bv_unsigned old_size))%Z).
    + destruct (listNN_eqb zs []);
      destruct (listNN_eqb us
        [(old + Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)),
          Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)
                       - page_round_up_Z (bv_unsigned new_size)))]);
      destruct (listCopy_eqb cs []); destruct copyins; discriminate.
    + destruct (mremap_inplace_grow_b m old
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))
        (page_round_up_Z (bv_unsigned old_size))
        (page_round_up_Z (bv_unsigned new_size)));
        [|destruct copyins; discriminate].
      destruct (listNN_eqb zs
        (mremap_tail old
          (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
          (page_round_up_Z (bv_unsigned old_size))
          (page_round_up_Z (bv_unsigned new_size))));
      destruct (listNN_eqb us []); destruct (listCopy_eqb cs []);
      destruct copyins;
      discriminate.
  - destruct ((page_round_up_Z (bv_unsigned old_size)
                 <? page_round_up_Z (bv_unsigned new_size))%Z);
      [|destruct copyins; discriminate].
    destruct (mremap_fresh_b m
      (page_round_up_Z (bv_unsigned old_size))
      (page_round_up_Z (bv_unsigned new_size)) old
      (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) r
      (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))));
      [|destruct copyins; discriminate].
    destruct (listNN_eqb zs
      (mremap_tail r
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
        (page_round_up_Z (bv_unsigned old_size))
        (page_round_up_Z (bv_unsigned new_size))));
    destruct (listNN_eqb us
      [(old, Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))]);
    destruct (listCopy_eqb cs
      [mkCopy old r
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))]);
    destruct copyins;
    discriminate.
Qed.

Lemma check_mremap_complete_ok : forall old old_size new_size flags eff m m' evs i,
  mremap_spec old old_size new_size flags i m (Ok eff m' evs) ->
  check_mremap old old_size new_size flags eff m = CheckOk m' evs.
Proof.
  intros old old_size new_size flags eff m m' evs i H.
  unfold mremap_spec in H. unfold check_mremap.
  destruct (negb (Z.eqb (bv_unsigned flags) MREMAP_MAYMOVE)) eqn:Hshape.
  { sys_unfold. inv_ok; discriminate. }
  destruct (negb (Z.eqb (bv_unsigned old mod page_size) 0)) eqn:Halign.
  { sys_unfold. inv_ok. cbn. rewrite bv_eqb_refl. reflexivity. }
  destruct (page_align_is0_b new_size) eqn:Hnew.
  { sys_unfold. inv_ok. cbn. rewrite bv_eqb_refl. reflexivity. }
  destruct (TASK_SIZE <? page_round_up_Z (bv_unsigned new_size))%Z eqn:Htask.
  { sys_unfold. inv_ok. cbn. rewrite bv_eqb_refl. reflexivity. }
  destruct (page_align_is0_b old_size) eqn:Hold.
  { sys_unfold. inv_ok; discriminate. }
  sys_unfold. cbv iota zeta in H. inv_ok.
  destruct (negb (mremap_source_b (m_vmmaps m) old
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
              (page_round_up_Z (bv_unsigned old_size))
            && mremap_backing_uniform_b m old
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))))) eqn:Hsrc;
    hall Hsrc; inv_ok.
  apply negb_false_iff in Hsrc.
  apply andb_true_iff in Hsrc as [Hsource Huniform].
  assert (Hold_nonneg :
    (0 <= page_round_up_Z (bv_unsigned old_size))%Z)
    by (apply page_round_up_Z_nonneg; pose proof (word_unsigned_range old_size); lia).
  assert (Hnew_nonneg :
    (0 <= page_round_up_Z (bv_unsigned new_size))%Z)
    by (apply page_round_up_Z_nonneg; pose proof (word_unsigned_range new_size); lia).
  assert (Hold_errno : errno_ret_in mremap_errnos old = false).
  { exact (mremap_source_ret_not_errno (m_vmmaps m) old
      (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
      (page_round_up_Z (bv_unsigned old_size)) Hold_nonneg Hsource). }
  destruct (Z.eqb (page_round_up_Z (bv_unsigned old_size))
                   (page_round_up_Z (bv_unsigned new_size))) eqn:Heq.
  - hall Heq; inv_ok. cbn. rewrite bv_eqb_refl. reflexivity.
  - hall Heq; inv_ok.
    all: try (cbv beta iota zeta in *; subst;
              rewrite errno_ret_in_intro by assumption; reflexivity).
    destruct ((page_round_up_Z (bv_unsigned new_size)
                 <? page_round_up_Z (bv_unsigned old_size))%Z) eqn:Hlt.
    + hall Hlt; inv_ok. cbv beta iota zeta in *; subst.
      unfold mremap_inplace_effect. rewrite Hlt.
      try rewrite Hold_errno. try rewrite bv_eqb_refl.
      try rewrite Heq. try rewrite Hlt.
      repeat match goal with
      | |- context [listNN_eqb ?l ?l] => rewrite (proj2 (listNN_eqb_eq l l) eq_refl)
      | |- context [listCopy_eqb ?l ?l] => rewrite (proj2 (listCopy_eqb_eq l l) eq_refl)
      end. reflexivity.
    + hall Hlt.
      assert (Hmove : (page_round_up_Z (bv_unsigned old_size)
                         <? page_round_up_Z (bv_unsigned new_size))%Z = true).
      { apply Z.ltb_lt. apply Z.ltb_ge in Hlt. apply Z.eqb_neq in Heq. lia. }
      destruct (mremap_inplace_grow_b m old
          (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
          (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))
          (page_round_up_Z (bv_unsigned old_size))
          (page_round_up_Z (bv_unsigned new_size))) eqn:Hgrow.
      * hall Hgrow; inv_ok.
        -- cbv beta iota zeta in *; subst.
           unfold mremap_inplace_effect. rewrite Hlt.
           try rewrite Hold_errno. try rewrite bv_eqb_refl.
           try rewrite Heq. try rewrite Hlt.
           try rewrite Hgrow.
           repeat match goal with
           | |- context [listNN_eqb ?l ?l] => rewrite (proj2 (listNN_eqb_eq l l) eq_refl)
           | |- context [listCopy_eqb ?l ?l] => rewrite (proj2 (listCopy_eqb_eq l l) eq_refl)
           end. reflexivity.
        -- cbv beta iota zeta in *; subst.
           unfold mremap_move_effect.
           match goal with
           | Hfresh : mremap_fresh_b _ _ _ old ?old_n ?dst _ = true |- _ =>
               rewrite (mremap_fresh_ret_not_errno _ _ _ old old_n dst _ Hnew_nonneg Hfresh);
               rewrite (mremap_fresh_neq_old _ _ _ old old_n dst _ Hfresh);
               try rewrite Hmove; try rewrite Hfresh
           end.
           repeat match goal with
           | |- context [listNN_eqb ?l ?l] => rewrite (proj2 (listNN_eqb_eq l l) eq_refl)
           | |- context [listCopy_eqb ?l ?l] => rewrite (proj2 (listCopy_eqb_eq l l) eq_refl)
           end. reflexivity.
      * hall Hgrow; inv_ok. cbv beta iota zeta in *; subst.
        unfold mremap_move_effect.
        match goal with
        | Hfresh : mremap_fresh_b _ _ _ old ?old_n ?dst _ = true |- _ =>
            rewrite (mremap_fresh_ret_not_errno _ _ _ old old_n dst _ Hnew_nonneg Hfresh);
            rewrite (mremap_fresh_neq_old _ _ _ old old_n dst _ Hfresh);
            try rewrite Hmove; try rewrite Hfresh
        end.
        repeat match goal with
        | |- context [listNN_eqb ?l ?l] => rewrite (proj2 (listNN_eqb_eq l l) eq_refl)
        | |- context [listCopy_eqb ?l ?l] => rewrite (proj2 (listCopy_eqb_eq l l) eq_refl)
        end. reflexivity.
Qed.

Lemma check_mremap_complete_unmodeled : forall old old_size new_size flags m i eff,
  mremap_spec old old_size new_size flags i m Unmodeled ->
  check_mremap old old_size new_size flags eff m = CheckUnmodeled.
Proof.
  intros old old_size new_size flags m i eff H.
  unfold mremap_spec in H. unfold check_mremap.
  destruct (negb (Z.eqb (bv_unsigned flags) MREMAP_MAYMOVE)) eqn:Hshape.
  { reflexivity. }
  destruct (negb (Z.eqb (bv_unsigned old mod page_size) 0)) eqn:Halign.
  { sys_unfold. inv_ok; discriminate. }
  destruct (page_align_is0_b new_size) eqn:Hnew.
  { sys_unfold. inv_ok; discriminate. }
  destruct (TASK_SIZE <? page_round_up_Z (bv_unsigned new_size))%Z eqn:Htask.
  { sys_unfold. inv_ok; discriminate. }
  destruct (page_align_is0_b old_size) eqn:Hold.
  { reflexivity. }
  sys_unfold. cbv iota zeta in H. inv_ok.
  destruct (negb (mremap_source_b (m_vmmaps m) old
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
              (page_round_up_Z (bv_unsigned old_size))
            && mremap_backing_uniform_b m old
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))))) eqn:Hsrc;
    hall Hsrc; inv_ok; [reflexivity|].
  exfalso.
  destruct (Z.eqb (page_round_up_Z (bv_unsigned old_size))
                   (page_round_up_Z (bv_unsigned new_size))) eqn:Heq;
    hall Heq; inv_ok; try discriminate.
  destruct ((page_round_up_Z (bv_unsigned new_size)
               <? page_round_up_Z (bv_unsigned old_size))%Z) eqn:Hlt;
    hall Hlt; inv_ok; try discriminate.
  destruct (mremap_inplace_grow_b m old
      (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
      (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))
      (page_round_up_Z (bv_unsigned old_size))
      (page_round_up_Z (bv_unsigned new_size))) eqn:Hgrow;
    hall Hgrow; inv_ok; discriminate.
Qed.
