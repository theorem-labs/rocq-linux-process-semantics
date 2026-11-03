(** * LinuxProcessSem.Checks.Sys.Mm.Mprotect — the mprotect (226) checkers, and their proofs

    Mirrors [Sys/Mm/Mprotect.v], which answers to Linux [mm/mprotect.c]:
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
  Prelude Fs.ReadWrite.

Definition check_mprotect (addr len prot : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if mprotect_grows_conflict_b prot
  then check_ret_only eff (errno_ret EINVAL) m []
  else if negb (Z.eqb (bv_unsigned addr mod page_size) 0)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if w_is0 len then check_ret_only eff (Z_to_bv 64 0) m []
  else if (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z
  then check_ret_only eff (errno_ret ENOMEM) m []
  else if negb (mprotect_modeled_b prot) then CheckUnmodeled
  else
    let nZ := page_round_up_Z (bv_unsigned len) in
    let n := Z_to_bv 64 nZ in
    (* The vdso/vvar pair: the spec answers [unmodeled] for a request
       that meets it, because the text carries [VM_MAYWRITE] and the
       model has no term for a vDSO whose bytes changed. *)
    if negb (region_free (vdso_reserved (m_kernel m) (vdso_top (m_vmmaps m)))
               addr n)
    then CheckUnmodeled
    else
    if map_contains (vm_noaccess (m_vmmaps m)) addr n
       && map_contains (vm_maps (m_vmmaps m)) addr n then
      match eff with
      | mkEffectU r [] zs [] [] [] =>
          if errno_ret_in mprotect_errnos r
          then match zs with [] => CheckOk m [] | _ => CheckReject end
          else if mprotect_budget_ok m addr n
                  && w_is0 r && listNN_eqb zs [(addr, n)]
          then CheckOk
            (mprotect_model_next m addr n) []
          else CheckReject
      | _ => CheckReject
      end
    else if map_contains (vm_maps (m_vmmaps m)) addr n
            && region_free (vm_noaccess (m_vmmaps m)) addr n then
      match eff with
      | mkEffectU r [] [] [] [] [] =>
          if w_is0 r then CheckOk m [] else CheckReject
      | _ => CheckReject
      end
    else CheckUnmodeled.

Lemma check_mprotect_sound_ok : forall addr len prot eff m m' evs i,
  check_mprotect addr len prot eff m = CheckOk m' evs ->
  mprotect_spec addr len prot i m (Ok eff m' evs).
Proof.
  intros addr len prot eff m m' evs i H.
  unfold check_mprotect in H. unfold mprotect_spec.
  destruct (mprotect_grows_conflict_b prot) eqn:Hgrows.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct (w_is0 len) eqn:Hlen.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hbig.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct (mprotect_modeled_b prot) eqn:Hprot; cbn [negb] in H;
    [|discriminate].
  cbv zeta in H.
  destruct (negb (region_free (vdso_reserved (m_kernel m) (vdso_top (m_vmmaps m)))
                   addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))) eqn:Hvd;
    [discriminate|].
  destruct (map_contains (vm_noaccess (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
            && map_contains (vm_maps (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hcover.
  { destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
      [destruct us as [|? ?];
        [destruct cs as [|? ?]; [destruct copyins as [|? ?]|]|]|];
      try discriminate.
    destruct (errno_ret_in mprotect_errnos r) eqn:He.
    - destruct zs as [|? ?]; [|discriminate].
      inversion H; clear H; subst.
      apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
      eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
      rewrite Hvd, Hcover. apply alt_l.
      eapply bind_ok0; [apply (choose_ok _ e); exact HIn|]. apply pure_ok.
    - destruct (mprotect_budget_ok m addr
                  (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
                && w_is0 r
                && listNN_eqb zs
                     [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])
        eqn:HC; [|discriminate].
      inversion H; clear H; subst.
      apply andb_true_iff in HC as [HC Hzs].
      apply andb_true_iff in HC as [Hbudget Hr].
      unfold w_is0 in Hr. apply bv_eqb_eq in Hr; subst r.
      apply listNN_eqb_eq in Hzs; subst zs.
      eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
      rewrite Hvd, Hcover. apply alt_r.
      eapply bind_ok0; [apply (choose_ok _ tt); exact Hbudget|].
      eapply bind_ok0; [apply modify_ok|]. apply pure_ok. }
  destruct (map_contains (vm_maps (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
            && region_free (vm_noaccess (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hrw.
  2: discriminate.
  destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
    [destruct zs as [|? ?];
      [destruct us as [|? ?];
        [destruct cs as [|? ?]; [destruct copyins as [|? ?]|]|]|]|];
    try discriminate.
  destruct (w_is0 r) eqn:HC; [|discriminate].
  inversion H; clear H; subst.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
  rewrite Hvd, Hcover, Hrw.
  unfold w_is0 in HC. apply bv_eqb_eq in HC; subst. apply pure_ok.
Qed.

Lemma check_mprotect_sound_unmodeled : forall addr len prot eff m i,
  check_mprotect addr len prot eff m = CheckUnmodeled ->
  mprotect_spec addr len prot i m Unmodeled.
Proof.
  intros addr len prot [r ws zs us cs copyins] m i H.
  unfold check_mprotect in H. unfold mprotect_spec.
  destruct (mprotect_grows_conflict_b prot) eqn:Hgrows.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (w_is0 len) eqn:Hlen.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hbig.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (mprotect_modeled_b prot) eqn:Hprot; cbn [negb] in H.
  2: apply unmodeled_intro.
  cbv zeta in H.
  destruct (negb (region_free (vdso_reserved (m_kernel m) (vdso_top (m_vmmaps m)))
                   addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))) eqn:Hvd;
    [eapply bind_unmodeled2; [apply get_model_ok|];
     cbv beta iota zeta; rewrite Hvd; apply unmodeled_intro|].
  destruct (map_contains (vm_noaccess (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
            && map_contains (vm_maps (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hcover.
  { exfalso. destruct ws;
      [destruct us; [destruct cs; [destruct copyins|]|]|]; try discriminate.
    destruct (errno_ret_in mprotect_errnos r); [destruct zs; discriminate|].
    destruct (mprotect_budget_ok m addr
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
              && w_is0 r
              && listNN_eqb zs
                   [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]);
      discriminate. }
  destruct (map_contains (vm_maps (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
            && region_free (vm_noaccess (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hrw.
  { exfalso. destruct ws;
      [destruct zs;
        [destruct us; [destruct cs; [destruct copyins|]|]|]|];
      try discriminate.
    destruct (w_is0 r); discriminate. }
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota zeta.
  rewrite Hvd, Hcover, Hrw. apply unmodeled_intro.
Qed.

Lemma check_mprotect_complete_ok : forall addr len prot eff m m' evs i,
  mprotect_spec addr len prot i m (Ok eff m' evs) ->
  check_mprotect addr len prot eff m = CheckOk m' evs.
Proof.
  intros addr len prot eff m m' evs i H.
  unfold mprotect_spec in H. unfold check_mprotect.
  destruct (mprotect_grows_conflict_b prot) eqn:Hgrows.
  { sys_unfold. inv_ok. cbn; try rewrite bv_eqb_refl; reflexivity. }
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
  { sys_unfold. inv_ok. cbn; try rewrite bv_eqb_refl; reflexivity. }
  destruct (w_is0 len) eqn:Hlen.
  { sys_unfold. inv_ok. cbn; try rewrite bv_eqb_refl; reflexivity. }
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hbig.
  { sys_unfold. inv_ok. cbn; try rewrite bv_eqb_refl; reflexivity. }
  destruct (mprotect_modeled_b prot) eqn:Hprot; cbn [negb].
  2: { unfold unmodeled in H. discriminate. }
  cbv zeta.
  destruct (negb (region_free (vdso_reserved (m_kernel m) (vdso_top (m_vmmaps m)))
                   addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))) eqn:Hvd;
    [sys_unfold; cbv iota in H; inv_ok; rewrite Hvd in *; inv_ok|].
  destruct (map_contains (vm_noaccess (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
            && map_contains (vm_maps (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hcover.
  { sys_unfold. cbv iota in H. inv_ok. rewrite Hvd, Hcover in *. inv_ok.
    - cbv zeta.
      match goal with
      | |- context [errno_ret_in ?es (errno_ret ?e)] =>
          rewrite (errno_ret_in_intro es e) by assumption
      end.
      reflexivity.
    - cbv zeta.
      assert (He0 : errno_ret_in mprotect_errnos (Z_to_bv 64 0) = false)
        by reflexivity.
      rewrite He0.
      assert (Hbudget :
        mprotect_budget_ok m addr
          (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true)
        by assumption.
      rewrite Hbudget.
      unfold w_is0. rewrite bv_eqb_refl.
      rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity. }
  destruct (map_contains (vm_maps (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
            && region_free (vm_noaccess (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hrw.
  2: { sys_unfold. cbv iota in H. inv_ok.
       rewrite Hvd, Hcover, Hrw in *. inv_ok. }
  sys_unfold. cbv iota in H. inv_ok.
  rewrite Hvd, Hcover, Hrw in *. inv_ok.
  reflexivity.
Qed.

Lemma check_mprotect_complete_unmodeled : forall addr len prot m i eff,
  mprotect_spec addr len prot i m Unmodeled ->
  check_mprotect addr len prot eff m = CheckUnmodeled.
Proof.
  intros addr len prot m i eff H.
  unfold mprotect_spec in H. unfold check_mprotect.
  destruct (mprotect_grows_conflict_b prot) eqn:Hgrows.
  { sys_unfold. cbv iota in H. inv_ok; discriminate. }
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
  { sys_unfold. cbv iota in H. inv_ok; discriminate. }
  destruct (w_is0 len) eqn:Hlen.
  { sys_unfold. cbv iota in H. inv_ok; discriminate. }
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hbig.
  { sys_unfold. cbv iota in H. inv_ok; discriminate. }
  destruct (mprotect_modeled_b prot) eqn:Hprot; cbn [negb].
  2: reflexivity.
  cbv zeta.
  destruct (negb (region_free (vdso_reserved (m_kernel m) (vdso_top (m_vmmaps m)))
                   addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))) eqn:Hvd;
    [reflexivity|].
  destruct (map_contains (vm_noaccess (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
            && map_contains (vm_maps (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hcover.
  { sys_unfold. cbv iota in H. inv_ok. rewrite Hvd, Hcover in *. inv_ok. }
  destruct (map_contains (vm_maps (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
            && region_free (vm_noaccess (m_vmmaps m)) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hrw.
  2: reflexivity.
  sys_unfold. cbv iota in H. inv_ok.
  rewrite Hvd, Hcover, Hrw in *. inv_ok.
Qed.
