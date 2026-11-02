(** * LinuxProcessSem.Checks.BudgetPremiseMremap — the mremap budget mark on invariant states

    Not part of the trusted specification.  The mremap twin of
    [BudgetPremise.mmap_budget_refused_is_refusal]: where the mark
    [Mremap.mremap_budget_refused_b] fires, every outcome
    [Mremap.mremap_spec] admits is one of [Run.refusal_b]'s refusals, an
    errno in [Mremap.mremap_errnos].  The marked request is a grow past
    every argument gate, so the spec's [Ok] arms are three: the injected
    errno, the in-place grow and the move.  The in-place grow is excluded
    on every state ([BudgetPremise.mremap_budget_refused_refuses_inplace]).
    The move is excluded at every destination that carries no backing
    metadata ([BudgetPremise.mremap_budget_refused_refuses_move]), and on
    the states this file takes every fresh destination is such a one:
    [NoaccessOwned.sys_inv] gives the fit of the live mappings
    ([MapsFit.vm_fit]) and [State.noaccess_pages_owned], hence
    a fresh destination meets no protected byte
    ([BudgetPremise.fresh_dst_avoids_noaccess]); and with both lazy
    ledgers ([m_vm_lazy], [m_vm_materialized]) empty the two lazy-ledger
    identities hold by computation. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs BudgetPremise MapsFit NoaccessOwned.
Import ListNotations.
Open Scope bv_scope.

Lemma mremap_dispatch : forall i m o,
  bv_unsigned (in_sysno i) = 216%Z ->
  syscall_spec i m o
  <-> mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o.
Proof.
  intros i m o E. unfold syscall_spec, dispatch. rewrite E. reflexivity.
Qed.

(** Where the mark fires AND there is no room above the source, on a
    [sys_inv] state with empty lazy ledgers, [Mremap.mremap_fresh_b]
    admits no destination at all.

    The no-room premise is not a weakening: since the placement change
    the grow has one non-errno resolution, chosen by the room test, so
    with room above the source Linux expands there and there is no
    move for this lemma to refuse (mm/mremap.c,
    [vrm_can_expand_in_place], Linux v6.18.46, commit 1f99e9ab748f).
    The caller covers that case with
    [BudgetPremise.mremap_budget_refused_refuses_inplace]. *)
Lemma mremap_budget_refused_no_fresh_sys_inv :
  forall old old_size new_size flags m dst,
  sys_inv (m_vmmaps m) ->
  m_vm_lazy m = [] ->
  m_vm_materialized m = [] ->
  mremap_inplace_room_b m old
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))
    (page_round_up_Z (bv_unsigned old_size))
    (page_round_up_Z (bv_unsigned new_size)) = false ->
  mremap_budget_refused_b old old_size new_size flags m = true ->
  mremap_fresh_b m
    (page_round_up_Z (bv_unsigned old_size))
    (page_round_up_Z (bv_unsigned new_size)) old
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) dst
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) = false.
Proof.
  intros old old_size new_size flags m dst Hinv Hlz Hmat Hnoroom Hmark.
  destruct (mremap_budget_refused_inv _ _ _ _ _ Hmark)
    as (_ & _ & Hnew & _ & _ & _ & Hgrow & _ & _).
  pose proof (sys_inv_noaccess_pages_owned _ Hinv) as Hown.
  destruct Hinv as (_ & Hfit & _).
  destruct (mremap_fresh_b m
              (page_round_up_Z (bv_unsigned old_size))
              (page_round_up_Z (bv_unsigned new_size)) old
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) dst
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))) eqn:Hf;
    [exfalso | reflexivity].
  pose proof Hf as Hf0.
  unfold mremap_fresh_b in Hf0. cbv zeta in Hf0.
  rewrite !Bool.andb_true_iff in Hf0.
  destruct Hf0 as (((((_ & Hdalign) & _) & _) & Hdfree) & _).
  apply Z.eqb_eq in Hdalign.
  pose proof (page_align_is0_b_false_word new_size Hnew) as Hnw.
  pose proof (page_round_up_Z_mod (bv_unsigned new_size)) as Hnmod.
  pose proof (page_round_up_Z_nonneg (bv_unsigned old_size)
                (proj1 (bv_unsigned_in_range 64 old_size))) as Honn.
  assert (Hpos : (0 < bv_unsigned
                        (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))))%Z)
    by (rewrite Hnw; lia).
  assert (Hmod : (bv_unsigned
                    (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))
                  mod page_size = 0)%Z)
    by (rewrite Hnw; exact Hnmod).
  rewrite (mremap_budget_refused_refuses_move old old_size new_size flags m dst
             Hfit
             (fresh_dst_avoids_noaccess _ _ _ Hown Hpos Hmod Hdalign Hdfree)
             ltac:(rewrite Hlz; reflexivity)
             ltac:(rewrite Hmat; reflexivity)
             Hnoroom Hmark) in Hf.
  discriminate Hf.
Qed.

(** SOUNDNESS over the whole arm, on invariant states: where the mark
    fires, every admitted outcome is a refusal.  The walk takes
    [Mremap.mremap_spec]'s gates in order under the facts
    [BudgetPremise.mremap_budget_refused_inv] reads off the mark.

    THE WALK NOW SPLITS ON THE ROOM TEST, because the grow has one
    non-errno resolution and the room test chooses it (mm/mremap.c,
    [vrm_can_expand_in_place], Linux v6.18.46, commit 1f99e9ab748f).
    With room above the source the only answer besides the injected
    errno is the in-place one, and the mark says its charge failed, so
    its [choose] is empty.  Without room the only answer is the move,
    and no destination is fresh
    ([mremap_budget_refused_no_fresh_sys_inv]). *)
Lemma mremap_budget_refused_is_refusal_sys_inv : forall i m eff m' evs,
  sys_inv (m_vmmaps m) ->
  m_vm_lazy m = [] ->
  m_vm_materialized m = [] ->
  bv_unsigned (in_sysno i) = 216%Z ->
  alloc_budget_refused_b i m = true ->
  syscall_spec i m (Ok eff m' evs) ->
  refusal_b i m (eff_ret eff) = true.
Proof.
  intros i m eff m' evs Hinv Hlz Hmat E Hmark Hspec.
  unfold alloc_budget_refused_b in Hmark. rewrite E in Hmark.
  cbn [Z.eqb Pos.eqb] in Hmark.
  destruct (mremap_budget_refused_inv _ _ _ _ _ Hmark)
    as (Hfl & Hal & Hnew & Htask & Hold & Hsrc & Hgrow & Hip & Hcase).
  apply (proj1 (mremap_dispatch i m _ E)) in Hspec.
  unfold refusal_b. rewrite E. cbv zeta.
  assert (Hne : (216 =? 214)%Z = false) by reflexivity. rewrite Hne.
  assert (Harm : injected_arm 216 = Some (mkInjectedArm 216 FamAlloc mremap_errnos))
    by reflexivity.
  rewrite Harm. cbn [ia_errnos].
  unfold mremap_spec in Hspec.
  rewrite Hfl, Hal, Hnew, Htask, Hold in Hspec. cbn [negb] in Hspec.
  apply (proj1 (bind_get_model _ i m _)) in Hspec. cbv beta zeta in Hspec.
  rewrite Hsrc in Hspec. cbn [negb] in Hspec.
  assert (Heq : (page_round_up_Z (bv_unsigned (in_arg i 1))
                 =? page_round_up_Z (bv_unsigned (in_arg i 2)))%Z = false)
    by (apply Z.eqb_neq; lia).
  assert (Hlt : (page_round_up_Z (bv_unsigned (in_arg i 2))
                 <? page_round_up_Z (bv_unsigned (in_arg i 1)))%Z = false)
    by (apply Z.ltb_ge; lia).
  rewrite Heq, Hlt in Hspec.
  destruct (mremap_inplace_room_b m (in_arg i 0)
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))))
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 2))))
              (page_round_up_Z (bv_unsigned (in_arg i 1)))
              (page_round_up_Z (bv_unsigned (in_arg i 2)))) eqn:Hroom;
    cbv iota in Hcase;
    cbv beta iota zeta in Hspec;
    unfold alt, bind, errno_from, choose, err_ret, ret_only, pure, modify
      in Hspec;
    cbv beta iota zeta in Hspec; sys_destruct.
  - (* room: the injected errno *)
    match goal with
    | [ Hin : In ?e mremap_errnos |- _ ] =>
        destruct Hin as [<- | []]; vm_compute; reflexivity
    end.
  - (* room: the in-place answer, whose charge the mark says refused *)
    exfalso.
    match goal with
    | [ Hb : mremap_final_budget_b _ _ _ _ _ = true |- _ ] =>
        rewrite Hcase in Hb; discriminate Hb
    end.
  - (* no room: the injected errno *)
    match goal with
    | [ Hin : In ?e mremap_errnos |- _ ] =>
        destruct Hin as [<- | []]; vm_compute; reflexivity
    end.
  - (* no room: the move, and no destination is fresh *)
    exfalso.
    match goal with
    | [ Hd : mremap_dst_ok _ _ _ _ _ ?d _ |- _ ] =>
        destruct Hd as [_ Hf];
        rewrite (mremap_budget_refused_no_fresh_sys_inv _ _ _ _ _ d
                   Hinv Hlz Hmat Hroom Hmark) in Hf;
        discriminate Hf
    end.
Qed.
