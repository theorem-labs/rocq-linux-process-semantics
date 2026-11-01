(** * LinuxProcessSem.Checks.Sys.Drivers.Char.Random — the getrandom (278) checkers, and their proofs

    Mirrors [Sys/Drivers/Char/Random.v], which answers to Linux
    [drivers/char/random.c]: this file holds the checkers for the
    syscalls defined there, and no others.

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

(** The acceptor for a getrandom call that MOVES NO BYTE: [r0] is the
    one answer besides the interrupted return — 0 for a zero-byte
    request the range test admits, -EFAULT for any range it refuses —
    and the interrupted return stays admissible either way, since
    [wait_for_random_bytes] runs before [import_ubuf]. *)
Definition check_getrandom_zero (r0 : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match eff with
  | mkEffectU r [] [] [] [] [] =>
      if errno_ret_in getrandom_errnos r || bv_eqb r r0 then CheckOk m []
      else CheckReject
  | _ => CheckReject
  end.

Definition check_getrandom (i : SyscallInput) (buf cap flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (Z.eqb (bv_unsigned flags) 0
           || Z.eqb (bv_unsigned flags) GRND_NONBLOCK) then CheckUnmodeled
  else
  if negb (modeled_rw_count cap) then CheckUnmodeled   (* see [rw_bytes_max] *)
  else
  match copy_bytes_map (in_wmem i) buf (bv_unsigned cap) with
  | None =>
      if negb (access_okb buf (bv_unsigned cap))
      then check_getrandom_zero (errno_ret EFAULT) eff m   (* [import_ubuf]'s [access_ok] *)
      else CheckUnmodeled   (* admitted, not wholly writable *)
  | Some _ =>
      if negb (w_is0 cap)
      then
        if (bv_unsigned cap <=? getrandom_small_max)%Z
        then
          (* the small request: full delivery at [buf], and nothing
             else — no short count, no -EINTR (see
             [Random.getrandom_small_max]) *)
          match eff with
          | mkEffectU r [(a, bs)] [] [] [] [] =>
              if bv_eqb a buf && bv_eqb r (len_word bs)
                 && (Z.of_nat (length bs) =? bv_unsigned cap)%Z
              then CheckOk m []
              else CheckReject
          | _ => CheckReject
          end
        else
          match eff with
          | mkEffectU r [] [] [] [] [] =>
              if errno_ret_in getrandom_errnos r then CheckOk m [] else CheckReject
          | mkEffectU r [(a, bs)] [] [] [] [] =>
              if bv_eqb a buf && bv_eqb r (len_word bs)
                 && (1 <=? Z.of_nat (length bs))%Z
                 && (Z.of_nat (length bs) <=? bv_unsigned cap)%Z
              then CheckOk m []
              else CheckReject
          | _ => CheckReject
          end
      else check_getrandom_zero (Z_to_bv 64 0) eff m
  end.

Lemma check_getrandom_zero_sound : forall r0 eff m m' evs,
  check_getrandom_zero r0 eff m = CheckOk m' evs ->
  m' = m /\ evs = [] /\
  ((exists e, In e getrandom_errnos /\ eff = mkEffect (errno_ret e) [] [])
   \/ eff = mkEffect r0 [] []).
Proof.
  intros r0 [r ws zs us cs copyins] m m' evs H. unfold check_getrandom_zero in H.
  destruct ws as [|? ?]; destruct zs as [|? ?]; destruct us as [|? ?];
    destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
  destruct (errno_ret_in getrandom_errnos r) eqn:He.
  - inversion H; subst.
    apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
    split; [reflexivity|split; [reflexivity|]].
    left. exists e. split; [exact HIn|reflexivity].
  - cbn [orb] in H. destruct (bv_eqb r r0) eqn:Hr; [|discriminate].
    apply bv_eqb_eq in Hr; subst r. inversion H; subst.
    split; [reflexivity|split; [reflexivity|]]. right. reflexivity.
Qed.

Lemma check_getrandom_sound_ok : forall i buf cap flags eff m m' evs,
  check_getrandom i buf cap flags eff m = CheckOk m' evs ->
  getrandom_spec buf cap flags i m (Ok eff m' evs).
Proof.
  intros i buf cap flags eff m m' evs H.
  unfold check_getrandom in H. unfold getrandom_spec.
  destruct (negb (Z.eqb (bv_unsigned flags) 0
                  || Z.eqb (bv_unsigned flags) GRND_NONBLOCK)) eqn:Hf;
    [discriminate|]. cbv iota.
  destruct (negb (modeled_rw_count cap)) eqn:Hn; [discriminate|]. cbv iota.
  destruct (copy_bytes_map (in_wmem i) buf (bv_unsigned cap)) as [bs0|] eqn:Hw.
  2: { (* the walk declined: a refused range answers -EFAULT beside
          -EINTR, and an admitted one the checker declines *)
       eapply bind_ok0; [apply input_ok|]. cbv beta. srw Hw.
       destruct (negb (access_okb buf (bv_unsigned cap))) eqn:Hs; cbv iota;
         [|discriminate].
       cbv iota in H. apply check_getrandom_zero_sound in H.
       destruct H as (-> & -> & [(e & HIn & He)|He]); subst eff.
       - apply alt_l. eapply bind_ok0; [apply (choose_ok _ e); exact HIn|].
         apply pure_ok.
       - apply alt_r. apply pure_ok. }
  eapply bind_ok0; [apply input_ok|]. cbv beta. srw Hw.
  destruct (negb (w_is0 cap)) eqn:Hc.
  - destruct (bv_unsigned cap <=? getrandom_small_max)%Z eqn:Hsm.
    { (* a small request: the full delivery, and only that *)
      destruct eff as [r ws zs us cs copyins]; destruct ws as [|[a bs] [|]];
        destruct zs as [|? ?]; destruct us as [|? ?];
        destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
      destruct (bv_eqb a buf && bv_eqb r (len_word bs)
                && (Z.of_nat (length bs) =? bv_unsigned cap)%Z) eqn:HC;
        [|discriminate].
      inversion H; clear H; subst.
      apply andb_true_iff in HC as [HC HD].
      apply andb_true_iff in HC as [HA HB].
      apply bv_eqb_eq in HA; subst a. apply bv_eqb_eq in HB; subst r.
      apply Z.eqb_eq in HD.
      eapply bind_ok0.
      { apply (choose_ok _ bs). cbv beta. exact HD. }
      apply pure_ok. }
    (* a large request: the interrupted return or a nonempty delivery *)
    destruct eff as [r ws zs us cs copyins]; destruct ws as [|[a bs] [|]];
      destruct zs as [|? ?]; destruct us as [|? ?];
      destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
    + destruct (errno_ret_in getrandom_errnos r) eqn:He; [|discriminate].
      inversion H; clear H; subst.
      apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
      apply alt_l. eapply bind_ok0.
      { apply (choose_ok _ e). exact HIn. }
      apply pure_ok.
    + destruct (bv_eqb a buf && bv_eqb r (len_word bs)
                && (1 <=? Z.of_nat (length bs))%Z
                && (Z.of_nat (length bs) <=? bv_unsigned cap)%Z) eqn:HC;
        [|discriminate].
      inversion H; clear H; subst.
      apply andb_true_iff in HC as [HC HE].
      apply andb_true_iff in HC as [HC HD].
      apply andb_true_iff in HC as [HA HB].
      apply bv_eqb_eq in HA; subst a. apply bv_eqb_eq in HB; subst r.
      apply Z.leb_le in HD. apply Z.leb_le in HE.
      apply alt_r.
      eapply bind_ok0.
      { apply (choose_ok _ bs). cbv beta. split; assumption. }
      apply pure_ok.
  - (* a zero-byte request on an admitted range: 0 beside -EINTR *)
    apply check_getrandom_zero_sound in H.
    destruct H as (-> & -> & [(e & HIn & He)|He]); subst eff.
    + apply alt_l. eapply bind_ok0; [apply (choose_ok _ e); exact HIn|].
      apply pure_ok.
    + apply alt_r. apply pure_ok.
Qed.

Lemma check_getrandom_zero_no_unmodeled : forall r0 eff m,
  check_getrandom_zero r0 eff m <> CheckUnmodeled.
Proof.
  intros r0 [r ws zs us cs copyins] m. unfold check_getrandom_zero.
  destruct ws as [|? ?]; destruct zs as [|? ?]; destruct us as [|? ?];
    destruct cs as [|? ?]; destruct copyins as [|? ?]; try discriminate.
  destruct (errno_ret_in getrandom_errnos r || bv_eqb r r0); discriminate.
Qed.

Lemma check_getrandom_sound_unmodeled : forall i buf cap flags eff m,
  check_getrandom i buf cap flags eff m = CheckUnmodeled ->
  getrandom_spec buf cap flags i m Unmodeled.
Proof.
  intros i buf cap flags [r ws zs us cs copyins] m H. unfold check_getrandom in H.
  unfold getrandom_spec.
  destruct (negb (Z.eqb (bv_unsigned flags) 0
                  || Z.eqb (bv_unsigned flags) GRND_NONBLOCK)) eqn:Hf.
  { cbv iota. apply unmodeled_intro. }
  cbv iota. cbv iota in H.
  destruct (negb (modeled_rw_count cap)) eqn:Hn.
  { cbv iota. apply unmodeled_intro. }
  cbv iota. cbv iota in H.
  destruct (copy_bytes_map (in_wmem i) buf (bv_unsigned cap)) as [bs0|] eqn:Hw.
  - eapply bind_unmodeled2; [apply input_ok|]. cbv beta. srw Hw.
    destruct (negb (w_is0 cap)) eqn:Hc.
    + destruct (bv_unsigned cap <=? getrandom_small_max)%Z eqn:Hsm;
        destruct ws as [|[a bs] [|]]; destruct zs as [|? ?];
        destruct us as [|? ?]; destruct cs as [|? ?];
        destruct copyins as [|? ?]; try discriminate.
      * destruct (bv_eqb a buf && bv_eqb r (len_word bs)
                  && (Z.of_nat (length bs) =? bv_unsigned cap)%Z); discriminate.
      * destruct (errno_ret_in getrandom_errnos r); discriminate.
      * destruct (bv_eqb a buf && bv_eqb r (len_word bs)
                  && (1 <=? Z.of_nat (length bs))%Z
                  && (Z.of_nat (length bs) <=? bv_unsigned cap)%Z); discriminate.
    + now apply check_getrandom_zero_no_unmodeled in H.
  - eapply bind_unmodeled2; [apply input_ok|]. cbv beta. srw Hw.
    destruct (negb (access_okb buf (bv_unsigned cap))) eqn:Hs; cbv iota in H |- *.
    + now apply check_getrandom_zero_no_unmodeled in H.
    + apply unmodeled_intro.
Qed.

Lemma check_getrandom_complete_ok : forall i buf cap flags eff m m' evs,
  getrandom_spec buf cap flags i m (Ok eff m' evs) ->
  check_getrandom i buf cap flags eff m = CheckOk m' evs.
Proof.
  intros i buf cap flags eff m m' evs H.
  unfold getrandom_spec in H. unfold check_getrandom. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (negb (Z.eqb (bv_unsigned flags) 0
                  || Z.eqb (bv_unsigned flags) GRND_NONBLOCK)) eqn:Hf; hall Hf;
    inv_ok.
  destruct (negb (modeled_rw_count cap)) eqn:Hn; hall Hn; inv_ok.
  destruct (copy_bytes_map (in_wmem i) buf (bv_unsigned cap)) as [bs0|] eqn:Hw;
    hall Hw; inv_ok.
  - (* the walk answered *)
    destruct (negb (w_is0 cap)) eqn:Hc; hall Hc; inv_ok.
    all: try (destruct (bv_unsigned cap <=? getrandom_small_max)%Z eqn:Hsm;
              hall Hsm; inv_ok).
    all: unfold check_getrandom_zero; cbv beta iota zeta in *.
    all: try solve [ match goal with
                     | |- context [errno_ret_in ?es (errno_ret ?e)] =>
                         rewrite (errno_ret_in_intro es e) by assumption
                     end; reflexivity ].
    all: try solve [ bool_true; cbn; reflexivity ].
    all: rewrite bv_eqb_refl, Bool.orb_true_r; reflexivity.
  - (* the walk declined: only a range [access_okb] refuses is answered *)
    destruct (negb (access_okb buf (bv_unsigned cap))) eqn:Hs; hall Hs; inv_ok.
    all: unfold check_getrandom_zero; cbv beta iota zeta in *.
    all: try solve [ match goal with
                     | |- context [errno_ret_in ?es (errno_ret ?e)] =>
                         rewrite (errno_ret_in_intro es e) by assumption
                     end; reflexivity ].
    all: rewrite bv_eqb_refl, Bool.orb_true_r; reflexivity.
Qed.

Lemma check_getrandom_complete_unmodeled : forall i buf cap flags m eff,
  getrandom_spec buf cap flags i m Unmodeled ->
  check_getrandom i buf cap flags eff m = CheckUnmodeled.
Proof.
  intros i buf cap flags m eff H.
  unfold getrandom_spec in H. unfold check_getrandom. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (negb (Z.eqb (bv_unsigned flags) 0
                  || Z.eqb (bv_unsigned flags) GRND_NONBLOCK)) eqn:Hf; hall Hf;
    inv_ok.
  - (* unmodeled flags: both sides fail closed *) reflexivity.
  - destruct (negb (modeled_rw_count cap)) eqn:Hn; hall Hn; inv_ok.
    + (* over the transfer bound: both sides fail closed *) reflexivity.
    + destruct (copy_bytes_map (in_wmem i) buf (bv_unsigned cap)) as [bs0|] eqn:Hw;
        hall Hw; inv_ok.
      * cbv zeta in *.
        destruct (negb (w_is0 cap)) eqn:Hc; hall Hc; inv_ok; try discriminate.
        destruct (bv_unsigned cap <=? getrandom_small_max)%Z eqn:Hsm; hall Hsm;
          inv_ok; discriminate.
      * (* the walk declined: a refused range answers, an admitted one
           declines on both sides *)
        destruct (negb (access_okb buf (bv_unsigned cap))) eqn:Hs; hall Hs;
          inv_ok; try discriminate; reflexivity.
Qed.

(* ------------------------------------------------------------------ exit *)
