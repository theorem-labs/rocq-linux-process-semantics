(** * LinuxProcessSem.Checks.Sys.Kernel.Capability — the capget (90) and capset (91) checkers, and their proofs

    Mirrors [Sys/Kernel/Capability.v], which answers to Linux
    [kernel/capability.c]: this file holds the checkers for the syscalls
    defined there, and no others.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export
  Prelude.

(** The two header reads, and for [capset] the data read, in the order
    the kernel performs them. *)
Definition cap_header_reads (header : word) : list (word * nat) :=
  [(header, 4%nat); (header + Z_to_bv 64 4, 4%nat)].

(* ----------------------------------------------------------------- capget *)

(** The copy-out, once every gate has passed: one write of a data image
    [capget_data_ok] admits at [dataptr], return 0, the two header reads
    on the ledger, and the model untouched. *)
Definition check_capget_copy (dataptr : word)
    (reads : list (word * nat)) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match eff with
  | mkEffectU r [(a, bs)] [] [] [] cis =>
      if bv_eqb r (Z_to_bv 64 0) && bv_eqb a dataptr
         && capget_data_ok bs && access_ranges_eqb cis reads
      then CheckOk m [] else CheckReject
  | _ => CheckReject
  end.

Lemma check_capget_copy_no_unmodeled : forall dataptr reads eff m,
  check_capget_copy dataptr reads eff m <> CheckUnmodeled.
Proof.
  intros dataptr reads [r ws zs us cs cis] m H.
  unfold check_capget_copy in H.
  destruct ws as [|[a bs] [|? ?]]; try discriminate.
  destruct zs as [|? ?]; [|discriminate].
  destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct (bv_eqb r (Z_to_bv 64 0) && bv_eqb a dataptr
            && capget_data_ok bs && access_ranges_eqb cis reads);
    discriminate.
Qed.

(** [Kernel.Capability.capget_spec] carries the argument; this mirrors
    its branch structure one for one. *)
Definition check_capget (i : SyscallInput) (header dataptr : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (access_okb header 4) then check_ret_only eff (errno_ret EFAULT) m []
  else
    match read_bytes_map (in_mem i) header (Z_to_bv 64 4) with
    | None => CheckUnmodeled
    | Some vb =>
        if negb (Z.eqb (bytes_le_to_Z vb) LINUX_CAPABILITY_VERSION_3)
        then CheckUnmodeled
        else if w_is0 dataptr
        then check_ret_only_copyins [(header, 4%nat)] eff (Z_to_bv 64 0) m []
        else if negb (access_okb (header + Z_to_bv 64 4) 4)
        then check_ret_only_copyins [(header, 4%nat)] eff (errno_ret EFAULT) m []
        else
          match read_bytes_map (in_mem i) (header + Z_to_bv 64 4) (Z_to_bv 64 4) with
          | None => CheckUnmodeled
          | Some pb =>
              if negb (Z.eqb (bytes_le_to_Z pb) 0) then CheckUnmodeled
              else if negb (access_okb dataptr CAP_V3_DATA_SIZE)
              then check_ret_only_copyins (cap_header_reads header)
                     eff (errno_ret EFAULT) m []
              else
                match read_bytes_map (in_wmem i) dataptr
                        (Z_to_bv 64 CAP_V3_DATA_SIZE) with
                | None => CheckUnmodeled
                | Some _ =>
                    if cap_permitted_nonempty_b (m_creds m) then CheckUnmodeled
                    else check_capget_copy dataptr (cap_header_reads header) eff m
                end
          end
    end.

Lemma check_capget_sound_ok : forall i header dataptr eff m m' evs,
  check_capget i header dataptr eff m = CheckOk m' evs ->
  capget_spec header dataptr i m (Ok eff m' evs).
Proof.
  intros i header dataptr eff m m' evs H.
  unfold check_capget in H. unfold capget_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (negb (access_okb header 4)) eqn:Ha; cbv iota in H |- *.
  { apply check_ret_only_ok_iff in H as (-> & -> & ->).
    unfold err_ret, ret_only. apply pure_ok. }
  destruct (read_bytes_map (in_mem i) header (Z_to_bv 64 4)) as [vb|] eqn:Hv;
    cbv iota in H |- *; [|discriminate].
  destruct (negb (Z.eqb (bytes_le_to_Z vb) LINUX_CAPABILITY_VERSION_3)) eqn:Hver;
    cbv iota in H |- *; [discriminate|].
  destruct (w_is0 dataptr) eqn:Hd; cbv iota in H |- *.
  { apply check_ret_only_copyins_ok_iff in H as (-> & -> & ->).
    apply record_copyins_ok_empty; [reflexivity|].
    unfold ret_only. apply pure_ok. }
  destruct (negb (access_okb (header + Z_to_bv 64 4) 4)) eqn:Ha2;
    cbv iota in H |- *.
  { apply check_ret_only_copyins_ok_iff in H as (-> & -> & ->).
    apply record_copyins_ok_empty; [reflexivity|].
    unfold err_ret, ret_only. apply pure_ok. }
  destruct (read_bytes_map (in_mem i) (header + Z_to_bv 64 4) (Z_to_bv 64 4))
    as [pb|] eqn:Hp; cbv iota in H |- *; [|discriminate].
  destruct (negb (Z.eqb (bytes_le_to_Z pb) 0)) eqn:Hz;
    cbv iota in H |- *; [discriminate|].
  destruct (negb (access_okb dataptr CAP_V3_DATA_SIZE)) eqn:Ha3;
    cbv iota in H |- *.
  { apply check_ret_only_copyins_ok_iff in H as (-> & -> & ->).
    apply (record_copyins_ok_eq _ _ i m
             (with_copyins [(header + Z_to_bv 64 4, 4%nat)]
                (mkEffect (errno_ret EFAULT) [] []))); [reflexivity|].
    apply record_copyins_ok_empty; [reflexivity|].
    unfold err_ret, ret_only. apply pure_ok. }
  destruct (read_bytes_map (in_wmem i) dataptr (Z_to_bv 64 CAP_V3_DATA_SIZE))
    as [wb|] eqn:Hw; cbv iota in H |- *; [|discriminate].
  destruct (cap_permitted_nonempty_b (m_creds m)) eqn:Hroot;
    cbv iota in H |- *; [discriminate|].
  unfold check_capget_copy in H.
  destruct eff as [r ws zs us cs cis].
  destruct ws as [|[a bs] [|? ?]]; try discriminate.
  destruct zs as [|? ?]; [|discriminate].
  destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct (bv_eqb r (Z_to_bv 64 0) && bv_eqb a dataptr
            && capget_data_ok bs
            && access_ranges_eqb cis (cap_header_reads header)) eqn:Hok;
    [|discriminate].
  cbv iota in H. injection H as Hm Hevs. subst m' evs.
  apply andb_true_iff in Hok as [Hok Hcis].
  apply andb_true_iff in Hok as [Hok Hdata].
  apply andb_true_iff in Hok as [Hr Ha'].
  apply bv_eqb_eq in Hr. apply bv_eqb_eq in Ha'.
  apply access_ranges_eqb_eq in Hcis. subst r a cis.
  apply (record_copyins_ok_eq _ _ i m
           (with_copyins [(header + Z_to_bv 64 4, 4%nat)]
              (mkEffect (Z_to_bv 64 0) [(dataptr, bs)] []))); [reflexivity|].
  apply record_copyins_ok_empty; [reflexivity|].
  eapply bind_ok0; [apply (choose_ok _ bs); exact Hdata|].
  apply pure_ok.
Qed.

Lemma check_capget_sound_unmodeled : forall i header dataptr eff m,
  check_capget i header dataptr eff m = CheckUnmodeled ->
  capget_spec header dataptr i m Unmodeled.
Proof.
  intros i header dataptr eff m H.
  unfold check_capget in H. unfold capget_spec.
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (negb (access_okb header 4)) eqn:Ha; cbv iota in H |- *.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (read_bytes_map (in_mem i) header (Z_to_bv 64 4)) as [vb|] eqn:Hv;
    cbv iota in H |- *; [|apply unmodeled_intro].
  apply record_copyins_unmodeled.
  destruct (negb (Z.eqb (bytes_le_to_Z vb) LINUX_CAPABILITY_VERSION_3)) eqn:Hver;
    cbv iota in H |- *; [apply unmodeled_intro|].
  destruct (w_is0 dataptr) eqn:Hd; cbv iota in H |- *.
  { now apply check_ret_only_copyins_no_unmodeled in H. }
  destruct (negb (access_okb (header + Z_to_bv 64 4) 4)) eqn:Ha2;
    cbv iota in H |- *.
  { now apply check_ret_only_copyins_no_unmodeled in H. }
  destruct (read_bytes_map (in_mem i) (header + Z_to_bv 64 4) (Z_to_bv 64 4))
    as [pb|] eqn:Hp; cbv iota in H |- *; [|apply unmodeled_intro].
  apply record_copyins_unmodeled.
  destruct (negb (Z.eqb (bytes_le_to_Z pb) 0)) eqn:Hz;
    cbv iota in H |- *; [apply unmodeled_intro|].
  destruct (negb (access_okb dataptr CAP_V3_DATA_SIZE)) eqn:Ha3;
    cbv iota in H |- *.
  { now apply check_ret_only_copyins_no_unmodeled in H. }
  destruct (read_bytes_map (in_wmem i) dataptr (Z_to_bv 64 CAP_V3_DATA_SIZE))
    as [wb|] eqn:Hw; cbv iota in H |- *; [|apply unmodeled_intro].
  destruct (cap_permitted_nonempty_b (m_creds m)) eqn:Hroot;
    cbv iota in H |- *; [apply unmodeled_intro|].
  exfalso. now apply check_capget_copy_no_unmodeled in H.
Qed.

Lemma check_capget_complete_ok : forall i header dataptr eff m m' evs,
  capget_spec header dataptr i m (Ok eff m' evs) ->
  check_capget i header dataptr eff m = CheckOk m' evs.
Proof.
  intros i header dataptr eff m m' evs H.
  unfold capget_spec in H. unfold check_capget.
  apply input_bind_ok_inv in H. cbv beta in H.
  apply get_model_bind_ok_inv in H. cbv beta in H.
  destruct (negb (access_okb header 4)) eqn:Ha; cbv iota in H |- *.
  { unfold err_ret, ret_only, pure in H. inversion H; subst.
    now apply check_ret_only_ok_iff. }
  destruct (read_bytes_map (in_mem i) header (Z_to_bv 64 4)) as [vb|] eqn:Hv;
    cbv iota in H |- *; [|unfold unmodeled in H; discriminate].
  apply record_copyins_ok_inv in H as (c1 & H & ->).
  destruct (negb (Z.eqb (bytes_le_to_Z vb) LINUX_CAPABILITY_VERSION_3)) eqn:Hver;
    cbv iota in H |- *; [unfold unmodeled in H; discriminate|].
  destruct (w_is0 dataptr) eqn:Hd; cbv iota in H |- *.
  { unfold ret_only, pure in H. inversion H; subst.
    apply check_ret_only_copyins_ok_iff. now repeat split. }
  destruct (negb (access_okb (header + Z_to_bv 64 4) 4)) eqn:Ha2;
    cbv iota in H |- *.
  { unfold err_ret, ret_only, pure in H. inversion H; subst.
    apply check_ret_only_copyins_ok_iff. now repeat split. }
  destruct (read_bytes_map (in_mem i) (header + Z_to_bv 64 4) (Z_to_bv 64 4))
    as [pb|] eqn:Hp; cbv iota in H |- *; [|unfold unmodeled in H; discriminate].
  apply record_copyins_ok_inv in H as (c2 & H & ->).
  destruct (negb (Z.eqb (bytes_le_to_Z pb) 0)) eqn:Hz;
    cbv iota in H |- *; [unfold unmodeled in H; discriminate|].
  destruct (negb (access_okb dataptr CAP_V3_DATA_SIZE)) eqn:Ha3;
    cbv iota in H |- *.
  { unfold err_ret, ret_only, pure in H. inversion H; subst.
    apply check_ret_only_copyins_ok_iff. now repeat split. }
  destruct (read_bytes_map (in_wmem i) dataptr (Z_to_bv 64 CAP_V3_DATA_SIZE))
    as [wb|] eqn:Hw; cbv iota in H |- *; [|unfold unmodeled in H; discriminate].
  destruct (cap_permitted_nonempty_b (m_creds m)) eqn:Hroot;
    cbv iota in H |- *; [unfold unmodeled in H; discriminate|].
  unfold bind in H. cbv beta iota in H.
  destruct H as (bs & m1 & e1 & e2 & Hch & Hpure & Hevs).
  unfold choose in Hch. destruct Hch as (x & Hx & Hch). cbv beta in Hx.
  inversion Hch; subst; clear Hch.
  unfold pure in Hpure. inversion Hpure; subst; clear Hpure.
  unfold check_capget_copy, with_copyins, cap_header_reads.
  cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins app].
  rewrite !bv_eqb_refl, Hx, access_ranges_eqb_refl. reflexivity.
Qed.

Lemma check_capget_complete_unmodeled : forall i header dataptr m eff,
  capget_spec header dataptr i m Unmodeled ->
  check_capget i header dataptr eff m = CheckUnmodeled.
Proof.
  intros i header dataptr m eff H.
  unfold capget_spec in H. unfold check_capget.
  apply input_bind_unmodeled_inv in H. cbv beta in H.
  apply get_model_bind_unmodeled_inv in H. cbv beta in H.
  destruct (negb (access_okb header 4)) eqn:Ha; cbv iota in H |- *.
  { unfold err_ret, ret_only, pure in H. discriminate. }
  destruct (read_bytes_map (in_mem i) header (Z_to_bv 64 4)) as [vb|] eqn:Hv;
    cbv iota in H |- *; [|reflexivity].
  apply record_copyins_unmodeled_inv in H.
  destruct (negb (Z.eqb (bytes_le_to_Z vb) LINUX_CAPABILITY_VERSION_3)) eqn:Hver;
    cbv iota in H |- *; [reflexivity|].
  destruct (w_is0 dataptr) eqn:Hd; cbv iota in H |- *.
  { unfold ret_only, pure in H. discriminate. }
  destruct (negb (access_okb (header + Z_to_bv 64 4) 4)) eqn:Ha2;
    cbv iota in H |- *.
  { unfold err_ret, ret_only, pure in H. discriminate. }
  destruct (read_bytes_map (in_mem i) (header + Z_to_bv 64 4) (Z_to_bv 64 4))
    as [pb|] eqn:Hp; cbv iota in H |- *; [|reflexivity].
  apply record_copyins_unmodeled_inv in H.
  destruct (negb (Z.eqb (bytes_le_to_Z pb) 0)) eqn:Hz;
    cbv iota in H |- *; [reflexivity|].
  destruct (negb (access_okb dataptr CAP_V3_DATA_SIZE)) eqn:Ha3;
    cbv iota in H |- *.
  { unfold err_ret, ret_only, pure in H. discriminate. }
  destruct (read_bytes_map (in_wmem i) dataptr (Z_to_bv 64 CAP_V3_DATA_SIZE))
    as [wb|] eqn:Hw; cbv iota in H |- *; [|reflexivity].
  destruct (cap_permitted_nonempty_b (m_creds m)) eqn:Hroot;
    cbv iota in H |- *; [reflexivity|].
  exfalso. unfold bind, choose, pure in H. cbv beta iota in H.
  destruct H as [(x & _ & Hc)|(x & m1 & e1 & _ & Hk)]; discriminate.
Qed.

(* ----------------------------------------------------------------- capset *)

(** The three reads on the ledger, in the kernel's order. *)
Definition capset_reads (header data : word) : list (word * nat) :=
  cap_header_reads header ++ [(data, Z.to_nat CAP_V3_DATA_SIZE)].

(** [Kernel.Capability.capset_spec] carries the argument; this mirrors
    its branch structure one for one.  The two answers of the one
    answered shape are told apart by the observed return. *)
Definition check_capset (i : SyscallInput) (header data : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (access_okb header 4) then check_ret_only eff (errno_ret EFAULT) m []
  else
    match read_bytes_map (in_mem i) header (Z_to_bv 64 4) with
    | None => CheckUnmodeled
    | Some vb =>
        if negb (Z.eqb (bytes_le_to_Z vb) LINUX_CAPABILITY_VERSION_3)
        then CheckUnmodeled
        else if negb (access_okb (header + Z_to_bv 64 4) 4)
        then check_ret_only_copyins [(header, 4%nat)] eff (errno_ret EFAULT) m []
        else
          match read_bytes_map (in_mem i) (header + Z_to_bv 64 4) (Z_to_bv 64 4) with
          | None => CheckUnmodeled
          | Some pb =>
              if negb (Z.eqb (bytes_le_to_Z pb) 0) then CheckUnmodeled
              else if negb (access_okb data CAP_V3_DATA_SIZE)
              then check_ret_only_copyins (cap_header_reads header)
                     eff (errno_ret EFAULT) m []
              else
                match read_bytes_map (in_mem i) data (Z_to_bv 64 CAP_V3_DATA_SIZE) with
                | None => CheckUnmodeled
                | Some db =>
                    if negb (Z.eqb (bytes_le_to_Z db) 0) then CheckUnmodeled
                    else if cap_permitted_nonempty_b (m_creds m) then CheckUnmodeled
                    else if bv_eqb (eff_ret eff) (errno_ret ENOMEM)
                    then check_ret_only_copyins (capset_reads header data)
                           eff (errno_ret ENOMEM) m []
                    else check_ret_only_copyins (capset_reads header data)
                           eff (Z_to_bv 64 0) m []
                end
          end
    end.

Lemma check_capset_sound_ok : forall i header data eff m m' evs,
  check_capset i header data eff m = CheckOk m' evs ->
  capset_spec header data i m (Ok eff m' evs).
Proof.
  intros i header data eff m m' evs H.
  unfold check_capset in H. unfold capset_spec.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (negb (access_okb header 4)) eqn:Ha; cbv iota in H |- *.
  { apply check_ret_only_ok_iff in H as (-> & -> & ->).
    unfold err_ret, ret_only. apply pure_ok. }
  destruct (read_bytes_map (in_mem i) header (Z_to_bv 64 4)) as [vb|] eqn:Hv;
    cbv iota in H |- *; [|discriminate].
  destruct (negb (Z.eqb (bytes_le_to_Z vb) LINUX_CAPABILITY_VERSION_3)) eqn:Hver;
    cbv iota in H |- *; [discriminate|].
  destruct (negb (access_okb (header + Z_to_bv 64 4) 4)) eqn:Ha2;
    cbv iota in H |- *.
  { apply check_ret_only_copyins_ok_iff in H as (-> & -> & ->).
    apply record_copyins_ok_empty; [reflexivity|].
    unfold err_ret, ret_only. apply pure_ok. }
  destruct (read_bytes_map (in_mem i) (header + Z_to_bv 64 4) (Z_to_bv 64 4))
    as [pb|] eqn:Hp; cbv iota in H |- *; [|discriminate].
  destruct (negb (Z.eqb (bytes_le_to_Z pb) 0)) eqn:Hz;
    cbv iota in H |- *; [discriminate|].
  destruct (negb (access_okb data CAP_V3_DATA_SIZE)) eqn:Ha3;
    cbv iota in H |- *.
  { apply check_ret_only_copyins_ok_iff in H as (-> & -> & ->).
    apply (record_copyins_ok_eq _ _ i m
             (with_copyins [(header + Z_to_bv 64 4, 4%nat)]
                (mkEffect (errno_ret EFAULT) [] []))); [reflexivity|].
    apply record_copyins_ok_empty; [reflexivity|].
    unfold err_ret, ret_only. apply pure_ok. }
  destruct (read_bytes_map (in_mem i) data (Z_to_bv 64 CAP_V3_DATA_SIZE))
    as [db|] eqn:Hdb; cbv iota in H |- *; [|discriminate].
  destruct (negb (Z.eqb (bytes_le_to_Z db) 0)) eqn:Hz2;
    cbv iota in H |- *; [discriminate|].
  destruct (cap_permitted_nonempty_b (m_creds m)) eqn:Hc;
    cbv iota in H |- *; [discriminate|].
  destruct (bv_eqb (eff_ret eff) (errno_ret ENOMEM)) eqn:Hr; cbv iota in H;
    apply check_ret_only_copyins_ok_iff in H as (-> & -> & ->).
  - apply (record_copyins_ok_eq _ _ i m
             (with_copyins [(header + Z_to_bv 64 4, 4%nat);
                            (data, Z.to_nat CAP_V3_DATA_SIZE)]
                (mkEffect (errno_ret ENOMEM) [] []))); [reflexivity|].
    apply (record_copyins_ok_eq _ _ i m
             (with_copyins [(data, Z.to_nat CAP_V3_DATA_SIZE)]
                (mkEffect (errno_ret ENOMEM) [] []))); [reflexivity|].
    apply record_copyins_ok_empty; [reflexivity|].
    apply alt_l. unfold err_ret, ret_only. apply pure_ok.
  - apply (record_copyins_ok_eq _ _ i m
             (with_copyins [(header + Z_to_bv 64 4, 4%nat);
                            (data, Z.to_nat CAP_V3_DATA_SIZE)]
                (mkEffect (Z_to_bv 64 0) [] []))); [reflexivity|].
    apply (record_copyins_ok_eq _ _ i m
             (with_copyins [(data, Z.to_nat CAP_V3_DATA_SIZE)]
                (mkEffect (Z_to_bv 64 0) [] []))); [reflexivity|].
    apply record_copyins_ok_empty; [reflexivity|].
    apply alt_r. unfold ret_only. apply pure_ok.
Qed.

Lemma check_capset_sound_unmodeled : forall i header data eff m,
  check_capset i header data eff m = CheckUnmodeled ->
  capset_spec header data i m Unmodeled.
Proof.
  intros i header data eff m H.
  unfold check_capset in H. unfold capset_spec.
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (negb (access_okb header 4)) eqn:Ha; cbv iota in H |- *.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (read_bytes_map (in_mem i) header (Z_to_bv 64 4)) as [vb|] eqn:Hv;
    cbv iota in H |- *; [|apply unmodeled_intro].
  apply record_copyins_unmodeled.
  destruct (negb (Z.eqb (bytes_le_to_Z vb) LINUX_CAPABILITY_VERSION_3)) eqn:Hver;
    cbv iota in H |- *; [apply unmodeled_intro|].
  destruct (negb (access_okb (header + Z_to_bv 64 4) 4)) eqn:Ha2;
    cbv iota in H |- *.
  { now apply check_ret_only_copyins_no_unmodeled in H. }
  destruct (read_bytes_map (in_mem i) (header + Z_to_bv 64 4) (Z_to_bv 64 4))
    as [pb|] eqn:Hp; cbv iota in H |- *; [|apply unmodeled_intro].
  apply record_copyins_unmodeled.
  destruct (negb (Z.eqb (bytes_le_to_Z pb) 0)) eqn:Hz;
    cbv iota in H |- *; [apply unmodeled_intro|].
  destruct (negb (access_okb data CAP_V3_DATA_SIZE)) eqn:Ha3;
    cbv iota in H |- *.
  { now apply check_ret_only_copyins_no_unmodeled in H. }
  destruct (read_bytes_map (in_mem i) data (Z_to_bv 64 CAP_V3_DATA_SIZE))
    as [db|] eqn:Hdb; cbv iota in H |- *; [|apply unmodeled_intro].
  apply record_copyins_unmodeled.
  destruct (negb (Z.eqb (bytes_le_to_Z db) 0)) eqn:Hz2;
    cbv iota in H |- *; [apply unmodeled_intro|].
  destruct (cap_permitted_nonempty_b (m_creds m)) eqn:Hc;
    cbv iota in H |- *; [apply unmodeled_intro|].
  exfalso.
  destruct (bv_eqb (eff_ret eff) (errno_ret ENOMEM)); cbv iota in H;
    now apply check_ret_only_copyins_no_unmodeled in H.
Qed.

Lemma check_capset_complete_ok : forall i header data eff m m' evs,
  capset_spec header data i m (Ok eff m' evs) ->
  check_capset i header data eff m = CheckOk m' evs.
Proof.
  intros i header data eff m m' evs H.
  unfold capset_spec in H. unfold check_capset.
  apply input_bind_ok_inv in H. cbv beta in H.
  apply get_model_bind_ok_inv in H. cbv beta in H.
  destruct (negb (access_okb header 4)) eqn:Ha; cbv iota in H |- *.
  { unfold err_ret, ret_only, pure in H. inversion H; subst.
    now apply check_ret_only_ok_iff. }
  destruct (read_bytes_map (in_mem i) header (Z_to_bv 64 4)) as [vb|] eqn:Hv;
    cbv iota in H |- *; [|unfold unmodeled in H; discriminate].
  apply record_copyins_ok_inv in H as (c1 & H & ->).
  destruct (negb (Z.eqb (bytes_le_to_Z vb) LINUX_CAPABILITY_VERSION_3)) eqn:Hver;
    cbv iota in H |- *; [unfold unmodeled in H; discriminate|].
  destruct (negb (access_okb (header + Z_to_bv 64 4) 4)) eqn:Ha2;
    cbv iota in H |- *.
  { unfold err_ret, ret_only, pure in H. inversion H; subst.
    apply check_ret_only_copyins_ok_iff. now repeat split. }
  destruct (read_bytes_map (in_mem i) (header + Z_to_bv 64 4) (Z_to_bv 64 4))
    as [pb|] eqn:Hp; cbv iota in H |- *; [|unfold unmodeled in H; discriminate].
  apply record_copyins_ok_inv in H as (c2 & H & ->).
  destruct (negb (Z.eqb (bytes_le_to_Z pb) 0)) eqn:Hz;
    cbv iota in H |- *; [unfold unmodeled in H; discriminate|].
  destruct (negb (access_okb data CAP_V3_DATA_SIZE)) eqn:Ha3;
    cbv iota in H |- *.
  { unfold err_ret, ret_only, pure in H. inversion H; subst.
    apply check_ret_only_copyins_ok_iff. now repeat split. }
  destruct (read_bytes_map (in_mem i) data (Z_to_bv 64 CAP_V3_DATA_SIZE))
    as [db|] eqn:Hdb; cbv iota in H |- *; [|unfold unmodeled in H; discriminate].
  apply record_copyins_ok_inv in H as (c3 & H & ->).
  destruct (negb (Z.eqb (bytes_le_to_Z db) 0)) eqn:Hz2;
    cbv iota in H |- *; [unfold unmodeled in H; discriminate|].
  destruct (cap_permitted_nonempty_b (m_creds m)) eqn:Hc;
    cbv iota in H |- *; [unfold unmodeled in H; discriminate|].
  unfold alt, err_ret, ret_only, pure in H.
  destruct H as [H|H]; inversion H; subst; clear H.
  - unfold with_copyins. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins app].
    rewrite bv_eqb_refl. cbv iota.
    apply check_ret_only_copyins_ok_iff. now repeat split.
  - unfold with_copyins. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins app].
    change (bv_eqb (Z_to_bv 64 0) (errno_ret ENOMEM)) with false. cbv iota.
    apply check_ret_only_copyins_ok_iff. now repeat split.
Qed.

Lemma check_capset_complete_unmodeled : forall i header data m eff,
  capset_spec header data i m Unmodeled ->
  check_capset i header data eff m = CheckUnmodeled.
Proof.
  intros i header data m eff H.
  unfold capset_spec in H. unfold check_capset.
  apply input_bind_unmodeled_inv in H. cbv beta in H.
  apply get_model_bind_unmodeled_inv in H. cbv beta in H.
  destruct (negb (access_okb header 4)) eqn:Ha; cbv iota in H |- *.
  { unfold err_ret, ret_only, pure in H. discriminate. }
  destruct (read_bytes_map (in_mem i) header (Z_to_bv 64 4)) as [vb|] eqn:Hv;
    cbv iota in H |- *; [|reflexivity].
  apply record_copyins_unmodeled_inv in H.
  destruct (negb (Z.eqb (bytes_le_to_Z vb) LINUX_CAPABILITY_VERSION_3)) eqn:Hver;
    cbv iota in H |- *; [reflexivity|].
  destruct (negb (access_okb (header + Z_to_bv 64 4) 4)) eqn:Ha2;
    cbv iota in H |- *.
  { unfold err_ret, ret_only, pure in H. discriminate. }
  destruct (read_bytes_map (in_mem i) (header + Z_to_bv 64 4) (Z_to_bv 64 4))
    as [pb|] eqn:Hp; cbv iota in H |- *; [|reflexivity].
  apply record_copyins_unmodeled_inv in H.
  destruct (negb (Z.eqb (bytes_le_to_Z pb) 0)) eqn:Hz;
    cbv iota in H |- *; [reflexivity|].
  destruct (negb (access_okb data CAP_V3_DATA_SIZE)) eqn:Ha3;
    cbv iota in H |- *.
  { unfold err_ret, ret_only, pure in H. discriminate. }
  destruct (read_bytes_map (in_mem i) data (Z_to_bv 64 CAP_V3_DATA_SIZE))
    as [db|] eqn:Hdb; cbv iota in H |- *; [|reflexivity].
  apply record_copyins_unmodeled_inv in H.
  destruct (negb (Z.eqb (bytes_le_to_Z db) 0)) eqn:Hz2;
    cbv iota in H |- *; [reflexivity|].
  destruct (cap_permitted_nonempty_b (m_creds m)) eqn:Hc;
    cbv iota in H |- *; [reflexivity|].
  exfalso. unfold alt, err_ret, ret_only, pure in H.
  destruct H as [H|H]; discriminate.
Qed.
