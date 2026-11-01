(** * LinuxProcessSem.Checks.Witness.Kernel.Capability — the capget (90) and capset (91) witnesses, and their proofs

    Mirrors [Sys/Kernel/Capability.v], which answers to Linux
    [kernel/capability.c]: this file holds the witnesses for the
    syscalls defined there, and no others.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export
  Prelude.

(** One data image [capget_data_ok_for] admits: the derived effective
    and permitted sets, and an empty inheritable set. *)
Definition capget_witness_bytes (eff perm : bool) : list byte :=
  let e := if eff then CAP_VALID_MASK else 0%Z in
  let p := if perm then CAP_VALID_MASK else 0%Z in
  Z_to_le_bytes 4 (Z.land e (Z.ones 32)) ++ Z_to_le_bytes 4 (Z.land p (Z.ones 32))
  ++ Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 (Z.shiftr e 32)
  ++ Z_to_le_bytes 4 (Z.shiftr p 32) ++ Z_to_le_bytes 4 0.

Lemma capget_witness_bytes_ok : forall eff perm,
  capget_data_ok_for eff perm (capget_witness_bytes eff perm) = true.
Proof. intros [|] [|]; vm_compute; reflexivity. Qed.

Definition capget_witness (header dataptr : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  if negb (access_okb header 4) then ret_outcome (errno_ret EFAULT) m
  else
    match read_bytes_map (in_mem i) header (Z_to_bv 64 4) with
    | None => Unmodeled
    | Some vb =>
        if negb (Z.eqb (bytes_le_to_Z vb) LINUX_CAPABILITY_VERSION_3)
        then Unmodeled
        else if w_is0 dataptr
        then Ok (with_copyins [(header, 4%nat)] (mkEffect (Z_to_bv 64 0) [] [])) m []
        else if negb (access_okb (header + Z_to_bv 64 4) 4)
        then Ok (with_copyins [(header, 4%nat)]
                   (mkEffect (errno_ret EFAULT) [] [])) m []
        else
          match read_bytes_map (in_mem i) (header + Z_to_bv 64 4) (Z_to_bv 64 4) with
          | None => Unmodeled
          | Some pb =>
              if negb (Z.eqb (bytes_le_to_Z pb) 0) then Unmodeled
              else if negb (access_okb dataptr CAP_V3_DATA_SIZE)
              then Ok (with_copyins
                         [(header, 4%nat); (header + Z_to_bv 64 4, 4%nat)]
                         (mkEffect (errno_ret EFAULT) [] [])) m []
              else
                match read_bytes_map (in_wmem i) dataptr
                        (Z_to_bv 64 CAP_V3_DATA_SIZE) with
                | None => Unmodeled
                | Some _ =>
                    Ok (with_copyins
                          [(header, 4%nat); (header + Z_to_bv 64 4, 4%nat)]
                          (mkEffect (Z_to_bv 64 0)
                             [(dataptr,
                               capget_witness_bytes
                                 (creds_privileged (m_creds m))
                                 (cap_permitted_full_b (m_creds m)))] [])) m []
                end
          end
    end.

Lemma capget_witness_ok : forall header dataptr i m,
  capget_spec header dataptr i m (capget_witness header dataptr i m).
Proof.
  intros. unfold capget_spec, capget_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (negb (access_okb header 4)) eqn:Ha; cbv iota.
  { unfold err_ret, ret_only, ret_outcome. apply pure_ok. }
  destruct (read_bytes_map (in_mem i) header (Z_to_bv 64 4)) as [vb|] eqn:Hv;
    cbv iota; [|apply unmodeled_intro].
  destruct (negb (Z.eqb (bytes_le_to_Z vb) LINUX_CAPABILITY_VERSION_3)) eqn:Hver;
    cbv iota.
  { apply record_copyins_unmodeled. apply unmodeled_intro. }
  destruct (w_is0 dataptr) eqn:Hd; cbv iota.
  { apply record_copyins_ok_empty; [reflexivity|]. unfold ret_only. apply pure_ok. }
  destruct (negb (access_okb (header + Z_to_bv 64 4) 4)) eqn:Ha2; cbv iota.
  { apply record_copyins_ok_empty; [reflexivity|].
    unfold err_ret, ret_only. apply pure_ok. }
  destruct (read_bytes_map (in_mem i) (header + Z_to_bv 64 4) (Z_to_bv 64 4))
    as [pb|] eqn:Hp; cbv iota.
  2: { apply record_copyins_unmodeled. apply unmodeled_intro. }
  destruct (negb (Z.eqb (bytes_le_to_Z pb) 0)) eqn:Hz; cbv iota.
  { apply record_copyins_unmodeled, record_copyins_unmodeled, unmodeled_intro. }
  destruct (negb (access_okb dataptr CAP_V3_DATA_SIZE)) eqn:Ha3; cbv iota.
  { apply (record_copyins_ok_eq _ _ i m
             (with_copyins [(header + Z_to_bv 64 4, 4%nat)]
                (mkEffect (errno_ret EFAULT) [] []))); [reflexivity|].
    apply record_copyins_ok_empty; [reflexivity|].
    unfold err_ret, ret_only. apply pure_ok. }
  destruct (read_bytes_map (in_wmem i) dataptr (Z_to_bv 64 CAP_V3_DATA_SIZE))
    as [wb|] eqn:Hw; cbv iota.
  2: { apply record_copyins_unmodeled, record_copyins_unmodeled, unmodeled_intro. }
  apply (record_copyins_ok_eq _ _ i m
           (with_copyins [(header + Z_to_bv 64 4, 4%nat)]
              (mkEffect (Z_to_bv 64 0)
                 [(dataptr,
                   capget_witness_bytes (creds_privileged (m_creds m))
                     (cap_permitted_full_b (m_creds m)))] []))); [reflexivity|].
  apply record_copyins_ok_empty; [reflexivity|].
  eapply bind_step.
  { apply choose_ok. cbv beta. unfold capget_data_ok.
    apply capget_witness_bytes_ok. }
  apply pure_ok.
Qed.

(** capset: the success answer where the arm answers at all. *)
Definition capset_witness (header data : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  if negb (access_okb header 4) then ret_outcome (errno_ret EFAULT) m
  else
    match read_bytes_map (in_mem i) header (Z_to_bv 64 4) with
    | None => Unmodeled
    | Some vb =>
        if negb (Z.eqb (bytes_le_to_Z vb) LINUX_CAPABILITY_VERSION_3)
        then Unmodeled
        else if negb (access_okb (header + Z_to_bv 64 4) 4)
        then Ok (with_copyins [(header, 4%nat)]
                   (mkEffect (errno_ret EFAULT) [] [])) m []
        else
          match read_bytes_map (in_mem i) (header + Z_to_bv 64 4) (Z_to_bv 64 4) with
          | None => Unmodeled
          | Some pb =>
              if negb (Z.eqb (bytes_le_to_Z pb) 0) then Unmodeled
              else if negb (access_okb data CAP_V3_DATA_SIZE)
              then Ok (with_copyins
                         [(header, 4%nat); (header + Z_to_bv 64 4, 4%nat)]
                         (mkEffect (errno_ret EFAULT) [] [])) m []
              else
                match read_bytes_map (in_mem i) data (Z_to_bv 64 CAP_V3_DATA_SIZE) with
                | None => Unmodeled
                | Some db =>
                    if negb (Z.eqb (bytes_le_to_Z db) 0) then Unmodeled
                    else if cap_permitted_full_b (m_creds m) then Unmodeled
                    else Ok (with_copyins
                               [(header, 4%nat); (header + Z_to_bv 64 4, 4%nat);
                                (data, Z.to_nat CAP_V3_DATA_SIZE)]
                               (mkEffect (Z_to_bv 64 0) [] [])) m []
                end
          end
    end.

Lemma capset_witness_ok : forall header data i m,
  capset_spec header data i m (capset_witness header data i m).
Proof.
  intros. unfold capset_spec, capset_witness.
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (negb (access_okb header 4)) eqn:Ha; cbv iota.
  { unfold err_ret, ret_only, ret_outcome. apply pure_ok. }
  destruct (read_bytes_map (in_mem i) header (Z_to_bv 64 4)) as [vb|] eqn:Hv;
    cbv iota; [|apply unmodeled_intro].
  destruct (negb (Z.eqb (bytes_le_to_Z vb) LINUX_CAPABILITY_VERSION_3)) eqn:Hver;
    cbv iota.
  { apply record_copyins_unmodeled. apply unmodeled_intro. }
  destruct (negb (access_okb (header + Z_to_bv 64 4) 4)) eqn:Ha2; cbv iota.
  { apply record_copyins_ok_empty; [reflexivity|].
    unfold err_ret, ret_only. apply pure_ok. }
  destruct (read_bytes_map (in_mem i) (header + Z_to_bv 64 4) (Z_to_bv 64 4))
    as [pb|] eqn:Hp; cbv iota.
  2: { apply record_copyins_unmodeled. apply unmodeled_intro. }
  destruct (negb (Z.eqb (bytes_le_to_Z pb) 0)) eqn:Hz; cbv iota.
  { apply record_copyins_unmodeled, record_copyins_unmodeled, unmodeled_intro. }
  destruct (negb (access_okb data CAP_V3_DATA_SIZE)) eqn:Ha3; cbv iota.
  { apply (record_copyins_ok_eq _ _ i m
             (with_copyins [(header + Z_to_bv 64 4, 4%nat)]
                (mkEffect (errno_ret EFAULT) [] []))); [reflexivity|].
    apply record_copyins_ok_empty; [reflexivity|].
    unfold err_ret, ret_only. apply pure_ok. }
  destruct (read_bytes_map (in_mem i) data (Z_to_bv 64 CAP_V3_DATA_SIZE))
    as [db|] eqn:Hdb; cbv iota.
  2: { apply record_copyins_unmodeled, record_copyins_unmodeled, unmodeled_intro. }
  destruct (negb (Z.eqb (bytes_le_to_Z db) 0)) eqn:Hz2; cbv iota.
  { apply record_copyins_unmodeled, record_copyins_unmodeled,
      record_copyins_unmodeled, unmodeled_intro. }
  destruct (cap_permitted_full_b (m_creds m)) eqn:Hc; cbv iota.
  { apply record_copyins_unmodeled, record_copyins_unmodeled,
      record_copyins_unmodeled, unmodeled_intro. }
  apply (record_copyins_ok_eq _ _ i m
           (with_copyins [(header + Z_to_bv 64 4, 4%nat);
                          (data, Z.to_nat CAP_V3_DATA_SIZE)]
              (mkEffect (Z_to_bv 64 0) [] []))); [reflexivity|].
  apply (record_copyins_ok_eq _ _ i m
           (with_copyins [(data, Z.to_nat CAP_V3_DATA_SIZE)]
              (mkEffect (Z_to_bv 64 0) [] []))); [reflexivity|].
  apply record_copyins_ok_empty; [reflexivity|].
  apply alt_r. unfold ret_only. apply pure_ok.
Qed.
