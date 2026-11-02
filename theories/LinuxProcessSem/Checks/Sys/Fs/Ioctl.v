(** * LinuxProcessSem.Checks.Sys.Fs.Ioctl — the ioctl (29) checkers, and their proofs

    Mirrors [Sys/Fs/Ioctl.v], which answers to Linux [fs/ioctl.c]: this
    file holds the checkers for the syscalls defined there, and no
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

(** The one effect a SIOCGIFINDEX that found its device takes: 0, the
    40 bytes [Ioctl.ifreq_with_index] puts back at [argp], the one
    copy-in of the [struct ifreq] in the ledger, and nothing else. *)
Definition check_ifreq_writeback (argp : word) (bs : list byte)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | mkEffectU ret ws [] [] [] cis =>
      if bv_eqb ret (Z_to_bv 64 0) && writes_eqb ws [(argp, bs)]
         && access_ranges_eqb cis [(argp, Z.to_nat IFREQ_SIZE)]
      then CheckOk m [] else CheckReject
  | _ => CheckReject
  end.

Lemma check_ifreq_writeback_ok_iff : forall argp bs eff m m' evs,
  check_ifreq_writeback argp bs eff m = CheckOk m' evs <->
  (eff = with_copyins [(argp, Z.to_nat IFREQ_SIZE)]
           (mkEffect (Z_to_bv 64 0) [(argp, bs)] [])
   /\ m' = m /\ evs = []).
Proof.
  intros argp bs [ret ws zs us cs cis] m m' evs.
  unfold check_ifreq_writeback, with_copyins.
  cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies].
  destruct zs as [|z zs]; [destruct us as [|u us]; [destruct cs as [|c cs]|]|];
    cbv beta iota;
    try (split; [discriminate|intros (H1 & _ & _); discriminate H1]).
  destruct (bv_eqb ret (Z_to_bv 64 0) && writes_eqb ws [(argp, bs)]
            && access_ranges_eqb cis [(argp, Z.to_nat IFREQ_SIZE)]) eqn:E.
  - apply andb_true_iff in E as [E Ek]. apply andb_true_iff in E as [Er Ew].
    apply bv_eqb_eq in Er. apply writes_eqb_eq in Ew.
    apply access_ranges_eqb_eq in Ek. subst.
    split; [intro H; inversion H; auto|intros (_ & -> & ->); reflexivity].
  - split; [discriminate|]. intros (H1 & _ & _). inversion H1; subst.
    rewrite bv_eqb_refl, (proj2 (writes_eqb_eq _ _) eq_refl),
      access_ranges_eqb_refl in E.
    discriminate.
Qed.

Lemma check_ifreq_writeback_no_unmodeled : forall argp bs eff m,
  check_ifreq_writeback argp bs eff m <> CheckUnmodeled.
Proof.
  intros argp bs [ret ws zs us cs cis] m. unfold check_ifreq_writeback.
  destruct zs; [destruct us; [destruct cs|]|]; cbv beta iota; try discriminate.
  destruct (bv_eqb ret (Z_to_bv 64 0) && writes_eqb ws [(argp, bs)]
            && access_ranges_eqb cis [(argp, Z.to_nat IFREQ_SIZE)]);
    discriminate.
Qed.

(** Mirrors [Ioctl.siocgifindex_spec] test for test: the 40-byte copy-in
    (-EFAULT with an empty ledger when any byte is unreadable), the name
    test ("lo" or decline), then the write-back: the whole of it lands
    ([check_ifreq_writeback]), none of it lands (-EFAULT with the
    copy-in in the ledger), or a prefix would (declined). *)
Definition check_siocgifindex (argp : word) (i : SyscallInput)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match copy_bytes_map (in_mem i) argp IFREQ_SIZE with
  | None => check_ret_only eff (errno_ret EFAULT) m []
  | Some ifr =>
      if negb (ifreq_names_lo ifr) then CheckUnmodeled
      else
        match read_bytes_map (in_wmem i) argp (Z_to_bv 64 IFREQ_SIZE) with
        | Some _ =>
            check_ifreq_writeback argp (ifreq_with_index ifr LOOPBACK_IFINDEX) eff m
        | None =>
            match read_bytes_map (in_wmem i) argp (Z_to_bv 64 1) with
            | None =>
                check_ret_only_copyins [(argp, Z.to_nat IFREQ_SIZE)] eff
                  (errno_ret EFAULT) m []
            | Some _ => CheckUnmodeled
            end
        end
  end.

Lemma check_siocgifindex_sound_ok : forall argp i eff m m' evs,
  check_siocgifindex argp i eff m = CheckOk m' evs ->
  siocgifindex_spec argp i i m (Ok eff m' evs).
Proof.
  intros argp i eff m m' evs H.
  unfold check_siocgifindex in H. unfold siocgifindex_spec.
  destruct (copy_bytes_map (in_mem i) argp IFREQ_SIZE) as [ifr|] eqn:Hc;
    cbv iota in H |- *.
  - destruct (ifreq_names_lo ifr) eqn:Hlo; cbn [negb] in H |- *;
      [|discriminate H].
    destruct (read_bytes_map (in_wmem i) argp (Z_to_bv 64 IFREQ_SIZE))
      as [w|] eqn:Hw; cbv iota in H |- *.
    + apply check_ifreq_writeback_ok_iff in H as (-> & -> & ->).
      apply record_copyins_ok_empty; [reflexivity|]. apply pure_ok.
    + destruct (read_bytes_map (in_wmem i) argp (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
        cbv iota in H |- *; [discriminate H|].
      apply check_ret_only_copyins_ok_iff in H as (-> & -> & ->).
      apply record_copyins_ok_empty; [reflexivity|]. apply pure_ok.
  - apply check_ret_only_ok_iff in H as (-> & -> & ->). apply pure_ok.
Qed.

Lemma check_siocgifindex_sound_unmodeled : forall argp i eff m,
  check_siocgifindex argp i eff m = CheckUnmodeled ->
  siocgifindex_spec argp i i m Unmodeled.
Proof.
  intros argp i eff m H.
  unfold check_siocgifindex in H. unfold siocgifindex_spec.
  destruct (copy_bytes_map (in_mem i) argp IFREQ_SIZE) as [ifr|] eqn:Hc;
    cbv iota in H |- *;
    [|now apply check_ret_only_no_unmodeled in H].
  apply record_copyins_unmodeled.
  destruct (ifreq_names_lo ifr) eqn:Hlo; cbn [negb] in H |- *;
    [|apply unmodeled_intro].
  destruct (read_bytes_map (in_wmem i) argp (Z_to_bv 64 IFREQ_SIZE))
    as [w|] eqn:Hw; cbv iota in H |- *;
    [now apply check_ifreq_writeback_no_unmodeled in H|].
  destruct (read_bytes_map (in_wmem i) argp (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
    cbv iota in H |- *; [apply unmodeled_intro|].
  now apply check_ret_only_copyins_no_unmodeled in H.
Qed.

Lemma check_siocgifindex_complete_ok : forall argp i eff m m' evs,
  siocgifindex_spec argp i i m (Ok eff m' evs) ->
  check_siocgifindex argp i eff m = CheckOk m' evs.
Proof.
  intros argp i eff m m' evs H.
  unfold siocgifindex_spec in H. unfold check_siocgifindex.
  destruct (copy_bytes_map (in_mem i) argp IFREQ_SIZE) as [ifr|] eqn:Hc;
    cbv iota in H |- *.
  - apply record_copyins_ok_inv in H as (core & Hcore & ->).
    destruct (ifreq_names_lo ifr) eqn:Hlo; cbn [negb] in Hcore |- *;
      [|unfold unmodeled in Hcore; cbv beta in Hcore; discriminate Hcore].
    destruct (read_bytes_map (in_wmem i) argp (Z_to_bv 64 IFREQ_SIZE))
      as [w|] eqn:Hw; cbv iota in Hcore |- *.
    + unfold pure in Hcore. cbv beta in Hcore. inversion Hcore; subst.
      apply check_ifreq_writeback_ok_iff. split; [reflexivity|split; reflexivity].
    + destruct (read_bytes_map (in_wmem i) argp (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
        cbv iota in Hcore |- *;
        [unfold unmodeled in Hcore; cbv beta in Hcore; discriminate Hcore|].
      unfold err_ret, ret_only, pure in Hcore. cbv beta in Hcore.
      inversion Hcore; subst.
      apply check_ret_only_copyins_ok_iff. split; [reflexivity|split; reflexivity].
  - unfold err_ret, ret_only, pure in H. cbv beta in H. inversion H; subst.
    apply check_ret_only_ok_iff. split; [reflexivity|split; reflexivity].
Qed.

Lemma check_siocgifindex_complete_unmodeled : forall argp i eff m,
  siocgifindex_spec argp i i m Unmodeled ->
  check_siocgifindex argp i eff m = CheckUnmodeled.
Proof.
  intros argp i eff m H.
  unfold siocgifindex_spec in H. unfold check_siocgifindex.
  destruct (copy_bytes_map (in_mem i) argp IFREQ_SIZE) as [ifr|] eqn:Hc;
    cbv iota in H |- *;
    [|unfold err_ret, ret_only, pure in H; cbv beta in H; discriminate H].
  apply record_copyins_unmodeled_inv in H.
  destruct (ifreq_names_lo ifr) eqn:Hlo; cbn [negb] in H |- *; [|reflexivity].
  destruct (read_bytes_map (in_wmem i) argp (Z_to_bv 64 IFREQ_SIZE))
    as [w|] eqn:Hw; cbv iota in H |- *;
    [unfold pure in H; cbv beta in H; discriminate H|].
  destruct (read_bytes_map (in_wmem i) argp (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
    cbv iota in H |- *; [reflexivity|].
  unfold err_ret, ret_only, pure in H. cbv beta in H. discriminate H.
Qed.

(** ioctl: -EBADF on a closed fd; the eight terminal requests answer
    -ENOTTY on every open kind but /dev/urandom (an unnamed file among
    them, as the regular file it is); SIOCGIFINDEX on a
    datagram socket is [check_siocgifindex], which reads the third
    argument out of [i]; everything else is unmodeled. *)
Definition check_ioctl (i : SyscallInput) (fd req : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | None => check_ret_only eff (errno_ret EBADF) m []
  | Some (FdChannel _) | Some (FdFile _ _) | Some (FdFileW _ _) | Some FdDir
  | Some (FdSocket _) | Some (FdStream _ _ _) | Some (FdEventfd _) | Some (FdPipe _ _)
  | Some (FdFileA _ _) | Some (FdFileRW _ _) | Some (FdDevNull _ _)
  | Some (FdAnon _ _) =>
      if tty_only_request req then check_ret_only eff (errno_ret ENOTTY) m []
      else CheckUnmodeled
  | Some FdUrandom => CheckUnmodeled
  | Some (FdDgram _) =>
      if tty_only_request req then check_ret_only eff (errno_ret ENOTTY) m []
      else if bv_eqb req SIOCGIFINDEX then check_siocgifindex (in_arg i 2) i eff m
      else CheckUnmodeled
  end.

Lemma check_ioctl_sound_ok : forall fd req eff m m' evs i,
  check_ioctl i fd req eff m = CheckOk m' evs -> ioctl_spec fd req i m (Ok eff m' evs).
Proof.
  intros fd req eff m m' evs i H.
  unfold check_ioctl in H. unfold ioctl_spec.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd.
  - (* enumerated open-fd arms: [e] must be destructed for the match to
       reduce; every constructor answers the terminal requests alike. *)
    destruct e; destruct (tty_only_request req) eqn:Hr; try discriminate;
      (eapply bind_ok0; [apply get_model_ok|]); cbv beta iota;
      srw Hfd;
      try (apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
           apply pure_ok).
    (* what is left is the datagram socket's SIOCGIFINDEX *)
    destruct (bv_eqb req SIOCGIFINDEX) eqn:Hs; [|discriminate H].
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    now apply check_siocgifindex_sound_ok.
  - apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    eapply bind_ok0; [apply get_model_ok|]. cbv beta iota.
    srw Hfd. apply pure_ok.
Qed.

Lemma check_ioctl_sound_unmodeled : forall fd req eff m i,
  check_ioctl i fd req eff m = CheckUnmodeled -> ioctl_spec fd req i m Unmodeled.
Proof.
  intros fd req eff m i H.
  unfold check_ioctl in H. unfold ioctl_spec.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd.
  - (* enumerated open-fd arms: destruct [e] so the match reduces. *)
    destruct e; destruct (tty_only_request req) eqn:Hr;
      try (now apply check_ret_only_no_unmodeled in H);
      (eapply bind_unmodeled2; [apply get_model_ok|]); cbv beta iota;
      srw Hfd; try apply unmodeled_intro.
    (* the datagram socket past the terminal requests *)
    destruct (bv_eqb req SIOCGIFINDEX) eqn:Hs; [|apply unmodeled_intro].
    eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    eapply check_siocgifindex_sound_unmodeled. exact H.
  - now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_ioctl_complete_ok : forall fd req eff m m' evs i,
  ioctl_spec fd req i m (Ok eff m' evs) -> check_ioctl i fd req eff m = CheckOk m' evs.
Proof.
  intros fd req eff m m' evs i H.
  unfold ioctl_spec in H. unfold check_ioctl.
  apply get_model_bind_ok_inv in H. cbv beta in H.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; cbv iota in H |- *.
  2: { sys_unfold. inv_ok. cbn; try rewrite bv_eqb_refl; reflexivity. }
  destruct e; cbv iota in H |- *;
    destruct (tty_only_request req) eqn:Hr; cbv iota in H |- *;
    try (sys_unfold; inv_ok; cbn; try rewrite bv_eqb_refl; reflexivity).
  (* what is left is the datagram socket past the terminal requests *)
  destruct (bv_eqb req SIOCGIFINDEX) eqn:Hs; cbv iota in H |- *;
    [|unfold unmodeled in H; cbv beta in H; discriminate H].
  apply input_bind_ok_inv in H. cbv beta in H.
  now apply check_siocgifindex_complete_ok.
Qed.

Lemma check_ioctl_complete_unmodeled : forall fd req m i eff,
  ioctl_spec fd req i m Unmodeled -> check_ioctl i fd req eff m = CheckUnmodeled.
Proof.
  intros fd req m i eff H.
  unfold ioctl_spec in H. unfold check_ioctl.
  apply get_model_bind_unmodeled_inv in H. cbv beta in H.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd; cbv iota in H |- *.
  2: { sys_unfold. inv_ok. }
  destruct e; cbv iota in H |- *;
    destruct (tty_only_request req) eqn:Hr; cbv iota in H |- *;
    try reflexivity;
    try (sys_unfold; inv_ok; fail).
  (* what is left is the datagram socket's SIOCGIFINDEX *)
  destruct (bv_eqb req SIOCGIFINDEX) eqn:Hs; cbv iota in H |- *; [|reflexivity].
  apply input_bind_unmodeled_inv in H. cbv beta in H.
  eapply check_siocgifindex_complete_unmodeled. exact H.
Qed.
