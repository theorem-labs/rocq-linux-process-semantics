(** * LinuxProcessSem.Checks.Witness.Kernel.Time.PosixTimers — the clock_gettime (113) and clock_getres (114) witnesses

    Mirrors [Sys/Kernel/Time/PosixTimers.v], which answers to Linux
    [kernel/time/posix-timers.c]: this file holds the witnesses for the
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

(** clock_gettime: the witness reads the clock WITHOUT ADVANCING IT.

    [timespec_ok_b] is satisfied non-strictly, so leaving the clock
    where it is is always admissible — which is what makes a witness
    possible at all for an arbitrary model state.  The bytes are the
    recorded nanosecond count split the way [ktime_to_timespec64]
    splits it, and [Z_to_le_bytes] is [bytes_le_to_Z]'s inverse
    ([BvBase.bytes_le_to_Z_of_le_bytes]), so the reading decodes back
    to exactly [m_clock m]. *)
Definition clock_gettime_bytes (t : Z) : list byte :=
  Z_to_le_bytes 8 (t / 1000000000) ++ Z_to_le_bytes 8 (t mod 1000000000).

Definition clock_gettime_witness (clkid tp : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  if clockid_percall_b clkid then
    (* a per-call id reads 0 ns: [realtime_ok_b] relates a reading to
       nothing, so the smallest normalized timespec is always
       admissible and the witness needs no model state at all. *)
    match read_bytes_map (in_wmem i) tp (Z_to_bv 64 16) with
    | None => Unmodeled                            (* unwritable destination *)
    | Some _ =>
        Ok (mkEffect (Z_to_bv 64 0) [(tp, clock_gettime_bytes 0)] [])
           m []
    end
  else if Z.eqb (bv_unsigned clkid) CLOCK_PROCESS_CPUTIME_ID then
    (* CPU time reads 0 ns: [cputime_ok_b] holds the envelope on the
       SIGNED reading, and 0 is inside it in both directions, so the
       same smallest normalized timespec is admissible for the same
       reason, and again with no model state. *)
    match read_bytes_map (in_wmem i) tp (Z_to_bv 64 16) with
    | None => Unmodeled                            (* unwritable destination *)
    | Some _ =>
        Ok (mkEffect (Z_to_bv 64 0) [(tp, clock_gettime_bytes 0)] [])
           m []
    end
  else if negb (Z.eqb (bv_unsigned clkid) CLOCK_MONOTONIC) then Unmodeled
  else if negb (Z.ltb (bv_unsigned (m_clock m)) CLOCK_NS_ENVELOPE)
  then Unmodeled
  else match read_bytes_map (in_wmem i) tp (Z_to_bv 64 16) with
       | None => Unmodeled                            (* unwritable destination *)
       | Some _ =>
           let bs := clock_gettime_bytes (bv_unsigned (m_clock m)) in
           Ok (mkEffect (Z_to_bv 64 0) [(tp, bs)] [])
              (with_clock (Z_to_bv 64 (timespec_ns bs)) m) []
       end.

(** The witness's bytes decode to the recorded reading exactly. *)
Lemma clock_gettime_bytes_ns : forall t,
  (0 <= t < CLOCK_NS_ENVELOPE)%Z ->
  timespec_ns (clock_gettime_bytes t) = t
  /\ tv_frac_of (clock_gettime_bytes t) = (t mod 1000000000)%Z
  /\ length (clock_gettime_bytes t) = 16%nat.
Proof.
  intros t Ht. unfold CLOCK_NS_ENVELOPE in Ht.
  unfold clock_gettime_bytes, timespec_ns, tv_sec_of, tv_frac_of.
  set (A := Z_to_le_bytes 8 (t / 1000000000)).
  set (B := Z_to_le_bytes 8 (t mod 1000000000)).
  assert (HA : length A = 8%nat) by apply length_Z_to_le_bytes.
  assert (HB : length B = 8%nat) by apply length_Z_to_le_bytes.
  assert (Hpow : (2 ^ 63 < 2 ^ 64)%Z) by (vm_compute; reflexivity).
  pose proof (Z.mod_pos_bound t 1000000000 ltac:(lia)) as Hmod.
  assert (Hdiv : (0 <= t / 1000000000)%Z) by (apply Z.div_pos; lia).
  assert (Hdle : (t / 1000000000 <= t)%Z)
    by (apply Z.div_le_upper_bound; lia).
  assert (Hf : firstn 8 (A ++ B) = A).
  { rewrite firstn_app, HA, Nat.sub_diag. cbn [firstn].
    rewrite app_nil_r, <- HA at 1. apply firstn_all. }
  assert (Hs : skipn 8 (A ++ B) = B).
  { rewrite skipn_app, HA, Nat.sub_diag. cbn [skipn].
    rewrite <- HA at 1. rewrite skipn_all. reflexivity. }
  assert (HAv : bytes_le_to_Z A = (t / 1000000000)%Z).
  { unfold A. rewrite bytes_le_to_Z_of_le_bytes by lia.
    change (8 * Z.of_nat 8)%Z with 64%Z. apply Z.mod_small. lia. }
  assert (HBv : bytes_le_to_Z B = (t mod 1000000000)%Z).
  { unfold B. rewrite bytes_le_to_Z_of_le_bytes by lia.
    change (8 * Z.of_nat 8)%Z with 64%Z. apply Z.mod_small. lia. }
  rewrite Hf, Hs, HAv, HBv.
  repeat split; try reflexivity;
    try (rewrite length_app, HA, HB; reflexivity);
    try (rewrite Z.mul_comm; symmetry; apply Z.div_mod; lia).
Qed.

Lemma clock_gettime_witness_ok : forall i clkid tp m,
  clock_gettime_spec clkid tp i m (clock_gettime_witness clkid tp i m).
Proof.
  intros. unfold clock_gettime_spec, clock_gettime_witness.
  destruct (clockid_percall_b clkid) eqn:Hrt.
  { eapply bind_step; [apply input_ok|]. cbv beta.
    destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hw0;
      [|apply unmodeled_intro].
    destruct (clock_gettime_bytes_ns 0) as [Hns0 [Hnsec0 Hlen0]];
      [unfold CLOCK_NS_ENVELOPE; lia|].
    eapply bind_step.
    { apply (choose_ok _ (clock_gettime_bytes 0)).
      unfold realtime_ok_b. rewrite Hlen0, Hns0, Hnsec0. cbn [Nat.eqb].
      reflexivity. }
    apply pure_ok. }
  destruct (Z.eqb (bv_unsigned clkid) CLOCK_PROCESS_CPUTIME_ID) eqn:Hcp.
  { eapply bind_step; [apply input_ok|]. cbv beta.
    destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hw1;
      [|apply unmodeled_intro].
    destruct (clock_gettime_bytes_ns 0) as [Hns0 [Hnsec0 Hlen0]];
      [unfold CLOCK_NS_ENVELOPE; lia|].
    eapply bind_step.
    { apply (choose_ok _ (clock_gettime_bytes 0)).
      unfold cputime_ok_b. rewrite Hlen0, Hnsec0. cbn [Nat.eqb].
      reflexivity. }
    apply pure_ok. }
  destruct (negb (Z.eqb (bv_unsigned clkid) CLOCK_MONOTONIC)) eqn:Hid;
    [apply unmodeled_intro|].
  eapply bind_step; [apply get_model_ok|]. cbv beta.
  destruct (negb (Z.ltb (bv_unsigned (m_clock m)) CLOCK_NS_ENVELOPE)) eqn:Henv;
    [apply unmodeled_intro|].
  eapply bind_step; [apply input_ok|]. cbv beta.
  destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hw;
    [|apply unmodeled_intro].
  apply negb_false_iff, Z.ltb_lt in Henv.
  pose proof (bv_unsigned_in_range 64 (m_clock m)).
  destruct (clock_gettime_bytes_ns (bv_unsigned (m_clock m)))
    as [Hns [Hnsec Hlen]]; [lia|].
  eapply bind_step.
  { apply (choose_ok _ (clock_gettime_bytes (bv_unsigned (m_clock m)))).
    unfold timespec_ok_b. rewrite Hlen, Hns, Hnsec. cbn [Nat.eqb].
    pose proof (Z.mod_pos_bound (bv_unsigned (m_clock m)) 1000000000).
    rewrite (proj2 (Z.ltb_lt _ 1000000000)) by lia.
    rewrite (proj2 (Z.leb_le _ _)) by lia.
    rewrite (proj2 (Z.ltb_lt _ CLOCK_NS_ENVELOPE)) by lia.
    reflexivity. }
  eapply bind_step; [apply modify_ok|].
  apply pure_ok.
Qed.

Definition clock_getres_witness (clkid tp : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  if clock_getres_supported_b clkid then
    if clock_getres_dst_ok_b i tp then
      if clock_getres_alarm_b clkid then ret_outcome (errno_ret EINVAL) m
      else if w_is0 tp then ret_outcome (Z_to_bv 64 0) m
      else Ok (mkEffect (Z_to_bv 64 0)
                    [(tp, clock_gettime_bytes 1)] []) m []
    else Unmodeled
  else if Z.eqb (bv_unsigned clkid) CLOCK_SGI_CYCLE
       then ret_outcome (errno_ret EINVAL) m
       else Unmodeled.

Lemma clock_getres_one_ns : forall clkid,
  clock_getres_resolution_b clkid (clock_gettime_bytes 1) = true.
Proof.
  intros clkid. unfold clock_getres_resolution_b.
  destruct (clock_getres_cpu_b clkid); vm_compute; reflexivity.
Qed.

Lemma clock_getres_witness_ok : forall i clkid tp m,
  clock_getres_spec clkid tp i m (clock_getres_witness clkid tp i m).
Proof.
  intros. unfold clock_getres_spec, clock_getres_witness.
  destruct (clock_getres_supported_b clkid).
  - eapply bind_step; [apply input_ok|]. cbv beta.
    destruct (clock_getres_dst_ok_b i tp); [|apply unmodeled_intro].
    destruct (clock_getres_alarm_b clkid).
    + apply alt_l. unfold err_ret, ret_only, ret_outcome. apply pure_ok.
    + unfold clock_getres_result_spec.
      destruct (w_is0 tp).
      * unfold ret_only, ret_outcome. apply pure_ok.
      * eapply bind_step.
        { apply (choose_ok _ (clock_gettime_bytes 1)).
          apply clock_getres_one_ns. }
        apply pure_ok.
  - destruct (Z.eqb (bv_unsigned clkid) CLOCK_SGI_CYCLE).
    + unfold err_ret, ret_only, ret_outcome. apply pure_ok.
    + apply unmodeled_intro.
Qed.
