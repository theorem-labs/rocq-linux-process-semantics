(** * LinuxProcessSem.Checks.ProcsClockSync — one CLOCK_MONOTONIC across processes

    Not part of the trusted specification: QA on [Procs.pstep_sync], in
    the sense of [Checks.Examples]'s header, under its first reason: the
    statements are universally quantified over configurations and steps.

    ** What this pins

    CLOCK_MONOTONIC is one clock in Linux and a per-entry copy here
    ([State.timest_clock] in [pe_model]).  The core keeps the copies in
    step: an entry at nanosleep (101) or clock_gettime (113) whose copy is
    behind another entry's first raises it ([Procs.pstep_sync]); only then
    does the released step answer ([Procs.sync_pending_b] gates
    [pstep_other]).

    - [syscall_spec_clock_ge]: the released answers of 101 and 113 never
      lower the clock copy.
    - [pstep_clock_monotone]: after any step of an entry at 101 or 113,
      that entry's copy is at least every copy in the table before the
      step.  Every reading starts from there, so no reading in one process
      precedes a reading another process made earlier, which is the
      monotonicity Linux gives across processes.
    - [sync_closed_one]: at one entry the gate is closed, so a one-process
      run is the released one. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run Procs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs VmMapsDisjoint ProcsWellFormed ProcsPrivateFrame.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope bool_scope.

Definition clk (m : Model) : Z := bv_unsigned (m_clock m).

(* =========================================================================
   The released answers never lower the copy
   ========================================================================= *)

Lemma bytes_le_to_Z_nonneg_c : forall bs, (0 <= bytes_le_to_Z bs)%Z.
Proof.
  induction bs as [|b bs IH]; cbn; [lia|].
  apply Z.lor_nonneg. split.
  - pose proof (bv_unsigned_in_range _ b). lia.
  - apply Z.shiftl_nonneg. exact IH.
Qed.

Lemma timespec_ns_nonneg : forall bs, (0 <= timespec_ns bs)%Z.
Proof.
  intros bs. unfold timespec_ns, tv_sec_of, tv_frac_of.
  pose proof (bytes_le_to_Z_nonneg_c (firstn 8 bs)).
  pose proof (bytes_le_to_Z_nonneg_c (skipn 8 bs)). lia.
Qed.

Lemma word_small : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. apply Z_to_bv_small. change (bv_modulus 64) with (2 ^ 64)%Z. lia.
Qed.

Lemma nanosleep_clock_ge : forall prev req rem,
  (bv_unsigned prev <= bv_unsigned (nanosleep_clock prev req rem))%Z.
Proof.
  intros prev req rem. unfold nanosleep_clock.
  pose proof (bv_unsigned_in_range _ prev) as Hr.
  change (bv_modulus 64) with (2 ^ 64)%Z in Hr.
  pose proof (timespec_ns_nonneg rem) as Hn.
  unfold KTIME_MAX.
  rewrite word_small; [lia|].
  split; [lia|].
  apply Z.max_lub_lt; [lia|].
  pose proof (Z.le_min_r (bv_unsigned prev + timespec_ktime req) (2 ^ 63 - 1)). lia.
Qed.

Lemma timespec_ok_ge : forall bs prev,
  timespec_ok_b bs prev = true ->
  (bv_unsigned prev <= bv_unsigned (Z_to_bv 64 (timespec_ns bs)))%Z.
Proof.
  intros bs prev H. unfold timespec_ok_b in H.
  apply andb_true_iff in H as [H Henv]. apply andb_true_iff in H as [_ Hge].
  apply Z.leb_le in Hge. apply Z.ltb_lt in Henv. unfold CLOCK_NS_ENVELOPE in Henv.
  pose proof (timespec_ns_nonneg bs).
  rewrite word_small; lia.
Qed.

Local Ltac clk_walk H :=
  repeat (cbv beta iota zeta in H;
          lazymatch type of H with
          | CheckOk _ _ = CheckOk _ _ => fail
          | _ => match type of H with
                 | context [match ?x with _ => _ end] => destruct x eqn:?
                 | context [if ?b then _ else _] => destruct b eqn:?
                 end
          end);
  try discriminate H.

Local Ltac clk_leaf H :=
  first
  [ apply check_ret_only_ok_iff in H; destruct H as (_ & -> & _); unfold clk; lia
  | apply check_ret_only_copyins_ok_iff in H; destruct H as (_ & -> & _); unfold clk; lia
  | injection H as <- <-; unfold clk; lia
  | injection H as <- <-; unfold clk; apply nanosleep_clock_ge
  | injection H as <- <-; unfold clk; apply timespec_ok_ge;
    match goal with
    | Ht : (_ && timespec_ok_b ?bs ?p) = true |- _ =>
        apply andb_true_iff in Ht as [_ Ht]; exact Ht
    end ].

Lemma check_clock_gettime_ge : forall i clkid tp eff m m' evs,
  check_clock_gettime i clkid tp eff m = CheckOk m' evs -> (clk m <= clk m')%Z.
Proof.
  intros i clkid tp [ret ws zs us cs ci] m m' evs H.
  unfold check_clock_gettime in H. clk_walk H. all: clk_leaf H.
Qed.

Lemma check_copyins_ok_model : forall reads eff r m' evs,
  check_copyins reads eff r = CheckOk m' evs ->
  r = CheckOk m' evs.
Proof.
  intros reads eff r m' evs H. unfold check_copyins in H.
  destruct (access_ranges_eqb _ _); [exact H | discriminate H].
Qed.

Lemma check_nanosleep_ge : forall i rqtp rmtp eff m m' evs,
  check_nanosleep i rqtp rmtp eff m = CheckOk m' evs -> (clk m <= clk m')%Z.
Proof.
  intros i rqtp rmtp eff m m' evs H.
  unfold check_nanosleep in H.
  repeat (cbv beta iota zeta in H;
          lazymatch type of H with
          | CheckOk _ _ = CheckOk _ _ => fail
          | check_copyins _ _ _ = CheckOk _ _ => apply check_copyins_ok_model in H
          | _ => match type of H with
                 | context [match ?x with _ => _ end] => destruct x eqn:?
                 | context [if ?b then _ else _] => destruct b eqn:?
                 end
          end);
    try discriminate H.
  all: clk_leaf H.
Qed.

(** THE SPEC FACT: at 101 and 113, every [Ok] answer keeps or raises the
    copy. *)
Theorem syscall_spec_clock_ge : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  List.existsb (Z.eqb (bv_unsigned (in_sysno i))) multiproc_clock_sysnos = true ->
  (clk m <= clk m')%Z.
Proof.
  intros i m eff m' evs H Hn. apply check_syscall_ok_iff in H.
  cbn [multiproc_clock_sysnos List.existsb] in Hn.
  apply orb_true_iff in Hn as [E|Hn];
    [|apply orb_true_iff in Hn as [E|E]; [|discriminate E]];
    apply Z.eqb_eq in E.
  - assert (Hc : check_syscall i eff m = ca_check arm_nanosleep i eff m)
      by (unfold check_syscall; rewrite E; reflexivity).
    rewrite Hc in H. autorewrite with arm_unfold in H.
    exact (check_nanosleep_ge _ _ _ _ _ _ _ H).
  - assert (Hc : check_syscall i eff m = ca_check arm_clock_gettime i eff m)
      by (unfold check_syscall; rewrite E; reflexivity).
    rewrite Hc in H. autorewrite with arm_unfold in H.
    exact (check_clock_gettime_ge _ _ _ _ _ _ _ H).
Qed.

(* =========================================================================
   The step
   ========================================================================= *)

Lemma clock_max_ge : forall ps q f,
  look_in ps q = Some f -> (clk (pe_model f) <= clock_max ps)%Z.
Proof.
  induction ps as [|[k x] r IH]; intros q f H; cbn [look_in] in H; [discriminate H|].
  unfold clock_max. cbn [List.fold_right snd]. fold (clock_max r).
  cbn [fst snd] in H. destruct (bv_eqb k q).
  - injection H as <-. unfold clk. lia.
  - specialize (IH q f H). lia.
Qed.

Lemma clock_max_range : forall ps, (0 <= clock_max ps < 2 ^ 64)%Z.
Proof.
  induction ps as [|[k x] r IH]; [cbn; lia|].
  unfold clock_max. cbn [List.fold_right snd]. fold (clock_max r).
  pose proof (bv_unsigned_in_range _ (m_clock (pe_model x))) as Hr.
  change (bv_modulus 64) with (2 ^ 64)%Z in Hr. lia.
Qed.

Lemma look_in_replace_same : forall ps p e',
  look_in ps p <> None -> look_in (replace_in ps p e') p = Some e'.
Proof.
  induction ps as [|[k x] r IH]; intros p e' H; cbn [look_in] in H; [contradiction|].
  cbn [replace_in fst]. destruct (bv_eqb k p) eqn:E.
  - cbn [look_in fst snd]. rewrite bv_eqb_same. reflexivity.
  - cbn [look_in fst snd]. rewrite E. cbn [fst snd] in H. rewrite E in H.
    exact (IH p e' H).
Qed.

(** The released step at a synced call keeps or raises the copy. *)
Lemma sstep_clock_ge : forall segs cfg c evs c',
  (match ms_svc_pending (cfg_ms c) with
   | Some x8 => List.existsb (Z.eqb (bv_unsigned x8)) multiproc_clock_sysnos
   | None => false
   end) = true ->
  sstep_cfg segs cfg c evs (SNext c') -> (clk (cfg_model c) <= clk (cfg_model c'))%Z.
Proof.
  intros segs cfg c evs c' Hp H.
  inversion H; subst; cbn [cfg_ms cfg_model] in Hp |- *.
  all: match goal with
       | Hs : ms_svc_pending ?s = None |- _ => rewrite Hs in Hp; discriminate Hp
       | Hs : ms_svc_pending ?s = Some _ |- _ => rewrite Hs in Hp
       end.
  all: match goal with
       | Hsp : syscall_spec (sys_input _ _ _) _ (Ok _ _ _) |- _ =>
           pose proof (syscall_spec_clock_ge _ _ _ _ _ Hsp) as Hg;
           cbn [in_sysno sys_input] in Hg; specialize (Hg Hp)
       end.
  all: first
    [ exact Hg
    | match goal with
      | Hm : materialize_model_accesses _ _ = Some _ |- _ =>
          unfold materialize_model_accesses in Hm;
          destruct (materialize_accesses _ _ _ _ _); [|discriminate Hm];
          injection Hm as <-; exact Hg
      end ].
Qed.

(** The producing arms, with what this file needs of each: the released
    step keeps its sync gate. *)
Lemma pstep_next_sync_cases : forall segs cfg p P evs P',
  pstep_at segs cfg p P evs (PNext P') ->
  exists e, look P p = Some e /\ pe_pid e = p /\
    ( (exists c', sstep_cfg segs cfg (pe_cfg (pcfg_shared P) e) evs (SNext c')
                  /\ sync_pending_b P e = false /\ P' = absorb P e c')
      \/ clone_pending_b (pe_cfg (pcfg_shared P) e) = true
      \/ wait4_intercept_b (pe_cfg (pcfg_shared P) e) = true
      \/ wait4_owned_b P e = true
      \/ (sync_pending_b P e = true /\ P' = sync_result P e)
      \/ root_pin_pending_b P e = true ).
Proof.
  intros segs cfg p P evs P' H. inversion H; subst;
    (eexists; split; [eassumption | split; [reflexivity|]]).
  all: first
    [ left; eexists; split; [eassumption | split; [assumption | reflexivity]]
    | right; left; eapply clone_success_pending; eassumption
    | right; right; left; assumption
    | right; right; right; left; assumption
    | right; right; right; right; left; split; [assumption | reflexivity]
    | right; right; right; right; right; assumption ].
Qed.

Lemma synced_not_other : forall (x8 : word) (n : Z),
  List.existsb (Z.eqb (bv_unsigned x8)) multiproc_clock_sysnos = true ->
  bv_unsigned x8 = n -> n <> 101%Z -> n <> 113%Z -> False.
Proof.
  intros x8 n H Hn H1 H2. cbn [multiproc_clock_sysnos List.existsb] in H.
  apply orb_true_iff in H as [E|H];
    [|apply orb_true_iff in H as [E|E]; [|discriminate E]];
    apply Z.eqb_eq in E; lia.
Qed.

(** THE MONOTONICITY.  After a step of an entry at 101 or 113, its copy is
    at least every copy the table held before the step. *)
Theorem pstep_clock_monotone : forall segs cfg p P evs P' e x8,
  look P p = Some e ->
  ms_svc_pending (pe_ms e) = Some x8 ->
  List.existsb (Z.eqb (bv_unsigned x8)) multiproc_clock_sysnos = true ->
  pstep_at segs cfg p P evs (PNext P') ->
  exists e', look P' p = Some e'
    /\ forall q f, look P q = Some f -> (clk (pe_model f) <= clk (pe_model e'))%Z.
Proof.
  intros segs cfg p P evs P' e x8 Hl Hs Hn H.
  destruct (pstep_next_sync_cases _ _ _ _ _ _ H) as (e1 & Hl1 & Hpid & Hcases).
  rewrite Hl in Hl1. injection Hl1 as <-. subst p.
  destruct Hcases as
    [ (c1 & Hss & Hsy & ->) | [ Hcp | [ Hwt | [ Hwo | [ (Hsy & ->) | Hrp ] ] ] ] ].
  - (* the released step: the copy was already the maximum *)
    unfold sync_pending_b in Hsy. rewrite Hs, Hn in Hsy. cbn [andb] in Hsy.
    apply orb_false_iff in Hsy as [Hsy _]. apply orb_false_iff in Hsy as [Hsy _].
    apply Z.ltb_ge in Hsy.
    assert (Hsyn : (match ms_svc_pending (cfg_ms (pe_cfg (pcfg_shared P) e)) with
                    | Some y => List.existsb (Z.eqb (bv_unsigned y)) multiproc_clock_sysnos
                    | None => false end) = true)
      by (cbn [cfg_ms pe_cfg]; rewrite Hs; exact Hn).
    pose proof (sstep_clock_ge _ _ _ _ _ Hsyn Hss) as Hg.
    exists (pe_absorb e c1). split.
    + unfold look, absorb. cbn [pcfg_procs].
      rewrite orphan_at_exit_map, look_in_orphan.
      rewrite look_in_replace_same by (unfold look in Hl; rewrite Hl; discriminate).
      cbn [option_map]. unfold orphan_slot.
      destruct (m_halted _); [|reflexivity].
      unfold orphan_one. cbn [fst snd]. rewrite bv_eqb_same. reflexivity.
    + intros q f Hf. pose proof (clock_max_ge _ _ _ Hf) as Hm.
      unfold clk in *.
      change (m_clock (pe_model (pe_absorb e c1))) with (m_clock (cfg_model c1)).
      change (m_clock (cfg_model (pe_cfg (pcfg_shared P) e))) with (m_clock (pe_model e)) in Hg.
      lia.
  - exfalso. unfold clone_pending_b, clone_sysno in Hcp. cbn [cfg_ms pe_cfg] in Hcp.
    rewrite Hs in Hcp. apply orb_true_iff in Hcp as [E|E]; apply Z.eqb_eq in E;
      exact (synced_not_other _ _ Hn E ltac:(lia) ltac:(lia)).
  - exfalso. unfold wait4_intercept_b in Hwt. cbn [cfg_ms pe_cfg] in Hwt. rewrite Hs in Hwt.
    apply andb_true_iff in Hwt as [E _]. apply Z.eqb_eq in E.
    exact (synced_not_other _ _ Hn E ltac:(lia) ltac:(lia)).
  - exfalso. destruct (wait4_owned_260 _ _ Hwo) as (y & Hy & E).
    rewrite Hs in Hy. injection Hy as <-.
    exact (synced_not_other _ _ Hn E ltac:(lia) ltac:(lia)).
  - (* the sync: the copy becomes the maximum *)
    exists (sync_entry P e). split.
    + unfold look, sync_result. cbn [pcfg_procs].
      apply look_in_replace_same. unfold look in Hl. rewrite Hl. discriminate.
    + intros q f Hf. pose proof (clock_max_ge _ _ _ Hf) as Hm.
      unfold clk in *.
      change (m_clock (pe_model (sync_entry P e)))
        with (Z_to_bv 64 (clock_max (pcfg_procs P))).
      rewrite word_small by exact (clock_max_range _). exact Hm.
  - (* the root pin: 101 and 113 are not getppid *)
    exfalso. unfold root_pin_pending_b in Hrp. rewrite Hs in Hrp.
    destruct (Z.eqb (bv_unsigned x8) 173) eqn:E; [|discriminate Hrp].
    apply Z.eqb_eq in E. exact (synced_not_other _ _ Hn E ltac:(lia) ltac:(lia)).
Qed.

(** At one entry the gate is closed. *)
Corollary sync_closed_one : forall c, sync_pending_b (one_proc c) (one_entry c) = false.
Proof. exact sync_pending_one. Qed.
