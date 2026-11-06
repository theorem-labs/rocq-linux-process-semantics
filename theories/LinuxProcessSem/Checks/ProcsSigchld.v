(** * LinuxProcessSem.Checks.ProcsSigchld — the SIGCHLD install bit across the core, and the decline it buys

    Not part of the trusted specification: QA on the multi-process core's
    reading of [State.procst_sigchld_dfl], in the sense of
    [Checks.Examples]'s header.  The released half is
    [Checks.ProcsSigchldFrame].

    The two [wait4] reap arms of [Procs] ([Procs.pstep_wait_reap],
    [Procs.pstep_wait_nohang_reap] and their [pstep_x_at] twins) require
    the caller's bit, and [Procs.wait4_refused_b] refuses a WNOHANG call
    of a caller without it that has a zombie child: under SIG_IGN or
    SA_NOCLDWAIT Linux reaps an exiting child itself ([do_notify_parent],
    kernel/signal.c, Linux v6.18.46, lines 2241-2261), so the table's
    zombie may not be Linux's.  The WNOHANG zero ([Procs.pstep_wait_nohang_zero])
    does not read the bit: with no zombie child and a live one, Linux's
    [__do_wait] answers 0 under either disposition (kernel/exit.c, lines
    1534-1539 and 1665-1709).

    - [sigchld_clear_wait4_declines] (and [_x]): a caller with a zombie
      child in the table and the bit clear gets no answer from the core,
      only the refusal.
    - THE NO-NARROWING INVARIANT, [sigchld_ok]: every entry of the table
      has the bit set.  [pstep_at_preserves_sigchld] keeps it over every
      step of the core ([pstep_cfg_preserves_sigchld], and
      [pstep_x_at_preserves_sigchld] wherever the extension agrees with
      the core); [sigchld_runs] carries it along a run, and
      [sigchld_reachable] from a launch whose model has the bit set.
      [sigchld_caller] then discharges the new premise of every gated arm
      at every reachable configuration, and [wait4_refused_b_dfl] says the
      refusal is the one it was before the gate, so from such a launch the
      core's [wait4] answers are exactly the answers it gave before.

    THE START CASE.  [sigchld_reachable]'s premise is the launch's bit,
    and [Run.valid_input] discharges it: it pins
    [State.in_sigchld_default] to [true] (SIG_DFL), [State.init_model]
    copies that into [State.procst_sigchld_dfl], and [Procs.one_entry]
    keeps the model's [ProcState] ([sigchld_launch]).  So
    [sigchld_reachable_valid] holds of every run from a valid launch with
    no start premise ([sigchld_reachable_inherited] likewise for
    [Run.valid_input_inherited]).  Every one of the 17 launch predicates of
    [Run], and [FinInput.finite_input], pins the field the same way:
    [sigchld_reachable_launch] takes the pin alone, and each predicate has
    its accessor ([valid_input_abort_sigchld_default] and its siblings) and
    corollary ([sigchld_reachable_abort] and its siblings).

    UNDER AN EXTENSION.  [pstep_x_at_preserves_sigchld_ext] keeps the
    invariant over every step of [Procs.pstep_x_at], with no agreement
    with the core, for any extension whose own answers keep a set bit
    ([ext_keeps_sigchld]; [no_ext_keeps_sigchld] here, and
    [Checks.NsSigchld.ns_ext_keeps_sigchld] for the namespace extension).
    [pxruns_sigchld_reachable] carries it along a run of
    [Procs.pstep_x_cfg], and [pxruns_sigchld_reachable_launch] starts it
    from a launch with any shared state. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run Procs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ProcsWellFormed ProcsWait4Gate ProcsChildPids ProcsSigchldFrame.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require NsCloneRefusers.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Ext.
From LinuxProcessSemantics.EquivalenceDefinition Require FinInput.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope bool_scope.

(* =========================================================================
   The decline
   ========================================================================= *)

(** A CALLER WITHOUT THE BIT IS NEVER ANSWERED FROM A ZOMBIE CHILD.  Every
    step of a caller with a zombie child in the table and the bit clear is
    the refusal: no reap, and no WNOHANG zero (which needs no zombie
    child).  (Its blocking [wait4] has no arm at all, which this statement
    also covers.) *)
Theorem sigchld_clear_wait4_declines : forall segs cfg p P e evs r,
  look P p = Some e ->
  wait4_owned_b P e = true ->
  m_sigchld_dfl (pe_model e) = false ->
  List.existsb pe_zombie_b (children_of P (pe_pid e)) = true ->
  pstep_at segs cfg p P evs r ->
  r = PError.
Proof.
  intros segs cfg p P e evs r Hl Hwo Hd Hz Hp. revert Hl Hwo Hd Hz.
  destruct Hp; intros Hl Hwo Hd Hz; try reflexivity;
    match goal with
    | H0 : look ?Q (pe_pid ?e0) = Some ?e0, Hl : look ?Q (pe_pid ?e0) = Some e |- _ =>
        rewrite H0 in Hl; injection Hl as Hl; subst e0
    end;
    first
    [ congruence
    | match goal with
      | Hs : clone_success_b _ _ = true |- _ =>
          rewrite (clone_pending_not_owned _ e (clone_success_pending _ _ Hs)) in Hwo;
          discriminate Hwo
      end
    | match goal with
      | Hsy : sync_pending_b _ _ = true |- _ =>
          rewrite (wait4_owned_not_sync _ e Hwo) in Hsy; discriminate Hsy
      end
    | match goal with
      | Hpin : root_pin_pending_b _ _ = true |- _ =>
          destruct (wait4_owned_260 _ e Hwo) as (y & Hy & Hy260);
          rewrite (root_pin_of_sysno _ _
                     (fun z Hz => ltac:(rewrite Hy in Hz; injection Hz as <-;
                                        rewrite Hy260; discriminate))) in Hpin;
          discriminate Hpin
      end ].
Qed.

Theorem sigchld_clear_wait4_declines_x : forall ext cenv segs cfg p P e evs r,
  look P p = Some e ->
  wait4_owned_b P e = true ->
  m_sigchld_dfl (pe_model e) = false ->
  List.existsb pe_zombie_b (children_of P (pe_pid e)) = true ->
  pstep_x_at ext cenv segs cfg p P evs r ->
  r = PError.
Proof.
  intros ext cenv segs cfg p P e evs r Hl Hwo Hd Hz Hp. revert Hl Hwo Hd Hz.
  destruct Hp; intros Hl Hwo Hd Hz; try reflexivity;
    match goal with
    | H0 : look ?Q (pe_pid ?e0) = Some ?e0, Hl : look ?Q (pe_pid ?e0) = Some e |- _ =>
        rewrite H0 in Hl; injection Hl as Hl; subst e0
    end;
    first
    [ congruence
    | match goal with
      | Hs : clone_success_b _ _ = true |- _ =>
          rewrite (clone_pending_not_owned _ e (clone_success_pending _ _ Hs)) in Hwo;
          discriminate Hwo
      end
    | match goal with
      | Hc : clone_pending_b _ = true |- _ =>
          rewrite (clone_pending_not_owned _ e Hc) in Hwo; discriminate Hwo
      end
    | match goal with
      | Hsy : sync_pending_b _ _ = true |- _ =>
          rewrite (wait4_owned_not_sync _ e Hwo) in Hsy; discriminate Hsy
      end
    | match goal with
      | Hpin : root_pin_pending_b _ _ = true |- _ =>
          destruct (wait4_owned_260 _ e Hwo) as (y & Hy & Hy260);
          rewrite (root_pin_of_sysno _ _
                     (fun z Hz => ltac:(rewrite Hy in Hz; injection Hz as <-;
                                        rewrite Hy260; discriminate))) in Hpin;
          discriminate Hpin
      end ].
Qed.

(** With the bit set the refusal is the one the gate had before it read
    the bit. *)
Lemma wait4_refused_b_dfl : forall segs P e,
  m_sigchld_dfl (pe_model e) = true ->
  wait4_refused_b segs P e
  = wait4_owned_b P e
    && negb (wait4_intercept_b (pe_cfg (pcfg_shared P) e))
    && (negb (wait4_nohang_shape_b segs e)
        || (List.existsb pe_zombie_b (children_of P (pe_pid e))
            && negb (wait4_nohang_reap_ok_b segs P e))).
Proof. intros segs P e H. unfold wait4_refused_b. rewrite H. reflexivity. Qed.

(* =========================================================================
   The invariant
   ========================================================================= *)

(** THE INVARIANT: every entry of the table has the bit set. *)
Definition sigchld_ok (P : pconfig) : Prop :=
  List.Forall (fun kv => m_sigchld_dfl (pe_model (snd kv)) = true) (pcfg_procs P).

(** Under it the new premise of every gated arm holds of every caller. *)
Lemma sigchld_caller : forall P p e,
  sigchld_ok P -> look P p = Some e -> m_sigchld_dfl (pe_model e) = true.
Proof.
  intros P p e H Hl. unfold look in Hl. apply look_in_In in Hl.
  unfold sigchld_ok in H. rewrite List.Forall_forall in H. exact (H _ Hl).
Qed.

Section Lists.
  Variable Q : Pid * ProcessEntry -> Prop.

  Lemma Forall_replace_in : forall ps p e',
    List.Forall Q ps -> Q (p, e') -> List.Forall Q (replace_in ps p e').
  Proof.
    induction ps as [|kv r IH]; intros p e' H Hq; cbn [replace_in]; [constructor|].
    inversion H as [|kv0 r0 Hkv Hr]; subst.
    destruct (bv_eqb (fst kv) p).
    - constructor; [exact Hq | exact Hr].
    - constructor; [exact Hkv | exact (IH p e' Hr Hq)].
  Qed.

  Lemma Forall_drop_in : forall ps p,
    List.Forall Q ps -> List.Forall Q (drop_in ps p).
  Proof.
    induction ps as [|kv r IH]; intros p H; cbn [drop_in]; [constructor|].
    inversion H as [|kv0 r0 Hkv Hr]; subst.
    destruct (bv_eqb (fst kv) p).
    - exact Hr.
    - constructor; [exact Hkv | exact (IH p Hr)].
  Qed.
End Lists.

Lemma sigchld_orphan_at_exit : forall m p ps,
  List.Forall (fun kv => m_sigchld_dfl (pe_model (snd kv)) = true) ps ->
  List.Forall (fun kv => m_sigchld_dfl (pe_model (snd kv)) = true)
    (orphan_at_exit m p ps).
Proof.
  intros m p ps H. unfold orphan_at_exit. destruct (m_halted m); cbv iota; [|exact H].
  unfold orphan_children. apply List.Forall_map.
  eapply List.Forall_impl; [|exact H].
  intros kv Hkv. cbv beta. unfold orphan_one.
  match goal with |- context [if ?b then _ else _] => destruct b end; exact Hkv.
Qed.

(** A first root-tid pin resolves the root's running children's parent
    pid ([Procs.root_children_ppid], [State.with_ppid]), which carries the
    bit. *)
Lemma sigchld_root_children : forall root t ps,
  List.Forall (fun kv => m_sigchld_dfl (pe_model (snd kv)) = true) ps ->
  List.Forall (fun kv => m_sigchld_dfl (pe_model (snd kv)) = true)
    (root_children_ppid root t ps).
Proof.
  intros root t ps H. unfold root_children_ppid. apply List.Forall_map.
  eapply List.Forall_impl; [|exact H].
  intros [q f] Hkv. cbv beta in *.
  destruct (root_child_ppid_one_model root t q f) as [E | E]; rewrite E; exact Hkv.
Qed.

Lemma sigchld_first_root_pin : forall P e m' ps,
  List.Forall (fun kv => m_sigchld_dfl (pe_model (snd kv)) = true) ps ->
  List.Forall (fun kv => m_sigchld_dfl (pe_model (snd kv)) = true)
    (first_root_pin_children P e m' ps).
Proof.
  intros P e m' ps H. unfold first_root_pin_children.
  destruct (bv_eqb (pe_pid e) (pcfg_root P)); [|exact H].
  destruct (m_tid (pe_model e)), (m_tid m');
    first [exact H | apply sigchld_root_children; exact H].
Qed.

(** An absorb keeps the invariant when the step's model keeps the bit. *)
Lemma sigchld_absorb : forall P e c',
  sigchld_ok P -> m_sigchld_dfl (cfg_model c') = true -> sigchld_ok (absorb P e c').
Proof.
  intros P e c' H Hc. unfold sigchld_ok, absorb. cbn [pcfg_procs].
  apply sigchld_orphan_at_exit.
  apply Forall_replace_in; [apply sigchld_first_root_pin; exact H|].
  exact Hc.
Qed.

(** The sync touches the clock, the UTS name and a stat pin, never the
    bit. *)
Lemma sigchld_sync_entry : forall P e,
  m_sigchld_dfl (pe_model (sync_entry P e)) = m_sigchld_dfl (pe_model e).
Proof.
  intros P e. unfold sync_entry, uts_fill, pin_fill. cbn [pe_model].
  repeat match goal with |- context [match ?x with _ => _ end] => destruct x end;
    reflexivity.
Qed.

(** A reap's entry keeps the bit of the caller. *)
Lemma sigchld_reap_entry : forall P e q eff model'',
  materialize_model_accesses (cfg_model (pe_cfg (pcfg_shared P) e))
    (syscall_effect_accesses eff) = Some model'' ->
  m_sigchld_dfl (clear_shared (reap_model q model'')) = m_sigchld_dfl (pe_model e).
Proof.
  intros P e q eff model'' Hm.
  transitivity (m_sigchld_dfl model''); [reflexivity|].
  rewrite (sd_materialize _ _ _ Hm). reflexivity.
Qed.

(** THE STEP: every step of the core keeps the invariant. *)
Theorem pstep_at_preserves_sigchld : forall segs cfg p P evs P',
  sigchld_ok P -> pstep_at segs cfg p P evs (PNext P') -> sigchld_ok P'.
Proof.
  intros segs cfg p P evs P' H Hs.
  inversion Hs; subst.
  - (* pstep_other: the released step keeps the bit *)
    match goal with
    | Hl : look ?Q (pe_pid ?e) = Some ?e, Hss : sstep_cfg _ _ _ _ (SNext ?c') |- _ =>
        apply sigchld_absorb; [exact H|];
        exact (sstep_sigchld_mono _ _ _ _ _ Hss (sigchld_caller _ _ _ H Hl))
    end.
  - (* pstep_clone: the parent's released step, and [child_proc] copies the bit *)
    match goal with
    | Hl : look ?Q (pe_pid ?e) = Some ?e, Hss : sstep_cfg _ _ _ _ (SNext ?c') |- _ =>
        unfold clone_result, sigchld_ok; cbn [pcfg_procs];
        apply List.Forall_app; split;
        [ apply Forall_replace_in; [exact H|];
          exact (sstep_sigchld_mono _ _ _ _ _ Hss (sigchld_caller _ _ _ H Hl))
        | constructor; [exact (sigchld_caller _ _ _ H Hl) | constructor] ]
    end.
  - (* pstep_wait_reap *)
    match goal with
    | Hl : look ?Q (pe_pid ?e) = Some ?e,
      Hm : materialize_model_accesses _ _ = Some ?model'' |- _ =>
        unfold sigchld_ok; cbn [pcfg_procs];
        apply Forall_drop_in; apply Forall_replace_in; [exact H|];
        cbv beta; cbn [snd pe_model];
        rewrite (sigchld_reap_entry _ _ _ _ _ Hm);
        exact (sigchld_caller _ _ _ H Hl)
    end.
  - (* pstep_wait_nohang_reap *)
    match goal with
    | Hl : look ?Q (pe_pid ?e) = Some ?e,
      Hm : materialize_model_accesses _ _ = Some ?model'' |- _ =>
        unfold wait4_reap_result, sigchld_ok; cbn [pcfg_procs];
        apply Forall_drop_in; apply Forall_replace_in; [exact H|];
        cbv beta; cbn [snd pe_model];
        rewrite (sigchld_reap_entry _ _ _ _ _ Hm);
        exact (sigchld_caller _ _ _ H Hl)
    end.
  - (* pstep_wait_nohang_zero *)
    match goal with
    | Hl : look ?Q (pe_pid ?e) = Some ?e |- _ =>
        unfold wait4_zero_result; apply sigchld_absorb; [exact H|];
        exact (sigchld_caller _ _ _ H Hl)
    end.
  - (* pstep_sync *)
    match goal with
    | Hl : look ?Q (pe_pid ?e) = Some ?e |- _ =>
        unfold sync_result, sigchld_ok; cbn [pcfg_procs];
        apply Forall_replace_in; [exact H|];
        cbv beta; cbn [snd]; rewrite sigchld_sync_entry;
        exact (sigchld_caller _ _ _ H Hl)
    end.
  - (* pstep_pin_root: the root's children's parent pid resolved, if
       this is the first pin *)
    match goal with
    | Hr : look ?Q (pcfg_root ?Q) = Some ?r |- _ =>
        unfold pin_root, sigchld_ok; cbn [pcfg_procs];
        apply Forall_replace_in;
        [ first
          [ exact H
          | match goal with
            | |- List.Forall _ (match ?x with _ => _ end) =>
                destruct x; first [exact H | apply sigchld_root_children; exact H]
            end ]
        | exact (sigchld_caller _ _ _ H Hr) ]
    end.
Qed.

Corollary pstep_cfg_preserves_sigchld : forall segs cfg P evs P',
  sigchld_ok P -> pstep_cfg segs cfg P evs (PNext P') -> sigchld_ok P'.
Proof.
  intros segs cfg P evs P' H (p & Hs).
  exact (pstep_at_preserves_sigchld _ _ _ _ _ _ H Hs).
Qed.

(** The extended relation, wherever it agrees with the core's. *)
Corollary pstep_x_at_preserves_sigchld : forall ext cenv segs cfg p P evs P',
  ext_agrees ext cenv segs P ->
  sigchld_ok P -> pstep_x_at ext cenv segs cfg p P evs (PNext P') -> sigchld_ok P'.
Proof.
  intros ext cenv segs cfg p P evs P' Hag H Hs.
  apply (pstep_at_preserves_sigchld segs cfg p P evs P' H).
  exact (proj1 (pstep_x_at_agree_iff ext cenv segs cfg p P evs (PNext P') Hag) Hs).
Qed.

(* =========================================================================
   Reachability
   ========================================================================= *)

(** Along any run of the core from a table that has it. *)
Theorem sigchld_runs : forall segs cfg P0 P,
  sigchld_ok P0 -> pruns segs cfg P0 P -> sigchld_ok P.
Proof.
  intros segs cfg P0 P H0 Hr. revert H0.
  induction Hr as [Q | Q evs Q' Q'' Hs _ IH]; intros H0; [exact H0|].
  apply IH. exact (pstep_cfg_preserves_sigchld _ _ _ _ _ H0 Hs).
Qed.

(** The launch: its one entry has the bit of the released model. *)
Lemma sigchld_ok_one_proc : forall c,
  m_sigchld_dfl (cfg_model c) = true -> sigchld_ok (one_proc c).
Proof.
  intros c H. unfold sigchld_ok, one_proc. cbn [pcfg_procs].
  constructor; [exact H | constructor].
Qed.

(** THE REACHABILITY COROLLARY: from a launch whose model has the bit set,
    every reachable table has it in every entry, so no gated arm's new
    premise ever fails ([sigchld_caller]). *)
Theorem sigchld_reachable : forall segs cfg c P,
  m_sigchld_dfl (cfg_model c) = true ->
  pruns segs cfg (one_proc c) P -> sigchld_ok P.
Proof.
  intros segs cfg c P H0 Hr.
  exact (sigchld_runs _ _ _ _ (sigchld_ok_one_proc c H0) Hr).
Qed.

(** THE START CASE, discharged: a valid launch has the bit. *)
Lemma sigchld_launch : forall segs pc ph sp brk0 mbase rnd lim inp,
  in_sigchld_default inp = true ->
  m_sigchld_dfl (cfg_model (init_config segs pc ph sp brk0 mbase rnd lim inp)) = true.
Proof.
  intros segs pc ph sp brk0 mbase rnd lim inp H.
  transitivity (in_sigchld_default inp); [reflexivity | exact H].
Qed.

(** Every reachable table of a run from a valid launch has the bit in
    every entry. *)
Theorem sigchld_reachable_valid : forall segs pc ph sp brk0 mbase rnd lim inp
    segs' cfg P,
  valid_input inp ->
  pruns segs' cfg (one_proc (init_config segs pc ph sp brk0 mbase rnd lim inp)) P ->
  sigchld_ok P.
Proof.
  intros segs pc ph sp brk0 mbase rnd lim inp segs' cfg P Hv Hr.
  exact (sigchld_reachable _ _ _ _
           (sigchld_launch segs pc ph sp brk0 mbase rnd lim inp
              (valid_input_sigchld_default inp Hv)) Hr).
Qed.

Theorem sigchld_reachable_inherited : forall segs pc ph sp brk0 mbase rnd lim inp
    segs' cfg P,
  valid_input_inherited inp ->
  pruns segs' cfg (one_proc (init_config segs pc ph sp brk0 mbase rnd lim inp)) P ->
  sigchld_ok P.
Proof.
  intros segs pc ph sp brk0 mbase rnd lim inp segs' cfg P Hv Hr.
  exact (sigchld_reachable _ _ _ _
           (sigchld_launch segs pc ph sp brk0 mbase rnd lim inp
              (valid_input_inherited_sigchld_default inp Hv)) Hr).
Qed.

(** EVERY LAUNCH PREDICATE.  The start case needs only the launch input's
    [in_sigchld_default inp = true], which each of the 17 launch predicates
    of [Run] and [FinInput.finite_input] ends with.  [sigchld_reachable_launch]
    is the one lemma; each predicate gets an accessor for its pin and a
    corollary ([valid_input] and [valid_input_inherited] have theirs above,
    through [Run]'s own accessors). *)
Theorem sigchld_reachable_launch : forall segs pc ph sp brk0 mbase rnd lim inp
    segs' cfg P,
  in_sigchld_default inp = true ->
  pruns segs' cfg (one_proc (init_config segs pc ph sp brk0 mbase rnd lim inp)) P ->
  sigchld_ok P.
Proof.
  intros segs pc ph sp brk0 mbase rnd lim inp segs' cfg P Hd Hr.
  exact (sigchld_reachable _ _ _ _
           (sigchld_launch segs pc ph sp brk0 mbase rnd lim inp Hd) Hr).
Qed.

(** The pin, read by shape from a predicate's conjuncts. *)
Local Ltac sigchld_pin :=
  let inp := fresh "inp" in let Hv := fresh "Hv" in
  intros inp Hv; red in Hv;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  assumption.

Lemma valid_input_abort_sigchld_default : forall inp,
  valid_input_abort inp -> in_sigchld_default inp = true.
Proof. sigchld_pin. Qed.
Lemma valid_input_either_sigchld_default : forall inp,
  valid_input_either inp -> in_sigchld_default inp = true.
Proof. sigchld_pin. Qed.
Lemma valid_input_sigpipe_ignored_sigchld_default : forall inp,
  valid_input_sigpipe_ignored inp -> in_sigchld_default inp = true.
Proof. sigchld_pin. Qed.
Lemma valid_input_sigpipe_either_sigchld_default : forall inp,
  valid_input_sigpipe_either inp -> in_sigchld_default inp = true.
Proof. sigchld_pin. Qed.
Lemma valid_input_channel_closed_sigchld_default : forall inp,
  valid_input_channel_closed inp -> in_sigchld_default inp = true.
Proof. sigchld_pin. Qed.
Lemma valid_input_channel_either_sigchld_default : forall inp,
  valid_input_channel_either inp -> in_sigchld_default inp = true.
Proof. sigchld_pin. Qed.
Lemma valid_input_paths_sigchld_default : forall inp,
  valid_input_paths inp -> in_sigchld_default inp = true.
Proof. sigchld_pin. Qed.
Lemma valid_input_sigpipe_kills_sigchld_default : forall inp,
  valid_input_sigpipe_kills inp -> in_sigchld_default inp = true.
Proof. sigchld_pin. Qed.
Lemma valid_input_sv39_sigchld_default : forall inp,
  valid_input_sv39 inp -> in_sigchld_default inp = true.
Proof. sigchld_pin. Qed.
Lemma valid_input_sv57_sigchld_default : forall inp,
  valid_input_sv57 inp -> in_sigchld_default inp = true.
Proof. sigchld_pin. Qed.
Lemma valid_input_va_any_sigchld_default : forall inp,
  valid_input_va_any inp -> in_sigchld_default inp = true.
Proof. sigchld_pin. Qed.
Lemma valid_input_hwcap_rv64gc_sigchld_default : forall inp,
  valid_input_hwcap_rv64gc inp -> in_sigchld_default inp = true.
Proof. sigchld_pin. Qed.
Lemma valid_input_hwcap_rv64gcv_sigchld_default : forall inp,
  valid_input_hwcap_rv64gcv inp -> in_sigchld_default inp = true.
Proof. sigchld_pin. Qed.
Lemma valid_input_abort_hwcap_rv64gc_sigchld_default : forall inp,
  valid_input_abort_hwcap_rv64gc inp -> in_sigchld_default inp = true.
Proof. sigchld_pin. Qed.
Lemma valid_input_abort_hwcap_rv64gcv_sigchld_default : forall inp,
  valid_input_abort_hwcap_rv64gcv inp -> in_sigchld_default inp = true.
Proof. sigchld_pin. Qed.
Lemma finite_input_sigchld_default : forall inp,
  FinInput.finite_input inp -> in_sigchld_default inp = true.
Proof. sigchld_pin. Qed.

(** One corollary per predicate: every reachable table has the bit in
    every entry. *)
Local Ltac sigchld_corollary acc :=
  let segs := fresh "segs" in let pc := fresh "pc" in let ph := fresh "ph" in
  let sp := fresh "sp" in let brk0 := fresh "brk0" in let mbase := fresh "mbase" in
  let rnd := fresh "rnd" in let lim := fresh "lim" in let inp := fresh "inp" in
  let segs' := fresh "segs'" in let cfg := fresh "cfg" in let P := fresh "P" in
  let Hv := fresh "Hv" in let Hr := fresh "Hr" in
  intros segs pc ph sp brk0 mbase rnd lim inp segs' cfg P Hv Hr;
  exact (sigchld_reachable_launch segs pc ph sp brk0 mbase rnd lim inp segs' cfg P
           (acc inp Hv) Hr).

Corollary sigchld_reachable_abort : forall segs pc ph sp brk0 mbase rnd lim inp segs' cfg P,
  valid_input_abort inp ->
  pruns segs' cfg (one_proc (init_config segs pc ph sp brk0 mbase rnd lim inp)) P -> sigchld_ok P.
Proof. sigchld_corollary valid_input_abort_sigchld_default. Qed.
Corollary sigchld_reachable_either : forall segs pc ph sp brk0 mbase rnd lim inp segs' cfg P,
  valid_input_either inp ->
  pruns segs' cfg (one_proc (init_config segs pc ph sp brk0 mbase rnd lim inp)) P -> sigchld_ok P.
Proof. sigchld_corollary valid_input_either_sigchld_default. Qed.
Corollary sigchld_reachable_sigpipe_ignored : forall segs pc ph sp brk0 mbase rnd lim inp segs' cfg P,
  valid_input_sigpipe_ignored inp ->
  pruns segs' cfg (one_proc (init_config segs pc ph sp brk0 mbase rnd lim inp)) P -> sigchld_ok P.
Proof. sigchld_corollary valid_input_sigpipe_ignored_sigchld_default. Qed.
Corollary sigchld_reachable_sigpipe_either : forall segs pc ph sp brk0 mbase rnd lim inp segs' cfg P,
  valid_input_sigpipe_either inp ->
  pruns segs' cfg (one_proc (init_config segs pc ph sp brk0 mbase rnd lim inp)) P -> sigchld_ok P.
Proof. sigchld_corollary valid_input_sigpipe_either_sigchld_default. Qed.
Corollary sigchld_reachable_channel_closed : forall segs pc ph sp brk0 mbase rnd lim inp segs' cfg P,
  valid_input_channel_closed inp ->
  pruns segs' cfg (one_proc (init_config segs pc ph sp brk0 mbase rnd lim inp)) P -> sigchld_ok P.
Proof. sigchld_corollary valid_input_channel_closed_sigchld_default. Qed.
Corollary sigchld_reachable_channel_either : forall segs pc ph sp brk0 mbase rnd lim inp segs' cfg P,
  valid_input_channel_either inp ->
  pruns segs' cfg (one_proc (init_config segs pc ph sp brk0 mbase rnd lim inp)) P -> sigchld_ok P.
Proof. sigchld_corollary valid_input_channel_either_sigchld_default. Qed.
Corollary sigchld_reachable_paths : forall segs pc ph sp brk0 mbase rnd lim inp segs' cfg P,
  valid_input_paths inp ->
  pruns segs' cfg (one_proc (init_config segs pc ph sp brk0 mbase rnd lim inp)) P -> sigchld_ok P.
Proof. sigchld_corollary valid_input_paths_sigchld_default. Qed.
Corollary sigchld_reachable_sigpipe_kills : forall segs pc ph sp brk0 mbase rnd lim inp segs' cfg P,
  valid_input_sigpipe_kills inp ->
  pruns segs' cfg (one_proc (init_config segs pc ph sp brk0 mbase rnd lim inp)) P -> sigchld_ok P.
Proof. sigchld_corollary valid_input_sigpipe_kills_sigchld_default. Qed.
Corollary sigchld_reachable_sv39 : forall segs pc ph sp brk0 mbase rnd lim inp segs' cfg P,
  valid_input_sv39 inp ->
  pruns segs' cfg (one_proc (init_config segs pc ph sp brk0 mbase rnd lim inp)) P -> sigchld_ok P.
Proof. sigchld_corollary valid_input_sv39_sigchld_default. Qed.
Corollary sigchld_reachable_sv57 : forall segs pc ph sp brk0 mbase rnd lim inp segs' cfg P,
  valid_input_sv57 inp ->
  pruns segs' cfg (one_proc (init_config segs pc ph sp brk0 mbase rnd lim inp)) P -> sigchld_ok P.
Proof. sigchld_corollary valid_input_sv57_sigchld_default. Qed.
Corollary sigchld_reachable_va_any : forall segs pc ph sp brk0 mbase rnd lim inp segs' cfg P,
  valid_input_va_any inp ->
  pruns segs' cfg (one_proc (init_config segs pc ph sp brk0 mbase rnd lim inp)) P -> sigchld_ok P.
Proof. sigchld_corollary valid_input_va_any_sigchld_default. Qed.
Corollary sigchld_reachable_hwcap_rv64gc : forall segs pc ph sp brk0 mbase rnd lim inp segs' cfg P,
  valid_input_hwcap_rv64gc inp ->
  pruns segs' cfg (one_proc (init_config segs pc ph sp brk0 mbase rnd lim inp)) P -> sigchld_ok P.
Proof. sigchld_corollary valid_input_hwcap_rv64gc_sigchld_default. Qed.
Corollary sigchld_reachable_hwcap_rv64gcv : forall segs pc ph sp brk0 mbase rnd lim inp segs' cfg P,
  valid_input_hwcap_rv64gcv inp ->
  pruns segs' cfg (one_proc (init_config segs pc ph sp brk0 mbase rnd lim inp)) P -> sigchld_ok P.
Proof. sigchld_corollary valid_input_hwcap_rv64gcv_sigchld_default. Qed.
Corollary sigchld_reachable_abort_hwcap_rv64gc : forall segs pc ph sp brk0 mbase rnd lim inp segs' cfg P,
  valid_input_abort_hwcap_rv64gc inp ->
  pruns segs' cfg (one_proc (init_config segs pc ph sp brk0 mbase rnd lim inp)) P -> sigchld_ok P.
Proof. sigchld_corollary valid_input_abort_hwcap_rv64gc_sigchld_default. Qed.
Corollary sigchld_reachable_abort_hwcap_rv64gcv : forall segs pc ph sp brk0 mbase rnd lim inp segs' cfg P,
  valid_input_abort_hwcap_rv64gcv inp ->
  pruns segs' cfg (one_proc (init_config segs pc ph sp brk0 mbase rnd lim inp)) P -> sigchld_ok P.
Proof. sigchld_corollary valid_input_abort_hwcap_rv64gcv_sigchld_default. Qed.
Corollary sigchld_reachable_finite : forall segs pc ph sp brk0 mbase rnd lim inp segs' cfg P,
  FinInput.finite_input inp ->
  pruns segs' cfg (one_proc (init_config segs pc ph sp brk0 mbase rnd lim inp)) P -> sigchld_ok P.
Proof. sigchld_corollary finite_input_sigchld_default. Qed.

(* =========================================================================
   Under an extension
   ========================================================================= *)

(** An extension whose own answers keep a set bit.  The core's arms keep
    it by the lemmas above; what an extension answers for a call it claims
    is the extension's, so this is its obligation (as
    [Checks.ProcsCloneRefusers.ext_keeps_clone_refusers] is for the
    refusers).  [Checks.NsSigchld.ns_ext_keeps_sigchld] discharges it for
    the namespace extension. *)
Definition ext_keeps_sigchld (ext : ExtSpec) : Prop :=
  forall i m ctx st eff m' ctx' st' evs,
    ext_spec ext i m ctx st (EOk eff m' ctx' st' evs) ->
    m_sigchld_dfl m = true -> m_sigchld_dfl m' = true.

Lemma no_ext_keeps_sigchld : ext_keeps_sigchld no_ext.
Proof. intros i m ctx st eff m' ctx' st' evs H. hnf in H. destruct H. Qed.

(** A process's step under such an extension keeps a set bit. *)
Lemma xsstep_sigchld_mono : forall ext segs cfg ctx st c evs c' ctx' st',
  ext_keeps_sigchld ext ->
  xsstep ext segs cfg ctx st c evs (SNext c') ctx' st' ->
  m_sigchld_dfl (cfg_model c) = true -> m_sigchld_dfl (cfg_model c') = true.
Proof.
  intros ext segs cfg ctx st c evs c' ctx' st' Hext H Hb.
  inversion H; subst; cbn [cfg_model] in *.
  - match goal with Hs : sstep_cfg _ _ _ _ _ |- _ =>
      exact (sstep_sigchld_mono _ _ _ _ _ Hs Hb) end.
  - match goal with
    | He : ext_spec _ _ _ _ _ (EOk _ ?m1 _ _ _),
      Hm : materialize_model_accesses ?m1 _ = Some _ |- _ =>
        rewrite (sd_materialize _ _ _ Hm); exact (Hext _ _ _ _ _ _ _ _ _ He Hb)
    end.
  - match goal with He : ext_spec _ _ _ _ _ (EOk _ _ _ _ _) |- _ =>
      exact (Hext _ _ _ _ _ _ _ _ _ He Hb) end.
  - match goal with He : ext_spec _ _ _ _ _ (EOk _ _ _ _ _) |- _ =>
      exact (Hext _ _ _ _ _ _ _ _ _ He Hb) end.
Qed.

(** THE STEP UNDER AN EXTENSION: every step of [Procs.pstep_x_at] keeps
    the invariant, for any extension whose own answers keep a set bit.  No
    agreement with the core is assumed. *)
Theorem pstep_x_at_preserves_sigchld_ext : forall ext cenv segs cfg p P evs P',
  ext_keeps_sigchld ext ->
  sigchld_ok P -> pstep_x_at ext cenv segs cfg p P evs (PNext P') -> sigchld_ok P'.
Proof.
  intros ext cenv segs cfg p P evs P' Hext H Hs.
  inversion Hs; subst.
  - (* px_other: the extension's step or the released one, absorbed *)
    match goal with
    | Hl : look ?Q (pe_pid ?e) = Some ?e, Hx : xsstep _ _ _ _ _ _ _ (SNext ?c') _ _ |- _ =>
        unfold absorb_x, sigchld_ok; cbn [pcfg_procs];
        apply sigchld_orphan_at_exit;
        apply Forall_replace_in; [apply sigchld_first_root_pin; exact H|];
        exact (xsstep_sigchld_mono _ _ _ _ _ _ _ _ _ _ Hext Hx (sigchld_caller _ _ _ H Hl))
    end.
  - (* px_clone: the parent's released step, and [child_proc] copies the bit *)
    match goal with |- context [with_ret _ ?rt] => destruct rt end;
    match goal with
    | Hl : look ?Q (pe_pid ?e) = Some ?e, Hss : sstep_cfg _ _ _ _ (SNext ?c') |- _ =>
        unfold clone_result_x, sigchld_ok; cbn [pcfg_procs];
        apply List.Forall_app; split;
        [ apply Forall_replace_in; [exact H|];
          exact (sstep_sigchld_mono _ _ _ _ _ Hss (sigchld_caller _ _ _ H Hl))
        | constructor; [exact (sigchld_caller _ _ _ H Hl) | constructor] ]
    end.
  - (* px_clone_fail: the released step under the clone's filter *)
    match goal with
    | Hl : look ?Q (pe_pid ?e) = Some ?e, Hf : clone_fail_step _ _ _ _ _ _ _ _ _ ?c' |- _ =>
        unfold clone_fail_step in Hf;
        unfold absorb_x, sigchld_ok; cbn [pcfg_procs];
        apply sigchld_orphan_at_exit;
        apply Forall_replace_in; [apply sigchld_first_root_pin; exact H|];
        destruct Hf as [Hs' | (Hs' & _)];
        exact (sstep_sigchld_mono _ _ _ _ _ Hs' (sigchld_caller _ _ _ H Hl))
    end.
  - (* px_wait_reap *)
    match goal with
    | Hl : look ?Q (pe_pid ?e) = Some ?e,
      Hm : materialize_model_accesses _ _ = Some ?model'' |- _ =>
        unfold sigchld_ok; cbn [pcfg_procs];
        apply Forall_drop_in; apply Forall_replace_in; [exact H|];
        cbv beta; cbn [snd pe_model];
        rewrite (sigchld_reap_entry _ _ _ _ _ Hm);
        exact (sigchld_caller _ _ _ H Hl)
    end.
  - (* px_wait_nohang_reap *)
    match goal with
    | Hl : look ?Q (pe_pid ?e) = Some ?e,
      Hm : materialize_model_accesses _ _ = Some ?model'' |- _ =>
        unfold wait4_reap_result, sigchld_ok; cbn [pcfg_procs];
        apply Forall_drop_in; apply Forall_replace_in; [exact H|];
        cbv beta; cbn [snd pe_model];
        rewrite (sigchld_reap_entry _ _ _ _ _ Hm);
        exact (sigchld_caller _ _ _ H Hl)
    end.
  - (* px_wait_nohang_zero *)
    match goal with
    | Hl : look ?Q (pe_pid ?e) = Some ?e |- _ =>
        unfold wait4_zero_result; apply sigchld_absorb; [exact H|];
        exact (sigchld_caller _ _ _ H Hl)
    end.
  - (* px_sync *)
    match goal with
    | Hl : look ?Q (pe_pid ?e) = Some ?e |- _ =>
        unfold sync_result, sigchld_ok; cbn [pcfg_procs];
        apply Forall_replace_in; [exact H|];
        cbv beta; cbn [snd]; rewrite sigchld_sync_entry;
        exact (sigchld_caller _ _ _ H Hl)
    end.
  - (* px_pin_root *)
    match goal with
    | Hr : look ?Q (pcfg_root ?Q) = Some ?r |- _ =>
        unfold pin_root, sigchld_ok; cbn [pcfg_procs];
        apply Forall_replace_in;
        [ first
          [ exact H
          | match goal with
            | |- List.Forall _ (match ?x with _ => _ end) =>
                destruct x; first [exact H | apply sigchld_root_children; exact H]
            end ]
        | exact (sigchld_caller _ _ _ H Hr) ]
    end.
Qed.

Corollary pstep_x_cfg_preserves_sigchld_ext : forall ext cenv segs cfg P evs P',
  ext_keeps_sigchld ext ->
  sigchld_ok P -> pstep_x_cfg ext cenv segs cfg P evs (PNext P') -> sigchld_ok P'.
Proof.
  intros ext cenv segs cfg P evs P' Hext H (p & Hs).
  exact (pstep_x_at_preserves_sigchld_ext _ _ _ _ _ _ _ _ Hext H Hs).
Qed.

(** Along any run of [Procs.pstep_x_cfg] ([Checks.NsCloneRefusers.pxruns])
    under such an extension. *)
Theorem pxruns_sigchld_reachable : forall ext cenv segs cfg P Q,
  ext_keeps_sigchld ext ->
  sigchld_ok P -> NsCloneRefusers.pxruns ext cenv segs cfg P Q -> sigchld_ok Q.
Proof.
  intros ext cenv segs cfg P Q Hext H0 Hr.
  induction Hr as [P0 | P0 evs P1 P2 Hs _ IH]; [exact H0|].
  apply IH. exact (pstep_x_cfg_preserves_sigchld_ext _ _ _ _ _ _ _ Hext H0 Hs).
Qed.

(** The launch, with any shared state: its one entry has the launch's bit. *)
Lemma sigchld_ok_one_proc_shared : forall c sh,
  m_sigchld_dfl (cfg_model c) = true ->
  sigchld_ok (mkPCfg (pcfg_procs (one_proc c)) (pcfg_root (one_proc c)) sh).
Proof. intros c sh H. exact (sigchld_ok_one_proc c H). Qed.

(** From any launch whose input pins [in_sigchld_default] to [true] (every
    launch predicate above does), with any shared state, under any
    extension whose own answers keep a set bit. *)
Corollary pxruns_sigchld_reachable_launch : forall ext cenv segs pc ph sp brk0 mbase rnd lim
    inp sh segs' cfg Q,
  ext_keeps_sigchld ext ->
  in_sigchld_default inp = true ->
  NsCloneRefusers.pxruns ext cenv segs' cfg
    (mkPCfg (pcfg_procs (one_proc (init_config segs pc ph sp brk0 mbase rnd lim inp)))
            (pcfg_root (one_proc (init_config segs pc ph sp brk0 mbase rnd lim inp))) sh) Q ->
  sigchld_ok Q.
Proof.
  intros ext cenv segs pc ph sp brk0 mbase rnd lim inp sh segs' cfg Q Hext Hd Hr.
  exact (pxruns_sigchld_reachable _ _ _ _ _ _ Hext
           (sigchld_ok_one_proc_shared _ sh
              (sigchld_launch segs pc ph sp brk0 mbase rnd lim inp Hd)) Hr).
Qed.

(** The extension that claims nothing ([Ext.no_ext]). *)
Corollary pxruns_sigchld_reachable_no_ext : forall cenv segs cfg c sh Q,
  m_sigchld_dfl (cfg_model c) = true ->
  NsCloneRefusers.pxruns no_ext cenv segs cfg
    (mkPCfg (pcfg_procs (one_proc c)) (pcfg_root (one_proc c)) sh) Q ->
  sigchld_ok Q.
Proof.
  intros cenv segs cfg c sh Q Hc Hr.
  exact (pxruns_sigchld_reachable _ _ _ _ _ _ no_ext_keeps_sigchld
           (sigchld_ok_one_proc_shared c sh Hc) Hr).
Qed.

Print Assumptions sigchld_reachable.
Print Assumptions sigchld_clear_wait4_declines.
Print Assumptions sigchld_reachable_valid.
Print Assumptions sigchld_reachable_launch.
Print Assumptions sigchld_reachable_abort.
Print Assumptions sigchld_reachable_finite.
Print Assumptions pstep_x_at_preserves_sigchld_ext.
Print Assumptions pxruns_sigchld_reachable.
Print Assumptions pxruns_sigchld_reachable_launch.
