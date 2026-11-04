(** * LinuxProcessSem.Checks.KillFree — no death by a signal while every kill gate is closed

    Not part of the trusted specification: a theorem ABOUT it.

    [Run.kill_frame] is the claim that, from a running model whose five
    kill gates are closed ([Run.kill_off]: the abort, SIGPIPE and
    self-kill declarations clear, nothing pending), no syscall outcome opens a
    gate, records a kill or emits a [State.KillEv].  This file PROVES it,
    arm by arm over the dispatcher [Checks.Sys.Dispatch.checked_table],
    and carries it to [Specs.syscall_spec] through
    [Checks.ExecutableSpecs.check_syscall_ok_iff]: [kill_frame_holds].

    With it, [Run.run_kill_off] closes: [valid_input_no_kill] says that
    no trace of a run under [Run.valid_input] -- unconfigured or under
    any [Run.SpuriousCfg] -- carries a death by a signal, and
    [valid_input_error_free_unkilled_iff] says what that means for the
    top statements: under [Run.valid_input], [Equivalence.error_free]
    and [Equivalence.error_free_unkilled] are the same predicate of a
    run.

    THE SHAPE IS [Checks.VmMapsDisjoint]'s.  Each arm gets a [_kf] lemma
    that unfolds its checker exactly as that file's [_frame] lemma does
    and then runs one tactic, [kf_frame], which splits every branch of
    the checker and closes each by conversion: every setter but
    [State.with_killed] carries the five gates and [State.m_killed]
    across, and the branches that reach [with_killed] are each behind a
    gate the hypotheses close.  [checked_table_kill_free] is the
    [Forall] over the table, so an arm added to the dispatcher without a
    [_kf] lemma fails the build here, by name.

    WHAT THIS REPLACES.  The published model stated the abort half of
    this claim as a HYPOTHESIS, [Run.decl_off_frame], consumed by
    [Run.sstep_off_no_kill] and [Run.star_off_no_kill].  That hypothesis
    had no running premise, so a model a SIGABRT had already killed met
    it and [rt_sigprocmask] carried the kill through: it was false, and
    the two lemmas held only vacuously.  [Run.kill_frame] has the running
    premise and covers SIGPIPE too, and this file discharges it. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs VmMapsDisjoint.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
Import ListNotations.
Open Scope bv_scope.

(** What one checker outcome owes: from a model with the gates closed
    and no kill recorded, the post-model has the same, and the events
    carry no kill. *)
Definition kill_post (m m' : Model) (evs : list event) : Prop :=
  kill_off m -> m_killed m = None ->
  kill_off m' /\ m_killed m' = None /\ no_kill evs.

(* -------------------------------------------------------------------------
   The three gated sites, each closed by the gate it sits behind
   ------------------------------------------------------------------------- *)

(** SIGPIPE: with the death undeclared, a write that would raise the
    signal either declines or, at SIG_IGN, leaves the model alone. *)
Lemma raise_sigpipe_off : forall m,
  m_sigpipe_terminal m = false -> sigpipe_declines m = false ->
  raise_sigpipe m = m.
Proof.
  intros m Ht Hd. unfold sigpipe_declines in Hd. rewrite Ht in Hd.
  unfold raise_sigpipe.
  destruct (m_sigpipe_default m) eqn:E; [cbn in Hd; discriminate Hd | reflexivity].
Qed.

(** The delivery inside [rt_sigprocmask]: with nothing pending it only
    installs the mask. *)
Lemma sigmask_deliver_model_off : forall new m,
  m_sigabrt_pending m = false -> m_sigpipe_pending m = false ->
  sigmask_deliver_model new m = with_sigmask new m.
Proof.
  intros new m Hp Hq. unfold sigmask_deliver_model. rewrite Hp, Hq. reflexivity.
Qed.

(* -------------------------------------------------------------------------
   The tactic
   ------------------------------------------------------------------------- *)

Lemma check_write_oset_copyins_kf_model : forall reads i oset old eff m1 m' evs,
  check_write_oset_copyins reads i oset old eff m1 = CheckOk m' evs ->
  m' = m1 /\ evs = [].
Proof.
  intros reads i oset old eff m1 m' evs H. unfold check_write_oset_copyins in H.
  destruct (check_write_oset i oset old (clear_copyins eff) m1) as [m2 evs2| |] eqn:E;
    try discriminate.
  destruct (access_ranges_eqb (eff_copyins eff) reads); [|discriminate].
  injection H as <- <-. apply check_write_oset_ok_iff in E.
  destruct E as (-> & -> & _). split; reflexivity.
Qed.

(** One step of taking a checker hypothesis apart.  [Checks.VmMapsDisjoint]'s
    [vm_step], with the event list kept: the conclusion here is about the
    events as well as the model. *)
Ltac kf_step H :=
  match type of H with
  | CheckReject = CheckOk _ _ => discriminate H
  | CheckUnmodeled = CheckOk _ _ => discriminate H
  | CheckOk _ _ = CheckOk _ _ => injection H as <- <-
  | check_ret_only _ _ _ _ = CheckOk _ _ =>
      apply check_ret_only_ok_iff in H;
      let H1 := fresh in let H2 := fresh in
      destruct H as (_ & H1 & H2); subst
  | check_ret_only_copyins _ _ _ _ _ = CheckOk _ _ =>
      apply check_ret_only_copyins_ok_iff in H;
      let H1 := fresh in let H2 := fresh in
      destruct H as (_ & H1 & H2); subst
  | check_write_oset _ _ _ _ _ = CheckOk _ _ =>
      apply check_write_oset_ok_iff in H;
      let H1 := fresh in let H2 := fresh in
      destruct H as (H1 & H2 & _); subst
  | check_write_oset_copyins _ _ _ _ _ _ = CheckOk _ _ =>
      apply check_write_oset_copyins_kf_model in H;
      let H1 := fresh in let H2 := fresh in
      destruct H as (H1 & H2); subst
  | Prelude.check_copyins_after _ _ _ = CheckOk _ _ =>
      apply check_copyins_after_model in H
  | check_copyin_prefix _ _ _ = CheckOk _ _ =>
      apply check_copyin_prefix_model in H
  | check_copyins _ _ _ = CheckOk _ _ => apply check_copyins_model in H
  | context [ if ?b then _ else _ ] => destruct b eqn:?
  | context [ match ?x with _ => _ end ] => destruct x eqn:?
  end.

(** One gate of the post-model: either it is a literal (a setter wrote
    it), or every setter on the way carried it across from [m], which is
    conversion. *)
Ltac kf_fld f m H :=
  first [ reflexivity | (transitivity (f m); [reflexivity | exact H]) ].

(** The events: none of the lists a checker builds holds a [KillEv]. *)
Ltac kf_ev :=
  let Hin := fresh "Hin" in
  intros ? ? Hin;
  repeat (apply in_app_or in Hin; destruct Hin as [Hin | Hin]);
  first
  [ exact Hin
  | (apply in_map_iff in Hin;
     let Heq := fresh in destruct Hin as (? & Heq & _); discriminate Heq)
  | (cbn in Hin;
     repeat (destruct Hin as [Hin | Hin]; [discriminate Hin |]);
     exact Hin) ].

(** THE m_proc ROUTE.  Most post-models keep [State.m_proc] whole, and
    then all four gates and [State.m_killed] come across at once.  Most
    such post-models are a stack of setters, equal to [m] on [m_proc] by
    conversion; the memory-map wrappers below recurse or branch, and
    need their own lemma. *)
Lemma m_proc_forget_vm_ranges : forall rs m,
  m_proc (forget_vm_ranges rs m) = m_proc m.
Proof.
  induction rs as [|[a n] rs IH]; intros m; [reflexivity|].
  cbn [forget_vm_ranges]. rewrite IH. reflexivity.
Qed.

Lemma m_proc_with_brk_next : forall m req r,
  m_proc (with_brk_next m req r) = m_proc m.
Proof.
  intros m req r. unfold with_brk_next. cbv zeta.
  rewrite m_proc_forget_vm_ranges. reflexivity.
Qed.

Lemma m_proc_with_mmap_backing : forall flags a n m,
  m_proc (with_mmap_backing flags a n m) = m_proc m.
Proof.
  intros flags a n m. unfold with_mmap_backing.
  destruct (mmap_noreserve_b flags); reflexivity.
Qed.

Lemma m_proc_with_mmap_replacement : forall flags a n m,
  m_proc (with_mmap_replacement flags a n m) = m_proc m.
Proof.
  intros flags a n m. unfold with_mmap_replacement.
  rewrite m_proc_with_mmap_backing. reflexivity.
Qed.

Create HintDb kf_proc.
#[local] Hint Rewrite m_proc_forget_vm_ranges m_proc_with_brk_next
  m_proc_with_mmap_backing m_proc_with_mmap_replacement : kf_proc.

Lemma kill_post_proc : forall m m' evs,
  m_proc m' = m_proc m -> no_kill evs ->
  kill_off m -> m_killed m = None ->
  kill_off m' /\ m_killed m' = None /\ no_kill evs.
Proof.
  intros m m' evs Hp Hev Hoff Hk.
  split; [exact (kill_off_proc _ _ Hp Hoff) |].
  split; [unfold m_killed; rewrite Hp; exact Hk | exact Hev].
Qed.

(** Close a branch: the [m_proc] route first, and field by field for the
    post-models that rebuild [State.ProcState] -- [with_halted],
    [with_sigmask], [with_tid] and the like, which write other fields
    and carry the gates. *)
Ltac kf_close m Hoff Hk :=
  first
  [ (apply (kill_post_proc m);
     [ first [ reflexivity | (autorewrite with kf_proc; reflexivity) ]
     | kf_ev | exact Hoff | exact Hk ])
  | (let Ha := fresh "Ha" in let Hp := fresh "Hp" in
     let Ht := fresh "Ht" in let Hq := fresh "Hq" in
     let Hs := fresh "Hs" in
     pose proof Hoff as (Ha & Hp & Ht & Hq & Hs);
     try rewrite !(sigmask_deliver_model_off _ _ Hp Hq);
     unfold kill_off;
     refine (conj (conj _ (conj _ (conj _ (conj _ _)))) (conj _ _));
     [ kf_fld m_abort_terminal m Ha | kf_fld m_sigabrt_pending m Hp
     | kf_fld m_sigpipe_terminal m Ht | kf_fld m_sigpipe_pending m Hq
     | kf_fld m_selfkill_terminal m Hs
     | kf_fld m_killed m Hk | kf_ev ]) ].

(** The atomic sub-checkers [kf_step] does not open, as [vm_done] has
    them in [Checks.VmMapsDisjoint]. *)
Lemma check_efault_or_kf : forall fb eff m m' evs,
  check_efault_or fb eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros fb eff m m' evs H Hoff Hk. unfold check_efault_or in H.
  repeat kf_step H; kf_close m Hoff Hk.
Qed.

Lemma check_sigpipe_write_kf : forall eff m m' evs,
  check_sigpipe_write eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros eff m m' evs H Hoff Hk. pose proof Hoff as (_ & _ & Ht & _).
  unfold check_sigpipe_write in H.
  destruct (sigpipe_declines m) eqn:Hd; cbv iota in H; [discriminate H|].
  apply check_ret_only_ok_iff in H. destruct H as (_ & -> & ->).
  rewrite (raise_sigpipe_off m Ht Hd).
  split; [exact Hoff | split; [exact Hk | intros ? ? []]].
Qed.

Lemma check_sigpipe_writev_kf : forall reads eff m m' evs,
  check_sigpipe_writev reads eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros reads eff m m' evs H Hoff Hk. pose proof Hoff as (_ & _ & Ht & _).
  unfold check_sigpipe_writev in H.
  destruct (sigpipe_declines m) eqn:Hd; cbv iota in H; [discriminate H|].
  apply check_ret_only_copyins_ok_iff in H. destruct H as (_ & -> & ->).
  rewrite (raise_sigpipe_off m Ht Hd).
  split; [exact Hoff | split; [exact Hk | intros ? ? []]].
Qed.

(** The new-descriptor answer of [openat] and its kin.  The model it
    installs is [mk fd]; the premise asks that one to owe what an outcome
    owes, which [kf_done] discharges with [kf_close] -- some of these
    models rebuild [State.ProcState] (the stat pins live there), so the
    premise is the gate fields' and not [State.m_proc]'s. *)
Lemma check_open_result_kf : forall eff m mk m' evs,
  check_open_result eff m mk = CheckOk m' evs ->
  (forall fd, kill_post m (mk fd) []) ->
  kill_post m m' evs.
Proof.
  intros eff m mk m' evs H Hmk Hoff Hk.
  unfold check_open_result, check_new_fd_result in H.
  repeat kf_step H.
  all: first
    [ kf_close m Hoff Hk
    | (split; [exact (proj1 (Hmk _ Hoff Hk)) |];
       split; [exact (proj1 (proj2 (Hmk _ Hoff Hk))) | intros ? ? []]) ].
Qed.

(** [readv]'s body after the iovecs are imported; [check_readv] leaves it
    folded, as [Checks.VmMapsDisjoint.check_readv_imported_frame] has it. *)
Lemma check_readv_imported_kf : forall i fd r iovs0 eff m m' evs,
  check_readv_imported i fd r iovs0 eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i fd r iovs0 eff m m' evs H Hoff Hk.
  unfold check_readv_imported in H. cbv beta iota zeta in H.
  repeat (kf_step H
          || exact (check_efault_or_kf _ _ _ _ _ H Hoff Hk)
          || elim (check_readv_gap_frame _ _ H));
  kf_close m Hoff Hk.
Qed.

Ltac kf_done H Hoff Hk :=
  first
  [ exact (check_efault_or_kf _ _ _ _ _ H Hoff Hk)
  | exact (check_sigpipe_write_kf _ _ _ _ H Hoff Hk)
  | exact (check_sigpipe_writev_kf _ _ _ _ _ H Hoff Hk)
  | elim (check_readv_gap_frame _ _ H)
  | exact (check_readv_imported_kf _ _ _ _ _ _ _ _ H Hoff Hk)
  | (match type of Hoff with
     | kill_off ?m0 =>
         refine (check_open_result_kf _ _ _ _ _ H _ Hoff Hk);
         let fd := fresh "fd" in let Ho := fresh "Ho" in let Hk2 := fresh "Hk2" in
         intros fd Ho Hk2; kf_close m0 Ho Hk2
     end) ].

(** [cbv beta iota zeta] first: an [intros] pattern that took the effect
    apart leaves a [match] on a constructor in [H], which [kf_step] would
    otherwise take for a case to split. *)
Ltac kf_frame H m Hoff Hk :=
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk); kf_close m Hoff Hk.

(* -------------------------------------------------------------------------
   The arms whose checker reaches a gate
   ------------------------------------------------------------------------- *)

(** [kill] declines outright while the self-kill declaration is clear,
    and [tkill] and [tgkill] while the abort declaration is. *)
Lemma check_kill_kf : forall pid sig eff m m' evs,
  check_kill pid sig eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros pid sig eff m m' evs H (_ & _ & _ & _ & Hs) _.
  unfold check_kill in H. rewrite Hs in H. cbv beta iota delta [negb] in H.
  discriminate H.
Qed.

Lemma check_tkill_kf : forall pid sig eff m m' evs,
  check_tkill pid sig eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros pid sig eff m m' evs H (Ha & _) _.
  unfold check_tkill in H. rewrite Ha in H. cbv beta iota delta [negb] in H.
  discriminate H.
Qed.

Lemma check_tgkill_kf : forall tgid pid sig eff m m' evs,
  check_tgkill tgid pid sig eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros tgid pid sig eff m m' evs H (Ha & _) _.
  unfold check_tgkill in H. rewrite Ha in H. cbv beta iota delta [negb] in H.
  discriminate H.
Qed.

(** [rt_sigprocmask] delivers a pending signal; with neither pending it
    only installs the mask ([sigmask_deliver_model_off], which
    [kf_close] applies). *)
Lemma check_rt_sigprocmask_kf : forall i how nset oset ss eff m m' evs,
  check_rt_sigprocmask i how nset oset ss eff m = CheckOk m' evs ->
  kill_post m m' evs.
Proof.
  intros i how nset oset ss eff m m' evs H Hoff Hk.
  unfold check_rt_sigprocmask in H. cbv zeta in H.
  kf_frame H m Hoff Hk.
Qed.

(* -------------------------------------------------------------------------
   Every other arm, unfolded as [Checks.VmMapsDisjoint] unfolds it
   ------------------------------------------------------------------------- *)

Lemma check_brk_kf : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros req [ret ws zs us cs ci] m m' evs H Hoff Hk.
  unfold check_brk in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_mmap_kf : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros addr len prot flags fd off [ret ws zs us cs ci] m m' evs H Hoff Hk.
  unfold check_mmap in H.
  cbv zeta in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_munmap_kf : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros addr len [ret ws zs us cs ci] m m' evs H Hoff Hk.
  unfold check_munmap in H.
  cbv zeta in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_mremap_kf : forall old old_size new_size flags eff m m' evs,
  check_mremap old old_size new_size flags eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros old old_size new_size flags [ret ws zs us cs ci] m m' evs H Hoff Hk.
  unfold check_mremap in H.
  cbv zeta in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_mprotect_kf : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros addr len prot [ret ws zs us cs ci] m m' evs H Hoff Hk.
  unfold check_mprotect in H.
  cbv zeta in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_madvise_kf : forall addr len advice eff m m' evs,
  check_madvise addr len advice eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros addr len advice [ret ws zs us cs ci] m m' evs H Hoff Hk.
  unfold check_madvise in H.
  cbv zeta in H.
  kf_frame H m Hoff Hk.
Qed.

(** OPENAT AND READ'S HELPERS, ONE LEMMA PER SUB-CHECKER.  Each proves
    its own step and closes the sub-checkers it calls with their lemmas,
    so no proof unfolds the whole openat tree: unfolding every
    sub-checker at once and splitting it costs the build more memory
    than a CI runner has. *)

Lemma kf_open_wronly : forall p eff m m' evs,
  check_create_wronly p eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros p eff m m' evs H Hoff Hk. unfold check_create_wronly in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_open_append : forall p eff m m' evs,
  check_open_append p eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros p eff m m' evs H Hoff Hk. unfold check_open_append in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_open_rdwr : forall p fs' eff m m' evs,
  check_open_rdwr p fs' eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros p fs' eff m m' evs H Hoff Hk. unfold check_open_rdwr in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_openat_read : forall p eff m m' evs,
  Open.check_openat_read p eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros p eff m m' evs H Hoff Hk. unfold Open.check_openat_read in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_openat_create : forall p eff m m' evs,
  Open.check_openat_create p eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros p eff m m' evs H Hoff Hk. unfold Open.check_openat_create in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk
          || (eapply kf_open_wronly in H; exact (H Hoff Hk))).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_openat_excl : forall p eff m m' evs,
  Open.check_openat_excl p eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros p eff m m' evs H Hoff Hk. unfold Open.check_openat_excl in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk
          || (eapply kf_open_wronly in H; exact (H Hoff Hk))).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_openat_append : forall excl p eff m m' evs,
  Open.check_openat_append excl p eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros excl p eff m m' evs H Hoff Hk. unfold Open.check_openat_append in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk
          || (eapply kf_open_append in H; exact (H Hoff Hk))).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_openat_rdwr : forall creat trunc p eff m m' evs,
  Open.check_openat_rdwr creat trunc p eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros creat trunc p eff m m' evs H Hoff Hk. unfold Open.check_openat_rdwr in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk
          || (eapply kf_open_rdwr in H; exact (H Hoff Hk))).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_openat_rdwr_excl : forall p eff m m' evs,
  Open.check_openat_rdwr_excl p eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros p eff m m' evs H Hoff Hk. unfold Open.check_openat_rdwr_excl in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk
          || (eapply kf_open_rdwr in H; exact (H Hoff Hk))).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_openat_dir : forall p eff m m' evs,
  Open.check_openat_dir p eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros p eff m m' evs H Hoff Hk. unfold Open.check_openat_dir in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_openat_localtime : forall flags eff m m' evs,
  Open.check_openat_localtime flags eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros flags eff m m' evs H Hoff Hk. unfold Open.check_openat_localtime in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_open_devnull : forall rd wr eff m m' evs,
  Open.check_open_devnull rd wr eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros rd wr eff m m' evs H Hoff Hk. unfold Open.check_open_devnull in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_openat_devnull : forall flags eff m m' evs,
  Open.check_openat_devnull flags eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros flags eff m m' evs H Hoff Hk. unfold Open.check_openat_devnull in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk
          || (eapply kf_open_devnull in H; exact (H Hoff Hk))).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_open_urandom : forall eff m m' evs,
  Open.check_open_urandom eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros eff m m' evs H Hoff Hk. unfold Open.check_open_urandom in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_openat_urandom : forall flags eff m m' evs,
  Open.check_openat_urandom flags eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros flags eff m m' evs H Hoff Hk. unfold Open.check_openat_urandom in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk
          || (eapply kf_open_urandom in H; exact (H Hoff Hk))).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_openat_tmp : forall n p flags eff m m' evs,
  Open.check_openat_tmp n p flags eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros n p flags eff m m' evs H Hoff Hk. unfold Open.check_openat_tmp in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk
          || (eapply kf_openat_read in H; exact (H Hoff Hk))
          || (eapply kf_openat_create in H; exact (H Hoff Hk))).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_openat_sep : forall p flags eff m m' evs,
  Open.check_openat_sep p flags eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros p flags eff m m' evs H Hoff Hk. unfold Open.check_openat_sep in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk
          || (eapply kf_openat_localtime in H; exact (H Hoff Hk))
          || (eapply kf_openat_devnull in H; exact (H Hoff Hk))
          || (eapply kf_openat_urandom in H; exact (H Hoff Hk))
          || (eapply kf_openat_tmp in H; exact (H Hoff Hk))).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_openat_resolved : forall p flags eff m m' evs,
  Open.check_openat_resolved p flags eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros p flags eff m m' evs H Hoff Hk. unfold Open.check_openat_resolved in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk
          || (eapply kf_openat_sep in H; exact (H Hoff Hk))
          || (eapply kf_openat_read in H; exact (H Hoff Hk))
          || (eapply kf_openat_create in H; exact (H Hoff Hk))
          || (eapply kf_openat_excl in H; exact (H Hoff Hk))
          || (eapply kf_openat_dir in H; exact (H Hoff Hk))
          || (eapply kf_openat_append in H; exact (H Hoff Hk))
          || (eapply kf_openat_rdwr in H; exact (H Hoff Hk))
          || (eapply kf_openat_rdwr_excl in H; exact (H Hoff Hk))).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_proc_open_result : forall o eff m m' evs,
  Open.check_proc_open_result o eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros o eff m m' evs H Hoff Hk. unfold Open.check_proc_open_result in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_openat_proc : forall c flags eff m m' evs,
  Open.check_openat_proc c flags eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros c flags eff m m' evs H Hoff Hk. unfold Open.check_openat_proc in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk
          || (eapply kf_proc_open_result in H; exact (H Hoff Hk))).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_openat_body : forall i dirfd pathp flags eff m m' evs,
  Open.check_openat_body i dirfd pathp flags eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i dirfd pathp flags eff m m' evs H Hoff Hk. unfold Open.check_openat_body in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk
          || (eapply kf_openat_proc in H; exact (H Hoff Hk))
          || (eapply kf_openat_resolved in H; exact (H Hoff Hk))).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_read_urandom : forall i buf count eff m m' evs,
  check_read_urandom i buf count eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i buf count eff m m' evs H Hoff Hk. unfold check_read_urandom, check_access_ok_zero in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_socket_pending_error : forall e fd peer ch buf count i eff m m' evs,
  check_socket_pending_error e fd peer ch buf count i eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros e fd peer ch buf count i eff m m' evs H Hoff Hk. unfold check_socket_pending_error, check_access_ok_zero in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_write_fault_extend : forall reads m p off eff m' evs,
  check_write_fault_extend reads m p off eff = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros reads m p off eff m' evs H Hoff Hk. unfold check_write_fault_extend, check_access_ok_zero in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_fstat_deliver_by : forall ok statbuf p pin eff m m' evs,
  check_fstat_deliver_by ok statbuf p pin eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros ok statbuf p pin eff m m' evs H Hoff Hk. unfold check_fstat_deliver_by in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_fstat_deliver : forall statbuf n p pin eff m m' evs,
  check_fstat_deliver statbuf n p pin eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros statbuf n p pin eff m m' evs H Hoff Hk. unfold check_fstat_deliver in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk
          || (eapply kf_fstat_deliver_by in H; exact (H Hoff Hk))).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_fstat_file : forall i p statbuf eff m m' evs,
  check_fstat_file i p statbuf eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i p statbuf eff m m' evs H Hoff Hk. unfold check_fstat_file in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk
          || (eapply kf_fstat_deliver in H; exact (H Hoff Hk))
          || (eapply kf_fstat_deliver_by in H; exact (H Hoff Hk))).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_fstat_chrdev : forall ok p i statbuf eff m m' evs,
  check_fstat_chrdev ok p i statbuf eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros ok p i statbuf eff m m' evs H Hoff Hk. unfold check_fstat_chrdev in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk
          || (eapply kf_fstat_deliver in H; exact (H Hoff Hk))
          || (eapply kf_fstat_deliver_by in H; exact (H Hoff Hk))).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_fstat_devnull : forall i statbuf eff m m' evs,
  check_fstat_devnull i statbuf eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i statbuf eff m m' evs H Hoff Hk. unfold check_fstat_devnull in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk
          || (eapply kf_fstat_chrdev in H; exact (H Hoff Hk))).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_fstat_urandom : forall i statbuf eff m m' evs,
  check_fstat_urandom i statbuf eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i statbuf eff m m' evs H Hoff Hk. unfold check_fstat_urandom in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk
          || (eapply kf_fstat_chrdev in H; exact (H Hoff Hk))).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_newfstatat_proc_errno : forall reads eff m m' evs,
  check_newfstatat_proc_errno reads eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros reads eff m m' evs H Hoff Hk. unfold check_newfstatat_proc_errno in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk).
  all: kf_close m Hoff Hk.
Qed.

Lemma kf_newfstatat_proc : forall i reads statbuf eff m m' evs,
  check_newfstatat_proc i reads statbuf eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i reads statbuf eff m m' evs H Hoff Hk. unfold check_newfstatat_proc in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk
          || (eapply kf_newfstatat_proc_errno in H; exact (H Hoff Hk))).
  all: kf_close m Hoff Hk.
Qed.


Lemma check_read_kf : forall i fd buf count eff m m' evs,
  check_read i fd buf count eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i fd buf count eff m m' evs H Hoff Hk.
  unfold check_read, check_read_file_data, check_access_ok_zero in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk
          || (apply check_read_opaque_keeps in H; destruct H as [-> ->])
          || (eapply kf_read_urandom in H; exact (H Hoff Hk))
          || (eapply kf_socket_pending_error in H; exact (H Hoff Hk))).
  all: kf_close m Hoff Hk.
Qed.

Lemma check_write_kf : forall i fd buf count eff m m' evs,
  check_write i fd buf count eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i fd buf count eff m m' evs H Hoff Hk.
  unfold check_write, check_access_ok_zero in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk
          || (apply check_write_opaque_keeps in H; destruct H as [-> ->])
          || (eapply kf_write_fault_extend in H; exact (H Hoff Hk))).
  all: kf_close m Hoff Hk.
Qed.

Lemma check_pread64_kf : forall i fd buf count pos eff m m' evs,
  check_pread64 i fd buf count pos eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i fd buf count pos eff m m' evs H Hoff Hk.
  unfold check_pread64, check_read_urandom in H.
  cbv zeta in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_pwrite64_kf : forall i fd buf count pos eff m m' evs,
  check_pwrite64 i fd buf count pos eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i fd buf count pos eff m m' evs H Hoff Hk.
  unfold check_pwrite64, check_write_fault_extend in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_readv_kf : forall i fd iov iovcnt eff m m' evs,
  check_readv i fd iov iovcnt eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i fd iov iovcnt eff m m' evs H Hoff Hk.
  unfold check_readv in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_writev_kf : forall i fd iov iovcnt eff m m' evs,
  check_writev i fd iov iovcnt eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i fd iov iovcnt eff m m' evs H Hoff Hk.
  unfold check_writev, check_write_fault_extend in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_openat_kf : forall i dirfd pathp flags eff m m' evs,
  check_openat i dirfd pathp flags eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i dirfd pathp flags eff m m' evs H Hoff Hk.
  unfold check_openat in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk
          || (eapply kf_openat_body in H; exact (H Hoff Hk))).
  all: kf_close m Hoff Hk.
Qed.

Lemma check_close_kf : forall fd eff m m' evs,
  check_close fd eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros fd eff m m' evs H Hoff Hk.
  unfold check_close in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_lseek_kf : forall fd off whence eff m m' evs,
  check_lseek fd off whence eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros fd off whence eff m m' evs H Hoff Hk.
  unfold check_lseek in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_ftruncate_kf : forall fd len eff m m' evs,
  check_ftruncate fd len eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros fd len eff m m' evs H Hoff Hk.
  unfold check_ftruncate in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_ioctl_kf : forall fd req eff m m' evs,
  check_ioctl fd req eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros fd req eff m m' evs H Hoff Hk.
  unfold check_ioctl in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_readlinkat_kf : forall i dirfd eff m m' evs,
  check_readlinkat i dirfd eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i dirfd eff m m' evs H Hoff Hk.
  unfold check_readlinkat in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_wait4_kf : forall i upid stat_addr options rusage eff m m' evs,
  check_wait4 i upid stat_addr options rusage eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i upid stat_addr options rusage eff m m' evs H Hoff Hk.
  unfold check_wait4 in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_fsync_kf : forall fd eff m m' evs,
  check_fsync fd eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros fd eff m m' evs H Hoff Hk.
  unfold check_fsync in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_getdents64_kf : forall i fd dirent count eff m m' evs,
  check_getdents64 i fd dirent count eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i fd dirent count eff m m' evs H Hoff Hk.
  unfold check_getdents64 in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk
          || (apply check_getdents64_opaque_fds in H;
              destruct H as ((fds & ->) & ->))).
  all: kf_close m Hoff Hk.
Qed.

Lemma check_flock_kf : forall fd cmd eff m m' evs,
  check_flock fd cmd eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros fd cmd eff m m' evs H Hoff Hk.
  unfold check_flock in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_exit_kf : forall code eff m m' evs,
  check_exit code eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros code eff m m' evs H Hoff Hk.
  unfold check_exit in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_set_tid_address_kf : forall eff m m' evs,
  check_set_tid_address eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros eff m m' evs H Hoff Hk.
  unfold check_set_tid_address in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_getpid_kf : forall eff m m' evs,
  check_getpid eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  exact check_set_tid_address_kf.
Qed.

Lemma check_gettid_kf : forall eff m m' evs,
  check_gettid eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  exact check_set_tid_address_kf.
Qed.

Lemma check_setsid_kf : forall eff m m' evs,
  check_setsid eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros eff m m' evs H Hoff Hk.
  unfold check_setsid in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_uname_kf : forall i name eff m m' evs,
  check_uname i name eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i name eff m m' evs H Hoff Hk.
  unfold check_uname, check_uname_copy in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_prctl_kf : forall i option_ arg2 eff m m' evs,
  check_prctl i option_ arg2 eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i option_ arg2 eff m m' evs H Hoff Hk.
  unfold check_prctl, check_ret_writes in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_prlimit64_kf : forall i pid resource new_rlim old_rlim eff m m' evs,
  check_prlimit64 i pid resource new_rlim old_rlim eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i pid resource new_rlim old_rlim eff m m' evs H Hoff Hk.
  unfold check_prlimit64, check_rlim64_read in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_getrandom_kf : forall i buf cap flags eff m m' evs,
  check_getrandom i buf cap flags eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i buf cap flags eff m m' evs H Hoff Hk.
  unfold check_getrandom, check_getrandom_zero in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_gettimeofday_kf : forall i tv tz eff m m' evs,
  check_gettimeofday i tv tz eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i tv tz eff m m' evs H Hoff Hk.
  unfold check_gettimeofday in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_clock_gettime_kf : forall i clkid tp eff m m' evs,
  check_clock_gettime i clkid tp eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i clkid tp eff m m' evs H Hoff Hk.
  unfold check_clock_gettime in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_clock_getres_kf : forall i clkid tp eff m m' evs,
  check_clock_getres i clkid tp eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i clkid tp eff m m' evs H Hoff Hk.
  unfold check_clock_getres, check_clock_getres_result in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_nanosleep_kf : forall i rqtp rmtp eff m m' evs,
  check_nanosleep i rqtp rmtp eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i rqtp rmtp eff m m' evs H Hoff Hk.
  unfold check_nanosleep in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_dup_kf : forall oldfd eff m m' evs,
  check_dup oldfd eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros oldfd eff m m' evs H Hoff Hk.
  unfold check_dup, check_dup_result in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_dup3_kf : forall oldfd newfd flags eff m m' evs,
  check_dup3 oldfd newfd flags eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros oldfd newfd flags eff m m' evs H Hoff Hk.
  unfold check_dup3 in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_unlinkat_kf : forall i dirfd pathp flags eff m m' evs,
  check_unlinkat i dirfd pathp flags eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i dirfd pathp flags eff m m' evs H Hoff Hk.
  unfold check_unlinkat, Namei.check_unlinkat_body, Namei.check_unlinkat_tmp, Namei.check_unlink_found, check_unlink_result in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_faccessat_kf : forall i dirfd pathp mode eff m m' evs,
  check_faccessat i dirfd pathp mode eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i dirfd pathp mode eff m m' evs H Hoff Hk.
  unfold check_faccessat, Open.check_faccessat_body, check_access_exists in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_faccessat2_kf : forall i dirfd pathp mode flags eff m m' evs,
  check_faccessat2 i dirfd pathp mode flags eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i dirfd pathp mode flags eff m m' evs H Hoff Hk.
  unfold check_faccessat2, Open.check_faccessat_body, check_access_exists in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_pselect6_kf : forall i n32 inp outp exp tsp sig eff m m' evs,
  check_pselect6 i n32 inp outp exp tsp sig eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i n32 inp outp exp tsp sig eff m m' evs H Hoff Hk.
  unfold check_pselect6 in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_ppoll_kf : forall i ufds nfds tsp sig sigsetsize eff m m' evs,
  check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i ufds nfds tsp sig sigsetsize eff m m' evs H Hoff Hk.
  unfold check_ppoll in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_newfstatat_kf : forall i dirfd pathp flag eff m m' evs,
  check_newfstatat i dirfd pathp flag eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i dirfd pathp flag eff m m' evs H Hoff Hk.
  unfold check_newfstatat in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk
          || (eapply kf_newfstatat_proc in H; exact (H Hoff Hk))
          || (eapply kf_newfstatat_proc_errno in H; exact (H Hoff Hk))).
  all: kf_close m Hoff Hk.
Qed.

Lemma check_fstat_kf : forall i fd statbuf eff m m' evs,
  check_fstat i fd statbuf eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i fd statbuf eff m m' evs H Hoff Hk.
  unfold check_fstat in H.
  cbv beta iota zeta in H;
  repeat (kf_step H || kf_done H Hoff Hk
          || (apply check_fstat_opaque_keeps in H; destruct H as [-> ->])
          || (eapply kf_fstat_file in H; exact (H Hoff Hk))
          || (eapply kf_fstat_devnull in H; exact (H Hoff Hk))
          || (eapply kf_fstat_urandom in H; exact (H Hoff Hk))
          || (eapply kf_fstat_chrdev in H; exact (H Hoff Hk))).
  all: kf_close m Hoff Hk.
Qed.

Lemma check_getid_kf : forall sel eff m m' evs,
  check_getid sel eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros sel eff m m' evs H Hoff Hk.
  unfold check_getid in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_setid_kf : forall get put user v eff m m' evs,
  check_setid get put user v eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros get put user v eff m m' evs H Hoff Hk.
  unfold check_setid, check_setid_result in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_setresid_kf : forall get put user r e sv eff m m' evs,
  check_setresid get put user r e sv eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros get put user r e sv eff m m' evs H Hoff Hk.
  unfold check_setresid, check_setid_result in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_getgroups_kf : forall gidsetsize eff m m' evs,
  check_getgroups gidsetsize eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros gidsetsize eff m m' evs H Hoff Hk.
  unfold check_getgroups in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_setgroups_kf : forall i eff m m' evs,
  check_setgroups i eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i eff m m' evs H Hoff Hk.
  unfold check_setgroups in H.
  kf_frame H m Hoff Hk.
Qed.

(** The parent-side arms the extensions added: each unfolds as its
    [Checks.VmMapsDisjoint] [_frame] lemma does.  None reaches
    [State.with_killed]: [capset] and [close_range] write the credentials
    and the descriptor table, the four readers write user memory only. *)
Lemma check_capget_kf : forall i header dataptr eff m m' evs,
  check_capget i header dataptr eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i header dataptr eff m m' evs H Hoff Hk.
  unfold check_capget, check_capget_copy in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_capset_kf : forall i header data eff m m' evs,
  check_capset i header data eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i header data eff m m' evs H Hoff Hk.
  unfold check_capset in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_close_range_kf : forall fd max_fd flags eff m m' evs,
  check_close_range fd max_fd flags eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros fd max_fd flags eff m m' evs H Hoff Hk.
  unfold check_close_range in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_getppid_kf : forall eff m m' evs,
  check_getppid eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros eff m m' evs H Hoff Hk.
  unfold check_getppid in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_getsid_kf : forall pid eff m m' evs,
  check_getsid pid eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros pid eff m m' evs H Hoff Hk.
  unfold check_getsid, check_getppid in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_getresid_kf : forall i get rp ep sp eff m m' evs,
  check_getresid i get rp ep sp eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i get rp ep sp eff m m' evs H Hoff Hk.
  unfold check_getresid, check_ret_writes in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_socket_kf : forall domain type protocol eff m m' evs,
  check_socket domain type protocol eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros domain type protocol eff m m' evs H Hoff Hk.
  unfold check_socket, check_new_fd_result, check_errno_or_list in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_bind_kf : forall i fd addrp addrlen eff m m' evs,
  check_bind i fd addrp addrlen eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i fd addrp addrlen eff m m' evs H Hoff Hk.
  unfold check_bind, check_errno_or_success in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_listen_kf : forall fd backlog eff m m' evs,
  check_listen fd backlog eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros fd backlog eff m m' evs H Hoff Hk.
  unfold check_listen, check_errno_or_success, check_errno_only in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_accept4_kf : forall fd addrp addrlenp flags eff m m' evs,
  check_accept4 fd addrp addrlenp flags eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros fd addrp addrlenp flags eff m m' evs H Hoff Hk.
  unfold check_accept4, check_new_fd_result, check_errno_or_success, check_errno_only, check_errno_or_list in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_fcntl_kf : forall fd cmd arg eff m m' evs,
  check_fcntl fd cmd arg eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros fd cmd arg eff m m' evs H Hoff Hk.
  unfold check_fcntl in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_sched_setscheduler_kf : forall i pid policy param eff m m' evs,
  check_sched_setscheduler i pid policy param eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i pid policy param eff m m' evs H Hoff Hk.
  unfold check_sched_setscheduler in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_sched_getaffinity_kf : forall len eff m m' evs,
  check_sched_getaffinity len eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros len eff m m' evs H Hoff Hk.
  unfold check_sched_getaffinity in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_sched_yield_kf : forall eff m m' evs,
  check_sched_yield eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros eff m m' evs H Hoff Hk.
  unfold check_sched_yield in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_sigaltstack_kf : forall i uss uoss eff m m' evs,
  check_sigaltstack i uss uoss eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i uss uoss eff m m' evs H Hoff Hk.
  unfold check_sigaltstack in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_rt_sigaction_kf : forall i sig act oact ss eff m m' evs,
  check_rt_sigaction i sig act oact ss eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i sig act oact ss eff m m' evs H Hoff Hk.
  unfold check_rt_sigaction in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_futex_kf : forall i uaddr op val utime eff m m' evs,
  check_futex i uaddr op val utime eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i uaddr op val utime eff m m' evs H Hoff Hk.
  unfold check_futex, check_futex_wake_private, check_futex_wait_private in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_set_robust_list_kf : forall len eff m m' evs,
  check_set_robust_list len eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros len eff m m' evs H Hoff Hk.
  unfold check_set_robust_list in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_setns_kf : forall fd eff m m' evs,
  check_setns fd eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros fd eff m m' evs H Hoff Hk.
  unfold check_setns in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_clone_kf : forall flags eff m m' evs,
  check_clone flags eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros flags eff m m' evs H Hoff Hk.
  unfold check_clone, check_clone_resolve, check_clone_answer,
    check_clone_ns_resolve, check_clone_ns_answer in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_clone3_kf : forall i uargs size eff m m' evs,
  check_clone3 i uargs size eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i uargs size eff m m' evs H Hoff Hk.
  unfold check_clone3, check_clone3_resolve, check_clone_answer in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_getsockname_kf : forall fd eff m m' evs,
  check_getsockname fd eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros fd eff m m' evs H Hoff Hk.
  unfold check_getsockname, check_getsockname_core in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_getpeername_kf : forall fd eff m m' evs,
  check_getpeername fd eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros fd eff m m' evs H Hoff Hk.
  unfold check_getpeername, check_getpeername_core in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_setsockopt_kf : forall fd level optlen eff m m' evs,
  check_setsockopt fd level optlen eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros fd level optlen eff m m' evs H Hoff Hk.
  unfold check_setsockopt, check_setsockopt_core in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_getsockopt_kf : forall i fd level optlenp eff m m' evs,
  check_getsockopt i fd level optlenp eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i fd level optlenp eff m m' evs H Hoff Hk.
  unfold check_getsockopt, check_getsockopt_core in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_shutdown_kf : forall fd how eff m m' evs,
  check_shutdown fd how eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros fd how eff m m' evs H Hoff Hk.
  unfold check_shutdown, check_shutdown_core in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_sendto_kf : forall i fd buf count flags addrp eff m m' evs,
  check_sendto i fd buf count flags addrp eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i fd buf count flags addrp eff m m' evs H Hoff Hk.
  unfold check_sendto, check_access_ok_zero, check_send_on_socket in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_sendmsg_kf : forall i fd msgp flags eff m m' evs,
  check_sendmsg i fd msgp flags eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i fd msgp flags eff m m' evs H Hoff Hk.
  unfold check_sendmsg, check_send_on_socket in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_socketpair_kf : forall i family type protocol sv eff m m' evs,
  check_socketpair i family type protocol sv eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i family type protocol sv eff m m' evs H Hoff Hk.
  unfold check_socketpair, check_socketpair_written, check_socketpair_faulted in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_recvfrom_kf : forall i fd buf size eff m m' evs,
  check_recvfrom i fd buf size eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i fd buf size eff m m' evs H Hoff Hk.
  unfold check_recvfrom, check_access_ok_zero, check_recv_fd_answer in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_recvmsg_kf : forall fd flags eff m m' evs,
  check_recvmsg fd flags eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros fd flags eff m m' evs H Hoff Hk.
  unfold check_recvmsg, check_recv_fd_answer in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_connect_kf : forall i fd addrp addrlen eff m m' evs,
  check_connect i fd addrp addrlen eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i fd addrp addrlen eff m m' evs H Hoff Hk.
  unfold check_connect in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_timerfd_create_kf : forall clkid flags eff m m' evs,
  check_timerfd_create clkid flags eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros clkid flags eff m m' evs H Hoff Hk.
  unfold check_timerfd_create in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_eventfd2_kf : forall flags eff m m' evs,
  check_eventfd2 flags eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros flags eff m m' evs H Hoff Hk.
  unfold check_eventfd2, check_new_fd_result in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_signalfd4_kf : forall i ufd mask sizemask flags eff m m' evs,
  check_signalfd4 i ufd mask sizemask flags eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i ufd mask sizemask flags eff m m' evs H Hoff Hk.
  unfold check_signalfd4, check_new_fd_result in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_pipe2_kf : forall i fildes flags eff m m' evs,
  check_pipe2 i fildes flags eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i fildes flags eff m m' evs H Hoff Hk.
  unfold check_pipe2, pipe2_model in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_getcwd_kf : forall size eff m m' evs,
  check_getcwd size eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros size eff m m' evs H Hoff Hk.
  unfold check_getcwd in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_epoll_create1_kf : forall flags32 eff m m' evs,
  check_epoll_create1 flags32 eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros flags32 eff m m' evs H Hoff Hk.
  unfold check_epoll_create1 in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_epoll_ctl_kf : forall i epfd op32 tfd event eff m m' evs,
  check_epoll_ctl i epfd op32 tfd event eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i epfd op32 tfd event eff m m' evs H Hoff Hk.
  unfold check_epoll_ctl in H.
  kf_frame H m Hoff Hk.
Qed.

Lemma check_epoll_pwait_kf : forall i epfd events maxevents32 sigmask sigsetsize eff m m' evs,
  check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i epfd events maxevents32 sigmask sigsetsize eff m m' evs H Hoff Hk.
  unfold check_epoll_pwait in H.
  kf_frame H m Hoff Hk.
Qed.

(* -------------------------------------------------------------------------
   The table, the dispatcher, the spec
   ------------------------------------------------------------------------- *)

(** What one dispatcher arm owes, as a property of the table entry. *)
Definition arm_kill_free (c : CheckedArm) : Prop :=
  forall i eff m m' evs,
    ca_check c i eff m = CheckOk m' evs -> kill_post m m' evs.

(** Every arm discharges it.  As in [Checks.VmMapsDisjoint], the last
    alternative names the lemma an uncovered arm needs. *)
Lemma checked_table_kill_free : Forall arm_kill_free checked_table.
Proof.
  unfold checked_table.
  repeat apply Forall_cons.
  all: try exact (Forall_nil arm_kill_free).
  all: unfold arm_kill_free; intros i eff m m' evs H;
       autorewrite with arm_unfold in H.
  all: first
    [ fail
    | eapply check_brk_kf; eassumption
    | eapply check_mmap_kf; eassumption
    | eapply check_munmap_kf; eassumption
    | eapply check_mremap_kf; eassumption
    | eapply check_mprotect_kf; eassumption
    | eapply check_madvise_kf; eassumption
    | eapply check_read_kf; eassumption
    | eapply check_write_kf; eassumption
    | eapply check_pread64_kf; eassumption
    | eapply check_pwrite64_kf; eassumption
    | eapply check_readv_kf; eassumption
    | eapply check_writev_kf; eassumption
    | eapply check_openat_kf; eassumption
    | eapply check_close_kf; eassumption
    | eapply check_lseek_kf; eassumption
    | eapply check_ftruncate_kf; eassumption
    | eapply check_ioctl_kf; eassumption
    | eapply check_readlinkat_kf; eassumption
    | eapply check_wait4_kf; eassumption
    | eapply check_fsync_kf; eassumption
    | eapply check_getdents64_kf; eassumption
    | eapply check_flock_kf; eassumption
    | eapply check_exit_kf; eassumption
    | eapply check_set_tid_address_kf; eassumption
    | eapply check_getpid_kf; eassumption
    | eapply check_gettid_kf; eassumption
    | eapply check_setsid_kf; eassumption
    | eapply check_uname_kf; eassumption
    | eapply check_prctl_kf; eassumption
    | eapply check_prlimit64_kf; eassumption
    | eapply check_getrandom_kf; eassumption
    | eapply check_gettimeofday_kf; eassumption
    | eapply check_clock_gettime_kf; eassumption
    | eapply check_clock_getres_kf; eassumption
    | eapply check_nanosleep_kf; eassumption
    | eapply check_dup_kf; eassumption
    | eapply check_dup3_kf; eassumption
    | eapply check_unlinkat_kf; eassumption
    | eapply check_faccessat_kf; eassumption
    | eapply check_faccessat2_kf; eassumption
    | eapply check_pselect6_kf; eassumption
    | eapply check_ppoll_kf; eassumption
    | eapply check_newfstatat_kf; eassumption
    | eapply check_fstat_kf; eassumption
    | eapply check_getid_kf; eassumption
    | eapply check_setid_kf; eassumption
    | eapply check_setresid_kf; eassumption
    | eapply check_getgroups_kf; eassumption
    | eapply check_setgroups_kf; eassumption
    | eapply check_socket_kf; eassumption
    | eapply check_bind_kf; eassumption
    | eapply check_listen_kf; eassumption
    | eapply check_accept4_kf; eassumption
    | eapply check_fcntl_kf; eassumption
    | eapply check_sched_setscheduler_kf; eassumption
    | eapply check_sched_getaffinity_kf; eassumption
    | eapply check_sched_yield_kf; eassumption
    | eapply check_sigaltstack_kf; eassumption
    | eapply check_rt_sigaction_kf; eassumption
    | eapply check_kill_kf; eassumption
    | eapply check_tkill_kf; eassumption
    | eapply check_tgkill_kf; eassumption
    | eapply check_rt_sigprocmask_kf; eassumption
    | eapply check_futex_kf; eassumption
    | eapply check_set_robust_list_kf; eassumption
    | eapply check_setns_kf; eassumption
    | eapply check_clone_kf; eassumption
    | eapply check_clone3_kf; eassumption
    | eapply check_getsockname_kf; eassumption
    | eapply check_getpeername_kf; eassumption
    | eapply check_setsockopt_kf; eassumption
    | eapply check_getsockopt_kf; eassumption
    | eapply check_shutdown_kf; eassumption
    | eapply check_sendto_kf; eassumption
    | eapply check_sendmsg_kf; eassumption
    | eapply check_socketpair_kf; eassumption
    | eapply check_recvfrom_kf; eassumption
    | eapply check_recvmsg_kf; eassumption
    | eapply check_connect_kf; eassumption
    | eapply check_timerfd_create_kf; eassumption
    | eapply check_eventfd2_kf; eassumption
    | eapply check_signalfd4_kf; eassumption
    | eapply check_pipe2_kf; eassumption
    | eapply check_getcwd_kf; eassumption
    | eapply check_epoll_create1_kf; eassumption
    | eapply check_epoll_ctl_kf; eassumption
    | eapply check_epoll_pwait_kf; eassumption
    | eapply check_capget_kf; eassumption
    | eapply check_capset_kf; eassumption
    | eapply check_close_range_kf; eassumption
    | eapply check_getppid_kf; eassumption
    | eapply check_getsid_kf; eassumption
    | eapply check_getresid_kf; eassumption
    | fail 1 "checked_table_kill_free has no case for this dispatcher arm: give the new checker a *_kf lemma and add it to the list above" ].
Qed.

Theorem check_syscall_kill_free : forall i eff m m' evs,
  check_syscall i eff m = CheckOk m' evs -> kill_post m m' evs.
Proof.
  intros i eff m m' evs H. unfold check_syscall in H.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk;
    [|discriminate H].
  pose proof checked_table_kill_free as Hall.
  rewrite Forall_forall in Hall.
  exact (Hall c (lookup_ca_In _ _ _ Elk) i eff m m' evs H).
Qed.

(** THE FRAME [Run] states, discharged. *)
Theorem kill_frame_holds : kill_frame.
Proof.
  intros i m eff m' evs Hs Hh Hoff.
  apply check_syscall_ok_iff in Hs.
  apply (check_syscall_kill_free _ _ _ _ _ Hs Hoff).
  unfold m_killed. unfold m_halted in Hh.
  destruct (procst_killed (m_proc m)); [exact Hh | reflexivity].
Qed.

(* -------------------------------------------------------------------------
   The consequences for runs
   ------------------------------------------------------------------------- *)

(** Any launch that leaves all three kill declarations clear. *)
Theorem run_no_kill_of_decls : forall img lim en inp tr,
  in_abort_terminal inp = false ->
  in_sigpipe_terminal inp = false ->
  in_selfkill_terminal inp = false ->
  bh_traces (run img lim en inp) tr ->
  no_kill tr.
Proof. exact (run_kill_off kill_frame_holds). Qed.

(** UNDER THE ORDINARY LAUNCH, NO RUN DIES BY A SIGNAL: no trace of
    [Run.run_scfg] under any configuration -- and so none of [Run.run],
    which is [run_scfg] at [Run.may_fail_cfg] -- carries a
    [State.KillEv].  This is the fact the error-free statements of
    [Equivalence] rest on when they ask [error_free] rather than
    [error_free_unkilled] under [Run.valid_input]. *)
Theorem valid_input_no_kill : forall cfg img lim en inp tr,
  valid_input inp ->
  bh_traces (run_scfg cfg img lim en inp) tr ->
  forall sig fs, ~ In (KillEv sig fs) tr.
Proof.
  intros cfg img lim en inp tr Hv Htr.
  apply run_scfg_sub_traces in Htr.
  apply (run_no_kill_of_decls img lim en inp tr); [| | | exact Htr].
  - red in Hv. repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
    assumption.
  - exact (valid_input_sigpipe_terminal _ Hv).
  - red in Hv. repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
    assumption.
Qed.

Corollary valid_input_no_kill_run : forall img lim en inp tr,
  valid_input inp ->
  bh_traces (run img lim en inp) tr ->
  forall sig fs, ~ In (KillEv sig fs) tr.
Proof.
  intros img lim en inp tr Hv Htr.
  apply (run_no_kill_of_decls img lim en inp tr); [| | | exact Htr].
  - red in Hv. repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
    assumption.
  - exact (valid_input_sigpipe_terminal _ Hv).
  - red in Hv. repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
    assumption.
Qed.

(** The SIG_IGN launch pins all three declarations clear too, so the same
    holds there. *)
Corollary valid_input_sigpipe_ignored_no_kill : forall cfg img lim en inp tr,
  valid_input_sigpipe_ignored inp ->
  bh_traces (run_scfg cfg img lim en inp) tr ->
  forall sig fs, ~ In (KillEv sig fs) tr.
Proof.
  intros cfg img lim en inp tr Hv Htr.
  apply run_scfg_sub_traces in Htr.
  red in Hv. repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  apply (run_no_kill_of_decls img lim en inp tr); assumption.
Qed.

(** WHAT IT MEANS FOR THE TOP STATEMENTS: under [Run.valid_input] a run
    never dies by a signal, so [Equivalence.error_free] and
    [Equivalence.error_free_unkilled] are the same predicate of it, and
    a statement that asks the first asks the second. *)
Corollary valid_input_not_dies_by_signal : forall cfg img lim en inp,
  valid_input inp -> ~ dies_by_signal (run_scfg cfg img lim en inp).
Proof.
  intros cfg img lim en inp Hv (tr & sig & fs & Htr & Hin).
  exact (valid_input_no_kill _ _ _ _ _ _ Hv Htr sig fs Hin).
Qed.

Corollary valid_input_error_free_unkilled_iff : forall cfg img lim en inp,
  valid_input inp ->
  error_free_unkilled (run_scfg cfg img lim en inp)
  <-> error_free (run_scfg cfg img lim en inp).
Proof.
  intros cfg img lim en inp Hv. split.
  - exact (error_free_unkilled_error_free _).
  - intros Hef. split; [exact Hef | exact (valid_input_not_dies_by_signal _ _ _ _ _ Hv)].
Qed.

Corollary valid_input_error_free_unkilled_iff_run : forall img lim en inp,
  valid_input inp ->
  error_free_unkilled (run img lim en inp) <-> error_free (run img lim en inp).
Proof.
  intros img lim en inp Hv. split.
  - exact (error_free_unkilled_error_free _).
  - intros Hef. split; [exact Hef |].
    intros (tr & sig & fs & Htr & Hin).
    exact (valid_input_no_kill_run _ _ _ _ _ Hv Htr sig fs Hin).
Qed.
