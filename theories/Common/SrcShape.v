(** * Common.SrcShape — shape realization for a SOURCE that may FAULT

    TRUST BOUNDARY: image-INDEPENDENT proof library, like every other file
    in [Common/].  Nothing here is part of the trusted specification, and
    [EquivalenceDefinition/Equivalence.v] is NOT touched.

    ** The problem

    [ShapeAlg.realizes segs c T] proves TWO things about [c]: its trace
    set is exactly [T] ([realizes_obs_iff]) AND it never takes the error
    transition ([realizes_no_error]).  That is what the TARGET side of
    [Equivalence.strong_equiv] needs ([~ bh_errors target]).  The SOURCE
    side needs strictly less: [Equivalence.modeled] — the run never
    reaches a configuration the MODEL declines to interpret
    ([Run.unmodeled_at]: a [MachineUnmodeled] instruction or an
    [Unmodeled] syscall) — plus trace-set equality with the target.

    A reference binary is entitled to CRASH on some nondeterministic
    branch (the canonical case: [malloc] returns NULL after a failed
    [mmap]/[brk], and the following store to address 0 is a
    [RiscvSemantics.MachineFault]).  [Run.v] is explicit that a fault is
    a faithfully modeled event (the process really dies, SIGSEGV) and is
    NOT [unmodeled_at]: [unmodeled_at] asks for [MachineUnmodeled], never
    for [MachineFault].  The faulting branch contributes exactly the empty
    trace to [obs_trace] (its only transition is [sstep_instr_fault],
    which goes to [SError] and emits nothing), so as far as trace-set
    equality is concerned it is a [t_nil] leaf.

    ** The design

    [srealizes] is [realizes] plus ONE constructor, [srz_fault]: a
    non-halted, non-syscall configuration whose instruction step is
    [MachineFault] realizes [t_nil].  Everything [ShapeAlg] proves by
    induction on [realizes] is re-proved here by the same induction with
    one extra (trivial) case — EXCEPT [realizes_no_error], which is false
    for [srealizes] and is replaced by

      [srealizes_modeled] : srealizes c T -> ~ reaches_unmodeled segs c.

    WHY THIS IS LEGITIMATE FOR THE SOURCE ONLY.  The master theorem
    [src_shape_strong_equiv] takes [srealizes] for the SOURCE and the
    ordinary [realizes] for the TARGET.  The target's obligation in
    [Equivalence.equiv] is [~ bh_errors], which a fault would violate, so
    a target derivation must still rule faults out; the source's
    obligation is [modeled = ~ bh_unmodeled], which a fault does not
    violate.  Nothing about the trusted definitions is weakened: the
    conclusion is literally [Equivalence.modeled /\ Equivalence.equiv]
    (right disjunct: trace equality + target never errors).

    [srz_realizes] embeds every [realizes] derivation, so all the
    [ShapeAlg] node combinators remain usable on the source side.

    ** Inventory

    - relation: [srealizes] with [srz_node] / [srz_halt] / [srz_fault] /
      [srz_conseq]; embedding [srz_realizes]; [srz_fault_any].
    - theorems: [srealizes_nonempty], [srealizes_pclosed],
      [srealizes_star_only], [srealizes_admits], [srealizes_obs_iff],
      [srealizes_star_not_unmodeled], [srealizes_modeled],
      [srealizes_unique].
    - generic combinators over a [ShapeAlg.node_ok] interface:
      [srz_of_node], [srz_silent1], [srz_emit1], [srz_alt2],
      [srz_node_same] (all resolutions continue as the same shape),
      [srz_node_same_or_nil] / [srz_alt2_absorb_l] / [srz_alt2_absorb_r]
      (FAULT ABSORPTION: resolutions that die silently contribute only
      the empty trace, so they vanish next to a branch realizing [T]).
    - concrete nodes: [srz_step], [srz_msteps], [srz_msteps_fault],
      [srz_write1], [srz_write_ch], [srz_exit], [srz_munmap], [srz_mmap].
    - master theorem: [src_shape_strong_equiv] (source [srealizes T],
      target [realizes T'], [t_eq T T']) and [src_shape_strong_equiv_same]. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import SimInv ExitSim CatSim MmapSim ShapeAlg.

Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

(* =========================================================================
   The relation: [realizes] + a fault leaf
   ========================================================================= *)

Inductive srealizes : config -> TSet -> Prop :=
| srz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok segs c I evs nx ->
    (forall i, srealizes (nx i) (T i)) ->
    srealizes c (t_alt (fun i => t_emit (evs i) (T i)))
| srz_halt : forall c,
    m_halted (cfg_model c) <> None ->
    srealizes c t_nil
| srz_fault : forall c,
    m_halted (cfg_model c) = None ->
    ms_svc_pending (cfg_ms c) = None ->
    m_vm_lazy (cfg_model c) = [] ->
    RiscvSemantics.step segs (cfg_ms c) = MachineFault ->
    srealizes c t_nil
| srz_conseq : forall c T T',
    srealizes c T -> t_eq T T' -> srealizes c T'.

(** The embedding: an error-free realization is a source realization. *)
Lemma srz_realizes : forall c T, realizes segs c T -> srealizes c T.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - apply (srz_node c I evs nx T i0 Hnode IH).
  - apply srz_halt; exact Hh.
  - eapply srz_conseq; eauto.
Qed.

(* -------------------------------------------------------------------------
   The fault leaf: no [SNext] successor, not unmodeled.
   ------------------------------------------------------------------------- *)

Lemma fault_no_snext : forall c evs c',
  ms_svc_pending (cfg_ms c) = None ->
  m_vm_lazy (cfg_model c) = [] ->
  RiscvSemantics.step segs (cfg_ms c) = MachineFault ->
  ~ sstep segs c evs (SNext c').
Proof.
  intros [ms model] evs c' Hsvc Hlazy Hf Hss; cbn in *.
  inversion Hss; subst;
    try match goal with
        | H : mi_account_step segs ms model = _ |- _ =>
            rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hf in H
        end;
    congruence.
Qed.

(** Every transition out of a fault leaf is the silent error transition. *)
Lemma fault_sstep_inv : forall c evs st,
  ms_svc_pending (cfg_ms c) = None ->
  m_vm_lazy (cfg_model c) = [] ->
  RiscvSemantics.step segs (cfg_ms c) = MachineFault ->
  sstep segs c evs st -> evs = [] /\ st = SError.
Proof.
  intros [ms model] evs st Hsvc Hlazy Hf Hss; cbn in *.
  inversion Hss; subst;
    try match goal with
        | H : mi_account_step segs ms model = _ |- _ =>
            rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hf in H
        end;
    split; congruence.
Qed.

Lemma fault_star_refl : forall c tr c',
  ms_svc_pending (cfg_ms c) = None ->
  m_vm_lazy (cfg_model c) = [] ->
  RiscvSemantics.step segs (cfg_ms c) = MachineFault ->
  star segs c tr c' -> tr = [] /\ c' = c.
Proof.
  intros c tr c' Hsvc Hlazy Hf Hstar.
  inversion Hstar as [| c1 evs c2 tr2 c3 Hss Hstar2]; subst; [split; reflexivity|].
  exfalso. exact (fault_no_snext c evs c2 Hsvc Hlazy Hf Hss).
Qed.

Lemma fault_not_unmodeled : forall c,
  ms_svc_pending (cfg_ms c) = None ->
  m_vm_lazy (cfg_model c) = [] ->
  RiscvSemantics.step segs (cfg_ms c) = MachineFault ->
  ~ unmodeled_at segs c.
Proof.
  intros [ms model] Hsvc Hlazy Hf (_ & [(_ & Hum) | (x8 & Hsvc' & _)]); cbn in *;
    [rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hf in Hum|];
    congruence.
Qed.

Lemma halted_not_unmodeled : forall c,
  m_halted (cfg_model c) <> None -> ~ unmodeled_at segs c.
Proof. intros c Hh (Hh' & _). exact (Hh Hh'). Qed.

(** At a node every transition is an [SNext] of the family, so the node is
    covered by the model. *)
Lemma node_not_unmodeled : forall c I evs nx,
  node_ok segs c I evs nx -> ~ unmodeled_at segs c.
Proof.
  intros c I evs nx [_ Hsound] Hun.
  destruct (unmodeled_at_sstep_error segs c Hun) as (e & Hss).
  destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
Qed.

(* -------------------------------------------------------------------------
   Structural facts: nonempty, prefix-closed.
   ------------------------------------------------------------------------- *)

Lemma srealizes_nonempty : forall c T, srealizes c T -> T [].
Proof.
  intros c T H;
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c Hh Hsvc Hlz Hf | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma srealizes_pclosed : forall c T, srealizes c T ->
  forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof.
  intros c T H;
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c Hh Hsvc Hlz Hf | c T T' H IH Heq];
    intros tr tr' HT Hp.
  - destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
    + left. eapply is_prefix_trans; eauto.
    + apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
      * left. exact Hp.
      * right. exists tr0'. split; [reflexivity | eapply IH; eauto].
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
Qed.

(* -------------------------------------------------------------------------
   Soundness / completeness of the trace set.
   ------------------------------------------------------------------------- *)

Lemma srealizes_star_only : forall c T, srealizes c T ->
  forall tr c', star segs c tr c' -> T tr.
Proof.
  intros c T H;
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c Hh Hsvc Hlz Hf | c T T' H IH Heq];
    intros tr c' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + exists i0. left. apply is_prefix_nil.
    + destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
      inversion Heq2; subst c2.
      exists i. right. exists tr2. split; [reflexivity | eapply IH; exact Hstar2].
  - destruct (star_halted_nil segs c tr c' Hh Hstar) as [-> _]. reflexivity.
  - destruct (fault_star_refl c tr c' Hsvc Hlz Hf Hstar) as [-> _]. reflexivity.
  - apply Heq. eapply IH; exact Hstar.
Qed.

Lemma srealizes_admits : forall c T, srealizes c T ->
  forall tr, T tr -> obs_trace segs c tr.
Proof.
  intros c T H;
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c Hh Hsvc Hlz Hf | c T T' H IH Heq];
    intros tr HT.
  - destruct Hnode as [Hcomp _].
    destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
    + exists (evs i), (nx i). split; [apply star_one; apply Hcomp | exact Hpre].
    + destruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
      exists (evs i ++ tr''), c''.
      split; [eapply star_step; [apply Hcomp | exact Hstar] | apply is_prefix_app_mono; exact Hp].
  - unfold t_nil in HT; subst tr. apply obs_trace_nil.
  - unfold t_nil in HT; subst tr. apply obs_trace_nil.
  - apply IH. apply Heq. exact HT.
Qed.

Theorem srealizes_obs_iff : forall c T, srealizes c T ->
  forall tr, obs_trace segs c tr <-> T tr.
Proof.
  intros c T H tr. split.
  - intros (tr' & c' & Hstar & Hp).
    eapply srealizes_pclosed; [exact H | eapply srealizes_star_only; eauto | exact Hp].
  - apply srealizes_admits; exact H.
Qed.

(* -------------------------------------------------------------------------
   Coverage: a source realization never reaches an unmodeled configuration.
   ------------------------------------------------------------------------- *)

Lemma srealizes_star_not_unmodeled : forall c T, srealizes c T ->
  forall tr c', star segs c tr c' -> ~ unmodeled_at segs c'.
Proof.
  intros c T H;
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c Hh Hsvc Hlz Hf | c T T' H IH Heq];
    intros tr c' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + eapply node_not_unmodeled; exact Hnode.
    + destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c2) Hss) as (i & _ & Heq2).
      inversion Heq2; subst c2. eapply IH; exact Hstar2.
  - destruct (star_halted_nil segs c tr c' Hh Hstar) as [_ ->].
    apply halted_not_unmodeled; exact Hh.
  - destruct (fault_star_refl c tr c' Hsvc Hlz Hf Hstar) as [_ ->].
    apply fault_not_unmodeled; assumption.
  - eapply IH; exact Hstar.
Qed.

Theorem srealizes_modeled : forall c T, srealizes c T -> ~ reaches_unmodeled segs c.
Proof.
  intros c T H (tr & c' & Hstar & Hun).
  exact (srealizes_star_not_unmodeled c T H tr c' Hstar Hun).
Qed.

(** The shape a configuration realizes is unique up to [t_eq] (both are
    its [obs_trace]). *)
Lemma srealizes_unique : forall c T T',
  srealizes c T -> srealizes c T' -> t_eq T T'.
Proof.
  intros c T T' H H' tr.
  rewrite <- (srealizes_obs_iff c T H tr), (srealizes_obs_iff c T' H' tr). reflexivity.
Qed.

(* -------------------------------------------------------------------------
   Shape algebra facts used by the fault-absorbing combinators.
   ------------------------------------------------------------------------- *)

Lemma t_alt2_nil_l : forall T, T [] -> t_eq (t_alt2 t_nil T) T.
Proof.
  intros T H0 tr. unfold t_alt2, t_nil. split.
  - intros [-> | HT]; [exact H0 | exact HT].
  - intro HT. right. exact HT.
Qed.

Lemma t_alt2_nil_r : forall T, T [] -> t_eq (t_alt2 T t_nil) T.
Proof.
  intros T H0 tr. unfold t_alt2, t_nil. split.
  - intros [HT | ->]; [exact HT | exact H0].
  - intro HT. left. exact HT.
Qed.

Lemma t_alt2_comm : forall A B, t_eq (t_alt2 A B) (t_alt2 B A).
Proof. intros A B tr. unfold t_alt2. tauto. Qed.

(* =========================================================================
   Combinators (continuation-polymorphic), mirroring [ShapeAlg]
   ========================================================================= *)

(** Generic node introduction (the constructor, with the shape left to
    unification). *)
Lemma srz_of_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                           (T : I -> TSet),
  node_ok segs c I evs nx -> I ->
  (forall i, srealizes (nx i) (T i)) ->
  srealizes c (t_alt (fun i => t_emit (evs i) (T i))).
Proof. intros c I evs nx T Hnode i0 Hcont. exact (srz_node c I evs nx T i0 Hnode Hcont). Qed.

(** The fault leaf regardless of the halted flag. *)
Lemma srz_fault_any : forall c,
  ms_svc_pending (cfg_ms c) = None ->
  m_vm_lazy (cfg_model c) = [] ->
  RiscvSemantics.step segs (cfg_ms c) = MachineFault ->
  srealizes c t_nil.
Proof.
  intros c Hsvc Hlz Hf. destruct (m_halted (cfg_model c)) eqn:Hh.
  - apply srz_halt. rewrite Hh. discriminate.
  - apply srz_fault; assumption.
Qed.

Lemma srz_silent1 : forall c c' T,
  node_ok segs c unit (fun _ => []) (fun _ => c') ->
  srealizes c' T ->
  srealizes c T.
Proof.
  intros c c' T Hnode Hc.
  apply (srz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (srz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply srealizes_nonempty; exact Hc ].
Qed.

Lemma srz_emit1 : forall c c' e T,
  node_ok segs c unit (fun _ => e) (fun _ => c') ->
  srealizes c' T ->
  srealizes c (t_emit e T).
Proof.
  intros c c' e T Hnode Hc.
  apply (srz_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (srz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

Lemma srz_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
                        (a0 : IA) (b0 : IB),
  node_ok segs c (IA + IB) (fun _ => []) nx ->
  (forall i, srealizes (nx (inl i)) A) ->
  (forall i, srealizes (nx (inr i)) B) ->
  srealizes c (t_alt2 A B).
Proof.
  intros c IA IB nx A B a0 b0 Hnode HA HB.
  assert (HA0 : A []) by (eapply srealizes_nonempty; apply (HA a0)).
  assert (HB0 : B []) by (eapply srealizes_nonempty; apply (HB b0)).
  apply (srz_conseq c
    (t_alt (fun i : IA + IB =>
              t_emit [] (match i with inl _ => A | inr _ => B end)))).
  - apply (srz_node c (IA + IB) (fun _ => []) nx
             (fun i => match i with inl _ => A | inr _ => B end) (inl a0) Hnode).
    intros [i|i]; [apply HA | apply HB].
  - intro tr. unfold t_alt2. split.
    + intros [[i|i] Hi];
        [ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi)
        | right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
    + intros [H | H];
        [ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H)
        | exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.

(** A SILENT nondeterministic node all of whose resolutions continue as
    the SAME shape collapses to that shape (no inhabitation premise beyond
    one index, which the always-admissible failure arm supplies for
    brk/mmap/mprotect). *)
Lemma srz_node_same : forall c (I : Type) (nx : I -> config) (T : TSet),
  node_ok segs c I (fun _ => []) nx -> I ->
  (forall i, srealizes (nx i) T) ->
  srealizes c T.
Proof.
  intros c I nx T Hnode i0 Hcont.
  assert (H0 : T []) by (eapply srealizes_nonempty; apply (Hcont i0)).
  apply (srz_conseq c (t_alt (fun _ : I => t_emit [] T))).
  - apply (srz_node c I (fun _ => []) nx (fun _ => T) i0 Hnode Hcont).
  - intro tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq T H0 tr) Hi).
    + intro HT. exists i0. exact (proj2 (t_emit_nil_eq T H0 tr) HT).
Qed.

(** FAULT ABSORPTION.  A silent nondeterministic node where every
    resolution either continues as [T] or dies silently ([t_nil] — e.g. a
    failed allocation followed by a store through NULL), and at least one
    resolution continues as [T], realizes [T]: the dying branches add only
    the empty trace, which [T] already contains. *)
Lemma srz_node_same_or_nil : forall c (I : Type) (nx : I -> config) (T : TSet),
  node_ok segs c I (fun _ => []) nx ->
  (exists i, srealizes (nx i) T) ->
  (forall i, srealizes (nx i) T \/ srealizes (nx i) t_nil) ->
  srealizes c T.
Proof.
  intros c I nx T Hnode [i1 Hi1] Hcont.
  assert (H0 : T []) by (eapply srealizes_nonempty; exact Hi1).
  pose (T' := fun (i : I) (tr : list event) =>
                (srealizes (nx i) T /\ T tr) \/ (srealizes (nx i) t_nil /\ tr = [])).
  assert (Hcont' : forall i, srealizes (nx i) (T' i)).
  { intro i. destruct (Hcont i) as [Hi | Hi].
    - apply (srz_conseq (nx i) T (T' i) Hi). intro tr. unfold T'. split.
      + intro HT. left. split; assumption.
      + intros [[_ HT] | [Hn ->]]; [exact HT | exact H0].
    - apply (srz_conseq (nx i) t_nil (T' i) Hi). intro tr. unfold T', t_nil. split.
      + intro Htr. right. split; assumption.
      + intros [[HiT HT] | [_ ->]]; [| reflexivity].
        exact (proj1 (srealizes_unique (nx i) T t_nil HiT Hi tr) HT). }
  apply (srz_conseq c (t_alt (fun i : I => t_emit [] (T' i)))).
  - apply (srz_node c I (fun _ => []) nx T' i1 Hnode Hcont').
  - intro tr. unfold t_alt, t_emit. split.
    + intros (i & [Hp | (tr' & -> & HT')]).
      * apply is_prefix_nil_r in Hp. subst tr. exact H0.
      * cbn. destruct HT' as [[_ HT] | [_ ->]]; [exact HT | exact H0].
    + intro HT. exists i1. right. exists tr. split; [reflexivity|].
      left. split; assumption.
Qed.

(** The two-group instance: one group of resolutions dies silently, the
    other continues as [B]. *)
Lemma srz_alt2_absorb_l : forall c (IA IB : Type) (nx : IA + IB -> config) (B : TSet)
                                 (b0 : IB),
  node_ok segs c (IA + IB) (fun _ => []) nx ->
  (forall i, srealizes (nx (inl i)) t_nil) ->
  (forall i, srealizes (nx (inr i)) B) ->
  srealizes c B.
Proof.
  intros c IA IB nx B b0 Hnode HA HB.
  apply (srz_node_same_or_nil c (IA + IB) nx B Hnode).
  - exists (inr b0). apply HB.
  - intros [i|i]; [right; apply HA | left; apply HB].
Qed.

Lemma srz_alt2_absorb_r : forall c (IA IB : Type) (nx : IA + IB -> config) (A : TSet)
                                 (a0 : IA),
  node_ok segs c (IA + IB) (fun _ => []) nx ->
  (forall i, srealizes (nx (inl i)) A) ->
  (forall i, srealizes (nx (inr i)) t_nil) ->
  srealizes c A.
Proof.
  intros c IA IB nx A a0 Hnode HA HB.
  apply (srz_node_same_or_nil c (IA + IB) nx A Hnode).
  - exists (inl a0). apply HA.
  - intros [i|i]; [left; apply HA | right; apply HB].
Qed.

(* -------------------------------------------------------------------------
   Concrete nodes: instruction step(s), write, exit, munmap, mmap.
   ------------------------------------------------------------------------- *)

Lemma srz_step : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  srealizes (mkCfg ms' model) T ->
  srealizes (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlz Hsvc Hstep Hc.
  eapply srz_silent1; [apply node_instr; eassumption | exact Hc].
Qed.

Lemma srz_msteps : forall ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  srealizes (mkCfg ms' model) T ->
  srealizes (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hlz Hms; induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
    intro Hc; [exact Hc|].
  eapply srz_step; [exact Hh | exact Hlz | exact Hsvc | exact Hstep | apply IH; exact Hc].
Qed.

(** A deterministic instruction line that ends in a genuine fault: the
    [ErrEscape] path, as a [t_nil] leaf. *)
Lemma srz_msteps_fault : forall ms ms' model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step segs ms' = MachineFault ->
  srealizes (mkCfg ms model) t_nil.
Proof.
  intros ms ms' model Hh Hlz Hms Hsvc Hf.
  eapply srz_msteps; [exact Hh | exact Hlz | exact Hms |].
  apply srz_fault; cbn; assumption.
Qed.

Lemma srz_write1 : forall ms model x8 buf T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     srealizes (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
  srealizes (mkCfg ms model) (t_write_ch (Z_to_bv 64 1) buf T).
Proof.
  intros ms model x8 buf T Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb Hc.
  unfold t_write_ch.
  apply (srz_of_node (mkCfg ms model) (wr_index buf)
           (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
           (fun i => mkCfg (advance_past_svc
                              (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                           model)
           (fun _ => T)).
  - apply (node_write1 segs ms model x8 buf); assumption.
  - exact (wr_full buf Hnb).
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.

Lemma srz_write_ch : forall ms model fd ch x8 buf T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model -> fd32 fd = fd ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     srealizes (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
  srealizes (mkCfg ms model) (t_write_ch ch buf T).
Proof.
  intros ms model fd ch x8 buf T Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hbm Hnb Hc.
  unfold t_write_ch.
  apply (srz_of_node (mkCfg ms model) (wr_index buf)
           (fun i => map (WriteEv ch) (firstn (proj1_sig i) buf))
           (fun i => mkCfg (advance_past_svc
                              (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                           model)
           (fun _ => T)).
  - eapply node_write_ch; eassumption.
  - exact (wr_full buf Hnb).
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.

(** The [exit] leaf (error-free, so simply embedded). *)
Lemma srz_exit : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  srealizes (mkCfg ms model)
            (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof. intros. apply srz_realizes. eapply rz_exit; eassumption. Qed.

Lemma srz_munmap : forall ms model x8 T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  srealizes (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                   (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T ->
  srealizes (mkCfg ms model) T.
Proof.
  intros ms model x8 T Hh Hlazy Hsvc Hno Hargs Hc.
  eapply srz_silent1; [| exact Hc]. split.
  - intros []. apply (sstep_syscall segs ms model x8 (munmap_eff ms)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
    + exact Hh.
    + exact Hsvc.
    + apply munmap_ok; assumption.
    + rewrite munmap_model_halted; exact Hh.
    + apply materialize_model_accesses_no_lazy.
      exact (munmap_model_no_lazy _ _ _ Hlazy).
  - intros e st Hss.
    destruct (sstep_munmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss)
      as [-> ->].
    exists tt. split; reflexivity.
Qed.

(** The [mmap] node: failure resolutions continue as [A] (typically the
    branch that later FAULTS), success resolutions as [B]. *)
Lemma srz_mmap : forall ms model x8 A B,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  (forall e, In e mmap_errnos ->
     srealizes (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A) ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     srealizes (mkCfg (advance_past_svc
                        (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                      (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B) ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  srealizes (mkCfg ms model) (t_alt2 A B).
Proof.
  intros ms model x8 A B Hh Hlazy Hsvc Hno Hargs HA HB Hex.
  set (n := page_round_up (ms_gpr ms 1)).
  set (nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1))).
  destruct Hex as [a0 Ha0].
  pose (IA := {e : Z | In e mmap_errnos}).
  pose (IB := {a : word | grant_ok (ms_gpr ms 0) model a nZ = true}).
  pose (nx := fun (i : IA + IB) =>
    match i with
    | inl (exist _ e _) => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
    | inr (exist _ a _) =>
        mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, n)])))
              (mmap_model a n model)
    end).
  apply (srz_alt2 (mkCfg ms model) IA IB nx A B
           (exist _ ENOMEM ENOMEM_in_mmap_errnos) (exist _ a0 Ha0)).
  - split.
    + intros [[e He] | [a Ha]]; cbn.
      * rewrite <- (apply_effect_no_write ms (errno_ret e)).
        apply (sstep_syscall segs ms model x8 (mkEffect (errno_ret e) [] [])
                 model model []).
        -- exact Hh.
        -- exact Hsvc.
        -- apply mmap_fail_ok; assumption.
        -- exact Hh.
        -- apply materialize_model_accesses_no_lazy. exact Hlazy.
      * apply (sstep_syscall segs ms model x8 (mkEffect a [] [(a, n)])
                 (mmap_model a n model) (mmap_model a n model) []).
        -- exact Hh.
        -- exact Hsvc.
        -- apply mmap_succ_ok; assumption.
        -- rewrite mmap_model_halted; exact Hh.
        -- apply materialize_model_accesses_no_lazy.
           exact (eq_trans (mmap_model_lazy _ _ _) Hlazy).
    + intros e st Hss.
      destruct (sstep_mmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss)
        as [-> [(er & Her & ->) | (a & Ha & ->)]].
      * exists (inl (exist _ er Her)). split; reflexivity.
      * exists (inr (exist _ a Ha)). split; reflexivity.
  - intros [e He]; cbn. apply HA; exact He.
  - intros [a Ha]; cbn. apply HB; exact Ha.
Qed.

End WithSegs.

(* =========================================================================
   The master equivalence theorem: may-faulting SOURCE vs error-free TARGET
   ========================================================================= *)

Theorem src_shape_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (T T' : TSet) (inp : ProcInput),
  srealizes source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T' ->
  t_eq T T' ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T T' inp Hsource Htarget Heq.
  split.
  { unfold Equivalence.modeled; cbn [run bh_unmodeled].
    eapply srealizes_modeled; exact Hsource. }
  right. split.
  - intro tr. cbn.
    rewrite (srealizes_obs_iff source_segs _ T Hsource tr).
    rewrite (realizes_obs_iff target_segs _ T' Htarget tr).
    apply Heq.
  - cbn. eapply realizes_no_error; exact Htarget.
Qed.

(** Same-shape instance. *)
Corollary src_shape_strong_equiv_same :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (T : TSet) (inp : ProcInput),
  srealizes source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros. eapply src_shape_strong_equiv; [eassumption | eassumption | apply t_eq_refl].
Qed.
