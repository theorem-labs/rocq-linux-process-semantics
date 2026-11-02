(* Written by the OSS-Fuzz proof collaborators. *)
(** * Common.ShapeEF — the ERROR-FREE master theorem over [ShapeAlg.realizes].

    Image-INDEPENDENT.  ([init_config] / [mkEntry] take the mmap base and
    the AT_RANDOM draw [ed_random] as extra arguments, so every statement
    carries one more binder of each per side.)

    [ShapeAlg.shape_strong_equiv] concludes [modeled /\ equiv]; the checked
    statements are [strong_universal_error_free_T], whose per-triple
    obligation is [strong_equiv_error_free] =
      error_free (run src) /\ error_free (run tgt) /\ trace_equiv ... .
    Both sides being [realizes] of ONE shape gives exactly that
    conjunction (stated with the images/limits/entries spelled out, so it
    unifies with [strong_equiv_error_free src tgt (mkEntry ..) (mkEntry ..) inp]
    after [unfold strong_equiv_error_free]): [realizes_no_error] on each
    side and [realizes_obs_iff] twice.

    The configuration surface ([Equivalence.strong_universal_error_free_T_cfg
    alloc_may_fail]) is reached only in its [true] reading, which is this
    statement by [Equivalence.strong_universal_error_free_T_cfg_true];
    [ShapeAlg.realizes] is stated over the default configuration, so the
    forced-only ([alloc_may_fail = false]) sibling is not derivable here. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.Common Require Import SimInv ExitSim CatSim ShapeAlg.

Import ListNotations.
Open Scope bv_scope.

Theorem shape_strong_equiv_ef :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes (run_segments source_segs inp rsp rmb)
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes (run_segments target_segs inp asp amb)
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd alim inp) T ->
  error_free (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hsource Htarget.
  split; [| split].
  - cbn. eapply realizes_no_error; exact Hsource.
  - cbn. eapply realizes_no_error; exact Htarget.
  - intro tr. cbn.
    rewrite (realizes_obs_iff (run_segments source_segs inp rsp rmb) _ T Hsource tr).
    rewrite (realizes_obs_iff (run_segments target_segs inp asp amb) _ T Htarget tr).
    reflexivity.
Qed.

(** Same, when the two sides were proved against extensionally equal but
    syntactically different shapes. *)
Corollary shape_strong_equiv_ef_eq :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T T' : TSet) (inp : ProcInput),
  realizes (run_segments source_segs inp rsp rmb)
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes (run_segments target_segs inp asp amb)
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd alim inp) T' ->
  t_eq T T' ->
  error_free (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros until T'. intros inp Hs Ht Heq.
  eapply shape_strong_equiv_ef; [| exact Ht].
  eapply rz_conseq; [exact Hs | exact Heq].
Qed.

(** The single-side facts, for callers that assemble the conjunction
    themselves. *)
Lemma realizes_error_free : forall segs pc ph sp brk0 mb rnd lim inp T,
  realizes (run_segments segs inp sp mb) (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) T ->
  error_free (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof. intros. cbn. eapply realizes_no_error; eassumption. Qed.

Lemma realizes_traces_iff : forall segs pc ph sp brk0 mb rnd lim inp T tr,
  realizes (run_segments segs inp sp mb) (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) T ->
  bh_traces (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) tr <-> T tr.
Proof. intros. cbn. apply realizes_obs_iff. assumption. Qed.
