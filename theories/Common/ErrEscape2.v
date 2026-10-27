(** * Common.ErrEscape2 — SOURCE-ERROR ESCAPE glue through syscall steps.

    TRUST BOUNDARY: image-INDEPENDENT proof library (like
    Common.ErrEscape), NOT part of the trusted specification.

    The statements are model-generic glue: [x8 : word] is a [bv 64]
    syscall number, and the [Equivalence]-level conclusion is spelled
    [Equivalence.equiv] (stdpp shadows bare [equiv]).

    Common.ErrEscape covers the universal escape for a straight line of
    ordinary instructions ending in an illegal one.  This file retains
    compositional MAY-error reachability helpers for diagnostics and
    target-safety proofs.  In particular, choosing one successful brk
    resolution and faulting afterward does NOT establish the source
    escape when a different brk resolution avoids error:

    - [reaches_error_star]: prepend any [star] run to a
      [reaches_error] witness;
    - [reaches_error_msteps]: prepend a deterministic instruction run;
    - [reaches_error_syscall]: step through an ecall with a CHOSEN
      admissible effect (the erroring resolution the prover picks);
    - [reaches_error_illegal]: the terminal witness — the current
      instruction is illegal;
    - [err_escape_run]: at the [Equivalence] level, an
      [all_traces_error] proof (not a [reaches_error] witness) discharges
      [equiv] against any target. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatSim ErrEscape FileSim.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

(* reaches_error_star lives in FileSim. *)

(** Prepend a deterministic instruction run (the model is untouched). *)
Lemma reaches_error_msteps : forall ms ms' model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  reaches_error segs (mkCfg ms' model) ->
  reaches_error segs (mkCfg ms model).
Proof.
  intros ms ms' model Hh Hlazy Hm Herr.
  eapply reaches_error_star; [|exact Herr].
  apply msteps_star_nil; assumption.
Qed.

(** Step through an ecall with a CHOSEN admissible effect. *)
Lemma reaches_error_syscall : forall ms model x8 eff model' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  m_halted model' = None ->
  m_vm_lazy model' = [] ->
  reaches_error segs
    (mkCfg (advance_past_svc (apply_effect ms eff)) model') ->
  reaches_error segs (mkCfg ms model).
Proof.
  intros ms model x8 eff model' evs Hh Hsvc Hspec Hh' Hlazy Herr.
  eapply reaches_error_star; [|exact Herr].
  apply star_one.
  apply (sstep_syscall segs ms model x8 eff model' model' evs);
    try assumption.
  rewrite (materialize_model_accesses_no_lazy model' _ Hlazy). reflexivity.
Qed.

(** Terminal witness: the current instruction faults. *)
Lemma reaches_error_illegal : forall ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineFault ->
  reaches_error segs (mkCfg ms model).
Proof.
  intros ms model Hh Hlazy Hsvc Hill.
  exists [], (mkCfg ms model), [].
  split; [apply star_refl |].
  apply sstep_instr_fault; try assumption.
  rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hill. reflexivity.
Qed.

End WithSegs.

(** Equivalence-level escape: every source execution must error. *)
Lemma err_escape_run :
  forall segs pc ph sp brk0 mb rnd lim inp (target : behavior),
  all_traces_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) ->
  Equivalence.equiv (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) target.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp target Hall.
  left. cbn [run bh_all_errors]. exact Hall.
Qed.
