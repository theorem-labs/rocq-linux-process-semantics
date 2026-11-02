(** * LinuxProcessSem.Ns.ProcsIface — what the namespace layer needs of a multi-process core

    The namespace-and-mount layer runs on a multi-process core: a relation
    over a list of per-process entries, with a shared state, in which a
    successful [clone] makes the child an entry.  This module type states the
    core's names and the laws the layer relies on, so the layer's
    definitions and proofs ([Ns.Step]) are written once, as a functor, and a
    core becomes usable by applying the functor to it and proving these laws.

    Every type is abstract.  The layer does not depend on the shape of the
    released single-process configuration, nor on whether the core's step
    takes the segment list: [StepCtx] stands for whatever the core's step is
    parameterised by.  The layer's own records reach the core through two
    accessors: [pe_nsctx], what a process's namespace context is, and
    [sh_nsstate], what the shared namespace state is.  A third, [pe_ofd],
    reads a process's descriptor table (descriptor number to the open file
    description it names), so a consumer can name descriptions.

    THE LAWS, each one a statement about the core that the core proves when
    it instantiates this module type:

    L1  [pstep_to_cases]            a core step ends in [PNext] or [PError].
    L2  [pstep_instr_single_next]   at an instruction, a one-process system
    L3  [pstep_instr_single_err]    steps exactly as the released step does.
    L4  [pstep_at_sub]              a step of one process is a core step.
    L5  [pstep_cfg_has_actor]       every core step is a step of some process.
    L6  [lineage_pick_one]          a one-process system's lineage is its one
                                    process, [one_pid].
    L7  [pstep_at_one]              in a one-process system, a step of
                                    [one_pid] is any core step.
    L8  [child_projection_of_clone] a step that adds an entry yields that
                                    entry, with a0 = 0, and the successor's
                                    shared state.
    L9  [lineage_pick_clone]        when the lineage process clones, the new
                                    child becomes the lineage.

    [pstep_at] is indexed by the process that steps, so a step of [p] is a
    step [p] took; the layer reads "who stepped" from that index alone.

    The core is the multi-process core WITH the namespace model plugged in
    ([Procs.pstep_x_at] at [Ns.Spec.ns_ext]), so the laws hold only where
    that relation is the released one: at an instruction (L2, L3), not at
    every call.  A one-process system at a clone that makes a namespace
    steps as the namespace model says, which is why the laws on calls
    (the old L4, L5) and the clone law (the old L10) are not here: a
    consumer uses the concrete core's own theorems for those.

    Numbering before 2026-11-01 (old -> now): L1-L3 unchanged; L4
    [pstep_single_next], L5 [pstep_single_err] and L10 [pstep_clone_law]
    removed; L6 -> L4; L7 -> L5; L8 -> L6; L9 -> L7; L11 -> L8; L12 -> L9.
    The names [clone_success], [wait4_intercept], [child_pid],
    [multiproc_allowed], [clone_result] and [pe_cfg], which only the
    removed laws read, are removed with them. *)

From Stdlib Require Import List PArith.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables.
Import ListNotations.

Module Type PROCS_CORE.

  (** A process id.  Abstract: the core fixes it (a machine word); the layer
      only compares them through [look] and the core's relations. *)
  Parameter Pid : Type.

  (* ---- The released single-process step, abstract ---- *)
  Parameter StepCtx : Type.
  Parameter config : Type.
  Parameter event : Type.
  Parameter step_to : Type.
  Parameter SNext : config -> step_to.
  Parameter SError : step_to.
  Parameter sstep_cfg : StepCtx -> config -> list event -> step_to -> Prop.
  (** No system call is pending: the next step is an instruction. *)
  Parameter at_instruction : config -> Prop.

  (* ---- The multi-process core ---- *)
  Parameter OfdId : Type.
  (** Two processes share an open file description when their tables name
      the same id, so the ids compare. *)
  Parameter ofd_eq_dec : forall a b : OfdId, {a = b} + {a <> b}.
  Parameter Fd : Type.
  Parameter ProcessEntry : Type.
  Parameter shared : Type.
  Parameter pconfig : Type.
  Parameter pe_pid : ProcessEntry -> Pid.
  Parameter pe_parent : ProcessEntry -> option Pid.
  Parameter pe_ofd : ProcessEntry -> list (Fd * OfdId).
  Parameter pe_nsctx : ProcessEntry -> NsCtx.
  Parameter sh_nsstate : shared -> NsState.
  Parameter pcfg_procs : pconfig -> list (Pid * ProcessEntry).
  Parameter pcfg_root : pconfig -> Pid.
  Parameter pcfg_shared : pconfig -> shared.
  Parameter look : pconfig -> Pid -> option ProcessEntry.
  Parameter one_pid : Pid.
  Parameter one_proc : config -> pconfig.

  Parameter pstep_to : Type.
  Parameter PNext : pconfig -> pstep_to.
  Parameter PError : pstep_to.
  Parameter pstep_cfg : StepCtx -> pconfig -> list event -> pstep_to -> Prop.
  Parameter pstep_at : StepCtx -> Pid -> pconfig -> list event -> pstep_to -> Prop.
  Parameter lineage_pick : pconfig -> Pid -> Prop.
  Parameter child_projection : pconfig -> pconfig -> option (ProcessEntry * shared).
  (** The entry's a0 register is zero: how a clone's child sees the call. *)
  Parameter entry_a0_zero : ProcessEntry -> Prop.

  (* ---- The laws ---- *)

  (** L1 *)
  Parameter pstep_to_cases : forall r, (exists P, r = PNext P) \/ r = PError.

  (** L2 *)
  Parameter pstep_instr_single_next : forall ctx c evs P', at_instruction c ->
    (pstep_cfg ctx (one_proc c) evs (PNext P')
     <-> exists c', P' = one_proc c' /\ sstep_cfg ctx c evs (SNext c')).

  (** L3 *)
  Parameter pstep_instr_single_err : forall ctx c evs, at_instruction c ->
    (pstep_cfg ctx (one_proc c) evs PError <-> sstep_cfg ctx c evs SError).

  (** L4 *)
  Parameter pstep_at_sub : forall ctx p P evs r,
    pstep_at ctx p P evs r -> pstep_cfg ctx P evs r.

  (** L5 *)
  Parameter pstep_cfg_has_actor : forall ctx P evs r,
    pstep_cfg ctx P evs r -> exists p, pstep_at ctx p P evs r.

  (** L6 *)
  Parameter lineage_pick_one : forall c p, lineage_pick (one_proc c) p <-> p = one_pid.

  (** L7 *)
  Parameter pstep_at_one : forall ctx c evs r,
    pstep_at ctx one_pid (one_proc c) evs r <-> pstep_cfg ctx (one_proc c) evs r.

  (** L8 *)
  Parameter child_projection_of_clone : forall ctx P evs P',
    pstep_cfg ctx P evs (PNext P') ->
    length (pcfg_procs P') > length (pcfg_procs P) ->
    exists e sh, child_projection P P' = Some (e, sh) /\ entry_a0_zero e /\ sh = pcfg_shared P'.

  (** L9 *)
  Parameter lineage_pick_clone : forall ctx P p evs P' e sh,
    lineage_pick P p ->
    pstep_at ctx p P evs (PNext P') ->
    child_projection P P' = Some (e, sh) ->
    lineage_pick P' (pe_pid e).

End PROCS_CORE.
