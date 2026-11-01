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
    L4  [pstep_single_next]         at any step that is not a successful clone
    L5  [pstep_single_err]          and not an intercepted wait, the same.
    L6  [pstep_at_sub]              a step of one process is a core step.
    L7  [pstep_cfg_has_actor]       every core step is a step of some process.
    L8  [lineage_pick_one]          a one-process system's lineage is its one
                                    process, [one_pid].
    L9  [pstep_at_one]              in a one-process system, a step of
                                    [one_pid] is any core step.
    L10 [pstep_clone_law]           a successful clone with a free child pid,
                                    where the core allows the call, is a core
                                    step to [clone_result].
    L11 [child_projection_of_clone] a step that adds an entry yields that
                                    entry, with a0 = 0, and the successor's
                                    shared state.
    L12 [lineage_pick_clone]        when the lineage process clones, the new
                                    child becomes the lineage.

    [pstep_at] is indexed by the process that steps, so a step of [p] is a
    step [p] took; the layer reads "who stepped" from that index alone.

    Numbering before 2026-11-01 (old -> now): L1-L6 unchanged; L7
    [pstep_at_stepped_by] removed, the index says who stepped; L8 -> L7;
    L9 -> L8; L10 -> L9; L11 [pstep_clone] -> L10 [pstep_clone_law], with
    the [multiproc_allowed] premise; L12 -> L11; L13 -> L12; L14
    [pni_unfold] -> a lemma of [Ns.Step], which now defines
    [descendant_or_self] and [parents_noninterfering]. *)

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
  Parameter clone_success : config -> config -> bool.
  Parameter wait4_intercept : config -> bool.
  Parameter child_pid : config -> Pid -> Prop.

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
  Parameter pe_cfg : shared -> ProcessEntry -> config.
  Parameter one_pid : Pid.
  Parameter one_proc : config -> pconfig.
  (** The core takes the call in a system of several processes; a clone it
      does not take there is no step of [pstep_clone_law]'s kind. *)
  Parameter multiproc_allowed : pconfig -> config -> bool.

  Parameter pstep_to : Type.
  Parameter PNext : pconfig -> pstep_to.
  Parameter PError : pstep_to.
  Parameter pstep_cfg : StepCtx -> pconfig -> list event -> pstep_to -> Prop.
  Parameter pstep_at : StepCtx -> Pid -> pconfig -> list event -> pstep_to -> Prop.
  Parameter lineage_pick : pconfig -> Pid -> Prop.
  Parameter clone_result : pconfig -> ProcessEntry -> config -> Pid -> pconfig.
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
  Parameter pstep_single_next : forall ctx c evs P',
    (forall c', sstep_cfg ctx c evs (SNext c') -> clone_success c c' = false) ->
    wait4_intercept c = false ->
    (pstep_cfg ctx (one_proc c) evs (PNext P')
     <-> exists c', P' = one_proc c' /\ sstep_cfg ctx c evs (SNext c')).

  (** L5 *)
  Parameter pstep_single_err : forall ctx c evs, wait4_intercept c = false ->
    (pstep_cfg ctx (one_proc c) evs PError <-> sstep_cfg ctx c evs SError).

  (** L6 *)
  Parameter pstep_at_sub : forall ctx p P evs r,
    pstep_at ctx p P evs r -> pstep_cfg ctx P evs r.

  (** L7 *)
  Parameter pstep_cfg_has_actor : forall ctx P evs r,
    pstep_cfg ctx P evs r -> exists p, pstep_at ctx p P evs r.

  (** L8 *)
  Parameter lineage_pick_one : forall c p, lineage_pick (one_proc c) p <-> p = one_pid.

  (** L9 *)
  Parameter pstep_at_one : forall ctx c evs r,
    pstep_at ctx one_pid (one_proc c) evs r <-> pstep_cfg ctx (one_proc c) evs r.

  (** L10 *)
  Parameter pstep_clone_law : forall ctx P e evs c' q,
    look P (pe_pid e) = Some e ->
    sstep_cfg ctx (pe_cfg (pcfg_shared P) e) evs (SNext c') ->
    clone_success (pe_cfg (pcfg_shared P) e) c' = true ->
    child_pid c' q ->
    look P q = None ->
    multiproc_allowed P (pe_cfg (pcfg_shared P) e) = true ->
    pstep_cfg ctx P evs (PNext (clone_result P e c' q)).

  (** L11 *)
  Parameter child_projection_of_clone : forall ctx P evs P',
    pstep_cfg ctx P evs (PNext P') ->
    length (pcfg_procs P') > length (pcfg_procs P) ->
    exists e sh, child_projection P P' = Some (e, sh) /\ entry_a0_zero e /\ sh = pcfg_shared P'.

  (** L12 *)
  Parameter lineage_pick_clone : forall ctx P p evs P' e sh,
    lineage_pick P p ->
    pstep_at ctx p P evs (PNext P') ->
    child_projection P P' = Some (e, sh) ->
    lineage_pick P' (pe_pid e).

End PROCS_CORE.
