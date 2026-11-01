(** * LinuxProcessSem.Ns.Ext — what a step extension answers

    A multi-process core may answer some system calls with an extension
    instead of the released step.  An extension says which inputs it
    claims, and relates a claimed input, the calling process's model (the
    spliced one: the process's own state with the shared file system and
    I/O in place), its namespace context and the shared namespace state to
    an outcome: an effect with the next model, context and state, or
    [EUnmodeled].

    [ext_coherent] is the obligation every extension carries: for a task
    in the released world ([flat_view]: each of its namespaces is the
    host's, which the released model describes), a claimed call that the
    released model answers has exactly the released outcomes, and the
    namespace context and state stay as they were.  So an extension answers
    differently from the released model only for a task in a namespace the
    released model does not describe.  [no_ext] claims nothing.

    [ext_refusal] is the forced-only filter for claimed calls, as
    [Run.spurious_refusal_cfg] is for the released ones: under a
    configuration [cfg], an answer that is an injected refusal of a family
    [cfg] keeps from failing, where the state did not force it, is not a
    step.  A core MUST make [~ ext_refusal cfg i m ctx st eff] a premise of
    the step that takes a claimed call's effect.  Without that premise a
    statement over an extension would be strictly easier than over the
    released model, which keeps no refusal branch the filter removes: that
    is the soundness gap the field closes.  [ext_refusal_coherent] makes it
    the released filter in the released world, for every [cfg]: under
    [forced_only_cfg] it drops exactly the refusals the released step
    drops, and under [may_fail_cfg] it drops nothing, as the released
    filter does (no family is off there); both readings occur in
    statements. *)

From Stdlib Require Import List PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables.

Inductive ext_outcome :=
  | EOk (eff : SyscallEffect) (m : Model) (ctx : NsCtx) (st : NsState) (evs : list event)
  | EUnmodeled.

(** A task is in the released world when each of its namespaces is the
    host's: its mount namespace is not in the tables or is marked
    [mntns_released]; its user namespace and pid namespace are not in the
    tables or have no parent; its network namespace is not in the tables
    or is not sealed.  A task the tables know nothing of is in the
    released world, so is every task of [empty_nsstate]
    ([flat_view_empty]); a new field of [NsState] must keep that. *)
Definition flat_view (ctx : NsCtx) (st : NsState) : bool :=
  match find (fun n => Pos.eqb (mntns_id n) (cx_mount ctx)) (ns_mntns st) with
  | Some n => mntns_released n | None => true end
  && match find (fun u => Pos.eqb (uns_id u) (cx_user ctx)) (ns_userns st) with
     | Some u => match uns_parent u with None => true | Some _ => false end | None => true end
  && match find (fun p => Pos.eqb (pidns_id p) (cx_pidns ctx)) (ns_pidns st) with
     | Some p => match pidns_parent p with None => true | Some _ => false end | None => true end
  && match find (fun n => Pos.eqb (netns_id n) (cx_net ctx)) (ns_netns st) with
     | Some n => negb (netns_sealed n) | None => true end.

Lemma flat_view_empty : forall ctx, flat_view ctx empty_nsstate = true.
Proof. reflexivity. Qed.

Record ExtSpec := mkExtSpec {
  ext_claims   : SyscallInput -> bool;
  ext_spec     : SyscallInput -> Model -> NsCtx -> NsState -> ext_outcome -> Prop;
  ext_refusal  : SpuriousCfg -> SyscallInput -> Model -> NsCtx -> NsState -> SyscallEffect -> Prop;
  ext_coherent : forall i m ctx st,
    flat_view ctx st = true -> ext_claims i = true -> ~ syscall_spec i m Unmodeled ->
    forall o, ext_spec i m ctx st o <->
              exists eff m' evs, o = EOk eff m' ctx st evs /\ syscall_spec i m (Ok eff m' evs);
  ext_refusal_coherent : forall cfg i m ctx st eff,
    flat_view ctx st = true -> ext_claims i = true ->
    (ext_refusal cfg i m ctx st eff <-> spurious_refusal_cfg cfg i m eff)
}.

(** The extension that claims nothing: the core's released step. *)
Definition no_ext : ExtSpec.
Proof.
  refine (mkExtSpec (fun _ => false) (fun _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False) _ _).
  - intros i m ctx st _ Hc. discriminate Hc.
  - intros cfg i m ctx st eff _ Hc. discriminate Hc.
Defined.

Lemma no_ext_claims_nothing : forall i, ext_claims no_ext i = false.
Proof. reflexivity. Qed.
