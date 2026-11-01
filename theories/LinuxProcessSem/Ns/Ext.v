(** * LinuxProcessSem.Ns.Ext — what a step extension answers

    A multi-process core may answer some system calls with an extension
    instead of the released step.  An extension says which inputs it
    claims, and relates a claimed input, the calling process's model (the
    spliced one: the process's own state with the shared file system and
    I/O in place), its namespace context and the shared namespace state to
    an outcome: an effect with the next model, context and state, or
    [EUnmodeled].

    [ext_coherent] is the obligation every extension carries: in the
    released world, where no mount tree is known ([flat_view]), a claimed
    call that the released model answers has exactly the released
    outcomes, and the namespace context and state stay as they were.  So an
    extension answers differently from the released model only in states
    the released model does not describe.  [no_ext] claims nothing.

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

From LinuxProcessSemantics.LinuxProcessSem Require Import State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables.

Inductive ext_outcome :=
  | EOk (eff : SyscallEffect) (m : Model) (ctx : NsCtx) (st : NsState) (evs : list event)
  | EUnmodeled.

(** The released world: no mount tree is known, so every path is the flat
    file system's.  A new field of [NsState] must keep
    [flat_view empty_nsstate = true] ([flat_view_empty]). *)
Definition flat_view (st : NsState) : bool :=
  match ns_mounts st with nil => true | cons _ _ => false end.

Lemma flat_view_empty : flat_view empty_nsstate = true.
Proof. reflexivity. Qed.

Record ExtSpec := mkExtSpec {
  ext_claims   : SyscallInput -> bool;
  ext_spec     : SyscallInput -> Model -> NsCtx -> NsState -> ext_outcome -> Prop;
  ext_refusal  : SpuriousCfg -> SyscallInput -> Model -> NsCtx -> NsState -> SyscallEffect -> Prop;
  ext_coherent : forall i m ctx st,
    flat_view st = true -> ext_claims i = true -> ~ syscall_spec i m Unmodeled ->
    forall o, ext_spec i m ctx st o <->
              exists eff m' evs, o = EOk eff m' ctx st evs /\ syscall_spec i m (Ok eff m' evs);
  ext_refusal_coherent : forall cfg i m ctx st eff,
    flat_view st = true -> ext_claims i = true ->
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
