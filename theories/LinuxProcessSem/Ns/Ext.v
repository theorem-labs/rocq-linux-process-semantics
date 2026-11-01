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
    host's, which the released model describes), a claimed call has
    exactly the released outcomes ([released]), [EUnmodeled] where the
    released model declines, and the namespace context and state stay as
    they were.  So an extension answers differently from the released
    model only for a task in a namespace the released model does not
    describe, and it adds no answer to a call the released model declines.
    [no_ext] claims nothing.

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
    statements.

    [ext_clone] is what a successful or failing [clone] does to the
    namespace model, for a core whose own clone step creates the child:
    for the clone's flag word, the caller's spliced model, context and
    state, and the pid the core gives the child, a [CnOk] with the child's
    context and the next state, or a [CnErr] with the errno and the state
    after the failure, or [CnUnmodeled].  [ext_clone_coherent] makes it
    the core's own clone in the released world for a word with no
    namespace bit: the child gets the caller's context, the state does
    not change, and a failure is any errno.

    Which clone failures a run admits is not the extension's to choose: a
    core takes it as an explicit argument, a [CloneEnv], which a statement
    names.  [any_clone_failure] admits every failure the core and the
    extension give.  A narrower one is an environment premise of the
    statement that names it (the LPS owner's decision, 2026-11-01).

    [ext_multiproc] names the claimed calls the extension answers soundly
    while other processes are live: those whose answer reads and writes
    only state the core shares between processes.  A core admits a
    claimed call in a system of several processes when its own guard
    admits it or this one does.  [ext_multiproc_coherent] gives a task in
    the released world the core's guard alone. *)

From Stdlib Require Import List PArith ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables.
Import ListNotations.

Inductive ext_outcome :=
  | EOk (eff : SyscallEffect) (m : Model) (ctx : NsCtx) (st : NsState) (evs : list event)
  | EUnmodeled.

(** A clone's answer: the child's context and the new shared state; or the
    errno and the shared state after the failure; or no answer. *)
Inductive CloneNs :=
  | CnOk (child : NsCtx) (st : NsState)
  | CnErr (e : Z) (st : NsState)
  | CnUnmodeled.

(** The namespace bits of a clone flag word: CLONE_NEWNS, CLONE_NEWCGROUP,
    CLONE_NEWUTS, CLONE_NEWIPC, CLONE_NEWUSER, CLONE_NEWPID, CLONE_NEWNET
    (include/uapi/linux/sched.h). *)
Definition clone_ns_bits : Z :=
  fold_left Z.lor [131072; 33554432; 67108864; 134217728; 268435456; 536870912; 1073741824]%Z 0%Z.

Definition has_ns_bits (f : Z) : bool := negb (Z.eqb (Z.land f clone_ns_bits) 0).

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

(** The released clone's own answer, seen by the namespace model: the
    child gets the caller's context, the state does not change, and a
    failure is any errno. *)
Definition released_clone (ctx : NsCtx) (st : NsState) (o : CloneNs) : Prop :=
  o = CnOk ctx st \/ exists e, (1 <= e <= 4095)%Z /\ o = CnErr e st.

(** The released answer, with the namespace context and state unchanged. *)
Definition released (i : SyscallInput) (m : Model) (ctx : NsCtx) (st : NsState)
    (o : ext_outcome) : Prop :=
  match o with
  | EOk eff m' ctx' st' evs => ctx' = ctx /\ st' = st /\ syscall_spec i m (Ok eff m' evs)
  | EUnmodeled => syscall_spec i m Unmodeled
  end.

Record ExtSpec := mkExtSpec {
  ext_claims    : SyscallInput -> bool;
  ext_spec      : SyscallInput -> Model -> NsCtx -> NsState -> ext_outcome -> Prop;
  ext_refusal   : SpuriousCfg -> SyscallInput -> Model -> NsCtx -> NsState -> SyscallEffect -> Prop;
  ext_clone     : Z -> Model -> NsCtx -> NsState -> Z -> CloneNs -> Prop;
  ext_multiproc : SyscallInput -> Model -> NsCtx -> NsState -> bool;
  ext_coherent : forall i m ctx st,
    flat_view ctx st = true -> ext_claims i = true ->
    forall o, ext_spec i m ctx st o <-> released i m ctx st o;
  ext_refusal_coherent : forall cfg i m ctx st eff,
    flat_view ctx st = true -> ext_claims i = true ->
    (ext_refusal cfg i m ctx st eff <-> spurious_refusal_cfg cfg i m eff);
  ext_clone_coherent : forall f m ctx st hq o,
    flat_view ctx st = true -> has_ns_bits f = false ->
    (ext_clone f m ctx st hq o <-> released_clone ctx st o);
  ext_multiproc_coherent : forall i m ctx st,
    flat_view ctx st = true -> ext_multiproc i m ctx st = false
}.

(** The extension that claims nothing: the core's released step, and the
    core's own clone. *)
Definition no_ext : ExtSpec.
Proof.
  refine (mkExtSpec (fun _ => false) (fun _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False)
                    (fun _ _ ctx st _ o => released_clone ctx st o) (fun _ _ _ _ => false)
                    _ _ _ _).
  - intros i m ctx st _ Hc. discriminate Hc.
  - intros cfg i m ctx st eff _ Hc. discriminate Hc.
  - intros f m ctx st hq o _ _. reflexivity.
  - intros i m ctx st _. reflexivity.
Defined.

Lemma no_ext_claims_nothing : forall i, ext_claims no_ext i = false.
Proof. reflexivity. Qed.

Lemma no_ext_clone : forall f m ctx st hq o, ext_clone no_ext f m ctx st hq o <-> released_clone ctx st o.
Proof. reflexivity. Qed.

Lemma no_ext_multiproc : forall i m ctx st, ext_multiproc no_ext i m ctx st = false.
Proof. reflexivity. Qed.

(** The clone failures a run admits: for the clone's flag word, the
    caller's model, context and state, the pid the core gives the child,
    the errno and the state after the failure. *)
Definition CloneEnv : Type := Z -> Model -> NsCtx -> NsState -> Z -> Z -> NsState -> Prop.

(** Every failure: the unrestricted relation. *)
Definition any_clone_failure : CloneEnv := fun _ _ _ _ _ _ _ => True.
