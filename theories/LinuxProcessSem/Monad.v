(** * LinuxProcessSem.Monad — the non-determinism monad for syscall specs

    TRUST BOUNDARY: this file is part of the trusted specification.

    A [Sys A] spec is a RELATION: given the syscall's [SyscallInput] (read-
    only) and the current [Model], it relates them to the set of admissible
    [outcome]s.  An outcome is either

    - [Ok x m' evs] — the syscall may return [x], leaving the model in [m']
      and emitting the observable events [evs]; or
    - [Unmodeled] — the program did something the model does not cover (an
      unmodeled syscall, an unreadable user buffer, unmodeled flags…).
      [Unmodeled] is a POSITIVE outcome, not an empty relation: it drives the
      explicit error transition in [Run.sstep] (fail closed), rather than
      leaving the semantics stuck.

    (Standard input is NOT part of this non-determinism: the bytes stdin
    delivers come from the run's [InputStream] parameter, threaded in the
    model's [m_stdin] field; only HOW MANY of them a given read delivers
    — short reads — is chosen here.)

    Non-determinism is set-valued: [choose P] has one [Ok] outcome per
    value satisfying [P], and [alt] unions two outcome sets.  Specs must be
    RECEPTIVE — every input and model state admits at least one outcome
    (possibly [Unmodeled]); this is validated by [Progress.receptive].  The one
    way to write a non-receptive spec is [choose] with an unsatisfiable
    predicate, so [choose] should always be guarded by an obviously
    inhabited predicate or an [alt]ernative branch.

    The spec GENERATES admissible effects.  It does not take the observed
    result as an input and accept or reject it: that would tie the spec's
    shape to what a particular tester could observe and need erased
    [Prop] side-conditions for memory framing.  The executable acceptor
    is derived separately and
    verified against this relation (see ExecutableSpecs.v).

    ** What kind of monad is this?

    [Sys] is a single monad that stacks five classic effects.  Reading the
    signature [SyscallInput -> Model -> outcome A -> Prop] left to right:

    - READER over [SyscallInput].  The input [i] is threaded unchanged
      through [bind] (both sides see the same [i]) and never appears on the
      output side of an [outcome].  It is read-only environment — [input],
      [sysno] and [arg] are the [ask]/[asks] of this reader.

    - STATE over [Model].  The model [m] flows in on the left and a possibly
      updated [m'] comes back inside [Ok].  [get_model] is [get]; [modify]
      (and its wrappers [set_fds], [set_fs], …) is [modify].

    - WRITER over [list event].  Each [Ok] carries the events emitted by
      that step; [bind] concatenates them in chronological order
      ([evs1 ++ evs2]).  The monoid is [(list event, [], ++)]; [emit] is
      [tell].

    - EXCEPTION with a unit payload: the [Unmodeled] outcome.  [bind]
      short-circuits on [Unmodeled] — no later step runs — and, crucially, an
      [Unmodeled] carries NO model and NO events, so a failing computation
      discards any state update and any events it might have produced.
      [unmodeled] is [throwError]; there is deliberately no [catchError] (fail
      closed).

    - NON-DETERMINISM.  [Sys A] is set-valued: [outcome A -> Prop] is the
      powerset of outcomes rather than a single outcome, so one computation
      may admit many results.  [choose] introduces choice and [alt] unions
      two outcome sets; the empty set is the (to-be-avoided) non-receptive
      spec.  This is the base effect the other four are layered on top of.

    ** The same thing as a Haskell monad-transformer stack

    If you built this in Haskell from off-the-shelf transformers, [Sys]
    would be (reading outermost transformer first):

        type NondetM = []             -- non-determinism (a set of results)

        type Sys =
          ReaderT SyscallInput      -- read-only input i
            (StateT  Model          -- threaded model m
              (WriterT [Event]      -- emitted events, monoid = (++)
                (ExceptT ()         -- Unmodeled (unit payload), short-circuits
                  NondetM)))        -- non-determinism is the base monad

    Equivalently, with [Set] (= [_ -> Prop]) as the non-determinism base to
    match the [Prop]-valued encoding used here:

        newtype Sys a = Sys
          { runSys :: SyscallInput -> Model -> Set (Either () ((a, Model), [Event])) }

    where [Left ()] is [Unmodeled] and [Right ((x, m'), evs)] is [Ok x m' evs].
    Expanding the [runSys] type of the transformer stack gives exactly

        SyscallInput -> Model -> Set (Either () ((a, Model), [Event]))

    which is [SyscallInput -> Model -> outcome a -> Prop] up to the iso
    [outcome a ≅ Either () ((a, Model), [Event])] and [Set x ≅ x -> Prop].

    The ORDER of the transformers is not incidental — it is what makes an
    [Unmodeled] discard the model and the events:

    - [ExceptT] sits INNERMOST (just above the [NondetM] base), i.e. BELOW both
      [StateT] and [WriterT].  With [StateT s (ExceptT e m)] a run yields
      [s -> m (Either e (a, s))]: the [Either] is inside, so the [Left]
      (unmodeled) branch carries no [s] — the state is thrown away.  Likewise
      [WriterT w (ExceptT e m)] yields [m (Either e (a, w))], so an error
      carries no accumulated [w].  Had we instead put [ExceptT] on the
      OUTSIDE ([ExceptT e (StateT s m)] ≡ [s -> m (Either e a, s)]) the
      final state would survive the error — the wrong semantics for a
      fail-closed model where [Unmodeled] means "the model does not cover
      this; abandon this run".

    - [ReaderT] can go anywhere (its environment does not interact with the
      other layers); outermost is the conventional, readable choice.

    - The non-determinism monad is the BASE, so the whole [runSys] is a set:
      choice ranges over complete outcomes.

    ** Monad laws

    Because [Sys A] is a RELATION, two specs are "equal" when they relate
    exactly the same outcomes.  We spell that out as [sys_equiv] and prove
    the three monad laws (left identity, right identity, associativity) up
    to it below, so [pure]/[bind] really do form a monad. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
Import ListNotations.
Open Scope bv_scope.

Inductive outcome (A : Type) :=
  | Ok (x : A) (m : Model) (evs : list event)
  | Unmodeled.
Arguments Ok {A}.
Arguments Unmodeled {A}.

Definition Sys (A : Type) : Type := SyscallInput -> Model -> outcome A -> Prop.

Definition pure {A} (x : A) : Sys A := fun _ m o => o = Ok x m [].

(** Sequencing: an [Unmodeled] anywhere in the chain is an [Unmodeled] of the whole
    program; event lists concatenate in chronological order. *)
Definition bind {A B} (c : Sys A) (k : A -> Sys B) : Sys B :=
  fun i m o =>
    match o with
    | Unmodeled =>
        c i m Unmodeled \/
        (exists x m1 evs1, c i m (Ok x m1 evs1) /\ k x i m1 Unmodeled)
    | Ok y m2 evs =>
        exists x m1 evs1 evs2,
          c i m (Ok x m1 evs1) /\ k x i m1 (Ok y m2 evs2) /\ evs = evs1 ++ evs2
    end.

Declare Scope sys_scope.
Delimit Scope sys_scope with sys.

Notation "x <- c ;; k" := (bind c (fun x => k))
  (at level 100, c at next level, k at level 200, right associativity) : sys_scope.
Notation "c ;; k" := (bind c (fun _ => k))
  (at level 100, k at level 200, right associativity) : sys_scope.

Open Scope sys_scope.

(* =========================================================================
   Monad laws

   [Sys A] is a relation, so equality of specs is extensional: two specs
   are equivalent when they admit exactly the same outcomes for every input
   and starting model.  We do not assume functional/propositional
   extensionality, so the laws are stated up to this [sys_equiv] rather than
   Rocq's [=].
   ========================================================================= *)

Definition sys_equiv {A} (c1 c2 : Sys A) : Prop :=
  forall i m o, c1 i m o <-> c2 i m o.

Infix "≡" := sys_equiv (at level 70, no associativity) : sys_scope.

(** [sys_equiv] is an equivalence relation (this is what lets us read the
    laws below as genuine equations). *)
Lemma sys_equiv_refl {A} (c : Sys A) : c ≡ c.
Proof. intros i m o; reflexivity. Qed.

Lemma sys_equiv_sym {A} (c1 c2 : Sys A) : c1 ≡ c2 -> c2 ≡ c1.
Proof. intros H i m o; symmetry; apply H. Qed.

Lemma sys_equiv_trans {A} (c1 c2 c3 : Sys A) : c1 ≡ c2 -> c2 ≡ c3 -> c1 ≡ c3.
Proof. intros H1 H2 i m o; split; intro H; [apply H2, H1 | apply H1, H2]; exact H. Qed.

(** A small solver: [bind] unfolds to nested existentials, conjunctions and
    disjunctions over [outcome] equalities, so destructing them and
    substituting the [Ok]/[Unmodeled] equations discharges most goals. *)
Ltac sys_destruct :=
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : exists _, _ |- _ => destruct H
  | H : _ \/ _ |- _ => destruct H
  | H : Ok _ _ _ = Ok _ _ _ |- _ => inversion H; clear H; subst
  | H : Ok _ _ _ = Unmodeled |- _ => discriminate H
  | H : Unmodeled = Ok _ _ _ |- _ => discriminate H
  end.

(** Left identity: [pure] is a left unit for [bind]. *)
Lemma bind_pure_l {A B} (a : A) (k : A -> Sys B) : bind (pure a) k ≡ k a.
Proof.
  intros i m o; unfold bind, pure; destruct o as [x m' evs | ]; split.
  - (* -> *) intros H; sys_destruct; rewrite app_nil_l; assumption.
  - (* <- *) intros H; exists a, m, [], evs; rewrite app_nil_l; auto.
  - (* -> *) intros H; sys_destruct; assumption.
  - (* <- *) intros H; right; exists a, m, []; auto.
Qed.

(** Right identity: [pure] is a right unit for [bind]. *)
Lemma bind_pure_r {A} (c : Sys A) : bind c pure ≡ c.
Proof.
  intros i m o; unfold bind, pure; destruct o as [x m' evs | ]; split.
  - (* -> *) intros H; sys_destruct; rewrite app_nil_r; assumption.
  - (* <- *) intros H; exists x, m', evs, []; rewrite app_nil_r; auto.
  - (* -> *) intros H; sys_destruct; assumption.
  - (* <- *) intros H; left; assumption.
Qed.

(** Associativity of [bind].  Both sides run [c], then [k], then [h];
    they differ only in how the three event lists are parenthesized, so the
    proof is a pile of existentials closed by [app_assoc]. *)
Lemma bind_assoc {A B C} (c : Sys A) (k : A -> Sys B) (h : B -> Sys C) :
  bind (bind c k) h ≡ bind c (fun x => bind (k x) h).
Proof.
  intros i m o; unfold bind; destruct o as [z m3 evs | ]; cbn; split.
  - (* Ok, -> *)
    intros (y & m2 & evsA & evsB & (x & m1 & evs1 & evs2 & Hc & Hk & HevsA)
            & Hh & Hevs); subst evsA evs.
    exists x, m1, evs1, (evs2 ++ evsB); rewrite app_assoc.
    split; [ exact Hc | split; [ exists y, m2, evs2, evsB; auto | reflexivity ] ].
  - (* Ok, <- *)
    intros (x & m1 & evs1 & evsBC & Hc
            & (y & m2 & evs2 & evsB & Hk & Hh & HevsBC) & Hevs); subst evsBC evs.
    exists y, m2, (evs1 ++ evs2), evsB; rewrite app_assoc.
    split; [ exists x, m1, evs1, evs2; auto | split; [ exact Hh | reflexivity ] ].
  - (* Unmodeled, -> *)
    intros [[Hc | (x & m1 & evs1 & Hc & Hk)]
           | (y & m2 & evsA & (x & m1 & evs1 & evs2 & Hc & Hk & _) & Hh)].
    + left; exact Hc.
    + right; exists x, m1, evs1; split; [ exact Hc | left; exact Hk ].
    + right; exists x, m1, evs1; split;
        [ exact Hc | right; exists y, m2, evs2; split; [ exact Hk | exact Hh ] ].
  - (* Unmodeled, <- *)
    intros [Hc | (x & m1 & evs1 & Hc
                  & [Hk | (y & m2 & evs2 & Hk & Hh)])].
    + left; left; exact Hc.
    + left; right; exists x, m1, evs1; split; [ exact Hc | exact Hk ].
    + right; exists y, m2, (evs1 ++ evs2); split;
        [ exists x, m1, evs1, evs2; auto | exact Hh ].
Qed.

(* =========================================================================
   Core effects
   ========================================================================= *)

(** The outcome that says THE MODEL DOES NOT COVER THIS CALL (fail closed).

    NOT a kernel failure.  A syscall that fails on real Linux — [-ENOENT],
    [-EBADF], a short read — is an ordinary [Ok] carrying the negative
    errno, because a real process observes exactly that and runs on.  The
    program leaves the modeled surface only via [unmodeled], and that is
    what [Run.unmodeled_at] reads and [Equivalence.modeled] forbids of a
    source binary.  Keeping the two apart is the whole point of the name:
    a name like [error]/[Err] would read like the former and mean the
    latter. *)
Definition unmodeled {A} : Sys A := fun _ _ o => o = Unmodeled.

(** Environment choice: any [x] satisfying [P] may be returned. *)
Definition choose {A} (P : A -> Prop) : Sys A :=
  fun _ m o => exists x, P x /\ o = Ok x m [].

(** Union of two admissible-outcome sets. *)
Definition alt {A} (c1 c2 : Sys A) : Sys A :=
  fun i m o => c1 i m o \/ c2 i m o.

(** Emit observable events. *)
Definition emit (evs : list event) : Sys unit := fun _ m o => o = Ok tt m evs.

(* =========================================================================
   Readers (the syscall input) and state accessors (the model)
   ========================================================================= *)

Definition input : Sys SyscallInput := fun i m o => o = Ok i m [].
Definition sysno : Sys word := fun i m o => o = Ok (in_sysno i) m [].
Definition arg (k : nat) : Sys word := fun i m o => o = Ok (in_arg i k) m [].

Definition get_model : Sys Model := fun _ m o => o = Ok m m [].
Definition modify (f : Model -> Model) : Sys unit := fun _ m o => o = Ok tt (f m) [].

(** Reading the model is pure: a [get_model] at the head of a chain
    binds the model the chain starts in and changes nothing, so the
    whole chain is the continuation at that model.  Written as an [iff]
    at a fixed outcome rather than as [≡] because that is the shape the
    callers want: a spec that reads the model to decide a branch is
    proved about by rewriting this once and then reasoning about the
    branch. *)
Lemma bind_get_model {A} (k : Model -> Sys A) : forall i m o,
  bind get_model k i m o <-> k m i m o.
Proof.
  intros i m o. unfold bind, get_model. destruct o as [x m2 evs|]; split.
  - intros (x0 & m1 & evs1 & evs2 & H1 & H2 & H3).
    injection H1 as -> -> ->. cbn in H3. subst evs. exact H2.
  - intros H. exists m, m, [], evs. split; [reflexivity|].
    split; [exact H | reflexivity].
  - intros [H | (x0 & m1 & evs1 & H1 & H2)]; [discriminate|].
    injection H1 as -> -> ->. exact H2.
  - intros H. right. exists m, m, []. split; [reflexivity | exact H].
Qed.


Definition get_fds  : Sys (list (word * FdEntry)) := fun _ m o => o = Ok (m_fds m) m [].
Definition get_vmmaps : Sys VmMaps := fun _ m o => o = Ok (m_vmmaps m) m [].

Definition set_fds  (fds : list (word * FdEntry)) : Sys unit := modify (with_fds fds).
Definition set_pipes (ps : list (word * PipeBuf)) : Sys unit := modify (with_pipes ps).
Definition set_vmmaps (h : VmMaps) : Sys unit := modify (with_vmmaps h).
Definition add_vm_lazy (a n : word) : Sys unit := modify (vm_add_lazy a n).
Definition forget_vm_range (lo hi : Z) : Sys unit :=
  modify (vm_forget_range lo hi).
Definition set_stdin (s : InputStream) : Sys unit := modify (with_stdin s).
Definition set_urandom (s : InputStream) : Sys unit := modify (with_urandom s).
Definition set_fs   (fs : Fs.Fs) : Sys unit := modify (with_fs fs).
Definition set_halted (code : word) : Sys unit := modify (with_halted code).
Definition set_tid (tid : word) : Sys unit := modify (with_tid tid).
Definition set_creds (c : Creds) : Sys unit := modify (with_creds c).

Definition set_rlimit_core (bs : list byte) : Sys unit :=
  modify (with_rlimit_core bs).

(** Record the UTS name the environment revealed.  Called on exactly one
    branch of [Kernel.Sys.uname_spec] -- the one where
    [State.m_utsname] was [None] -- so the pin is written once; see
    [State.with_utsname]. *)
Definition set_utsname (bs : list byte) : Sys unit :=
  modify (with_utsname bs).
Definition set_setsid_succeeded : Sys unit := modify with_setsid_succeeded.
(** Install the parent-death signal: [Kernel.Sys.prctl_spec]'s
    [PR_SET_PDEATHSIG] arm is the caller.  See [State.with_pdeath_signal]. *)
Definition set_pdeath_signal (s : word) : Sys unit := modify (with_pdeath_signal s).
(** Record the [struct stat] a file was first seen with.  Called on
    exactly one branch of [Sys.Fs.Stat.fstat_spec] -- the one where
    [State.statpin_lookup] was [None] -- so a path's pin is written
    once; see [State.procst_statpins]. *)
Definition set_statpin (p : Fs.path) (bs : list byte) : Sys unit :=
  modify (with_statpin p bs).


Definition set_sigmask (sm : word) : Sys unit := modify (with_sigmask sm).

Definition set_sigaltstack_installed : Sys unit :=
  modify with_sigaltstack_installed.

(** Record a BLOCKED SIGABRT as pending, and end the process by a fatal
    signal.  [Kernel.Signal] holds the only callers of either; see
    [State.with_sigabrt_pending] and [State.with_killed] for what each
    writes and why. *)
Definition set_sigabrt_pending : Sys unit := modify with_sigabrt_pending.
Definition set_killed (sig : word) : Sys unit := modify (with_killed sig).


Definition set_clock (t : word) : Sys unit := modify (with_clock t).

(* =========================================================================
   Introduction lemmas — building admissible outcomes compositionally.
   Used by the receptiveness proof (Progress.v), the checker verification
   (ExecutableSpecs.v), and target equivalence proofs.
   ========================================================================= *)

Lemma bind_ok {A B} : forall (c : Sys A) (k : A -> Sys B) i m x m1 evs1 y m2 evs2,
  c i m (Ok x m1 evs1) ->
  k x i m1 (Ok y m2 evs2) ->
  bind c k i m (Ok y m2 (evs1 ++ evs2)).
Proof. intros; cbn; eauto 8. Qed.

Lemma bind_unmodeled1 {A B} : forall (c : Sys A) (k : A -> Sys B) i m,
  c i m Unmodeled -> bind c k i m Unmodeled.
Proof. intros; cbn; auto. Qed.

Lemma bind_unmodeled2 {A B} : forall (c : Sys A) (k : A -> Sys B) i m x m1 evs1,
  c i m (Ok x m1 evs1) -> k x i m1 Unmodeled -> bind c k i m Unmodeled.
Proof. intros; cbn; eauto 8. Qed.

Lemma pure_ok {A} : forall (x : A) i m, pure x i m (Ok x m []).
Proof. reflexivity. Qed.

Lemma choose_ok {A} : forall (P : A -> Prop) x i m, P x -> choose P i m (Ok x m []).
Proof. intros; exists x; auto. Qed.

Lemma unmodeled_intro {A} : forall i m, (@unmodeled A) i m Unmodeled.
Proof. reflexivity. Qed.

Lemma alt_l {A} : forall (c1 c2 : Sys A) i m o, c1 i m o -> alt c1 c2 i m o.
Proof. intros; left; auto. Qed.

Lemma alt_r {A} : forall (c1 c2 : Sys A) i m o, c2 i m o -> alt c1 c2 i m o.
Proof. intros; right; auto. Qed.

Lemma emit_ok : forall evs i m, emit evs i m (Ok tt m evs).
Proof. reflexivity. Qed.

Lemma input_ok : forall i m, input i m (Ok i m []).
Proof. reflexivity. Qed.

Lemma sysno_ok : forall i m, sysno i m (Ok (in_sysno i) m []).
Proof. reflexivity. Qed.

Lemma arg_ok : forall k i m, arg k i m (Ok (in_arg i k) m []).
Proof. reflexivity. Qed.

Lemma get_model_ok : forall i m, get_model i m (Ok m m []).
Proof. reflexivity. Qed.

Lemma get_fds_ok : forall i m, get_fds i m (Ok (m_fds m) m []).
Proof. reflexivity. Qed.

Lemma get_vmmaps_ok : forall i m, get_vmmaps i m (Ok (m_vmmaps m) m []).
Proof. reflexivity. Qed.

Lemma modify_ok : forall f i m, modify f i m (Ok tt (f m) []).
Proof. reflexivity. Qed.

Create HintDb sys discriminated.
#[export] Hint Resolve bind_ok bind_unmodeled1 bind_unmodeled2 pure_ok choose_ok unmodeled_intro
  emit_ok input_ok sysno_ok arg_ok get_model_ok get_fds_ok get_vmmaps_ok
  modify_ok : sys.
