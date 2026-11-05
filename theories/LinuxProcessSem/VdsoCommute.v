(** * LinuxProcessSem.VdsoCommute — the vDSO draw is a frame of the syscall layer

    [State.with_vdso] installs the launch's vDSO draw and its call count.
    NOTHING in the syscall layer reads either: the only reader in the whole
    development is [Run.vdso_post], which is the vDSO arm of the step relation
    and not a syscall specification.  So every [Specs.syscall_spec] outcome
    survives the wrapper, with the wrapper carried through to the outcome's
    model.

    That fact is not statable once and for all.  [Monad.Sys A] is
    [SyscallInput -> Model -> outcome A -> Prop]: a shallow RELATIONAL monad,
    not a term that a generic frame lemma could quantify over.  So the work is
    a walk: this file is the walker and its combinators, [VdsoCommuteArms.v]
    is one lemma per specification in [Sys.SyscallTable.spec_table], and
    [VdsoCommuteSys.v] assembles them into [syscall_spec_vdso_commutes] and
    lifts the result to [Run.sstep] and [Run.star].

    ONE DIRECTION IS PROVED, and the converse is free.  [with_vdso] is an
    equivalence on models — [with_vdso_same] and [with_vdso_idem] below — so
    [vdso_commutes_iff] turns the forward walk into an [iff] without a second
    pass over the table.  (A budget-style walk, where the two directions are
    genuinely different, has to carry a direction parameter and prove each arm
    twice.)

    PURE ADDITION: this file changes no existing statement. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs Vdso State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(* =========================================================================
   The wrapper on models, and on outcomes
   ========================================================================= *)

(** Carry the wrapper through an outcome.  [Unmodeled] carries no model, so
    it is its own image — which is the whole reason the fail-closed branch
    costs nothing in this walk. *)
Definition outcome_with_vdso {A} (v : VdsoRun) (o : outcome A) : outcome A :=
  match o with
  | Ok x m evs => Ok x (with_vdso v m) evs
  | Unmodeled  => Unmodeled
  end.

Lemma outcome_with_vdso_Ok {A} : forall v (x : A) m evs,
  outcome_with_vdso v (Ok x m evs) = Ok x (with_vdso v m) evs.
Proof. reflexivity. Qed.

Lemma outcome_with_vdso_Unmodeled {A} : forall v,
  outcome_with_vdso v (@Unmodeled A) = Unmodeled.
Proof. reflexivity. Qed.

(** A specification neither reads nor writes the vDSO draw: installing one
    before the call is the same as installing it after. *)
Definition vdso_commutes {A} (c : Sys A) : Prop :=
  forall v i m o, c i m o -> c i (with_vdso v m) (outcome_with_vdso v o).

(* =========================================================================
   [with_vdso] is an equivalence on models

   These two give the converse direction of every statement in this
   development for free.
   ========================================================================= *)

(** Installing the draw a model already carries changes nothing.  [Model]
    and [VmState] are ordinary records, so Rocq gives no definitional eta
    and this needs the two [destruct]s; it is proved ONCE here and is what
    makes every converse direction below free. *)
Lemma with_vdso_same : forall m, with_vdso (m_vdso m) m = m.
Proof. intros [fd vm io fs pr lim tm]; destruct vm; reflexivity. Qed.

(** The second install wins. *)
Lemma with_vdso_idem : forall v w m,
  with_vdso v (with_vdso w m) = with_vdso v m.
Proof. reflexivity. Qed.

Lemma m_vdso_with_vdso_eq : forall v m, m_vdso (with_vdso v m) = v.
Proof. reflexivity. Qed.

Lemma outcome_with_vdso_idem {A} : forall v w (o : outcome A),
  outcome_with_vdso v (outcome_with_vdso w o) = outcome_with_vdso v o.
Proof. intros v w [x m evs|]; cbn; [rewrite with_vdso_idem|]; reflexivity. Qed.

(** THE INVERSE DIRECTION, for free: an outcome of the WRAPPED model is an
    outcome of the bare one, with the bare model's own draw put back.

    The draw has to be put back, and this is the one place where saying so
    matters.  [vdso_commutes] does NOT say that a specification leaves the
    draw where it found it — that would be a second walk over the table —
    so the outcome this returns carries [m]'s draw rather than whatever the
    wrapped run's outcome carried.  That is enough for every consumer,
    because [with_vdso_same] turns it back into the outcome itself whenever
    the outcome's model already carries [m]'s draw. *)
Lemma vdso_commutes_inv {A} : forall (c : Sys A), vdso_commutes c ->
  forall v i m o, c i (with_vdso v m) o ->
  c i m (outcome_with_vdso (m_vdso m) o).
Proof.
  intros c Hc v i m o H.
  pose proof (Hc (m_vdso m) i (with_vdso v m) o H) as H'.
  rewrite with_vdso_idem, with_vdso_same in H'. exact H'.
Qed.

(** The two directions as one equivalence. *)
Lemma vdso_commutes_iff {A} : forall (c : Sys A), vdso_commutes c ->
  forall v i m o,
  c i (with_vdso v m) (outcome_with_vdso v o)
  <-> c i m (outcome_with_vdso (m_vdso m) o).
Proof.
  intros c Hc v i m o. split; intros H.
  - pose proof (vdso_commutes_inv c Hc v i m _ H) as H'.
    rewrite outcome_with_vdso_idem in H'. exact H'.
  - pose proof (Hc v i m _ H) as H'.
    rewrite outcome_with_vdso_idem in H'. exact H'.
Qed.

(** The shape a consumer usually has: an outcome whose model carries the
    starting model's draw, which is every outcome a specification produces.
    Here the equivalence is the naive one. *)
Lemma vdso_commutes_iff_ok {A} : forall (c : Sys A), vdso_commutes c ->
  forall v i m (x : A) m' evs, m_vdso m' = m_vdso m ->
  (c i (with_vdso v m) (Ok x (with_vdso v m') evs) <-> c i m (Ok x m' evs)).
Proof.
  intros c Hc v i m x m' evs Hv.
  pose proof (vdso_commutes_iff c Hc v i m (Ok x m' evs)) as H.
  cbn in H. rewrite <- Hv in H. rewrite with_vdso_same in H. exact H.
Qed.

(* =========================================================================
   The setter frame

   Every [State.with_*] setter rebuilds the model from its projections, and
   the projections of [with_vdso v m] are those of [m] except the draw.  So
   each setter commutes with [with_vdso] by [reflexivity], and the collection
   is a rewrite database the walker's leaves use.  [with_vdso] and
   [with_vdso_bump] are not here: they are the thing being framed.
   ========================================================================= *)

Lemma with_fds_with_vdso : forall fds v m,
  with_fds fds (with_vdso v m) = with_vdso v (with_fds fds m).
Proof. reflexivity. Qed.

Lemma with_pipes_with_vdso : forall ps v m,
  with_pipes ps (with_vdso v m) = with_vdso v (with_pipes ps m).
Proof. reflexivity. Qed.

Lemma with_vmmaps_with_vdso : forall h v m,
  with_vmmaps h (with_vdso v m) = with_vdso v (with_vmmaps h m).
Proof. reflexivity. Qed.

Lemma with_vm_backing_with_vdso : forall lazy mat v m,
  with_vm_backing lazy mat (with_vdso v m)
  = with_vdso v (with_vm_backing lazy mat m).
Proof. reflexivity. Qed.

Lemma with_kernel_with_vdso : forall kb v m,
  with_kernel kb (with_vdso v m) = with_vdso v (with_kernel kb m).
Proof. reflexivity. Qed.

Lemma with_stdin_with_vdso : forall s v m,
  with_stdin s (with_vdso v m) = with_vdso v (with_stdin s m).
Proof. reflexivity. Qed.

Lemma with_urandom_with_vdso : forall s v m,
  with_urandom s (with_vdso v m) = with_vdso v (with_urandom s m).
Proof. reflexivity. Qed.

Lemma with_net_with_vdso : forall q v m,
  with_net q (with_vdso v m) = with_vdso v (with_net q m).
Proof. reflexivity. Qed.

Lemma with_fs_with_vdso : forall fs v m,
  with_fs fs (with_vdso v m) = with_vdso v (with_fs fs m).
Proof. reflexivity. Qed.

Lemma with_halted_with_vdso : forall code v m,
  with_halted code (with_vdso v m) = with_vdso v (with_halted code m).
Proof. reflexivity. Qed.

Lemma with_tid_with_vdso : forall tid v m,
  with_tid tid (with_vdso v m) = with_vdso v (with_tid tid m).
Proof. reflexivity. Qed.

Lemma with_rlimit_core_with_vdso : forall bs v m,
  with_rlimit_core bs (with_vdso v m) = with_vdso v (with_rlimit_core bs m).
Proof. reflexivity. Qed.

Lemma with_utsname_with_vdso : forall bs v m,
  with_utsname bs (with_vdso v m) = with_vdso v (with_utsname bs m).
Proof. reflexivity. Qed.

Lemma with_statpin_with_vdso : forall p bs v m,
  with_statpin p bs (with_vdso v m) = with_vdso v (with_statpin p bs m).
Proof. reflexivity. Qed.

Lemma with_abort_terminal_with_vdso : forall b v m,
  with_abort_terminal b (with_vdso v m) = with_vdso v (with_abort_terminal b m).
Proof. reflexivity. Qed.

Lemma with_nofile_with_vdso : forall n v m,
  with_nofile n (with_vdso v m) = with_vdso v (with_nofile n m).
Proof. reflexivity. Qed.

Lemma with_creds_with_vdso : forall c v m,
  with_creds c (with_vdso v m) = with_vdso v (with_creds c m).
Proof. reflexivity. Qed.

Lemma with_setsid_succeeded_with_vdso : forall v m,
  with_setsid_succeeded (with_vdso v m) = with_vdso v (with_setsid_succeeded m).
Proof. reflexivity. Qed.

Lemma with_children_with_vdso : forall v m,
  with_children (with_vdso v m) = with_vdso v (with_children m).
Proof. reflexivity. Qed.

Lemma with_sigmask_with_vdso : forall s v m,
  with_sigmask s (with_vdso v m) = with_vdso v (with_sigmask s m).
Proof. reflexivity. Qed.

Lemma with_sigaltstack_installed_with_vdso : forall v m,
  with_sigaltstack_installed (with_vdso v m)
  = with_vdso v (with_sigaltstack_installed m).
Proof. reflexivity. Qed.

Lemma with_sigabrt_pending_with_vdso : forall v m,
  with_sigabrt_pending (with_vdso v m) = with_vdso v (with_sigabrt_pending m).
Proof. reflexivity. Qed.

Lemma with_sigpipe_pending_with_vdso : forall v m,
  with_sigpipe_pending (with_vdso v m) = with_vdso v (with_sigpipe_pending m).
Proof. reflexivity. Qed.

Lemma with_channel_reader_with_vdso : forall b v m,
  with_channel_reader b (with_vdso v m) = with_vdso v (with_channel_reader b m).
Proof. reflexivity. Qed.

Lemma with_sigpipe_default_with_vdso : forall dfl v m,
  with_sigpipe_default dfl (with_vdso v m)
  = with_vdso v (with_sigpipe_default dfl m).
Proof. reflexivity. Qed.

Lemma with_sigpipe_terminal_with_vdso : forall b v m,
  with_sigpipe_terminal b (with_vdso v m)
  = with_vdso v (with_sigpipe_terminal b m).
Proof. reflexivity. Qed.

Lemma with_sigpipe_install_with_vdso : forall a v m,
  with_sigpipe_install a (with_vdso v m) = with_vdso v (with_sigpipe_install a m).
Proof. reflexivity. Qed.

Lemma with_killed_with_vdso : forall sig v m,
  with_killed sig (with_vdso v m) = with_vdso v (with_killed sig m).
Proof. reflexivity. Qed.

Lemma with_clock_with_vdso : forall t v m,
  with_clock t (with_vdso v m) = with_vdso v (with_clock t m).
Proof. reflexivity. Qed.

Lemma with_accepted_with_vdso : forall fds v m,
  with_accepted fds (with_vdso v m) = with_vdso v (with_accepted fds m).
Proof. reflexivity. Qed.

(** The two VM updates [Monad.add_vm_lazy] and [Monad.forget_vm_range] pass
    through [with_vm_backing], so they commute for the same reason. *)
Lemma vm_add_lazy_with_vdso : forall a n v m,
  vm_add_lazy a n (with_vdso v m) = with_vdso v (vm_add_lazy a n m).
Proof. reflexivity. Qed.

Lemma vm_forget_range_with_vdso : forall lo hi v m,
  vm_forget_range lo hi (with_vdso v m) = with_vdso v (vm_forget_range lo hi m).
Proof. reflexivity. Qed.

(** No rewrite database is declared over these.  The walker does not need
    one: every side condition it raises is closed by [reflexivity], which is
    the same conversion each lemma above records.  They are stated for the
    consumer, and because a setter that stopped commuting would fail HERE,
    in one line, rather than inside a walk of the table. *)

(* =========================================================================
   The combinators

   [vdso_commutes] is closed under every combinator a specification is built
   from, so a specification whose body is combinators alone needs no walk of
   its own.
   ========================================================================= *)

Lemma vc_pure {A} : forall (x : A), vdso_commutes (pure x).
Proof. intros x v i m o H. unfold pure in *. subst o. reflexivity. Qed.

Lemma vc_unmodeled {A} : vdso_commutes (@unmodeled A).
Proof. intros v i m o H. unfold unmodeled in *. subst o. reflexivity. Qed.

Lemma vc_choose {A} : forall (P : A -> Prop), vdso_commutes (choose P).
Proof.
  intros P v i m o (x & HP & ->). exists x. split; [exact HP | reflexivity].
Qed.

Lemma vc_emit : forall evs, vdso_commutes (emit evs).
Proof. intros evs v i m o H. unfold emit in *. subst o. reflexivity. Qed.

Lemma vc_input : vdso_commutes input.
Proof. intros v i m o H. unfold input in *. subst o. reflexivity. Qed.

Lemma vc_sysno : vdso_commutes sysno.
Proof. intros v i m o H. unfold sysno in *. subst o. reflexivity. Qed.

Lemma vc_arg : forall k, vdso_commutes (arg k).
Proof. intros k v i m o H. unfold arg in *. subst o. reflexivity. Qed.

Lemma vc_alt {A} : forall (c1 c2 : Sys A),
  vdso_commutes c1 -> vdso_commutes c2 -> vdso_commutes (alt c1 c2).
Proof.
  intros c1 c2 H1 H2 v i m o [H | H]; [left; apply H1 | right; apply H2]; exact H.
Qed.

(** Sequencing.  The intermediate model is wrapped too, which is what makes
    the walk go through a chain of any length. *)
Lemma vc_bind {A B} : forall (c : Sys A) (k : A -> Sys B),
  vdso_commutes c -> (forall x, vdso_commutes (k x)) ->
  vdso_commutes (bind c k).
Proof.
  intros c k Hc Hk v i m o H. destruct o as [y m2 evs|]; cbn in *.
  - destruct H as (x & m1 & evs1 & evs2 & Hc' & Hk' & ->).
    exists x, (with_vdso v m1), evs1, evs2.
    split; [exact (Hc v i m _ Hc')|].
    split; [exact (Hk x v i m1 _ Hk') | reflexivity].
  - destruct H as [H | (x & m1 & evs1 & Hc' & Hk')].
    + left. exact (Hc v i m Unmodeled H).
    + right. exists x, (with_vdso v m1), evs1.
      split; [exact (Hc v i m _ Hc') | exact (Hk x v i m1 Unmodeled Hk')].
Qed.

(** Writing a field.  The side condition is the setter frame above, so every
    [Monad.set_*] discharges it from [vdso_frame]. *)
Lemma vc_modify : forall (f : Model -> Model),
  (forall v m, f (with_vdso v m) = with_vdso v (f m)) ->
  vdso_commutes (modify f).
Proof.
  intros f Hf v i m o H. unfold modify in *. subst o. cbn. rewrite Hf. reflexivity.
Qed.

(** READING the model is the one combinator that is not closed on its own.
    [get_model] hands the continuation the model it is called at, so under
    the wrapper it hands it the WRAPPED model — a different VALUE, which is
    not what [outcome_with_vdso] maps.  What rescues it is that no
    continuation can tell the difference: a continuation reads fields, and
    [with_vdso] changes none of them but the draw, so [k (with_vdso v m)] and
    [k m] are convertible.  That is the first premise, and every caller
    discharges it by [reflexivity]. *)
Lemma vc_bind_get_model {A} : forall (k : Model -> Sys A),
  (forall v m, k (with_vdso v m) = k m) ->
  (forall m, vdso_commutes (k m)) ->
  vdso_commutes (bind get_model k).
Proof.
  intros k Heq Hk v i m o H.
  apply bind_get_model in H. apply bind_get_model.
  rewrite Heq. apply Hk. exact H.
Qed.

(** The two narrow readers ARE closed, because the value they hand over is a
    field, and a field of the wrapper is the field itself. *)
Lemma vc_get_fds : vdso_commutes get_fds.
Proof. intros v i m o H. unfold get_fds in *. subst o. reflexivity. Qed.

Lemma vc_get_vmmaps : vdso_commutes get_vmmaps.
Proof. intros v i m o H. unfold get_vmmaps in *. subst o. reflexivity. Qed.

(** [input], [sysno] and [arg] read the SyscallInput, which the wrapper does
    not touch, so their binds are closed outright. *)
Lemma vc_bind_input {A} : forall (k : SyscallInput -> Sys A),
  (forall x, vdso_commutes (k x)) -> vdso_commutes (bind input k).
Proof. intros k Hk. apply vc_bind; [apply vc_input | exact Hk]. Qed.

Lemma vc_bind_arg {A} : forall n (k : word -> Sys A),
  (forall x, vdso_commutes (k x)) -> vdso_commutes (bind (arg n) k).
Proof. intros n k Hk. apply vc_bind; [apply vc_arg | exact Hk]. Qed.

(* =========================================================================
   The [Sys/Syscall.v] layer
   ========================================================================= *)

Lemma vc_ret_only : forall r, vdso_commutes (ret_only r).
Proof. intros r. apply vc_pure. Qed.

Lemma vc_err_ret : forall e, vdso_commutes (err_ret e).
Proof. intros e. apply vc_ret_only. Qed.

Lemma vc_errno_from : forall es, vdso_commutes (errno_from es).
Proof. intros es. apply vc_choose. Qed.

Lemma vc_record_copyins : forall reads spec,
  vdso_commutes spec -> vdso_commutes (record_copyins reads spec).
Proof.
  intros reads spec Hs. unfold record_copyins.
  apply vc_bind; [exact Hs | intros eff; apply vc_pure].
Qed.

(* =========================================================================
   The walker

   [vdso_walk] closes a specification whose body is the combinators above,
   matches on its arguments and matches on the model's fields.  Three facts
   do all the work and each is a [reflexivity]:

   - a [State.with_*] setter commutes with the wrapper, which closes
     [vc_modify]'s side condition;
   - a field reader applied to the wrapper is the reader applied to the
     model, which closes [vc_bind_get_model]'s first premise, so a match on
     a field selects the same branch on both sides;
   - the wrapper does not touch the [SyscallInput], so the argument readers
     are closed outright.

   A specification the walker does not close is not a counterexample to any
   of the three: it is a body whose shape the [match] below does not name.
   Add the shape rather than proving the arm by hand.
   ========================================================================= *)

(** One step of the walk: peel a combinator, or split a branch. *)
Ltac vdso_step :=
  match goal with
  | |- vdso_commutes (bind get_model _) =>
      apply vc_bind_get_model; [intros; reflexivity | intros]
  | |- vdso_commutes (bind _ _) => apply vc_bind; [| intros]
  | |- vdso_commutes (alt _ _) => apply vc_alt
  | |- vdso_commutes (record_copyins _ _) => apply vc_record_copyins
  | |- vdso_commutes (pure _) => apply vc_pure
  | |- vdso_commutes (ret_only _) => apply vc_ret_only
  | |- vdso_commutes (err_ret _) => apply vc_err_ret
  | |- vdso_commutes (errno_from _) => apply vc_errno_from
  | |- vdso_commutes (choose _) => apply vc_choose
  | |- vdso_commutes (emit _) => apply vc_emit
  | |- vdso_commutes (@unmodeled _) => apply vc_unmodeled
  | |- vdso_commutes input => apply vc_input
  | |- vdso_commutes sysno => apply vc_sysno
  | |- vdso_commutes (arg _) => apply vc_arg
  | |- vdso_commutes get_fds => apply vc_get_fds
  | |- vdso_commutes get_vmmaps => apply vc_get_vmmaps
  | |- vdso_commutes (modify _) => apply vc_modify; intros; reflexivity
  | |- vdso_commutes (if ?b then _ else _) => destruct b
  | |- vdso_commutes (match ?x with _ => _ end) => destruct x
  | |- vdso_commutes (let _ := ?x in _) => destruct x
  end.

(** The walk.  [unfold] the specification first; [vdso_walk] takes it from
    there. *)
Ltac vdso_walk := intros; repeat (cbn beta zeta iota; vdso_step).
