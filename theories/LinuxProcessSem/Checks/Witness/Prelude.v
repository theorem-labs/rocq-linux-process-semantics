(** * LinuxProcessSem.Checks.Witness.Prelude — the witnesses' shared helpers and tactics

    Shared infrastructure for the witnesses below it: this one mirrors
    no kernel source, and holds nothing syscall-specific.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from.

    Ported in part from theorem-labs/linux-process-semantics
    r22/namespace-core at 6ff3d045 (issue #1011). *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.

(** Rewrite a scrutinee equation, then iota-reduce the match/if it
    unblocks. *)
Ltac srw H := rewrite H; cbv beta iota zeta.

(** A bind step whose first component contributes no events (it may still
    update the model), propagating EITHER outcome shape of the
    continuation.  Every step in the witnesses below is of this form
    except [emit], which gets its own lemma. *)

Lemma bind_step {A B} : forall (c : Sys A) (k : A -> Sys B) i m x m1 o,
  c i m (Ok x m1 []) -> k x i m1 o -> bind c k i m o.
Proof.
  intros c k i m x m1 o Hc Hk. destruct o as [y m2 evs|].
  - replace evs with ([] ++ evs) by reflexivity. eapply bind_ok; eauto.
  - eapply bind_unmodeled2; eauto.
Qed.

(** [emit] followed by [pure]: the whole program's events are exactly the
    emitted ones. *)

Lemma emit_pure_ok {A} : forall evs (x : A) i m,
  (emit evs ;; pure x) i m (Ok x m evs).
Proof.
  intros. unfold bind; cbv iota. exists tt, m, evs, [].
  rewrite app_nil_r. auto using emit_ok, pure_ok.
Qed.

(** Every injectable-errno set is inhabited, so the failure branch is
    always available: the head of the list is a member.  ENOMEM heads
    [openat_errnos], [mmap_errnos], [mprotect_errnos] and [dup_errnos];
    [getrandom_errnos] is headed by EINTR. *)

Lemma errno_from_witness : forall es e i m,
  In e es -> errno_from es i m (Ok e m []).
Proof. intros. apply choose_ok. assumption. Qed.

Lemma errno_head_witness : forall e es i m,
  errno_from (e :: es) i m (Ok e m []).
Proof. intros. apply choose_ok. left. reflexivity. Qed.

(** ENOMEM (12): the errno the openat/mmap/dup witnesses below fail
    with (it heads those sets). *)

Definition witness_errno : Z := ENOMEM.

(** Shorthand for the "return [r], change nothing, emit nothing"
    outcome. *)

Definition ret_outcome (r : word) (m : Model) : outcome SyscallEffect :=
  Ok (mkEffect r [] []) m [].

Lemma witness_bind_ok_eq {A B} :
  forall (c : Sys A) (k : A -> Sys B) i m x m1 evs1 y m2 evs2 evs,
  c i m (Ok x m1 evs1) -> k x i m1 (Ok y m2 evs2) -> evs = evs1 ++ evs2 ->
  bind c k i m (Ok y m2 evs).
Proof. intros; subst; eapply bind_ok; eauto. Qed.


(* =========================================================================
   read (63) — witness: the one-byte delivery from the input stream
   (channel; 0 at end of input), the deterministic file read (file),
   -EFAULT for a destination whose first byte cannot be written, or
   the fail-closed [Unmodeled]
   ========================================================================= *)

(** [Uaccess.access_ok_zero] as a witness: the zero answer where the model
    is sure the range passed [access_ok], -EFAULT where it is sure it did
    not, and the fail-closed decline in between. *)


(** [State.descriptor_invariant], AS A TACTIC.  That predicate says
    every [State.FdFile*] key resolves to an [Fs.EFile], so the
    [Fs.EDir] and [Fs.EDev] branches a file-content lookup now has are
    states it forbids.  It is not yet proved invariant -- see its own
    comment and [Run.valid_image] -- so what these branches are is
    FAIL CLOSED on both sides, which is what this tactic discharges.
    They are FAIL-CLOSED in the spec and in the checker alike, so the
    two sides agree there and neither admits anything.

    The alternatives below are the shapes that agreement takes: a
    contradictory hypothesis on the checker side, and the "both decline"
    obligation on the spec side, whose proof is the ABSENT case's proof
    with the same two rewrites.  It is [solve], so a branch that is NOT
    one of these fails loudly here instead of being absorbed. *)
Ltac entry_rewrites :=
  do 12 (try (match goal with
              | H : _ = _ |- _ => progress (srw H)
              end)).

Ltac entry_absurd :=
  solve [ discriminate
        | reflexivity
        | congruence
        | assumption
        | apply unmodeled_intro
        | (eapply bind_unmodeled2; [apply input_ok|]; cbv beta;
           eapply bind_unmodeled2; [apply get_model_ok|]; cbv beta iota;
           entry_rewrites; apply unmodeled_intro)
        | (eapply bind_step; [apply input_ok|]; cbv beta;
           eapply bind_step; [apply get_model_ok|]; cbv beta iota zeta;
           entry_rewrites; apply unmodeled_intro)
        | (eapply bind_step; [apply get_model_ok|]; cbv beta iota zeta;
           entry_rewrites; apply unmodeled_intro) ].
