(** * Riscv.CheckedBv — the checked bitvector constructor both extraction
      boundaries are built on

    TRUST BOUNDARY: this file is part of the trusted specification.

    WHY IT EXISTS.  This tree extracts two artifacts to OCaml: the
    verified syscall checker ([LinuxProcessSem/Checks/Extraction.v]) and
    the RV64GC instruction model ([Riscv/Extraction.v]).  Both hand their
    inputs to Rocq terms typed in [bv n], and stdpp's [bv n] is a record
    whose second field is the PROOF [BvWf n bv_unsigned] — a [Prop].
    Extraction erases a [Prop], so in both artifacts a bitvector is
    zarith's arbitrary-precision integer, with no width and no range:

      type bv = Big_int_Z.big_int
        (* singleton inductive, whose constructor was BV *)

    An integer that no register holds therefore reaches a Rocq term that
    its type does not contain, and no theorem in this tree says anything
    about what happens next.  Each artifact answers that with a boundary
    of its own — [Checks.CheckedInput] and [Riscv.CheckedIsa] — and this
    file is the one definition they share, so the next boundary does not
    arrive with a third spelling of the same check.

    WHAT IS HERE.  [Z_to_bv_checked] is stdpp's, and it is the whole
    mechanism: [Some b] exactly when [z = bv_unsigned b]
    ([Z_to_bv_checked_Some]), so it never wraps and never truncates.  It
    is NOT [Z_to_bv], which wraps mod 2^n and would turn a value no
    machine can produce into a different value a machine might.  Around
    it: the per-width names, the two lemmas that say what a [Some] and a
    [None] mean, and the list traversal a boundary needs to check a
    vector of values and refuse the lot if one of them fails. *)

From LinuxProcessSemantics.Riscv Require Import Prelude.
From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.

(* =========================================================================
   The primitive
   ========================================================================= *)

Definition bv_of_Z (n : N) (z : Z) : option (bv n) := Z_to_bv_checked n z.

Definition word_of_Z (z : Z) : option word := bv_of_Z 64 z.
Definition byte_of_Z (z : Z) : option (bv 8) := bv_of_Z 8 z.
Definition bv32_of_Z (z : Z) : option (bv 32) := bv_of_Z 32 z.
Definition bv16_of_Z (z : Z) : option (bv 16) := bv_of_Z 16 z.
Definition bv12_of_Z (z : Z) : option (bv 12) := bv_of_Z 12 z.
Definition reg_of_Z (z : Z) : option reg := bv_of_Z 5 z.

(** A [Some] carries the caller's own integer: nothing was wrapped,
    truncated or defaulted on the way in. *)
Lemma bv_of_Z_value : forall n z (b : bv n),
  bv_of_Z n z = Some b -> bv_unsigned b = z.
Proof.
  intros n z b H. unfold bv_of_Z in H.
  apply Z_to_bv_checked_Some in H. congruence.
Qed.

(** A [None] is exactly the out-of-range case, neither more nor less. *)
Lemma bv_of_Z_refused : forall n z,
  bv_of_Z n z = None <-> ~ (0 <= z < bv_modulus n)%Z.
Proof.
  intros n z. unfold bv_of_Z. split.
  - intros Hnone [Hlo Hhi].
    assert (BvWf n z) as Hwf by (apply bv_wf_in_range; lia).
    pose proof (Z_to_bv_checked_bv_unsigned n (@BV n z Hwf)) as H.
    rewrite bv_unsigned_BV in H. rewrite H in Hnone. discriminate.
  - intros Hout. destruct (Z_to_bv_checked n z) as [b|] eqn:E; [|reflexivity].
    apply Z_to_bv_checked_Some in E. subst z.
    exfalso. apply Hout. apply bv_unsigned_in_range.
Qed.

(** Nothing a Rocq term could have said is refused: the boundary is a
    filter on the EXTRACTED representation, not a narrowing of the
    model. *)
Lemma bv_of_Z_total : forall n (b : bv n), bv_of_Z n (bv_unsigned b) = Some b.
Proof. intros n b. apply Z_to_bv_checked_bv_unsigned. Qed.

(** The per-width shapes, by name, for the boundaries and their tests. *)
Lemma word_of_Z_refused : forall z, word_of_Z z = None <-> ~ (0 <= z < 2 ^ 64)%Z.
Proof. intros z. unfold word_of_Z. rewrite bv_of_Z_refused. reflexivity. Qed.

Lemma byte_of_Z_refused : forall z, byte_of_Z z = None <-> ~ (0 <= z < 2 ^ 8)%Z.
Proof. intros z. unfold byte_of_Z. rewrite bv_of_Z_refused. reflexivity. Qed.

Lemma word_of_Z_total : forall w : word, word_of_Z (bv_unsigned w) = Some w.
Proof. intros w. apply bv_of_Z_total. Qed.

Lemma byte_of_Z_total : forall b : bv 8, byte_of_Z (bv_unsigned b) = Some b.
Proof. intros b. apply bv_of_Z_total. Qed.

(* =========================================================================
   The other erased invariant: [N]
   ========================================================================= *)

(** [N] is realized by zarith too, and its whole well-formedness
    condition is that it is not negative — which the extracted code
    does not hold it to, exactly as it does not hold a [bv] to its
    width.  A value the MODEL holds as an [N] and a caller declares
    from outside therefore needs this on the way in, and it is here
    rather than in one boundary because both artifacts will want it:
    [Checks.CheckedInput] takes the kernel build's eight numeric
    components through it, and a root of the ISA model that took a
    width or a shift amount would take the same check.

    It is NOT [Z.to_N], which answers 0 for a negative integer and so
    would turn a value no machine can produce into a different value a
    machine might — the same reason [Z_to_bv_checked] is not
    [Z_to_bv]. *)
Definition n_of_Z (z : Z) : option N :=
  if (0 <=? z)%Z then Some (Z.to_N z) else None.

(** What a [Some] and a [None] mean, as [bv_of_Z_value] and
    [bv_of_Z_refused] say it for a bitvector.  Non-negativity is the
    whole of [N]'s invariant, so the second iff is complete. *)
Lemma n_of_Z_value : forall z n, n_of_Z z = Some n -> Z.of_N n = z.
Proof.
  intros z n H. unfold n_of_Z in H.
  destruct (0 <=? z)%Z eqn:Hle; [|discriminate].
  injection H as <-. apply Z2N.id. now apply Z.leb_le.
Qed.

Lemma n_of_Z_refused : forall z, n_of_Z z = None <-> ~ (0 <= z)%Z.
Proof.
  intros z. unfold n_of_Z. destruct (0 <=? z)%Z eqn:Hle.
  - apply Z.leb_le in Hle.
    split; [intros H; discriminate H | intros Hout; contradiction].
  - apply Z.leb_gt in Hle.
    split; [intros _; lia | intros _; reflexivity].
Qed.

(** Nothing the model can say is refused. *)
Lemma n_of_Z_total : forall n : N, n_of_Z (Z.of_N n) = Some n.
Proof.
  intros n. unfold n_of_Z.
  rewrite (proj2 (Z.leb_le 0 (Z.of_N n)) (N2Z.is_nonneg n)).
  now rewrite N2Z.id.
Qed.

(* =========================================================================
   Checking a vector of values
   ========================================================================= *)

Fixpoint mapM_opt {A B} (f : A -> option B) (l : list A) : option (list B) :=
  match l with
  | [] => Some []
  | x :: r =>
      match f x with
      | None => None
      | Some y => match mapM_opt f r with
                  | None => None
                  | Some ys => Some (y :: ys)
                  end
      end
  end.

Lemma mapM_opt_None_elem : forall {A B} (f : A -> option B) l,
  mapM_opt f l = None -> exists x, In x l /\ f x = None.
Proof.
  intros A B f l. induction l as [|x r IH]; cbn; [discriminate|].
  destruct (f x) as [y|] eqn:Hx.
  - destruct (mapM_opt f r) as [ys|] eqn:Hr; [discriminate|].
    intros _. destruct (IH eq_refl) as (z & Hin & Hz). eauto.
  - intros _. exists x. auto.
Qed.

Lemma mapM_opt_elem_None : forall {A B} (f : A -> option B) l x,
  In x l -> f x = None -> mapM_opt f l = None.
Proof.
  intros A B f l x. induction l as [|y r IH]; cbn; [contradiction|].
  intros [->|Hin] Hx.
  - rewrite Hx. reflexivity.
  - rewrite (IH Hin Hx). destruct (f y); reflexivity.
Qed.

Lemma mapM_opt_values : forall {A B} (f : A -> option B) (g : B -> A) l ys,
  (forall x y, f x = Some y -> g y = x) ->
  mapM_opt f l = Some ys -> map g ys = l.
Proof.
  intros A B f g l. induction l as [|x r IH]; cbn; intros ys Hfg H.
  - injection H as <-. reflexivity.
  - destruct (f x) as [y|] eqn:Hx; [|discriminate].
    destruct (mapM_opt f r) as [zs|] eqn:Hr; [|discriminate].
    injection H as <-. cbn. f_equal; [now apply Hfg | now apply IH].
Qed.

Lemma mapM_opt_map_total : forall {A B} (f : A -> option B) (g : B -> A) (l : list B),
  (forall b, f (g b) = Some b) -> mapM_opt f (map g l) = Some l.
Proof.
  intros A B f g l Hf. induction l as [|x r IH]; cbn; [reflexivity|].
  rewrite Hf, IH. reflexivity.
Qed.

Definition words_of_Z : list Z -> option (list word) := mapM_opt word_of_Z.
Definition bytes_of_Z : list Z -> option (list (bv 8)) := mapM_opt byte_of_Z.

Lemma words_of_Z_elem_None : forall l z,
  In z l -> word_of_Z z = None -> words_of_Z l = None.
Proof. intros l z Hin Hz. unfold words_of_Z. eapply mapM_opt_elem_None; eauto. Qed.

Lemma bytes_of_Z_elem_None : forall l z,
  In z l -> byte_of_Z z = None -> bytes_of_Z l = None.
Proof. intros l z Hin Hz. unfold bytes_of_Z. eapply mapM_opt_elem_None; eauto. Qed.

Lemma words_of_Z_total : forall l : list word,
  words_of_Z (map bv_unsigned l) = Some l.
Proof. intros l. apply (mapM_opt_map_total word_of_Z bv_unsigned l word_of_Z_total). Qed.

Lemma bytes_of_Z_total : forall l : list (bv 8),
  bytes_of_Z (map bv_unsigned l) = Some l.
Proof. intros l. apply (mapM_opt_map_total byte_of_Z bv_unsigned l byte_of_Z_total). Qed.

Lemma words_of_Z_values : forall l ws,
  words_of_Z l = Some ws -> map bv_unsigned ws = l.
Proof.
  intros l ws H. apply (mapM_opt_values word_of_Z bv_unsigned l ws); [|exact H].
  intros x y Hx. now apply bv_of_Z_value.
Qed.

Lemma bytes_of_Z_values : forall l bs,
  bytes_of_Z l = Some bs -> map bv_unsigned bs = l.
Proof.
  intros l bs H. apply (mapM_opt_values byte_of_Z bv_unsigned l bs); [|exact H].
  intros x y Hx. now apply bv_of_Z_value.
Qed.
