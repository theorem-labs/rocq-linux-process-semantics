(** * LinuxProcessSem.Checks.CheckedInput — the extracted checker's input boundary

    TRUST BOUNDARY: this file is part of the trusted specification.

    WHY IT EXISTS.  [Checks/Extraction.v] extracts the verified checker to
    OCaml.  A machine quantity is [word = bv 64] and a memory byte is
    [byte = bv 8], and stdpp's [bv n] is a record whose second field is the
    PROOF [BvWf n bv_unsigned] — a [Prop].  Extraction erases a [Prop], so
    the extracted [word] is zarith's arbitrary-precision integer and nothing
    in the extracted code holds it to [0 <= z < 2^64].  A caller that hands
    the checker an integer no 64-bit register can hold therefore gets a
    VERDICT on a value that is not in the Rocq type, and no theorem in this
    tree covers that verdict: [ExecutableSpecs]'s own header says the
    [Forall (b < 256)] conditions "are enforced by the [byte] type", which is
    true of the Rocq term and false of the extracted one.

    (The witness: theorem-labs/linux-process-semantics at ff0313ba4f,
    testing/syscall-check/traces/set_tid/022.jsonl, record [seq 1], case
    [reject --mutate set_tid_address#2:ret=2^64].  The record carries
    [effect.ret = 18446744073709551616] and the verdict [reject].  That
    repository's harness builds the value with no reduction mod 2^64 — see
    its main.ml [parse_value], the ["2^64"] arm — and its TRACE.md states
    the rule as "a word is any non-negative integer, and is not bounded at
    2^64: the checker's word type is the model's [bv], which is Z".
    A system-call return reaches the task in a0, 64 bits wide
    (arch/riscv/include/asm/syscall.h, [syscall_set_return_value], Linux
    v6.18.46, commit 1f99e9ab748f), so no kernel produces that answer.)

    WHAT IT DOES.  This file is the extracted checker's one input
    boundary.  Every entry point it offers takes the outside world's
    values as [Z] — plain integers, with no invariant to break — and
    REFUSES, before the checker runs, any integer that is not in the Rocq
    type it would have to inhabit.  A refusal is a THIRD answer
    ([CheckedRefused], and [None] from [init_model_checked]), distinct
    from every verdict: [CheckReject] says the kernel did something the
    model forbids, and a refusal says this is not a kernel observation at
    all.

    No value reaches a verdict except through [Z_to_bv_checked], which
    returns the bitvector only when the integer is in range
    ([Z_to_bv_checked_Some]).  What a [SyscallInput] and a [ProcInput]
    carry as FUNCTIONS or as INFINITE objects in the model — the readable
    memory view, the two byte streams, the network queue — is not taken
    from the caller in that shape, because what such an object would
    answer with cannot be checked before it is asked: each is taken as
    the finite data every reader already holds, checked value by value,
    and built here.  The writable memory view is the exception and says
    why at [wmem_view]: the model reads it for definedness alone, so it
    is taken as a predicate, whose [bool] result carries nothing to
    erase.

    WHAT IT DOES NOT DO.  Extraction writes a .mli beside the .ml, but it
    publishes everything the roots reach, [ExecutableSpecs.
    check_syscall_for_run], [State.init_model] and the [SyscallInput] and
    [SyscallEffect] record types included: the checked entry points reach
    them, so no choice of roots can hide them.  The guarantee this file
    carries is therefore about the SUPPORTED surface — the roots of
    [Checks/Extraction.v] — and that surface offers no way to reach a
    verdict without this boundary. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   The primitive: an integer becomes a bitvector only if it is one
   ========================================================================= *)

(** [Z_to_bv_checked] is stdpp's: [Some b] exactly when [z = bv_unsigned b]
    ([Z_to_bv_checked_Some]), so it never wraps and never truncates.  It is
    NOT [Z_to_bv], which wraps mod 2^n and would turn a value the kernel
    cannot have produced into a different value the kernel might have. *)
Definition word_of_Z (z : Z) : option word := Z_to_bv_checked 64 z.
Definition byte_of_Z (z : Z) : option byte := Z_to_bv_checked 8 z.
Definition bv32_of_Z (z : Z) : option (bv 32) := Z_to_bv_checked 32 z.
Definition bv16_of_Z (z : Z) : option (bv 16) := Z_to_bv_checked 16 z.

Lemma bv_of_Z_value : forall n z (b : bv n),
  Z_to_bv_checked n z = Some b -> bv_unsigned b = z.
Proof. intros n z b H. apply Z_to_bv_checked_Some in H. congruence. Qed.

Lemma bv_of_Z_refused : forall n z,
  Z_to_bv_checked n z = None <-> ~ (0 <= z < bv_modulus n)%Z.
Proof.
  intros n z. split.
  - intros Hnone [Hlo Hhi].
    assert (BvWf n z) as Hwf by (apply bv_wf_in_range; lia).
    pose proof (Z_to_bv_checked_bv_unsigned n (@BV n z Hwf)) as H.
    rewrite bv_unsigned_BV in H. rewrite H in Hnone. discriminate.
  - intros Hout. destruct (Z_to_bv_checked n z) as [b|] eqn:E; [|reflexivity].
    apply Z_to_bv_checked_Some in E. subst z.
    exfalso. apply Hout. apply bv_unsigned_in_range.
Qed.

(** The two shapes the tests and the theorems below use by name. *)
Lemma word_of_Z_refused : forall z,
  word_of_Z z = None <-> ~ (0 <= z < 2 ^ 64)%Z.
Proof. intros z. unfold word_of_Z. rewrite bv_of_Z_refused. reflexivity. Qed.

Lemma byte_of_Z_refused : forall z,
  byte_of_Z z = None <-> ~ (0 <= z < 2 ^ 8)%Z.
Proof. intros z. unfold byte_of_Z. rewrite bv_of_Z_refused. reflexivity. Qed.

(** Nothing a Rocq term could have said is refused: the boundary is a
    filter on the EXTRACTED representation, not a narrowing of the model. *)
Lemma word_of_Z_total : forall w : word, word_of_Z (bv_unsigned w) = Some w.
Proof. intros w. apply Z_to_bv_checked_bv_unsigned. Qed.

Lemma byte_of_Z_total : forall b : byte, byte_of_Z (bv_unsigned b) = Some b.
Proof. intros b. apply Z_to_bv_checked_bv_unsigned. Qed.

(* ------------------------------------------------------------------ lists *)

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

Definition words_of_Z : list Z -> option (list word) := mapM_opt word_of_Z.
Definition bytes_of_Z : list Z -> option (list byte) := mapM_opt byte_of_Z.

Definition pair_of_Z (p : Z * Z) : option (word * word) :=
  match word_of_Z (fst p), word_of_Z (snd p) with
  | Some a, Some b => Some (a, b)
  | _, _ => None
  end.
Definition pairs_of_Z : list (Z * Z) -> option (list (word * word)) :=
  mapM_opt pair_of_Z.

Definition run_of_Z (r : Z * list Z) : option (word * list byte) :=
  match word_of_Z (fst r), bytes_of_Z (snd r) with
  | Some a, Some bs => Some (a, bs)
  | _, _ => None
  end.
Definition runs_of_Z : list (Z * list Z) -> option (list (word * list byte)) :=
  mapM_opt run_of_Z.

Definition copy_of_Z (c : Z * Z * Z) : option MemCopy :=
  let '(s, d, l) := c in
  match word_of_Z s, word_of_Z d, word_of_Z l with
  | Some s', Some d', Some l' => Some (mkCopy s' d' l')
  | _, _, _ => None
  end.
Definition copies_of_Z : list (Z * Z * Z) -> option (list MemCopy) :=
  mapM_opt copy_of_Z.

(** A copy-in length is a [nat] in the model: its only well-formedness
    condition is that it is not negative.  The address beside it is a
    [word] and is checked as one. *)
Definition copyin_of_Z (c : Z * Z) : option (word * nat) :=
  match word_of_Z (fst c) with
  | Some a => if (0 <=? snd c)%Z then Some (a, Z.to_nat (snd c)) else None
  | None => None
  end.
Definition copyins_of_Z : list (Z * Z) -> option (list (word * nat)) :=
  mapM_opt copyin_of_Z.

(** One refused element refuses the whole list, by name for each list the
    boundary builds. *)
Lemma words_of_Z_elem_None : forall l z,
  In z l -> word_of_Z z = None -> words_of_Z l = None.
Proof. intros l z Hin Hz. unfold words_of_Z. eapply mapM_opt_elem_None; eauto. Qed.

Lemma bytes_of_Z_elem_None : forall l z,
  In z l -> byte_of_Z z = None -> bytes_of_Z l = None.
Proof. intros l z Hin Hz. unfold bytes_of_Z. eapply mapM_opt_elem_None; eauto. Qed.

Lemma pairs_of_Z_elem_None : forall l p,
  In p l -> pair_of_Z p = None -> pairs_of_Z l = None.
Proof. intros l p Hin Hp. unfold pairs_of_Z. eapply mapM_opt_elem_None; eauto. Qed.

Lemma runs_of_Z_elem_None : forall l r,
  In r l -> run_of_Z r = None -> runs_of_Z l = None.
Proof. intros l r Hin Hr. unfold runs_of_Z. eapply mapM_opt_elem_None; eauto. Qed.

Lemma copies_of_Z_elem_None : forall l c,
  In c l -> copy_of_Z c = None -> copies_of_Z l = None.
Proof. intros l c Hin Hc. unfold copies_of_Z. eapply mapM_opt_elem_None; eauto. Qed.

Lemma copyins_of_Z_elem_None : forall l c,
  In c l -> copyin_of_Z c = None -> copyins_of_Z l = None.
Proof. intros l c Hin Hc. unfold copyins_of_Z. eapply mapM_opt_elem_None; eauto. Qed.

(* =========================================================================
   The two memory views, built here from the data a reader holds
   ========================================================================= *)

(** The readable view.  A reader captures pre-syscall memory as RUNS of
    consecutive bytes (that is what a trace carries, and what a live tracer
    reads off the guest); this builds the model's [word -> option byte] from
    them, through the radix map of [Riscv.Prelude] so a lookup costs the
    width of the address and not the length of the run.

    Addresses advance with the model's own wrapping [bv] addition, which is
    what [State.read_bytes_aux] walks a buffer with.  An EARLIER run wins
    over a later one on an address they share; a reader whose runs overlap
    is describing memory twice, which only a buggy reader does. *)
Fixpoint mem_insert_bytes (base : word) (bs : list byte) (m : bvmap 64 byte)
    : bvmap 64 byte :=
  match bs with
  | [] => m
  | b :: r => mem_insert_bytes (base + 1) r (bvmap_set base b m)
  end.

Fixpoint mem_of_runs (runs : list (word * list byte)) : bvmap 64 byte :=
  match runs with
  | [] => bvmap_empty
  | (base, bs) :: r => mem_insert_bytes base bs (mem_of_runs r)
  end.

Definition mem_view (runs : list (word * list byte)) : word -> option byte :=
  fun a => bvmap_get a (mem_of_runs runs).

(** THE PROPERTY THAT MATTERS HERE: every byte the checker can read out of
    this view is one of the bytes the boundary checked.  (What the view
    answers WHERE is the reader's description of the guest's memory; that it
    answers only with checked bytes is this file's business.) *)
(** [tget] recurses on its key, so it does not reduce on an abstract
    one even against the empty tree; this is the lemma that says it. *)
Lemma bvmap_get_empty : forall {n A} (k : bv n),
  bvmap_get k (@bvmap_empty n A) = None.
Proof. intros n A k. unfold bvmap_get, bvmap_empty. destruct (bv_key k); reflexivity. Qed.

Lemma mem_insert_bytes_elem : forall bs base m a b,
  bvmap_get a (mem_insert_bytes base bs m) = Some b ->
  In b bs \/ bvmap_get a m = Some b.
Proof.
  induction bs as [|b0 r IH]; cbn; intros base m a b H; [right; exact H|].
  destruct (IH _ _ _ _ H) as [Hin | Hm]; [left; right; exact Hin|].
  destruct (decide (a = base)) as [->|Hne].
  - rewrite bvmap_get_set_same in Hm. left. left. congruence.
  - rewrite bvmap_get_set_other in Hm by congruence.
    right; exact Hm.
Qed.

Lemma mem_view_elem : forall runs a b,
  mem_view runs a = Some b -> exists base bs, In (base, bs) runs /\ In b bs.
Proof.
  unfold mem_view. induction runs as [|[base bs] r IH]; cbn; intros a b H.
  - rewrite bvmap_get_empty in H. discriminate H.
  - destruct (mem_insert_bytes_elem _ _ _ _ _ H) as [Hin | Hrest].
    + exists base, bs. split; [now left | exact Hin].
    + destruct (IH _ _ Hrest) as (base' & bs' & Hin & Hb).
      exists base', bs'. split; [now right | exact Hb].
Qed.

(** The writable view is a PREDICATE on the address, and that is not a
    weaker boundary than the readable view's data: the model reads this
    view for DEFINEDNESS only — an output buffer that is unmapped or
    read-only is [unmodeled] — and every arm reads it through
    [State.read_bytes_map] or [copy_bytes_map] and matches [Some]/[None],
    never the byte.  So the byte is fixed here at zero, the value both
    existing readers already supply for it.

    A predicate carries nothing that extraction could erase: its result
    is a [bool], which has no well-formedness condition, and the [Z] it
    is asked about is [bv_unsigned] of an address this boundary built.
    Taking it as data instead would cost a reader that decides
    writability one page at a time the enumeration of every writable
    page, which is not a thing it can do over a 2^47 address space. *)
Definition wmem_view (p : Z -> bool) : word -> option byte :=
  fun a => if p (bv_unsigned a) then Some (Z_to_bv 8 0) else None.

(** The predicate a reader that holds RANGES hands in: [(base, length)]
    pairs, read in [Z] over unsigned values, so a range that runs off the
    top of the address space covers what it says and nothing more. *)
Definition wmem_ranges (rs : list (Z * Z)) : Z -> bool :=
  fun a => existsb (fun r => (fst r <=? a)%Z && (a <? fst r + snd r)%Z) rs.

(* =========================================================================
   What a reader hands in
   ========================================================================= *)

(** The syscall as the outside world has it: integers, byte runs, and a
    predicate on the address.  Field for field this is
    [State.SyscallInput], with each memory view replaced by what it is
    built from. *)
Record RawInput := mkRawInput {
  rin_sysno : Z;                   (* a7 at ecall *)
  rin_args  : list Z;              (* a0..a5 at ecall *)
  rin_mem   : list (Z * list Z);   (* captured readable runs: (address, bytes) *)
  rin_wmem  : Z -> bool            (* is this address one the kernel may write? *)
}.

(** The observed effect as the outside world has it: field for field
    [State.SyscallEffect]. *)
Record RawEffect := mkRawEffect {
  reff_ret     : Z;
  reff_writes  : list (Z * list Z);
  reff_zeros   : list (Z * Z);
  reff_unmaps  : list (Z * Z);
  reff_copies  : list (Z * Z * Z);  (* (source, destination, length) *)
  reff_copyins : list (Z * Z)       (* (address, length) *)
}.

Definition input_of_raw (r : RawInput) : option SyscallInput :=
  match word_of_Z (rin_sysno r), words_of_Z (rin_args r),
        runs_of_Z (rin_mem r) with
  | Some sysno, Some args, Some runs =>
      Some (mkInput sysno args (mem_view runs) (wmem_view (rin_wmem r)))
  | _, _, _ => None
  end.

Definition effect_of_raw (r : RawEffect) : option SyscallEffect :=
  match word_of_Z (reff_ret r), runs_of_Z (reff_writes r),
        pairs_of_Z (reff_zeros r), pairs_of_Z (reff_unmaps r),
        copies_of_Z (reff_copies r), copyins_of_Z (reff_copyins r) with
  | Some ret, Some ws, Some zs, Some us, Some cs, Some ins =>
      Some (mkEffectU ret ws zs us cs ins)
  | _, _, _, _, _, _ => None
  end.

(** The way back, for a reader that built an effect with the model's own
    constructors ([mremap_inplace_effect], [mremap_move_effect],
    [brk_zeros], [brk_unmaps]): hand the result through this and the
    boundary checks it like any other outside value. *)
Definition raw_of_effect (e : SyscallEffect) : RawEffect :=
  mkRawEffect
    (bv_unsigned (eff_ret e))
    (map (fun w => (bv_unsigned (fst w), map bv_unsigned (snd w))) (eff_writes e))
    (map (fun p => (bv_unsigned (fst p), bv_unsigned (snd p))) (eff_zeros e))
    (map (fun p => (bv_unsigned (fst p), bv_unsigned (snd p))) (eff_unmaps e))
    (map (fun c => (bv_unsigned (copy_src c), bv_unsigned (copy_dst c),
                    bv_unsigned (copy_len c))) (eff_copies e))
    (map (fun p => (bv_unsigned (fst p), Z.of_nat (snd p))) (eff_copyins e)).

(* =========================================================================
   The checked entry point
   ========================================================================= *)

(** THE THIRD ANSWER.  [CheckedRefused] is not a verdict: it says the
    boundary was handed something that is not a machine observation, and
    that the checker was never asked.  A caller that counts verdicts must
    count this separately — it is neither a pass nor a conformance failure.
    [CheckedAnswer] carries [check_syscall_for_run]'s answer unchanged, the
    outer [None] included (the run's error transition). *)
Inductive checked_answer : Type :=
| CheckedRefused
| CheckedAnswer (r : option check_result).

Definition check_syscall_for_run_checked
    (ri : RawInput) (re : RawEffect) (m : Model) : checked_answer :=
  match input_of_raw ri, effect_of_raw re with
  | Some i, Some e => CheckedAnswer (check_syscall_for_run i e m)
  | _, _ => CheckedRefused
  end.

(** An answer is the verified checker's answer on values that ARE in the
    Rocq type, and on the caller's own integers: nothing was wrapped,
    truncated or defaulted on the way in. *)
Theorem checked_answer_is_the_checker : forall ri re m a,
  check_syscall_for_run_checked ri re m = CheckedAnswer a ->
  exists i e,
    input_of_raw ri = Some i /\ effect_of_raw re = Some e /\
    bv_unsigned (in_sysno i) = rin_sysno ri /\
    map bv_unsigned (in_args i) = rin_args ri /\
    bv_unsigned (eff_ret e) = reff_ret re /\
    a = check_syscall_for_run i e m.
Proof.
  intros ri re m a H. unfold check_syscall_for_run_checked in H.
  destruct (input_of_raw ri) as [i|] eqn:Hi; [|discriminate].
  destruct (effect_of_raw re) as [e|] eqn:He; [|discriminate].
  injection H as <-.
  exists i, e. repeat split; try assumption.
  - unfold input_of_raw in Hi.
    destruct (word_of_Z (rin_sysno ri)) as [sysno|] eqn:Hs; [|discriminate].
    destruct (words_of_Z (rin_args ri)); [|discriminate].
    destruct (runs_of_Z (rin_mem ri)); [|discriminate].
    injection Hi as <-. cbn. now apply bv_of_Z_value.
  - unfold input_of_raw in Hi.
    destruct (word_of_Z (rin_sysno ri)); [|discriminate].
    destruct (words_of_Z (rin_args ri)) as [args|] eqn:Ha; [|discriminate].
    destruct (runs_of_Z (rin_mem ri)); [|discriminate].
    injection Hi as <-. cbn. clear - Ha.
    revert args Ha. unfold words_of_Z.
    induction (rin_args ri) as [|z l IH]; cbn; intros args Ha.
    + injection Ha as <-. reflexivity.
    + destruct (word_of_Z z) as [w|] eqn:Hw; [|discriminate].
      destruct (mapM_opt word_of_Z l) as [ws|] eqn:Hl; [|discriminate].
      injection Ha as <-. cbn. f_equal.
      * now apply bv_of_Z_value.
      * now apply IH.
  - unfold effect_of_raw in He.
    destruct (word_of_Z (reff_ret re)) as [ret|] eqn:Hr; [|discriminate].
    destruct (runs_of_Z (reff_writes re)); [|discriminate].
    destruct (pairs_of_Z (reff_zeros re)); [|discriminate].
    destruct (pairs_of_Z (reff_unmaps re)); [|discriminate].
    destruct (copies_of_Z (reff_copies re)); [|discriminate].
    destruct (copyins_of_Z (reff_copyins re)); [|discriminate].
    injection He as <-. cbn. now apply bv_of_Z_value.
Qed.

(** THE DEFECT, closed: a return value no 64-bit word holds is refused and
    never judged.  [2^64] is the witness's value; the statement is the
    whole out-of-range set. *)
Theorem checked_refuses_out_of_range_ret : forall ri re m,
  ~ (0 <= reff_ret re < 2 ^ 64)%Z ->
  check_syscall_for_run_checked ri re m = CheckedRefused.
Proof.
  intros ri re m Hout. unfold check_syscall_for_run_checked.
  replace (effect_of_raw re) with (@None SyscallEffect).
  - now destruct (input_of_raw ri).
  - symmetry. unfold effect_of_raw.
    rewrite (proj2 (word_of_Z_refused (reff_ret re)) Hout).
    reflexivity.
Qed.

Theorem checked_refuses_out_of_range_sysno : forall ri re m,
  ~ (0 <= rin_sysno ri < 2 ^ 64)%Z ->
  check_syscall_for_run_checked ri re m = CheckedRefused.
Proof.
  intros ri re m Hout. unfold check_syscall_for_run_checked.
  replace (input_of_raw ri) with (@None SyscallInput); [reflexivity|].
  symmetry. unfold input_of_raw.
  rewrite (proj2 (word_of_Z_refused (rin_sysno ri)) Hout).
  reflexivity.
Qed.

Theorem checked_refuses_out_of_range_arg : forall ri re m z,
  In z (rin_args ri) -> ~ (0 <= z < 2 ^ 64)%Z ->
  check_syscall_for_run_checked ri re m = CheckedRefused.
Proof.
  intros ri re m z Hin Hout. unfold check_syscall_for_run_checked.
  replace (input_of_raw ri) with (@None SyscallInput); [reflexivity|].
  symmetry. unfold input_of_raw.
  rewrite (words_of_Z_elem_None _ _ Hin (proj2 (word_of_Z_refused z) Hout)).
  now destruct (word_of_Z (rin_sysno ri)).
Qed.

Theorem checked_refuses_out_of_range_byte : forall ri re m a bs z,
  In (a, bs) (rin_mem ri) -> In z bs -> ~ (0 <= z < 2 ^ 8)%Z ->
  check_syscall_for_run_checked ri re m = CheckedRefused.
Proof.
  intros ri re m a bs z Hrun Hin Hout. unfold check_syscall_for_run_checked.
  replace (input_of_raw ri) with (@None SyscallInput); [reflexivity|].
  symmetry. unfold input_of_raw.
  assert (runs_of_Z (rin_mem ri) = None) as Hruns.
  { apply (runs_of_Z_elem_None _ _ Hrun). unfold run_of_Z. cbn.
    rewrite (bytes_of_Z_elem_None _ _ Hin (proj2 (byte_of_Z_refused z) Hout)).
    now destruct (word_of_Z a). }
  rewrite Hruns.
  destruct (word_of_Z (rin_sysno ri)); [|reflexivity].
  now destruct (words_of_Z (rin_args ri)).
Qed.

Theorem checked_refuses_out_of_range_write_byte : forall ri re m a bs z,
  In (a, bs) (reff_writes re) -> In z bs -> ~ (0 <= z < 2 ^ 8)%Z ->
  check_syscall_for_run_checked ri re m = CheckedRefused.
Proof.
  intros ri re m a bs z Hrun Hin Hout. unfold check_syscall_for_run_checked.
  replace (effect_of_raw re) with (@None SyscallEffect).
  - now destruct (input_of_raw ri).
  - symmetry. unfold effect_of_raw.
    assert (runs_of_Z (reff_writes re) = None) as Hruns.
    { apply (runs_of_Z_elem_None _ _ Hrun). unfold run_of_Z. cbn.
      rewrite (bytes_of_Z_elem_None _ _ Hin (proj2 (byte_of_Z_refused z) Hout)).
      now destruct (word_of_Z a). }
    rewrite Hruns. now destruct (word_of_Z (reff_ret re)).
Qed.

(** Nothing the model can say is lost: an effect that EXISTS in Rocq is
    accepted by the boundary and comes back unchanged.  So a refusal is
    never a verdict the checker would have had. *)
Lemma mapM_opt_map_total : forall {A B} (f : A -> option B) (g : B -> A) (l : list B),
  (forall b, f (g b) = Some b) -> mapM_opt f (map g l) = Some l.
Proof.
  intros A B f g l Hf. induction l as [|x r IH]; cbn; [reflexivity|].
  rewrite Hf, IH. reflexivity.
Qed.

Lemma bytes_of_Z_total_list : forall l : list byte,
  bytes_of_Z (map bv_unsigned l) = Some l.
Proof. intros l. apply (mapM_opt_map_total byte_of_Z bv_unsigned l byte_of_Z_total). Qed.

Lemma words_of_Z_total_list : forall l : list word,
  words_of_Z (map bv_unsigned l) = Some l.
Proof. intros l. apply (mapM_opt_map_total word_of_Z bv_unsigned l word_of_Z_total). Qed.

Lemma run_of_Z_total : forall w : word * list byte,
  run_of_Z (bv_unsigned (fst w), map bv_unsigned (snd w)) = Some w.
Proof.
  intros [a bs]. unfold run_of_Z. cbn [fst snd].
  rewrite word_of_Z_total, bytes_of_Z_total_list. reflexivity.
Qed.

Lemma pair_of_Z_total : forall p : word * word,
  pair_of_Z (bv_unsigned (fst p), bv_unsigned (snd p)) = Some p.
Proof.
  intros [a b]. unfold pair_of_Z. cbn [fst snd].
  rewrite !word_of_Z_total. reflexivity.
Qed.

Lemma copy_of_Z_total : forall c : MemCopy,
  copy_of_Z (bv_unsigned (copy_src c), bv_unsigned (copy_dst c),
             bv_unsigned (copy_len c)) = Some c.
Proof.
  intros [s d l]. unfold copy_of_Z. cbn [copy_src copy_dst copy_len].
  rewrite !word_of_Z_total. reflexivity.
Qed.

Lemma copyin_of_Z_total : forall c : word * nat,
  copyin_of_Z (bv_unsigned (fst c), Z.of_nat (snd c)) = Some c.
Proof.
  intros [a n]. unfold copyin_of_Z. cbn [fst snd].
  rewrite word_of_Z_total.
  rewrite (proj2 (Z.leb_le 0 (Z.of_nat n)) (Nat2Z.is_nonneg n)).
  rewrite Nat2Z.id. reflexivity.
Qed.

Lemma runs_of_Z_total : forall l : list (word * list byte),
  runs_of_Z (map (fun w => (bv_unsigned (fst w), map bv_unsigned (snd w))) l)
  = Some l.
Proof. intros l. apply (mapM_opt_map_total run_of_Z _ l run_of_Z_total). Qed.

Lemma pairs_of_Z_total : forall l : list (word * word),
  pairs_of_Z (map (fun p => (bv_unsigned (fst p), bv_unsigned (snd p))) l)
  = Some l.
Proof. intros l. apply (mapM_opt_map_total pair_of_Z _ l pair_of_Z_total). Qed.

Lemma copies_of_Z_total : forall l : list MemCopy,
  copies_of_Z (map (fun c => (bv_unsigned (copy_src c), bv_unsigned (copy_dst c),
                              bv_unsigned (copy_len c))) l) = Some l.
Proof. intros l. apply (mapM_opt_map_total copy_of_Z _ l copy_of_Z_total). Qed.

Lemma copyins_of_Z_total : forall l : list (word * nat),
  copyins_of_Z (map (fun p => (bv_unsigned (fst p), Z.of_nat (snd p))) l)
  = Some l.
Proof. intros l. apply (mapM_opt_map_total copyin_of_Z _ l copyin_of_Z_total). Qed.

Theorem effect_of_raw_of_effect : forall e, effect_of_raw (raw_of_effect e) = Some e.
Proof.
  intros e. unfold effect_of_raw, raw_of_effect.
  cbn [reff_ret reff_writes reff_zeros reff_unmaps reff_copies reff_copyins].
  rewrite word_of_Z_total, runs_of_Z_total, !pairs_of_Z_total,
    copies_of_Z_total, copyins_of_Z_total.
  destruct e; reflexivity.
Qed.

(* =========================================================================
   The model's seed
   ========================================================================= *)

(** [init_model]'s own arguments and the whole of [State.ProcInput] come
    from outside too, and carry the same erased proofs: the reserved
    segments, the initial break, the mmap base and the stack pointer are
    [word]s, and the input record holds [word]s, byte lists, a file system,
    two byte STREAMS and a network QUEUE whose peers carry a [bv 32]
    address and a [bv 16] port.

    The streams and the queue are coinductive, so a caller cannot be asked
    for one: an infinite object's bytes cannot be checked before it is
    consumed.  They are taken here as the finite data every reader actually
    has — standard input is a finite byte string, the random device is a
    declared prefix and then zeros forever ([State.default_urandom]'s own
    value), and the network is a list of peers and then
    [State.net_silent] — and built here. *)

Variant RawNetEnd : Type := RneFin | RneRst | RneTimedOut.

Record RawPeer := mkRawPeer {
  rpe_addr  : Z;        (* sin_addr.s_addr, network order: a [bv 32] *)
  rpe_port  : Z;        (* sin_port, network order: a [bv 16] *)
  rpe_bytes : list Z;   (* what the peer says, in order *)
  rpe_end   : RawNetEnd (* how its stream ends *)
}.

(** It is built with [State.mkProcInput_full], the record's own
    constructor, and NOT with the thirteen-place [State.mkProcInput]: a
    field added to the end of [ProcInput] must break this file, so that
    whoever adds it gives it a raw counterpart here and a reader has to
    declare it.  [mkProcInput] would default it instead, and a defaulted
    environment field is a claim about the run that nobody made. *)
Record RawProcInput := mkRawProcInput {
  rpi_argv  : list (list Z);
  rpi_envp  : list (list Z);
  rpi_image_fs : list (list Z * list Z);  (* (path, contents) *)
  rpi_stdin : list Z;
  rpi_uid   : Z;
  rpi_gid   : Z;
  rpi_groups : list Z;
  rpi_net   : list RawPeer;
  rpi_nofile : Z;
  rpi_sigmask : Z;
  rpi_hwcap : Z;
  rpi_abort_terminal : bool;
  rpi_va_size : VaSize;
  rpi_urandom : list Z;                   (* the declared prefix; zeros after *)
  rpi_tmp   : list (list Z * list Z)
}.

Fixpoint stream_of_bytes (l : list byte) : InputStream :=
  match l with
  | [] => IEof
  | b :: r => ICons b (stream_of_bytes r)
  end.

(** The random device never ends ([Run.valid_urandom]), so the declared
    prefix is followed by [State.default_urandom] rather than by [IEof]. *)
Fixpoint urandom_of_bytes (l : list byte) : InputStream :=
  match l with
  | [] => default_urandom
  | b :: r => ICons b (urandom_of_bytes r)
  end.

Definition net_end (e : RawNetEnd) : NetStream :=
  match e with
  | RneFin => NFin
  | RneRst => NRst
  | RneTimedOut => NTimedOut
  end.

Definition net_script (bs : list byte) (e : RawNetEnd) : NetStream :=
  fold_right NCons (net_end e) bs.

Fixpoint net_of_raw (ps : list RawPeer) : option NetQueue :=
  match ps with
  | [] => Some net_silent
  | p :: r =>
      match bv32_of_Z (rpe_addr p), bv16_of_Z (rpe_port p),
            bytes_of_Z (rpe_bytes p), net_of_raw r with
      | Some a, Some pt, Some bs, Some rest =>
          Some (NConn (mkPeer a pt) (net_script bs (rpe_end p)) rest)
      | _, _, _, _ => None
      end
  end.

Definition bytes_list_of_Z : list (list Z) -> option (list (list byte)) :=
  mapM_opt bytes_of_Z.

(** The file system is kept strictly sorted by [Fs.path_ltb], so the
    entries are seeded through [Fs.fs_set] rather than consed. *)
Fixpoint fs_of_raw (l : list (list Z * list Z)) : option Fs.Fs :=
  match l with
  | [] => Some []
  | (p, d) :: r =>
      match bytes_of_Z p, bytes_of_Z d, fs_of_raw r with
      | Some p', Some d', Some fs => Some (Fs.fs_set fs p' d')
      | _, _, _ => None
      end
  end.

Definition proc_input_of_raw (r : RawProcInput) : option ProcInput :=
  match bytes_list_of_Z (rpi_argv r), bytes_list_of_Z (rpi_envp r),
        fs_of_raw (rpi_image_fs r), bytes_of_Z (rpi_stdin r),
        word_of_Z (rpi_uid r), word_of_Z (rpi_gid r),
        words_of_Z (rpi_groups r), net_of_raw (rpi_net r) with
  | Some argv, Some envp, Some image_fs, Some stdin,
    Some uid, Some gid, Some groups, Some net =>
      match word_of_Z (rpi_nofile r), word_of_Z (rpi_sigmask r),
            word_of_Z (rpi_hwcap r), bytes_of_Z (rpi_urandom r),
            fs_of_raw (rpi_tmp r) with
      | Some nofile, Some sigmask, Some hwcap, Some urandom, Some tmp =>
          Some (mkProcInput_full argv envp image_fs (stream_of_bytes stdin)
                  uid gid groups net nofile sigmask hwcap
                  (rpi_abort_terminal r) (rpi_va_size r)
                  (urandom_of_bytes urandom) tmp)
      | _, _, _, _, _ => None
      end
  | _, _, _, _, _, _, _, _ => None
  end.

(** [lim] is the run's byte budget and is a [Z] in the model
    ([State.vm_limit]), so every integer is one it can hold: it is passed
    through unchecked, and that is not an omission. *)
Definition init_model_checked (reserved : list (Z * Z))
    (brk0 mbase sp : Z) (lim : Z) (r : RawProcInput) : option Model :=
  match pairs_of_Z reserved, word_of_Z brk0, word_of_Z mbase, word_of_Z sp,
        proc_input_of_raw r with
  | Some res, Some b, Some mb, Some s, Some inp =>
      Some (init_model res b mb s lim inp)
  | _, _, _, _, _ => None
  end.

Theorem init_model_checked_refuses_out_of_range_sp : forall reserved brk0 mbase sp lim r,
  ~ (0 <= sp < 2 ^ 64)%Z ->
  init_model_checked reserved brk0 mbase sp lim r = None.
Proof.
  intros reserved brk0 mbase sp lim r Hout. unfold init_model_checked.
  rewrite (proj2 (word_of_Z_refused sp) Hout).
  destruct (pairs_of_Z reserved); [|reflexivity].
  destruct (word_of_Z brk0); [|reflexivity].
  now destruct (word_of_Z mbase).
Qed.

Theorem init_model_checked_refuses_out_of_range_uid : forall reserved brk0 mbase sp lim r,
  ~ (0 <= rpi_uid r < 2 ^ 64)%Z ->
  init_model_checked reserved brk0 mbase sp lim r = None.
Proof.
  intros reserved brk0 mbase sp lim r Hout. unfold init_model_checked.
  assert (proc_input_of_raw r = None) as Hp.
  { unfold proc_input_of_raw.
    rewrite (proj2 (word_of_Z_refused (rpi_uid r)) Hout).
    destruct (bytes_list_of_Z (rpi_argv r)); [|reflexivity].
    destruct (bytes_list_of_Z (rpi_envp r)); [|reflexivity].
    destruct (fs_of_raw (rpi_image_fs r)); [|reflexivity].
    now destruct (bytes_of_Z (rpi_stdin r)). }
  rewrite Hp.
  destruct (pairs_of_Z reserved); [|reflexivity].
  destruct (word_of_Z brk0); [|reflexivity].
  destruct (word_of_Z mbase); [|reflexivity].
  now destruct (word_of_Z sp).
Qed.

Theorem init_model_checked_refuses_out_of_range_peer_port :
  forall reserved brk0 mbase sp lim r p,
  In p (rpi_net r) -> ~ (0 <= rpe_port p < 2 ^ 16)%Z ->
  init_model_checked reserved brk0 mbase sp lim r = None.
Proof.
  intros reserved brk0 mbase sp lim r p Hin Hout. unfold init_model_checked.
  assert (net_of_raw (rpi_net r) = None) as Hnet.
  { clear - Hin Hout. induction (rpi_net r) as [|q l IH]; cbn; [contradiction|].
    destruct Hin as [->|Hin].
    - unfold bv16_of_Z. rewrite (proj2 (bv_of_Z_refused 16 (rpe_port p)) Hout).
      now destruct (bv32_of_Z (rpe_addr p)).
    - rewrite (IH Hin).
      destruct (bv32_of_Z (rpe_addr q)); [|reflexivity].
      destruct (bv16_of_Z (rpe_port q)); [|reflexivity].
      now destruct (bytes_of_Z (rpe_bytes q)). }
  assert (proc_input_of_raw r = None) as Hp.
  { unfold proc_input_of_raw. rewrite Hnet.
    destruct (bytes_list_of_Z (rpi_argv r)); [|reflexivity].
    destruct (bytes_list_of_Z (rpi_envp r)); [|reflexivity].
    destruct (fs_of_raw (rpi_image_fs r)); [|reflexivity].
    destruct (bytes_of_Z (rpi_stdin r)); [|reflexivity].
    destruct (word_of_Z (rpi_uid r)); [|reflexivity].
    destruct (word_of_Z (rpi_gid r)); [|reflexivity].
    now destruct (words_of_Z (rpi_groups r)). }
  rewrite Hp.
  destruct (pairs_of_Z reserved); [|reflexivity].
  destruct (word_of_Z brk0); [|reflexivity].
  destruct (word_of_Z mbase); [|reflexivity].
  now destruct (word_of_Z sp).
Qed.
