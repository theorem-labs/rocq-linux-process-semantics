(** * Riscv.CheckedIsa — the extracted ISA model's input boundary

    TRUST BOUNDARY: this file is part of the trusted specification.

    WHY IT EXISTS.  [Riscv/Extraction.v] extracts the RV64GC model to
    OCaml for the differential tester that holds it against a
    disassembler and against the Sail RISC-V model.  Its header has
    always said what that costs: "[bv n] is a record whose only
    computational field is the unsigned [Z] (the [BvWf] proof is erased),
    so a bitvector extracts to a bare [Big_int_Z.big_int] and the WIDTH
    IS ERASED.  The OCaml caller must therefore mask values itself when
    constructing inputs."

    A sentence telling the caller to mask is not a boundary; it is a
    contract nobody checks.  It is the same failure that let a system
    call return of 2^64 reach a verdict through the other extracted
    artifact ([Checks.CheckedInput], and the witness it names).  Here the
    consequence is a comparison against Sail on a value no register
    holds rather than a verdict, which lowers the cost of the bug and not
    the cost of fixing it.

    WHAT IT DOES.  Every entry point takes the outside world's values as
    [Z] and refuses, before the model runs, any integer that is not in
    the Rocq type it would have to inhabit.  A refusal is a THIRD answer
    ([CkRefused]), kept apart from both of the model's own answers: a
    word that does not decode is [CkAnswer None], and a word that is not
    a word at all is [CkRefused].  Nothing can read a refusal as "the
    model declined this encoding".

    WHAT A CALLER NEVER PASSES IN, and why.  The instruction AST, the
    compressed AST and the core state are all built out of [bv]s, so none
    of them is an argument of this surface: a caller gives an ENCODING
    and a [RawCore] of plain integers, and this file builds the terms.
    [exec]'s own [sz] argument is gone with them — the size is the one
    [decode_any] reports for the encoding, which is what [Sem.step]
    already uses ([Sem.v], [step]).

    [Sem.step] takes its decoder as a parameter; [step_checked] fixes it
    to this model's own [decode_any].  The parameter is not lost by
    accident: plugging a foreign decoder into the model is a different
    experiment from testing the model, and it is one no boundary here
    could check, because the instructions such a decoder returns are
    [bv]-carrying terms built outside Rocq.

    THE ONE VALUE THAT ARRIVES MID-EXECUTION.  [Sem.eff]'s [ELoad n a k]
    hands the interpreter a continuation, and the interpreter answers it
    with the bytes it read.  That value enters the model between one
    instruction and its result rather than at a call, which is where a
    mask is easiest to forget and hardest to notice afterwards.
    [eff_feed_load] is the checked way to answer it, and it refuses a
    value the pending width does not hold.

    WHAT IT DOES NOT DO.  Extraction writes a .mli beside the .ml, and it
    publishes everything the roots reach — [Sem.exec], [Sem.step],
    [Decode.decode] and the [core], [instr] and [eff] types included:
    the checked entry points reach them, so no choice of roots can hide
    them.  The guarantee this file carries is therefore about the
    SUPPORTED surface — the roots of [Riscv/Extraction.v] — and that
    surface offers no way to run the model on a value it has not
    checked. *)

From LinuxProcessSemantics.Riscv Require Import
  Prelude CheckedBv Instr Decode DecodeC Sem.
From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.
Open Scope Z_scope.

(** The third answer.  [CkRefused] is not one of the model's answers. *)
Inductive checked (A : Type) : Type :=
| CkRefused
| CkAnswer (a : A).
Arguments CkRefused {A}.
Arguments CkAnswer {A} a.

(* =========================================================================
   Decoding
   ========================================================================= *)

Definition decode_checked (z : Z) : checked (option instr) :=
  match bv32_of_Z z with
  | Some w => CkAnswer (decode w)
  | None => CkRefused
  end.

Definition decode16_checked (z : Z) : checked (option cinstr) :=
  match bv16_of_Z z with
  | Some h => CkAnswer (decode16 h)
  | None => CkRefused
  end.

(** Decode a compressed parcel and expand it, so that a caller comparing
    the expansion never has to build a [cinstr] — whose immediates are
    [bv]s — itself. *)
Definition expand_c_checked (z : Z) : checked (option instr) :=
  match bv16_of_Z z with
  | Some h => CkAnswer (option_map expand_c (decode16 h))
  | None => CkRefused
  end.

Definition decode_any_checked (z : Z) : checked (option (instr * Z)) :=
  match bv32_of_Z z with
  | Some w => CkAnswer (decode_any w)
  | None => CkRefused
  end.

Definition is_defined_illegal_checked (z : Z) : checked bool :=
  match bv32_of_Z z with
  | Some w => CkAnswer (is_defined_illegal w)
  | None => CkRefused
  end.

(* =========================================================================
   The core state
   ========================================================================= *)

(** The thirty-two architectural registers, x0 first.  The register file
    is a [bvmap] keyed by the 5-bit index; x0 hardwiring lives in
    [Sem.rget]/[Sem.rset], so a caller never special-cases it. *)
Fixpoint regs_of_list_aux (i : nat) (l : list word) (m : bvmap 5 word)
    : bvmap 5 word :=
  match l with
  | [] => m
  | v :: r => regs_of_list_aux (S i) r (bvmap_set (Z_to_bv 5 (Z.of_nat i)) v m)
  end.

Definition regs_of_list (l : list word) : bvmap 5 word :=
  regs_of_list_aux 0 l (@bvmap_empty 5 word).

Definition reg_list (m : bvmap 5 word) : list word :=
  map (fun i => reg_get m (Z_to_bv 5 (Z.of_nat i))) (seq 0 32).

(** The core as the outside world has it: integers, and the reservation
    as an optional address.  Field for field this is [Sem.core], with
    each register file given as its thirty-two values. *)
Record RawCore := mkRawCore {
  rc_regs  : list Z;      (* x0..x31, all thirty-two, in order *)
  rc_fregs : list Z;      (* f0..f31, all thirty-two, in order *)
  rc_pc    : Z;
  rc_fcsr  : Z;           (* the 32-bit fcsr *)
  rc_resv  : option Z     (* the LR/SC reservation address, if one is live *)
}.

Definition resv_of_Z (o : option Z) : option (option word) :=
  match o with
  | None => Some None
  | Some z => match word_of_Z z with
              | Some w => Some (Some w)
              | None => None
              end
  end.

(** A register file of any length other than thirty-two is refused
    rather than padded: a caller that gives thirty-one values has not
    said what x31 is, and a padded zero would be a claim it never
    made. *)
Definition core_of_raw (r : RawCore) : option core :=
  match words_of_Z (rc_regs r), words_of_Z (rc_fregs r),
        word_of_Z (rc_pc r), bv32_of_Z (rc_fcsr r), resv_of_Z (rc_resv r) with
  | Some regs, Some fregs, Some pc, Some fcsr, Some resv =>
      if (Nat.eqb (length regs) 32 && Nat.eqb (length fregs) 32)%bool
      then Some (Core (regs_of_list regs) (regs_of_list fregs) pc fcsr resv)
      else None
  | _, _, _, _, _ => None
  end.

(** The way back, for a caller comparing the retired state. *)
Definition raw_of_core (c : core) : RawCore :=
  mkRawCore
    (map bv_unsigned (reg_list (c_regs c)))
    (map bv_unsigned (reg_list (c_fregs c)))
    (bv_unsigned (c_pc c))
    (bv_unsigned (c_fcsr c))
    (option_map bv_unsigned (c_resv c)).

(* =========================================================================
   Running one instruction
   ========================================================================= *)

(** Execute the instruction an encoding denotes, at the size
    [decode_any] reports for it.  [CkAnswer None] is a word this model
    does not decode; [CkRefused] is not a 32-bit word, or not a core. *)
Definition exec_encoded_checked (w32 : Z) (rc : RawCore) : checked (option eff) :=
  match bv32_of_Z w32, core_of_raw rc with
  | Some w, Some c =>
      CkAnswer (match decode_any w with
                | Some (i, isz) => Some (exec (Z_to_bv 64 isz) i c)
                | None => None
                end)
  | _, _ => CkRefused
  end.

(** One step from the core's own pc: the effect tree opens with the
    instruction fetch, exactly as [Sem.step] builds it. *)
Definition step_checked (rc : RawCore) : checked eff :=
  match core_of_raw rc with
  | Some c => CkAnswer (step decode_any c)
  | None => CkRefused
  end.

(** What a pending effect is waiting for, read without matching the
    constructor: the load's width in bits and its address. *)
Definition eff_pending_load (e : eff) : option (Z * Z) :=
  match e with
  | ELoad n a _ => Some (Z.of_N n, bv_unsigned a)
  | _ => None
  end.

(** Answering the pending load.  [LsRefused] is a value the width does
    not hold; [LsNotPending] is a caller mistake — this effect is not
    waiting for a load — and neither is a result of the model. *)
Inductive load_step : Type :=
| LsRefused
| LsNotPending
| LsNext (e : eff).

Definition eff_feed_load (e : eff) (z : Z) : load_step :=
  match e with
  | ELoad n _ k =>
      match bv_of_Z n z with
      | Some v => LsNext (k v)
      | None => LsRefused
      end
  | _ => LsNotPending
  end.

(* =========================================================================
   What the boundary promises
   ========================================================================= *)

Theorem decode_checked_refuses : forall z,
  ~ (0 <= z < 2 ^ 32) -> decode_checked z = CkRefused.
Proof.
  intros z Hout. unfold decode_checked, bv32_of_Z.
  rewrite (proj2 (bv_of_Z_refused 32 z) Hout). reflexivity.
Qed.

Theorem decode16_checked_refuses : forall z,
  ~ (0 <= z < 2 ^ 16) -> decode16_checked z = CkRefused.
Proof.
  intros z Hout. unfold decode16_checked, bv16_of_Z.
  rewrite (proj2 (bv_of_Z_refused 16 z) Hout). reflexivity.
Qed.

Theorem expand_c_checked_refuses : forall z,
  ~ (0 <= z < 2 ^ 16) -> expand_c_checked z = CkRefused.
Proof.
  intros z Hout. unfold expand_c_checked, bv16_of_Z.
  rewrite (proj2 (bv_of_Z_refused 16 z) Hout). reflexivity.
Qed.

Theorem decode_any_checked_refuses : forall z,
  ~ (0 <= z < 2 ^ 32) -> decode_any_checked z = CkRefused.
Proof.
  intros z Hout. unfold decode_any_checked, bv32_of_Z.
  rewrite (proj2 (bv_of_Z_refused 32 z) Hout). reflexivity.
Qed.

Theorem is_defined_illegal_checked_refuses : forall z,
  ~ (0 <= z < 2 ^ 32) -> is_defined_illegal_checked z = CkRefused.
Proof.
  intros z Hout. unfold is_defined_illegal_checked, bv32_of_Z.
  rewrite (proj2 (bv_of_Z_refused 32 z) Hout). reflexivity.
Qed.

(** An answer is the model's own answer on the caller's own integer:
    nothing was wrapped or truncated on the way in. *)
Theorem decode_any_checked_answer : forall z a,
  decode_any_checked z = CkAnswer a ->
  exists w, bv_unsigned w = z /\ decode_any w = a.
Proof.
  intros z a H. unfold decode_any_checked in H.
  destruct (bv32_of_Z z) as [w|] eqn:Hw; [|discriminate].
  injection H as <-. exists w. split; [now apply bv_of_Z_value | reflexivity].
Qed.

Theorem exec_encoded_checked_refuses_word : forall w32 rc,
  ~ (0 <= w32 < 2 ^ 32) -> exec_encoded_checked w32 rc = CkRefused.
Proof.
  intros w32 rc Hout. unfold exec_encoded_checked, bv32_of_Z.
  rewrite (proj2 (bv_of_Z_refused 32 w32) Hout). reflexivity.
Qed.

Theorem exec_encoded_checked_refuses_core : forall w32 rc,
  core_of_raw rc = None -> exec_encoded_checked w32 rc = CkRefused.
Proof.
  intros w32 rc H. unfold exec_encoded_checked. rewrite H.
  now destruct (bv32_of_Z w32).
Qed.

Theorem step_checked_refuses : forall rc,
  core_of_raw rc = None -> step_checked rc = CkRefused.
Proof. intros rc H. unfold step_checked. now rewrite H. Qed.

(** The core carries the caller's own integers: each register is one of
    the thirty-two values given, in type, and the file is built from
    them and from nothing else. *)
Theorem core_of_raw_regs : forall r c,
  core_of_raw r = Some c ->
  exists regs, words_of_Z (rc_regs r) = Some regs
            /\ map bv_unsigned regs = rc_regs r
            /\ length regs = 32%nat
            /\ c_regs c = regs_of_list regs.
Proof.
  intros r c H. unfold core_of_raw in H.
  destruct (words_of_Z (rc_regs r)) as [regs|] eqn:Hregs; [|discriminate].
  destruct (words_of_Z (rc_fregs r)) as [fregs|]; [|discriminate].
  destruct (word_of_Z (rc_pc r)); [|discriminate].
  destruct (bv32_of_Z (rc_fcsr r)); [|discriminate].
  destruct (resv_of_Z (rc_resv r)); [|discriminate].
  destruct (Nat.eqb (length regs) 32 && Nat.eqb (length fregs) 32)%bool
    eqn:Hb; [|discriminate].
  apply andb_true_iff in Hb as [Hb1 _].
  injection H as <-. exists regs. split; [reflexivity|].
  split; [now apply words_of_Z_values|].
  split; [now apply Nat.eqb_eq | reflexivity].
Qed.

Theorem core_of_raw_pc : forall r c,
  core_of_raw r = Some c -> bv_unsigned (c_pc c) = rc_pc r.
Proof.
  intros r c H. unfold core_of_raw in H.
  destruct (words_of_Z (rc_regs r)) as [regs|]; [|discriminate].
  destruct (words_of_Z (rc_fregs r)) as [fregs|]; [|discriminate].
  destruct (word_of_Z (rc_pc r)) as [pc|] eqn:Hpc; [|discriminate].
  destruct (bv32_of_Z (rc_fcsr r)); [|discriminate].
  destruct (resv_of_Z (rc_resv r)); [|discriminate].
  destruct (Nat.eqb (length regs) 32 && Nat.eqb (length fregs) 32)%bool;
    [|discriminate].
  injection H as <-. cbn. now apply bv_of_Z_value.
Qed.

Theorem core_of_raw_fcsr : forall r c,
  core_of_raw r = Some c -> bv_unsigned (c_fcsr c) = rc_fcsr r.
Proof.
  intros r c H. unfold core_of_raw in H.
  destruct (words_of_Z (rc_regs r)) as [regs|]; [|discriminate].
  destruct (words_of_Z (rc_fregs r)) as [fregs|]; [|discriminate].
  destruct (word_of_Z (rc_pc r)); [|discriminate].
  destruct (bv32_of_Z (rc_fcsr r)) as [f|] eqn:Hf; [|discriminate].
  destruct (resv_of_Z (rc_resv r)); [|discriminate].
  destruct (Nat.eqb (length regs) 32 && Nat.eqb (length fregs) 32)%bool;
    [|discriminate].
  injection H as <-. cbn. now apply bv_of_Z_value.
Qed.

Theorem core_of_raw_refuses_pc : forall r,
  ~ (0 <= rc_pc r < 2 ^ 64) -> core_of_raw r = None.
Proof.
  intros r Hout. unfold core_of_raw.
  rewrite (proj2 (word_of_Z_refused (rc_pc r)) Hout).
  destruct (words_of_Z (rc_regs r)); [|reflexivity].
  now destruct (words_of_Z (rc_fregs r)).
Qed.

Theorem core_of_raw_refuses_reg : forall r z,
  In z (rc_regs r) -> ~ (0 <= z < 2 ^ 64) -> core_of_raw r = None.
Proof.
  intros r z Hin Hout. unfold core_of_raw.
  rewrite (words_of_Z_elem_None _ _ Hin (proj2 (word_of_Z_refused z) Hout)).
  reflexivity.
Qed.

Theorem core_of_raw_refuses_freg : forall r z,
  In z (rc_fregs r) -> ~ (0 <= z < 2 ^ 64) -> core_of_raw r = None.
Proof.
  intros r z Hin Hout. unfold core_of_raw.
  rewrite (words_of_Z_elem_None _ _ Hin (proj2 (word_of_Z_refused z) Hout)).
  now destruct (words_of_Z (rc_regs r)).
Qed.

Theorem core_of_raw_refuses_fcsr : forall r,
  ~ (0 <= rc_fcsr r < 2 ^ 32) -> core_of_raw r = None.
Proof.
  intros r Hout. unfold core_of_raw, bv32_of_Z.
  rewrite (proj2 (bv_of_Z_refused 32 (rc_fcsr r)) Hout).
  destruct (words_of_Z (rc_regs r)); [|reflexivity].
  destruct (words_of_Z (rc_fregs r)); [|reflexivity].
  now destruct (word_of_Z (rc_pc r)).
Qed.

Theorem core_of_raw_refuses_resv : forall r z,
  rc_resv r = Some z -> ~ (0 <= z < 2 ^ 64) -> core_of_raw r = None.
Proof.
  intros r z Hr Hout. unfold core_of_raw.
  assert (resv_of_Z (rc_resv r) = None) as Hres.
  { unfold resv_of_Z. rewrite Hr.
    now rewrite (proj2 (word_of_Z_refused z) Hout). }
  rewrite Hres.
  destruct (words_of_Z (rc_regs r)); [|reflexivity].
  destruct (words_of_Z (rc_fregs r)); [|reflexivity].
  destruct (word_of_Z (rc_pc r)); [|reflexivity].
  now destruct (bv32_of_Z (rc_fcsr r)).
Qed.

(** The value that arrives mid-execution. *)
Theorem eff_feed_load_refuses : forall n a k z,
  ~ (0 <= z < bv_modulus n) -> eff_feed_load (ELoad n a k) z = LsRefused.
Proof.
  intros n a k z Hout. cbn.
  now rewrite (proj2 (bv_of_Z_refused n z) Hout).
Qed.

Theorem eff_feed_load_value : forall e z e',
  eff_feed_load e z = LsNext e' ->
  exists n a k (v : bv n), e = ELoad n a k /\ bv_unsigned v = z /\ e' = k v.
Proof.
  intros e z e' H. destruct e; cbn in H; try discriminate.
  destruct (bv_of_Z n z) as [v|] eqn:Hv; [|discriminate].
  injection H as <-. exists n, a, k, v.
  split; [reflexivity|]. split; [now apply bv_of_Z_value | reflexivity].
Qed.

Theorem eff_feed_load_not_pending : forall e z,
  eff_pending_load e = None -> eff_feed_load e z = LsNotPending.
Proof. intros e z H. destruct e; cbn in *; congruence. Qed.
