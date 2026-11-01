(** * LinuxProcessSem.Checks.Sys.Fs.Select — the pselect6 (72) and ppoll (73) checkers, and their proofs

    Mirrors [Sys/Fs/Select.v], which answers to Linux [fs/select.c]: this
    file holds the checkers for the syscalls defined there, and no
    others.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export
  Prelude.

(* =========================================================================
   The acceptor shared by both syscalls

   [Select.pselect_answer] admits, for one call, every choice [sel] of the
   undecided pair ends and, where a remaining time is written, every
   sixteen bytes [Select.pselect_remaining_ok] admits.  Both choices are
   in the effect, so the acceptor READS THEM BACK rather than search:
   [sel] through a syscall-specific readback [rd] of the writes, the
   remaining time as the last write.  It then rebuilds the answer for
   that choice and compares.  Soundness needs nothing of [rd]; for
   completeness [rd] must return the choice that made the writes
   ([pa_readback]), which each syscall proves below.
   ========================================================================= *)

Definition check_pselect_answer (pa : PselectAnswers)
    (rd : list (word * list byte) -> Z) (reads : list (word * nat))
    (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | mkEffectU r' ws' [] [] [] ks =>
      if access_ranges_eqb ks reads then
        match pa_ans pa (Z.land (pa_und pa) (rd ws')) with
        | (r, ws, None) =>
            if bv_eqb r' r && writes_eqb ws' ws then CheckOk m [] else CheckReject
        | (r, ws, Some (tsp, (sec, nsec))) =>
            if bv_eqb r' r
               && writes_eqb ws' (ws ++ [(tsp, snd (last ws' (tsp, [])))])
               && pselect_remaining_ok sec nsec (snd (last ws' (tsp, [])))
            then CheckOk m [] else CheckReject
        end
      else CheckReject
  | _ => CheckReject
  end.

(** What completeness asks of a readback: on the writes of any choice
    [sel], followed by anything, it returns [sel] within [pa_und]. *)
Definition pa_readback (pa : PselectAnswers) (rd : list (word * list byte) -> Z)
    : Prop :=
  forall sel extra, Z.land (pa_und pa) sel = sel ->
    Z.land (pa_und pa) (rd (snd (fst (pa_ans pa sel)) ++ extra)) = sel.

Lemma land_und_idem : forall u x, Z.land u (Z.land u x) = Z.land u x.
Proof. intros u x. rewrite Z.land_assoc, Z.land_diag. reflexivity. Qed.

(** With nothing undecided any readback will do: the one choice is 0. *)
Lemma pa_readback_und0 : forall pa rd, pa_und pa = 0%Z -> pa_readback pa rd.
Proof.
  intros pa rd H sel extra Hs. rewrite H in Hs |- *.
  rewrite Z.land_0_l in Hs |- *. exact Hs.
Qed.

Lemma check_pselect_answer_sound : forall pa rd reads eff m m' evs i,
  check_pselect_answer pa rd reads eff m = CheckOk m' evs ->
  pselect_answer reads pa i m (Ok eff m' evs).
Proof.
  intros pa rd reads [r' ws' zs us cs ks] m m' evs i H.
  unfold check_pselect_answer in H.
  destruct zs as [|? ?]; [|discriminate H].
  destruct us as [|? ?]; [|discriminate H].
  destruct cs as [|? ?]; [|discriminate H].
  destruct (access_ranges_eqb ks reads) eqn:Hk; [|discriminate H].
  apply access_ranges_eqb_eq in Hk. subst ks.
  unfold pselect_answer.
  eapply bind_ok0;
    [apply (choose_ok _ (Z.land (pa_und pa) (rd ws'))); apply land_und_idem|].
  cbv beta.
  destruct (pa_ans pa (Z.land (pa_und pa) (rd ws'))) as [[r ws] [[tsp [sec nsec]]|]];
    cbv beta iota in H |- *.
  - match type of H with context [if ?b then _ else _] => destruct b eqn:Hg end;
      cbv beta iota in H; [|discriminate H].
    injection H as <- <-.
    apply andb_true_iff in Hg as [Hg Hok]. apply andb_true_iff in Hg as [Hr Hw].
    apply bv_eqb_eq in Hr. apply writes_eqb_eq in Hw. subst r'.
    rewrite Hw at 1.
    eapply bind_ok0; [apply (choose_ok _ (snd (last ws' (tsp, [])))); exact Hok|].
    cbv beta. apply pure_ok.
  - match type of H with context [if ?b then _ else _] => destruct b eqn:Hg end;
      cbv beta iota in H; [|discriminate H].
    injection H as <- <-.
    apply andb_true_iff in Hg as [Hr Hw].
    apply bv_eqb_eq in Hr. apply writes_eqb_eq in Hw. subst r' ws'.
    apply pure_ok.
Qed.

Lemma check_pselect_answer_not_unmodeled : forall pa rd reads eff m,
  check_pselect_answer pa rd reads eff m <> CheckUnmodeled.
Proof.
  intros pa rd reads [r' ws' zs us cs ks] m. unfold check_pselect_answer.
  destruct zs as [|? ?]; [|discriminate].
  destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct (access_ranges_eqb ks reads); [|discriminate].
  destruct (pa_ans pa (Z.land (pa_und pa) (rd ws'))) as [[r ws] [[tsp [sec nsec]]|]];
    cbv beta iota;
    match goal with |- context [if ?b then _ else _] => destruct b end; discriminate.
Qed.

(** The acceptor never moves the model. *)
Lemma check_pselect_answer_model : forall pa rd reads eff m m' evs,
  check_pselect_answer pa rd reads eff m = CheckOk m' evs -> m' = m.
Proof.
  intros pa rd reads [r' ws' zs us cs ks] m m' evs H.
  unfold check_pselect_answer in H.
  destruct zs as [|? ?]; [|discriminate H].
  destruct us as [|? ?]; [|discriminate H].
  destruct cs as [|? ?]; [|discriminate H].
  destruct (access_ranges_eqb ks reads); [|discriminate H].
  destruct (pa_ans pa (Z.land (pa_und pa) (rd ws'))) as [[r ws] [[tsp [sec nsec]]|]];
    cbv beta iota in H;
    (match type of H with context [if ?b then _ else _] => destruct b end;
     cbv beta iota in H; [injection H as <- _; reflexivity | discriminate H]).
Qed.

Lemma pselect_answer_no_unmodeled : forall reads pa i m,
  ~ pselect_answer reads pa i m Unmodeled.
Proof.
  intros reads pa i m H.
  unfold pselect_answer, bind, choose, pure in H. cbv beta iota in H.
  destruct H as [(x & _ & Hx) | (sel & m1 & evs1 & _ & Hk)]; [discriminate Hx|].
  destruct (pa_ans pa sel) as [[r ws] [[tsp [sec nsec]]|]]; cbv beta iota in Hk.
  - destruct Hk as [(y & _ & Hy) | (rem & m2 & e1 & _ & Hk2)];
      [discriminate Hy | discriminate Hk2].
  - discriminate Hk.
Qed.

Lemma check_pselect_answer_complete : forall pa rd reads i m eff m' evs,
  pa_readback pa rd ->
  pselect_answer reads pa i m (Ok eff m' evs) ->
  check_pselect_answer pa rd reads eff m = CheckOk m' evs.
Proof.
  intros pa rd reads i m eff m' evs Hrd H.
  unfold pselect_answer, bind, choose, pure in H. cbv beta iota in H.
  destruct H as (sel & m1 & evs1 & evs2 & (sel0 & Hsel & Hc) & Hk & ->).
  injection Hc as -> -> ->.
  destruct (pa_ans pa sel0) as [[r ws] [[tsp [sec nsec]]|]] eqn:Ha;
    cbv beta iota in Hk.
  - destruct Hk as (rem & m2 & e1 & e2 & (rem0 & Hrem & Hc2) & Hk2 & ->).
    injection Hc2 as -> -> ->.
    injection Hk2 as -> -> ->.
    pose proof (Hrd sel0 [(tsp, rem0)] Hsel) as E.
    rewrite Ha in E. cbn [fst snd] in E.
    cbn [app]. unfold check_pselect_answer, with_copyins.
    cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
    cbv beta iota.
    rewrite access_ranges_eqb_refl. cbv beta iota.
    rewrite E, Ha. cbv beta iota.
    rewrite last_last. cbn [snd].
    rewrite bv_eqb_refl, (proj2 (writes_eqb_eq _ _) eq_refl), Hrem.
    reflexivity.
  - injection Hk as -> -> ->.
    pose proof (Hrd sel0 [] Hsel) as E.
    rewrite Ha in E. cbn [fst snd] in E. rewrite app_nil_r in E.
    cbn [app]. unfold check_pselect_answer, with_copyins.
    cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
    cbv beta iota.
    rewrite access_ranges_eqb_refl. cbv beta iota.
    rewrite E, Ha. cbv beta iota.
    rewrite bv_eqb_refl, (proj2 (writes_eqb_eq _ _) eq_refl).
    reflexivity.
Qed.

(* =========================================================================
   Reading the undecided ends back: the core, then [poll_select_finish]
   ========================================================================= *)

(** The writes of the core's choice 0, which a readback may compare
    against. *)
Definition core_ws0 (c : PselectCore) : list (word * list byte) :=
  match c with PsCoreDone _ ans => snd (ans 0%Z) | _ => [] end.

(** A readback [rd2], given the choice-0 writes, returns the choice that
    made the core's writes. *)
Definition core_readback (c : PselectCore)
    (rd2 : list (word * list byte) -> list (word * list byte) -> Z) : Prop :=
  match c with
  | PsCoreDone und ans =>
      forall sel e, Z.land und sel = sel ->
        Z.land und (rd2 (snd (ans 0%Z)) (snd (ans sel) ++ e)) = sel
  | _ => True
  end.

(** [pselect_finish] keeps the core's choices and writes, and only ever
    appends to them. *)
Lemma finish_readback : forall i tsp tmo c pa rd2,
  core_readback c rd2 ->
  pselect_finish i tsp tmo c = Some pa ->
  pa_readback pa (rd2 (core_ws0 c)).
Proof.
  intros i tsp tmo c pa rd2 Hc H.
  destruct c as [| e0 | und ans]; unfold pselect_finish in H.
  - discriminate H.
  - destruct tmo as [| | | | sec nsec]; cbv beta iota in H;
      try (unfold pselect_err in H; injection H as <-;
           apply pa_readback_und0; reflexivity).
    destruct (writes_all_writable i [(tsp, pselect_timespec_zero)]);
      cbv beta iota in H; [|discriminate H].
    injection H as <-. apply pa_readback_und0. reflexivity.
  - cbn [core_ws0 core_readback] in *.
    destruct (ans 0%Z) as [r0 ws0] eqn:H0.
    cbv beta iota in H.
    destruct tmo as [| | | | sec nsec]; cbv beta iota in H; try discriminate H.
    + destruct (r0 =? 0)%Z; cbv beta iota in H; [discriminate H|].
      destruct (writes_all_writable i ws0); cbv beta iota in H; [|discriminate H].
      injection H as <-. unfold pa_readback. intros sel extra Hs.
      cbn [pa_und pa_ans] in *.
      pose proof (Hc sel extra Hs) as E.
      destruct (ans sel) as [r ws] eqn:Hsel. cbv beta iota.
      cbn [fst snd] in E |- *. exact E.
    + destruct (writes_all_writable i ws0); cbv beta iota in H; [|discriminate H].
      injection H as <-. unfold pa_readback. intros sel extra Hs.
      cbn [pa_und pa_ans] in *.
      pose proof (Hc sel extra Hs) as E.
      destruct (ans sel) as [r ws] eqn:Hsel. cbv beta iota.
      cbn [fst snd] in E |- *. exact E.
    + destruct (writes_all_writable i (ws0 ++ [(tsp, pselect_timespec_zero)]));
        cbv beta iota in H; [|discriminate H].
      injection H as <-. unfold pa_readback. intros sel extra Hs.
      cbn [pa_und pa_ans] in *.
      pose proof (Hc sel ([(tsp, pselect_timespec_zero)] ++ extra) Hs) as E1.
      pose proof (Hc sel extra Hs) as E2.
      destruct (ans sel) as [r ws] eqn:Hsel. cbv beta iota.
      cbn [fst snd] in E1, E2 |- *.
      destruct (r =? 0)%Z; cbv beta iota; cbn [fst snd].
      * rewrite <- app_assoc. exact E1.
      * exact E2.
Qed.

(* -------------------------------------------------- byte decoding *)

Lemma word_range64 : forall w : word, (0 <= bv_unsigned w < 2 ^ 64)%Z.
Proof.
  intro w. pose proof (bv_unsigned_in_range _ w) as H.
  unfold bv_modulus in H. change (Z.of_N 64) with 64%Z in H. exact H.
Qed.

Local Lemma extract_byte : forall (v : word) (s : N) (z : Z),
  z = Z.shiftr (bv_unsigned v) (Z.of_N s) -> bv_extract s 8 v = Z_to_bv 8 z.
Proof.
  intros v s z ->. apply bv_eq.
  rewrite bv_extract_unsigned, Z_to_bv_unsigned. reflexivity.
Qed.

(** [word_le8] and [word_le2] are [Z_to_le_bytes] of the value, so
    [bytes_le_to_Z] reads them back. *)
Lemma word_le8_spec : forall v : word, word_le8 v = Z_to_le_bytes 8 (bv_unsigned v).
Proof.
  intro v. unfold word_le8. cbn [Z_to_le_bytes].
  rewrite !Z.shiftr_shiftr by lia.
  repeat (apply f_equal2; [apply extract_byte; reflexivity|]).
  reflexivity.
Qed.

Lemma word_le2_spec : forall v : word, word_le2 v = Z_to_le_bytes 2 (bv_unsigned v).
Proof.
  intro v. unfold word_le2. cbn [Z_to_le_bytes].
  repeat (apply f_equal2; [apply extract_byte; reflexivity|]).
  reflexivity.
Qed.

Lemma bytes_le_to_Z_word_le8 : forall v : word,
  bytes_le_to_Z (word_le8 v) = bv_unsigned v.
Proof.
  intro v. rewrite word_le8_spec.
  pose proof (word_range64 v) as Hv.
  rewrite bytes_le_to_Z_of_le_bytes by lia.
  change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z.
  apply Z.mod_small. exact Hv.
Qed.

Lemma bytes_le_to_Z_word_le2 : forall v : word,
  bytes_le_to_Z (word_le2 v) = (bv_unsigned v mod 2 ^ 16)%Z.
Proof.
  intro v. rewrite word_le2_spec.
  pose proof (word_range64 v) as Hv.
  rewrite bytes_le_to_Z_of_le_bytes by lia.
  reflexivity.
Qed.

(** Two [revents] below 2^16 are written as the same two bytes only if
    they are equal. *)
Lemma word_le2_inj : forall a b, (0 <= a < 2 ^ 16)%Z -> (0 <= b < 2 ^ 16)%Z ->
  word_le2 (Z_to_bv 64 a) = word_le2 (Z_to_bv 64 b) -> a = b.
Proof.
  intros a b Ha Hb H.
  assert (Hlt : (2 ^ 16 < 2 ^ 64)%Z) by (compute; reflexivity).
  apply (f_equal bytes_le_to_Z) in H.
  rewrite !bytes_le_to_Z_word_le2, !Z_to_bv_unsigned in H.
  unfold bv_wrap, bv_modulus in H. change (Z.of_N 64) with 64%Z in H.
  rewrite (Z.mod_small a (2 ^ 64)), (Z.mod_small b (2 ^ 64)) in H by lia.
  rewrite (Z.mod_small a (2 ^ 16)), (Z.mod_small b (2 ^ 16)) in H by lia.
  exact H.
Qed.

Lemma land_bound : forall k w x, (0 <= k)%Z -> (0 <= w < 2 ^ k)%Z ->
  (0 <= Z.land w x < 2 ^ k)%Z.
Proof.
  intros k w x Hk Hw.
  assert (E : Z.land w x = (Z.land w x mod 2 ^ k)%Z).
  { rewrite <- Z.land_ones by exact Hk.
    rewrite <- Z.land_assoc, (Z.land_comm x (Z.ones k)), Z.land_assoc.
    rewrite Z.land_ones by exact Hk. rewrite Z.mod_small by exact Hw.
    reflexivity. }
  rewrite E. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

(* -------------------------------------------------- pselect6 *)

(** Whether [set_fd_set] writes the set at [p] back. *)
Definition set_written (n : Z) (p : word) : bool :=
  pselect_touches_sets n && negb (w_is0 p).

(** Take the word at the head of [ws] when the set is written ([b]),
    else nothing. *)
Definition take_word (b : bool) (ws : list (word * list byte))
    : Z * list (word * list byte) :=
  if b then match ws with
            | (_, bs) :: rest => (bytes_le_to_Z bs, rest)
            | [] => (0%Z, [])
            end
  else (0%Z, ws).

(** The three result words a pselect6 effect writes, in [inp], [outp],
    [exp] order, each 0 where the set is not written back. *)
Definition pselect6_words (n32 inp outp exp : word) (ws : list (word * list byte))
    : Z * Z * Z :=
  let n := nfds_signed n32 in
  let ti := take_word (set_written n inp) ws in
  let to := take_word (set_written n outp) (snd ti) in
  let tx := take_word (set_written n exp) (snd to) in
  (fst ti, fst to, fst tx).

(** pselect6's readback: the descriptors whose result bits differ
    between the words written and the words choice 0 writes ([ws0]). *)
Definition pselect6_readback (n32 inp outp exp : word)
    (ws0 ws : list (word * list byte)) : Z :=
  let w0 := pselect6_words n32 inp outp exp ws0 in
  let w1 := pselect6_words n32 inp outp exp ws in
  Z.lor (Z.lxor (fst (fst w0)) (fst (fst w1)))
    (Z.lor (Z.lxor (snd (fst w0)) (snd (fst w1))) (Z.lxor (snd w0) (snd w1))).

Definition pselect6_rd (i : SyscallInput) (m : Model) (n32 inp outp exp : word)
    : list (word * list byte) -> Z :=
  pselect6_readback n32 inp outp exp (core_ws0 (pselect_core i m n32 inp outp exp)).

Definition ps_slot (b : bool) (a : Z) : Z :=
  if b then bytes_le_to_Z (word_le8 (Z_to_bv 64 a)) else 0%Z.

Lemma pselect6_words_eq : forall n32 inp outp exp a b c e,
  pselect6_words n32 inp outp exp
    ((fd_set_writeback inp (nfds_signed n32) (Z_to_bv 64 a)
      ++ fd_set_writeback outp (nfds_signed n32) (Z_to_bv 64 b)
      ++ fd_set_writeback exp (nfds_signed n32) (Z_to_bv 64 c)) ++ e)
  = (ps_slot (set_written (nfds_signed n32) inp) a,
     ps_slot (set_written (nfds_signed n32) outp) b,
     ps_slot (set_written (nfds_signed n32) exp) c).
Proof.
  intros. unfold pselect6_words. cbv zeta.
  unfold set_written, fd_set_writeback, ps_slot.
  destruct (pselect_touches_sets (nfds_signed n32)), (w_is0 inp), (w_is0 outp),
    (w_is0 exp); reflexivity.
Qed.

Lemma pselect6_words_eq0 : forall n32 inp outp exp a b c,
  pselect6_words n32 inp outp exp
    (fd_set_writeback inp (nfds_signed n32) (Z_to_bv 64 a)
     ++ fd_set_writeback outp (nfds_signed n32) (Z_to_bv 64 b)
     ++ fd_set_writeback exp (nfds_signed n32) (Z_to_bv 64 c))
  = (ps_slot (set_written (nfds_signed n32) inp) a,
     ps_slot (set_written (nfds_signed n32) outp) b,
     ps_slot (set_written (nfds_signed n32) exp) c).
Proof.
  intros. pose proof (pselect6_words_eq n32 inp outp exp a b c []) as E.
  rewrite app_nil_r in E. exact E.
Qed.

(** A set that is not written back was imported as the zero word, so
    nothing in it is asked. *)
Lemma unwritten_set_zero : forall mp p n r,
  read_fd_set mp p n = Some r -> set_written n p = false ->
  bv_unsigned (fd_set_scanned r n) = 0%Z.
Proof.
  intros mp p n r H Hw. unfold read_fd_set in H. unfold set_written in Hw.
  destruct (pselect_touches_sets n); cbn [negb andb] in H, Hw.
  - destruct (w_is0 p); cbn [negb] in Hw; [|discriminate Hw].
    cbv beta iota in H. injection H as <-.
    unfold fd_set_scanned. rewrite bv_and_unsigned, !Z_to_bv_unsigned. reflexivity.
  - cbv beta iota in H. injection H as <-.
    unfold fd_set_scanned. rewrite bv_and_unsigned, !Z_to_bv_unsigned. reflexivity.
Qed.

(** A written result word is the word read back. *)
Lemma slot_value : forall b w, (b = false -> w = 0%Z) -> (0 <= w < 2 ^ 64)%Z ->
  forall x, ps_slot b (Z.land w x) = Z.land w x.
Proof.
  intros b w Hb Hw x. unfold ps_slot. destruct b.
  - rewrite bytes_le_to_Z_word_le8, Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64%Z.
    apply Z.mod_small. apply land_bound; [lia | exact Hw].
  - rewrite (Hb eq_refl), Z.land_0_l. reflexivity.
Qed.

(** The bit identity behind pselect6's readback: where the descriptors in
    [sel] report [hi] and the rest [lo], the words differ from choice 0's
    exactly at the undecided descriptors in [sel]. *)
Lemma select_readback_bits : forall wi wo wx il ih ol oh xl xh sel,
  Z.land (Z.lor (Z.land wi (Z.lxor il ih))
            (Z.lor (Z.land wo (Z.lxor ol oh)) (Z.land wx (Z.lxor xl xh)))) sel = sel ->
  Z.land (Z.lor (Z.land wi (Z.lxor il ih))
            (Z.lor (Z.land wo (Z.lxor ol oh)) (Z.land wx (Z.lxor xl xh))))
    (Z.lor (Z.lxor (Z.land wi (select_pick il ih 0)) (Z.land wi (select_pick il ih sel)))
       (Z.lor (Z.lxor (Z.land wo (select_pick ol oh 0)) (Z.land wo (select_pick ol oh sel)))
          (Z.lxor (Z.land wx (select_pick xl xh 0)) (Z.land wx (select_pick xl xh sel)))))
  = sel.
Proof.
  intros wi wo wx il ih ol oh xl xh sel Hsel.
  transitivity
    (Z.land (Z.lor (Z.land wi (Z.lxor il ih))
               (Z.lor (Z.land wo (Z.lxor ol oh)) (Z.land wx (Z.lxor xl xh)))) sel);
    [|exact Hsel].
  apply Z.bits_inj'. intros j Hj. unfold select_pick.
  repeat first [ rewrite Z.land_spec | rewrite Z.lor_spec | rewrite Z.lxor_spec
               | rewrite Z.testbit_0_l | rewrite (Z.lnot_spec _ j Hj) ].
  destruct (Z.testbit wi j), (Z.testbit wo j), (Z.testbit wx j),
    (Z.testbit il j), (Z.testbit ih j), (Z.testbit ol j), (Z.testbit oh j),
    (Z.testbit xl j), (Z.testbit xh j), (Z.testbit sel j); reflexivity.
Qed.

Lemma pselect_core_readback : forall i m n32 inp outp exp,
  core_readback (pselect_core i m n32 inp outp exp) (pselect6_readback n32 inp outp exp).
Proof.
  intros i m n32 inp outp exp.
  destruct (pselect_core i m n32 inp outp exp) as [| e0 | und ans] eqn:H;
    try exact I.
  cbn [core_readback]. intros sel e Hsel.
  unfold pselect_core in H. cbv zeta in H.
  destruct (nfds_signed n32 <? 0)%Z; cbv beta iota in H; [discriminate H|].
  destruct (pselect_nfds_max <? nfds_signed n32)%Z; cbv beta iota in H;
    [discriminate H|].
  destruct (read_fd_set (in_mem i) inp (nfds_signed n32)) as [rin|] eqn:Hi;
    cbv beta iota in H; [|discriminate H].
  destruct (read_fd_set (in_mem i) outp (nfds_signed n32)) as [rout|] eqn:Ho;
    cbv beta iota in H; [|discriminate H].
  destruct (read_fd_set (in_mem i) exp (nfds_signed n32)) as [rex|] eqn:Hx;
    cbv beta iota in H; [|discriminate H].
  match type of H with context [if negb ?b then _ else _] => destruct b end;
    cbn [negb] in H; [|discriminate H].
  match type of H with context [select_scan ?f ?a ?k] =>
    destruct (select_scan f a k) as [[[[il ol] xl] [[ih oh] xh]]|] end;
    cbv beta iota in H; [|discriminate H].
  injection H as Hu Ha. subst und ans.
  cbv beta zeta. cbn [fst snd].
  unfold pselect6_readback. cbv zeta.
  rewrite pselect6_words_eq0, pselect6_words_eq. cbn [fst snd].
  pose proof (unwritten_set_zero _ _ _ _ Hi) as Zi.
  pose proof (unwritten_set_zero _ _ _ _ Ho) as Zo.
  pose proof (unwritten_set_zero _ _ _ _ Hx) as Zx.
  pose proof (word_range64 (fd_set_scanned rin (nfds_signed n32))) as Ri.
  pose proof (word_range64 (fd_set_scanned rout (nfds_signed n32))) as Ro.
  pose proof (word_range64 (fd_set_scanned rex (nfds_signed n32))) as Rx.
  rewrite !(slot_value _ _ Zi Ri), !(slot_value _ _ Zo Ro), !(slot_value _ _ Zx Rx).
  apply select_readback_bits. exact Hsel.
Qed.

Lemma pselect6_outcome_readback : forall i m n32 inp outp exp tsp sig pa,
  pselect6_outcome i m n32 inp outp exp tsp sig = Some pa ->
  pa_readback pa (pselect6_rd i m n32 inp outp exp).
Proof.
  intros i m n32 inp outp exp tsp sig pa H.
  unfold pselect6_outcome in H. cbv zeta in H.
  destruct (pselect_sigpack (in_mem i) sig);
    destruct (pselect_timeout (in_mem i) tsp) as [| | | | sec nsec];
    cbv beta iota in H;
    try (unfold pselect_err in H; injection H as <-;
         apply pa_readback_und0; reflexivity);
    try discriminate H;
    (unfold pselect6_rd; eapply finish_readback;
       [apply pselect_core_readback | exact H]).
Qed.

(** pselect6: [Select.pselect6_outcome] names the answers, or [None]
    where the model declines, which is [CheckUnmodeled] here.  An answer
    may hold two choices, both in the effect: the result bits of an
    undecided pair end, read back by [pselect6_rd], and the remaining
    time, read back as the last write; [check_pselect_answer] rebuilds
    the answer for them and compares, the copy-from-user ledger
    [Select.pselect6_reads] included. *)
Definition check_pselect6 (i : SyscallInput) (n32 inp outp exp tsp sig : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match pselect6_outcome i m n32 inp outp exp tsp sig with
  | None => CheckUnmodeled
  | Some pa =>
      check_pselect_answer pa (pselect6_rd i m n32 inp outp exp)
        (pselect6_reads i n32 inp outp exp tsp sig) eff m
  end.

(** Reading the syscall input and the model off the head of a spec. *)
Lemma bind_input_iff {A} (k : SyscallInput -> Sys A) : forall i m o,
  bind input k i m o <-> k i i m o.
Proof.
  intros i m o. unfold bind, input. destruct o as [x m2 evs|]; split.
  - intros (x0 & m1 & evs1 & evs2 & H1 & H2 & H3).
    injection H1 as -> -> ->. cbn in H3. subst evs. exact H2.
  - intros H. exists i, m, [], evs. split; [reflexivity|].
    split; [exact H | reflexivity].
  - intros [H | (x0 & m1 & evs1 & H1 & H2)]; [discriminate|].
    injection H1 as -> -> ->. exact H2.
  - intros H. right. exists i, m, []. split; [reflexivity | exact H].
Qed.

Lemma check_pselect6_sound_ok :
  forall i n32 inp outp exp tsp sig eff m m' evs,
  check_pselect6 i n32 inp outp exp tsp sig eff m = CheckOk m' evs ->
  pselect6_spec n32 inp outp exp tsp sig i m (Ok eff m' evs).
Proof.
  intros i n32 inp outp exp tsp sig eff m m' evs H.
  unfold check_pselect6 in H. unfold pselect6_spec.
  apply bind_input_iff. cbv beta. apply bind_get_model. cbv beta.
  destruct (pselect6_outcome i m n32 inp outp exp tsp sig) as [pa|];
    cbv beta iota; [|discriminate H].
  eapply check_pselect_answer_sound. exact H.
Qed.

Lemma check_pselect6_sound_unmodeled :
  forall i n32 inp outp exp tsp sig eff m,
  check_pselect6 i n32 inp outp exp tsp sig eff m = CheckUnmodeled ->
  pselect6_spec n32 inp outp exp tsp sig i m Unmodeled.
Proof.
  intros i n32 inp outp exp tsp sig eff m H.
  unfold check_pselect6 in H. unfold pselect6_spec.
  apply bind_input_iff. cbv beta. apply bind_get_model. cbv beta.
  destruct (pselect6_outcome i m n32 inp outp exp tsp sig) as [pa|];
    cbv beta iota; [|apply unmodeled_intro].
  exfalso. exact (check_pselect_answer_not_unmodeled _ _ _ _ _ H).
Qed.

Lemma check_pselect6_complete_ok :
  forall i n32 inp outp exp tsp sig eff m m' evs,
  pselect6_spec n32 inp outp exp tsp sig i m (Ok eff m' evs) ->
  check_pselect6 i n32 inp outp exp tsp sig eff m = CheckOk m' evs.
Proof.
  intros i n32 inp outp exp tsp sig eff m m' evs H.
  unfold pselect6_spec in H. apply bind_input_iff in H. cbv beta in H.
  apply bind_get_model in H. cbv beta in H.
  unfold check_pselect6.
  destruct (pselect6_outcome i m n32 inp outp exp tsp sig) as [pa|] eqn:Ho;
    cbv beta iota in H |- *; [|unfold unmodeled in H; discriminate H].
  eapply check_pselect_answer_complete; [|exact H].
  exact (pselect6_outcome_readback _ _ _ _ _ _ _ _ _ Ho).
Qed.

Lemma check_pselect6_complete_unmodeled :
  forall i n32 inp outp exp tsp sig m eff,
  pselect6_spec n32 inp outp exp tsp sig i m Unmodeled ->
  check_pselect6 i n32 inp outp exp tsp sig eff m = CheckUnmodeled.
Proof.
  intros i n32 inp outp exp tsp sig m eff H.
  unfold pselect6_spec in H. apply bind_input_iff in H. cbv beta in H.
  apply bind_get_model in H. cbv beta in H.
  unfold check_pselect6.
  destruct (pselect6_outcome i m n32 inp outp exp tsp sig) as [pa|];
    cbv beta iota in H |- *; [|reflexivity].
  exfalso. exact (pselect_answer_no_unmodeled _ _ _ _ H).
Qed.

(* -------------------------------------------------- ppoll *)

(** What makes an entry's two answers readable apart: equal, or a
    stream-pair end's two masks, both below 2^16, which [word_le2]
    writes apart. *)
Definition cand_ok (c : Z * Z * Z) : Prop :=
  let '(fd, lo, hi) := c in
  lo = hi \/ ((0 <= fd)%Z /\ (0 <= lo < 2 ^ 16)%Z /\ (0 <= hi < 2 ^ 16)%Z).

Ltac destr_ifs :=
  repeat match goal with
  | |- context [if ?b then _ else _] =>
      lazymatch b with
      | true => fail
      | false => fail
      | _ => destruct b
      end
  end.

(** Every bit [unix_poll] can report is below 2^16. *)
Lemma stream_poll_mask_small : forall fds id side st,
  ((0 <=? fst (stream_poll_mask fds id side st))
   && (fst (stream_poll_mask fds id side st) <? 2 ^ 16)
   && (0 <=? snd (stream_poll_mask fds id side st))
   && (snd (stream_poll_mask fds id side st) <? 2 ^ 16))%Z = true.
Proof.
  intros fds id side st. unfold stream_poll_mask. cbv zeta.
  destruct (stream_peer fds id side) as [[x pst]|]; destruct (se_rx st);
    cbv beta iota; destr_ifs; reflexivity.
Qed.

Lemma ppoll_revents_of_ok : forall fds fd ev lo hi,
  ppoll_revents_of fds fd ev = Some (lo, hi) -> cand_ok (fd, lo, hi).
Proof.
  intros fds fd ev lo hi H. unfold ppoll_revents_of in H. cbv zeta in H.
  cbv [cand_ok].
  destruct (fd <? 0)%Z eqn:Hf; cbv beta iota in H.
  { injection H as <- <-. left. reflexivity. }
  apply Z.ltb_ge in Hf.
  destruct (fd_lookup fds (Z_to_bv 64 fd)) as [[]|]; cbv beta iota in H;
    try discriminate H;
    try (injection H as <- <-; left; reflexivity).
  match type of H with context [stream_poll_mask ?a ?b ?c ?d] =>
    pose proof (stream_poll_mask_small a b c d) as B;
    destruct (stream_poll_mask a b c d) as [l h] end.
  cbv beta iota in H. injection H as <- <-.
  cbn [fst snd] in B.
  apply andb_true_iff in B as [B Hh2]. apply andb_true_iff in B as [B Hh1].
  apply andb_true_iff in B as [Hl1 Hl2].
  apply Z.leb_le in Hl1, Hh1. apply Z.ltb_lt in Hl2, Hh2.
  right. split; [exact Hf|].
  split; apply land_bound; lia.
Qed.

Lemma ppoll_revents_ok : forall fds es cs,
  ppoll_revents fds es = Some cs -> Forall cand_ok cs.
Proof.
  intros fds es. induction es as [|[fd ev] es IH]; intros cs H; cbn [ppoll_revents] in H.
  - injection H as <-. constructor.
  - destruct (ppoll_revents_of fds fd ev) as [[lo hi]|] eqn:Hr; [|discriminate H].
    destruct (ppoll_revents fds es) as [cs'|] eqn:Hrest; [|discriminate H].
    injection H as <-. constructor.
    + exact (ppoll_revents_of_ok _ _ _ _ _ Hr).
    + exact (IH cs' eq_refl).
Qed.

Lemma ppoll_scan_cands : forall i m ufds nfds cs,
  ppoll_scan i m ufds nfds = PpScanDone cs -> Forall cand_ok cs.
Proof.
  intros i m ufds nfds cs H. unfold ppoll_scan in H. cbv zeta in H.
  destruct (bv_unsigned (m_nofile m) <? bv_unsigned nfds)%Z; cbv beta iota in H;
    [discriminate H|].
  destruct (ppoll_nfds_max <? bv_unsigned nfds)%Z; cbv beta iota in H;
    [discriminate H|].
  match type of H with context [if ?b then PpScanErr EFAULT else _] => destruct b end;
    cbv beta iota in H; [discriminate H|].
  match type of H with context [read_bytes_map ?a ?b ?c] =>
    destruct (read_bytes_map a b c) as [bs|] end;
    cbv beta iota in H; [|discriminate H].
  match type of H with context [ppoll_revents ?a ?b] =>
    destruct (ppoll_revents a b) as [cs'|] eqn:Hr end;
    cbv beta iota in H; [|discriminate H].
  injection H as <-. exact (ppoll_revents_ok _ _ _ Hr).
Qed.

(** ppoll's readback: for each entry whose two answers differ, bit [fd]
    when the [revents] written are [hi]'s. *)
Fixpoint ppoll_read_sel (cs : list (Z * Z * Z)) (ws : list (word * list byte)) : Z :=
  match cs, ws with
  | (fd, lo, hi) :: cs', (_, bs) :: ws' =>
      Z.lor (if negb (Z.eqb lo hi) && listN_eqb bs (word_le2 (Z_to_bv 64 hi))
             then Z.shiftl 1 fd else 0%Z)
            (ppoll_read_sel cs' ws')
  | _, _ => 0%Z
  end.

Definition ppoll_rd (i : SyscallInput) (m : Model) (ufds nfds : word)
    (ws : list (word * list byte)) : Z :=
  match ppoll_scan i m ufds nfds with
  | PpScanDone cs => ppoll_read_sel cs ws
  | _ => 0%Z
  end.

Lemma land_pow2 : forall fd sel, (0 <= fd)%Z ->
  Z.land (Z.shiftl 1 fd) sel = if Z.testbit sel fd then Z.shiftl 1 fd else 0%Z.
Proof.
  intros fd sel Hfd. rewrite Z.shiftl_1_l.
  destruct (Z.testbit sel fd) eqn:Hs; cbv beta iota; apply Z.bits_inj'; intros j Hj;
    rewrite Z.land_spec; rewrite ?Z.testbit_0_l;
    rewrite (Z.pow2_bits_eqb fd j Hfd);
    destruct (Z.eqb_spec fd j) as [<-|Hne]; rewrite ?Hs; reflexivity.
Qed.

Lemma ppoll_read_sel_pick : forall cs p sel e, Forall cand_ok cs ->
  ppoll_read_sel cs (ppoll_writeback p (ppoll_pick cs sel) ++ e)
  = Z.land (ppoll_undecided cs) sel.
Proof.
  induction cs as [|[[fd lo] hi] cs IH]; intros p sel e Hc.
  - reflexivity.
  - pose proof (Forall_inv Hc) as Hok. pose proof (Forall_inv_tail Hc) as Hcs.
    cbn [ppoll_pick ppoll_writeback ppoll_undecided app ppoll_read_sel].
    rewrite (IH _ sel e Hcs).
    rewrite Z.land_lor_distr_l. f_equal.
    cbv [cand_ok] in Hok.
    destruct (Z.eqb_spec lo hi) as [Heq|Hne].
    + subst hi. cbn [negb andb]. rewrite Z.land_0_l. reflexivity.
    + destruct Hok as [Heq|(Hfd & Hlo & Hhi)]; [contradiction|].
      cbn [negb andb].
      rewrite (land_pow2 fd sel Hfd).
      destruct (Z.testbit sel fd); cbv beta iota.
      * rewrite (proj2 (listN_eqb_eq _ _) eq_refl). reflexivity.
      * destruct (listN_eqb (word_le2 (Z_to_bv 64 lo)) (word_le2 (Z_to_bv 64 hi))) eqn:E;
          [|reflexivity].
        apply listN_eqb_eq in E.
        exfalso. exact (Hne (word_le2_inj lo hi Hlo Hhi E)).
Qed.

Lemma ppoll_core_readback : forall i m ufds nfds,
  core_readback (ppoll_core i m ufds nfds) (fun _ => ppoll_rd i m ufds nfds).
Proof.
  intros i m ufds nfds. unfold ppoll_core.
  destruct (ppoll_scan i m ufds nfds) as [| e0 | cs] eqn:Hs; try exact I.
  cbn [core_readback]. intros sel e Hsel. cbv beta zeta. cbn [fst snd].
  unfold ppoll_rd. rewrite Hs. cbv beta iota.
  rewrite (ppoll_read_sel_pick cs ufds sel e (ppoll_scan_cands _ _ _ _ _ Hs)).
  rewrite land_und_idem. exact Hsel.
Qed.

Lemma writeback_access_readback : forall ufds nfds tmo c rd2,
  core_readback c rd2 -> core_readback (ppoll_writeback_access ufds nfds tmo c) rd2.
Proof.
  intros ufds nfds tmo c rd2 H.
  destruct c as [| e0 | und ans]; [exact I | exact I |].
  unfold ppoll_writeback_access.
  destruct (access_okb ufds (pollfd_bytes * bv_unsigned nfds)); [exact H|].
  destruct tmo; try exact I.
  destruct (fst (ans 0%Z) =? 0)%Z; exact I.
Qed.

Lemma ppoll_outcome_readback : forall i m ufds nfds tsp sig sigsetsize pa,
  ppoll_outcome i m ufds nfds tsp sig sigsetsize = Some pa ->
  pa_readback pa (ppoll_rd i m ufds nfds).
Proof.
  intros i m ufds nfds tsp sig sigsetsize pa H.
  unfold ppoll_outcome in H.
  destruct (pselect_timeout (in_mem i) tsp) as [| | | | sec nsec];
    cbv beta iota in H;
    try (unfold pselect_err in H; injection H as <-;
         apply pa_readback_und0; reflexivity).
  all: destruct (ppoll_sigmask (in_mem i) sig sigsetsize); cbv beta iota in H;
    try (unfold pselect_err in H; injection H as <-;
         apply pa_readback_und0; reflexivity);
    try discriminate H.
  all: eapply (finish_readback i tsp _ _ pa (fun _ => ppoll_rd i m ufds nfds));
         [|exact H].
  all: apply writeback_access_readback; apply ppoll_core_readback.
Qed.

(** ppoll: [Select.ppoll_outcome] names the answers, or [None] where the
    model declines, which is [CheckUnmodeled] here.  Its choices are
    pselect6's, read back the same way: the [revents] of an undecided
    pair end by [ppoll_rd], and the remaining time as the last write.
    The ledger [Select.ppoll_reads] is compared as well. *)
Definition check_ppoll (i : SyscallInput) (ufds nfds tsp sig sigsetsize : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match ppoll_outcome i m ufds nfds tsp sig sigsetsize with
  | None => CheckUnmodeled
  | Some pa =>
      check_pselect_answer pa (ppoll_rd i m ufds nfds)
        (ppoll_reads i m ufds nfds tsp sig sigsetsize) eff m
  end.

Lemma check_ppoll_sound_ok :
  forall i ufds nfds tsp sig sigsetsize eff m m' evs,
  check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckOk m' evs ->
  ppoll_spec ufds nfds tsp sig sigsetsize i m (Ok eff m' evs).
Proof.
  intros i ufds nfds tsp sig sigsetsize eff m m' evs H.
  unfold check_ppoll in H. unfold ppoll_spec.
  apply bind_input_iff. cbv beta. apply bind_get_model. cbv beta.
  destruct (ppoll_outcome i m ufds nfds tsp sig sigsetsize) as [pa|];
    cbv beta iota; [|discriminate H].
  eapply check_pselect_answer_sound. exact H.
Qed.

Lemma check_ppoll_sound_unmodeled :
  forall i ufds nfds tsp sig sigsetsize eff m,
  check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckUnmodeled ->
  ppoll_spec ufds nfds tsp sig sigsetsize i m Unmodeled.
Proof.
  intros i ufds nfds tsp sig sigsetsize eff m H.
  unfold check_ppoll in H. unfold ppoll_spec.
  apply bind_input_iff. cbv beta. apply bind_get_model. cbv beta.
  destruct (ppoll_outcome i m ufds nfds tsp sig sigsetsize) as [pa|];
    cbv beta iota; [|apply unmodeled_intro].
  exfalso. exact (check_pselect_answer_not_unmodeled _ _ _ _ _ H).
Qed.

Lemma check_ppoll_complete_ok :
  forall i ufds nfds tsp sig sigsetsize eff m m' evs,
  ppoll_spec ufds nfds tsp sig sigsetsize i m (Ok eff m' evs) ->
  check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckOk m' evs.
Proof.
  intros i ufds nfds tsp sig sigsetsize eff m m' evs H.
  unfold ppoll_spec in H. apply bind_input_iff in H. cbv beta in H.
  apply bind_get_model in H. cbv beta in H.
  unfold check_ppoll.
  destruct (ppoll_outcome i m ufds nfds tsp sig sigsetsize) as [pa|] eqn:Ho;
    cbv beta iota in H |- *; [|unfold unmodeled in H; discriminate H].
  eapply check_pselect_answer_complete; [|exact H].
  exact (ppoll_outcome_readback _ _ _ _ _ _ _ _ Ho).
Qed.

Lemma check_ppoll_complete_unmodeled :
  forall i ufds nfds tsp sig sigsetsize m eff,
  ppoll_spec ufds nfds tsp sig sigsetsize i m Unmodeled ->
  check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckUnmodeled.
Proof.
  intros i ufds nfds tsp sig sigsetsize m eff H.
  unfold ppoll_spec in H. apply bind_input_iff in H. cbv beta in H.
  apply bind_get_model in H. cbv beta in H.
  unfold check_ppoll.
  destruct (ppoll_outcome i m ufds nfds tsp sig sigsetsize) as [pa|];
    cbv beta iota in H |- *; [|reflexivity].
  exfalso. exact (pselect_answer_no_unmodeled _ _ _ _ H).
Qed.
