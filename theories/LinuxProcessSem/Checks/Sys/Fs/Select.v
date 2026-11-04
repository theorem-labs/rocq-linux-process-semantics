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
   that choice and compares, and the model after the call is the call's
   record [rec] of that choice: so it is a function of the model before
   the call and of the effect.  Soundness needs nothing of [rd]; for
   completeness [rd] must return the choice that made the writes
   ([pa_readback]), which each syscall proves below.
   ========================================================================= *)

Definition check_pselect_answer (pa : PselectAnswers)
    (rd : list (word * list byte) -> Z) (reads : list (word * nat))
    (rec : Z -> Model -> Model) (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | mkEffectU r' ws' [] [] [] ks =>
      if access_ranges_eqb ks reads then
        match pa_ans pa (Z.land (pa_und pa) (rd ws')) with
        | (r, ws, None) =>
            if bv_eqb r' r && writes_eqb ws' ws
            then CheckOk (rec (Z.land (pa_und pa) (rd ws')) m) [] else CheckReject
        | (r, ws, Some (tsp, (sec, nsec))) =>
            if bv_eqb r' r
               && writes_eqb ws' (ws ++ [(tsp, snd (last ws' (tsp, [])))])
               && pselect_remaining_ok sec nsec (snd (last ws' (tsp, [])))
            then CheckOk (rec (Z.land (pa_und pa) (rd ws')) m) [] else CheckReject
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

Lemma check_pselect_answer_sound : forall pa rd reads rec eff m m' evs i,
  check_pselect_answer pa rd reads rec eff m = CheckOk m' evs ->
  pselect_answer reads pa rec i m (Ok eff m' evs).
Proof.
  intros pa rd reads rec [r' ws' zs us cs ks] m m' evs i H.
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
  eapply bind_ok0; [apply modify_ok|]. cbv beta.
  destruct (pa_ans pa (Z.land (pa_und pa) (rd ws'))) as [[r ws] [[tsp [sec nsec]]|]];
    cbv beta iota in H |- *.
  - match type of H with context [if ?b then _ else _] => destruct b eqn:Hg end;
      cbv beta iota in H; [|discriminate H].
    injection H as <- <-.
    apply andb_true_iff in Hg as [Hg Hok]. apply andb_true_iff in Hg as [Hr Hw].
    apply bv_eqb_eq in Hr. apply writes_eqb_eq in Hw. subst r'.
    set (mm := rec (Z.land (pa_und pa) (rd ws')) m).
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

Lemma check_pselect_answer_not_unmodeled : forall pa rd reads rec eff m,
  check_pselect_answer pa rd reads rec eff m <> CheckUnmodeled.
Proof.
  intros pa rd reads rec [r' ws' zs us cs ks] m. unfold check_pselect_answer.
  destruct zs as [|? ?]; [|discriminate].
  destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct (access_ranges_eqb ks reads); [|discriminate].
  destruct (pa_ans pa (Z.land (pa_und pa) (rd ws'))) as [[r ws] [[tsp [sec nsec]]|]];
    cbv beta iota;
    match goal with |- context [if ?b then _ else _] => destruct b end; discriminate.
Qed.

(** The acceptor's model is the call's record of the choice it read
    back. *)
Lemma check_pselect_answer_model : forall pa rd reads rec eff m m' evs,
  check_pselect_answer pa rd reads rec eff m = CheckOk m' evs ->
  m' = rec (Z.land (pa_und pa) (rd (eff_writes eff))) m.
Proof.
  intros pa rd reads rec [r' ws' zs us cs ks] m m' evs H.
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

Lemma pselect_answer_no_unmodeled : forall reads pa rec i m,
  ~ pselect_answer reads pa rec i m Unmodeled.
Proof.
  intros reads pa rec i m H.
  unfold pselect_answer, bind, choose, modify, pure in H. cbv beta iota in H.
  destruct H as [(x & _ & Hx) | (sel & m1 & evs1 & _ & Hk)]; [discriminate Hx|].
  destruct Hk as [Hu | (u & m2 & evs2 & _ & Hk)]; [discriminate Hu|].
  destruct (pa_ans pa sel) as [[r ws] [[tsp [sec nsec]]|]]; cbv beta iota in Hk.
  - destruct Hk as [(y & _ & Hy) | (rem & m3 & e1 & _ & Hk2)];
      [discriminate Hy | discriminate Hk2].
  - discriminate Hk.
Qed.

Lemma check_pselect_answer_complete : forall pa rd reads rec i m eff m' evs,
  pa_readback pa rd ->
  pselect_answer reads pa rec i m (Ok eff m' evs) ->
  check_pselect_answer pa rd reads rec eff m = CheckOk m' evs.
Proof.
  intros pa rd reads rec i m eff m' evs Hrd H.
  unfold pselect_answer, bind, choose, modify, pure in H. cbv beta iota in H.
  destruct H as (sel & m1 & evs1 & evs2 & (sel0 & Hsel & Hc) & Hk & ->).
  injection Hc as -> -> ->.
  destruct Hk as (u & m2 & evs3 & evs4 & Hm & Hk & ->).
  injection Hm as -> -> ->.
  destruct (pa_ans pa sel0) as [[r ws] [[tsp [sec nsec]]|]] eqn:Ha;
    cbv beta iota in Hk.
  - destruct Hk as (rem & m3 & e1 & e2 & (rem0 & Hrem & Hc2) & Hk2 & ->).
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
        (pselect6_reads i n32 inp outp exp tsp sig) (fun _ m0 => m0) eff m
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
  exfalso. exact (check_pselect_answer_not_unmodeled _ _ _ _ _ _ H).
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
  exfalso. exact (pselect_answer_no_unmodeled _ _ _ _ _ H).
Qed.

(* -------------------------------------------------------------------------
   ppoll (73)
   ------------------------------------------------------------------------- *)

(** Where the plan is decided, the acceptor is [check_pselect_answer] on
    the spec's own answer, the ledger [Select.ppoll_reads] included,
    exactly as for pselect6.  Where it reaches [do_poll], the acceptor
    reads the observed [revents] off the effect's writes
    ([ppoll_read_choice]), requires them to be one choice
    ([Select.ppoll_choice_in]), and hands [Select.ppoll_finish]'s answer
    for that choice to [check_pselect_answer], whose only choice left is
    the remaining time.  The model after the call is [Select.ppoll_rec]
    of the choice read: the EPOLLERR each survivor it named has shown.
    The gate [Select.ppoll_all_answered] is the spec's own, so a call the
    spec declines is [CheckUnmodeled] here. *)

(** The [revents] value the 2-byte write [b] stores, among an entry's
    admitted ones [s]. *)
Definition ppoll_read_one (s : list (Z * PpollTag)) (b : list byte) : option Z :=
  option_map fst (find (fun a => listN_eqb (word_le2 (Z_to_bv 64 (fst a))) b) s).

(** The observed choice: one value per entry, read off the writes in
    entry order, or [None] where a write stores no admitted value. *)
Fixpoint ppoll_read_choice (cs : list (Z * list (Z * PpollTag)))
    (ws : list (word * list byte)) : option (list Z) :=
  match cs with
  | [] => Some []
  | (_, s) :: cs' =>
      match ws with
      | [] => None
      | w :: ws' =>
          match ppoll_read_one s (snd w), ppoll_read_choice cs' ws' with
          | Some r, Some rs => Some (r :: rs)
          | _, _ => None
          end
      end
  end.

Definition check_ppoll (i : SyscallInput) (ufds nfds tsp sig sigsetsize : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match ppoll_plan i m ufds nfds tsp sig sigsetsize with
  | PpDecided None => CheckUnmodeled
  | PpDecided (Some pa) =>
      check_pselect_answer pa (fun _ => 0%Z)
        (ppoll_reads i m ufds nfds tsp sig sigsetsize) (fun _ m0 => m0) eff m
  | PpPoll tmo cs =>
      if negb (ppoll_all_answered i ufds nfds tsp tmo cs) then CheckUnmodeled
      else
        match ppoll_read_choice cs (eff_writes eff) with
        | None => CheckReject
        | Some rs =>
            if negb (ppoll_choice_in cs rs) then CheckReject
            else
              match ppoll_finish i ufds nfds tsp tmo rs with
              | None => CheckReject
              | Some pa =>
                  check_pselect_answer pa (fun _ => 0%Z)
                    (ppoll_reads i m ufds nfds tsp sig sigsetsize)
                    (fun _ => ppoll_rec cs rs) eff m
              end
        end
  end.

(** ** What an entry admits *)

(** No two admitted values of an opaque descriptor's entry store the
    same two bytes. *)
Definition ppoll_set_inj (s : list Z) : Prop :=
  forall r r', In r s -> In r' s ->
  listN_eqb (word_le2 (Z_to_bv 64 r')) (word_le2 (Z_to_bv 64 r)) = true -> r' = r.

Local Lemma ppoll_set_inj_single : forall v, ppoll_set_inj [v].
Proof.
  intros v. unfold ppoll_set_inj. intros r r' Hr Hr' _.
  destruct Hr as [<-|[]]; destruct Hr' as [<-|[]]; reflexivity.
Qed.

Local Lemma ppoll_set_inj_eventfd :
  ppoll_set_inj [0%Z; POLLIN; Z.lor POLLIN POLLERR].
Proof.
  unfold ppoll_set_inj. intros r r' Hr Hr' Hb. cbn [In] in Hr, Hr'.
  destruct Hr as [<-|[<-|[<-|[]]]]; destruct Hr' as [<-|[<-|[<-|[]]]];
    try reflexivity; vm_compute in Hb; discriminate Hb.
Qed.

Local Lemma ppoll_set_inj_signalfd : ppoll_set_inj [0%Z; POLLIN].
Proof.
  unfold ppoll_set_inj. intros r r' Hr Hr' Hb. cbn [In] in Hr, Hr'.
  destruct Hr as [<-|[<-|[]]]; destruct Hr' as [<-|[<-|[]]];
    try reflexivity; vm_compute in Hb; discriminate Hb.
Qed.

(** No two alternatives of an entry store the same two bytes unless
    they are the same [revents]. *)
Definition ppoll_alts_inj (s : list (Z * PpollTag)) : Prop :=
  forall a a', In a s -> In a' s ->
  listN_eqb (word_le2 (Z_to_bv 64 (fst a'))) (word_le2 (Z_to_bv 64 (fst a))) = true ->
  fst a' = fst a.

Definition ppoll_is_end (t : PpollTag) : bool :=
  match t with
  | PpEnd _ => true
  | _ => false
  end.

(** What every entry [do_poll] scanned satisfies: it admits some
    [revents], no two of its values are written alike, and it is either
    a stream-pair end's two distinct masks -- [hi] nonzero, the
    descriptor not negative -- or has no stream-pair alternative at
    all. *)
Definition ppoll_alts_ok (c : Z * list (Z * PpollTag)) : Prop :=
  snd c <> [] /\ ppoll_alts_inj (snd c)
  /\ ((exists lo hi, snd c = [(lo, PpEnd false); (hi, PpEnd true)]
                     /\ lo <> hi /\ (0 <= fst c)%Z /\ hi <> 0%Z)
      \/ (forall a, In a (snd c) -> ppoll_is_end (snd a) = false)).

(** What makes a pair's two answers readable apart: equal, or a
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
    destruct (se_reset st); cbv beta iota; destr_ifs; reflexivity.
Qed.

(** [unix_poll]'s [lo] mask is within its [hi] mask: the undecided bits
    are only ever added. *)
Lemma stream_poll_mask_mono : forall fds id side st,
  Z.lor (fst (stream_poll_mask fds id side st)) (snd (stream_poll_mask fds id side st))
  = snd (stream_poll_mask fds id side st).
Proof.
  intros fds id side st. unfold stream_poll_mask. cbv zeta.
  destruct (stream_peer fds id side) as [[x pst]|]; destruct (se_rx st);
    destruct (se_reset st); cbv beta iota; destr_ifs; reflexivity.
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

(** Where an entry's two masks differ, the [hi] one is not 0. *)
Lemma ppoll_revents_of_mono : forall fds fd ev lo hi,
  ppoll_revents_of fds fd ev = Some (lo, hi) -> lo <> hi -> hi <> 0%Z.
Proof.
  intros fds fd ev lo hi H Hne Hh0. apply Hne. unfold ppoll_revents_of in H.
  destruct (fd <? 0)%Z; cbv beta iota in H.
  { injection H as <- <-. reflexivity. }
  destruct (fd_lookup fds (Z_to_bv 64 fd)) as [[]|]; cbv beta iota zeta in H;
    try discriminate H;
    try (injection H as <- <-; reflexivity).
  match type of H with context [stream_poll_mask ?a ?b ?c ?d] =>
    pose proof (stream_poll_mask_mono a b c d) as Hm;
    destruct (stream_poll_mask a b c d) as [l h] end.
  cbn [fst snd] in Hm. cbv beta iota in H. injection H as <- <-.
  rewrite Hh0.
  assert (Hlh : Z.land l h = l).
  { apply Z.bits_inj'. intros n _. rewrite Z.land_spec, <- Hm, Z.lor_spec.
    destruct (Z.testbit l n), (Z.testbit h n); reflexivity. }
  rewrite <- Hlh, <- Z.land_assoc, Hh0, Z.land_0_r. reflexivity.
Qed.

Lemma ppoll_pair_alts_ok : forall fds fd ev lo hi,
  ppoll_revents_of fds fd ev = Some (lo, hi) ->
  ppoll_alts_ok (fd, ppoll_pair_alts (lo, hi)).
Proof.
  intros fds fd ev lo hi H.
  pose proof (ppoll_revents_of_ok _ _ _ _ _ H) as Hc. cbv [cand_ok] in Hc.
  unfold ppoll_pair_alts, ppoll_alts_ok. cbv beta iota. cbn [fst snd].
  destruct (Z.eqb_spec lo hi) as [<-|Hne].
  - split; [discriminate|]. split.
    + intros a a' Ha Ha' _. cbn [In] in Ha, Ha'.
      destruct Ha as [<-|[]]; destruct Ha' as [<-|[]]; reflexivity.
    + right. intros a Ha. cbn [In] in Ha. destruct Ha as [<-|[]]. reflexivity.
  - destruct Hc as [Heq|(Hfd & Hlo & Hhi)]; [contradiction|].
    split; [discriminate|]. split.
    + intros a a' Ha Ha' Hb. apply listN_eqb_eq in Hb. cbn [In] in Ha, Ha'.
      destruct Ha as [<-|[<-|[]]]; destruct Ha' as [<-|[<-|[]]]; cbn [fst] in Hb |- *;
        first [ reflexivity
              | exact (word_le2_inj _ _ Hhi Hlo Hb)
              | exact (word_le2_inj _ _ Hlo Hhi Hb) ].
    + left. exists lo, hi. split; [reflexivity|]. split; [exact Hne|].
      split; [exact Hfd|]. exact (ppoll_revents_of_mono _ _ _ _ _ H Hne).
Qed.

Local Lemma ppoll_opaque_revents_ok : forall m o ev l,
  ppoll_opaque_revents m o ev = Some l -> l <> [] /\ ppoll_set_inj l.
Proof.
  intros m o ev l H. unfold ppoll_opaque_revents in H.
  destruct o as [p|p|fl|h|fl pos|mask fl]; cbv iota in H; try discriminate H.
  - (* an eventfd *)
    destruct (Z.eqb ev POLLIN); cbv iota in H; [|discriminate H].
    injection H as <-. split; [discriminate | apply ppoll_set_inj_eventfd].
  - (* a signalfd *)
    destruct (negb (Z.eqb ev POLLIN)); cbv iota in H; [discriminate H|].
    destruct (signalfd_other_may_pend mask m); cbv iota in H; [discriminate H|].
    destruct (signalfd_sigchld_may_pend mask m); cbv iota in H; injection H as <-;
      (split; [discriminate|]); [apply ppoll_set_inj_signalfd | apply ppoll_set_inj_single].
Qed.

Lemma ppoll_alts_of_ok : forall m fd ev s,
  ppoll_alts_of m fd ev = Some s -> ppoll_alts_ok (fd, s).
Proof.
  intros m fd ev s H. unfold ppoll_alts_of in H.
  assert (Hpair : option_map ppoll_pair_alts (ppoll_revents_of (m_fds m) fd ev) = Some s ->
                  ppoll_alts_ok (fd, s)).
  { intros Hp. destruct (ppoll_revents_of (m_fds m) fd ev) as [[lo hi]|] eqn:Hr;
      cbn [option_map] in Hp; [|discriminate Hp].
    injection Hp as <-. exact (ppoll_pair_alts_ok _ _ _ _ _ Hr). }
  destruct (fd <? 0)%Z; [exact (Hpair H)|].
  destruct (fd_lookup (m_fds m) (Z_to_bv 64 fd)) as [[]|]; try exact (Hpair H).
  (* an opaque descriptor *)
  match type of H with context [ppoll_opaque_revents ?m0 ?o0 ?e0] =>
    destruct (ppoll_opaque_revents m0 o0 e0) as [l|] eqn:Ho end;
    cbn [option_map] in H; [|discriminate H].
  injection H as <-. destruct (ppoll_opaque_revents_ok _ _ _ _ Ho) as [Hne Hinj].
  unfold ppoll_alts_ok. cbn [fst snd]. split; [|split].
  - destruct l as [|z l]; [contradiction|]. cbn [map]. discriminate.
  - intros a a' Ha Ha' Hb. apply in_map_iff in Ha as (r & <- & Hr).
    apply in_map_iff in Ha' as (r' & <- & Hr'). cbn [fst] in Hb |- *.
    exact (Hinj r r' Hr Hr' Hb).
  - right. intros a Ha. apply in_map_iff in Ha as (r & <- & _). reflexivity.
Qed.

Lemma ppoll_entries_alts_ok : forall m es cs,
  ppoll_entries m es = Some cs -> Forall ppoll_alts_ok cs.
Proof.
  intros m. induction es as [|[fd ev] es IH]; intros cs H; cbn [ppoll_entries] in H.
  - injection H as <-. constructor.
  - destruct (ppoll_alts_of m fd ev) as [s|] eqn:Hs; [|discriminate H].
    destruct (ppoll_entries m es) as [cs'|] eqn:Hrest; [|discriminate H].
    injection H as <-. constructor.
    + exact (ppoll_alts_of_ok _ _ _ _ Hs).
    + exact (IH cs' eq_refl).
Qed.

Lemma ppoll_scan_alts_ok : forall i m ufds nfds cs,
  ppoll_scan i m ufds nfds = PpScanDone cs -> Forall ppoll_alts_ok cs.
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
  match type of H with context [ppoll_entries ?a ?b] =>
    destruct (ppoll_entries a b) as [cs'|] eqn:Hr end;
    cbv beta iota in H; [|discriminate H].
  injection H as <-. exact (ppoll_entries_alts_ok _ _ _ Hr).
Qed.

Lemma ppoll_plan_alts_ok : forall i m ufds nfds tsp sig sigsetsize tmo cs,
  ppoll_plan i m ufds nfds tsp sig sigsetsize = PpPoll tmo cs ->
  Forall ppoll_alts_ok cs.
Proof.
  intros i m ufds nfds tsp sig sigsetsize tmo cs H.
  destruct (ppoll_plan_poll _ _ _ _ _ _ _ _ _ H) as [Hs _].
  exact (ppoll_scan_alts_ok _ _ _ _ _ Hs).
Qed.

(** ** Choices of one entry *)

Local Lemma tag_of_some : forall s r t,
  ppoll_tag_of s r = Some t -> exists a, In a s /\ fst a = r /\ snd a = t.
Proof.
  intros s r t H. unfold ppoll_tag_of in H.
  destruct (find (fun a => Z.eqb (fst a) r) s) as [a|] eqn:E;
    cbn [option_map] in H; [|discriminate H].
  injection H as <-. apply find_some in E as [Hin Heq]. apply Z.eqb_eq in Heq.
  exists a. split; [exact Hin | split; [exact Heq | reflexivity]].
Qed.

Local Lemma tag_of_in : forall s a, In a s ->
  exists b, ppoll_tag_of s (fst a) = Some (snd b) /\ In b s.
Proof.
  intros s a Hin. unfold ppoll_tag_of.
  destruct (find (fun b => Z.eqb (fst b) (fst a)) s) as [b|] eqn:Ef.
  - apply find_some in Ef as [Hb _]. exists b. split; [reflexivity | exact Hb].
  - exfalso. eapply find_none in Ef; [|exact Hin]. cbv beta in Ef.
    rewrite Z.eqb_refl in Ef. discriminate Ef.
Qed.

Local Lemma choice_at_admitted : forall sel fd s cs r rs,
  ppoll_choice_at sel ((fd, s) :: cs) (r :: rs) = true ->
  (exists a, In a s /\ fst a = r) /\ ppoll_choice_at sel cs rs = true.
Proof.
  intros sel fd s cs r rs H. cbn [ppoll_choice_at] in H.
  apply andb_true_iff in H as [H1 H2]. split; [|exact H2].
  destruct (ppoll_tag_of s r) as [t|] eqn:E; [|discriminate H1].
  destruct (tag_of_some _ _ _ E) as (a & Hin & Ha & _).
  exists a. split; [exact Hin | exact Ha].
Qed.

Local Lemma is_hi_end : forall t, ppoll_is_hi t = true -> ppoll_is_end t = true.
Proof. intros [| |[]] H; first [reflexivity | discriminate H]. Qed.

Local Lemma least_of_in : forall s, s <> [] ->
  exists a, In a s /\ ppoll_least_of s = fst a.
Proof.
  intros s Hne. unfold ppoll_least_of.
  destruct (existsb (fun a => Z.eqb (fst a) 0) s) eqn:E.
  - apply existsb_exists in E as (a & Hin & Ha). cbv beta in Ha.
    apply Z.eqb_eq in Ha. exists a. split; [exact Hin | symmetry; exact Ha].
  - destruct s as [|a s]; [contradiction|].
    exists a. split; [left; reflexivity | reflexivity].
Qed.

Local Lemma most_of_in : forall s, s <> [] ->
  exists a, In a s /\ ppoll_most_of s = fst a.
Proof.
  intros s Hne. unfold ppoll_most_of.
  destruct (find (fun a => ppoll_is_hi (snd a)) s) as [a|] eqn:Eh.
  { apply find_some in Eh as [Ha _]. exists a. split; [exact Ha | reflexivity]. }
  destruct (find (fun a => negb (Z.eqb (fst a) 0)) s) as [a|] eqn:En.
  { apply find_some in En as [Ha _]. exists a. split; [exact Ha | reflexivity]. }
  destruct s as [|a s]; [contradiction|].
  exists a. split; [left; reflexivity | reflexivity].
Qed.

(** The LEAST choice of an entry is never a stream-pair end's [hi]. *)
Local Lemma least_of_tag : forall fd s, ppoll_alts_ok (fd, s) ->
  exists t, ppoll_tag_of s (ppoll_least_of s) = Some t /\ t <> PpEnd true.
Proof.
  intros fd s Hok. unfold ppoll_alts_ok in Hok. cbn [fst snd] in Hok.
  destruct Hok as (Hne & _ & [(lo & hi & -> & _ & _ & Hhi) | Hno]).
  - assert (E : ppoll_least_of [(lo, PpEnd false); (hi, PpEnd true)] = lo).
    { unfold ppoll_least_of. cbn [existsb fst map hd].
      destruct (Z.eqb_spec lo 0) as [->|_]; [reflexivity|].
      rewrite (proj2 (Z.eqb_neq _ _) Hhi). reflexivity. }
    rewrite E. exists (PpEnd false). split; [|discriminate].
    unfold ppoll_tag_of. cbn [find fst]. rewrite Z.eqb_refl. reflexivity.
  - destruct (least_of_in s Hne) as (a & Hin & ->).
    destruct (tag_of_in s a Hin) as (b & -> & Hb).
    exists (snd b). split; [reflexivity|]. intros E.
    pose proof (Hno b Hb) as Hb'. rewrite E in Hb'. cbn [ppoll_is_end] in Hb'.
    discriminate Hb'.
Qed.

(** The MOST choice of an entry is a stream-pair end's [hi] exactly
    where the entry has one. *)
Local Lemma most_of_tag : forall fd s, ppoll_alts_ok (fd, s) ->
  exists t, ppoll_tag_of s (ppoll_most_of s) = Some t
    /\ ((t = PpEnd true /\ (0 <= fd)%Z
         /\ existsb (fun a => ppoll_is_hi (snd a)) s = true)
        \/ (ppoll_is_end t = false
            /\ existsb (fun a => ppoll_is_hi (snd a)) s = false)).
Proof.
  intros fd s Hok. unfold ppoll_alts_ok in Hok. cbn [fst snd] in Hok.
  destruct Hok as (Hne & _ & [(lo & hi & -> & Hlh & Hfd & _) | Hno]).
  - exists (PpEnd true). split.
    + unfold ppoll_most_of, ppoll_tag_of. cbn [find ppoll_is_hi snd fst].
      rewrite (proj2 (Z.eqb_neq _ _) Hlh), Z.eqb_refl. reflexivity.
    + left. split; [reflexivity|]. split; [exact Hfd | reflexivity].
  - destruct (most_of_in s Hne) as (a & Hin & ->).
    destruct (tag_of_in s a Hin) as (b & -> & Hb).
    exists (snd b). split; [reflexivity|]. right. split; [exact (Hno b Hb)|].
    destruct (existsb (fun a0 => ppoll_is_hi (snd a0)) s) eqn:E; [|reflexivity].
    apply existsb_exists in E as (c & Hc & Hh).
    pose proof (is_hi_end _ Hh) as Hc'. rewrite (Hno c Hc) in Hc'. discriminate Hc'.
Qed.

Local Lemma most_of_nonzero : forall fd s r, ppoll_alts_ok (fd, s) ->
  (exists a, In a s /\ fst a = r) -> r <> 0%Z -> ppoll_most_of s <> 0%Z.
Proof.
  intros fd s r Hok (a & Hin & <-) Hr. unfold ppoll_alts_ok in Hok. cbn [fst snd] in Hok.
  destruct Hok as (_ & _ & [(lo & hi & -> & _ & _ & Hhi) | Hno]).
  - unfold ppoll_most_of. cbn [find ppoll_is_hi snd fst]. exact Hhi.
  - unfold ppoll_most_of.
    destruct (find (fun b => ppoll_is_hi (snd b)) s) as [b|] eqn:Eh.
    + exfalso. apply find_some in Eh as [Hb Hh].
      pose proof (is_hi_end _ Hh) as Hb'. rewrite (Hno b Hb) in Hb'. discriminate Hb'.
    + destruct (find (fun b => negb (Z.eqb (fst b) 0)) s) as [b|] eqn:En.
      * apply find_some in En as [_ Hb]. apply negb_true_iff, Z.eqb_neq in Hb. exact Hb.
      * exfalso. eapply find_none in En; [|exact Hin]. cbv beta in En.
        rewrite (proj2 (Z.eqb_neq _ _) Hr) in En. discriminate En.
Qed.

(** ** What the observed choice is *)

Local Lemma ppoll_read_one_ok : forall s a, ppoll_alts_inj s -> In a s ->
  ppoll_read_one s (word_le2 (Z_to_bv 64 (fst a))) = Some (fst a).
Proof.
  intros s a Hinj Hin. unfold ppoll_read_one.
  destruct (find (fun b => listN_eqb (word_le2 (Z_to_bv 64 (fst b)))
                                     (word_le2 (Z_to_bv 64 (fst a)))) s) as [b|] eqn:Ef.
  - apply find_some in Ef as [Hb Heq]. cbn [option_map]. f_equal.
    exact (Hinj a b Hin Hb Heq).
  - exfalso. eapply find_none in Ef; [|exact Hin]. cbv beta in Ef.
    rewrite (proj2 (listN_eqb_eq _ _) eq_refl) in Ef. discriminate Ef.
Qed.

(** The choice read off a choice's write-back is that choice. *)
Local Lemma ppoll_read_choice_writeback : forall sel cs rs p x,
  Forall ppoll_alts_ok cs -> ppoll_choice_at sel cs rs = true ->
  ppoll_read_choice cs (ppoll_writeback p rs ++ x) = Some rs.
Proof.
  intros sel. induction cs as [|[fd s] cs IH]; intros rs p x Hok Hc.
  - destruct rs; [reflexivity | discriminate Hc].
  - destruct rs as [|r rs]; [discriminate Hc|].
    apply choice_at_admitted in Hc as [(a & Hin & <-) Hc].
    destruct (Forall_inv Hok) as (_ & Hinj & _).
    cbn [ppoll_writeback app ppoll_read_choice snd].
    rewrite (IH rs _ x (Forall_inv_tail Hok) Hc).
    rewrite (ppoll_read_one_ok s a Hinj Hin). reflexivity.
Qed.

Local Lemma pselect_effect_writes : forall reads a eff,
  pselect_effect reads a eff -> exists y, eff_writes eff = snd (fst a) ++ y.
Proof.
  intros reads [[r ws] [[t [sec nsec]]|]] eff H; unfold pselect_effect in H;
    cbv beta iota in H.
  - destruct H as (rem & _ & ->). exists [(t, rem)]. reflexivity.
  - subst eff. exists []. rewrite app_nil_r. reflexivity.
Qed.

(** An answered effect at [do_poll] shows the choice that made it. *)
Local Lemma ppoll_poll_writes :
  forall i m ufds nfds tsp sig sigsetsize tmo cs rs pa reads rec eff m' evs,
  ppoll_plan i m ufds nfds tsp sig sigsetsize = PpPoll tmo cs ->
  ppoll_choice_in cs rs = true ->
  ppoll_finish i ufds nfds tsp tmo rs = Some pa ->
  pselect_answer reads pa rec i m (Ok eff m' evs) ->
  ppoll_read_choice cs (eff_writes eff) = Some rs.
Proof.
  intros i m ufds nfds tsp sig sigsetsize tmo cs rs pa reads rec eff m' evs Hp Hc Hf H.
  pose proof (ppoll_choice_in_length _ _ Hc) as Hl.
  apply pselect_answer_iff in H as (sel & eff' & Hsel & He & Ho).
  injection Ho as Heff Hm Hv. subst eff'.
  rewrite (ppoll_finish_und _ _ _ _ _ _ _ Hf), Z.land_0_l in Hsel. subst sel.
  destruct (pselect_effect_writes _ _ _ He) as (y & ->).
  destruct (ppoll_finish_writes _ _ _ _ _ _ _ Hf) as [(x & ->) | (-> & Ha)].
  - rewrite <- app_assoc. unfold ppoll_choice_in in Hc.
    exact (ppoll_read_choice_writeback _ _ _ _ _
             (ppoll_plan_alts_ok _ _ _ _ _ _ _ _ _ Hp) Hc).
  - destruct (ppoll_plan_poll _ _ _ _ _ _ _ _ _ Hp) as [Hs _].
    pose proof (proj2 (ppoll_scan_done _ _ _ _ _ Hs) Ha) as E. subst cs.
    destruct rs as [|r rs]; [reflexivity | discriminate Hl].
Qed.

(** [PpDecided] is injective; stated over variables so that no
    reduction of the answers happens on the way. *)
Lemma ppoll_decided_inj : forall o o', PpDecided o = PpDecided o' -> o = o'.
Proof. intros o o' E. injection E as E. exact E. Qed.

(** A decided answer has no choice but the remaining time. *)
Lemma ppoll_decided_und : forall i m ufds nfds tsp sig sigsetsize pa,
  ppoll_plan i m ufds nfds tsp sig sigsetsize = PpDecided (Some pa) -> pa_und pa = 0%Z.
Proof.
  intros i m ufds nfds tsp sig sigsetsize pa H. unfold ppoll_plan in H.
  destruct (pselect_timeout (in_mem i) tsp) as [| | | | sec nsec]; cbv beta iota in H;
    try (unfold pselect_err, ps_fixed in H; injection H as <-; reflexivity).
  all: destruct (ppoll_sigmask (in_mem i) sig sigsetsize); cbv beta iota in H;
    try (unfold pselect_err, ps_fixed in H; injection H as <-; reflexivity);
    try discriminate H.
  all: destruct (ppoll_scan i m ufds nfds) as [|e|cs]; cbv beta iota in H;
    try discriminate H.
  all: first
    [ exact (pselect_finish_err_und _ _ _ _ _ (ppoll_decided_inj _ _ H))
    | match type of H with
      | context [ppoll_env_deadline ?t ?c] => destruct (ppoll_env_deadline t c)
      end; discriminate H ].
Qed.

(** What [check_ppoll] accepts leaves the model as it was, or records
    one choice at [do_poll]. *)
Lemma check_ppoll_model : forall i ufds nfds tsp sig sigsetsize eff m m' evs,
  check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckOk m' evs ->
  m' = m
  \/ exists tmo cs rs, ppoll_plan i m ufds nfds tsp sig sigsetsize = PpPoll tmo cs
                       /\ m' = ppoll_rec cs rs m.
Proof.
  intros i ufds nfds tsp sig sigsetsize eff m m' evs H.
  unfold check_ppoll in H.
  destruct (ppoll_plan i m ufds nfds tsp sig sigsetsize) as [[pa|]|tmo cs] eqn:Hp;
    cbv beta iota in H.
  - left. apply check_pselect_answer_model in H. exact H.
  - discriminate H.
  - destruct (negb (ppoll_all_answered i ufds nfds tsp tmo cs)); cbv beta iota in H;
      [discriminate H|].
    destruct (ppoll_read_choice cs (eff_writes eff)) as [rs|]; cbv iota in H;
      [|discriminate H].
    destruct (negb (ppoll_choice_in cs rs)); cbv iota in H; [discriminate H|].
    destruct (ppoll_finish i ufds nfds tsp tmo rs) as [pa|]; cbv iota in H;
      [|discriminate H].
    right. exists tmo, cs, rs. split; [reflexivity|].
    apply check_pselect_answer_model in H. exact H.
Qed.

(** ** The four agreement lemmas *)

Lemma check_ppoll_sound_ok :
  forall i ufds nfds tsp sig sigsetsize eff m m' evs,
  check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckOk m' evs ->
  ppoll_spec ufds nfds tsp sig sigsetsize i m (Ok eff m' evs).
Proof.
  intros i ufds nfds tsp sig sigsetsize eff m m' evs H.
  unfold check_ppoll in H. unfold ppoll_spec.
  apply bind_input_iff. cbv beta. apply bind_get_model. cbv beta.
  destruct (ppoll_plan i m ufds nfds tsp sig sigsetsize) as [[pa|]|tmo cs];
    cbv beta iota in H |- *.
  - eapply check_pselect_answer_sound. exact H.
  - discriminate H.
  - destruct (negb (ppoll_all_answered i ufds nfds tsp tmo cs));
      cbv beta iota in H |- *; [discriminate H|].
    destruct (ppoll_read_choice cs (eff_writes eff)) as [rs|]; cbv iota in H;
      [|discriminate H].
    destruct (negb (ppoll_choice_in cs rs)) eqn:Hc; cbv iota in H; [discriminate H|].
    apply negb_false_iff in Hc.
    destruct (ppoll_finish i ufds nfds tsp tmo rs) as [pa|] eqn:Hf; cbv iota in H;
      [|discriminate H].
    apply bind_choose_iff. exists (rs, pa). cbv beta. cbn [fst snd].
    split; [split; [exact Hc | exact Hf]|].
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
  destruct (ppoll_plan i m ufds nfds tsp sig sigsetsize) as [[pa|]|tmo cs];
    cbv beta iota in H |- *.
  - exfalso. exact (check_pselect_answer_not_unmodeled _ _ _ _ _ _ H).
  - apply unmodeled_intro.
  - destruct (negb (ppoll_all_answered i ufds nfds tsp tmo cs));
      cbv beta iota in H |- *; [apply unmodeled_intro|].
    exfalso.
    destruct (ppoll_read_choice cs (eff_writes eff)) as [rs|]; cbv iota in H;
      [|discriminate H].
    destruct (negb (ppoll_choice_in cs rs)); cbv iota in H; [discriminate H|].
    destruct (ppoll_finish i ufds nfds tsp tmo rs) as [pa|]; cbv iota in H;
      [|discriminate H].
    exact (check_pselect_answer_not_unmodeled _ _ _ _ _ _ H).
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
  destruct (ppoll_plan i m ufds nfds tsp sig sigsetsize) as [[pa|]|tmo cs] eqn:Hp;
    cbv beta iota in H |- *.
  - eapply check_pselect_answer_complete; [|exact H].
    apply pa_readback_und0. exact (ppoll_decided_und _ _ _ _ _ _ _ _ Hp).
  - unfold unmodeled in H. cbv beta in H. discriminate H.
  - destruct (negb (ppoll_all_answered i ufds nfds tsp tmo cs));
      cbv beta iota in H |- *; [unfold unmodeled in H; cbv beta in H; discriminate H|].
    apply bind_choose_iff in H. destruct H as ([rs pa] & (Hc & Hf) & H).
    cbn [fst snd] in Hc, Hf, H.
    rewrite (ppoll_poll_writes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp Hc Hf H).
    cbv beta iota. rewrite Hc. cbn [negb]. rewrite Hf. cbv beta iota.
    eapply check_pselect_answer_complete; [|exact H].
    apply pa_readback_und0. exact (ppoll_finish_und _ _ _ _ _ _ _ Hf).
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
  destruct (ppoll_plan i m ufds nfds tsp sig sigsetsize) as [[pa|]|tmo cs];
    cbv beta iota in H |- *.
  - exfalso. exact (pselect_answer_no_unmodeled _ _ _ _ _ H).
  - reflexivity.
  - destruct (negb (ppoll_all_answered i ufds nfds tsp tmo cs));
      cbv beta iota in H |- *; [reflexivity|].
    exfalso. apply bind_choose_iff in H. destruct H as (c & _ & H).
    exact (pselect_answer_no_unmodeled _ _ _ _ _ H).
Qed.

(** ** The gate is exact

    [Select.ppoll_all_answered] tests two choices, the least and the most
    ready, where the spec's reading is about every choice.  These lemmas
    are what make the two the same for every scan result
    ([ppoll_plan_alts_ok]): the gate admits only where EVERY choice is
    answered ([ppoll_all_answered_sound]), so no admissible choice is
    silently dropped, and where every choice is answered the gate admits
    ([ppoll_all_answered_complete]). *)

Local Lemma ppoll_least_length : forall cs, length (ppoll_least cs) = length cs.
Proof. intros cs. unfold ppoll_least. apply length_map. Qed.

Local Lemma ppoll_most_length : forall cs, length (ppoll_most cs) = length cs.
Proof. intros cs. unfold ppoll_most. apply length_map. Qed.

Local Lemma ppoll_least_count : forall sel cs rs,
  ppoll_choice_at sel cs rs = true -> ppoll_count rs = 0%Z ->
  ppoll_count (ppoll_least cs) = 0%Z.
Proof.
  intros sel. unfold ppoll_least.
  induction cs as [|[fd s] cs IH]; intros [|r rs] Hc H0; try discriminate Hc;
    [reflexivity|].
  apply choice_at_admitted in Hc as [(a & Hin & Ha) Hc].
  cbn [ppoll_count] in H0. pose proof (proj1 (ppoll_count_bounds rs)) as Hn.
  destruct (Z.eqb r 0) eqn:Er; cbv iota in H0; [|lia].
  apply Z.eqb_eq in Er. rewrite Er in Ha.
  assert (E : ppoll_least_of s = 0%Z).
  { unfold ppoll_least_of.
    replace (existsb (fun a0 => Z.eqb (fst a0) 0) s) with true; [reflexivity|].
    symmetry. apply existsb_exists. exists a. split; [exact Hin|].
    cbv beta. rewrite Ha. reflexivity. }
  cbn [map snd ppoll_count]. rewrite E, (IH rs Hc) by lia. reflexivity.
Qed.

Local Lemma ppoll_most_count : forall sel cs rs,
  Forall ppoll_alts_ok cs ->
  ppoll_choice_at sel cs rs = true -> ppoll_count rs <> 0%Z ->
  ppoll_count (ppoll_most cs) <> 0%Z.
Proof.
  intros sel. unfold ppoll_most.
  induction cs as [|[fd s] cs IH]; intros [|r rs] Hok Hc H0; try discriminate Hc;
    [exact H0|].
  apply choice_at_admitted in Hc as [Hr Hc].
  cbn [map snd ppoll_count] in H0 |- *.
  pose proof (proj1 (ppoll_count_bounds rs)) as Hn.
  pose proof (proj1 (ppoll_count_bounds (map (fun c => ppoll_most_of (snd c)) cs))) as Hm.
  destruct (Z.eqb r 0) eqn:Er; cbv iota in H0.
  - specialize (IH rs (Forall_inv_tail Hok) Hc ltac:(lia)).
    destruct (Z.eqb (ppoll_most_of s) 0); cbv iota; lia.
  - apply Z.eqb_neq in Er.
    rewrite (proj2 (Z.eqb_neq _ _) (most_of_nonzero fd s r (Forall_inv Hok) Hr Er)).
    cbv iota. lia.
Qed.

Local Lemma ppoll_least_choice : forall cs, Forall ppoll_alts_ok cs ->
  ppoll_choice_in cs (ppoll_least cs) = true.
Proof.
  intros cs Hok. unfold ppoll_choice_in.
  enough (H : ppoll_sel cs (ppoll_least cs) = 0%Z
              /\ ppoll_choice_at 0 cs (ppoll_least cs) = true)
    by (destruct H as [-> H]; exact H).
  revert Hok. unfold ppoll_least.
  induction cs as [|[fd s] cs IH]; intros Hok; [split; reflexivity|].
  destruct (IH (Forall_inv_tail Hok)) as [IH1 IH2].
  destruct (least_of_tag fd s (Forall_inv Hok)) as (t & Ht & Hnt).
  cbn [map snd ppoll_sel ppoll_choice_at]. rewrite Ht, IH1, IH2.
  destruct t as [| |[]]; cbn [ppoll_is_hi];
    [split; reflexivity | split; reflexivity | exfalso; apply Hnt; reflexivity |].
  rewrite Z.testbit_0_l. split; reflexivity.
Qed.

Local Lemma ppoll_sel_most_bit : forall cs fd s,
  Forall ppoll_alts_ok cs -> In (fd, s) cs ->
  existsb (fun a => ppoll_is_hi (snd a)) s = true ->
  Z.testbit (ppoll_sel cs (ppoll_most cs)) fd = true.
Proof.
  unfold ppoll_most.
  induction cs as [|[fd0 s0] cs IH]; intros fd s Hok Hin Hhi; [destruct Hin|].
  cbn [map snd ppoll_sel]. rewrite Z.lor_spec. apply orb_true_iff.
  destruct Hin as [E|Hin].
  - injection E as <- <-. left.
    destruct (most_of_tag fd0 s0 (Forall_inv Hok))
      as (t & Ht & [(-> & Hfd & _) | (_ & Hno)]).
    + rewrite Ht. cbn [ppoll_is_hi]. rewrite Z.shiftl_1_l.
      apply Z.pow2_bits_true. exact Hfd.
    + rewrite Hno in Hhi. discriminate Hhi.
  - right. exact (IH fd s (Forall_inv_tail Hok) Hin Hhi).
Qed.

Local Lemma ppoll_most_choice_at : forall sel cs, Forall ppoll_alts_ok cs ->
  (forall fd s, In (fd, s) cs -> existsb (fun a => ppoll_is_hi (snd a)) s = true ->
     Z.testbit sel fd = true) ->
  ppoll_choice_at sel cs (ppoll_most cs) = true.
Proof.
  intros sel. unfold ppoll_most.
  induction cs as [|[fd s] cs IH]; intros Hok Hb; [reflexivity|].
  cbn [map snd ppoll_choice_at].
  rewrite (IH (Forall_inv_tail Hok) (fun fd' s' H Hh => Hb fd' s' (or_intror H) Hh)),
    andb_true_r.
  destruct (most_of_tag fd s (Forall_inv Hok))
    as (t & Ht & [(-> & Hfd & Hhi) | (Hne & _)]); rewrite Ht; cbv beta iota.
  - rewrite (Hb fd s (or_introl eq_refl) Hhi). reflexivity.
  - destruct t as [| |b]; [reflexivity | reflexivity |].
    cbn [ppoll_is_end] in Hne. discriminate Hne.
Qed.

Local Lemma ppoll_most_choice : forall cs, Forall ppoll_alts_ok cs ->
  ppoll_choice_in cs (ppoll_most cs) = true.
Proof.
  intros cs Hok. unfold ppoll_choice_in.
  apply ppoll_most_choice_at; [exact Hok|].
  intros fd s Hin Hhi. exact (ppoll_sel_most_bit cs fd s Hok Hin Hhi).
Qed.

(** [Select.ppoll_writeback]'s addresses and lengths do not depend on the
    values written, so neither does its writability. *)
Local Lemma ppoll_writeback_writable : forall i p rs rs' x,
  length rs = length rs' ->
  writes_all_writable i (ppoll_writeback p rs ++ x)
  = writes_all_writable i (ppoll_writeback p rs' ++ x).
Proof.
  intros i p rs. revert p.
  induction rs as [|r rs IH]; intros p [|r' rs'] x Hl; try discriminate Hl;
    [reflexivity|].
  cbn [ppoll_writeback app]. unfold writes_all_writable in *.
  cbn [forallb fst snd].
  rewrite (IH _ rs' x) by (cbn [length] in Hl; lia). reflexivity.
Qed.

(** [Select.ppoll_finish] answers or declines a choice by whether its
    count is 0 and by nothing else about it. *)
Local Lemma ppoll_finish_shape : forall i ufds nfds tsp tmo rs rs',
  length rs = length rs' ->
  Z.eqb (ppoll_count rs) 0 = Z.eqb (ppoll_count rs') 0 ->
  ppoll_answers (ppoll_finish i ufds nfds tsp tmo rs)
  = ppoll_answers (ppoll_finish i ufds nfds tsp tmo rs').
Proof.
  intros i ufds nfds tsp tmo rs rs' Hl Hc.
  pose proof (ppoll_writeback_writable i ufds rs rs' [] Hl) as Hw.
  rewrite !app_nil_r in Hw.
  pose proof (ppoll_writeback_writable i ufds rs rs'
                [(tsp, pselect_timespec_zero)] Hl) as Hd.
  rewrite !ppoll_finish_eq.
  destruct (access_okb ufds (pollfd_bytes * bv_unsigned nfds)); destruct tmo;
    rewrite ?Hc, ?Hw, ?Hd; try reflexivity;
    repeat match goal with
           | |- context [if ?b then _ else _] => destruct b
           end;
    reflexivity.
Qed.

Lemma ppoll_all_answered_sound : forall i ufds nfds tsp tmo cs,
  Forall ppoll_alts_ok cs ->
  ppoll_all_answered i ufds nfds tsp tmo cs = true ->
  forall rs, ppoll_choice_in cs rs = true ->
  ppoll_finish i ufds nfds tsp tmo rs <> None.
Proof.
  intros i ufds nfds tsp tmo cs Hok Hg rs Hc.
  unfold ppoll_all_answered in Hg.
  apply Bool.andb_true_iff in Hg as [Hg Hhi].
  apply Bool.andb_true_iff in Hg as [Hg Hlo].
  pose proof (ppoll_choice_in_length _ _ Hc) as Hl.
  pose proof (ppoll_least_length cs) as Hllo.
  pose proof (ppoll_most_length cs) as Hlhi.
  unfold ppoll_choice_in in Hc.
  assert (Ha : ppoll_answers (ppoll_finish i ufds nfds tsp tmo rs) = true).
  { destruct (Z.eqb (ppoll_count rs) 0) eqn:E.
    - apply Z.eqb_eq in E.
      rewrite (ppoll_finish_shape i ufds nfds tsp tmo rs (ppoll_least cs));
        [exact Hlo | lia |].
      rewrite (proj2 (Z.eqb_eq _ _) E),
        (proj2 (Z.eqb_eq _ _) (ppoll_least_count _ _ _ Hc E)).
      reflexivity.
    - apply Z.eqb_neq in E.
      rewrite (ppoll_finish_shape i ufds nfds tsp tmo rs (ppoll_most cs));
        [exact Hhi | lia |].
      rewrite (proj2 (Z.eqb_neq _ _) E),
        (proj2 (Z.eqb_neq _ _) (ppoll_most_count _ _ _ Hok Hc E)).
      reflexivity. }
  unfold ppoll_answers in Ha.
  destruct (ppoll_finish i ufds nfds tsp tmo rs); [discriminate | discriminate Ha].
Qed.

Lemma ppoll_all_answered_complete : forall i ufds nfds tsp tmo cs,
  Forall ppoll_alts_ok cs ->
  (forall rs, ppoll_choice_in cs rs = true ->
     ppoll_finish i ufds nfds tsp tmo rs <> None) ->
  ppoll_all_answered i ufds nfds tsp tmo cs = true.
Proof.
  intros i ufds nfds tsp tmo cs Hok Hall.
  pose proof (ppoll_least_choice _ Hok) as Hlo.
  pose proof (ppoll_most_choice _ Hok) as Hhi.
  unfold ppoll_all_answered. rewrite Hlo, Hhi. cbn [andb].
  destruct (ppoll_finish i ufds nfds tsp tmo (ppoll_least cs)) eqn:E1;
    [|exfalso; exact (Hall _ Hlo E1)].
  destruct (ppoll_finish i ufds nfds tsp tmo (ppoll_most cs)) eqn:E2;
    [|exfalso; exact (Hall _ Hhi E2)].
  reflexivity.
Qed.
