(** * Common.RunSegmentsLift — from a binary's segments to the run's segments.

    A run reads [Run.run_segments segs inp sp mbase], which is [segs]
    followed by the vDSO pair ([Run.vdso_segments]).  The generated
    fetch lemmas of an example ([<name>_code.v]) and its image read-backs
    are stated over the binary's own [segs]; this file carries them to
    [segs ++ vt] for any appended [vt].

    Two facts carry the lift:
    - every reader scans [find_segment] head first, so a hit in [segs]
      is the same hit in [segs ++ vt] ([find_segment_app]): a fetch, a
      load, a writable-view read or a store bound that succeeds over
      [segs] succeeds the same way over [segs ++ vt], whatever [vt] is;
    - neither vDSO segment is executable ([vdso_segments_no_exec]: both
      carry ["r--"]), so every FETCH path answers over [segs ++ vt]
      exactly what it answers over [segs] ([fetch_word_append] and its
      siblings), which is what lifts a whole machine step ([step_app]).

    A step never reads [ms_rom], so a lifted step relates the same two
    states.  A [to_wexit] chain lifts whole ([to_wexit_app]): its write
    node reads the buffer through [ms_read_bytes], the state's own memory
    and rom.  Chains whose syscall nodes read user memory through the
    segment list are stated over the run's list instead.

    The Lean twin is [lean/LinuxProcessSemantics/Common/RunSegmentsLift.lean]. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Common Require Import PropExec CatSim StreamSim WallSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.

(* ========================================================================= *)
(* [find_segment] over an appended list                                       *)
(* ========================================================================= *)

Lemma find_segment_append : forall segs vt a n,
  find_segment (segs ++ vt) a n =
  match find_segment segs a n with
  | Some s => Some s
  | None => find_segment vt a n
  end.
Proof.
  induction segs as [|s rest IH]; intros vt a n; [reflexivity|].
  cbn [app find_segment].
  match goal with |- (if ?c then _ else _) = _ => destruct c end;
    cbn beta iota; [reflexivity | apply IH].
Qed.

Lemma find_segment_app : forall segs vt a n seg,
  find_segment segs a n = Some seg -> find_segment (segs ++ vt) a n = Some seg.
Proof. intros segs vt a n seg H. rewrite find_segment_append, H. reflexivity. Qed.

Lemma find_segment_in : forall l a n s, find_segment l a n = Some s -> In s l.
Proof.
  induction l as [|x rest IH]; intros a n s H; [discriminate H|].
  cbn [find_segment] in H. revert H.
  match goal with |- (if ?c then _ else _) = _ -> _ => destruct c end;
    intro H; [injection H as <-; left; reflexivity | right; exact (IH _ _ _ H)].
Qed.

(* ========================================================================= *)
(* The vDSO pair is not executable                                            *)
(* ========================================================================= *)

(** No segment of [vt] carries 'x'. *)
Definition vt_no_exec (vt : list Segment) : Prop :=
  forall s, In s vt -> seg_executable s = false.

Local Transparent vdso_segments.
Lemma vdso_segments_no_exec : forall kb sp mbase,
  vt_no_exec (vdso_segments kb sp mbase).
Proof.
  intros kb sp mbase s Hs. unfold vdso_segments in Hs. cbv zeta in Hs.
  revert Hs.
  match goal with |- In _ (if ?c then _ else _) -> _ => destruct c end;
    [intros [] | intros [<- | [<- | []]]; reflexivity].
Qed.

(** A lookup below every segment's base finds nothing. *)
Lemma find_segment_none_of_base : forall l a n,
  (forall s, In s l -> (a < Z.of_N (seg_base s))%Z) -> find_segment l a n = None.
Proof.
  induction l as [|s rest IH]; intros a n H; [reflexivity|].
  cbn [find_segment].
  rewrite (proj2 (Z.leb_gt _ _) (H s (or_introl eq_refl))). cbn [andb].
  apply IH. intros t Ht. apply H. right. exact Ht.
Qed.

(** The pair sits at or above [page_size]: [Run.vdso_segments] builds it
    only when its base is at least [page_size], and the text is above
    the vvar pages.  So an address on the first page is in neither. *)
Lemma vdso_find_low : forall kb sp mbase a n, (a < page_size)%Z ->
  find_segment (vdso_segments kb sp mbase) a n = None.
Proof.
  intros kb sp mbase a n Ha. unfold vdso_segments. cbv zeta.
  match goal with
  | |- find_segment (if ?c then _ else _) _ _ = _ => destruct c eqn:Hb
  end; [reflexivity|].
  apply Z.ltb_ge in Hb.
  pose proof (vdso_text_pages_pos kb) as Hp.
  (* Since public #150 the text's base is [Run.vdso_text_base], a word:
     its value is the pair's top less the text pages, which lies between
     the base the guard tested and the top, so the word holds it. *)
  pose proof (page_round_down_Z_le (Z.min (bv_unsigned mbase)
                (page_round_down_Z (bv_unsigned sp - stack_max_size)))) as Htop.
  pose proof (bv_unsigned_in_range 64 mbase) as Hm.
  apply find_segment_none_of_base.
  intros s [<- | [<- | []]]; cbn [seg_base].
  - rewrite Z2N.id; unfold vdso_len, vdso_vvar_pages, page_size in *; lia.
  - unfold vdso_text_base, vdso_pair_top in *.
    rewrite Z_to_bv_small
      by (unfold bv_modulus, vdso_len, vdso_vvar_pages, page_size in *; lia).
    rewrite Z2N.id; unfold vdso_len, vdso_vvar_pages, page_size in *; lia.
Qed.

(** The pair is two kernel mappings, so it adds nothing to the ledger the
    run's [brk] and [mmap] consult: the run's reservations are the
    binary's. *)
Lemma segments_reserved_vdso : forall kb sp mbase,
  segments_reserved (vdso_segments kb sp mbase) = [].
Proof.
  intros kb sp mbase. unfold vdso_segments. cbv zeta.
  match goal with |- segments_reserved (if ?c then _ else _) = _ => destruct c end;
    reflexivity.
Qed.
Local Opaque vdso_segments.

(* ========================================================================= *)
(* Fetch paths: equal over [segs ++ vt] when [vt] is not executable           *)
(* ========================================================================= *)

Section Fetch.
Variables segs vt : list Segment.
Hypothesis Hvt : vt_no_exec vt.

Lemma code_read_append : forall a n, code_read (segs ++ vt) a n = code_read segs a n.
Proof.
  intros a n. unfold code_read. rewrite find_segment_append.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [s|]; [reflexivity|].
  destruct (find_segment vt (bv_unsigned a) (Z.of_N n)) as [s|] eqn:Hv; [|reflexivity].
  cbn beta iota. rewrite (Hvt s (find_segment_in _ _ _ _ Hv)). reflexivity.
Qed.

Lemma code_read_ov_append : forall m a n,
  code_read_ov (segs ++ vt) m a n = code_read_ov segs m a n.
Proof.
  intros m a n. unfold code_read_ov. rewrite find_segment_append.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [s|]; [reflexivity|].
  destruct (find_segment vt (bv_unsigned a) (Z.of_N n)) as [s|] eqn:Hv; [|reflexivity].
  cbn beta iota. rewrite (Hvt s (find_segment_in _ _ _ _ Hv)). reflexivity.
Qed.

Lemma fetch_word_append : forall a, fetch_word (segs ++ vt) a = fetch_word segs a.
Proof. intros a. unfold fetch_word. rewrite code_read_append. reflexivity. Qed.

Lemma fetch_word_ov_append : forall m a,
  fetch_word_ov (segs ++ vt) m a = fetch_word_ov segs m a.
Proof. intros m a. unfold fetch_word_ov. rewrite code_read_ov_append. reflexivity. Qed.

Lemma fetch_half_append : forall a, fetch_half (segs ++ vt) a = fetch_half segs a.
Proof. intros a. unfold fetch_half. rewrite code_read_append. reflexivity. Qed.

Lemma fetch_half_ov_append : forall m a,
  fetch_half_ov (segs ++ vt) m a = fetch_half_ov segs m a.
Proof. intros m a. unfold fetch_half_ov. rewrite code_read_ov_append. reflexivity. Qed.

Lemma fetch_half_any_append : forall m a,
  fetch_half_any (segs ++ vt) m a = fetch_half_any segs m a.
Proof.
  intros m a. unfold fetch_half_any.
  rewrite fetch_half_append, fetch_half_ov_append. reflexivity.
Qed.

Lemma fetch_tail_any_append : forall m a,
  fetch_tail_any (segs ++ vt) m a = fetch_tail_any segs m a.
Proof.
  intros m a. unfold fetch_tail_any. rewrite !fetch_half_any_append. reflexivity.
Qed.

End Fetch.

(* ========================================================================= *)
(* Successful reads and store bounds carry over (no premise on [vt])          *)
(* ========================================================================= *)

Lemma code_read_app : forall segs vt (a : word) n bs,
  code_read segs a n = Some bs -> code_read (segs ++ vt) a n = Some bs.
Proof.
  intros segs vt a n bs H. unfold code_read in *.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:Hf;
    [|discriminate H].
  rewrite (find_segment_app segs vt _ _ seg Hf). exact H.
Qed.

Lemma fetch_word_app : forall segs vt (pc : word) w,
  fetch_word segs pc = Some w -> fetch_word (segs ++ vt) pc = Some w.
Proof.
  intros segs vt pc w H. unfold fetch_word in *.
  destruct (negb (Z.eqb (bv_unsigned pc mod 2) 0)%Z); [discriminate H|].
  destruct (code_read segs pc 4) as [bs|] eqn:Hc; [|discriminate H].
  rewrite (code_read_app segs vt pc 4 bs Hc). exact H.
Qed.

Lemma memory_read_app : forall segs vt (a : word) n bs,
  memory_read segs a n = Some bs -> memory_read (segs ++ vt) a n = Some bs.
Proof.
  intros segs vt a n bs H. unfold memory_read in *.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:Hf;
    [|discriminate H].
  rewrite (find_segment_app segs vt _ _ seg Hf). exact H.
Qed.

Lemma seg_rom_app : forall segs vt (a : word) b,
  seg_rom segs a = Some b -> seg_rom (segs ++ vt) a = Some b.
Proof.
  intros segs vt a b H. unfold seg_rom in *.
  destruct (memory_read segs a 1) as [l|] eqn:Hm; [|discriminate H].
  rewrite (memory_read_app segs vt a 1 l Hm). exact H.
Qed.

Lemma ov_read_bytes_app : forall segs vt m n (a : word) bs,
  ov_read_bytes segs m a n = Some bs -> ov_read_bytes (segs ++ vt) m a n = Some bs.
Proof.
  intros segs vt m n. induction n as [|n IH]; intros a bs H; [exact H|].
  cbn [ov_read_bytes] in *. revert H.
  destruct (m a) as [b|].
  - destruct (ov_read_bytes segs m (a + 1) n) as [rest|] eqn:Hr;
      intro H; [|discriminate H].
    rewrite (IH _ _ Hr). exact H.
  - destruct (memory_read segs a 1) as [l|] eqn:Hmr; [|intro H; discriminate H].
    rewrite (memory_read_app segs vt a 1 l Hmr).
    destruct l as [|b tl]; [intro H; discriminate H|].
    destruct (ov_read_bytes segs m (a + 1) n) as [rest|] eqn:Hr;
      intro H; [|discriminate H].
    rewrite (IH _ _ Hr). exact H.
Qed.

(** Named [rdn_lift], not [rdn_app]: [SeqExec.rdn_app] is the
    length-split lemma. *)
Lemma rdn_lift : forall segs vt mem n (a : word) bs,
  rdn segs mem a n = Some bs -> rdn (segs ++ vt) mem a n = Some bs.
Proof.
  intros segs vt mem n. induction n as [|n IH]; intros a bs H; [exact H|].
  cbn [rdn] in *. revert H.
  destruct (mem a) as [b|].
  - destruct (rdn segs mem (a + 1) n) as [rest|] eqn:Hr; intro H; [|discriminate H].
    rewrite (IH _ _ Hr). exact H.
  - destruct (seg_rom segs a) as [b|] eqn:Hs; [|intro H; discriminate H].
    rewrite (seg_rom_app segs vt a b Hs).
    destruct (rdn segs mem (a + 1) n) as [rest|] eqn:Hr; intro H; [|discriminate H].
    rewrite (IH _ _ Hr). exact H.
Qed.

Lemma wview_app : forall segs vt m (a : word) b,
  wview segs m a = Some b -> wview (segs ++ vt) m a = Some b.
Proof.
  intros segs vt m a b H. unfold wview in *.
  destruct (m a) as [b'|]; [exact H|].
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Hf; [|discriminate H].
  rewrite (find_segment_app segs vt _ _ seg Hf). exact H.
Qed.

Lemma store_ok_app : forall segs vt m n (a : word),
  store_ok segs m a n = true -> store_ok (segs ++ vt) m a n = true.
Proof.
  intros segs vt m n. induction n as [|n IH]; intros a H; [reflexivity|].
  cbn [store_ok] in *.
  destruct (wview segs m a) as [b|] eqn:Hw; [|discriminate H].
  rewrite (wview_app segs vt m a b Hw). exact (IH _ H).
Qed.

Lemma wseg_ok_lift : forall segs vt n (a : word),
  wseg_ok segs a n = true -> wseg_ok (segs ++ vt) a n = true.
Proof.
  intros segs vt n. induction n as [|n IH]; intros a H; [reflexivity|].
  cbn [wseg_ok] in *.
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Hf; [|discriminate H].
  rewrite (find_segment_app segs vt _ _ seg Hf).
  apply andb_prop in H as [H1 H2].
  apply andb_true_intro. split; [exact H1 | exact (IH _ H2)].
Qed.

(* ========================================================================= *)
(* Instruction execution                                                      *)
(* ========================================================================= *)

Lemma interp_eff_accesses_app : forall segs vt t m r,
  interp_eff_accesses segs t m = MachineOk r ->
  interp_eff_accesses (segs ++ vt) t m = MachineOk r.
Proof.
  intros segs vt t.
  induction t as [c|c|c|c|c|c|n a k IHk|n a v k IHk]; intros m r H;
    cbn [interp_eff_accesses] in *; try discriminate H.
  - exact H.
  - revert H.
    destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|] eqn:Hr.
    + rewrite (ov_read_bytes_app segs vt m (width_bytes n) a bs Hr). cbn beta iota.
      destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m)
        as [rep| |] eqn:Hk; intro H; try discriminate H.
      rewrite (IHk _ m rep Hk). exact H.
    + destruct (range_meets_vvar segs a (width_bytes n)); intro H; discriminate H.
  - revert H.
    destruct (store_ok segs m a (width_bytes n)) eqn:Hs; [|intro H; discriminate H].
    rewrite (store_ok_app segs vt m (width_bytes n) a Hs).
    destruct (interp_eff_accesses segs k
                (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v))))
      as [rep| |] eqn:Hk; intro H; try discriminate H.
    rewrite (IHk _ rep Hk). exact H.
Qed.

Lemma decode_exec_accesses_app : forall segs vt st w r,
  decode_exec_accesses segs st w = MachineOk r ->
  decode_exec_accesses (segs ++ vt) st w = MachineOk r.
Proof.
  intros segs vt st w r. unfold decode_exec_accesses.
  destruct (is_ecall w); cbn beta iota; [intro H; exact H|].
  destruct (decode_any w) as [[i isz]|]; cbn beta iota; [|intro H; exact H].
  match goal with
  | |- context [interp_eff_accesses segs ?t ?m] =>
      destruct (interp_eff_accesses segs t m) as [rep| |] eqn:Hi;
        intro H; try discriminate H;
        rewrite (interp_eff_accesses_app segs vt t m rep Hi); exact H
  end.
Qed.

Lemma fetch_failure_ne_ok : forall segs m a st',
  fetch_failure segs m a <> MachineOk st'.
Proof.
  intros segs m a st'. unfold fetch_failure. cbv zeta.
  repeat match goal with
         | |- (if ?c then _ else _) <> _ => destruct c; cbn beta iota
         end; discriminate.
Qed.

Lemma step_accesses_app : forall segs vt st r,
  vt_no_exec vt ->
  step_accesses segs st = MachineOk r ->
  step_accesses (segs ++ vt) st = MachineOk r.
Proof.
  intros segs vt st r Hvt. unfold step_accesses.
  rewrite (fetch_word_append segs vt Hvt), (fetch_word_ov_append segs vt Hvt),
    (fetch_tail_any_append segs vt Hvt).
  destruct (fetch_word segs (ms_pc st)) as [w|]; cbn beta iota;
    [apply decode_exec_accesses_app|].
  destruct (fetch_word_ov segs (ms_mem st) (ms_pc st)) as [w|]; cbn beta iota;
    [apply decode_exec_accesses_app|].
  destruct (fetch_tail_any segs (ms_mem st) (ms_pc st)) as [w|]; cbn beta iota;
    [apply decode_exec_accesses_app|].
  destruct (fetch_failure segs (ms_mem st) (ms_pc st)) as [st'| |] eqn:Hf;
    [ exfalso; exact (fetch_failure_ne_ok _ _ _ _ Hf)
    | intro Hc; discriminate Hc
    | intro Hc; discriminate Hc ].
Qed.

Lemma step_app : forall segs vt st st',
  vt_no_exec vt ->
  RiscvSemantics.step segs st = MachineOk st' ->
  RiscvSemantics.step (segs ++ vt) st = MachineOk st'.
Proof.
  intros segs vt st st' Hvt. unfold RiscvSemantics.step, drop_access_report.
  destruct (step_accesses segs st) as [r| |] eqn:Hs; intro H; try discriminate H.
  rewrite (step_accesses_app segs vt st r Hvt Hs). exact H.
Qed.

Lemma msteps_app : forall segs vt ms ms',
  vt_no_exec vt -> msteps segs ms ms' -> msteps (segs ++ vt) ms ms'.
Proof.
  intros segs vt ms ms' Hvt H.
  induction H as [ms | ms ms1 ms2 Hsvc Hst _ IH].
  - apply mst_refl.
  - eapply mst_step; [exact Hsvc | exact (step_app segs vt ms ms1 Hvt Hst) | exact IH].
Qed.

(** Every [to_wexit] chain lifts: its write node reads the buffer through
    [ms_read_bytes] (the state's own memory and rom), not through the
    segment list, so only the machine steps see [segs]. *)
Lemma to_wexit_app : forall segs vt ms bufs code,
  vt_no_exec vt -> to_wexit segs ms bufs code -> to_wexit (segs ++ vt) ms bufs code.
Proof.
  intros segs vt ms bufs code Hvt H.
  induction H as [ms x8 Hsvc Hx8
                 | ms x8 buf bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH
                 | ms ms' bufs code Hsvc Hstep _ IH].
  - eapply tw_exit; eassumption.
  - eapply tw_write; [exact Hsvc | exact Hno | exact Hg | exact Hr | exact Hok
                     | exact Hnb | exact IH].
  - eapply tw_step; [exact Hsvc | exact (step_app segs vt ms ms' Hvt Hstep) | exact IH].
Qed.

(** A write-all chain lifts the same way: its write node reads the buffer
    through [ms_read_bytes], so only the machine steps see [segs]. *)
Lemma to_wall_lift_mut : forall segs vt fd, vt_no_exec vt ->
  (forall ms rest k, to_wall segs fd ms rest k ->
     forall k' : machine_state -> Prop, (forall m, k m -> k' m) ->
     to_wall (segs ++ vt) fd ms rest k')
  /\ (forall ms rest k, to_wall_tail segs fd ms rest k ->
     forall k' : machine_state -> Prop, (forall m, k m -> k' m) ->
     to_wall_tail (segs ++ vt) fd ms rest k').
Proof.
  intros segs vt fd Hvt.
  apply (to_wall_mutind segs fd
           (fun ms rest k => forall k' : machine_state -> Prop,
              (forall m, k m -> k' m) -> to_wall (segs ++ vt) fd ms rest k')
           (fun ms rest k => forall k' : machine_state -> Prop,
              (forall m, k m -> k' m) -> to_wall_tail (segs ++ vt) fd ms rest k')).
  - intros ms x8 rest k Hsvc Hno Hg Hr Hok Hnb _ IH k' Hk.
    eapply twl_write; [exact Hsvc | exact Hno | exact Hg | exact Hr | exact Hok
                      | exact Hnb |].
    intros n Hn1 Hn2. exact (IH n Hn1 Hn2 k' Hk).
  - intros ms k Hkm k' Hk. apply twt_done. exact (Hk ms Hkm).
  - intros ms rest k Hnb _ IH k' Hk. apply twt_more; [exact Hnb | exact (IH k' Hk)].
  - intros ms ms' rest k Hsvc Hstep _ IH k' Hk.
    eapply twt_step; [exact Hsvc | exact (step_app segs vt ms ms' Hvt Hstep) | exact (IH k' Hk)].
Qed.

Lemma to_wallexit_app : forall segs vt fd bufs code ms,
  vt_no_exec vt ->
  to_wallexit segs fd bufs code ms -> to_wallexit (segs ++ vt) fd bufs code ms.
Proof.
  intros segs vt fd bufs code ms Hvt. revert ms.
  induction bufs as [|buf rest IH]; intros ms H.
  - exact (to_wexit_app segs vt ms [] code Hvt H).
  - destruct H as [Hl Ht]. split; [exact Hl|].
    exact (proj2 (to_wall_lift_mut segs vt fd Hvt) ms buf _ Ht _ IH).
Qed.

(* ========================================================================= *)
(* At the run's list                                                          *)
(* ========================================================================= *)

Lemma msteps_run : forall segs inp sp mbase ms ms',
  msteps segs ms ms' -> msteps (run_segments segs inp sp mbase) ms ms'.
Proof.
  intros segs inp sp mbase ms ms' H. unfold run_segments.
  exact (msteps_app segs _ ms ms' (vdso_segments_no_exec _ _ _) H).
Qed.

Lemma fetch_word_run : forall segs inp sp mbase (pc : word) w,
  fetch_word segs pc = Some w -> fetch_word (run_segments segs inp sp mbase) pc = Some w.
Proof. intros segs inp sp mbase pc w H. unfold run_segments. exact (fetch_word_app _ _ _ _ H). Qed.

Lemma store_ok_run : forall segs inp sp mbase m n (a : word),
  store_ok segs m a n = true -> store_ok (run_segments segs inp sp mbase) m a n = true.
Proof. intros segs inp sp mbase m n a H. unfold run_segments. exact (store_ok_app _ _ _ _ _ H). Qed.

Lemma to_wexit_run : forall segs inp sp mbase ms bufs code,
  to_wexit segs ms bufs code -> to_wexit (run_segments segs inp sp mbase) ms bufs code.
Proof.
  intros segs inp sp mbase ms bufs code H. unfold run_segments.
  exact (to_wexit_app segs _ ms bufs code (vdso_segments_no_exec _ _ _) H).
Qed.

Lemma to_wallexit_run : forall segs inp sp mbase fd bufs code ms,
  to_wallexit segs fd bufs code ms ->
  to_wallexit (run_segments segs inp sp mbase) fd bufs code ms.
Proof.
  intros segs inp sp mbase fd bufs code ms H. unfold run_segments.
  exact (to_wallexit_app segs _ fd bufs code ms (vdso_segments_no_exec _ _ _) H).
Qed.

(* ExFive additions *)

(* ========================================================================= *)
(* Chain lifts for the write/munmap/exit and mmap derivations ([MmapSim])    *)
(* ========================================================================= *)

(** Their syscall nodes read the buffer through [ms_read_bytes] and the
    model only, never through the segment list, so only the machine steps
    see [segs]; [step_app] lifts those. *)

From LinuxProcessSemantics.Common Require Import MmapSim.

Section MmapLifts.
Context {fx : FPState}.

(** The write/munmap/exit triple. *)
Lemma twm_app : forall segs vt, vt_no_exec vt ->
  (forall ms model bufs code, twm segs ms model bufs code ->
     twm (segs ++ vt) ms model bufs code) /\
  (forall ms model rest bufs code, twm_pend segs ms model rest bufs code ->
     twm_pend (segs ++ vt) ms model rest bufs code) /\
  (forall ms model rest bufs code, twm_tail segs ms model rest bufs code ->
     twm_tail (segs ++ vt) ms model rest bufs code).
Proof.
  intros segs vt Hvt.
  apply (twm_mutind segs (twm (segs ++ vt)) (twm_pend (segs ++ vt))
           (twm_tail (segs ++ vt))).
  - intros ms model x8 H1 H2. eapply twm_exit; eassumption.
  - intros ms model buf bufs code H1 _ IH. apply twm_write; assumption.
  - intros ms model x8 bufs code H1 H2 H3 _ IHf _ IHc.
    eapply twm_munmap; eassumption.
  - intros ms ms' model bufs code H1 H2 _ IH.
    eapply twm_step; [exact H1 | exact (step_app segs vt ms ms' Hvt H2) | exact IH].
  - intros ms model x8 rest bufs code H1 H2 H3 H4 H5 H6 _ IH.
    eapply twmp_write; eassumption.
  - intros ms model bufs code _ IH. apply twmt_done. exact IH.
  - intros ms model rest bufs code H1 _ IH. apply twmt_more; assumption.
  - intros ms ms' model rest bufs code H1 H2 _ IH.
    eapply twmt_step; [exact H1 | exact (step_app segs vt ms ms' Hvt H2) | exact IH].
Qed.

(** The mmap node and its deterministic prefix. *)
Lemma tmw_app : forall segs vt, vt_no_exec vt ->
  forall ms model bf cf bs cs, tmw segs ms model bf cf bs cs ->
  tmw (segs ++ vt) ms model bf cf bs cs.
Proof.
  intros segs vt Hvt ms model bf cf bs cs H.
  induction H as [ms model x8 bf cf bs cs H1 H2 H3 Hd Hf Hs Hex
                 | ms ms' model bf cf bs cs H1 H2 _ IH].
  - eapply tmw_mmap; [exact H1 | exact H2 | exact H3 | exact Hd | | | exact Hex].
    + intros e He. exact (proj1 (twm_app segs vt Hvt) _ _ _ _ (Hf e He)).
    + intros a Ha. exact (proj1 (twm_app segs vt Hvt) _ _ _ _ (Hs a Ha)).
  - eapply tmw_step; [exact H1 | exact (step_app segs vt ms ms' Hvt H2) | exact IH].
Qed.

End MmapLifts.

From LinuxProcessSemantics.Common Require Import StepTac.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.

(* ========================================================================= *)
(* The one-page grant on the run's launch model                              *)
(* ========================================================================= *)

(** A ledger range that every entry lies wholly above or wholly below is
    free.  The grant witness reads it for the launch's ledger: the image's
    entries below, the vDSO pair above. *)
Lemma region_free_all_apart : forall (maps : list (word * word)) (lo n : word),
  (forall a sz, In (a, sz) maps ->
     (bv_unsigned lo + bv_unsigned n <= bv_unsigned a)%Z \/
     (bv_unsigned a + bv_unsigned sz <= bv_unsigned lo)%Z) ->
  region_free maps lo n = true.
Proof.
  induction maps as [|[a sz] r IH]; intros lo n H; [reflexivity|].
  cbn [region_free]. unfold iv_overlap.
  rewrite (IH lo n (fun a' s' Hm => H a' s' (or_intror Hm))).
  destruct (H a sz (or_introl eq_refl)) as [H1 | H1].
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned a) (bv_unsigned lo + bv_unsigned n)) H1).
    rewrite andb_false_r. reflexivity.
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned lo) (bv_unsigned a + bv_unsigned sz)) H1).
    reflexivity.
Qed.

Lemma page_round_down_Z_bounds : forall M,
  (M - 4095 <= page_round_down_Z M <= M)%Z.
Proof.
  intros M. unfold page_round_down_Z, page_size.
  pose proof (Z.div_mod M 4096 ltac:(lia)).
  pose proof (Z.mod_pos_bound M 4096 ltac:(lia)). lia.
Qed.

(** A GRANT EXISTS on the launch's model, for any page-multiple length up
    to [2^40].  [MmapSim.grant_ok] asks that the address be the one Linux
    places ([Placement.linux_place_is]), so the witness is not a fixed
    address: it is [Placement.linux_place_exists]'s, fed the bottom-up gap
    at [Mmap.task_unmapped_base], which the image's reservations lie below
    and the vDSO pair (within [vdso_len] below the page under
    [min mmap_base (sp - stack_max_size)], so at or above
    [mmap_base_min] less 21 pages) lies above. *)
Lemma grant_witness_init_len : forall segs inp (hint brk0 mb sp : word) (lim g : Z) v,
  (forall a sz, In (a, sz) (segments_reserved segs) ->
     (bv_unsigned a + bv_unsigned sz <= Mmap.task_unmapped_base)%Z) ->
  (sp_window_lo <= bv_unsigned sp)%Z -> (mmap_base_min <= bv_unsigned mb)%Z ->
  (0 < g)%Z -> (g mod page_size = 0)%Z -> (g <= 2 ^ 40)%Z ->
  (g <= lim)%Z ->
  exists a, grant_ok hint
              (with_vdso v (init_model (segments_reserved segs) brk0 mb sp lim inp))
              a g = true.
Proof.
  intros segs inp hint brk0 mb sp lim g v Hres Hsp Hmb Hg0 Hgal Hg40 Hlim.
  pose proof (u64_range sp) as Hsp64. pose proof (u64_range mb) as Hmb64.
  set (m := with_vdso v (init_model (segments_reserved segs) brk0 mb sp lim inp)).
  assert (Hat : alloc_top (m_vmmaps m) = (bv_unsigned sp - stack_max_size)%Z)
    by reflexivity.
  assert (Hex : exists a, Mmap.linux_place (m_vmmaps m) (kb_thp (m_kernel m)) hint g a).
  { apply linux_place_exists; [exact Hg0 | exact Hgal |].
    exists Mmap.task_unmapped_base. right.
    unfold Mmap.gap_fits, Mmap.task_unmapped_base in *.
    split; [reflexivity|]. split; [lia|].
    split; [rewrite Hat; unfold sp_window_lo in Hsp; unfold stack_max_size; lia|].
    change (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
      with (init_reserved (segments_reserved segs) mb sp (in_kernel inp) ++ []).
    apply region_free_all_apart.
    intros a sz Hm.
    rewrite (u_Z2bv 0x2aaaaab000) by lia. rewrite (u_Z2bv g) by lia.
    rewrite app_nil_r in Hm. unfold init_reserved in Hm.
    apply in_app_or in Hm as [Hm | Hm].
    - right. exact (Hres a sz Hm).
    - left.
      set (M := Z.min (bv_unsigned mb) (bv_unsigned sp - stack_max_size)) in *.
      assert (Hmin : (0x154555557000 <= M)%Z)
        by (unfold M, sp_window_lo, mmap_base_min, stack_max_size in *; lia).
      assert (Hmax : (M <= bv_unsigned sp)%Z) by (unfold M, stack_max_size; lia).
      pose proof (page_round_down_Z_bounds M) as Hpd.
      assert (Htop : (page_round_down_Z M < two_pow_64)%Z) by (unfold two_pow_64; lia).
      destruct (vdso_reserved_above (in_kernel inp) _ a sz Htop Hm) as [H1 _].
      pose proof (vdso_len_bounds (in_kernel inp)) as Hl.
      unfold page_size in Hl. lia. }
  destruct Hex as [a Hpl].
  destruct (linux_place_admissible _ _ _ g a Hg0 Hgal Hpl)
    as (_ & Hpos & Hhi & _).
  rewrite Hat in Hhi. unfold stack_max_size in Hhi.
  exists (Z_to_bv 64 a).
  apply grant_ok_intro; [exact Hg0 | exact Hgal | |].
  - apply (proj2 (linux_place_is_iff _ _ _ g _ Hg0 Hgal)).
    rewrite u_Z2bv by lia. exact Hpl.
  - (* the launch model has no backed mapping yet *)
    change (vm_backing_used m) with 0%Z.
    change (vm_limit (m_vmmaps m)) with lim. lia.
Qed.

(** The one-page grant, [grant_witness_init_len] at [4096]. *)
Lemma grant_witness_init : forall segs inp (hint brk0 mb sp : word) (lim : Z) v,
  (forall a sz, In (a, sz) (segments_reserved segs) ->
     (bv_unsigned a + bv_unsigned sz <= Mmap.task_unmapped_base)%Z) ->
  (sp_window_lo <= bv_unsigned sp)%Z -> (mmap_base_min <= bv_unsigned mb)%Z ->
  (4096 <= lim)%Z ->
  exists a, grant_ok hint
              (with_vdso v (init_model (segments_reserved segs) brk0 mb sp lim inp))
              a 4096 = true.
Proof.
  intros segs inp hint brk0 mb sp lim v Hres Hsp Hmb Hlim.
  apply grant_witness_init_len;
    [exact Hres | exact Hsp | exact Hmb | lia | reflexivity | lia | exact Hlim].
Qed.
