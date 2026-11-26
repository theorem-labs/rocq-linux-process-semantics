(** * conditional_bug-ns: the SAME musl [write] summary, a DIFFERENT
      binary and a DIFFERENT load address.

    PROTOTYPE / EXPLORATION.  PROOF-SIDE FILE.

    This file exists to demonstrate the payoff of
    [Common/MuslCall.v]'s address parametricity: the blob that
    [modprint_ns] loads at 0x11098 sits at 0x110fc here, and the summary
    is reused with no reproof — only the 26 [SF_*] rebasings below, each
    one line.

    A run reads [Run.run_segments]: the image's segments, then the vDSO
    pair.  The summary is instantiated over [source_segs ++ vt] for any
    appended [vt], each fetch lemma carried there by
    [RunSegmentsLift.fetch_word_app], and the write's buffer range
    carries the [access_okb] premise [MuslCall.musl_write_wall] takes. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WallSim MuslCall RunSegmentsLift.
From LinuxProcessSemantics.Examples.conditional_bug_ns Require Import conditional_bug_ns_code.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(** This binary's load address for the blob. *)
Definition CBB : word := 0x110fc.

Lemma fetch_at : forall segs (b : word) (d : Z) (a : word) w,
  at_ b d = a -> fetch_word segs a = Some w -> fetch_word segs (at_ b d) = Some w.
Proof. intros segs b d a w Ha Hf. rewrite Ha. exact Hf. Qed.

Ltac fat SF :=
  refine (fetch_at _ _ _ _ _ _ (fetch_word_app _ _ _ _ SF)); unfold at_, CBB; bveq.

Section RunList.
Context {fx : FPState}.

(** The segments appended after the image's own: the vDSO pair, at the
    run's list. *)
Variable vt : list Segment.

Lemma f00 : fetch_word (source_segs ++ vt) (at_ CBB 0x00) = Some Wsp16m. Proof. fat SF_110fc. Qed.
Lemma f04 : fetch_word (source_segs ++ vt) (at_ CBB 0x04) = Some Wmv_a3a2. Proof. fat SF_11100. Qed.
Lemma f08 : fetch_word (source_segs ++ vt) (at_ CBB 0x08) = Some Wli_a6_0. Proof. fat SF_11104. Qed.
Lemma f0c : fetch_word (source_segs ++ vt) (at_ CBB 0x0c) = Some Wmv_a2a1. Proof. fat SF_11108. Qed.
Lemma f10 : fetch_word (source_segs ++ vt) (at_ CBB 0x10) = Some Wli_a5_0. Proof. fat SF_1110c. Qed.
Lemma f14 : fetch_word (source_segs ++ vt) (at_ CBB 0x14) = Some Wmv_a1a0. Proof. fat SF_11110. Qed.
Lemma f18 : fetch_word (source_segs ++ vt) (at_ CBB 0x18) = Some Wli_a4_0. Proof. fat SF_11114. Qed.
Lemma f1c : fetch_word (source_segs ++ vt) (at_ CBB 0x1c) = Some Wli_a0_64. Proof. fat SF_11118. Qed.
Lemma f20 : fetch_word (source_segs ++ vt) (at_ CBB 0x20) = Some Wsd_ra8. Proof. fat SF_1111c. Qed.
Lemma f24 : fetch_word (source_segs ++ vt) (at_ CBB 0x24) = Some Wjal_cp. Proof. fat SF_11120. Qed.
Lemma f28 : fetch_word (source_segs ++ vt) (at_ CBB 0x28) = Some Wld_ra8. Proof. fat SF_11124. Qed.
Lemma f2c : fetch_word (source_segs ++ vt) (at_ CBB 0x2c) = Some Wsp16p. Proof. fat SF_11128. Qed.
Lemma f30 : fetch_word (source_segs ++ vt) (at_ CBB 0x30) = Some Wj4. Proof. fat SF_1112c. Qed.
Lemma f34 : fetch_word (source_segs ++ vt) (at_ CBB 0x34) = Some Wlui_a5. Proof. fat SF_11130. Qed.
Lemma f38 : fetch_word (source_segs ++ vt) (at_ CBB 0x38) = Some Wbltu. Proof. fat SF_11134. Qed.
Lemma f3c : fetch_word (source_segs ++ vt) (at_ CBB 0x3c) = Some Wret. Proof. fat SF_11138. Qed.
Lemma f6c : fetch_word (source_segs ++ vt) (at_ CBB 0x6c) = Some Wmv_a7a0. Proof. fat SF_11168. Qed.
Lemma f70 : fetch_word (source_segs ++ vt) (at_ CBB 0x70) = Some Wmv_a0a1. Proof. fat SF_1116c. Qed.
Lemma f74 : fetch_word (source_segs ++ vt) (at_ CBB 0x74) = Some Wmv_a1a2. Proof. fat SF_11170. Qed.
Lemma f78 : fetch_word (source_segs ++ vt) (at_ CBB 0x78) = Some Wmv_a2a3. Proof. fat SF_11174. Qed.
Lemma f7c : fetch_word (source_segs ++ vt) (at_ CBB 0x7c) = Some Wmv_a3a4. Proof. fat SF_11178. Qed.
Lemma f80 : fetch_word (source_segs ++ vt) (at_ CBB 0x80) = Some Wmv_a4a5. Proof. fat SF_1117c. Qed.
Lemma f84 : fetch_word (source_segs ++ vt) (at_ CBB 0x84) = Some Wmv_a5a6. Proof. fat SF_11180. Qed.
Lemma f88 : fetch_word (source_segs ++ vt) (at_ CBB 0x88) = Some Wecall. Proof. fat SF_11184. Qed.
Lemma f8c : fetch_word (source_segs ++ vt) (at_ CBB 0x8c) = Some Wret. Proof. fat SF_11188. Qed.
Lemma f90 : fetch_word (source_segs ++ vt) (at_ CBB 0x90) = Some Wj_cpc. Proof. fat SF_1118c. Qed.

(** The instantiated summary.  No proof: the work was done once, in
    [Common/MuslCall.v]. *)
Definition cb_write_wall0 := musl_write_wall (source_segs ++ vt) CBB f00 f04 f08 f0c f10 f14 f18 f1c f20 f24 f28 f2c f30 f34 f38 f3c f6c f70 f74 f78 f7c f80 f84 f88 f8c f90.

(** The summary in the form a caller in [conditional_bug_ns_source.v]
    actually meets it: the entry pc as the raw literal 0x110fc rather
    than [at_ CBB 0x00], the [rom] fixed to [seg_rom (source_segs ++ vt)], and
    the summary's two [ret_ok] obligations reduced to "the caller's
    return address is even".  The continuation is the put-loop form:
    per delivered length [n], a [WallSim.to_wall_tail] of the remainder
    [skipn n out] down to the caller's continuation predicate [k]. *)
Lemma cb_write_call :
  forall (k : machine_state -> Prop)
         (regs : bvmap 5 word) (mem : word -> option byte)
         (kra sp0 buf len : word) (out : list byte),
  (bv_unsigned kra mod 2 = 0)%Z ->
  getr regs 1 = kra -> getr regs 2 = sp0 ->
  getr regs 10 = Z_to_bv 64 1 -> getr regs 11 = buf -> getr regs 12 = len ->
  RiscvSemantics.store_ok (source_segs ++ vt) mem (at_ sp0 (-8)) 8%nat = true ->
  (bv_unsigned (at_ sp0 (-8)) + 8 <= 2^64)%Z ->
  (bv_unsigned len <= 18446744073709547520)%Z ->
  rdn (source_segs ++ vt) (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 kra))
      buf (word_to_nat len) = Some out ->
  (* the range [vfs_write]'s [access_ok] accepts *)
  access_okb buf (bv_unsigned len) = true ->
  (1 <= length out)%nat ->
  (forall regs' n, (1 <= n)%nat -> (n <= length out)%nat ->
     getr regs' 1 = kra -> getr regs' 2 = sp0 ->
     getr regs' 10 = len_word (firstn n out) ->
     to_wall_tail (source_segs ++ vt) (Z_to_bv 64 1)
       (mkst regs' kra (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 kra))
          (seg_rom (source_segs ++ vt)))
       (skipn n out) k) ->
  to_wall_tail (source_segs ++ vt) (Z_to_bv 64 1)
    (mkst regs (0x110fc : word) mem (seg_rom (source_segs ++ vt))) out k.
Proof.
  intros k regs mem kra sp0 buf len out Hev H1 H2 H10 H11 H12 Hok Hnw Hlen
         Hread Hacc Hnb Hcont.
  replace (0x110fc : word) with (at_ CBB 0x00) by (unfold at_, CBB; bveq).
  eapply cb_write_wall0;
    [ reflexivity
    | apply ret_ok_even; exact Hev
    | (* [at_ CBB 0x28] is 0x11124, the wrapper's own return point *)
      apply ret_ok_even; unfold at_, CBB; vm_compute; reflexivity
    | exact H1 | exact H2 | exact H10 | exact H11 | exact H12
    | exact Hok | exact Hnw | exact Hlen | exact Hread | exact Hacc | exact Hnb | ].
  intros regs' n Hn1 Hn2 Hag R1 R2 R10.
  exact (Hcont regs' n Hn1 Hn2 R1 R2 R10).
Qed.

End RunList.
