(** * mmap-upper-ns: shared definitions, tactics and value lemmas.

    PROOF-SIDE FILE (not part of the trusted specification).

    Both binaries implement mmap-upper.  With [s = argv[1]], [n = |s|]:
      argc < 2            -> exit 2, no output
      n > 4095            -> exit 3, no output
      mmap fails (-errno) -> exit 4, no output
      mmap grants a page  -> ONE write of [upper s ++ '\n'], munmap, exit 0.

    The mmap branch point is handled by Common.MmapSim ([tmw]/[twm] and
    [mmap_strong_equiv_te]); this file carries the shared pure spec
    ([upperb]/[upperv]/[out_buf]) and the value lemmas for both
    binaries' uppercase idioms.

    Conventions: string bytes are [byte = bv 8], machine values
    [word = bv 64]; unbounded bookkeeping is in [Z] over [bv_unsigned];
    computed sp-relative values use the canonical [Z_to_bv 64 (...)]
    form, pc values the numeral-literal form; loop indices ride
    [nat_to_word].  The step-chaining tactics
    ([chain_step]/[stepi]/[stepiv]/[stepj]/[stepi_at]/[sp_norm]/
    [norm_pc]) live in Common/StepTac.v. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec MmapSim StepTac ListFacts MuslStrlen.
From LinuxProcessSemantics.Examples.mmap_upper_ns Require Import mmap_upper_ns_code.
From LinuxProcessSemantics.Examples.mmap_upper_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.mmap_upper_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(* ######################################################################### *)
(* Small generic helpers (candidates for a Common lift)                      *)
(* ######################################################################### *)

(** Close a CLOSED word/byte equation by unsigned comparison. *)


(** [bv_unsigned] of a byte zero-extended into a word. *)


Lemma word_to_nat_ntw : forall n : nat, (Z.of_nat n < 2^64)%Z ->
  word_to_nat (nat_to_word n) = n.
Proof. intros n Hn. unfold word_to_nat. rewrite u_ntw by lia. lia. Qed.

(* [c_eq_0_of_u] lives in Common/PropExec.v (imported above). *)

Lemma c_eq_refl : forall x : word, c_eq x x = true.
Proof. intro x. unfold c_eq, bv_eqb. apply Z.eqb_refl. Qed.

(** Signed-compare of two small (below 2^63) words is the unsigned
    [Z.ltb] — the composition of [c_lts_small] and [c_ltu_ltb]. *)
Lemma c_lts_small_ltb : forall x y : word,
  (bv_unsigned x < 2^63)%Z -> (bv_unsigned y < 2^63)%Z ->
  c_lts x y = (bv_unsigned x <? bv_unsigned y)%Z.
Proof.
  intros x y Hx Hy. rewrite c_lts_small by assumption.
  change (bv_ltu x y) with (c_ltu x y). apply c_ltu_ltb.
Qed.

(** Loop-index word bridges. *)
Lemma v_addi_word_Sj : forall (a : word) (j : nat),
  v_addi (a + nat_to_word j) 1 = a + nat_to_word (S j).
Proof.
  intros a j.
  rewrite !word_add_nat. unfold v_addi.
  apply bv_eq. rewrite !Z_to_bv_unsigned.
  rewrite bv_wrap_add_idemp_l. f_equal; lia.
Qed.

Lemma v_addi_ntw_pred : forall j : nat, (Z.of_nat j + 1 < 2^64)%Z ->
  v_addi (nat_to_word (S j)) (-1) = nat_to_word j.
Proof.
  intros j Hj. unfold v_addi, nat_to_word.
  rewrite u_Z2bv by lia. f_equal; lia.
Qed.

(** Sealed [Z.of_nat] equation for [valid_envp]'s large literal
    (companion of CatExec's [of_nat_131071]/[of_nat_2097152]). *)

(* ######################################################################### *)
(* The shared observable-behavior spec                                       *)
(* ######################################################################### *)

(* [byte_at] (byte [k] of string [s] as laid out in memory, [s] then a
   NUL) now lives in CatExec. *)

Definition islower (b : byte) : bool :=
  ((97 <=? bv_unsigned b) && (bv_unsigned b <=? 122))%Z.

Definition upperb (b : byte) : byte :=
  if islower b then Z_to_bv 8 (bv_unsigned b - 32) else b.

Definition upperv (s : list byte) : list byte := map upperb s.

(** The single written buffer: uppercased string plus '\n'. *)
Definition out_buf (s : list byte) : list byte := upperv s ++ [Z_to_bv 8 10].

Lemma length_upperv : forall s, length (upperv s) = length s.
Proof. intro s. unfold upperv. apply length_map. Qed.

Lemma length_out_buf : forall s, length (out_buf s) = S (length s).
Proof.
  intro s. unfold out_buf. rewrite length_app, length_upperv. cbn [length]. lia.
Qed.

Lemma islower_bounds : forall b : byte, islower b = true ->
  (97 <= bv_unsigned b)%Z /\ (bv_unsigned b <= 122)%Z.
Proof.
  intros b Hl. unfold islower in Hl. apply andb_true_iff in Hl.
  destruct Hl as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  auto.
Qed.

(* ######################################################################### *)
(* Shared small facts                                                        *)
(* ######################################################################### *)

(* valid_argv_str_len/str_nz/str_bytes, byte_at_bound/len/nz, and
   nth_lt_byte_at live in CatExec. *)


(** Peeling one element off the uppercased prefix. *)
Lemma upperv_firstn_S : forall s i, (i < length s)%nat ->
  upperv (firstn (S i) s) = upperv (firstn i s) ++ [upperb (byte_at s i)].
Proof.
  intros s i Hi.
  rewrite nth_lt_byte_at by exact Hi.
  unfold upperv.
  rewrite (firstn_S_nth byte s i (Z_to_bv 8 0)) by exact Hi.
  apply map_app.
Qed.

Lemma length_upperv_firstn : forall s i, (i <= length s)%nat ->
  length (upperv (firstn i s)) = i.
Proof.
  intros s i Hi. rewrite length_upperv. apply firstn_length_le. exact Hi.
Qed.

(* ######################################################################### *)
(* Value lemmas: the uppercase idioms                                        *)
(* ######################################################################### *)

(** Low byte of [b - 97] (source: addiw -97 + andi 255; target: addi -97
    + andi 255). *)
Definition usub97 (b : byte) : word :=
  Z_to_bv 64 (if (97 <=? bv_unsigned b)%Z
              then bv_unsigned b - 97 else bv_unsigned b + 159).

Lemma u_usub97 : forall b : byte,
  bv_unsigned (usub97 b)
  = (if (97 <=? bv_unsigned b)%Z
     then bv_unsigned b - 97 else bv_unsigned b + 159)%Z.
Proof.
  intro b. unfold usub97. pose proof (u8_range b).
  destruct (Z.leb_spec 97 (bv_unsigned b)); apply u_Z2bv; lia.
Qed.

Lemma usub97_le25 : forall b : byte, islower b = true ->
  (bv_unsigned (usub97 b) <= 25)%Z.
Proof.
  intros b Hl. destruct (islower_bounds b Hl) as [H1 H2].
  rewrite u_usub97.
  rewrite (proj2 (Z.leb_le 97 (bv_unsigned b))) by lia. lia.
Qed.

Lemma usub97_gt25 : forall b : byte, islower b = false ->
  (25 < bv_unsigned (usub97 b))%Z.
Proof.
  intros b Hl. unfold islower in Hl. apply andb_false_iff in Hl.
  pose proof (u8_range b). rewrite u_usub97.
  destruct (Z.leb_spec 97 (bv_unsigned b)) as [H97|H97].
  - destruct Hl as [Hc|Hc]; [discriminate | apply Z.leb_gt in Hc; lia].
  - lia.
Qed.

Lemma land255_mod_Z : forall z, (0 <= z)%Z -> Z.land z 255 = (z mod 256)%Z.
Proof.
  intros z Hz. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia.
  reflexivity.
Qed.

(** [andi 255] as a mod-256 truncation. *)
Lemma v_andi_255 : forall x : word,
  v_andi x 255 = Z_to_bv 64 (bv_unsigned x mod 256).
Proof.
  intro x. unfold v_andi.
  change (bv_wrap 64 255) with 255%Z.
  rewrite land255_mod_Z by (pose proof (u64_range x); lia).
  reflexivity.
Qed.

(** [addiw]/[addi] of a small negative constant on a zero-extended byte
    stays a plain Z subtraction ([Z_to_bv] wraps at the end). *)
Lemma v_addiw_m97 : forall b : byte,
  v_addiw (Z_to_bv 64 (bv_unsigned b)) (-97) = Z_to_bv 64 (bv_unsigned b - 97).
Proof.
  intro b. pose proof (u8_range b).
  unfold v_addiw. rewrite u_zext8.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia).
  f_equal; lia.
Qed.

Lemma v_addiw_m32 : forall b : byte,
  v_addiw (Z_to_bv 64 (bv_unsigned b)) (-32) = Z_to_bv 64 (bv_unsigned b - 32).
Proof.
  intro b. pose proof (u8_range b).
  unfold v_addiw. rewrite u_zext8.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia).
  f_equal; lia.
Qed.

Lemma v_addi_byte_m97 : forall b : byte,
  v_addi (Z_to_bv 64 (bv_unsigned b)) (-97) = Z_to_bv 64 (bv_unsigned b - 97).
Proof.
  intro b. unfold v_addi. rewrite u_zext8. f_equal; lia.
Qed.

(** Shared tail: [andi 255] of the (wrapped) [b - 97]. *)
Lemma usub97_andi : forall b : byte,
  v_andi (Z_to_bv 64 (bv_unsigned b - 97)) 255 = usub97 b.
Proof.
  intro b. pose proof (u8_range b) as Hb.
  rewrite v_andi_255. unfold usub97.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  destruct (Z.leb_spec 97 (bv_unsigned b)) as [H97|H97].
  - rewrite (Z.mod_small (bv_unsigned b - 97) (2^64)) by lia.
    rewrite (Z.mod_small (bv_unsigned b - 97) 256) by lia.
    reflexivity.
  - replace (bv_unsigned b - 97)%Z
      with ((bv_unsigned b - 97 + 2^64) + (-1) * 2^64)%Z by lia.
    rewrite Z.mod_add by lia.
    rewrite (Z.mod_small (bv_unsigned b - 97 + 2^64) (2^64)) by lia.
    replace (bv_unsigned b - 97 + 2^64)%Z
      with ((bv_unsigned b + 159) + (2^56 - 1) * 256)%Z by lia.
    rewrite Z.mod_add by lia.
    rewrite (Z.mod_small (bv_unsigned b + 159) 256) by lia.
    reflexivity.
Qed.

(** Source form: [addiw -97] then [andi 255]. *)
Lemma usub97_addiw : forall b : byte,
  v_andi (v_addiw (Z_to_bv 64 (bv_unsigned b)) (-97)) 255 = usub97 b.
Proof. intro b. rewrite v_addiw_m97. apply usub97_andi. Qed.

(** Target form: [addi -97] then [andi 255]. *)
Lemma usub97_addi : forall b : byte,
  v_andi (v_addi (Z_to_bv 64 (bv_unsigned b)) (-97)) 255 = usub97 b.
Proof. intro b. rewrite v_addi_byte_m97. apply usub97_andi. Qed.

(** Source lowercase path: [addiw -32] then [andi 255] is the uppercased
    word. *)
Lemma upper_addiw : forall b : byte, islower b = true ->
  v_andi (v_addiw (Z_to_bv 64 (bv_unsigned b)) (-32)) 255
  = Z_to_bv 64 (bv_unsigned b - 32).
Proof.
  intros b Hl. destruct (islower_bounds b Hl) as [H1 H2].
  rewrite v_addiw_m32. rewrite v_andi_255.
  rewrite u_Z2bv by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.

(** Stored-byte normalizations ([step_sb_at]'s [Z_to_bv 8 (bv_unsigned v)]
    hypothesis). *)
Lemma sb_upper_lo : forall b : byte, islower b = true ->
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned b - 32))) = upperb b.
Proof.
  intros b Hl. destruct (islower_bounds b Hl) as [H1 H2].
  unfold upperb. rewrite Hl.
  f_equal. apply u_Z2bv; lia.
Qed.

Lemma sb_id : forall b : byte,
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned b))) = b.
Proof.
  intro b. rewrite u_zext8. apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small. pose proof (u8_range b).
  change (bv_modulus 8) with 256%Z. lia.
Qed.

Lemma sb_upper_hi : forall b : byte, islower b = false ->
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned b))) = upperb b.
Proof.
  intros b Hl. rewrite sb_id. unfold upperb. rewrite Hl. reflexivity.
Qed.

(** Target sltiu flag on the shifted byte. *)
Lemma v_sltiu_26 : forall x : word,
  v_sltiu x 26
  = (if (bv_unsigned x <? 26)%Z then Z_to_bv 64 1 else Z_to_bv 64 0).
Proof.
  intro x. unfold v_sltiu. change (bv_wrap 64 26) with 26%Z. reflexivity.
Qed.

(** Target negw of the flag. *)
Lemma negw_1 : v_subw (Z_to_bv 64 0) (Z_to_bv 64 1) = Z_to_bv 64 (2^64 - 1).
Proof. bveq. Qed.

Lemma negw_0 : v_subw (Z_to_bv 64 0) (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof. bveq. Qed.

Lemma andi_m1_224 : v_andi (Z_to_bv 64 (2^64 - 1)) 224 = Z_to_bv 64 224.
Proof. bveq. Qed.

Lemma andi_0_224 : v_andi (Z_to_bv 64 0) 224 = Z_to_bv 64 0.
Proof. bveq. Qed.

(** Target stored byte, lowercase branch: low 8 bits of [b + 224]. *)
Lemma target_upper_lo : forall b : byte, islower b = true ->
  Z_to_bv 8 (bv_unsigned (v_add (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 224)))
  = upperb b.
Proof.
  intros b Hl. destruct (islower_bounds b Hl) as [H1 H2].
  pose proof (u8_range b).
  unfold v_add. rewrite u_zext8.
  change (bv_unsigned (Z_to_bv 64 224)) with 224%Z.
  rewrite u_Z2bv by lia.
  unfold upperb. rewrite Hl.
  apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 8) with 256%Z.
  replace (bv_unsigned b + 224)%Z with ((bv_unsigned b - 32) + 1 * 256)%Z by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma target_upper_hi : forall b : byte, islower b = false ->
  Z_to_bv 8 (bv_unsigned (v_add (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 0)))
  = upperb b.
Proof.
  intros b Hl.
  unfold v_add. rewrite u_zext8.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  rewrite Z.add_0_r. apply sb_upper_hi. exact Hl.
Qed.


(* ######################################################################### *)
(* musl strlen's word-at-a-time zero detection                               *)
(*                                                                           *)
(* gcc 15 lowers the source's [slen] loop to a call to musl's [strlen],      *)
(* which scans EIGHT bytes at a time with the classic bit trick              *)
(*                                                                           *)
(*     hz w  =  (w + 0xfefefefefefefeff) & ~w & 0x8080808080808080           *)
(*                                                                           *)
(* The arithmetic -- the test is zero iff no byte of [w] is zero, with the   *)
(* borrow-chain caveat -- is shared machinery: Common/MuslStrlen proves it   *)
(* over Z ([HZ.Tz_nozero]/[HZ.Tz_haszero]) together with the byte bridge     *)
(* ([zb_of_bytes]) and the instruction-shape bridge ([v_haszero]).  Here we  *)
(* only restate it over [le_bytes_to_word] in the two forms the walk in      *)
(* mmap_upper_ns_source.v consumes.                                          *)
(* ######################################################################### *)

Local Open Scope Z_scope.

(** The machine-level zero-detection value computed by musl's strlen
    word loop: [(w + 0xfefefefefefefeff) & ~w & 0x8080808080808080]. *)
Definition hzw (v : word) : word :=
  v_and (v_and (v_add v (Z_to_bv 64 18374403900871474943))
               (v_xori v (-1)))
        (Z_to_bv 64 9259542123273814144).

Lemma u_hzw : forall v : word, bv_unsigned (hzw v) = HZ.Tz (bv_unsigned v).
Proof. exact v_haszero. Qed.

(** [step_ld]'s value side condition for an arbitrary 8-byte read. *)
Lemma u_le_bytes_to_word8 : forall bs, length bs = 8%nat ->
  bytes_le_to_Z bs = bv_unsigned (le_bytes_to_word bs).
Proof.
  intros bs Hlen. unfold le_bytes_to_word. symmetry.
  pose proof (bytes_le_to_Z_range bs Hlen) as Hb.
  apply u_Z2bv; lia.
Qed.

Lemma hzw_miss : forall bs, length bs = 8%nat ->
  (forall b, In b bs -> bv_unsigned b <> 0%Z) ->
  hzw (le_bytes_to_word bs) = Z_to_bv 64 0.
Proof.
  intros bs Hlen Hnz. apply bv_eq.
  rewrite u_hzw, <- (u_le_bytes_to_word8 bs Hlen).
  assert (Hr : 0 <= bytes_le_to_Z bs < 2^64)
    by (apply bytes_le_to_Z_range; exact Hlen).
  assert (Hz : forall i, (i < 8)%nat -> HZ.zb (bytes_le_to_Z bs) i <> 0).
  { intros i Hi. rewrite zb_of_bytes by lia. apply Hnz, nth_In. lia. }
  rewrite (HZ.Tz_nozero _ Hr Hz). vm_compute. reflexivity.
Qed.

Lemma hzw_hit : forall pre (z : byte) post,
  length (pre ++ z :: post) = 8%nat ->
  (forall b, In b pre -> bv_unsigned b <> 0%Z) -> bv_unsigned z = 0%Z ->
  bv_unsigned (hzw (le_bytes_to_word (pre ++ z :: post))) <> 0%Z.
Proof.
  intros pre z post Hlen Hnz Hz.
  rewrite u_hzw, <- (u_le_bytes_to_word8 _ Hlen).
  assert (Hpre : (length pre < 8)%nat)
    by (rewrite length_app in Hlen; cbn [length] in Hlen; lia).
  apply (HZ.Tz_haszero _ (length pre)).
  - apply bytes_le_to_Z_range. exact Hlen.
  - exact Hpre.
  - rewrite zb_of_bytes by (rewrite length_app; cbn [length]; lia).
    rewrite nth_middle. exact Hz.
  - intros j Hj.
    rewrite zb_of_bytes by (rewrite length_app; cbn [length]; lia).
    rewrite app_nth1 by exact Hj.
    apply Hnz, nth_In. exact Hj.
Qed.

Close Scope Z_scope.

(* ######################################################################### *)
(* Misc numeric facts                                                        *)
(* ######################################################################### *)

Lemma page_round_up_Z_4096 : page_round_up_Z 4096 = 4096%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma pru_4096 : MmapSim.page_round_up (Z_to_bv 64 4096) = Z_to_bv 64 4096.
Proof. bveq. Qed.

(* errno_ret_range/errno_ret_signed live in PropExec; v_addi_0 is
   hypothesis-free. *)
