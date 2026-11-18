(** * arena-tee-ns SOURCE binary: frames, grant facts, and the run to the
      mmap ecall.

    PROOF-SIDE FILE (not part of the trusted specification).

    Machine plan (musl-gcc 15 -Os, see the disassembly comments in
    arena_tee_ns_code.v):

      _start 0x110fc..0x1112c: gp = 0x13800, argc/argv, environ store to
        0x13000, jal main (ra = 0x11128; 0x11128 = li a7,93; ecall).
      main 0x11000..0x11034: frame (sp = rsp-48, six sd's: s1, ra, s0,
        s2, s3, s4), mmap args in a0..a6.
      0x11038 jal raw_syscall 0x11130..0x11150: shuffle into a7=222 and
        ecall at 0x1114c; ret to 0x1103c.
      0x1103c..0x11044: s1 = a0, a0 = 1, [bltz s1] -> 0x110cc (the
        mmap-failure epilogue, exit 1, no output).
      0x11048..0x1105c: s4 = 0xff8 (= cap), s3 = 0xff7 (= cap - 1),
        s2 = s1 (the write cursor), s0 = 0 (the byte count).
      DRAIN LOOP HEAD 0x11060: a1 = s1 + s0 + 8, a2 = s4 - s0
        (= cap - |acc|, exactly [DrainAlg.dcnt]), a0 = 0, jal read.
        [bltz a0] -> 0x110ec (dead in model), [beqz a0] -> 0x11084 (EOF),
        else s0 += a0 and [bgeu s3,s0] loops back — i.e. continue while
        |acc| <= cap - 1, stop at |acc| >= cap.
      TAIL 0x11084..0x110a4: hexword(n,16) -> [sw a0,0(s1)],
        hexword(n,0) -> [sw a0,4(s1)] (the two stores INTO the grant),
        s0 += 8.
      PUT2 LOOP 0x110a8..0x110c4: write(2, s2, s0), [blez a0] -> 0x110f4
        (dead in model), s0 -= a0, s2 += a0, loop while s0 <> 0.
      0x110c8 a0 = 0; epilogue 0x110cc..0x110e8 reloads and rets into
        _start's [li a7,93; ecall].

    Sp-relative addresses/register values are in the canonical
    [Z_to_bv 64 (bv_unsigned rsp - k)] form, pc and rodata constants in
    numeral-literal form, loop indices as [nat_to_word]; all range
    bookkeeping is in [Z] over [bv_unsigned]. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec AllocSim WallSim MmapSim StepTac StreamExec StreamSim StoreOk.
From LinuxProcessSemantics.Common Require Import Footprint SymExec SymTac SymSide SymBranch.
From LinuxProcessSemantics.Common Require Import ShapeAlg DrainAlg RunSegmentsLift.
From LinuxProcessSemantics.Examples.arena_tee_ns Require Import arena_tee_ns_code arena_tee_ns_defs.
From LinuxProcessSemantics.Examples.arena_tee_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.arena_tee_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(** The derivations run from process entry ([init_mkst]'s right side is
    [@mkst fx0 ...]), so the FP register file and [fcsr] of every state
    below are [fx0]'s; no instruction here touches them.  [fx0] itself is
    the instance, so every state here is [init_mkst]'s [@mkst fx0]. *)
#[local] Existing Instance fx0.

(* ================================================================= *)
(* Store legality: everything at/above the data segment base          *)
(* ================================================================= *)

(** Under [-z separate-code] with gcc 15 the image has FOUR LOAD
    segments — 000 ([0x10000,0x11000), headers), 001 ([0x11000,0x12000),
    .text), 002 ([0x12000,0x13000), .rodata/.eh_frame) and the writable
    003 ([0x13000,0x14000)).  Identical to [mmap_upper_ns]'s layout, so
    the bounds below are the same numbers. *)
Lemma source_avoids_data : forall a n : Z, (0x13000 <= a)%Z ->
  range_avoids_ro_segs source_segs a n = true.
Proof.
  intros a n Ha.
  apply range_avoids_ro_above with (data_base := 0x13000%Z);
    [vm_compute; reflexivity | exact Ha].
Qed.

Lemma source_data_wseg : wseg_ok source_segs (0x13000 : word) 4096 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma source_store_ok : forall (m : word -> option byte) (a : word) (k : nat),
  (0x13000 <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat k <= 0x14000)%Z ->
  store_ok source_segs m a k = true.
Proof.
  intros m a k Hlo Hhi.
  eapply store_ok_window with (base := 0x13000%Z) (hi := 0x14000%Z);
    [ | | | exact source_data_wseg | | ];
    [ vm_compute; reflexivity | vm_compute; reflexivity | lia
    | exact Hlo | exact Hhi ].
Qed.

(* ================================================================= *)
(* Grant facts for the source image                                   *)
(* ================================================================= *)

Lemma source_reserved_val :
  segments_reserved source_segs
  = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x1000); (Z_to_bv 64 0x11000, Z_to_bv 64 0x1000);
     (Z_to_bv 64 0x12000, Z_to_bv 64 0x1000); (Z_to_bv 64 0x13000, Z_to_bv 64 0x1000)].
Proof.
  apply (@bool_decide_eq_true_1 (_ = _) _).
  vm_cast_no_check (eq_refl true).
Qed.

(** The run's reservations are the image's: the vDSO pair reserves
    nothing there ([RunSegmentsLift.segments_reserved_vdso]); the image's
    list is concrete, so the split is by computation. *)
Lemma source_reserved_run : forall inp (sp mb : word),
  segments_reserved (run_segments source_segs inp sp mb) = segments_reserved source_segs.
Proof.
  intros inp sp mb.
  replace (segments_reserved (run_segments source_segs inp sp mb))
    with (segments_reserved source_segs
          ++ segments_reserved (vdso_segments (in_kernel inp) sp mb))
    by reflexivity.
  rewrite segments_reserved_vdso, app_nil_r. reflexivity.
Qed.

Lemma source_reserved_low : forall a sz, In (a, sz) (segments_reserved source_segs) ->
  (bv_unsigned a + bv_unsigned sz <= Mmap.task_unmapped_base)%Z.
Proof.
  intros a sz Hin. rewrite source_reserved_val in Hin.
  unfold Mmap.task_unmapped_base.
  repeat destruct Hin as [Hin | Hin];
    try (injection Hin as <- <-; rewrite !u_Z2bv by lia; lia).
  destruct Hin.
Qed.

(** The launch model's one-page grant exists
    ([RunSegmentsLift.grant_witness_init]); the model is [Run]'s:
    [State.with_vdso] of the draw's vDSO counter over [State.init_model]. *)
Lemma source_grant_witness : forall inp (hint brk0 mb sp : word) v,
  (sp_window_lo <= bv_unsigned sp)%Z -> (mmap_base_min <= bv_unsigned mb)%Z ->
  exists a, grant_ok hint
    (with_vdso v (init_model (segments_reserved source_segs) brk0 mb sp source_alloc_limit inp))
    a 4096 = true.
Proof.
  intros inp hint brk0 mb sp v Hsp Hmb.
  apply grant_witness_init; [exact source_reserved_low | exact Hsp | exact Hmb |].
  rewrite source_alloc_limit_val. lia.
Qed.

Lemma source_grant_unpack : forall inp (hint brk0 mb sp aG : word) v,
  grant_ok hint (with_vdso v (init_model (segments_reserved source_segs) brk0 mb sp
                                source_alloc_limit inp)) aG 4096 = true ->
  (0 < bv_unsigned aG)%Z /\ (bv_unsigned aG mod page_size = 0)%Z /\
  (bv_unsigned aG + 4096 <= bv_unsigned sp - stack_max_size)%Z /\
  ((bv_unsigned aG + 4096 <= 0x10000)%Z \/ (0x11000 <= bv_unsigned aG)%Z) /\
  ((bv_unsigned aG + 4096 <= 0x11000)%Z \/ (0x12000 <= bv_unsigned aG)%Z) /\
  ((bv_unsigned aG + 4096 <= 0x12000)%Z \/ (0x13000 <= bv_unsigned aG)%Z).
Proof.
  intros inp hint brk0 mb sp aG v Hg.
  destruct (grant_ok_unpack _ _ _ _ Hg) as (Hal & Hpos & Hceil & Hfree & _).
  change (alloc_top (m_vmmaps (with_vdso v (init_model (segments_reserved source_segs)
            brk0 mb sp source_alloc_limit inp))))
    with (bv_unsigned sp - stack_max_size)%Z in Hceil.
  change (vm_reserved (m_vmmaps (with_vdso v (init_model (segments_reserved source_segs)
            brk0 mb sp source_alloc_limit inp))))
    with (init_reserved (segments_reserved source_segs) mb sp (in_kernel inp)) in Hfree.
  change (vm_maps (m_vmmaps (with_vdso v (init_model (segments_reserved source_segs)
            brk0 mb sp source_alloc_limit inp))))
    with (@nil (word * word)) in Hfree.
  unfold init_reserved in Hfree.
  rewrite source_reserved_val in Hfree.
  cbn [app] in Hfree.
  apply region_free_cons in Hfree. destruct Hfree as [Hda Hfree].
  apply region_free_cons in Hfree. destruct Hfree as [Hdb Hfree].
  apply region_free_cons in Hfree. destruct Hfree as [Hdc _].
  rewrite !u_Z2bv in Hda by lia.
  rewrite !u_Z2bv in Hdb by lia.
  rewrite !u_Z2bv in Hdc by lia.
  refine (conj Hpos (conj Hal (conj Hceil (conj _ (conj _ _))))).
  - destruct Hda as [H|H]; [left; lia | right; lia].
  - destruct Hdb as [H|H]; [left; lia | right; lia].
  - destruct Hdc as [H|H]; [left; lia | right; lia].
Qed.

(** A grant-backed range avoids the read-only segments: a page-sized
    grant cannot start inside the image, so it lies wholly below 0x10000
    or at/above 0x13000. *)
Lemma source_grant_avoids : forall aGZ x k : Z,
  (aGZ + 4096 <= 0x10000 \/ 0x11000 <= aGZ)%Z ->
  (aGZ + 4096 <= 0x11000 \/ 0x12000 <= aGZ)%Z ->
  (aGZ + 4096 <= 0x12000 \/ 0x13000 <= aGZ)%Z ->
  (aGZ <= x)%Z -> (x + k <= aGZ + 4096)%Z ->
  range_avoids_ro_segs source_segs x k = true.
Proof.
  intros aGZ x k Hd1 Hd2 Hd3 Hx1 Hx2.
  assert (Hcase : (x + k <= 0x10000)%Z \/ (0x13000 <= x)%Z).
  { destruct Hd1 as [H1|H1]; [left; lia|].
    destruct Hd2 as [H2|H2]; [left; lia|].
    destruct Hd3 as [H3|H3]; [left; lia| right; lia]. }
  destruct Hcase as [Hbelow | Habove];
    [| apply range_avoids_ro_above with (data_base := 0x13000%Z);
       [vm_compute; reflexivity | lia]].
  unfold source_segs, SourceMemImage_loaded_segments, range_avoids_ro_segs.
  cbn [forallb].
  change (seg_writable SourceMemImage_segment_000) with false.
  change (seg_writable SourceMemImage_segment_001) with false.
  change (seg_writable SourceMemImage_segment_002) with false.
  change (seg_writable SourceMemImage_segment_003) with true.
  change (Z.of_N (seg_base SourceMemImage_segment_000)) with 0x10000%Z.
  change (Z.of_N (seg_base SourceMemImage_segment_001)) with 0x11000%Z.
  change (Z.of_N (seg_base SourceMemImage_segment_002)) with 0x12000%Z.
  assert (Hb0 : (0x10000 <? x + k)%Z = false) by (apply Z.ltb_ge; lia).
  assert (Hb1 : (0x11000 <? x + k)%Z = false) by (apply Z.ltb_ge; lia).
  assert (Hb2 : (0x12000 <? x + k)%Z = false) by (apply Z.ltb_ge; lia).
  rewrite Hb0, Hb1, Hb2. cbn [andb negb orb]. reflexivity.
Qed.

Lemma source_init_pc_val : SourceMemImage_init_pc = 0x110fc%N.
Proof. vm_compute. reflexivity. Qed.



(* ================================================================= *)
(* hexword: the packed digit word, machine-side                       *)
(* ================================================================= *)

(** The executor denotes [andi a5,a5,15] with the materialized-literal
    register [v_and]; bridge back to the immediate spelling [dig_val]
    is stated against (the target file has the same bridge). *)
Lemma v_and_15 : forall x : word, v_and x (Z_to_bv 64 15) = v_andi x 15.
Proof. intro x. unfold v_and, v_andi. f_equal. Qed.

(** hexword's accumulator after [k] of its four iterations, for the
    call whose LOWEST nibble index is [oq] (the 16-argument call: 4,
    the 0-argument call: 0): iteration [j] ors digit [oq+3-j] into
    byte position [j]. *)
Fixpoint hw4 (n oq k : nat) : Z :=
  match k with
  | O => 0%Z
  | S k' => (hw4 n oq k' + digZ n (oq + 3 - k') * 2 ^ (8 * Z.of_nat k'))%Z
  end.

Lemma hw4_range : forall n oq k, (k <= 4)%nat ->
  (0 <= hw4 n oq k < 2 ^ (8 * Z.of_nat k))%Z.
Proof.
  intros n oq k Hk. induction k as [|k IH].
  - cbn. lia.
  - cbn [hw4].
    destruct IH as [IH0 IH1]; [lia|].
    pose proof (digZ_range n (oq + 3 - k)) as Hd.
    assert (Hp : (0 < 2 ^ (8 * Z.of_nat k))%Z) by (apply Z.pow_pos_nonneg; lia).
    split; [nia|].
    replace (8 * Z.of_nat (S k))%Z with (8 * Z.of_nat k + 8)%Z by lia.
    rewrite Z.pow_add_r by lia. nia.
Qed.

(** Disjoint-or is add: the accumulated digits live strictly below the
    bit the new digit enters at. *)
Lemma lor_mul_pow2 : forall d a k : Z, (0 <= k)%Z -> (0 <= a < 2 ^ k)%Z ->
  (0 <= d)%Z -> Z.lor (d * 2 ^ k) a = (d * 2 ^ k + a)%Z.
Proof.
  intros d a k Hk Ha Hd.
  assert (Hland : Z.land (d * 2 ^ k) a = 0%Z).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb i k) eqn:E.
    - apply Z.ltb_lt in E.
      rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - apply Z.ltb_ge in E.
      replace (Z.testbit a i) with false; [apply andb_false_r|].
      symmetry. apply Z.testbit_false; [lia|].
      rewrite Z.div_small; [reflexivity|].
      split; [lia|]. eapply Z.lt_le_trans; [apply Ha|].
      apply Z.pow_le_mono_r; lia. }
  rewrite <- Z.lxor_lor by exact Hland.
  rewrite <- Z.add_nocarry_lxor by exact Hland.
  reflexivity.
Qed.

Lemma hw4_expand : forall n oq,
  hw4 n oq 4
  = (digZ n (oq + 3)
     + (digZ n (oq + 2)
        + (digZ n (oq + 1) + digZ n oq * 256) * 256) * 256)%Z.
Proof.
  intros n oq.
  assert (E1 : (2 ^ (8 * Z.of_nat 0))%Z = 1%Z) by reflexivity.
  assert (E2 : (2 ^ (8 * Z.of_nat 1))%Z = 256%Z) by reflexivity.
  assert (E3 : (2 ^ (8 * Z.of_nat 2))%Z = 65536%Z) by reflexivity.
  assert (E4 : (2 ^ (8 * Z.of_nat 3))%Z = 16777216%Z) by reflexivity.
  cbn [hw4]. rewrite E1, E2, E3, E4.
  replace (oq + 3 - 0)%nat with (oq + 3)%nat by lia.
  replace (oq + 3 - 1)%nat with (oq + 2)%nat by lia.
  replace (oq + 3 - 2)%nat with (oq + 1)%nat by lia.
  replace (oq + 3 - 3)%nat with oq by lia.
  lia.
Qed.

(** The four little-endian bytes of the packed word ARE the four header
    digits, most significant nibble in the LOW byte — exactly [hdr8]'s
    order once the two calls' words are stored at [aG] and [aG+4]. *)
Lemma hw4_bytes : forall n oq,
  word_to_le_bytes 4 (Z_to_bv 64 (hw4 n oq 4))
  = [hex_digit (nib n (oq + 3)); hex_digit (nib n (oq + 2));
     hex_digit (nib n (oq + 1)); hex_digit (nib n oq)].
Proof.
  intros n oq.
  pose proof (digZ_range n (oq + 3)) as H0.
  pose proof (digZ_range n (oq + 2)) as H1.
  pose proof (digZ_range n (oq + 1)) as H2.
  pose proof (digZ_range n oq) as H3.
  pose proof (hw4_expand n oq) as Hz.
  set (d0 := digZ n (oq + 3)) in *.
  set (d1 := digZ n (oq + 2)) in *.
  set (d2 := digZ n (oq + 1)) in *.
  set (d3 := digZ n oq) in *.
  unfold word_to_le_bytes. cbn [Z_to_le_bytes].
  rewrite u_Z2bv by lia.
  rewrite Hz.
  rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 8)%Z with 256%Z.
  assert (D1 : ((d0 + (d1 + (d2 + d3 * 256) * 256) * 256) / 256)%Z
               = (d1 + (d2 + d3 * 256) * 256)%Z)
    by (rewrite Z.div_add, Z.div_small by lia; lia).
  assert (D2 : ((d1 + (d2 + d3 * 256) * 256) / 256)%Z = (d2 + d3 * 256)%Z)
    by (rewrite Z.div_add, Z.div_small by lia; lia).
  assert (D3 : ((d2 + d3 * 256) / 256)%Z = d3)
    by (rewrite Z.div_add, Z.div_small by lia; lia).
  rewrite D1, D2, D3.
  rewrite !hex_digit_digZ.
  fold d0 d1 d2 d3.
  apply f_equal2; [ | apply f_equal2; [ | apply f_equal2;
    [ | apply f_equal2; [ | reflexivity ] ] ] ].
  1-4: (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap;
        change (bv_modulus 8) with 256%Z;
        rewrite ?Z_mod_plus_full; rewrite !Z.mod_small by lia;
        first [ reflexivity | lia ]).
Qed.

(** One digit folded into the packed word, on each side of the
    data-dependent [bltu] split, in exactly the spelling the symbolic
    executor denotes the [addiw]/[sllw]/[or] chain in. *)
Lemma hex_step_lo : forall n oq k, (n <= cap)%nat -> (oq <= 4)%nat ->
  (k < 4)%nat -> (nib n (oq + 3 - k) < 10)%nat ->
  v_or (v_sllw (v_addiw (v_and (v_srl (nat_to_word n)
                                      (Z_to_bv 64 (4 * Z.of_nat (oq + 3 - k))))
                               (Z_to_bv 64 15)) 48)
               (Z_to_bv 64 (8 * Z.of_nat k)))
       (Z_to_bv 64 (hw4 n oq k))
  = Z_to_bv 64 (hw4 n oq (S k)).
Proof.
  intros n oq k Hn Hoq Hk Hd.
  rewrite v_and_15, (dig_val n (oq + 3 - k) _ Hn ltac:(lia) eq_refl).
  pose proof (nib_lt16 n (oq + 3 - k)) as Hn16.
  pose proof (digZ_range n (oq + 3 - k)) as HdR.
  pose proof (hw4_range n oq k ltac:(lia)) as HaR.
  assert (Hpk : (2 ^ (8 * Z.of_nat k) <= 2 ^ 24)%Z)
    by (apply Z.pow_le_mono_r; lia).
  assert (Hpk0 : (0 < 2 ^ (8 * Z.of_nat k))%Z)
    by (apply Z.pow_pos_nonneg; lia).
  assert (Hstep1 : v_addiw (Z_to_bv 64 (Z.of_nat (nib n (oq + 3 - k)))) 48
                   = Z_to_bv 64 (digZ n (oq + 3 - k))).
  { unfold v_addiw.
    rewrite (u_Z2bv (Z.of_nat (nib n (oq + 3 - k)))) by lia.
    rewrite bv_swrap_small
      by (change (bv_half_modulus 32) with (2 ^ 31)%Z; lia).
    unfold digZ. destruct (Nat.ltb_spec (nib n (oq + 3 - k)) 10);
      [f_equal; lia | lia]. }
  rewrite Hstep1.
  assert (Hstep2 : v_sllw (Z_to_bv 64 (digZ n (oq + 3 - k)))
                          (Z_to_bv 64 (8 * Z.of_nat k))
                   = Z_to_bv 64 (digZ n (oq + 3 - k) * 2 ^ (8 * Z.of_nat k))).
  { unfold v_sllw.
    rewrite !u_Z2bv by lia.
    rewrite (Z.mod_small (8 * Z.of_nat k) 32) by lia.
    rewrite Z.shiftl_mul_pow2 by lia.
    rewrite bv_swrap_small
      by (change (bv_half_modulus 32) with (2 ^ 31)%Z; nia).
    reflexivity. }
  rewrite Hstep2.
  unfold v_or.
  rewrite !u_Z2bv by nia.
  rewrite lor_mul_pow2 by lia.
  f_equal. cbn [hw4]. lia.
Qed.

Lemma hex_step_hi : forall n oq k, (n <= cap)%nat -> (oq <= 4)%nat ->
  (k < 4)%nat -> (10 <= nib n (oq + 3 - k))%nat ->
  v_or (v_sllw (v_addiw (v_and (v_srl (nat_to_word n)
                                      (Z_to_bv 64 (4 * Z.of_nat (oq + 3 - k))))
                               (Z_to_bv 64 15)) 87)
               (Z_to_bv 64 (8 * Z.of_nat k)))
       (Z_to_bv 64 (hw4 n oq k))
  = Z_to_bv 64 (hw4 n oq (S k)).
Proof.
  intros n oq k Hn Hoq Hk Hd.
  rewrite v_and_15, (dig_val n (oq + 3 - k) _ Hn ltac:(lia) eq_refl).
  pose proof (nib_lt16 n (oq + 3 - k)) as Hn16.
  pose proof (digZ_range n (oq + 3 - k)) as HdR.
  pose proof (hw4_range n oq k ltac:(lia)) as HaR.
  assert (Hpk : (2 ^ (8 * Z.of_nat k) <= 2 ^ 24)%Z)
    by (apply Z.pow_le_mono_r; lia).
  assert (Hpk0 : (0 < 2 ^ (8 * Z.of_nat k))%Z)
    by (apply Z.pow_pos_nonneg; lia).
  assert (Hstep1 : v_addiw (Z_to_bv 64 (Z.of_nat (nib n (oq + 3 - k)))) 87
                   = Z_to_bv 64 (digZ n (oq + 3 - k))).
  { unfold v_addiw.
    rewrite (u_Z2bv (Z.of_nat (nib n (oq + 3 - k)))) by lia.
    rewrite bv_swrap_small
      by (change (bv_half_modulus 32) with (2 ^ 31)%Z; lia).
    unfold digZ. destruct (Nat.ltb_spec (nib n (oq + 3 - k)) 10);
      [lia | f_equal; lia]. }
  rewrite Hstep1.
  assert (Hstep2 : v_sllw (Z_to_bv 64 (digZ n (oq + 3 - k)))
                          (Z_to_bv 64 (8 * Z.of_nat k))
                   = Z_to_bv 64 (digZ n (oq + 3 - k) * 2 ^ (8 * Z.of_nat k))).
  { unfold v_sllw.
    rewrite !u_Z2bv by lia.
    rewrite (Z.mod_small (8 * Z.of_nat k) 32) by lia.
    rewrite Z.shiftl_mul_pow2 by lia.
    rewrite bv_swrap_small
      by (change (bv_half_modulus 32) with (2 ^ 31)%Z; nia).
    reflexivity. }
  rewrite Hstep2.
  unfold v_or.
  rewrite !u_Z2bv by nia.
  rewrite lor_mul_pow2 by lia.
  f_equal. cbn [hw4]. lia.
Qed.

Lemma word_to_nat_ntw : forall n : nat, (Z.of_nat n < 2^64)%Z ->
  word_to_nat (nat_to_word n) = n.
Proof.
  intros n Hn. unfold word_to_nat. rewrite u_ntw by lia. lia.
Qed.

Lemma c_eq_sub_self : forall x : word, bv_eqb (v_sub x x) (Z_to_bv 64 0) = true.
Proof.
  intro x. rewrite bv_eqb_Z. apply Z.eqb_eq.
  unfold v_sub. rewrite Z.sub_diag. reflexivity.
Qed.


(* ================================================================= *)
(* The source binary's derivation                                     *)
(* ================================================================= *)

(** From here on the file follows [Common/DrainAlg.v]'s [rz_mmap_drain]:
    the mmap prologue, the failure tail, and the bounded drain loop with
    its per-binary loop-head predicate [src_LH]. *)

Section SourceProof.

(** No [fs0] abbreviation here, unlike the other sections that need a
    file system: [src_inv], [src_LH] and [src_tail] below take an
    arbitrary one as a parameter named [fs0], and abbreviating the name
    would shadow those binders. *)
Variable inp : ProcInput.
Local Abbreviation av := (in_argv inp).
Local Abbreviation ev := (in_envp inp).
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.

Variable rsp : word.

(** The entry stack draw this run was started with
    ([Run.ExecEntry]'s [en_draw]): the 16 AT_RANDOM bytes the kernel
    picks afresh at every [execve], and the bytes of the entry stack's
    last page above the block.  This proof may assume NOTHING about
    either, exactly as it may assume nothing about where the stack
    landed.  Quantified per binary, so the target's draw below is a
    different variable. *)
Variable rrnd : EntryDraw.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned rsp)%Z.
Hypothesis Hsp_hi : (bv_unsigned rsp <= sp_window_hi)%Z.

(** This example allocates with mmap and never calls brk, so the initial
    break is read only by the launch conjunct. *)
Variable rbrk : word.
Variable rmb : word.
Hypothesis Hvl : valid_launch inp.

(** The fifth conjunct of [Run.valid_entry_va]: this placement is one a
    Linux launch can give ([create_elf_tables] and [setup_arg_pages],
    fs/binfmt_elf.c and fs/exec.c, Linux v6.18.46).  With [Hvl] it bounds
    the entry block and places the stack-store window. *)
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry rsp rbrk rmb rrnd) inp.

(** [Run.valid_mmap_base]'s floor: it keeps the vDSO pair above the
    grant's gap. *)
Hypothesis Hmb : (mmap_base_min <= bv_unsigned rmb)%Z.

(** The output channel has a reader ([Run.valid_input_channel_reader]). *)
Hypothesis Hrd : in_channel_reader inp = true.

Lemma rsp_lo_num : (0x7fff80000000 <= bv_unsigned rsp)%Z.
Proof. exact Hsp_lo. Qed.
Lemma rsp_hi_num : (bv_unsigned rsp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

Definition argcN : word := len_word av.
(** The initial overlay, with the entry point [init_mkst] passes to it. *)
Definition rwmem : word -> option byte :=
  wrap_mem inp rmb source_phdrs (Z_to_bv 64 (Z.of_N 0x110fc)) rsp rrnd.
(** The run's rom: the image's segments, then the vDSO pair. *)
Definition rrom : word -> option byte := seg_rom (run_segments source_segs inp rsp rmb).

Lemma u_argcN : bv_unsigned argcN = Z.of_nat (length av).
Proof.
  pose proof (valid_argv_len av Hva).
  unfold argcN, len_word. apply u_Z2bv; lia.
Qed.

(** No-overflow bound for the initial stack image, for any entry word. *)
Lemma source_bsb_nw : forall entry : word,
  (bv_unsigned rsp
   + Z.of_nat (length (entry_stack_image inp rmb source_phdrs entry rsp rrnd)) < 2^64)%Z.
Proof.
  intros entry.
  pose proof (bsb_bound Sv48 inp rmb source_phdrs entry rsp rbrk rrnd Hvl Hlau).
  pose proof rsp_hi_num. lia.
Qed.

Lemma v_sll_3 : forall x : word, v_sll x (Z_to_bv 64 3) = v_slli x 3.
Proof. intro x. unfold v_sll, v_slli. f_equal. Qed.

(** The environ value _start stores at 0x13000. *)
Definition envval : word :=
  Z_to_bv 64 (bv_unsigned rsp + 16 + 8 * Z.of_nat (length av)).

Lemma envval_eq : v_addi (v_add (v_addi rsp 8) (v_slli argcN 3)) 8 = envval.
Proof.
  pose proof rsp_hi_num. pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_len av Hva) as Hlen.
  apply bv_eq. unfold envval, v_addi.
  rewrite !Z_to_bv_unsigned.
  rewrite v_add_small
    by (rewrite u_Z2bv by lia; rewrite v_slli_3 by (rewrite u_argcN; lia);
        rewrite u_argcN; lia).
  rewrite u_Z2bv by lia.
  rewrite v_slli_3 by (rewrite u_argcN; lia).
  rewrite u_argcN.
  f_equal; lia.
Qed.

Lemma envval_sym :
  Z_to_bv 64 (bv_unsigned (alu64 ALU_ADD (Z_to_bv 64 (bv_unsigned rsp + 8))
                                         (v_sll argcN (Z_to_bv 64 3))) + 8)
  = envval.
Proof. rewrite alu_add, v_sll_3. exact envval_eq. Qed.

(** Memory after _start's environ store. *)
Definition emem : word -> option byte :=
  wbytes rwmem 0x13000 (word_to_le_bytes 8 envval).

(** Memory after main's prologue: six callee-saved spills into the
    48-byte frame, in execution order (s1@24, ra@40, s0@32, s2@16,
    s3@8, s4@0).  Every saved register is 0 at entry except [ra], which
    is _start's return address 0x11128. *)
Definition fmem : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
    emem
    (Z_to_bv 64 (bv_unsigned rsp - 0x18)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 0x8))  (word_to_le_bytes 8 (0x11128 : word)))
    (Z_to_bv 64 (bv_unsigned rsp - 0x10)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 0x20)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 0x28)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (bv_unsigned rsp - 0x30)) (word_to_le_bytes 8 (Z_to_bv 64 0)).

(* ----------------------------------------------------------------- *)
(* Frame-slot read-back through [fmem]                                *)
(* ----------------------------------------------------------------- *)

Lemma fread_slot_ra :
  rdn source_segs fmem (Z_to_bv 64 (bv_unsigned rsp - 0x8)) 8%nat
  = Some (word_to_le_bytes 8 (0x11128 : word)).
Proof.
  pose proof rsp_lo_num. pose proof rsp_hi_num. unfold fmem.
  repeat (rewrite rdn_wbytes_disjoint
            by (rewrite ?length_N_to_le_bytes; u_norm; lia)).
  apply rdn_wbytes_hit8; u_norm; lia.
Qed.

Lemma fread_slot_0 : forall a,
  In a [Z_to_bv 64 (bv_unsigned rsp - 0x30); Z_to_bv 64 (bv_unsigned rsp - 0x28);
        Z_to_bv 64 (bv_unsigned rsp - 0x20); Z_to_bv 64 (bv_unsigned rsp - 0x18);
        Z_to_bv 64 (bv_unsigned rsp - 0x10)] ->
  rdn source_segs fmem a 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
  intros a Ha. pose proof rsp_lo_num. pose proof rsp_hi_num. unfold fmem.
  repeat destruct Ha as [<- | Ha]; try (exfalso; exact Ha);
    repeat first
      [ apply rdn_wbytes_hit8; u_norm; lia
      | rewrite rdn_wbytes_disjoint
          by (rewrite ?length_N_to_le_bytes; u_norm; lia)
      | rewrite rdn_wbytes_below
          by (rewrite ?length_N_to_le_bytes; u_norm; lia) ].
Qed.

(* ================================================================= *)
(* The mmap ecall state                                               *)
(* ================================================================= *)

(** [main] puts the six mmap arguments in a0..a6 and tail-calls the
    crt's [raw_syscall], whose seven [mv]s leave a7 = 222, a0 = 0
    (hint), a1 = 4096, a2 = 3, a3 = 34, a4 = -1, a5 = 0, with the ecall
    at 0x1114c pending. *)
Definition src_mmap_ms (regs : bvmap 5 word) : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := 0x1114c;
     ms_svc_pending := Some (getr regs 17); ms_resv := None;
     ms_fcsr := fp_csr; ms_mem := fmem; ms_rom := rrom |}.

Lemma src_to_mmap :
  exists regs,
    getr regs 1 = (0x1103c : word) /\
    getr regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) /\
    getr regs 11 = Z_to_bv 64 4096 /\
    getr regs 12 = Z_to_bv 64 3 /\
    getr regs 13 = Z_to_bv 64 34 /\
    getr regs 14 = Z_to_bv 64 (2^64 - 1) /\
    getr regs 15 = Z_to_bv 64 0 /\
    getr regs 10 = Z_to_bv 64 0 /\
    bv_unsigned (getr regs 17) = 222%Z /\
    msteps source_segs
      (init_machine_state (run_segments source_segs inp rsp rmb) SourceMemImage_init_pc
         source_phdrs rsp rmb rrnd inp)
      (src_mmap_ms regs).
(** THIRTY-THREE instructions in ONE reflective block: the whole crt
    entry sequence (gp setup, the [ld] of argc, the envp pointer
    arithmetic and its store into musl's [__environ] slot, the [jal]
    into main), main's frame push with its SIX spills and six mmap
    argument [li]s, the [jal] into the crt's [raw_syscall] and its
    seven register moves — stopping at the [ecall] that is the mmap
    branch point.  Seven stores and one load, no branches.  The five
    callee-saved registers are PINNED to [ELit 0] so that their spilled
    values are literals, which is what makes the exit memory literally
    [fmem]. *)
Proof.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (valid_argv_len av Hva) as Hlen.
  pose proof u_argcN as Hu.
  rewrite source_init_pc_val, init_mkst.
  sym_block_ex source_segs
    (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 rsp)
          (Z_to_bv 64 (Z.of_N 0x110fc))
          (wrap_mem inp rmb source_phdrs (Z_to_bv 64 (Z.of_N 0x110fc)) rsp rrnd)
          (seg_rom (run_segments source_segs inp rsp rmb)))
    40%nat (@nil bool) (@nil expr)
    [((2 : reg), EVar 32); ((8 : reg), ELit 0); ((9 : reg), ELit 0);
     ((18 : reg), ELit 0); ((19 : reg), ELit 0); ((20 : reg), ELit 0)]
    [rsp] [argcN] RA HRA Hms.
  (* the six frame spills *)
  1-6: solve_store_ok.
  (* [sd a2,0(t1)] at 0x11120 -> musl's [__environ] slot at 0x13000 *)
  1: (apply source_store_ok; u_norm; lia).
  { (* [ld a0,0(sp)] at 0x11104 -> argc, out of the initial stack image *)
    replace (Z_to_bv 64 (bv_unsigned rsp + 0)) with rsp
      by (apply bv_eq; u_norm; lia);
    exists (word_le8 argcN); split;
      [ rewrite rdn_wrap_stack_above by lia;
        apply read_argc; apply source_bsb_nw
      | apply bytes_le_n_to_le_8 ]. }
  exists RA.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ _))))))))).
  1-9: (sym_regs HRA;
        first [ reflexivity | assumption | (f_equal; lia)
              | (apply bv_eq; u_norm; lia) | bveq ]).
  unfold src_mmap_ms.
  eapply msteps_trans;
    [ unfold fmem, emem, rwmem, rrom; revert Hms; sym_mem_norm;
      rewrite envval_sym; exact (fun x => x) | ].
  norm_pc; sym_pc_lit.
  eapply mst_step;
    [ reflexivity | exact (step_ecall _ _ _ _ _ _ SF_1114c eq_refl) | apply mst_refl ].
Qed.

(** The failure tail: the crt wrapper's [ret], [mv s1,a0], [li a0,1],
    the taken [bltz s1] and the shared epilogue into _start's exit. *)
Lemma src_fail_wexit : forall regs e,
  (1 <= e)%Z -> (e <= 4095)%Z ->
  getr regs 1 = (0x1103c : word) ->
  getr regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) ->
  to_wexit source_segs
    (advance_past_svc (set_gpr0 (src_mmap_ms regs) (errno_ret e)))
    [] (Z_to_bv 64 1).
(** THIRTEEN instructions in ONE reflective block: the crt wrapper's
    [ret], the [mv s1,a0] of the negative return value, [li a0,1], the
    taken [bltz s1], the shared epilogue's six reloads and stack pop,
    and main's [ret] into _start's [li a7,93].  No write happens on this
    path, so the buffer list is empty and the code is 1. *)
Proof.
  intros regs e He1 He2 Hr1 Hr2.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (errno_ret_range e He1 He2) as [Her1 Her2].
  unfold src_mmap_ms. rewrite adv_set. norm_pc.
  sym_block source_segs 13%nat [true]
    [ELit 0x11128; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0]
    [((1 : reg), ELit 0x1103c); ((2 : reg), EVar 32); ((10 : reg), EVar 33)]
    [Z_to_bv 64 (bv_unsigned rsp - 0x30); errno_ret e] (@nil word) RA HRA.
  (* the six frame reloads, out of [fmem], in the executor's reverse order *)
  1-6: (eexists; split;
        [ solve [ apply fread_slot_0; repeat first [ left; reflexivity | right ]
                | exact fread_slot_ra ]
        | first [ apply bytes_le_to_Z_8
                | (rewrite bytes_le_to_Z_8; vm_compute; reflexivity) ] ]).
  { (* [bltz s1] at 0x11044 -> taken: the raw syscall returned [-e] *)
    apply (c_lts_neg_0 (errno_ret e)); lia. }
  (* the three pins: the wrapper's [ra], the frame [sp], the errno in [a0] *)
  1-3: (getr_resolve; regupd_resolve; rewrite <- ?getr_nz by reg_neq_tac;
        first [ reflexivity
              | (rewrite Hr1; sym_close)
              | (rewrite Hr2; sym_close) ]).
  (* 0x1112c: the exit [ecall] *)
  eapply tw_step;
    [ reflexivity | exact (step_ecall _ _ _ _ _ _ SF_1112c eq_refl) | ].
  apply tw_exit_coden.
  - sym_regs HRA. vm_compute. reflexivity.
  - sym_regs HRA. reflexivity.
  - u_norm; lia.
Qed.

(* ================================================================= *)
(* The grant: bounds, memory, and the loop invariant                  *)
(* ================================================================= *)

Definition gbounds (aG : word) : Prop :=
  (0 < bv_unsigned aG)%Z /\
  (bv_unsigned aG mod page_size = 0)%Z /\
  (bv_unsigned aG + 4096 <= bv_unsigned rsp - stack_max_size)%Z /\
  ((bv_unsigned aG + 4096 <= 0x10000)%Z \/ (0x11000 <= bv_unsigned aG)%Z) /\
  ((bv_unsigned aG + 4096 <= 0x11000)%Z \/ (0x12000 <= bv_unsigned aG)%Z) /\
  ((bv_unsigned aG + 4096 <= 0x12000)%Z \/ (0x13000 <= bv_unsigned aG)%Z).

(** The zero-filled grant, layered on the post-prologue memory. *)
Definition gmem (aG : word) : word -> option byte :=
  zfill aG (Z_to_bv 64 4096) fmem.

(** Memories reachable from [gmem aG]: the overlay only grows, and they
    agree with [fmem] outside the musl wrappers' 8-byte [ra] scratch
    slot at [rsp-0x38] and outside the grant. *)
Definition mem_ok (aG : word) (mem : word -> option byte) : Prop :=
  mem_grows (gmem aG) mem /\
  (forall (a : word) (n : nat),
     (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
     ((bv_unsigned rsp - 0x30 <= bv_unsigned a)%Z \/
      (bv_unsigned a + Z.of_nat n <= bv_unsigned rsp - 0x38)%Z) ->
     ((bv_unsigned aG + 4096 <= bv_unsigned a)%Z \/
      (bv_unsigned a + Z.of_nat n <= bv_unsigned aG)%Z) ->
     rdn source_segs mem a n = rdn source_segs fmem a n).

Lemma mem_ok_grows_w : forall aG mem, mem_ok aG mem -> mem_grows rwmem mem.
Proof.
  intros aG mem [Hg _]. eapply mem_grows_trans; [| exact Hg].
  unfold gmem, zfill, fmem, emem. solve_mem_grows.
Qed.

Local Hint Resolve mem_ok_grows_w : store_ok_db.

Lemma gmem_ok : forall aG, gbounds aG -> mem_ok aG (gmem aG).
Proof.
  intros aG Hb. split; [apply mem_grows_refl|].
  intros a n Hnw _ Hd. unfold gmem.
  apply rdn_zfill_out; [exact Hnw|].
  destruct Hd as [H|H]; [right | left];
    change (bv_unsigned (Z_to_bv 64 4096)) with 4096%Z; lia.
Qed.

(** A grant lies entirely below the stack: [State.alloc_top] is a
    stack's width under this run's [sp]. *)
Lemma grant_below_stack : forall aG, gbounds aG ->
  (bv_unsigned aG + 4096 <= bv_unsigned rsp - 0x800000)%Z.
Proof.
  intros aG (_ & _ & Hc & _). unfold stack_max_size in Hc. lia.
Qed.

(** Every store inside the grant is legal in any [mem_ok] memory. *)
Lemma grant_store_ok : forall aG mem (a : word) (k : nat),
  mem_ok aG mem -> gbounds aG ->
  (bv_unsigned aG <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat k <= bv_unsigned aG + 4096)%Z ->
  store_ok source_segs mem a k = true.
Proof.
  intros aG mem a k [Hg _] (_ & _ & Hc & _) Hlo Hhi.
  pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  eapply store_ok_mono; [exact Hg|].
  unfold gmem, zfill. apply store_ok_zmem;
    [ | exact Hlo | ];
    change (bv_unsigned (Z_to_bv 64 4096)) with 4096%Z; lia.
Qed.

(** An 8-byte store into the wrappers' scratch slot preserves [mem_ok]. *)
Lemma mem_ok_scratch8 : forall aG mem (a v : word),
  mem_ok aG mem -> gbounds aG ->
  (bv_unsigned rsp - 0x38 <= bv_unsigned a)%Z ->
  (bv_unsigned a + 8 <= bv_unsigned rsp - 0x30)%Z ->
  mem_ok aG (wbytes mem a (word_to_le_bytes 8 v)).
Proof.
  intros aG mem a v [Hg Hm] Hb Hlo Hhi. pose proof rsp_hi_num.
  pose proof (grant_below_stack aG Hb).
  split; [solve_mem_grows|].
  intros a' n Hnw Hd Hdg.
  destruct Hd as [Hd | Hd].
  - rewrite rdn_wbytes_disjoint by (rewrite ?length_N_to_le_bytes; lia).
    apply Hm; [exact Hnw | left; exact Hd | exact Hdg].
  - rewrite rdn_wbytes_below by (rewrite ?length_N_to_le_bytes; lia).
    apply Hm; [exact Hnw | right; exact Hd | exact Hdg].
Qed.

(** A block delivered by [read] into the arena preserves [mem_ok]. *)
Lemma mem_ok_grant : forall aG mem (a : word) bs,
  mem_ok aG mem -> gbounds aG ->
  (bv_unsigned aG <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned aG + 4096)%Z ->
  mem_ok aG (wbytes mem a bs).
Proof.
  intros aG mem a bs [Hg Hm] (_ & _ & Hc & _) Hlo Hhi. split; [solve_mem_grows|].
  pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  intros a' n Hnw Hd Hdg.
  rewrite rdn_wbytes_out
    by (first [ destruct Hdg as [H|H]; [right | left]; lia | lia ]).
  apply Hm; assumption.
Qed.

(** A block delivered by [read] into the arena preserves [mem_ok]. *)
Lemma mem_ok_buf : forall aG mem (buf : word) bs,
  mem_ok aG mem -> gbounds aG ->
  (bv_unsigned aG <= bv_unsigned buf)%Z ->
  (bv_unsigned buf + Z.of_nat (length bs) <= bv_unsigned aG + 4096)%Z ->
  mem_ok aG (write_to_mem mem buf bs).
Proof.
  intros aG mem buf bs Hm Hb Hlo Hhi. rewrite write_to_mem_wbytes.
  apply mem_ok_grant; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(* The loop / tail invariant                                          *)
(* ----------------------------------------------------------------- *)

(** [s1] holds the arena base, [s2] the put2 write cursor (still the
    base), [s4] = 4088 = [cap], [s3] = 4087, [s0] the count drained so
    far; the arena at [aG + 8] holds exactly those bytes.  [pc] is the
    drain loop head 0x11060 while there is capacity left and the header
    block 0x11084 once the arena is full — the source jumps straight to
    the header when the last read fills it, so [DrainAlg]'s single
    loop-head predicate has to cover both. *)
Definition src_inv (fs0 : Fs.Fs) (acc : list byte) (pc : word) (c : config) : Prop :=
  exists (aG : word) (regs : bvmap 5 word) (mem : word -> option byte),
    gbounds aG /\
    m_halted (cfg_model c) = None /\
    m_vm_lazy (cfg_model c) = [] /\
    m_fs (cfg_model c) = fs0 /\
    fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 0)
      = Some (FdChannel (Z_to_bv 64 0)) /\
    fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) (cfg_model c) /\
    msteps source_segs (cfg_ms c) (mkst regs pc mem rrom) /\
    getr regs 9 = aG /\
    getr regs 18 = aG /\
    getr regs 20 = Z_to_bv 64 4088 /\
    getr regs 19 = Z_to_bv 64 4087 /\
    getr regs 8 = nat_to_word (length acc) /\
    getr regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) /\
    (length acc <= cap)%nat /\
    mem_ok aG mem /\
    rdn source_segs mem (Z_to_bv 64 (bv_unsigned aG + 8)) (length acc)
      = Some acc.

Definition src_LH (fs0 : Fs.Fs) (acc : list byte) (c : config) : Prop :=
  src_inv fs0 acc
    (if (cap <=? length acc)%nat then (0x11084 : word) else (0x11060 : word)) c.

(* ----------------------------------------------------------------- *)
(* Arena addresses and the wrappers' scratch slot                     *)
(* ----------------------------------------------------------------- *)

(** The read buffer at loop head [k]: the arena base, past the eight
    header bytes, past what has already been drained. *)
Definition bufA (aG : word) (k : nat) : word :=
  Z_to_bv 64 (bv_unsigned aG + 8 + Z.of_nat k).

(** The 8-byte slot the musl read/write wrappers spill [ra] into. *)
Definition scr : word := Z_to_bv 64 (bv_unsigned rsp - 0x38).

Lemma bufA_split : forall aG k, gbounds aG -> (k <= cap)%nat ->
  Z_to_bv 64 (bv_unsigned aG + 8) + nat_to_word k = bufA aG k.
Proof.
  intros aG k (_ & _ & Hc & _) Hk. pose proof (u64_range aG). unfold bufA.
  pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  rewrite word_add_nat.
  rewrite u_Z2bv by (unfold cap in *; lia).
  f_equal; lia.
Qed.

Lemma bufA_calc : forall (aG : word) k, gbounds aG -> (k <= cap)%nat ->
  Z_to_bv 64 (bv_unsigned aG + (bv_unsigned (nat_to_word k) + 8)) = bufA aG k.
Proof.
  intros aG k (_ & _ & Hc & _) Hk.
  pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  assert (Huk : bv_unsigned (nat_to_word k) = Z.of_nat k)
    by (apply u_ntw; unfold cap in *; lia).
  unfold bufA. rewrite Huk. f_equal; lia.
Qed.

Lemma dcnt_src : forall (aG : word) k, (k <= cap)%nat ->
  v_sub (Z_to_bv 64 4088) (nat_to_word k) = Z_to_bv 64 (Z.of_nat (cap - k)).
Proof.
  intros aG k Hk. apply bv_eq.
  rewrite v_sub_small by (rewrite u_ntw, u_Z2bv; unfold cap in *; lia).
  rewrite u_ntw by (unfold cap in *; lia).
  rewrite !u_Z2bv by (unfold cap in *; lia). unfold cap in *. lia.
Qed.

(* ----------------------------------------------------------------- *)
(* The obligations                                                    *)
(* ----------------------------------------------------------------- *)

(** The grant lands the binary on the drain loop head with an empty
    accumulator: 0x1103c..0x1105c, [mv s1,a0], the untaken [bltz s1],
    and the four setup [li]/[mv]s. *)
Lemma src_grant_LH : forall regs (hint : word) a,
  getr regs 1 = (0x1103c : word) ->
  getr regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) ->
  getr regs 11 = Z_to_bv 64 4096 ->
  grant_ok hint (with_vdso (Vdso.vdso_run_init (ed_vdso rrnd))
                  (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)) a
    (page_round_up_Z (bv_unsigned (ms_gpr (src_mmap_ms regs) 1))) = true ->
  src_LH (in_fs inp) []
    (mkCfg (advance_past_svc
              (apply_effect (src_mmap_ms regs)
                 (mkEffect a []
                    [(a, page_round_up (ms_gpr (src_mmap_ms regs) 1))])))
           (mmap_model a (page_round_up (ms_gpr (src_mmap_ms regs) 1))
              (with_vdso (Vdso.vdso_run_init (ed_vdso rrnd))
                 (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)))).
(** TEN instructions in ONE reflective block: the crt wrapper's [ret],
    [mv s1,a0] of the grant address, [li a0,1], the untaken [bltz s1],
    and the four setup instructions that put [cap] in s4, [cap-1] in s3,
    the base in s2 and 0 in s0. *)
Proof.
  intros regs hint a Hr1 Hr2 H11 Hg.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  assert (Hga : ms_gpr (src_mmap_ms regs) 1 = Z_to_bv 64 4096).
  { unfold ms_gpr, src_mmap_ms; cbn [ms_regs]; rewrite arg_reg_1;
    rewrite <- getr_nz by reg_neq_tac; exact H11. }
  rewrite Hga in Hg |- *.
  change (page_round_up_Z (bv_unsigned (Z_to_bv 64 4096))) with 4096%Z in Hg.
  destruct (source_grant_unpack inp _ rbrk rmb rsp a _ Hg)
    as (Hpos & Hal & Hceil & Hda & Hdb & Hdc).
  assert (Hb : gbounds a)
    by (repeat split; assumption).
  rewrite pru_4096.
  unfold src_mmap_ms. rewrite adv_apply.
  replace (v_addi (0x1114c : word) 4) with (Z_to_bv 64 0x11150) by bveq.
  sym_block_ex source_segs
    (mkst (regupd regs 10 a) (Z_to_bv 64 0x11150)
          (zfill a (Z_to_bv 64 4096) fmem) rrom)
    10%nat [false] (@nil expr)
    [((1 : reg), ELit 0x1103c); ((2 : reg), EVar 32); ((10 : reg), EVar 33)]
    [Z_to_bv 64 (bv_unsigned rsp - 0x30); a] (@nil word) RA HRA Hms.
  { (* [bltz s1] at 0x11044 -> not taken: the grant address is positive *)
    apply (c_lts_pos_0 a); lia. }
  1-3: (getr_resolve; regupd_resolve; rewrite <- ?getr_nz by reg_neq_tac;
        first [ reflexivity
              | (rewrite Hr1; sym_close)
              | (rewrite Hr2; sym_close) ]).
  unfold src_LH.
  change ((cap <=? length (@nil byte))%nat) with false. cbv iota.
  exists a, RA, (zfill a (Z_to_bv 64 4096) fmem).
  cbn [cfg_ms cfg_model].
  refine (conj Hb (conj eq_refl (conj _
    (conj eq_refl (conj eq_refl (conj _ (conj _ _))))))).
  { rewrite mmap_model_lazy. reflexivity. }
  { split; [reflexivity | split; [reflexivity | exact Hrd]]. }
  { replace (0x11060 : word) with (Z_to_bv 64 0x11060) by bveq. exact Hms. }
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  1-6: (sym_regs HRA; sym_close).
  - cbn [length]; unfold cap; lia.
  - apply gmem_ok; exact Hb.
  - reflexivity.
Qed.

(** The drain loop's [add s0,s0,a0]: the accumulated count plus the
    delivered block length, back in [nat_to_word] form. *)
Lemma ntw_add_len : forall k (bs : list byte), (k + length bs <= cap)%nat ->
  v_add (nat_to_word k) (len_word bs) = nat_to_word (k + length bs).
Proof.
  intros k bs H. unfold v_add. apply bv_eq.
  rewrite (u_ntw k) by (unfold cap in *; lia).
  rewrite u_len_word by (unfold cap in *; lia).
  rewrite u_Z2bv by (unfold cap in *; lia).
  rewrite u_ntw by (unfold cap in *; lia). lia.
Qed.

(* ----------------------------------------------------------------- *)
(* From the drain loop head to the read ecall                          *)
(* ----------------------------------------------------------------- *)

(** TWENTY-THREE instructions in ONE reflective block: the loop head's
    three argument computations ([a1 = s1 + s0 + 8],
    [a2 = s4 - s0 = cap - |acc|], [a0 = 0]), the [jal] into musl's
    [read], its frame push, seven-register shuffle and [ra] spill, the
    [j] into [__syscall_cp] and [__syscall_cp_c]'s seven moves — the
    executor stops of its own accord at the [ecall] at 0x11258.  One
    store, no loads, no branches. *)
Lemma src_read_block : forall (aG : word) (regs : bvmap 5 word) mem (k : nat),
  gbounds aG -> (k <= cap)%nat -> mem_ok aG mem ->
  getr regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) ->
  getr regs 8 = nat_to_word k ->
  getr regs 9 = aG -> getr regs 18 = aG ->
  getr regs 19 = Z_to_bv 64 4087 -> getr regs 20 = Z_to_bv 64 4088 ->
  exists R1,
    getr R1 1 = (0x111c4 : word) /\
    getr R1 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40) /\
    getr R1 8 = nat_to_word k /\
    getr R1 9 = aG /\ getr R1 18 = aG /\
    getr R1 19 = Z_to_bv 64 4087 /\ getr R1 20 = Z_to_bv 64 4088 /\
    bv_unsigned (getr R1 17) = 63%Z /\
    getr R1 10 = Z_to_bv 64 0 /\
    getr R1 11 = bufA aG k /\
    getr R1 12 = Z_to_bv 64 (Z.of_nat (cap - k)) /\
    msteps source_segs (mkst regs (Z_to_bv 64 0x11060) mem rrom)
      (mkst R1 (Z_to_bv 64 0x11258)
            (wbytes mem scr (word_to_le_bytes 8 (0x11074 : word))) rrom).
Proof.
  intros aG regs mem k Hb Hk Hmok H2 H8 H9 H18 H19 H20.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  sym_block_ex source_segs (mkst regs (Z_to_bv 64 0x11060) mem rrom)
    30%nat (@nil bool) (@nil expr)
    [((2 : reg), EVar 32); ((8 : reg), EVar 33); ((9 : reg), EVar 34);
     ((18 : reg), EVar 34); ((19 : reg), ELit 4087); ((20 : reg), ELit 4088)]
    [Z_to_bv 64 (bv_unsigned rsp - 0x30); nat_to_word k; aG]
    (@nil word) R1 HR1 Hms.
  { (* the read wrapper's [ra] spill, inside the stack window *)
    eapply store_ok_mono; [ apply (mem_ok_grows_w aG mem Hmok) | ].
    unfold rwmem.
    apply (store_ok_wrap_window_valid source_segs inp rmb source_phdrs _ rsp rbrk _ _ rrnd
             Hvl Hlau);
      unfold stack_window_reach, stack_max_size; u_norm; lia. }
  1-6: (rewrite <- ?getr_nz by reg_neq_tac;
        first [ reflexivity
              | (rewrite H2; sym_close) | (rewrite H8; sym_close)
              | (rewrite H9; sym_close) | (rewrite H18; sym_close)
              | (rewrite H19; sym_close) | (rewrite H20; sym_close) ]).
  exists R1.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ (conj _ (conj _ _))))))))))).
  1-11: (sym_regs HR1; rewrite ?alu_add, ?alu_sub;
         first [ reflexivity
               | (apply bufA_calc; assumption)
               | (apply (dcnt_src aG); exact Hk)
               | sym_close ]).
  unfold scr. revert Hms. sym_mem_norm. exact (fun x => x).
Qed.

(** The state the drain loop's [read] ecall dispatches from. *)
Definition src_rd_ms (R1 : bvmap 5 word) (mem : word -> option byte)
  : machine_state :=
  {| ms_regs := R1; ms_fregs := fp_regs; ms_pc_val := 0x11258;
     ms_svc_pending := Some (getr R1 17); ms_resv := None;
     ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rrom |}.

(* ----------------------------------------------------------------- *)
(* The read wrapper's return path                                     *)
(* ----------------------------------------------------------------- *)

(** The side conditions the wrappers' return path emits: the [ra]
    reload out of the scratch slot, and the branch tests, one of whose
    operands is [__syscall_ret]'s [lui a5,0xfffff] = -4096. *)
Local Ltac ret_sc Hra :=
  exists (word_to_le_bytes 8 (0x11074 : word)); split;
    [ unfold scr in Hra; exact Hra
    | rewrite bytes_le_to_Z_8; vm_compute; reflexivity ].

(** The block resolution's four branch tests, plus the same reload.
    [__syscall_ret]'s [lui a5,0xfffff] is [-4096], whose [bv_unsigned]
    no [u_norm] can produce, so it gets an alternative of its own. *)
Local Ltac blk_sc Hra Huk Hul :=
  first
    [ solve [ ret_sc Hra ]
    | solve [ rewrite ?negb_true_iff, ?negb_false_iff, ?bv_ltu_Z;
              replace (bv_unsigned (Z_to_bv 64 (-4096)))
                 with 18446744073709547520%Z by (vm_compute; reflexivity);
              rewrite ?Z.ltb_ge, ?Z.ltb_lt, ?Hul; lia ]
    | solve [ rewrite ?negb_true_iff, ?negb_false_iff;
              rewrite ?bv_ltu_Z, ?bv_eqb_Z;
              rewrite ?bv_lts_small by (rewrite ?Hul; u_norm; lia);
              unfold v_add;
              rewrite ?u_Z2bv by (rewrite ?Huk, ?Hul; lia);
              rewrite ?Z.ltb_ge, ?Z.ltb_lt, ?Z.eqb_eq, ?Z.eqb_neq;
              rewrite ?Huk, ?Hul; lia ] ].

(** From the post-ecall state at 0x1125c back through
    [__syscall_cp_c]'s [ret], the [read] wrapper's reload and pop,
    [__syscall_ret]'s untaken errno [bltu] and its [ret], to main's
    two tests of the return value.  A channel read never returns an
    error ([ReadWrite.read_spec]), so the [bltz] at 0x11074 is dead.

    EOF (a0 = 0) takes the [beqz] at 0x11078 into the header block. *)
Lemma src_ret_eof : forall (aG : word) (R1 : bvmap 5 word) mem (k : nat),
  getr R1 1 = (0x111c4 : word) ->
  getr R1 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40) ->
  getr R1 8 = nat_to_word k ->
  getr R1 9 = aG -> getr R1 18 = aG ->
  getr R1 19 = Z_to_bv 64 4087 -> getr R1 20 = Z_to_bv 64 4088 ->
  rdn source_segs mem scr 8%nat = Some (word_to_le_bytes 8 (0x11074 : word)) ->
  exists R2,
    getr R2 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) /\
    getr R2 8 = nat_to_word k /\
    getr R2 9 = aG /\ getr R2 18 = aG /\
    getr R2 19 = Z_to_bv 64 4087 /\ getr R2 20 = Z_to_bv 64 4088 /\
    msteps source_segs
      (mkst (regupd R1 10 (Z_to_bv 64 0)) (Z_to_bv 64 0x1125c) mem rrom)
      (mkst R2 (Z_to_bv 64 0x11084) mem rrom).
Proof.
  intros aG R1 mem k H1 H2 H8 H9 H18 H19 H20 Hra.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  sym_block_ex source_segs
    (mkst (regupd R1 10 (Z_to_bv 64 0)) (Z_to_bv 64 0x1125c) mem rrom)
    9%nat [false; false; true] [ELit 0x11074]
    [((1 : reg), ELit 0x111c4); ((2 : reg), EVar 32); ((8 : reg), EVar 33);
     ((9 : reg), EVar 34); ((18 : reg), EVar 34); ((19 : reg), ELit 4087);
     ((20 : reg), ELit 4088); ((10 : reg), ELit 0)]
    [Z_to_bv 64 (bv_unsigned rsp - 0x40); nat_to_word k; aG]
    (@nil word) R2 HR2 Hms.
  1: ret_sc Hra.
  1-8: (getr_resolve; regupd_resolve; rewrite <- ?getr_nz by reg_neq_tac;
        first [ reflexivity
              | (rewrite H1; sym_close) | (rewrite H2; sym_close)
              | (rewrite H8; sym_close) | (rewrite H9; sym_close)
              | (rewrite H18; sym_close) | (rewrite H19; sym_close)
              | (rewrite H20; sym_close) ]).
  exists R2. repeat split.
  1-6: (sym_regs HR2; sym_close).
  exact Hms.
Qed.

(** A delivered block (a0 = |bs| > 0) falls through both tests, adds the
    count into s0 and re-enters the loop at 0x11060 — unless it has
    just filled the arena, in which case the [bgeu s3,s0] at 0x11080 is
    not taken and control falls into the header block at 0x11084.  That
    is why [src_LH] carries the pc as a function of the fullness. *)
Lemma src_ret_blk : forall (aG : word) (R1 : bvmap 5 word) mem (k : nat) (bs : list byte),
  getr R1 1 = (0x111c4 : word) ->
  getr R1 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40) ->
  getr R1 8 = nat_to_word k ->
  getr R1 9 = aG -> getr R1 18 = aG ->
  getr R1 19 = Z_to_bv 64 4087 -> getr R1 20 = Z_to_bv 64 4088 ->
  rdn source_segs mem scr 8%nat = Some (word_to_le_bytes 8 (0x11074 : word)) ->
  (1 <= length bs)%nat -> (k + length bs <= cap)%nat ->
  exists R2,
    getr R2 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) /\
    getr R2 8 = nat_to_word (k + length bs) /\
    getr R2 9 = aG /\ getr R2 18 = aG /\
    getr R2 19 = Z_to_bv 64 4087 /\ getr R2 20 = Z_to_bv 64 4088 /\
    msteps source_segs
      (mkst (regupd R1 10 (len_word bs)) (Z_to_bv 64 0x1125c) mem rrom)
      (mkst R2 (if (cap <=? k + length bs)%nat
                then Z_to_bv 64 0x11084 else Z_to_bv 64 0x11060) mem rrom).
Proof.
  intros aG R1 mem k bs H1 H2 H8 H9 H18 H19 H20 Hra Hlo Hhi.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  assert (Huk : bv_unsigned (nat_to_word k) = Z.of_nat k)
    by (apply u_ntw; unfold cap in *; lia).
  assert (Hul : bv_unsigned (len_word bs) = Z.of_nat (length bs))
    by (apply u_len_word; unfold cap in *; lia).
  destruct (Nat.leb_spec cap (k + length bs)) as [Hfull | Hpart].
  - (* the arena is now full: the [bgeu] is NOT taken *)
    sym_block_ex source_segs
      (mkst (regupd R1 10 (len_word bs)) (Z_to_bv 64 0x1125c) mem rrom)
      11%nat [false; false; false; false] [ELit 0x11074]
      [((1 : reg), ELit 0x111c4); ((2 : reg), EVar 32); ((8 : reg), EVar 33);
       ((9 : reg), EVar 34); ((18 : reg), EVar 34); ((19 : reg), ELit 4087);
       ((20 : reg), ELit 4088); ((10 : reg), EVar 35)]
      [Z_to_bv 64 (bv_unsigned rsp - 0x40); nat_to_word k; aG; len_word bs]
      (@nil word) R2 HR2 Hms.
    5: ret_sc Hra.
    4: (rewrite bv_ltu_Z; apply Z.ltb_ge; rewrite Hul;
        replace (bv_unsigned (Z_to_bv 64 (-4096))) with 18446744073709547520%Z
          by (vm_compute; reflexivity); unfold cap in *; lia).
    3: (rewrite bv_lts_small by (rewrite ?Hul, ?u_Z2bv; unfold cap in *; lia);
        apply Z.ltb_ge; rewrite Hul, u_Z2bv by lia; lia).
    2: (rewrite bv_eqb_Z; apply Z.eqb_neq; rewrite Hul, u_Z2bv by lia; lia).
    1: (rewrite negb_false_iff, bv_ltu_Z; apply Z.ltb_lt; unfold v_add;
        rewrite !u_Z2bv by (rewrite ?Huk, ?Hul; unfold cap in *; lia);
        rewrite Huk, Hul; unfold cap in *; lia).

    1-8: (getr_resolve; regupd_resolve; rewrite <- ?getr_nz by reg_neq_tac;
          first [ reflexivity
                | (rewrite H1; sym_close) | (rewrite H2; sym_close)
                | (rewrite H8; sym_close) | (rewrite H9; sym_close)
                | (rewrite H18; sym_close) | (rewrite H19; sym_close)
                | (rewrite H20; sym_close) ]).
    exists R2. repeat split.
    1-6: (sym_regs HR2; rewrite ?alu_add;
          first [ reflexivity
                | (apply ntw_add_len; unfold cap in *; lia)
                | sym_close ]).
    exact Hms.
  - (* capacity left: the [bgeu] IS taken, back to the loop head *)
    sym_block_ex source_segs
      (mkst (regupd R1 10 (len_word bs)) (Z_to_bv 64 0x1125c) mem rrom)
      11%nat [false; false; false; true] [ELit 0x11074]
      [((1 : reg), ELit 0x111c4); ((2 : reg), EVar 32); ((8 : reg), EVar 33);
       ((9 : reg), EVar 34); ((18 : reg), EVar 34); ((19 : reg), ELit 4087);
       ((20 : reg), ELit 4088); ((10 : reg), EVar 35)]
      [Z_to_bv 64 (bv_unsigned rsp - 0x40); nat_to_word k; aG; len_word bs]
      (@nil word) R2 HR2 Hms.
    5: ret_sc Hra.
    4: (rewrite bv_ltu_Z; apply Z.ltb_ge; rewrite Hul;
        replace (bv_unsigned (Z_to_bv 64 (-4096))) with 18446744073709547520%Z
          by (vm_compute; reflexivity); unfold cap in *; lia).
    3: (rewrite bv_lts_small by (rewrite ?Hul, ?u_Z2bv; unfold cap in *; lia);
        apply Z.ltb_ge; rewrite Hul, u_Z2bv by lia; lia).
    2: (rewrite bv_eqb_Z; apply Z.eqb_neq; rewrite Hul, u_Z2bv by lia; lia).
    1: (rewrite negb_true_iff, bv_ltu_Z; apply Z.ltb_ge; unfold v_add;
        rewrite !u_Z2bv by (rewrite ?Huk, ?Hul; unfold cap in *; lia);
        rewrite Huk, Hul; unfold cap in *; lia).
    1-8: (getr_resolve; regupd_resolve; rewrite <- ?getr_nz by reg_neq_tac;
          first [ reflexivity
                | (rewrite H1; sym_close) | (rewrite H2; sym_close)
                | (rewrite H8; sym_close) | (rewrite H9; sym_close)
                | (rewrite H18; sym_close) | (rewrite H19; sym_close)
                | (rewrite H20; sym_close) ]).
    exists R2. repeat split.
    1-6: (sym_regs HR2; rewrite ?alu_add;
          first [ reflexivity
                | (apply ntw_add_len; unfold cap in *; lia)
                | sym_close ]).
    exact Hms.
Qed.

(* ----------------------------------------------------------------- *)
(* The header block: hexword and the two packing stores               *)
(* ----------------------------------------------------------------- *)

(** One iteration of hexword's four-trip digit loop 0x11168..0x11188:
    [srl a5,a0,a1], [andi a5,a5,15], the DATA-DEPENDENT [bltu a6,a5]
    ('0'+d against 'a'+d-10, taken on the HI side here), [sllw] into
    byte position [a4/8], [or] into the accumulator [a3], the two
    [addiw] index steps, and the backward [bne a4,a2] — taken on the
    first three trips, untaken on the fourth, which falls out to the
    [mv a0,a3]/[ret] at 0x1118c. *)
Lemma src_hex_iter : forall (R : bvmap 5 word) (mem : word -> option byte)
                            (n oq k : nat),
  (n <= cap)%nat -> (oq <= 4)%nat -> (k < 4)%nat ->
  getr R 10 = nat_to_word n ->
  getr R 11 = Z_to_bv 64 (4 * Z.of_nat (oq + 3 - k)) ->
  getr R 12 = Z_to_bv 64 32 ->
  getr R 13 = Z_to_bv 64 (hw4 n oq k) ->
  getr R 14 = Z_to_bv 64 (8 * Z.of_nat k) ->
  getr R 16 = Z_to_bv 64 9 ->
  exists R',
    getr R' 1 = getr R 1 /\
    getr R' 2 = getr R 2 /\
    getr R' 8 = getr R 8 /\
    getr R' 9 = getr R 9 /\
    getr R' 18 = getr R 18 /\
    getr R' 10 = nat_to_word n /\
    ((S k < 4)%nat -> getr R' 11 = Z_to_bv 64 (4 * Z.of_nat (oq + 3 - S k))) /\
    getr R' 12 = Z_to_bv 64 32 /\
    getr R' 13 = Z_to_bv 64 (hw4 n oq (S k)) /\
    getr R' 14 = Z_to_bv 64 (8 * Z.of_nat (S k)) /\
    getr R' 16 = Z_to_bv 64 9 /\
    msteps source_segs (mkst R (Z_to_bv 64 0x11168) mem rrom)
      (mkst R' (Z_to_bv 64 (if (S k <? 4)%nat then 0x11168%Z else 0x1118c%Z))
            mem rrom).
Proof.
  intros R mem n oq k Hn Hoq Hk H10 H11 H12 H13 H14 H16.
  destruct (Nat.ltb_spec (S k) 4) as [HSk|HSk].
  - destruct (Nat.ltb_spec (nib n (oq + 3 - k)) 10) as [Hd|Hd].
    + (* '0' + d, loop back *)
      sym_block_ex source_segs (mkst R (Z_to_bv 64 0x11168) mem rrom)
        9%nat [false; true] (@nil expr)
        [((10 : reg), EVar 32); ((11 : reg), EVar 33); ((12 : reg), ELit 32);
         ((13 : reg), EVar 34); ((14 : reg), EVar 35); ((16 : reg), ELit 9)]
        [nat_to_word n; Z_to_bv 64 (4 * Z.of_nat (oq + 3 - k));
         Z_to_bv 64 (hw4 n oq k); Z_to_bv 64 (8 * Z.of_nat k)]
        (@nil word) R' HR' Hms.
      { (* [bne a4,a2] taken: fewer than four digits so far *)
        rewrite negb_true_iff, bv_eqb_Z. apply Z.eqb_neq.
        unfold v_addiw. rewrite (u_Z2bv (8 * Z.of_nat k)) by lia.
        rewrite bv_swrap_small
          by (change (bv_half_modulus 32) with (2 ^ 31)%Z; lia).
        rewrite !u_Z2bv by lia. lia. }
      { (* the data-dependent [bltu a6,a5] *)
        rewrite v_and_15, (dig_val n (oq + 3 - k) _ Hn ltac:(lia) eq_refl).
        rewrite bv_ltu_Z. apply Z.ltb_ge.
        rewrite !u_Z2bv by (pose proof (nib_lt16 n (oq + 3 - k)); lia). lia. }
      1-6: (rewrite <- ?getr_nz by reg_neq_tac;
            first [ reflexivity | exact H10 | exact H11 | exact H12
                  | exact H13 | exact H14 | exact H16 ]).
      exists R'.
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; reflexivity. }
      split. { intros _. sym_regs HR'.
               unfold v_addiw.
               rewrite (u_Z2bv (4 * Z.of_nat (oq + 3 - k))) by lia.
               rewrite bv_swrap_small
                 by (change (bv_half_modulus 32) with (2 ^ 31)%Z; lia).
               f_equal. lia. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'. rewrite w_sllw.
               apply hex_step_lo; [exact Hn | exact Hoq | lia | exact Hd]. }
      split. { sym_regs HR';
               first [ reflexivity | (f_equal; lia)
                     | (unfold v_addiw;
                        rewrite (u_Z2bv (8 * Z.of_nat k)) by lia;
                        rewrite bv_swrap_small
                          by (change (bv_half_modulus 32) with (2 ^ 31)%Z; lia);
                        f_equal; lia) ]. }
      split. { sym_regs HR'; reflexivity. }
      exact Hms.
    + (* 'a' + d - 10, loop back *)
      sym_block_ex source_segs (mkst R (Z_to_bv 64 0x11168) mem rrom)
        10%nat [true; true] (@nil expr)
        [((10 : reg), EVar 32); ((11 : reg), EVar 33); ((12 : reg), ELit 32);
         ((13 : reg), EVar 34); ((14 : reg), EVar 35); ((16 : reg), ELit 9)]
        [nat_to_word n; Z_to_bv 64 (4 * Z.of_nat (oq + 3 - k));
         Z_to_bv 64 (hw4 n oq k); Z_to_bv 64 (8 * Z.of_nat k)]
        (@nil word) R' HR' Hms.
      { (* [bne a4,a2] taken: fewer than four digits so far *)
        rewrite negb_true_iff, bv_eqb_Z. apply Z.eqb_neq.
        unfold v_addiw. rewrite (u_Z2bv (8 * Z.of_nat k)) by lia.
        rewrite bv_swrap_small
          by (change (bv_half_modulus 32) with (2 ^ 31)%Z; lia).
        rewrite !u_Z2bv by lia. lia. }
      { (* the data-dependent [bltu a6,a5] *)
        rewrite v_and_15, (dig_val n (oq + 3 - k) _ Hn ltac:(lia) eq_refl).
        rewrite bv_ltu_Z. apply Z.ltb_lt.
        rewrite !u_Z2bv by (pose proof (nib_lt16 n (oq + 3 - k)); lia). lia. }
      1-6: (rewrite <- ?getr_nz by reg_neq_tac;
            first [ reflexivity | exact H10 | exact H11 | exact H12
                  | exact H13 | exact H14 | exact H16 ]).
      exists R'.
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; reflexivity. }
      split. { intros _. sym_regs HR'.
               unfold v_addiw.
               rewrite (u_Z2bv (4 * Z.of_nat (oq + 3 - k))) by lia.
               rewrite bv_swrap_small
                 by (change (bv_half_modulus 32) with (2 ^ 31)%Z; lia).
               f_equal. lia. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'. rewrite w_sllw.
               apply hex_step_hi; [exact Hn | exact Hoq | lia | exact Hd]. }
      split. { sym_regs HR';
               first [ reflexivity | (f_equal; lia)
                     | (unfold v_addiw;
                        rewrite (u_Z2bv (8 * Z.of_nat k)) by lia;
                        rewrite bv_swrap_small
                          by (change (bv_half_modulus 32) with (2 ^ 31)%Z; lia);
                        f_equal; lia) ]. }
      split. { sym_regs HR'; reflexivity. }
      exact Hms.
  - (* the fourth trip: the CLOSED untaken [bne] is auto-discharged and
       control falls out of the loop to 0x1118c *)
    assert (Hk3 : k = 3%nat) by lia. subst k.
    destruct (Nat.ltb_spec (nib n (oq + 3 - 3)) 10) as [Hd|Hd].
    + (* '0' + d *)
      sym_block_ex source_segs (mkst R (Z_to_bv 64 0x11168) mem rrom)
        9%nat [false; false] (@nil expr)
        [((10 : reg), EVar 32); ((11 : reg), EVar 33); ((12 : reg), ELit 32);
         ((13 : reg), EVar 34); ((14 : reg), EVar 35); ((16 : reg), ELit 9)]
        [nat_to_word n; Z_to_bv 64 (4 * Z.of_nat (oq + 3 - 3));
         Z_to_bv 64 (hw4 n oq 3); Z_to_bv 64 (8 * Z.of_nat 3)]
        (@nil word) R' HR' Hms.
      { (* the data-dependent [bltu a6,a5] *)
        rewrite v_and_15, (dig_val n (oq + 3 - 3) _ Hn ltac:(lia) eq_refl).
        rewrite bv_ltu_Z. apply Z.ltb_ge.
        rewrite !u_Z2bv by (pose proof (nib_lt16 n (oq + 3 - 3)); lia). lia. }
      1-6: (rewrite <- ?getr_nz by reg_neq_tac;
            first [ reflexivity | exact H10 | exact H11 | exact H12
                  | exact H13 | exact H14 | exact H16 ]).
      exists R'.
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; reflexivity. }
      split. { intro Hc. exfalso. lia. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'. rewrite w_sllw.
               apply hex_step_lo; [exact Hn | exact Hoq | lia | exact Hd]. }
      split. { sym_regs HR';
               first [ reflexivity | (f_equal; lia)
                     | (unfold v_addiw;
                        rewrite (u_Z2bv (8 * Z.of_nat 3)) by lia;
                        rewrite bv_swrap_small
                          by (change (bv_half_modulus 32) with (2 ^ 31)%Z; lia);
                        f_equal; lia) ]. }
      split. { sym_regs HR'; reflexivity. }
      exact Hms.
    + (* 'a' + d - 10 *)
      sym_block_ex source_segs (mkst R (Z_to_bv 64 0x11168) mem rrom)
        10%nat [true; false] (@nil expr)
        [((10 : reg), EVar 32); ((11 : reg), EVar 33); ((12 : reg), ELit 32);
         ((13 : reg), EVar 34); ((14 : reg), EVar 35); ((16 : reg), ELit 9)]
        [nat_to_word n; Z_to_bv 64 (4 * Z.of_nat (oq + 3 - 3));
         Z_to_bv 64 (hw4 n oq 3); Z_to_bv 64 (8 * Z.of_nat 3)]
        (@nil word) R' HR' Hms.
      { (* the data-dependent [bltu a6,a5] *)
        rewrite v_and_15, (dig_val n (oq + 3 - 3) _ Hn ltac:(lia) eq_refl).
        rewrite bv_ltu_Z. apply Z.ltb_lt.
        rewrite !u_Z2bv by (pose proof (nib_lt16 n (oq + 3 - 3)); lia). lia. }
      1-6: (rewrite <- ?getr_nz by reg_neq_tac;
            first [ reflexivity | exact H10 | exact H11 | exact H12
                  | exact H13 | exact H14 | exact H16 ]).
      exists R'.
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'; reflexivity. }
      split. { intro Hc. exfalso. lia. }
      split. { sym_regs HR'; reflexivity. }
      split. { sym_regs HR'. rewrite w_sllw.
               apply hex_step_hi; [exact Hn | exact Hoq | lia | exact Hd]. }
      split. { sym_regs HR';
               first [ reflexivity | (f_equal; lia)
                     | (unfold v_addiw;
                        rewrite (u_Z2bv (8 * Z.of_nat 3)) by lia;
                        rewrite bv_swrap_small
                          by (change (bv_half_modulus 32) with (2 ^ 31)%Z; lia);
                        f_equal; lia) ]. }
      split. { sym_regs HR'; reflexivity. }
      exact Hms.
Qed.

(** 0x11084 -> 0x11168: [li a1,16], [mv a0,s0], the [jal] into hexword
    and its five setup instructions, landing on the digit loop head
    with ra = 0x11090 (the first [sw]). *)
Lemma src_hdr_entry : forall (regs : bvmap 5 word) mem (n : nat) (aG : word),
  (n <= cap)%nat ->
  getr regs 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) ->
  getr regs 8 = nat_to_word n ->
  getr regs 9 = aG -> getr regs 18 = aG ->
  exists R,
    getr R 1 = (0x11090 : word) /\
    getr R 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) /\
    getr R 8 = nat_to_word n /\
    getr R 9 = aG /\
    getr R 18 = aG /\
    getr R 10 = nat_to_word n /\
    getr R 11 = Z_to_bv 64 (4 * Z.of_nat (4 + 3 - 0)) /\
    getr R 12 = Z_to_bv 64 32 /\
    getr R 13 = Z_to_bv 64 (hw4 n 4 0) /\
    getr R 14 = Z_to_bv 64 (8 * Z.of_nat 0) /\
    getr R 16 = Z_to_bv 64 9 /\
    msteps source_segs (mkst regs (Z_to_bv 64 0x11084) mem rrom)
                       (mkst R (Z_to_bv 64 0x11168) mem rrom).
Proof.
  intros regs mem n aG Hn H2 H8 H9 H18.
  sym_block_ex source_segs (mkst regs (Z_to_bv 64 0x11084) mem rrom)
    8%nat (@nil bool) (@nil expr)
    [((8 : reg), EVar 32)]
    [nat_to_word n] (@nil word) R HR Hms.
  1: (rewrite <- ?getr_nz by reg_neq_tac; exact H8).
  exists R.
  split. { sym_regs HR; first [reflexivity | bveq]. }
  split. { sym_regs HR; first [ exact H2 | reflexivity ]. }
  split. { sym_regs HR; first [ exact H8 | reflexivity ]. }
  split. { sym_regs HR; first [ exact H9 | reflexivity ]. }
  split. { sym_regs HR; first [ exact H18 | reflexivity ]. }
  split. { sym_regs HR; first [ reflexivity | (f_equal; lia) ]. }
  split. { sym_regs HR; first [ reflexivity | (f_equal; lia) ]. }
  split. { sym_regs HR; first [ reflexivity | (f_equal; lia) ]. }
  split. { sym_regs HR; first [ reflexivity | (f_equal; lia) ]. }
  split. { sym_regs HR; first [ reflexivity | (f_equal; lia) ]. }
  split. { sym_regs HR; first [ reflexivity | (f_equal; lia) ]. }
  exact Hms.
Qed.

(** hexword's first exit through the [ret] at 0x11190, the [sw] of the
    packed high word at [aG], and the second call's entry back to the
    loop head with ra = 0x110a0. *)
Lemma src_hdr_mid : forall (R : bvmap 5 word) mem (n : nat) (aG : word),
  (n <= cap)%nat ->
  (bv_unsigned aG + 8 <= 2 ^ 64)%Z ->
  store_ok source_segs mem aG 4%nat = true ->
  getr R 1 = (0x11090 : word) ->
  getr R 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) ->
  getr R 8 = nat_to_word n ->
  getr R 9 = aG -> getr R 18 = aG ->
  getr R 13 = Z_to_bv 64 (hw4 n 4 4) ->
  exists R',
    getr R' 1 = (0x110a0 : word) /\
    getr R' 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) /\
    getr R' 8 = nat_to_word n /\
    getr R' 9 = aG /\
    getr R' 18 = aG /\
    getr R' 10 = nat_to_word n /\
    getr R' 11 = Z_to_bv 64 (4 * Z.of_nat (0 + 3 - 0)) /\
    getr R' 12 = Z_to_bv 64 32 /\
    getr R' 13 = Z_to_bv 64 (hw4 n 0 0) /\
    getr R' 14 = Z_to_bv 64 (8 * Z.of_nat 0) /\
    getr R' 16 = Z_to_bv 64 9 /\
    msteps source_segs (mkst R (Z_to_bv 64 0x1118c) mem rrom)
      (mkst R' (Z_to_bv 64 0x11168)
            (wbytes mem aG (word_to_le_bytes 4 (Z_to_bv 64 (hw4 n 4 4))))
            rrom).
Proof.
  intros R mem n aG Hn HaB Hso H1 H2 H8 H9 H18 H13.
  pose proof (u64_range aG) as HaR.
  sym_block_ex source_segs (mkst R (Z_to_bv 64 0x1118c) mem rrom)
    11%nat (@nil bool) (@nil expr)
    [((1 : reg), ELit 0x11090); ((8 : reg), EVar 32); ((9 : reg), EVar 33);
     ((13 : reg), EVar 34)]
    [nat_to_word n; aG; Z_to_bv 64 (hw4 n 4 4)] (@nil word) R' HR' Hms.
  { (* the [sw] into the grant; its SCFlat auto-discharged *)
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hso. }
  1-4: (rewrite <- ?getr_nz by reg_neq_tac;
        first [ reflexivity | (rewrite H1; bveq) | exact H8 | exact H9
              | exact H13 ]).
  exists R'.
  split. { sym_regs HR'; first [reflexivity | bveq]. }
  split. { sym_regs HR'; first [ exact H2 | reflexivity ]. }
  split. { sym_regs HR'; first [ exact H8 | reflexivity ]. }
  split. { sym_regs HR'; first [ exact H9 | reflexivity ]. }
  split. { sym_regs HR'; first [ exact H18 | reflexivity ]. }
  split. { sym_regs HR'; first [ reflexivity | (f_equal; lia) ]. }
  split. { sym_regs HR'; first [ reflexivity | (f_equal; lia) ]. }
  split. { sym_regs HR'; first [ reflexivity | (f_equal; lia) ]. }
  split. { sym_regs HR'; first [ reflexivity | (f_equal; lia) ]. }
  split. { sym_regs HR'; first [ reflexivity | (f_equal; lia) ]. }
  split. { sym_regs HR'; first [ reflexivity | (f_equal; lia) ]. }
  match type of Hms with
  | msteps _ _ (mkst _ _ ?M _) =>
      replace (wbytes mem aG (word_to_le_bytes 4 (Z_to_bv 64 (hw4 n 4 4))))
        with M; [ exact Hms | ]
  end.
  rewrite adenot_var.
  cbn [edenot Eplus Nat.ltb Nat.leb Nat.sub nth app].
  rewrite ?edenot_lit.
  rewrite ?alu64_add_0.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  reflexivity.
Qed.

(** hexword's second exit, the [sw] of the packed low word at [aG+4],
    [s0 += 8], and the put2 setup through musl's [write] wrapper — its
    frame push, [ra] spill into the scratch slot, seven-register
    shuffle — to the [ecall] at 0x11258 with a7 = 64. *)
Lemma src_put2_ecall : forall (R : bvmap 5 word) mem (n : nat) (aG : word),
  (n <= cap)%nat ->
  (bv_unsigned aG + 8 <= 2 ^ 64)%Z ->
  store_ok source_segs mem (Z_to_bv 64 (bv_unsigned aG + 4)) 4%nat = true ->
  store_ok source_segs mem
    (Z_to_bv 64 (bv_unsigned rsp - 0x38)) 8%nat = true ->
  getr R 1 = (0x110a0 : word) ->
  getr R 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30) ->
  getr R 8 = nat_to_word n ->
  getr R 9 = aG -> getr R 18 = aG ->
  getr R 13 = Z_to_bv 64 (hw4 n 0 4) ->
  exists R',
    getr R' 1 = (0x111f8 : word) /\
    getr R' 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40) /\
    getr R' 8 = nat_to_word (8 + n) /\
    getr R' 9 = aG /\
    getr R' 18 = aG /\
    getr R' 10 = Z_to_bv 64 2 /\
    getr R' 11 = aG /\
    getr R' 12 = nat_to_word (8 + n) /\
    getr R' 17 = Z_to_bv 64 64 /\
    msteps source_segs (mkst R (Z_to_bv 64 0x1118c) mem rrom)
      (mkst R' (Z_to_bv 64 0x11258)
            (wbytes (wbytes mem (Z_to_bv 64 (bv_unsigned aG + 4))
                            (word_to_le_bytes 4 (Z_to_bv 64 (hw4 n 0 4))))
                    scr (word_to_le_bytes 8 (0x110b8 : word)))
            rrom).
Proof.
  intros R mem n aG Hn HaB Hso Hsc H1 H2 H8 H9 H18 H13.
  pose proof (u64_range aG) as HaR.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  sym_block_ex source_segs (mkst R (Z_to_bv 64 0x1118c) mem rrom)
    26%nat (@nil bool) (@nil expr)
    [((1 : reg), ELit 0x110a0); ((2 : reg), EVar 32); ((8 : reg), EVar 33);
     ((9 : reg), EVar 34); ((18 : reg), EVar 34); ((13 : reg), EVar 35)]
    [Z_to_bv 64 (bv_unsigned rsp - 0x30); nat_to_word n; aG;
     Z_to_bv 64 (hw4 n 0 4)] (@nil word) R' HR' Hms.
  { (* the wrapper's [ra] spill into the scratch slot *) exact Hsc. }
  { (* the second [sw] into the grant *) exact Hso. }
  1-6: (rewrite <- ?getr_nz by reg_neq_tac;
        first [ reflexivity | (rewrite H1; bveq) | exact H2 | exact H8
              | exact H9 | exact H18 | exact H13 ]).
  exists R'.
  split. { sym_regs HR'; first [reflexivity | bveq]. }
  split. { sym_regs HR'; first [ reflexivity | (apply bv_eq; u_norm; lia) ]. }
  split. { sym_regs HR'. apply bv_eq.
           rewrite !u_ntw by (unfold cap in *; lia).
           rewrite !u_Z2bv by (unfold cap in *; lia). lia. }
  split. { sym_regs HR'; first [ exact H9 | reflexivity ]. }
  split. { sym_regs HR'; first [ exact H18 | reflexivity ]. }
  split. { sym_regs HR'; first [ reflexivity | bveq ]. }
  split. { sym_regs HR'; first [ reflexivity | (apply bv_eq; u_norm; lia) ]. }
  split. { sym_regs HR'. apply bv_eq.
           rewrite !u_ntw by (unfold cap in *; lia).
           rewrite !u_Z2bv by (unfold cap in *; lia). lia. }
  split. { sym_regs HR'; first [ reflexivity | bveq ]. }
  match type of Hms with
  | msteps _ _ (mkst _ _ ?M _) =>
      replace (wbytes (wbytes mem (Z_to_bv 64 (bv_unsigned aG + 4))
                              (word_to_le_bytes 4 (Z_to_bv 64 (hw4 n 0 4))))
                      scr (word_to_le_bytes 8 (0x110b8 : word)))
        with M; [ exact Hms | ]
  end.
  rewrite !adenot_var.
  cbn [edenot Eplus Nat.ltb Nat.leb Nat.sub nth app].
  rewrite ?edenot_lit.
  rewrite ?alu64_add_0.
  unfold scr. f_equal.
  rewrite u_Z2bv by lia. f_equal. lia.
Qed.

(** The write wrapper's return path (the errno [bltu] is dead), the
    put2 loop exit ([s0 -= a0] reaches 0 on the LAST delivery), the
    epilogue's six frame reloads and its [ret] into _start's exit tail,
    up to the [li a7,93] before the exit [ecall].

    [rest] is whatever the write was still offering; this is the arm the
    retry loop takes when the environment delivers all of it. *)
Lemma src_put2_ret : forall (R : bvmap 5 word) mem (rest : list byte) (p : word),
  (1 <= length rest)%nat -> (length rest <= 8 + cap)%nat ->
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x38)) 8%nat
    = Some (word_to_le_bytes 8 (0x110b8 : word)) ->
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x8)) 8%nat
    = Some (word_to_le_bytes 8 (0x11128 : word)) ->
  (forall a,
     In a [Z_to_bv 64 (bv_unsigned rsp - 0x30);
           Z_to_bv 64 (bv_unsigned rsp - 0x28);
           Z_to_bv 64 (bv_unsigned rsp - 0x20);
           Z_to_bv 64 (bv_unsigned rsp - 0x18);
           Z_to_bv 64 (bv_unsigned rsp - 0x10)] ->
     rdn source_segs mem a 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) ->
  getr R 1 = (0x111f8 : word) ->
  getr R 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40) ->
  getr R 8 = len_word rest ->
  getr R 18 = p ->
  exists R2,
    getr R2 17 = Z_to_bv 64 93 /\
    getr R2 10 = Z_to_bv 64 0 /\
    msteps source_segs
      (mkst (regupd R 10 (len_word rest)) (Z_to_bv 64 0x1125c) mem rrom)
      (mkst R2 (Z_to_bv 64 0x1112c) mem rrom).
Proof.
  intros R mem rest p Hne Hn Hscr Hra Hframe H1 H2 H8 H18.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  assert (Huc : bv_unsigned (len_word rest) = Z.of_nat (length rest))
    by (apply u_len_word; unfold cap in *; lia).
  sym_block_ex source_segs
    (mkst (regupd R 10 (len_word rest)) (Z_to_bv 64 0x1125c) mem rrom)
    21%nat [false; false; false]
    [ELit 0x110b8; ELit 0x11128; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0]
    [((1 : reg), ELit 0x111f8); ((2 : reg), EVar 32); ((8 : reg), EVar 33);
     ((10 : reg), EVar 33); ((18 : reg), EVar 34)]
    [Z_to_bv 64 (bv_unsigned rsp - 0x40); len_word rest; p]
    (@nil word) R2 HR2 Hms.
  (* the six epilogue reloads, in the executor's reverse order *)
  1-6: (eexists; split;
        [ solve [ apply Hframe;
                  repeat first [ left; reflexivity | right ]
                | exact Hra ]
        | rewrite bytes_le_to_Z_8; vm_compute; reflexivity ]).
  { (* [bne s0,zero] untaken: the write consumed everything *)
    rewrite negb_false_iff. apply c_eq_sub_self. }
  { (* [blez a0] untaken: the delivered count is positive *)
    rewrite negb_false_iff.
    rewrite bv_lts_small
      by (rewrite ?Huc, ?u_Z2bv by lia; unfold cap in *; lia).
    apply Z.ltb_lt. rewrite Huc, u_Z2bv by lia. lia. }
  { (* [__syscall_ret]'s errno [bltu] untaken *)
    rewrite bv_ltu_Z. apply Z.ltb_ge.
    replace (bv_unsigned (Z_to_bv 64 (-4096)))
      with 18446744073709547520%Z by (vm_compute; reflexivity).
    rewrite Huc. unfold cap in *. lia. }
  { (* the wrapper's [ra] reload out of the scratch slot *)
    eexists; split;
      [ exact Hscr | rewrite bytes_le_to_Z_8; vm_compute; reflexivity ]. }
  1-5: (getr_resolve; regupd_resolve; rewrite <- ?getr_nz by reg_neq_tac;
        first [ reflexivity | (rewrite H1; bveq) | exact H2 | exact H8
              | exact H18 ]).
  exists R2.
  split. { sym_regs HR2; first [reflexivity | bveq]. }
  split. { sym_regs HR2; first [reflexivity | bveq]. }
  exact Hms.
Qed.

(** The put2 emit loop, as a write-all node ([WallSim.to_wall_tail]).

    Entry is 0x1125c, the [ret] of the raw-syscall trampoline the write
    [ecall] returns to, with [a0] the DELIVERED length.  The path back
    to the loop test runs through musl's wrapper — its [ra] reload out
    of the scratch slot, its frame pop and [__syscall_ret]'s errno
    [bltu], all dead — then [s0 -= a0], [s2 += a0] and the [bnez s0]
    that either falls through into the epilogue ([src_put2_ret]) or
    re-enters the wrapper on [skipn n rest].  Induction on
    [fuel >= length rest]; the remainder shrinks strictly.

    The reissue re-spills [ra] into the SAME scratch slot, so the loop
    invariant is stated over an arbitrary [mem] carrying the frame's
    [rdn] facts rather than over one fixed memory. *)
Lemma src_put_wall : forall fuel (rest : list byte) (p : word) n
                            (R : bvmap 5 word) mem,
  (length rest <= fuel)%nat ->
  (1 <= n)%nat -> (n <= length rest)%nat ->
  (length rest <= 8 + cap)%nat ->
  (0 < bv_unsigned p)%Z ->
  (bv_unsigned p + Z.of_nat (length rest) <= bv_unsigned rsp - 0x800000)%Z ->
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x38)) 8%nat
    = Some (word_to_le_bytes 8 (0x110b8 : word)) ->
  rdn source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x8)) 8%nat
    = Some (word_to_le_bytes 8 (0x11128 : word)) ->
  (forall a,
     In a [Z_to_bv 64 (bv_unsigned rsp - 0x30);
           Z_to_bv 64 (bv_unsigned rsp - 0x28);
           Z_to_bv 64 (bv_unsigned rsp - 0x20);
           Z_to_bv 64 (bv_unsigned rsp - 0x18);
           Z_to_bv 64 (bv_unsigned rsp - 0x10)] ->
     rdn source_segs mem a 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) ->
  store_ok source_segs mem (Z_to_bv 64 (bv_unsigned rsp - 0x38)) 8%nat = true ->
  rdn source_segs mem p (length rest) = Some rest ->
  getr R 1 = (0x111f8 : word) ->
  getr R 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40) ->
  getr R 8 = len_word rest ->
  getr R 18 = p ->
  to_wall_tail source_segs (Z_to_bv 64 2)
    (mkst (regupd R 10 (len_word (firstn n rest))) (Z_to_bv 64 0x1125c) mem rrom)
    (skipn n rest)
    (fun ms => to_wexit source_segs ms [] (Z_to_bv 64 0)).
Proof.
  induction fuel as [|fuel IH];
    intros rest p n R mem Hfuel Hn1 Hn2 Hlen Hplo Hstk
           Hscr Hra Hframe Hsc Hread H1 H2 H8 H18.
  { lia. }
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  assert (Huc : bv_unsigned (len_word rest) = Z.of_nat (length rest))
    by (apply u_len_word; unfold cap in *; lia).
  assert (Hud : bv_unsigned (len_word (firstn n rest)) = Z.of_nat n)
    by (apply u_len_word_firstn; [lia | unfold cap in *; lia]).
  destruct (Nat.eq_dec n (length rest)) as [Hfull | Hne].
  - (* everything delivered: the [bnez s0] falls through to the exit *)
    subst n. rewrite skipn_all. rewrite firstn_all.
    apply twt_done. cbv beta.
    destruct (src_put2_ret R mem rest p ltac:(lia) Hlen Hscr Hra Hframe
                H1 H2 H8 H18)
      as (R2 & M17 & M10 & HmsM).
    eapply msteps_to_wexit; [exact HmsM|].
    replace (Z_to_bv 64 0x1112c) with (0x1112c : word) by bveq.
    eapply tw_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ SF_1112c eq_refl) | ].
    match goal with
    | |- to_wexit _ ?ms _ _ =>
        replace (Z_to_bv 64 0) with (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
          by (unfold ms_gpr; cbn [ms_regs]; rewrite arg_reg_0;
              rewrite <- getr_nz by reg_neq_tac; rewrite M10; bveq)
    end.
    eapply tw_exit.
    + cbn [ms_svc_pending]. reflexivity.
    + left. rewrite M17. vm_compute. reflexivity.
  - (* a short delivery: the [bnez s0] re-enters the write wrapper *)
    assert (Hlt : (n < length rest)%nat) by lia.
    sym_block source_segs 33%nat [false; false; true] [ELit 0x110b8]
      [((1 : reg), ELit 0x111f8); ((2 : reg), EVar 32); ((8 : reg), EVar 33);
       ((10 : reg), EVar 34); ((18 : reg), EVar 35)]
      [Z_to_bv 64 (bv_unsigned rsp - 0x40); len_word rest;
       len_word (firstn n rest); p]
      (@nil word) R' HR'.
    1-5: solve
      [ (* the wrapper's [ra] reload out of the scratch slot *)
        (eexists; split;
         [ exact Hscr | rewrite bytes_le_to_Z_8; vm_compute; reflexivity ])
      | (* the wrapper's [ra] spill into the scratch slot *) exact Hsc
      | (* [bnez s0] TAKEN: the remainder is nonempty *)
        (rewrite negb_true_iff;
         rewrite v_sub_len_firstn by (unfold cap in *; lia);
         apply c_eq_0_false;
         rewrite u_len_word by (rewrite length_skipn; unfold cap in *; lia);
         rewrite length_skipn; lia)
      | (* [blez a0] untaken: the delivery is nonempty *)
        (rewrite negb_false_iff;
         rewrite bv_lts_small
           by (rewrite ?Hud, ?u_Z2bv by lia; unfold cap in *; lia);
         apply Z.ltb_lt; rewrite Hud, u_Z2bv by lia; lia)
      | (* [__syscall_ret]'s errno [bltu] untaken *)
        (rewrite bv_ltu_Z; apply Z.ltb_ge;
         replace (bv_unsigned (Z_to_bv 64 (-4096)))
           with 18446744073709547520%Z by (vm_compute; reflexivity);
         rewrite Hud; unfold cap in *; lia) ].
    1-5: (getr_resolve; regupd_resolve; rewrite <- ?getr_nz by reg_neq_tac;
          first [ reflexivity | (rewrite H1; bveq) | exact H2 | exact H8
                | exact H18 ]).
    assert (N1 : getr R' 1 = (0x111f8 : word))
      by (sym_regs HR'; first [reflexivity | bveq]).
    assert (N2 : getr R' 2 = Z_to_bv 64 (bv_unsigned rsp - 0x40))
      by (sym_regs HR'; first [reflexivity | bveq]).
    assert (N8 : getr R' 8 = len_word (skipn n rest))
      by (sym_regs HR'; apply v_sub_len_firstn; [lia | unfold cap in *; lia]).
    assert (N10 : getr R' 10 = Z_to_bv 64 2)
      by (sym_regs HR'; first [reflexivity | bveq]).
    assert (N11 : getr R' 11 = p + nat_to_word n)
      by (sym_regs HR'; apply v_add_len_firstn; lia).
    assert (N12 : getr R' 12 = len_word (skipn n rest))
      by (sym_regs HR'; apply v_sub_len_firstn; [lia | unfold cap in *; lia]).
    assert (N17 : getr R' 17 = Z_to_bv 64 64)
      by (sym_regs HR'; first [reflexivity | bveq]).
    assert (N18 : getr R' 18 = p + nat_to_word n)
      by (sym_regs HR'; apply v_add_len_firstn; lia).
    clear HR' Hlf.
    (* the reissue re-spills [ra] into the scratch slot; every frame
       fact survives, the grant being far below the stack *)
    assert (Hu56 : bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 0x38))
                   = (bv_unsigned rsp - 0x38)%Z) by (apply u_Z2bv; lia).
    assert (HuP : bv_unsigned (p + nat_to_word n)
                  = (bv_unsigned p + Z.of_nat n)%Z)
      by (rewrite word_add_nat_Z by (unfold cap in *; lia);
          apply u_Z2bv; lia).
    assert (Hout : forall (a : word) (k : nat),
              (bv_unsigned a + Z.of_nat k <= bv_unsigned rsp - 0x38
               \/ bv_unsigned rsp - 0x30 <= bv_unsigned a)%Z ->
              (bv_unsigned a + Z.of_nat k <= 2 ^ 64)%Z ->
              rdn source_segs
                (wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 0x38))
                        (word_to_le_bytes 8 (0x110b8 : word))) a k
              = rdn source_segs mem a k).
    { intros a k Ha Hk. apply rdn_wbytes_out;
        rewrite ?length_N_to_le_bytes, ?Hu56; lia. }
    assert (Hscr' : rdn source_segs
                      (wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 0x38))
                              (word_to_le_bytes 8 (0x110b8 : word)))
                      (Z_to_bv 64 (bv_unsigned rsp - 0x38)) 8%nat
                    = Some (word_to_le_bytes 8 (0x110b8 : word)))
      by (apply rdn_wbytes_hit8; rewrite Hu56; lia).
    assert (Hra' : rdn source_segs
                     (wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 0x38))
                             (word_to_le_bytes 8 (0x110b8 : word)))
                     (Z_to_bv 64 (bv_unsigned rsp - 0x8)) 8%nat
                   = Some (word_to_le_bytes 8 (0x11128 : word))).
    { rewrite Hout by (rewrite u_Z2bv by lia; lia). exact Hra. }
    assert (Hframe' : forall a,
      In a [Z_to_bv 64 (bv_unsigned rsp - 0x30);
            Z_to_bv 64 (bv_unsigned rsp - 0x28);
            Z_to_bv 64 (bv_unsigned rsp - 0x20);
            Z_to_bv 64 (bv_unsigned rsp - 0x18);
            Z_to_bv 64 (bv_unsigned rsp - 0x10)] ->
      rdn source_segs
        (wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 0x38))
                (word_to_le_bytes 8 (0x110b8 : word))) a 8%nat
      = Some (word_to_le_bytes 8 (Z_to_bv 64 0))).
    { intros a Ha.
      repeat destruct Ha as [<- | Ha]; try (exfalso; exact Ha);
        (rewrite Hout by (rewrite u_Z2bv by lia; lia);
         apply Hframe; repeat first [ left; reflexivity | right ]). }
    assert (Hsc' : store_ok source_segs
                     (wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 0x38))
                             (word_to_le_bytes 8 (0x110b8 : word)))
                     (Z_to_bv 64 (bv_unsigned rsp - 0x38)) 8%nat = true)
      by (eapply store_ok_mono; [apply wbytes_grows | exact Hsc]).
    assert (Hsk : rdn source_segs
                    (wbytes mem (Z_to_bv 64 (bv_unsigned rsp - 0x38))
                            (word_to_le_bytes 8 (0x110b8 : word)))
                    (p + nat_to_word n) (length rest - n)%nat
                  = Some (skipn n rest)).
    { rewrite Hout by (rewrite HuP; unfold cap in *; lia).
      exact (SeqExec.rdn_skipn source_segs mem (length rest) p rest n
               Hread Hn2). }
    eapply twt_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ SF_11258 eq_refl) | ].
    apply twt_more; [rewrite length_skipn; lia|].
    apply (twl_write_rec source_segs (Z_to_bv 64 2)).
    + rewrite N17. vm_compute. reflexivity.
    + rewrite <- getr_nz by reg_neq_tac; exact N10.
    + rewrite <- ?getr_nz by reg_neq_tac; rewrite N11, N12.
      rewrite (ms_read_bytes_rdn (run_segments source_segs inp rsp rmb)) by reflexivity;
        unfold run_segments; apply rdn_lift.
      cbn [ms_mem].
      replace (word_to_nat (len_word (skipn n rest)))
        with (length rest - n)%nat
        by (unfold word_to_nat;
            rewrite u_len_word by (rewrite length_skipn; unfold cap in *; lia);
            rewrite length_skipn, Nat2Z.id; reflexivity).
      exact Hsk.
    + (* [vfs_write]'s [access_ok] on the remaining range *)
      rewrite <- ?getr_nz by reg_neq_tac; rewrite N11, N12.
      apply Uaccess.access_okb_intro.
      rewrite u_len_word by (rewrite length_skipn; unfold cap in *; lia).
      rewrite HuP, length_skipn. unfold TASK_SIZE. lia.
    + rewrite length_skipn; lia.
    + intros m Hm1 Hm2.
      replace (v_addi (0x11258 : word) 4) with (Z_to_bv 64 0x1125c) by bveq.
      apply (IH (skipn n rest) (p + nat_to_word n) m).
      * rewrite length_skipn; lia.
      * exact Hm1.
      * exact Hm2.
      * rewrite length_skipn; lia.
      * rewrite HuP; lia.
      * rewrite HuP, length_skipn; lia.
      * exact Hscr'.
      * exact Hra'.
      * exact Hframe'.
      * exact Hsc'.
      * rewrite length_skipn; exact Hsk.
      * getr_resolve; exact N1.
      * getr_resolve; exact N2.
      * getr_resolve; exact N8.
      * getr_resolve; exact N18.
Qed.

(** The whole tail, through the fd-2 WRITE-ALL machinery:
    [wall_realizes_ch] to enter (the emit is a put-style retry loop, so
    its trace contribution is the whole buffer however the environment
    chunks the delivery), [WallSim.msteps_to_wall_tail] for the silent
    runs, [WallSim.twl_write_rec] for the write(2, base, 8+|acc|) — the
    buffer read-back is [SeqExec.rdn_wbytes_hit] for the two just-stored
    header words spliced with [CatExec.rdn_wbytes_out] (TWO-SIDED: all
    that is known of the grant base is that it avoids the image) for the
    drained prefix by [SeqExec.rdn_app] — and [src_put_wall] for every
    delivered length.  The [blez a0] at 0x110b8 is dead: a delivery on a
    channel is always nonempty ([ReadWrite.write_spec] only returns
    [-EFAULT] when NOTHING at the buffer is readable, which the mapped
    grant rules out). *)
Lemma src_tail : forall fs0 acc c,
  src_inv fs0 acc (0x11084 : word) c ->
  realizes (run_segments source_segs inp rsp rmb) c (arena_tail fs0 acc).
Proof.
  intros fs0 acc c HI.
  destruct HI as (aG & regs & mem & Hb & Hh & Hlazy & Hfs & Hfd0 & Hfd2 & Hms0 &
                  H9 & H18 & H20 & H19 & H8 & H2 & Hle & Hmok & Hrdn).
  destruct c as [ms0 model]. cbn [cfg_ms cfg_model] in *.
  pose proof Hb as Hb2. destruct Hb2 as (Hpos & Hal & Hceil & _).
  pose proof rsp_hi_num. unfold stack_max_size in Hceil.
  pose proof (u64_range aG) as HaR.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  pose proof (grant_below_stack aG Hb) as Hbs.
  assert (HaB : (bv_unsigned aG + 8 <= 2 ^ 64)%Z) by lia.
  unfold arena_tail. rewrite <- Hfs.
  apply (wall_realizes_ch (run_segments source_segs inp rsp rmb) (Z_to_bv 64 2) ch2 ms0 model
           [arena_out acc] (Z_to_bv 64 0) Hh Hlazy Hfd2 fd32_2);
    [| exact (arena_out_modeled acc Hle)].
  split; [rewrite arena_out_length; lia|].
  (* the write chain is built over the image's segments and lifted whole
     ([RunSegmentsLift.to_wall_lift_mut]; neither vDSO segment executes) *)
  unfold run_segments.
  apply (proj2 (to_wall_lift_mut source_segs _ (Z_to_bv 64 2) (vdso_segments_no_exec _ _ _))
           ms0 (arena_out acc) (fun ms => to_wexit source_segs ms [] (Z_to_bv 64 0)));
    [| intros m Hm; exact (to_wexit_app source_segs _ m [] _ (vdso_segments_no_exec _ _ _) Hm)].
  replace (0x11084 : word) with (Z_to_bv 64 0x11084) in Hms0 by bveq.
  eapply msteps_to_wall_tail; [exact Hms0|].
  (* 0x11084 -> the first hexword's loop head *)
  destruct (src_hdr_entry regs mem (length acc) aG Hle H2 H8 H9 H18)
    as (Ra & A1 & A2 & A8 & A9 & A18 & A10 & A11 & A12 & A13 & A14 & A16
        & HmsA).
  eapply msteps_to_wall_tail; [exact HmsA|].
  (* the first call's four digit trips *)
  destruct (src_hex_iter Ra mem (length acc) 4 0 Hle ltac:(lia) ltac:(lia)
              A10 A11 A12 A13 A14 A16)
    as (Rb & Pb1 & Pb2 & Pb8 & Pb9 & Pb18 & Qb10 & Qb11 & Qb12 & Qb13 & Qb14
        & Qb16 & HmsB).
  eapply msteps_to_wall_tail; [exact HmsB|].
  destruct (src_hex_iter Rb mem (length acc) 4 1 Hle ltac:(lia) ltac:(lia)
              Qb10 (Qb11 ltac:(lia)) Qb12 Qb13 Qb14 Qb16)
    as (Rc & Pc1 & Pc2 & Pc8 & Pc9 & Pc18 & Qc10 & Qc11 & Qc12 & Qc13 & Qc14
        & Qc16 & HmsC).
  eapply msteps_to_wall_tail; [exact HmsC|].
  destruct (src_hex_iter Rc mem (length acc) 4 2 Hle ltac:(lia) ltac:(lia)
              Qc10 (Qc11 ltac:(lia)) Qc12 Qc13 Qc14 Qc16)
    as (Rd & Pd1 & Pd2 & Pd8 & Pd9 & Pd18 & Qd10 & Qd11 & Qd12 & Qd13 & Qd14
        & Qd16 & HmsD).
  eapply msteps_to_wall_tail; [exact HmsD|].
  destruct (src_hex_iter Rd mem (length acc) 4 3 Hle ltac:(lia) ltac:(lia)
              Qd10 (Qd11 ltac:(lia)) Qd12 Qd13 Qd14 Qd16)
    as (Re & Pe1 & Pe2 & Pe8 & Pe9 & Pe18 & Qe10 & Qe11 & Qe12 & Qe13 & Qe14
        & Qe16 & HmsE).
  eapply msteps_to_wall_tail; [exact HmsE|].
  assert (F1 : getr Re 1 = (0x11090 : word))
    by (rewrite Pe1, Pd1, Pc1, Pb1; exact A1).
  assert (F2 : getr Re 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30))
    by (rewrite Pe2, Pd2, Pc2, Pb2; exact A2).
  assert (F8 : getr Re 8 = nat_to_word (length acc))
    by (rewrite Pe8, Pd8, Pc8, Pb8; exact A8).
  assert (F9 : getr Re 9 = aG)
    by (rewrite Pe9, Pd9, Pc9, Pb9; exact A9).
  assert (F18 : getr Re 18 = aG)
    by (rewrite Pe18, Pd18, Pc18, Pb18; exact A18).
  (* the first packing [sw] and the second hexword's entry *)
  assert (Hso1 : store_ok source_segs mem aG 4%nat = true)
    by (eapply grant_store_ok; [ exact Hmok | exact Hb | lia | lia ]).
  destruct (src_hdr_mid Re mem (length acc) aG Hle HaB Hso1 F1 F2 F8 F9 F18
              Qe13)
    as (Rf & G1 & G2 & G8 & G9 & G18 & G10 & G11 & G12 & G13 & G14 & G16
        & HmsF).
  eapply msteps_to_wall_tail; [exact HmsF|].
  set (h1 := word_to_le_bytes 4 (Z_to_bv 64 (hw4 (length acc) 4 4))) in *.
  set (mem1 := wbytes mem aG h1) in *.
  assert (Hmok1 : mem_ok aG mem1).
  { unfold mem1. apply mem_ok_grant;
      [ exact Hmok | exact Hb | lia
      | unfold h1; rewrite length_N_to_le_bytes; lia ]. }
  (* the second call's four digit trips *)
  destruct (src_hex_iter Rf mem1 (length acc) 0 0 Hle ltac:(lia) ltac:(lia)
              G10 G11 G12 G13 G14 G16)
    as (Rg & Pg1 & Pg2 & Pg8 & Pg9 & Pg18 & Qg10 & Qg11 & Qg12 & Qg13 & Qg14
        & Qg16 & HmsG).
  eapply msteps_to_wall_tail; [exact HmsG|].
  destruct (src_hex_iter Rg mem1 (length acc) 0 1 Hle ltac:(lia) ltac:(lia)
              Qg10 (Qg11 ltac:(lia)) Qg12 Qg13 Qg14 Qg16)
    as (Rh & Ph1 & Ph2 & Ph8 & Ph9 & Ph18 & Qh10 & Qh11 & Qh12 & Qh13 & Qh14
        & Qh16 & HmsH).
  eapply msteps_to_wall_tail; [exact HmsH|].
  destruct (src_hex_iter Rh mem1 (length acc) 0 2 Hle ltac:(lia) ltac:(lia)
              Qh10 (Qh11 ltac:(lia)) Qh12 Qh13 Qh14 Qh16)
    as (Ri & Pi1 & Pi2 & Pi8 & Pi9 & Pi18 & Qi10 & Qi11 & Qi12 & Qi13 & Qi14
        & Qi16 & HmsI).
  eapply msteps_to_wall_tail; [exact HmsI|].
  destruct (src_hex_iter Ri mem1 (length acc) 0 3 Hle ltac:(lia) ltac:(lia)
              Qi10 (Qi11 ltac:(lia)) Qi12 Qi13 Qi14 Qi16)
    as (Rj & Pj1 & Pj2 & Pj8 & Pj9 & Pj18 & Qj10 & Qj11 & Qj12 & Qj13 & Qj14
        & Qj16 & HmsJ).
  eapply msteps_to_wall_tail; [exact HmsJ|].
  assert (J1 : getr Rj 1 = (0x110a0 : word))
    by (rewrite Pj1, Pi1, Ph1, Pg1; exact G1).
  assert (J2 : getr Rj 2 = Z_to_bv 64 (bv_unsigned rsp - 0x30))
    by (rewrite Pj2, Pi2, Ph2, Pg2; exact G2).
  assert (J8 : getr Rj 8 = nat_to_word (length acc))
    by (rewrite Pj8, Pi8, Ph8, Pg8; exact G8).
  assert (J9 : getr Rj 9 = aG)
    by (rewrite Pj9, Pi9, Ph9, Pg9; exact G9).
  assert (J18 : getr Rj 18 = aG)
    by (rewrite Pj18, Pi18, Ph18, Pg18; exact G18).
  (* the second packing [sw], and the write wrapper up to its ecall *)
  assert (Hso2 : store_ok source_segs mem1
                   (Z_to_bv 64 (bv_unsigned aG + 4)) 4%nat = true).
  { eapply grant_store_ok;
      [ exact Hmok1 | exact Hb | rewrite u_Z2bv by lia; lia
      | rewrite u_Z2bv by lia; lia ]. }
  assert (Hsc3 : store_ok source_segs mem1
                   (Z_to_bv 64 (bv_unsigned rsp - 0x38)) 8%nat = true).
  { eapply store_ok_mono; [ apply (mem_ok_grows_w aG mem1 Hmok1) | ].
    unfold rwmem.
    apply (store_ok_wrap_window_valid source_segs inp rmb source_phdrs _ rsp rbrk _ _ rrnd
             Hvl Hlau);
      unfold stack_window_reach, stack_max_size; u_norm; lia. }
  destruct (src_put2_ecall Rj mem1 (length acc) aG Hle HaB Hso2 Hsc3
              J1 J2 J8 J9 J18 Qj13)
    as (Rk & K1 & K2 & K8 & K9 & K18 & K10 & K11 & K12 & K17 & HmsK).
  eapply msteps_to_wall_tail; [exact HmsK|].
  set (h2 := word_to_le_bytes 4 (Z_to_bv 64 (hw4 (length acc) 0 4))) in *.
  set (mem3 := wbytes (wbytes mem1 (Z_to_bv 64 (bv_unsigned aG + 4)) h2)
                      scr (word_to_le_bytes 8 (0x110b8 : word))) in *.
  assert (Hmok3 : mem_ok aG mem3).
  { unfold mem3. apply mem_ok_scratch8;
      [ apply mem_ok_grant;
          [ exact Hmok1 | exact Hb | rewrite u_Z2bv by lia; lia
          | unfold h2; rewrite length_N_to_le_bytes, u_Z2bv by lia; lia ]
      | exact Hb
      | unfold scr; rewrite u_Z2bv by lia; lia
      | unfold scr; rewrite u_Z2bv by lia; lia ].
  }
  (* the frame slots the put2 retry loop carries across a reissue *)
  pose proof Hmok3 as Hmok3'.
  destruct Hmok3' as [Hg3 Hread3].
  assert (Hscr3 : rdn source_segs mem3
                    (Z_to_bv 64 (bv_unsigned rsp - 0x38)) 8%nat
                  = Some (word_to_le_bytes 8 (0x110b8 : word))).
  { unfold mem3, scr. apply rdn_wbytes_hit8. u_norm. lia. }
  assert (Hra3 : rdn source_segs mem3
                   (Z_to_bv 64 (bv_unsigned rsp - 0x8)) 8%nat
                 = Some (word_to_le_bytes 8 (0x11128 : word))).
  { rewrite Hread3 by (rewrite ?u_Z2bv by lia; lia).
    exact fread_slot_ra. }
  assert (Hframe3 : forall a,
    In a [Z_to_bv 64 (bv_unsigned rsp - 0x30);
          Z_to_bv 64 (bv_unsigned rsp - 0x28);
          Z_to_bv 64 (bv_unsigned rsp - 0x20);
          Z_to_bv 64 (bv_unsigned rsp - 0x18);
          Z_to_bv 64 (bv_unsigned rsp - 0x10)] ->
    rdn source_segs mem3 a 8%nat
    = Some (word_to_le_bytes 8 (Z_to_bv 64 0))).
  { intros a Ha.
    repeat destruct Ha as [<- | Ha]; try (exfalso; exact Ha);
      (rewrite Hread3 by (rewrite ?u_Z2bv by lia; lia);
       apply fread_slot_0;
       repeat first [ left; reflexivity | right ]). }
  assert (Hsc3' : store_ok source_segs mem3
                    (Z_to_bv 64 (bv_unsigned rsp - 0x38)) 8%nat = true).
  { eapply store_ok_mono; [ apply (mem_ok_grows_w aG mem3 Hmok3) | ].
    unfold rwmem.
    apply (store_ok_wrap_window_valid source_segs inp rmb source_phdrs _ rsp rbrk _ _ rrnd
             Hvl Hlau);
      unfold stack_window_reach, stack_max_size; u_norm; lia. }
  (* the whole emitted buffer, read back out of the grant: the two
     just-stored header words spliced with the drained prefix *)
  assert (Hbuf : rdn source_segs mem3 aG (8 + length acc)%nat
                 = Some (arena_out acc)).
  { unfold arena_out.
    assert (Hh8 : hdr8 (length acc) = h1 ++ h2)
      by (unfold h1, h2; rewrite !hw4_bytes; reflexivity).
    rewrite Hh8.
    apply rdn_app.
    - (* the eight header bytes, from the two [sw]s *)
      unfold mem3.
      rewrite (rdn_wbytes_out source_segs (word_to_le_bytes 8 (0x110b8 : word)))
        by (unfold scr; rewrite ?length_N_to_le_bytes;
            rewrite ?u_Z2bv by lia; lia).
      change 8%nat with (4 + 4)%nat.
      apply rdn_app.
      + unfold mem1.
        rewrite (rdn_wbytes_out source_segs h2)
          by (unfold h2; rewrite ?length_N_to_le_bytes;
              rewrite ?u_Z2bv by lia; lia).
        replace 4%nat with (length h1)
          by (unfold h1; apply length_N_to_le_bytes).
        apply rdn_wbytes_hit.
        unfold h1; rewrite length_N_to_le_bytes; lia.
      + rewrite word_add_nat.
        change (Z.of_nat 4) with 4%Z.
        replace 4%nat with (length h2)
          by (unfold h2; apply length_N_to_le_bytes).
        apply rdn_wbytes_hit.
        unfold h2; rewrite length_N_to_le_bytes;
          rewrite u_Z2bv by lia; lia.
    - (* the drained prefix, untouched below all three stores *)
      rewrite word_add_nat.
      change (Z.of_nat 8) with 8%Z.
      unfold mem3.
      rewrite (rdn_wbytes_out source_segs (word_to_le_bytes 8 (0x110b8 : word)))
        by (unfold scr; rewrite ?length_N_to_le_bytes;
            rewrite ?u_Z2bv by (unfold cap in *; lia);
            unfold cap in *; lia).
      rewrite (rdn_wbytes_out source_segs h2)
        by (unfold h2; rewrite ?length_N_to_le_bytes;
            rewrite ?u_Z2bv by (unfold cap in *; lia);
            unfold cap in *; lia).
      unfold mem1.
      rewrite (rdn_wbytes_out source_segs h1)
        by (unfold h1; rewrite ?length_N_to_le_bytes;
            rewrite ?u_Z2bv by (unfold cap in *; lia);
            unfold cap in *; lia).
      exact Hrdn. }
  (* the write ecall *)
  replace (Z_to_bv 64 0x11258) with (0x11258 : word) in HmsK |- * by bveq.
  eapply twt_step;
    [ reflexivity | exact (step_ecall _ _ _ _ _ _ SF_11258 eq_refl) | ].
  apply twt_more; [rewrite arena_out_length; lia|].
  apply (twl_write_rec source_segs (Z_to_bv 64 2)).
  - rewrite K17. vm_compute. reflexivity.
  - rewrite <- getr_nz by reg_neq_tac; exact K10.
  - rewrite <- ?getr_nz by reg_neq_tac; rewrite K11, K12.
    rewrite (ms_read_bytes_rdn (run_segments source_segs inp rsp rmb)) by reflexivity;
      unfold run_segments; apply rdn_lift.
    cbn [ms_mem].
    rewrite word_to_nat_ntw by (unfold cap in *; lia).
    exact Hbuf.
  - (* [vfs_write]'s [access_ok]: the arena page lies below the stack *)
    rewrite <- ?getr_nz by reg_neq_tac; rewrite K11, K12.
    apply Uaccess.access_okb_intro.
    rewrite u_ntw by (unfold cap in *; lia).
    unfold TASK_SIZE, cap in *. lia.
  - rewrite arena_out_length; lia.
  - (* every delivered length: the put2 retry loop delivers the rest *)
    intros n Hn1 Hn2.
    replace (v_addi (0x11258 : word) 4) with (Z_to_bv 64 0x1125c) by bveq.
    apply (src_put_wall (length (arena_out acc)) (arena_out acc) aG n).
    + lia.
    + exact Hn1.
    + exact Hn2.
    + rewrite arena_out_length; unfold cap in *; lia.
    + exact Hpos.
    + rewrite arena_out_length; unfold cap in *; lia.
    + exact Hscr3.
    + exact Hra3.
    + exact Hframe3.
    + exact Hsc3'.
    + rewrite arena_out_length. exact Hbuf.
    + exact K1.
    + exact K2.
    + transitivity (nat_to_word (8 + length acc));
        [ exact K8
        | unfold len_word, nat_to_word; rewrite arena_out_length;
          reflexivity ].
    + exact K18.
Qed.

Lemma src_Hfull : forall fs0 acc c,
  src_LH fs0 acc c -> (cap <= length acc)%nat ->
  realizes (run_segments source_segs inp rsp rmb) c (arena_tail fs0 acc).
Proof.
  intros fs0 acc c HLH Hfull. apply src_tail.
  unfold src_LH in HLH.
  rewrite (proj2 (Nat.leb_le _ _) Hfull) in HLH. exact HLH.
Qed.

(** The loop body: from the head at 0x11060 the three argument
    instructions compute a1 = s1 + s0 + 8 and a2 = s4 - s0 =
    [DrainAlg.dcnt acc], and musl's [read] wrapper runs to the ecall at
    0x11258 with a7 = 63. *)
Lemma src_Hread : forall fs0 acc c,
  src_LH fs0 acc c -> (length acc < cap)%nat ->
  exists ms1 buf x8 w,
    m_halted (cfg_model c) = None /\
    m_vm_lazy (cfg_model c) = [] /\
    fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 0)
      = Some (FdChannel (Z_to_bv 64 0)) /\
    msteps (run_segments source_segs inp rsp rmb) (cfg_ms c) ms1 /\
    ms_svc_pending ms1 = Some x8 /\
    bv_unsigned x8 = 63%Z /\
    ms_gpr ms1 0 = Z_to_bv 64 0 /\
    ms_gpr ms1 1 = buf /\
    ms_gpr ms1 2 = dcnt cap acc /\
    read_bytes_map (ms_writable_byte (run_segments source_segs inp rsp rmb) ms1) buf (dcnt cap acc)
      = Some w /\
    (* the read range passes [access_ok]: the arena is a grant under this
       run's [alloc_top], itself under [State.TASK_SIZE]; [DrainAlg]'s
       [Hread] asks for it because [vfs_read] tests it before the fd is
       consulted *)
    access_okb buf (bv_unsigned (dcnt cap acc)) = true /\
    realizes (run_segments source_segs inp rsp rmb) (rd_next ms1 (cfg_model c) buf [])
      (arena_tail fs0 acc) /\
    (forall bs, rd_adm (m_stdin (cfg_model c)) (dcnt cap acc) bs -> bs <> [] ->
       src_LH fs0 (acc ++ bs) (rd_next ms1 (cfg_model c) buf bs)).
Proof.
  intros fs0 acc c HLH Hlt.
  pose proof rsp_lo_num. pose proof rsp_hi_num. pose proof stack_max_size_val as Hsms.
  unfold src_LH in HLH.
  rewrite (proj2 (Nat.leb_gt cap (length acc)) Hlt) in HLH.
  destruct HLH as (aG & regs & mem & Hb & Hh & Hlazy & Hfs & Hfd0 & Hfd2 & Hms0 &
                   H9 & H18 & H20 & H19 & H8 & H2 & Hle & Hmok & Hrdn).
  pose proof Hb as Hb2. destruct Hb2 as (Hpos & Hal & Hceil & _).
  pose proof rsp_hi_num. unfold stack_max_size in Hceil.
  pose proof (u64_range aG) as HaR.
  pose proof (grant_below_stack aG Hb) as Hbs.
  destruct (src_read_block aG regs mem (length acc) Hb ltac:(lia) Hmok
              H2 H8 H9 H18 H19 H20)
    as (R1 & K1 & K2 & K8 & K9 & K18 & K19 & K20 & K17 & K10 & K11 & K12 & Hms1).
  set (mem1 := wbytes mem scr (word_to_le_bytes 8 (0x11074 : word))) in *.
  assert (Hmok1 : mem_ok aG mem1).
  { unfold mem1. apply mem_ok_scratch8;
      [ exact Hmok | exact Hb | unfold scr; u_norm; lia | unfold scr; u_norm; lia ]. }
  assert (Hra1 : rdn source_segs mem1 scr 8%nat
                 = Some (word_to_le_bytes 8 (0x11074 : word))).
  { unfold mem1. apply rdn_wbytes_hit8. unfold scr; u_norm; lia. }
  assert (Hrdn1 : rdn source_segs mem1 (Z_to_bv 64 (bv_unsigned aG + 8))
                    (length acc) = Some acc).
  { unfold mem1. rewrite rdn_wbytes_below
      by (rewrite ?length_N_to_le_bytes; unfold scr; u_norm; unfold cap in *; lia).
    exact Hrdn. }
  assert (Hgr : mem_grows (zmem fmem aG (Z_to_bv 64 4096)) mem1).
  { unfold mem1. eapply mem_grows_trans; [ | apply wbytes_grows ].
    exact (proj1 Hmok). }
  assert (Hwb : exists w,
    read_bytes_map (ms_writable_byte (run_segments source_segs inp rsp rmb) (src_rd_ms R1 mem1))
      (bufA aG (length acc)) (dcnt cap acc) = Some w).
  { eapply (zmem_wbuf (run_segments source_segs inp rsp rmb) (src_rd_ms R1 mem1) fmem aG
              (Z_to_bv 64 4096)).
    - unfold src_rd_ms; cbn [ms_mem]. exact Hgr.
    - change (bv_unsigned (Z_to_bv 64 4096)) with 4096%Z. lia.
    - unfold bufA. rewrite u_Z2bv by (unfold cap in *; lia). lia.
    - unfold bufA. rewrite u_Z2bv by (unfold cap in *; lia).
      rewrite (dcnt_val cap Hcap_lt (src_LH fs0) (arena_tail fs0) acc) by lia.
      change (bv_unsigned (Z_to_bv 64 4096)) with 4096%Z. unfold cap in *. lia. }
  destruct Hwb as (w & Hwb).
  exists (src_rd_ms R1 mem1), (bufA aG (length acc)), (getr R1 17), w.
  split; [exact Hh|]. split; [exact Hlazy|]. split; [exact Hfd0|].
  split.
  { (* the silent run from the loop head to the [ecall] *)
    apply msteps_run.
    replace (0x11060 : word) with (Z_to_bv 64 0x11060) in Hms0 by bveq.
    eapply msteps_trans; [exact Hms0|].
    eapply msteps_trans; [exact Hms1|].
    norm_pc. unfold src_rd_ms.
    eapply mst_step;
      [ reflexivity | exact (step_ecall _ _ _ _ _ _ SF_11258 eq_refl)
      | apply mst_refl ]. }
  split; [reflexivity|]. split; [exact K17|].
  split; [ unfold ms_gpr, src_rd_ms; cbn [ms_regs]; rewrite arg_reg_0;
           rewrite <- getr_nz by reg_neq_tac; exact K10 |].
  split; [ unfold ms_gpr, src_rd_ms; cbn [ms_regs]; rewrite arg_reg_1;
           rewrite <- getr_nz by reg_neq_tac; exact K11 |].
  split; [ unfold ms_gpr, src_rd_ms, dcnt; cbn [ms_regs]; rewrite arg_reg_2;
           rewrite <- getr_nz by reg_neq_tac; exact K12 |].
  split; [exact Hwb|].
  split.
  { (* the range passes [access_ok]: the arena base plus 4096 is under
       this run's [alloc_top], itself far under [State.TASK_SIZE] *)
    apply Uaccess.access_okb_intro.
    unfold bufA. rewrite u_Z2bv by (unfold cap in *; lia).
    rewrite (dcnt_val cap Hcap_lt (src_LH fs0) (arena_tail fs0) acc) by lia.
    unfold TASK_SIZE, cap in *. lia. }
  split.
  { (* EOF: the [beqz] at 0x11078 breaks the loop into the header block *)
    cbn [rd_next]. unfold src_rd_ms. rewrite adv_set.
    apply src_tail.
    destruct (src_ret_eof aG R1 mem1 (length acc) K1 K2 K8 K9 K18 K19 K20 Hra1)
      as (R2 & L2 & L8 & L9 & L18 & L19 & L20 & Hms2).
    unfold src_inv. exists aG, R2, mem1. cbn [cfg_ms cfg_model].
    split; [exact Hb|]. split; [exact Hh|]. split; [exact Hlazy|].
    split; [exact Hfs|].
    split; [exact Hfd0|]. split; [exact Hfd2|].
    split.
    { replace (v_addi (0x11258 : word) 4) with (Z_to_bv 64 0x1125c) by bveq.
      replace (0x11084 : word) with (Z_to_bv 64 0x11084) by bveq.
      exact Hms2. }
    split; [exact L9|]. split; [exact L18|]. split; [exact L20|].
    split; [exact L19|]. split; [exact L8|]. split; [exact L2|].
    split; [exact Hle|]. split; [exact Hmok1|]. exact Hrdn1. }
  (* a delivered block: back to the loop head, or into the header block
     if it has just filled the arena *)
  intros bs Hadm Hne.
  assert (Hbl : (length acc + length bs <= cap)%nat).
  { destruct Hadm as [(-> & _)|(Hlo1 & Hhi1 & _)]; [congruence|].
    rewrite (dcnt_val cap Hcap_lt (src_LH fs0) (arena_tail fs0) acc) in Hhi1
      by lia. lia. }
  assert (Hb1 : (1 <= length bs)%nat)
    by (destruct bs; [congruence | cbn [length]; lia]).
  destruct bs as [|b0 bs0]; [congruence|].
  cbn [rd_next]. unfold src_rd_ms. rewrite adv_write.
  set (bs := b0 :: bs0) in *.
  set (mem2 := write_to_mem mem1 (bufA aG (length acc)) bs) in *.
  assert (Hmok2 : mem_ok aG mem2).
  { unfold mem2. apply mem_ok_buf;
      [ exact Hmok1 | exact Hb
      | unfold bufA; rewrite u_Z2bv by (unfold cap in *; lia); lia
      | unfold bufA; rewrite u_Z2bv by (unfold cap in *; lia);
        unfold cap in *; lia ]. }
  assert (Hra2 : rdn source_segs mem2 scr 8%nat
                 = Some (word_to_le_bytes 8 (0x11074 : word))).
  { unfold mem2. rewrite write_to_mem_wbytes.
    rewrite rdn_wbytes_disjoint
      by (unfold bufA, scr; rewrite ?u_Z2bv by (unfold cap in *; lia);
          unfold cap in *; lia).
    exact Hra1. }
  assert (Hrdn2 : rdn source_segs mem2 (Z_to_bv 64 (bv_unsigned aG + 8))
                    (length acc + length bs) = Some (acc ++ bs)).
  { apply rdn_app.
    - unfold mem2. rewrite write_to_mem_wbytes.
      rewrite rdn_wbytes_below
        by (unfold bufA; rewrite ?u_Z2bv by (unfold cap in *; lia);
            unfold cap in *; lia).
      exact Hrdn1.
    - rewrite (bufA_split aG (length acc) Hb ltac:(lia)).
      unfold mem2. apply rdn_write_to_mem.
      unfold bufA. rewrite u_Z2bv by (unfold cap in *; lia).
      unfold cap in *; lia. }
  destruct (src_ret_blk aG R1 mem2 (length acc) bs K1 K2 K8 K9 K18 K19 K20
              Hra2 Hb1 Hbl)
    as (R2 & L2 & L8 & L9 & L18 & L19 & L20 & Hms2).
  unfold src_LH, src_inv. rewrite length_app.
  exists aG, R2, mem2. cbn [cfg_ms cfg_model].
  split; [exact Hb|].
  split; [rewrite m_halted_with_stdin; exact Hh|].
  split; [rewrite m_vm_lazy_with_stdin; exact Hlazy|].
  split; [rewrite m_fs_with_stdin; exact Hfs|].
  split; [rewrite m_fds_with_stdin; exact Hfd0|].
  split; [unfold fdchan in *; rewrite m_fds_with_stdin; exact Hfd2|].
  split.
  { replace (v_addi (0x11258 : word) 4) with (Z_to_bv 64 0x1125c) by bveq.
    destruct (cap <=? length acc + length bs)%nat;
      [ replace (0x11084 : word) with (Z_to_bv 64 0x11084) by bveq
      | replace (0x11060 : word) with (Z_to_bv 64 0x11060) by bveq ];
      exact Hms2. }
  split; [exact L9|]. split; [exact L18|]. split; [exact L20|].
  split; [exact L19|]. split; [exact L8|]. split; [exact L2|].
  split; [exact Hbl|]. split; [exact Hmok2|]. exact Hrdn2.
Qed.

(* ----------------------------------------------------------------- *)
(* The composition                                                    *)
(* ----------------------------------------------------------------- *)

Lemma source_realizes :
  realizes (run_segments source_segs inp rsp rmb)
    (init_config (run_segments source_segs inp rsp rmb) SourceMemImage_init_pc source_phdrs
       rsp rbrk rmb rrnd source_alloc_limit inp)
    (arena_outcomes (in_fs inp) (in_stdin inp)).
Proof.
  destruct src_to_mmap
    as (regs & Hra & Hsp & H11 & H12 & H13 & H14 & H15 & H10 & Hno & Hms).
  unfold init_config, arena_outcomes, arena_fail.
  rewrite source_reserved_run.
  set (fs0 := in_fs inp) in *.
  eapply (rz_mmap_drain (run_segments source_segs inp rsp rmb) cap Hcap_lt Hcap_mod
            (src_LH fs0) (arena_tail fs0) (src_Hfull fs0) (src_Hread fs0)
            _ (src_mmap_ms regs)
            (with_vdso (Vdso.vdso_run_init (ed_vdso rrnd))
               (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp))
            (getr regs 17) [] (Z_to_bv 64 1)).
  - reflexivity.
  - reflexivity.
  - (* fd 1 is the stdout channel with a reader ([State.with_vdso] keeps
       the descriptor table) *)
    split; [reflexivity | exact Hrd].
  - exact (msteps_run source_segs inp rsp rmb _ _ Hms).
  - reflexivity.
  - exact Hno.
  - (* mmap_args_ok *)
    unfold mmap_args_ok, ms_gpr, src_mmap_ms; cbn [ms_regs].
    rewrite arg_reg_1, arg_reg_2.
    assert (E3 : Z_to_bv 5 (10 + Z.of_nat 3) = (13 : reg)) by (apply bv_eq; reflexivity).
    assert (E4 : Z_to_bv 5 (10 + Z.of_nat 4) = (14 : reg)) by (apply bv_eq; reflexivity).
    assert (E5 : Z_to_bv 5 (10 + Z.of_nat 5) = (15 : reg)) by (apply bv_eq; reflexivity).
    rewrite E3, E4, E5.
    rewrite <- !getr_nz by reg_neq_tac.
    refine (conj _ (conj H12 (conj H13 (conj _ H15)))).
    + rewrite H11. discriminate.
    + rewrite H14. apply bv_eq. vm_compute. reflexivity.
  - (* a NULL hint is never declined: Linux v6.18.46 mm/mmap.c:754-761
       tries the hint only when it is nonzero, :763-770 search *)
    assert (Ha0 : ms_gpr (src_mmap_ms regs) 0 = Z_to_bv 64 0).
    { unfold ms_gpr, src_mmap_ms; cbn [ms_regs]. rewrite arg_reg_0.
      rewrite <- getr_nz by reg_neq_tac. exact H10. }
    rewrite Ha0. reflexivity.
  - intros e He. cbn [mmap_errnos In] in He.
    destruct He as [<- | []].
    cbn [to_wallexit]. apply to_wexit_run.
    apply src_fail_wexit;
      [ unfold ENOMEM; lia | unfold ENOMEM; lia | exact Hra | exact Hsp ].
  - intros a Ha. eapply src_grant_LH; eassumption.
  - assert (Hlen : ms_gpr (src_mmap_ms regs) 1 = Z_to_bv 64 4096).
    { unfold ms_gpr, src_mmap_ms; cbn [ms_regs]. rewrite arg_reg_1.
      rewrite <- getr_nz by reg_neq_tac. exact H11. }
    rewrite Hlen.
    change (page_round_up_Z (bv_unsigned (Z_to_bv 64 4096))) with 4096%Z.
    exact (source_grant_witness inp _ rbrk rmb rsp _ Hsp_lo Hmb).
  - (* the failure branch writes nothing at all *)
    constructor.
Qed.

End SourceProof.
