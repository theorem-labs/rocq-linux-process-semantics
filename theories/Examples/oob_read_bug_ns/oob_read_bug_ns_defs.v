(** * oob-read-bug-ns: shared definitions and helper lemmas.

    PROOF-SIDE FILE (not part of the trusted specification).

    Bytes are [byte = bv 8], machine values [word = bv 64]; the byte
    sum lives in unbounded [Z] over [bv_unsigned] (it feeds
    [udec : Z -> list byte]); the outcome sets are
    [(list (list byte) * word)] pairs with exit codes [Z_to_bv 64 4] /
    [Z_to_bv 64 0]; the resolution-set algebra
    ([growable]/[T1]/[T2]/[brk_r_ok]) comes from Common/AllocSim over words.

    With [s = argv[1]], [n = strlen(s)], the shared observable behavior:
    - argc < 2                    : no output, exit 2
    - n > 65536                   : no output, exit 3
    - n <= 65536                  : the outcome SET
        { ([], 4) } ∪ { ([udec (sumb s); "\n"], 0) }
      (brk resolutions: any failing resolution exits 4 silently; any
      succeeding resolution writes the decimal byte sum + newline and
      exits 0; both kinds of resolution always exist — except that for
      n = 0 the second brk cannot fail, which the set algebra below
      accounts for).  The chunk loop may read beyond the logical
      n-byte allocation, but the page-rounded brk grant supplies zero
      padding through the rounded chunk boundary.

    This file: the outcome-set definitions and resolution-set algebra,
    the decimal-rendering spec [udec] and its decomposition lemmas, the
    byte-sum [sumb], argv/byte helpers, arbitrary-byte stores, and the
    step-chaining tactics. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec AllocSim WallSim NumPrint StepTac MuslStrlen StreamSim StoreOk.
From LinuxProcessSemantics.Examples.oob_read_bug_ns Require Import oob_read_bug_ns_code.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.

Import ListNotations.


Open Scope bv_scope.

(* ######################################################################### *)
(* The spec functions: byte sum and unsigned decimal rendering               *)
(* ######################################################################### *)

(** Sum of the bytes of a string, in unbounded [Z] over [bv_unsigned]. *)
Definition sumb (s : list byte) : Z :=
  fold_right (fun b acc => (bv_unsigned b + acc)%Z) 0%Z s.

(* udec_aux/udec (unsigned decimal rendering) live in NumPrint. *)

(** The two output buffers of a successful run. *)
Definition outbufs (s : list byte) : list (list byte) :=
  [udec (sumb s); [Z_to_bv 8 10]].

(** Both output buffers are small enough for the model to transfer in one
    [write]: the decimal rendering is capped by [udec]'s own fuel (24 digits)
    whatever the byte sum is, and the newline is a single byte. *)
Lemma outbufs_modeled : forall s, bufs_modeled (outbufs s).
Proof.
  intro s.
  assert (Hdec : (length (udec (sumb s)) <= 24)%nat).
  { unfold udec. destruct (sumb s =? 0)%Z; [cbn; lia | apply udec_aux_len]. }
  unfold outbufs, bufs_modeled.
  apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]];
    unfold buf_modeled, rw_bytes_max; cbn [length]; lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* sumb lemmas                                                                *)
(* ------------------------------------------------------------------------- *)

Lemma sumb_app : forall a b, sumb (a ++ b) = (sumb a + sumb b)%Z.
Proof.
  induction a as [|x a IH]; intro b; [reflexivity|].
  cbn [app]. unfold sumb in *. cbn [fold_right]. rewrite IH. lia.
Qed.

Lemma sumb_le : forall s, Forall (fun b : byte => (bv_unsigned b < 256)%Z) s ->
  (sumb s <= 255 * Z.of_nat (length s))%Z.
Proof.
  induction s as [|x s IH]; intro Hf; [cbn; lia|].
  inversion Hf as [|? ? Hx Hs]; subst.
  specialize (IH Hs). unfold sumb in *. cbn [fold_right length].
  rewrite Nat2Z.inj_succ. pose proof (u8_range x). lia.
Qed.

Lemma firstn_snoc : forall (s : list byte) k, (k < length s)%nat ->
  firstn (S k) s = firstn k s ++ [nth k s (Z_to_bv 8 0)].
Proof.
  intros s k Hk.
  rewrite <- (firstn_skipn k s) at 1.
  rewrite (skipn_nth s k (Z_to_bv 8 0) Hk).
  replace (S k) with (k + 1)%nat by lia.
  rewrite firstn_app, firstn_firstn.
  replace (Nat.min (k + 1) k) with k by lia.
  rewrite firstn_length_le by lia.
  replace (k + 1 - k)%nat with 1%nat by lia.
  cbn [firstn]. reflexivity.
Qed.

Lemma sumb_firstn_S : forall (s : list byte) k, (k < length s)%nat ->
  sumb (firstn (S k) s) = (sumb (firstn k s) + bv_unsigned (nth k s (Z_to_bv 8 0)))%Z.
Proof.
  intros s k Hk. rewrite firstn_snoc by exact Hk.
  rewrite sumb_app. cbn [sumb fold_right]. lia.
Qed.

(** The same recurrence with a zero default, including indices in a
    page-rounded padding tail past the end of the list. *)
Lemma sumb_firstn_S_default : forall (s : list byte) k,
  sumb (firstn (S k) s) =
  (sumb (firstn k s) + bv_unsigned (nth k s (Z_to_bv 8 0)))%Z.
Proof.
  intros s k. destruct (lt_dec k (length s)) as [Hlt|Hge].
  - apply sumb_firstn_S. exact Hlt.
  - rewrite !firstn_all2 by lia.
    rewrite nth_overflow by lia.
    change (bv_unsigned (Z_to_bv 8 0)) with 0%Z. lia.
Qed.

Lemma sumb_firstn_all : forall (s : list byte), sumb (firstn (length s) s) = sumb s.
Proof. intro s. rewrite firstn_all. reflexivity. Qed.

(** The digit-char formation [addiw d 48] for a digit d. *)
Lemma v_addiw_d48 : forall d : word, (bv_unsigned d <= 9)%Z ->
  bv_unsigned (v_addiw d 48) = (48 + bv_unsigned d)%Z.
Proof.
  intros d Hd. rewrite v_addiw_small; pose proof (u64_range d); lia.
Qed.

(* ######################################################################### *)
(* The shared outcome sets and the resolution-set algebra                    *)
(* ######################################################################### *)

(** The outcome set, parameterized by the grow amount [n] (= strlen):
    the silent exit-4 outcome exists exactly when the second brk is a
    GENUINE grow ([n <> 0]) that the kernel may refuse.  For [n = 0] the
    second brk re-requests the current break, which never fails (the
    same on Linux: newbrk = oldbrk short-circuits to success), so the
    run is deterministic. *)
Definition oobU (n : word) (bufs : list (list byte))
    : (list (list byte) * word) -> Prop :=
  fun o => (n <> Z_to_bv 64 0 /\ o = ([], Z_to_bv 64 4))
        \/ o = (bufs, Z_to_bv 64 0).


(* growable, T1, T2, brk_r_ok_query_iff, brk_r_ok_grow_iff, T1_iff_T2,
   T2_fail_iff, T2_succ_iff live in Common/AllocSim. *)

(** The first brk node: brk(0) is DETERMINISTIC — it reports the
    quantified ASLR base [b] — so the resolution set is the singleton
    {b} and the outcome set is [T1] AT [b].  Works for [n = 0] too:
    [growable] then excludes the exit-4 element on both sides. *)
Lemma oobU_iff_T1 : forall reserved (lim top : Z) (n : word) bufs (b : word) (P : word -> Prop),
  (forall r, P r <-> r = b) ->
  growable reserved lim top n b ->
  forall o, oobU n bufs o <->
    (exists r, P r /\ T1 reserved lim top n bufs r o).
Proof.
  intros reserved lim top n bufs b P HP Hg o.
  split.
  - intros [[Hn ->] | ->]; exists b; (split; [apply HP; reflexivity|]).
    + left. split; [reflexivity | right; right; exact Hn].
    + right. split; [exact Hg | reflexivity].
  - intros (r & Hr & [[-> Hcase] | [_ Ho]]).
    + apply HP in Hr; subst r.
      destruct Hg as (Hb0 & Hw & _).
      left. split; [| reflexivity].
      destruct Hcase as [Hc | [Hc | Hc]]; [congruence | lia | exact Hc].
    + right; exact Ho.
Qed.

(** A region entirely above every reservation is free. *)
Lemma region_free_above : forall (l : list (word * word)) lo n,
  Forall (fun p => (bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned lo)%Z) l ->
  region_free l lo n = true.
Proof.
  induction l as [|[a sz] l IH]; intros lo n Hf; [reflexivity|].
  inversion Hf as [|? ? Ha Hl]; subst. cbn [fst snd] in Ha.
  cbn [region_free]. unfold iv_overlap.
  assert (E : Z.ltb (bv_unsigned lo) (bv_unsigned a + bv_unsigned sz) = false)
    by (apply Z.ltb_ge; lia).
  rewrite E. cbn [andb negb]. apply IH. exact Hl.
Qed.

(* ######################################################################### *)
(* The run's brk ledger: the image's reservations, then the vDSO pair        *)
(* ######################################################################### *)

Lemma region_free_cat : forall l1 l2 (lo n : word),
  region_free (l1 ++ l2) lo n = region_free l1 lo n && region_free l2 lo n.
Proof.
  induction l1 as [|[b s] l1 IH]; intros l2 lo n; [reflexivity|].
  cbn [region_free app]. rewrite IH, andb_assoc. reflexivity.
Qed.

Lemma page_round_down_Z_bounds : forall x,
  (x - page_size < page_round_down_Z x <= x)%Z.
Proof.
  intro x. unfold page_round_down_Z, page_size.
  pose proof (Z.div_mod x 4096 ltac:(lia)).
  pose proof (Z.mod_pos_bound x 4096 ltac:(lia)). lia.
Qed.

(** A range free of the run's brk ledger ([State.init_reserved]) is free
    of the image's part of it. *)
Lemma region_free_init_reserved_img : forall res (mbase sp : word) kb (lo n : word),
  region_free (init_reserved res mbase sp kb) lo n = true ->
  region_free res lo n = true.
Proof.
  intros res mbase sp kb lo n H.
  unfold init_reserved in H. rewrite region_free_cat in H.
  apply andb_true_iff in H. exact (proj1 H).
Qed.

(** The run's brk ledger ([State.init_reserved]: the image's
    reservations, then the vDSO pair at the page below
    [min mbase (sp - stack_max_size)]) leaves every range below [2^40]
    free once the image's part does.  The pair sits at or above
    [mmap_base_min - stack_max_size - 20 pages] ([State.vdso_len_bounds]),
    far above [2^40]. *)
Lemma run_ledger_free : forall res (mbase sp : word) kb (lo n : word),
  (mmap_base_min <= bv_unsigned mbase)%Z ->
  (sp_window_lo <= bv_unsigned sp)%Z ->
  region_free res lo n = true ->
  (bv_unsigned lo + bv_unsigned n <= 2 ^ 40)%Z ->
  region_free (init_reserved res mbase sp kb) lo n = true.
Proof.
  intros res mbase sp kb lo n Hmb Hsp Hres Hlo.
  unfold init_reserved. rewrite region_free_cat, Hres. cbn [andb].
  apply region_free_below.
  pose proof (u64_range mbase) as Hmu.
  pose proof (vdso_len_bounds kb) as Hv.
  pose proof (page_round_down_Z_bounds
                (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size))) as Ht.
  unfold mmap_base_min in Hmb. unfold sp_window_lo in Hsp.
  unfold vdso_reserved. cbv zeta.
  match goal with |- Forall _ (if ?c then _ else _) => destruct c eqn:E end;
    [constructor|].
  apply Z.ltb_ge in E.
  unfold stack_max_size, vdso_vvar_pages, page_size in *.
  repeat constructor; cbn [fst]; rewrite u_Z2bv by lia; lia.
Qed.

(** [AllocSim.growable] over the run's ledger, for a page-aligned break
    above the image that grows by a small positive [t]: the image part is
    free by [region_free_above_top], the vDSO pair by [run_ledger_free];
    the page-rounded budget is at most [t + page_size - 1]. *)
Lemma growable_ledger : forall res (mbase sp : word) kb (lim top : Z) (t r : word),
  (mmap_base_min <= bv_unsigned mbase)%Z ->
  (sp_window_lo <= bv_unsigned sp)%Z ->
  (bv_unsigned r mod page_size = 0)%Z ->
  (0 < bv_unsigned r)%Z ->
  (reserved_top res <= bv_unsigned r)%Z ->
  (0 < bv_unsigned t)%Z ->
  (bv_unsigned r + bv_unsigned t + page_size - 1 <= top)%Z ->
  (bv_unsigned t + page_size - 1 <= lim)%Z ->
  (bv_unsigned r + bv_unsigned t + 2 * page_size <= 2 ^ 40)%Z ->
  growable (init_reserved res mbase sp kb) lim top t r.
Proof.
  intros res mbase sp kb lim top t r Hmb Hsp Halign Hr0 Htop Hpos Hceil Hlim Hsmall.
  pose proof (u64_range r) as Hru. pose proof (u64_range t) as Hut.
  assert (Hps : page_size = 4096%Z) by reflexivity.
  split; [|split].
  - intro Hc. apply (f_equal bv_unsigned) in Hc.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia.
  - lia.
  - right.
    rewrite (page_round_up_Z_aligned (bv_unsigned r)) by first [lia | exact Halign].
    pose proof (page_round_up_Z_bounds (bv_unsigned r + bv_unsigned t) ltac:(lia))
      as Hb2.
    assert (Hlt : (bv_unsigned r < page_round_up_Z (bv_unsigned r + bv_unsigned t))%Z)
      by lia.
    rewrite (proj2 (Z.ltb_lt _ _) Hlt), Z_to_bv_bv_unsigned.
    cbv iota.
    assert (Hfree : region_free (init_reserved res mbase sp kb) r
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned r + bv_unsigned t)
                           + page_size - bv_unsigned r)) = true).
    { apply run_ledger_free; [exact Hmb | exact Hsp | |].
      - apply region_free_above_top. exact Htop.
      - rewrite u_Z2bv by lia. lia. }
    rewrite Hfree.
    apply andb_true_iff. split; [apply andb_true_iff; split; [|reflexivity]|].
    + apply Z.leb_le. lia.
    + apply Z.leb_le. lia.
Qed.

(* ######################################################################### *)
(* argv helpers                                                              *)
(* ######################################################################### *)

Lemma nth_bound : forall (s : list byte) j,
  Forall (fun b : byte => (bv_unsigned b < 256)%Z) s -> (j < length s)%nat ->
  (bv_unsigned (nth j s (Z_to_bv 8 0)) < 256)%Z.
Proof. intros s j _ _. apply u8_range. Qed.

(* ######################################################################### *)
(* Value-shape facts                                                         *)
(* ######################################################################### *)

Lemma v_add_wrap : forall x y : word,
  (2 ^ 64 <= bv_unsigned x + bv_unsigned y)%Z ->
  bv_unsigned (v_add x y) = (bv_unsigned x + bv_unsigned y - 2 ^ 64)%Z.
Proof.
  intros x y Hw. unfold v_add.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  pose proof (u64_range x). pose proof (u64_range y).
  assert (E : (bv_unsigned x + bv_unsigned y
               = (bv_unsigned x + bv_unsigned y - 2 ^ 64) + 1 * 2 ^ 64)%Z) by lia.
  rewrite E at 1. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma v_mul_small : forall x y : word,
  (bv_unsigned x * bv_unsigned y < 2 ^ 64)%Z ->
  bv_unsigned (v_mul x y) = (bv_unsigned x * bv_unsigned y)%Z.
Proof.
  intros x y Hxy. unfold v_mul.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  pose proof (u64_range x). pose proof (u64_range y).
  apply Z.mod_small; nia.
Qed.

(* ######################################################################### *)
(* Byte store (sb) with an arbitrary byte value                               *)
(* ######################################################################### *)

(** Store byte, address and value pre-normalized ([step_sb256]/[step_sb]
    live in [SeqExec]).  The stored byte is the low byte of the source
    register, pre-normalized to [b : byte].  Generic in the FP state (the
    machine states of [SeqExec] are). *)
Section StepSbAt.
Context {fx : FPState}.

Lemma step_sb_at : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a : word) (b : byte),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  Z_to_bv 8 (bv_unsigned (getr regs rs2)) = b ->
  RiscvSemantics.store_ok segs mem a 1%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) (wbytes mem a [b]) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm a b Hf He Hd Ha Hb Hok.
  rewrite (step_sb256 segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
  - rewrite Ha, N_to_le_bytes_1_small, Hb. reflexivity.
  - rewrite Ha. exact Hok.
Qed.

End StepSbAt.

(* ######################################################################### *)
(* wbytes pointwise theory: in-range lookup and disjoint commutation         *)
(* ######################################################################### *)

Lemma wbytes_get : forall (bs : list byte) m (a x : word),
  (bv_unsigned a + Z.of_nat (length bs) < 2 ^ 64)%Z ->
  (bv_unsigned a <= bv_unsigned x)%Z ->
  (Z.to_nat (bv_unsigned x - bv_unsigned a) < length bs)%nat ->
  wbytes m a bs x = nth_error bs (Z.to_nat (bv_unsigned x - bv_unsigned a)).
Proof.
  induction bs as [|b bs IH]; intros m a x Hnw Hax Hlen; [cbn in Hlen; lia|].
  cbn [wbytes].
  pose proof (u64_range a). pose proof (u64_range x). cbn [length] in Hnw.
  assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq | Hne].
  - assert (Hxa : x = a) by (apply bv_eq; exact Heq).
    subst x. rewrite Z.sub_diag. cbn [Z.to_nat nth_error].
    rewrite (wbytes_below bs).
    + rewrite bv_eqb_refl. reflexivity.
    + rewrite Hu1. lia.
    + rewrite Hu1. lia.
  - assert (Hgt : (bv_unsigned a < bv_unsigned x)%Z) by lia.
    rewrite (IH _ (a + 1) x); [| rewrite Hu1; lia | rewrite Hu1; lia | ].
    + replace (Z.to_nat (bv_unsigned x - bv_unsigned a))
        with (S (Z.to_nat (bv_unsigned x - bv_unsigned (a + 1)))) by (rewrite Hu1; lia).
      reflexivity.
    + rewrite Hu1. cbn [length] in Hlen. lia.
Qed.

(** Two disjoint [wbytes] overlays commute (first block entirely below
    the second, both within [2^64]). *)
Lemma wbytes_disjoint_comm : forall (bs1 bs2 : list byte) m (a1 a2 : word),
  (bv_unsigned a1 + Z.of_nat (length bs1) <= bv_unsigned a2)%Z ->
  (bv_unsigned a2 + Z.of_nat (length bs2) < 2 ^ 64)%Z ->
  wbytes (wbytes m a1 bs1) a2 bs2 = wbytes (wbytes m a2 bs2) a1 bs1.
Proof.
  intros bs1 bs2 m a1 a2 Hd Hnw2.
  pose proof (u64_range a1). pose proof (u64_range a2).
  apply FunctionalExtensionality.functional_extensionality. intro x.
  pose proof (u64_range x).
  assert (Hnw1 : (bv_unsigned a1 + Z.of_nat (length bs1) < 2 ^ 64)%Z) by lia.
  destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned a1)) as [Hx1 | Hx1].
  - rewrite (wbytes_below bs2) by lia.
    rewrite !(wbytes_below bs1) by lia.
    rewrite (wbytes_below bs2) by lia. reflexivity.
  - destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned a1 + Z.of_nat (length bs1)))
      as [Hx2 | Hx2].
    + rewrite (wbytes_below bs2) by lia.
      rewrite !(wbytes_get bs1) by lia.
      reflexivity.
    + rewrite (wbytes_above bs1) by lia.
      destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned a2)) as [Hx3 | Hx3].
      * rewrite !(wbytes_below bs2) by lia.
        rewrite (wbytes_above bs1) by lia. reflexivity.
      * destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned a2 + Z.of_nat (length bs2)))
          as [Hx4 | Hx4].
        { rewrite !(wbytes_get bs2) by lia. reflexivity. }
        { rewrite !(wbytes_above bs2) by lia.
          rewrite (wbytes_above bs1) by lia. reflexivity. }
Qed.

(* ######################################################################### *)
(* Byte-sum positivity for a nonempty NUL-free string                         *)
(* ######################################################################### *)

Lemma sumb_pos : forall s, s <> [] -> ~ In (Z_to_bv 8 0) s -> (1 <= sumb s)%Z.
Proof.
  intros [|b t] Hne Hnz; [congruence|].
  assert (Hb : b <> Z_to_bv 8 0) by (intro; apply Hnz; left; auto).
  assert (Hbu : (0 < bv_unsigned b)%Z).
  { pose proof (u8_range b).
    destruct (Z.eq_dec (bv_unsigned b) 0) as [Hz | Hz]; [|lia].
    exfalso. apply Hb. apply bv_eq. rewrite Hz. reflexivity. }
  unfold sumb. cbn [fold_right].
  assert (0 <= fold_right (fun b acc => (bv_unsigned b + acc)%Z) 0%Z t)%Z.
  { clear. induction t as [|c t IH]; cbn [fold_right]; [lia|].
    pose proof (u8_range c). lia. }
  lia.
Qed.

(** The decimal rendering of a value below 2^64 fits in the 24-byte
    stack buffer with at least 4 slots to spare. *)
Lemma udec_len_24 : forall v, (0 <= v)%Z -> (v < 2^64)%Z -> (length (udec v) <= 20)%nat.
Proof. exact udec_len_le. Qed.

(* ######################################################################### *)
(* The machine-level SWAR zero test                                          *)
(* ######################################################################### *)

(** The two magic constants musl's [strlen] materialises before its
    word-at-a-time loop: [-0x0101010101010101] and [0x8080808080808080]. *)
Definition swar_K : word := Z_to_bv 64 0xFEFEFEFEFEFEFEFF.
Definition swar_M : word := Z_to_bv 64 0x8080808080808080.

(** The value musl's loop tests against zero: [(x + K) & ~x & M]. *)
Definition swar_res (x : word) : word :=
  v_and (v_and (v_add x swar_K) (v_xori x (-1)%Z)) swar_M.

(** [swar_res] IS the [HZ.Tz] test of Common/MuslStrlen: the constants
    match [v_haszero]'s literals digit for digit. *)
Lemma swar_res_Tz : forall x : word,
  bv_unsigned (swar_res x) = HZ.Tz (bv_unsigned x).
Proof. intro x. unfold swar_res, swar_K, swar_M. apply v_haszero. Qed.

(** First zero byte of a list: its index, and everything below it
    nonzero (what [HZ.Tz_haszero]'s borrow side condition wants). *)
Lemma in_first_zero : forall bs : list byte, In (Z_to_bv 8 0) bs ->
  exists i, (i < length bs)%nat
    /\ nth i bs (Z_to_bv 8 0) = Z_to_bv 8 0
    /\ forall j, (j < i)%nat -> nth j bs (Z_to_bv 8 0) <> Z_to_bv 8 0.
Proof.
  induction bs as [|b bs IH]; intro Hin; [destruct Hin|].
  destruct (decide (b = Z_to_bv 8 0)) as [-> | Hb].
  - exists 0%nat. cbn [length nth]. split; [lia|].
    split; [reflexivity | intros j Hj; lia].
  - destruct Hin as [He | Hin]; [exact (False_ind _ (Hb He)) |].
    destruct (IH Hin) as (i & Hi & Hz & Hlow).
    exists (S i). cbn [length nth]. split; [lia|]. split; [exact Hz|].
    intros j Hj. destruct j as [|j]; [exact Hb | apply Hlow; lia].
Qed.

(** The two directions of the test at the machine level, via
    [HZ.Tz_nozero] / [HZ.Tz_haszero]. *)
Lemma swar_res_zero : forall (bs : list byte) (x : word),
  length bs = 8%nat -> bv_unsigned x = bytes_le_to_Z bs ->
  ~ In (Z_to_bv 8 0) bs ->
  swar_res x = Z_to_bv 64 0.
Proof.
  intros bs x Hlen Hx Hnz. apply bv_eq.
  rewrite swar_res_Tz, Hx.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  apply HZ.Tz_nozero; [apply bytes_le_to_Z_range; exact Hlen|].
  intros i Hi.
  rewrite zb_of_bytes by lia.
  intro Hz. apply Hnz.
  replace (Z_to_bv 8 0) with (nth i bs (Z_to_bv 8 0));
    [apply nth_In; lia |].
  apply bv_eq. rewrite Hz. symmetry. exact u8_zero.
Qed.

Lemma swar_res_nonzero : forall (bs : list byte) (x : word),
  length bs = 8%nat -> bv_unsigned x = bytes_le_to_Z bs ->
  In (Z_to_bv 8 0) bs ->
  swar_res x <> Z_to_bv 64 0.
Proof.
  intros bs x Hlen Hx Hin Heq.
  apply (f_equal bv_unsigned) in Heq.
  rewrite swar_res_Tz, Hx in Heq.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Heq.
  destruct (in_first_zero bs Hin) as (i & Hi & Hz & Hlow).
  refine (HZ.Tz_haszero (bytes_le_to_Z bs) i
            (bytes_le_to_Z_range bs Hlen) ltac:(lia) _ _ Heq).
  - rewrite zb_of_bytes by lia. rewrite Hz. exact u8_zero.
  - intros j Hj. rewrite zb_of_bytes by lia.
    intro Hzj. apply (Hlow j Hj). apply bv_eq.
    rewrite Hzj. symmetry. exact u8_zero.
Qed.
