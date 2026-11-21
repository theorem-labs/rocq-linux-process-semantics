(** * alloc-join-ns: shared definitions and helper lemmas.

    PROOF-SIDE FILE (not part of the trusted specification).

    Shared observable-behavior spec of both binaries (argv = av):
    - argc < 2                          : no output, exit 2
    - total = |join(av[1..])| + 1 > 65536 : no output, exit 3
    - otherwise                         : the outcome SET
        { ([], 4) } ∪ { ([join(av[1..]) ++ '\n'], 0) }
      — the SOURCE reaches it through two brk resolutions, the TARGET
      through the two mmap resolution families; allocation emits no
      events, so the sets coincide.

    This file: the join-list theory, the brk resolution-set algebra
    (parametric in the total byte count [t]), argv/byte helpers, byte
    stores of arbitrary bytes, and shared word/nat bridge lemmas.

    Bytes are [byte = bv 8], machine values [word = bv 64]; unbounded
    bookkeeping is in [Z] over [bv_unsigned]; the brk resolution-set
    algebra (growable/T1/T2/...) lives in Common/AllocSim over [word]s
    with [Z] bounds. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec AllocSim WallSim MmapSim AllocSim2 StepTac ListFacts MuslStrlen StreamSim StoreOk.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(* ######################################################################### *)
(* Join-list theory                                                          *)
(* ######################################################################### *)

(** Join with single interior spaces (byte 32). *)
Fixpoint join1 (l : list (list byte)) : list byte :=
  match l with
  | [] => []
  | [s] => s
  | s :: r => s ++ Z_to_bv 8 32 :: join1 r
  end.

(** Join with a TRAILING space after every element. *)
Fixpoint wjoin (l : list (list byte)) : list byte :=
  match l with
  | [] => []
  | s :: r => s ++ Z_to_bv 8 32 :: wjoin r
  end.

(** The single written buffer on a successful run. *)
Definition jout (av : list (list byte)) : list byte :=
  join1 (tl av) ++ [Z_to_bv 8 10].

Lemma join1_cons : forall s l, l <> [] ->
  join1 (s :: l) = s ++ Z_to_bv 8 32 :: join1 l.
Proof. intros s l Hl. destruct l; [congruence | reflexivity]. Qed.

Lemma join1_snoc : forall l s, join1 (l ++ [s]) = wjoin l ++ s.
Proof.
  induction l as [|a l IH]; intro s; [reflexivity|].
  cbn [wjoin app].
  rewrite join1_cons by (destruct l; cbn; congruence).
  rewrite IH, <- app_assoc. reflexivity.
Qed.

Lemma wjoin_join1 : forall l, l <> [] -> wjoin l = join1 l ++ [Z_to_bv 8 32].
Proof.
  induction l as [|a l IH]; intro Hl; [congruence|].
  destruct l as [|b l'].
  - reflexivity.
  - change (wjoin (a :: b :: l')) with (a ++ Z_to_bv 8 32 :: wjoin (b :: l')).
    rewrite IH by (intro HX; discriminate HX).
    rewrite (join1_cons a (b :: l')) by (intro HX; discriminate HX).
    rewrite <- !app_assoc. reflexivity.
Qed.

Lemma length_wjoin : forall l, length (wjoin l) = total_arg_bytes_nat l.
Proof.
  induction l as [|a l IH]; [reflexivity|].
  cbn [wjoin total_arg_bytes_nat fold_right].
  rewrite length_app. cbn [length]. unfold total_arg_bytes_nat in IH. lia.
Qed.

Lemma length_join1 : forall l, l <> [] ->
  S (length (join1 l)) = total_arg_bytes_nat l.
Proof.
  intros l Hl.
  rewrite <- length_wjoin. rewrite (wjoin_join1 l Hl).
  rewrite length_app. cbn [length]. lia.
Qed.

Lemma tab_app : forall l1 l2,
  total_arg_bytes_nat (l1 ++ l2) = (total_arg_bytes_nat l1 + total_arg_bytes_nat l2)%nat.
Proof.
  induction l1 as [|a l1 IH]; intro l2; [reflexivity|].
  cbn [app]. unfold total_arg_bytes_nat in *. cbn [fold_right].
  rewrite IH. lia.
Qed.

(* [firstn_S_nth] now lives in Common/ListFacts.v (imported above). *)

Lemma nth_tl : forall (l : list (list byte)) i, nth i (tl l) [] = nth (S i) l [].
Proof. intros l i. destruct l; [destruct i; reflexivity | reflexivity]. Qed.

Lemma length_tl_list : forall (l : list (list byte)),
  length (tl l) = (length l - 1)%nat.
Proof. intro l. destruct l; cbn [tl length]; lia. Qed.

Lemma firstn_nonnil : forall (l : list (list byte)) i,
  (1 <= i)%nat -> l <> [] -> firstn i l <> [].
Proof.
  intros l i Hi Hl. destruct l; [congruence|].
  destruct i; [lia | cbn; congruence].
Qed.

(* ######################################################################### *)
(* Closed word/byte equations, word/nat bridges                              *)
(* ######################################################################### *)

(* [bveq], [byte_nz_u], [u_zext8], [u_ntw], [word_add_nat] now live in
   Common/StepTac.v (imported above). *)

Lemma of_nat_word_to_nat : forall w : word,
  Z.of_nat (word_to_nat w) = bv_unsigned w.
Proof.
  intro w. unfold word_to_nat. pose proof (u64_range w). lia.
Qed.

Lemma v_slli3_nat : forall i : nat, (Z.of_nat i <= 1024)%Z ->
  v_slli (nat_to_word i) 3 = Z_to_bv 64 (8 * Z.of_nat i).
Proof.
  intros i Hi. apply bv_eq. rewrite Z_to_bv_unsigned.
  rewrite v_slli_3 by (rewrite u_ntw by lia; lia).
  rewrite u_ntw by lia.
  rewrite bv_wrap_small; [reflexivity|].
  change (bv_modulus 64) with (2^64)%Z. lia.
Qed.

Lemma word_to_nat_ntw : forall n : nat, (Z.of_nat n < 2^64)%Z ->
  word_to_nat (nat_to_word n) = n.
Proof. intros n Hn. unfold word_to_nat. rewrite u_ntw by lia. lia. Qed.

(** Successor step of a [nat_to_word] index as a wrapping [bv] add
    (hypothesis-free: both sides wrap identically). *)
Lemma ntw_S : forall n : nat, nat_to_word (S n) = nat_to_word n + 1.
Proof.
  intro n. apply bv_eq. unfold nat_to_word.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  change (bv_unsigned (1 : word)) with 1%Z.
  rewrite bv_wrap_add_idemp_l. f_equal. lia.
Qed.

(** [v_sub] on in-range [nat_to_word] operands. *)
Lemma ntw_sub : forall m k : nat, (k <= m)%nat -> (Z.of_nat m < 2^64)%Z ->
  v_sub (nat_to_word m) (nat_to_word k) = nat_to_word (m - k).
Proof.
  intros m k Hk Hm. apply bv_eq. unfold v_sub.
  rewrite !u_ntw by lia.
  rewrite u_Z2bv by lia. lia.
Qed.

(* [c_eq_0_of_u] lives in Common/PropExec.v, and [of_nat_131072] and
   [bsb_bound] in Common/StepTac.v (both imported above). *)

(* ######################################################################### *)
(* brk resolution-set algebra (parametric in the total byte count t)         *)
(* ######################################################################### *)

(* growable, T1, T2, brk_r_ok_query_iff, T1_iff_T2,
   T2_fail_iff, T2_succ_iff now live in Common/AllocSim, parameterized
   directly over the outcome buffers list ([bufs : list (list byte)]); this
   example's payload is the single buffer [jout av], so every call
   site instantiates AllocSim's [bufs] with [[jout av]]. *)

(** The first brk node: brk(0) is DETERMINISTIC — it reports the
    quantified ASLR base [b] — so the resolution set is the singleton
    {b} and the branch outcome set is [T1] AT [b].  [growable] at [b]
    (from [Run.valid_brk]'s window bounds) makes both outcomes live. *)
Lemma twoU_iff_T1 : forall reserved (lim top : Z) (t : word) (wbuf : list byte)
    (b : word) (P : word -> Prop),
  (forall r, P r <-> r = b) ->
  growable reserved lim top t b -> t <> Z_to_bv 64 0 ->
  forall o, two_outcomes [] (Z_to_bv 64 4) [wbuf] (Z_to_bv 64 0) o <->
    (exists r, P r /\ T1 reserved lim top t [wbuf] r o).
Proof.
  intros reserved lim top t wbuf b P HP Hg Ht o.
  split.
  - intros [-> | ->]; exists b; (split; [apply HP; reflexivity|]).
    + left. split; [reflexivity | right; right; exact Ht].
    + right. split; [exact Hg | reflexivity].
  - intros (r & _ & [[Ho _] | [_ Ho]]); [left | right]; exact Ho.
Qed.

(** A region entirely above every reservation is free. *)
Lemma region_free_above : forall (l : list (word * word)) (lo n : word),
  Forall (fun p => (bv_unsigned (fst p) + bv_unsigned (snd p)
                    <= bv_unsigned lo)%Z) l ->
  region_free l lo n = true.
Proof.
  induction l as [|[a sz] l IH]; intros lo n Hf; [reflexivity|].
  inversion Hf as [|? ? Ha Hl]; subst. cbn [fst snd] in Ha.
  cbn [region_free]. unfold iv_overlap.
  assert (E : (bv_unsigned lo <? bv_unsigned a + bv_unsigned sz)%Z = false)
    by (apply Z.ltb_ge; lia).
  rewrite E. cbn [andb negb]. apply IH. exact Hl.
Qed.

(** A region entirely below every reservation is free. *)
Lemma region_free_below : forall (l : list (word * word)) (lo n : word),
  Forall (fun p => (bv_unsigned lo + bv_unsigned n
                    <= bv_unsigned (fst p))%Z) l ->
  region_free l lo n = true.
Proof.
  induction l as [|[a sz] l IH]; intros lo n Hf; [reflexivity|].
  inversion Hf as [|? ? Ha Hl]; subst. cbn [fst snd] in Ha.
  cbn [region_free]. unfold iv_overlap.
  assert (E : (bv_unsigned a <? bv_unsigned lo + bv_unsigned n)%Z = false)
    by (apply Z.ltb_ge; lia).
  rewrite E, andb_false_r. cbn [negb andb]. apply IH. exact Hl.
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
(* page_round_up bounds                                                      *)
(* ######################################################################### *)

Lemma pru_Z_bounds : forall n : Z, (0 <= n)%Z ->
  (n <= page_round_up_Z n)%Z /\ (page_round_up_Z n <= n + 4095)%Z.
Proof.
  intros n Hn. unfold page_round_up_Z, page_size.
  replace (n + 4096 - 1)%Z with (n + 4095)%Z by lia.
  pose proof (Z.div_mod (n + 4095) 4096 ltac:(lia)) as H.
  pose proof (Z.mod_pos_bound (n + 4095) 4096 ltac:(lia)) as Hm.
  set (q := ((n + 4095) / 4096)%Z) in *.
  set (m := ((n + 4095) mod 4096)%Z) in *.
  split; lia.
Qed.

(** [bv_unsigned] of the word-level page round-up, for small lengths. *)
Lemma pru_u : forall w : word, (bv_unsigned w <= 2097152)%Z ->
  bv_unsigned (page_round_up w) = page_round_up_Z (bv_unsigned w).
Proof.
  intros w Hw. unfold MmapSim.page_round_up.
  pose proof (u64_range w).
  destruct (pru_Z_bounds (bv_unsigned w) ltac:(lia)) as [H1 H2].
  apply u_Z2bv; lia.
Qed.

(* ######################################################################### *)
(* argv helpers                                                              *)
(* ######################################################################### *)

(* byte_at, byte_at_bound/nz/len, and valid_argv_len/str_len/str_nz/str_bytes
   now live in CatExec. *)

Lemma valid_argv_tab : forall av, valid_argv av ->
  (total_arg_bytes_nat av <= 2097152)%nat.
Proof.
  intros av [_ [Htot _]]. rewrite total_arg_bytes_Z in Htot.
  apply Nat2Z.inj_le. rewrite of_nat_2097152. exact Htot.
Qed.

(* ######################################################################### *)
(* Value-shape facts                                                          *)
(* ######################################################################### *)

(** [v_add]/[v_sub] agree with the wrapping [bv] operators
    (hypothesis-free: both sides wrap identically). *)
Lemma v_add_word : forall x y : word, v_add x y = x + y.
Proof.
  intros x y. apply bv_eq. unfold v_add.
  rewrite Z_to_bv_unsigned, bv_add_unsigned. reflexivity.
Qed.

Lemma v_sub_word : forall x y : word, v_sub x y = x - y.
Proof.
  intros x y. apply bv_eq. unfold v_sub.
  rewrite Z_to_bv_unsigned, bv_sub_unsigned. reflexivity.
Qed.

Lemma word_add_comm : forall x y : word, x + y = y + x.
Proof.
  intros x y. apply bv_eq. rewrite !bv_add_unsigned. f_equal. lia.
Qed.

(** Unsigned value of a wrapping [v_add] (single wraparound).
    NOTE: this is the [bv_unsigned]-level variant of StepTac's
    [v_add_wrap] (which equates the [v_add] value to a [Z_to_bv]);
    kept here under a non-shadowing name. *)
Lemma v_add_wrap_u : forall x y : word,
  (2^64 <= bv_unsigned x + bv_unsigned y)%Z ->
  bv_unsigned (v_add x y) = (bv_unsigned x + bv_unsigned y - 2^64)%Z.
Proof.
  intros x y Hw. unfold v_add.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  pose proof (u64_range x). pose proof (u64_range y).
  replace (bv_unsigned x + bv_unsigned y)%Z
    with ((bv_unsigned x + bv_unsigned y - 2^64) + 1 * 2^64)%Z at 1 by lia.
  rewrite Z_mod_plus_full.
  apply Z.mod_small. lia.
Qed.

(** Signed-vs-2 comparison for the [sltiu ., ., 2] separator test. *)
Lemma v_sltiu_2 : forall x : word,
  v_sltiu x 2 = (if (bv_unsigned x <? 2)%Z then Z_to_bv 64 1 else Z_to_bv 64 0).
Proof.
  intro x. unfold v_sltiu.
  change (bv_wrap 64 2) with 2%Z. reflexivity.
Qed.

Lemma v_xori_1_1 : v_xori (Z_to_bv 64 1) 1 = Z_to_bv 64 0.
Proof. bveq. Qed.

Lemma v_xori_0_1 : v_xori (Z_to_bv 64 0) 1 = Z_to_bv 64 1.
Proof. bveq. Qed.

(** Signed comparison as a [Z] test on small operands ([c_lts_small]
    composed with the definitional [bv_ltu]-is-[Z.ltb]). *)
Lemma c_lts_ltb : forall x y : word,
  (bv_unsigned x < 2^63)%Z -> (bv_unsigned y < 2^63)%Z ->
  c_lts x y = (bv_unsigned x <? bv_unsigned y)%Z.
Proof.
  intros x y Hx Hy. rewrite c_lts_small by assumption. reflexivity.
Qed.

(* ######################################################################### *)
(* Byte store (sb) with an arbitrary byte value                              *)
(* ######################################################################### *)

(** Store byte, address and BYTE value pre-normalized: the register
    holds the zero-extension of the byte [b] (an [lbu] writeback).
    [step_sb256]-era value hypotheses are typed away; this is
    [MmapSim.step_sb_at] with the low-byte equation discharged.  Generic
    in the FP state ([MmapSim]'s machine states are). *)
Section StepSbAtv.
Context {fx : FPState}.

Lemma step_sb_atv : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12)
                           (a : word) (b : byte),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = Z_to_bv 64 (bv_unsigned b) ->
  RiscvSemantics.store_ok segs mem a 1%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) (wbytes mem a [b]) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm a b Hf He Hd Ha Hv Hok.
  apply (step_sb_at segs regs pc mem rom w rs1 rs2 imm a
           (Z_to_bv 64 (bv_unsigned b)) b Hf He Hd Ha Hv); [|exact Hok].
  rewrite u_zext8. apply bv_eq.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  pose proof (u8_range b). change (bv_modulus 8) with 256%Z. lia.
Qed.

End StepSbAtv.

(* ######################################################################### *)
(* Step-chaining tactics                                                      *)
(* ######################################################################### *)

(* [norm_pc]/[chain_step]/[stepi]/[stepj]/[sp_norm]/[stepi_at] and the
   [v_addi_m16]/[v_addi_m48]/[v_addi_m64]/[v_addi_m1] literal instances
   now live in Common/StepTac.v (imported above), in the canonical
   [Z_to_bv 64 (...)] form. *)

(* ######################################################################### *)
(* musl strlen support                                                       *)
(*                                                                           *)
(* gcc 15 no longer inlines the C [slen] loop: it recognizes it and emits a  *)
(* call to musl strlen, which scans 8 bytes at a time with the classic       *)
(* has-zero test.  The [Z]-level correctness of that test (module [HZ]), the *)
(* value/byte bridges ([v_haszero]/[zb_of_bytes]/[bytes_le_to_Z_range]), and *)
(* the fact that an 8-byte load inside an argv string never faults           *)
(* ([bsb_len_lower]/[read_word_stack]/[argv_word_readable]) live in          *)
(* Common/MuslStrlen.v (imported above).  The per-instruction walk over the  *)
(* routine stays in [alloc_join_ns_source.v], pinned to this binary's        *)
(* addresses.                                                                *)
(* ######################################################################### *)

