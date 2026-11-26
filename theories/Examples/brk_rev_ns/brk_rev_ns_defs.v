(** * brk-rev-ns: shared definitions and helper lemmas.

    PROOF-SIDE FILE (not part of the trusted specification).

    The shared observable-behavior spec of both binaries:
    - argc < 2                      : no output, exit 2
    - n = strlen(argv[1]) > 65536   : no output, exit 3
    - otherwise                     : the outcome SET
        { ([], 4) } ∪ { ([rev_buf argv[1]], 0) }
      (brk resolutions: any failing resolution exits 4 silently; any
      succeeding resolution writes the reversed string + '\n' and exits 0;
      both kinds of resolution always exist).

    This file: the outcome-set definitions and the resolution-set algebra
    shared by the two per-binary proofs, plus argv/byte helpers, the
    byte-store step lemma for arbitrary register byte values, and word
    bridges for the down-counting loops.

    Conventions: bytes are [byte = bv 8],
    machine values [word = bv 64]; unbounded bookkeeping is in [Z] over
    [bv_unsigned]; computed stack addresses use the canonical
    [Z_to_bv 64 (...)] form; loop indices/counters use [nat_to_word]. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec AllocSim StepTac StreamSim StoreOk.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.

Import ListNotations.
Open Scope bv_scope.

(** Every state in this file is reached from process entry, where the FP
    register file is empty and [fcsr] is zero ([PropExec.fx0]). *)
#[local] Instance brk_rev_ns_defs_fx : FPState := fx0.

(* ######################################################################### *)
(* The shared observable-behavior spec                                       *)
(* ######################################################################### *)

(** The single written buffer on a successful run: argv[1] reversed,
    then a newline. *)
Definition rev_buf (s : list byte) : list byte := rev s ++ [Z_to_bv 8 10].

(** The shared outcome set for the main (argc >= 2, n <= 65536) case. *)
Definition brkU (wbuf : list byte) : (list (list byte) * word) -> Prop :=
  fun o => o = ([], Z_to_bv 64 4) \/ o = ([wbuf], Z_to_bv 64 0).

(* growable, T1, T2, brk_r_ok_query_iff, T1_iff_T2,
   T2_fail_iff, T2_succ_iff now live in Common/AllocSim, parameterized
   directly over the grow amount and the outcome buffers list.  This
   example's grow amount is [n + 1] (reversed argv[1] plus a newline) and
   its payload is the single buffer [rev_buf s]. *)

(* ------------------------------------------------------------------------- *)
(* Small word/byte bridges                                                    *)
(* ------------------------------------------------------------------------- *)

(** Close a CLOSED word/byte equation by unsigned comparison. *)



(** [bv_unsigned] of a byte zero-extended into a word. *)

(** Truncating the zero-extended byte back to 8 bits recovers it. *)


(** Loop-index steps over a symbolic base (both sides wrap). *)
Lemma nat_to_word_S : forall m : nat,
  v_addi (nat_to_word m) 1 = nat_to_word (S m).
Proof.
  intro m. unfold v_addi, nat_to_word. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma word_add_nat_1 : forall (a : word) (m : nat),
  v_addi (a + nat_to_word m) 1 = a + nat_to_word (S m).
Proof.
  intros a m. rewrite !word_add_nat. unfold v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma word_add_nat_m1 : forall (a : word) (m : nat),
  v_addi (a + nat_to_word (S m)) (-1) = a + nat_to_word m.
Proof.
  intros a m. rewrite !word_add_nat. unfold v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

(** [v_add] is commutative up to the wrap. *)
Lemma v_add_comm : forall x y : word, v_add x y = y + x.
Proof.
  intros x y. apply bv_eq.
  change (v_add x y) with (x + y).
  rewrite !bv_add_unsigned. f_equal. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* Set algebra: the resolution-set identities used at the two brk nodes.      *)
(* ------------------------------------------------------------------------- *)

(** The first brk node: brk(0) is DETERMINISTIC — it reports the
    quantified ASLR base [b] ([Run.mi_init_brk], established at execve) —
    so the resolution set is the singleton {b}, and the branch outcome
    set is [T1] AT [b].  [growable] at [b] (from [Run.valid_brk]'s window
    bounds) makes both outcomes live: the second brk's failure resolution
    exits 4, its success resolution writes and exits 0. *)
Lemma brkU_iff_T1 : forall reserved (lim top : Z) (n : word) (wbuf : list byte)
    (b : word) (P : word -> Prop),
  (forall r, P r <-> r = b) ->
  growable reserved lim top (n + 1) b ->
  n + 1 <> Z_to_bv 64 0 ->
  forall o, brkU wbuf o <->
    (exists r, P r /\ T1 reserved lim top (n + 1) [wbuf] r o).
Proof.
  intros reserved lim top n wbuf b P HP Hg Hn1 o.
  split.
  - intros [-> | ->]; exists b; (split; [apply HP; reflexivity|]).
    + left. split; [reflexivity | right; right; exact Hn1].
    + right. split; [exact Hg | reflexivity].
  - intros (r & _ & [[Ho _] | [_ Ho]]); [left | right]; exact Ho.
Qed.

(** The second brk node: T1 at a usable r = union over grow resolutions
    of T2 — restated with the example's [n + 1] grow amount, the "want"
    value spelled as the machine's [r + (n + 1)].  [r] is the established
    break with heap base [s <= r] (Linux [min_brk]), so [r + (n+1)] takes
    the grow path, not the invalid one. *)
Lemma T1_iff_T2 : forall reserved (lim : Z) (s mb sp n : word) wbuf (r : word),
  r <> Z_to_bv 64 0 ->
  (bv_unsigned s <= bv_unsigned r)%Z ->
  (bv_unsigned n + 1 < 2^64)%Z ->
  (bv_unsigned r + bv_unsigned n + 1 < 2^64)%Z ->
  forall o, T1 reserved lim (bv_unsigned sp - stack_max_size) (n + 1) wbuf r o <->
    (exists r2, brk_r_ok (mkVmMapsFull reserved [] [] s r lim mb sp) (r + (n + 1)) r2
                /\ T2 (r + (n + 1)) wbuf r2 o).
Proof.
  intros reserved lim s mb sp n wbuf r Hr0 Hs Hn1 Hnw o.
  assert (Hu : bv_unsigned (n + 1) = (bv_unsigned n + 1)%Z).
  { rewrite u_add_small; change (bv_unsigned (1 : word)) with 1%Z; lia. }
  apply AllocSim.T1_iff_T2; [exact Hr0 | exact Hs | rewrite Hu; lia].
Qed.

(* T2_fail_iff/T2_succ_iff are used unchanged from AllocSim (their `want`/
   `r2` parameters pass straight through). *)

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
(* argv helpers (as in the other examples)                                    *)
(* ######################################################################### *)

(* byte_at, byte_at_bound/nz/len, nth_lt_byte_at, and
   valid_argv_len/str_len/str_nz/str_bytes now live in CatExec. *)

(** Sealed [Z.of_nat] equation for [valid_envp]'s large literal
    (companion of CatExec's [of_nat_131071]/[of_nat_2097152]). *)

(* rev-list facts *)

Lemma length_rev_buf : forall s : list byte, length (rev_buf s) = S (length s).
Proof.
  intro s. unfold rev_buf. rewrite length_app, length_rev. cbn [length]. lia.
Qed.

Lemma nth_rev_lt : forall (s : list byte) i, (i < length s)%nat ->
  nth i (rev s) (Z_to_bv 8 0) = nth (length s - S i) s (Z_to_bv 8 0).
Proof.
  intros s i Hi. apply rev_nth. exact Hi.
Qed.

Lemma firstn_rev_snoc : forall (s : list byte) i, (i < length s)%nat ->
  firstn (S i) (rev s)
  = firstn i (rev s) ++ [nth (length s - S i) s (Z_to_bv 8 0)].
Proof.
  intros s i Hi.
  assert (Hi' : (i < length (rev s))%nat) by (rewrite length_rev; exact Hi).
  rewrite <- (firstn_skipn i (rev s)) at 1.
  rewrite (skipn_nth (rev s) i (Z_to_bv 8 0) Hi').
  rewrite <- nth_rev_lt by exact Hi.
  replace (S i) with (i + 1)%nat by lia.
  rewrite firstn_app.
  rewrite firstn_firstn.
  replace (Nat.min (i + 1) i) with i by lia.
  rewrite firstn_length_le by lia.
  replace (i + 1 - i)%nat with 1%nat by lia.
  cbn [firstn]. reflexivity.
Qed.

Lemma firstn_all_rev : forall (s : list byte),
  firstn (length s) (rev s) = rev s.
Proof.
  intro s. rewrite <- (length_rev s). apply firstn_all.
Qed.

(* ######################################################################### *)
(* Value-shape facts for the wrap analysis and the down-counting loops        *)
(* ######################################################################### *)

(** A wrapping [v_add], with the wrapped value made explicit. *)

(** [sub x0, y]: two's-complement negation in the canonical form. *)

(** Unsigned value of a small negation. *)

(** Incrementing a negative down-counter. *)

(* c_eq_neq/c_eq_refl now live in PropExec. *)


(* ######################################################################### *)
(* Byte store (sb) with an arbitrary register byte value                      *)
(* ######################################################################### *)

(** Store byte, address pre-normalized and the stored byte named;
    memory becomes a one-byte [wbytes], via the pre-normalization equation
    on the stored byte ([sb_chain256]/[step_sb256] live in [SeqExec]).
    Generic over the FP state: each per-binary file rewrites with it at
    its own instance. *)
Lemma step_sb_at : forall (fx : FPState) segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12)
                          (a : word) (b : byte),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Instr.Store Instr.SZ1 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  Z_to_bv 8 (bv_unsigned (getr regs rs2)) = b ->
  RiscvSemantics.store_ok segs mem a 1%nat = true ->
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst fx regs (v_addi pc 4) (wbytes mem a [b]) rom).
Proof.
  intros fx segs regs pc mem rom w rs1 rs2 imm a b Hf He Hd Ha Hb Hok.
  rewrite (@step_sb256 fx segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
  - rewrite Ha, N_to_le_bytes_1_small, Hb. reflexivity.
  - rewrite Ha. exact Hok.
Qed.
Arguments step_sb_at {fx}.

(* ######################################################################### *)
(* Step-chaining tactics (as in the other examples)                           *)
(* ######################################################################### *)

(* [norm_pc]/[stepi]/[stepiv]/[stepj]/[sp_norm]/[wlit]/[wlits] and the
   [v_addi_m16]/[v_addi_m64]/[v_addi_m1] literal instances now live in
   Common/StepTac.v (imported above). *)
