(** * arena-tee-ns: the specification, as a shape.

    PROOF-SIDE FILE (not part of the trusted specification).

    Both binaries drain stdin into a 4088-byte arena obtained from a
    single anonymous [mmap], then write, ON CHANNEL 2, eight lowercase
    hex digits holding the drained byte count followed by the drained
    bytes themselves, and exit 0.  A failed [mmap] exits 1 with no
    output.

    The observable behavior is therefore a two-element outcome set, which
    is exactly the shape [DrainAlg.rz_mmap_drain] concludes with:

      mmap failed    ->  no output, [ExitEv 1]
      mmap succeeded ->  [ReadEv 0] for each of the first 4088 bytes of
                         stdin, then [WriteEv 2] for each byte of
                         [arena_out (firstn 4088 stdin)], then [ExitEv 0]

    Note what does NOT appear: the chunking.  A read delivers one
    [ReadEv] per byte, so how the bytes were split across [read] calls is
    invisible in the trace, and [DrainAlg.t_drain_collapse] turns the
    whole nondeterministic loop into that single deterministic block.
    This is what lets the two binaries chunk differently — the source
    asks for [cap - len] each time, the target likewise, but neither the
    proof nor the spec depends on the kernel's answer — and still realize
    the same [TSet].

    In-model neither error path of either binary is reachable: [read] on
    an [FdChannel 0] returns 0 or a positive count and never an error
    ([ReadWrite.read_spec]), and [write] on a channel only yields [-EFAULT]
    when nothing at the buffer is readable ([ReadWrite.write_spec]), which a
    mapped grant rules out.  So the C's exit-2 and exit-3 branches, and
    the Zig's, are dead — as are the equivalent branches in the already
    proven [cat1024_ns]. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ShapeAlg DrainAlg MmapSim WallSim StepTac PropExec CatExec CatSim AllocSim.

Import ListNotations.
Open Scope bv_scope.

(** Every state the lemmas below build is a process-entry state
    ([init_mkst]'s right side is [@mkst fx0 ...]): [fx0] is the instance. *)
#[local] Existing Instance fx0.

(** The arena is one page and the header is eight bytes, so the drain
    capacity is [4096 - 8].  Kept as a [nat] because [DrainAlg]'s [cap]
    is a [nat]. *)
Definition cap : nat := 4088%nat.

Lemma Hcap_lt : (Z.of_nat cap < 2 ^ 64)%Z.
Proof. unfold cap. lia. Qed.

(** Every [read] the drain loop issues asks for [cap - |acc|] bytes, so
    one page is an upper bound on all of them and the model evaluates
    each one ([Uaccess.rw_bytes_max] is 131072). *)
Lemma Hcap_mod : (Z.of_nat cap <= rw_bytes_max)%Z.
Proof. unfold cap, rw_bytes_max. lia. Qed.

(** ** The header

    Eight lowercase hex digits, most significant nibble first, of the
    low 32 bits of [n].  Both binaries compute exactly this: the source
    packs four digits at a time into a word and stores two words, the
    target stores eight bytes one at a time.  Only the resulting bytes
    matter here. *)

Definition hex_digit (v : nat) : byte :=
  if (v <? 10)%nat then Z_to_bv 8 (Z.of_nat (48 + v))
  else Z_to_bv 8 (Z.of_nat (87 + v)).

Definition nib (n : nat) (k : nat) : nat := (n / (16 ^ k)) mod 16.

Definition hdr8 (n : nat) : list byte :=
  [hex_digit (nib n 7); hex_digit (nib n 6);
   hex_digit (nib n 5); hex_digit (nib n 4);
   hex_digit (nib n 3); hex_digit (nib n 2);
   hex_digit (nib n 1); hex_digit (nib n 0)].

Lemma hdr8_length : forall n, length (hdr8 n) = 8%nat.
Proof. reflexivity. Qed.

(** The single buffer the successful run writes: the header for however
    many bytes were drained, followed by those bytes. *)
Definition arena_out (bs : list byte) : list byte := hdr8 (length bs) ++ bs.

Lemma arena_out_length : forall bs,
  length (arena_out bs) = (8 + length bs)%nat.
Proof. intro bs. unfold arena_out. rewrite length_app, hdr8_length. reflexivity. Qed.

(** The one buffer a successful run writes is the eight-byte header plus
    at most [cap] drained bytes — one page — so the model evaluates the
    [write] that emits it. *)
Lemma arena_out_modeled : forall bs, (length bs <= cap)%nat ->
  bufs_modeled [arena_out bs].
Proof.
  intros bs H. constructor; [| constructor].
  unfold buf_modeled. rewrite arena_out_length.
  unfold cap in *. unfold rw_bytes_max. lia.
Qed.

(** ** The shape

    The output channel is 2, not 1, which is why this needs
    [ShapeAlg.t_writes_ch] rather than [t_writes]. *)

Definition ch2 : word := Z_to_bv 64 2.
Definition ch0 : word := Z_to_bv 64 0.

(** The tail: one write of [arena_out bs] on channel 2, then exit 0. *)
Definition arena_tail (fs0 : Fs.Fs) (bs : list byte) : TSet :=
  t_writes_ch ch2 [arena_out bs] (t_exit (Z_to_bv 64 0) fs0).

(** The failure tail: no output at all, exit 1. *)
Definition arena_fail (fs0 : Fs.Fs) : TSet :=
  t_writes [] (t_exit (Z_to_bv 64 1) fs0).

(** The whole behavior, as [rz_mmap_drain] delivers it. *)
Definition arena_outcomes (fs0 : Fs.Fs) (stdin0 : InputStream) : TSet :=
  t_alt2 (arena_fail fs0)
         (t_drain cap (arena_tail fs0) cap stdin0 []).

(** The collapsed form, which is what the spec actually says: the
    chunking is gone and the tail is a function of the input. *)
Definition arena_spec (fs0 : Fs.Fs) (stdin0 : InputStream) : TSet :=
  t_alt2 (arena_fail fs0)
         (t_emit (map (ReadEv ch0) (stream_firstn stdin0 cap))
                 (arena_tail fs0 (stream_firstn stdin0 cap))).

(** The tail shape contains the empty trace — automatic for anything a
    binary realizes ([ShapeAlg.realizes_nonempty]), but [t_drain]'s
    collapse wants it as a fact about [TSet]s alone. *)
Lemma arena_tail_ne : forall fs0 acc, arena_tail fs0 acc [].
Proof.
  intros fs0 acc. unfold arena_tail. rewrite t_writes_ch_cons.
  unfold t_emit. left. exact I.
Qed.

Lemma arena_outcomes_spec : forall fs0 stdin0,
  t_eq (arena_outcomes fs0 stdin0) (arena_spec fs0 stdin0).
Proof.
  intros fs0 stdin0. unfold arena_outcomes, arena_spec.
  apply t_alt2_cong; [apply t_eq_refl|].
  exact (t_drain_top_collapse cap Hcap_lt (fun _ _ => True)
           (arena_tail fs0) (arena_tail_ne fs0) stdin0).
Qed.

(* ######################################################################### *)
(* The write-all retry node, on channel 2                                    *)
(*                                                                           *)
(* Both binaries emit their single buffer through a put-style RETRY loop, so *)
(* the trace contribution of the emit is the WHOLE buffer however the        *)
(* environment chunks the delivery: the shape is [t_writes_ch], not the      *)
(* per-delivery [t_writes_ch_pick] that a single ret-oblivious write node    *)
(* ([CatSim.to_wexit_ch]) realizes.  [ShapeAlg.rz_wall1_mut]/[wall_realizes] *)
(* prove exactly that collapse, but pinned to fd/channel 1.  This example    *)
(* writes on channel 2, so the same two proofs are replayed here over the    *)
(* channel-parametric node lemma [ShapeAlg.node_write_ch]; the fd-1          *)
(* development in [ShapeAlg] is the (1,1) instance of what follows.          *)
(*                                                                           *)
(* THE REPLAY IS A DUPLICATION, AND IT IS DELIBERATE ONLY FOR NOW.  The two  *)
(* pairs differ by exactly four substitutions: [fd1chan] vs [fdchan fd ch]   *)
(* (which adds [w_is0 ch = false]), the extra [fd32 fd = fd] hypothesis,     *)
(* [node_write1] vs [node_write_ch], and [t_writes_cons] vs                  *)
(* [t_writes_ch_cons].  Nothing else differs — same four bullets, same       *)
(* tactics, same order.  The fd-1 pair IS derivable from this one: neither   *)
(* is an inductive, the one mutual induction they share                      *)
(* ([WallSim.to_wall]/[to_wall_tail], [Combined Scheme to_wall_mutind]) is   *)
(* already parametric in [fd], both side conditions exist as                 *)
(* [CatSim.fd1chan_fdchan] and [WallSim.fd32_1], and [t_writes] is           *)
(* DEFINITIONALLY [t_writes_ch] at channel 1 — so [wall_realizes]'s proof    *)
(* collapses to a single [exact].  Doing it means moving this pair up into   *)
(* [Common/ShapeAlg.v] (where a third channel-2 binary could reach it, which *)
(* it cannot here) and moving [ShapeAlg.node_write_ch] above the wall        *)
(* lemmas.  Net about -64 lines, with no statement change and no example     *)
(* proof script touched.                                                     *)
(*                                                                           *)
(* It is NOT done on this branch because the move lands on exactly the lines *)
(* PR #242 ("Bound the transfer size read and write will judge") is editing: *)
(* #242 rewrites [node_write_ch] in place and touches [ShapeAlg.v],          *)
(* [CatSim.v] and this file among its 50, and relocating [node_write_ch]     *)
(* underneath it would turn a clean merge into a hand repair for no          *)
(* semantic gain.  So: after #242 merges, on main, as its own change.  Note  *)
(* that [ShapeAlg] carries the same fd-1/parametric split for the NODE       *)
(* lemmas ([node_write1]/[rz_write1] vs [node_write_ch]/[rz_write_ch]) and   *)
(* in [twm_realizes_mut]; parametrizing those is a bigger job than the wall  *)
(* pair and should not be folded into it.                                    *)
(* ######################################################################### *)

Lemma rz_wall_ch_mut : forall segs (fd ch : word) model,
  m_halted model = None -> m_vm_lazy model = [] ->
  fdchan fd ch model -> fd32 fd = fd ->
  (forall ms rest k, to_wall segs fd ms rest k ->
     buf_modeled rest ->
     forall T : TSet, T [] ->
     (forall ms', k ms' -> realizes segs (mkCfg ms' model) T) ->
     realizes segs (mkCfg ms model) (t_emit (map (WriteEv ch) rest) T))
  /\ (forall ms rest k, to_wall_tail segs fd ms rest k ->
     buf_modeled rest ->
     forall T : TSet, T [] ->
     (forall ms', k ms' -> realizes segs (mkCfg ms' model) T) ->
     realizes segs (mkCfg ms model) (t_emit (map (WriteEv ch) rest) T)).
Proof.
  intros segs fd ch model Hh Hlazy Hfd H32.
  apply (to_wall_mutind segs fd
    (fun ms rest k => buf_modeled rest -> forall T : TSet, T [] ->
       (forall ms', k ms' -> realizes segs (mkCfg ms' model) T) ->
       realizes segs (mkCfg ms model) (t_emit (map (WriteEv ch) rest) T))
    (fun ms rest k => buf_modeled rest -> forall T : TSet, T [] ->
       (forall ms', k ms' -> realizes segs (mkCfg ms' model) T) ->
       realizes segs (mkCfg ms model) (t_emit (map (WriteEv ch) rest) T))).
  - (* twl_write *)
    intros ms x8 rest k Hsvc Hno Hg Hr Hok Hnb Hcont IH Hbm T HT Hk.
    eapply rz_conseq.
    { apply (rz_node segs (mkCfg ms model) (wr_index rest)
        (fun i => map (WriteEv ch) (firstn (proj1_sig i) rest))
        (fun i => mkCfg (advance_past_svc
                           (set_gpr0 ms (len_word (firstn (proj1_sig i) rest))))
                        model)
        (fun i => t_emit (map (WriteEv ch)
                              (skipn (proj1_sig i) rest)) T)
        (wr_full rest Hnb)).
      - apply (node_write_ch segs ms model fd ch x8 rest); assumption.
      - intros [n [Hn1 Hn2]]. cbn [proj1_sig].
        apply (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) T HT Hk). }
    apply t_alt_wall; [exact HT | exact Hnb].
  - (* twt_done *)
    intros ms k Hk Hbm T HT Hcont.
    eapply rz_conseq; [apply Hcont; exact Hk|].
    cbn [map]. apply t_eq_sym. apply t_emit_nil_eq. exact HT.
  - (* twt_more *)
    intros ms rest k Hnb Hw IH Hbm T HT Hk. exact (IH Hbm T HT Hk).
  - (* twt_step *)
    intros ms ms' rest k Hsvc Hstep Ht IH Hbm T HT Hk.
    eapply rz_step;
      [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
      | exact (IH Hbm T HT Hk)].
Qed.

(** The channel-parametric [ShapeAlg.wall_realizes]: a retry-loop
    exit-after-writes run realizes the FULL-DELIVERY shape [t_writes_ch]. *)
Lemma wall_realizes_ch : forall segs (fd ch : word) ms model bufs code,
  m_halted model = None -> m_vm_lazy model = [] ->
  fdchan fd ch model -> fd32 fd = fd ->
  to_wallexit segs fd bufs code ms ->
  bufs_modeled bufs ->
  realizes segs (mkCfg ms model)
    (t_writes_ch ch bufs (t_exit code (m_fs model))).
Proof.
  intros segs fd ch ms model bufs code Hh Hlazy Hfd H32 Hw Hbm.
  revert ms Hw Hbm.
  induction bufs as [|buf rest IH]; intros ms Hw Hbm.
  - exact (exitline_realizes segs ms code model Hw Hh Hlazy).
  - destruct Hw as [Hnb Ht]. apply Forall_cons_iff in Hbm as [Hb Hbs].
    rewrite t_writes_ch_cons.
    eapply (proj2 (rz_wall_ch_mut segs fd ch model Hh Hlazy Hfd H32)).
    + exact Ht.
    + exact Hb.
    + apply t_writes_ch_exit_has_nil.
    + intros ms' Hk. apply IH; [exact Hk | exact Hbs].
Qed.

(* ######################################################################### *)
(* Misc numeric facts                                                        *)
(* ######################################################################### *)

Lemma page_round_up_Z_4096 : page_round_up_Z 4096 = 4096%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma pru_4096 : MmapSim.page_round_up (Z_to_bv 64 4096) = Z_to_bv 64 4096.
Proof. bveq. Qed.

(* ######################################################################### *)
(* Digit values, machine-side                                                *)
(*                                                                           *)
(* Both binaries compute a hex digit as [((n >> 4k) & 15) + (48 | 87)]; the  *)
(* lemmas here relate that machine arithmetic to [nib]/[hex_digit].          *)
(* ######################################################################### *)

Lemma nib_lt16 : forall n k, (nib n k < 16)%nat.
Proof. intros n k. unfold nib. apply Nat.mod_upper_bound. lia. Qed.

(** The digit's ASCII code, as a [Z]. *)
Definition digZ (n k : nat) : Z :=
  if (nib n k <? 10)%nat then (48 + Z.of_nat (nib n k))%Z
  else (87 + Z.of_nat (nib n k))%Z.

Lemma digZ_range : forall n k, (48 <= digZ n k < 103)%Z.
Proof.
  intros n k. unfold digZ. pose proof (nib_lt16 n k).
  destruct (Nat.ltb_spec (nib n k) 10); lia.
Qed.

Lemma hex_digit_digZ : forall n k, hex_digit (nib n k) = Z_to_bv 8 (digZ n k).
Proof.
  intros n k. unfold hex_digit, digZ.
  destruct (nib n k <? 10)%nat; f_equal; lia.
Qed.

(** The low byte of the 64-bit digit value IS the header byte. *)
Lemma digb : forall n k,
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (digZ n k))) = hex_digit (nib n k).
Proof.
  intros n k. pose proof (digZ_range n k).
  rewrite u_Z2bv by lia. rewrite hex_digit_digZ. reflexivity.
Qed.

Lemma nib_Z : forall n k,
  Z.of_nat (nib n k) = ((Z.of_nat n / 2 ^ (4 * Z.of_nat k)) mod 16)%Z.
Proof.
  intros n k. unfold nib.
  rewrite Nat2Z.inj_mod, Nat2Z.inj_div, Nat2Z.inj_pow.
  change (Z.of_nat 16) with 16%Z.
  replace (16 ^ Z.of_nat k)%Z with (2 ^ (4 * Z.of_nat k))%Z; [reflexivity|].
  replace 16%Z with (2 ^ 4)%Z at 1 by reflexivity.
  rewrite <- Z.pow_mul_r by lia. reflexivity.
Qed.

(** The machine's [(n >> s) & 15] IS the nibble, for [s = 4k]. *)
Lemma dig_val : forall (n k : nat) (s : Z),
  (n <= cap)%nat -> (k <= 7)%nat -> s = (4 * Z.of_nat k)%Z ->
  v_andi (v_srl (nat_to_word n) (Z_to_bv 64 s)) 15
  = Z_to_bv 64 (Z.of_nat (nib n k)).
Proof.
  intros n k s Hn Hk ->.
  unfold v_srl, v_andi.
  rewrite (u_Z2bv (4 * Z.of_nat k)) by lia.
  rewrite (Z.mod_small (4 * Z.of_nat k) 64) by lia.
  rewrite u_ntw by (unfold cap in *; lia).
  rewrite Z.shiftr_div_pow2 by lia.
  assert (Hp : (0 < 2 ^ (4 * Z.of_nat k))%Z) by (apply Z.pow_pos_nonneg; lia).
  assert (Hq0 : (0 <= Z.of_nat n / 2 ^ (4 * Z.of_nat k))%Z)
    by (apply Z.div_pos; lia).
  assert (Hqh : (Z.of_nat n / 2 ^ (4 * Z.of_nat k) <= Z.of_nat n)%Z)
    by (apply Z.div_le_upper_bound; nia).
  rewrite u_Z2bv by (unfold cap in *; lia).
  change (bv_wrap 64 15) with (Z.ones 4).
  rewrite Z.land_ones by lia.
  change (2 ^ 4)%Z with 16%Z.
  f_equal. symmetry. apply nib_Z.
Qed.

Lemma hdr8_nth : forall n i (d : byte), (i < 8)%nat ->
  nth i (hdr8 n) d = hex_digit (nib n (7 - i)).
Proof.
  intros n i d Hi. unfold hdr8.
  do 8 (destruct i as [|i]; [reflexivity|]). lia.
Qed.

(* ######################################################################### *)
(* Collapsing the two syscall post-states both binaries dispatch from        *)
(* ######################################################################### *)

(** Collapse [advance_past_svc (apply_effect <record> (mkEffect a [] [(a,n)]))]
    — the state an [mmap] grant dispatches from — to a [mkst] over the
    zero-filled overlay.  The [set_gpr0] counterpart is
    [CatExec.adv_set]; this is the same collapse with the effect's
    single zero range folded into [MmapSim.zfill].  Both collapses hold at
    any FP state. *)
Section AdvFx.
Context {fx : FPState}.

Lemma adv_apply : forall regs pc sv mem rom (a n : word),
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := @fp_regs fx; ms_pc_val := pc;
       ms_svc_pending := sv; ms_resv := None; ms_fcsr := @fp_csr fx;
       ms_mem := mem; ms_rom := rom |}
    (mkEffect a [] [(a, n)]))
  = @mkst fx (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom.
Proof.
  intros regs pc sv mem rom a n.
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies
       apply_writes apply_unmaps apply_copies].
  unfold mkst, regupd, zfill.
  rewrite apply_zeros_one, b_npc4. reflexivity.
Qed.

(** The same collapse for a [read]'s delivered block: one write range,
    no zero ranges. *)
Lemma adv_write : forall regs pc sv mem rom (v buf : word) bs,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := @fp_regs fx; ms_pc_val := pc;
       ms_svc_pending := sv; ms_resv := None; ms_fcsr := @fp_csr fx;
       ms_mem := mem; ms_rom := rom |}
    (mkEffect v [(buf, bs)] []))
  = @mkst fx (regupd regs 10 v) (v_addi pc 4) (write_to_mem mem buf bs) rom.
Proof.
  intros regs pc sv mem rom v buf bs.
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies
       apply_writes apply_unmaps apply_copies
       apply_zeros].
  unfold mkst, regupd. rewrite b_npc4. reflexivity.
Qed.

End AdvFx.
