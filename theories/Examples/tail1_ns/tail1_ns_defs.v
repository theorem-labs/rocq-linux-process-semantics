(** * tail1-ns: shared helpers for the two per-binary drain proofs.

    PROOF-SIDE FILE (not part of the trusted specification).

    Both binaries implement tail-1: read all of stdin to EOF in 1024-byte
    chunks, folding each byte through the newline/append logic that tracks
    the current unterminated line [cur] and the last completed line [done]
    (with its trailing '\n'); at EOF write the last line (cur if nonempty,
    else done, else nothing) in one write and exit 0.  A line exceeding
    4096 bytes aborts with exit 3.

    This file fixes the shared abstract model ([A], [f], [out], [ec]) that
    both per-binary proofs fold onto, the image probes, memory read-back
    helpers, value facts, and the DrainSim record entry-point lemmas.

    Conventions: bytes are [byte = bv 8], machine values [word = bv 64];
    unbounded address bookkeeping is in [Z] over [bv_unsigned]; computed
    stack addresses use the canonical [Z_to_bv 64 (...)] form, pc values
    the numeral-literal form.

    A run reads [Run.run_segments]: the image's segments, then the vDSO
    pair.  The store bounds and the buffers' writability below are stated
    over [segs ++ vt] for any appended [vt] ([RunSegmentsLift]), and a
    write carries [access_okb] on its user buffer ([tout_wr_rec]). *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim WallSim StreamSim DrainSim StepTac StoreOk RunSegmentsLift.
From LinuxProcessSemantics.Examples.tail1_ns Require Import tail1_ns_code.
From LinuxProcessSemantics.Examples.tail1_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.tail1_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(** Every state in this file is reached from process entry, where the FP
    register file is empty and [fcsr] is zero ([PropExec.fx0]). *)
#[local] Instance tail1_ns_defs_fx : FPState := fx0.

(* ######################################################################### *)
(* The shared abstract model                                                 *)
(* ######################################################################### *)

(** Abstract fold state: [(cur, done)] — the current unterminated line and
    the last completed line (including its trailing '\n').  The concrete
    counters [cur_n]/[done_n] are the list lengths. *)
Definition A : Type := (list byte * list byte)%type.

(** Per-byte step.  A '\n' (=10) closes the current line into [done] and
    resets [cur]; otherwise a line already at 4096 bytes aborts ([None]),
    else the byte is appended to [cur]. *)
Definition f (a : A) (b : byte) : option A :=
  let (cur, done) := a in
  if bv_eqb b (Z_to_bv 8 10) then Some ([], cur ++ [Z_to_bv 8 10])
  else if (4096 <=? Z.of_nat (length cur))%Z then None
       else Some (cur ++ [b], done).

(** At EOF: emit [cur] if nonempty, else [done], else nothing. *)
Definition out (a : A) : list byte :=
  let (cur, done) := a in
  match cur with [] => done | _ => cur end.

(** The emitted line always fits in one modeled write
    ([CatSim.buf_modeled], far below [Uaccess.rw_bytes_max]).  Both cases
    are capped by the fold itself: [f] refuses a 4097th byte of [cur],
    and [done] is a closed line plus its '\n'.  Stated over the caps the
    per-binary invariants carry rather than over every abstract state, so
    [out] stays the plain projection it was. *)
Lemma out_modeled : forall cur done,
  (Z.of_nat (length cur) <= 4096)%Z ->
  (Z.of_nat (length done) <= 4097)%Z ->
  buf_modeled (out (cur, done)).
Proof.
  intros cur done Hc Hd. unfold buf_modeled, out, rw_bytes_max.
  destruct cur; lia.
Qed.

(** Line-too-long exit code. *)
Definition ec : word := Z_to_bv 64 3.

(** Initial abstract state: both buffers empty. *)
Definition a0 : A := ([], []).

Lemma ec_lt256 : (bv_unsigned ec < 256)%Z.
Proof. vm_compute. reflexivity. Qed.

(* ######################################################################### *)
(* Word/byte arithmetic bridges (local helpers; candidates for BvBase)       *)
(* ######################################################################### *)

(** Close a CLOSED word/byte equation by unsigned comparison. *)


(** The wrapping word/nat offset add in the canonical [Z_to_bv] form
    (hypothesis-free: both sides wrap identically). *)

Lemma word_to_nat_ntw : forall n : nat, (Z.of_nat n < 2^64)%Z ->
  word_to_nat (nat_to_word n) = n.
Proof. intros n Hn. unfold word_to_nat. rewrite u_ntw by lia. lia. Qed.

(** [bv_unsigned] of a byte zero-extended into a word. *)

(** The low byte of a zero-extended byte is the byte back (the store
    normal form after an [lbu]/[sb] round-trip). *)
Lemma byte_low_zext : forall b : byte,
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned b))) = b.
Proof.
  intro b. apply bv_eq. rewrite Z_to_bv_unsigned, u_zext8.
  apply bv_wrap_small. pose proof (u8_range b).
  change (bv_modulus 8) with 256%Z. lia.
Qed.

(** The machine's newline test on the zero-extended loaded byte IS the
    abstract byte-level test. *)
Lemma c_eq_zext10 : forall b : byte,
  c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 10) = bv_eqb b (Z_to_bv 8 10).
Proof.
  intro b. unfold c_eq, bv_eqb.
  rewrite u_zext8.
  change (bv_unsigned (Z_to_bv 64 10)) with 10%Z.
  change (bv_unsigned (Z_to_bv 8 10)) with 10%Z.
  reflexivity.
Qed.

Lemma bv_ltu_ltb : forall x y : word,
  bv_ltu x y = (bv_unsigned x <? bv_unsigned y)%Z.
Proof. exact c_ltu_ltb. Qed.

Lemma c_ltu_x0 : forall x : word, c_ltu x (Z_to_bv 64 0) = false.
Proof.
  intro x. rewrite c_ltu_ltb.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  apply Z.ltb_ge. pose proof (u64_range x). lia.
Qed.

(** Count comparisons over [nat_to_word] as Z comparisons. *)
Lemma c_eq_ntw : forall m n : nat,
  (Z.of_nat m < 2^64)%Z -> (Z.of_nat n < 2^64)%Z ->
  c_eq (nat_to_word m) (nat_to_word n) = (Z.of_nat m =? Z.of_nat n)%Z.
Proof. intros. unfold c_eq, bv_eqb. rewrite !u_ntw by lia. reflexivity. Qed.

Lemma c_lts_ntw : forall m n : nat,
  (Z.of_nat m < 2^63)%Z -> (Z.of_nat n < 2^63)%Z ->
  c_lts (nat_to_word m) (nat_to_word n) = (Z.of_nat m <? Z.of_nat n)%Z.
Proof.
  intros m n Hm Hn.
  rewrite c_lts_small by (rewrite u_ntw by lia; lia).
  rewrite bv_ltu_ltb, !u_ntw by lia. reflexivity.
Qed.

(* [c_eq_0_of_u] lives in Common/PropExec.v (imported above). *)

Lemma c_eq_sub_self : forall x : word, c_eq (v_sub x x) (Z_to_bv 64 0) = true.
Proof.
  intro x. apply c_eq_0_of_u. unfold v_sub.
  rewrite Z.sub_diag. reflexivity.
Qed.

(** Loop-counter decrement over [nat_to_word]. *)
Lemma v_addi_ntw_pred : forall n : nat, (0 < n)%nat -> (Z.of_nat n < 2^64)%Z ->
  v_addi (nat_to_word n) (-1) = nat_to_word (n - 1).
Proof.
  intros n Hn Hb. apply bv_eq. unfold v_addi.
  rewrite u_ntw by lia.
  unfold nat_to_word. rewrite !Z_to_bv_unsigned.
  f_equal. lia.
Qed.

(** Pointer increment: [addi p,p,1] advances a pointer-plus-index by
    one index step (hypothesis-free: both sides are the same wrap;
    same bridge as grep_args_ns's local [v_addi_ptr_S]). *)
Lemma v_addi_ptr_S : forall (p : word) (j : nat),
  v_addi (p + nat_to_word j) 1 = p + nat_to_word (S j).
Proof.
  intros p j.
  change (v_addi (p + nat_to_word j) 1)
    with (p + nat_to_word j + nat_to_word 1).
  rewrite nat_to_word_add_merge. do 2 f_equal. lia.
Qed.

(** [base + nat_to_word j] against the machine's [add rs_count rs_base]
    operand order ([v_add] with the count FIRST — the one reversed add in
    the source's copy loop). *)
Lemma word_add_nat_comm : forall (a : word) (n : nat), (Z.of_nat n < 2^64)%Z ->
  a + nat_to_word n = v_add (nat_to_word n) a.
Proof.
  intros a n Hn. rewrite word_add_nat. unfold v_add.
  rewrite u_ntw by lia. apply bv_eq. rewrite !Z_to_bv_unsigned.
  f_equal. lia.
Qed.

(** Sealed [Z.of_nat] equation for [valid_envp]'s large literal
    (companion of CatExec's [of_nat_131071]/[of_nat_2097152]). *)

(** Upper bound on the initial stack image (feeds every read lemma's
    no-overflow side condition; the numbers come from [valid_argv]/
    [valid_envp]). *)

(* ######################################################################### *)
(* Image probes                                                              *)
(* ######################################################################### *)

Lemma source_init_pc_val : SourceMemImage_init_pc = 0x11154%N.
Proof. vm_compute. reflexivity. Qed.

Lemma target_init_pc_val : TargetMemImage_init_pc = 0x1001190%N.
Proof. vm_compute. reflexivity. Qed.

(** Store targets at/above the end of the (page-rounded) source rodata
    segment avoid all read-only segments (the rw data segment is exempt).
    After the [-z separate-code] relink there are THREE read-only
    segments — r-- headers/.riscv.attributes [0x10000, 0x11000), r-x
    text [0x11000, 0x12000) and r-- .eh_frame [0x12000, 0x13000) — so
    the rw- data segment, and the first writable address, start at
    0x13000. *)
Lemma source_avoids_ro : forall (a : word) (n : Z), (0x13000 <= bv_unsigned a)%Z ->
  range_avoids_ro_segs source_segs (bv_unsigned a) n = true.
Proof.
  intros a n Ha.
  apply range_avoids_ro_above with (data_base := 0x13000%Z);
    [vm_compute; reflexivity | exact Ha].
Qed.

(** The source image's WRITABLE window: the rw- segment covers
    [0x13000, 0x16000) and the snapshot carries a byte for every address in
    it (.bss is zero-filled in the .hex), so [wview] is defined there
    whatever the overlay holds — a store into .data/.bss needs no
    prior write.  That is the [store_ok] side condition machine stores
    now carry; stack targets go through the RLIMIT_STACK window
    ([solve_store_ok]) instead. *)
Lemma source_data_wseg : wseg_ok source_segs (0x13000 : word) 12288 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma source_store_ok : forall vt (m : word -> option byte) (a : word) (n : nat),
  (0x13000 <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 0x16000)%Z ->
  store_ok (source_segs ++ vt) m a n = true.
Proof.
  intros vt m a n Hlo Hhi. apply store_ok_app.
  eapply store_ok_window with (base := 0x13000%Z) (hi := 0x16000%Z);
    [ | | | exact source_data_wseg | | ];
    [ vm_compute; reflexivity | vm_compute; reflexivity | lia
    | exact Hlo | exact Hhi ].
Qed.

(** Target: two read-only (page-rounded) segments ending at 0x1001000
    and 0x1002000. *)
Lemma target_avoids_ro : forall (a : word) (n : Z), (0x1002000 <= bv_unsigned a)%Z ->
  range_avoids_ro_segs target_segs (bv_unsigned a) n = true.
Proof.
  intros a n Ha.
  unfold target_segs, TargetMemImage_loaded_segments, range_avoids_ro_segs.
  cbn [forallb].
  change (seg_writable TargetMemImage_segment_002) with true.
  change (Z.of_N (seg_base TargetMemImage_segment_000)
          + Z.of_N (seg_size TargetMemImage_segment_000))%Z with 0x1001000%Z.
  change (Z.of_N (seg_base TargetMemImage_segment_001)
          + Z.of_N (seg_size TargetMemImage_segment_001))%Z with 0x1002000%Z.
  assert (H0 : Z.ltb (bv_unsigned a) 0x1001000 = false) by (apply Z.ltb_ge; lia).
  assert (H1 : Z.ltb (bv_unsigned a) 0x1002000 = false) by (apply Z.ltb_ge; lia).
  rewrite H0, H1. rewrite !andb_false_r.
  cbn [negb orb andb]. reflexivity.
Qed.

(** The target image's WRITABLE window: the rw- segment covers
    [0x1002000, 0x1005000) and the snapshot carries a byte for every address in
    it (.bss is zero-filled in the .hex), so [wview] is defined there
    whatever the overlay holds — a store into .data/.bss needs no
    prior write.  That is the [store_ok] side condition machine stores
    now carry; stack targets go through the RLIMIT_STACK window
    ([solve_store_ok]) instead. *)
Lemma target_data_wseg : wseg_ok target_segs (0x1002000 : word) 12288 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma target_store_ok : forall vt (m : word -> option byte) (a : word) (n : nat),
  (0x1002000 <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 0x1005000)%Z ->
  store_ok (target_segs ++ vt) m a n = true.
Proof.
  intros vt m a n Hlo Hhi. apply store_ok_app.
  eapply store_ok_window with (base := 0x1002000%Z) (hi := 0x1005000%Z);
    [ | | | exact target_data_wseg | | ];
    [ vm_compute; reflexivity | vm_compute; reflexivity | lia
    | exact Hlo | exact Hhi ].
Qed.

(** The 1024-byte read buffers are fully inside writable byte-defined
    segments. *)
Lemma source_rb_wseg : forall vt,
  wseg_ok (source_segs ++ vt) 0x13008 (word_to_nat (Z_to_bv 64 1024)) = true.
Proof. intros vt. apply wseg_ok_lift. vm_compute. reflexivity. Qed.

Lemma target_rb_wseg : forall vt,
  wseg_ok (target_segs ++ vt) 0x10022ec (word_to_nat (Z_to_bv 64 1024)) = true.
Proof. intros vt. apply wseg_ok_lift. vm_compute. reflexivity. Qed.

(* write_to_mem_above/rdn_wtm_out/rdn_write_to_mem (frame/read-back
   lemmas around write_to_mem, alongside write_to_mem_below) live
   in Common/StreamExec. *)

(** Reading a single byte through a disjoint [wbytes] one-byte store. *)
Lemma rdn_wbytes1_out : forall segs m (addr : word) c (a : word) n,
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  ((bv_unsigned addr < bv_unsigned a)%Z \/
   (bv_unsigned a + Z.of_nat n <= bv_unsigned addr)%Z) ->
  rdn segs (wbytes m addr [c]) a n = rdn segs m a n.
Proof.
  intros segs m addr c a n Hnw Hd. apply rdn_ext; [exact Hnw|].
  intros x Hx. destruct Hd as [Hd | Hd].
  - apply (wbytes_above [c] m addr x). cbn [length]. lia.
  - apply wbytes_below;
      [cbn [length]; pose proof (u64_range addr); lia | lia].
Qed.

(** Append a single byte to a buffer read-back: if [rdn mem base |L| = L]
    then storing one byte at [base+|L|] extends the read-back to [L++[c]]. *)
Lemma rdn_snoc_store : forall segs mem (base : word) L c,
  (bv_unsigned base + Z.of_nat (length L) + 1 <= 2^64)%Z ->
  rdn segs mem base (length L) = Some L ->
  rdn segs (wbytes mem (base + nat_to_word (length L)) [c]) base (length L + 1)
    = Some (L ++ [c]).
Proof.
  intros segs mem base L c Hnw HL.
  assert (Hu : bv_unsigned (base + nat_to_word (length L))
               = (bv_unsigned base + Z.of_nat (length L))%Z).
  { rewrite word_add_nat.
    apply u_Z2bv; [pose proof (u64_range base); lia | lia]. }
  rewrite (rdn_app segs _ (length L) 1 base L [c]).
  - reflexivity.
  - rewrite rdn_wbytes1_out; [exact HL | lia | right; lia].
  - change 1%nat with (length [c]).
    apply rdn_wbytes_hit. cbn [length]. lia.
Qed.

(* ######################################################################### *)
(* DrainSim record entry points                                              *)
(* ######################################################################### *)

(** [to_rd] at the raw ecall post-state record, at this example's chunk
    count of 1024: a7=63 (read), a0=0 (stdin), a1=buffer, a2=1024, buffer
    writable, plus the EOF ([to_out]) and per-block ([procs])
    continuations. *)
Lemma trd_here_rec :
  forall (St:Type) segs (ff:St->byte->option St) (oo:St->list byte) (e:word)
         (LH:St->machine_state->Prop) (a:St) regs pc mem rom buf,
  bv_unsigned (getr regs 17) = 63%Z ->
  reg_get regs 10 = Z_to_bv 64 0 ->
  reg_get regs 11 = buf ->
  reg_get regs 12 = Z_to_bv 64 1024 ->
  wseg_ok segs buf (word_to_nat (Z_to_bv 64 1024)) = true ->
  (* the range passes [access_ok], which [vfs_read] tests before the
     input is consulted.  [DrainSim.ReadPend] asks for this on top of
     the buffer being mapped, because [read_bytes_map]'s walk wraps at
     2^64 while [access_ok] reads [buf + 1024] exactly.  Both buffers
     here are link-time constants. *)
  access_okb buf (bv_unsigned (Z_to_bv 64 1024)) = true ->
  to_out segs (oo a) (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom) ->
  buf_modeled (oo a) ->
  (forall bs, (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= 1024)%Z ->
     match procs ff a bs with
     | Some a' => lh_next segs LH a'
         (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4)
               (write_to_mem mem buf bs) rom)
     | None => to_exit segs e
         (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4)
               (write_to_mem mem buf bs) rom)
     end) ->
  to_rd segs (Z_to_bv 64 1024) ff oo e LH a
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
       ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
       ms_mem := mem; ms_rom := rom |}.
Proof.
  intros St segs ff oo e LH a regs pc mem rom buf
    H17 H10 H11 H12 Hw Haok Hout Hobm Hbytes.
  apply trd_here. exists buf, (getr regs 17).
  unfold ms_gpr. cbn [ms_regs ms_svc_pending].
  rewrite arg_reg_0, arg_reg_1, arg_reg_2.
  refine (conj eq_refl (conj H17 (conj H10 (conj H11 (conj H12
            (conj _ (conj Haok (conj _ (conj Hobm _))))))))).
  - eapply wseg_ok_wdef. exact Hw.
  - rewrite adv_set. exact Hout.
  - intros bs Hlo Hhi. rewrite adv_apply_write. exact (Hbytes bs Hlo Hhi).
Qed.

(** [to_out] emitting [bs] then exit 0, at the raw write ecall record: a7=64
    (write), a0=1 (stdout), buffer bytes read back, exit-0 continuation. *)
Lemma tout_wr_rec : forall segs bs regs pc mem rom,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = Z_to_bv 64 1 ->
  ms_read_bytes {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                   ms_mem := mem; ms_rom := rom |}
    (reg_get regs 11) (reg_get regs 12) = Some bs ->
  (* the range [vfs_write]'s [access_ok] accepts; see [CatSim.write1_check_n] *)
  access_okb (reg_get regs 11) (bv_unsigned (reg_get regs 12)) = true ->
  (1 <= length bs)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length bs)%nat ->
     to_wall_tail segs (Z_to_bv 64 1)
       (mkst (regupd regs 10 (len_word (firstn n bs))) (v_addi pc 4) mem rom)
       (skipn n bs) (to_exit segs (Z_to_bv 64 0))) ->
  to_out segs bs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                    ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                    ms_mem := mem; ms_rom := rom |}.
Proof.
  intros segs bs regs pc mem rom H17 H10 Hr Hok Hnb Hcont.
  apply tout_wr. unfold WrFin. split; [exact Hnb|].
  apply (twl_write_rec segs (Z_to_bv 64 1)); assumption.
Qed.

(** Exit with code [code] at the raw ecall record: a7=93, a0=code. *)
Lemma te_here_rec : forall segs code regs pc mem rom,
  bv_unsigned (getr regs 17) = 93%Z ->
  reg_get regs 10 = code ->
  to_exit segs code {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                       ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                       ms_mem := mem; ms_rom := rom |}.
Proof.
  intros segs code regs pc mem rom H17 H10.
  eapply te_here with (x8 := getr regs 17).
  - reflexivity.
  - left. exact H17.
  - unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_0. exact H10.
Qed.
