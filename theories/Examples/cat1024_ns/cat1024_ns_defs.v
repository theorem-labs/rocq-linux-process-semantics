(** * cat1024-ns: shared helpers for the two per-binary stream proofs.

    PROOF-SIDE FILE (not part of the trusted specification).

    Both binaries implement cat-1024: loop { r = read(0, buf, 1024);
    r = 0 -> exit 0; write all r bytes to fd 1 }.  This file collects the
    image probes (init pcs, store-target checks, buffer writability),
    small value/condition facts, the step tactics shared by the source
    and target proofs, and the ecall-record entry points for the
    StreamSim predicates.

    Bytes are [byte = bv 8], machine values [word = bv 64]; unbounded
    address bookkeeping is in [Z] over [bv_unsigned]; computed stack
    addresses use the canonical [Z_to_bv 64 (...)] form, pc values the
    numeral-literal form.  The chunk size instantiates StreamSim's [cnt]
    at [Z_to_bv 64 1024] (cat1024 is the 1024-byte instance of the shared
    cnt-parameterized loop shape, not a fork).

    A run reads [Run.run_segments]: the image's segments, then the vDSO
    pair.  The store bounds and the buffers' writability below are stated
    over [segs ++ vt] for any appended [vt] ([RunSegmentsLift]), and a
    write carries [access_okb] on its user buffer ([twr_here_rec]). *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StreamExec WallSim StreamSim StoreOk RunSegmentsLift.
From LinuxProcessSemantics.Examples.cat1024_ns Require Import cat1024_ns_code.
From LinuxProcessSemantics.Examples.cat1024_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.cat1024_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(** Every state in this file is reached from process entry, where the FP
    register file is empty and [fcsr] is zero ([PropExec.fx0]). *)
#[local] Instance cat1024_ns_defs_fx : FPState := fx0.

(* ######################################################################### *)
(* Image probes                                                              *)
(* ######################################################################### *)

Lemma source_init_pc_val : SourceMemImage_init_pc = 0x11078%N.
Proof. vm_compute. reflexivity. Qed.

Lemma target_init_pc_val : TargetMemImage_init_pc = 0x1001190%N.
Proof. vm_compute. reflexivity. Qed.

(** Store targets at/above the end of the source text segment avoid all
    read-only segments (the rw data segment is exempt).

    The source has THREE read-only segments, not one: [-z separate-code]
    gives the image a read-only segment (000, holding the ELF headers)
    below the executable one (001, .text), a second read-only segment
    (002, .rodata/.eh_frame) above it, and the writable data segment
    (003) above all three.  See the Makefile's SOURCE_LDFLAGS for why
    the link cannot merge them. *)
Lemma source_avoids_ro : forall (a : word) (n : Z), (0x13000 <= bv_unsigned a)%Z ->
  range_avoids_ro_segs source_segs (bv_unsigned a) n = true.
Proof.
  intros a n Ha.
  apply range_avoids_ro_above with (data_base := 0x13000%Z);
    [vm_compute; reflexivity | exact Ha].
Qed.

(** The source image's WRITABLE window: the rw- segment covers
    [0x13000, 0x14000) and the snapshot carries a byte for every address in
    it (.bss is zero-filled in the .hex), so [wview] is defined there
    whatever the overlay holds — a store into .data/.bss needs no
    prior write.  That is the [store_ok] side condition machine stores
    now carry; stack targets go through the RLIMIT_STACK window
    ([solve_store_ok]) instead. *)
Lemma source_data_wseg : wseg_ok source_segs (0x13000 : word) 4096 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma source_store_ok : forall vt (m : word -> option byte) (a : word) (n : nat),
  (0x13000 <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 0x14000)%Z ->
  store_ok (source_segs ++ vt) m a n = true.
Proof.
  intros vt m a n Hlo Hhi. apply store_ok_app.
  eapply store_ok_window with (base := 0x13000%Z) (hi := 0x14000%Z);
    [ | | | exact source_data_wseg | | ];
    [ vm_compute; reflexivity | vm_compute; reflexivity | lia
    | exact Hlo | exact Hhi ].
Qed.

(** Two-read-only-segment helper (the target has segments 000/001 ro,
    002 rw). *)

(** Same for the target: its two read-only segments end at 0x1000190 and
    0x1001208. *)
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
    [0x1002000, 0x1003000) and the snapshot carries a byte for every address in
    it (.bss is zero-filled in the .hex), so [wview] is defined there
    whatever the overlay holds — a store into .data/.bss needs no
    prior write.  That is the [store_ok] side condition machine stores
    now carry; stack targets go through the RLIMIT_STACK window
    ([solve_store_ok]) instead. *)
Lemma target_data_wseg : wseg_ok target_segs (0x1002000 : word) 4096 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma target_store_ok : forall vt (m : word -> option byte) (a : word) (n : nat),
  (0x1002000 <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 0x1003000)%Z ->
  store_ok (target_segs ++ vt) m a n = true.
Proof.
  intros vt m a n Hlo Hhi. apply store_ok_app.
  eapply store_ok_window with (base := 0x1002000%Z) (hi := 0x1003000%Z);
    [ | | | exact target_data_wseg | | ];
    [ vm_compute; reflexivity | vm_compute; reflexivity | lia
    | exact Hlo | exact Hhi ].
Qed.

(** The 1024-byte buffers are fully inside writable, byte-defined segments. *)
Lemma source_buf_wseg : forall vt,
  wseg_ok (source_segs ++ vt) 0x13008 (word_to_nat (Z_to_bv 64 1024)) = true.
Proof. intros vt. apply wseg_ok_lift. vm_compute. reflexivity. Qed.

Lemma target_buf_wseg : forall vt,
  wseg_ok (target_segs ++ vt) 0x1002208 (word_to_nat (Z_to_bv 64 1024)) = true.
Proof. intros vt. apply wseg_ok_lift. vm_compute. reflexivity. Qed.

(* write_to_mem_above/rdn_wtm_out/rdn_write_to_mem (frame/read-back
   lemmas around write_to_mem, alongside write_to_mem_below) live in
   Common/StreamExec. *)

(* ######################################################################### *)
(* Value / condition facts                                                   *)
(* ######################################################################### *)

(* v_addi_m16/v_addi_m32 (literal negative-immediate instances of
   [SeqExec.v_addi_m]) now live in Common/StepTac.v, in the canonical
   [Z_to_bv 64 (...)] form; [sp_norm] uses them. *)

(** Close a CLOSED word/byte equation by unsigned comparison. *)

(** Nothing is unsigned-below 0. *)
Lemma c_ltu_x0 : forall x : word, c_ltu x (Z_to_bv 64 0) = false.
Proof.
  intro x. rewrite c_ltu_ltb. apply Z.ltb_ge.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  pose proof (u64_range x). lia.
Qed.

(* c_lts_pos_0, c_lts_0_pos and c_eq_0_of_u all live in PropExec. *)

(** Sealed [Z.of_nat] equation for [valid_envp]'s large literal
    (companion of CatExec's [of_nat_131071]/[of_nat_2097152]). *)

(* ######################################################################### *)
(* [cnt]-instantiation for Common.StreamSim: cat1024 is the                  *)
(* 1024-byte instance of StreamSim's [cnt]-parameterized read/write loop     *)
(* shape.                                                                    *)
(* ######################################################################### *)

Lemma cat_Hcnt : (0 < bv_unsigned (Z_to_bv 64 1024) <= rw_bytes_max)%Z.
Proof.
  change (bv_unsigned (Z_to_bv 64 1024)) with 1024%Z.
  unfold rw_bytes_max. lia.
Qed.

(* ######################################################################### *)
(* Step tactics (chained inside msteps / to_rd / to_wr / to_exit)            *)
(* ######################################################################### *)

(** Normalize a closed pc expression ([v_addi pc 4], [btgt ...], ...) at
    the head of the current chain goal to its numeral-literal form (so
    the next fetch lemma applies by conversion).  Extends StepTac's
    [norm_pc] with the StreamSim [to_rd]/[to_wr] arms. *)


(** One non-branching ALU step. *)

(** One ALU step with the written value pre-normalized ([step_addi_at]). *)

(** Unconditional jump (jal x0). *)

(* ######################################################################### *)
(* Ecall-record entry points for the stream predicates                       *)
(* ######################################################################### *)

(** [to_rd] at the raw ecall post-state record (as [step_ecall] leaves it):
    a7 = 63 (read, Z-characterized), a0 = 0 (stdin), a1 = the 1024-byte
    buffer, a2 = 1024, the buffer writable-mapped, plus the two
    continuations. *)
Lemma trd_here_rec : forall segs (LH : machine_state -> Prop) regs pc mem rom buf,
  bv_unsigned (getr regs 17) = 63%Z ->
  reg_get regs 10 = Z_to_bv 64 0 ->
  reg_get regs 11 = buf ->
  reg_get regs 12 = Z_to_bv 64 1024 ->
  wseg_ok segs buf (word_to_nat (Z_to_bv 64 1024)) = true ->
  (* the range passes [access_ok], which [vfs_read] tests before the
     input is consulted.  [StreamSim.ReadPend] asks for this on top of
     the buffer being mapped, because [read_bytes_map]'s walk wraps at
     2^64 while [access_ok] reads [buf + 1024] exactly.  Both buffers
     here are link-time constants, so it is one inequality. *)
  access_okb buf (bv_unsigned (Z_to_bv 64 1024)) = true ->
  to_exit segs (Z_to_bv 64 0)
    (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom) ->
  (forall bs, (1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= 1024)%Z ->
     to_wr segs LH bs (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4)
                            (write_to_mem mem buf bs) rom)) ->
  to_rd segs LH (Z_to_bv 64 1024)
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := Some (getr regs 17);
       ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}.
Proof.
  intros segs LH regs pc mem rom buf H17 H10 H11 H12 Hw Haok Hexit Hbytes.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
  apply trd_here. unfold ReadPend.
  exists buf, (getr regs 17).
  unfold ms_gpr. cbn [ms_regs ms_svc_pending].
  rewrite E10, E11, E12.
  refine (conj eq_refl (conj H17 (conj H10 (conj H11 (conj H12
            (conj _ (conj Haok (conj _ _)))))))).
  - eapply wseg_ok_wdef. exact Hw.
  - rewrite adv_set. exact Hexit.
  - intros bs Hlo Hhi.
    change (bv_unsigned (Z_to_bv 64 1024)) with 1024%Z in Hhi.
    rewrite adv_apply_write. apply Hbytes; assumption.
Qed.

(** [to_wr] at the raw ecall post-state record: a7 = 64 (write,
    Z-characterized), a0 = 1 (stdout), the buffer bytes read back, and
    — per delivered length [n] — the retry-loop continuation: a
    [WallSim.to_wall_tail] of the remainder [skipn n bs] down to the
    loop head (the model returns [len_word (firstn n bs)] in a0). *)
Lemma twr_here_rec : forall segs (LH : machine_state -> Prop) bs regs pc mem rom,
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
       (skipn n bs) (lh_next segs LH)) ->
  to_wr segs LH bs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                      ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                      ms_mem := mem; ms_rom := rom |}.
Proof.
  intros segs LH bs regs pc mem rom H17 H10 Hr Hok Hnb Hcont.
  apply twr_here. unfold WrPend.
  split; [exact Hnb|].
  apply (twl_write_rec segs (Z_to_bv 64 1)); assumption.
Qed.

(** Exit(0) at the raw ecall post-state record: a7 = 93, a0 = 0. *)
Lemma te_here_rec0 : forall segs regs pc mem rom,
  bv_unsigned (getr regs 17) = 93%Z ->
  reg_get regs 10 = Z_to_bv 64 0 ->
  to_exit segs (Z_to_bv 64 0)
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := Some (getr regs 17);
       ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}.
Proof.
  intros segs regs pc mem rom H17 H10.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  eapply te_here with (x8 := getr regs 17).
  - cbn [ms_svc_pending]. reflexivity.
  - left. exact H17.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
Qed.

(* [sp_norm] (nested [v_addi] normalization over an abstract in-window
   sp) lives in Common/StepTac.v. *)
