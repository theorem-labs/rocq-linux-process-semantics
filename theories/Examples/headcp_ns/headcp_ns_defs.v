(** * headcp-ns: shared spec and image probes for the two per-binary proofs.

    PROOF-SIDE FILE (not part of the trusted specification).

    Both binaries implement headcp: open argv[1] read-only, create/truncate
    argv[2], a SINGLE read of a 128-byte buffer, a SINGLE write of exactly
    what was read, close both.  File I/O emits no trace events, so the only
    observables are the exit code and the final file system.  This file
    fixes:

    - the outcome set [hc_outcomes fs0 cwd ur src dst] over the syscall
      resolutions (open-in fails -> code 3, image unchanged; open-out
      fails -> code 4, image unchanged; with both descriptors, code 5
      for a folder source, else code 0 with the bytes read written
      through the destination descriptor), stated over what each open
      of an operand from the working folder answers
      ([FileSimWalk.open_arm]) and used identically by the source and
      target [to_fout] derivations;
    - image probes ([*_init_pc_val], buffer writability);
    - the small fs-algebra facts the single read/write needs.

    Conventions: bytes are [byte = bv 8], machine values/exit codes
    [word = bv 64] (codes spelled [Z_to_bv 64 k]); file offsets/counts
    are [word]s; unbounded address bookkeeping is in [Z] over
    [bv_unsigned].

    Ported in part from theorem-labs/linux-process-semantics
    r22/namespace-core at 6ff3d045 (issue #1011). *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StreamExec StreamSim FileSim ListFacts StoreOk RunSegmentsLift FileSimWalk.
From LinuxProcessSemantics.Examples.headcp_ns Require Import headcp_ns_code.
From LinuxProcessSemantics.Examples.headcp_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.headcp_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(* ######################################################################### *)
(* Image probes                                                              *)
(* ######################################################################### *)

Lemma source_init_pc_val : SourceMemImage_init_pc = 0x11100%N.
Proof. vm_compute. reflexivity. Qed.

Lemma target_init_pc_val : TargetMemImage_init_pc = 0x1001190%N.
Proof. vm_compute. reflexivity. Qed.

(** The 128-byte buffers are fully inside writable, byte-defined segments
    (source [buf] at 0x13008; target [buf] at 0x1002278), whatever the
    run appends after the image's own segments. *)
Lemma source_buf_wseg : forall vt,
  wseg_ok (source_segs ++ vt) 0x13008 (word_to_nat (Z_to_bv 64 128)) = true.
Proof. intros vt. apply wseg_ok_lift. vm_compute. reflexivity. Qed.

Lemma target_buf_wseg : forall vt,
  wseg_ok (target_segs ++ vt) 0x1002278 (word_to_nat (Z_to_bv 64 128)) = true.
Proof. intros vt. apply wseg_ok_lift. vm_compute. reflexivity. Qed.

(* ######################################################################### *)
(* The copy result and the outcome set                                       *)
(* ######################################################################### *)

(** The descriptor table at process entry: the three standard channels,
    so the two opens hand out 3 and then 4. *)
Definition fds0 : list (word * FdEntry) :=
  [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
    (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
    (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ].

Lemma hc_fd1 : alloc_fd fds0 = Z_to_bv 64 3.
Proof. vm_compute. reflexivity. Qed.

Lemma hc_free1 : fd_lookup fds0 (alloc_fd fds0) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma hc_fd2 : forall fe, alloc_fd (fd_insert fds0 (Z_to_bv 64 3) fe) = Z_to_bv 64 4.
Proof. intros fe. vm_compute. reflexivity. Qed.

Lemma hc_free2 : forall fe,
  fd_lookup (fd_insert fds0 (Z_to_bv 64 3) fe)
            (alloc_fd (fd_insert fds0 (Z_to_bv 64 3) fe)) = None.
Proof. intros fe. vm_compute. reflexivity. Qed.

(** The bytes the single 128-byte read delivers on the source
    descriptor, once both descriptors are open on the image [fs]: the
    first (up to) 128 bytes of the source inode as it is then (none when
    the destination's open emptied that same inode), none from
    /dev/null, the first 128 bytes of the run's declared random stream
    [ur] from /dev/urandom ([ReadWrite.read_urandom] takes the whole
    count); [None] is a folder, whose read is -EISDIR. *)
Definition hc_read (fe : FdEntry) (fs : Fs) (ur : InputStream) : option (list byte) :=
  match fe with
  | FdFile i _ => Some (file_read (Fs.fs_ino_data fs i) (Z_to_bv 64 0) (Z_to_bv 64 128))
  | FdDevNull _ _ => Some []
  | FdUrandom _ _ => Some (fst (stream_take_z ur 128))
  | _ => None
  end.

(** The image after the single write of [bs] through the destination
    descriptor: a regular file takes the bytes at offset 0, a device
    leaves the image alone. *)
Definition hc_written (fe : FdEntry) (fs : Fs) (bs : list byte) : Fs :=
  match fe with
  | FdFileW j _ => Fs.fs_set_ino_data fs j (file_write (Fs.fs_ino_data fs j) (Z_to_bv 64 0) bs)
  | _ => fs
  end.

(** THE READ AND THE WRITE.  A folder's read is -EISDIR (code 5).
    Otherwise the write of exactly the bytes read lands whole -- a file
    writes the whole readable buffer, /dev/null answers the count,
    /dev/urandom takes every byte of a readable buffer of at most 128
    bytes ([ReadWrite.random_write]) -- so both binaries exit 0. *)
Definition hc_copy (fs : Fs) (ur : InputStream) (fe_s fe_d : FdEntry)
    : (word * Fs) -> Prop :=
  fun o =>
    match hc_read fe_s fs ur with
    | None => o = (Z_to_bv 64 5, fs)
    | Some bs => o = (Z_to_bv 64 0, hc_written fe_d fs bs)
    end.

Definition hc_fs1 (fs0 : Fs) (ofs : option Fs) : Fs :=
  match ofs with Some f => f | None => fs0 end.

(** The exact set of (exit code, final image) outcomes.  Code 3 with the
    image unchanged is always one (an open answered before the walk, an
    errno at the walk's end, or a refusal beside a descriptor); with a
    source descriptor so is code 4; with both, the read and the write. *)
Definition hc_outcomes (fs0 : Fs) (cwd : path) (ur : InputStream) (src dst : path)
    : (word * Fs) -> Prop :=
  fun o =>
    o = (Z_to_bv 64 3, fs0)
    \/ (op_walked src = true /\
        match open_arm true fs0 cwd src with
        | inl (fe_s, _) =>
            o = (Z_to_bv 64 4, fs0)
            \/ (op_walked dst = true /\
                match open_arm false fs0 cwd dst with
                | inl (fe_d, ofs) => hc_copy (hc_fs1 fs0 ofs) ur fe_s fe_d o
                | inr _ => False
                end)
        | inr _ => False
        end).

(** The chunk is at most 128 bytes. *)
Lemma hc_chunk_le : forall d,
  (length (file_read d (Z_to_bv 64 0) (Z_to_bv 64 128)) <= 128)%nat.
Proof.
  intro d. rewrite length_file_read.
  change (word_to_nat (Z_to_bv 64 128)) with 128%nat. lia.
Qed.

(** What the destination's open hands the write
    ([FileSimWalk.open_arm_wr_cases]): a regular file at offset 0, empty
    in the image [fs], or one of the two devices opened for writing. *)
Definition hc_dst_ok (fe : FdEntry) (fs : Fs) : Prop :=
  (exists j, fe = FdFileW j (Z_to_bv 64 0) /\ Fs.fs_ino_data fs j = [])
  \/ fe = FdDevNull false true \/ fe = FdUrandom false true.

Lemma hc_dst_ok_arm : forall fs cwd dst fe ofs,
  open_arm false fs cwd dst = inl (fe, ofs) -> hc_dst_ok fe (hc_fs1 fs ofs).
Proof.
  intros fs cwd dst fe ofs H. unfold hc_dst_ok, hc_fs1.
  destruct (open_arm_wr_cases _ _ _ _ _ H) as [(j & Hj & Hd) | [(Hj & _) | (Hj & _)]].
  - left. exists j. split; [exact Hj | exact Hd].
  - right. left. exact Hj.
  - right. right. exact Hj.
Qed.

(* ######################################################################### *)
(* Store legality: stores at/above the end of the read-only segments         *)
(* ######################################################################### *)

(** Source: THREE read-only segments — r-- headers [0x10000, 0x11000),
    r-x text [0x11000, 0x12000) and r-- rodata/.eh_frame
    [0x12000, 0x13000) — so the first writable address is 0x13000, where
    the rw- data segment starts. *)
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

(** Target: the two read-only segments end at 0x1001000 and 0x1002000. *)
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

(* ######################################################################### *)
(* valid_argv helpers                                                        *)
(* ######################################################################### *)

(* valid_argv_len/str_len/str_nz live in CatExec. *)

(* ######################################################################### *)
(* Value / condition facts                                                   *)
(* ######################################################################### *)

(** Close a CLOSED word/byte equation by unsigned comparison. *)

(** Nothing is unsigned-below 0. *)
Lemma c_ltu_x0 : forall x : word, c_ltu x (Z_to_bv 64 0) = false.
Proof.
  intro x. rewrite c_ltu_ltb. apply Z.ltb_ge.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  pose proof (u64_range x). lia.
Qed.

(* c_lts_pos_0/c_lts_neg_0 and c_lts_errno live in PropExec; [errno_ret e]
   is a [word], and [PropExec.errno_ret_range] covers the residual
   Z bounds. *)

(** [bv_unsigned] of a modeled block length (all lengths here are far
    below 2^64). *)
Lemma u_len_word : forall {A} (l : list A), (Z.of_nat (length l) < 2^64)%Z ->
  bv_unsigned (len_word l) = Z.of_nat (length l).
Proof. intros A l Hl. unfold len_word. apply u_Z2bv; lia. Qed.

(** [bv_unsigned] of a small [nat_to_word] index. *)

(** The wrapping word/nat offset add in the canonical [Z_to_bv] form
    (hypothesis-free: both sides wrap identically). *)

(** Sealed [Z.of_nat] equation for [valid_envp]'s large literal
    (companion of CatExec's [of_nat_131071]/[of_nat_2097152]). *)

(** Upper bound on the initial stack image (feeds every stack-read
    lemma's no-overflow side condition; the numbers come from
    [valid_argv]/[valid_envp]). *)

(* ######################################################################### *)
(* Step-chaining tactics                                                     *)
(* ######################################################################### *)

(* [norm_pc]/[step_intro]/[stepi]/[stepiv]/[stepiwv]/[stepj]/[sp_norm]/
   [u_norm]/[imm_norm] live in Common/StepTac.v (imported above). *)

(** Normalize a computed address/value equation ([v_addi]-headed side)
    against its canonical [Z_to_bv 64 (...)] / literal form. *)
Ltac addr_tac :=
  getr_resolve; regupd_resolve; sp_norm;
  first [ reflexivity | f_equal; lia | bveq ].

(** A jalr x0 (ret) to a concrete (in-chain) target. *)
Ltac sret F D tt0 :=
  stepjr F D tt0 ltac:(getr_resolve; regupd_resolve; first [ reflexivity | bveq ]).

(** A store-double with pre-normalized address and value; the address
    tactic is explicit so abstract-register frames can rewrite their
    register hypotheses. *)
Ltac ssd_at F D aexp vexp atac vtac rotac :=
  step_intro;
  [ reflexivity
  | eapply step_sd_at with (a := aexp) (v := vexp);
    [ exact F | reflexivity | exact D | atac | vtac | rotac ]
  | step_simpl ].

Ltac ssd F D aexp vexp vtac rotac :=
  ssd_at F D aexp vexp addr_tac vtac rotac.

(** A load-double of a known 8-byte slot (explicit address tactic, as
    for [ssd_at]). *)
Ltac sld_at F D aexp vexp atac readtac :=
  step_intro;
  [ reflexivity
  | eapply step_ld with (bs := word_to_le_bytes 8 vexp) (v := vexp);
    [ exact F | reflexivity | exact D
    | match goal with |- rdn _ _ ?ad _ = _ =>
        replace ad with aexp by atac
      end; readtac
    | exact (bytes_le_to_Z_8 _) ]
  | step_simpl ].

Ltac sld F D aexp vexp readtac :=
  sld_at F D aexp vexp addr_tac readtac.

(* fd-table lemmas beyond FileSim's own, and the tfo_*_rec ergonomic
   "at the raw ecall record" wrappers (record_gpr, tfo_exit_rec,
   tfo_read_rec, tfo_write_rec, tfo_close_rec, tfo_open_enoent_rec,
   tfo_open_rd_rec, tfo_open_wr_rec, tfo_open_toolong_rec), live in
   Common/FileSim. *)

(* write_to_mem_above/rdn_wtm_out/rdn_write_to_mem (frame/read-back
   lemmas around write_to_mem, alongside write_to_mem_below) live
   in Common/StreamExec. *)

(* ######################################################################### *)
(* Miscellany                                                                *)
(* ######################################################################### *)

(** Reduce [m_fds]/[m_fs]/[m_halted] applied to [with_fds]/[with_fs] chains. *)
Ltac model_simp := cbn [with_fds with_fs m_fds m_fs m_halted]; autorewrite with model.

(** In of a firstn is In of the whole list. *)
