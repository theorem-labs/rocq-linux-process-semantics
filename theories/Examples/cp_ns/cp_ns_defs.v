(** * cp-ns: shared spec and image probes for the two per-binary proofs.

    PROOF-SIDE FILE (not part of the trusted specification).

    Both binaries implement cp: open argv[1] read-only, create/truncate
    argv[2], copy through a 1024-byte buffer, close both.  File I/O emits
    no trace events, so the only observables are the exit code and the
    final file system.  This file fixes:

    - the outcome set [cp_outcomes fs0 cwd ur src dst] over the syscall
      resolutions (open-in fails -> code 3, image unchanged; open-out
      fails -> code 4, image unchanged; with both descriptors, the copy:
      code 5 for a folder source, code 0 with the destination's inode
      holding the source inode's bytes, or the image after the
      destination's open for a device on either side; code 5 for a
      source of [2^63 - 1024] bytes or more, cut there; code 6 for
      /dev/urandom into a regular file, cut at the same offset), stated
      over what each operand's open hands out ([FileSimWalk.open_arm])
      and the declared random stream [ur], and used identically by the
      source and target derivations;
    - image probes ([*_init_pc_val], buffer writability);
    - the descriptor table at entry and what the destination's open
      hands the copy ([cp_dst_ok]);
    - the inode facts the copy-loop invariant needs.

    Bytes are [byte = bv 8], machine values [word = bv 64]; file offsets
    are [word]s.  [rw_verify_area]'s position test bounds every regular
    file transfer: the copy loop reads and writes 1024 bytes at offsets
    that are multiples of 1024, so the read or write at [cp_cut] =
    [2^63 - 1024] is -EINVAL (fs/read_write.c:467-469, Linux v6.18.46).
    A regular-file source of that many bytes or more is copied up to
    [cp_cut] and both binaries exit 5 (their read-error path); a copy
    from /dev/urandom into a regular file stops at the write at
    [cp_cut] and both exit 6 (their write-error path).  /dev/urandom
    never returns 0, and a device destination's position never moves
    ([write_null] and [random_write_iter] leave it at 0), so a copy
    from /dev/urandom into a device is the one copy that never ends:
    [cp_copy] has no outcome for it, and the per-binary
    derivations end it in a silent loop ([FileSimLoop.tfl_loop]).

    Ported in part from theorem-labs/linux-process-semantics
    r22/namespace-core at 6ff3d045 (issue #1011). *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StreamExec StreamSim FileSim ErrEscape StoreOk RunSegmentsLift FileSimWalk.
From LinuxProcessSemantics.Examples.cp_ns Require Import cp_ns_code.
From LinuxProcessSemantics.Examples.cp_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.cp_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(* ######################################################################### *)
(* Small word/nat bridges                                                    *)
(* ######################################################################### *)

Lemma wtn_ntw : forall n : nat, (Z.of_nat n < 2^64)%Z ->
  word_to_nat (nat_to_word n) = n.
Proof.
  intros n Hn. unfold word_to_nat. rewrite u_ntw by exact Hn.
  apply Nat2Z.id.
Qed.

Lemma u_len_word : forall {A} (l : list A), (Z.of_nat (length l) < 2^64)%Z ->
  bv_unsigned (len_word l) = Z.of_nat (length l).
Proof. intros A l Hl. unfold len_word. apply u_Z2bv; lia. Qed.

Lemma wtn_len_word : forall {A} (l : list A), (Z.of_nat (length l) < 2^64)%Z ->
  word_to_nat (len_word l) = length l.
Proof.
  intros A l Hl. unfold word_to_nat. rewrite u_len_word by exact Hl.
  apply Nat2Z.id.
Qed.

(** [len_word] is [nat_to_word] of the length (definitional). *)
Lemma len_word_ntw : forall {A} (l : list A), len_word l = nat_to_word (length l).
Proof. reflexivity. Qed.

(** A write that starts at or before end-of-file leaves the file at least
    [off + length bs] bytes long: no gap is opened, so the written bytes
    land inside (or just past) the existing data. *)
Lemma file_write_len_lb : forall data off bs,
  (bv_unsigned off <= Z.of_nat (length data))%Z ->
  (bv_unsigned off + Z.of_nat (length bs)
     <= Z.of_nat (length (file_write data off bs)))%Z.
Proof.
  intros data off bs Hoff.
  pose proof (u64_range off) as Hr.
  assert (Hn : Z.of_nat (word_to_nat off) = bv_unsigned off)
    by (unfold word_to_nat; rewrite Z2Nat.id; lia).
  destruct bs as [|b bs'].
  - change (file_write data off []) with data. cbn [length]. lia.
  - unfold file_write, file_extend. cbv beta iota zeta.
    replace (word_to_nat off - length data)%nat with 0%nat by lia.
    cbn [repeat]. rewrite app_nil_r.
    rewrite !length_app, length_firstn, length_skipn.
    lia.
Qed.

(** The loop invariant's step: appending at end-of-file keeps the fd
    offset at or before the new end-of-file, wrap-around included. *)
Lemma file_write_off_bound : forall data off bs,
  (Z.of_nat (length bs) < 2^64)%Z ->
  (bv_unsigned off <= Z.of_nat (length data))%Z ->
  (bv_unsigned (off + len_word bs)
     <= Z.of_nat (length (file_write data off bs)))%Z.
Proof.
  intros data off bs Hbs Hoff.
  pose proof (file_write_len_lb data off bs Hoff) as Hlb.
  pose proof (u64_range off) as Hr.
  rewrite bv_add_unsigned, bv_wrap64_mod, (u_len_word bs Hbs).
  eapply Z.le_trans; [apply Z.mod_le; lia | exact Hlb].
Qed.

(** The wrapping word/nat addition (hypothesis-free: both sides wrap). *)
Lemma ntw_add : forall a b : nat,
  nat_to_word a + nat_to_word b = nat_to_word (a + b).
Proof.
  intros a b. apply bv_eq. unfold nat_to_word.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  rewrite bv_wrap_add_idemp_l, bv_wrap_add_idemp_r.
  rewrite Nat2Z.inj_add. reflexivity.
Qed.

Lemma wtn_1024 : word_to_nat (Z_to_bv 64 1024) = 1024%nat.
Proof. vm_compute. reflexivity. Qed.

(* ######################################################################### *)
(* Image probes                                                              *)
(* ######################################################################### *)

Lemma source_init_pc_val : SourceMemImage_init_pc = 0x1112c%N.
Proof. vm_compute. reflexivity. Qed.

Lemma target_init_pc_val : TargetMemImage_init_pc = 0x1001190%N.
Proof. vm_compute. reflexivity. Qed.

(** The 1024-byte copy buffers are fully inside writable, byte-defined
    segments (source [buf] at 0x13008; target [buf] at 0x1002298),
    whatever the run appends after the image's own segments. *)
Lemma source_buf_wseg : forall vt,
  wseg_ok (source_segs ++ vt) 0x13008 (word_to_nat (Z_to_bv 64 1024)) = true.
Proof. intros vt. apply wseg_ok_lift. vm_compute. reflexivity. Qed.

Lemma target_buf_wseg : forall vt,
  wseg_ok (target_segs ++ vt) 0x1002298 (word_to_nat (Z_to_bv 64 1024)) = true.
Proof. intros vt. apply wseg_ok_lift. vm_compute. reflexivity. Qed.

(* ######################################################################### *)
(* The copy result and the outcome set                                       *)
(* ######################################################################### *)

(** THE COPY, once both opens returned descriptors ([FileSimWalk.open_arm]:
    the source's entry [fe_s], the destination's [fe_d], the image [fs1]
    the second open leaves).  A folder's read is -EISDIR (code 5);
    /dev/null reads 0 bytes at once (code 0, the image [fs1]); a regular
    file is copied whole, by inode, into the destination (an empty source
    writes nothing; a file destination takes the bytes at its inode, a
    device every write whole: /dev/null answers the count, /dev/urandom
    takes every byte of a readable buffer of at most 1024 bytes,
    [ReadWrite.random_write]), code 0, when it is shorter than [cp_cut].
    One of [cp_cut] bytes or more is copied up to [cp_cut], where the
    read is -EINVAL: code 5.  A source and a destination that are one inode read the
    truncated, empty file.  /dev/urandom as the source never reads 0
    bytes: into a regular file it is copied up to [cp_cut], where the
    write is -EINVAL (code 6), the file then holding the stream's first
    [cp_cut] bytes; into a device it is copied forever, and there is no
    outcome (the per-binary derivations end it in a silent loop,
    [FileSimLoop.tfl_loop]). *)
(** THE CUT: [2^63 - 1024], the first multiple of 1024 at which a
    1024-byte read or write fails [rw_verify_area]'s position test
    ([ReadWrite.rw_pos_einvalb]).  It is a [nat] that must never be
    computed: as a unary numeral it does not fit in memory, and [lia]
    evaluates a closed [nat] it meets.  So it is sealed behind an opaque
    proof, and the proofs reason about it through [cp_cut_Z] alone. *)
Lemma cp_cut_sig : { n : nat | Z.of_nat n = (2 ^ 63 - 1024)%Z }.
Proof. exists (Z.to_nat (2 ^ 63 - 1024)). apply Z2Nat.id. lia. Qed.

Definition cp_cut : nat := proj1_sig cp_cut_sig.

Lemma cp_cut_Z : Z.of_nat cp_cut = (2 ^ 63 - 1024)%Z.
Proof. exact (proj2_sig cp_cut_sig). Qed.

Definition cp_copied (fe_d : FdEntry) (fs1 : Fs) (D : list byte) : Fs :=
  match fe_d, D with
  | FdFileW j _, _ :: _ => Fs.fs_set_ino_data fs1 j D
  | _, _ => fs1
  end.

(** What the copy of a regular file's bytes [D] into [fe_d] ends in:
    the whole file and exit 0 when it is shorter than [cp_cut], else its
    first [cp_cut] bytes and the read-error exit 5. *)
Definition cp_file_outcome (fe_d : FdEntry) (fs1 : Fs) (D : list byte)
    : (word * Fs) -> Prop :=
  fun o =>
    if (Z.of_nat (length D) <? 2 ^ 63 - 1024)%Z
    then o = (Z_to_bv 64 0, cp_copied fe_d fs1 D)
    else o = (Z_to_bv 64 5, cp_copied fe_d fs1 (firstn cp_cut D)).

Definition cp_copy (fs1 : Fs) (ur : InputStream) (fe_s fe_d : FdEntry)
    : (word * Fs) -> Prop :=
  fun o =>
    match fe_s with
    | FdDir _ => o = (Z_to_bv 64 5, fs1)
    | FdDevNull _ _ => o = (Z_to_bv 64 0, fs1)
    | FdFile i _ => cp_file_outcome fe_d fs1 (Fs.fs_ino_data fs1 i) o
    | FdUrandom _ _ =>
        match fe_d with
        | FdFileW _ _ => o = (Z_to_bv 64 6, cp_copied fe_d fs1 (fst (stream_take ur cp_cut)))
        | _ => False
        end
    | _ => False
    end.

Definition cp_fs1 (fs0 : Fs) (ofs : option Fs) : Fs :=
  match ofs with Some f => f | None => fs0 end.

(** The descriptor table at process entry: the three standard channels,
    so the two opens hand out 3 and then 4. *)
Definition fds0 : list (word * FdEntry) :=
  [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
    (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
    (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ].

Lemma cp_fd1 : alloc_fd fds0 = Z_to_bv 64 3.
Proof. vm_compute. reflexivity. Qed.

Lemma cp_free1 : fd_lookup fds0 (alloc_fd fds0) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma cp_fd2 : forall fe, alloc_fd (fd_insert fds0 (Z_to_bv 64 3) fe) = Z_to_bv 64 4.
Proof. intros fe. vm_compute. reflexivity. Qed.

Lemma cp_free2 : forall fe,
  fd_lookup (fd_insert fds0 (Z_to_bv 64 3) fe)
            (alloc_fd (fd_insert fds0 (Z_to_bv 64 3) fe)) = None.
Proof. intros fe. vm_compute. reflexivity. Qed.

(** What the destination's open hands the copy
    ([FileSimWalk.open_arm_wr_cases]): a regular file at offset 0, empty
    in the image [fs], or one of the two devices opened for writing. *)
Definition cp_dst_ok (fe : FdEntry) (fs : Fs) : Prop :=
  (exists j, fe = FdFileW j (Z_to_bv 64 0) /\ Fs.fs_ino_data fs j = [])
  \/ fe = FdDevNull false true \/ fe = FdUrandom false true.

Lemma cp_dst_ok_arm : forall fs cwd dst fe ofs,
  open_arm false fs cwd dst = inl (fe, ofs) -> cp_dst_ok fe (cp_fs1 fs ofs).
Proof.
  intros fs cwd dst fe ofs H. unfold cp_dst_ok, cp_fs1.
  destruct (open_arm_wr_cases _ _ _ _ _ H) as [(j & Hj & Hd) | [(Hj & _) | (Hj & _)]].
  - left. exists j. split; [exact Hj | exact Hd].
  - right. left. exact Hj.
  - right. right. exact Hj.
Qed.

(** The exact set of (exit code, final image) outcomes.  Code 3 with the
    image unchanged is always one (an open answered before the walk, an
    errno at the walk's end, or a refusal beside a descriptor); with a
    source descriptor so is code 4; with both, the copy's. *)
Definition cp_outcomes (fs0 : Fs) (cwd : path) (ur : InputStream) (src dst : path)
    : (word * Fs) -> Prop :=
  fun o =>
    o = (Z_to_bv 64 3, fs0)
    \/ (op_walked src = true /\
        match open_arm true fs0 cwd src with
        | inl (fe_s, _) =>
            o = (Z_to_bv 64 4, fs0)
            \/ (op_walked dst = true /\
                match open_arm false fs0 cwd dst with
                | inl (fe_d, ofs) => cp_copy (cp_fs1 fs0 ofs) ur fe_s fe_d o
                | inr _ => False
                end)
        | inr _ => False
        end).

(* ######################################################################### *)
(* Inode facts for the copy loop                                             *)
(* ######################################################################### *)

(** Writing the destination's inode leaves every other inode's bytes. *)
Lemma cp_src_data_stable : forall fs i j d,
  Z.eqb i j = false ->
  Fs.fs_ino_data (Fs.fs_set_ino_data fs j d) i = Fs.fs_ino_data fs i.
Proof. intros fs i j d H. now apply Fs.fs_ino_data_set_neq. Qed.

(** Chunk-length bookkeeping (word offsets, in-range). *)
Lemma cp_chunk_len : forall (D : list byte) k, (Z.of_nat k < 2^64)%Z ->
  length (file_read D (nat_to_word k) (Z_to_bv 64 1024))
  = Nat.min 1024 (length D - k)%nat.
Proof.
  intros D k Hk. rewrite length_file_read.
  rewrite wtn_1024, wtn_ntw by exact Hk. reflexivity.
Qed.

(** The copy loop's destination entry and image after [k] bytes: a file
    destination at offset [k] holding the first [k] bytes (the image the
    second open left while nothing is written yet), a device as it was. *)
Definition cp_dst_at (fe_d : FdEntry) (k : nat) : FdEntry :=
  match fe_d with
  | FdFileW j _ => FdFileW j (nat_to_word k)
  | _ => fe_d
  end.

Definition cp_fs_at (fe_d : FdEntry) (fs1 : Fs) (D : list byte) (k : nat) : Fs :=
  match fe_d, k with
  | FdFileW j _, S _ => Fs.fs_set_ino_data fs1 j (firstn k D)
  | _, _ => fs1
  end.

Lemma cp_fs_at_final : forall fe_d fs1 D,
  cp_fs_at fe_d fs1 D (length D) = cp_copied fe_d fs1 D.
Proof.
  intros fe_d fs1 D. unfold cp_fs_at, cp_copied.
  destruct fe_d; try reflexivity.
  destruct D as [|b D']; [reflexivity|].
  cbn [length]. f_equal. exact (firstn_all (b :: D')).
Qed.

Lemma cp_fs_at_data_dst : forall j o fs1 D k,
  Fs.fs_ino_data fs1 j = [] ->
  Fs.fs_ino_data (cp_fs_at (FdFileW j o) fs1 D k) j = firstn k D.
Proof.
  intros j o fs1 D k Hj. destruct k as [|k'].
  - cbn [cp_fs_at firstn]. exact Hj.
  - cbn [cp_fs_at]. apply Fs.fs_ino_data_set_eq.
Qed.

Lemma cp_fs_at_data_src : forall fe_d fs1 i D k,
  Fs.fs_ino_data fs1 i = D -> (k <= length D)%nat ->
  (forall j o, fe_d = FdFileW j o -> D <> [] -> i <> j) ->
  Fs.fs_ino_data (cp_fs_at fe_d fs1 D k) i = D.
Proof.
  intros fe_d fs1 i D k HD Hk Hij.
  destruct fe_d as [c|i0 o0|j o|i1 o1|i2 o2|p0|sk|pid pw|nr nw|ur uw|sid ss st|ctx|fam];
    try exact HD.
  destruct k as [|k']; [exact HD|].
  cbn [cp_fs_at].
  assert (HDne : D <> []) by (intro He; rewrite He in Hk; cbn in Hk; lia).
  rewrite cp_src_data_stable; [exact HD|].
  apply Z.eqb_neq. exact (Hij j o eq_refl HDne).
Qed.

(** One write step of the copy into the file destination [j]. *)
Lemma cp_fs_at_step : forall j o fs1 D k,
  (k < length D)%nat -> (Z.of_nat k < 2^64)%Z ->
  Fs.fs_set_ino_data (cp_fs_at (FdFileW j o) fs1 D k) j
    (file_write (firstn k D) (nat_to_word k)
                (file_read D (nat_to_word k) (Z_to_bv 64 1024)))
  = cp_fs_at (FdFileW j o) fs1 D (k + Nat.min 1024 (length D - k)).
Proof.
  intros j o fs1 D k Hk HD.
  assert (Hw : file_write (firstn k D) (nat_to_word k)
                 (file_read D (nat_to_word k) (Z_to_bv 64 1024))
               = firstn (k + Nat.min 1024 (length D - k)) D).
  { rewrite file_write_append
      by (rewrite wtn_ntw by lia; rewrite length_firstn; lia).
    pose proof (copy_step D (nat_to_word k) (Z_to_bv 64 1024)) as H.
    rewrite wtn_1024, wtn_ntw in H by lia.
    exact H. }
  rewrite Hw.
  destruct (k + Nat.min 1024 (length D - k))%nat as [|n] eqn:Hn; [lia|].
  destruct k as [|k'].
  - cbn [cp_fs_at]. reflexivity.
  - cbn [cp_fs_at]. rewrite fs_set_ino_data_twice. reflexivity.
Qed.

(** Reduce [m_fds]/[m_fs]/[m_halted] applied to [with_fds]/[with_fs] chains. *)
Ltac model_simp := cbn [with_fds with_fs m_fds m_fs m_halted]; autorewrite with model.

(* ######################################################################### *)
(* Store legality: stores at/above the end of the read-only segments         *)
(* ######################################################################### *)

(** Source: THREE read-only segments after the toolchain bump — the r--
    headers segment [0x10000, 0x11000), the r-x text segment
    [0x11000, 0x12000) and the r-- .rodata/.eh_frame segment
    [0x12000, 0x13000) (page-rounded LOAD segment size 0x1000 each).  The
    first writable address is therefore 0x13000, where the rw- data
    segment starts. *)
Lemma source_avoids_ro : forall (a : word) (n : Z),
  (0x13000 <= bv_unsigned a)%Z ->
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

(** Target: the two read-only segments end at 0x1001000 and 0x1002000
    (page-rounded LOAD segment sizes 0x1000 each). *)
Lemma target_avoids_ro : forall (a : word) (n : Z),
  (0x1002000 <= bv_unsigned a)%Z ->
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
(* The endless copies: what the copy loop's read anchors keep                *)
(* ######################################################################### *)

(** The destination descriptor of an endless copy: a device opened for
    writing.  A regular file is not one: its write at [cp_cut] is
    -EINVAL, which ends the copy ([source_uloop], [target_uloop]). *)
Definition cp_edst (fdout : word) (m : Model) : Prop :=
  (exists rd, fd_lookup (m_fds m) fdout = Some (FdDevNull rd true))
  \/ (exists rd, fd_lookup (m_fds m) fdout = Some (FdUrandom rd true)).

(** The source descriptor of an endless copy: /dev/urandom opened for
    reading with an endless declared stream.  A regular file is not one:
    its read at [cp_cut] is -EINVAL, which ends the copy. *)
Definition cp_esrc (fdin : word) (m : Model) : Prop :=
  fd_lookup (m_fds m) fdin = Some (FdUrandom true false) /\
  stream_infinite (m_urandom m).

Definition cp_emodel (fdin fdout : word) (m : Model) : Prop :=
  m_halted m = None /\ m_vm_lazy m = [] /\ cp_esrc fdin m /\ cp_edst fdout m.

(** What the destination's open hands out, when it is a device, is such a
    destination. *)
Lemma cp_edst_open : forall fdout m fe,
  fd_lookup (m_fds m) fdout = Some fe ->
  fe = FdDevNull false true \/ fe = FdUrandom false true ->
  cp_edst fdout m.
Proof.
  intros fdout m fe Hfd [-> | ->]; unfold cp_edst.
  - left. exists false. exact Hfd.
  - right. exists false. exact Hfd.
Qed.

(** A read moves only the source descriptor. *)
Lemma cp_edst_read : forall fdin fdout m e,
  fdin <> fdout -> cp_edst fdout m ->
  cp_edst fdout (with_fds (fd_insert (m_fds m) fdin e) m).
Proof.
  intros fdin fdout m e Hne H. unfold cp_edst in *. model_simp.
  rewrite fd_lookup_insert_neq by congruence. exact H.
Qed.

(* ######################################################################### *)
(* The cut: where [rw_verify_area]'s position test ends a copy             *)
(* ######################################################################### *)

(** The loop's offsets are multiples of 1024 until the last, short read,
    and [cp_cut] is one: so an offset under [cp_cut] that is a multiple
    of 1024 leaves room for a whole 1024-byte transfer before it. *)
Lemma cp_room : forall k q,
  Z.of_nat k = (1024 * q)%Z -> (Z.of_nat k < Z.of_nat cp_cut)%Z ->
  (Z.of_nat k + 1024 <= Z.of_nat cp_cut)%Z.
Proof. intros k q Hq Hk. rewrite cp_cut_Z in *. lia. Qed.

(** The position test of a transfer of at most 1024 bytes at an offset
    under [cp_cut] passes: the transfer ends at or before [LLONG_MAX]. *)
Lemma cp_pos_ok : forall k (n : Z),
  (Z.of_nat k < Z.of_nat cp_cut)%Z -> (n <= 1024)%Z ->
  rw_pos_einvalb (nat_to_word k) n = false.
Proof.
  intros k n Hk Hn. unfold rw_pos_einvalb. apply Z.ltb_ge.
  pose proof cp_cut_Z as Hc.
  rewrite u_ntw by lia. lia.
Qed.

(** ...and at [cp_cut] itself a 1024-byte transfer fails it: the read of
    a regular file, and the write of a whole /dev/urandom chunk. *)
Lemma cp_pos_at_cut : forall (n : Z),
  (1024 <= n)%Z -> rw_pos_einvalb (nat_to_word cp_cut) n = true.
Proof.
  intros n Hn. unfold rw_pos_einvalb. apply Z.ltb_lt.
  pose proof cp_cut_Z as Hc.
  rewrite u_ntw by lia. lia.
Qed.

(** [blez a0] is TAKEN on an errno return: the write-error branch both
    binaries take on the -EINVAL at [cp_cut]. *)
Lemma c_lts_0_errno : forall e, (1 <= e)%Z -> (e <= 4095)%Z ->
  c_lts (Z_to_bv 64 0) (errno_ret e) = false.
Proof.
  intros e H1 H2. unfold c_lts, bv_lts.
  change (bv_signed (Z_to_bv 64 0)) with 0%Z.
  rewrite errno_ret_signed by lia.
  apply Z.ltb_ge. lia.
Qed.

(** After [k] bytes of [D], [k] at least one, the destination is the
    first [k] bytes copied ([cp_copied] of them): the cut's image. *)
Lemma cp_fs_at_copied : forall fe_d fs1 D k,
  (1 <= k)%nat -> (k <= length D)%nat ->
  cp_fs_at fe_d fs1 D k = cp_copied fe_d fs1 (firstn k D).
Proof.
  intros fe_d fs1 D k H1 Hk. unfold cp_fs_at, cp_copied.
  destruct fe_d; try reflexivity.
  destruct k as [|k']; [lia|].
  destruct D as [|b D']; [cbn in Hk; lia|].
  reflexivity.
Qed.

(** THE URANDOM COPY INTO A FILE: after [k] bytes the destination's inode
    [j] holds the stream's first [k] bytes, the image the second open
    left while nothing is written yet. *)
Definition cp_ufs_at (fs1 : Fs) (j : Fs.ino) (ur : InputStream) (k : nat) : Fs :=
  match k with
  | O => fs1
  | S _ => Fs.fs_set_ino_data fs1 j (fst (stream_take ur k))
  end.

Lemma cp_ufs_at_data : forall fs1 j ur k,
  Fs.fs_ino_data fs1 j = [] ->
  Fs.fs_ino_data (cp_ufs_at fs1 j ur k) j = fst (stream_take ur k).
Proof.
  intros fs1 j ur k Hj. destruct k as [|k'].
  - cbn [cp_ufs_at]. rewrite Hj. reflexivity.
  - cbn [cp_ufs_at]. apply Fs.fs_ino_data_set_eq.
Qed.

(** One chunk of the stream written at offset [k], the end of the
    stream's first [k] bytes. *)
Lemma cp_ufs_at_step : forall fs1 j ur k chunk,
  (Z.of_nat k < 2^64)%Z ->
  chunk = fst (stream_take (snd (stream_take ur k)) 1024) ->
  stream_infinite ur ->
  Fs.fs_set_ino_data (cp_ufs_at fs1 j ur k) j
    (file_write (fst (stream_take ur k)) (nat_to_word k) chunk)
  = cp_ufs_at fs1 j ur (k + 1024).
Proof.
  intros fs1 j ur k chunk Hk -> Hinf.
  rewrite file_write_append
    by (rewrite wtn_ntw by exact Hk;
        rewrite (stream_take_infinite_length _ _ Hinf); reflexivity).
  assert (Hadd : fst (stream_take ur k) ++ fst (stream_take (snd (stream_take ur k)) 1024)
                 = fst (stream_take ur (k + 1024))).
  { rewrite stream_take_add. reflexivity. }
  rewrite Hadd.
  destruct (k + 1024)%nat as [|n] eqn:Hn; [lia|].
  destruct k as [|k'].
  - cbn [cp_ufs_at]. reflexivity.
  - cbn [cp_ufs_at]. rewrite fs_set_ino_data_twice. reflexivity.
Qed.

(** After [n] bytes, [n] at least one, the image is [cp_copied] of the
    stream's first [n] bytes: at [cp_cut], [cp_copy]'s code-6 image. *)
Lemma cp_ufs_at_copied : forall fs1 j o ur n,
  stream_infinite ur -> (1 <= n)%nat ->
  cp_ufs_at fs1 j ur n = cp_copied (FdFileW j o) fs1 (fst (stream_take ur n)).
Proof.
  intros fs1 j o ur n Hinf Hn.
  pose proof (stream_take_infinite_length n ur Hinf) as Hlen.
  destruct n as [|c]; [lia|].
  unfold cp_ufs_at, cp_copied.
  destruct (fst (stream_take ur (S c))) as [|b bs]; [cbn in Hlen; lia|].
  reflexivity.
Qed.
