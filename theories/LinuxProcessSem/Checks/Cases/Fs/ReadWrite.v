(** * LinuxProcessSem.Checks.Cases.Fs.ReadWrite — worked examples over read (63), write (64), pread64 (67), pwrite64 (68), writev (66), readv (65), lseek (62)

    Mirrors [Sys/Fs/ReadWrite.v], which answers to Linux
    [fs/read_write.c]: this file holds the worked examples for the
    syscalls defined there, and no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary.

    Ported in part from theorem-labs/linux-process-semantics
    r22/namespace-core at 6ff3d045 (issue #1011). *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Decode DecodeC.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Fs.Stat.

Lemma file_write_emits_nothing : forall fd buf count i m p off eff m' evs,
  fd_lookup (m_fds m) fd = Some (FdFileW p off) ->
  write_spec fd buf count i m (Ok eff m' evs) ->
  evs = [].
Proof.
  intros fd buf count i m p off eff m' evs Hfd Hspec.
  apply check_write_complete_ok in Hspec.
  unfold check_write in Hspec. rewrite Hfd in Hspec. cbv iota zeta in Hspec.
  (* the transfer gate, [vfs_write]'s [access_ok], then the -EFAULT gate *)
  destruct (negb (modeled_rw_range buf count)); cbv iota in Hspec; [discriminate|].
  destruct (negb (access_okb buf (bv_unsigned count))); cbv iota in Hspec.
  { (* the named range is refused: -EFAULT, no events *)
    apply check_ret_only_ok_iff in Hspec. destruct Hspec as (_ & _ & Hev).
    exact Hev. }
  destruct (rw_pos_einvalb off (bv_unsigned count)); cbv iota in Hspec.
  { (* [rw_verify_area]'s position test: -EINVAL, no events *)
    apply check_ret_only_ok_iff in Hspec. destruct Hspec as (_ & _ & Hev).
    exact Hev. }
  lazymatch type of Hspec with (if ?b then _ else _) = _ => destruct b end;
    cbv iota in Hspec.
  - (* -EFAULT: no writes, no events, whatever the file it extends *)
    unfold check_write_fault_extend in Hspec. cbv zeta in Hspec.
    destruct (negb (modeled_zero_fill (bv_unsigned off) (fs_ino_data (m_fs m) p)));
      cbv iota in Hspec; [discriminate|].
    apply check_ret_only_copyins_ok_iff in Hspec.
    destruct Hspec as (_ & _ & Hev). exact Hev.
  - (* the range verdict a zero-length write still faces, then the file *)
    destruct (w_is0 count); cbv iota in Hspec;
      [ unfold check_access_ok_zero in Hspec;
        destruct (access_okb buf (bv_unsigned count)); cbv iota in Hspec;
        [ | apply check_ret_only_ok_iff in Hspec;
            destruct Hspec as (_ & _ & Hev); exact Hev ]
      | ].
    (* and the past-end-of-file hole guard *)
    all: destruct (negb (modeled_file_gap (fs_ino_data (m_fs m) p) off
                           (write_source (in_mem i) buf count)));
         cbv iota in Hspec; [discriminate|].
    all: first
      [ apply check_ret_only_ok_iff in Hspec
      | apply check_ret_only_copyins_ok_iff in Hspec ];
      destruct Hspec as (_ & _ & Hev); exact Hev.
Qed.

(** Once the input stream has run out, every later read on stdin has
    exactly one admissible outcome: change nothing, emit nothing, and
    return 0 — or -EFAULT, for a range past [State.TASK_SIZE], which is
    the range verdict rather than a copy fault.  Neither carries events or moves the
    model, which is what the retry argument needs.  Hence `cat` and `cat-that-retries-once-after-EOF` are trace
    equivalent: the retry deterministically sees end-of-file again and is
    invisible.  Stickiness is STRUCTURAL — [IEof] has no successor,
    so there is nothing left for a later read to deliver; it is not a
    model invariant a spec could accidentally break. *)

Lemma read_after_eof_deterministic : forall fd buf count i m ch eff m' evs,
  fd_lookup (m_fds m) fd = Some (FdChannel ch) ->
  ch = 0 ->
  m_stdin m = IEof ->
  read_spec fd buf count i m (Ok eff m' evs) ->
  (eff = mkEffect 0 [] [] \/ eff = mkEffect (errno_ret EFAULT) [] [])
  /\ m' = m /\ evs = [].
Proof.
  intros fd buf count i m ch eff m' evs Hfd Hch Heof Hspec. subst ch.
  apply check_read_complete_ok in Hspec.
  unfold check_read in Hspec. rewrite Hfd in Hspec. cbv iota in Hspec.
  change (negb (w_is0 0)) with false in Hspec. cbv iota in Hspec.
  destruct (negb (access_okb buf (bv_unsigned count))); cbv iota in Hspec.
  { (* the range is refused: the -EFAULT the statement's right disjunct
       carries *)
    apply check_ret_only_ok_iff in Hspec. destruct Hspec as (-> & -> & ->).
    split; [right; reflexivity|split; reflexivity]. }
  assert (HZ : Z_to_bv 64 0 = (0 : word)) by (apply bv_eq; reflexivity).
  destruct (w_is0 count) eqn:Hc; cbv iota in Hspec;
    [|rewrite Heof in Hspec; cbv iota in Hspec].
  all: apply check_ret_only_ok_iff in Hspec; rewrite HZ in Hspec;
       destruct Hspec as (-> & -> & ->);
       split; [left; reflexivity|split; reflexivity].
Qed.

(** And a 0 return on a positive-count stdin read really does mean the
    input is exhausted: it is only admissible at [IEof].  Together with
    the lemma above this is the sticky-EOF property — once a read reports
    end-of-file, no later read can deliver a byte. *)

Lemma read_eof_is_sticky : forall fd buf count i m ch eff m' evs,
  fd_lookup (m_fds m) fd = Some (FdChannel ch) ->
  ch = 0 ->
  (0 < bv_unsigned count)%Z ->
  read_spec fd buf count i m (Ok eff m' evs) ->
  eff_ret eff = 0 ->
  m_stdin m = IEof /\ m_stdin m' = IEof.
Proof.
  intros fd buf count i m ch eff m' evs Hfd Hch Hcount Hspec Hret. subst ch.
  apply check_read_complete_ok in Hspec.
  unfold check_read in Hspec. rewrite Hfd in Hspec. cbv iota in Hspec.
  change (negb (w_is0 0)) with false in Hspec. cbv iota in Hspec.
  destruct (negb (access_okb buf (bv_unsigned count))); cbv iota in Hspec.
  { (* the range is refused: only -EFAULT, and [Hret] says the return
       was 0 *)
    apply check_ret_only_ok_iff in Hspec. destruct Hspec as (-> & _ & _).
    cbn in Hret. apply (f_equal bv_unsigned) in Hret. vm_compute in Hret.
    discriminate Hret. }
  assert (Hc : w_is0 count = false).
  { unfold w_is0, bv_eqb. apply Z.eqb_neq.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia. }
  rewrite Hc in Hspec. cbv iota in Hspec.
  destruct (m_stdin m) as [|b0 s0] eqn:He; cbv iota in Hspec.
  - (* already at end of input: the read changes nothing *)
    apply check_ret_only_ok_iff in Hspec.
    destruct Hspec as (_ & <- & _). split; [reflexivity | exact He].
  - (* input available: a 0 return is impossible (the delivery is nonempty) *)
    exfalso.
    destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
      cbv iota in Hspec.
    2: { (* not one byte of the destination can be written: the read is
            -EFAULT, which is not a 0 return either *)
      apply check_ret_only_ok_iff in Hspec. destruct Hspec as (-> & _ & _).
      cbn in Hret. apply (f_equal bv_unsigned) in Hret. vm_compute in Hret.
      discriminate Hret. }
    destruct (read_bytes_map (in_wmem i) buf
                (len_word (fst (stream_take_z (ICons b0 s0) (rw_count_clamp count)))))
      as [wn|] eqn:Hwn; cbv iota in Hspec; [|discriminate Hspec].
    destruct eff as [ret ws zs us cs copyins]. cbn in Hret. subst ret.
    destruct ws as [|[a bs] [|w' ws']]; destruct zs as [|z zs'];
      destruct us as [|u us']; destruct cs as [|c cs'];
      destruct copyins as [|copyin copyins'];
      cbv iota in Hspec; try discriminate Hspec.
    destruct (bv_eqb a buf && bv_eqb 0 (len_word bs)
              && (1 <=? Z.of_nat (length bs))%Z
              && (Z.of_nat (length bs) <=? rw_count_clamp count)%Z
              && listN_eqb (fst (stream_take (ICons b0 s0) (length bs))) bs
              && wmem_ok i buf (len_word bs)) eqn:Hcond;
      cbv iota in Hspec; [|discriminate Hspec].
    apply andb_true_iff in Hcond as [Hcond _].
    apply andb_true_iff in Hcond as [Hcond _].
    apply andb_true_iff in Hcond as [Hcond Hle].
    apply andb_true_iff in Hcond as [Hcond Hge1].
    apply andb_true_iff in Hcond as [_ H0].
    apply bv_eqb_eq in H0.
    apply Z.leb_le in Hge1. apply Z.leb_le in Hle.
    pose proof (rw_count_clamp_range count) as Hclr.
    unfold MAX_RW_COUNT in Hclr.
    pose proof (word_unsigned_range count) as Hcr. unfold two_pow_64 in Hcr.
    apply (f_equal bv_unsigned) in H0. unfold len_word in H0.
    rewrite Z_to_bv_unsigned in H0.
    rewrite bv_wrap_small in H0
      by (unfold bv_modulus; change (Z.of_N 64) with 64%Z; lia).
    change (bv_unsigned (0 : word)) with 0%Z in H0. lia.
Qed.

(** A stdin read delivers exactly a prefix of the INPUT STREAM: the
    delivered bytes are determined by the input, not chosen by the
    environment, and the stream advances past exactly them.  This is what
    makes a program's behavior a function of its input. *)

Lemma read_delivers_stream_prefix : forall fd buf count i m ch eff m' evs,
  fd_lookup (m_fds m) fd = Some (FdChannel ch) ->
  ch = 0 ->
  read_spec fd buf count i m (Ok eff m' evs) ->
  forall a bs, eff_writes eff = [(a, bs)] ->
  fst (stream_take (m_stdin m) (length bs)) = bs
  /\ m_stdin m' = snd (stream_take (m_stdin m) (length bs))
  /\ evs = map (ReadEv 0) bs.
Proof.
  intros fd buf count i m ch eff m' evs Hfd Hch Hspec a bs Hws. subst ch.
  apply check_read_complete_ok in Hspec.
  unfold check_read in Hspec. rewrite Hfd in Hspec. cbv iota in Hspec.
  change (negb (w_is0 0)) with false in Hspec. cbv iota in Hspec.
  destruct (negb (access_okb buf (bv_unsigned count))); cbv iota in Hspec.
  { (* the range is refused: only -EFAULT, which delivers nothing —
       against [Hws]'s singleton ledger *)
    apply check_ret_only_ok_iff in Hspec. destruct Hspec as (-> & _ & _).
    discriminate Hws. }
  (* neither the zero-count arm nor end of input delivers a byte *)
  assert (Hnodel : forall k, check_ret_only eff (Z_to_bv 64 0) m k = CheckOk m' evs ->
                   eff_writes eff = []).
  { intros k Hz. apply check_ret_only_ok_iff in Hz. destruct Hz as (-> & _ & _).
    reflexivity. }
  destruct (w_is0 count) eqn:Hc; cbv iota in Hspec.
  - rewrite (Hnodel _ Hspec) in Hws. discriminate Hws.
  - destruct (m_stdin m) as [|b0 s0] eqn:He; cbv iota in Hspec.
    + rewrite (Hnodel _ Hspec) in Hws. discriminate Hws.
    + destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1;
        cbv iota in Hspec.
      2: { (* nothing writable: -EFAULT delivers no bytes at all *)
        apply check_ret_only_ok_iff in Hspec.
        destruct Hspec as (Heff & _ & _). subst eff. discriminate Hws. }
      destruct (read_bytes_map (in_wmem i) buf
                  (len_word (fst (stream_take_z (ICons b0 s0) (rw_count_clamp count)))))
        as [wn|] eqn:Hwn; cbv iota in Hspec; [|discriminate Hspec].
      destruct eff as [ret ws zs us cs copyins]. cbn in Hws. subst ws.
      destruct zs as [|z zs']; destruct us as [|u us'];
        destruct cs as [|c cs']; destruct copyins as [|copyin copyins'];
        cbv iota in Hspec; try discriminate Hspec.
      destruct (bv_eqb a buf && bv_eqb ret (len_word bs)
                && (1 <=? Z.of_nat (length bs))%Z
                && (Z.of_nat (length bs) <=? rw_count_clamp count)%Z
                && listN_eqb (fst (stream_take (ICons b0 s0) (length bs))) bs
                && wmem_ok i buf (len_word bs)) eqn:Hcond;
        cbv iota in Hspec; [|discriminate Hspec].
      apply andb_true_iff in Hcond as [Hcond _].
      apply andb_true_iff in Hcond as [_ Hpre].
      apply listN_eqb_eq in Hpre.
      injection Hspec as Hm Hev. subst m' evs.
      split; [exact Hpre | split; reflexivity].
Qed.

(** The [MAX_RW_COUNT] clamp on the scalar read.  The clamp's content
    is pinned here (Checks/Examples.v's third reason: a model CONSTANT
    no observation of a real execution reveals).  Two directions.

    First the bound itself: whatever the count and however long the
    file or stream, no admissible read outcome delivers more than
    [MAX_RW_COUNT] bytes. *)

Lemma file_read_clamped_len : forall data off count,
  (Z.of_nat (length (file_read data off (Z_to_bv 64 (rw_count_clamp count))))
   <= MAX_RW_COUNT)%Z.
Proof.
  intros data off count.
  rewrite file_read_unguarded, length_firstn.
  pose proof (rw_count_clamp_range count) as Hr.
  assert (Hu : bv_unsigned (Z_to_bv 64 (rw_count_clamp count))
               = rw_count_clamp count).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    unfold bv_modulus. change (Z.of_N 64) with 64%Z.
    unfold MAX_RW_COUNT in Hr. lia. }
  unfold word_to_nat. rewrite Hu.
  rewrite Nat2Z.inj_min. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma read_delivery_clamped : forall fd buf count i m eff m' evs a bs,
  read_spec fd buf count i m (Ok eff m' evs) ->
  eff_writes eff = [(a, bs)] ->
  (Z.of_nat (length bs) <= MAX_RW_COUNT)%Z.
Proof.
  intros fd buf count i m eff m' evs a bs Hspec Hws.
  apply check_read_complete_ok in Hspec.
  unfold check_read in Hspec.
  (* every non-delivering answer carries an empty write list, which
     [Hws]'s singleton refutes; the two delivering arms carry the bound
     in their own checks *)
  assert (Hro : forall v mk evs' (H : check_ret_only eff v mk evs'
                                      = CheckOk m' evs), False).
  { intros v mk evs' H. apply check_ret_only_ok_iff in H.
    destruct H as (-> & _ & _). discriminate Hws. }
  (* generic in the RETURN VALUE, because the socket arms reach this
     shape with -ENOTCONN where the channel and file arms reach it with
     0.  Nothing in the proof depended on the 0. *)
  assert (Hnodel : forall v mk mk2 k,
             check_access_ok_zero buf count eff mk
               (check_ret_only eff v mk2 k) = CheckOk m' evs ->
             False).
  { intros v mk mk2 k Hz. unfold check_access_ok_zero in Hz.
    destruct (access_okb buf (bv_unsigned count)); cbv iota in Hz;
      exact (Hro _ _ _ Hz). }
  (* the one-shot -ECONNRESET, or -ETIMEDOUT or a soft error
     ([check_socket_pending_error]): an errno, so no write either *)
  assert (Hpend : forall e more fd' after,
             check_socket_pending_error e more fd' after buf count i eff m
             = CheckOk m' evs -> False).
  { intros e more fd' after Hz.
    unfold check_socket_pending_error, check_access_ok_zero in Hz.
    destruct (access_okb buf (bv_unsigned count)); cbv iota in Hz;
      [ apply check_pending_errno_ok in Hz; destruct Hz as (e' & _ & -> & _);
        discriminate Hws
      | exact (Hro _ _ _ Hz) ]. }
  (* Every [State.FdEntry] constructor, not only the files: [FdSocket] delivers
     too, and so does a pipe READ end, a stream-pair end and an O_RDWR file,
     so each gets a bullet rather than a one-line dismissal.  The two
     write-only kinds ([FdFileW] and the append [FdFileA]) are the -EBADF
     pair. *)
  destruct (fd_lookup (m_fds m) fd)
    as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |sid side st|ctx|fam]|] eqn:Hfd;
    cbv iota in Hspec;
    [ | | now destruct (Hro _ _ _ Hspec)
      | now destruct (Hro _ _ _ Hspec)
      |
      | destruct (negb (access_okb buf (bv_unsigned count))); cbv iota in Hspec;
        now destruct (Hro _ _ _ Hspec)
      | |
      | destruct (negb rd); cbv iota in Hspec;
        [ now destruct (Hro _ _ _ Hspec) | now destruct (Hnodel _ _ _ _ Hspec) ]
      | (* /dev/urandom: the access mode, the range verdict, then a
           delivery of exactly [count] bytes, which the count gate keeps
           under the clamp *)
        repeat (match type of Hspec with
                | (if ?b then _ else _) = _ => destruct b; cbv iota in Hspec
                end);
        first [ now destruct (Hro _ _ _ Hspec)
              | exact (check_read_urandom_delivery_clamped _ _ _ _ _ _ _ _ _ Hspec Hws) ]
      | (* stream-pair end: the range verdict, the zero count, then a
           delivery of [pipe_take] of the queue at the clamped count *)
        destruct (negb (access_okb buf (bv_unsigned count))); cbv iota in Hspec;
          [ now destruct (Hro _ _ _ Hspec) | ];
        destruct (w_is0 count); cbv iota in Hspec;
          [ now destruct (Hro _ _ _ Hspec)
          | exact (check_stream_read_delivery_clamped
                     _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hspec Hws) ]
      | (* eventfd: the range verdict, then the eight bytes of the count *)
        destruct (negb (access_okb buf (bv_unsigned count))); cbv iota in Hspec;
          [ now destruct (Hro _ _ _ Hspec)
          | exact (check_eventfd_read_delivery_clamped
                     _ _ _ _ _ _ _ _ _ _ _ Hspec Hws) ]
      | (* datagram socket: declined, never an [Ok] *)
        discriminate Hspec
      | now destruct (Hro _ _ _ Hspec) ].
  - (* channel *)
    destruct (negb (w_is0 ch)); cbv iota in Hspec;
      [now destruct (Hro _ _ _ Hspec)|].
    destruct (negb (access_okb buf (bv_unsigned count))); cbv iota in Hspec;
      [now destruct (Hro _ _ _ Hspec)|].
    destruct (w_is0 count); cbv iota in Hspec;
      [now destruct (Hro _ _ _ Hspec)|].
    destruct (m_stdin m) as [|b0 s0]; cbv iota in Hspec;
      [now destruct (Hro _ _ _ Hspec)|].
    destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)); cbv iota in Hspec;
      [|now destruct (Hro _ _ _ Hspec)].
    destruct (read_bytes_map (in_wmem i) buf
              (len_word (fst (stream_take_z (ICons b0 s0) (rw_count_clamp count)))));
      cbv iota in Hspec; [|discriminate Hspec].
    destruct eff as [ret ws zs us cs copyins]. cbn in Hws. subst ws.
    destruct zs; destruct us; destruct cs; destruct copyins;
      cbv iota in Hspec; try discriminate Hspec.
    destruct (bv_eqb a buf && bv_eqb ret (len_word bs)
              && (1 <=? Z.of_nat (length bs))%Z
              && (Z.of_nat (length bs) <=? rw_count_clamp count)%Z
              && listN_eqb (fst (stream_take (ICons b0 s0) (length bs))) bs
              && wmem_ok i buf (len_word bs)) eqn:Hcond;
      cbv iota in Hspec; [|discriminate Hspec].
    apply andb_true_iff in Hcond as [Hcond _].
    apply andb_true_iff in Hcond as [Hcond _].
    apply andb_true_iff in Hcond as [Hcond Hle].
    apply Z.leb_le in Hle.
    pose proof (rw_count_clamp_range count) as Hr. lia.
  - (* file *)
    destruct (negb (access_okb buf (bv_unsigned count))); cbv iota in Hspec;
      [now destruct (Hro _ _ _ Hspec)|].
    destruct (rw_pos_einvalb off (bv_unsigned count)); cbv iota in Hspec;
      [now destruct (Hro _ _ _ Hspec)|].
    cbv zeta in Hspec. set (data := fs_ino_data (m_fs m) p) in Hspec.
    destruct (file_read data off (Z_to_bv 64 (rw_count_clamp count)))
      as [|b bsr] eqn:Hbs; cbv iota in Hspec.
    + destruct (read_bytes_map (in_wmem i) buf (len_word ([] : list byte)));
        cbv iota in Hspec.
      * now destruct (Hro _ _ _ Hspec).
      * destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1));
          cbv iota in Hspec;
          [discriminate|now destruct (Hro _ _ _ Hspec)].
    + destruct (read_bytes_map (in_wmem i) buf (len_word (b :: bsr)));
        cbv iota in Hspec.
      2: { destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1));
             cbv iota in Hspec;
             [discriminate|now destruct (Hro _ _ _ Hspec)]. }
      destruct eff as [ret ws zs us cs copyins]. cbn in Hws. subst ws.
      destruct zs; destruct us; destruct cs; destruct copyins;
        cbv iota in Hspec; try discriminate Hspec.
      destruct (bv_eqb a buf && listN_eqb bs (b :: bsr)
                && bv_eqb ret (len_word (b :: bsr))) eqn:Hcond;
        cbv iota in Hspec; [|discriminate Hspec].
      apply andb_true_iff in Hcond as [Hcond _].
      apply andb_true_iff in Hcond as [_ Hbs'].
      apply listN_eqb_eq in Hbs'. subst bs.
      pose proof (file_read_clamped_len data off count) as Hl.
      rewrite Hbs in Hl. exact Hl.
  - (* the same file opened O_RDWR: the file bullet above *)
    destruct (negb (access_okb buf (bv_unsigned count))); cbv iota in Hspec;
      [now destruct (Hro _ _ _ Hspec)|].
    destruct (rw_pos_einvalb off (bv_unsigned count)); cbv iota in Hspec;
      [now destruct (Hro _ _ _ Hspec)|].
    cbv zeta in Hspec. set (data := fs_ino_data (m_fs m) p) in Hspec.
    destruct (file_read data off (Z_to_bv 64 (rw_count_clamp count)))
      as [|b bsr] eqn:Hbs; cbv iota in Hspec.
    + destruct (read_bytes_map (in_wmem i) buf (len_word ([] : list byte)));
        cbv iota in Hspec.
      * now destruct (Hro _ _ _ Hspec).
      * destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1));
          cbv iota in Hspec;
          [discriminate|now destruct (Hro _ _ _ Hspec)].
    + destruct (read_bytes_map (in_wmem i) buf (len_word (b :: bsr)));
        cbv iota in Hspec.
      2: { destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1));
             cbv iota in Hspec;
             [discriminate|now destruct (Hro _ _ _ Hspec)]. }
      destruct eff as [ret ws zs us cs copyins]. cbn in Hws. subst ws.
      destruct zs; destruct us; destruct cs; destruct copyins;
        cbv iota in Hspec; try discriminate Hspec.
      destruct (bv_eqb a buf && listN_eqb bs (b :: bsr)
                && bv_eqb ret (len_word (b :: bsr))) eqn:Hcond;
        cbv iota in Hspec; [|discriminate Hspec].
      apply andb_true_iff in Hcond as [Hcond _].
      apply andb_true_iff in Hcond as [_ Hbs'].
      apply listN_eqb_eq in Hbs'. subst bs.
      pose proof (file_read_clamped_len data off count) as Hl.
      rewrite Hbs in Hl. exact Hl.
  - (* socket.  The delivery arm bounds the prefix by
       [State.rw_count_clamp] of the count, exactly as the channel and
       file arms do, so the bound is the clamp's own range and not a gap
       between two constants. *)
    destruct (negb (modeled_rw_range buf count)) eqn:Emrc; cbv iota in Hspec;
      [discriminate|].
    destruct (w_is0 count); cbv iota in Hspec;
      [now destruct (Hnodel _ _ _ _ Hspec)|].
    destruct sk as [| | |peer ch rx|peer ch rx pending bound]; cbv iota in Hspec;
      try (now destruct (Hnodel _ _ _ _ Hspec)).
    (* a connection, and a reset one whose queue is still read: the same
       delivery arm on each, so one script closes both *)
    all: destruct rx as [| | |b0 s0];
      [ | try destruct pending | try destruct pending | ]; cbv iota in Hspec;
      try (now destruct (Hnodel _ _ _ _ Hspec));
      try (now destruct (Hpend _ _ _ _ Hspec)).
    all: (
    (* [vfs_read]'s [access_ok] on the named count: -EFAULT delivers nothing *)
    destruct (negb (access_okb buf (bv_unsigned count))); cbv iota in Hspec;
      [now destruct (Hro _ _ _ Hspec)|];
    destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)); cbv iota in Hspec;
      [|now destruct (Hro _ _ _ Hspec)];
    destruct (read_bytes_map (in_wmem i) buf
              (len_word (fst (net_take_z (NCons b0 s0) (rw_count_clamp count)))));
      cbv iota in Hspec; [|discriminate Hspec];
    destruct eff as [ret ws zs us cs copyins]; cbn in Hws; subst ws;
    destruct zs; destruct us; destruct cs; destruct copyins;
      cbv iota in Hspec; try discriminate Hspec;
    destruct (bv_eqb a buf && bv_eqb ret (len_word bs)
              && (1 <=? Z.of_nat (length bs))%Z
              && (Z.of_nat (length bs) <=? rw_count_clamp count)%Z
              && listN_eqb (fst (net_take (NCons b0 s0) (length bs))) bs
              && wmem_ok i buf (len_word bs)) eqn:Hcond;
      cbv iota in Hspec; [|discriminate Hspec];
    apply andb_true_iff in Hcond as [Hcond _];
    apply andb_true_iff in Hcond as [Hcond _];
    apply andb_true_iff in Hcond as [_ Hle];
    apply Z.leb_le in Hle;
    pose proof (rw_count_clamp_range count); lia).
  - (* pipe read end: the third delivering arm, after the channel and
       the file, and its bound is the clamp's too.  The
       delivery is [State.pipe_take q (rw_count_clamp count)], whose
       length [State.pipe_take_length] bounds by the clamped count, and
       [State.rw_count_clamp_range] bounds that by [MAX_RW_COUNT].

       THE BOUND IS TIGHT: it is the clamp's own range, not a gap
       between two constants. *)
    destruct w; cbv iota in Hspec; [now destruct (Hro _ _ _ Hspec)|].
    destruct (negb (modeled_rw_range buf count)) eqn:Hmc; cbv iota in Hspec;
      [discriminate|].
    destruct (w_is0 count); cbv iota in Hspec;
      [now destruct (Hnodel _ _ _ _ Hspec)|].
    destruct (pipe_lookup (m_pipes m) id) as [[q used]|]; cbv iota in Hspec;
      [|discriminate].
    destruct q as [|b q0]; cbv iota in Hspec.
    { destruct (pipe_end_live (m_fds m) id true); cbv iota in Hspec;
        [discriminate|now destruct (Hnodel _ _ _ _ Hspec)]. }
    cbv zeta in Hspec.
    destruct (negb (access_okb buf (bv_unsigned count))); cbv iota in Hspec;
      [now destruct (Hro _ _ _ Hspec)|].
    destruct (read_bytes_map (in_wmem i) buf
                (len_word (pipe_take (b :: q0) (rw_count_clamp count))));
      cbv iota in Hspec.
    2: { destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1));
           cbv iota in Hspec;
           [discriminate|now destruct (Hro _ _ _ Hspec)]. }
    destruct eff as [ret ws zs us cs copyins]. cbn in Hws. subst ws.
    destruct zs; destruct us; destruct cs; destruct copyins;
      cbv iota in Hspec; try discriminate Hspec.
    destruct (writes_eqb [(a, bs)]
                (delivered_writes buf (pipe_take (b :: q0) (rw_count_clamp count)))
              && bv_eqb ret
                   (len_word (pipe_take (b :: q0) (rw_count_clamp count)))) eqn:Hcond;
      cbv iota in Hspec; [|discriminate Hspec].
    apply andb_true_iff in Hcond as [Hcond _].
    apply writes_eqb_eq in Hcond.
    destruct (pipe_take (b :: q0) (rw_count_clamp count)) as [|d ds] eqn:Hdel;
      cbn in Hcond; [discriminate|].
    inversion Hcond as [[Ha Hbs']]. subst bs.
    assert (Hlen : (Z.of_nat (length (d :: ds))
                    <= Z.max 0 (rw_count_clamp count))%Z).
    { rewrite <- Hdel. apply pipe_take_length. }
    pose proof (rw_count_clamp_range count). lia.
Qed.

(** ...and the rejecting direction: the specific lie no kernel in scope
    can tell — the FULL count acknowledged, with the full payload, where
    the count is one past the clamp and the file holds every byte of it
    past the offset.  End of file is ruled out ([Heof]), and the
    destination is writable for the whole count ([Hwall]), so the clamp
    is the only thing that makes the model's delivery shorter than the
    count: a checker without the clamp would deliver exactly this effect
    and accept it.  [Hwall] is what makes that so, not what the proof
    below uses.  The verdict is [CheckReject]: rejected, not merely
    unwitnessed. *)
Lemma read_ret_over_clamp_rejected : forall i m fd p data buf count off w w',
  fd_lookup (m_fds m) fd = Some (FdFile p off) ->
  fs_ino_data (m_fs m) p = data ->
  bv_unsigned count = (MAX_RW_COUNT + 1)%Z ->
  (* the range passes [access_ok], and the position test after it: the
     clamp is only reached past both *)
  access_okb buf (bv_unsigned count) = true ->
  rw_pos_einvalb off (bv_unsigned count) = false ->
  (* no end of file before the count: the file holds every byte named *)
  (bv_unsigned off + bv_unsigned count <= Z.of_nat (length data))%Z ->
  read_bytes_map (in_wmem i) buf
    (len_word (file_read data off (Z_to_bv 64 (rw_count_clamp count))))
    = Some w ->
  (* the destination is writable for the whole count, so no unwritable
     byte past the clamp can be what refuses the full payload *)
  read_bytes_map (in_wmem i) buf (len_word (file_read data off count)) = Some w' ->
  check_read i fd buf count
    (mkEffect count [(buf, file_read data off count)] []) m
  = CheckReject.
Proof.
  intros i m fd p data buf count off w w' Hfd Hfs Hc Hok Hpos Heof Hw Hwall.
  unfold check_read. rewrite Hfd, Hok. cbv beta iota zeta.
  rewrite Hpos. cbv beta iota zeta.
  rewrite Hfs.
  destruct (file_read data off (Z_to_bv 64 (rw_count_clamp count)))
    as [|b bsr] eqn:Hbs.
  { (* the clamped delivery is not empty: the file holds the clamp's
       bytes past [off] *)
    exfalso. rewrite file_read_unguarded in Hbs.
    apply (f_equal (@length byte)) in Hbs.
    rewrite length_firstn, length_skipn in Hbs. cbn [length] in Hbs.
    unfold word_to_nat in Hbs. rewrite rw_count_clamp_word in Hbs.
    unfold rw_count_clamp in Hbs. rewrite Hc in Hbs.
    pose proof (bv_unsigned_in_range 64 off) as Hoff.
    unfold MAX_RW_COUNT in *. lia. }
  rewrite <- Hbs in *. rewrite Hw. cbv beta iota.
  rewrite Hbs. cbv beta iota.
  (* the return is the raw count; the admissible one is the clamped
     delivery's length, which the clamp holds strictly below it *)
  assert (Hlen : (Z.of_nat (length (b :: bsr)) <= MAX_RW_COUNT)%Z).
  { pose proof (file_read_clamped_len data off count) as Hl.
    rewrite Hbs in Hl. exact Hl. }
  assert (Hne' : bv_eqb count (len_word (b :: bsr)) = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Hc.
    unfold len_word. rewrite Z_to_bv_unsigned, bv_wrap_small;
      [ lia
      | unfold bv_modulus; change (Z.of_N 64) with 64%Z;
        unfold MAX_RW_COUNT in Hlen; lia ]. }
  rewrite Hne', !Bool.andb_false_r. reflexivity.
Qed.

(** For a raw count within [IOV_MAX] the 32-bit truncation is the
    identity. *)

Lemma write_channel_outcome : forall fd buf count i m ch bs eff m' evs,
  fd_lookup (m_fds m) fd = Some (FdChannel ch) ->
  ch <> 0 ->
  (* the far end has a reader.  Not a modelling shortcut and not the
     model assuming one: with the reader gone [ReadWrite.write_spec]'s
     channel arm answers -EPIPE and raises SIGPIPE, which KILLS the
     process under the default disposition, so no delivery is
     admissible there *)
  m_channel_reader m = true ->
  (* at or below [rw_bytes_max] the clamp inside [Uaccess.write_source]
     is the identity; see [Uaccess.modeled_rw_range] *)
  (bv_unsigned count <= rw_bytes_max)%Z ->
  read_bytes_map (in_mem i) buf count = Some bs ->
  (* THE RANGE [vfs_write]'s [access_ok] ACCEPTS, a premise this lemma
     did not used to carry.  Without it the statement was true of a
     channel arm that judged a write by its readable prefix and is false
     of one that asks [access_ok] first: a [buf] whose bytes the memory
     backs past [State.TASK_SIZE], or round the top of the address space
     by wrapping, is now -EFAULT, which delivers nothing.  So this repairs
     a statement that had become false; it is not a weakening.  It is
     [buf + count <= TASK_SIZE] by [Uaccess.access_okb_intro] *)
  access_okb buf (bv_unsigned count) = true ->
  bs <> [] ->
  write_spec fd buf count i m (Ok eff m' evs) ->
  (Z.of_nat (length bs) <= rw_bytes_max)%Z
  /\ exists n, (1 <= n)%nat /\ (n <= length bs)%nat
  /\ eff = with_copyins [(buf, n)]
       (mkEffect (len_word (firstn n bs)) [] []) /\ m' = m
  /\ evs = map (WriteEv ch) (firstn n bs).
Proof.
  intros fd buf count i m ch bs eff m' evs Hfd Hch Hrdr Hmax Hb Hok Hnonempty Hspec.
  apply check_write_complete_ok in Hspec.
  unfold check_write in Hspec. rewrite Hfd in Hspec. cbv iota in Hspec.
  assert (Hch0 : w_is0 ch = false).
  { unfold w_is0, bv_eqb. apply Z.eqb_neq. intro Heq. apply Hch, bv_eq.
    rewrite Heq. reflexivity. }
  rewrite Hch0 in Hspec. cbv iota in Hspec.
  rewrite (rw_range_in_range _ _ Hmax) in Hspec. cbv iota in Hspec.
  pose proof (read_bytes_map_length _ _ _ _ Hb) as Hlen.
  assert (Hbnd : (Z.of_nat (length bs) <= rw_bytes_max)%Z) by lia.
  split; [exact Hbnd|].
  assert (Hlpos : (0 < length bs)%nat)
    by (destruct bs; [congruence|cbn; lia]).
  assert (Hc : w_is0 count = false).
  { unfold w_is0, bv_eqb. apply Z.eqb_neq.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia. }
  rewrite Hc in Hspec. cbv iota zeta in Hspec.
  rewrite Hok in Hspec. cbn [negb] in Hspec. cbv iota in Hspec.
  rewrite Hrdr in Hspec. change (negb true) with false in Hspec.
  cbv iota zeta in Hspec.
  rewrite (write_source_of_rw _ _ _ Hmax),
          (readable_bytes_full _ _ _ _ Hb) in Hspec.
  assert (Hg0 : Nat.eqb (length bs) 0 = false) by (apply Nat.eqb_neq; lia).
  rewrite Hg0 in Hspec. cbv iota in Hspec.
  destruct eff as [ret ws zs us cs copyins]; destruct ws as [|? ?];
    destruct zs as [|? ?]; destruct us as [|? ?];
      destruct cs as [|? ?]; try discriminate.
  destruct ((1 <=? bv_unsigned ret)%Z
            && (bv_unsigned ret <=? Z.of_nat (length bs))%Z) eqn:Hgr.
  2:{ (* a wholly readable source has no fault inside its first copy, so
         the -EFAULT the arm admits beside the delivery is not reached *)
      exfalso. cbv beta iota in Hspec.
      assert (Hx : (Z.of_nat (length bs) <? rw_count_clamp count)%Z = false).
      { apply Z.ltb_ge. unfold rw_count_clamp, MAX_RW_COUNT.
        unfold rw_bytes_max in Hmax. lia. }
      unfold fault_in_first_copyb in Hspec. rewrite Hx in Hspec.
      cbn [andb] in Hspec. rewrite Bool.andb_false_r in Hspec.
      cbv beta iota in Hspec. discriminate Hspec. }
  destruct (access_ranges_eqb copyins [(buf, Z.to_nat (bv_unsigned ret))])
    eqn:Hreads; [|discriminate].
  inversion Hspec; clear Hspec; subst.
  apply andb_true_iff in Hgr as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  apply access_ranges_eqb_eq in Hreads. subst copyins.
  pose proof (word_unsigned_range ret) as Hr.
  exists (Z.to_nat (bv_unsigned ret)).
  assert (Hlw : len_word (firstn (Z.to_nat (bv_unsigned ret)) bs) = ret)
    by (apply len_word_firstn_ret; lia).
  rewrite Hlw. repeat split; try reflexivity; lia.
Qed.

(** The headline property, short writes included: on the same model, an
    admissible channel-writev outcome whose gathered bytes equal the
    readable contents of a write's flat buffer determines an admissible
    outcome of that write — same return, same post-model, same per-byte
    events, with only [eff_copyins] replaced by the flat-buffer range.
    (And hence, byte-level events erasing chunking — see part 3 — its
    events are also events of the per-iovec SEQUENCE of writes.  This
    is why musl's stdio flushing through writev costs nothing.)

    Inherits [writev_channel_outcome]'s import premise: the iovec array
    has to import cleanly ([ImpOk]), which readability alone does not
    give — a descriptor whose length is negative as [ssize_t] is
    -EINVAL, and there is no writev outcome to place. *)

Example write_ab_events :
  check_syscall (mkInput 64 [1; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
    (with_copyins [(4096, 2%nat)] (mkEffect 2 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) [WriteEv 1 97; WriteEv 1 98].
Proof. check_eq. Qed.

(** The same write("ab") may deliver only "a" — a SHORT channel write,
    the environment's choice: ret 1 with one event for the delivered
    byte is admissible.  What is NOT admissible: delivering more than
    was readable-and-requested (ret 3), and a zero-byte delivery of a
    nonzero request (a blocked pipe blocks; it does not return 0). *)

Example write_ab_short_delivery :
  check_syscall (mkInput 64 [1; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
    (with_copyins [(4096, 1%nat)] (mkEffect 1 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) [WriteEv 1 97]
  /\ check_syscall (mkInput 64 [1; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
       (with_copyins [(4096, 3%nat)] (mkEffect 3 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckReject
  /\ check_syscall (mkInput 64 [1; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
       (with_copyins [(4096, 0%nat)] (mkEffect 0 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckReject.
Proof. split; [|split]; check_eq. Qed.

(** ...produces exactly the events of write("a"); write("b"): the trace
    cannot tell the syscall chunking apart, which is the point of
    byte-granularity events.  (Channel writes do not change the model,
    so both writes run from [init_model].) *)

Example write_a_then_b_events :
  check_syscall (mkInput 64 [1; 4096; 1; 0; 0; 0] mem_ab (fun _ => None))
    (with_copyins [(4096, 1%nat)] (mkEffect 1 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) [WriteEv 1 97]
  /\ check_syscall (mkInput 64 [1; 4097; 1; 0; 0; 0] mem_ab (fun _ => None))
       (with_copyins [(4097, 1%nat)] (mkEffect 1 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) [WriteEv 1 98].
Proof. split; check_eq. Qed.

(** Concretely for writev: [mem_ab] plus an iovec array at 8192
    splitting "ab" into two single-byte iovecs {4096,1},{4097,1} (LP64
    iovec layout: 8-byte little-endian base then length). *)

Example read_bad_fd_ebadf :
  check_syscall (mkInput 63 [5; 4096; 16; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EBADF) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) [].
Proof. check_eq. Qed.

Example read_bad_fd_success_rejected :
  check_syscall (mkInput 63 [5; 4096; 16; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 4 [(4096, [1; 2; 3; 4])] []) (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(* -------------------------------------------------------------------------
   munmap: length, alignment, and the ledger.  A model with one live
   4096-byte anonymous mapping at 65536.
   ------------------------------------------------------------------------- *)

Example write_fd_truncates_to_32_bits :
  check_syscall (mkInput 64 [Z_to_bv 64 (2 ^ 32 + 1); 4096; 2; 0; 0; 0]
                   mem_ab (fun _ => None))
    (with_copyins [(4096, 2%nat)] (mkEffect 2 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
  = check_syscall (mkInput 64 [1; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
      (with_copyins [(4096, 2%nat)] (mkEffect 2 [] []))
      (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
  /\ check_syscall (mkInput 64 [Z_to_bv 64 (2 ^ 32 + 1); 4096; 2; 0; 0; 0]
                     mem_ab (fun _ => None))
       (with_copyins [(4096, 2%nat)] (mkEffect 2 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) [WriteEv 1 97; WriteEv 1 98].
Proof. split; check_eq. Qed.

Example write_fd_high_bits_ebadf_rejected :
  check_syscall (mkInput 64 [Z_to_bv 64 (2 ^ 32 + 1); 4096; 2; 0; 0; 0]
                   mem_ab (fun _ => None))
    (with_copyins [(4096, 2%nat)] (mkEffect (errno_ret EBADF) [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
  = CheckReject.
Proof. check_eq. Qed.

(** read(2^32, buf, 16) is a read on STDIN: at end of input it returns 0,
    not -EBADF. *)

Example read_fd_truncates_to_32_bits :
  check_syscall (mkInput 63 [Z_to_bv 64 (2 ^ 32); 4096; 16; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) []
  /\ check_syscall (mkInput 63 [Z_to_bv 64 (2 ^ 32); 4096; 16; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** The dead-fd boundary sweep: 2^31 (INT_MIN as an [int]), 2^32 - 1
    (-1), and 2^64 - 1 all have low halves at or above 2^31, which no
    entry of a table capped at 4096 ([State.alloc_fd]) can match — so
    zero- and sign-extension of the low half agree on every one of them,
    which is what makes [fd32]'s zero-extension faithful. *)

(** THE SHARED WRITE GUARD IS SHARED, pinned once per file kind.

    [write_spec]'s three file arms -- the write-only one, the append one
    and the read-write one -- reach their count gate through ONE helper,
    [ReadWrite.write_range_gate].  Agreeing on the helper's NAME is not
    enough, and this example checks the ANSWER: a helper the arms agree
    on can still be given the wrong boundary, and no proof in this
    development relates the three arms.

    THIS IS THE TEST THAT NOTICES, and it is written as three claims
    rather than one because the thing at risk is precisely that the
    three stop being one thing.  A single example on a single kind would
    pass throughout the divergence it exists to catch.

    THE COUNT IS DERIVED FROM THE BOUND, not written as a literal:
    [Uaccess.rw_bytes_max] is the constant the guard reads, so moving it
    moves this example with it.  A literal 131073 would keep passing
    against a bound that had moved, which is the same failure one step
    removed.

    THE BUFFER IS AT THE TOP OF THE ADDRESS SPACE, and it has to be.
    The gate is the DISJUNCTION
    [modeled_rw_count count || access_okb buf count], so a count past
    [rw_bytes_max] at an ordinary mapped buffer is admitted by the right
    disjunct and declines on no kind at all.  Putting [buf] where
    [buf + count] passes [State.TASK_SIZE] switches the right disjunct
    off and leaves the count as the only thing that can admit the call,
    which is what makes this a test of the COUNT boundary.

    AND THAT IS ALSO WHY THE LAST THREE CONJUNCTS EXIST.  At [near_top]
    the disjunction and its LEFT disjunct alone agree at every count, so
    everything above is blind to an arm that gates on [modeled_rw_count]
    by itself.  The mapped buffer is where the two part, and
    the three answers there are what a re-acquired count gate would
    move.

    The file is present and the fd is open, so nothing else on any of
    the three arms can be what declines -- and the guard runs ahead of
    each arm's [access_ok] and [rw_verify_area] too, so the three
    really do meet here rather than at three different tests. *)
Example write_count_bound_declines_on_every_file_kind :
  let over := Z_to_bv 64 (rw_bytes_max + 1) in
  let at_bound := Z_to_bv 64 rw_bytes_max in
  let near_top := Z_to_bv 64 (TASK_SIZE - 4) in
  let unmod r := match r with CheckUnmodeled => true | _ => false end in
  let model_of (k : Fs.ino -> word -> FdEntry) : Model :=
    mkModel [(3, k 1%Z (Z_to_bv 64 0))] (mkVmMaps [] [] 0 0 demo_limit) IEof
      (demo_fs_raw [([102], SFile [104; 105])]) None None None in
  let call_at b n k := check_syscall
        (mkInput 64 [3; b; n; 0; 0; 0]
           (fun a => if bv_eqb a b then Some 122 else None)
           (fun _ => None))
        (with_copyins [(b, 1%nat)] (mkEffect 1 [] []))
        (model_of k) in
  let call n k := call_at near_top n k in
  call over FdFileW = CheckUnmodeled
  /\ call over FdFileA = CheckUnmodeled
  /\ call over FdFileRW = CheckUnmodeled
  (* ...and the SAME call at the bound itself declines on no kind, which
     is what stops the three claims above from holding for some reason of
     their own.  A count of [rw_bytes_max] is inside the gate's LEFT
     disjunct, so the call is admitted even though the buffer is not
     addressable -- and whatever each arm then answers, and the three
     answer differently because their middles differ, none of them
     answers [CheckUnmodeled].  Without this half the example would keep
     passing if an arm started declining for an unrelated reason, which
     is exactly the shape it exists to rule out. *)
  /\ unmod (call at_bound FdFileW) = false
  /\ unmod (call at_bound FdFileA) = false
  /\ unmod (call at_bound FdFileRW) = false
  (* ...AND THE SAME OVERSIZED COUNT AT A MAPPED BUFFER DECLINES ON NO
     KIND EITHER, which is the half that says WHICH disjunct is missing
     when one goes.  Above the bound the two candidate gates part company
     only here: [Uaccess.modeled_rw_count] alone would decline this call,
     the disjunction admits it through [access_okb].  Without these three
     the example would still pass on an arm with a [modeled_rw_count]
     gate of its own, because at [near_top] above the two agree at every
     count. *)
  /\ unmod (call_at (Z_to_bv 64 4096) over FdFileW) = false
  /\ unmod (call_at (Z_to_bv 64 4096) over FdFileA) = false
  /\ unmod (call_at (Z_to_bv 64 4096) over FdFileRW) = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** ...AND THE SECOND BOUNDARY, which is the one a change to the RANGE
    judgement moves.  The count guard above is not enough on its own:
    [Uaccess.modeled_rw_count] reads the count and nothing else, so a
    rewrite that folded the BUFFER into the shared guard would agree
    with it at every count and disagree only where [buf + count] crosses
    [State.TASK_SIZE].  A test that never puts a buffer there cannot
    tell the two apart, and would stay green through exactly the
    divergence it was written to catch.

    So this pins the three kinds at that address instead.  The three
    answers USED TO DIFFER: the append arm modeled [vfs_write]'s
    [access_ok] and refused a delivering write whose named range passes
    TASK_SIZE, while the write-only and read-write arms judged it by its
    readable prefix and delivered — a known divergence from Linux, and
    on a buffer straddling 2^64 a delivery of bytes the walk reached by
    wrapping.  All three now ask [access_ok] (fs/read_write.c,
    [vfs_write]), so all three refuse it, and that agreement is what
    this pins.

    WHAT THIS LINE IS FOR: a change to the shared range judgement has to
    come here and say what it did to all three.  Drop the [access_ok]
    from one arm, where it would look like tidying since [write_source]
    reads nothing past what the memory backs, and that arm's verdict
    below flips back to a delivery Linux refuses. *)
Example write_range_boundary_pins_the_three_file_kinds :
  let near_top := Z_to_bv 64 (TASK_SIZE - 4) in
  let small := Z_to_bv 64 8 in
  let model_of (k : Fs.ino -> word -> FdEntry) : Model :=
    mkModel [(3, k 1%Z (Z_to_bv 64 0))] (mkVmMaps [] [] 0 0 demo_limit) IEof
      (demo_fs_raw [([102], SFile [104; 105])]) None None None in
  let call k := check_syscall
        (mkInput 64 [3; near_top; small; 0; 0; 0]
           (fun a => if bv_eqb a near_top then Some 122 else None)
           (fun _ => None))
        (with_copyins [(near_top, 1%nat)] (mkEffect 1 [] []))
        (model_of k) in
  let verdict (r : check_result) : nat :=
    match r with
    | CheckOk _ _ => 0%nat | CheckReject => 1%nat | CheckUnmodeled => 2%nat
    end in
  (* the count is far inside [rw_bytes_max], so the guard pinned above is
     not what answers here *)
  verdict (call FdFileW) = 1%nat      (* access_ok: the delivering write is refused *)
  /\ verdict (call FdFileA) = 1%nat   (* access_ok, then rw_verify_area: refused *)
  /\ verdict (call FdFileRW) = 1%nat. (* the write-only arm's tests, so its answer *)
Proof. vm_compute. repeat split; reflexivity. Qed.

(** ...AND NO AGGREGATE BOUND OF THE MODEL'S OWN on [writev], pinned the
    same way.

    [writev_spec]'s file arms carry no gate declining an aggregate past
    [Uaccess.rw_bytes_max]: the import already clamps the aggregate at
    the kernel's own [State.MAX_RW_COUNT] ([State.cap_iovecs]), so a
    bound of the model's own in front of it would only narrow what is
    judged.  An arm that kept such a gate would decline on an O_RDWR
    descriptor an aggregate the same [writev] on an O_WRONLY descriptor
    delivers.  Not a wrong answer — a decline never is — but the same
    call judged by which descriptor it holds.

    THE THREE ANSWER ALIKE HERE.  The aggregate is one byte past
    [Uaccess.rw_bytes_max], DERIVED from it rather than spelled, so it
    moves if the constant does.  The source address is
    unmapped, so every kind gathers nothing and answers -EFAULT against a
    claimed length of 1; what this asserts is that none of them answers
    [CheckUnmodeled], which is exactly what such a gate would make an
    arm do.

    THE PIPE IS THE CONTROL.  A vectored write to a pipe declines for a
    reason of its own ([writev_buf_gap], the atomicity argument being per
    transfer rather than per vector), so [CheckUnmodeled] is reachable in
    this fixture and "not unmodeled" above is a fact about the file arms
    rather than about the shape of the call. *)
Example writev_aggregate_past_the_retired_bound_is_judged_by_every_file_kind :
  let iovbytes := word_le8 (Z_to_bv 64 4096)
                    ++ word_le8 (Z_to_bv 64 (rw_bytes_max + 1)) in
  let mem : word -> option byte :=
    fun a =>
      if bv_leu 8192 a && bv_ltu a 8208
      then nth_error iovbytes (Z.to_nat (bv_unsigned a - 8192))
      else None in
  let unmod r := match r with CheckUnmodeled => true | _ => false end in
  let call (e : FdEntry) := check_syscall
        (mkInput 66 [3; 8192; 1; 0; 0; 0] mem (fun _ => None))
        (mkEffect 1 [] [])
        (mkModel [(3, e)] (mkVmMaps [] [] 0 0 demo_limit) IEof
           (demo_fs_raw [([102], SFile [104; 105])]) None None None) in
  unmod (call (FdFileW 1 (Z_to_bv 64 0))) = false
  /\ unmod (call (FdFileRW 1 (Z_to_bv 64 0))) = false
  /\ unmod (call (FdFileA 1 (Z_to_bv 64 0))) = false
  /\ unmod (call (FdPipe (Z_to_bv 64 7) true)) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE KIND ANSWERS IN BOTH DIRECTIONS, which is the whole content of
    [State.FdFileRW], and the half no real run reaches is the REFUSAL: a
    kernel cannot make a read-write fd answer -EBADF to either
    direction, so the model must not admit one that claims to.  Both
    -EBADFs are the answer the OTHER two file kinds really give, which
    is what makes this the mistake a flag on [FdFileW] would have
    produced. *)
Example rdwr_fd_refuses_ebadf_in_either_direction :
  let m := mkModel [(3, FdFileRW 1 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
             (demo_fs_raw [([102], SFile [104; 105])]) None None None in
  check_syscall (mkInput 63 [3; 4096; 1; 0; 0; 0] (fun _ => None)
                   (fun a => if bv_eqb a 4096 then Some 0 else None))
    (mkEffect (errno_ret EBADF) [] []) m = CheckReject
  /\ check_syscall (mkInput 64 [3; 4096; 1; 0; 0; 0]
                      (fun a => if bv_eqb a 4096 then Some 122 else None)
                      (fun _ => None))
       (with_copyins [(4096, 1%nat)] (mkEffect (errno_ret EBADF) [] [])) m
     = CheckReject.
Proof. vm_compute. split; reflexivity. Qed.

(** ...and the positive half of the same claim, on ONE descriptor: the
    read moves the offset the WRITE then lands at.  A model that minted
    two independent positions, or that wrote the entry back under the
    read-only kind, gives "hz" here rather than "hz" at index 1 — the
    file below is "hi" with the second byte overwritten. *)
Example rdwr_read_then_write_shares_one_offset :
  let m := mkModel [(3, FdFileRW 1 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
             (demo_fs_raw [([102], SFile [104; 105])]) None None None in
  match check_syscall (mkInput 63 [3; 4096; 1; 0; 0; 0] (fun _ => None)
                         (fun a => if bv_eqb a 4096 then Some 0 else None))
          (mkEffect 1 [(4096, [104])] []) m with
  | CheckOk m1 [] =>
      fd_lookup (m_fds m1) 3 = Some (FdFileRW 1 1)
      /\ match check_syscall
                 (mkInput 64 [3; 4096; 1; 0; 0; 0]
                    (fun a => if bv_eqb a 4096 then Some 122 else None)
                    (fun _ => None))
                 (with_copyins [(4096, 1%nat)] (mkEffect 1 [] [])) m1 with
         | CheckOk m2 [] => file_at (m_fs m2) (wk [102]) = Some [104; 122]
         | _ => False
         end
  | _ => False
  end.
Proof. vm_compute. split; check_eq. Qed.

Definition mem_open_write : word -> option byte :=
  fun a => if bv_eqb a 8192 then Some 102       (* 'f' *)
           else if bv_eqb a 8193 then Some 0    (* NUL *)
           else if bv_eqb a 4096 then Some 104  (* 'h' *)
           else if bv_eqb a 4097 then Some 105  (* 'i' *)
           else None.

Example create_write_updates_fs :
  match check_syscall
          (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 wr_create_flags; 420; 0; 0]
             mem_open_write (fun _ => None))
          (with_copyins [(8192, 2%nat)] (mkEffect 3 [] []))
          (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) with
  | CheckOk m1 [] =>
      match check_syscall (mkInput 64 [3; 4096; 2; 0; 0; 0] mem_open_write (fun _ => None))
              (with_copyins [(4096, 2%nat)] (mkEffect 2 [] [])) m1 with
      | CheckOk m2 [] => file_at (m_fs m2) (wk [102]) = Some [104; 105]
      | _ => False
      end
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** File "f" = "hi" open FOR WRITING at fd 3, with the offset parked at 4
    — two bytes PAST end-of-file, where only an lseek can put it. *)

Example write_zero_len_past_eof_leaves_file_alone :
  match check_syscall (mkInput 64 [3; 4096; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
          (mkEffect 0 [] []) wpast_model with
  | CheckOk m [] =>
      file_at (m_fs m) (wk [102]) = Some [104; 105]
      /\ fd_lookup (m_fds m) 3 = Some (FdFileW 1 4)
  | _ => False
  end.
Proof. vm_compute. split; check_eq. Qed.

Example write_zero_len_rejects_zero_length_copyin :
  check_syscall (mkInput 64 [3; 4096; 0; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (with_copyins [(4096, 0%nat)] (mkEffect 0 [] [])) wpast_model = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** The contrast: a NONEMPTY write at the same offset does zero-fill the
    gap (sparse-file semantics), so the no-op above is confined to the
    zero-length corner.  write(3, "z", 1) makes "f" = "hi\0\0z". *)

Example write_one_byte_past_eof_zero_fills :
  match check_syscall
          (mkInput 64 [3; 4096; 1; 0; 0; 0]
             (fun a => if bv_eqb a 4096 then Some 122 else None) (fun _ => None))
          (with_copyins [(4096, 1%nat)] (mkEffect 1 [] [])) wpast_model with
  | CheckOk m [] =>
      file_at (m_fs m) (wk [102]) = Some [104; 105; 0; 0; 122]
      /\ fd_lookup (m_fds m) 3 = Some (FdFileW 1 5)
  | _ => False
  end.
Proof. vm_compute. split; check_eq. Qed.

(** A zero-length write WITHIN the file is a no-op, since the two
    [file_write] arms agree at or below end-of-file. *)

Example write_zero_len_within_file_is_a_noop :
  match check_syscall (mkInput 64 [3; 4096; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
          (mkEffect 0 [] [])
          (with_fds (fd_insert (m_fds wpast_model) 3 (FdFileW 1 1)) wpast_model) with
  | CheckOk m [] => file_at (m_fs m) (wk [102]) = Some [104; 105]
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** File "f" = "hi" open in APPEND MODE at fd 3, twice, with [f_pos]
    parked at two different places -- one past end-of-file, one at the
    start.  Only an lseek can put it either way. *)

Definition apast_model : Model :=
  mkModel [(3, FdFileA 1 4)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    (demo_fs_raw [([102], SFile [104; 105])]) None None None.

Definition azero_model : Model :=
  mkModel [(3, FdFileA 1 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    (demo_fs_raw [([102], SFile [104; 105])]) None None None.

(** AN APPEND WRITE DOES NOT READ [f_pos], stated as an equality between
    two whole checker answers rather than as two separate runs.  A real
    run can move the offset and watch the bytes land at the end anyway,
    but it runs ONE offset per execution and so can never say that the answer is the SAME for two
    of them -- which is the actual claim, and the one a spec that
    quietly used [off] would falsify.

    Both answers write "hiz", not "hi\0\0z": the byte goes to
    [len_word data], and the zero-fill the [FdFileW] arm would have had
    to build here is exactly what [ReadWrite.append_opens_no_gap] proves
    an append write never asks for.  And [f_pos] ends at the new end of
    file, 3, from BOTH starting offsets. *)
Example append_write_ignores_the_offset :
  let w m := check_syscall
        (mkInput 64 [3; 4096; 1; 0; 0; 0]
           (fun a => if bv_eqb a 4096 then Some 122 else None) (fun _ => None))
        (with_copyins [(4096, 1%nat)] (mkEffect 1 [] [])) m in
  w apast_model = w azero_model
  /\ match w apast_model with
     | CheckOk m [] =>
         file_at (m_fs m) (wk [102]) = Some [104; 105; 122]
         /\ fd_lookup (m_fds m) 3 = Some (FdFileA 1 3)
     | _ => False
     end.
Proof. vm_compute. split_conj; check_eq. Qed.

(** ...AND A ZERO-LENGTH APPEND WRITE MOVES NOTHING, which is the one
    place the equality above stops holding — deliberately, and it is the
    sharper claim of the two.

    [generic_write_checks] (mm/filemap.c) opens with
    [if (!iov_iter_count(from)) return 0;] BEFORE the
    [if (iocb->ki_flags & IOCB_APPEND) iocb->ki_pos = i_size_read(inode);]
    line, so a zero-count write never computes the append position at
    all; and [new_sync_write] (fs/read_write.c) copies [ki_pos] back only
    under [if (ret > 0 && ppos)].  [f_pos] therefore stays exactly where
    an [lseek] left it, and the two models below answer DIFFERENTLY —
    4 and 0 — where a delivering write makes them agree.  An arm that
    assigned end-of-file unconditionally would answer 3 for both, which
    is a modeled wrong answer rather than a gap: the next
    [lseek(fd, 0, SEEK_CUR)] reports it.

    The file is untouched in both, as [Fs.file_write]'s own [[]] arm
    already guarantees; it is the offset that needed
    [ReadWrite.append_new_pos]. *)
Example append_zero_write_leaves_the_offset_alone :
  let w m := check_syscall
        (mkInput 64 [3; 4096; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
        (mkEffect 0 [] []) m in
  match w apast_model, w azero_model with
  | CheckOk m1 [], CheckOk m2 [] =>
      file_at (m_fs m1) (wk [102]) = Some [104; 105]
      /\ fd_lookup (m_fds m1) 3 = Some (FdFileA 1 4)
      /\ file_at (m_fs m2) (wk [102]) = Some [104; 105]
      /\ fd_lookup (m_fds m2) 3 = Some (FdFileA 1 0)
  | _, _ => False
  end.
Proof. vm_compute. split_conj; check_eq. Qed.

(** [rw_verify_area]'s position test on a SCALAR write to an APPEND fd.

    [vfs_write] hands [rw_verify_area] (fs/read_write.c) the fd's real
    [&f_pos] and it runs BEFORE the iterator, so
    [(loff_t)(pos + count) < 0] is decided on the position an [lseek]
    left behind — [generic_write_checks] (mm/filemap.c) overrides
    [ki_pos] only once the write is under way.  So the test is about the
    fd's position and not about where the bytes go: without it the
    model would have appended the byte and answered 1 where Linux
    answers -EINVAL.  The write-only and read-write arms make the same
    test ([write_at_llong_max_is_einval]).

    A REAL RUN REACHES IT: [lseek(fd, LLONG_MAX, SEEK_SET)] succeeds on
    tmpfs and ramfs, whose [s_maxbytes] is [MAX_LFS_FILESIZE], the file
    systems of the configuration of record whose regular files hold
    bytes (SCOPE.md).  Both directions are pinned here. *)
Definition append_llong_max_model : Model :=
  mkModel [(3, FdFileA 1 (Z_to_bv 64 (2 ^ 63 - 1)))]
    (mkVmMaps [] [] 0 0 demo_limit) IEof (demo_fs_raw [([102], SFile [104; 105])]) None None None.

Example append_write_at_llong_max_is_einval :
  check_syscall (mkInput 64 [3; 4096; 1; 0; 0; 0]
                   (fun a => if bv_eqb a 4096 then Some 122 else None)
                   (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) append_llong_max_model
  = CheckOk append_llong_max_model []
  (* ...and the append the model would have made without the test is
     refused, file and offset untouched *)
  /\ check_syscall (mkInput 64 [3; 4096; 1; 0; 0; 0]
                      (fun a => if bv_eqb a 4096 then Some 122 else None)
                      (fun _ => None))
       (with_copyins [(4096, 1%nat)] (mkEffect 1 [] [])) append_llong_max_model
     = CheckReject.
Proof. split; check_eq. Qed.

(** ...AND [access_ok] COMES FIRST, which is the half that decides the
    ORDER rather than the answer.  [vfs_write] runs
    [if (unlikely(!access_ok(buf, count))) return -EFAULT;] before it
    calls [rw_verify_area] (fs/read_write.c, Linux v6.18.46), so a buffer
    whose named range passes [State.TASK_SIZE] is -EFAULT even at a
    position that would otherwise be -EINVAL.  An arm that modeled the
    later test without the earlier one would answer -EINVAL here, and
    only a state satisfying BOTH conditions can tell the two orders
    apart — which is why this is its own example and not a conjunct of
    the one above.

    [buf] is [2 ^ 47] exactly, the first address whose one-byte range
    leaves the user address space. *)
Example append_write_access_ok_precedes_the_position_test :
  check_syscall (mkInput 64 [3; Z_to_bv 64 (2 ^ 47); 1; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) append_llong_max_model
  = CheckOk append_llong_max_model []
  (* the position test's answer, offered at the same call, is refused *)
  /\ check_syscall (mkInput 64 [3; Z_to_bv 64 (2 ^ 47); 1; 0; 0; 0]
                      (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) append_llong_max_model
     = CheckReject.
Proof. split; check_eq. Qed.

(** ...and the [FdFileW] fd at the SAME offset is the contrast that makes
    the claim above about O_APPEND rather than about writes in general:
    it zero-fills out to 4 and leaves [f_pos] at 5. *)
Example non_append_write_at_the_same_offset_differs :
  let w m := check_syscall
        (mkInput 64 [3; 4096; 1; 0; 0; 0]
           (fun a => if bv_eqb a 4096 then Some 122 else None) (fun _ => None))
        (with_copyins [(4096, 1%nat)] (mkEffect 1 [] [])) m in
  match w wpast_model with
  | CheckOk m [] =>
      file_at (m_fs m) (wk [102]) = Some [104; 105; 0; 0; 122]
      /\ fd_lookup (m_fds m) 3 = Some (FdFileW 1 5)
  | _ => False
  end.
Proof. vm_compute. split; check_eq. Qed.

(* -------------------------------------------------------------------------
   fsync (82) / fdatasync (83)
   ------------------------------------------------------------------------- *)

(** A model carrying one fd of every kind, so the arms can be compared
    side by side. *)

Lemma writev_channel_outcome : forall fd iov iovcnt i m ch iovs bs eff m' evs,
  fd_lookup (m_fds m) fd = Some (FdChannel ch) ->
  ch <> 0 ->
  (* the far end has a reader.  Not a modelling shortcut and not the
     model assuming one: with the reader gone [ReadWrite.writev_spec]
     answers -EPIPE and raises SIGPIPE, which KILLS the process under
     the default disposition, so no delivery is admissible there *)
  m_channel_reader m = true ->
  (bv_unsigned iovcnt <= IOV_MAX)%Z ->
  import_iovecs (in_mem i) iov iovcnt = ImpOk iovs ->
  gather_iovecs (in_mem i) (cap_iovecs iovs) = Some bs ->
  addr_is_error_b (len_word bs) = false ->
  bs <> [] ->
  writev_spec fd iov iovcnt i m (Ok eff m' evs) ->
  (Z.of_nat (length bs) <= MAX_RW_COUNT)%Z
  /\ exists n, (1 <= n)%nat /\ (n <= length bs)%nat
  /\ eff = with_copyins
       (import_iovecs_accesses (in_mem i) iov iovcnt ++
        iov_prefix_accesses (cap_iovecs iovs) n)
       (mkEffect (len_word (firstn n bs)) [] []) /\ m' = m
  /\ evs = map (WriteEv ch) (firstn n bs).
Proof.
  intros fd iov iovcnt i m ch iovs bs eff m' evs Hfd Hch Hrdr Hmax Hiv Hg Hae
    Hnonempty Hspec.
  apply check_writev_complete_ok in Hspec.
  assert (H32 : iovcnt32 iovcnt = iovcnt) by (apply iovcnt32_small; exact Hmax).
  unfold check_writev in Hspec. rewrite Hfd in Hspec.
  assert (Hch0 : w_is0 ch = false).
  { unfold w_is0, bv_eqb. apply Z.eqb_neq. intro Heq. apply Hch, bv_eq.
    rewrite Heq. reflexivity. }
  rewrite Hch0 in Hspec. cbv iota in Hspec. rewrite H32, Hiv in Hspec.
  cbv iota in Hspec.
  (* the aggregate the gather ran over is the CAPPED one, so its length
     is under the kernel's clamp by construction *)
  assert (Hbnd : (Z.of_nat (length bs) <= MAX_RW_COUNT)%Z).
  { rewrite (gather_iovecs_length _ _ _ Hg), iovs_total_cap. lia. }
  split; [exact Hbnd|].
  unfold writev_gathered in Hspec. cbv iota zeta in Hspec.
  rewrite (gather_prefix_full _ _ _ Hg) in Hspec.
  assert (Hlpos : (0 < length bs)%nat)
    by (destruct bs; [congruence|cbn; lia]).
  assert (Htot : Z.eqb (iovs_total (cap_iovecs iovs)) 0 = false).
  { apply Z.eqb_neq. rewrite <- (gather_iovecs_length _ _ _ Hg). lia. }
  rewrite Htot in Hspec. cbv iota in Hspec.
  rewrite Hrdr in Hspec. change (negb true) with false in Hspec.
  cbv iota in Hspec.
  assert (Hg0 : Nat.eqb (length bs) 0 = false) by (apply Nat.eqb_neq; lia).
  rewrite Hg0 in Hspec. cbv iota in Hspec.
  rewrite Hae in Hspec. cbv iota in Hspec.
  destruct eff as [ret ws zs us cs copyins]; destruct ws as [|? ?];
    destruct zs as [|? ?]; destruct us as [|? ?];
    destruct cs as [|? ?]; try discriminate.
  destruct ((1 <=? bv_unsigned ret)%Z
            && (bv_unsigned ret <=? Z.of_nat (length bs))%Z
            && negb (addr_is_error_b ret)) eqn:Hgr.
  2:{ (* a wholly gathered source has no fault inside its first copy,
         so the -EFAULT the arm admits beside the delivery is not
         reached *)
      exfalso. cbv beta iota in Hspec.
      assert (Hx : fault_in_first_copyb channel_first_copy_max
                     (Z.of_nat (length bs)) (iovs_total (cap_iovecs iovs))
                   = false).
      { unfold fault_in_first_copyb.
        rewrite <- (gather_iovecs_length _ _ _ Hg), Z.ltb_irrefl.
        reflexivity. }
      rewrite Hx, Bool.andb_false_r in Hspec. discriminate Hspec. }
  destruct (access_ranges_eqb copyins
              (import_iovecs_accesses (in_mem i) iov iovcnt ++
               iov_prefix_accesses (cap_iovecs iovs)
                 (Z.to_nat (bv_unsigned ret)))) eqn:Hreads; [|discriminate].
  inversion Hspec; clear Hspec; subst.
  apply andb_true_iff in Hgr as [Hgr _].
  apply andb_true_iff in Hgr as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  apply access_ranges_eqb_eq in Hreads. subst copyins.
  pose proof (word_unsigned_range ret) as Hr.
  exists (Z.to_nat (bv_unsigned ret)).
  assert (Hlw : len_word (firstn (Z.to_nat (bv_unsigned ret)) bs) = ret)
    by (apply len_word_firstn_ret; lia).
  rewrite Hlw. repeat split; try reflexivity; lia.
Qed.

(** ...and the write-side counterpart: a channel write from a FULLY
    readable buffer delivers a nonempty — possibly short — prefix of
    it, returning the delivered length.  As above, an [Ok] pins [count]
    — and so the buffer — inside [rw_bytes_max].  [bs <> []] also keeps
    the zero-length case out: a write of nothing is decided by the range
    verdict instead ([Uaccess.access_ok_zero]).  And the far end must
    have a reader ([State.m_channel_reader]): without one the write
    answers -EPIPE and raises SIGPIPE instead of delivering. *)

Corollary writev_outcome_is_write_outcome :
  forall fd iov iovcnt buf count iv iw m ch iovs bs eff m' evs,
  fd_lookup (m_fds m) fd = Some (FdChannel ch) ->
  ch <> 0 ->
  m_channel_reader m = true ->
  (bv_unsigned iovcnt <= IOV_MAX)%Z ->
  import_iovecs (in_mem iv) iov iovcnt = ImpOk iovs ->
  gather_iovecs (in_mem iv) (cap_iovecs iovs) = Some bs ->
  addr_is_error_b (len_word bs) = false ->
  bs <> [] ->
  (bv_unsigned count <= rw_bytes_max)%Z ->
  read_bytes_map (in_mem iw) buf count = Some bs ->
  (* the range [vfs_write]'s [access_ok] accepts; see
     [write_channel_outcome], which needs it for the same reason *)
  access_okb buf (bv_unsigned count) = true ->
  writev_spec fd iov iovcnt iv m (Ok eff m' evs) ->
  exists n, (1 <= n)%nat /\ (n <= length bs)%nat
  /\ eff = with_copyins
       (import_iovecs_accesses (in_mem iv) iov iovcnt ++
        iov_prefix_accesses (cap_iovecs iovs) n)
       (mkEffect (len_word (firstn n bs)) [] [])
  /\ write_spec fd buf count iw m
       (Ok (with_copyins [(buf, n)]
              (mkEffect (len_word (firstn n bs)) [] [])) m' evs).
Proof.
  intros fd iov iovcnt buf count iv iw m ch iovs bs eff m' evs
         Hfd Hch Hrdr Hmax Hiv Hg Hae Hnonempty Hcmax Hb Hok Hv.
  destruct (writev_channel_outcome _ _ _ _ _ _ _ _ _ _ _
              Hfd Hch Hrdr Hmax Hiv Hg Hae Hnonempty Hv)
    as (Hbnd & n & Hn1 & Hn2 & Heff & Hm & Hevs).
  exists n. split; [exact Hn1|]. split; [exact Hn2|].
  split; [exact Heff|]. subst m' evs.
  apply check_write_sound_ok.
  unfold check_write. rewrite Hfd.
  assert (Hch0 : w_is0 ch = false).
  { unfold w_is0, bv_eqb. apply Z.eqb_neq. intro Heq. apply Hch, bv_eq.
    rewrite Heq. reflexivity. }
  rewrite Hch0. cbv beta iota.
  pose proof (read_bytes_map_length _ _ _ _ Hb) as Hlen.
  rewrite (rw_range_in_range _ _ Hcmax). cbv beta iota.
  assert (Hlpos : (0 < length bs)%nat)
    by (destruct bs; [congruence|cbn; lia]).
  assert (Hc : w_is0 count = false).
  { unfold w_is0, bv_eqb. apply Z.eqb_neq.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia. }
  rewrite Hc. cbv beta iota zeta.
  rewrite Hok. cbn [negb]. cbv beta iota.
  rewrite Hrdr. change (negb true) with false. cbv beta iota zeta.
  rewrite (write_source_of_rw _ _ _ Hcmax), (readable_bytes_full _ _ _ _ Hb).
  assert (Hg0 : Nat.eqb (length bs) 0 = false) by (apply Nat.eqb_neq; lia).
  rewrite Hg0. cbv beta iota.
  unfold with_copyins. cbn.
  pose proof (word_unsigned_range count) as Hcr.
  assert (Hlenf : Z.of_nat (length (firstn n bs)) = Z.of_nat n)
    by (rewrite length_firstn; lia).
  assert (Hru : bv_unsigned (len_word (firstn n bs)) = Z.of_nat n).
  { unfold len_word. rewrite Hlenf. rewrite Z_to_bv_small; [reflexivity|].
    unfold bv_modulus. change (Z.of_N 64) with 64%Z.
    unfold two_pow_64 in Hcr. lia. }
  rewrite Hru.
  assert (Hg1 : (1 <=? Z.of_nat n)%Z = true) by (apply Z.leb_le; lia).
  assert (Hg2 : (Z.of_nat n <=? Z.of_nat (length bs))%Z = true)
    by (apply Z.leb_le; lia).
  rewrite Hg1, Hg2. cbn [andb].
  rewrite Nat2Z.id, bv_eqb_refl, Nat.eqb_refl. reflexivity.
Qed.

(** The converse correspondence.  Together with the previous corollary it
    says the two calls admit matching returns, post-models, and events;
    their [Ok] outcomes are not identical because [eff_copyins] records a
    flat buffer for write and an iovec table plus data ranges for writev.
    Each corollary explicitly replaces that ledger.  (Under these premises neither
    spec has a reachable [Err] branch: [bs <> []] forces both [count] and
    [iovs_total iovs] nonzero, so restricting to [Ok] loses nothing.)
    The write and the writev choose their delivered lengths independently,
    so two admissible outcomes need not agree.  A ledger-translating
    correspondence is the right statement.

    This direction is not free.  [writev_spec]'s [choose] carries an
    [addr_is_error_b (len_word ds) = false] conjunct that [write_spec]'s
    does not (a write never returns an error-encoded count), so a write
    outcome whose delivered length landed in the error window would have
    no writev counterpart.  It goes through because the [addr_is_error_b
    (len_word bs) = false] premise already caps [length bs] below that
    window, and a delivered prefix is no longer than [bs].  Drop that
    premise and the inclusion fails in exactly the window where the two
    specs disagree. *)

Corollary write_outcome_is_writev_outcome :
  forall fd iov iovcnt buf count iv iw m ch iovs bs eff m' evs,
  fd_lookup (m_fds m) fd = Some (FdChannel ch) ->
  ch <> 0 ->
  m_channel_reader m = true ->
  (bv_unsigned iovcnt <= IOV_MAX)%Z ->
  import_iovecs (in_mem iv) iov iovcnt = ImpOk iovs ->
  gather_iovecs (in_mem iv) (cap_iovecs iovs) = Some bs ->
  addr_is_error_b (len_word bs) = false ->
  bs <> [] ->
  (bv_unsigned count <= rw_bytes_max)%Z ->
  read_bytes_map (in_mem iw) buf count = Some bs ->
  (* the range [vfs_write]'s [access_ok] accepts; see
     [write_channel_outcome], which needs it for the same reason *)
  access_okb buf (bv_unsigned count) = true ->
  write_spec fd buf count iw m (Ok eff m' evs) ->
  exists n, (1 <= n)%nat /\ (n <= length bs)%nat
  /\ eff = with_copyins [(buf, n)]
       (mkEffect (len_word (firstn n bs)) [] [])
  /\ writev_spec fd iov iovcnt iv m
       (Ok (with_copyins
              (import_iovecs_accesses (in_mem iv) iov iovcnt ++
               iov_prefix_accesses (cap_iovecs iovs) n)
              (mkEffect (len_word (firstn n bs)) [] [])) m' evs).
Proof.
  intros fd iov iovcnt buf count iv iw m ch iovs bs eff m' evs
         Hfd Hch Hrdr Hmax Hiv Hg Hae Hnonempty Hcmax Hb Hok Hw.
  destruct (write_channel_outcome _ _ _ _ _ _ _ _ _ _
              Hfd Hch Hrdr Hcmax Hb Hok Hnonempty Hw)
    as (Hbnd & n & Hn1 & Hn2 & Heff & Hm & Hevs).
  exists n. split; [exact Hn1|]. split; [exact Hn2|].
  split; [exact Heff|]. subst m' evs.
  apply check_writev_sound_ok.
  assert (H32 : iovcnt32 iovcnt = iovcnt) by (apply iovcnt32_small; exact Hmax).
  pose proof (read_bytes_map_length _ _ _ _ Hb) as Hlen.
  pose proof (word_unsigned_range count) as Hcr.
  assert (Hlpos : (0 < length bs)%nat)
    by (destruct bs; [congruence|cbn; lia]).
  (* [bs] is not error-encoded, and it does not wrap, so its length is
     capped below the error window; the delivered prefix inherits that. *)
  assert (Hbsu : bv_unsigned (len_word bs) = Z.of_nat (length bs)).
  { unfold len_word. rewrite Z_to_bv_small; [reflexivity|].
    unfold bv_modulus. change (Z.of_N 64) with 64%Z.
    unfold two_pow_64 in Hcr. lia. }
  assert (Hcap : (Z.of_nat (length bs) <= two_pow_64 - 4096)%Z).
  { unfold addr_is_error_b in Hae. apply Z.ltb_ge in Hae.
    rewrite Hbsu in Hae. exact Hae. }
  assert (Hlenf : Z.of_nat (length (firstn n bs)) = Z.of_nat n)
    by (rewrite length_firstn; lia).
  assert (Hru : bv_unsigned (len_word (firstn n bs)) = Z.of_nat n).
  { unfold len_word. rewrite Hlenf. rewrite Z_to_bv_small; [reflexivity|].
    unfold bv_modulus. change (Z.of_N 64) with 64%Z.
    unfold two_pow_64 in Hcr. lia. }
  assert (Hbody : check_writev iv fd iov iovcnt
                    (with_copyins
                      (import_iovecs_accesses (in_mem iv) iov iovcnt ++
                       iov_prefix_accesses (cap_iovecs iovs) n)
                      (mkEffect (len_word (firstn n bs)) [] [])) m
                  = CheckOk m (map (WriteEv ch) (firstn n bs))).
  { unfold check_writev. rewrite Hfd. cbv iota.
    assert (Hch0 : w_is0 ch = false).
    { unfold w_is0, bv_eqb. apply Z.eqb_neq. intro Heq. apply Hch, bv_eq.
      rewrite Heq. reflexivity. }
    rewrite Hch0. cbv iota. rewrite H32.
    rewrite Hiv. cbv iota.
    unfold writev_gathered.
    cbv iota zeta.
    rewrite (gather_prefix_full _ _ _ Hg).
    assert (Htot : Z.eqb (iovs_total (cap_iovecs iovs)) 0 = false).
    { apply Z.eqb_neq. rewrite <- (gather_iovecs_length _ _ _ Hg). lia. }
    rewrite Htot. cbv iota.
    rewrite Hrdr. change (negb true) with false. cbv iota.
    assert (Hg0 : Nat.eqb (length bs) 0 = false) by (apply Nat.eqb_neq; lia).
    rewrite Hg0. cbv iota. rewrite Hae. cbv iota.
    unfold with_copyins. cbn.
    assert (Hg1 : (1 <=? bv_unsigned (len_word (firstn n bs)))%Z = true)
      by (rewrite Hru; apply Z.leb_le; lia).
    assert (Hg2 : (bv_unsigned (len_word (firstn n bs))
                     <=? Z.of_nat (length bs))%Z = true)
      by (rewrite Hru; apply Z.leb_le; lia).
    assert (Hg3 : negb (addr_is_error_b (len_word (firstn n bs))) = true).
    { unfold addr_is_error_b. rewrite Hru.
      apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
    rewrite Hg1, Hg2, Hg3. cbn [andb].
    rewrite Hru, Nat2Z.id.
    rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl).
    reflexivity. }
  exact Hbody.
Qed.

(* =========================================================================
   PART 3 — byte-level events erase syscall chunking

   Each example here compares TWO RUNS.  "These two calls emit the same
   events" is a statement about a pair of traces, and a real run yields
   one trace, so nothing in this part is reachable from a real run.
   ========================================================================= *)

Definition mem_writev_ab : word -> option byte :=
  fun a =>
    match mem_ab a with
    | Some b => Some b
    | None =>
        if bv_leu 8192 a && bv_ltu a 8224
        then if bv_eqb a 8193 then Some 16       (* iov[0].iov_base = 4096 *)
             else if bv_eqb a 8200 then Some 1   (* iov[0].iov_len  = 1 *)
             else if bv_eqb a 8208 then Some 1   (* iov[1].iov_base = 4097... *)
             else if bv_eqb a 8209 then Some 16  (* ...= 1 + 16*256 *)
             else if bv_eqb a 8216 then Some 1   (* iov[1].iov_len  = 1 *)
             else Some 0
        else None
    end.

(** writev(1, [{4096,1},{4097,1}], 2) is accepted with exactly the
    verdict and events of write(1, "ab", 2) — one event per byte
    (cf. [write_ab_events]/[write_a_then_b_events]: the same events as
    write("a");write("b") too).  The concrete witness for the
    [writev_outcome_is_write_outcome] / [write_outcome_is_writev_outcome]
    pair — in particular that their two memory premises are jointly
    satisfiable, the flat buffer and the gathered iovecs living in
    different [in_mem]s. *)

Example writev_two_iovecs_equals_one_write :
  check_syscall (mkInput 66 [1; 8192; 2; 0; 0; 0] mem_writev_ab (fun _ => None))
    (with_copyins
       (import_iovecs_accesses mem_writev_ab 8192 2 ++
        iov_prefix_accesses (cap_iovecs [(4096, 1); (4097, 1)]) 2)
       (mkEffect 2 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
  = check_syscall (mkInput 64 [1; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
      (with_copyins [(4096, 2%nat)] (mkEffect 2 [] []))
      (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
  /\ check_syscall (mkInput 66 [1; 8192; 2; 0; 0; 0] mem_writev_ab (fun _ => None))
       (with_copyins
          (import_iovecs_accesses mem_writev_ab 8192 2 ++
           iov_prefix_accesses (cap_iovecs [(4096, 1); (4097, 1)]) 2)
          (mkEffect 2 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) [WriteEv 1 97; WriteEv 1 98].
Proof. split; check_eq. Qed.

(** Linux >= 4.1 truncates writev's count to 32 bits before validating it
    ([iovcnt32]): with the same two-iovec array, iovcnt = 2^32 + 2 writes
    2 iovecs exactly like iovcnt = 2, and iovcnt = 2^32 is an empty writev
    returning 0.  A count whose low 32 bits exceed IOV_MAX (e.g. 1025, or
    -1's low 32 bits) is -EINVAL on every path.

    (qemu-user answers -EINVAL for the raw count instead.) *)

Example writev_iovcnt_truncates_to_32_bits :
  check_syscall (mkInput 66 [1; 8192; Z_to_bv 64 (2 ^ 32 + 2); 0; 0; 0]
                   mem_writev_ab (fun _ => None))
    (with_copyins
       (import_iovecs_accesses mem_writev_ab 8192 2 ++
        iov_prefix_accesses (cap_iovecs [(4096, 1); (4097, 1)]) 2)
       (mkEffect 2 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
  = check_syscall (mkInput 66 [1; 8192; 2; 0; 0; 0] mem_writev_ab (fun _ => None))
      (with_copyins
         (import_iovecs_accesses mem_writev_ab 8192 2 ++
          iov_prefix_accesses (cap_iovecs [(4096, 1); (4097, 1)]) 2)
         (mkEffect 2 [] []))
      (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
  /\ check_syscall (mkInput 66 [1; 8192; Z_to_bv 64 (2 ^ 32); 0; 0; 0]
                     mem_writev_ab (fun _ => None))
       (mkEffect 0 [] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) []
  /\ check_syscall (mkInput 66 [1; 8192; 1025; 0; 0; 0] mem_writev_ab (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) []
  /\ check_syscall (mkInput 66 [1; 8192; Z_to_bv 64 (two_pow_64 - 1); 0; 0; 0]
                     mem_writev_ab (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) [].
Proof. split; [|split; [|split]]; check_eq. Qed.

(** A raw count over IOV_MAX whose low 32 bits are in range is the
    truncated transfer and NOTHING ELSE: the bare -EINVAL qemu-user's
    [lock_iovec] answers for the raw count is REJECTED, where an older
    reading of this model admitted it beside the transfer.  The third
    conjunct keeps the count band honest from the other side: an IN-RANGE
    count accepts the delivery and NOT -EINVAL either. *)

Example writev_over_max_truncates_only :
  check_syscall (mkInput 66 [1; 8192; Z_to_bv 64 (2 ^ 32 + 2); 0; 0; 0]
                   mem_writev_ab (fun _ => None))
    (with_copyins
       (import_iovecs_accesses mem_writev_ab 8192 2 ++
        iov_prefix_accesses (cap_iovecs [(4096, 1); (4097, 1)]) 2)
       (mkEffect 2 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) [WriteEv 1 97; WriteEv 1 98]
  /\ check_syscall (mkInput 66 [1; 8192; Z_to_bv 64 (2 ^ 32 + 2); 0; 0; 0]
                     mem_writev_ab (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckReject
  /\ check_syscall (mkInput 66 [1; 8192; 2; 0; 0; 0] mem_writev_ab (fun _ => None))
       (with_copyins (import_iovecs_accesses mem_writev_ab 8192 2)
          (mkEffect (errno_ret EINVAL) [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckReject.
Proof. split; [|split]; check_eq. Qed.

(** A two-entry array at 8192 with the entries given as words, plus one
    readable source byte at 4096: the shapes below vary the entries and
    keep the array. *)
Definition mem_iov_pair (b0 l0 b1 l1 : word) : word -> option byte :=
  fun a =>
    if bv_leu 8192 a && bv_ltu a 8224 then
      nth_error (word_le8 b0 ++ word_le8 l0 ++ word_le8 b1 ++ word_le8 l1)
        (Z.to_nat (bv_unsigned a - 8192))
    else if bv_eqb a 4096 then Some 97
    else None.

(** THE PER-SEGMENT [access_ok] REACHES writev TOO — [vfs_writev] and
    [vfs_readv] call the same [import_iovec] — and it runs on EVERY
    entry's uncapped length, zero-length entries included, before a byte
    is gathered.  A readable first entry followed by one whose range
    leaves the user address space is -EFAULT at import, not the one-byte
    short write an import without the check would gather; and a lone
    zero-length entry with a base past the ceiling is -EFAULT, not the 0
    qemu-user answers when its [lock_iovec] skips the entry.  Both pin
    the order whatever value the limit takes: the second entry's
    [addr <= TASK_SIZE - size] fails by one for base 1 and length
    [TASK_SIZE], and [2^63 <= TASK_SIZE] fails for any limit under
    2^63. *)
Example writev_import_range_fault_beats_the_gather :
  let mem := mem_iov_pair 4096 1 1 (Z_to_bv 64 TASK_SIZE) in
  let m := init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof) in
  check_syscall (mkInput 66 [1; 8192; 2; 0; 0; 0] mem (fun _ => None))
    (with_copyins (import_iovecs_accesses mem 8192 2)
       (mkEffect (errno_ret EFAULT) [] [])) m
  = CheckOk m []
  /\ check_syscall (mkInput 66 [1; 8192; 2; 0; 0; 0] mem (fun _ => None))
       (with_copyins (import_iovecs_accesses mem 8192 2 ++
                      iov_prefix_accesses (cap_iovecs [(4096, 1)]) 1)
          (mkEffect 1 [] [])) m
     = CheckReject
  /\ let mem1 := mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 0 0 in
     check_syscall (mkInput 66 [1; 8192; 1; 0; 0; 0] mem1 (fun _ => None))
       (with_copyins (import_iovecs_accesses mem1 8192 1)
          (mkEffect (errno_ret EFAULT) [] [])) m
     = CheckOk m []
  /\ let mem1 := mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 0 0 in
     check_syscall (mkInput 66 [1; 8192; 1; 0; 0; 0] mem1 (fun _ => None))
       (with_copyins (import_iovecs_accesses mem1 8192 1) (mkEffect 0 [] [])) m
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** [rw_verify_area]'s position test on the vectored write: a nonempty
    writev to a regular file at offset [LLONG_MAX] is -EINVAL, and the
    file and offset are untouched. *)
Definition writev_llong_max_model : Model :=
  mkModel [(3, FdFileW 1 (Z_to_bv 64 (2 ^ 63 - 1)))]
    (mkVmMaps [] [] 0 0 demo_limit) IEof (demo_fs_raw [([102], SFile [])]) None None None.

Example writev_at_llong_max_is_einval :
  check_syscall (mkInput 66 [3; 8192; 2; 0; 0; 0] mem_writev_ab (fun _ => None))
    (with_copyins (import_iovecs_accesses mem_writev_ab 8192 2)
       (mkEffect (errno_ret EINVAL) [] [])) writev_llong_max_model
  = CheckOk writev_llong_max_model []
  /\ check_syscall (mkInput 66 [3; 8192; 2; 0; 0; 0] mem_writev_ab (fun _ => None))
       (with_copyins (import_iovecs_accesses mem_writev_ab 8192 2 ++
                      iov_prefix_accesses (cap_iovecs [(4096, 1); (4097, 1)]) 2)
          (mkEffect 2 [] [])) writev_llong_max_model
     = CheckReject.
Proof. split; check_eq. Qed.

(** THE AGGREGATE IS THE KERNEL'S, NOT THE MODEL'S.  A raw count of
    2^32 + 1 truncates to one segment; with that segment one byte over
    [Uaccess.rw_bytes_max] the call is JUDGED — a one-byte short write,
    since only [4096] is mapped — and not declined.  The first conjunct
    is the negative half: qemu-user's raw-count -EINVAL is REJECTED
    rather than declined, which is what an answered arm buys over a
    fail-closed one. *)
Example writev_over_rw_bytes_max_total_is_judged :
  let mem := mem_iov_pair 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 0 in
  let m := init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof) in
  check_syscall (mkInput 66 [1; 8192; Z_to_bv 64 (2 ^ 32 + 1); 0; 0; 0] mem (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) m
  = CheckReject
  /\ check_syscall (mkInput 66 [1; 8192; Z_to_bv 64 (2 ^ 32 + 1); 0; 0; 0] mem (fun _ => None))
       (with_copyins (import_iovecs_accesses mem 8192 1 ++
                      iov_prefix_accesses (cap_iovecs [(4096, Z_to_bv 64 (rw_bytes_max + 1))]) 1)
          (mkEffect 1 [] [])) m
     = CheckOk m [WriteEv 1 97].
Proof. split; check_eq. Qed.

(** The [MAX_RW_COUNT] aggregate cap is a per-entry walk, not a truncation
    of the total.  On a vector whose budget runs out INSIDE the second
    entry, all three of its behaviours show at once: the first entry, which
    fits, passes through UNCHANGED; the straddling second entry is cut IN
    PLACE to exactly the 16 bytes of budget left; and the third entry, past
    the cap entirely, SURVIVES AT LENGTH ZERO.

    That last one is the part a naive implementation gets wrong, and it
    matters because the kernel imports and address-checks the whole array:
    dropping the tail would renumber the vector, so a later index would
    silently shift onto a different descriptor.  [iovs_total_cap] proves
    the aggregate is right for every vector; this pins the SHAPE, which the
    aggregate alone does not determine.

    No real run can reach this: it would need a 2 GB aggregate, and the
    extracted checker overflows its stack well below that. *)

Definition mem_readv_iov : word -> option byte :=
  fun a =>
    if bv_leu 8192 a && bv_ltu a 8208
    then if bv_eqb a 8193 then Some 16       (* iov[0].iov_base = 4096 *)
         else if bv_eqb a 8200 then Some 1   (* iov[0].iov_len  = 1 *)
         else Some 0
    else None.

(** The single-iovec import path caps its length BEFORE [access_ok], while
    the multi-iovec path checks every original length BEFORE applying the
    aggregate cap (lib/iov_iter.c [import_ubuf] against [__import_iovec]'s
    loop, v6.18.46).  Put the first base exactly [MAX_RW_COUNT] below
    [TASK_SIZE] and give it one byte more than [MAX_RW_COUNT]: the
    capped range ends exactly at the limit, but the original range ends
    one byte past it.  With [TASK_SIZE] = 2^47 the base is
    0x7fff80001000, a real user address.  The second descriptor is
    {NULL, 0} and matters only by selecting the multi-iovec path.

    The first two conjuncts pin the imported state directly.  The next two
    pin the corresponding readv results with EOF on stdin: count one
    reaches the read and returns zero, while count two faults during
    import.  The final rejection makes that distinction non-vacuous. *)

Definition readv_cap_order_base : word :=
  Z_to_bv 64 (TASK_SIZE - MAX_RW_COUNT).

Definition readv_cap_order_len : word :=
  Z_to_bv 64 (MAX_RW_COUNT + 1).

Definition mem_readv_cap_order : word -> option byte :=
  fun a =>
    if bv_leu 8192 a && bv_ltu a 8224 then
      nth_error
        (word_le8 readv_cap_order_base ++ word_le8 readv_cap_order_len ++
         word_le8 (Z_to_bv 64 0) ++ word_le8 (Z_to_bv 64 0))
        (Z.to_nat (bv_unsigned a - 8192))
    else None.

Example readv_single_iovec_caps_before_access_ok :
  import_iovecs mem_readv_cap_order 8192 1
    = ImpOk [(readv_cap_order_base, readv_cap_order_len)]
  /\ import_iovecs mem_readv_cap_order 8192 2 = ImpFault
  /\ check_syscall
       (mkInput 65 [0; 8192; 1; 0; 0; 0]
          mem_readv_cap_order (fun _ => None))
       (with_copyins
          (import_iovecs_accesses mem_readv_cap_order 8192 1)
          (mkEffect 0 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) []
  /\ check_syscall
       (mkInput 65 [0; 8192; 2; 0; 0; 0]
          mem_readv_cap_order (fun _ => None))
       (with_copyins
          (import_iovecs_accesses mem_readv_cap_order 8192 2)
          (mkEffect (errno_ret EFAULT) [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) []
  /\ check_syscall
       (mkInput 65 [0; 8192; 2; 0; 0; 0]
          mem_readv_cap_order (fun _ => None))
       (with_copyins
          (import_iovecs_accesses mem_readv_cap_order 8192 2)
          (mkEffect 0 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** A huge positive iov_len must not become a huge Peano natural during
    extraction.  These concrete checks force both bounded conversions:
    the channel case scatters one available byte through a 2^62-byte
    descriptor, and the file case first reads a one-byte file with that
    count and then scatters it.  Both ordinary one-byte deliveries remain
    modeled; the implementation bound changes evaluation strategy, not
    the relational syscall surface. *)

Definition readv_huge_len : word := Z_to_bv 64 (2 ^ 62).

Definition mem_readv_huge : word -> option byte :=
  fun a =>
    if bv_leu 8192 a && bv_ltu a 8208 then
      nth_error (word_le8 (Z_to_bv 64 4096) ++ word_le8 readv_huge_len)
        (Z.to_nat (bv_unsigned a - 8192))
    else None.

Definition wmem_readv_one : word -> option byte :=
  fun a => if bv_eqb a 4096 then Some 0 else None.

Definition readv_huge_file_model : Model :=
  mkModel [(3, FdFile 1 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    (demo_fs_raw [([102], SFile [120])]) None None None.

Example readv_huge_len_delivers_one_byte_without_unary_expansion :
  check_syscall
    (mkInput 65 [0; 8192; 1; 0; 0; 0] mem_readv_huge wmem_readv_one)
    (with_copyins (import_iovecs_accesses mem_readv_huge 8192 1)
       (mkEffect 1 [(4096, [120])] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) (ICons 120 IEof)))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) [ReadEv 0 120]
  /\ check_syscall
       (mkInput 65 [3; 8192; 1; 0; 0; 0] mem_readv_huge wmem_readv_one)
       (with_copyins (import_iovecs_accesses mem_readv_huge 8192 1)
          (mkEffect 1 [(4096, [120])] [])) readv_huge_file_model
     = CheckOk
         (with_fds
            (fd_insert (m_fds readv_huge_file_model) 3 (FdFile 1 1))
            readv_huge_file_model) [].
Proof. split; check_eq. Qed.

(** The matching offset guard is bounded by the concrete file length too:
    an enormous offset on a one-byte file reaches EOF without converting
    that offset to a request-sized natural. *)

Example readv_huge_file_offset_is_bounded_by_file_length :
  let m := with_fds
    (fd_insert (m_fds readv_huge_file_model) 3
      (FdFile 1 readv_huge_len)) readv_huge_file_model in
  check_syscall
    (mkInput 65 [3; 8192; 1; 0; 0; 0] mem_readv_huge wmem_readv_one)
    (with_copyins (import_iovecs_accesses mem_readv_huge 8192 1)
       (mkEffect 0 [] [])) m = CheckOk m [].
Proof. check_eq. Qed.

(** Linux keeps only eight descriptors on the syscall stack.  Counts 9
    through 1024 may fail their temporary allocation before importing any
    descriptor, so readv deliberately fails closed over that whole range.
    THE BAND IS KEYED ON THE NARROWED COUNT, so a raw 2^32+9 lands in it too
    and declines exactly as a bare 9 does. *)

Definition mem_readv_eight_zero : word -> option byte :=
  fun a =>
    if bv_leu 8192 a && bv_ltu a (8192 + 8 * 16) then Some 0 else None.

Definition readv_write_only_model : Model :=
  mkModel [(3, FdFileW 1 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    (demo_fs_raw [([102], SFile [])]) None None None.

Example readv_heap_iovec_boundary_fails_closed :
  check_syscall
    (mkInput 65 [0; 8192; 8; 0; 0; 0] mem_readv_eight_zero (fun _ => None))
    (with_copyins (import_iovecs_accesses mem_readv_eight_zero 8192 8)
       (mkEffect 0 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) []
  /\ check_syscall
       (mkInput 65 [0; 8192; 8; 0; 0; 0]
          mem_readv_eight_zero (fun _ => None))
       (with_copyins (import_iovecs_accesses mem_readv_eight_zero 8192 8)
          (mkEffect (errno_ret ENOMEM) [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckReject
  /\ check_syscall
       (mkInput 65 [0; 8192; 9; 0; 0; 0]
          mem_readv_eight_zero (fun _ => None))
       (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckUnmodeled
  /\ check_syscall
       (mkInput 65 [0; 8192; 9; 0; 0; 0]
          mem_readv_eight_zero (fun _ => None))
       (mkEffect (errno_ret ENOMEM) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckUnmodeled
  /\ check_syscall
       (mkInput 65 [0; 8192; 1024; 0; 0; 0]
          mem_readv_eight_zero (fun _ => None))
       (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckUnmodeled
  /\ check_syscall
       (mkInput 65 [5; 8192; 9; 0; 0; 0]
          mem_readv_eight_zero (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) []
  /\ check_syscall
       (mkInput 65 [3; 8192; 9; 0; 0; 0]
          mem_readv_eight_zero (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) readv_write_only_model
     = CheckOk readv_write_only_model []
  (* A raw count of 2^32 + 9 narrows to 9, inside the heap-backed band,
     so the call DECLINES exactly as the in-range twin above does: the raw
     high bits do not change whether the model can describe the call.
     Neither the -EINVAL qemu-user answers for the raw count nor the
     -ENOMEM the allocation may produce is admitted -- the first is not
     Linux's answer at all, the second is the decline's reason. *)
  /\ check_syscall
       (mkInput 65 [0; 8192; Z_to_bv 64 (2 ^ 32 + 9); 0; 0; 0]
          mem_readv_eight_zero (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckUnmodeled
  /\ check_syscall
       (mkInput 65 [0; 8192; Z_to_bv 64 (2 ^ 32 + 9); 0; 0; 0]
          mem_readv_eight_zero (fun _ => None))
       (mkEffect (errno_ret ENOMEM) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckUnmodeled
  /\ check_syscall
       (mkInput 65 [0; 8192; 1025; 0; 0; 0]
          mem_readv_eight_zero (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) [].
Proof. split_conj; check_eq. Qed.

(** readv's count reaches Linux through [__import_iovec]'s [unsigned]
    parameter, so only the low 32 bits are used ([iovcnt32]): a raw count
    of 2^32 + 1 behaves exactly as 1.  Such a count takes the
    SINGLE-DESCRIPTOR import path and never reaches the UIO_MAXIOV test
    at all, which is why the answer is a plain 0 and not -EINVAL.

    (qemu-user validates the FULL 64-bit count in [lock_iovec] before
    dispatching, and answers -EINVAL instead.) *)

Example readv_iovcnt_truncates_to_32_bits :
  check_syscall (mkInput 65 [0; 8192; Z_to_bv 64 (2 ^ 32 + 1); 0; 0; 0]
                   mem_readv_iov (fun _ => None))
    (with_copyins (import_iovecs_accesses mem_readv_iov 8192 1)
       (mkEffect 0 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
  = check_syscall (mkInput 65 [0; 8192; 1; 0; 0; 0] mem_readv_iov (fun _ => None))
      (with_copyins (import_iovecs_accesses mem_readv_iov 8192 1)
         (mkEffect 0 [] []))
      (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
  /\ check_syscall (mkInput 65 [0; 8192; 1; 0; 0; 0] mem_readv_iov (fun _ => None))
       (with_copyins (import_iovecs_accesses mem_readv_iov 8192 1)
          (mkEffect 0 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) []
  (* two descriptors reaches the unreadable one: -EFAULT, so a zero return
     is inadmissible there -- the conjunct that makes the first two
     non-vacuous *)
  /\ check_syscall (mkInput 65 [0; 8192; 2; 0; 0; 0] mem_readv_iov (fun _ => None))
       (with_copyins (import_iovecs_accesses mem_readv_iov 8192 2)
          (mkEffect 0 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckReject.
Proof. split; [|split]; check_eq. Qed.

(** A raw count over IOV_MAX whose low 32 bits select the on-stack path
    (one here) is a real transfer and NOTHING ELSE: the bare -EINVAL
    qemu-user's [lock_iovec] answers for the raw count is REJECTED.  The
    third conjunct keeps the count band honest from the other side: an
    IN-RANGE count accepts the delivery and NOT -EINVAL either. *)

Example readv_over_max_truncates_only :
  check_syscall (mkInput 65 [0; 8192; Z_to_bv 64 (2 ^ 32 + 1); 0; 0; 0]
                   mem_readv_iov (fun _ => None))
    (with_copyins (import_iovecs_accesses mem_readv_iov 8192 1)
       (mkEffect 0 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) []
  /\ check_syscall (mkInput 65 [0; 8192; Z_to_bv 64 (2 ^ 32 + 1); 0; 0; 0]
                     mem_readv_iov (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckReject
  /\ check_syscall (mkInput 65 [0; 8192; 1; 0; 0; 0] mem_readv_iov (fun _ => None))
       (with_copyins (import_iovecs_accesses mem_readv_iov 8192 1)
          (mkEffect (errno_ret EINVAL) [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckReject.
Proof. split; [|split]; check_eq. Qed.

(** An fd not open for reading is -EBADF decided BEFORE the iovec array is
    imported: fd 1 is stdout, and here NO memory is readable at all, so the
    array import would fault if it ran (fs/read_write.c [vfs_readv]'s
    [FMODE_READ] test precedes its [import_iovec] call, v6.18.46; commit
    b8e1425bae85 hoisted it there, first released in v6.8).  The second
    conjunct pins the order.

    (qemu-user's lock_iovec locks the descriptor array before it
    dispatches on the fd at all, so under qemu-user this shape answers
    -EFAULT.) *)

Example readv_write_only_fd_is_ebadf_before_import :
  check_syscall (mkInput 65 [1; 8192; 2; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EBADF) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) []
  /\ check_syscall (mkInput 65 [1; 8192; 2; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckReject.
Proof. split; check_eq. Qed.

(** A file "abcde" on fd 3 at offset [off], and a directory on fd 3. *)
Definition readv_abcde_model (off : word) : Model :=
  mkModel [(3, FdFile 1 off)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    (demo_fs_raw [([102], SFile [97; 98; 99; 100; 101])]) None None None.

Definition readv_dir_model : Model :=
  mkModel [(3, FdDir Fs.default_cwd)] (mkVmMaps [] [] 0 0 demo_limit) IEof Fs.fs_empty
    None None None.

(** A ZERO-LENGTH ENTRY, THEN A BAD BASE, on a regular file.  The
    zero-length entry is skipped and the first delivered byte lands at
    NULL, which is not writable: -EFAULT, nothing delivered, the offset
    unchanged (mm/shmem.c [shmem_file_read_iter]: [copied = 0] on the
    first folio, so [-EFAULT] is returned rather than a count).  The
    negatives are the answers qemu-user gives for this vector: its
    [lock_iovec] zeroes a bad LATER range and every following length and
    lets the host call return 0 for the empty aggregate, and the same
    vector on a directory is -EISDIR.  Neither is Linux's answer on a
    file. *)
Example readv_zero_prefix_then_bad_base_is_efault_on_a_file :
  let mem := mem_iov_pair 0 0 0 1 in
  let m := readv_abcde_model 0 in
  check_syscall (mkInput 65 [3; 8192; 2; 0; 0; 0] mem (fun _ => None))
    (with_copyins (import_iovecs_accesses mem 8192 2)
       (mkEffect (errno_ret EFAULT) [] [])) m
  = CheckOk m []
  /\ check_syscall (mkInput 65 [3; 8192; 2; 0; 0; 0] mem (fun _ => None))
       (with_copyins (import_iovecs_accesses mem 8192 2) (mkEffect 0 [] [])) m
     = CheckReject
  /\ check_syscall (mkInput 65 [3; 8192; 2; 0; 0; 0] mem (fun _ => None))
       (with_copyins (import_iovecs_accesses mem 8192 2)
          (mkEffect (errno_ret EISDIR) [] [])) m
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** THE SAME VECTOR ON A DIRECTORY never reaches a copy: the entries
    import (an in-range NULL base passes [access_ok]; whether it is mapped
    is not asked), the aggregate is 1, and fs/libfs.c [generic_read_dir]
    answers -EISDIR without touching the destination.  qemu-user's 0 and
    -EFAULT for this vector are both refused.  The second pair puts a
    WRITABLE first entry ahead of the NULL one, and pins that -EFAULT is
    not admitted for a bad later base either. *)
Example readv_directory_never_consults_the_destination :
  let mem := mem_iov_pair 0 0 0 1 in
  let mem2 := mem_iov_pair 4096 1 0 1 in
  let m := readv_dir_model in
  check_syscall (mkInput 65 [3; 8192; 2; 0; 0; 0] mem (fun _ => None))
    (with_copyins (import_iovecs_accesses mem 8192 2)
       (mkEffect (errno_ret EISDIR) [] [])) m
  = CheckOk m []
  /\ check_syscall (mkInput 65 [3; 8192; 2; 0; 0; 0] mem (fun _ => None))
       (with_copyins (import_iovecs_accesses mem 8192 2) (mkEffect 0 [] [])) m
     = CheckReject
  /\ check_syscall (mkInput 65 [3; 8192; 2; 0; 0; 0] mem (fun _ => None))
       (with_copyins (import_iovecs_accesses mem 8192 2)
          (mkEffect (errno_ret EFAULT) [] [])) m
     = CheckReject
  /\ check_syscall (mkInput 65 [3; 8192; 2; 0; 0; 0] mem2 wmem_readv_one)
       (with_copyins (import_iovecs_accesses mem2 8192 2)
          (mkEffect (errno_ret EISDIR) [] [])) m
     = CheckOk m []
  /\ check_syscall (mkInput 65 [3; 8192; 2; 0; 0; 0] mem2 wmem_readv_one)
       (with_copyins (import_iovecs_accesses mem2 8192 2)
          (mkEffect (errno_ret EFAULT) [] [])) m
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** WHAT THE DESTINATION CAN SAY ON A DIRECTORY, IT SAYS AT IMPORT.  An
    entry whose range leaves the user address space — base 1 with length
    [TASK_SIZE], so [addr <= TASK_SIZE - size] fails by one — is -EFAULT
    from [__import_iovec]'s per-segment [access_ok], ahead of
    [generic_read_dir]; -EISDIR is not admitted.  Stated against the
    constant rather than a number so that it pins the ORDER, import
    before the read operation, whatever value the limit takes. *)
Example readv_directory_import_range_fault_beats_eisdir :
  let mem := mem_iov_pair 1 (Z_to_bv 64 TASK_SIZE) 4096 3 in
  let m := readv_dir_model in
  check_syscall (mkInput 65 [3; 8192; 2; 0; 0; 0] mem wmem_readv_one)
    (with_copyins (import_iovecs_accesses mem 8192 2)
       (mkEffect (errno_ret EFAULT) [] [])) m
  = CheckOk m []
  /\ check_syscall (mkInput 65 [3; 8192; 2; 0; 0; 0] mem wmem_readv_one)
       (with_copyins (import_iovecs_accesses mem 8192 2)
          (mkEffect (errno_ret EISDIR) [] [])) m
     = CheckReject.
Proof. split; check_eq. Qed.

(** [copy_iovec_from_user] loads BOTH fields of a descriptor before it
    tests the sign of [iov_len] (lib/iov_iter.c, v6.18.46), so a readable
    negative length beside an UNREADABLE base is -EFAULT, not -EINVAL:
    the base load faults first.  Here the first entry's base bytes
    (8192..8199) are absent and its length bytes hold 2^63.  Reachable
    on a real kernel through a page-granular hole with the array
    straddling the boundary.  The copy-in ledger is the length field
    alone, 8200..8207: [iov_len] is loaded first, and the fault on
    [iov_base] ends the copy. *)
Definition mem_readv_len_only : word -> option byte :=
  fun a =>
    if bv_leu 8200 a && bv_ltu a 8224 then
      nth_error (word_le8 (Z_to_bv 64 (2 ^ 63)) ++ word_le8 4096 ++ word_le8 1)
        (Z.to_nat (bv_unsigned a - 8200))
    else None.

Example readv_unreadable_base_faults_before_the_sign_test :
  import_iovecs_accesses mem_readv_len_only 8192 2 = [(8200, 8%nat)]
  /\ check_syscall (mkInput 65 [0; 8192; 2; 0; 0; 0] mem_readv_len_only (fun _ => None))
       (with_copyins (import_iovecs_accesses mem_readv_len_only 8192 2)
          (mkEffect (errno_ret EFAULT) [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) []
  /\ check_syscall (mkInput 65 [0; 8192; 2; 0; 0; 0] mem_readv_len_only (fun _ => None))
       (with_copyins (import_iovecs_accesses mem_readv_len_only 8192 2)
          (mkEffect (errno_ret EINVAL) [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** A DESCRIPTOR WHOSE LENGTH FAULTS WAS NOT READ.  [copy_iovec_from_user]
    loads [iov_len] before [iov_base] (lib/iov_iter.c:1272-1273,
    v6.18.46), and a fault leaves at once.  Here the descriptor at 69624
    straddles a page boundary: its [iov_base] bytes, 69624..69631, end a
    MAP_NORESERVE page that nothing has touched, so they read as zero,
    and its [iov_len] bytes, 69632..69639, are unmapped.  Linux returns -EFAULT having read
    nothing, so the ledger is empty on each path: readv at a count of 2
    ([copy_iovecs_aux]) and of 1 ([__import_iovec_ubuf]), and the bare
    [copy_iovecs_accesses] underneath both.  The
    empty ledger charges no backing; the whole-descriptor range
    [(69624, 16)] would charge the lazy page for a read Linux did not
    make.
    The two [check_syscall] conjuncts pin the ledger readv answers with. *)
Definition iov_len_fault_model : Model :=
  vm_add_lazy 65536 4096
    (with_vmmaps (mkVmMaps [] [(65536, 4096)] 0 0 4096)
       (init_model [] 0 0 demo_sp 4096 (demo_input Fs.fs_empty IEof))).

Definition mem_iov_base_only : word -> option byte :=
  fun a =>
    if bv_leu 69624 a && bv_ltu a 69632
    then nth_error (word_le8 0) (Z.to_nat (bv_unsigned a - 69624))
    else None.

Example readv_iov_len_fault_reads_nothing :
  import_iovecs mem_iov_base_only 69624 2 = ImpFault
  /\ import_iovecs_accesses mem_iov_base_only 69624 2 = []
  /\ import_iovecs mem_iov_base_only 69624 1 = ImpFault
  /\ import_iovecs_accesses mem_iov_base_only 69624 1 = []
  /\ copy_iovecs_aux mem_iov_base_only 69624 1 = ImpFault
  /\ copy_iovecs_accesses mem_iov_base_only 69624 1 = []
  /\ vm_backing_used iov_len_fault_model = 0%Z
  /\ materialize_model_accesses iov_len_fault_model
       (import_iovecs_accesses mem_iov_base_only 69624 2)
     = Some iov_len_fault_model
  /\ option_map vm_backing_used
       (materialize_model_accesses iov_len_fault_model [(69624, 16%nat)])
     = Some 4096%Z
  /\ check_syscall (mkInput 65 [0; 69624; 2; 0; 0; 0] mem_iov_base_only (fun _ => None))
       (with_copyins [] (mkEffect (errno_ret EFAULT) [] []))
       iov_len_fault_model
     = CheckOk iov_len_fault_model []
  /\ check_syscall (mkInput 65 [0; 69624; 2; 0; 0; 0] mem_iov_base_only (fun _ => None))
       (with_copyins [(69624, 16%nat)] (mkEffect (errno_ret EFAULT) [] []))
       iov_len_fault_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** The other side of the same boundary: [iov_len], 69632..69639, is
    readable and [iov_base], 69624..69631, is not.  The length was read
    before the base faulted, so the ledger is those 8 bytes, at a count
    of 2 and at a count of 1. *)
Definition mem_iov_len_only : word -> option byte :=
  fun a =>
    if bv_leu 69632 a && bv_ltu a 69640
    then nth_error (word_le8 1) (Z.to_nat (bv_unsigned a - 69632))
    else None.

Example readv_iov_base_fault_records_the_length :
  import_iovecs mem_iov_len_only 69624 2 = ImpFault
  /\ import_iovecs_accesses mem_iov_len_only 69624 2 = [(69632, 8%nat)]
  /\ import_iovecs mem_iov_len_only 69624 1 = ImpFault
  /\ import_iovecs_accesses mem_iov_len_only 69624 1 = [(69632, 8%nat)]
  /\ copy_iovecs_accesses mem_iov_len_only 69624 1 = [(69632, 8%nat)].
Proof. repeat split; check_eq. Qed.

(** [rw_verify_area]'s position test (fs/read_write.c, v6.18.46): a
    nonempty readv of a regular file at offset [LLONG_MAX] is -EINVAL —
    [(loff_t)(pos + count) < 0] — where an offset merely past end-of-file
    is 0.  Reachable, since [lseek(fd, LLONG_MAX, SEEK_SET)] succeeds on
    tmpfs.  The scalar [read] makes the same test ([vfs_read],
    fs/read_write.c:563-565): the last two conjuncts pin its -EINVAL and
    refuse the end-of-file 0 the model used to answer there. *)
Example readv_at_llong_max_is_einval_not_eof :
  let m := readv_abcde_model (Z_to_bv 64 (2 ^ 63 - 1)) in
  check_syscall (mkInput 65 [3; 8192; 1; 0; 0; 0] mem_readv_iov wmem_readv_one)
    (with_copyins (import_iovecs_accesses mem_readv_iov 8192 1)
       (mkEffect (errno_ret EINVAL) [] [])) m
  = CheckOk m []
  /\ check_syscall (mkInput 65 [3; 8192; 1; 0; 0; 0] mem_readv_iov wmem_readv_one)
       (with_copyins (import_iovecs_accesses mem_readv_iov 8192 1)
          (mkEffect 0 [] [])) m
     = CheckReject
  /\ check_syscall (mkInput 63 [3; 4096; 1; 0; 0; 0] (fun _ => None) wmem_readv_one)
       (mkEffect (errno_ret EINVAL) [] []) m
     = CheckOk m []
  /\ check_syscall (mkInput 63 [3; 4096; 1; 0; 0; 0] (fun _ => None) wmem_readv_one)
       (mkEffect 0 [] []) m
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** [rw_verify_area]'s position test on the SCALAR [read] and [write] of
    a regular file, on each positional kind: [FdFile] and [FdFileRW] for
    [read], [FdFileW] and [FdFileRW] for [write].  [vfs_read] and
    [vfs_write] call it after [access_ok] and before the [MAX_RW_COUNT]
    clamp (fs/read_write.c:560-567 and :674-681, Linux v6.18.46), and it
    answers -EINVAL when [pos] is negative (:462-464) or [pos + count]
    passes [LLONG_MAX] (:467-469), for every file the model holds: none
    has [FOP_UNSIGNED_OFFSET].

    WHAT EACH ANSWER USED TO BE, which is what the refused conjuncts
    name.  A one-byte read at [LLONG_MAX] answered 0, as at end-of-file.
    A one-byte write there met [modeled_file_gap] first and declined,
    and a write on a file already within [Uaccess.rw_bytes_max] of the
    offset was judged as a delivering write.  Reaching the offset needs
    [lseek(fd, LLONG_MAX, SEEK_SET)] to succeed, which it does on tmpfs
    ([s_maxbytes] is [MAX_LFS_FILESIZE]). *)
Definition rw_pos_model (e : FdEntry) : Model :=
  mkModel [(3, e)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    (demo_fs_raw [([102], SFile [104; 105])]) None None None.

Definition rw_pos_llong_max : word := Z_to_bv 64 (2 ^ 63 - 1).

Definition rw_pos_rmem : word -> option byte :=
  fun a => if bv_eqb a 4096 then Some 122 else None.

(** The model a read that delivers nothing leaves: the descriptor
    written back at its offset.  A zero-length write leaves the same,
    with the file's bytes written back unchanged ([Fs.file_write] of no
    bytes is the identity). *)
Definition rw_pos_after_read (e : FdEntry) : Model :=
  let m := rw_pos_model e in with_fds (fd_insert (m_fds m) 3 e) m.

Definition rw_pos_after_write0 (e : FdEntry) : Model :=
  let m := rw_pos_model e in
  with_fds (fd_insert (m_fds m) 3 e)
    (with_fs (fs_set_ino_data (m_fs m) 1 (fs_ino_data (m_fs m) 1)) m).

Example read_at_llong_max_is_einval :
  let rd e r := check_syscall (mkInput 63 [3; 4096; 1; 0; 0; 0] (fun _ => None) wmem_readv_one)
                  r (rw_pos_model e) in
  rd (FdFile 1 rw_pos_llong_max) (mkEffect (errno_ret EINVAL) [] [])
    = CheckOk (rw_pos_model (FdFile 1 rw_pos_llong_max)) []
  /\ rd (FdFile 1 rw_pos_llong_max) (mkEffect 0 [] []) = CheckReject
  /\ rd (FdFileRW 1 rw_pos_llong_max) (mkEffect (errno_ret EINVAL) [] [])
       = CheckOk (rw_pos_model (FdFileRW 1 rw_pos_llong_max)) []
  /\ rd (FdFileRW 1 rw_pos_llong_max) (mkEffect 0 [] []) = CheckReject.
Proof. split_conj; check_eq. Qed.

Example write_at_llong_max_is_einval :
  let wr e r := check_syscall (mkInput 64 [3; 4096; 1; 0; 0; 0] rw_pos_rmem (fun _ => None))
                  r (rw_pos_model e) in
  wr (FdFileW 1 rw_pos_llong_max) (mkEffect (errno_ret EINVAL) [] [])
    = CheckOk (rw_pos_model (FdFileW 1 rw_pos_llong_max)) []
  /\ wr (FdFileW 1 rw_pos_llong_max) (with_copyins [(4096, 1%nat)] (mkEffect 1 [] []))
       = CheckReject
  /\ wr (FdFileRW 1 rw_pos_llong_max) (mkEffect (errno_ret EINVAL) [] [])
       = CheckOk (rw_pos_model (FdFileRW 1 rw_pos_llong_max)) []
  /\ wr (FdFileRW 1 rw_pos_llong_max) (with_copyins [(4096, 1%nat)] (mkEffect 1 [] []))
       = CheckReject.
Proof. split_conj; check_eq. Qed.

(** ...AND [access_ok] COMES FIRST on these arms as on the append one
    ([append_write_access_ok_precedes_the_position_test]): a range that
    leaves the user address space is -EFAULT at a position that would
    otherwise be -EINVAL (fs/read_write.c:560-565 and :674-679).  [buf]
    is [2 ^ 47], the first address whose one-byte range is past
    [State.TASK_SIZE]. *)
Example scalar_access_ok_precedes_the_position_test :
  let top := Z_to_bv 64 (2 ^ 47) in
  let call n e r := check_syscall (mkInput n [3; top; 1; 0; 0; 0] (fun _ => None) (fun _ => None))
                      r (rw_pos_model e) in
  call 63 (FdFile 1 rw_pos_llong_max) (mkEffect (errno_ret EFAULT) [] [])
    = CheckOk (rw_pos_model (FdFile 1 rw_pos_llong_max)) []
  /\ call 63 (FdFile 1 rw_pos_llong_max) (mkEffect (errno_ret EINVAL) [] []) = CheckReject
  /\ call 63 (FdFileRW 1 rw_pos_llong_max) (mkEffect (errno_ret EFAULT) [] [])
       = CheckOk (rw_pos_model (FdFileRW 1 rw_pos_llong_max)) []
  /\ call 63 (FdFileRW 1 rw_pos_llong_max) (mkEffect (errno_ret EINVAL) [] []) = CheckReject
  /\ call 64 (FdFileW 1 rw_pos_llong_max) (mkEffect (errno_ret EFAULT) [] [])
       = CheckOk (rw_pos_model (FdFileW 1 rw_pos_llong_max)) []
  /\ call 64 (FdFileW 1 rw_pos_llong_max) (mkEffect (errno_ret EINVAL) [] []) = CheckReject
  /\ call 64 (FdFileRW 1 rw_pos_llong_max) (mkEffect (errno_ret EFAULT) [] [])
       = CheckOk (rw_pos_model (FdFileRW 1 rw_pos_llong_max)) []
  /\ call 64 (FdFileRW 1 rw_pos_llong_max) (mkEffect (errno_ret EINVAL) [] []) = CheckReject.
Proof. split_conj; check_eq. Qed.

(** THE BOUNDARY, from below.  The test is [pos + count > LLONG_MAX],
    so a call whose end is exactly [LLONG_MAX] passes it, and so does a
    zero count AT [LLONG_MAX]: [pos + 0] is not negative (:467).  Each
    such call gets the answer it gets anywhere past end-of-file, and the
    -EINVAL is refused:
    - [read] of one byte at [LLONG_MAX - 1], and of zero bytes at
      [LLONG_MAX]: 0, the descriptor unmoved;
    - [write] of zero bytes at [LLONG_MAX]: 0, the file unchanged.  A
      zero-length write opens no hole, so [modeled_file_gap] admits it;
    - [write] of one byte at [LLONG_MAX - 1]: past the position test it
      meets [modeled_file_gap], which declines a hole of almost [2^63]
      bytes.  That decline is the model's own bound and not a kernel
      answer; what this conjunct pins is that the -EINVAL is not it. *)
Example scalar_position_test_boundary :
  let below := Z_to_bv 64 (2 ^ 63 - 2) in
  let rd e n r := check_syscall (mkInput 63 [3; 4096; n; 0; 0; 0] (fun _ => None) wmem_readv_one)
                    r (rw_pos_model e) in
  let wr e n r := check_syscall (mkInput 64 [3; 4096; n; 0; 0; 0] rw_pos_rmem (fun _ => None))
                    r (rw_pos_model e) in
  rd (FdFile 1 below) 1 (mkEffect 0 [] []) = CheckOk (rw_pos_after_read (FdFile 1 below)) []
  /\ rd (FdFile 1 below) 1 (mkEffect (errno_ret EINVAL) [] []) = CheckReject
  /\ rd (FdFileRW 1 below) 1 (mkEffect 0 [] [])
       = CheckOk (rw_pos_after_read (FdFileRW 1 below)) []
  /\ rd (FdFile 1 rw_pos_llong_max) 0 (mkEffect 0 [] [])
       = CheckOk (rw_pos_after_read (FdFile 1 rw_pos_llong_max)) []
  /\ rd (FdFile 1 rw_pos_llong_max) 0 (mkEffect (errno_ret EINVAL) [] []) = CheckReject
  /\ wr (FdFileW 1 rw_pos_llong_max) 0 (mkEffect 0 [] [])
       = CheckOk (rw_pos_after_write0 (FdFileW 1 rw_pos_llong_max)) []
  /\ wr (FdFileW 1 rw_pos_llong_max) 0 (mkEffect (errno_ret EINVAL) [] []) = CheckReject
  /\ wr (FdFileRW 1 rw_pos_llong_max) 0 (mkEffect 0 [] [])
       = CheckOk (rw_pos_after_write0 (FdFileRW 1 rw_pos_llong_max)) []
  /\ rd (FdFileRW 1 rw_pos_llong_max) 0 (mkEffect 0 [] [])
       = CheckOk (rw_pos_after_read (FdFileRW 1 rw_pos_llong_max)) []
  /\ wr (FdFileW 1 below) 1 (mkEffect (errno_ret EINVAL) [] []) = CheckUnmodeled
  /\ wr (FdFileRW 1 below) 1 (mkEffect (errno_ret EINVAL) [] []) = CheckUnmodeled.
Proof. split_conj; check_eq. Qed.

(** ...AND THE ONE-BYTE WRITE AT [LLONG_MAX - 1] WHERE THE MODEL HAS NO
    HOLE TO DECLINE.  Its end is exactly [LLONG_MAX], so [rw_verify_area]
    (fs/read_write.c:467-469, Linux v6.18.46) passes it.  On a file that
    already holds [LLONG_MAX - 1] bytes it opens no hole, so the model
    delivers the byte, as [vfs_write] does: it returns 1, reads one
    source byte, writes it at [LLONG_MAX - 1] and leaves the descriptor
    at [LLONG_MAX].  This is the only answer: the -EINVAL and a decline
    are both refused.  The file's length is abstract. *)
Lemma write_file_one_byte_at_llong_max_minus_1_delivers :
  forall i fd buf m p data x o,
  fd_lookup (m_fds m) fd = Some (FdFileW p (Z_to_bv 64 (2 ^ 63 - 2))) ->
  fs_ino_data (m_fs m) p = data ->
  Z.of_nat (length data) = (2 ^ 63 - 2)%Z ->
  access_okb buf 1 = true ->
  in_mem i buf = Some x ->
  write_spec fd buf (Z_to_bv 64 1) i m o <->
  o = Ok (with_copyins [(buf, 1%nat)] (mkEffect (Z_to_bv 64 1) [] []))
         (with_fds (fd_insert (m_fds m) fd (FdFileW p (Z_to_bv 64 (2 ^ 63 - 1))))
            (with_fs (fs_set_ino_data (m_fs m) p
                        (file_write data (Z_to_bv 64 (2 ^ 63 - 2)) [x])) m))
         [].
Proof.
  intros i fd buf m p data x o Hfd Hfs Hlen Hok Hx.
  assert (Hok' : access_okb buf (bv_unsigned (Z_to_bv 64 1)) = true) by exact Hok.
  assert (Hg : modeled_rw_range buf (Z_to_bv 64 1) = true).
  { unfold modeled_rw_range. rewrite Hok'. apply Bool.orb_true_r. }
  assert (Hpos : rw_pos_einvalb (Z_to_bv 64 (2 ^ 63 - 2))
                   (bv_unsigned (Z_to_bv 64 1)) = false) by reflexivity.
  assert (Hw0 : w_is0 (Z_to_bv 64 1) = false) by reflexivity.
  assert (Hsrc : write_source (in_mem i) buf (Z_to_bv 64 1) = [x]).
  { unfold write_source. change (rw_count_clamp (Z_to_bv 64 1)) with 1%Z.
    rewrite readable_bytes_eq. change (word_to_nat (Z_to_bv 64 1)) with 1%nat.
    cbn [readable_bytes_aux]. rewrite Hx. reflexivity. }
  assert (Hgap : modeled_file_gap data (Z_to_bv 64 (2 ^ 63 - 2)) [x] = true).
  { unfold modeled_file_gap, modeled_zero_fill. rewrite Hlen. reflexivity. }
  assert (Hoff : (Z_to_bv 64 (2 ^ 63 - 2) + len_word [x])%bv
                 = Z_to_bv 64 (2 ^ 63 - 1)) by (apply bv_eq; reflexivity).
  assert (Hchk : forall eff, check_write i fd buf (Z_to_bv 64 1) eff m
    = check_ret_only_copyins [(buf, 1%nat)] eff (Z_to_bv 64 1)
        (with_fds (fd_insert (m_fds m) fd (FdFileW p (Z_to_bv 64 (2 ^ 63 - 1))))
           (with_fs (fs_set_ino_data (m_fs m) p
                       (file_write data (Z_to_bv 64 (2 ^ 63 - 2)) [x])) m))
        []).
  { intro eff. unfold check_write. rewrite Hfd. cbv beta iota.
    rewrite Hg, Hok', Hpos. cbn [negb]. cbv beta iota zeta.
    rewrite Hsrc, Hw0. cbn [negb andb length Nat.eqb]. cbv beta iota zeta.
    rewrite Hfs, Hgap, Hoff. cbn [negb]. cbv beta iota.
    reflexivity. }
  split.
  - intro H. destruct o as [eff m' evs|].
    + apply check_write_complete_ok in H. rewrite Hchk in H.
      apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
      reflexivity.
    + apply check_write_complete_unmodeled with (eff := mkEffect 0 [] []) in H.
      rewrite Hchk in H. exfalso.
      exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ H).
  - intros ->. apply check_write_sound_ok. rewrite Hchk.
    apply check_ret_only_copyins_ok_iff. split; [reflexivity | split; reflexivity].
Qed.

(** A NEGATIVE POSITION.  [rw_verify_area] answers -EINVAL for
    [pos < 0] at ANY count, a zero one included (fs/read_write.c:462-464),
    and [rw_pos_einvalb] does too: an [off] of [2^63] or more makes the
    sum pass [2^63 - 1] whatever the count.  No [lseek] reaches this
    ([lseek_dest] answers only offsets under [2^63]).  It is pinned
    because the model's states include such a descriptor, and the
    answer there must still be Linux's. *)
Example scalar_negative_position_is_einval :
  let neg := Z_to_bv 64 (2 ^ 63) in
  let rd e r := check_syscall (mkInput 63 [3; 4096; 0; 0; 0; 0] (fun _ => None) wmem_readv_one)
                  r (rw_pos_model e) in
  let wr e r := check_syscall (mkInput 64 [3; 4096; 0; 0; 0; 0] rw_pos_rmem (fun _ => None))
                  r (rw_pos_model e) in
  rd (FdFile 1 neg) (mkEffect (errno_ret EINVAL) [] []) = CheckOk (rw_pos_model (FdFile 1 neg)) []
  /\ rd (FdFile 1 neg) (mkEffect 0 [] []) = CheckReject
  /\ rd (FdFileRW 1 neg) (mkEffect (errno_ret EINVAL) [] [])
       = CheckOk (rw_pos_model (FdFileRW 1 neg)) []
  /\ wr (FdFileW 1 neg) (mkEffect (errno_ret EINVAL) [] []) = CheckOk (rw_pos_model (FdFileW 1 neg)) []
  /\ wr (FdFileW 1 neg) (mkEffect 0 [] []) = CheckReject
  /\ wr (FdFileRW 1 neg) (mkEffect (errno_ret EINVAL) [] [])
       = CheckOk (rw_pos_model (FdFileRW 1 neg)) []
  /\ wr (FdFileA 1 neg) (mkEffect (errno_ret EINVAL) [] [])
       = CheckOk (rw_pos_model (FdFileA 1 neg)) [].
Proof. split_conj; check_eq. Qed.

(** ...AND A NEGATIVE POSITION WHOSE 64-BIT SUM WRAPS: [pos = -1] and
    [count = 1] make [(loff_t)(pos + count)] 0, so only the [pos < 0]
    branch (fs/read_write.c:462-464) answers -EINVAL.  A predicate that
    transcribed the sum test (:467-469) alone would answer this read 0
    and decline this write. *)
Example scalar_negative_position_wrapping_sum_is_einval :
  let m1 := Z_to_bv 64 (2 ^ 64 - 1) in
  let rd e r := check_syscall (mkInput 63 [3; 4096; 1; 0; 0; 0] (fun _ => None) wmem_readv_one)
                  r (rw_pos_model e) in
  let wr e r := check_syscall (mkInput 64 [3; 4096; 1; 0; 0; 0] rw_pos_rmem (fun _ => None))
                  r (rw_pos_model e) in
  rd (FdFile 1 m1) (mkEffect (errno_ret EINVAL) [] []) = CheckOk (rw_pos_model (FdFile 1 m1)) []
  /\ rd (FdFile 1 m1) (mkEffect 0 [] []) = CheckReject
  /\ rd (FdFileRW 1 m1) (mkEffect (errno_ret EINVAL) [] [])
       = CheckOk (rw_pos_model (FdFileRW 1 m1)) []
  /\ wr (FdFileW 1 m1) (mkEffect (errno_ret EINVAL) [] []) = CheckOk (rw_pos_model (FdFileW 1 m1)) []
  /\ wr (FdFileRW 1 m1) (mkEffect (errno_ret EINVAL) [] [])
       = CheckOk (rw_pos_model (FdFileRW 1 m1)) [].
Proof. split_conj; check_eq. Qed.

(** THE TEST READS THE COUNT THE CALL NAMED: [vfs_read] and [vfs_write]
    call [rw_verify_area] before the [MAX_RW_COUNT] clamp
    (fs/read_write.c:563-567, :677-681).  At [2^63 - 2^31] a count of
    [2^32] passes [LLONG_MAX], where the clamped count [0x7ffff000]
    would not: an arm that tested the clamped count would answer this
    read 0 and decline this write. *)
Example scalar_position_test_reads_the_unclamped_count :
  let off := Z_to_bv 64 (2 ^ 63 - 2 ^ 31) in
  let big := Z_to_bv 64 (2 ^ 32) in
  let rd e r := check_syscall (mkInput 63 [3; 4096; big; 0; 0; 0] (fun _ => None) wmem_readv_one)
                  r (rw_pos_model e) in
  let wr e r := check_syscall (mkInput 64 [3; 4096; big; 0; 0; 0] rw_pos_rmem (fun _ => None))
                  r (rw_pos_model e) in
  rd (FdFile 1 off) (mkEffect (errno_ret EINVAL) [] []) = CheckOk (rw_pos_model (FdFile 1 off)) []
  /\ rd (FdFile 1 off) (mkEffect 0 [] []) = CheckReject
  /\ rd (FdFileRW 1 off) (mkEffect (errno_ret EINVAL) [] [])
       = CheckOk (rw_pos_model (FdFileRW 1 off)) []
  /\ wr (FdFileW 1 off) (mkEffect (errno_ret EINVAL) [] [])
       = CheckOk (rw_pos_model (FdFileW 1 off)) []
  /\ wr (FdFileRW 1 off) (mkEffect (errno_ret EINVAL) [] [])
       = CheckOk (rw_pos_model (FdFileRW 1 off)) [].
Proof. split_conj; check_eq. Qed.

(** ...AND IT PRECEDES THE FAULTING SOURCE: [rw_verify_area] runs before
    [write_iter] (fs/read_write.c:677-679), so an unreadable source at
    [LLONG_MAX] is -EINVAL with the file not extended, where an arm that
    made the test after the faulting-source path would decline. *)
Example scalar_position_test_precedes_the_faulting_source :
  let wr e r := check_syscall (mkInput 64 [3; 4096; 1; 0; 0; 0] (fun _ => None) (fun _ => None))
                  r (rw_pos_model e) in
  wr (FdFileW 1 rw_pos_llong_max) (mkEffect (errno_ret EINVAL) [] [])
    = CheckOk (rw_pos_model (FdFileW 1 rw_pos_llong_max)) []
  /\ wr (FdFileW 1 rw_pos_llong_max) (mkEffect (errno_ret EFAULT) [] []) = CheckReject
  /\ wr (FdFileRW 1 rw_pos_llong_max) (mkEffect (errno_ret EINVAL) [] [])
       = CheckOk (rw_pos_model (FdFileRW 1 rw_pos_llong_max)) []
  /\ wr (FdFileRW 1 rw_pos_llong_max) (mkEffect (errno_ret EFAULT) [] []) = CheckReject.
Proof. split_conj; check_eq. Qed.

(** A PARTIALLY WRITABLE DESTINATION ON A PIPE IS DECLINED.  Five bytes
    are queued on stdin and the vector holds five, but only the first
    four destination bytes are writable: fs/pipe.c [anon_pipe_read]
    answers -EFAULT with four bytes stored and nothing consumed if the
    five arrived in one buffer, and a count of whole buffers otherwise,
    so the model declines the five-byte delivery, the -EFAULT and the
    four-byte short read alike.  Give it the fifth byte and the delivery
    is admitted: the decline is exactly [w < min total remaining].  The
    scalar [read] follows the same rule. *)
Definition hello_stdin : InputStream :=
  ICons 104 (ICons 101 (ICons 108 (ICons 108 (ICons 111 IEof)))).

Definition wmem_first (n : Z) : word -> option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a (Z_to_bv 64 (4096 + n)) then Some 0 else None.

Example partial_destination_on_a_pipe_declines :
  let mem := mem_iov_pair 4096 2 4098 3 in
  let m := init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) hello_stdin) in
  let delivered := mkEffect 5 [(4096, [104; 101]); (4098, [108; 108; 111])] [] in
  check_syscall (mkInput 65 [0; 8192; 2; 0; 0; 0] mem (wmem_first 4))
    (with_copyins (import_iovecs_accesses mem 8192 2) delivered) m
  = CheckUnmodeled
  /\ check_syscall (mkInput 65 [0; 8192; 2; 0; 0; 0] mem (wmem_first 4))
       (with_copyins (import_iovecs_accesses mem 8192 2)
          (mkEffect (errno_ret EFAULT) [] [])) m
     = CheckUnmodeled
  /\ check_syscall (mkInput 65 [0; 8192; 2; 0; 0; 0] mem (wmem_first 4))
       (with_copyins (import_iovecs_accesses mem 8192 2)
          (mkEffect 4 [(4096, [104; 101]); (4098, [108; 108])] [])) m
     = CheckUnmodeled
  /\ check_syscall (mkInput 65 [0; 8192; 2; 0; 0; 0] mem (wmem_first 5))
       (with_copyins (import_iovecs_accesses mem 8192 2) delivered) m
     = CheckOk (with_stdin IEof m)
         [ReadEv 0 104; ReadEv 0 101; ReadEv 0 108; ReadEv 0 108; ReadEv 0 111]
  /\ check_syscall (mkInput 63 [0; 4096; 100; 0; 0; 0] (fun _ => None) (wmem_first 4))
       (mkEffect 4 [(4096, [104; 101; 108; 108])] []) m
     = CheckUnmodeled
  /\ check_syscall (mkInput 63 [0; 4096; 100; 0; 0; 0] (fun _ => None) (wmem_first 5))
       (mkEffect 5 [(4096, [104; 101; 108; 108; 111])] []) m
     = CheckOk (with_stdin IEof m)
         [ReadEv 0 104; ReadEv 0 101; ReadEv 0 108; ReadEv 0 108; ReadEv 0 111].
Proof. split_conj; check_eq. Qed.

(* =========================================================================
   PART 4 — fail-closed, and the model state no observation reveals

   The rest of the per-syscall checks: cases a real run could reach only
   by making a REAL kernel misbehave, cases about model-internal
   bookkeeping, and the places qemu-user is known to diverge from
   Linux.
   ========================================================================= *)

(** An unmodeled syscall number (umask = 166) is a model error — the
    dispatcher fails closed, so the trace semantics takes the [SError]
    transition.  Fatal for a target, so source binaries must keep away
    from unmodeled syscalls.  This is the shape of every [CheckUnmodeled]
    verdict in the development.

    Pick a number here that the dispatcher really does not cover, because
    the example does not fail loudly when its number gets an arm.  A
    modeled [uname] on an unmapped destination, for example, is
    [Unmodeled] too — for a different reason, a copy the model will not
    tear — so an example on it would go on computing to [CheckUnmodeled]
    and say nothing about the fallback arm it is named for.  A number
    whose decline is a JUDGEMENT rather than a missing field is what
    keeps it honest; umask is not modeled. *)

Definition lseek_model : Model :=
  mkModel [(0, FdChannel 0); (3, FdFile 1 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    (demo_fs_raw [([102], SFile [104; 105])]) None None None.

(** Channels are unseekable streams: -ESPIPE. *)

Example lseek_channel_espipe :
  check_syscall (mkInput 62 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ESPIPE) [] []) lseek_model
  = CheckOk lseek_model [].
Proof. check_eq. Qed.

(** The whence check precedes the fd's KIND, which is what makes an
    unseekable fd answer -EINVAL rather than -ESPIPE: [ksys_lseek]
    (fs/read_write.c, Linux v6.18.46) tests [whence <= SEEK_MAX] before
    calling [vfs_llseek], and [SEEK_MAX] is [SEEK_HOLE], 4.  So on a pipe
    whence 42 is -EINVAL and whence 4 is -ESPIPE.  (A run on a real pipe
    under qemu-riscv64, which is not a supported implementation, showed
    the same.) *)

Example lseek_channel_bad_whence_is_einval_not_espipe :
  check_syscall (mkInput 62 [0; 0; 42; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) lseek_model
  = CheckOk lseek_model []
  /\ check_syscall (mkInput 62 [0; 0; 42; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ESPIPE) [] []) lseek_model
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** A whence the kernel DOES accept (SEEK_HOLE = 4 = [SEEK_MAX]) still
    reaches the fd's kind, so a channel is -ESPIPE there. *)

Example lseek_channel_seek_hole_is_espipe :
  check_syscall (mkInput 62 [0; 0; 4; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ESPIPE) [] []) lseek_model
  = CheckOk lseek_model [].
Proof. check_eq. Qed.

(** On a FILE, SEEK_DATA/SEEK_HOLE are answered by real filesystems —
    with a filesystem-dependent notion of a hole — so the model fails
    CLOSED there rather than claiming an -EINVAL. *)

Example lseek_seek_data_on_a_file_is_unmodeled :
  check_syscall (mkInput 62 [3; 0; 3; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) lseek_model
  = CheckUnmodeled
  /\ check_syscall (mkInput 62 [3; 0; 4; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 2 [] []) lseek_model
     = CheckUnmodeled
  (* AND THE TWO NEIGHBOURS THAT STILL ANSWER, one along each axis, so
     the pair above is a boundary rather than a description of one.
     Both declines are [CheckUnmodeled] and would survive [lseek]
     declining MORE -- SEEK_HOLE going unmodeled on the channel too, or
     the file arm going quiet on every whence.  So: whence 4 on the
     CHANNEL is still -ESPIPE, and whence 2 (SEEK_END) on the FILE still
     reports the size and advances the offset. *)
  /\ check_syscall (mkInput 62 [0; 0; 4; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ESPIPE) [] []) lseek_model
     = CheckOk lseek_model []
  /\ check_syscall (mkInput 62 [3; 0; 2; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 2 [] []) lseek_model
     = CheckOk (with_fds (fd_insert (m_fds lseek_model) 3 (FdFile 1 2))
                  lseek_model) [].
Proof.
  split; [vm_compute; reflexivity
         |split; [vm_compute; reflexivity|split; check_eq]].
Qed.

(** [SYSCALL_DEFINE3(lseek, unsigned int, fd, off_t, offset,
    unsigned int, whence)]: the origin selector is truncated exactly like
    the fd, so lseek(3, 0, 2^32 | SEEK_END) is a SEEK_END and reports the
    file size.  A model that compared the full register would demand
    -EINVAL — a return no kernel produces — and so REJECT a conforming
    trace.  A real run can show the accepting half; that the -EINVAL is
    inadmissible it cannot. *)

Example lseek_whence_high_bits_einval_rejected :
  check_syscall (mkInput 62 [3; 0; Z_to_bv 64 (2 ^ 32 + 2); 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect 2 [] []) lseek_model
  = CheckOk (with_fds (fd_insert (m_fds lseek_model) 3 (FdFile 1 2))
               lseek_model) []
  /\ check_syscall (mkInput 62 [3; 0; Z_to_bv 64 (2 ^ 32 + 2); 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) lseek_model
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** The whence checks are ORDERED as [ksys_lseek] orders them: the fd is
    resolved first, so a whence no kernel accepts does not turn a bad fd
    into -EINVAL. *)

Example lseek_bad_fd_beats_a_bad_whence :
  check_syscall (mkInput 62 [9; 0; 42; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EBADF) [] []) lseek_model
  = CheckOk lseek_model []
  /\ check_syscall (mkInput 62 [9; 0; 42; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) lseek_model
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(* -------------------------------------------------------------------------
   ftruncate on a writable file fd whose path is NOT in the file system.

   Every other arm of [Open.ftruncate_spec] is reachable from a real
   run — including all five fd kinds, the negative length decided
   before the fd lookup, and both sides of the grow bound.  THIS arm is the exception:
   [Open.create_wronly] inserts the path into [m_fs] in the same step
   that hands out the [FdFileW], so no run can reach an [FdFileW]
   pointing at an absent file.  The arm exists because the spec cannot
   appeal to that invariant locally, and it fails closed rather than
   inventing an answer; this pins that it does.
   ------------------------------------------------------------------------- *)

(** fd 3 is open write-only on "f", but "f" is not in the file system. *)

(* -------------------------------------------------------------------------
   ioctl on a CHANNEL.  Whether a run's standard channels are terminals
   is the environment's business, not the model's.
   ------------------------------------------------------------------------- *)

(** TIOCGWINSZ — stdio's buffering-mode probe — answers -ENOTTY on a
    channel. *)

Example bit31_is_part_of_the_32_bit_arguments :
  check_syscall (mkInput 62 [3; 5; Z_to_bv 64 (2 ^ 31 + 2); 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) lseek_model
  = CheckOk lseek_model []
  /\ check_syscall (mkInput 64 [Z_to_bv 64 (2 ^ 31 + 1); 4096; 2; 0; 0; 0]
                     mem_ab (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) []
  /\ check_syscall (mkInput 29 [Z_to_bv 64 (2 ^ 31 + 1); TIOCGWINSZ; 4096; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) []
  /\ check_syscall (mkInput 29 [1; Z_to_bv 64 (2 ^ 31 + 21523); 4096; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ENOTTY) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckUnmodeled.
Proof. split; [|split; [|split]]; first [check_eq | vm_compute; reflexivity]. Qed.

(** The empty pathname always fails with -ENOENT (path_resolution(7)),
    EVEN WHEN the file-system image contains an empty-path key — open("")
    must not match it.  A real run has one image, so only a Rocq
    literal can quantify the image this way.  Path bytes at
    8192: NUL only. *)

(* -------------------------------------------------------------------------
   Three answers Linux can produce that the model REJECTS.

   Each of these is a [CheckReject] on an honest kernel trace, so each is
   a known limitation of the model rather than a demonstration that the
   model is right.

   Every one pairs its rejection with the honest answer AT THE SAME CALL.
   That is the point of the pairing: a checker that had become constantly
   rejecting would fail these examples rather than pass them.  Each of
   the four discriminates further, and would flip to [CheckOk] if an arm
   for its limitation were added; [write_channel_epipe_rejected] says at
   its own docstring which part of its limitation is already modeled.
   ------------------------------------------------------------------------- *)

(** -EINTR on a read.  read(0, buf, 1) with one byte of input delivers
    it; no model state admits the -EINTR a caught signal produces on a
    blocking read. *)

Example read_channel_eintr_rejected :
  check_syscall (mkInput 63 [0; 4096; 1; 0; 0; 0] (fun _ => None) wmem_readv_one)
    (mkEffect 1 [(4096, [120])] [])
    (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) (ICons 120 IEof)))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) [ReadEv 0 120]
  /\ check_syscall (mkInput 63 [0; 4096; 1; 0; 0; 0] (fun _ => None) wmem_readv_one)
       (mkEffect (errno_ret EINTR) [] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) (ICons 120 IEof)))
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** -EINTR on a write.  write(1, "ab", 2) delivers both bytes; there is
    no arm for what a full pipe and a caught signal give.  fs/pipe.c
    [anon_pipe_write] returns -ERESTARTSYS, and only when nothing was
    copied; arch/riscv/kernel/signal.c [arch_do_signal_or_restart] is
    what turns that into -EINTR, on the branch where a handler runs.
    The same limitation.

    The second conjunct closes by [check_eq], which is [vm_compute], and
    that is a pin of its own: [check_write]'s channel arm converts the
    claimed return to a unary [nat] only under its range test, so an
    errno-encoded return evaluates in bounded time where a flat [&&]
    chain never came back. *)

Example write_channel_eintr_rejected :
  check_syscall (mkInput 64 [1; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
    (with_copyins [(4096, 2%nat)] (mkEffect 2 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
      [WriteEv 1 97; WriteEv 1 98]
  /\ check_syscall (mkInput 64 [1; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
       (mkEffect (errno_ret EINTR) [] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckReject.
Proof. split; check_eq. Qed.

(** -EPIPE on a channel write, on a launch whose far end HAS a reader.
    The model answers -EPIPE on a channel now, but only on a launch whose
    reader has gone ([State.in_channel_reader] false): there the channel
    arm of [ReadWrite.write_spec] raises SIGPIPE through
    [ReadWrite.raise_sigpipe] -- a death at the default disposition, the
    -EPIPE only with signal 13 blocked -- and refuses the short write
    below.  This launch is [demo_input]'s, built by the 13-place
    [State.mkProcInput], which says the reader is there, so the short
    write is admitted and -EPIPE is refused, which is right for a reader
    that stays for the whole run.  The limitation left is a reader that
    goes away PARTWAY through a run -- `prog | head -1` once [head] has
    had its line -- which the model has no term for: the reader is a
    launch fact ([State.procst_channel_reader]).  An arm that let it go
    away mid-run would admit the -EPIPE here and break the second
    conjunct. *)

Example write_channel_epipe_rejected :
  check_syscall (mkInput 64 [1; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
    (with_copyins [(4096, 1%nat)] (mkEffect 1 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) [WriteEv 1 97]
  /\ check_syscall (mkInput 64 [1; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
       (mkEffect (errno_ret EPIPE) [] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof))
     = CheckReject.
Proof. split; check_eq. Qed.

(** A SHORT write on a regular file.  [readv_write_only_model] has fd 3
    open write-only on the empty file "f", so write(3, "ab", 2) writes
    both bytes; the short positive count mm/filemap.c
    [generic_perform_write] returns when write_end fails partway
    (-ENOSPC, -EIO, -ENOMEM, -EDQUOT) is rejected. *)

Example file_write_short_rejected :
  match check_syscall (mkInput 64 [3; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
          (with_copyins [(4096, 2%nat)] (mkEffect 2 [] []))
          readv_write_only_model with
  | CheckOk m [] => file_at (m_fs m) (wk [102]) = Some [97; 98]
  | _ => False
  end
  /\ check_syscall (mkInput 64 [3; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
       (with_copyins [(4096, 1%nat)] (mkEffect 1 [] []))
       readv_write_only_model
     = CheckReject.
Proof. split; vm_compute; reflexivity. Qed.

(** ** pread64 (67) and pwrite64 (68): the claims a run cannot show

    A real run shows ONE outcome per syscall, so it can report that a
    particular pread left the offset where it was and never that EVERY
    admissible pread does.  The three lemmas here are quantified over
    all admissible outcomes for that reason; the concrete [CheckReject]
    beneath them is the rejecting half in the checker's own terms. *)

(** A PREAD MOVES NO DESCRIPTOR.  [ksys_pread64] hands [vfs_read] the
    address of its own [pos] parameter (fs/read_write.c:763, v6.18.46),
    so the advance [vfs_read] makes lands in a stack slot the syscall
    discards: the fd table, the file system, standard input and the
    trace are all as they were.  What a pread MAY move is the random
    device's declared stream, because [urandom_read_iter] reads no
    position and draws from the generator whatever the position — so
    the one field this lemma does not pin is [m_urandom], and
    [pread64_urandom_advances_the_stream] beneath says exactly what
    happens to it. *)
Lemma pread64_leaves_the_model_alone : forall fd buf count pos i m eff m' evs,
  pread64_spec fd buf count pos i m (Ok eff m' evs) ->
  m_fds m' = m_fds m /\ m_fs m' = m_fs m /\ m_stdin m' = m_stdin m /\ evs = [].
Proof.
  intros fd buf count pos i m eff m' evs H.
  apply check_pread64_complete_ok in H. unfold check_pread64, check_read_urandom in H.
  repeat (match type of H with
          | (if ?b then _ else _) = _ => destruct b
          | (match ?x with _ => _ end) = _ => destruct x
          end; cbv beta iota zeta in H);
    try discriminate;
    try (apply check_ret_only_ok_iff in H;
         destruct H as (_ & -> & ->); repeat split; reflexivity);
    try (inversion H; subst; repeat split; autorewrite with model; reflexivity).
Qed.

(** ...and on the random device, the stream it moves: a delivering
    pread leaves [m_urandom] at the remainder past the prefix it
    delivered, the same remainder a [read] delivering as much would
    leave.  How much that is the device chooses: the clamped count, or
    a page multiple below it ([Sys.Fs.ReadWrite.random_page_stopb]);
    [Checks.Cases.Fs.Open.urandom_read_stops_at_a_page] admits such a
    short pread. *)
Lemma pread64_urandom_advances_the_stream : forall fd rd wr buf count pos i m eff m' evs,
  fd_lookup (m_fds m) fd = Some (FdUrandom rd wr) ->
  pread64_spec fd buf count pos i m (Ok eff m' evs) ->
  m_urandom m' = m_urandom m
  \/ exists a bs, eff_writes eff = [(a, bs)]
       /\ m_urandom m' = snd (stream_take_z (m_urandom m) (Z.of_nat (length bs))).
Proof.
  intros fd rd wr buf count pos i m eff m' evs Hfd H.
  apply check_pread64_complete_ok in H. unfold check_pread64, check_read_urandom in H.
  rewrite Hfd in H. cbv beta iota zeta in H.
  repeat (match type of H with
          | (if ?b then _ else _) = _ => destruct b
          | (match ?x with _ => _ end) = _ => destruct x
          end; cbv beta iota zeta in H);
    try discriminate;
    try (apply check_ret_only_ok_iff in H; destruct H as (_ & -> & ->); now left);
    try (inversion H; subst; right; do 2 eexists; split; [reflexivity|];
         autorewrite with model; reflexivity).
Qed.

(** THE FMODE_PREAD GATE PRECEDES [vfs_read]'S FMODE_READ TEST.  Both
    ends of a pipe went through [stream_open] (fs/pipe.c:966-967), which
    clears the bit (fs/open.c:1658), so [ksys_pread64] answers -ESPIPE at
    fs/read_write.c:765 and never reaches the -EBADF that [read] on the
    write end of that same pipe returns.  Stated over every admissible
    outcome, so it says the -EBADF is not among them. *)
Lemma pread64_pipe_end_is_espipe : forall fd buf count pos i m id w eff m' evs,
  (0 <= bv_signed pos)%Z ->
  fd_lookup (m_fds m) fd = Some (FdPipe id w) ->
  pread64_spec fd buf count pos i m (Ok eff m' evs) ->
  eff = mkEffect (errno_ret ESPIPE) [] [].
Proof.
  intros fd buf count pos i m id w eff m' evs Hpos Hfd H.
  apply check_pread64_complete_ok in H. unfold check_pread64 in H.
  unfold ppos_einvalb in H.
  rewrite (proj2 (Z.ltb_ge _ _) Hpos) in H. cbv beta iota zeta in H.
  rewrite Hfd in H. cbv beta iota zeta in H.
  now apply check_ret_only_ok_iff in H; destruct H as (-> & _ & _).
Qed.

(** THE NEGATIVE POSITION PRECEDES THE DESCRIPTOR.  [ksys_pwrite64]
    tests [pos < 0] at fs/read_write.c:785-786, above the
    [CLASS(fd, f)(fd)] declaration at :788 that fetches the descriptor,
    so the answer is -EINVAL WHATEVER the fd table holds — this lemma
    takes no premise about it at all, which is the whole content of the
    ordering claim. *)
Lemma pwrite64_negative_pos_precedes_the_descriptor :
  forall fd buf count pos i m eff m' evs,
  (bv_signed pos < 0)%Z ->
  pwrite64_spec fd buf count pos i m (Ok eff m' evs) ->
  eff = mkEffect (errno_ret EINVAL) [] [] /\ m' = m /\ evs = [].
Proof.
  intros fd buf count pos i m eff m' evs Hpos H.
  apply check_pwrite64_complete_ok in H. unfold check_pwrite64 in H.
  unfold ppos_einvalb in H.
  rewrite (proj2 (Z.ltb_lt _ _) Hpos) in H. cbv beta iota zeta in H.
  apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
  now repeat split.
Qed.

(** The same ordering as a verdict.  fd 5 is not open in
    [readv_write_only_model], so a descriptor-first reading would answer
    -EBADF; the model answers -EINVAL and REFUSES the -EBADF.  The
    second conjunct is what makes the first one a check: without it the
    example would pass on a model that admitted both. *)
Example pwrite64_negative_pos_rejects_ebadf :
  check_syscall
    (mkInput 68 [5; 4096; 2; Z_to_bv 64 (-1); 0; 0] mem_ab (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) readv_write_only_model
  = CheckOk readv_write_only_model []
  /\ check_syscall
       (mkInput 68 [5; 4096; 2; Z_to_bv 64 (-1); 0; 0] mem_ab (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) readv_write_only_model
     = CheckReject.
Proof. split; check_eq. Qed.

(** A pwrite64 lands at the position the CALL names, not at the
    descriptor's offset — which is 0 on fd 3 here, so the two are
    distinguishable — and the descriptor's offset does not move.  Its
    reject twin is the same delivery claimed with the return a write at
    offset 0 would have made. *)
Example pwrite64_writes_at_the_named_position :
  match check_syscall
          (mkInput 68 [3; 4096; 2; 4; 0; 0] mem_ab (fun _ => None))
          (with_copyins [(4096, 2%nat)] (mkEffect 2 [] []))
          readv_write_only_model with
  | CheckOk m [] =>
      file_at (m_fs m) (wk [102]) = Some [0; 0; 0; 0; 97; 98]
      /\ fd_lookup (m_fds m) 3 = Some (FdFileW 1 0)
  | _ => False
  end
  /\ check_syscall
       (mkInput 68 [3; 4096; 2; 4; 0; 0] mem_ab (fun _ => None))
       (with_copyins [(4096, 2%nat)] (mkEffect 1 [] []))
       readv_write_only_model
     = CheckReject.
Proof. split; [vm_compute; split|]; check_eq. Qed.

(** ** Three more arms that judge a count over [Uaccess.rw_bytes_max]

    Like [write] and [writev], [pwrite64]'s write-only arm and [read]'s
    socket and pipe arms judge a count over [Uaccess.rw_bytes_max]
    rather than decline it.  These pin that.

    The socket half is in Checks/Cases/Net/Socket.v, beside the model
    that has a connection to read from. *)

(** A [pwrite64] one byte over [Uaccess.rw_bytes_max] is JUDGED — a
    two-byte write, since [mem_ab] maps two bytes and a regular-file
    write takes the readable prefix — and not declined.  The
    second conjunct is the arm's determinism at that count: a SHORT
    write of one byte is refused, so the first conjunct is a claim about
    the only admissible answer rather than about one of several. *)
Example pwrite64_over_rw_bytes_max_is_judged :
  match check_syscall
          (mkInput 68 [3; 4096; Z_to_bv 64 (rw_bytes_max + 1); 0; 0; 0]
             mem_ab (fun _ => None))
          (with_copyins [(4096, 2%nat)] (mkEffect 2 [] []))
          readv_write_only_model with
  | CheckOk m [] => file_at (m_fs m) (wk [102]) = Some [97; 98]
  | _ => False
  end
  /\ check_syscall
       (mkInput 68 [3; 4096; Z_to_bv 64 (rw_bytes_max + 1); 0; 0; 0]
          mem_ab (fun _ => None))
       (with_copyins [(4096, 1%nat)] (mkEffect 1 [] []))
       readv_write_only_model
     = CheckReject.
Proof. split; [vm_compute; reflexivity|check_eq]. Qed.

(** Every count [ReadWrite.random_write_countb] admits is at most the
    count asked. *)
Lemma random_write_countb_le : forall n l r,
  random_write_countb n l r = true -> (r <= n)%Z.
Proof.
  intros n l r H. unfold random_write_countb, random_page_stopb in H. cbv zeta in H.
  repeat rewrite ?orb_true_iff, ?andb_true_iff in H.
  rewrite ?Z.eqb_eq, ?Z.ltb_lt, ?Z.leb_le in H.
  lia.
Qed.

(** THE CLAMP, WHICH NO CONCRETE CASE CAN REACH.  A count over
    [State.MAX_RW_COUNT] needs a buffer of 2 GiB for the clamp to be
    observable at all, which is past what a checker can hold, so the
    pin is over a SYMBOLIC buffer
    instead: whatever [pwrite64] copies in, it is at most the clamp.
    [Checks.Cases.Fs.ReadWrite.read_delivery_clamped] is the read-side
    twin, and this is what makes the bound a CLAMP rather than an
    absence of any bound.

    Stated on the copy-in ledger because that is the quantity a count
    gate would bound: the number of user bytes the call read. *)
Lemma pwrite64_copyin_clamped : forall fd buf count pos i m eff m' evs a n,
  pwrite64_spec fd buf count pos i m (Ok eff m' evs) ->
  eff_copyins eff = [(a, n)] ->
  (Z.of_nat n <= MAX_RW_COUNT)%Z.
Proof.
  intros fd buf count pos i m eff m' evs a n H Hc.
  apply check_pwrite64_complete_ok in H. unfold check_pwrite64 in H.
  (* every arm but the transfer answers with an EMPTY copy-in ledger,
     which [Hc]'s singleton refutes *)
  assert (Hro : forall v mk evs' (Hx : check_ret_only eff v mk evs'
                                       = CheckOk m' evs), False).
  { intros v mk evs' Hx. apply check_ret_only_ok_iff in Hx.
    destruct Hx as (-> & _ & _). cbn in Hc. discriminate. }
  destruct (ppos_einvalb pos); [now destruct (Hro _ _ _ H)|].
  destruct (fd_lookup (m_fds m) fd)
    as [[ch|p off|p off|p off|p off|dk|sk|id w|rd wr|urd uwr|sid side st|ctx|fam]|];
    cbv iota in H; try (now destruct (Hro _ _ _ H)).
  (* three file kinds survive that: the APPEND arm, which writes at
     end-of-file, and the two kinds that write at [pos] -- the O_WRONLY
     and O_RDWR descriptions, which share one arm.  One script for those
     two, run under [all:] rather than written twice. *)
  2: { (* the append kind: its ledger is the same [write_source] prefix *)
       destruct (negb (access_okb buf (bv_unsigned count))); cbv iota in H;
         [now destruct (Hro _ _ _ H)|].
       destruct (rw_pos_einvalb pos (bv_unsigned count)); cbv iota in H;
         [now destruct (Hro _ _ _ H)|].
       cbv zeta in H.
       (* the file-size limit answers -EFBIG with an empty ledger, and
          otherwise the ledger is the prefix of the cut count *)
       destruct (append_efbigb (fs_ino_data (m_fs m) p) count); cbv iota in H;
         [now destruct (Hro _ _ _ H)|].
       set (cnt := append_count (fs_ino_data (m_fs m) p) count) in H. clearbody cnt.
       destruct (negb (w_is0 cnt)
                 && Nat.eqb (length (write_source (in_mem i) buf cnt)) 0);
         cbv iota in H; [now destruct (Hro _ _ _ H)|].
       destruct (w_is0 cnt); cbv iota in H; [now destruct (Hro _ _ _ H)|].
       apply check_ret_only_copyins_ok_iff in H.
       destruct H as (-> & _ & _).
       cbn in Hc. injection Hc as Ha Hn. subst n.
       eapply Z.le_trans; [apply write_source_length_le|].
       apply (proj2 (rw_count_clamp_range cnt)). }
  (* /dev/urandom is read-only, so its pwrite is the bare -EBADF the
     [try] above already dismissed; and /dev/null, whose every answer is
     a bare return: the ledger is empty on every one of its arms *)
  3: { destruct wr; cbn [negb] in H; cbv iota in H;
       [ | now destruct (Hro _ _ _ H) ].
       destruct (negb (access_okb buf (bv_unsigned count))); cbv iota in H;
         [now destruct (Hro _ _ _ H)|].
       destruct (rw_pos_einvalb pos (bv_unsigned count)); cbv iota in H;
         now destruct (Hro _ _ _ H). }
  (* /dev/urandom: -EBADF on a read-only descriptor, the refusals ahead
     of the transfer, and on a writable one [check_random_write], whose
     ledger is the buffer's first [r] bytes for a return of [r], at most
     the clamped count *)
  3: { repeat (match type of H with
               | (if ?b then _ else _) = _ => destruct b; cbv iota in H
               end);
       try (now destruct (Hro _ _ _ H)).
       rewrite check_random_write_eq in H. cbv beta in H.
       destruct (Z.eqb (rw_count_clamp count) 0); cbv iota in H;
         [now destruct (Hro _ _ _ H)|].
       destruct eff as [ret ws zs us cs cis];
         destruct ws, zs, us, cs; cbv iota in H; try discriminate H.
       cbn [eff_copyins] in Hc. subst cis.
       match type of H with (if ?b then _ else _) = _ => destruct b eqn:H1 end.
       - apply andb_true_iff in H1 as [H1 HL]. apply andb_true_iff in H1 as [_ HK].
         apply access_ranges_eqb_eq in HL. injection HL as _ Hn. subst n.
         pose proof (bv_unsigned_in_range _ ret) as Hr.
         rewrite Z2Nat.id by lia.
         eapply Z.le_trans; [exact (random_write_countb_le _ _ _ HK)|].
         apply (proj2 (rw_count_clamp_range count)).
       - cbv iota in H. rewrite andb_false_r in H. discriminate H. }
  all: destruct (negb (access_okb buf (bv_unsigned count)));
       [now destruct (Hro _ _ _ H)|].
  all: destruct (rw_pos_einvalb pos (bv_unsigned count));
       [now destruct (Hro _ _ _ H)|].
  all: cbv zeta in H.
  all: destruct (negb (w_is0 count)
                 && Nat.eqb (length (write_source (in_mem i) buf count)) 0);
       [ (* the faulting source answers with an empty ledger too, over
            the file it extends *)
         unfold check_write_fault_extend in H; cbv zeta in H;
         destruct (negb (modeled_zero_fill (bv_unsigned pos) (fs_ino_data (m_fs m) p)));
           [discriminate|];
         apply check_ret_only_copyins_ok_iff in H;
         destruct H as (-> & _ & _); cbn in Hc; discriminate |].
  all: destruct (negb (modeled_file_gap (fs_ino_data (m_fs m) p) pos
                         (write_source (in_mem i) buf count)));
       [discriminate|].
  all: destruct (w_is0 count); [now destruct (Hro _ _ _ H)|].
  all: apply check_ret_only_copyins_ok_iff in H;
       destruct H as (-> & _ & _).
  all: cbn in Hc; injection Hc as Ha Hn; subst n.
  all: eapply Z.le_trans; [apply write_source_length_le|].
  all: apply (proj2 (rw_count_clamp_range count)).
Qed.

(** A pipe holding two bytes, on the descriptors [Pipe.pipe2_spec]
    hands out: 3 the read end, 4 the write end, and the queue's mark at
    the two bytes a writer put there. *)
Definition pipe_queued_model : Model :=
  with_pipes [(0, ([97; 98], 2%Z))]
    (mkModel [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
              (3, FdPipe 0 false); (4, FdPipe 0 true)]
       (mkVmMaps [] [] 0 0 demo_limit) IEof Fs.fs_empty None None None).

(** A pipe [read] one byte over [Uaccess.rw_bytes_max] is JUDGED, and
    delivers the whole queue: [State.pipe_take] takes the minimum
    against the queue, so the count never reaches a unary numeral and
    needs no ceiling.

    The second conjunct is the arm's determinism — a pipe read delivers
    [min count (length q)] and never less (fs/pipe.c [anon_pipe_read],
    v6.18.46: [if (ret) break] precedes the only wait), so a one-byte
    answer at this count is refused.  The first conjunct also reads the
    QUEUE back, and finds it empty rather than untouched: that is what
    says that passing the delivered length to [State.pipe_consume]
    consumes the same bytes the count would have
    ([State.pipe_consume_of_take]). *)
Example pipe_read_over_rw_bytes_max_is_judged :
  match check_syscall
          (mkInput 63 [3; 4096; Z_to_bv 64 (rw_bytes_max + 1); 0; 0; 0]
             (fun _ => None) (wmem_first 2))
          (mkEffect 2 [(4096, [97; 98])] []) pipe_queued_model with
  | CheckOk m [] => m_pipes m = [(0, (@nil byte, 2%Z))]
  | _ => False
  end
  /\ check_syscall
       (mkInput 63 [3; 4096; Z_to_bv 64 (rw_bytes_max + 1); 0; 0; 0]
          (fun _ => None) (wmem_first 2))
       (mkEffect 1 [(4096, [97])] []) pipe_queued_model
     = CheckReject.
Proof. split; [vm_compute; reflexivity|check_eq]. Qed.

(* =========================================================================
   PART 6 — what a write LEAVES BEHIND when its source faults
   ========================================================================= *)

(** [Cases.Prelude.wpast_model] is the fixture these three need: a file
    "hi" on fd 3, O_WRONLY, with [f_pos] two bytes PAST its end.  Only
    an [lseek] can put it there, and it is the one shape in which
    [shmem_write_end]'s size test is not a no-op.

    The same file through an iovec array, with ONLY the array readable:
    [import_iovec] succeeds, and the gathered prefix is then empty. *)


Definition mem_iovecs_only : word -> option byte :=
  fun a => if bv_leu 8192 a && bv_ltu a 8224 then mem_writev_ab a else None.

(** A FAULTING SOURCE IS NOT A NO-OP ON THE FILE.  Linux runs
    [a_ops->write_begin] BEFORE the copy and [a_ops->write_end] with
    [copied = 0] after it ([generic_perform_write], mm/filemap.c,
    v6.18.46), and [shmem_write_end] (mm/shmem.c) opens
    [if (pos + copied > inode->i_size) i_size_write(inode, pos + copied);]
    — so the file comes out extended to the write's own offset, with the
    hole reading back as zeros, and only THEN does the loop answer
    -EFAULT ([fault_in_iov_iter_readable] cannot fault the range in,
    [if (!written) return status;]).  [f_pos] does not move:
    [new_sync_write] (fs/read_write.c) writes a position back only under
    [if (ret > 0 && ppos)].

    The first conjunct is that post-state, read out of the model the
    checker returns.  The second is THE ANSWER THIS CALL USED TO GIVE —
    the same -EFAULT over an untouched model — now refused.  The third
    is the same statement for [writev], which reaches the same
    [vfs_write] body: the iovec array is readable, so the import
    succeeds and the empty gathered prefix is what faults.  The fourth
    is the APPEND arm, where the kernel's own arithmetic makes the
    extension a no-op ([ki_pos] IS [i_size], so [pos + 0 > i_size] is
    false) and the file is untouched. *)
Example write_with_a_faulting_source_extends_the_file :
  match check_syscall (mkInput 64 [3; 4096; 2; 0; 0; 0]
                         (fun _ => None) (fun _ => None))
          (mkEffect (errno_ret EFAULT) [] []) wpast_model with
  | CheckOk m [] =>
      file_at (m_fs m) (wk [102]) = Some [104; 105; 0; 0]
      /\ fd_lookup (m_fds m) 3 = Some (FdFileW 1 4)
  | _ => False
  end
  /\ check_syscall (mkInput 64 [3; 4096; 2; 0; 0; 0]
                      (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) wpast_model
     <> CheckOk wpast_model []
  /\ match check_syscall (mkInput 66 [3; 8192; 2; 0; 0; 0]
                            mem_iovecs_only (fun _ => None))
             (with_copyins (import_iovecs_accesses mem_iovecs_only 8192 2)
                (mkEffect (errno_ret EFAULT) [] [])) wpast_model with
     | CheckOk m [] => file_at (m_fs m) (wk [102]) = Some [104; 105; 0; 0]
     | _ => False
     end
  /\ check_syscall (mkInput 64 [3; 4096; 2; 0; 0; 0]
                      (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) apast_model
     = CheckOk apast_model [].
Proof.
  split; [vm_compute; split; check_eq|].
  split; [vm_compute; discriminate|].
  split; [vm_compute; check_eq|check_eq].
Qed.

(** "hi" on fd 3, O_RDWR, with [f_pos] just past its two bytes: what
    openat(O_RDWR|O_CREAT|O_TRUNC) and write(3, "hi", 2) leave. *)
Definition hi_rdwr_model : Model :=
  mkModel [(3, FdFileRW 1 2)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    (demo_fs [([102], SFile [104; 105])]) None None None.

(** That file run out to offset 100, the 98 bytes past "hi" zero. *)
Definition hi_hole_100 : list byte := [104; 105] ++ repeat (Z_to_bv 8 0) 98.

(** A FAULTING WRITE A HUNDRED BYTES OUT, AND WHAT THE NEXT CALLS SEE.
    lseek(3, 100, SEEK_SET), then write(3, p, 1) with no page at [p]:
    -EFAULT, over a file now a hundred bytes long.
    [generic_perform_write] (mm/filemap.c:4272-4294, Linux v6.18.46)
    calls [write_begin], copies nothing, and calls [write_end] with
    [copied] 0; tmpfs's [shmem_write_end] sets [i_size] to
    [pos + copied] (mm/shmem.c:3352-3353); and only then does the loop
    find the source unfaultable and return -EFAULT
    (mm/filemap.c:4321-4323, :4331-4332).  The first write zeroed its
    folio past the two bytes it copied (mm/shmem.c:3355-3362), so the
    hole reads as zeros.  Linux v6.16 and v6.17 run the same loop and
    the same size test.

    The conjuncts after the write are what a program can read of the
    file.  [fstat] reports [st_size] 100, and 2, the size of the file
    the write would have left untouched, is refused.  pread64(3, buf,
    98, 2) delivers 98 zeros, and the end-of-file a two-byte file gives
    there is refused.  lseek(3, 0, SEEK_END) is 100, and 2 is refused.
    [f_pos] stays at 100 through the write and the read.  The last
    conjunct is pwrite64(3, p, 1, 100) on the same two-byte file: the
    same -EFAULT and the same hundred bytes, with the offset left at 2.
    testing/syscall-check/tests/write_past_eof_fault.c makes these
    calls. *)
Example write_past_eof_from_an_unmapped_page_leaves_a_100_byte_file :
  let wr := mkInput 64 [3; 4096; 1; 0; 0; 0] (fun _ => None) (fun _ => None) in
  let pread := mkInput 67 [3; 4096; 98; 2; 0; 0] (fun _ => None) (wmem_first 98) in
  let seek_end := mkInput 62 [3; 0; 2; 0; 0; 0] (fun _ => None) (fun _ => None) in
  match check_syscall (mkInput 62 [3; 100; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
          (mkEffect 100 [] []) hi_rdwr_model with
  | CheckOk m1 [] =>
      match check_syscall wr (mkEffect (errno_ret EFAULT) [] []) m1 with
      | CheckOk m2 [] =>
          file_at (m_fs m2) (wk [102]) = Some hi_hole_100
          /\ fd_lookup (m_fds m2) 3 = Some (FdFileRW 1 100)
          /\ match check_syscall Cases.Fs.Stat.fstat_input
                     (mkEffect 0 [(4096, Cases.Fs.Stat.stat_of 4711 S_IFREG 100 8 1700000000)] [])
                     m2 with
             | CheckOk _ [] => True
             | _ => False
             end
          /\ check_syscall Cases.Fs.Stat.fstat_input
               (mkEffect 0 [(4096, Cases.Fs.Stat.stat_of 4711 S_IFREG 2 8 1700000000)] [])
               m2 = CheckReject
          /\ match check_syscall pread (mkEffect 98 [(4096, repeat (Z_to_bv 8 0) 98)] []) m2 with
             | CheckOk m3 [] => fd_lookup (m_fds m3) 3 = Some (FdFileRW 1 100)
             | _ => False
             end
          /\ check_syscall pread (mkEffect 0 [] []) m2 = CheckReject
          /\ match check_syscall seek_end (mkEffect 100 [] []) m2 with
             | CheckOk m3 [] => fd_lookup (m_fds m3) 3 = Some (FdFileRW 1 100)
             | _ => False
             end
          /\ check_syscall seek_end (mkEffect 2 [] []) m2 = CheckReject
      | _ => False
      end
  | _ => False
  end
  /\ match check_syscall (mkInput 68 [3; 4096; 1; 100; 0; 0] (fun _ => None) (fun _ => None))
             (mkEffect (errno_ret EFAULT) [] []) hi_rdwr_model with
     | CheckOk m [] =>
         file_at (m_fs m) (wk [102]) = Some hi_hole_100
         /\ fd_lookup (m_fds m) 3 = Some (FdFileRW 1 2)
     | _ => False
     end.
Proof. vm_compute. split_conj; first [exact I | check_eq]. Qed.

(** A pipe whose queue is EMPTY, on the descriptors [Pipe.pipe2_spec]
    hands out: 3 the read end, 4 the write end. *)
Definition pipe_empty_model : Model :=
  with_pipes [(0, (@nil byte, 0%Z))]
    (mkModel [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
              (3, FdPipe 0 false); (4, FdPipe 0 true)]
       (mkVmMaps [] [] 0 0 demo_limit) IEof Fs.fs_empty None None None).

(** A WRITE INTO AN EMPTY PIPE CAN ANSWER -ENOMEM, and that answer was
    not in the model before.  [anon_pipe_write] (fs/pipe.c, v6.18.46)
    guards its merge path with [if (chars && !was_empty)] (:478), so an
    empty queue falls through to the ring loop, whose first act is
    [page = anon_pipe_get_page(pipe); if (unlikely(!page)) { if (!ret)
    ret = -ENOMEM; break; }] (:515-519) — a [break] with [ret] still 0,
    so no byte was copied and the pipe is untouched.  Whether
    [alloc_page(GFP_HIGHUSER | __GFP_ACCOUNT)] fails is the
    ENVIRONMENT's, not the model's state: [ReadWrite.write_errnos] is
    the injected answer and [Run.injected_table] registers it, exactly
    as [Open.openat_errnos] and [Pipe.pipe2_errnos] do for their own
    allocations.

    The first conjunct is the new answer, with the pipe left as it was;
    before this arm it was [CheckReject].  The second is that the
    DELIVERY is still admitted beside it, so nothing was traded away.
    The third is the bound: on a NONEMPTY queue the write merges into
    the page that is already there and allocates nothing
    ([State.pipe_needs_page]), so -ENOMEM is refused there. *)
Example pipe_write_into_an_empty_pipe_may_be_enomem :
  check_syscall (mkInput 64 [4; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
    (mkEffect (errno_ret ENOMEM) [] []) pipe_empty_model
  = CheckOk pipe_empty_model []
  /\ check_syscall (mkInput 64 [4; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
       (with_copyins [(4096, 2%nat)] (mkEffect 2 [] [])) pipe_empty_model
     = CheckOk (with_pipes [(0, ([97; 98], 2%Z))] pipe_empty_model) []
  /\ check_syscall (mkInput 64 [4; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
       (mkEffect (errno_ret ENOMEM) [] []) pipe_queued_model
     = CheckReject.
Proof. split; [check_eq | split; [check_eq | vm_compute; reflexivity]]. Qed.

(* =========================================================================
   PART 7 — death by SIGPIPE: what each arm answers, and what it still
   admits beside it
   ========================================================================= *)

(** The launch of [demo_input] with THE READER GONE: the far end of
    descriptors 1 and 2 is a pipe or a socket nothing reads any more,
    which is `prog | head -1` once [head] has had its line.  Everything
    else is [demo_input]'s, except that this launch DECLARES the
    SIGPIPE death (the last field, [State.in_sigpipe_terminal]), as
    [Run.valid_input_channel_closed] -- the predicate that names it --
    pins it.  [Run.valid_input] pins the reader present and the death
    declined, and so does not admit this launch. *)
Definition noreader_input : ProcInput :=
  mkProcInput_full [] [] Fs.fs_empty Fs.default_cwd IEof demo_uid demo_gid demo_groups
                   net_silent default_nofile (Z_to_bv 64 0) demo_hwcap false
                   Sv48 default_urandom default_kernel default_execfn
                   false true true.

(** The same launch again, with SIGPIPE at SIG_IGN: the launcher ran
    `signal(SIGPIPE, SIG_IGN)` before execve and execve kept it
    ([State.in_sigpipe_default]).  [Run.valid_input_channel_closed]
    ADMITS THIS ONE TOO: that predicate pins the reader gone and the
    death declared and says NOTHING about the disposition, so these
    two inputs are the two starts it covers and the pair below is what
    separates them.  The death declaration has to be on here as it is
    above -- with it off the write declines at either disposition
    ([Sys.Fs.ReadWrite.sigpipe_declines]), which is what keeps
    [Run.valid_input] able to leave the disposition free. *)
Definition noreader_ignored_input : ProcInput :=
  mkProcInput_full [] [] Fs.fs_empty Fs.default_cwd IEof demo_uid demo_gid demo_groups
                   net_silent default_nofile (Z_to_bv 64 0) demo_hwcap false
                   Sv48 default_urandom default_kernel default_execfn
                   false false true.

Definition noreader_model : Model :=
  init_model [] 0 0 demo_sp demo_limit noreader_input.
Definition noreader_ignored_model : Model :=
  init_model [] 0 0 demo_sp demo_limit noreader_ignored_input.
Definition reader_model : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input Fs.fs_empty IEof).

(** PAIR 1 — A WRITE TO STANDARD OUTPUT WHOSE READER HAS GONE KILLS THE
    PROCESS, AND THE SAME WRITE WITH A READER STILL DELIVERS.

    Linux raises SIGPIPE and sets -EPIPE, in that order and without a
    flag write(2) can suppress: fs/pipe.c [anon_pipe_write] :460-465
    when the far end is a pipe, net/core/stream.c [sk_stream_error]
    :190-198 when it is a socket (Linux v6.18.46, commit 1f99e9ab748f).
    Signal 13's default action is terminate, so the -EPIPE is never
    returned and what the world sees is a death by signal 13.

    The first conjunct is that answer: the post-state is
    [State.with_killed 13], which [Run.sstep_killed] takes and
    [Run.sstep_exit] declines, and the ledger is empty because no byte
    of the source is read on this path.  THE SECOND CONJUNCT IS WHY
    THIS IS NOT A CHECKER THAT HAS BECOME CONSTANTLY KILLING: the same
    call on the launch whose reader is there still delivers both bytes,
    with the two [State.WriteEv]s and the copy-in ledger it always
    had.  The third says the two answers do not cross: the delivering
    answer is REFUSED on the reader-less launch. *)
Example write_channel_no_reader_dies_by_sigpipe :
  check_syscall (mkInput 64 [1; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
    (mkEffect (errno_ret EPIPE) [] []) noreader_model
  = CheckOk (with_killed (Z_to_bv 64 13) noreader_model) []
  /\ check_syscall (mkInput 64 [1; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
       (with_copyins [(4096, 2%nat)] (mkEffect 2 [] [])) reader_model
     = CheckOk reader_model [WriteEv 1 97; WriteEv 1 98]
  /\ check_syscall (mkInput 64 [1; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
       (with_copyins [(4096, 2%nat)] (mkEffect 2 [] [])) noreader_model
     = CheckReject.
Proof. split; [check_eq | split; check_eq]. Qed.

(** PAIR 2 — THE SAME WRITE UNDER THE OTHER LAUNCH DECLARATION.

    [State.in_sigpipe_default] is the task's declaration that signal 13
    is still at SIG_DFL, and the predicate in play here does not pin it:
    both starts are ones Linux produces, so
    [Run.valid_input_channel_closed] -- like [Run.valid_input], and
    unlike [Run.valid_input_sigpipe_ignored], which pins the SIG_IGN
    start -- admits this input and the one above alike and the DISPOSITION
    ALONE separates them.  At SIG_IGN the
    kernel never delivers the signal at all --
    kernel/signal.c [prepare_signal]/[sig_ignored] drops it unblocked,
    [get_signal]'s [if (ka->sa.sa_handler == SIG_IGN) continue] drops it
    after an unblock -- so the call's whole answer is the -EPIPE and
    THE PROCESS IS STILL RUNNING.

    The first conjunct is that: the same -EPIPE over an UNCHANGED
    model, no kill.  The second is the discrimination, and it is what
    makes the field worth having: the killing answer of pair 1 is
    REFUSED on this launch, and the surviving answer here is refused on
    that one.  Without the field one of the two launches would get the
    other's answer. *)
Example write_channel_no_reader_survives_when_sigpipe_is_ignored :
  check_syscall (mkInput 64 [1; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
    (mkEffect (errno_ret EPIPE) [] []) noreader_ignored_model
  = CheckOk noreader_ignored_model []
  /\ check_syscall (mkInput 64 [1; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
       (mkEffect (errno_ret EPIPE) [] []) noreader_ignored_model
     <> CheckOk (with_killed (Z_to_bv 64 13) noreader_ignored_model) []
  /\ check_syscall (mkInput 64 [1; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
       (mkEffect (errno_ret EPIPE) [] []) noreader_model
     <> CheckOk noreader_model [].
Proof.
  split; [check_eq|].
  split; vm_compute; discriminate.
Qed.

(** A pipe whose READ END HAS BEEN CLOSED: fd 4 is the write end and no
    descriptor of pipe 0 is open for reading, which is what
    [State.pipe_end_live _ 0 false] asks.  Built on [State.mkModel],
    which seeds SIGPIPE at SIG_DFL and the death NOT declared -- the
    ordinary launch. *)
Definition pipe_reader_gone_model : Model :=
  with_pipes [(0, (@nil byte, 0%Z))]
    (mkModel [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
              (4, FdPipe 0 true)]
       (mkVmMaps [] [] 0 0 demo_limit) IEof Fs.fs_empty None None None).

(** The same pipe on a launch that declares the SIGPIPE death, the
    world [Run.valid_input_sigpipe_kills] names. *)
Definition pipe_reader_gone_kills_model : Model :=
  with_sigpipe_terminal true pipe_reader_gone_model.

(** PAIR 3 — A WRITE TO A PIPE WITH NO READER IS ANSWERED ON A LAUNCH
    THAT DECLARES THE DEATH, AND THE PIPE'S OTHER ANSWERS ARE UNCHANGED.

    This arm used to answer [unmodeled], on the argument that the model
    had no signals and no death that is not [exit].  It has both now,
    so on a launch that declares the death the call is judged: signal
    13 and -EPIPE, fs/pipe.c [anon_pipe_write] :460-465, repeated at
    the top of each loop iteration at :501-506.  On the ordinary launch
    it still declines; [Checks.Cases.Fs.SigpipeLaunch] is that pair, on
    launches proved valid and a pipe the program made with [pipe2].

    The first conjunct is the answer.  The second is the ordering
    that makes it sound, and it is not a stylistic one: the no-reader
    test is STRICTLY ABOVE the page allocation at :515 and its
    [ret = -ENOMEM] at :517-519, so a reader-less pipe can never answer
    -ENOMEM, and the model refuses that answer here while
    [pipe_write_into_an_empty_pipe_may_be_enomem] above admits it on the
    same empty pipe WITH a reader.  The third is the zero-count
    exception, which is also ordering: :454-456 returns 0 before the
    [mutex_lock] at :458 and so before the readers test, so a
    zero-length write to a reader-less pipe is 0 and raises nothing.
    The fourth is the neighbouring case still admitted: with the read
    end open the write delivers. *)
Example write_pipe_no_reader_is_answered :
  check_syscall (mkInput 64 [4; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
    (mkEffect (errno_ret EPIPE) [] []) pipe_reader_gone_kills_model
  = CheckOk (with_killed (Z_to_bv 64 13) pipe_reader_gone_kills_model) []
  /\ check_syscall (mkInput 64 [4; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
       (mkEffect (errno_ret ENOMEM) [] []) pipe_reader_gone_kills_model
     = CheckReject
  /\ check_syscall (mkInput 64 [4; 4096; 0; 0; 0; 0] mem_ab (fun _ => None))
       (mkEffect 0 [] []) pipe_reader_gone_kills_model
     = CheckOk pipe_reader_gone_kills_model []
  /\ check_syscall (mkInput 64 [4; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
       (with_copyins [(4096, 2%nat)] (mkEffect 2 [] [])) pipe_empty_model
     = CheckOk (with_pipes [(0, ([97; 98], 2%Z))] pipe_empty_model) [].
Proof.
  split; [check_eq|].
  split; [vm_compute; reflexivity|].
  split; check_eq.
Qed.

(** THE SAME READER-LESS PIPE, AT A RANGE [access_ok] REFUSES: -EFAULT
    AND NO DEATH.  [vfs_write] tests [access_ok] on the named range before
    it calls [f_op->write_iter], so a refused range is -EFAULT and never
    reaches [anon_pipe_write]'s readers test or its signal
    (fs/read_write.c, [vfs_write]; fs/pipe.c, [anon_pipe_write]).  Before
    the merge put that test above the no-reader branch, this call was the
    death of [write_pipe_no_reader_is_answered].

    Two bytes from one below the top of the address space: the byte at
    2^64 - 1 and the byte at 0.  Each memory maps exactly its own range. *)
Definition pipe_noreader_wrap_buf : word := Z_to_bv 64 (2 ^ 64 - 1).

Definition pipe_noreader_wrap_mem : word -> option byte :=
  fun a => if ((bv_unsigned a <? 1)%Z || (2 ^ 64 - 1 <=? bv_unsigned a)%Z)%bool
           then Some (Z_to_bv 8 97) else None.

(** The last two bytes [State.access_okb] accepts. *)
Definition pipe_noreader_top_buf : word := Z_to_bv 64 (TASK_SIZE - 2).

Definition pipe_noreader_top_mem : word -> option byte :=
  fun a => if ((TASK_SIZE - 2 <=? bv_unsigned a)%Z
               && (bv_unsigned a <? TASK_SIZE)%Z)%bool
           then Some (Z_to_bv 8 97) else None.

(** THE CONTROL: the bare walk at the wrapping buffer passes. *)
Example write_pipe_no_reader_wrap_would_pass_the_bare_walk :
  read_bytes_map pipe_noreader_wrap_mem pipe_noreader_wrap_buf (Z_to_bv 64 2)
    <> None.
Proof. vm_compute. discriminate. Qed.

(** -EFAULT over the model as it was, and the death refused. *)
Example write_pipe_no_reader_wrapping_buffer_is_efault :
  check_syscall (mkInput 64 [4; pipe_noreader_wrap_buf; 2; 0; 0; 0]
                   pipe_noreader_wrap_mem (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) pipe_reader_gone_kills_model
  = CheckOk pipe_reader_gone_kills_model []
  /\ check_syscall (mkInput 64 [4; pipe_noreader_wrap_buf; 2; 0; 0; 0]
                      pipe_noreader_wrap_mem (fun _ => None))
       (mkEffect (errno_ret EPIPE) [] []) pipe_reader_gone_kills_model
     = CheckReject.
Proof. split; check_eq. Qed.

(** THE NEIGHBOUR: at the top of what [State.access_okb] accepts the call
    is answered exactly as [write_pipe_no_reader_is_answered] answers it,
    a death by signal 13, and -EFAULT is refused there. *)
Example write_pipe_no_reader_at_the_top_still_dies :
  check_syscall (mkInput 64 [4; pipe_noreader_top_buf; 2; 0; 0; 0]
                   pipe_noreader_top_mem (fun _ => None))
    (mkEffect (errno_ret EPIPE) [] []) pipe_reader_gone_kills_model
  = CheckOk (with_killed (Z_to_bv 64 13) pipe_reader_gone_kills_model) []
  /\ check_syscall (mkInput 64 [4; pipe_noreader_top_buf; 2; 0; 0; 0]
                      pipe_noreader_top_mem (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) pipe_reader_gone_kills_model
     = CheckReject.
Proof. split; check_eq. Qed.

(* =========================================================================
   PART 8 — THE TRANSFER ARMS THAT WALKED OFF THE TOP OF THE ADDRESS SPACE

   [read]'s socket and pipe arms and [write]'s channel, pipe and plain
   file arms used to let the walk over the buffer speak for the range:
   a small count passed [Uaccess.modeled_rw_range] by its left disjunct
   and the arm then walked [buf] with [State.read_bytes_map] or
   [Uaccess.write_source], which advance in WORD arithmetic and WRAP at
   2^64.  A buffer in the last bytes of the address space read the bytes
   below the wrap and then the bytes from 0 on, the walk said [Some],
   and the arm ANSWERED the call: a delivery where Linux answers -EFAULT.
   Each arm now asks [vfs_read]'s or [vfs_write]'s [access_ok] on the
   count the call named (fs/read_write.c, [vfs_read] and [vfs_write])
   before its walks; [Uaccess.modeled_rw_range]'s note says which arm
   asks it where, and [State.copy_bytes_map]'s note has the wrap.

   EACH GROUP IS THREE EXAMPLES, and all three are needed.  The wrapping
   call is refused.  A NEIGHBOURING ordinary call at the top of what
   [State.access_okb] accepts is still answered, so the test is not a
   blanket refusal of high addresses.  And the CONTROL: the bare walk
   really would have passed at the wrapping buffer, so the refusal
   cannot be passing because the memory quietly stopped short.

   THE MEMORIES MAP EXACTLY THEIR OWN RANGE and nothing else, for that
   reason: [wmem_open] answers [Some] at every address and could not
   tell a wrapping buffer from any other.
   ========================================================================= *)

(** Eight bytes below the top and eight from 0, sixteen in all, every
    one of them 'a'. *)
Definition top_wrap_buf : word := Z_to_bv 64 (2 ^ 64 - 8).

Definition top_wrap_mem : word -> option byte :=
  fun a => if ((bv_unsigned a <? 8)%Z || (2 ^ 64 - 8 <=? bv_unsigned a)%Z)%bool
           then Some (Z_to_bv 8 97) else None.

(** The last sixteen bytes [State.access_okb] accepts, mapped end to end
    and nothing else. *)
Definition task_top_buf : word := Z_to_bv 64 (TASK_SIZE - 16).

Definition task_top_mem : word -> option byte :=
  fun a => if ((TASK_SIZE - 16 <=? bv_unsigned a)%Z
               && (bv_unsigned a <? TASK_SIZE)%Z)%bool
           then Some (Z_to_bv 8 97) else None.

Definition sixteen_a : list byte := repeat (Z_to_bv 8 97) 16%nat.

(** The events of an answered call, and [None] for a refused or declined
    one: the neighbours below are measured as still answered by this,
    without spelling the post-model a delivery leaves. *)
Definition answered_events (r : check_result) : option (list event) :=
  match r with CheckOk _ evs => Some evs | _ => None end.

(** THE CONTROL, shared by every group below: the walk the arms used to
    make at the wrapping buffer passes, over all sixteen bytes. *)
Example top_wrap_would_pass_the_bare_walk :
  read_bytes_map top_wrap_mem top_wrap_buf (Z_to_bv 64 16) <> None.
Proof. vm_compute. discriminate. Qed.

(* ---- read (63) on a connected socket ----------------------------------- *)

Definition rw_sock_peer : PeerAddr := mkPeer (Z_to_bv 32 0) (Z_to_bv 16 0).

Fixpoint rw_net_of (l : list byte) : NetStream :=
  match l with
  | [] => NFin
  | b :: r => NCons b (rw_net_of r)
  end.

(** fd 3 is a connection on channel 3 with [rx] queued. *)
Definition rw_sock_model (rx : NetStream) : Model :=
  mkModel [(3, FdSocket (SkConnected rw_sock_peer 3 rx false))]
    (mkVmMaps [] [] 0 0 demo_limit) IEof Fs.fs_empty None None None.

(** Sixteen queued bytes and a sixteen-byte read at the wrapping buffer.
    Before the test the arm delivered them, into eight bytes below the
    top and eight from 0; [vfs_read]'s [access_ok] refuses the range
    before [sock_read_iter] (net/socket.c) is reached, so the answer is
    -EFAULT with nothing delivered and the queue untouched. *)
Example read_socket_wrapping_buffer_is_efault :
  check_syscall (mkInput 63 [3; top_wrap_buf; 16; 0; 0; 0]
                   (fun _ => None) top_wrap_mem)
    (mkEffect (errno_ret EFAULT) [] []) (rw_sock_model (rw_net_of sixteen_a))
  = CheckOk (rw_sock_model (rw_net_of sixteen_a)) []
  /\ check_syscall (mkInput 63 [3; top_wrap_buf; 16; 0; 0; 0]
                      (fun _ => None) top_wrap_mem)
       (mkEffect (Z_to_bv 64 16) [(top_wrap_buf, sixteen_a)] [])
       (rw_sock_model (rw_net_of sixteen_a))
     = CheckReject.
Proof. split; check_eq. Qed.

(** THE NEIGHBOUR: the same read at the top of what [State.access_okb]
    accepts delivers all sixteen bytes on the connection's channel, and
    -EFAULT is refused there. *)
Example read_socket_at_the_top_still_delivers :
  answered_events
    (check_syscall (mkInput 63 [3; task_top_buf; 16; 0; 0; 0]
                      (fun _ => None) task_top_mem)
       (mkEffect (Z_to_bv 64 16) [(task_top_buf, sixteen_a)] [])
       (rw_sock_model (rw_net_of sixteen_a)))
  = Some (map (ReadEv 3) sixteen_a)
  /\ check_syscall (mkInput 63 [3; task_top_buf; 16; 0; 0; 0]
                      (fun _ => None) task_top_mem)
       (mkEffect (errno_ret EFAULT) [] []) (rw_sock_model (rw_net_of sixteen_a))
     = CheckReject.
Proof. split; check_eq. Qed.

(** THE NAMED COUNT, NOT ONLY THE WRAP.  [read(sock, TASK_SIZE - 4, 8)]
    with two bytes queued: the delivered two bytes fit under
    [State.TASK_SIZE] and the walk over them passes (the control below),
    so before the test the arm delivered them.  [vfs_read] tests the
    NAMED range, which passes the top, and answers -EFAULT. *)
Definition residue_buf : word := Z_to_bv 64 (TASK_SIZE - 4).

Definition residue_mem : word -> option byte :=
  fun a => if ((TASK_SIZE - 4 <=? bv_unsigned a)%Z
               && (bv_unsigned a <? TASK_SIZE)%Z)%bool
           then Some (Z_to_bv 8 97) else None.

Example read_socket_residue_walk_passes :
  read_bytes_map residue_mem residue_buf (Z_to_bv 64 2) <> None.
Proof. vm_compute. discriminate. Qed.

Example read_socket_named_range_past_the_top_is_efault :
  check_syscall (mkInput 63 [3; residue_buf; 8; 0; 0; 0]
                   (fun _ => None) residue_mem)
    (mkEffect (errno_ret EFAULT) [] [])
    (rw_sock_model (rw_net_of [Z_to_bv 8 97; Z_to_bv 8 97]))
  = CheckOk (rw_sock_model (rw_net_of [Z_to_bv 8 97; Z_to_bv 8 97])) []
  /\ check_syscall (mkInput 63 [3; residue_buf; 8; 0; 0; 0]
                      (fun _ => None) residue_mem)
       (mkEffect (Z_to_bv 64 2) [(residue_buf, [Z_to_bv 8 97; Z_to_bv 8 97])] [])
       (rw_sock_model (rw_net_of [Z_to_bv 8 97; Z_to_bv 8 97]))
     = CheckReject.
Proof. split; check_eq. Qed.

(* ---- read (63) on a pipe's read end ------------------------------------ *)

(** fd 3 the read end, fd 4 the write end, sixteen bytes queued. *)
Definition rw_pipe16_model : Model :=
  with_pipes [(0, (sixteen_a, 16%Z))]
    (mkModel [(3, FdPipe 0 false); (4, FdPipe 0 true)]
       (mkVmMaps [] [] 0 0 demo_limit) IEof Fs.fs_empty None None None).

(** Before the test [anon_pipe_read] (fs/pipe.c) was reached and the
    queue delivered across the wrap; now -EFAULT with the queue
    untouched. *)
Example read_pipe_wrapping_buffer_is_efault :
  check_syscall (mkInput 63 [3; top_wrap_buf; 16; 0; 0; 0]
                   (fun _ => None) top_wrap_mem)
    (mkEffect (errno_ret EFAULT) [] []) rw_pipe16_model
  = CheckOk rw_pipe16_model []
  /\ check_syscall (mkInput 63 [3; top_wrap_buf; 16; 0; 0; 0]
                      (fun _ => None) top_wrap_mem)
       (mkEffect (Z_to_bv 64 16) [(top_wrap_buf, sixteen_a)] []) rw_pipe16_model
     = CheckReject.
Proof. split; check_eq. Qed.

Example read_pipe_at_the_top_still_delivers :
  answered_events
    (check_syscall (mkInput 63 [3; task_top_buf; 16; 0; 0; 0]
                      (fun _ => None) task_top_mem)
       (mkEffect (Z_to_bv 64 16) [(task_top_buf, sixteen_a)] []) rw_pipe16_model)
  = Some []
  /\ check_syscall (mkInput 63 [3; task_top_buf; 16; 0; 0; 0]
                      (fun _ => None) task_top_mem)
       (mkEffect (errno_ret EFAULT) [] []) rw_pipe16_model
     = CheckReject.
Proof. split; check_eq. Qed.

(* ---- write (64) on stdout ---------------------------------------------- *)

Definition rw_chan_model : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input Fs.fs_empty IEof).

(** Before the test the channel arm delivered the sixteen bytes it
    walked across the wrap; [vfs_write]'s [access_ok] refuses the range
    first, so -EFAULT with no copy-in and no event. *)
Example write_channel_wrapping_buffer_is_efault :
  check_syscall (mkInput 64 [1; top_wrap_buf; 16; 0; 0; 0]
                   top_wrap_mem (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) rw_chan_model
  = CheckOk rw_chan_model []
  /\ check_syscall (mkInput 64 [1; top_wrap_buf; 16; 0; 0; 0]
                      top_wrap_mem (fun _ => None))
       (with_copyins [(top_wrap_buf, 16%nat)] (mkEffect 16 [] [])) rw_chan_model
     = CheckReject.
Proof. split; check_eq. Qed.

Example write_channel_at_the_top_still_delivers :
  answered_events
    (check_syscall (mkInput 64 [1; task_top_buf; 16; 0; 0; 0]
                      task_top_mem (fun _ => None))
       (with_copyins [(task_top_buf, 16%nat)] (mkEffect 16 [] [])) rw_chan_model)
  = Some (map (WriteEv 1) sixteen_a)
  /\ check_syscall (mkInput 64 [1; task_top_buf; 16; 0; 0; 0]
                      task_top_mem (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) rw_chan_model
     = CheckReject.
Proof. split; check_eq. Qed.

(* ---- write (64) on a pipe's write end ---------------------------------- *)

(** [pipe_queued_model]'s write end, with a reader alive and room in the
    page.  Before the test the whole wrapped source passed the arm's
    wholly-readable test and was appended; [vfs_write]'s [access_ok] runs
    before [anon_pipe_write] (fs/pipe.c), so -EFAULT and the pipe left
    as it was. *)
Example write_pipe_wrapping_buffer_is_efault :
  check_syscall (mkInput 64 [4; top_wrap_buf; 16; 0; 0; 0]
                   top_wrap_mem (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) pipe_queued_model
  = CheckOk pipe_queued_model []
  /\ check_syscall (mkInput 64 [4; top_wrap_buf; 16; 0; 0; 0]
                      top_wrap_mem (fun _ => None))
       (with_copyins [(top_wrap_buf, 16%nat)] (mkEffect 16 [] [])) pipe_queued_model
     = CheckReject.
Proof. split; check_eq. Qed.

Example write_pipe_at_the_top_still_delivers :
  answered_events
    (check_syscall (mkInput 64 [4; task_top_buf; 16; 0; 0; 0]
                      task_top_mem (fun _ => None))
       (with_copyins [(task_top_buf, 16%nat)] (mkEffect 16 [] [])) pipe_queued_model)
  = Some []
  /\ check_syscall (mkInput 64 [4; task_top_buf; 16; 0; 0; 0]
                      task_top_mem (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) pipe_queued_model
     = CheckReject.
Proof. split; check_eq. Qed.

(* ---- write (64) on an O_WRONLY file ------------------------------------ *)

Definition rw_filew_model : Model :=
  mkModel [(3, FdFileW 1 (Z_to_bv 64 0))] (mkVmMaps [] [] 0 0 demo_limit) IEof
    (Fs.fs_create_file Fs.fs_empty [102] [104; 105]) None None None.

(** Before the test the arm wrote the sixteen wrapped bytes into the
    file at offset 0; [vfs_write]'s [access_ok] refuses the range before
    [write_begin] is reached, so -EFAULT with the file and [f_pos] as they
    were.  The O_RDWR arm takes the same two tests through the same
    helpers, and [write_range_boundary_pins_the_three_file_kinds] pins
    the three kinds agreeing at [State.TASK_SIZE]. *)
Example write_file_wrapping_buffer_is_efault :
  check_syscall (mkInput 64 [3; top_wrap_buf; 16; 0; 0; 0]
                   top_wrap_mem (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) rw_filew_model
  = CheckOk rw_filew_model []
  /\ check_syscall (mkInput 64 [3; top_wrap_buf; 16; 0; 0; 0]
                      top_wrap_mem (fun _ => None))
       (with_copyins [(top_wrap_buf, 16%nat)] (mkEffect 16 [] [])) rw_filew_model
     = CheckReject.
Proof. split; check_eq. Qed.

Example write_file_at_the_top_still_writes :
  answered_events
    (check_syscall (mkInput 64 [3; task_top_buf; 16; 0; 0; 0]
                      task_top_mem (fun _ => None))
       (with_copyins [(task_top_buf, 16%nat)] (mkEffect 16 [] [])) rw_filew_model)
  = Some []
  /\ check_syscall (mkInput 64 [3; task_top_buf; 16; 0; 0; 0]
                      task_top_mem (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) rw_filew_model
     = CheckReject.
Proof. split; check_eq. Qed.

(* ---- write (64) on a connected socket: declined, at both addresses ----- *)

(** A CONNECTED SOCKET'S WRITE IS DECLINED WHATEVER THE BUFFER
    ([write_spec]'s [FdSocket] arm declines every delivering socket
    write, where [State.sock_send_dead] is false), so there was no
    wrapped answer to withdraw here.  A socket with no connection is
    answered, and that arm asks [vfs_write]'s [access_ok] on the named
    count before its -EPIPE, so it never walked the buffer.  Pinned so
    that a delivering socket write arm grown later has to come past this
    line with its own range test. *)
Example write_socket_is_declined_at_both_addresses :
  check_syscall (mkInput 64 [3; top_wrap_buf; 16; 0; 0; 0]
                   top_wrap_mem (fun _ => None))
    (with_copyins [(top_wrap_buf, 16%nat)] (mkEffect 16 [] []))
    (rw_sock_model NFin)
  = CheckUnmodeled
  /\ check_syscall (mkInput 64 [3; task_top_buf; 16; 0; 0; 0]
                      task_top_mem (fun _ => None))
       (with_copyins [(task_top_buf, 16%nat)] (mkEffect 16 [] []))
       (rw_sock_model NFin)
     = CheckUnmodeled.
Proof. split; check_eq. Qed.

(* --------------- the write side: the random device, stream ends, eventfds *)

(** The random device opened for writing only at fd 3 (what
    [openat("/dev/urandom", O_WRONLY)] installs), and for reading only at
    fd 4. *)
Definition wrpin_urandom_model : Model :=
  mkModel [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
           (3, FdUrandom false true); (4, FdUrandom true false)]
    (mkVmMaps [] [] 0 0 demo_limit) IEof Fs.fs_empty None None None.

(** One end of a stream pair: empty, blocking, 4096-byte buffers, open for
    reading, shut for writing as [shut_wr] says, no reset recorded. *)
Definition wrpin_end (shut_wr : bool) : StreamEnd :=
  mkStreamEnd [] false 4096%Z 4096%Z false shut_wr RsNone.

(** Pair 0: fd 3 is side [false] (state [a]), fd 4 side [true] (state [b]). *)
Definition wrpin_pair_model (a b : StreamEnd) : Model :=
  mkModel [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
           (3, FdStream 0 false a); (4, FdStream 0 true b)]
    (mkVmMaps [] [] 0 0 demo_limit) IEof Fs.fs_empty None None None.

(** An eventfd at fd 3 holding [c], not a semaphore, O_NONBLOCK [nb]. *)
Definition wrpin_eventfd_model (c : Z) (nb : bool) : Model :=
  mkModel [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
           (3, FdEventfd (mkEventfdCtx c false nb))]
    (mkVmMaps [] [] 0 0 demo_limit) IEof Fs.fs_empty None None None.

(** "x" (byte 120) at path 102, inode 1, open in APPEND MODE at fd 3,
    offset 0. *)
Definition wrpin_append_model : Model :=
  mkModel [(3, FdFileA 1 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    (raw_files [([102], [120])]) None None None.

(** "a" at 4096 and nothing else readable: the first of two bytes. *)
Definition wrpin_mem_a : word -> option byte :=
  fun a => if bv_eqb a 4096 then Some 97 else None.

(** The eight little-endian bytes of [v] at 4096, and nothing else. *)
Definition wrpin_ef_src (v : Z) : word -> option byte :=
  bytes_at 4096 (word_le8 (Z_to_bv 64 v)).

(** One iovec [{4096, 8}] at 8192, and nothing else readable. *)
Definition wrpin_iov_eight : word -> option byte :=
  bytes_at 8192 (word_le8 4096 ++ word_le8 8).

(** A WRITE OF TWO READABLE BYTES INTO THE RANDOM DEVICE returns 2, both
    bytes in the ledger and the model unchanged: [random_write_iter]
    (drivers/char/random.c:1448-1451, Linux v6.18.46) is
    [write_pool_user], whose first 64-byte block takes both bytes and
    empties the iterator (:1430-1434).  A short count is refused: a
    block of a readable source does not copy short. *)
Example urandom_write_readable_source_returns_the_count :
  check_syscall (mkInput 64 [3; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
    (with_copyins [(4096, 2%nat)] (mkEffect 2 [] [])) wrpin_urandom_model
  = CheckOk wrpin_urandom_model []
  /\ check_syscall (mkInput 64 [3; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
       (with_copyins [(4096, 1%nat)] (mkEffect 1 [] [])) wrpin_urandom_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** TWO BYTES ASKED, ONLY THE FIRST READABLE: [write_pool_user]'s one
    block copies the readable byte and stops at the unreadable one
    (drivers/char/random.c:1430, Linux v6.18.46; a copy that short is
    riscv64's byte loop, [Sys.Fs.ReadWrite.random_write_countb] says
    why), the short block ends the loop (:1433-1434), and [ret] is 1.
    So 1 is the answer; the -EFAULT of [return ret ? ret : -EFAULT]
    (:1445), which needs a first block that copies nothing, is refused,
    and so is the whole count, which reads the unreadable byte. *)
Example urandom_write_first_byte_readable_is_one :
  check_syscall (mkInput 64 [3; 4096; 2; 0; 0; 0] wrpin_mem_a (fun _ => None))
    (with_copyins [(4096, 1%nat)] (mkEffect 1 [] [])) wrpin_urandom_model
  = CheckOk wrpin_urandom_model []
  /\ check_syscall (mkInput 64 [3; 4096; 2; 0; 0; 0] wrpin_mem_a (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) wrpin_urandom_model
     = CheckReject
  /\ check_syscall (mkInput 64 [3; 4096; 2; 0; 0; 0] wrpin_mem_a (fun _ => None))
       (with_copyins [(4096, 2%nat)] (mkEffect 2 [] [])) wrpin_urandom_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** A SOURCE WITH NO READABLE BYTE is -EFAULT past a page as below it:
    the first block copies nothing and ends the loop
    (drivers/char/random.c:1430-1434, Linux v6.18.46) before the page
    test (:1437-1439), so [ret] stays 0 and the return is -EFAULT
    (:1445).  The page stop at 4096, which needs 4096 bytes copied
    before it, is refused. *)
Example urandom_write_unreadable_source_is_efault :
  check_syscall (mkInput 64 [3; 4096; 4097; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) wrpin_urandom_model
  = CheckOk wrpin_urandom_model []
  /\ check_syscall (mkInput 64 [3; 4096; 4097; 0; 0; 0] (fun _ => None) (fun _ => None))
       (with_copyins [(4096, 4096%nat)] (mkEffect 4096 [] [])) wrpin_urandom_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** WRITEV ON THE DEVICE OPENED FOR WRITING moves the gathered "ab":
    [vfs_writev] (fs/read_write.c:1028-1066, Linux v6.18.46) passes the
    FMODE_WRITE test (:1037-1038), imports the two descriptors
    (:1042-1045) and hands the iterator to the device's [write_iter]
    (:1056-1057), [random_write_iter] (drivers/char/random.c:1448-1451).
    Both descriptors and both source bytes are in the ledger, and the
    -EBADF of a read-only descriptor is refused. *)
Example urandom_writev_moves_the_gathered_bytes :
  check_syscall (mkInput 66 [3; 8192; 2; 0; 0; 0] mem_writev_ab (fun _ => None))
    (with_copyins [(8192, 16%nat); (8208, 16%nat); (4096, 1%nat); (4097, 1%nat)]
       (mkEffect 2 [] [])) wrpin_urandom_model
  = CheckOk wrpin_urandom_model []
  /\ check_syscall (mkInput 66 [3; 8192; 2; 0; 0; 0] mem_writev_ab (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) wrpin_urandom_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** A DESCRIPTOR WHOSE BASE [access_ok] REFUSES is -EFAULT at the import:
    one descriptor is [__import_iovec_ubuf] (lib/iov_iter.c:1330-1350,
    Linux v6.18.46), and [import_ubuf] refuses base 2^63 even at length 0
    (:1437-1438).  The descriptor read is in the ledger; the call is
    answered, so a 0 is refused rather than declined. *)
Example urandom_writev_bad_descriptor_base_is_efault :
  check_syscall (mkInput 66 [3; 8192; 1; 0; 0; 0]
                   (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 0 0) (fun _ => None))
    (with_copyins [(8192, 16%nat)] (mkEffect (errno_ret EFAULT) [] [])) wrpin_urandom_model
  = CheckOk wrpin_urandom_model []
  /\ check_syscall (mkInput 66 [3; 8192; 1; 0; 0; 0]
                      (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 0 0) (fun _ => None))
       (with_copyins [(8192, 16%nat)] (mkEffect 0 [] [])) wrpin_urandom_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** PWRITEV2 ON THE DEVICE OPENED FOR WRITING moves the gathered "ab":
    [do_pwritev] (fs/read_write.c:1141-1160, Linux v6.18.46) reaches
    [vfs_writev] because [do_dentry_open] (fs/open.c:961) gave the device
    FMODE_PWRITE and [memory_open] (drivers/char/mem.c:707-727) adds only
    FMODE_NOWAIT (:701, :721).  The aggregate is 2, so the 0 of an empty
    vector (fs/read_write.c:1047-1049) is refused. *)
Example urandom_pwritev2_moves_the_gathered_bytes :
  check_syscall (mkInput 287 [3; 8192; 2; 0; 0; 0] mem_writev_ab (fun _ => None))
    (with_copyins [(8192, 16%nat); (8208, 16%nat); (4096, 1%nat); (4097, 1%nat)]
       (mkEffect 2 [] [])) wrpin_urandom_model
  = CheckOk wrpin_urandom_model []
  /\ check_syscall (mkInput 287 [3; 8192; 2; 0; 0; 0] mem_writev_ab (fun _ => None))
       (with_copyins [(8192, 16%nat); (8208, 16%nat)] (mkEffect 0 [] [])) wrpin_urandom_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** AT POSITION [LLONG_MAX] the same call is -EINVAL after the import:
    [rw_verify_area] (fs/read_write.c:467-469, Linux v6.18.46) finds
    [pos + count] negative, and [urandom_fops]
    (drivers/char/random.c:1572-1581) sets no FOP_UNSIGNED_OFFSET.  Both
    descriptors are in the ledger; the write is refused. *)
Example urandom_pwritev2_at_llong_max_is_einval :
  check_syscall (mkInput 287 [3; 8192; 2; Z_to_bv 64 (2 ^ 63 - 1); 0; 0]
                   mem_writev_ab (fun _ => None))
    (with_copyins [(8192, 16%nat); (8208, 16%nat)] (mkEffect (errno_ret EINVAL) [] []))
    wrpin_urandom_model
  = CheckOk wrpin_urandom_model []
  /\ check_syscall (mkInput 287 [3; 8192; 2; Z_to_bv 64 (2 ^ 63 - 1); 0; 0]
                      mem_writev_ab (fun _ => None))
       (with_copyins [(8192, 16%nat); (8208, 16%nat); (4096, 1%nat); (4097, 1%nat)]
          (mkEffect 2 [] [])) wrpin_urandom_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** The import's two errnos on the same descriptor: a base [access_ok]
    refuses is -EFAULT ([import_ubuf], lib/iov_iter.c:1437-1438, Linux
    v6.18.46), the descriptor read in the ledger, and 1025 descriptors is
    -EINVAL before any is read ([iovec_from_user], :1306-1307). *)
Example urandom_pwritev2_bad_descriptor_base_is_efault :
  check_syscall (mkInput 287 [3; 8192; 1; 0; 0; 0]
                   (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 0 0) (fun _ => None))
    (with_copyins [(8192, 16%nat)] (mkEffect (errno_ret EFAULT) [] [])) wrpin_urandom_model
  = CheckOk wrpin_urandom_model []
  /\ check_syscall (mkInput 287 [3; 8192; 1025; 0; 0; 0] mem_writev_ab (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) wrpin_urandom_model
     = CheckOk wrpin_urandom_model [].
Proof. split_conj; check_eq. Qed.

(** THE DEVICE OPENED FOR READING ONLY is -EBADF: [vfs_writev]'s
    FMODE_WRITE test (fs/read_write.c:1037-1038, Linux v6.18.46), before
    the import; the write a writable descriptor gets is refused. *)
Example urandom_pwritev2_read_only_is_ebadf :
  check_syscall (mkInput 287 [4; 8192; 2; 0; 0; 0] mem_writev_ab (fun _ => None))
    (mkEffect (errno_ret EBADF) [] []) wrpin_urandom_model
  = CheckOk wrpin_urandom_model []
  /\ check_syscall (mkInput 287 [4; 8192; 2; 0; 0; 0] mem_writev_ab (fun _ => None))
       (with_copyins [(8192, 16%nat); (8208, 16%nat); (4096, 1%nat); (4097, 1%nat)]
          (mkEffect 2 [] [])) wrpin_urandom_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** A BLOCKING SEND WHOSE SOURCE IS READABLE ONLY IN PART DECLINES: of the
    two bytes only the first is readable.  [unix_stream_sendmsg]
    (net/unix/af_unix.c:2401-2546, Linux v6.18.46) copies the send into
    its skb with [skb_copy_datagram_from_iter] (:2493-2495), which
    answers -EFAULT on the short copy, and returns [sent ? : err]
    (:2545); the arm answers a send only where every byte it moves is
    readable, and declines this one. *)
Example stream_write_partly_readable_source_declines :
  check_syscall (mkInput 64 [3; 4096; 2; 0; 0; 0] wrpin_mem_a (fun _ => None))
    (with_copyins [(4096, 2%nat)] (mkEffect 2 [] []))
    (wrpin_pair_model (wrpin_end false) (wrpin_end false))
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** A ZERO-COUNT WRITE TO AN END SHUT FOR WRITING still KILLS, on a launch
    that declares the SIGPIPE death: [sock_write_iter]
    (net/socket.c:1176-1199, Linux v6.18.46) has no zero-count return, and
    [unix_stream_sendmsg] tests SEND_SHUTDOWN (net/unix/af_unix.c:2441-2442)
    before its [while (sent < len)] (:2444), raising SIGPIPE with nothing
    sent (:2537-2540).  The 0 an open end answers is refused. *)
Example stream_write_zero_count_on_a_shut_end_kills :
  check_syscall (mkInput 64 [3; 4096; 0; 0; 0; 0] mem_ab (fun _ => None))
    (mkEffect (errno_ret EPIPE) [] [])
    (with_sigpipe_terminal true (wrpin_pair_model (wrpin_end true) (wrpin_end false)))
  = CheckOk (with_killed (Z_to_bv 64 13)
               (with_sigpipe_terminal true (wrpin_pair_model (wrpin_end true) (wrpin_end false)))) []
  /\ check_syscall (mkInput 64 [3; 4096; 0; 0; 0; 0] mem_ab (fun _ => None))
       (mkEffect 0 [] [])
       (with_sigpipe_terminal true (wrpin_pair_model (wrpin_end true) (wrpin_end false)))
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** WRITEV ON A STREAM-PAIR END: the import's errnos come before the
    protocol.  A base [access_ok] refuses is -EFAULT ([import_ubuf],
    lib/iov_iter.c:1437-1438, Linux v6.18.46), the descriptor read in the
    ledger; 1025 descriptors is -EINVAL ([iovec_from_user],
    :1306-1307), nothing read, and answered rather than declined. *)
Example stream_writev_bad_descriptor_base_is_efault :
  check_syscall (mkInput 66 [3; 8192; 1; 0; 0; 0]
                   (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 0 0) (fun _ => None))
    (with_copyins [(8192, 16%nat)] (mkEffect (errno_ret EFAULT) [] []))
    (wrpin_pair_model (wrpin_end false) (wrpin_end false))
  = CheckOk (wrpin_pair_model (wrpin_end false) (wrpin_end false)) []
  /\ check_syscall (mkInput 66 [3; 8192; 1025; 0; 0; 0] mem_writev_ab (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] [])
       (wrpin_pair_model (wrpin_end false) (wrpin_end false))
     = CheckOk (wrpin_pair_model (wrpin_end false) (wrpin_end false)) [].
Proof. split_conj; check_eq. Qed.

(** AN ADD THAT WOULD REACH [ULLONG_MAX] ON A BLOCKING EVENTFD DECLINES:
    [eventfd_write] (fs/eventfd.c:247-280, Linux v6.18.46) finds
    [ULLONG_MAX - ctx->count > ucnt] false (:262) and, without
    O_NONBLOCK, sleeps (:264-269) for a reader a one-thread process
    cannot be.  The -EAGAIN of a non-blocking eventfd (:261) is not this
    descriptor's answer. *)
Example eventfd_write_overflow_blocking_declines :
  check_syscall (mkInput 64 [3; 4096; 8; 0; 0; 0] (wrpin_ef_src 1) (fun _ => None))
    (with_copyins [(4096, 8%nat)] (mkEffect (errno_ret EAGAIN) [] []))
    (wrpin_eventfd_model (2 ^ 64 - 2) false)
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** A SOURCE [access_ok] REFUSES AT A COUNT THAT IS NOT 8 is -EFAULT: the
    test is [vfs_write]'s (fs/read_write.c:674-675, Linux v6.18.46), made
    before [eventfd_write] is called (:683-684), so its own -EINVAL for a
    count other than 8 (fs/eventfd.c:254-255) is refused. *)
Example eventfd_write_bad_buffer_short_count_is_efault :
  check_syscall (mkInput 64 [3; Z_to_bv 64 TASK_SIZE; 4; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) (wrpin_eventfd_model 5 false)
  = CheckOk (wrpin_eventfd_model 5 false) []
  /\ check_syscall (mkInput 64 [3; Z_to_bv 64 TASK_SIZE; 4; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) (wrpin_eventfd_model 5 false)
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** WRITEV OF EIGHT BYTES ON AN EVENTFD DECLINES: [eventfd_fops]
    (fs/eventfd.c:302-311, Linux v6.18.46) has [.write] and no
    [.write_iter], so [vfs_writev] (fs/read_write.c:1056-1059) hands the
    vector to the per-segment loop, which the arm does not follow.  A
    base [access_ok] refuses is still -EFAULT at the import, ahead of the
    eventfd ([import_ubuf], lib/iov_iter.c:1437-1438). *)
Example eventfd_writev_nonzero_total_declines :
  check_syscall (mkInput 66 [3; 8192; 1; 0; 0; 0] wrpin_iov_eight (fun _ => None))
    (with_copyins [(8192, 16%nat)] (mkEffect 0 [] [])) (wrpin_eventfd_model 5 false)
  = CheckUnmodeled
  /\ check_syscall (mkInput 66 [3; 8192; 1; 0; 0; 0]
                      (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 0 0) (fun _ => None))
       (with_copyins [(8192, 16%nat)] (mkEffect (errno_ret EFAULT) [] []))
       (wrpin_eventfd_model 5 false)
     = CheckOk (wrpin_eventfd_model 5 false) [].
Proof. split_conj; check_eq. Qed.

(** PWRITE64 ON AN EVENTFD is -ESPIPE: [ksys_pwrite64]
    (fs/read_write.c:782-796, Linux v6.18.46) answers it without
    FMODE_PWRITE (:792-795), and the eventfd's file never gets that bit:
    it is built by [anon_inode_getfile_fmode] (fs/eventfd.c:409-410)
    through [file_init_path] (fs/file_table.c:356-377), and only
    [do_dentry_open] (fs/open.c:961) sets FMODE_PWRITE.  The eight-byte
    add a [write] makes is refused. *)
Example eventfd_pwrite64_is_espipe :
  check_syscall (mkInput 68 [3; 4096; 8; 0; 0; 0] (wrpin_ef_src 3) (fun _ => None))
    (mkEffect (errno_ret ESPIPE) [] []) (wrpin_eventfd_model 5 false)
  = CheckOk (wrpin_eventfd_model 5 false) []
  /\ check_syscall (mkInput 68 [3; 4096; 8; 0; 0; 0] (wrpin_ef_src 3) (fun _ => None))
       (with_copyins [(4096, 8%nat)] (mkEffect 8 [] [])) (wrpin_eventfd_model 5 false)
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** PWRITE64 THROUGH O_APPEND AT POSITION [LLONG_MAX] is -EINVAL:
    [rw_verify_area] (fs/read_write.c:467-469, Linux v6.18.46) reads the
    position the call NAMED, before the append moves the write to the end
    of the file, and [pos + count] is negative.  The append is refused. *)
Example pwrite64_append_at_llong_max_is_einval :
  check_syscall (mkInput 68 [3; 4096; 1; Z_to_bv 64 (2 ^ 63 - 1); 0; 0]
                   wrpin_mem_a (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) wrpin_append_model
  = CheckOk wrpin_append_model []
  /\ check_syscall (mkInput 68 [3; 4096; 1; Z_to_bv 64 (2 ^ 63 - 1); 0; 0]
                      wrpin_mem_a (fun _ => None))
       (with_copyins [(4096, 1%nat)] (mkEffect 1 [] [])) wrpin_append_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** WRITEV TO STANDARD OUTPUT WHOSE READER HAS GONE, FROM A SOURCE WITH NO
    READABLE BYTE, still KILLS: [anon_pipe_write] (fs/pipe.c:431, Linux
    v6.18.46) tests [pipe->readers] (:460-465) before it copies a byte, so
    the source is never read; the two descriptors are.  The -EFAULT of a
    source with nothing to gather is refused. *)
Example writev_channel_no_reader_unreadable_source_dies_by_sigpipe :
  check_syscall (mkInput 66 [1; 8192; 2; 0; 0; 0] mem_iovecs_only (fun _ => None))
    (with_copyins [(8192, 16%nat); (8208, 16%nat)] (mkEffect (errno_ret EPIPE) [] []))
    noreader_model
  = CheckOk (with_killed (Z_to_bv 64 13) noreader_model) []
  /\ check_syscall (mkInput 66 [1; 8192; 2; 0; 0; 0] mem_iovecs_only (fun _ => None))
       (with_copyins [(8192, 16%nat); (8208, 16%nat)] (mkEffect (errno_ret EFAULT) [] []))
       noreader_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(* ------------------------------------------- the random stream running out *)

(** THE DECLARED RANDOM STREAM CAN BE SHORTER THAN THE COUNT, and then
    [read_urandom] DECLINES.

    [State.in_urandom] is a colist of bytes and the TYPE admits [IEof],
    so a record can declare five bytes, or none, and the arm has to
    answer for one.  [read_urandom] takes [rw_count_clamp count] from
    the stream and declines if fewer come back, because a short count
    from this device is not a delivery the model has a term for.  What
    keeps a declaration like that out of the whole-program theorems is
    [Run.valid_urandom].

    THE DECLINE IS UNREACHABLE UNDER [Run.valid_input], and that is the
    point of pinning it rather than deleting it.  [Run.valid_urandom]
    asks that a launch's declared stream never end, so no valid input
    reaches this row.  The arm is still TOTAL over
    [State.InputStream] -- it has to be, the type admits [IEof] -- and a
    caller outside [valid_input] still meets the decline, which is what
    these literals are.  What they record is the exact shape the
    validity clause excludes, so that deleting the clause would show up
    as a whole-program theorem going false rather than as a pin quietly
    becoming reachable.

    THE SECOND AND THIRD CONJUNCTS KEEP THE FIRST HONEST: at a count the
    declared stream DOES cover the same descriptor is judged rather than
    declined, and the stream every valid input declares covers every
    count, so the decline is about the declaration's length and not
    about the device. *)
Definition urandom_input (s : InputStream) : ProcInput :=
  mkProcInput_full [[]] [] (demo_fs []) Fs.default_cwd IEof
    demo_uid demo_gid demo_groups net_silent default_nofile
    (Z_to_bv 64 0) demo_hwcap false Sv48 s
    default_kernel default_execfn true true false.

Definition urandom_open_model (s : InputStream) : Model :=
  with_fds [(3, FdUrandom true false)]
    (init_model [] 0 0 demo_sp demo_limit (urandom_input s)).

Example read_past_the_declared_urandom_stream_declines :
  check_syscall
    (mkInput 63 [3; 4096; 128; 0; 0; 0] (fun _ => None) (wmem_first 128))
    (mkEffect 128 [] []) (urandom_open_model hello_stdin)
  = CheckUnmodeled
  /\ match check_syscall
             (mkInput 63 [3; 4096; 5; 0; 0; 0] (fun _ => None) (wmem_first 5))
             (mkEffect 5 [(4096, [104; 101; 108; 108; 111])] [])
             (urandom_open_model hello_stdin) with
     | CheckOk _ _ => True
     | _ => False
     end
  (* and an EMPTY declaration declines at any positive count -- the
     shape [Run.valid_urandom] rules out *)
  /\ check_syscall
       (mkInput 63 [3; 4096; 1; 0; 0; 0] (fun _ => None) (wmem_first 1))
       (mkEffect 1 [(4096, [0])] []) (urandom_open_model IEof)
     = CheckUnmodeled
  (* ...while the stream every valid input declares covers the count the
     examples ask for, and is JUDGED *)
  /\ match check_syscall
             (mkInput 63 [3; 4096; 128; 0; 0; 0] (fun _ => None) (wmem_first 128))
             (mkEffect 128 [(4096, repeat (Z_to_bv 8 0) 128)] [])
             (urandom_open_model default_urandom) with
     | CheckOk _ _ => True
     | _ => False
     end.
Proof.
  split; [check_eq|]. split; [vm_compute; exact I|].
  split; [check_eq | vm_compute; exact I].
Qed.

(* -------------------------------------------------------------------------
   The append and read-write kinds on the calls the examples above do not
   make through them: [read] on the append kind, and [pread64],
   [pwrite64], [lseek] and [readv] on both.

   These pin the remaining arms of this file's syscalls on one one-byte
   file, inode 1, each stating the answer the Lean port's twin of this
   file states for the same call, so that both sides carry a check of
   every arm.  ADMISSION REASON: each is a whole checker verdict -- the
   return, and the fd table and file system after -- beside the
   neighbouring kind's answer refused, and a probe sees one return per
   run and none of the model state it leaves.
   ------------------------------------------------------------------------- *)

(** "f" = "x" (byte 120), inode 1, open O_RDWR at fd 3, offset 0. *)
Definition rdwr_one_byte_model : Model :=
  mkModel [(3, FdFileRW 1 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    (raw_files [([102], [120])]) None None None.

(** The same file open in APPEND MODE at fd 3, offset 0. *)
Definition append_one_byte_model : Model :=
  mkModel [(3, FdFileA 1 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    (raw_files [([102], [120])]) None None None.

(** "f" = "hi", inode 1, open O_RDWR at fd 3, offset 0, named for the
    positional write below that lands past its end. *)
Definition rdwr_hi_model : Model :=
  mkModel [(3, FdFileRW 1 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    (raw_files [([102], [104; 105])]) None None None.

(** A READ THROUGH AN APPEND FD IS -EBADF, as through a write-only one:
    O_APPEND rides on O_WRONLY, so FMODE_READ is clear and [vfs_read]
    answers at its first test (fs/read_write.c:556-557, Linux v6.18.46).
    The second conjunct refuses the 0 a readable kind gives the same
    zero-count call, which an arm reading the kind as [FdFileRW] would
    answer. *)
Example append_read_is_ebadf :
  check_syscall (mkInput 63 [3; 4096; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EBADF) [] []) append_one_byte_model
  = CheckOk append_one_byte_model []
  /\ check_syscall (mkInput 63 [3; 4096; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) append_one_byte_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** [pread64] through an append fd is the same -EBADF.  A regular file
    keeps FMODE_PREAD, so [ksys_pread64] (fs/read_write.c:762-763, Linux
    v6.18.46) hands the call to [vfs_read], whose FMODE_READ test fails
    (:556-557).  Not the -ESPIPE a stream gets ahead of that test, and
    not the 0 the read-write kind answers below. *)
Example append_pread64_is_ebadf :
  check_syscall (mkInput 67 [3; 4096; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EBADF) [] []) append_one_byte_model
  = CheckOk append_one_byte_model []
  /\ check_syscall (mkInput 67 [3; 4096; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) append_one_byte_model
     = CheckReject
  /\ check_syscall (mkInput 67 [3; 4096; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ESPIPE) [] []) append_one_byte_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** [pread64] of 0 bytes through a read-write fd is 0 and moves nothing:
    O_RDWR passes [vfs_read]'s FMODE_READ test, and the advance
    [vfs_read] makes lands in [ksys_pread64]'s own [pos]
    (fs/read_write.c:763, Linux v6.18.46), so the returned model is the
    SAME model, offset 0 included.  The -EBADF the append kind answers
    above is refused. *)
Example rdwr_pread64_is_zero :
  check_syscall (mkInput 67 [3; 4096; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) rdwr_one_byte_model
  = CheckOk rdwr_one_byte_model []
  /\ check_syscall (mkInput 67 [3; 4096; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) rdwr_one_byte_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** [pwrite64] of 0 bytes through an append fd is 0.  [ReadWrite.pwrite64_spec]
    answers this kind on its own arm, the bytes at end-of-file whatever
    [pos] says: [generic_write_checks_count] (fs/read_write.c:1747-1748,
    Linux v6.18.46) replaces [ki_pos] under IOCB_APPEND, and a zero-count
    write returns at :1744-1745 before that line, with nothing written.
    The file is written back as the same "x" ([Fs.file_write] of no bytes
    at its own length) and the offset is not touched; the -EBADF a
    read-only kind gets is refused. *)
Example append_pwrite64_zero_count_is_zero :
  check_syscall (mkInput 68 [3; 4096; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) append_one_byte_model
  = CheckOk (with_fs (Fs.fs_set_ino_data (m_fs append_one_byte_model) 1
                        (Fs.file_write [120] 1 []))
               append_one_byte_model) []
  /\ check_syscall (mkInput 68 [3; 4096; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) append_one_byte_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** [pwrite64] through a read-write fd takes the write-only kind's arm,
    since O_RDWR passes [vfs_write]'s FMODE_WRITE test
    (fs/read_write.c:670-671, Linux v6.18.46).  A zero-count write is 0
    with the file and the offset as they were -- the file written back
    as the same "x", the -EBADF of a read-only kind refused.  And one
    byte at position 4, past the end of "hi", from a source with no
    readable byte is -EFAULT with the file EXTENDED to position 4 by a
    zero hole: [generic_perform_write] (mm/filemap.c:4244-4335) runs
    [write_begin] and [write_end] with nothing copied, and
    [shmem_write_end] (mm/shmem.c:3346-3368) sets [i_size] to the
    position ([ReadWrite.write_fault_extend]).  A 0 offered for the same
    call is refused. *)
Example rdwr_pwrite64_shares_the_write_only_arm :
  check_syscall (mkInput 68 [3; 4096; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) rdwr_one_byte_model
  = CheckOk (with_fs (Fs.fs_set_ino_data (m_fs rdwr_one_byte_model) 1 [120])
               rdwr_one_byte_model) []
  /\ check_syscall (mkInput 68 [3; 4096; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) rdwr_one_byte_model
     = CheckReject
  /\ check_syscall (mkInput 68 [3; 4096; 1; 4; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) rdwr_hi_model
     = CheckOk (with_fs (Fs.fs_set_ino_data (m_fs rdwr_hi_model) 1
                           (Fs.file_extend [104; 105] 4))
                  rdwr_hi_model) []
  /\ check_syscall (mkInput 68 [3; 4096; 1; 4; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) rdwr_hi_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** [lseek(fd, 0, SEEK_SET)] through an append fd is 0, and the offset
    is recorded under the APPEND kind: [ksys_lseek] (fs/read_write.c:393,
    Linux v6.18.46) reads no access mode, and O_APPEND does not stop
    [vfs_llseek] moving [f_pos] -- the append position is taken per
    write, in [generic_write_checks_count] (:1747-1748).  The -ESPIPE a
    stream answers is refused. *)
Example append_lseek_is_zero :
  check_syscall (mkInput 62 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) append_one_byte_model
  = CheckOk (with_fds (fd_insert (m_fds append_one_byte_model) 3 (FdFileA 1 0))
               append_one_byte_model) []
  /\ check_syscall (mkInput 62 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ESPIPE) [] []) append_one_byte_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** ...and through a read-write fd the same, the offset recorded under
    the READ-WRITE kind. *)
Example rdwr_lseek_is_zero :
  check_syscall (mkInput 62 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) rdwr_one_byte_model
  = CheckOk (with_fds (fd_insert (m_fds rdwr_one_byte_model) 3 (FdFileRW 1 0))
               rdwr_one_byte_model) []
  /\ check_syscall (mkInput 62 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ESPIPE) [] []) rdwr_one_byte_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** [readv] through an append fd is -EBADF: [vfs_readv]'s FMODE_READ
    test (fs/read_write.c:999-1000, Linux v6.18.46) refuses it as it
    refuses a write-only fd, and [ReadWrite.readable_fd] is where the
    model turns the kind away.  The vector is one empty, in-range entry,
    so nothing but the mode decides the call; the answer the read-write
    kind gives the same call below -- 0, with the array's sixteen bytes
    in the ledger -- is refused. *)
Example append_readv_is_ebadf :
  readable_fd (FdFileA 1 7) = None
  /\ check_syscall
       (mkInput 65 [3; 8192; 1; 0; 0; 0] (mem_iov_pair 4096 0 4096 0) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) append_one_byte_model
     = CheckOk append_one_byte_model []
  /\ check_syscall
       (mkInput 65 [3; 8192; 1; 0; 0; 0] (mem_iov_pair 4096 0 4096 0) (fun _ => None))
       (with_copyins [(8192, 16%nat)] (mkEffect 0 [] [])) append_one_byte_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** [readv] through a read-write fd READS: O_RDWR passes [vfs_readv]'s
    FMODE_READ test (fs/read_write.c:999-1000, Linux v6.18.46), so the
    one-byte descriptor {4096, 1} delivers "x" and the offset moves to 1,
    recorded under the read-write kind -- an arm writing the entry back
    as [FdFile] would fail here.  The empty vector is 0 with the array
    in the ledger, and the -EBADF the append kind answers to that call
    is refused. *)
Example rdwr_readv_delivers :
  check_syscall (mkInput 65 [3; 8192; 1; 0; 0; 0] mem_readv_iov wmem_readv_one)
    (with_copyins [(8192, 16%nat)] (mkEffect 1 [(4096, [120])] [])) rdwr_one_byte_model
  = CheckOk (with_fds (fd_insert (m_fds rdwr_one_byte_model) 3 (FdFileRW 1 1))
               rdwr_one_byte_model) []
  /\ check_syscall
       (mkInput 65 [3; 8192; 1; 0; 0; 0] (mem_iov_pair 4096 0 4096 0) (fun _ => None))
       (with_copyins [(8192, 16%nat)] (mkEffect 0 [] [])) rdwr_one_byte_model
     = CheckOk rdwr_one_byte_model []
  /\ check_syscall
       (mkInput 65 [3; 8192; 1; 0; 0; 0] (mem_iov_pair 4096 0 4096 0) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) rdwr_one_byte_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(* -------------------------------------------------------------------------
   Reads that reach a TCP socket whose end was already processed, a
   stream-pair end, an eventfd, an unconnected datagram socket and a
   write-only /dev/urandom.

   Each example is the checker's verdict on one call, beside the
   neighbouring answer refused; for a decline, beside the answers the
   checker will not judge there.  Line numbers are Linux v6.18.46
   (commit 1f99e9ab748f).
   ------------------------------------------------------------------------- *)

(** fd 25 a TCP socket in [SkReset], its end already processed (a RST or
    a timeout): [rx] is what is still queued ahead of the end and
    [pending] whether the end's error is still to be reported.  The
    connection's channel is 7. *)
Definition rdpin_reset_model (rx : NetStream) (pending : bool) : Model :=
  mkModel [(25, FdSocket (SkReset rw_sock_peer 7 rx pending false false))]
    (mkVmMaps [] [] 0 0 demo_limit) IEof Fs.fs_empty None None None.

(** One end of a stream pair holding [rx], blocking, open both ways, no
    reset recorded. *)
Definition rdpin_sp_end (rx : list byte) : StreamEnd :=
  mkStreamEnd rx false 4096%Z 4096%Z false false RsNone.

(** Pair 0: fd 3 is side [false] holding [rx], fd 4 side [true] holding
    nothing. *)
Definition rdpin_sp_model (rx : list byte) : Model :=
  mkModel [(3, FdStream 0 false (rdpin_sp_end rx)); (4, FdStream 0 true (rdpin_sp_end []))]
    (mkVmMaps [] [] 0 0 demo_limit) IEof Fs.fs_empty None None None.

(** One end of a stream pair with nothing queued and the reset record
    [rs]. *)
Definition rdpin_reset_end (rs : ResetState) : StreamEnd :=
  mkStreamEnd [] false 4096%Z 4096%Z false false rs.

(** fd 3 alone: its peer is closed. *)
Definition rdpin_sp_alone_model (rs : ResetState) : Model :=
  mkModel [(3, FdStream 0 false (rdpin_reset_end rs))]
    (mkVmMaps [] [] 0 0 demo_limit) IEof Fs.fs_empty None None None.

(** An eventfd at fd 3: counter [c], EFD_SEMAPHORE [sem], O_NONBLOCK
    [nb]. *)
Definition rdpin_ef_model (c : Z) (sem nb : bool) : Model :=
  mkModel [(3, FdEventfd (mkEventfdCtx c sem nb))]
    (mkVmMaps [] [] 0 0 demo_limit) IEof Fs.fs_empty None None None.

(** An unconnected AF_UNIX datagram socket at fd 3, and /dev/urandom
    opened O_WRONLY at fd 4. *)
Definition rdpin_kinds_model : Model :=
  mkModel [(3, FdDgram 1%Z); (4, FdUrandom false true)]
    (mkVmMaps [] [] 0 0 demo_limit) IEof Fs.fs_empty None None None.

(** A SOCKET WHOSE END WAS ALREADY PROCESSED REPORTS THE END'S ERROR ONCE,
    THEN READS 0.  [tcp_reset] (net/ipv4/tcp_input.c:4678-4703) stores
    ECONNRESET in [sk_err] through [tcp_done_with_error]
    (net/ipv4/tcp_input.c:4663-4674); [tcp_write_err]
    (net/ipv4/tcp_timer.c:76-80) stores ETIMEDOUT, or the soft error the
    connection held ([read_timed_out_socket_may_report_the_soft_error]),
    the same way.  With the
    queue empty, the read takes the error with [sock_error]
    (net/ipv4/tcp.c:2744-2747), which clears it
    (include/net/sock.h:2496), so the record moves to not pending.  Once
    it is gone, the read leaves on [RCV_SHUTDOWN] (net/ipv4/tcp.c:2749),
    which [tcp_done] set (net/ipv4/tcp.c:5038): 0, and the error is not
    reported again. *)
Example read_reset_socket_reports_its_pending_error_once :
  check_syscall (mkInput 63 [25; 4096; 16; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ECONNRESET) [] []) (rdpin_reset_model NRst true)
  = CheckOk (with_fds (fd_insert (m_fds (rdpin_reset_model NRst true)) 25
                         (FdSocket (SkReset rw_sock_peer 7 NRst false false false)))
               (rdpin_reset_model NRst true)) []
  /\ check_syscall (mkInput 63 [25; 4096; 16; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) (rdpin_reset_model NRst true)
     = CheckReject
  /\ check_syscall (mkInput 63 [25; 4096; 16; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ETIMEDOUT) [] []) (rdpin_reset_model NTimedOut true)
     = CheckOk (with_fds (fd_insert (m_fds (rdpin_reset_model NTimedOut true)) 25
                            (FdSocket (SkReset rw_sock_peer 7 NTimedOut false false false)))
                  (rdpin_reset_model NTimedOut true)) []
  /\ check_syscall (mkInput 63 [25; 4096; 16; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) (rdpin_reset_model NTimedOut true)
     = CheckReject
  /\ check_syscall (mkInput 63 [25; 4096; 16; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) (rdpin_reset_model NTimedOut false)
     = CheckOk (rdpin_reset_model NTimedOut false) []
  /\ check_syscall (mkInput 63 [25; 4096; 16; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ETIMEDOUT) [] []) (rdpin_reset_model NTimedOut false)
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** The same through [readv]: the pending error once, the record moved,
    the array's two descriptors in the ledger, and 0 refused while the
    error is pending. *)
Example readv_reset_socket_reports_its_pending_error_once :
  let mem := mem_iov_pair 4096 2 4098 3 in
  check_syscall (mkInput 65 [25; 8192; 2; 0; 0; 0] mem (wmem_first 5))
    (with_copyins (import_iovecs_accesses mem 8192 2) (mkEffect (errno_ret ECONNRESET) [] []))
    (rdpin_reset_model NRst true)
  = CheckOk (with_fds (fd_insert (m_fds (rdpin_reset_model NRst true)) 25
                         (FdSocket (SkReset rw_sock_peer 7 NRst false false false)))
               (rdpin_reset_model NRst true)) []
  /\ check_syscall (mkInput 65 [25; 8192; 2; 0; 0; 0] mem (wmem_first 5))
       (with_copyins (import_iovecs_accesses mem 8192 2) (mkEffect 0 [] []))
       (rdpin_reset_model NRst true)
     = CheckReject
  /\ check_syscall (mkInput 65 [25; 8192; 2; 0; 0; 0] mem (wmem_first 5))
       (with_copyins (import_iovecs_accesses mem 8192 2) (mkEffect (errno_ret ETIMEDOUT) [] []))
       (rdpin_reset_model NTimedOut true)
     = CheckOk (with_fds (fd_insert (m_fds (rdpin_reset_model NTimedOut true)) 25
                            (FdSocket (SkReset rw_sock_peer 7 NTimedOut false false false)))
                  (rdpin_reset_model NTimedOut true)) []
  /\ check_syscall (mkInput 65 [25; 8192; 2; 0; 0; 0] mem (wmem_first 5))
       (with_copyins (import_iovecs_accesses mem 8192 2) (mkEffect 0 [] []))
       (rdpin_reset_model NTimedOut true)
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** THE TIMER'S END MAY CARRY THE SOFT ERROR.  [tcp_write_err]
    (net/ipv4/tcp_timer.c:76-80, Linux v6.18.46) stores [sk_err_soft] in
    place of ETIMEDOUT when the connection holds one, and an established
    connection can: [tcp_v4_err] keeps there the EHOSTUNREACH of a
    router's host unreachable when the socket has no IP_RECVERR
    (net/ipv4/tcp_ipv4.c:579-601, :650-656; [State.tcp_soft_errnos]).
    [tcp_recvmsg_locked] hands it back through [sock_error]
    (net/ipv4/tcp.c:2744-2747) as it does ETIMEDOUT.  So a read of a
    connection whose script ends [NTimedOut] answers -EHOSTUNREACH once
    and retires it, on a connection still [SkConnected] (fd 3) and on a
    reset one whose error is pending (fd 25).  THE CONTROLS: a RST
    stores ECONNRESET whatever [sk_err_soft] holds
    (net/ipv4/tcp_input.c:4691-4703), so -EHOSTUNREACH on an [NRst] end
    is refused on both, and -ECONNRESET on the timed-out end stays
    refused.  (313362fd refused the two -EHOSTUNREACH answers.) *)
Example read_timed_out_socket_may_report_the_soft_error :
  check_syscall (mkInput 63 [3; 4096; 16; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EHOSTUNREACH) [] []) (rw_sock_model NTimedOut)
  = CheckOk (with_fds (fd_insert (m_fds (rw_sock_model NTimedOut)) 3
                         (FdSocket (SkReset rw_sock_peer 3 NTimedOut false false false)))
               (rw_sock_model NTimedOut)) []
  /\ check_syscall (mkInput 63 [25; 4096; 16; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EHOSTUNREACH) [] []) (rdpin_reset_model NTimedOut true)
     = CheckOk (with_fds (fd_insert (m_fds (rdpin_reset_model NTimedOut true)) 25
                            (FdSocket (SkReset rw_sock_peer 7 NTimedOut false false false)))
                  (rdpin_reset_model NTimedOut true)) []
  /\ check_syscall (mkInput 63 [3; 4096; 16; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EHOSTUNREACH) [] []) (rw_sock_model NRst)
     = CheckReject
  /\ check_syscall (mkInput 63 [25; 4096; 16; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EHOSTUNREACH) [] []) (rdpin_reset_model NRst true)
     = CheckReject
  /\ check_syscall (mkInput 63 [3; 4096; 16; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ECONNRESET) [] []) (rw_sock_model NTimedOut)
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** The same through [readv]: the soft error once on both connections,
    the record moved, the array's two descriptors in the ledger; on an
    [NRst] end it is refused. *)
Example readv_timed_out_socket_may_report_the_soft_error :
  let mem := mem_iov_pair 4096 2 4098 3 in
  check_syscall (mkInput 65 [3; 8192; 2; 0; 0; 0] mem (wmem_first 5))
    (with_copyins (import_iovecs_accesses mem 8192 2) (mkEffect (errno_ret EHOSTUNREACH) [] []))
    (rw_sock_model NTimedOut)
  = CheckOk (with_fds (fd_insert (m_fds (rw_sock_model NTimedOut)) 3
                         (FdSocket (SkReset rw_sock_peer 3 NTimedOut false false false)))
               (rw_sock_model NTimedOut)) []
  /\ check_syscall (mkInput 65 [25; 8192; 2; 0; 0; 0] mem (wmem_first 5))
       (with_copyins (import_iovecs_accesses mem 8192 2) (mkEffect (errno_ret EHOSTUNREACH) [] []))
       (rdpin_reset_model NTimedOut true)
     = CheckOk (with_fds (fd_insert (m_fds (rdpin_reset_model NTimedOut true)) 25
                            (FdSocket (SkReset rw_sock_peer 7 NTimedOut false false false)))
                  (rdpin_reset_model NTimedOut true)) []
  /\ check_syscall (mkInput 65 [25; 8192; 2; 0; 0; 0] mem (wmem_first 5))
       (with_copyins (import_iovecs_accesses mem 8192 2) (mkEffect (errno_ret EHOSTUNREACH) [] []))
       (rdpin_reset_model NRst true)
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** NO TIMER'S END CARRIES -ENODEV.  The route lookup answers it only for
    an output interface that names no device (net/ipv4/route.c:2801-2805,
    Linux v6.18.46), and no modeled connection has an interface bound, so
    [sk_err_soft] never holds it ([State.tcp_soft_errnos] says why).  So
    a read answering -ENODEV is refused on a timed-out connection still
    [SkConnected] (fd 3) and on a reset one whose timeout is pending
    (fd 25), and so is a [readv] on fd 3.  (8de3d051 admitted all
    three.) *)
Example read_timed_out_socket_never_reports_enodev :
  let mem := mem_iov_pair 4096 2 4098 3 in
  check_syscall (mkInput 63 [3; 4096; 16; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENODEV) [] []) (rw_sock_model NTimedOut)
  = CheckReject
  /\ check_syscall (mkInput 63 [25; 4096; 16; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ENODEV) [] []) (rdpin_reset_model NTimedOut true)
     = CheckReject
  /\ check_syscall (mkInput 65 [3; 8192; 2; 0; 0; 0] mem (wmem_first 5))
       (with_copyins (import_iovecs_accesses mem 8192 2) (mkEffect (errno_ret ENODEV) [] []))
       (rw_sock_model NTimedOut)
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** THE BYTES QUEUED AHEAD OF THE END ARE DELIVERED, the error still
    pending behind them: [tcp_done_with_error]
    (net/ipv4/tcp_input.c:4663-4674) purges only the write queue, and
    [tcp_recvmsg_locked] walks [sk_receive_queue] (net/ipv4/tcp.c:2703)
    before it looks at [sk_err] (net/ipv4/tcp.c:2744), copying at most
    [len] (net/ipv4/tcp.c:2794-2796).  At a count of one the one byte is
    delivered and the two are refused.  With only the first destination
    byte writable the read is declined: what Linux answers there turns on
    how the two bytes were split into skbs. *)
Example read_reset_socket_delivers_the_bytes_ahead_of_the_end :
  check_syscall (mkInput 63 [25; 4096; 100; 0; 0; 0] (fun _ => None) (wmem_first 5))
    (mkEffect 2 [(4096, [104; 105])] []) (rdpin_reset_model (NCons 104 (NCons 105 NRst)) true)
  = CheckOk (with_fds (fd_insert (m_fds (rdpin_reset_model (NCons 104 (NCons 105 NRst)) true)) 25
                         (FdSocket (SkReset rw_sock_peer 7 NRst true false false)))
               (rdpin_reset_model (NCons 104 (NCons 105 NRst)) true))
      [ReadEv 7 104; ReadEv 7 105]
  /\ check_syscall (mkInput 63 [25; 4096; 1; 0; 0; 0] (fun _ => None) (wmem_first 5))
       (mkEffect 1 [(4096, [104])] []) (rdpin_reset_model (NCons 104 (NCons 105 NRst)) true)
     = CheckOk (with_fds (fd_insert (m_fds (rdpin_reset_model (NCons 104 (NCons 105 NRst)) true)) 25
                            (FdSocket (SkReset rw_sock_peer 7 (NCons 105 NRst) true false false)))
                  (rdpin_reset_model (NCons 104 (NCons 105 NRst)) true))
         [ReadEv 7 104]
  /\ check_syscall (mkInput 63 [25; 4096; 1; 0; 0; 0] (fun _ => None) (wmem_first 5))
       (mkEffect 2 [(4096, [104; 105])] []) (rdpin_reset_model (NCons 104 (NCons 105 NRst)) true)
     = CheckReject
  /\ check_syscall (mkInput 63 [25; 4096; 100; 0; 0; 0] (fun _ => None) (wmem_first 1))
       (mkEffect 1 [(4096, [104])] []) (rdpin_reset_model (NCons 104 (NCons 105 NRst)) true)
     = CheckUnmodeled.
Proof. split_conj; check_eq. Qed.

(** The same through [readv]: both bytes into the first segment; one byte
    of room takes exactly one; 0 and a scatter across both segments are
    refused, the scatter being canonical ([iterate_iovec],
    include/linux/iov_iter.h:41-69); and a destination that takes no
    byte is -EFAULT with the queue and the record untouched
    (net/ipv4/tcp.c:2822-2827). *)
Example readv_reset_socket_delivers_the_bytes_ahead_of_the_end :
  let mem := mem_iov_pair 4096 2 4098 3 in
  let m := rdpin_reset_model (NCons 104 (NCons 105 NRst)) true in
  check_syscall (mkInput 65 [25; 8192; 2; 0; 0; 0] mem (wmem_first 5))
    (with_copyins (import_iovecs_accesses mem 8192 2) (mkEffect 2 [(4096, [104; 105])] [])) m
  = CheckOk (with_fds (fd_insert (m_fds m) 25 (FdSocket (SkReset rw_sock_peer 7 NRst true false false))) m)
      [ReadEv 7 104; ReadEv 7 105]
  /\ check_syscall (mkInput 65 [25; 8192; 1; 0; 0; 0] mem_readv_iov wmem_readv_one)
       (with_copyins (import_iovecs_accesses mem_readv_iov 8192 1) (mkEffect 1 [(4096, [104])] [])) m
     = CheckOk (with_fds (fd_insert (m_fds m) 25
                            (FdSocket (SkReset rw_sock_peer 7 (NCons 105 NRst) true false false))) m)
         [ReadEv 7 104]
  /\ check_syscall (mkInput 65 [25; 8192; 2; 0; 0; 0] mem (wmem_first 5))
       (with_copyins (import_iovecs_accesses mem 8192 2) (mkEffect 0 [] [])) m
     = CheckReject
  /\ check_syscall (mkInput 65 [25; 8192; 2; 0; 0; 0] mem (wmem_first 5))
       (with_copyins (import_iovecs_accesses mem 8192 2)
          (mkEffect 2 [(4096, [104]); (4098, [105])] [])) m
     = CheckReject
  /\ check_syscall (mkInput 65 [25; 8192; 2; 0; 0; 0] mem (fun _ => None))
       (with_copyins (import_iovecs_accesses mem 8192 2) (mkEffect (errno_ret EFAULT) [] [])) m
     = CheckOk m [].
Proof. split_conj; check_eq. Qed.

(** /dev/urandom OPENED WRITE-ONLY IS -EBADF ON [read], whatever the
    destination: [init_file] (fs/file_table.c:199) gives the file the
    open's access mode, and [vfs_read] tests FMODE_READ
    (fs/read_write.c:556-557) before [access_ok]; the -EFAULT of a copy
    into the unwritable destination is refused. *)
Example read_urandom_write_only_is_ebadf :
  check_syscall (mkInput 63 [4; 4096; 8; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EBADF) [] []) rdpin_kinds_model
  = CheckOk rdpin_kinds_model []
  /\ check_syscall (mkInput 63 [4; 4096; 8; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) rdpin_kinds_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** BYTES QUEUED ON A STREAM-PAIR END, READ INTO A DESTINATION THAT TAKES
    NONE OF THEM: -EFAULT with the queue untouched, through [read] and
    [readv].  [unix_stream_read_generic] (net/unix/af_unix.c:2933) hands
    the skb to [unix_stream_read_actor] (net/unix/af_unix.c:3142-3150),
    whose copy fails; with nothing copied it answers -EFAULT
    (net/unix/af_unix.c:3069-3072) before it marks a byte consumed
    (net/unix/af_unix.c:3079). *)
Example stream_read_unwritable_destination_is_efault :
  let mem := mem_iov_pair 4096 2 4098 3 in
  check_syscall (mkInput 63 [3; 4096; 2; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) (rdpin_sp_model [97; 98])
  = CheckOk (rdpin_sp_model [97; 98]) []
  /\ check_syscall (mkInput 63 [3; 4096; 2; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 2 [(4096, [97; 98])] []) (rdpin_sp_model [97; 98])
     = CheckReject
  /\ check_syscall (mkInput 65 [3; 8192; 2; 0; 0; 0] mem (fun _ => None))
       (with_copyins (import_iovecs_accesses mem 8192 2) (mkEffect (errno_ret EFAULT) [] []))
       (rdpin_sp_model [97; 98])
     = CheckOk (rdpin_sp_model [97; 98]) []
  /\ check_syscall (mkInput 65 [3; 8192; 2; 0; 0; 0] mem (fun _ => None))
       (with_copyins (import_iovecs_accesses mem 8192 2) (mkEffect 2 [(4096, [97; 98])] []))
       (rdpin_sp_model [97; 98])
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** [readv] OF A STREAM-PAIR END DRAINS WHAT IS QUEUED, up to the vector:
    both bytes land in the first segment and the queue is left empty,
    [unix_stream_read_generic] copying while [size] is left
    (net/unix/af_unix.c:3121); a delivery of one byte is refused. *)
Example readv_stream_delivers_the_queue :
  let mem := mem_iov_pair 4096 2 4098 3 in
  check_syscall (mkInput 65 [3; 8192; 2; 0; 0; 0] mem (wmem_first 5))
    (with_copyins (import_iovecs_accesses mem 8192 2) (mkEffect 2 [(4096, [97; 98])] []))
    (rdpin_sp_model [97; 98])
  = CheckOk (with_fds (fd_insert (m_fds (rdpin_sp_model [97; 98])) 3
                         (FdStream 0 false (se_set_rx (rdpin_sp_end [97; 98]) [])))
               (rdpin_sp_model [97; 98])) []
  /\ check_syscall (mkInput 65 [3; 8192; 2; 0; 0; 0] mem (wmem_first 5))
       (with_copyins (import_iovecs_accesses mem 8192 2) (mkEffect 1 [(4096, [97])] []))
       (rdpin_sp_model [97; 98])
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** A STREAM-PAIR END WHOSE PEER CLOSED, ITS RESET SHOWN ([RsPending]),
    reads -ECONNRESET once and records the error gone: [unix_release_sock]
    (net/unix/af_unix.c:665) left ECONNRESET in the survivor's [sk_err]
    (net/unix/af_unix.c:708-709), and with the queue empty
    [unix_stream_read_generic] takes [sock_error]
    (net/unix/af_unix.c:3008-3010) before the end of file of
    [RCV_SHUTDOWN] (net/unix/af_unix.c:3011); that end of file is
    refused here. *)
Example stream_read_closed_peer_pending_reset_is_econnreset :
  check_syscall (mkInput 63 [3; 4096; 2; 0; 0; 0] (fun _ => None) (wmem_first 2))
    (mkEffect (errno_ret ECONNRESET) [] []) (rdpin_sp_alone_model RsPending)
  = CheckOk (with_fds (fd_insert (m_fds (rdpin_sp_alone_model RsPending)) 3
                         (FdStream 0 false (se_set_reset (rdpin_reset_end RsPending) RsNone)))
               (rdpin_sp_alone_model RsPending)) []
  /\ check_syscall (mkInput 63 [3; 4096; 2; 0; 0; 0] (fun _ => None) (wmem_first 2))
       (mkEffect 0 [] []) (rdpin_sp_alone_model RsPending)
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** A BLOCKING READ OF AN EVENTFD AT 0 IS DECLINED, the -EAGAIN of a
    non-blocking file included: [eventfd_read] (fs/eventfd.c:223-228)
    answers -EAGAIN only with O_NONBLOCK or IOCB_NOWAIT, and otherwise
    sleeps (fs/eventfd.c:230-233) for a writer this one-thread model
    does not have ([ReadWrite.eventfd_read]). *)
Example eventfd_read_zero_counter_blocking_declines :
  check_syscall (mkInput 63 [3; 4096; 8; 0; 0; 0] (fun _ => None) (wmem_first 8))
    (mkEffect (errno_ret EAGAIN) [] []) (rdpin_ef_model 0%Z false false)
  = CheckUnmodeled.
Proof. check_eq. Qed.

(** THE COUNT IS TESTED BEFORE THE COUNTER: four bytes asked of a
    non-blocking eventfd at 0 is -EINVAL ([eventfd_read],
    fs/eventfd.c:220-221, ahead of fs/eventfd.c:223), not -EAGAIN. *)
Example eventfd_read_short_count_beats_the_zero_counter :
  check_syscall (mkInput 63 [3; 4096; 4; 0; 0; 0] (fun _ => None) (wmem_first 8))
    (mkEffect (errno_ret EINVAL) [] []) (rdpin_ef_model 0%Z false true)
  = CheckOk (rdpin_ef_model 0%Z false true) []
  /\ check_syscall (mkInput 63 [3; 4096; 4; 0; 0; 0] (fun _ => None) (wmem_first 8))
       (mkEffect (errno_ret EAGAIN) [] []) (rdpin_ef_model 0%Z false true)
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** A DESTINATION THAT TAKES FOUR OF THE EIGHT BYTES IS DECLINED:
    [eventfd_read] (fs/eventfd.c:235) has already taken the count, and
    the short copy is -EFAULT (fs/eventfd.c:241-242) after storing a
    prefix whose length is the copy routine's progress.  Neither that
    -EFAULT nor the -EINVAL of a short count is judged. *)
Example eventfd_read_partial_destination_declines :
  check_syscall (mkInput 63 [3; 4096; 8; 0; 0; 0] (fun _ => None) (wmem_first 4))
    (mkEffect (errno_ret EFAULT) [] []) (rdpin_ef_model 5%Z false false)
  = CheckUnmodeled
  /\ check_syscall (mkInput 63 [3; 4096; 8; 0; 0; 0] (fun _ => None) (wmem_first 4))
       (mkEffect (errno_ret EINVAL) [] []) (rdpin_ef_model 5%Z false false)
     = CheckUnmodeled.
Proof. split_conj; check_eq. Qed.

(** LSEEK ON A SOCKET'S FILE IS -ESPIPE, a stream-pair end and a datagram
    socket alike: [sock_alloc_file] (net/socket.c:476-499) ends with
    [stream_open], which clears FMODE_LSEEK (fs/open.c:1658), and
    [vfs_llseek] answers -ESPIPE on a file without it
    (fs/read_write.c:387-388).  The 0 of [noop_llseek] is refused. *)
Example lseek_on_a_socket_file_is_espipe :
  check_syscall (mkInput 62 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ESPIPE) [] []) (rdpin_sp_model [])
  = CheckOk (rdpin_sp_model []) []
  /\ check_syscall (mkInput 62 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) (rdpin_sp_model [])
     = CheckReject
  /\ check_syscall (mkInput 62 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ESPIPE) [] []) rdpin_kinds_model
     = CheckOk rdpin_kinds_model []
  /\ check_syscall (mkInput 62 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) rdpin_kinds_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** [pread64] ON A STREAM-PAIR END IS -ESPIPE before the queue is looked
    at: [stream_open] cleared FMODE_PREAD too (fs/open.c:1658), and
    [ksys_pread64] calls [vfs_read] only on a file that carries it
    (fs/read_write.c:762-765).  The delivery a [read] would make is
    refused. *)
Example pread64_stream_end_is_espipe :
  check_syscall (mkInput 67 [3; 4096; 2; 0; 0; 0] (fun _ => None) (wmem_first 2))
    (mkEffect (errno_ret ESPIPE) [] []) (rdpin_sp_model [97; 98])
  = CheckOk (rdpin_sp_model [97; 98]) []
  /\ check_syscall (mkInput 67 [3; 4096; 2; 0; 0; 0] (fun _ => None) (wmem_first 2))
       (mkEffect 2 [(4096, [97; 98])] []) (rdpin_sp_model [97; 98])
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(* ===================================================================== *)
(* The file-size limit of an append ([ReadWrite.append_room])            *)
(* ===================================================================== *)

(** THE SIZE LIMIT OF AN APPEND WRITE: -EFBIG on a file that already
    holds [Fs.MAX_LFS_FILESIZE] bytes.  [generic_write_checks_count]
    (fs/read_write.c:1736-1756, Linux v6.18.46) moves an append write's
    position to [i_size] (:1747-1748), and [generic_write_check_limits]
    answers -EFBIG when that position is at or past [s_maxbytes]
    (:1726-1727), which on tmpfs is [MAX_LFS_FILESIZE]
    ([shmem_fill_super], mm/shmem.c:5118).  No file system with a smaller
    limit can hold such a file, so the answer is the same on every one.
    This pins the only answer for every outcome [o]: the append of the
    bytes the model used to make is refused with it, and so is a decline.
    The file's length is abstract, so no [2^63]-element list is built;
    the call is any one that passes the tests before the limit. *)
Lemma append_write_at_the_cap_is_efbig : forall i fd buf count m p off o,
  fd_lookup (m_fds m) fd = Some (FdFileA p off) ->
  (Fs.MAX_LFS_FILESIZE <= Z.of_nat (length (fs_ino_data (m_fs m) p)))%Z ->
  w_is0 count = false ->
  modeled_rw_range buf count = true ->
  access_okb buf (bv_unsigned count) = true ->
  rw_pos_einvalb off (bv_unsigned count) = false ->
  write_spec fd buf count i m o <-> o = Ok (mkEffect (errno_ret EFBIG) [] []) m [].
Proof.
  intros i fd buf count m p off o Hfd Hcap Hc Hg Hok Hpos.
  assert (Hfb : append_efbigb (fs_ino_data (m_fs m) p) count = true).
  { unfold append_efbigb, append_room. rewrite Hc. cbn [negb andb].
    apply Z.leb_le. lia. }
  assert (Hchk : forall eff, check_write i fd buf count eff m
                             = check_ret_only eff (errno_ret EFBIG) m []).
  { intro eff. unfold check_write. rewrite Hfd. cbv beta iota.
    rewrite Hg, Hok, Hpos. cbn [negb]. cbv beta iota zeta.
    rewrite Hfb. reflexivity. }
  split.
  - intro H. destruct o as [eff m' evs|].
    + apply check_write_complete_ok in H. rewrite Hchk in H.
      apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      reflexivity.
    + apply check_write_complete_unmodeled with (eff := mkEffect 0 [] []) in H.
      rewrite Hchk in H. exfalso. exact (check_ret_only_no_unmodeled _ _ _ _ H).
  - intros ->. apply check_write_sound_ok. rewrite Hchk.
    apply check_ret_only_ok_iff. split; [reflexivity | split; reflexivity].
Qed.

(** AND A WRITE THAT WOULD CROSS THE LIMIT IS CUT TO END AT IT.
    [generic_write_check_limits] shortens the count to
    [s_maxbytes - pos] (fs/read_write.c:1729, Linux v6.18.46), and
    [generic_write_checks] truncates the source to it (:1775), before
    any byte is copied; so the write lands the readable prefix [bs] of
    THAT range and returns its length.  Here the file has [append_room
    data] bytes left below the limit, the call names more, and the cut
    range has a readable byte: the only answer is the cut write, so the
    full write the model used to make is refused.  [write_source] also
    applies [vfs_write]'s [MAX_RW_COUNT] clamp (fs/read_write.c:680-681),
    which Linux applies before the limit.  On a file system whose
    [s_maxbytes] is smaller than [Fs.MAX_LFS_FILESIZE] Linux cuts
    earlier, and the model still admits this write
    ([ReadWrite.append_room]). *)
Lemma append_write_across_the_cap_is_cut_to_end_at_it :
  forall i fd buf count m p off data bs o,
  fd_lookup (m_fds m) fd = Some (FdFileA p off) ->
  fs_ino_data (m_fs m) p = data ->
  (0 < append_room data < bv_unsigned count)%Z ->
  modeled_rw_range buf count = true ->
  access_okb buf (bv_unsigned count) = true ->
  rw_pos_einvalb off (bv_unsigned count) = false ->
  write_source (in_mem i) buf (Z_to_bv 64 (append_room data)) = bs ->
  bs <> [] ->
  write_spec fd buf count i m o <->
  o = Ok (with_copyins [(buf, length bs)] (mkEffect (len_word bs) [] []))
         (with_fds (fd_insert (m_fds m) fd (FdFileA p (append_new_pos data bs off)))
            (with_fs (fs_set_ino_data (m_fs m) p (file_write data (len_word data) bs)) m))
         [].
Proof.
  intros i fd buf count m p off data bs o Hfd Hfs Hroom Hg Hok Hpos Hbs Hne.
  assert (Hmax : Fs.MAX_LFS_FILESIZE = 9223372036854775807%Z) by reflexivity.
  assert (Hrm : (append_room data <= 9223372036854775807)%Z).
  { unfold append_room. rewrite Hmax. lia. }
  assert (Hc : w_is0 count = false) by (apply w_is0_pos; lia).
  assert (Hfb : append_efbigb data count = false).
  { unfold append_efbigb. rewrite Hc. cbn [negb andb]. apply Z.leb_gt. lia. }
  assert (Hcut : append_count data count = Z_to_bv 64 (append_room data)).
  { unfold append_count. rewrite Hc. cbn [orb].
    rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity. }
  assert (Hc' : w_is0 (Z_to_bv 64 (append_room data)) = false).
  { apply w_is0_pos. rewrite Z_to_bv_unsigned, bv_wrap_small; [lia|].
    unfold bv_modulus. change (Z.of_N 64) with 64%Z. lia. }
  assert (Hbl : Nat.eqb (length bs) 0 = false).
  { destruct bs; [contradiction|reflexivity]. }
  assert (Hchk : forall eff, check_write i fd buf count eff m
    = check_ret_only_copyins [(buf, length bs)] eff (len_word bs)
        (with_fds (fd_insert (m_fds m) fd (FdFileA p (append_new_pos data bs off)))
           (with_fs (fs_set_ino_data (m_fs m) p (file_write data (len_word data) bs)) m))
        []).
  { intro eff. unfold check_write. rewrite Hfd. cbv beta iota.
    rewrite Hg, Hok, Hpos. cbn [negb]. cbv beta iota zeta.
    rewrite Hfs, Hfb. cbv beta iota.
    rewrite Hcut, Hbs, Hc', Hbl. reflexivity. }
  split.
  - intro H. destruct o as [eff m' evs|].
    + apply check_write_complete_ok in H. rewrite Hchk in H.
      apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
      reflexivity.
    + apply check_write_complete_unmodeled with (eff := mkEffect 0 [] []) in H.
      rewrite Hchk in H. exfalso.
      exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ H).
  - intros ->. apply check_write_sound_ok. rewrite Hchk.
    apply check_ret_only_copyins_ok_iff. split; [reflexivity | split; reflexivity].
Qed.

(** THE APPEND POSITION AFTER THE CUT.  When the room below the limit is
    readable throughout and within the clamp, the cut write lands exactly
    the room: the file then holds [Fs.MAX_LFS_FILESIZE] bytes, and the
    descriptor's position is [Fs.MAX_LFS_FILESIZE], the new end of file.
    Linux puts the write at [i_size] (fs/read_write.c:1747-1748, Linux
    v6.18.46), advances [ki_pos] by what it copied and copies that back
    to [f_pos] ([new_sync_write], fs/read_write.c:595-596).  So a next
    nonzero append through THIS descriptor is -EINVAL, not -EFBIG:
    [rw_verify_area] (fs/read_write.c:467-469, Linux v6.18.46) tests that
    position, now [LLONG_MAX], before the size limit is reached.  An
    append through a descriptor whose position passes that test is the
    -EFBIG pinned above. *)
Lemma append_write_across_the_cap_ends_at_the_cap :
  forall i fd buf count m p off data bs o,
  fd_lookup (m_fds m) fd = Some (FdFileA p off) ->
  fs_ino_data (m_fs m) p = data ->
  (0 < append_room data < bv_unsigned count)%Z ->
  modeled_rw_range buf count = true ->
  access_okb buf (bv_unsigned count) = true ->
  rw_pos_einvalb off (bv_unsigned count) = false ->
  write_source (in_mem i) buf (Z_to_bv 64 (append_room data)) = bs ->
  Z.of_nat (length bs) = append_room data ->
  write_spec fd buf count i m o ->
  exists eff,
    o = Ok eff
          (with_fds (fd_insert (m_fds m) fd (FdFileA p (append_new_pos data bs off)))
             (with_fs (fs_set_ino_data (m_fs m) p (file_write data (len_word data) bs)) m))
          []
    /\ Z.of_nat (length (file_write data (len_word data) bs)) = Fs.MAX_LFS_FILESIZE
    /\ bv_unsigned (append_new_pos data bs off) = Fs.MAX_LFS_FILESIZE.
Proof.
  intros i fd buf count m p off data bs o Hfd Hfs Hroom Hg Hok Hpos Hbs Hfull Hw.
  assert (Hne : bs <> []).
  { intro E. rewrite E in Hfull. cbn [length] in Hfull. lia. }
  apply (proj1 (append_write_across_the_cap_is_cut_to_end_at_it
                  i fd buf count m p off data bs o Hfd Hfs Hroom Hg Hok Hpos Hbs Hne))
    in Hw.
  subst o. eexists. split; [reflexivity|].
  assert (Hmax : Fs.MAX_LFS_FILESIZE = 9223372036854775807%Z) by reflexivity.
  assert (Hlen : (Z.of_nat (length data) + Z.of_nat (length bs)
                  = Fs.MAX_LFS_FILESIZE)%Z).
  { unfold append_room in Hfull. lia. }
  assert (Hdw : word_to_nat (len_word data) = length data).
  { unfold word_to_nat. rewrite len_word_unsigned by (unfold two_pow_64; lia).
    apply Nat2Z.id. }
  destruct bs as [|b bs']; [contradiction|].
  split.
  - unfold file_write, file_extend. cbv zeta.
    rewrite Hdw, Nat.sub_diag. cbn [repeat]. rewrite app_nil_r, firstn_all.
    rewrite skipn_all2 by lia. rewrite app_nil_r.
    rewrite length_app, Nat2Z.inj_add. exact Hlen.
  - cbn [append_new_pos].
    rewrite bv_add_unsigned, !len_word_unsigned by (unfold two_pow_64; lia).
    rewrite bv_wrap_small; [exact Hlen|].
    unfold bv_modulus. change (Z.of_N 64) with 64%Z. lia.
Qed.

(** A WRITE ONE BYTE PAST THE ROOM LANDS EXACTLY THE ROOM.  This isolates
    the size limit from the other two things that can make a write short:
    the whole named range is readable, so no source fault cuts it, and the
    count is within [MAX_RW_COUNT], so [vfs_write]'s clamp
    (fs/read_write.c:680-681, Linux v6.18.46) does not either.  Only
    [generic_write_check_limits] (fs/read_write.c:1729, Linux v6.18.46)
    is left to cut the count to the room, so the write lands the first
    [append_room data] bytes of the source, exactly that many. *)
Lemma append_write_one_past_the_room_lands_the_room :
  forall i fd buf count m p off data w o,
  fd_lookup (m_fds m) fd = Some (FdFileA p off) ->
  fs_ino_data (m_fs m) p = data ->
  (0 < append_room data)%Z ->
  bv_unsigned count = (append_room data + 1)%Z ->
  (bv_unsigned count <= MAX_RW_COUNT)%Z ->
  modeled_rw_range buf count = true ->
  access_okb buf (bv_unsigned count) = true ->
  rw_pos_einvalb off (bv_unsigned count) = false ->
  read_bytes_map (in_mem i) buf count = Some w ->
  Z.of_nat (length (firstn (Z.to_nat (append_room data)) w)) = append_room data
  /\ (write_spec fd buf count i m o <->
      o = Ok (with_copyins [(buf, length (firstn (Z.to_nat (append_room data)) w))]
                (mkEffect (len_word (firstn (Z.to_nat (append_room data)) w)) [] []))
             (with_fds (fd_insert (m_fds m) fd
                  (FdFileA p (append_new_pos data
                                (firstn (Z.to_nat (append_room data)) w) off)))
                (with_fs (fs_set_ino_data (m_fs m) p
                   (file_write data (len_word data)
                      (firstn (Z.to_nat (append_room data)) w))) m))
             []).
Proof.
  intros i fd buf count m p off data w o Hfd Hfs Hr0 Hc Hcl Hg Hok Hpos Hw.
  pose proof (read_bytes_map_length _ _ _ _ Hw) as Hlw.
  assert (Hlb : Z.of_nat (length (firstn (Z.to_nat (append_room data)) w))
                = append_room data).
  { rewrite length_firstn. lia. }
  assert (Hr64 : bv_unsigned (Z_to_bv 64 (append_room data)) = append_room data).
  { rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|].
    unfold bv_modulus. change (Z.of_N 64) with 64%Z.
    unfold MAX_RW_COUNT in Hcl. lia. }
  assert (Hsrc : write_source (in_mem i) buf (Z_to_bv 64 (append_room data))
                 = firstn (Z.to_nat (append_room data)) w).
  { unfold write_source.
    rewrite (rw_count_clamp_small (Z_to_bv 64 (append_room data)))
      by (rewrite Hr64; lia).
    rewrite Z_to_bv_bv_unsigned, readable_bytes_eq.
    rewrite read_bytes_map_eq in Hw.
    replace (word_to_nat (Z_to_bv 64 (append_room data)))
      with (Z.to_nat (append_room data))
      by (unfold word_to_nat; now rewrite Hr64).
    apply (readable_bytes_aux_prefix _ (word_to_nat count) _ _ _ Hw).
    unfold word_to_nat. lia. }
  split; [exact Hlb|].
  apply (append_write_across_the_cap_is_cut_to_end_at_it
           i fd buf count m p off data _ o Hfd Hfs ltac:(lia) Hg Hok Hpos Hsrc).
  intro E. rewrite E in Hlb. cbn [length] in Hlb. lia.
Qed.

(** -EFBIG ON A VECTORED APPEND TOO.  [vfs_writev] reaches the same
    [generic_write_check_limits] through the file's [write_iter], after
    the import, the zero-aggregate return and the position test
    (fs/read_write.c:1051, Linux v6.18.46), and before any byte is copied
    (:1726-1727).  So once those have passed, a file of
    [Fs.MAX_LFS_FILESIZE] bytes or more admits only -EFBIG, with the
    import's copy-in ledger; an append of the gathered bytes, and a
    decline, are both refused.  The file's length is abstract. *)
Lemma append_writev_at_the_cap_is_efbig :
  forall i fd iov iovcnt m p off iovs o,
  fd_lookup (m_fds m) fd = Some (FdFileA p off) ->
  (Fs.MAX_LFS_FILESIZE <= Z.of_nat (length (fs_ino_data (m_fs m) p)))%Z ->
  import_iovecs (in_mem i) iov (iovcnt32 iovcnt) = ImpOk iovs ->
  Z.eqb (iovs_total (cap_iovecs iovs)) 0 = false ->
  rw_pos_einvalb off (iovs_total (cap_iovecs iovs)) = false ->
  writev_spec fd iov iovcnt i m o <->
  o = Ok (with_copyins (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
            (mkEffect (errno_ret EFBIG) [] [])) m [].
Proof.
  intros i fd iov iovcnt m p off iovs o Hfd Hcap Hiv Htot Hpos.
  assert (Hfb : (append_room (fs_ino_data (m_fs m) p) <=? 0)%Z = true).
  { unfold append_room. apply Z.leb_le. lia. }
  assert (Hchk : forall eff, check_writev i fd iov iovcnt eff m
    = check_ret_only_copyins
        (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
        eff (errno_ret EFBIG) m []).
  { intro eff. unfold check_writev. rewrite Hfd. cbv beta iota zeta.
    rewrite Hiv. cbv beta iota zeta. rewrite Htot, Hpos, Hfb. reflexivity. }
  split.
  - intro H. destruct o as [eff m' evs|].
    + apply check_writev_complete_ok in H. rewrite Hchk in H.
      apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
      reflexivity.
    + apply check_writev_complete_unmodeled with (eff := mkEffect 0 [] []) in H.
      rewrite Hchk in H. exfalso.
      exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ H).
  - intros ->. apply check_writev_sound_ok. rewrite Hchk.
    apply check_ret_only_copyins_ok_iff. split; [reflexivity | split; reflexivity].
Qed.

(** A VECTORED APPEND WITH ROOM LANDS THE CUT PREFIX, whether or not it
    crosses the limit; the crossing itself is the next lemma.
    [generic_write_check_limits] cuts the count to the room
    (fs/read_write.c:1729, Linux v6.18.46), and [generic_write_checks]
    truncates the iterator to it (:1775) before a byte is copied, so the
    write copies the readable prefix of the first [room] bytes of the
    gather and touches no source byte past them.  The model's
    [writev_cut] of the gathered prefix is that list: the gathered prefix
    is readable up to its first fault, so its first [room] bytes are the
    readable prefix of the first [room] bytes.  The return, the copy-in
    ledger and the file all read the cut list, so a later segment past
    the room changes none of them.  The file's length is abstract. *)
Lemma append_writev_with_room_lands_the_cut_prefix :
  forall i fd iov iovcnt m p off data iovs bs o,
  fd_lookup (m_fds m) fd = Some (FdFileA p off) ->
  fs_ino_data (m_fs m) p = data ->
  import_iovecs (in_mem i) iov (iovcnt32 iovcnt) = ImpOk iovs ->
  Z.eqb (iovs_total (cap_iovecs iovs)) 0 = false ->
  rw_pos_einvalb off (iovs_total (cap_iovecs iovs)) = false ->
  (0 < append_room data)%Z ->
  writev_cut (append_room data) (writev_gathered (in_mem i) iovs) = bs ->
  bs <> [] ->
  addr_is_error_b (len_word bs) = false ->
  writev_spec fd iov iovcnt i m o <->
  o = Ok (with_copyins (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt)
                        ++ iov_prefix_accesses (cap_iovecs iovs) (length bs))
            (mkEffect (len_word bs) [] []))
         (with_fds (fd_insert (m_fds m) fd (FdFileA p (append_new_pos data bs off)))
            (with_fs (fs_set_ino_data (m_fs m) p (file_write data (len_word data) bs)) m))
         [].
Proof.
  intros i fd iov iovcnt m p off data iovs bs o Hfd Hfs Hiv Htot Hpos Hroom Hbs Hne
    Herr.
  assert (Hfb : (append_room data <=? 0)%Z = false) by (apply Z.leb_gt; lia).
  assert (Hbl : Nat.eqb (length bs) 0 = false).
  { destruct bs; [contradiction|reflexivity]. }
  assert (Hchk : forall eff, check_writev i fd iov iovcnt eff m
    = check_ret_only_copyins
        (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt)
         ++ iov_prefix_accesses (cap_iovecs iovs) (length bs))
        eff (len_word bs)
        (with_fds (fd_insert (m_fds m) fd (FdFileA p (append_new_pos data bs off)))
           (with_fs (fs_set_ino_data (m_fs m) p (file_write data (len_word data) bs)) m))
        []).
  { intro eff. unfold check_writev. rewrite Hfd. cbv beta iota zeta.
    rewrite Hiv. cbv beta iota zeta. rewrite Hfs.
    rewrite Htot, Hpos, Hfb, Hbs, Hbl, Herr. reflexivity. }
  split.
  - intro H. destruct o as [eff m' evs|].
    + apply check_writev_complete_ok in H. rewrite Hchk in H.
      apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
      reflexivity.
    + apply check_writev_complete_unmodeled with (eff := mkEffect 0 [] []) in H.
      rewrite Hchk in H. exfalso.
      exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ H).
  - intros ->. apply check_writev_sound_ok. rewrite Hchk.
    apply check_ret_only_copyins_ok_iff. split; [reflexivity | split; reflexivity].
Qed.

(** AND A VECTORED APPEND THAT CROSSES THE LIMIT LANDS EXACTLY THE ROOM.
    Here the request and the readable prefix both exceed the room, so
    [generic_write_check_limits] cuts the count to the room
    (fs/read_write.c:1729, Linux v6.18.46), and the iterator truncated to
    it (:1775) is readable throughout: the write lands the first [room]
    bytes, exactly that many, with a copy-in ledger over them.  The
    file's length is abstract. *)
Lemma append_writev_across_the_cap_lands_the_cut_prefix :
  forall i fd iov iovcnt m p off data iovs bs o,
  fd_lookup (m_fds m) fd = Some (FdFileA p off) ->
  fs_ino_data (m_fs m) p = data ->
  import_iovecs (in_mem i) iov (iovcnt32 iovcnt) = ImpOk iovs ->
  rw_pos_einvalb off (iovs_total (cap_iovecs iovs)) = false ->
  (0 < append_room data)%Z ->
  (append_room data < iovs_total (cap_iovecs iovs))%Z ->
  (append_room data < Z.of_nat (length (writev_gathered (in_mem i) iovs)))%Z ->
  writev_cut (append_room data) (writev_gathered (in_mem i) iovs) = bs ->
  addr_is_error_b (len_word bs) = false ->
  Z.of_nat (length bs) = append_room data
  /\ (writev_spec fd iov iovcnt i m o <->
      o = Ok (with_copyins (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt)
                            ++ iov_prefix_accesses (cap_iovecs iovs) (length bs))
                (mkEffect (len_word bs) [] []))
             (with_fds (fd_insert (m_fds m) fd (FdFileA p (append_new_pos data bs off)))
                (with_fs (fs_set_ino_data (m_fs m) p (file_write data (len_word data) bs)) m))
             []).
Proof.
  intros i fd iov iovcnt m p off data iovs bs o Hfd Hfs Hiv Hpos Hroom Hreq Hpre Hbs
    Herr.
  assert (Hlen : Z.of_nat (length bs) = append_room data).
  { rewrite <- Hbs. unfold writev_cut.
    destruct (append_room data <? Z.of_nat (length (writev_gathered (in_mem i) iovs)))%Z
      eqn:E; [|apply Z.ltb_ge in E; lia].
    rewrite length_firstn. lia. }
  split; [exact Hlen|].
  apply (append_writev_with_room_lands_the_cut_prefix
           i fd iov iovcnt m p off data iovs bs o Hfd Hfs Hiv).
  - apply Z.eqb_neq. lia.
  - exact Hpos.
  - exact Hroom.
  - exact Hbs.
  - intro E. rewrite E in Hlen. cbn [length] in Hlen. lia.
  - exact Herr.
Qed.

(** THE CROSSING WITH A LATER UNREADABLE SEGMENT.  One byte of room, a
    first segment of two readable bytes, and a second segment whose byte
    is unreadable.  Linux truncates the iterator to the one byte of room
    (fs/read_write.c:1729 and :1775, Linux v6.18.46) and copies only the
    first byte; it never reaches the second segment, so the write returns
    1 and reads one byte.  The model answers the same: the gathered
    prefix is the two readable bytes, the cut keeps the first, and the
    ledger covers that one byte. *)
Lemma append_writev_one_byte_of_room_skips_a_later_unreadable_segment :
  forall i fd iov iovcnt m p off data a c x0 x1 o,
  fd_lookup (m_fds m) fd = Some (FdFileA p off) ->
  fs_ino_data (m_fs m) p = data ->
  import_iovecs (in_mem i) iov (iovcnt32 iovcnt)
    = ImpOk [(a, Z_to_bv 64 2); (c, Z_to_bv 64 1)] ->
  rw_pos_einvalb off 3%Z = false ->
  append_room data = 1%Z ->
  in_mem i a = Some x0 ->
  in_mem i (a + 1)%bv = Some x1 ->
  in_mem i c = None ->
  writev_spec fd iov iovcnt i m o <->
  o = Ok (with_copyins (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt)
                        ++ [(a, 1%nat)])
            (mkEffect (Z_to_bv 64 1) [] []))
         (with_fds (fd_insert (m_fds m) fd (FdFileA p (append_new_pos data [x0] off)))
            (with_fs (fs_set_ino_data (m_fs m) p (file_write data (len_word data) [x0])) m))
         [].
Proof.
  intros i fd iov iovcnt m p off data a c x0 x1 o Hfd Hfs Hiv Hpos Hroom Ha0 Ha1 Hc0.
  assert (Hcap : cap_iovecs [(a, Z_to_bv 64 2); (c, Z_to_bv 64 1)]
                 = [(a, Z_to_bv 64 2); (c, Z_to_bv 64 1)]) by reflexivity.
  assert (Hrb1 : readable_bytes (in_mem i) a (Z_to_bv 64 2) = [x0; x1]).
  { rewrite readable_bytes_eq. change (word_to_nat (Z_to_bv 64 2)) with 2%nat.
    cbn [readable_bytes_aux]. rewrite Ha0, Ha1. reflexivity. }
  assert (Hrb2 : readable_bytes (in_mem i) c (Z_to_bv 64 1) = []).
  { rewrite readable_bytes_eq. change (word_to_nat (Z_to_bv 64 1)) with 1%nat.
    cbn [readable_bytes_aux]. rewrite Hc0. reflexivity. }
  assert (Hg : writev_gathered (in_mem i) [(a, Z_to_bv 64 2); (c, Z_to_bv 64 1)]
               = [x0; x1]).
  { unfold writev_gathered. rewrite Hcap. cbn [gather_prefix].
    rewrite Hrb1, Hrb2. reflexivity. }
  rewrite (append_writev_with_room_lands_the_cut_prefix
             i fd iov iovcnt m p off data _ [x0] o Hfd Hfs Hiv).
  - rewrite Hcap. reflexivity.
  - rewrite Hcap. reflexivity.
  - rewrite Hcap. exact Hpos.
  - lia.
  - rewrite Hg, Hroom. reflexivity.
  - discriminate.
  - reflexivity.
Qed.

(** THE CUT IS THE GATHER OF THE TRUNCATED SOURCE, at every
    readability.  Linux cuts the count to the room (fs/read_write.c:1729,
    Linux v6.18.46) and truncates the iterator to it (:1775) before it
    copies a byte, so it copies from the first [room] bytes of the source
    only.  The model gathers the readable prefix of the whole capped
    vector and keeps its first [room] bytes ([writev_cut]).  The two are
    the same list whatever is readable or not, before the room or after
    it: the first [r] bytes of the gathered prefix are the gathered
    prefix of the vector truncated to [r] bytes ([cap_iovecs_aux], the
    truncation the aggregate clamp uses).  The gather on the right reads
    no byte past the first [r] bytes of the source.  The first three
    lemmas are steps. *)
Lemma readable_bytes_aux_firstn : forall mp n k a,
  (k <= n)%nat ->
  readable_bytes_aux mp a k = firstn k (readable_bytes_aux mp a n).
Proof.
  intros mp n; induction n as [|n IH]; intros k a Hk.
  - destruct k; [reflexivity|lia].
  - destruct k as [|k]; [reflexivity|].
    cbn [readable_bytes_aux]. destruct (mp a); [|reflexivity].
    cbn [firstn]. f_equal. apply IH. lia.
Qed.

Lemma gather_prefix_cap_aux_zero : forall mp iovs,
  gather_prefix mp (cap_iovecs_aux iovs 0) = [].
Proof.
  intros mp iovs. induction iovs as [|[base len] rest IH]; [reflexivity|].
  cbn [cap_iovecs_aux gather_prefix]. cbv beta zeta.
  replace (Z.min 0 (bv_unsigned len)) with 0%Z
    by (pose proof (bv_unsigned_in_range 64 len); lia).
  replace (0 - 0)%Z with 0%Z by lia.
  assert (H0 : readable_bytes mp base (Z_to_bv 64 0) = []).
  { rewrite readable_bytes_eq. reflexivity. }
  rewrite H0.
  destruct (Z.of_nat (length (@nil byte)) =? bv_unsigned (Z_to_bv 64 0))%Z;
    [exact IH|reflexivity].
Qed.

Lemma gather_prefix_length_le : forall mp iovs,
  (Z.of_nat (length (gather_prefix mp iovs)) <= iovs_total iovs)%Z.
Proof.
  intros mp iovs. induction iovs as [|[base len] rest IH];
    cbn [gather_prefix iovs_total]; [cbn; lia|].
  pose proof (readable_bytes_length_le mp base len).
  pose proof (iovs_total_nonneg rest).
  destruct (Z.of_nat (length (readable_bytes mp base len)) =? bv_unsigned len)%Z;
    [rewrite length_app, Nat2Z.inj_add|]; lia.
Qed.

Lemma gather_prefix_firstn_cap_aux : forall mp iovs r,
  (0 <= r)%Z ->
  firstn (Z.to_nat r) (gather_prefix mp iovs)
  = gather_prefix mp (cap_iovecs_aux iovs r).
Proof.
  intros mp iovs; induction iovs as [|[base len] rest IH]; intros r Hr.
  - cbn [gather_prefix cap_iovecs_aux]. apply firstn_nil.
  - cbn [cap_iovecs_aux gather_prefix]. cbv beta zeta.
    pose proof (bv_unsigned_in_range 64 len) as Hl. unfold bv_modulus in Hl.
    assert (Hn : bv_unsigned (Z_to_bv 64 (Z.min r (bv_unsigned len)))
                 = Z.min r (bv_unsigned len)).
    { rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|].
      unfold bv_modulus. lia. }
    rewrite Hn, !readable_bytes_eq.
    assert (Hw : word_to_nat (Z_to_bv 64 (Z.min r (bv_unsigned len)))
                 = Z.to_nat (Z.min r (bv_unsigned len))).
    { unfold word_to_nat. rewrite Hn. reflexivity. }
    rewrite Hw.
    pose proof (readable_bytes_aux_length_le mp (word_to_nat len) base) as Hbl.
    unfold word_to_nat in *.
    destruct (Z.le_gt_cases (bv_unsigned len) r) as [Hle|Hgt].
    + (* the whole segment lies inside the cut *)
      rewrite (Z.min_r r (bv_unsigned len) Hle).
      destruct (Z.of_nat (length (readable_bytes_aux mp base (Z.to_nat (bv_unsigned len))))
                =? bv_unsigned len)%Z eqn:E.
      * apply Z.eqb_eq in E. rewrite firstn_app.
        rewrite (firstn_all2 (n := Z.to_nat r)) by lia.
        f_equal.
        replace (Z.to_nat r - length (readable_bytes_aux mp base (Z.to_nat (bv_unsigned len))))%nat
          with (Z.to_nat (r - bv_unsigned len)) by lia.
        apply IH. lia.
      * apply firstn_all2. lia.
    + (* the cut falls inside this segment *)
      rewrite (Z.min_l r (bv_unsigned len)) by lia.
      replace (r - r)%Z with 0%Z by lia.
      rewrite gather_prefix_cap_aux_zero, app_nil_r.
      rewrite (readable_bytes_aux_firstn mp (Z.to_nat (bv_unsigned len)) (Z.to_nat r) base)
        by lia.
      assert (Hlhs :
        firstn (Z.to_nat r)
          (if (Z.of_nat (length (readable_bytes_aux mp base (Z.to_nat (bv_unsigned len))))
               =? bv_unsigned len)%Z
           then readable_bytes_aux mp base (Z.to_nat (bv_unsigned len)) ++ gather_prefix mp rest
           else readable_bytes_aux mp base (Z.to_nat (bv_unsigned len)))
        = firstn (Z.to_nat r) (readable_bytes_aux mp base (Z.to_nat (bv_unsigned len)))).
      { destruct (Z.of_nat (length (readable_bytes_aux mp base (Z.to_nat (bv_unsigned len))))
                  =? bv_unsigned len)%Z eqn:E; [|reflexivity].
        apply Z.eqb_eq in E. rewrite firstn_app.
        replace (Z.to_nat r - length (readable_bytes_aux mp base (Z.to_nat (bv_unsigned len))))%nat
          with 0%nat by lia.
        cbn [firstn]. apply app_nil_r. }
      rewrite Hlhs.
      destruct (Z.of_nat (length (firstn (Z.to_nat r)
                  (readable_bytes_aux mp base (Z.to_nat (bv_unsigned len))))) =? r)%Z;
        reflexivity.
Qed.

Lemma writev_cut_is_the_truncated_gather : forall mp iovs r,
  (0 <= r)%Z ->
  writev_cut r (gather_prefix mp iovs) = gather_prefix mp (cap_iovecs_aux iovs r).
Proof.
  intros mp iovs r Hr. rewrite <- (gather_prefix_firstn_cap_aux mp iovs r Hr).
  unfold writev_cut.
  destruct (r <? Z.of_nat (length (gather_prefix mp iovs)))%Z eqn:E; [reflexivity|].
  apply Z.ltb_ge in E. symmetry. apply firstn_all2. lia.
Qed.

(** A VECTORED APPEND LANDS THE READABLE ROOM, WHATEVER FOLLOWS IT.
    [bs] is the source truncated to the room, every byte readable: the
    vector truncated to the room reads whole ([gather_iovecs]).  So [bs]
    is the first [room] bytes of the source when the capped request is
    longer than the room, and the whole capped request when it is not:
    its length is the smaller of the two.  Nothing is assumed about any
    byte after [bs]: readable, unreadable, or a mix, in the same segment
    or a later one.  The return is the length of [bs], the copy-in
    ledger covers [bs], and the file gains [bs] at its end.  This
    is [writev_cut_is_the_truncated_gather] at the syscall: Linux copies
    from the iterator truncated to the room (fs/read_write.c:1729 and
    :1775, Linux v6.18.46).  The file's length is abstract. *)
Lemma append_writev_lands_the_readable_room_whatever_follows :
  forall i fd iov iovcnt m p off data iovs bs o,
  fd_lookup (m_fds m) fd = Some (FdFileA p off) ->
  fs_ino_data (m_fs m) p = data ->
  import_iovecs (in_mem i) iov (iovcnt32 iovcnt) = ImpOk iovs ->
  Z.eqb (iovs_total (cap_iovecs iovs)) 0 = false ->
  rw_pos_einvalb off (iovs_total (cap_iovecs iovs)) = false ->
  (0 < append_room data)%Z ->
  gather_iovecs (in_mem i) (cap_iovecs_aux (cap_iovecs iovs) (append_room data)) = Some bs ->
  writev_spec fd iov iovcnt i m o <->
  o = Ok (with_copyins (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt)
                        ++ iov_prefix_accesses (cap_iovecs iovs) (length bs))
            (mkEffect (len_word bs) [] []))
         (with_fds (fd_insert (m_fds m) fd (FdFileA p (append_new_pos data bs off)))
            (with_fs (fs_set_ino_data (m_fs m) p (file_write data (len_word data) bs)) m))
         [].
Proof.
  intros i fd iov iovcnt m p off data iovs bs o Hfd Hfs Hiv Htot Hpos Hroom Hg.
  assert (Hlen : Z.of_nat (length bs)
                 = Z.min (iovs_total (cap_iovecs iovs)) (append_room data)).
  { rewrite (gather_iovecs_length _ _ _ Hg). apply iovs_total_cap_aux. lia. }
  pose proof (iovs_total_cap iovs) as Hcap.
  pose proof (iovs_total_nonneg iovs) as Hnn.
  pose proof (iovs_total_nonneg (cap_iovecs iovs)) as Hnn'.
  apply Z.eqb_neq in Htot as Htot'.
  apply (append_writev_with_room_lands_the_cut_prefix
           i fd iov iovcnt m p off data iovs bs o Hfd Hfs Hiv Htot Hpos Hroom).
  - unfold writev_gathered. rewrite writev_cut_is_the_truncated_gather by lia.
    apply gather_prefix_full, Hg.
  - intro E. rewrite E in Hlen. cbn [length] in Hlen. lia.
  - unfold addr_is_error_b. change two_pow_64 with 18446744073709551616%Z.
    rewrite len_word_unsigned.
    + apply Z.ltb_ge. unfold MAX_RW_COUNT in Hcap. lia.
    + change two_pow_64 with 18446744073709551616%Z. unfold MAX_RW_COUNT in Hcap. lia.
Qed.

(** THE MUTANT THE LEMMA ABOVE CATCHES: the append arm with the cut
    removed.  [writev_append_arm room] is [writev_spec]'s append arm with
    the room as a parameter.  Given the room it IS that arm, and it
    passes the lemma ([append_writev_arm_with_the_cut_passes_the_lemma]);
    given none, it lands the whole gathered prefix.  Under the lemma's premises with one readable
    byte past the room, the mutant lands more than the room, so the
    lemma's equivalence is false for it
    ([append_writev_without_the_cut_fails_the_lemma]): the lemma fails
    without the cut, which is what the single test it replaces did not. *)
Definition writev_append_arm (room : option Z) (fd iov iovcnt : word) (p : ino) (off : word)
    : Sys SyscallEffect :=
  fun i m o =>
    let data := fs_ino_data (m_fs m) p in
    writev_file_arm (in_mem i) iov iovcnt off room (Some write_fault_keep)
      (fun bs => Some (fun k =>
         bind (set_fs (fs_set_ino_data (m_fs m) p (file_write data (len_word data) bs)))
           (fun _ => bind (set_fds (fd_insert (m_fds m) fd (FdFileA p (append_new_pos data bs off))))
              (fun _ => k))))
      i m o.

Lemma append_writev_arm_with_the_cut_passes_the_lemma :
  forall i fd iov iovcnt m p off data iovs bs o,
  fd_lookup (m_fds m) fd = Some (FdFileA p off) ->
  fs_ino_data (m_fs m) p = data ->
  import_iovecs (in_mem i) iov (iovcnt32 iovcnt) = ImpOk iovs ->
  Z.eqb (iovs_total (cap_iovecs iovs)) 0 = false ->
  rw_pos_einvalb off (iovs_total (cap_iovecs iovs)) = false ->
  (0 < append_room data)%Z ->
  gather_iovecs (in_mem i) (cap_iovecs_aux (cap_iovecs iovs) (append_room data)) = Some bs ->
  writev_append_arm (Some (append_room data)) fd iov iovcnt p off i m o <->
  o = Ok (with_copyins (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt)
                        ++ iov_prefix_accesses (cap_iovecs iovs) (length bs))
            (mkEffect (len_word bs) [] []))
         (with_fds (fd_insert (m_fds m) fd (FdFileA p (append_new_pos data bs off)))
            (with_fs (fs_set_ino_data (m_fs m) p (file_write data (len_word data) bs)) m))
         [].
Proof.
  intros i fd iov iovcnt m p off data iovs bs o Hfd Hfs Hiv Htot Hpos Hroom Hg.
  assert (Hin : forall (k : SyscallInput -> Sys SyscallEffect),
             bind input k i m o <-> k i i m o).
  { intros k. unfold bind, input. destruct o as [x m2 evs|]; split.
    - intros (x0 & m1 & evs1 & evs2 & H1 & H2 & H3).
      injection H1 as -> -> ->. cbn in H3. subst evs. exact H2.
    - intros H. exists i, m, [], evs. split; [reflexivity|].
      split; [exact H|reflexivity].
    - intros [H | (x0 & m1 & evs1 & H1 & H2)]; [discriminate|].
      injection H1 as -> -> ->. exact H2.
    - intros H. right. exists i, m, []. split; [reflexivity|exact H]. }
  (* with the room, the parameterised arm IS [writev_spec]'s append arm *)
  assert (Hspec : writev_spec fd iov iovcnt i m o
                  <-> writev_append_arm (Some (append_room (fs_ino_data (m_fs m) p)))
                        fd iov iovcnt p off i m o).
  { unfold writev_spec. rewrite Hin, bind_get_model, Hfd. reflexivity. }
  subst data. rewrite <- Hspec.
  exact (append_writev_lands_the_readable_room_whatever_follows
           i fd iov iovcnt m p off _ iovs bs o Hfd eq_refl Hiv Htot Hpos Hroom Hg).
Qed.

Lemma append_writev_without_the_cut_fails_the_lemma :
  forall i fd iov iovcnt m p off data iovs bs,
  fd_lookup (m_fds m) fd = Some (FdFileA p off) ->
  fs_ino_data (m_fs m) p = data ->
  import_iovecs (in_mem i) iov (iovcnt32 iovcnt) = ImpOk iovs ->
  Z.eqb (iovs_total (cap_iovecs iovs)) 0 = false ->
  rw_pos_einvalb off (iovs_total (cap_iovecs iovs)) = false ->
  (0 < append_room data)%Z ->
  gather_iovecs (in_mem i) (cap_iovecs_aux (cap_iovecs iovs) (append_room data)) = Some bs ->
  (append_room data < Z.of_nat (length (writev_gathered (in_mem i) iovs)))%Z ->
  ~ (forall o, writev_append_arm None fd iov iovcnt p off i m o <->
       o = Ok (with_copyins (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt)
                             ++ iov_prefix_accesses (cap_iovecs iovs) (length bs))
                 (mkEffect (len_word bs) [] []))
              (with_fds (fd_insert (m_fds m) fd (FdFileA p (append_new_pos data bs off)))
                 (with_fs (fs_set_ino_data (m_fs m) p (file_write data (len_word data) bs)) m))
              []).
Proof.
  intros i fd iov iovcnt m p off data iovs bs Hfd Hfs Hiv Htot Hpos Hroom Hg Hpast Hiff.
  assert (Hlen : Z.of_nat (length bs)
                 = Z.min (iovs_total (cap_iovecs iovs)) (append_room data)).
  { rewrite (gather_iovecs_length _ _ _ Hg). apply iovs_total_cap_aux. lia. }
  assert (HG : (Z.of_nat (length (writev_gathered (in_mem i) iovs)) <= MAX_RW_COUNT)%Z).
  { pose proof (gather_prefix_length_le (in_mem i) (cap_iovecs iovs)) as H.
    rewrite iovs_total_cap in H. unfold writev_gathered. lia. }
  assert (Hne : Nat.eqb (length (writev_gathered (in_mem i) iovs)) 0 = false)
    by (apply Nat.eqb_neq; lia).
  assert (Herr : addr_is_error_b (len_word (writev_gathered (in_mem i) iovs)) = false).
  { unfold addr_is_error_b. change two_pow_64 with 18446744073709551616%Z.
    rewrite len_word_unsigned.
    - apply Z.ltb_ge. unfold MAX_RW_COUNT in HG. lia.
    - change two_pow_64 with 18446744073709551616%Z. unfold MAX_RW_COUNT in HG. lia. }
  (* the mutant lands the whole gathered prefix *)
  assert (Hm : exists eff m' evs,
             writev_append_arm None fd iov iovcnt p off i m (Ok eff m' evs)
             /\ eff_ret eff = len_word (writev_gathered (in_mem i) iovs)).
  { unfold writev_append_arm, writev_file_arm. rewrite Hiv. cbv beta iota zeta.
    rewrite Htot, Hpos, Hne, Herr. cbv beta iota.
    do 3 eexists. split.
    - apply record_copyins_ok.
      eapply bind_ok; [apply modify_ok|].
      eapply bind_ok; [apply modify_ok|].
      unfold writev_ledger. apply record_copyins_ok. apply pure_ok.
    - reflexivity. }
  destruct Hm as (eff & m' & evs & Hm & Hret).
  apply Hiff in Hm. injection Hm as Heff _ _. subst eff. cbn in Hret.
  apply (f_equal bv_unsigned) in Hret.
  pose proof (iovs_total_cap iovs) as Hcap.
  rewrite !len_word_unsigned in Hret;
    change two_pow_64 with 18446744073709551616%Z; unfold MAX_RW_COUNT in *; try lia.
Qed.

(** -EFBIG ON A POSITIONAL APPEND.  [pwrite64] on an O_APPEND descriptor
    lands at [i_size] whatever position it names (fs/read_write.c:1748,
    Linux v6.18.46), so it meets the same limit after [vfs_write]'s
    [access_ok] and [rw_verify_area] on the named position (:674-679).
    On a file of [Fs.MAX_LFS_FILESIZE] bytes or more only -EFBIG is
    admitted. *)
Lemma append_pwrite64_at_the_cap_is_efbig : forall i fd buf count pos m p off o,
  ppos_einvalb pos = false ->
  fd_lookup (m_fds m) fd = Some (FdFileA p off) ->
  (Fs.MAX_LFS_FILESIZE <= Z.of_nat (length (fs_ino_data (m_fs m) p)))%Z ->
  w_is0 count = false ->
  access_okb buf (bv_unsigned count) = true ->
  rw_pos_einvalb pos (bv_unsigned count) = false ->
  pwrite64_spec fd buf count pos i m o <-> o = Ok (mkEffect (errno_ret EFBIG) [] []) m [].
Proof.
  intros i fd buf count pos m p off o Hpp Hfd Hcap Hc Hok Hpos.
  assert (Hfb : append_efbigb (fs_ino_data (m_fs m) p) count = true).
  { unfold append_efbigb, append_room. rewrite Hc. cbn [negb andb].
    apply Z.leb_le. lia. }
  assert (Hchk : forall eff, check_pwrite64 i fd buf count pos eff m
                             = check_ret_only eff (errno_ret EFBIG) m []).
  { intro eff. unfold check_pwrite64. rewrite Hpp. cbv beta iota.
    rewrite Hfd. cbv beta iota.
    rewrite Hok, Hpos. cbn [negb]. cbv beta iota zeta.
    rewrite Hfb. reflexivity. }
  split.
  - intro H. destruct o as [eff m' evs|].
    + apply check_pwrite64_complete_ok in H. rewrite Hchk in H.
      apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      reflexivity.
    + apply check_pwrite64_complete_unmodeled with (eff := mkEffect 0 [] []) in H.
      rewrite Hchk in H. exfalso. exact (check_ret_only_no_unmodeled _ _ _ _ H).
  - intros ->. apply check_pwrite64_sound_ok. rewrite Hchk.
    apply check_ret_only_ok_iff. split; [reflexivity | split; reflexivity].
Qed.

(** -EFBIG ON A [pwritev2] APPEND, without [RWF_NOAPPEND] (a flag word
    of 0): the bytes go to [i_size] (fs/read_write.c:1748, Linux
    v6.18.46), so the limit applies after the import, the zero-aggregate
    return and the position test on the named position (:1051), as for
    [writev].  With [RWF_NOAPPEND] the write lands at the named position
    and meets no limit before [LLONG_MAX]. *)
Lemma append_pwritev2_at_the_cap_is_efbig :
  forall i fd iov iovcnt pos_l pos_h flags m p off iovs o,
  bv_unsigned flags = 0%Z ->
  Z.eqb (bv_signed pos_l) (-1)%Z = false ->
  ppos_einvalb pos_l = false ->
  fd_lookup (m_fds m) fd = Some (FdFileA p off) ->
  (Fs.MAX_LFS_FILESIZE <= Z.of_nat (length (fs_ino_data (m_fs m) p)))%Z ->
  import_iovecs (in_mem i) iov (iovcnt32 iovcnt) = ImpOk iovs ->
  Z.eqb (iovs_total (cap_iovecs iovs)) 0 = false ->
  rw_pos_einvalb pos_l (iovs_total (cap_iovecs iovs)) = false ->
  pwritev2_spec fd iov iovcnt pos_l pos_h flags i m o <->
  o = Ok (with_copyins (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
            (mkEffect (errno_ret EFBIG) [] [])) m [].
Proof.
  intros i fd iov iovcnt pos_l pos_h flags m p off iovs o Hfl Hm1 Hpp Hfd Hcap Hiv
    Htot Hpos.
  assert (Hfb : (append_room (fs_ino_data (m_fs m) p) <=? 0)%Z = true).
  { unfold append_room. apply Z.leb_le. lia. }
  assert (Hchk : forall eff, check_pwritev2 i fd iov iovcnt pos_l pos_h flags eff m
    = check_ret_only_copyins
        (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
        eff (errno_ret EFBIG) m []).
  { intro eff. unfold check_pwritev2. cbv zeta. rewrite Hfl.
    cbn [Z.eqb orb negb]. cbv beta iota.
    rewrite Hm1, Hpp. cbv beta iota.
    rewrite Hfd. cbv beta iota.
    unfold check_pwritev2_file. cbv zeta.
    rewrite (Z.eqb_refl 0). cbn [andb]. cbv beta iota.
    rewrite Hiv. cbv beta iota zeta. rewrite Htot, Hpos, Hfb. reflexivity. }
  split.
  - intro H. destruct o as [eff m' evs|].
    + apply check_pwritev2_complete_ok in H. rewrite Hchk in H.
      apply check_ret_only_copyins_ok_iff in H. destruct H as (-> & -> & ->).
      reflexivity.
    + apply check_pwritev2_complete_unmodeled with (eff := mkEffect 0 [] []) in H.
      rewrite Hchk in H. exfalso.
      exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ H).
  - intros ->. apply check_pwritev2_sound_ok. rewrite Hchk.
    apply check_ret_only_copyins_ok_iff. split; [reflexivity | split; reflexivity].
Qed.

(* ----------- a channel write from a source readable at its start only *)

Definition chan_model : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof).

(** "a" at 4096 and nothing after it. *)
Definition chan_mem_a : word -> option byte :=
  fun a => if bv_eqb a 4096 then Some 97 else None.

(** [n] readable bytes from [base] up, each 0, and nothing past them;
    constant time per address, so a 64 KiB prefix evaluates. *)
Definition chan_mem_prefix (base n : Z) : word -> option byte :=
  fun a => if (base <=? bv_unsigned a)%Z && (bv_unsigned a <? base + n)%Z
           then Some (Z_to_bv 8 0) else None.

(** [write(fd, 4096, count)] over [mem], answering [r] with ledger [cis]. *)
Definition chan_write_from (fd : word) (mem : word -> option byte) (count : Z)
    (r : word) (cis : list (word * nat)) : check_result :=
  check_syscall (mkInput 64 [fd; 4096; Z_to_bv 64 count; 0; 0; 0] mem (fun _ => None))
    (mkEffectU r [] [] [] [] cis) chan_model.

(** A WRITE TO STDOUT OR STDERR FROM A SOURCE READABLE AT ITS START AND
    NOT THROUGHOUT CAN BE -EFAULT.  On a pipe [anon_pipe_write] copies
    the request into one fresh page, or merges it into the last buffer,
    with [copy_page_from_iter], and a short copy with nothing counted is
    -EFAULT (fs/pipe.c:488-492 and :522-528, Linux v6.18.46), however
    many readable bytes preceded the hole; the other far ends a launch
    may give fds 1 and 2 fail their first chunk whole the same way
    ([ReadWrite.channel_first_copy_max]).  So "a" then a hole, count 2,
    is -EFAULT with an empty ledger on fd 1 and on fd 2, beside the
    one-byte short write a first chunk of one byte gives.  An -EFAULT
    claiming the byte it read, and a write of the unreadable byte, are
    refused.  testing/syscall-check/tests/write_spec.c's
    [w-full]/[mem-hide:a1+1:1] case and its [efault] probe on fd 2 are
    the conformance side. *)
Example write_channel_fault_inside_the_first_copy_is_efault :
  chan_write_from 1 chan_mem_a 2 (errno_ret EFAULT) [] = CheckOk chan_model []
  /\ chan_write_from 2 chan_mem_a 2 (errno_ret EFAULT) [] = CheckOk chan_model []
  /\ chan_write_from 1 chan_mem_a 2 1 [(4096, 1%nat)]
    = CheckOk chan_model [WriteEv 1 97]
  /\ chan_write_from 1 chan_mem_a 2 (errno_ret EFAULT) [(4096, 1%nat)] = CheckReject
  /\ chan_write_from 1 chan_mem_a 2 2 [(4096, 2%nat)] = CheckReject.
Proof. split_conj; check_eq. Qed.

(** THE BOUND IS THE LARGEST FIRST COPY OF ANY FAR END,
    [ReadWrite.channel_first_copy_max] = 36544: which far end fds 1 and
    2 have, and in what state, is hidden, and in the configuration of
    record an AF_UNIX stream socket copies one skb of up to
    SKB_MAX_HEAD(0) + UNIX_SKB_FRAGS_SZ = 3776 + 32768 = 36544 bytes first
    (net/unix/af_unix.c [unix_stream_sendmsg] :2457, copied whole at
    :2493-2495, Linux v6.18.46), more than a pipe's page, a terminal's
    2048-byte chunk or a TCP fragment.  So -EFAULT is admitted for a
    fault at offset 36543, which that first skb holds -- a choice over
    the hidden far end, not an answer of its own -- and refused for a
    fault at offset 36544, past every first copy, where the first copy
    moves bytes and a short count answers; the one-byte short write
    stays admitted there.  A terminal copies 65536 bytes first only under
    [TTY_NO_WRITE_SPLIT] (drivers/tty/tty_io.c [iterate_tty_write]
    :976-977), whose setters the configuration of record does not build,
    so a fault at offset 36544 is not inside any first copy. *)
Example write_channel_fault_at_the_largest_first_copy :
  chan_write_from 1 (chan_mem_prefix 4096 36543) 36544 (errno_ret EFAULT) []
    = CheckOk chan_model []
  /\ chan_write_from 1 (chan_mem_prefix 4096 36544) 36545 (errno_ret EFAULT) []
    = CheckReject
  /\ chan_write_from 1 (chan_mem_prefix 4096 36544) 36545 1 [(4096, 1%nat)]
    = CheckOk chan_model [WriteEv 1 0].
Proof. split_conj; check_eq. Qed.

(** THE VECTORED FORM: the first chunk runs across the iovecs in order
    ([copy_page_from_iter] over the gathered iterator, fs/pipe.c:488 and
    :522), so a readable first iovec followed by an unreadable second one
    inside it is -EFAULT too, behind the import's ledger and with no
    payload byte in it; the one-byte short write stays beside it, and an
    -EFAULT that forgets the two descriptors it imported is refused. *)
Example writev_channel_fault_in_a_later_iovec_is_efault :
  let mem := mem_iov_pair 4096 1 12288 1 in
  check_syscall (mkInput 66 [1; 8192; 2; 0; 0; 0] mem (fun _ => None))
    (with_copyins (import_iovecs_accesses mem 8192 2)
       (mkEffect (errno_ret EFAULT) [] [])) chan_model
  = CheckOk chan_model []
  /\ check_syscall (mkInput 66 [1; 8192; 2; 0; 0; 0] mem (fun _ => None))
       (with_copyins (import_iovecs_accesses mem 8192 2 ++
                      iov_prefix_accesses (cap_iovecs [(4096, 1); (12288, 1)]) 1)
          (mkEffect 1 [] [])) chan_model
     = CheckOk chan_model [WriteEv 1 97]
  /\ check_syscall (mkInput 66 [1; 8192; 2; 0; 0; 0] mem (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) chan_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.
