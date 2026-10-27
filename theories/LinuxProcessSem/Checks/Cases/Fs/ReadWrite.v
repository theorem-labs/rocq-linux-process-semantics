(** * LinuxProcessSem.Checks.Cases.Fs.ReadWrite — worked examples over read (63), write (64), pread64 (67), pwrite64 (68), writev (66), readv (65), lseek (62)

    Mirrors [Sys/Fs/ReadWrite.v], which answers to Linux
    [fs/read_write.c]: this file holds the worked examples for the
    syscalls defined there, and no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary. *)

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

Lemma file_write_emits_nothing : forall fd buf count i m p off eff m' evs,
  fd_lookup (m_fds m) fd = Some (FdFileW p off) ->
  write_spec fd buf count i m (Ok eff m' evs) ->
  evs = [].
Proof.
  intros fd buf count i m p off eff m' evs Hfd Hspec.
  apply check_write_complete_ok in Hspec.
  unfold check_write in Hspec. rewrite Hfd in Hspec. cbv iota zeta in Hspec.
  (* the transfer gate, then the -EFAULT gate *)
  destruct (negb (modeled_rw_range buf count)); cbv iota in Hspec; [discriminate|].
  lazymatch type of Hspec with (if ?b then _ else _) = _ => destruct b end;
    cbv iota in Hspec.
  - (* -EFAULT: no writes, no events *)
    apply check_ret_only_ok_iff in Hspec. destruct Hspec as (_ & _ & Hev). exact Hev.
  - (* the range verdict a zero-length write still faces, then the file *)
    destruct (w_is0 count); cbv iota in Hspec;
      [ unfold check_access_ok_zero in Hspec;
        destruct (access_okb buf (bv_unsigned count)); cbv iota in Hspec;
        [ | apply check_ret_only_ok_iff in Hspec;
            destruct Hspec as (_ & _ & Hev); exact Hev ]
      | ].
    all: destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
         cbv iota in Hspec; [|discriminate].
    (* and the past-end-of-file hole guard *)
    all: destruct (negb (modeled_file_gap data off
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
     shape with -ENOTCONN and with the one-shot -ECONNRESET/-ETIMEDOUT
     ([check_socket_pending_error]) where the channel and file arms
     reach it with 0.  Nothing in the proof depended on the 0. *)
  assert (Hnodel : forall v mk mk2 k,
             check_access_ok_zero buf count eff mk
               (check_ret_only eff v mk2 k) = CheckOk m' evs ->
             False).
  { intros v mk mk2 k Hz. unfold check_access_ok_zero in Hz.
    destruct (access_okb buf (bv_unsigned count)); cbv iota in Hz;
      exact (Hro _ _ _ Hz). }
  (* Every [State.FdEntry] constructor, not only the files: [FdSocket] delivers
     too, and so does a pipe READ end and an O_RDWR file, so each gets a
     bullet rather than a one-line dismissal.  The two write-only kinds
     ([FdFileW] and the append [FdFileA]) are the -EBADF pair. *)
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| ]|] eqn:Hfd;
    cbv iota in Hspec;
    [ | | now destruct (Hro _ _ _ Hspec)
      | now destruct (Hro _ _ _ Hspec)
      |
      | destruct (negb (access_okb buf (bv_unsigned count))); cbv iota in Hspec;
        now destruct (Hro _ _ _ Hspec)
      | |
      | destruct (negb rd); cbv iota in Hspec;
        [ now destruct (Hro _ _ _ Hspec) | now destruct (Hnodel _ _ _ _ Hspec) ]
      | (* /dev/urandom: the range verdict, then a delivery of exactly
           [count] bytes, which the count gate keeps under the clamp *)
        destruct (negb (access_okb buf (bv_unsigned count))); cbv iota in Hspec;
        [ now destruct (Hro _ _ _ Hspec)
        | exact (check_read_urandom_delivery_clamped _ _ _ _ _ _ _ _ _ Hspec Hws) ]
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
    destruct (fs_lookup (m_fs m) p) as [data|]; cbv iota in Hspec;
      [|discriminate].
    cbv zeta in Hspec.
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
    destruct (fs_lookup (m_fs m) p) as [data|]; cbv iota in Hspec;
      [|discriminate].
    cbv zeta in Hspec.
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
    destruct sk as [| | |peer ch rx|peer ch]; cbv iota in Hspec;
      try (now destruct (Hnodel _ _ _ _ Hspec)).
    unfold check_socket_pending_error in Hspec.
    destruct rx as [| | |b0 s0]; cbv iota in Hspec;
      try (now destruct (Hnodel _ _ _ _ Hspec)).
    destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)); cbv iota in Hspec;
      [|now destruct (Hro _ _ _ Hspec)].
    destruct (read_bytes_map (in_wmem i) buf
              (len_word (fst (net_take_z (NCons b0 s0) (rw_count_clamp count)))));
      cbv iota in Hspec; [|discriminate Hspec].
    destruct eff as [ret ws zs us cs copyins]. cbn in Hws. subst ws.
    destruct zs; destruct us; destruct cs; destruct copyins;
      cbv iota in Hspec; try discriminate Hspec.
    destruct (bv_eqb a buf && bv_eqb ret (len_word bs)
              && (1 <=? Z.of_nat (length bs))%Z
              && (Z.of_nat (length bs) <=? rw_count_clamp count)%Z
              && listN_eqb (fst (net_take (NCons b0 s0) (length bs))) bs
              && wmem_ok i buf (len_word bs)) eqn:Hcond;
      cbv iota in Hspec; [|discriminate Hspec].
    apply andb_true_iff in Hcond as [Hcond _].
    apply andb_true_iff in Hcond as [Hcond _].
    apply andb_true_iff in Hcond as [_ Hle].
    apply Z.leb_le in Hle.
    pose proof (rw_count_clamp_range count). lia.
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
    can tell — the FULL count acknowledged where the count is one past
    the clamp and the file could have served every byte of it.  The
    delivered prefix is the model's own (so the ONLY wrong thing about
    the effect is the return exceeding the clamp), and the verdict is
    [CheckReject]: rejected, not merely unwitnessed. *)
Lemma read_ret_over_clamp_rejected : forall i m fd p data buf count off w,
  fd_lookup (m_fds m) fd = Some (FdFile p off) ->
  fs_lookup (m_fs m) p = Some data ->
  bv_unsigned count = (MAX_RW_COUNT + 1)%Z ->
  (* the range passes [access_ok]: the clamp is only reached past it *)
  access_okb buf (bv_unsigned count) = true ->
  read_bytes_map (in_wmem i) buf
    (len_word (file_read data off (Z_to_bv 64 (rw_count_clamp count))))
    = Some w ->
  file_read data off (Z_to_bv 64 (rw_count_clamp count)) <> [] ->
  check_read i fd buf count
    (mkEffect count
       [(buf, file_read data off (Z_to_bv 64 (rw_count_clamp count)))] []) m
  = CheckReject.
Proof.
  intros i m fd p data buf count off w Hfd Hfs Hc Hok Hw Hne.
  unfold check_read. rewrite Hfd, Hok. cbv beta iota.
  rewrite Hfs. cbv beta iota zeta.
  destruct (file_read data off (Z_to_bv 64 (rw_count_clamp count)))
    as [|b bsr] eqn:Hbs; [congruence|].
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
  rewrite bv_eqb_refl. rewrite (proj2 (listN_eqb_eq _ _) eq_refl).
  rewrite Hne'. cbn [andb]. reflexivity.
Qed.

(** For a raw count within [IOV_MAX] the 32-bit truncation is the
    identity. *)

Lemma write_channel_outcome : forall fd buf count i m ch bs eff m' evs,
  fd_lookup (m_fds m) fd = Some (FdChannel ch) ->
  ch <> 0 ->
  (* at or below [rw_bytes_max] the clamp inside [Uaccess.write_source]
     is the identity; see [Uaccess.modeled_rw_range] *)
  (bv_unsigned count <= rw_bytes_max)%Z ->
  read_bytes_map (in_mem i) buf count = Some bs ->
  bs <> [] ->
  write_spec fd buf count i m (Ok eff m' evs) ->
  (Z.of_nat (length bs) <= rw_bytes_max)%Z
  /\ exists n, (1 <= n)%nat /\ (n <= length bs)%nat
  /\ eff = with_copyins [(buf, n)]
       (mkEffect (len_word (firstn n bs)) [] []) /\ m' = m
  /\ evs = map (WriteEv ch) (firstn n bs).
Proof.
  intros fd buf count i m ch bs eff m' evs Hfd Hch Hmax Hb Hnonempty Hspec.
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
  rewrite (write_source_of_rw _ _ _ Hmax),
          (readable_bytes_full _ _ _ _ Hb) in Hspec.
  assert (Hg0 : Nat.eqb (length bs) 0 = false) by (apply Nat.eqb_neq; lia).
  rewrite Hg0 in Hspec. cbv iota in Hspec.
  destruct eff as [ret ws zs us cs copyins]; destruct ws as [|? ?];
    destruct zs as [|? ?]; destruct us as [|? ?];
      destruct cs as [|? ?]; try discriminate.
  destruct ((1 <=? bv_unsigned ret)%Z
            && (bv_unsigned ret <=? Z.of_nat (length bs))%Z) eqn:Hgr;
    [|discriminate].
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
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [WriteEv 1 97; WriteEv 1 98].
Proof. check_eq. Qed.

(** The same write("ab") may deliver only "a" — a SHORT channel write,
    the environment's choice: ret 1 with one event for the delivered
    byte is admissible.  What is NOT admissible: delivering more than
    was readable-and-requested (ret 3), and a zero-byte delivery of a
    nonzero request (a blocked pipe blocks; it does not return 0). *)

Example write_ab_short_delivery :
  check_syscall (mkInput 64 [1; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
    (with_copyins [(4096, 1%nat)] (mkEffect 1 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [WriteEv 1 97]
  /\ check_syscall (mkInput 64 [1; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
       (with_copyins [(4096, 3%nat)] (mkEffect 3 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckReject
  /\ check_syscall (mkInput 64 [1; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
       (with_copyins [(4096, 0%nat)] (mkEffect 0 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckReject.
Proof. split; [|split]; check_eq. Qed.

(** ...produces exactly the events of write("a"); write("b"): the trace
    cannot tell the syscall chunking apart, which is the point of
    byte-granularity events.  (Channel writes do not change the model,
    so both writes run from [init_model].) *)

Example write_a_then_b_events :
  check_syscall (mkInput 64 [1; 4096; 1; 0; 0; 0] mem_ab (fun _ => None))
    (with_copyins [(4096, 1%nat)] (mkEffect 1 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [WriteEv 1 97]
  /\ check_syscall (mkInput 64 [1; 4097; 1; 0; 0; 0] mem_ab (fun _ => None))
       (with_copyins [(4097, 1%nat)] (mkEffect 1 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [WriteEv 1 98].
Proof. split; check_eq. Qed.

(** Concretely for writev: [mem_ab] plus an iovec array at 8192
    splitting "ab" into two single-byte iovecs {4096,1},{4097,1} (LP64
    iovec layout: 8-byte little-endian base then length). *)

Example read_bad_fd_ebadf :
  check_syscall (mkInput 63 [5; 4096; 16; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EBADF) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [].
Proof. check_eq. Qed.

Example read_bad_fd_success_rejected :
  check_syscall (mkInput 63 [5; 4096; 16; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 4 [(4096, [1; 2; 3; 4])] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
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
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = check_syscall (mkInput 64 [1; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
      (with_copyins [(4096, 2%nat)] (mkEffect 2 [] []))
      (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  /\ check_syscall (mkInput 64 [Z_to_bv 64 (2 ^ 32 + 1); 4096; 2; 0; 0; 0]
                     mem_ab (fun _ => None))
       (with_copyins [(4096, 2%nat)] (mkEffect 2 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [WriteEv 1 97; WriteEv 1 98].
Proof. split; check_eq. Qed.

Example write_fd_high_bits_ebadf_rejected :
  check_syscall (mkInput 64 [Z_to_bv 64 (2 ^ 32 + 1); 4096; 2; 0; 0; 0]
                   mem_ab (fun _ => None))
    (with_copyins [(4096, 2%nat)] (mkEffect (errno_ret EBADF) [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckReject.
Proof. check_eq. Qed.

(** read(2^32, buf, 16) is a read on STDIN: at end of input it returns 0,
    not -EBADF. *)

Example read_fd_truncates_to_32_bits :
  check_syscall (mkInput 63 [Z_to_bv 64 (2 ^ 32); 4096; 16; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  /\ check_syscall (mkInput 63 [Z_to_bv 64 (2 ^ 32); 4096; 16; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
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
    the append arm's [access_ok] and [rw_verify_area] too, so the three
    really do meet here rather than at three different tests. *)
Example write_count_bound_declines_on_every_file_kind :
  let over := Z_to_bv 64 (rw_bytes_max + 1) in
  let at_bound := Z_to_bv 64 rw_bytes_max in
  let near_top := Z_to_bv 64 (TASK_SIZE - 4) in
  let unmod r := match r with CheckUnmodeled => true | _ => false end in
  let model_of (k : path -> word -> FdEntry) : Model :=
    mkModel [(3, k [102] (Z_to_bv 64 0))] (mkVmMaps [] [] 0 0 demo_limit) IEof
      [([102], [104; 105])] None None None in
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

    So this pins the three kinds at that address instead, and the three
    answers DIFFER -- which is the point rather than a defect, and the
    one thing the shared helper deliberately does NOT make uniform.  The
    append arm models [vfs_write]'s [access_ok] and refuses a delivering
    write whose named range passes TASK_SIZE; the write-only arm models
    neither that test nor [rw_verify_area], judging a delivering write
    by its readable prefix instead, which is a known divergence from
    Linux; and the
    read-write arm takes the write-only answer because it calls the same
    two helpers with the same empty middle in front of them.

    WHAT THIS LINE IS FOR: a change to the shared range judgement has to
    come here and say what it did to all three.  Move the append arm's
    [access_ok] into [ReadWrite.write_file_tail], where it would look
    like tidying, and the first verdict below flips -- the write-only arm
    would start refusing a write Linux's own [vfs_write] does not refuse
    on that arm's reading, which is a behaviour change wearing a
    refactor's clothes. *)
Example write_range_boundary_pins_the_three_file_kinds :
  let near_top := Z_to_bv 64 (TASK_SIZE - 4) in
  let small := Z_to_bv 64 8 in
  let model_of (k : path -> word -> FdEntry) : Model :=
    mkModel [(3, k [102] (Z_to_bv 64 0))] (mkVmMaps [] [] 0 0 demo_limit) IEof
      [([102], [104; 105])] None None None in
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
  verdict (call FdFileW) = 0%nat      (* no access_ok modeled: judged by the readable prefix *)
  /\ verdict (call FdFileA) = 1%nat   (* access_ok modeled: the delivering write is refused *)
  /\ verdict (call FdFileRW) = 0%nat. (* the write-only shape, so the write-only answer *)
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
           [([102], [104; 105])] None None None) in
  unmod (call (FdFileW [102] (Z_to_bv 64 0))) = false
  /\ unmod (call (FdFileRW [102] (Z_to_bv 64 0))) = false
  /\ unmod (call (FdFileA [102] (Z_to_bv 64 0))) = false
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
  let m := mkModel [(3, FdFileRW [102] 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
             [([102], [104; 105])] None None None in
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
  let m := mkModel [(3, FdFileRW [102] 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
             [([102], [104; 105])] None None None in
  match check_syscall (mkInput 63 [3; 4096; 1; 0; 0; 0] (fun _ => None)
                         (fun a => if bv_eqb a 4096 then Some 0 else None))
          (mkEffect 1 [(4096, [104])] []) m with
  | CheckOk m1 [] =>
      fd_lookup (m_fds m1) 3 = Some (FdFileRW [102] 1)
      /\ match check_syscall
                 (mkInput 64 [3; 4096; 1; 0; 0; 0]
                    (fun a => if bv_eqb a 4096 then Some 122 else None)
                    (fun _ => None))
                 (with_copyins [(4096, 1%nat)] (mkEffect 1 [] [])) m1 with
         | CheckOk m2 [] => fs_lookup (m_fs m2) [102] = Some [104; 122]
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
          (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) with
  | CheckOk m1 [] =>
      match check_syscall (mkInput 64 [3; 4096; 2; 0; 0; 0] mem_open_write (fun _ => None))
              (with_copyins [(4096, 2%nat)] (mkEffect 2 [] [])) m1 with
      | CheckOk m2 [] => fs_lookup (m_fs m2) [102] = Some [104; 105]
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
      fs_lookup (m_fs m) [102] = Some [104; 105]
      /\ fd_lookup (m_fds m) 3 = Some (FdFileW [102] 4)
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
      fs_lookup (m_fs m) [102] = Some [104; 105; 0; 0; 122]
      /\ fd_lookup (m_fds m) 3 = Some (FdFileW [102] 5)
  | _ => False
  end.
Proof. vm_compute. split; check_eq. Qed.

(** A zero-length write WITHIN the file is a no-op, since the two
    [file_write] arms agree at or below end-of-file. *)

Example write_zero_len_within_file_is_a_noop :
  match check_syscall (mkInput 64 [3; 4096; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
          (mkEffect 0 [] [])
          (with_fds (fd_insert (m_fds wpast_model) 3 (FdFileW [102] 1)) wpast_model) with
  | CheckOk m [] => fs_lookup (m_fs m) [102] = Some [104; 105]
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** File "f" = "hi" open in APPEND MODE at fd 3, twice, with [f_pos]
    parked at two different places -- one past end-of-file, one at the
    start.  Only an lseek can put it either way. *)

Definition apast_model : Model :=
  mkModel [(3, FdFileA [102] 4)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [104; 105])] None None None.

Definition azero_model : Model :=
  mkModel [(3, FdFileA [102] 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [104; 105])] None None None.

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
         fs_lookup (m_fs m) [102] = Some [104; 105; 122]
         /\ fd_lookup (m_fds m) 3 = Some (FdFileA [102] 3)
     | _ => False
     end.
Proof. vm_compute. repeat split; check_eq. Qed.

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
      fs_lookup (m_fs m1) [102] = Some [104; 105]
      /\ fd_lookup (m_fds m1) 3 = Some (FdFileA [102] 4)
      /\ fs_lookup (m_fs m2) [102] = Some [104; 105]
      /\ fd_lookup (m_fds m2) 3 = Some (FdFileA [102] 0)
  | _, _ => False
  end.
Proof. vm_compute. repeat split; check_eq. Qed.

(** [rw_verify_area]'s position test on a SCALAR write to an APPEND fd,
    which is the one place that arm is not the write-only arm with the
    destination moved.

    [vfs_write] hands [rw_verify_area] (fs/read_write.c) the fd's real
    [&f_pos] and it runs BEFORE the iterator, so
    [(loff_t)(pos + count) < 0] is decided on the position an [lseek]
    left behind — [generic_write_checks] (mm/filemap.c) overrides
    [ki_pos] only once the write is under way.  The append arm keeps the
    test for a reason the write-only arm does not have: it drops
    [modeled_file_gap], and that guard is the whole of why the
    write-only arm's omission of the test is unreachable.  Without
    either guard the
    model would have appended the byte and answered 1 where Linux
    answers -EINVAL.

    A REAL RUN HERE DEPENDS ON THE FILE SYSTEM rather than the model:
    reaching it needs [lseek(fd, LLONG_MAX, SEEK_SET)] to SUCCEED, which
    holds on tmpfs ([s_maxbytes] is [MAX_LFS_FILESIZE]) and fails with
    -EINVAL on a file system whose [s_maxbytes] is smaller, ext4 among
    them.  Both directions are pinned here instead. *)
Definition append_llong_max_model : Model :=
  mkModel [(3, FdFileA [102] (Z_to_bv 64 (2 ^ 63 - 1)))]
    (mkVmMaps [] [] 0 0 demo_limit) IEof [([102], [104; 105])] None None None.

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
      fs_lookup (m_fs m) [102] = Some [104; 105; 0; 0; 122]
      /\ fd_lookup (m_fds m) 3 = Some (FdFileW [102] 5)
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
  intros fd iov iovcnt i m ch iovs bs eff m' evs Hfd Hch Hmax Hiv Hg Hae
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
  assert (Hg0 : Nat.eqb (length bs) 0 = false) by (apply Nat.eqb_neq; lia).
  rewrite Hg0 in Hspec. cbv iota in Hspec.
  rewrite Hae in Hspec. cbv iota in Hspec.
  destruct eff as [ret ws zs us cs copyins]; destruct ws as [|? ?];
    destruct zs as [|? ?]; destruct us as [|? ?];
    destruct cs as [|? ?]; try discriminate.
  destruct ((1 <=? bv_unsigned ret)%Z
            && (bv_unsigned ret <=? Z.of_nat (length bs))%Z
            && negb (addr_is_error_b ret)) eqn:Hgr; [|discriminate].
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
    verdict instead ([Uaccess.access_ok_zero]). *)

Corollary writev_outcome_is_write_outcome :
  forall fd iov iovcnt buf count iv iw m ch iovs bs eff m' evs,
  fd_lookup (m_fds m) fd = Some (FdChannel ch) ->
  ch <> 0 ->
  (bv_unsigned iovcnt <= IOV_MAX)%Z ->
  import_iovecs (in_mem iv) iov iovcnt = ImpOk iovs ->
  gather_iovecs (in_mem iv) (cap_iovecs iovs) = Some bs ->
  addr_is_error_b (len_word bs) = false ->
  bs <> [] ->
  (bv_unsigned count <= rw_bytes_max)%Z ->
  read_bytes_map (in_mem iw) buf count = Some bs ->
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
         Hfd Hch Hmax Hiv Hg Hae Hnonempty Hcmax Hb Hv.
  destruct (writev_channel_outcome _ _ _ _ _ _ _ _ _ _ _
              Hfd Hch Hmax Hiv Hg Hae Hnonempty Hv)
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
  (bv_unsigned iovcnt <= IOV_MAX)%Z ->
  import_iovecs (in_mem iv) iov iovcnt = ImpOk iovs ->
  gather_iovecs (in_mem iv) (cap_iovecs iovs) = Some bs ->
  addr_is_error_b (len_word bs) = false ->
  bs <> [] ->
  (bv_unsigned count <= rw_bytes_max)%Z ->
  read_bytes_map (in_mem iw) buf count = Some bs ->
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
         Hfd Hch Hmax Hiv Hg Hae Hnonempty Hcmax Hb Hw.
  destruct (write_channel_outcome _ _ _ _ _ _ _ _ _ _
              Hfd Hch Hcmax Hb Hnonempty Hw)
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
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = check_syscall (mkInput 64 [1; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
      (with_copyins [(4096, 2%nat)] (mkEffect 2 [] []))
      (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  /\ check_syscall (mkInput 66 [1; 8192; 2; 0; 0; 0] mem_writev_ab (fun _ => None))
       (with_copyins
          (import_iovecs_accesses mem_writev_ab 8192 2 ++
           iov_prefix_accesses (cap_iovecs [(4096, 1); (4097, 1)]) 2)
          (mkEffect 2 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [WriteEv 1 97; WriteEv 1 98].
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
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = check_syscall (mkInput 66 [1; 8192; 2; 0; 0; 0] mem_writev_ab (fun _ => None))
      (with_copyins
         (import_iovecs_accesses mem_writev_ab 8192 2 ++
          iov_prefix_accesses (cap_iovecs [(4096, 1); (4097, 1)]) 2)
         (mkEffect 2 [] []))
      (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  /\ check_syscall (mkInput 66 [1; 8192; Z_to_bv 64 (2 ^ 32); 0; 0; 0]
                     mem_writev_ab (fun _ => None))
       (mkEffect 0 [] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  /\ check_syscall (mkInput 66 [1; 8192; 1025; 0; 0; 0] mem_writev_ab (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  /\ check_syscall (mkInput 66 [1; 8192; Z_to_bv 64 (two_pow_64 - 1); 0; 0; 0]
                     mem_writev_ab (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [].
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
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [WriteEv 1 97; WriteEv 1 98]
  /\ check_syscall (mkInput 66 [1; 8192; Z_to_bv 64 (2 ^ 32 + 2); 0; 0; 0]
                     mem_writev_ab (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckReject
  /\ check_syscall (mkInput 66 [1; 8192; 2; 0; 0; 0] mem_writev_ab (fun _ => None))
       (with_copyins (import_iovecs_accesses mem_writev_ab 8192 2)
          (mkEffect (errno_ret EINVAL) [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
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
  let m := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) in
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
Proof. repeat split; check_eq. Qed.

(** [rw_verify_area]'s position test on the vectored write: a nonempty
    writev to a regular file at offset [LLONG_MAX] is -EINVAL, and the
    file and offset are untouched. *)
Definition writev_llong_max_model : Model :=
  mkModel [(3, FdFileW [102] (Z_to_bv 64 (2 ^ 63 - 1)))]
    (mkVmMaps [] [] 0 0 demo_limit) IEof [([102], [])] None None None.

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
  let m := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) in
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
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  /\ check_syscall
       (mkInput 65 [0; 8192; 2; 0; 0; 0]
          mem_readv_cap_order (fun _ => None))
       (with_copyins
          (import_iovecs_accesses mem_readv_cap_order 8192 2)
          (mkEffect (errno_ret EFAULT) [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  /\ check_syscall
       (mkInput 65 [0; 8192; 2; 0; 0; 0]
          mem_readv_cap_order (fun _ => None))
       (with_copyins
          (import_iovecs_accesses mem_readv_cap_order 8192 2)
          (mkEffect 0 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckReject.
Proof. repeat split; check_eq. Qed.

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
  mkModel [(3, FdFile [102] 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [120])] None None None.

Example readv_huge_len_delivers_one_byte_without_unary_expansion :
  check_syscall
    (mkInput 65 [0; 8192; 1; 0; 0; 0] mem_readv_huge wmem_readv_one)
    (with_copyins (import_iovecs_accesses mem_readv_huge 8192 1)
       (mkEffect 1 [(4096, [120])] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] (ICons 120 IEof)))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [ReadEv 0 120]
  /\ check_syscall
       (mkInput 65 [3; 8192; 1; 0; 0; 0] mem_readv_huge wmem_readv_one)
       (with_copyins (import_iovecs_accesses mem_readv_huge 8192 1)
          (mkEffect 1 [(4096, [120])] [])) readv_huge_file_model
     = CheckOk
         (with_fds
            (fd_insert (m_fds readv_huge_file_model) 3 (FdFile [102] 1))
            readv_huge_file_model) [].
Proof. split; check_eq. Qed.

(** The matching offset guard is bounded by the concrete file length too:
    an enormous offset on a one-byte file reaches EOF without converting
    that offset to a request-sized natural. *)

Example readv_huge_file_offset_is_bounded_by_file_length :
  let m := with_fds
    (fd_insert (m_fds readv_huge_file_model) 3
      (FdFile [102] readv_huge_len)) readv_huge_file_model in
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
  mkModel [(3, FdFileW [102] 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [])] None None None.

Example readv_heap_iovec_boundary_fails_closed :
  check_syscall
    (mkInput 65 [0; 8192; 8; 0; 0; 0] mem_readv_eight_zero (fun _ => None))
    (with_copyins (import_iovecs_accesses mem_readv_eight_zero 8192 8)
       (mkEffect 0 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  /\ check_syscall
       (mkInput 65 [0; 8192; 8; 0; 0; 0]
          mem_readv_eight_zero (fun _ => None))
       (with_copyins (import_iovecs_accesses mem_readv_eight_zero 8192 8)
          (mkEffect (errno_ret ENOMEM) [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckReject
  /\ check_syscall
       (mkInput 65 [0; 8192; 9; 0; 0; 0]
          mem_readv_eight_zero (fun _ => None))
       (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckUnmodeled
  /\ check_syscall
       (mkInput 65 [0; 8192; 9; 0; 0; 0]
          mem_readv_eight_zero (fun _ => None))
       (mkEffect (errno_ret ENOMEM) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckUnmodeled
  /\ check_syscall
       (mkInput 65 [0; 8192; 1024; 0; 0; 0]
          mem_readv_eight_zero (fun _ => None))
       (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckUnmodeled
  /\ check_syscall
       (mkInput 65 [5; 8192; 9; 0; 0; 0]
          mem_readv_eight_zero (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
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
       (mkEffect (errno_ret EINVAL) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckUnmodeled
  /\ check_syscall
       (mkInput 65 [0; 8192; Z_to_bv 64 (2 ^ 32 + 9); 0; 0; 0]
          mem_readv_eight_zero (fun _ => None))
       (mkEffect (errno_ret ENOMEM) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckUnmodeled
  /\ check_syscall
       (mkInput 65 [0; 8192; 1025; 0; 0; 0]
          mem_readv_eight_zero (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [].
Proof. repeat split; check_eq. Qed.

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
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = check_syscall (mkInput 65 [0; 8192; 1; 0; 0; 0] mem_readv_iov (fun _ => None))
      (with_copyins (import_iovecs_accesses mem_readv_iov 8192 1)
         (mkEffect 0 [] []))
      (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  /\ check_syscall (mkInput 65 [0; 8192; 1; 0; 0; 0] mem_readv_iov (fun _ => None))
       (with_copyins (import_iovecs_accesses mem_readv_iov 8192 1)
          (mkEffect 0 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  (* two descriptors reaches the unreadable one: -EFAULT, so a zero return
     is inadmissible there -- the conjunct that makes the first two
     non-vacuous *)
  /\ check_syscall (mkInput 65 [0; 8192; 2; 0; 0; 0] mem_readv_iov (fun _ => None))
       (with_copyins (import_iovecs_accesses mem_readv_iov 8192 2)
          (mkEffect 0 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
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
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  /\ check_syscall (mkInput 65 [0; 8192; Z_to_bv 64 (2 ^ 32 + 1); 0; 0; 0]
                     mem_readv_iov (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckReject
  /\ check_syscall (mkInput 65 [0; 8192; 1; 0; 0; 0] mem_readv_iov (fun _ => None))
       (with_copyins (import_iovecs_accesses mem_readv_iov 8192 1)
          (mkEffect (errno_ret EINVAL) [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
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
    (mkEffect (errno_ret EBADF) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  /\ check_syscall (mkInput 65 [1; 8192; 2; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckReject.
Proof. split; check_eq. Qed.

(** A file "abcde" on fd 3 at offset [off], and a directory on fd 3. *)
Definition readv_abcde_model (off : word) : Model :=
  mkModel [(3, FdFile [102] off)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [97; 98; 99; 100; 101])] None None None.

Definition readv_dir_model : Model :=
  mkModel [(3, FdDir)] (mkVmMaps [] [] 0 0 demo_limit) IEof [] None None None.

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
Proof. repeat split; check_eq. Qed.

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
Proof. repeat split; check_eq. Qed.

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
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  /\ check_syscall (mkInput 65 [0; 8192; 2; 0; 0; 0] mem_readv_len_only (fun _ => None))
       (with_copyins (import_iovecs_accesses mem_readv_len_only 8192 2)
          (mkEffect (errno_ret EINVAL) [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** A DESCRIPTOR WHOSE LENGTH FAULTS WAS NOT READ.  [copy_iovec_from_user]
    loads [iov_len] before [iov_base] (lib/iov_iter.c:1272-1273,
    v6.18.46), and a fault leaves at once.  Here the descriptor at 69624
    straddles a page boundary: its [iov_base] bytes, 69624..69631, end a
    MAP_NORESERVE page that nothing has touched, so they read as zero,
    and its [iov_len] bytes, 69632..69639, are unmapped.  Linux returns -EFAULT having read
    nothing, so the ledger is empty on each path: readv at a count of 2
    ([copy_iovecs_aux]) and of 1 ([__import_iovec_ubuf]), and
    [copy_iovecs_accesses] as [Net.Socket.sendmsg_spec] calls it.  The
    empty ledger charges no backing; the whole-descriptor range
    [(69624, 16)] would charge the lazy page for a read Linux did not
    make.
    The two [check_syscall] conjuncts pin the ledger readv answers with. *)
Definition iov_len_fault_model : Model :=
  vm_add_lazy 65536 4096
    (with_vmmaps (mkVmMaps [] [(65536, 4096)] 0 0 4096)
       (init_model [] 0 0 demo_sp 4096 (demo_input [] IEof))).

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
    tmpfs.  The scalar [read] reaches the same test on the kernel and
    still answers 0 in the model: the last two conjuncts pin THAT known
    divergence from Linux, so that closing it is a visible flip here
    rather than a silent one. *)
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
       (mkEffect 0 [] []) m
     = CheckOk (with_fds (fd_insert (m_fds m) 3
                  (FdFile [102] (Z_to_bv 64 (2 ^ 63 - 1)))) m) []
  /\ check_syscall (mkInput 63 [3; 4096; 1; 0; 0; 0] (fun _ => None) wmem_readv_one)
       (mkEffect (errno_ret EINVAL) [] []) m
     = CheckReject.
Proof. repeat split; check_eq. Qed.

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
  let m := init_model [] 0 0 demo_sp demo_limit (demo_input [] hello_stdin) in
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
Proof. repeat split; check_eq. Qed.

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
  mkModel [(0, FdChannel 0); (3, FdFile [102] 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [104; 105])] None None None.

(** Channels are unseekable streams: -ESPIPE. *)

Example lseek_channel_espipe :
  check_syscall (mkInput 62 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ESPIPE) [] []) lseek_model
  = CheckOk lseek_model [].
Proof. check_eq. Qed.

(** The whence check precedes the fd's KIND, which is what makes an
    unseekable fd answer -EINVAL rather than -ESPIPE: [ksys_lseek] tests
    [whence <= SEEK_MAX] before calling [vfs_llseek].  Verified on a real
    pipe under qemu-riscv64: whence 42 is -EINVAL, whence 4 (SEEK_HOLE)
    is -ESPIPE. *)

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
     = CheckOk (with_fds (fd_insert (m_fds lseek_model) 3 (FdFile [102] 2))
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
  = CheckOk (with_fds (fd_insert (m_fds lseek_model) 3 (FdFile [102] 2))
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
       (mkEffect (errno_ret EBADF) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  /\ check_syscall (mkInput 29 [Z_to_bv 64 (2 ^ 31 + 1); TIOCGWINSZ; 4096; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  /\ check_syscall (mkInput 29 [1; Z_to_bv 64 (2 ^ 31 + 21523); 4096; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ENOTTY) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
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
   rejecting would fail these examples rather than pass them.  Three of
   the four discriminate further, and would flip to [CheckOk] if an arm
   for the limitation were added; [write_channel_epipe_rejected] is the
   exception and says so at its own docstring.
   ------------------------------------------------------------------------- *)

(** -EINTR on a read.  read(0, buf, 1) with one byte of input delivers
    it; no model state admits the -EINTR a caught signal produces on a
    blocking read. *)

Example read_channel_eintr_rejected :
  check_syscall (mkInput 63 [0; 4096; 1; 0; 0; 0] (fun _ => None) wmem_readv_one)
    (mkEffect 1 [(4096, [120])] [])
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] (ICons 120 IEof)))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [ReadEv 0 120]
  /\ check_syscall (mkInput 63 [0; 4096; 1; 0; 0; 0] (fun _ => None) wmem_readv_one)
       (mkEffect (errno_ret EINTR) [] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] (ICons 120 IEof)))
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
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
      [WriteEv 1 97; WriteEv 1 98]
  /\ check_syscall (mkInput 64 [1; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
       (mkEffect (errno_ret EINTR) [] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = CheckReject.
Proof. split; check_eq. Qed.

(** -EPIPE on a channel write.  This rejection is the RIGHT answer for a
    process that installs no handler — SIGPIPE kills it before the errno
    is returned — and the defect is the other direction: the short write
    in the first conjunct is admitted in a state where the reader has
    gone and Linux kills the process instead.  So unlike the other three
    this pair does NOT discriminate its own limitation: no model state
    can express "the reader has gone", so neither conjunct would move if
    it were fixed.  What it carries is that -EPIPE is not admitted here,
    which is what a premature arm would break. *)

Example write_channel_epipe_rejected :
  check_syscall (mkInput 64 [1; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
    (with_copyins [(4096, 1%nat)] (mkEffect 1 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [WriteEv 1 97]
  /\ check_syscall (mkInput 64 [1; 4096; 2; 0; 0; 0] mem_ab (fun _ => None))
       (mkEffect (errno_ret EPIPE) [] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
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
  | CheckOk m [] => fs_lookup (m_fs m) [102] = Some [97; 98]
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
    pread leaves [m_urandom] at the remainder past the delivered
    prefix, the same remainder a [read] of the same count would leave. *)
Lemma pread64_urandom_advances_the_stream : forall fd buf count pos i m eff m' evs,
  fd_lookup (m_fds m) fd = Some FdUrandom ->
  pread64_spec fd buf count pos i m (Ok eff m' evs) ->
  m_urandom m' = m_urandom m
  \/ m_urandom m' = snd (stream_take_z (m_urandom m) (rw_count_clamp count)).
Proof.
  intros fd buf count pos i m eff m' evs Hfd H.
  apply check_pread64_complete_ok in H. unfold check_pread64, check_read_urandom in H.
  rewrite Hfd in H. cbv beta iota zeta in H.
  repeat (match type of H with
          | (if ?b then _ else _) = _ => destruct b
          | (match ?x with _ => _ end) = _ => destruct x
          end; cbv beta iota zeta in H);
    try discriminate;
    try (apply check_ret_only_ok_iff in H; destruct H as (_ & -> & ->); now left);
    try (inversion H; subst; right; autorewrite with model; reflexivity).
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
      fs_lookup (m_fs m) [102] = Some [0; 0; 0; 0; 97; 98]
      /\ fd_lookup (m_fds m) 3 = Some (FdFileW [102] 0)
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
  | CheckOk m [] => fs_lookup (m_fs m) [102] = Some [97; 98]
  | _ => False
  end
  /\ check_syscall
       (mkInput 68 [3; 4096; Z_to_bv 64 (rw_bytes_max + 1); 0; 0; 0]
          mem_ab (fun _ => None))
       (with_copyins [(4096, 1%nat)] (mkEffect 1 [] []))
       readv_write_only_model
     = CheckReject.
Proof. split; [vm_compute; reflexivity|check_eq]. Qed.

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
    as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| ]|];
    cbv iota in H; try (now destruct (Hro _ _ _ H)).
  (* three kinds survive that: the APPEND arm, whose checker is
     [CheckUnmodeled] and so never equals a [CheckOk], and the two
     TRANSFERRING kinds -- the O_WRONLY and O_RDWR descriptions, which
     share one arm.  One script for both, run under [all:]
     rather than written twice. *)
  2: discriminate.
  (* /dev/urandom is read-only, so its pwrite is the bare -EBADF the
     [try] above already dismissed; and /dev/null, whose every answer is
     a bare return: the ledger is empty on every one of its arms *)
  3: { destruct wr; cbn [negb] in H; cbv iota in H;
       [ | now destruct (Hro _ _ _ H) ].
       destruct (negb (access_okb buf (bv_unsigned count))); cbv iota in H;
         [now destruct (Hro _ _ _ H)|].
       destruct (rw_pos_einvalb pos (bv_unsigned count)); cbv iota in H;
         now destruct (Hro _ _ _ H). }
  all: destruct (negb (access_okb buf (bv_unsigned count)));
       [now destruct (Hro _ _ _ H)|].
  all: destruct (rw_pos_einvalb pos (bv_unsigned count));
       [now destruct (Hro _ _ _ H)|].
  all: cbv zeta in H.
  all: destruct (negb (w_is0 count)
                 && Nat.eqb (length (write_source (in_mem i) buf count)) 0);
       [now destruct (Hro _ _ _ H)|].
  all: destruct (fs_lookup (m_fs m) p) as [data|]; [|discriminate].
  all: destruct (negb (modeled_file_gap data pos
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
       (mkVmMaps [] [] 0 0 demo_limit) IEof [] None None None).

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
