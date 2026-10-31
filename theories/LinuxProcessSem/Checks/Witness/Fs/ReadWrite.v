(** * LinuxProcessSem.Checks.Witness.Fs.ReadWrite — the read (63), write (64), pread64 (67), pwrite64 (68), writev (66), readv (65), lseek (62) witnesses, and their proofs

    Mirrors [Sys/Fs/ReadWrite.v], which answers to Linux
    [fs/read_write.c]: this file holds the witnesses for the syscalls
    defined there, and no others.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export
  Prelude Uaccess.

(** [ReadWrite.read_urandom]'s one outcome per branch: the delivery is
    computed, so the witness IS the delivery. *)
Definition read_urandom_witness (buf count : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  if w_is0 count then ret_outcome (Z_to_bv 64 0) m
  else
  match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
  | None => ret_outcome (errno_ret EFAULT) m
  | Some _ =>
      let r := stream_take_z (m_urandom m) (rw_count_clamp count) in
      if negb (Z.eqb (Z.of_nat (length (fst r))) (rw_count_clamp count))
      then Unmodeled
      else
      match read_bytes_map (in_wmem i) buf (len_word (fst r)) with
      | None => Unmodeled
      | Some _ => Ok (mkEffect (len_word (fst r)) [(buf, fst r)] []) (with_urandom (snd r) m) []
      end
  end.

Lemma read_urandom_witness_ok : forall buf count i m,
  read_urandom buf count i m i m (read_urandom_witness buf count i m).
Proof.
  intros. unfold read_urandom, read_urandom_witness. cbv zeta.
  destruct (w_is0 count); [apply pure_ok|].
  destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|];
    [|apply pure_ok].
  destruct (negb (Z.eqb (Z.of_nat (length (fst (stream_take_z (m_urandom m)
                                                  (rw_count_clamp count)))))
                        (rw_count_clamp count))); [apply unmodeled_intro|].
  destruct (read_bytes_map (in_wmem i) buf
              (len_word (fst (stream_take_z (m_urandom m) (rw_count_clamp count)))))
    as [wn|]; [|apply unmodeled_intro].
  eapply bind_step; [apply modify_ok|]. apply pure_ok.
Qed.

(** [ReadWrite.read_proc_spec]: the -EFAULT, the count gate's decline,
    and otherwise the EMPTY delivery (a 0 with nothing written), which
    the spec admits over a wholly writable range and over one with no
    writable byte at all; a partly writable range is the decline. *)
Definition read_proc_witness (buf count : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  if negb (access_okb buf (bv_unsigned count)) then ret_outcome (errno_ret EFAULT) m
  else if negb (modeled_rw_count count) then Unmodeled
  else match read_bytes_map (in_wmem i) buf count with
       | Some _ => ret_outcome (Z_to_bv 64 0) m
       | None =>
           match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
           | None => ret_outcome (Z_to_bv 64 0) m
           | Some _ => Unmodeled
           end
       end.

Lemma read_proc_witness_ok : forall buf count i m,
  read_proc_spec buf count i m (read_proc_witness buf count i m).
Proof.
  intros. unfold read_proc_spec, read_proc_witness.
  destruct (negb (access_okb buf (bv_unsigned count))); [apply pure_ok|].
  destruct (negb (modeled_rw_count count)); [apply unmodeled_intro|].
  eapply bind_step; [apply input_ok|]. cbv beta.
  destruct (read_bytes_map (in_wmem i) buf count) as [w|].
  - apply alt_r. eapply bind_step.
    { apply (choose_ok _ []). cbn. pose proof (bv_unsigned_in_range 64 count). lia. }
    apply pure_ok.
  - destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|];
      [apply unmodeled_intro | apply alt_r; apply pure_ok].
Qed.

Definition read_witness (fd buf count : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m
  | Some (FdChannel ch) =>
      if negb (w_is0 ch) then ret_outcome (errno_ret EBADF) m  (* write-only channel *)
      else if negb (access_okb buf (bv_unsigned count))
      then ret_outcome (errno_ret EFAULT) m   (* vfs_read's access_ok *)
      else if w_is0 count then ret_outcome (Z_to_bv 64 0) m
      else
        match m_stdin m with
        | IEof => ret_outcome (Z_to_bv 64 0) m   (* end of input: needs no writable buffer *)
        | ICons b s' =>
            match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
            | None => ret_outcome (errno_ret EFAULT) m  (* no byte can land: -EFAULT *)
            | Some _ =>
            match read_bytes_map (in_wmem i) buf
                    (len_word (fst (stream_take_z (m_stdin m) (rw_count_clamp count)))) with
            | None => Unmodeled                  (* partially writable destination *)
            | Some _ =>                          (* the one-byte delivery is always available *)
                Ok (mkEffect (Z_to_bv 64 1) [(buf, [b])] []) (with_stdin s' m)
                   [ReadEv ch b]
            end
            end
        end
  | Some FdDir =>
      if negb (access_okb buf (bv_unsigned count))
      then ret_outcome (errno_ret EFAULT) m  (* access_ok precedes the directory's .read *)
      else ret_outcome (errno_ret EISDIR) m  (* directory fd: -EISDIR *)
  | Some (FdFileW _ _) => ret_outcome (errno_ret EBADF) m  (* write-only file *)
  | Some (FdFileA _ _) => ret_outcome (errno_ret EBADF) m  (* append fd: also O_WRONLY *)
  | Some (FdFile p off) =>
      if negb (access_okb buf (bv_unsigned count))
      then ret_outcome (errno_ret EFAULT) m   (* vfs_read's access_ok *)
      else
      match fs_lookup (m_fs m) p with
      | None => Unmodeled
      | Some data =>
          let bs := file_read data off (Z_to_bv 64 (rw_count_clamp count)) in
          match read_bytes_map (in_wmem i) buf (len_word bs) with
          | None =>                            (* unwritable DELIVERED prefix: -EFAULT when not
                                                  even its first byte can land, else fail closed *)
              match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
              | None => ret_outcome (errno_ret EFAULT) m
              | Some _ => Unmodeled
              end
          | Some _ =>
              let k :=
                Ok (mkEffect (len_word bs) (delivered_writes buf bs) [])
                   (with_fds (fd_insert (m_fds m) fd
                                (FdFile p (off + len_word bs))) m)
                   [] in
              k
          end
      end
  | Some (FdSocket sk) =>
      if negb (modeled_rw_range buf count) then Unmodeled  (* see [ReadWrite.read_spec] *)
      else if w_is0 count then
        access_ok_zero_witness buf count m (ret_outcome (Z_to_bv 64 0) m)
          (* count = 0 short-circuits before the protocol *)
      else
      match sk with
      | SkConnected peer ch rx =>
          match rx with
          | NFin =>
              access_ok_zero_witness buf count m
                (ret_outcome (Z_to_bv 64 0) m)   (* the peer's FIN, taken in sequence *)
          | NRst =>
              access_ok_zero_witness buf count m
                (ret_outcome (errno_ret ECONNRESET)
                   (with_fds (fd_insert (m_fds m) fd (FdSocket (SkReset peer ch))) m))
          | NTimedOut =>
              access_ok_zero_witness buf count m
                (ret_outcome (errno_ret ETIMEDOUT)
                   (with_fds (fd_insert (m_fds m) fd (FdSocket (SkReset peer ch))) m))
          | NCons b rest =>
              if negb (access_okb buf (bv_unsigned count))
              then ret_outcome (errno_ret EFAULT) m  (* [vfs_read]'s [access_ok], named count *)
              else
              match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
              | None => ret_outcome (errno_ret EFAULT) m  (* no byte can land: -EFAULT *)
              | Some _ =>
              match read_bytes_map (in_wmem i) buf
                      (len_word (fst (net_take_z rx (rw_count_clamp count)))) with
              | None => Unmodeled                (* partially writable destination *)
              | Some _ =>                        (* the one-byte delivery is always available *)
                  Ok (mkEffect (Z_to_bv 64 1) [(buf, [b])] [])
                     (with_fds (fd_insert (m_fds m) fd
                                  (FdSocket (SkConnected peer ch rest))) m)
                     [ReadEv ch b]
              end
              end
          end
      | SkReset _ _ =>
          access_ok_zero_witness buf count m
            (ret_outcome (Z_to_bv 64 0) m)       (* the error was delivered once already *)
      | _ =>
          access_ok_zero_witness buf count m
            (ret_outcome (errno_ret ENOTCONN) m) (* fresh, bound or listening *)
      end
  | Some (FdFileRW p off) =>   (* the [FdFile] arm above, on the O_RDWR kind *)
      if negb (access_okb buf (bv_unsigned count))
      then ret_outcome (errno_ret EFAULT) m   (* vfs_read's access_ok *)
      else
      match fs_lookup (m_fs m) p with
      | None => Unmodeled
      | Some data =>
          let bs := file_read data off (Z_to_bv 64 (rw_count_clamp count)) in
          match read_bytes_map (in_wmem i) buf (len_word bs) with
          | None =>                            (* unwritable DELIVERED prefix: -EFAULT when not
                                                  even its first byte can land, else fail closed *)
              match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
              | None => ret_outcome (errno_ret EFAULT) m
              | Some _ => Unmodeled
              end
          | Some _ =>
              let k :=
                Ok (mkEffect (len_word bs) (delivered_writes buf bs) [])
                   (with_fds (fd_insert (m_fds m) fd
                                (FdFileRW p (off + len_word bs))) m)
                   [] in
              k
          end
      end
  | Some (FdDevNull rd _) =>
      if negb rd then ret_outcome (errno_ret EBADF) m
      else access_ok_zero_witness buf count m (ret_outcome (Z_to_bv 64 0) m)
  | Some FdUrandom =>
      if negb (access_okb buf (bv_unsigned count))
      then ret_outcome (errno_ret EFAULT) m
      else read_urandom_witness buf count i m
  | Some (FdOpaque (OProcFile _)) => read_proc_witness buf count i m
  | Some (FdOpaque (OProcPath _)) => Unmodeled
  | Some (FdOpaque (OEventFd _)) => Unmodeled
  | Some (FdPipe id w) =>
      if w then ret_outcome (errno_ret EBADF) m   (* write end: read is -EBADF *)
      else if negb (modeled_rw_range buf count) then Unmodeled
      else if w_is0 count then
        access_ok_zero_witness buf count m (ret_outcome (Z_to_bv 64 0) m)
      else
      match pipe_lookup (m_pipes m) id with
      | None => Unmodeled
      | Some ([], _) =>
          if pipe_end_live (m_fds m) id true then Unmodeled  (* would block *)
          else access_ok_zero_witness buf count m
                 (ret_outcome (Z_to_bv 64 0) m)               (* end of file *)
      | Some ((b :: bs0) as q, used) =>
          if negb (access_okb buf (bv_unsigned count))
          then ret_outcome (errno_ret EFAULT) m      (* [vfs_read]'s [access_ok], named count *)
          else
          let del := pipe_take q (rw_count_clamp count) in
          match read_bytes_map (in_wmem i) buf (len_word del) with
          | None =>
              match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
              | None => ret_outcome (errno_ret EFAULT) m
              | Some _ => Unmodeled
              end
          | Some _ =>
              Ok (mkEffect (len_word del) (delivered_writes buf del) [])
                 (with_pipes (pipe_insert (m_pipes m) id
                                (pipe_consume (q, used) (length del))) m)
                 []
          end
      end
  end.

Lemma read_witness_ok : forall fd buf count i m,
  read_spec fd buf count i m (read_witness fd buf count i m).
Proof.
  intros. unfold read_spec, read_witness.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |o]|] eqn:Hfd.
  9:{ (* /dev/null *)
      eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
      srw Hfd. destruct rd; cbn [negb]; cbv beta iota; [|apply pure_ok].
      unfold access_ok_zero, access_ok_zero_witness.
      destruct (access_okb buf (bv_unsigned count)); apply pure_ok. }
  9:{ (* /dev/urandom *)
      eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
      srw Hfd. destruct (negb (access_okb buf (bv_unsigned count)));
        cbv beta iota; [apply pure_ok | apply read_urandom_witness_ok]. }
  9:{ (* the opaque kinds: a /proc/sys file reads, the other two decline *)
      eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
      srw Hfd. destruct o as [q|q|fl]; cbv beta iota;
        [apply unmodeled_intro | apply read_proc_witness_ok | apply unmodeled_intro]. }
  - (* channel *)
    destruct (negb (w_is0 ch)) eqn:Hm.
    { eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|].
      cbv beta iota; srw Hfd; srw Hm. apply pure_ok. }
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn.
    { eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|].
      cbv beta iota; srw Hfd; srw Hm. apply pure_ok. }
    destruct (w_is0 count) eqn:Hc.
    + eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|].
      cbv beta iota; srw Hfd; srw Hm. apply pure_ok.
    + destruct (m_stdin m) as [|b s'] eqn:He.
      * eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|].
        cbv beta iota; srw Hfd; srw Hm; srw He. apply pure_ok.
      * destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1.
        -- destruct (read_bytes_map (in_wmem i) buf
                       (len_word (fst (stream_take_z (ICons b s') (rw_count_clamp count)))))
             as [wn|] eqn:Hwn.
           2:{ eapply bind_step; [apply input_ok|]. cbv beta.
               eapply bind_step; [apply get_model_ok|].
               cbv beta iota; srw Hfd; srw Hm; srw He; srw Hw1; srw Hwn.
               apply unmodeled_intro. }
           eapply bind_step; [apply input_ok|]. cbv beta.
           eapply bind_step; [apply get_model_ok|].
           cbv beta iota; srw Hfd; srw Hm; srw He; srw Hw1; srw Hwn.
           eapply bind_step.
           { apply (choose_ok _ [b]). cbv beta. cbn [length stream_take fst].
             assert (Hc' : bv_unsigned count <> 0%Z).
             { unfold w_is0 in Hc. intro Hz.
               apply Bool.not_true_iff_false in Hc. apply Hc.
               apply bv_eqb_eq. apply bv_eq. rewrite Hz. reflexivity. }
             pose proof (bv_unsigned_in_range 64 count) as Hr.
             unfold bv_modulus in Hr.
             unfold rw_count_clamp, MAX_RW_COUNT.
             repeat split; try lia; try reflexivity.
             change (len_word [b]) with (Z_to_bv 64 1). rewrite Hw1. discriminate. }
           cbv beta. cbn [length stream_take fst snd].
           eapply bind_step; [apply modify_ok|].
           change (map (ReadEv ch) [b]) with [ReadEv ch b].
           change (len_word [b]) with (Z_to_bv 64 1).
           apply emit_pure_ok.
        -- eapply bind_step; [apply input_ok|]. cbv beta.
           eapply bind_step; [apply get_model_ok|].
           cbv beta iota; srw Hfd; srw Hm; srw He; srw Hw1. apply pure_ok.
  - (* file *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn.
    { eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|].
      cbv beta iota; srw Hfd. apply pure_ok. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    + destruct (read_bytes_map (in_wmem i) buf
                  (len_word (file_read data off
                               (Z_to_bv 64 (rw_count_clamp count)))))
        as [ok|] eqn:Hw.
      * eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|].
        cbv beta iota zeta; srw Hfd; srw Hfs; srw Hw.
        eapply bind_step; [apply modify_ok|]. apply pure_ok.
      * destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1.
        -- eapply bind_step; [apply input_ok|]. cbv beta.
           eapply bind_step; [apply get_model_ok|].
           cbv beta iota zeta; srw Hfd; srw Hfs; srw Hw; srw Hw1.
           apply unmodeled_intro.
        -- eapply bind_step; [apply input_ok|]. cbv beta.
           eapply bind_step; [apply get_model_ok|].
           cbv beta iota zeta; srw Hfd; srw Hfs; srw Hw; srw Hw1. apply pure_ok.
    + eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; srw Hfs. apply unmodeled_intro.
  - (* write-only file fd: -EBADF *)
    eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd. apply pure_ok.
  - (* append fd: -EBADF for the same reason *)
    eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd. apply pure_ok.
  - (* the same file opened O_RDWR: the file bullet above *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn.
    { eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|].
      cbv beta iota; srw Hfd. apply pure_ok. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    + destruct (read_bytes_map (in_wmem i) buf
                  (len_word (file_read data off
                               (Z_to_bv 64 (rw_count_clamp count)))))
        as [ok|] eqn:Hw.
      * eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|].
        cbv beta iota zeta; srw Hfd; srw Hfs; srw Hw.
        eapply bind_step; [apply modify_ok|]. apply pure_ok.
      * destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1.
        -- eapply bind_step; [apply input_ok|]. cbv beta.
           eapply bind_step; [apply get_model_ok|].
           cbv beta iota zeta; srw Hfd; srw Hfs; srw Hw; srw Hw1.
           apply unmodeled_intro.
        -- eapply bind_step; [apply input_ok|]. cbv beta.
           eapply bind_step; [apply get_model_ok|].
           cbv beta iota zeta; srw Hfd; srw Hfs; srw Hw; srw Hw1. apply pure_ok.
    + eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; srw Hfs. apply unmodeled_intro.
  - (* directory fd: -EFAULT past TASK_SIZE, else -EISDIR *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn;
      (eapply bind_step; [apply input_ok|]); cbv beta;
      (eapply bind_step; [apply get_model_ok|]);
      cbv beta iota zeta; srw Hfd; apply pure_ok.
  - (* socket *)
    destruct (negb (modeled_rw_range buf count)) eqn:Hn.
    { eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd. apply unmodeled_intro. }
    destruct (w_is0 count) eqn:Hc.
    { eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd.
      unfold access_ok_zero, access_ok_zero_witness.
      destruct (access_okb buf (bv_unsigned count)); apply pure_ok. }
    destruct sk as [| | |peer ch rx|peer ch].
    + (* fresh: -ENOTCONN, behind the range verdict *)
      eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd.
      unfold access_ok_zero, access_ok_zero_witness.
      destruct (access_okb buf (bv_unsigned count)); apply pure_ok.
    + (* bound: same *)
      eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd.
      unfold access_ok_zero, access_ok_zero_witness.
      destruct (access_okb buf (bv_unsigned count)); apply pure_ok.
    + (* listening: same *)
      eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd.
      unfold access_ok_zero, access_ok_zero_witness.
      destruct (access_okb buf (bv_unsigned count)); apply pure_ok.
    + destruct rx as [| | |b rest].
      * (* the peer's FIN: 0, behind the range verdict *)
        eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|].
        cbv beta iota zeta; srw Hfd.
        unfold access_ok_zero, access_ok_zero_witness.
        destruct (access_okb buf (bv_unsigned count)); apply pure_ok.
      * (* a pending reset, consumed by this read *)
        eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|].
        cbv beta iota zeta; srw Hfd.
        unfold socket_pending_error, access_ok_zero, access_ok_zero_witness.
        destruct (access_okb buf (bv_unsigned count)).
        { eapply bind_step; [apply modify_ok|]. apply pure_ok. }
        apply pure_ok.
      * (* a pending timeout: the same shape *)
        eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|].
        cbv beta iota zeta; srw Hfd.
        unfold socket_pending_error, access_ok_zero, access_ok_zero_witness.
        destruct (access_okb buf (bv_unsigned count)).
        { eapply bind_step; [apply modify_ok|]. apply pure_ok. }
        apply pure_ok.
      * (* a queued byte: the one-byte delivery *)
        destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak.
        { (* [vfs_read]'s [access_ok] refuses the named range: -EFAULT *)
          eapply bind_step; [apply input_ok|]. cbv beta.
          eapply bind_step; [apply get_model_ok|].
          cbv beta iota zeta; srw Hfd. apply pure_ok. }
        destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1.
        -- destruct (read_bytes_map (in_wmem i) buf
                       (len_word (fst (net_take_z (NCons b rest) (rw_count_clamp count)))))
             as [wn|] eqn:Hwn.
           2:{ eapply bind_step; [apply input_ok|]. cbv beta.
               eapply bind_step; [apply get_model_ok|].
               cbv beta iota zeta; srw Hfd; srw Hw1; srw Hwn.
               apply unmodeled_intro. }
           eapply bind_step; [apply input_ok|]. cbv beta.
           eapply bind_step; [apply get_model_ok|].
           cbv beta iota zeta; srw Hfd; srw Hw1; srw Hwn.
           eapply bind_step.
           { apply (choose_ok _ [b]). cbv beta. cbn [length net_take fst].
             assert (Hc' : bv_unsigned count <> 0%Z).
             { unfold w_is0 in Hc. intro Hz.
               apply Bool.not_true_iff_false in Hc. apply Hc.
               apply bv_eqb_eq. apply bv_eq. rewrite Hz. reflexivity. }
             pose proof (bv_unsigned_in_range 64 count) as Hr.
             unfold bv_modulus in Hr.
             unfold rw_count_clamp, MAX_RW_COUNT.
             repeat split; try lia; try reflexivity.
             change (len_word [b]) with (Z_to_bv 64 1). rewrite Hw1. discriminate. }
           cbv beta. cbn [length net_take fst snd].
           eapply bind_step; [apply modify_ok|].
           change (map (ReadEv ch) [b]) with [ReadEv ch b].
           change (len_word [b]) with (Z_to_bv 64 1).
           apply emit_pure_ok.
        -- eapply bind_step; [apply input_ok|]. cbv beta.
           eapply bind_step; [apply get_model_ok|].
           cbv beta iota zeta; srw Hfd; srw Hw1. apply pure_ok.
    + (* the error already delivered: reads as end of stream *)
      eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd.
      unfold access_ok_zero, access_ok_zero_witness.
      destruct (access_okb buf (bv_unsigned count)); apply pure_ok.
  - (* pipe: -EBADF on the write end, else the queue's head or its
       end-of-file / would-block verdict *)
    destruct w.
    { eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd. apply pure_ok. }
    destruct (negb (modeled_rw_range buf count)) eqn:Hn.
    { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; rewrite ?Hn; cbv beta iota zeta.
      apply unmodeled_intro. }
    destruct (w_is0 count) eqn:Hc.
    { eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; rewrite ?Hn, ?Hc; cbv beta iota zeta.
      unfold access_ok_zero, access_ok_zero_witness.
      destruct (access_okb buf (bv_unsigned count)); apply pure_ok. }
    destruct (pipe_lookup (m_pipes m) id) as [[q used]|] eqn:Hp.
    2:{ eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
        eapply bind_unmodeled2; [apply get_model_ok|].
        cbv beta iota zeta; srw Hfd; rewrite ?Hn, ?Hc; cbv beta iota zeta;
          srw Hp. apply unmodeled_intro. }
    destruct q as [|b bs0].
    { destruct (pipe_end_live (m_fds m) id true) eqn:Hlv.
      { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
        eapply bind_unmodeled2; [apply get_model_ok|].
        cbv beta iota zeta; srw Hfd; rewrite ?Hn, ?Hc; cbv beta iota zeta;
          srw Hp; srw Hlv. apply unmodeled_intro. }
      eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; rewrite ?Hn, ?Hc; cbv beta iota zeta;
        srw Hp; srw Hlv.
      unfold access_ok_zero, access_ok_zero_witness.
      destruct (access_okb buf (bv_unsigned count)); apply pure_ok. }
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak.
    { (* [vfs_read]'s [access_ok] refuses the named range: -EFAULT *)
      eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; rewrite ?Hn, ?Hc; cbv beta iota zeta;
        srw Hp. apply pure_ok. }
    destruct (read_bytes_map (in_wmem i) buf
                (len_word (pipe_take (b :: bs0) (rw_count_clamp count)))) as [okw|]
      eqn:Hw.
    + eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; rewrite ?Hn, ?Hc; cbv beta iota zeta;
        srw Hp; srw Hw.
      eapply bind_step; [apply modify_ok|]. apply pure_ok.
    + destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1.
      * eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
        eapply bind_unmodeled2; [apply get_model_ok|].
        cbv beta iota zeta; srw Hfd; rewrite ?Hn, ?Hc; cbv beta iota zeta;
          srw Hp; srw Hw; srw Hw1. apply unmodeled_intro.
      * eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|].
        cbv beta iota zeta; srw Hfd; rewrite ?Hn, ?Hc; cbv beta iota zeta;
          srw Hp; srw Hw; srw Hw1. apply pure_ok.
  - eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd. apply pure_ok.
Qed.

(* =========================================================================
   write (64) — witness: the (deterministic) full write, or [Unmodeled]
   ========================================================================= *)

(** [ReadWrite.write_fault_extend] as a witness: the -EFAULT a
    positional file write answers when no source byte is readable, over
    the model it leaves behind -- the file extended to [off], the
    descriptor untouched -- and [Unmodeled] where the spec declines the
    hole.  [write], [writev] and [pwrite64] all exhibit through this. *)
Definition write_fault_extend_witness (m : Model) (p : path) (off : word)
    : outcome SyscallEffect :=
  match fs_lookup (m_fs m) p with
  | None => Unmodeled
  | Some data =>
      if negb (modeled_zero_fill (bv_unsigned off) data) then Unmodeled
      else ret_outcome (errno_ret EFAULT)
             (with_fs (fs_set (m_fs m) p (file_extend data off)) m)
  end.

Definition write_witness (fd buf count : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m
  | Some (FdChannel ch) =>
      if w_is0 ch then ret_outcome (errno_ret EBADF) m  (* stdin is read-only *)
      else
      if negb (modeled_rw_range buf count) then Unmodeled
        (* see [Uaccess.modeled_rw_range] *)
      else
      if w_is0 count then
        access_ok_zero_witness buf count m (ret_outcome (Z_to_bv 64 0) m)
          (* count = 0: return 0, but only once the range passes
             [access_ok] — see [Uaccess.access_ok_zero] *)
      else
      if negb (access_okb buf (bv_unsigned count))
      then ret_outcome (errno_ret EFAULT) m    (* [vfs_write]'s [access_ok], named count *)
      else
      if negb (m_channel_reader m)
      then ret_outcome (errno_ret EPIPE) (raise_sigpipe m)
        (* no reader on the far end, past [access_ok]: signal 13 -- see
           [ReadWrite.write_spec]'s channel arm *)
      else
      let bs := write_source (in_mem i) buf count in
      if Nat.eqb (length bs) 0
      then ret_outcome (errno_ret EFAULT) m    (* nothing readable: -EFAULT *)
      else outcome_copyins [(buf, length bs)]
             (Ok (mkEffect (len_word bs) [] []) m (map (WriteEv ch) bs))
             (* the full delivery *)
  | Some FdDir => ret_outcome (errno_ret EBADF) m   (* directory fd is O_RDONLY: -EBADF *)
  | Some (FdFile _ _) => ret_outcome (errno_ret EBADF) m  (* read-only file *)
  | Some (FdFileW p off) =>
      if negb (modeled_rw_range buf count) then Unmodeled
        (* see [Uaccess.modeled_rw_range] *)
      else
      if negb (access_okb buf (bv_unsigned count))
      then ret_outcome (errno_ret EFAULT) m    (* [vfs_write]'s [access_ok], named count *)
      else
      let bs := write_source (in_mem i) buf count in
      if negb (w_is0 count) && Nat.eqb (length bs) 0
      then write_fault_extend_witness m p off
        (* nothing readable: -EFAULT, over the file that write still
           extends; see [ReadWrite.write_file_tail] *)
      else
        let k :=
          match fs_lookup (m_fs m) p with
          | None => Unmodeled
          | Some data =>
              if negb (modeled_file_gap data off bs) then Unmodeled
                (* a hole past end-of-file too large to zero-fill *)
              else
              let out :=
                Ok (mkEffect (len_word bs) [] [])
                  (with_fds (fd_insert (m_fds m) fd
                               (FdFileW p (off + len_word bs)))
                     (with_fs (fs_set (m_fs m) p (file_write data off bs)) m))
                  [] in
              if w_is0 count then out
              else outcome_copyins [(buf, length bs)] out
          end in
        if w_is0 count then access_ok_zero_witness buf count m k else k
  | Some (FdFileRW p off) =>   (* the [FdFileW] arm above, on the O_RDWR kind *)
      if negb (modeled_rw_range buf count) then Unmodeled
      else
      if negb (access_okb buf (bv_unsigned count))
      then ret_outcome (errno_ret EFAULT) m    (* [vfs_write]'s [access_ok], named count *)
      else
      let bs := write_source (in_mem i) buf count in
      if negb (w_is0 count) && Nat.eqb (length bs) 0
      then write_fault_extend_witness m p off
      else
        let k :=
          match fs_lookup (m_fs m) p with
          | None => Unmodeled
          | Some data =>
              if negb (modeled_file_gap data off bs) then Unmodeled
                (* a hole past end-of-file too large to zero-fill *)
              else
              let out :=
                Ok (mkEffect (len_word bs) [] [])
                  (with_fds (fd_insert (m_fds m) fd
                               (FdFileRW p (off + len_word bs)))
                     (with_fs (fs_set (m_fs m) p (file_write data off bs)) m))
                  [] in
              if w_is0 count then out
              else outcome_copyins [(buf, length bs)] out
          end in
        if w_is0 count then access_ok_zero_witness buf count m k else k
  | Some (FdFileA p off) =>
      if negb (modeled_rw_range buf count) then Unmodeled
        (* the [FdFileW] arm's gate; see [ReadWrite.write_spec]'s
           [FdFileA] arm for why it does not subsume the [access_ok] *)
      else if negb (access_okb buf (bv_unsigned count))
      then ret_outcome (errno_ret EFAULT) m           (* [vfs_write]'s [access_ok], first *)
      else if rw_pos_einvalb off (bv_unsigned count)
      then ret_outcome (errno_ret EINVAL) m           (* [rw_verify_area], on [f_pos] *)
      else
      let bs := write_source (in_mem i) buf count in
      if negb (w_is0 count) && Nat.eqb (length bs) 0
      then ret_outcome (errno_ret EFAULT) m    (* nothing readable: -EFAULT *)
      else
        let k :=
          match fs_lookup (m_fs m) p with
          | None => Unmodeled
          | Some data =>
              let out :=
                Ok (mkEffect (len_word bs) [] [])
                  (with_fds (fd_insert (m_fds m) fd
                               (FdFileA p (append_new_pos data bs off)))
                     (with_fs (fs_set (m_fs m) p
                                 (file_write data (len_word data) bs)) m))
                  [] in
              if w_is0 count then out
              else outcome_copyins [(buf, length bs)] out
          end in
        if w_is0 count then access_ok_zero_witness buf count m k else k
  | Some (FdSocket sk) =>
      if negb (sock_send_dead sk) then Unmodeled
        (* a delivering socket write is still unmodeled *)
      else
      if negb (modeled_rw_range buf count) then Unmodeled
      else
      if negb (access_okb buf (bv_unsigned count))
      then ret_outcome (errno_ret EFAULT) m
      else ret_outcome (errno_ret EPIPE) (raise_sigpipe m)
        (* no connection to send on: -EPIPE and SIGPIPE *)
  | Some FdUrandom => ret_outcome (errno_ret EBADF) m   (* read-only *)
  | Some (FdOpaque _) => Unmodeled
  | Some (FdDevNull _ wr) =>
      if negb wr then ret_outcome (errno_ret EBADF) m
      else if negb (modeled_rw_range buf count) then Unmodeled
      else access_ok_zero_witness buf count m
             (ret_outcome (Z_to_bv 64 (rw_count_clamp count)) m)
  | Some (FdPipe id w) =>
      if negb w then ret_outcome (errno_ret EBADF) m   (* read end: write is -EBADF *)
      else if negb (modeled_rw_range buf count) then Unmodeled
      else if w_is0 count then
        access_ok_zero_witness buf count m (ret_outcome (Z_to_bv 64 0) m)
      else if negb (access_okb buf (bv_unsigned count))
      then ret_outcome (errno_ret EFAULT) m    (* [vfs_write]'s [access_ok], before the readers test *)
      else if negb (pipe_end_live (m_fds m) id false)
      then ret_outcome (errno_ret EPIPE) (raise_sigpipe m)  (* SIGPIPE *)
      else
      match pipe_lookup (m_pipes m) id with
      | None => Unmodeled
      | Some st =>
          if negb (pipe_write_room st (bv_unsigned count)) then Unmodeled
          else
          let bs := write_source (in_mem i) buf count in
          if negb (Nat.eqb (length bs) (word_to_nat count)) then Unmodeled
          else outcome_copyins [(buf, length bs)]
                 (Ok (mkEffect count [] [])
                    (with_pipes (pipe_insert (m_pipes m) id (pipe_append st bs)) m)
                    [])
                 (* the whole source is read, so the range goes in the
                    copy-in ledger, exactly as the channel and file arms
                    record theirs *)
      end
  end.

Lemma write_witness_ok : forall fd buf count i m,
  write_spec fd buf count i m (write_witness fd buf count i m).
Proof.
  intros. unfold write_spec, write_range_gate, write_file_tail,
    write_fault_keep, write_ledger, write_witness.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |o]|] eqn:Hfd.
  9:{ (* /dev/null *)
      destruct wr; cbn [negb]; cbv beta iota.
      2:{ eapply bind_step; [apply input_ok|]. cbv beta.
          eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
          srw Hfd. cbn [negb]. cbv beta iota. apply pure_ok. }
      destruct (modeled_rw_range buf count) eqn:Hg; cbn [negb]; cbv beta iota.
      2:{ eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
          eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota zeta.
          srw Hfd. cbn [negb]. cbv beta iota. try rewrite Hg. cbn [negb].
          cbv beta iota. apply unmodeled_intro. }
      unfold access_ok_zero_witness.
      destruct (access_okb buf (bv_unsigned count)) eqn:Hok;
        (eapply bind_step; [apply input_ok|]); cbv beta;
        (eapply bind_step; [apply get_model_ok|]); cbv beta iota zeta;
        srw Hfd; cbn [negb]; cbv beta iota; try rewrite Hg; cbn [negb];
        cbv beta iota; unfold access_ok_zero; rewrite Hok; cbv beta iota;
        apply pure_ok. }
  9:{ (* /dev/urandom: -EBADF *)
      eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
      srw Hfd. apply pure_ok. }
  9:{ (* the opaque kinds: declined *)
      eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
      srw Hfd. apply unmodeled_intro. }
  - destruct (w_is0 ch) eqn:Hm.
    { eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; srw Hm. apply pure_ok. }
    destruct (negb (modeled_rw_range buf count)) eqn:Hn.
    { eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; srw Hm. apply unmodeled_intro. }
    destruct (w_is0 count) eqn:Hc.
    { eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; srw Hm.
      unfold access_ok_zero, access_ok_zero_witness.
      destruct (access_okb buf (bv_unsigned count)); apply pure_ok. }
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak.
    { (* [vfs_write]'s [access_ok] refuses the named range: -EFAULT *)
      eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; srw Hm. apply pure_ok. }
    destruct (negb (m_channel_reader m)) eqn:Hcr.
    { (* the far end has no reader, past [access_ok]: signal 13 *)
      eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; srw Hm; srw Hcr.
      unfold sigpipe_write.
      eapply bind_step; [apply modify_ok|]. apply pure_ok. }
    destruct (Nat.eqb (length (write_source (in_mem i) buf count)) 0)
      eqn:Hg.
    + eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; srw Hm; srw Hcr; srw Hg. apply pure_ok.
    + eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; srw Hm; srw Hcr; srw Hg.
      eapply bind_step.
      { apply (choose_ok _ (write_source (in_mem i) buf count)).
        repeat split.
        - apply Nat.eqb_neq in Hg. lia.
        - apply write_source_length_le.
        - now rewrite firstn_all. }
      eapply witness_bind_ok_eq with
        (evs1 := map (WriteEv ch) (write_source (in_mem i) buf count))
        (evs2 := []); [apply emit_ok| |now rewrite app_nil_r].
      unfold record_copyins. eapply bind_step; [apply pure_ok|]. apply pure_ok.
  - (* read-only file fd: -EBADF *)
    eapply bind_step; [apply input_ok|].
    cbv beta. eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd. apply pure_ok.
  - destruct (negb (modeled_rw_range buf count)) eqn:Hn.
    { eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd. apply unmodeled_intro. }
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak.
    { (* [vfs_write]'s [access_ok] refuses the named range: -EFAULT *)
      eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd. apply pure_ok. }
    destruct (negb (w_is0 count)
              && Nat.eqb (length (write_source (in_mem i) buf count)) 0)
      eqn:Hg.
    + (* the faulting source: -EFAULT over the file it still extends *)
      unfold write_fault_extend_witness.
      eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; srw Hg. unfold write_fault_extend.
      destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
        [ destruct (negb (modeled_zero_fill (bv_unsigned off) data)) eqn:Hz;
          [ apply unmodeled_intro
          | eapply bind_step; [apply modify_ok|]; apply pure_ok ]
        | apply unmodeled_intro ].
    + eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; srw Hg.
      (* [count = 0] adds the range verdict in front of the same file
         analysis; both branches end in it, so it is proved twice *)
      destruct (w_is0 count) eqn:Hc;
        [ unfold access_ok_zero, access_ok_zero_witness;
          destruct (access_okb buf (bv_unsigned count)); [ | apply pure_ok ]
        | ].
      all: (destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
            [ destruct (negb (modeled_file_gap data off
                                (write_source (in_mem i) buf count))) eqn:Hk;
              [ apply unmodeled_intro
              | eapply bind_step; [apply modify_ok|];
                eapply bind_step; [apply modify_ok|];
                first
                  [ apply pure_ok
                  | apply record_copyins_outcome; apply pure_ok ] ]
            | apply unmodeled_intro ]).
  - (* append fd: the arm above with the position fixed at end-of-file,
       so there is no zero-fill guard to discharge -- and with
       [rw_verify_area]'s -EINVAL kept on the fd's real position *)
    destruct (negb (modeled_rw_range buf count)) eqn:Hn.
    { eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd. apply unmodeled_intro. }
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak.
    { eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd. apply pure_ok. }
    destruct (rw_pos_einvalb off (bv_unsigned count)) eqn:Hpos.
    { eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; srw Hpos. apply pure_ok. }
    destruct (negb (w_is0 count)
              && Nat.eqb (length (write_source (in_mem i) buf count)) 0)
      eqn:Hg.
    + eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; srw Hpos; srw Hg. apply pure_ok.
    + eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; srw Hpos; srw Hg.
      destruct (w_is0 count) eqn:Hc;
        [ unfold access_ok_zero, access_ok_zero_witness;
          destruct (access_okb buf (bv_unsigned count)); [ | apply pure_ok ]
        | ].
      all: (destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
            [ eapply bind_step; [apply modify_ok|];
              eapply bind_step; [apply modify_ok|];
              first
                [ apply pure_ok
                | apply record_copyins_outcome; apply pure_ok ]
            | apply unmodeled_intro ]).
  - (* the same file opened O_RDWR: the write-only bullet above *)
    destruct (negb (modeled_rw_range buf count)) eqn:Hn.
    { eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd. apply unmodeled_intro. }
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak.
    { (* [vfs_write]'s [access_ok] refuses the named range: -EFAULT *)
      eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd. apply pure_ok. }
    destruct (negb (w_is0 count)
              && Nat.eqb (length (write_source (in_mem i) buf count)) 0)
      eqn:Hg.
    + (* the faulting source: the [FdFileW] branch above *)
      unfold write_fault_extend_witness.
      eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; srw Hg. unfold write_fault_extend.
      destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
        [ destruct (negb (modeled_zero_fill (bv_unsigned off) data)) eqn:Hz;
          [ apply unmodeled_intro
          | eapply bind_step; [apply modify_ok|]; apply pure_ok ]
        | apply unmodeled_intro ].
    + eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; srw Hg.
      (* [count = 0] adds the range verdict in front of the same file
         analysis; both branches end in it, so it is proved twice *)
      destruct (w_is0 count) eqn:Hc;
        [ unfold access_ok_zero, access_ok_zero_witness;
          destruct (access_okb buf (bv_unsigned count)); [ | apply pure_ok ]
        | ].
      all: (destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
            [ destruct (negb (modeled_file_gap data off
                                (write_source (in_mem i) buf count))) eqn:Hk;
              [ apply unmodeled_intro
              | eapply bind_step; [apply modify_ok|];
                eapply bind_step; [apply modify_ok|];
                first
                  [ apply pure_ok
                  | apply record_copyins_outcome; apply pure_ok ] ]
            | apply unmodeled_intro ]).
  - (* directory fd: -EBADF *)
    eapply bind_step; [apply input_ok|].
    cbv beta. eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd. apply pure_ok.
  - (* socket: a delivering write is still unmodeled; a socket with no
       connection answers -EPIPE and raises signal 13 *)
    cbv beta iota.
    destruct (negb (sock_send_dead sk)) eqn:Hsd.
    { eapply bind_unmodeled2; [apply input_ok|].
      cbv beta. eapply bind_unmodeled2; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; srw Hsd. apply unmodeled_intro. }
    destruct (negb (modeled_rw_range buf count)) eqn:Hn.
    { eapply bind_unmodeled2; [apply input_ok|].
      cbv beta. eapply bind_unmodeled2; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; srw Hsd. apply unmodeled_intro. }
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hok;
      (eapply bind_step; [apply input_ok|]); cbv beta;
      (eapply bind_step; [apply get_model_ok|]);
      cbv beta iota zeta; srw Hfd; srw Hsd.
    + apply pure_ok.
    + unfold sigpipe_write.
      eapply bind_step; [apply modify_ok|]. apply pure_ok.
  - (* pipe: -EBADF on the read end, else the deterministic append, the
       no-reader -EPIPE with signal 13, or one of the three fail-closed
       verdicts *)
    destruct w.
    2:{ eapply bind_step; [apply input_ok|].
        cbv beta. eapply bind_step; [apply get_model_ok|].
        cbv beta iota zeta; srw Hfd. apply pure_ok. }
    destruct (negb (modeled_rw_range buf count)) eqn:Hn.
    { eapply bind_unmodeled2; [apply input_ok|].
      cbv beta. eapply bind_unmodeled2; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; rewrite ?Hn; cbv beta iota zeta.
      apply unmodeled_intro. }
    destruct (w_is0 count) eqn:Hc.
    { eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; rewrite ?Hn, ?Hc; cbv beta iota zeta.
      unfold access_ok_zero, access_ok_zero_witness.
      destruct (access_okb buf (bv_unsigned count)); apply pure_ok. }
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hak.
    { (* [vfs_write]'s [access_ok] refuses the named range: -EFAULT *)
      eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; rewrite ?Hn, ?Hc; cbv beta iota zeta.
      apply pure_ok. }
    destruct (negb (pipe_end_live (m_fds m) id false)) eqn:Hrd.
    { eapply bind_step; [apply input_ok|].
      cbv beta. eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; rewrite ?Hn, ?Hc; cbv beta iota zeta;
        srw Hrd.
      unfold sigpipe_write.
      eapply bind_step; [apply modify_ok|]. apply pure_ok. }
    destruct (pipe_lookup (m_pipes m) id) as [st|] eqn:Hp.
    2:{ eapply bind_unmodeled2; [apply input_ok|].
        cbv beta. eapply bind_unmodeled2; [apply get_model_ok|].
        cbv beta iota zeta; srw Hfd; rewrite ?Hn, ?Hc; cbv beta iota zeta;
          srw Hrd; srw Hp. apply unmodeled_intro. }
    destruct (negb (pipe_write_room st (bv_unsigned count))) eqn:Hroom.
    { eapply bind_unmodeled2; [apply input_ok|].
      cbv beta. eapply bind_unmodeled2; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; rewrite ?Hn, ?Hc; cbv beta iota zeta;
        srw Hrd; srw Hp; srw Hroom. apply unmodeled_intro. }
    destruct (negb (Nat.eqb (length (write_source (in_mem i) buf count))
                      (word_to_nat count))) eqn:Hsrc.
    { eapply bind_unmodeled2; [apply input_ok|].
      cbv beta. eapply bind_unmodeled2; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; rewrite ?Hn, ?Hc; cbv beta iota zeta;
        srw Hrd; srw Hp; srw Hroom; srw Hsrc. apply unmodeled_intro. }
    eapply bind_step; [apply input_ok|].
    cbv beta. eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd; rewrite ?Hn, ?Hc; cbv beta iota zeta;
      srw Hrd; srw Hp; srw Hroom; srw Hsrc.
    (* the delivery is the witness on both sides of the page the empty
       pipe's write must allocate: under [alt] it is the right one *)
    destruct (pipe_needs_page st) eqn:Hpg; cbv beta iota zeta;
      [apply alt_r|];
      (eapply bind_step; [apply modify_ok|];
       unfold record_copyins; eapply bind_step; [apply pure_ok|];
       apply pure_ok).
  - eapply bind_step; [apply input_ok|].
    cbv beta. eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd. apply pure_ok.
Qed.

(* =========================================================================
   writev (66) — witness: the (deterministic) gathered-prefix write, the
   iovcnt/EFAULT edge cases, or [Unmodeled]
   ========================================================================= *)

(** pread64 (67) and pwrite64 (68).  Neither spec is nondeterministic on
    any arm it answers — a positional transfer never reaches the channel,
    pipe or socket arms whose short deliveries are where [read_spec] and
    [write_spec] have a choice to make — so each witness is that spec's
    one outcome rather than a chosen representative. *)

Definition pread64_witness (fd buf count pos : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  if ppos_einvalb pos then ret_outcome (errno_ret EINVAL) m
  else
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m
  | Some (FdChannel _) => ret_outcome (errno_ret ESPIPE) m
  | Some (FdPipe _ _) => ret_outcome (errno_ret ESPIPE) m
  | Some (FdSocket _) => ret_outcome (errno_ret ESPIPE) m
  | Some (FdFileW _ _) => ret_outcome (errno_ret EBADF) m
  | Some (FdFileA _ _) => ret_outcome (errno_ret EBADF) m
  | Some (FdDevNull rd _) =>
      if negb rd then ret_outcome (errno_ret EBADF) m
      else if negb (access_okb buf (bv_unsigned count))
      then ret_outcome (errno_ret EFAULT) m
      else if rw_pos_einvalb pos (bv_unsigned count)
      then ret_outcome (errno_ret EINVAL) m
      else ret_outcome (Z_to_bv 64 0) m
  | Some (FdOpaque _) => Unmodeled
  | Some FdUrandom =>
      if negb (access_okb buf (bv_unsigned count))
      then ret_outcome (errno_ret EFAULT) m
      else if rw_pos_einvalb pos (bv_unsigned count)
      then ret_outcome (errno_ret EINVAL) m
      else read_urandom_witness buf count i m
  | Some FdDir =>
      if negb (access_okb buf (bv_unsigned count))
      then ret_outcome (errno_ret EFAULT) m
      else if rw_pos_einvalb pos (bv_unsigned count)
      then ret_outcome (errno_ret EINVAL) m
      else ret_outcome (errno_ret EISDIR) m
  | Some (FdFile p _) | Some (FdFileRW p _) =>
      if negb (access_okb buf (bv_unsigned count))
      then ret_outcome (errno_ret EFAULT) m
      else if rw_pos_einvalb pos (bv_unsigned count)
      then ret_outcome (errno_ret EINVAL) m
      else
      match fs_lookup (m_fs m) p with
      | None => Unmodeled
      | Some data =>
          let bs := file_read data pos (Z_to_bv 64 (rw_count_clamp count)) in
          match read_bytes_map (in_wmem i) buf (len_word bs) with
          | None =>
              match read_bytes_map (in_wmem i) buf (Z_to_bv 64 1) with
              | None => ret_outcome (errno_ret EFAULT) m
              | Some _ => Unmodeled
              end
          | Some _ =>
              Ok (mkEffect (len_word bs) (delivered_writes buf bs) []) m []
              (* the model is unchanged: a pread advances no offset *)
          end
      end
  end.

Lemma pread64_witness_ok : forall fd buf count pos i m,
  pread64_spec fd buf count pos i m (pread64_witness fd buf count pos i m).
Proof.
  intros. unfold pread64_spec, pread64_witness.
  destruct (ppos_einvalb pos) eqn:Hpos; [apply pure_ok|].
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |o]|] eqn:Hfd.
  9:{ (* /dev/null *)
    destruct rd; cbn [negb]; cbv beta iota;
      [ destruct (access_okb buf (bv_unsigned count)) eqn:Hok; cbn [negb];
        cbv beta iota;
        [ destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv | ] | ];
      (eapply bind_step; [apply input_ok|]); cbv beta;
      (eapply bind_step; [apply get_model_ok|]); cbv beta iota zeta;
      srw Hfd; cbn [negb]; cbv beta iota; try rewrite Hok; cbn [negb];
      cbv beta iota; try rewrite Hrv; cbv beta iota; apply pure_ok. }
  9:{ (* /dev/urandom *)
      eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
      srw Hfd.
      destruct (negb (access_okb buf (bv_unsigned count))); cbv beta iota;
        [apply pure_ok|].
      destruct (rw_pos_einvalb pos (bv_unsigned count)); cbv beta iota;
        [apply pure_ok|].
      apply read_urandom_witness_ok. }
  9:{ (* the opaque kinds: declined *)
      eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
      srw Hfd. apply unmodeled_intro. }
  - (* channel *)
    eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd. apply pure_ok.
  - (* readable file *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn.
    { eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd. apply pure_ok. }
    destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv.
    { eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd. apply pure_ok. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    2: { eapply bind_step; [apply input_ok|]. cbv beta.
         eapply bind_step; [apply get_model_ok|].
         cbv beta iota zeta; srw Hfd; srw Hfs. apply unmodeled_intro. }
    destruct (read_bytes_map (in_wmem i) buf
                (len_word (file_read data pos
                             (Z_to_bv 64 (rw_count_clamp count)))))
      as [ok|] eqn:Hw.
    + eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; srw Hfs; srw Hw. apply pure_ok.
    + destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1.
      * eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|].
        cbv beta iota zeta; srw Hfd; srw Hfs; srw Hw; srw Hw1.
        apply unmodeled_intro.
      * eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|].
        cbv beta iota zeta; srw Hfd; srw Hfs; srw Hw; srw Hw1. apply pure_ok.
  - (* write-only file fd *)
    eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd. apply pure_ok.
  - (* append fd: -EBADF for the same reason *)
    eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd. apply pure_ok.
  - (* the same file opened O_RDWR: the readable-file bullet above *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn.
    { eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd. apply pure_ok. }
    destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv.
    { eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd. apply pure_ok. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    2: { eapply bind_step; [apply input_ok|]. cbv beta.
         eapply bind_step; [apply get_model_ok|].
         cbv beta iota zeta; srw Hfd; srw Hfs. apply unmodeled_intro. }
    destruct (read_bytes_map (in_wmem i) buf
                (len_word (file_read data pos
                             (Z_to_bv 64 (rw_count_clamp count)))))
      as [ok|] eqn:Hw.
    + eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|].
      cbv beta iota zeta; srw Hfd; srw Hfs; srw Hw. apply pure_ok.
    + destruct (read_bytes_map (in_wmem i) buf (Z_to_bv 64 1)) as [w1|] eqn:Hw1.
      * eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|].
        cbv beta iota zeta; srw Hfd; srw Hfs; srw Hw; srw Hw1.
        apply unmodeled_intro.
      * eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|].
        cbv beta iota zeta; srw Hfd; srw Hfs; srw Hw; srw Hw1. apply pure_ok.
  - (* directory *)
    destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn;
      [ | destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv ];
      (eapply bind_step; [apply input_ok|]); cbv beta;
      (eapply bind_step; [apply get_model_ok|]);
      cbv beta iota zeta; srw Hfd; apply pure_ok.
  - (* socket *)
    eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd. apply pure_ok.
  - (* either pipe end *)
    eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd. apply pure_ok.
  - (* no such descriptor *)
    eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd. apply pure_ok.
Qed.

Definition pwrite64_witness (fd buf count pos : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  if ppos_einvalb pos then ret_outcome (errno_ret EINVAL) m
  else
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m
  | Some (FdChannel _) => ret_outcome (errno_ret ESPIPE) m
  | Some (FdPipe _ _) => ret_outcome (errno_ret ESPIPE) m
  | Some (FdSocket _) => ret_outcome (errno_ret ESPIPE) m
  | Some (FdFile _ _) => ret_outcome (errno_ret EBADF) m
  | Some FdDir => ret_outcome (errno_ret EBADF) m
  | Some (FdFileA _ _) => Unmodeled        (* see [ReadWrite.pwrite64_spec] *)
  | Some FdUrandom => ret_outcome (errno_ret EBADF) m   (* read-only *)
  | Some (FdOpaque _) => Unmodeled
  | Some (FdDevNull _ wr) =>
      if negb wr then ret_outcome (errno_ret EBADF) m
      else if negb (access_okb buf (bv_unsigned count))
      then ret_outcome (errno_ret EFAULT) m
      else if rw_pos_einvalb pos (bv_unsigned count)
      then ret_outcome (errno_ret EINVAL) m
      else ret_outcome (Z_to_bv 64 (rw_count_clamp count)) m
  | Some (FdFileW p _) | Some (FdFileRW p _) =>
      if negb (access_okb buf (bv_unsigned count))
      then ret_outcome (errno_ret EFAULT) m
      else if rw_pos_einvalb pos (bv_unsigned count)
      then ret_outcome (errno_ret EINVAL) m
      else
      let bs := write_source (in_mem i) buf count in
        (* no count gate: see [ReadWrite.pwrite64_spec] *)
      if negb (w_is0 count) && Nat.eqb (length bs) 0
      then write_fault_extend_witness m p pos
      else
      match fs_lookup (m_fs m) p with
      | None => Unmodeled
      | Some data =>
          if negb (modeled_file_gap data pos bs) then Unmodeled
          else
          let out :=
            Ok (mkEffect (len_word bs) [] [])
               (with_fs (fs_set (m_fs m) p (file_write data pos bs)) m) [] in
          if w_is0 count then out
          else outcome_copyins [(buf, length bs)] out
      end
  end.

Lemma pwrite64_witness_ok : forall fd buf count pos i m,
  pwrite64_spec fd buf count pos i m (pwrite64_witness fd buf count pos i m).
Proof.
  intros. unfold pwrite64_spec, pwrite64_witness.
  destruct (ppos_einvalb pos) eqn:Hpos; [apply pure_ok|].
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |o]|] eqn:Hfd;
    try (eapply bind_step; [apply input_ok|]; cbv beta;
         (eapply bind_step; [apply get_model_ok|]);
         cbv beta iota zeta; srw Hfd; apply pure_ok).
  (* Three goals survive that: the write-only file arm and the O_RDWR
     one, which both transfer, and the APPEND arm, which fails closed --
     see [ReadWrite.pwrite64_spec] for why an append fd is the one kind
     whose answer is not the write-only arm's.  The first two are ONE
     SCRIPT run twice: a positional write reads no [f_pos], so nothing
     on this path can tell the two kinds apart, which is exactly why
     the spec gives them one arm. *)
  5: { (* the opaque kinds: declined *)
       eapply bind_step; [apply input_ok|]. cbv beta.
       eapply bind_step; [apply get_model_ok|].
       cbv beta iota zeta; srw Hfd. apply unmodeled_intro. }
  2: { eapply bind_step; [apply input_ok|]. cbv beta.
       eapply bind_step; [apply get_model_ok|].
       cbv beta iota zeta; srw Hfd. apply unmodeled_intro. }
  1: {
  destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn.
  { eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd. apply pure_ok. }
  destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv.
  { eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd. apply pure_ok. }
  destruct (negb (w_is0 count)
            && Nat.eqb (length (write_source (in_mem i) buf count)) 0) eqn:Hg.
  { (* the faulting source: -EFAULT over the file it still extends *)
    unfold write_fault_extend_witness.
    eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd; srw Hg. unfold write_fault_extend.
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
      [ destruct (negb (modeled_zero_fill (bv_unsigned pos) data)) eqn:Hz;
        [ apply unmodeled_intro
        | eapply bind_step; [apply modify_ok|]; apply pure_ok ]
      | apply unmodeled_intro ]. }
  destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
  2: { eapply bind_step; [apply input_ok|]. cbv beta.
       eapply bind_step; [apply get_model_ok|].
       cbv beta iota zeta; srw Hfd; srw Hg; srw Hfs. apply unmodeled_intro. }
  destruct (negb (modeled_file_gap data pos
                    (write_source (in_mem i) buf count))) eqn:Hk.
  { eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd; srw Hg; srw Hfs; srw Hk. apply unmodeled_intro. }
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|].
  cbv beta iota zeta; srw Hfd; srw Hg; srw Hfs; srw Hk.
  eapply bind_step; [apply modify_ok|].
  destruct (w_is0 count).
  - apply pure_ok.
  - apply record_copyins_outcome. apply pure_ok.
  }
  destruct (negb (access_okb buf (bv_unsigned count))) eqn:Hn.
  { eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd. apply pure_ok. }
  destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv.
  { eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd. apply pure_ok. }
  destruct (negb (w_is0 count)
            && Nat.eqb (length (write_source (in_mem i) buf count)) 0) eqn:Hg.
  { (* the faulting source: the branch above, on the O_RDWR kind *)
    unfold write_fault_extend_witness.
    eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd; srw Hg. unfold write_fault_extend.
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
      [ destruct (negb (modeled_zero_fill (bv_unsigned pos) data)) eqn:Hz;
        [ apply unmodeled_intro
        | eapply bind_step; [apply modify_ok|]; apply pure_ok ]
      | apply unmodeled_intro ]. }
  destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
  2: { eapply bind_step; [apply input_ok|]. cbv beta.
       eapply bind_step; [apply get_model_ok|].
       cbv beta iota zeta; srw Hfd; srw Hg; srw Hfs. apply unmodeled_intro. }
  destruct (negb (modeled_file_gap data pos
                    (write_source (in_mem i) buf count))) eqn:Hk.
  { eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|].
    cbv beta iota zeta; srw Hfd; srw Hg; srw Hfs; srw Hk. apply unmodeled_intro. }
  eapply bind_step; [apply input_ok|]. cbv beta.
  eapply bind_step; [apply get_model_ok|].
  cbv beta iota zeta; srw Hfd; srw Hg; srw Hfs; srw Hk.
  eapply bind_step; [apply modify_ok|].
  destruct (w_is0 count).
  - apply pure_ok.
  - apply record_copyins_outcome. apply pure_ok.
  - (* /dev/null *)
    destruct wr; cbn [negb]; cbv beta iota;
      [ destruct (access_okb buf (bv_unsigned count)) eqn:Hok; cbn [negb];
        cbv beta iota;
        [ destruct (rw_pos_einvalb pos (bv_unsigned count)) eqn:Hrv | ] | ];
      (eapply bind_step; [apply input_ok|]); cbv beta;
      (eapply bind_step; [apply get_model_ok|]); cbv beta iota zeta;
      srw Hfd; cbn [negb]; cbv beta iota; try rewrite Hok; cbn [negb];
      cbv beta iota; try rewrite Hrv; cbv beta iota; apply pure_ok.
Qed.

Definition writev_witness (fd iov iovcnt : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m
  | Some (FdChannel ch) =>
      if w_is0 ch then ret_outcome (errno_ret EBADF) m  (* stdin is read-only *)
      else outcome_copyins
        (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
        (match import_iovecs (in_mem i) iov (iovcnt32 iovcnt) with
           | ImpFault => ret_outcome (errno_ret EFAULT) m
           | ImpInval => ret_outcome (errno_ret EINVAL) m
           | ImpOk iovs0 =>
               let total := iovs_total (cap_iovecs iovs0) in
               let bs := writev_gathered (in_mem i) iovs0 in
               if Z.eqb total 0 then ret_outcome (Z_to_bv 64 0) m   (* zero aggregate *)
               else if negb (m_channel_reader m)
               then ret_outcome (errno_ret EPIPE) (raise_sigpipe m)
                 (* no reader on the far end: -EPIPE and signal 13 *)
               else if Nat.eqb (length bs) 0
               then ret_outcome (errno_ret EFAULT) m   (* nothing gatherable *)
               else if addr_is_error_b (len_word bs) then Unmodeled
               else outcome_copyins
                      (iov_prefix_accesses (cap_iovecs iovs0)
                         (length (firstn 1 bs)))
                      (Ok (mkEffect (len_word (firstn 1 bs)) [] []) m
                        (map (WriteEv ch) (firstn 1 bs)))  (* the one-byte delivery *)
           end)
  | Some FdDir => ret_outcome (errno_ret EBADF) m   (* directory fd is O_RDONLY: -EBADF *)
  | Some (FdFile _ _) => ret_outcome (errno_ret EBADF) m  (* read-only file *)
  | Some (FdPipe _ w) =>
      if negb w then ret_outcome (errno_ret EBADF) m   (* read end: -EBADF *)
      else outcome_copyins
        (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
        (match import_iovecs (in_mem i) iov (iovcnt32 iovcnt) with
           | ImpFault => ret_outcome (errno_ret EFAULT) m
           | ImpInval => ret_outcome (errno_ret EINVAL) m
           | ImpOk iovs0 =>
               if Z.eqb (iovs_total (cap_iovecs iovs0)) 0
               then ret_outcome (Z_to_bv 64 0) m   (* zero aggregate: above the file kind *)
               else Unmodeled                      (* vectored pipe writes *)
           end)
  | Some FdUrandom => ret_outcome (errno_ret EBADF) m   (* read-only *)
  | Some (FdOpaque _) => Unmodeled
  | Some (FdDevNull _ wr) =>
      if negb wr then ret_outcome (errno_ret EBADF) m
      else outcome_copyins
        (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
        (match import_iovecs (in_mem i) iov (iovcnt32 iovcnt) with
           | ImpFault => ret_outcome (errno_ret EFAULT) m
           | ImpInval => ret_outcome (errno_ret EINVAL) m
           | ImpOk iovs0 =>
               ret_outcome (Z_to_bv 64 (iovs_total (cap_iovecs iovs0))) m
           end)
  | Some (FdFileW p off) =>
      outcome_copyins
        (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
        (match import_iovecs (in_mem i) iov (iovcnt32 iovcnt) with
           | ImpFault => ret_outcome (errno_ret EFAULT) m
           | ImpInval => ret_outcome (errno_ret EINVAL) m
           | ImpOk iovs0 =>
               let total := iovs_total (cap_iovecs iovs0) in
               let bs := writev_gathered (in_mem i) iovs0 in
               if Z.eqb total 0 then ret_outcome (Z_to_bv 64 0) m
               else if rw_pos_einvalb off total then ret_outcome (errno_ret EINVAL) m
               else if Nat.eqb (length bs) 0
               then write_fault_extend_witness m p off
               else
                 match fs_lookup (m_fs m) p with
                 | None => Unmodeled
                 | Some data =>
                     if negb (modeled_file_gap data off bs) then Unmodeled  (* hole too large *)
                     else
                     if addr_is_error_b (len_word bs) then Unmodeled
                     else outcome_copyins
                       (iov_prefix_accesses (cap_iovecs iovs0) (length bs))
                       (Ok (mkEffect (len_word bs) [] [])
                          (with_fds (fd_insert (m_fds m) fd
                                       (FdFileW p (off + len_word bs)))
                             (with_fs (fs_set (m_fs m) p (file_write data off bs)) m))
                          [])
                 end
           end)
  | Some (FdFileRW p off) =>   (* the [FdFileW] arm above, on the O_RDWR kind *)
      outcome_copyins
        (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
        (match import_iovecs (in_mem i) iov (iovcnt32 iovcnt) with
           | ImpFault => ret_outcome (errno_ret EFAULT) m
           | ImpInval => ret_outcome (errno_ret EINVAL) m
           | ImpOk iovs0 =>
               let total := iovs_total (cap_iovecs iovs0) in
               let bs := writev_gathered (in_mem i) iovs0 in
               if Z.eqb total 0 then ret_outcome (Z_to_bv 64 0) m
               else if rw_pos_einvalb off total then ret_outcome (errno_ret EINVAL) m
               else if Nat.eqb (length bs) 0
               then write_fault_extend_witness m p off
               else
                 match fs_lookup (m_fs m) p with
                 | None => Unmodeled
                 | Some data =>
                     if negb (modeled_file_gap data off bs) then Unmodeled  (* hole too large *)
                     else
                     if addr_is_error_b (len_word bs) then Unmodeled
                     else outcome_copyins
                       (iov_prefix_accesses (cap_iovecs iovs0) (length bs))
                       (Ok (mkEffect (len_word bs) [] [])
                          (with_fds (fd_insert (m_fds m) fd
                                       (FdFileRW p (off + len_word bs)))
                             (with_fs (fs_set (m_fs m) p (file_write data off bs)) m))
                          [])
                 end
           end)
  | Some (FdFileA p off) =>
      outcome_copyins
        (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
        (match import_iovecs (in_mem i) iov (iovcnt32 iovcnt) with
           | ImpFault => ret_outcome (errno_ret EFAULT) m
           | ImpInval => ret_outcome (errno_ret EINVAL) m
           | ImpOk iovs0 =>
               let total := iovs_total (cap_iovecs iovs0) in
               let bs := writev_gathered (in_mem i) iovs0 in
               if Z.eqb total 0 then ret_outcome (Z_to_bv 64 0) m
               else if rw_pos_einvalb off total then ret_outcome (errno_ret EINVAL) m
               else if Nat.eqb (length bs) 0
               then ret_outcome (errno_ret EFAULT) m
               else
                 match fs_lookup (m_fs m) p with
                 | None => Unmodeled
                 | Some data =>
                     if addr_is_error_b (len_word bs) then Unmodeled
                     else outcome_copyins
                       (iov_prefix_accesses (cap_iovecs iovs0) (length bs))
                       (Ok (mkEffect (len_word bs) [] [])
                          (with_fds (fd_insert (m_fds m) fd
                                       (FdFileA p (append_new_pos data bs off)))
                             (with_fs (fs_set (m_fs m) p
                                         (file_write data (len_word data) bs)) m))
                          [])
                 end
           end)
  | Some (FdSocket _) => Unmodeled
      (* writing a socket is unmodeled at every count — see
         [Sys.Fs.ReadWrite.writev_buf_gap] *)
  end.

Local Ltac wvw_open Hfd :=
  eapply bind_step; [apply input_ok|]; cbv beta;
  eapply bind_step; [apply get_model_ok|]; cbv beta iota zeta; srw Hfd.

Lemma writev_witness_ok : forall fd iov iovcnt i m,
  writev_spec fd iov iovcnt i m (writev_witness fd iov iovcnt i m).
Proof.
  intros. unfold writev_witness, writev_spec, writev_file_arm,
    write_fault_keep, writev_ledger.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p off|p off|p off|p off| |sk|id w|rd wr| |o]|] eqn:Hfd.
  9:{ (* /dev/null *)
      destruct wr.
      2:{ wvw_open Hfd. apply pure_ok. }
      cbn [negb]. cbv iota.
      destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv;
        (wvw_open Hfd; srw Hiv; eapply bind_step; [apply pure_ok|apply pure_ok]). }
  9:{ (* /dev/urandom: -EBADF *) wvw_open Hfd. apply pure_ok. }
  9:{ (* the opaque kinds: declined *) wvw_open Hfd. apply unmodeled_intro. }
  - destruct (w_is0 ch) eqn:Hm.
    { wvw_open Hfd. srw Hm. apply pure_ok. }
    destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv.
    2:{ wvw_open Hfd. srw Hm. srw Hiv. eapply bind_step; [apply pure_ok|apply pure_ok]. }
    2:{ wvw_open Hfd. srw Hm. srw Hiv. eapply bind_step; [apply pure_ok|apply pure_ok]. }
    unfold writev_gathered. cbv zeta.
    destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Htot.
    { wvw_open Hfd. srw Hm. srw Hiv. srw Htot.
      eapply bind_step; [apply pure_ok|apply pure_ok]. }
    destruct (negb (m_channel_reader m)) eqn:Hrdr.
    { (* no reader on the far end: -EPIPE and signal 13 *)
      wvw_open Hfd. srw Hm. srw Hiv. srw Htot. srw Hrdr.
      eapply bind_step;
        [ unfold sigpipe_write; eapply bind_step; [apply modify_ok | apply pure_ok]
        | apply pure_ok ]. }
    destruct (Nat.eqb (length (gather_prefix (in_mem i) (cap_iovecs iovs))) 0) eqn:Ht.
    { wvw_open Hfd. srw Hm. srw Hiv. srw Htot. srw Hrdr. srw Ht.
      eapply bind_step; [apply pure_ok|apply pure_ok]. }
    destruct (addr_is_error_b (len_word (gather_prefix (in_mem i) (cap_iovecs iovs))))
      eqn:Hae.
    { wvw_open Hfd. srw Hm. srw Hiv. srw Htot. srw Hrdr. srw Ht. srw Hae.
      left. unfold writev_buf_gap. apply unmodeled_intro. }
    wvw_open Hfd. srw Hm. srw Hiv. srw Htot. srw Hrdr. srw Ht. srw Hae.
    eapply witness_bind_ok_eq with
      (evs1 := map (WriteEv ch)
                 (firstn 1 (gather_prefix (in_mem i) (cap_iovecs iovs))))
      (evs2 := []); [|apply pure_ok|now rewrite app_nil_r].
    eapply bind_step.
    { apply (choose_ok _ (firstn 1 (gather_prefix (in_mem i) (cap_iovecs iovs)))).
      assert (Hl1 : length (firstn 1 (gather_prefix (in_mem i) (cap_iovecs iovs)))
                      = 1%nat).
      { rewrite length_firstn. apply Nat.eqb_neq in Ht. lia. }
      repeat split.
      - rewrite Hl1. lia.
      - rewrite Hl1. unfold two_pow_64. lia.
      - unfold len_word. rewrite Hl1. vm_compute. reflexivity.
      - rewrite Hl1. reflexivity. }
    eapply witness_bind_ok_eq with
      (evs1 := map (WriteEv ch)
                 (firstn 1 (gather_prefix (in_mem i) (cap_iovecs iovs))))
      (evs2 := []); [apply emit_ok| |now rewrite app_nil_r].
    unfold record_copyins. eapply bind_step; [apply pure_ok|apply pure_ok].
  - (* read-only file fd: -EBADF *)
    wvw_open Hfd. apply pure_ok.
  - destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv.
    2:{ wvw_open Hfd. srw Hiv. eapply bind_step; [apply pure_ok|apply pure_ok]. }
    2:{ wvw_open Hfd. srw Hiv. eapply bind_step; [apply pure_ok|apply pure_ok]. }
    unfold writev_gathered. cbv zeta.
    destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Htot.
    { wvw_open Hfd. srw Hiv. srw Htot.
      eapply bind_step; [apply pure_ok|apply pure_ok]. }
    destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs))) eqn:Hpos.
    { wvw_open Hfd. srw Hiv. srw Htot. srw Hpos.
      eapply bind_step; [apply pure_ok|apply pure_ok]. }
    destruct (Nat.eqb (length (gather_prefix (in_mem i) (cap_iovecs iovs))) 0) eqn:Ht.
    { (* the faulting source: -EFAULT over the file it still extends *)
      unfold write_fault_extend_witness.
      wvw_open Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht.
      unfold write_fault_extend.
      destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
        [ destruct (negb (modeled_zero_fill (bv_unsigned off) data)) eqn:Hz;
          [ left; apply unmodeled_intro
          | eapply bind_step;
            [ eapply bind_step; [apply modify_ok|]; apply pure_ok
            | apply pure_ok ] ]
        | left; apply unmodeled_intro ]. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    2:{ wvw_open Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht. srw Hfs.
        left. unfold writev_buf_gap. apply unmodeled_intro. }
    destruct (negb (modeled_file_gap data off
                      (gather_prefix (in_mem i) (cap_iovecs iovs)))) eqn:Hk.
    { wvw_open Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht. srw Hfs. srw Hk.
      left. unfold writev_buf_gap. apply unmodeled_intro. }
    destruct (addr_is_error_b (len_word (gather_prefix (in_mem i) (cap_iovecs iovs))))
      eqn:Hae.
    { wvw_open Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht. srw Hfs. srw Hk. srw Hae.
      left. unfold writev_buf_gap. apply unmodeled_intro. }
    wvw_open Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht. srw Hfs. srw Hk. srw Hae.
    eapply bind_step; [|apply pure_ok].
    eapply bind_step; [apply modify_ok|].
    eapply bind_step; [apply modify_ok|].
    unfold record_copyins. eapply bind_step; [apply pure_ok|apply pure_ok].
  - (* append fd: the arm above, minus the zero-fill guard, with the
       write landing at [len_word data] *)
    destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv.
    2:{ wvw_open Hfd. srw Hiv. eapply bind_step; [apply pure_ok|apply pure_ok]. }
    2:{ wvw_open Hfd. srw Hiv. eapply bind_step; [apply pure_ok|apply pure_ok]. }
    unfold writev_gathered. cbv zeta.
    destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Htot.
    { wvw_open Hfd. srw Hiv. srw Htot.
      eapply bind_step; [apply pure_ok|apply pure_ok]. }
    destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs))) eqn:Hpos.
    { wvw_open Hfd. srw Hiv. srw Htot. srw Hpos.
      eapply bind_step; [apply pure_ok|apply pure_ok]. }
    destruct (Nat.eqb (length (gather_prefix (in_mem i) (cap_iovecs iovs))) 0) eqn:Ht.
    { wvw_open Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht.
      eapply bind_step; [apply pure_ok|apply pure_ok]. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    2:{ wvw_open Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht. srw Hfs.
        left. unfold writev_buf_gap. apply unmodeled_intro. }
    destruct (addr_is_error_b (len_word (gather_prefix (in_mem i) (cap_iovecs iovs))))
      eqn:Hae.
    { wvw_open Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht. srw Hfs. srw Hae.
      left. unfold writev_buf_gap. apply unmodeled_intro. }
    wvw_open Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht. srw Hfs. srw Hae.
    eapply bind_step; [|apply pure_ok].
    eapply bind_step; [apply modify_ok|].
    eapply bind_step; [apply modify_ok|].
    unfold record_copyins. eapply bind_step; [apply pure_ok|apply pure_ok].
  - (* the same file opened O_RDWR: the write-only bullet above *)
    destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv.
    2:{ wvw_open Hfd. srw Hiv. eapply bind_step; [apply pure_ok|apply pure_ok]. }
    2:{ wvw_open Hfd. srw Hiv. eapply bind_step; [apply pure_ok|apply pure_ok]. }
    unfold writev_gathered. cbv zeta.
    destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Htot.
    { wvw_open Hfd. srw Hiv. srw Htot.
      eapply bind_step; [apply pure_ok|apply pure_ok]. }
    destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs))) eqn:Hpos.
    { wvw_open Hfd. srw Hiv. srw Htot. srw Hpos.
      eapply bind_step; [apply pure_ok|apply pure_ok]. }
    destruct (Nat.eqb (length (gather_prefix (in_mem i) (cap_iovecs iovs))) 0) eqn:Ht.
    { (* the faulting source: the [FdFileW] bullet above *)
      unfold write_fault_extend_witness.
      wvw_open Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht.
      unfold write_fault_extend.
      destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs;
        [ destruct (negb (modeled_zero_fill (bv_unsigned off) data)) eqn:Hz;
          [ left; apply unmodeled_intro
          | eapply bind_step;
            [ eapply bind_step; [apply modify_ok|]; apply pure_ok
            | apply pure_ok ] ]
        | left; apply unmodeled_intro ]. }
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    2:{ wvw_open Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht. srw Hfs.
        left. unfold writev_buf_gap. apply unmodeled_intro. }
    destruct (negb (modeled_file_gap data off
                      (gather_prefix (in_mem i) (cap_iovecs iovs)))) eqn:Hk.
    { wvw_open Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht. srw Hfs. srw Hk.
      left. unfold writev_buf_gap. apply unmodeled_intro. }
    destruct (addr_is_error_b (len_word (gather_prefix (in_mem i) (cap_iovecs iovs))))
      eqn:Hae.
    { wvw_open Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht. srw Hfs. srw Hk. srw Hae.
      left. unfold writev_buf_gap. apply unmodeled_intro. }
    wvw_open Hfd. srw Hiv. srw Htot. srw Hpos. srw Ht. srw Hfs. srw Hk. srw Hae.
    eapply bind_step; [|apply pure_ok].
    eapply bind_step; [apply modify_ok|].
    eapply bind_step; [apply modify_ok|].
    unfold record_copyins. eapply bind_step; [apply pure_ok|apply pure_ok].
  - (* directory fd: -EBADF *)
    wvw_open Hfd. apply pure_ok.
  - (* socket: the vectored gap declines *)
    wvw_open Hfd. unfold writev_buf_gap. apply unmodeled_intro.
  - (* pipe: -EBADF on the read end, 0 at a zero aggregate, else the
       fail-closed vectored gap *)
    destruct w.
    2:{ wvw_open Hfd. apply pure_ok. }
    cbn [negb]. cbv iota.
    destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs| |] eqn:Hiv.
    2:{ wvw_open Hfd. srw Hiv. eapply bind_step; [apply pure_ok|apply pure_ok]. }
    2:{ wvw_open Hfd. srw Hiv. eapply bind_step; [apply pure_ok|apply pure_ok]. }
    destruct (Z.eqb (iovs_total (cap_iovecs iovs)) 0) eqn:Htot.
    { wvw_open Hfd. srw Hiv. srw Htot. eapply bind_step; [apply pure_ok|apply pure_ok]. }
    wvw_open Hfd. srw Hiv. srw Htot.
    left. unfold writev_buf_gap. apply unmodeled_intro.
  - wvw_open Hfd. apply pure_ok.
Qed.

(* =========================================================================
   readv (65) — witness: a one-byte channel scatter, the deterministic
   file scatter, concrete argument/fd errors, or [Unmodeled]
   ========================================================================= *)

Definition readv_witness (fd iov iovcnt : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m
  | Some e =>
      match readable_fd e with
      | None => if fd_is_opaque e then Unmodeled else ret_outcome (errno_ret EBADF) m
          (* the read end has a [RdPipe]; only the O_WRONLY write end
             reaches this arm, where -EBADF is the kernel's own answer *)
      | Some r =>
          if readv_heap_iovecb iovcnt
          then Unmodeled
          else
          outcome_copyins
            (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
          (match import_iovecs (in_mem i) iov (iovcnt32 iovcnt) with
          | ImpFault => ret_outcome (errno_ret EFAULT) m
          | ImpInval => ret_outcome (errno_ret EINVAL) m
          | ImpOk iovs0 =>
              let iovs := cap_iovecs iovs0 in
              let total := iovs_total iovs in
              if Z.eqb total 0 then ret_outcome (Z_to_bv 64 0) m
              else
              match r with
              | RdChannel ch =>
                  match m_stdin m with
                  | IEof => ret_outcome (Z_to_bv 64 0) m
                  | ICons b s =>
                      match scatter_iovecs (in_wmem i) iovs [Z_to_bv 8 0] with
                      | None => ret_outcome (errno_ret EFAULT) m
                      | Some _ =>
                          match scatter_iovecs (in_wmem i) iovs
                                  (fst (stream_take_z (m_stdin m) total)) with
                          | None => Unmodeled   (* partially writable destination *)
                          | Some _ =>
                              match scatter_iovecs (in_wmem i) iovs [b] with
                              | None => Unmodeled
                                  (* unreachable: byte values do not affect
                                     writability, see scatter_iovecs_singleton_some *)
                              | Some writes =>
                                  Ok (mkEffect (Z_to_bv 64 1) writes [])
                                     (with_stdin s m) [ReadEv ch b]
                              end
                          end
                      end
                  end
              | RdPipe _ => Unmodeled   (* vectored pipe reads *)
              | RdDevNull => ret_outcome (Z_to_bv 64 0) m
              | RdUrandom => Unmodeled   (* vectored device reads decline *)
              | RdDir => ret_outcome (errno_ret EISDIR) m
              | RdSocket sk =>
                  match sk with
                  | SkConnected peer ch rx =>
                      match rx with
                      | NFin => ret_outcome (Z_to_bv 64 0) m
                      | NRst =>
                          ret_outcome (errno_ret ECONNRESET)
                            (with_fds (fd_insert (m_fds m) fd
                                         (FdSocket (SkReset peer ch))) m)
                      | NTimedOut =>
                          ret_outcome (errno_ret ETIMEDOUT)
                            (with_fds (fd_insert (m_fds m) fd
                                         (FdSocket (SkReset peer ch))) m)
                      | NCons b rest =>
                          match scatter_iovecs (in_wmem i) iovs [Z_to_bv 8 0] with
                          | None => ret_outcome (errno_ret EFAULT) m
                          | Some _ =>
                              match scatter_iovecs (in_wmem i) iovs
                                      (fst (net_take_z rx total)) with
                              | None => Unmodeled   (* partially writable destination *)
                              | Some _ =>
                                  match scatter_iovecs (in_wmem i) iovs [b] with
                                  | None => Unmodeled
                                      (* unreachable: byte values do not affect
                                         writability, see scatter_iovecs_singleton_some *)
                                  | Some writes =>
                                      Ok (mkEffect (Z_to_bv 64 1) writes [])
                                         (with_fds (fd_insert (m_fds m) fd
                                            (FdSocket (SkConnected peer ch rest))) m)
                                         [ReadEv ch b]
                                  end
                              end
                          end
                      end
                  | SkReset _ _ => ret_outcome (Z_to_bv 64 0) m
                  | _ => ret_outcome (errno_ret ENOTCONN) m
                  end
              | RdFile p off =>
                  match fs_lookup (m_fs m) p with
                  | None => Unmodeled
                  | Some data =>
                      if rw_pos_einvalb off total then ret_outcome (errno_ret EINVAL) m
                      else
                      let bs := file_read data off (Z_to_bv 64 total) in
                      match scatter_iovecs (in_wmem i) iovs bs with
                      | Some writes =>
                          if addr_is_error_b (len_word bs) then Unmodeled
                          else Ok (mkEffect (len_word bs) writes [])
                                 (with_fds (fd_insert (m_fds m) fd
                                    (FdFile p (off + len_word bs))) m) []
                      | None =>
                          match scatter_iovecs (in_wmem i) iovs [Z_to_bv 8 0] with
                          | None => ret_outcome (errno_ret EFAULT) m
                          | Some _ => Unmodeled
                          end
                      end
                  end
                  | RdFileRW p off =>   (* the [RdFile] arm above, on the O_RDWR kind *)
                  match fs_lookup (m_fs m) p with
                  | None => Unmodeled
                  | Some data =>
                      if rw_pos_einvalb off total then ret_outcome (errno_ret EINVAL) m
                      else
                      let bs := file_read data off (Z_to_bv 64 total) in
                      match scatter_iovecs (in_wmem i) iovs bs with
                      | Some writes =>
                          if addr_is_error_b (len_word bs) then Unmodeled
                          else Ok (mkEffect (len_word bs) writes [])
                                 (with_fds (fd_insert (m_fds m) fd
                                    (FdFileRW p (off + len_word bs))) m) []
                      | None =>
                          match scatter_iovecs (in_wmem i) iovs [Z_to_bv 8 0] with
                          | None => ret_outcome (errno_ret EFAULT) m
                          | Some _ => Unmodeled
                          end
                      end
                  end
              end
          end)
      end
  end.

Lemma readv_witness_ok : forall fd iov iovcnt i m,
  readv_spec fd iov iovcnt i m (readv_witness fd iov iovcnt i m).
Proof.
  intros. unfold readv_witness, readv_spec.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd.
  2:{ eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|]. cbv beta iota.
      srw Hfd. apply pure_ok. }
  destruct (readable_fd e) as [r|] eqn:Hr.
  2:{ eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|]. cbv beta iota.
      srw Hfd; srw Hr.
      destruct e; cbv beta iota;
        first [apply unmodeled_intro | apply pure_ok]. }
  destruct (readv_heap_iovecb iovcnt) eqn:Hheap.
  { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota.
    srw Hfd; srw Hr. unfold readv_heap_gap, readv_buf_gap.
    apply unmodeled_intro. }
  destruct (import_iovecs (in_mem i) iov (iovcnt32 iovcnt)) as [iovs0| |] eqn:Himp.
  2:{ eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|]. cbv beta iota.
      srw Hfd; srw Hr; srw Himp.
      eapply bind_step; [apply pure_ok|apply pure_ok]. }
  2:{ eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|]. cbv beta iota.
      srw Hfd; srw Hr; srw Himp.
      eapply bind_step; [apply pure_ok|apply pure_ok]. }
  unfold readv_imported. cbv zeta.
  destruct (Z.eqb (iovs_total (cap_iovecs iovs0)) 0) eqn:Htotal.
  { eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
    srw Hfd; srw Hr; srw Himp; srw Htotal.
    eapply bind_step; [apply pure_ok|apply pure_ok]. }
  destruct r as [ch|p off|p off| |sk|id| | ].
  7:{ eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
      srw Hfd; srw Hr; srw Himp; srw Htotal.
      eapply bind_step; [apply pure_ok|apply pure_ok]. }
  7:{ (* /dev/urandom: the vectored read declines *)
      eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
      eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota zeta.
      srw Hfd; srw Hr; srw Himp; srw Htotal.
      unfold readv_buf_gap. left. apply unmodeled_intro. }
  - destruct (m_stdin m) as [|b s] eqn:Hstdin.
    { eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
      srw Hfd; srw Hr; srw Himp; srw Htotal; srw Hstdin.
      eapply bind_step; [apply pure_ok|apply pure_ok]. }
    destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs0) [Z_to_bv 8 0])
      as [zero_writes|] eqn:Hzero.
    2:{ eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
        srw Hfd; srw Hr; srw Himp; srw Htotal; srw Hstdin; srw Hzero.
        eapply bind_step; [apply pure_ok|apply pure_ok]. }
    destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs0)
                (fst (stream_take_z (ICons b s) (iovs_total (cap_iovecs iovs0)))))
      as [need|] eqn:Hneed.
    2:{ eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
        srw Hfd; srw Hr; srw Himp; srw Htotal; srw Hstdin; srw Hzero; srw Hneed.
        left. unfold readv_buf_gap. apply unmodeled_intro. }
    destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs0) [b])
      as [writes|] eqn:Hone.
    2:{ exfalso.
        destruct (scatter_iovecs_singleton_some _ _ _ _ b Hzero) as [writes H].
        rewrite Hone in H. discriminate. }
    eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
    srw Hfd; srw Hr; srw Himp; srw Htotal; srw Hstdin; srw Hzero; srw Hneed.
    eapply witness_bind_ok_eq with (evs1 := [ReadEv ch b]) (evs2 := []);
      [|apply pure_ok|reflexivity].
    eapply bind_step.
    { apply (choose_ok _ [b]). split; [cbn; lia|]. split.
      - apply Z.eqb_neq in Htotal. pose proof (iovs_total_nonneg (cap_iovecs iovs0)).
        cbn. lia.
      - split; [reflexivity|]. rewrite Hone. discriminate. }
    cbv beta. rewrite Hone.
    eapply bind_step; [apply modify_ok|]. apply emit_pure_ok.
  - destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    2:{ eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
        srw Hfd; srw Hr; srw Himp; srw Htotal; srw Hfs.
        left. unfold readv_buf_gap. apply unmodeled_intro. }
    destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs0))) eqn:Hpos.
    { eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
      srw Hfd; srw Hr; srw Himp; srw Htotal; srw Hfs; srw Hpos.
      eapply bind_step; [apply pure_ok|apply pure_ok]. }
    cbv zeta.
    destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs0)
                (file_read data off
                   (Z_to_bv 64 (iovs_total (cap_iovecs iovs0))))) eqn:Hscatter.
    + destruct (addr_is_error_b
                  (len_word (file_read data off
                    (Z_to_bv 64 (iovs_total (cap_iovecs iovs0)))))) eqn:Hae.
      * eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
        srw Hfd; srw Hr; srw Himp; srw Htotal; srw Hfs; srw Hpos;
          srw Hscatter; srw Hae.
        left. unfold readv_buf_gap. apply unmodeled_intro.
      * eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
        srw Hfd; srw Hr; srw Himp; srw Htotal; srw Hfs; srw Hpos;
          srw Hscatter; srw Hae.
        eapply bind_step; [|apply pure_ok].
        eapply bind_step; [apply modify_ok|]. apply pure_ok.
    + destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs0) [Z_to_bv 8 0])
        eqn:Hzero.
      * eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
        srw Hfd; srw Hr; srw Himp; srw Htotal; srw Hfs; srw Hpos;
          srw Hscatter; srw Hzero.
        left. unfold readv_buf_gap. apply unmodeled_intro.
      * eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
        srw Hfd; srw Hr; srw Himp; srw Htotal; srw Hfs; srw Hpos;
          srw Hscatter; srw Hzero.
        eapply bind_step; [apply pure_ok|apply pure_ok].
  - (* the same file opened O_RDWR: the file bullet above *)
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    2:{ eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
        srw Hfd; srw Hr; srw Himp; srw Htotal; srw Hfs.
        left. unfold readv_buf_gap. apply unmodeled_intro. }
    destruct (rw_pos_einvalb off (iovs_total (cap_iovecs iovs0))) eqn:Hpos.
    { eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
      srw Hfd; srw Hr; srw Himp; srw Htotal; srw Hfs; srw Hpos.
      eapply bind_step; [apply pure_ok|apply pure_ok]. }
    cbv zeta.
    destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs0)
                (file_read data off
                   (Z_to_bv 64 (iovs_total (cap_iovecs iovs0))))) eqn:Hscatter.
    + destruct (addr_is_error_b
                  (len_word (file_read data off
                    (Z_to_bv 64 (iovs_total (cap_iovecs iovs0)))))) eqn:Hae.
      * eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
        srw Hfd; srw Hr; srw Himp; srw Htotal; srw Hfs; srw Hpos;
          srw Hscatter; srw Hae.
        left. unfold readv_buf_gap. apply unmodeled_intro.
      * eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
        srw Hfd; srw Hr; srw Himp; srw Htotal; srw Hfs; srw Hpos;
          srw Hscatter; srw Hae.
        eapply bind_step; [|apply pure_ok].
        eapply bind_step; [apply modify_ok|]. apply pure_ok.
    + destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs0) [Z_to_bv 8 0])
        eqn:Hzero.
      * eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
        srw Hfd; srw Hr; srw Himp; srw Htotal; srw Hfs; srw Hpos;
          srw Hscatter; srw Hzero.
        left. unfold readv_buf_gap. apply unmodeled_intro.
      * eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
        srw Hfd; srw Hr; srw Himp; srw Htotal; srw Hfs; srw Hpos;
          srw Hscatter; srw Hzero.
        eapply bind_step; [apply pure_ok|apply pure_ok].
  - eapply bind_step; [apply input_ok|]. cbv beta.
    eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
    srw Hfd; srw Hr; srw Himp; srw Htotal.
    eapply bind_step; [apply pure_ok|apply pure_ok].
  - (* socket *)
    destruct sk as [| | |peer ch rx|peer ch].
    + (* fresh: -ENOTCONN *)
      eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
      srw Hfd; srw Hr; srw Himp; srw Htotal.
      eapply bind_step; [apply pure_ok|apply pure_ok].
    + (* bound: -ENOTCONN *)
      eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
      srw Hfd; srw Hr; srw Himp; srw Htotal.
      eapply bind_step; [apply pure_ok|apply pure_ok].
    + (* listening: -ENOTCONN *)
      eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
      srw Hfd; srw Hr; srw Himp; srw Htotal.
      eapply bind_step; [apply pure_ok|apply pure_ok].
    + destruct rx as [| | |b rest].
      * (* the peer's FIN: 0 *)
        eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
        srw Hfd; srw Hr; srw Himp; srw Htotal.
        eapply bind_step; [apply pure_ok|apply pure_ok].
      * (* a pending reset, consumed by this readv *)
        eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
        srw Hfd; srw Hr; srw Himp; srw Htotal.
        eapply bind_step; [|apply pure_ok].
        eapply bind_step; [apply modify_ok|]. apply pure_ok.
      * (* a pending timeout: the same shape *)
        eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
        srw Hfd; srw Hr; srw Himp; srw Htotal.
        eapply bind_step; [|apply pure_ok].
        eapply bind_step; [apply modify_ok|]. apply pure_ok.
      * (* a queued byte: the one-byte scatter *)
        destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs0) [Z_to_bv 8 0])
          as [zero_writes|] eqn:Hzero.
        2:{ eapply bind_step; [apply input_ok|]. cbv beta.
            eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
            srw Hfd; srw Hr; srw Himp; srw Htotal; srw Hzero.
            eapply bind_step; [apply pure_ok|apply pure_ok]. }
        destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs0)
                    (fst (net_take_z (NCons b rest) (iovs_total (cap_iovecs iovs0)))))
          as [need|] eqn:Hneed.
        2:{ eapply bind_step; [apply input_ok|]. cbv beta.
            eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
            srw Hfd; srw Hr; srw Himp; srw Htotal; srw Hzero; srw Hneed.
            left. unfold readv_buf_gap. apply unmodeled_intro. }
        destruct (scatter_iovecs (in_wmem i) (cap_iovecs iovs0) [b])
          as [writes|] eqn:Hone.
        2:{ exfalso.
            destruct (scatter_iovecs_singleton_some _ _ _ _ b Hzero) as [writes H].
            rewrite Hone in H. discriminate. }
        eapply bind_step; [apply input_ok|]. cbv beta.
        eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
        srw Hfd; srw Hr; srw Himp; srw Htotal; srw Hzero; srw Hneed.
        eapply witness_bind_ok_eq with (evs1 := [ReadEv ch b]) (evs2 := []);
          [|apply pure_ok|reflexivity].
        eapply bind_step.
        { apply (choose_ok _ [b]). split; [cbn; lia|]. split.
          - apply Z.eqb_neq in Htotal. pose proof (iovs_total_nonneg (cap_iovecs iovs0)).
            cbn. lia.
          - split; [reflexivity|]. rewrite Hone. discriminate. }
        cbv beta. rewrite Hone.
        eapply bind_step; [apply modify_ok|]. apply emit_pure_ok.
    + (* the error already delivered: reads as end of stream *)
      eapply bind_step; [apply input_ok|]. cbv beta.
      eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
      srw Hfd; srw Hr; srw Himp; srw Htotal.
      eapply bind_step; [apply pure_ok|apply pure_ok].
  - (* pipe read end: vectored pipe reads are unmodeled, whatever the
       vector says *)
    eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota zeta.
    srw Hfd; srw Hr; srw Himp; srw Htotal.
    unfold readv_buf_gap. left. apply unmodeled_intro.
Qed.

(* =========================================================================
   openat (56) — witness: a path errno (-ENAMETOOLONG / -EFAULT /
   -ENOENT), the environment-failure branch (errno 12), or [Unmodeled]
   ========================================================================= *)

Definition lseek_witness (fd off whence : word) (m : Model)
    : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m
  | Some e =>
      if (SEEK_MAX <? bv_unsigned whence)%Z
      then (if fd_is_opaque e then Unmodeled else ret_outcome (errno_ret EINVAL) m)
      else
      match e with
      | FdChannel _ => ret_outcome (errno_ret ESPIPE) m
      | FdSocket _ => ret_outcome (errno_ret ESPIPE) m  (* a socket has no offset *)
      | FdPipe _ _ => ret_outcome (errno_ret ESPIPE) m
      | FdDevNull _ _ => ret_outcome (Z_to_bv 64 0) m
      | FdUrandom => ret_outcome (Z_to_bv 64 0) m
      | FdOpaque _ => Unmodeled
      | FdDir => Unmodeled   (* unmodeled: see [ReadWrite.lseek_spec] *)
      | FdFile p cur =>
          match fs_lookup (m_fs m) p with
          | None => Unmodeled
          | Some data =>
              match lseek_base whence cur (len_word data) with
              | None => Unmodeled   (* SEEK_DATA/SEEK_HOLE: unmodeled *)
              | Some base =>
                  match lseek_dest base off with
                  | None => ret_outcome (errno_ret EINVAL) m
                  | Some r =>
                      ret_outcome r
                        (with_fds (fd_insert (m_fds m) fd (FdFile p r)) m)
                  end
              end
          end
      | FdFileW p cur =>
          match fs_lookup (m_fs m) p with
          | None => Unmodeled
          | Some data =>
              match lseek_base whence cur (len_word data) with
              | None => Unmodeled   (* SEEK_DATA/SEEK_HOLE: unmodeled *)
              | Some base =>
                  match lseek_dest base off with
                  | None => ret_outcome (errno_ret EINVAL) m
                  | Some r =>
                      ret_outcome r
                        (with_fds (fd_insert (m_fds m) fd (FdFileW p r)) m)
                  end
              end
          end
      | FdFileRW p cur =>   (* the [FdFileW] arm above, on the O_RDWR kind *)
          match fs_lookup (m_fs m) p with
          | None => Unmodeled
          | Some data =>
              match lseek_base whence cur (len_word data) with
              | None => Unmodeled   (* SEEK_DATA/SEEK_HOLE: unmodeled *)
              | Some base =>
                  match lseek_dest base off with
                  | None => ret_outcome (errno_ret EINVAL) m
                  | Some r =>
                      ret_outcome r
                        (with_fds (fd_insert (m_fds m) fd (FdFileRW p r)) m)
                  end
              end
          end
      | FdFileA p cur =>
          match fs_lookup (m_fs m) p with
          | None => Unmodeled
          | Some data =>
              match lseek_base whence cur (len_word data) with
              | None => Unmodeled   (* SEEK_DATA/SEEK_HOLE: unmodeled *)
              | Some base =>
                  match lseek_dest base off with
                  | None => ret_outcome (errno_ret EINVAL) m
                  | Some r =>
                      ret_outcome r
                        (with_fds (fd_insert (m_fds m) fd (FdFileA p r)) m)
                  end
              end
          end
      end
  end.

Lemma lseek_witness_ok : forall fd off whence i m,
  lseek_spec fd off whence i m (lseek_witness fd off whence m).
Proof.
  intros. unfold lseek_spec, lseek_witness.
  destruct (fd_lookup (m_fds m) fd) as [[ch|p cur|p cur|p cur|p cur| |sk|id w|rd wr| |o]|] eqn:Hfd;
    try (destruct ((SEEK_MAX <? bv_unsigned whence)%Z) eqn:Hw;
         [ eapply bind_step; [apply get_model_ok|];
           cbv beta iota; srw Hfd; first [apply pure_ok | apply unmodeled_intro] |]).
  - (* channel *)
    eapply bind_step; [apply get_model_ok|].
    cbv beta iota; srw Hfd. apply pure_ok.
  - destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    + destruct (lseek_base whence cur (len_word data)) as [base|]
        eqn:Hbase.
      * destruct (lseek_dest base off) as [r|] eqn:Hdst.
        -- eapply bind_step; [apply get_model_ok|].
           cbv beta iota; srw Hfd; srw Hfs; srw Hbase; srw Hdst.
           eapply bind_step; [apply modify_ok|]. apply pure_ok.
        -- eapply bind_step; [apply get_model_ok|].
           cbv beta iota; srw Hfd; srw Hfs; srw Hbase; srw Hdst. apply pure_ok.
      * (* SEEK_DATA/SEEK_HOLE: unmodeled *)
        eapply bind_step; [apply get_model_ok|].
        cbv beta iota; srw Hfd; srw Hfs; srw Hbase. apply unmodeled_intro.
    + eapply bind_step; [apply get_model_ok|].
      cbv beta iota; srw Hfd; srw Hfs. apply unmodeled_intro.
  - (* write-only file fd: same repositioning *)
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    + destruct (lseek_base whence cur (len_word data)) as [base|]
        eqn:Hbase.
      * destruct (lseek_dest base off) as [r|] eqn:Hdst.
        -- eapply bind_step; [apply get_model_ok|].
           cbv beta iota; srw Hfd; srw Hfs; srw Hbase; srw Hdst.
           eapply bind_step; [apply modify_ok|]. apply pure_ok.
        -- eapply bind_step; [apply get_model_ok|].
           cbv beta iota; srw Hfd; srw Hfs; srw Hbase; srw Hdst. apply pure_ok.
      * eapply bind_step; [apply get_model_ok|].
        cbv beta iota; srw Hfd; srw Hfs; srw Hbase. apply unmodeled_intro.
    + eapply bind_step; [apply get_model_ok|].
      cbv beta iota; srw Hfd; srw Hfs. apply unmodeled_intro.
  - (* append fd: same repositioning again — lseek reads neither the
       access mode nor O_APPEND *)
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    + destruct (lseek_base whence cur (len_word data)) as [base|]
        eqn:Hbase.
      * destruct (lseek_dest base off) as [r|] eqn:Hdst.
        -- eapply bind_step; [apply get_model_ok|].
           cbv beta iota; srw Hfd; srw Hfs; srw Hbase; srw Hdst.
           eapply bind_step; [apply modify_ok|]. apply pure_ok.
        -- eapply bind_step; [apply get_model_ok|].
           cbv beta iota; srw Hfd; srw Hfs; srw Hbase; srw Hdst. apply pure_ok.
      * eapply bind_step; [apply get_model_ok|].
        cbv beta iota; srw Hfd; srw Hfs; srw Hbase. apply unmodeled_intro.
    + eapply bind_step; [apply get_model_ok|].
      cbv beta iota; srw Hfd; srw Hfs. apply unmodeled_intro.
  - (* the same file opened O_RDWR: same repositioning, and the one
       arm where the shared [f_pos] is set for both directions at once *)
    destruct (fs_lookup (m_fs m) p) as [data|] eqn:Hfs.
    + destruct (lseek_base whence cur (len_word data)) as [base|]
        eqn:Hbase.
      * destruct (lseek_dest base off) as [r|] eqn:Hdst.
        -- eapply bind_step; [apply get_model_ok|].
           cbv beta iota; srw Hfd; srw Hfs; srw Hbase; srw Hdst.
           eapply bind_step; [apply modify_ok|]. apply pure_ok.
        -- eapply bind_step; [apply get_model_ok|].
           cbv beta iota; srw Hfd; srw Hfs; srw Hbase; srw Hdst. apply pure_ok.
      * eapply bind_step; [apply get_model_ok|].
        cbv beta iota; srw Hfd; srw Hfs; srw Hbase. apply unmodeled_intro.
    + eapply bind_step; [apply get_model_ok|].
      cbv beta iota; srw Hfd; srw Hfs. apply unmodeled_intro.
  - (* directory fd: unmodeled, fail closed *)
    eapply bind_step; [apply get_model_ok|].
    cbv beta iota; srw Hfd. apply unmodeled_intro.
  - (* socket: -ESPIPE, whatever its state *)
    eapply bind_step; [apply get_model_ok|].
    cbv beta iota; srw Hfd. apply pure_ok.
  - (* either pipe end: -ESPIPE *)
    eapply bind_step; [apply get_model_ok|].
    cbv beta iota; srw Hfd. apply pure_ok.
  - (* /dev/null: [null_lseek]'s 0, whatever the whence *)
    eapply bind_step; [apply get_model_ok|].
    cbv beta iota; srw Hfd. apply pure_ok.
  - (* /dev/urandom: [noop_llseek]'s pinned 0 *)
    eapply bind_step; [apply get_model_ok|].
    cbv beta iota; srw Hfd. apply pure_ok.
  - (* the opaque kinds: declined *)
    eapply bind_step; [apply get_model_ok|].
    cbv beta iota; srw Hfd. apply unmodeled_intro.
  - eapply bind_step; [apply get_model_ok|].
    cbv beta iota; srw Hfd. apply pure_ok.
Qed.

(* =========================================================================
   brk (214) — witness: KEEP THE CURRENT BREAK ([r = vm_brk h]), which
   every path admits (query/invalid returns it; shrink and grow both have
   the failure branch that keeps it) — so receptivity never needs a
   "a free region always exists" lemma.
   ========================================================================= *)

(** One admissible outcome of [syscall_spec] for EVERY input and model
    state (unmodeled syscall numbers get [Unmodeled] — fail closed, but never
    stuck).  Mirrors the dispatch of [Specs.syscall_spec]. *)
