(** * LinuxProcessSem.Checks.Cases.Fs.TmpFile — worked examples over the unnamed temporary file: openat (56) of /tmp with O_RDWR|O_CREAT|O_EXCL, unlinkat (35) of the open name, and the reopen through /proc/self/fd/N

    The acceptance case A9 of dispatch://OSSV-287 (spec version 9).
    Linux v6.18.46 (commit 1f99e9ab748f) throughout: fs/namei.c,
    fs/proc/fd.c, fs/open.c, fs/read_write.c, fs/stat.c.  musl's
    [tmpfile()] (src/stdio/tmpfile.c) makes the sequence of PART 1.

    PART 1 names no constructor that this change adds: every Example is
    stated through [check_syscall] and [syscall_spec_witness] alone, so
    the same text compiles against the model before this change.  There
    each one is FALSE except the controls named where they are, because
    every run below starts with the O_RDWR|O_CREAT|O_EXCL create of a
    /tmp name, which the model declined.  That is the fail-before half.

    PART 2 pins the model states the calls produce. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Decode DecodeC.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export Prelude.

(* =========================================================================
   Fixtures
   ========================================================================= *)

(** The start: [init_model]'s three channels, so the next descriptor is 3. *)
Definition tf_m0 : Model := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof).

Fixpoint region_byte (rs : list (Z * list byte)) (a : Z) : option byte :=
  match rs with
  | [] => None
  | (b, bs) :: r =>
      if ((b <=? a) && (a <? b + Z.of_nat (length bs)))%Z
      then nth_error bs (Z.to_nat (a - b)%Z)
      else region_byte r a
  end.
Definition region_mem (rs : list (Z * list byte)) : word -> option byte :=
  fun a => region_byte rs (bv_unsigned a).

Definition zeros (n : nat) : list byte := repeat (Z_to_bv 8 0) n.

(** Bytes from their codes, and the same with a NUL after them.  The
    texts are written as ASCII codes, with the text in a comment. *)
Definition bytes_of (l : list Z) : list byte := map (Z_to_bv 8) l.
Definition cstr (l : list Z) : list byte := bytes_of l ++ [Z_to_bv 8 0].

(** Addresses: the two path strings, a write source, a read destination,
    a winsize, and a stat buffer. *)
Definition tmp_a : Z := 0xA000.
Definition proc_a : Z := 0xA100.
Definition src_a : Z := 0xA200.
Definition dst_a : Z := 0xA300.
Definition ws_a : Z := 0xA400.
Definition st_a : Z := 0xA500.

(** Everything a call below may write is writable. *)
Definition tf_wmem : word -> option byte :=
  region_mem [(dst_a, zeros 64); (ws_a, zeros 8); (st_a, zeros 128)].

Definition w (z : Z) : word := Z_to_bv 64 z.
Definition at_fdcwd : Z := (2 ^ 64 - 100)%Z.

Definition tmp_name : list Z := [47; 116; 109; 112; 47; 116; 109; 112; 102; 105; 108; 101; 95; 97; 98; 99; 100; 101; 102]%Z.   (* "/tmp/tmpfile_abcdef" *)
Definition proc_name (n : list Z) : list Z := [47; 112; 114; 111; 99; 47; 115; 101; 108; 102; 47; 102; 100; 47]%Z ++ n.   (* "/proc/self/fd/" ++ n *)

Definition mk (sysno : Z) (args : list Z) (rs : list (Z * list byte)) : SyscallInput :=
  mkInput (w sysno) (map w args) (region_mem rs) tf_wmem.

Definition errno_eff (e : Z) : SyscallEffect := mkEffect (errno_ret e) [] [].
Definition ok_eff (r : Z) : SyscallEffect := mkEffect (w r) [] [].

(** The calls.  O_RDWR|O_CREAT|O_EXCL|O_LARGEFILE is 32962; musl passes
    mode 0600 (384). *)
Definition create_in : SyscallInput :=
  mk 56 [at_fdcwd; tmp_a; 32962; 384]%Z [(tmp_a, cstr tmp_name)].
Definition unlink_in : SyscallInput :=
  mk 35 [at_fdcwd; tmp_a; 0]%Z [(tmp_a, cstr tmp_name)].
Definition winsz_in (fd : Z) : SyscallInput :=
  mk 29 [fd; 21523; ws_a]%Z [].
Definition ftruncate_in (fd len : Z) : SyscallInput := mk 46 [fd; len]%Z [].
(** pwritev2(fd, iov, 1, pos, 0, RWF_NOAPPEND): musl 1.2.6's pwrite
    (src/unistd/pwrite.c).  The one iovec at [iov_a] names [bs] at
    [src_a].  Its effect is the witness's (a [None] step), and the
    examples check its return. *)
Definition iov_a : Z := 0xA600.
Definition pwv_in (fd : Z) (bs : list byte) (pos : Z) : SyscallInput :=
  mk 287 [fd; iov_a; 1; pos; 0; 32]%Z
     [(src_a, bs); (iov_a, Z_to_le_bytes 8 src_a ++ Z_to_le_bytes 8 (Z.of_nat (length bs)))].
Definition write_in (fd : Z) (bs : list byte) : SyscallInput :=
  mk 64 [fd; src_a; Z.of_nat (length bs)]%Z [(src_a, bs)].
Definition write_ok (bs : list byte) : SyscallEffect :=
  with_copyins [(w src_a, length bs)] (mkEffect (w (Z.of_nat (length bs))) [] []).
Definition proc_open_in (n : list Z) (flags mode : Z) : SyscallInput :=
  mk 56 [at_fdcwd; proc_a; flags; mode]%Z [(proc_a, cstr (proc_name n))].
Definition read_in (fd : Z) : SyscallInput := mk 63 [fd; dst_a; 64]%Z [].
Definition read_ok (bs : list byte) : SyscallEffect :=
  mkEffect (w (Z.of_nat (length bs))) (match bs with [] => [] | _ => [(w dst_a, bs)] end) [].
Definition fstat_in (fd : Z) : SyscallInput := mk 80 [fd; st_a]%Z [].
Definition close_in (fd : Z) : SyscallInput := mk 57 [fd]%Z [].
(** The path reads that openat and unlinkat record: the bytes of the name
    and its NUL ("/tmp/tmpfile_abcdef" is 19 bytes, "/proc/self/fd/" 14). *)
Definition at_tmp (e : SyscallEffect) : SyscallEffect := with_copyins [(w tmp_a, 20%nat)] e.
Definition at_proc (n : list Z) (e : SyscallEffect) : SyscallEffect :=
  with_copyins [(w proc_a, (15 + length n)%nat)] e.

(** Run the steps through the checker, every one accepted; a step with
    [None] takes its effect from [syscall_spec_witness]. *)
Fixpoint run_steps (m : Model) (steps : list (SyscallInput * option SyscallEffect))
    : option Model :=
  match steps with
  | [] => Some m
  | (i, oe) :: rest =>
      let e := match oe with
               | Some e => Some e
               | None => match syscall_spec_witness i m with
                         | Ok e _ _ => Some e
                         | Unmodeled => None
                         end
               end in
      match e with
      | None => None
      | Some e =>
          match check_syscall i e m with
          | CheckOk m' _ => run_steps m' rest
          | _ => None
          end
      end
  end.

Definition after (steps : list (SyscallInput * option SyscallEffect))
    (i : SyscallInput) (e : SyscallEffect) : option check_result :=
  match run_steps tf_m0 steps with
  | Some m => Some (check_syscall i e m)
  | None => None
  end.
Definition is_ok (r : option check_result) : bool :=
  match r with Some (CheckOk _ _) => true | _ => false end.

(** The witness's effect after a run, with the checker accepting it. *)
Definition answer (steps : list (SyscallInput * option SyscallEffect)) (i : SyscallInput)
    : option SyscallEffect :=
  match run_steps tf_m0 steps with
  | Some m =>
      match syscall_spec_witness i m with
      | Ok e _ _ => match check_syscall i e m with
                    | CheckOk _ _ => Some e
                    | _ => None
                    end
      | Unmodeled => None
      end
  | None => None
  end.

Definition hello : list byte := bytes_of [104; 101; 108; 108; 111]%Z.   (* "hello" *)

(** musl's [tmpfile()] and the harness's first write: the create at 3,
    the removal of the name, [__fdopen]'s TIOCGWINSZ, then
    [BoundedAnonymousInputFile::Write]'s ftruncate and pwrite (pwritev2). *)
Definition tmpfile_and_write : list (SyscallInput * option SyscallEffect) :=
  [ (create_in, Some (at_tmp (ok_eff 3)));
    (unlink_in, Some (at_tmp (ok_eff 0)));
    (winsz_in 3, Some (errno_eff ENOTTY));
    (ftruncate_in 3 0, Some (ok_eff 0));
    (pwv_in 3 hello 0, None) ].

(* =========================================================================
   PART 1 — A9: the tmpfile sequence and the reopen
   ========================================================================= *)

(** The whole sequence of A9: the reopen of /proc/self/fd/3 read-only at
    4, an fstat (the witness's answer), the read of the same five bytes,
    and the close. *)
Example a9_tmpfile_sequence_is_accepted :
  is_ok (after (tmpfile_and_write
                ++ [ (proc_open_in [51]%Z 32768 0, Some (at_proc [51]%Z (ok_eff 4)));
                     (fstat_in 4, None) ])
               (read_in 4) (read_ok hello)) = true
  /\ is_ok (after (tmpfile_and_write
                   ++ [ (proc_open_in [51]%Z 32768 0, Some (at_proc [51]%Z (ok_eff 4)));
                        (fstat_in 4, None);
                        (read_in 4, Some (read_ok hello)) ])
                  (close_in 4) (ok_eff 0)) = true.
Proof. split; check_eq. Qed.

(** The pwritev2 of the harness writes the five bytes and returns 5. *)
Example a9_pwritev2_returns_its_count :
  option_map eff_ret (answer (firstn 4 tmpfile_and_write) (pwv_in 3 hello 0)) = Some (w 5).
Proof. check_eq. Qed.

(** The read is refused when it claims bytes the file does not hold. *)
Example a9_read_refuses_other_bytes :
  after (tmpfile_and_write ++ [(proc_open_in [51]%Z 32768 0, Some (at_proc [51]%Z (ok_eff 4)))])
        (read_in 4) (read_ok (bytes_of [104; 101; 108; 108; 120]%Z)) = Some CheckReject.
Proof. check_eq. Qed.

(** A held name gives -EEXIST to a second exclusive create, and the
    create is refused a descriptor there. *)
Example a9_exclusive_create_of_a_held_name_is_eexist :
  is_ok (after [(create_in, Some (at_tmp (ok_eff 3)))] create_in (at_tmp (errno_eff EEXIST))) = true
  /\ after [(create_in, Some (at_tmp (ok_eff 3)))] create_in (at_tmp (ok_eff 4)) = Some CheckReject.
Proof. split; check_eq. Qed.

(** /proc/self/fd/9 with no descriptor 9 open: -ENOENT, with O_CREAT too. *)
Example a9_proc_fd_of_a_closed_descriptor_is_enoent :
  is_ok (after tmpfile_and_write (proc_open_in [57]%Z 32768 0) (at_proc [57]%Z (errno_eff ENOENT))) = true
  /\ is_ok (after tmpfile_and_write (proc_open_in [57]%Z (1 + 64 + 512) 420) (at_proc [57]%Z (errno_eff ENOENT))) = true.
Proof. split; check_eq. Qed.

(** A write through 3 after the reopen is seen through 4. *)
Example a9_write_through_one_descriptor_is_seen_through_another :
  is_ok (after (tmpfile_and_write
                ++ [ (proc_open_in [51]%Z 32768 0, Some (at_proc [51]%Z (ok_eff 4)));
                     (pwv_in 3 (bytes_of [88; 89]%Z) 0, None) ])
               (read_in 4) (read_ok (bytes_of [88; 89; 108; 108; 111]%Z))) = true.
Proof. check_eq. Qed.

(** O_WRONLY|O_CREAT|O_TRUNC through /proc/self/fd/3 empties the file for
    every descriptor: a read through a later read-only reopen gets end of
    file, and so does a read through a read-only reopen made BEFORE it. *)
Example a9_trunc_through_proc_empties_every_descriptor :
  is_ok (after (tmpfile_and_write
                ++ [ (proc_open_in [51]%Z (1 + 64 + 512) 420, Some (at_proc [51]%Z (ok_eff 4)));
                     (proc_open_in [51]%Z 32768 0, Some (at_proc [51]%Z (ok_eff 5))) ])
               (read_in 5) (read_ok [])) = true
  /\ is_ok (after (tmpfile_and_write
                   ++ [ (proc_open_in [51]%Z 32768 0, Some (at_proc [51]%Z (ok_eff 4)));
                        (proc_open_in [51]%Z (1 + 64 + 512) 420, Some (at_proc [51]%Z (ok_eff 5))) ])
                  (read_in 4) (read_ok [])) = true.
Proof. split; check_eq. Qed.

(** A write through an O_APPEND reopen lands at the end of the file. *)
Example a9_append_write_lands_at_the_end :
  is_ok (after (tmpfile_and_write
                ++ [ (proc_open_in [51]%Z (1 + 64 + 1024) 420, Some (at_proc [51]%Z (ok_eff 4)));
                     (write_in 4 (bytes_of [33; 33]%Z), Some (write_ok (bytes_of [33; 33]%Z)));
                     (proc_open_in [51]%Z 32768 0, Some (at_proc [51]%Z (ok_eff 5))) ])
               (read_in 5) (read_ok (bytes_of [104; 101; 108; 108; 111; 33; 33]%Z))) = true.
Proof. check_eq. Qed.

(** Two fstats of the file give the same stable fields: the second is
    accepted with the first's bytes, and refused with its inode changed. *)
Definition first_stat : option (list byte) :=
  match answer (tmpfile_and_write ++ [(proc_open_in [51]%Z 32768 0, Some (at_proc [51]%Z (ok_eff 4)))]) (fstat_in 4) with
  | Some e => match eff_writes e with [(_, bs)] => Some bs | _ => None end
  | None => None
  end.
Definition bump_ino (bs : list byte) : list byte :=
  firstn 8 bs ++ [Z_to_bv 8 (bv_unsigned (nth 8 bs (Z_to_bv 8 0)) + 1)] ++ skipn 9 bs.
Example a9_two_fstats_agree :
  match first_stat with
  | Some bs =>
      let steps := tmpfile_and_write ++ [ (proc_open_in [51]%Z 32768 0, Some (at_proc [51]%Z (ok_eff 4)));
                                          (fstat_in 4, Some (mkEffect 0 [(w st_a, bs)] [])) ] in
      is_ok (after steps (fstat_in 4) (mkEffect 0 [(w st_a, bs)] [])) = true
      /\ after steps (fstat_in 4) (mkEffect 0 [(w st_a, bump_ino bs)] []) = Some CheckReject
  | None => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

(** The declining case: readv of 8 bytes on the unnamed file (one iovec
    at [src_a] naming [dst_a]). *)
Example a9_readv_on_the_unnamed_file_declines :
  match run_steps tf_m0 tmpfile_and_write with
  | Some m => syscall_spec_witness (mk 65 [3; src_a; 1]%Z [(src_a, Z_to_le_bytes 8 dst_a ++ Z_to_le_bytes 8 8)]) m = Unmodeled
  | None => False
  end.
Proof. check_eq. Qed.

(** CONTROL, true at the base as well: /proc/self/fd/03 declines. *)
Example a9_proc_fd_with_a_leading_zero_declines :
  syscall_spec_witness (proc_open_in [48; 51]%Z 32768 0) tf_m0 = Unmodeled.
Proof. check_eq. Qed.

(** CONTROL, true at the base as well: the working-directory arm still
    declines the removal of a name that a descriptor holds.  "f" is
    created at 3 with O_WRONLY|O_CREAT|O_TRUNC (577) and stays open. *)
Example a9_working_directory_removal_of_an_open_name_declines :
  match run_steps tf_m0 [(mk 56 [at_fdcwd; tmp_a; 577; 420]%Z [(tmp_a, cstr [102]%Z)], Some (with_copyins [(w tmp_a, 2%nat)] (ok_eff 3)))] with
  | Some m => syscall_spec_witness (mk 35 [at_fdcwd; tmp_a; 0]%Z [(tmp_a, cstr [102]%Z)]) m = Unmodeled
  | None => False
  end.
Proof. check_eq. Qed.

(* =========================================================================
   PART 3 — A10: three sequences of the curl_fuzzer_proto_file census
   ========================================================================= *)

(** The census of curl_fuzzer_proto_file (dispatch://OSSV-287/artifact/a10-summary-md,
    sections 3 and 5) gives every call made on the temporary file and on
    the descriptors its /proc/self/fd/N reopens return.  The sequences
    below are those calls, in order, for three of its scenarios; the calls
    on other descriptors (the eventfds, /dev/null, the IPv6 probe) are
    left out, and the descriptor numbers are the model's: the temporary
    file at 3, the read reopen at 4, the write reopen at 5. *)

Definition lseek_in (fd off whence : Z) : SyscallInput := mk 62 [fd; off; whence]%Z [].
Definition read_n_in (fd n : Z) : SyscallInput := mk 63 [fd; dst_a; n]%Z [].

(** The harness half of every lifecycle, with [bs] as the file source. *)
Definition harness_head (bs : list byte) : list (SyscallInput * option SyscallEffect) :=
  [ (create_in, Some (at_tmp (ok_eff 3)));
    (unlink_in, Some (at_tmp (ok_eff 0)));
    (winsz_in 3, Some (errno_eff ENOTTY));
    (ftruncate_in 3 0, Some (ok_eff 0));
    (pwv_in 3 bs 0, None) ].

(** file_resume_range (file_source "0123456789", range "4-4"): the read
    reopen, fstat, lseek(4, SEEK_SET) = 4, read 1 byte = "4", read 0 = 0,
    the two closes. *)
Definition seq_resume_range : list (SyscallInput * option SyscallEffect) :=
  harness_head (bytes_of [48; 49; 50; 51; 52; 53; 54; 55; 56; 57]%Z)
  ++ [ (proc_open_in [51]%Z 32768 0, Some (at_proc [51]%Z (ok_eff 4)));
       (fstat_in 4, None);
       (lseek_in 4 4 0, Some (ok_eff 4));
       (read_n_in 4 1, Some (mkEffect (w 1) [(w dst_a, bytes_of [52]%Z)] []));
       (read_n_in 4 0, Some (ok_eff 0));
       (close_in 4, Some (ok_eff 0));
       (close_in 3, Some (ok_eff 0)) ].

Example a10_resume_range_is_accepted :
  match run_steps tf_m0 seq_resume_range with Some _ => True | None => False end.
Proof. vm_compute. exact I. Qed.

(** file_upload (file_source "sink"): the read reopen, the write reopen
    with O_WRONLY|O_CREAT|O_TRUNC|O_LARGEFILE (0x8241) and mode 0644,
    writes of 3, 5 and 12 bytes, the three closes. *)
Definition seq_upload : list (SyscallInput * option SyscallEffect) :=
  harness_head (bytes_of [115; 105; 110; 107]%Z)
  ++ [ (proc_open_in [51]%Z 32768 0, Some (at_proc [51]%Z (ok_eff 4)));
       (proc_open_in [51]%Z 33345 420, Some (at_proc [51]%Z (ok_eff 5)));
       (write_in 5 (bytes_of [102; 105; 108]%Z), Some (write_ok (bytes_of [102; 105; 108]%Z)));
       (write_in 5 (bytes_of [101; 32; 117; 112; 108]%Z), Some (write_ok (bytes_of [101; 32; 117; 112; 108]%Z)));
       (write_in 5 (bytes_of [111; 97; 100; 32; 112; 97; 121; 108; 111; 97; 100; 10]%Z), Some (write_ok (bytes_of [111; 97; 100; 32; 112; 97; 121; 108; 111; 97; 100; 10]%Z)));
       (close_in 5, Some (ok_eff 0)) ].

Example a10_upload_is_accepted_and_the_file_holds_the_upload :
  is_ok (after (seq_upload ++ [(close_in 4, Some (ok_eff 0))]) (close_in 3) (ok_eff 0)) = true
  /\ is_ok (after (seq_upload ++ [(proc_open_in [51]%Z 32768 0, Some (at_proc [51]%Z (ok_eff 5)))])
                  (read_in 5) (read_ok (bytes_of [102; 105; 108; 101; 32; 117; 112; 108; 111; 97; 100; 32; 112; 97; 121; 108; 111; 97; 100; 10]%Z))) = true.
Proof. split; check_eq. Qed.

(** file_upload_resume: the write reopen with O_WRONLY|O_CREAT|O_APPEND|O_LARGEFILE
    (0x8441), writes of 0, 5 and 6 bytes, which land after "sink". *)
Definition seq_upload_resume : list (SyscallInput * option SyscallEffect) :=
  harness_head (bytes_of [115; 105; 110; 107]%Z)
  ++ [ (proc_open_in [51]%Z 32768 0, Some (at_proc [51]%Z (ok_eff 4)));
       (proc_open_in [51]%Z 33857 420, Some (at_proc [51]%Z (ok_eff 5)));
       (write_in 5 [], None);   (* a zero-length write: the witness's effect, which records no read *)
       (write_in 5 (bytes_of [45; 97; 110; 100; 45]%Z), Some (write_ok (bytes_of [45; 97; 110; 100; 45]%Z)));
       (write_in 5 (bytes_of [117; 112; 108; 111; 97; 100]%Z), Some (write_ok (bytes_of [117; 112; 108; 111; 97; 100]%Z)));
       (close_in 5, Some (ok_eff 0)) ].

Example a10_upload_resume_appends :
  is_ok (after (seq_upload_resume ++ [(proc_open_in [51]%Z 32768 0, Some (at_proc [51]%Z (ok_eff 5)))])
               (read_in 5) (read_ok (bytes_of [115; 105; 110; 107; 45; 97; 110; 100; 45; 117; 112; 108; 111; 97; 100]%Z))) = true.
Proof. check_eq. Qed.

(** One more call of the census, on another descriptor: curl's multi
    wait polls its wakeup eventfd for POLLIN with a timeout and gets 0
    (census shape 33).  This holds since wave two, which added the
    eventfd; it is a CONTROL of the fail-before run, true at its base. *)
Definition ppoll_eventfd_in : SyscallInput :=
  mk 73 [ws_a; 1; st_a; 0; 8]%Z
     [(ws_a, Z_to_le_bytes 4 3 ++ Z_to_le_bytes 2 1 ++ Z_to_le_bytes 2 0);
      (st_a, Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 1000000)].
Example a10_ppoll_of_the_wakeup_eventfd_returns_0 :
  option_map eff_ret (answer [(mk 19 [0; 526336]%Z [], Some (ok_eff 3))] ppoll_eventfd_in) = Some (w 0).
Proof. check_eq. Qed.

(* =========================================================================
   PART 2 — the states the calls produce
   ========================================================================= *)

(** After the removal the name is gone from the file system, which is the
    file system the exit event carries, and descriptor 3 holds the file. *)
Example removal_leaves_no_name_and_keeps_the_file :
  match run_steps tf_m0 [(create_in, Some (at_tmp (ok_eff 3))); (unlink_in, Some (at_tmp (ok_eff 0)))] with
  | Some m =>
      fs_lookup (m_fs m) (bytes_of tmp_name) = None
      /\ match fd_lookup (m_fds m) 3 with
         | Some (FdAnon _ af) => af_data af = [] /\ af_rd af = true /\ af_wr af = true
         | _ => False
         end
  | None => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.
