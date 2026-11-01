(** * LinuxProcessSem.Checks.Cases.Fs.Open — worked examples over openat (56), close (57), ftruncate (46), faccessat (48), faccessat2 (439)

    Mirrors [Sys/Fs/Open.v], which answers to Linux [fs/open.c]: this
    file holds the worked examples for the syscalls defined there, and
    no others.

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
  Prelude Fs.ReadWrite.

Example openat_live_dirfd_still_unmodeled :
  check_syscall
    (mkInput 56 [1; 8192; 0; 0; 0; 0]
       (fun a => if bv_eqb a 8192 then Some 102
                 else if bv_eqb a 8193 then Some 0 else None)
       (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret ENOENT) [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** Bit 31 is part of every one of these 32-bit arguments, and nothing
    else pins it: each truncation test uses a high half of the form
    2^32·k, which a WRONG truncation keeping only the low 31 bits would
    pass.  A whence of 2^31 + SEEK_END names no origin (-EINVAL from
    [ksys_lseek]'s [whence <= SEEK_MAX] test, fs/read_write.c,
    v6.18.46), an fd of 2^31 + 1 is not stdout, and a request of
    2^31 + TIOCGWINSZ is not TIOCGWINSZ. *)

Example openat_empty_path_enoent :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
       (fun a => if bv_eqb a 8192 then Some 0 else None)
       (fun _ => None))
    (with_copyins [(8192, 1%nat)] (mkEffect (errno_ret ENOENT) [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([], [104])] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [([], [104])] IEof)) [].
Proof. check_eq. Qed.

(** O_NONBLOCK is an IGNORED bit, on every modeled shape: the open lands
    in exactly the model the same open without it lands in.  Only a Rocq
    literal can say that, because it is an EQUALITY BETWEEN TWO FLAG
    WORDS — a real run issues one word, so it can show the
    O_NONBLOCK open succeeds but never that the two agree.  Two images
    are needed to keep every equation between two SUCCESSES: "f" is
    present for the read and clobber shapes, absent for the exclusive
    ones, which refuse an existing path.

    The second half pins the boundary the first half must not have
    dragged along.  O_RDWR is an ADMITTED access mode, so it joins
    the first half as a fifth ignored-bit equation and a fifth success;
    what stays [CheckUnmodeled] beside it is O_NOCTTY, meaningful only
    on a terminal the model does not have, and the O_RDWR spellings
    whose arms do not exist — O_RDWR|O_APPEND, O_RDWR|O_EXCL without
    O_CREAT, and O_RDWR|O_DIRECTORY ([Fs.Open.modeled_open_flags] says
    why each). *)
Example o_nonblock_is_an_ignored_open_flag :
  let open fs fl := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           mem_open_write (fun _ => None))
        (with_copyins [(8192, 2%nat)] (mkEffect 3 [] []))
        (init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof)) in
  let ok r := match r with CheckOk _ _ => true | _ => false end in
  let have := [([102], [104; 105])] in
  let absent := [] in
  open have (0 + O_NONBLOCK)%Z = open have 0%Z
  /\ open have (wr_create_flags + O_NONBLOCK)%Z = open have wr_create_flags
  /\ open absent (excl_create_flags + O_NONBLOCK)%Z
     = open absent excl_create_flags
  /\ open absent (excl_create_flags + O_TRUNC + O_NONBLOCK)%Z
     = open absent (excl_create_flags + O_TRUNC)%Z
  /\ open have (O_RDWR + O_NONBLOCK)%Z = open have O_RDWR
  (* every one of those five is a SUCCESS at fd 3, not two matching refusals *)
  /\ ok (open have (0 + O_NONBLOCK)%Z) = true
  /\ ok (open have (wr_create_flags + O_NONBLOCK)%Z) = true
  /\ ok (open absent (excl_create_flags + O_NONBLOCK)%Z) = true
  /\ ok (open absent (excl_create_flags + O_TRUNC + O_NONBLOCK)%Z) = true
  /\ ok (open have (O_RDWR + O_NONBLOCK)%Z) = true
  (* and the flags next to them are still declined, O_NONBLOCK or not *)
  /\ open have 256%Z = CheckUnmodeled                     (* O_NOCTTY *)
  /\ open have (256 + O_NONBLOCK)%Z = CheckUnmodeled      (* O_NOCTTY|O_NONBLOCK *)
  /\ open have 1024%Z = CheckUnmodeled                    (* O_APPEND *)
  /\ open have (O_RDWR + O_APPEND)%Z = CheckUnmodeled     (* O_RDWR|O_APPEND *)
  /\ open have (O_RDWR + O_EXCL)%Z = CheckUnmodeled       (* O_EXCL without O_CREAT *)
  /\ open have (O_RDWR + O_DIRECTORY)%Z = CheckUnmodeled. (* O_RDWR|O_DIRECTORY *)
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE APPEND CREATE SHAPE, as three equalities and four declines.

    The first equality is the one only a Rocq literal can state, for the
    reason the O_NONBLOCK example above gives: it is an equality BETWEEN
    TWO FLAG WORDS, and a real run issues one word.

    The other two are what separates this shape from the clobbering one,
    and they are the reason the arm exists: on a path that is ALREADY
    THERE the open succeeds AND leaves the bytes alone, where
    O_WRONLY|O_CREAT|O_TRUNC would have emptied the file.  Both images
    are the same one, so the pair is a real contrast rather than two
    unrelated runs.

    The declines are the O_APPEND spellings beside the modeled ones
    ([Fs.Open.modeled_open_flags] names each and says why), plus
    O_APPEND on its own, which is O_RDONLY|O_APPEND and not this
    shape.  The O_EXCL spelling is no longer among them: it has an arm
    of its own, and [openat_excl_append_flag_word] below is its
    example. *)
Example openat_append_flag_word :
  let open fs fl := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           mem_open_write (fun _ => None))
        (with_copyins [(8192, 2%nat)] (mkEffect 3 [] []))
        (init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof)) in
  let ok r := match r with CheckOk _ _ => true | _ => false end in
  let kept r := match r with
                | CheckOk m _ => fs_lookup (m_fs m) [102]
                | _ => None
                end in
  let have := [([102], [104; 105])] in
  let absent := [] in
  (* the ignored bit is ignored on this arm too *)
  open have (append_create_flags + O_NONBLOCK)%Z = open have append_create_flags
  /\ ok (open have (append_create_flags + O_NONBLOCK)%Z) = true
  (* an ABSENT path is created empty, an EXISTING one keeps its bytes *)
  /\ kept (open absent append_create_flags) = Some []
  /\ kept (open have append_create_flags) = Some [104; 105]
  (* ...where the clobbering shape empties it *)
  /\ kept (open have wr_create_flags) = Some []
  (* and the spellings next to it stay declined *)
  /\ open have (append_create_flags + O_TRUNC)%Z = CheckUnmodeled
  /\ open have (O_WRONLY + O_APPEND)%Z = CheckUnmodeled
  /\ open have (O_RDWR + O_CREAT + O_APPEND)%Z = CheckUnmodeled.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE EXCLUSIVE APPEND WORDS, O_WRONLY|O_CREAT|O_EXCL|O_APPEND with
    and without O_TRUNC, against one image so that every pair below is a
    real contrast.

    What only a Rocq literal can state, for the reason the O_NONBLOCK
    example gives (an equality BETWEEN TWO FLAG WORDS): the O_TRUNC
    spelling lands in exactly the model the plain one does, and so does
    the plain one with the ignored bits set.

    What separates the arm from its two neighbours, and is the arm's
    whole claim ([Fs.Open.is_excl_append_create]):
    - an ABSENT name is created EMPTY and the fd is the APPEND kind, at
      offset 0, where the exclusive shape hands back a [FdFileW];
    - an EXISTING name is -EEXIST and only -EEXIST: the open that
      succeeds there and the injectable -EMFILE are both refused, where
      the append shape opens it and keeps its bytes;
    - "." is -EEXIST and nothing else, the answer [do_open] gives at
      its O_EXCL test before [d_is_dir] (fs/namei.c, Linux v6.18.46):
      -EISDIR, the descriptor and -ENOENT are all refused.
    The creation, unlike the -EEXIST, does admit an [openat_errnos]
    alternative. *)
Example openat_excl_append_flag_word :
  let open fs pathm fl eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           pathm (fun _ => None))
        (with_copyins [(8192, 2%nat)] eff)
        (init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof)) in
  let dot := fun a => if bv_eqb a 8192 then Some 46
                      else if bv_eqb a 8193 then Some 0 else None in
  let have := [([102], [104; 105])] in
  let absent := [] in
  let base fs := init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof) in
  let fd3 := mkEffect 3 [] [] in
  let kept r := match r with
                | CheckOk m _ => fs_lookup (m_fs m) [102]
                | _ => None
                end in
  let kind r := match r with
                | CheckOk m _ => fd_lookup (m_fds m) 3
                | _ => None
                end in
  (* the O_TRUNC spelling and the ignored bits change nothing *)
  open absent mem_open_write (excl_append_create_flags + O_TRUNC)%Z fd3
    = open absent mem_open_write excl_append_create_flags fd3
  /\ open absent mem_open_write
       (excl_append_create_flags + O_CLOEXEC + O_LARGEFILE + O_NONBLOCK)%Z fd3
     = open absent mem_open_write excl_append_create_flags fd3
  (* an ABSENT name: created empty, and the fd is the APPEND kind *)
  /\ kept (open absent mem_open_write excl_append_create_flags fd3) = Some []
  /\ kind (open absent mem_open_write excl_append_create_flags fd3)
     = Some (FdFileA [102] 0)
  (* ...where the exclusive shape mints the plain write-only kind *)
  /\ kind (open absent mem_open_write excl_create_flags fd3)
     = Some (FdFileW [102] 0)
  (* and the creation may still fail with an injectable errno *)
  /\ open absent mem_open_write excl_append_create_flags
       (mkEffect (errno_ret ENOMEM) [] [])
     = CheckOk (base absent) []
  (* an EXISTING name: -EEXIST, deterministically *)
  /\ open have mem_open_write excl_append_create_flags
       (mkEffect (errno_ret EEXIST) [] [])
     = CheckOk (base have) []
  /\ open have mem_open_write (excl_append_create_flags + O_TRUNC)%Z
       (mkEffect (errno_ret EEXIST) [] [])
     = CheckOk (base have) []
  /\ open have mem_open_write excl_append_create_flags fd3 = CheckReject
  /\ open have mem_open_write excl_append_create_flags
       (mkEffect (errno_ret EMFILE) [] [])
     = CheckReject
  (* ...where the append shape opens it, bytes intact *)
  /\ kept (open have mem_open_write append_create_flags fd3)
     = Some [104; 105]
  (* "." is -EEXIST, v6.18.46's answer, and only that *)
  /\ open absent dot excl_append_create_flags
       (mkEffect (errno_ret EEXIST) [] [])
     = CheckOk (base absent) []
  /\ open absent dot excl_append_create_flags
       (mkEffect (errno_ret EISDIR) [] [])
     = CheckReject
  /\ open absent dot excl_append_create_flags fd3 = CheckReject
  /\ open absent dot excl_append_create_flags
       (mkEffect (errno_ret ENOENT) [] [])
     = CheckReject
  (* ...where the append shape, with no O_EXCL, is -EISDIR alone *)
  /\ open absent dot append_create_flags (mkEffect (errno_ret EISDIR) [] [])
     = CheckOk (base absent) []
  /\ open absent dot append_create_flags (mkEffect (errno_ret EEXIST) [] [])
     = CheckReject
  (* the read-write spelling of the same bits is still declined *)
  /\ open absent mem_open_write (O_RDWR + O_CREAT + O_EXCL + O_APPEND)%Z fd3
     = CheckUnmodeled.
Proof. vm_compute. repeat split; check_eq. Qed.

(** THE SIX READ-WRITE WORDS, as the table the two bits decide.

    A real run issues one word, so every equation here that relates
    TWO flag words is one only a Rocq literal can state; and the
    file-content contrasts are stated against ONE image, so a pair is a
    real contrast rather than two unrelated runs.

    What the table says, and it is exactly [Fs.Open.openat_rdwr_spec]'s
    claim: O_TRUNC decides whether an EXISTING file keeps its bytes, and
    O_CREAT what an ABSENT name gets.  The declines beside them are the
    O_RDWR spellings [Fs.Open.modeled_open_flags] names and does not
    admit. *)
Example openat_rdwr_flag_words :
  let open fs fl := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           mem_open_write (fun _ => None))
        (with_copyins [(8192, 2%nat)] (mkEffect 3 [] []))
        (init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof)) in
  let ok r := match r with CheckOk _ _ => true | _ => false end in
  let kept r := match r with
                | CheckOk m _ => fs_lookup (m_fs m) [102]
                | _ => None
                end in
  let have := [([102], [104; 105])] in
  let absent := [] in
  (* the ignored bit is ignored on this arm too *)
  open have (O_RDWR + O_NONBLOCK)%Z = open have O_RDWR
  /\ ok (open have O_RDWR) = true
  (* O_TRUNC decides what an EXISTING file keeps *)
  /\ kept (open have O_RDWR) = Some [104; 105]
  /\ kept (open have (O_RDWR + O_TRUNC)%Z) = Some []
  /\ kept (open have (O_RDWR + O_CREAT)%Z) = Some [104; 105]
  /\ kept (open have (O_RDWR + O_CREAT + O_TRUNC)%Z) = Some []
  (* O_CREAT decides what an ABSENT one gets: a fresh empty file on the
     three words that carry it, and nothing at all on the two that do
     not (those answer -ENOENT, below) *)
  /\ kept (open absent (O_RDWR + O_CREAT)%Z) = Some []
  /\ kept (open absent (O_RDWR + O_CREAT + O_TRUNC)%Z) = Some []
  /\ kept (open absent rdwr_excl_create_flags) = Some []
  /\ kept (open absent (rdwr_excl_create_flags + O_TRUNC)%Z) = Some []
  (* and the fd it hands back is the READ-WRITE kind, at offset 0 *)
  /\ match open have O_RDWR with
     | CheckOk m _ => fd_lookup (m_fds m) 3 = Some (FdFileRW [102] 0)
     | _ => False
     end
  (* the spellings beside them stay declined *)
  /\ open have (O_RDWR + O_APPEND)%Z = CheckUnmodeled
  /\ open have (O_RDWR + O_CREAT + O_APPEND)%Z = CheckUnmodeled
  /\ open have (O_RDWR + O_EXCL)%Z = CheckUnmodeled
  /\ open have (O_RDWR + O_TRUNC + O_EXCL)%Z = CheckUnmodeled
  /\ open have (O_RDWR + O_DIRECTORY)%Z = CheckUnmodeled.
Proof. vm_compute. repeat split; check_eq. Qed.

(** THE ERRNO HALF OF THE SAME TABLE, and the -EMFILE reject twins that
    pin it as DETERMINISTIC.

    Two answers here admit an [Fs.Open.openat_errnos] alternative and
    two do not, and no real run can separate them: a run is shown one
    answer, and the claim is that a kernel offering a DIFFERENT one is
    refused.  An open that can succeed may instead report the -EMFILE a
    real kernel raises before path resolution; an arm that reports a
    path-resolution errno insists on it, which is the approximation
    [Fs.Open.openat_spec]'s header records and the reason its
    hand-maintained list wants a twin per arm. *)
Example openat_rdwr_errnos :
  let open fs fl eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           mem_open_write (fun _ => None))
        (with_copyins [(8192, 2%nat)] eff)
        (init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof)) in
  let have := [([102], [104; 105])] in
  let absent := [] in
  let base fs := init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof) in
  (* no O_CREAT and no such name: the kernel's own -ENOENT *)
  open absent O_RDWR (mkEffect (errno_ret ENOENT) [] [])
    = CheckOk (base absent) []
  /\ open absent (O_RDWR + O_TRUNC)%Z (mkEffect (errno_ret ENOENT) [] [])
     = CheckOk (base absent) []
  (* the exclusive words on a name that IS there: -EEXIST *)
  /\ open have rdwr_excl_create_flags (mkEffect (errno_ret EEXIST) [] [])
     = CheckOk (base have) []
  (* those three are deterministic, so a kernel that answered -EMFILE
     instead is REJECTED rather than admitted *)
  /\ open absent O_RDWR (mkEffect (errno_ret EMFILE) [] []) = CheckReject
  /\ open have rdwr_excl_create_flags (mkEffect (errno_ret EMFILE) [] [])
     = CheckReject
  (* while an open that can SUCCEED admits it *)
  /\ open have O_RDWR (mkEffect (errno_ret EMFILE) [] []) = CheckOk (base have) []
  /\ open absent (O_RDWR + O_CREAT)%Z (mkEffect (errno_ret ENOMEM) [] [])
     = CheckOk (base absent) [].
Proof. vm_compute. repeat split; check_eq. Qed.

(** A DIRECTORY REFERENCE, whose two answers come from two different
    kernel tests reached in the same call.  "." is [Uapi.dot_path]; the
    path bytes at 8192 are '.', NUL.

    Without O_CREAT nothing in [do_open]'s O_CREAT block runs and the
    -EISDIR is [may_open]'s S_IFDIR arm under [acc_mode & MAY_WRITE],
    which O_RDWR carries through [ACC_MODE] (fs/namei.c and fs/open.c,
    Linux v6.18.46).  With O_CREAT it is [do_open]'s own
    [d_is_dir(nd->path.dentry)] — unless O_EXCL is set, which is tested
    first and answers -EEXIST.  No real run separates the two -EISDIRs, and
    the -EEXIST is the one a reader gets backwards. *)
Example openat_rdwr_dirref :
  let open fl e := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           (fun a => if bv_eqb a 8192 then Some 46
                     else if bv_eqb a 8193 then Some 0 else None)
           (fun _ => None))
        (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret e) [] []))
        (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) in
  let base := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) in
  open O_RDWR EISDIR = CheckOk base []
  /\ open (O_RDWR + O_TRUNC)%Z EISDIR = CheckOk base []
  /\ open (O_RDWR + O_CREAT)%Z EISDIR = CheckOk base []
  /\ open (O_RDWR + O_CREAT + O_TRUNC)%Z EISDIR = CheckOk base []
  /\ open rdwr_excl_create_flags EEXIST = CheckOk base []
  (* the exclusive word does NOT answer -EISDIR, and none of the other
     four answers -EEXIST *)
  /\ open rdwr_excl_create_flags EISDIR = CheckReject
  /\ open O_RDWR EEXIST = CheckReject.
Proof. vm_compute. repeat split; check_eq. Qed.

(** The interpreted file system, end to end: openat(AT_FDCWD, "f",
    O_WRONLY|O_CREAT|O_TRUNC, 0644) creating "f" (path bytes at 8192:
    'f', NUL), then write(3, "hi", 2) — and the file contents appear in
    the final model.  This is the readable statement of what the model
    does. *)

Definition ftruncate_dangling_model : Model :=
  mkModel [(3, FdFileW [102] 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    [] None None None.

Example ftruncate_on_a_dangling_fd_is_unmodeled :
  check_syscall (mkInput 46 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) ftruncate_dangling_model
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(* ======================================== close (57), ftruncate (46) on
   a stream-pair end *)

(** One AF_UNIX stream pair, id 0: side [false] at fd 3 holds two bytes
    its peer wrote and nobody has read, side [true] at fd 4 holds
    nothing.  Both ends block and neither is shut down; the buffer sizes
    are [State.default_kernel]'s, and nothing below reads them. *)
Definition close_pair_end (rx : list byte) : StreamEnd :=
  mkStreamEnd rx false 212992%Z 212992%Z false false.

Definition close_pair_model : Model :=
  mkModel [(0, FdChannel 0); (1, FdChannel 1);
           (3, FdStream 0 false (close_pair_end [104; 105]));
           (4, FdStream 0 true (close_pair_end []))]
    (mkVmMaps [] [] 0 0 demo_limit) IEof [] None None None.

(** CLOSING AN END MOVES NOTHING BUT ITS OWN ENTRY: [Open.close_spec]
    is kind-blind on a stream-pair end too, and the survivor at fd 4
    keeps its entry exactly as it was -- it reads its peer's close off
    the table ([State.stream_peer] is [None]), not off its own state.
    A close that wrote [SHUTDOWN_MASK] into the survivor, as
    [unix_release_sock] does, fails this line. *)
Example close_of_a_stream_end_moves_only_its_entry :
  check_syscall (mkInput 57 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) close_pair_model
  = CheckOk (with_fds [(0, FdChannel 0); (1, FdChannel 1);
                       (4, FdStream 0 true (close_pair_end []))] close_pair_model) [].
Proof. check_eq. Qed.

(** ftruncate on a stream-pair end is -EINVAL: the inode is S_ISSOCK,
    and [do_ftruncate]'s [!S_ISREG] test answers before FMODE_WRITE is
    read.  The 0 is the reject twin. *)
Example ftruncate_on_a_stream_end_is_einval :
  check_syscall (mkInput 46 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) close_pair_model
  = CheckOk close_pair_model []
  /\ check_syscall (mkInput 46 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) close_pair_model
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(* ================================================ faccessat (48)

   Four claims.  One needs a file-system image no modeled syscall can
   build.  The other three are the mode-before-pathname order and its
   ledger halves — an -EINVAL that read nothing, a 0 that must have. *)

(** Path bytes at 8192 for the faccessat examples: 'a', NUL. *)
Definition fa_mem_name_a : word -> option byte :=
  fun a => if bv_eqb a 8192 then Some 97        (* 'a' *)
           else if bv_eqb a 8193 then Some 0    (* NUL *)
           else None.

(** A key living UNDER a name means reality has a DIRECTORY the flat map
    only implies, and F_OK of a directory is 0 where the map would answer
    -ENOENT.  So [Fs.Namei.fs_under] declines it.  This is the one
    faccessat decline only the starting image can set up: no modeled
    syscall puts a separator in a key.  The guard [unlinkat] uses to avoid a wrong ERRNO is used
    here to avoid a wrong exists-or-not. *)
Example faccessat_implied_directory_unmodeled :
  check_syscall
    (mkInput 48 [AT_FDCWD; 8192; 0; 0; 0; 0] fa_mem_name_a (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect 0 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], []); ([97; 47; 98], [104])] IEof))
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** The contrast, so the guard is a COMPONENT prefix and not a byte
    prefix: "ab" does not live under "a", so "a" is an ordinary present
    key and F_OK of it is 0, with the model left exactly as it was —
    faccessat changes nothing. *)
Example faccessat_byte_prefix_is_not_a_directory :
  match check_syscall
          (mkInput 48 [AT_FDCWD; 8192; 0; 0; 0; 0] fa_mem_name_a (fun _ => None))
          (with_copyins [(8192, 2%nat)] (mkEffect 0 [] []))
          (init_model [] 0 0 demo_sp demo_limit
             (demo_input [([97], []); ([97; 98], [104])] IEof)) with
  | CheckOk m [] => m_fs m = [([97], []); ([97; 98], [104])]
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** THE MODE BEATS THE PATHNAME FETCH, which is the sharpest claim
    [Fs.Open.faccessat_spec] makes: fs/open.c [do_faccessat] (v6.18.46)
    tests [mode & ~S_IRWXO] before [getname], so a bad mode with an
    UNREADABLE path is -EINVAL and never -EFAULT.  Here the pathname is
    at an address no byte answers at, and the answer is still -EINVAL with an
    empty ledger.  A spec that fetched first would answer -EFAULT and
    this would reject. *)
Example faccessat_bad_mode_beats_an_unreadable_path :
  check_syscall
    (mkInput 48 [AT_FDCWD; 8192; 8; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] [])
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], [])] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], [])] IEof)) [].
Proof. vm_compute. reflexivity. Qed.

(** ...and because the mode is decided before [user_path_at], that arm
    reads NO user memory: a ledger claimed there is a read the kernel did
    not perform.  This is the case a spec that wrapped the whole body in
    [record_copyins] gets wrong — it would EXPECT this range and accept. *)
Example faccessat_bad_mode_records_no_copyin :
  check_syscall
    (mkInput 48 [AT_FDCWD; 8192; 8; 0; 0; 0] fa_mem_name_a (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EINVAL) [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], [])] IEof))
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** Past the mode test the ledger is REQUIRED: the F_OK call really did
    read the path, so denying it is a rejection.  These two differ in the
    mode word alone, and the ledger obligation flips with it. *)
Example faccessat_existence_needs_the_copyin :
  check_syscall
    (mkInput 48 [AT_FDCWD; 8192; 0; 0; 0; 0] fa_mem_name_a (fun _ => None))
    (mkEffect 0 [] [])
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], [])] IEof))
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(* ================================ openat's flat-namespace declines

   [Fs.Open.openat_resolved_spec] declines a pathname with a separator
   in it, because the flat file system has no path walk and so cannot
   reach any of the answers one produces; ".." it ANSWERS, being a
   directory reference the walk settles on its own, and so do the two
   paths [Fs.Open.openat_sep_spec] names: /etc/localtime, on a declared
   assumption rather than a walk, and /dev/null, whose answers come from
   its driver (their examples follow the declines).  These are claims
   about that boundary which a real run cannot make: a run cannot vary
   the KERNEL'S answer (it gets the one the kernel gives) or build a
   file-system image whose keys hold a separator (no modeled syscall
   puts one there). *)

(** Path bytes at 8192, NUL-terminated, for the examples below. *)
Definition open_path_mem (bs : list Z) : word -> option byte :=
  fun a => if (8192 <=? bv_unsigned a)%Z
           then nth_error (map (fun z => Z_to_bv 8 z) (bs ++ [0%Z]))
                  (Z.to_nat (bv_unsigned a - 8192))
           else None.

(** THE DECLINE DOES NOT DEPEND ON WHAT THE KERNEL SAID, which is the
    half no real run reaches: a run is shown one answer, and the claim
    here is over two that could not both be right.  The write-create
    open of "/a" is [CheckUnmodeled] when the kernel is offered as having
    SUCCEEDED at fd 3 and when it is offered as having failed -ENOENT —
    so the model is not quietly agreeing with one of them.

    Without the guard the first of these would be [CheckOk]: a create
    that tested the pathname against "." and nothing else would bind
    fd 3 and record a key literally spelled "/a" where Linux resolves a
    directory it never looked in.  That is the unsound admission this
    guard prevents, and it is why the pair below is stated as a pair. *)
Example openat_absolute_create_unmodeled :
  let open eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 wr_create_flags; 420; 0; 0]
           (open_path_mem [47%Z; 97%Z]) (fun _ => None))
        (with_copyins [(8192, 3%nat)] eff)
        (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) in
  open (mkEffect 3 [] []) = CheckUnmodeled
  /\ open (mkEffect (errno_ret ENOENT) [] []) = CheckUnmodeled.
Proof. vm_compute. split; reflexivity. Qed.

(** THE CONTROL, and the reason the pair above is evidence of anything.
    The identical call on a slash-free name is not declined: it succeeds
    at the lowest free fd and the key appears in the model's file system.
    So the guard discriminates on the PATH SHAPE — it does not disable
    the create arm, and a run of nothing but declines would not show
    that. *)
Example openat_plain_create_still_mints_the_key :
  match check_syscall
          (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 wr_create_flags; 420; 0; 0]
             (open_path_mem [97%Z]) (fun _ => None))
          (with_copyins [(8192, 2%nat)] (mkEffect 3 [] []))
          (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) with
  | CheckOk m [] => m_fs m = [([Z_to_bv 8 97], [])]
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(* ================================ an implied directory under the create words

   [Fs.Open.openat_create_spec] and its siblings test
   [path_is_dirref p || fs_under (m_fs m) p]: a plain name some key of
   the image lives under is a directory the flat map only implies, and
   an O_CREAT open of it is the deterministic answer [do_open] gives a
   positive directory dentry — -EEXIST under O_EXCL, -EISDIR otherwise
   (fs/namei.c, Linux v6.18.46).  No modeled syscall creates a
   directory, so only the starting image can set this up, and the
   `reject` half of each claim is pinned here as a literal beside the
   accepted answer. *)

(** THE CLOBBERING CREATE OF AN IMPLIED DIRECTORY IS -EISDIR, and the
    model is untouched by it: with "a/b" in the image, the
    O_WRONLY|O_CREAT|O_TRUNC open of "a" accepts -EISDIR, REFUSES the
    descriptor the kernel could be offered as having minted (the answer
    before this arm), and the control — the same call on "c", which
    nothing lives under — still creates its key. *)
Example openat_implied_directory_create_eisdir :
  let m0 fs := init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof) in
  let under := [([Z_to_bv 8 97; Z_to_bv 8 47; Z_to_bv 8 98], [104])] in
  let open name eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 wr_create_flags; 420; 0; 0]
           (open_path_mem [name]) (fun _ => None))
        (with_copyins [(8192, 2%nat)] eff) (m0 under) in
  open 97%Z (mkEffect (errno_ret EISDIR) [] []) = CheckOk (m0 under) []
  /\ open 97%Z (mkEffect 3 [] []) = CheckReject
  /\ match open 99%Z (mkEffect 3 [] []) with
     | CheckOk m [] => m_fs m = fs_set under [Z_to_bv 8 99] []
     | _ => False
     end.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE TEST IS A COMPONENT PREFIX, NOT A BYTE PREFIX, AND NOT EQUALITY.
    [Fs.Namei.fs_under] asks whether some key continues [p] with a
    separator, so an image holding "ab" does not make "a" a directory —
    the create of "a" mints its key beside "ab", as before — and an
    image holding "a" itself is the ordinary truncating create, the file
    emptied and no -EISDIR: the offered -EISDIR is refused on both.  The
    openat twin of [faccessat_byte_prefix_is_not_a_directory]. *)
Example openat_byte_prefix_and_exact_key_still_create :
  let m0 fs := init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof) in
  let sibling := [([Z_to_bv 8 97; Z_to_bv 8 98], [104])] in
  let exact := [([Z_to_bv 8 97], [104])] in
  let open fs eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 wr_create_flags; 420; 0; 0]
           (open_path_mem [97%Z]) (fun _ => None))
        (with_copyins [(8192, 2%nat)] eff) (m0 fs) in
  match open sibling (mkEffect 3 [] []) with
  | CheckOk m [] => m_fs m = fs_set sibling [Z_to_bv 8 97] []
  | _ => False
  end
  /\ open sibling (mkEffect (errno_ret EISDIR) [] []) = CheckReject
  /\ match open exact (mkEffect 3 [] []) with
     | CheckOk m [] => m_fs m = [([Z_to_bv 8 97], [])]
     | _ => False
     end
  /\ open exact (mkEffect (errno_ret EISDIR) [] []) = CheckReject.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE EXCLUSIVE CREATE OF AN IMPLIED DIRECTORY IS -EEXIST, not
    -EISDIR: [do_open] tests O_EXCL against [FMODE_CREATED] before it
    tests [d_is_dir], the same order that makes "." -EEXIST under this
    word.  The descriptor is refused, and the control on "c" creates. *)
Example openat_implied_directory_excl_eexist :
  let m0 fs := init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof) in
  let under := [([Z_to_bv 8 97; Z_to_bv 8 47; Z_to_bv 8 98], [104])] in
  let open name eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 excl_create_flags; 420; 0; 0]
           (open_path_mem [name]) (fun _ => None))
        (with_copyins [(8192, 2%nat)] eff) (m0 under) in
  open 97%Z (mkEffect (errno_ret EEXIST) [] []) = CheckOk (m0 under) []
  /\ open 97%Z (mkEffect 3 [] []) = CheckReject
  /\ match open 99%Z (mkEffect 3 [] []) with
     | CheckOk m [] => m_fs m = fs_set under [Z_to_bv 8 99] []
     | _ => False
     end.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE OTHER WRITE-CAPABLE WORDS AGREE, each through its own arm: the
    append shape and the read-write shapes with and without O_CREAT and
    O_TRUNC answer -EISDIR (the O_CREAT-free ones through [may_open]'s
    S_IFDIR arm rather than [do_open]'s [d_is_dir], the same errno by
    a different route), and the two other exclusive shapes, read-write
    and append, answer -EEXIST.  The exclusive append word is the one
    whose O_EXCL-free neighbour answers -EISDIR on the same image, so
    its -EISDIR is refused beside its -EEXIST. *)
Example openat_implied_directory_other_write_words :
  let m0 fs := init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof) in
  let under := [([Z_to_bv 8 97; Z_to_bv 8 47; Z_to_bv 8 98], [104])] in
  let open fl eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           (open_path_mem [97%Z]) (fun _ => None))
        (with_copyins [(8192, 2%nat)] eff) (m0 under) in
  open append_create_flags (mkEffect (errno_ret EISDIR) [] []) = CheckOk (m0 under) []
  /\ open (O_RDWR + O_CREAT)%Z (mkEffect (errno_ret EISDIR) [] []) = CheckOk (m0 under) []
  /\ open (O_RDWR + O_CREAT + O_TRUNC)%Z (mkEffect (errno_ret EISDIR) [] []) = CheckOk (m0 under) []
  /\ open O_RDWR (mkEffect (errno_ret EISDIR) [] []) = CheckOk (m0 under) []
  /\ open (O_RDWR + O_TRUNC)%Z (mkEffect (errno_ret EISDIR) [] []) = CheckOk (m0 under) []
  /\ open rdwr_excl_create_flags (mkEffect (errno_ret EEXIST) [] []) = CheckOk (m0 under) []
  /\ open excl_append_create_flags (mkEffect (errno_ret EEXIST) [] []) = CheckOk (m0 under) []
  /\ open excl_append_create_flags (mkEffect (errno_ret EISDIR) [] []) = CheckReject
  /\ open excl_append_create_flags (mkEffect 3 [] []) = CheckReject
  /\ open (O_RDWR + O_CREAT)%Z (mkEffect 3 [] []) = CheckReject.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** A KEY SPELLED WITH A SEPARATOR comes only from the starting image —
    no modeled syscall puts a separator in a key — and it is the one
    where answering would look
    most defensible: the map HOLDS "a/b", so a read of "a/b" could just
    return it.  It is declined anyway, because whether that key is
    reachable depends on "a" being a directory, which the map does not
    say.  The same guard, and the same reason, as
    [faccessat_implied_directory_unmodeled] above. *)
Example openat_slash_key_in_image_unmodeled :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
       (open_path_mem [97%Z; 47%Z; 98%Z]) (fun _ => None))
    (with_copyins [(8192, 4%nat)] (mkEffect 3 [] []))
    (init_model [] 0 0 demo_sp demo_limit
       (demo_input [([Z_to_bv 8 97; Z_to_bv 8 47; Z_to_bv 8 98], [104])] IEof))
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(* ================================ "/etc/localtime", the answered exception

   [Fs.Open.openat_localtime_spec] answers -ENOENT for exactly this path
   under a MAINTAINER-DECLARED assumption about the image (the image has
   no /etc/localtime), and fails closed wherever
   the assumption does not reach.  These pin both halves, and the edges
   of the byte string the assumption was declared for. *)

(** The bytes of "/etc/localtime". *)
Definition localtime_bytes : list Z :=
  [47; 101; 116; 99; 47; 108; 111; 99; 97; 108; 116; 105; 109; 101]%Z.

(** THE -ENOENT IS AN ANSWER, NOT A DECLINE, and the model insists on
    it: every O_CREAT-free word the model interprets is a [CheckOk] in
    the unchanged model when the kernel reports -ENOENT, and a kernel
    that reports a descriptor instead is REJECTED.  The
    O_CLOEXEC|O_NONBLOCK row is the word musl's [__map_file] issues for
    this path (musl 1.2.6, src/time/__map_file.c); both bits are in
    [Fs.Open.open_ignored_flags], so it is the O_RDONLY arm.  Beside
    them, every word with O_CREAT is [CheckUnmodeled]: Linux would
    create the file under /etc, and the model has no /etc to create it
    in. *)
Example openat_localtime_enoent :
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) in
  let open fl eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           (open_path_mem localtime_bytes) (fun _ => None))
        (with_copyins [(8192, 15%nat)] eff) m0 in
  let enoent := mkEffect (errno_ret ENOENT) [] [] in
  (* without O_CREAT: -ENOENT, an Ok, whatever the access mode *)
  open 0%Z enoent = CheckOk m0 []
  /\ open (0 + O_CLOEXEC)%Z enoent = CheckOk m0 []
  /\ open (O_CLOEXEC + O_NONBLOCK)%Z enoent = CheckOk m0 []
  /\ open O_RDWR enoent = CheckOk m0 []
  /\ open (O_RDWR + O_TRUNC)%Z enoent = CheckOk m0 []
  /\ open O_DIRECTORY enoent = CheckOk m0 []
  (* a claimed success is refused: the answer is deterministic *)
  /\ open 0%Z (mkEffect 3 [] []) = CheckReject
  /\ open 0%Z (mkEffect (errno_ret EACCES) [] []) = CheckReject
  (* with O_CREAT: fail closed, in every spelling the model admits *)
  /\ open wr_create_flags enoent = CheckUnmodeled
  /\ open excl_create_flags enoent = CheckUnmodeled
  /\ open append_create_flags enoent = CheckUnmodeled
  /\ open (O_RDWR + O_CREAT)%Z enoent = CheckUnmodeled
  /\ open rdwr_excl_create_flags enoent = CheckUnmodeled
  /\ open wr_create_flags (mkEffect 3 [] []) = CheckUnmodeled.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE ASSUMPTION DOES NOT REACH AN IMAGE THAT SHIPS THE FILE.  A map
    holding the key "/etc/localtime", or a key under it, describes an
    image the declaration was not made about, and the open is declined
    rather than answered from the map — whatever the kernel is offered
    as having said, so the model is not quietly siding with one
    answer. *)
Example openat_localtime_in_image_unmodeled :
  let open fs eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; 0; 420; 0; 0]
           (open_path_mem localtime_bytes) (fun _ => None))
        (with_copyins [(8192, 15%nat)] eff)
        (init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof)) in
  let key := map (fun z => Z_to_bv 8 z) localtime_bytes in
  let enoent := mkEffect (errno_ret ENOENT) [] [] in
  open [(key, [104])] enoent = CheckUnmodeled
  /\ open [(key, [104])] (mkEffect 3 [] []) = CheckUnmodeled
  /\ open [(key ++ [Z_to_bv 8 47; Z_to_bv 8 120], [104])] enoent = CheckUnmodeled
  /\ open [(key ++ [Z_to_bv 8 47; Z_to_bv 8 120], [104])] (mkEffect 3 [] [])
     = CheckUnmodeled
  (* the control: an unrelated key leaves the answer in place *)
  /\ open [([Z_to_bv 8 97], [104])] enoent
     = CheckOk (init_model [] 0 0 demo_sp demo_limit
                  (demo_input [([Z_to_bv 8 97], [104])] IEof)) [].
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE MATCH IS EXACT.  Linux resolves "/etc//localtime" and
    "//etc/localtime" to the same file, and a prefix or an extension of
    the name to a different one; the model identifies none of them with
    the declared path, so each is the separator decline the arm sits in
    front of.  The last conjunct is the control that keeps the others
    from being satisfied by a model that declines everything. *)
Example openat_localtime_match_is_exact :
  let open bs n := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; 0; 420; 0; 0]
           (open_path_mem bs) (fun _ => None))
        (with_copyins [(8192, n)] (mkEffect (errno_ret ENOENT) [] []))
        (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) in
  open ([47; 101; 116; 99; 47; 47; 108; 111; 99; 97; 108; 116; 105; 109; 101]%Z)
       16%nat = CheckUnmodeled
  /\ open ([47; 47; 101; 116; 99; 47; 108; 111; 99; 97; 108; 116; 105; 109; 101]%Z)
       16%nat = CheckUnmodeled
  /\ open ([47; 101; 116; 99; 47; 108; 111; 99; 97; 108; 116; 105; 109]%Z)
       14%nat = CheckUnmodeled
  /\ open (localtime_bytes ++ [115%Z]) 16%nat = CheckUnmodeled
  /\ open localtime_bytes 15%nat
     = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [].
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ================================ "/dev/null", the answered device

   [Fs.Open.openat_devnull_spec] answers the exact byte string
   "/dev/null" ahead of the separator decline and mints
   [State.FdDevNull], the kind whose every answer comes from
   [null_fops] (drivers/char/mem.c) rather than from the file system.
   These pin the open under each admitted word, the open, write, read,
   close sequence, and the answers the
   kind forces at every fd-kind dispatch site outside fs/open.c, which
   have nowhere else to be pinned. *)

(** The bytes of "/dev/null". *)
Definition devnull_bytes : list Z := [47; 100; 101; 118; 47; 110; 117; 108; 108]%Z.

Definition devnull_m0 : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof).

(** THE OPEN, under every admitted word.  The access mode the word
    names is what the entry records; the O_TRUNC of the clobbering word
    and the O_APPEND of the append word are inert on the device, so both
    mint the write-only entry; the O_EXCL words are -EEXIST and the
    O_DIRECTORY word -ENOTDIR, deterministically (a claimed success is
    rejected on those two); and the image is untouched by every one of
    them, which is the whole point of a device over a key. *)
Example devnull_open_by_word :
  let open fl eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           (open_path_mem devnull_bytes) (fun _ => None))
        (with_copyins [(8192, 10%nat)] eff) devnull_m0 in
  let minted fl rd wr :=
        match open fl (mkEffect 3 [] []) with
        | CheckOk m [] => fd_lookup (m_fds m) 3 = Some (FdDevNull rd wr)
                          /\ m_fs m = []
        | _ => False
        end in
  minted 0%Z true false
  /\ minted (0 + O_CLOEXEC)%Z true false
  /\ minted wr_create_flags false true
  /\ minted append_create_flags false true
  /\ minted O_RDWR true true
  /\ minted (O_RDWR + O_CREAT + O_TRUNC)%Z true true
  /\ open excl_create_flags (mkEffect (errno_ret EEXIST) [] []) = CheckOk devnull_m0 []
  /\ open rdwr_excl_create_flags (mkEffect (errno_ret EEXIST) [] []) = CheckOk devnull_m0 []
  /\ open excl_append_create_flags (mkEffect (errno_ret EEXIST) [] []) = CheckOk devnull_m0 []
  /\ open (excl_append_create_flags + O_TRUNC)%Z (mkEffect (errno_ret EEXIST) [] [])
     = CheckOk devnull_m0 []
  /\ open O_DIRECTORY (mkEffect (errno_ret ENOTDIR) [] []) = CheckOk devnull_m0 []
  /\ open excl_create_flags (mkEffect 3 [] []) = CheckReject
  /\ open excl_append_create_flags (mkEffect 3 [] []) = CheckReject
  /\ open O_DIRECTORY (mkEffect 3 [] []) = CheckReject.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE ASSUMPTION DOES NOT REACH AN IMAGE THAT SHIPS A FILE UNDER THE
    NAME, or a key under it, and THE MATCH IS EXACT: each of those is the
    ordinary separator decline, whatever the kernel is offered as having
    said.  The last conjunct is the control. *)
Example devnull_open_declines :
  let open fs bs n eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; 0; 420; 0; 0]
           (open_path_mem bs) (fun _ => None))
        (with_copyins [(8192, n)] eff)
        (init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof)) in
  let key := map (fun z => Z_to_bv 8 z) devnull_bytes in
  open [(key, [104])] devnull_bytes 10%nat (mkEffect 3 [] []) = CheckUnmodeled
  /\ open [(key, [104])] devnull_bytes 10%nat (mkEffect (errno_ret ENOENT) [] [])
     = CheckUnmodeled
  /\ open [(key ++ [Z_to_bv 8 47; Z_to_bv 8 120], [104])] devnull_bytes 10%nat
       (mkEffect 3 [] []) = CheckUnmodeled
  /\ open [] ([47; 100; 101; 118; 47; 47; 110; 117; 108; 108]%Z) 11%nat
       (mkEffect 3 [] []) = CheckUnmodeled
  /\ open [] ([47; 100; 101; 118; 47; 110; 117; 108]%Z) 9%nat
       (mkEffect 3 [] []) = CheckUnmodeled
  /\ (match open [] devnull_bytes 10%nat (mkEffect 3 [] []) with
      | CheckOk _ [] => True | _ => False end).
Proof. vm_compute. repeat split; reflexivity. Qed.

(** A table with one descriptor of each access mode, for the dispatch
    sites below: 3 read-only, 4 write-only, 5 read-write. *)
Definition devnull_model : Model :=
  mkModel [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
           (3, FdDevNull true false); (4, FdDevNull false true);
           (5, FdDevNull true true)]
    (mkVmMaps [] [] 0 0 demo_limit) IEof [] None None None.

(** THE COMMON SHAPE: open write-only, write, read, close.  The write
    returns the count from an UNMAPPED buffer with an EMPTY ledger —
    [write_null] reads no byte, so a claimed copy-in is rejected — and
    the read on the same descriptor is the kernel's -EBADF.  Then the
    read-only and read-write descriptors: a read is 0 into a buffer no
    page backs, with nothing written, and a write through the read-only
    one is -EBADF. *)
Example devnull_open_write_read_close :
  let call no args eff m := check_syscall
        (mkInput no args (fun _ => None) (fun _ => None)) eff m in
  match check_syscall
          (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 wr_create_flags; 420; 0; 0]
             (open_path_mem devnull_bytes) (fun _ => None))
          (with_copyins [(8192, 10%nat)] (mkEffect 3 [] [])) devnull_m0 with
  | CheckOk m1 [] =>
      call 64 [3; 4096; 5; 0; 0; 0] (mkEffect 5 [] []) m1 = CheckOk m1 []
      /\ call 64 [3; 4096; 5; 0; 0; 0]
           (with_copyins [(4096, 5%nat)] (mkEffect 5 [] [])) m1 = CheckReject
      /\ call 64 [3; 4096; 5; 0; 0; 0] (mkEffect 4 [] []) m1 = CheckReject
      /\ call 63 [3; 4096; 16; 0; 0; 0] (mkEffect (errno_ret EBADF) [] []) m1
         = CheckOk m1 []
      /\ call 57 [3; 0; 0; 0; 0; 0] (mkEffect 0 [] []) m1 = CheckOk devnull_m0 []
  | _ => False
  end
  /\ call 63 [3; 4096; 16; 0; 0; 0] (mkEffect 0 [] []) devnull_model
     = CheckOk devnull_model []
  /\ call 63 [5; 4096; 16; 0; 0; 0] (mkEffect 0 [] []) devnull_model
     = CheckOk devnull_model []
  /\ call 63 [3; 4096; 16; 0; 0; 0] (mkEffect 1 [(4096, [104])] [])
       devnull_model = CheckReject
  /\ call 64 [3; 4096; 5; 0; 0; 0] (mkEffect (errno_ret EBADF) [] []) devnull_model
     = CheckOk devnull_model []
  /\ call 64 [5; 4096; 5; 0; 0; 0] (mkEffect 5 [] []) devnull_model
     = CheckOk devnull_model [].
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE DISPATCH SITES.  [lseek] is 0 for every whence and offset
    ([null_lseek]), and a claimed repositioning is rejected; [pread64]
    is 0 and [pwrite64] the count at any position; [fsync] and
    [ftruncate] are -EINVAL; [getdents64] is -ENOTDIR; [dup] copies the
    entry; [fcntl] F_SETFD is 0 and F_GETFL declines; [ioctl] answers
    TCGETS with -ENOTTY (the kind's table has no [.unlocked_ioctl]) and
    still declines a request outside the terminal-only eight, and
    [flock] fails closed; [fstat] delivers, and its own example
    follows. *)
Example devnull_dispatch_sites :
  let call no args eff := check_syscall
        (mkInput no args (fun _ => None) (fun _ => None)) eff devnull_model in
  let ok eff := call 62 [5; 3; 0; 0; 0; 0] eff in
  ok (mkEffect 0 [] []) = CheckOk devnull_model []
  /\ ok (mkEffect 3 [] []) = CheckReject
  /\ call 62 [5; 7; 2; 0; 0; 0] (mkEffect 0 [] []) = CheckOk devnull_model []   (* SEEK_END *)
  /\ call 62 [5; 0; 4; 0; 0; 0] (mkEffect 0 [] []) = CheckOk devnull_model []   (* SEEK_HOLE *)
  /\ call 67 [3; 4096; 16; 100; 0; 0] (mkEffect 0 [] []) = CheckOk devnull_model []
  /\ call 68 [4; 4096; 5; 100; 0; 0] (mkEffect 5 [] []) = CheckOk devnull_model []
  /\ call 82 [4; 0; 0; 0; 0; 0] (mkEffect (errno_ret EINVAL) [] []) = CheckOk devnull_model []
  /\ call 46 [4; 0; 0; 0; 0; 0] (mkEffect (errno_ret EINVAL) [] []) = CheckOk devnull_model []
  /\ call 61 [3; 4096; 1024; 0; 0; 0] (mkEffect (errno_ret ENOTDIR) [] [])
     = CheckOk devnull_model []
  /\ (match call 23 [5; 0; 0; 0; 0; 0] (mkEffect 6 [] []) with
      | CheckOk m [] => fd_lookup (m_fds m) 6 = Some (FdDevNull true true)
      | _ => False end)
  /\ call 25 [5; F_SETFD; 1; 0; 0; 0] (mkEffect 0 [] []) = CheckOk devnull_model []
  /\ call 25 [5; F_GETFL; 0; 0; 0; 0] (mkEffect 0 [] []) = CheckUnmodeled
  /\ call 80 [5; 4096; 0; 0; 0; 0] (mkEffect 0 [] []) = CheckUnmodeled
     (* an fstat into a destination no page backs: the partial
        [copy_to_user] decline, before any byte is judged — the
        delivering arm is the example after this one *)
  /\ call 29 [5; TCGETS; 4096; 0; 0; 0] (mkEffect (errno_ret ENOTTY) [] [])
     = CheckOk devnull_model []
  /\ call 29 [5; Z_to_bv 64 21537; 4096; 0; 0; 0] (mkEffect 0 [] [])
     = CheckUnmodeled   (* FIONBIO 0x5421: outside the eight, still declined *)
  /\ call 32 [5; 2; 0; 0; 0; 0] (mkEffect 0 [] []) = CheckUnmodeled.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** A [struct stat] for the examples: the device's asserted members as
    given, zero everywhere else. *)
Definition dev_stat (mode rdev size : Z) : list byte :=
  Z_to_le_bytes 16 0 ++ Z_to_le_bytes 4 mode ++ Z_to_le_bytes 12 0
  ++ Z_to_le_bytes 8 rdev ++ Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 size
  ++ Z_to_le_bytes 72 0.

(** fstat ON /dev/null IS ANSWERED, AND THE DEVICE'S MEMBERS ARE ASSERTED.
    A delivered S_IFCHR with [st_rdev] 1:3 and a zero size is accepted
    and PINNED under [devnull_path]; the regular-file answer a plain key
    would produce (S_IFREG, the recorded length) is rejected, as
    are the right type with the wrong device number and the right device
    with a nonzero size.  A second fstat must repeat the pin's stable
    members: the same bytes are accepted again, and bytes differing in
    the inode are rejected.  The destination is 128 writable bytes at
    4096. *)
Example devnull_fstat_asserts_the_device :
  let wmem := fun a => if ((4096 <=? bv_unsigned a) && (bv_unsigned a <? 4224))%Z
                       then Some (Z_to_bv 8 0) else None in
  let call m eff := check_syscall
        (mkInput 80 [5; 4096; 0; 0; 0; 0] (fun _ => None) wmem) eff m in
  let good := dev_stat S_IFCHR DEVNULL_RDEV 0 in
  let deliver bs := mkEffect 0 [(4096, bs)] [] in
  (match call devnull_model (deliver good) with
   | CheckOk m [] =>
       statpin_lookup (m_statpins m) devnull_path = Some good
       /\ call m (deliver good) = CheckOk m []
       /\ call m (deliver (Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 7
                            ++ skipn 16 good)) = CheckReject
   | _ => False
   end)
  /\ call devnull_model (deliver (dev_stat S_IFREG 0 5)) = CheckReject
  /\ call devnull_model (deliver (dev_stat S_IFCHR 0 0)) = CheckReject
  /\ call devnull_model (deliver (dev_stat S_IFCHR DEVNULL_RDEV 5)) = CheckReject
  /\ call devnull_model (mkEffect 0 [] []) = CheckReject.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ================================ "/dev/urandom", the declared stream

   [Fs.Open.openat_urandom_spec] answers the exact byte string
   "/dev/urandom" ahead of the separator decline and mints
   [State.FdUrandom], whose reads hand out the run's DECLARED stream
   ([State.in_urandom]: arbitrary but fixed, a parameter of the
   execution like argv and envp).  These pin the open under each word,
   the open, read, close sequence with a stream long enough, the decline
   when the stream runs out, the answers at every dispatch site, the
   fstat delivery, and — the point of the declared stream — that two
   models seeded from one stream read the same bytes. *)

(** The bytes of "/dev/urandom". *)
Definition urandom_bytes : list Z :=
  [47; 100; 101; 118; 47; 117; 114; 97; 110; 100; 111; 109]%Z.

(** A declared stream from a byte list, for the fixtures. *)
Fixpoint urandom_stream (l : list Z) : InputStream :=
  match l with
  | [] => IEof
  | z :: r => ICons (Z_to_bv 8 z) (urandom_stream r)
  end.

(** A run whose device declares sixteen bytes. *)
Definition urandom_decl : list Z :=
  [17; 34; 51; 68; 85; 102; 119; 136; 153; 170; 187; 204; 221; 238; 255; 0]%Z.

Definition urandom_m0 : Model :=
  with_urandom (urandom_stream urandom_decl)
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)).

(** THE OPEN, under every word: O_RDONLY (with or without O_CLOEXEC)
    mints the read-only kind and leaves the image alone; the O_EXCL
    words are -EEXIST and the O_DIRECTORY word -ENOTDIR (a claimed
    success is rejected on both); the WRITE words — clobbering,
    appending, read-write — are declined, not answered. *)
Example urandom_open_by_word :
  let open fl eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           (open_path_mem urandom_bytes) (fun _ => None))
        (with_copyins [(8192, 13%nat)] eff) urandom_m0 in
  let minted fl :=
        match open fl (mkEffect 3 [] []) with
        | CheckOk m [] => fd_lookup (m_fds m) 3 = Some FdUrandom
                          /\ m_fs m = []
                          /\ m_urandom m = urandom_stream urandom_decl
        | _ => False
        end in
  minted 0%Z
  /\ minted (0 + O_CLOEXEC)%Z
  /\ open excl_create_flags (mkEffect (errno_ret EEXIST) [] []) = CheckOk urandom_m0 []
  /\ open rdwr_excl_create_flags (mkEffect (errno_ret EEXIST) [] []) = CheckOk urandom_m0 []
  /\ open excl_append_create_flags (mkEffect (errno_ret EEXIST) [] []) = CheckOk urandom_m0 []
  /\ open (excl_append_create_flags + O_TRUNC)%Z (mkEffect (errno_ret EEXIST) [] [])
     = CheckOk urandom_m0 []
  /\ open O_DIRECTORY (mkEffect (errno_ret ENOTDIR) [] []) = CheckOk urandom_m0 []
  /\ open excl_create_flags (mkEffect 3 [] []) = CheckReject
  /\ open excl_append_create_flags (mkEffect 3 [] []) = CheckReject
  /\ open O_DIRECTORY (mkEffect 3 [] []) = CheckReject
  /\ open wr_create_flags (mkEffect 3 [] []) = CheckUnmodeled
  /\ open append_create_flags (mkEffect 3 [] []) = CheckUnmodeled
  /\ open O_RDWR (mkEffect 3 [] []) = CheckUnmodeled
  /\ open (O_RDWR + O_CREAT + O_TRUNC)%Z (mkEffect 3 [] []) = CheckUnmodeled.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE ASSUMPTION DOES NOT REACH AN IMAGE THAT SHIPS A FILE UNDER THE
    NAME, or a key under it, and THE MATCH IS EXACT: "/dev//urandom"
    and "/dev/random" — a different device the ladder does not name —
    are the ordinary separator decline.  The last conjunct is the
    control. *)
Example urandom_open_declines :
  let open fs bs n eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; 0; 420; 0; 0]
           (open_path_mem bs) (fun _ => None))
        (with_copyins [(8192, n)] eff)
        (init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof)) in
  let key := map (fun z => Z_to_bv 8 z) urandom_bytes in
  open [(key, [104])] urandom_bytes 13%nat (mkEffect 3 [] []) = CheckUnmodeled
  /\ open [(key ++ [Z_to_bv 8 47; Z_to_bv 8 120], [104])] urandom_bytes 13%nat
       (mkEffect 3 [] []) = CheckUnmodeled
  /\ open [] ([47; 100; 101; 118; 47; 47; 117; 114; 97; 110; 100; 111; 109]%Z) 14%nat
       (mkEffect 3 [] []) = CheckUnmodeled
  /\ open [] ([47; 100; 101; 118; 47; 114; 97; 110; 100; 111; 109]%Z) 12%nat
       (mkEffect 3 [] []) = CheckUnmodeled
  /\ (match open [] urandom_bytes 13%nat (mkEffect 3 [] []) with
      | CheckOk _ [] => True | _ => False end).
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ================================ the images those three declines are about

   [openat_localtime_in_image_unmodeled], [devnull_open_declines] and
   [urandom_open_declines] above each pin what the arm does on an image
   that ships the device's name as a key: it declines.  That answer is
   the courtesy the arms' comments call it, and the pins stay — an
   [Fs.Fs] is a type, and a checker handed one of those maps really does
   answer [CheckUnmodeled].

   The other half is here: such a map is not an image a run can have.
   [Run.valid_input] carries
   [Fs.fs_keys_relative] over [State.in_image_fs], so a
   statement quantified over valid inputs never reaches those declines,
   and the pins below say so at both ends — the pathological image is
   refused by the validity predicate, and an image the predicate ADMITS
   answers the open.

   THE CONTROL IS THE POINT.  "Not a valid input" is easy to prove for
   the wrong reason: [Cases.Prelude.demo_input] has an empty argv, which
   [Run.valid_argv] already refuses, so a refutation over it would hold
   with no premise about keys at all.  So these run over a fixture with
   the one empty argument [Run.valid_argv] asks for, and each refutation
   is paired with the SAME fixture over a key that differs by the
   leading separator alone, which is admitted. *)

(** The launchable fixture: [Cases.Prelude.demo_input_tmp] with
    [Run.valid_argv]'s one empty argument, so that [Run.valid_input] of
    it turns on the image and on the declaration and on nothing else. *)
Definition image_input_tmp (fs0 tmp0 : Fs.Fs) : ProcInput :=
  (* [valid_input] asks the declared /dev/urandom stream to be infinite, so
     the image inputs declare [default_urandom] (as [Cases.Prelude]'s
     fixture does) rather than [IEof]. *)
  mkProcInput_full [[]] [] fs0 IEof demo_uid demo_gid demo_groups net_silent
                   default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48 default_urandom tmp0
                   default_kernel default_execfn true true.

Definition image_input (fs0 : Fs.Fs) : ProcInput := image_input_tmp fs0 [].

(** The three device names as keys, and the same three with the leading
    separator dropped — "dev/null", "etc/localtime", "dev/urandom",
    which are ordinary cwd-relative names a launch really can hand a
    process, separators and all. *)
Definition key_of (bs : list Z) : Fs.path := map (fun z => Z_to_bv 8 z) bs.

Definition devnull_key : Fs.path := key_of devnull_bytes.
Definition localtime_key : Fs.path := key_of localtime_bytes.
Definition urandom_key : Fs.path := key_of urandom_bytes.

Definition devnull_relative_key : Fs.path := key_of (tl devnull_bytes).
Definition localtime_relative_key : Fs.path := key_of (tl localtime_bytes).
Definition urandom_relative_key : Fs.path := key_of (tl urandom_bytes).

Ltac key_byte_neq :=
  let H := fresh in
  intros H; apply (proj2 (bv_eqb_eq _ _)) in H; vm_compute in H; discriminate.

(** [Fs.valid_fs]'s NUL-free clause, decided rather than case-split: on a
    concrete key the membership is the boolean test [State.tmp_nul_free]
    already runs, so [vm_compute] closes it. *)
Lemma not_in_bytes_of_existsb : forall (b : byte) (l : list byte),
  existsb (fun c => bv_eqb c b) l = false -> ~ In b l.
Proof.
  intros b l H Hin.
  assert (existsb (fun c => bv_eqb c b) l = true) as Hc.
  { apply existsb_exists. exists b. split; [exact Hin | apply bv_eqb_eq; reflexivity]. }
  rewrite Hc in H. discriminate.
Qed.

(** An image keyed by a device name is not [Fs.fs_keys_relative]. *)
Example device_key_images_are_not_relative :
  ~ fs_keys_relative [(devnull_key, [Z_to_bv 8 104])]
  /\ ~ fs_keys_relative [(localtime_key, [Z_to_bv 8 104])]
  /\ ~ fs_keys_relative [(urandom_key, [Z_to_bv 8 104])].
Proof.
  repeat split; intros H; apply (Forall_inv H); reflexivity.
Qed.

(** …so no run has one: the fixture over it is refused by
    [Run.valid_input], and refused THROUGH the keys clause — the
    conjunct the pattern below names is the one that fails. *)
Example device_key_inputs_are_not_valid :
  ~ valid_input (image_input [(devnull_key, [Z_to_bv 8 104])])
  /\ ~ valid_input (image_input [(localtime_key, [Z_to_bv 8 104])])
  /\ ~ valid_input (image_input [(urandom_key, [Z_to_bv 8 104])]).
Proof.
  destruct device_key_images_are_not_relative as (Hd & Hl & Hu).
  repeat split; intros (_ & _ & _ & Hk & _);
    [exact (Hd Hk) | exact (Hl Hk) | exact (Hu Hk)].
Qed.

(** THE CONTROL.  Drop the leading separator and the very same fixture
    IS valid — with a declared private /tmp beside it, so the seeded
    image really does carry the absolute key "/tmp/f" and the clause is
    seen to be about the PRE-SEED image rather than about the map the
    run starts from. *)
Example relative_key_inputs_are_valid :
  let tmp0 := [([Z_to_bv 8 102], [Z_to_bv 8 105])] in
  valid_input (image_input_tmp [(devnull_relative_key, [Z_to_bv 8 104])] tmp0)
  /\ valid_input (image_input_tmp [(localtime_relative_key, [Z_to_bv 8 104])] tmp0)
  /\ valid_input (image_input_tmp [(urandom_relative_key, [Z_to_bv 8 104])] tmp0).
Proof.
  repeat split; cbn;
    try valid_urandom_default;
    try (unfold valid_nofile; apply Z.leb_le; vm_compute; reflexivity);
    try (unfold valid_sigmask; apply bv_eq; vm_compute; reflexivity);
    try (unfold valid_hwcap; left; reflexivity);
    try (vm_compute; reflexivity);
    try lia;
    repeat first [ apply Forall_nil | apply Forall_cons
                 | apply not_in_bytes_of_existsb; vm_compute; reflexivity
                 | key_byte_neq | split | cbn; lia | reflexivity | intros [] ].
  (* [Run.valid_launch], the last conjunct: the fixture declares
     [State.default_execfn], the one-byte relative name "a" that
     [getname_flags] (fs/namei.c, Linux v6.18.46, commit 1f99e9ab748f)
     can return -- one byte, no NUL -- so the first arm of
     [Run.valid_execfn] applies, and the launch it makes is a handful of
     bytes, far under the E2BIG limit [bprm_stack_limits] (fs/exec.c)
     computes. *)
  all: try (left; split;
            [ cbn; lia
            | cbn; intros [H | []];
              apply (proj2 (bv_eqb_eq _ _)) in H; vm_compute in H;
              discriminate ]).
  all: try (vm_compute; discriminate).
Qed.

(* ========================= a key that is also a directory another key lives in

   The same shape of pin, for [Fs.fs_image_real].  An image with the
   keys "a" and "a/b" says that "a" is a regular file AND the directory
   "b" lives in.  No file system holds both: one name in one directory
   is one inode.  The model has no such rule in [Fs.valid_fs], which
   asks only for sorted NUL-free keys, so without the clause
   [Run.valid_input] admits the image and every statement quantified
   there covers a launch no kernel can produce.

   THE CONTROL IS THE POINT here too: the refused image and the
   admitted one differ by the one separator that makes "a" a directory
   ("a" and "ab" nest nowhere). *)

(** The pathological image: "a" is a file, and "a/b" puts a file in the
    directory "a".  [Fs.valid_fs] admits it and so does
    [Fs.fs_keys_relative] — neither key begins with "/" — so the
    refutation below rests on [Fs.fs_image_real] and on nothing else. *)
Definition prefix_key_image : Fs.Fs :=
  [([Z_to_bv 8 97], [Z_to_bv 8 104]);
   ([Z_to_bv 8 97; Z_to_bv 8 47; Z_to_bv 8 98], [Z_to_bv 8 104])].

(** The same two names with no separator between them: an ordinary
    image. *)
Definition flat_key_image : Fs.Fs :=
  [([Z_to_bv 8 97], [Z_to_bv 8 104]);
   ([Z_to_bv 8 97; Z_to_bv 8 98], [Z_to_bv 8 104])].

(** The clause that separates them, and the two it does NOT rest on. *)
Example fs_prefix_key_image_is_not_real :
  fs_image_real prefix_key_image = false
  /\ fs_image_real flat_key_image = true
  /\ fs_sorted prefix_key_image = true
  /\ fs_keys_relative prefix_key_image.
Proof.
  repeat split; try (vm_compute; reflexivity).
  repeat first [ apply Forall_nil | apply Forall_cons | cbn; key_byte_neq ].
Qed.

(** …so no run has it: the fixture over the image is refused by
    [Run.valid_input], THROUGH the image clause, while the fixture over
    the flat image is admitted. *)
Example fs_prefix_key_input_is_not_valid :
  ~ valid_input (image_input prefix_key_image).
Proof.
  intros (_ & _ & _ & _ & Hr & _).
  vm_compute in Hr. discriminate.
Qed.

Example fs_flat_key_input_is_valid :
  let tmp0 := [([Z_to_bv 8 102], [Z_to_bv 8 105])] in
  valid_input (image_input_tmp flat_key_image tmp0).
Proof.
  repeat split; cbn;
    try valid_urandom_default;
    try (unfold valid_nofile; apply Z.leb_le; vm_compute; reflexivity);
    try (unfold valid_sigmask; apply bv_eq; vm_compute; reflexivity);
    try (unfold valid_hwcap; left; reflexivity);
    (* [Run.valid_launch], the last conjunct: [State.mkProcInput_full]
       here carries [State.default_execfn], the one-byte relative path
       "a", which takes [Run.valid_execfn]'s first arm
       ([Run.valid_path_name]), and this launch's string and pointer
       bytes are far under [Run.e2big_limit].  Two arms rather than
       one, because [repeat split] reaches inside [valid_launch]
       wherever the conjunct has already been split. *)
    try (unfold valid_launch; split;
         [ unfold valid_execfn, valid_path_name, default_execfn; left; split;
           [ cbn; lia
           | cbn; intros [Hz | []]; apply (f_equal bv_unsigned) in Hz;
             vm_compute in Hz; discriminate ]
         | unfold e2big_limit; apply Z.leb_le; vm_compute; reflexivity ]);
    try (unfold valid_execfn, valid_path_name, default_execfn; left; split;
         [ cbn; lia
         | cbn; intros [Hz | []]; apply (f_equal bv_unsigned) in Hz;
           vm_compute in Hz; discriminate ]);
    try (unfold e2big_limit; apply Z.leb_le; vm_compute; reflexivity);
    try (vm_compute; reflexivity);
    try lia;
    repeat first [ apply Forall_nil | apply Forall_cons
                 | apply not_in_bytes_of_existsb; vm_compute; reflexivity
                 | key_byte_neq | split | cbn; lia | reflexivity | intros [] ].
Qed.

(** A non-canonical key is refused by the same clause: "./a" and "a/"
    and "a//b" each spell a path a walk resolves elsewhere, and a
    directory entry named "." cannot exist. *)
Example fs_noncanonical_keys_are_not_real :
  fs_image_real [([Z_to_bv 8 46; Z_to_bv 8 47; Z_to_bv 8 97], [])] = false
  /\ fs_image_real [([Z_to_bv 8 97; Z_to_bv 8 47], [])] = false
  /\ fs_image_real [([Z_to_bv 8 97; Z_to_bv 8 47; Z_to_bv 8 47;
                      Z_to_bv 8 98], [])] = false
  /\ fs_image_real [([], [])] = false.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** And on those admitted images the three opens are ANSWERED: the
    seeded "/tmp/f" key did not trip a guard, and neither did the
    relative key that spells the device's own name without its leading
    separator.  /dev/null mints [State.FdDevNull], /dev/urandom mints
    [State.FdUrandom], /etc/localtime is the -ENOENT its declaration
    promises. *)
Example device_opens_answer_on_a_valid_image :
  let tmp0 := [([Z_to_bv 8 102], [Z_to_bv 8 105])] in
  let open key bs n eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; 0; 420; 0; 0]
           (open_path_mem bs) (fun _ => None))
        (with_copyins [(8192, n)] eff)
        (init_model [] 0 0 demo_sp demo_limit
           (image_input_tmp [(key, [Z_to_bv 8 104])] tmp0)) in
  (match open devnull_relative_key devnull_bytes 10%nat (mkEffect 3 [] []) with
   | CheckOk m [] => fd_lookup (m_fds m) 3 = Some (FdDevNull true false)
   | _ => False
   end)
  /\ (match open urandom_relative_key urandom_bytes 13%nat (mkEffect 3 [] []) with
      | CheckOk m [] => fd_lookup (m_fds m) 3 = Some FdUrandom
      | _ => False
      end)
  /\ (match open localtime_relative_key localtime_bytes 15%nat
              (mkEffect (errno_ret ENOENT) [] []) with
      | CheckOk _ [] => True
      | _ => False
      end).
Proof. vm_compute. repeat split; reflexivity. Qed.

(** A table with the device at 3, over the declared stream. *)
Definition urandom_model : Model :=
  with_urandom (urandom_stream urandom_decl)
    (mkModel [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
              (3, FdUrandom)]
       (mkVmMaps [] [] 0 0 demo_limit) IEof [] None None None).

(** 128 writable bytes at 4096, the destination of every read below. *)
Definition urandom_wmem : word -> option byte :=
  fun a => if ((4096 <=? bv_unsigned a) && (bv_unsigned a <? 4224))%Z
           then Some (Z_to_bv 8 0) else None.

(** THE COMMON SHAPE: open, read, close.  A read of eight bytes
    delivers exactly the first eight of the declaration and advances
    the stream past them; the next read of eight delivers the next
    eight; a claimed delivery of other bytes, a short one, or one
    into another buffer is rejected; a zero count is 0 and consumes
    nothing; an unmapped destination is -EFAULT and consumes nothing;
    a write through the descriptor is -EBADF; close returns the
    model to its opening state. *)
Example urandom_open_read_close :
  let call no args eff m := check_syscall
        (mkInput no args (fun _ => None) urandom_wmem) eff m in
  let first8 := map (fun z => Z_to_bv 8 z) (firstn 8 urandom_decl) in
  let next8 := map (fun z => Z_to_bv 8 z) (firstn 8 (skipn 8 urandom_decl)) in
  match check_syscall
          (mkInput 56 [AT_FDCWD; 8192; 0; 420; 0; 0]
             (open_path_mem urandom_bytes) (fun _ => None))
          (with_copyins [(8192, 13%nat)] (mkEffect 3 [] [])) urandom_m0 with
  | CheckOk m1 [] =>
      (match call 63 [3; 4096; 8; 0; 0; 0] (mkEffect 8 [(4096, first8)] []) m1 with
       | CheckOk m2 [] =>
           m_urandom m2 = urandom_stream (skipn 8 urandom_decl)
           /\ (match call 63 [3; 4096; 8; 0; 0; 0] (mkEffect 8 [(4096, next8)] []) m2 with
               | CheckOk m3 [] => m_urandom m3 = IEof
                                  /\ call 63 [3; 4096; 1; 0; 0; 0] (mkEffect 0 [] []) m3
                                     = CheckUnmodeled
               | _ => False end)
           /\ call 63 [3; 4096; 8; 0; 0; 0] (mkEffect 8 [(4096, first8)] []) m2 = CheckReject
       | _ => False end)
      /\ call 63 [3; 4096; 8; 0; 0; 0] (mkEffect 8 [(4096, next8)] []) m1 = CheckReject
      /\ call 63 [3; 4096; 8; 0; 0; 0] (mkEffect 4 [(4096, firstn 4 first8)] []) m1
         = CheckReject
      /\ call 63 [3; 4096; 8; 0; 0; 0] (mkEffect 8 [(4100, first8)] []) m1 = CheckReject
      /\ call 63 [3; 4096; 0; 0; 0; 0] (mkEffect 0 [] []) m1 = CheckOk m1 []
      /\ check_syscall (mkInput 63 [3; 4096; 8; 0; 0; 0] (fun _ => None) (fun _ => None))
           (mkEffect (errno_ret EFAULT) [] []) m1 = CheckOk m1 []
      /\ call 64 [3; 4096; 8; 0; 0; 0] (mkEffect (errno_ret EBADF) [] []) m1 = CheckOk m1 []
      /\ call 57 [3; 0; 0; 0; 0; 0] (mkEffect 0 [] []) m1 = CheckOk urandom_m0 []
  | _ => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE STREAM RUNNING OUT IS A DECLINE, not a short read: a
    declaration of four bytes cannot meet a request for eight, and a
    claimed short delivery is not accepted either.

    THE DECLINE IS UNREACHABLE UNDER [Run.valid_input], and that is why
    it is pinned here rather than deleted.  [Run.valid_urandom] asks
    that a launch's declared stream never end, so no valid input reaches
    this row.  The arm is still TOTAL over [State.InputStream] — it has
    to be, the type admits [State.IEof] — and a caller outside
    [Run.valid_input] still meets the decline, which is what the model
    literals below are.  What they record is the exact shape the
    validity clause excludes, so that deleting the clause would show up
    as a whole-program theorem going false rather than as a pin quietly
    becoming reachable.
    [Checks.Examples.the_random_clause_is_what_the_fixture_carries] is
    the input side of the same fact.

    THE LAST CONJUNCT KEEPS THE FIRST THREE HONEST: the stream every
    valid input declares ([State.default_urandom]) delivers EVERY count
    in full, so the test the first three conjuncts fail —
    [Sys.Fs.ReadWrite.read_urandom]'s comparison of the delivered length
    against [State.rw_count_clamp count] — is one it passes at every
    count at once.  So the decline is about the DECLARATION's length and
    not about the device.  It is stated over the take rather than over a
    [check_syscall] literal because a model holding
    [State.default_urandom] holds a [CoFixpoint], which no [vm_compute]
    may be handed; [State.stream_take_z_infinite_length] is the fact
    the arm actually reads. *)
Example urandom_stream_runs_out :
  let m := with_urandom (urandom_stream [1; 2; 3; 4]%Z) urandom_model in
  let call eff := check_syscall
        (mkInput 63 [3; 4096; 8; 0; 0; 0] (fun _ => None) urandom_wmem) eff m in
  call (mkEffect 4 [(4096, map (fun z => Z_to_bv 8 z) [1; 2; 3; 4]%Z)] []) = CheckUnmodeled
  /\ call (mkEffect 8 [(4096, map (fun z => Z_to_bv 8 z) [1; 2; 3; 4; 0; 0; 0; 0]%Z)] [])
     = CheckUnmodeled
  /\ (match check_syscall
              (mkInput 63 [3; 4096; 4; 0; 0; 0] (fun _ => None) urandom_wmem)
              (mkEffect 4 [(4096, map (fun z => Z_to_bv 8 z) [1; 2; 3; 4]%Z)] []) m with
      | CheckOk m' [] => m_urandom m' = IEof | _ => False end)
  /\ (forall n, (0 <= n)%Z ->
        Z.of_nat (length (fst (stream_take_z default_urandom n))) = n).
Proof.
  cbv zeta.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  intros n Hn.
  exact (stream_take_z_infinite_length _ _ default_urandom_infinite Hn).
Qed.

(** THE DISPATCH SITES.  [lseek] is 0 for every whence and offset
    ([noop_llseek] over the pinned position) and a claimed
    repositioning is rejected; [pread64] at any position delivers the
    front of the stream exactly as [read] does; [pwrite64] and
    [writev] are -EBADF; [fsync] and [ftruncate] are -EINVAL;
    [getdents64] is -ENOTDIR; [dup] copies the entry; [fcntl] F_SETFD
    is 0 and F_GETFL declines; [ioctl] RNDGETENTCNT and [flock] fail
    closed; [fstat] into an unbacked destination declines, and its
    delivering example follows. *)
Example urandom_dispatch_sites :
  let call no args eff := check_syscall
        (mkInput no args (fun _ => None) urandom_wmem) eff urandom_model in
  let first8 := map (fun z => Z_to_bv 8 z) (firstn 8 urandom_decl) in
  call 62 [3; 3; 0; 0; 0; 0] (mkEffect 0 [] []) = CheckOk urandom_model []
  /\ call 62 [3; 3; 0; 0; 0; 0] (mkEffect 3 [] []) = CheckReject
  /\ call 62 [3; 7; 2; 0; 0; 0] (mkEffect 0 [] []) = CheckOk urandom_model []   (* SEEK_END *)
  /\ call 62 [3; 0; 4; 0; 0; 0] (mkEffect 0 [] []) = CheckOk urandom_model []   (* SEEK_HOLE *)
  /\ (match call 67 [3; 4096; 8; 100; 0; 0] (mkEffect 8 [(4096, first8)] []) with
      | CheckOk m [] => m_urandom m = urandom_stream (skipn 8 urandom_decl)
      | _ => False end)
  /\ call 68 [3; 4096; 5; 100; 0; 0] (mkEffect (errno_ret EBADF) [] []) = CheckOk urandom_model []
  /\ call 82 [3; 0; 0; 0; 0; 0] (mkEffect (errno_ret EINVAL) [] []) = CheckOk urandom_model []
  /\ call 46 [3; 0; 0; 0; 0; 0] (mkEffect (errno_ret EINVAL) [] []) = CheckOk urandom_model []
  /\ call 61 [3; 4096; 1024; 0; 0; 0] (mkEffect (errno_ret ENOTDIR) [] [])
     = CheckOk urandom_model []
  /\ (match call 23 [3; 0; 0; 0; 0; 0] (mkEffect 4 [] []) with
      | CheckOk m [] => fd_lookup (m_fds m) 4 = Some FdUrandom
      | _ => False end)
  /\ call 25 [3; F_SETFD; 1; 0; 0; 0] (mkEffect 0 [] []) = CheckOk urandom_model []
  /\ call 25 [3; F_GETFL; 0; 0; 0; 0] (mkEffect 0 [] []) = CheckUnmodeled
  /\ check_syscall (mkInput 80 [3; 4096; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) urandom_model = CheckUnmodeled
  /\ call 29 [3; TCGETS; 4096; 0; 0; 0] (mkEffect (errno_ret ENOTTY) [] [])
     = CheckUnmodeled
  /\ call 32 [3; 2; 0; 0; 0; 0] (mkEffect 0 [] []) = CheckUnmodeled.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** fstat ON /dev/urandom ASSERTS THE RANDOM DEVICE: S_IFCHR with
    [st_rdev] 1:9 and a zero size is accepted and PINNED under
    [urandom_path]; the null device's number, a regular file, and a
    nonzero size are rejected; a second fstat must repeat the pin's
    stable members. *)
Example urandom_fstat_asserts_the_device :
  let call m eff := check_syscall
        (mkInput 80 [3; 4096; 0; 0; 0; 0] (fun _ => None) urandom_wmem) eff m in
  let good := dev_stat S_IFCHR URANDOM_RDEV 0 in
  let deliver bs := mkEffect 0 [(4096, bs)] [] in
  (match call urandom_model (deliver good) with
   | CheckOk m [] =>
       statpin_lookup (m_statpins m) urandom_path = Some good
       /\ call m (deliver good) = CheckOk m []
       /\ call m (deliver (Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 7
                            ++ skipn 16 good)) = CheckReject
   | _ => False
   end)
  /\ call urandom_model (deliver (dev_stat S_IFCHR DEVNULL_RDEV 0)) = CheckReject
  /\ call urandom_model (deliver (dev_stat S_IFREG 0 5)) = CheckReject
  /\ call urandom_model (deliver (dev_stat S_IFCHR URANDOM_RDEV 5)) = CheckReject
  /\ call urandom_model (mkEffect 0 [] []) = CheckReject.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE SAME STREAM ON BOTH SIDES OF A PAIR.  A source and a target
    that differ in everything the model lets them differ in — here the
    descriptor table, so the device sits at 3 on one side and at 5 on
    the other — read the same eight bytes when they are seeded from one
    [in_urandom], and are left holding the same remainder.  Concretely
    below; in general [Checks.Sys.Fs.ReadWrite.check_read_urandom_same_stream],
    which this instantiates. *)
Example urandom_same_bytes_on_both_sides :
  let inp := mkProcInput_full [[]] [] [] IEof
               demo_uid demo_gid demo_groups net_silent
               default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48
               (urandom_stream urandom_decl) [] default_kernel default_execfn
               true true in
  let src := with_fds (fd_insert (m_fds (init_model [] 0 0 demo_sp demo_limit inp))
                         3 FdUrandom)
               (init_model [] 0 0 demo_sp demo_limit inp) in
  let tgt := with_fds (fd_insert (fd_insert (m_fds (init_model [] 0 0 demo_sp demo_limit inp))
                                    4 FdDir) 5 FdUrandom)
               (init_model [] 0 0 demo_sp demo_limit inp) in
  let first8 := map (fun z => Z_to_bv 8 z) (firstn 8 urandom_decl) in
  let read fd m eff := check_syscall
        (mkInput 63 [fd; 4096; 8; 0; 0; 0] (fun _ => None) urandom_wmem) eff m in
  match read 3 src (mkEffect 8 [(4096, first8)] []),
        read 5 tgt (mkEffect 8 [(4096, first8)] []) with
  | CheckOk s' [], CheckOk t' [] =>
      m_urandom s' = m_urandom t'
      /\ m_urandom s' = urandom_stream (skipn 8 urandom_decl)
  | _, _ => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma urandom_same_bytes_in_general :
  forall i buf count eff1 eff2 m1 m2 m1' m2' evs1 evs2,
  m_urandom m1 = m_urandom m2 ->
  check_read_urandom i buf count eff1 m1 = CheckOk m1' evs1 ->
  check_read_urandom i buf count eff2 m2 = CheckOk m2' evs2 ->
  eff_writes eff1 = eff_writes eff2 /\ m_urandom m1' = m_urandom m2'.
Proof.
  intros. destruct (check_read_urandom_same_stream _ _ _ _ _ _ _ _ _ _ _ H H0 H1)
    as (Hw & _ & Hm). now split.
Qed.

(** ".." AND "." GET THE SAME ANSWER ON EVERY ARM, which is a claim
    about two flag words and two pathnames at once and so is a literal
    rather than a real run: a run makes the one call it makes.  Both are
    directory references the walk answers without a lookup, so the
    clobbering shape is -EISDIR for each and the read shape hands back a
    directory fd for each.

    Without this arm, the second of each pair would be wrong: the
    create shape would MINT A KEY SPELLED "..", and the read shape would
    answer -ENOENT, which Linux never returns for "..".  The last conjunct is
    the control that keeps the first four from being satisfied by a
    model that declines everything — a claimed SUCCESS on the create
    shape is rejected, for ".." exactly as for ".". *)
Example openat_dotdot_answers_as_dot_does :
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) in
  let open bs n fl eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           (open_path_mem bs) (fun _ => None))
        (with_copyins [(8192, n)] eff) m0 in
  let dot := [46%Z] in let dotdot := [46%Z; 46%Z] in
  (* the clobbering shape: -EISDIR for both, and it really is an Ok *)
  open dot 2%nat wr_create_flags (mkEffect (errno_ret EISDIR) [] [])
    = CheckOk m0 []
  /\ open dotdot 3%nat wr_create_flags (mkEffect (errno_ret EISDIR) [] [])
     = CheckOk m0 []
  (* the read shape: a directory fd at the lowest free slot, for both *)
  /\ match open dot 2%nat 0%Z (mkEffect 3 [] []) with
     | CheckOk m [] => fd_lookup (m_fds m) (Z_to_bv 64 3) = Some FdDir
     | _ => False end
  /\ match open dotdot 3%nat 0%Z (mkEffect 3 [] []) with
     | CheckOk m [] => fd_lookup (m_fds m) (Z_to_bv 64 3) = Some FdDir
     | _ => False end
  (* ...and neither is answered by declining: a claimed success on the
     create shape is REFUSED, which is what makes the four above real *)
  /\ open dot 2%nat wr_create_flags (mkEffect 3 [] []) = CheckReject
  /\ open dotdot 3%nat wr_create_flags (mkEffect 3 [] []) = CheckReject.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE OVER-MATCH GUARD FOR [path_is_dirref], and the most load-bearing
    of the three below.  "..." is an ORDINARY NAME: it is not a directory
    reference, so the create arm mints a key for it exactly as it would
    for "f".  [path_is_dirref] uses [path_eqb] against the two constants
    and nothing else, so this holds — but nothing else in the tree
    pins it, and the obvious "improvement" of matching a LEADING ".."
    would break it silently, turning every dotfile-ish name into a
    directory reference.  A real run cannot make this claim: it would show
    one open succeeding, not that the classifier draws its line between
    ".." and "...".

    The three-byte path also sits one byte past [dotdot_path], which is
    where a prefix test rather than an equality test would go wrong. *)
Example openat_dot3_is_an_ordinary_name :
  match check_syscall
          (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 wr_create_flags; 420; 0; 0]
             (open_path_mem [46%Z; 46%Z; 46%Z]) (fun _ => None))
          (with_copyins [(8192, 4%nat)] (mkEffect 3 [] []))
          (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) with
  | CheckOk m [] => m_fs m = [([Z_to_bv 8 46; Z_to_bv 8 46; Z_to_bv 8 46], [])]
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** THE EMPTY PATHNAME BEATS O_CREAT, and no key spelled "" can ever be
    minted.  Two halves of one boundary, which is the shape a boundary
    claim needs: the deterministic -ENOENT is accepted with the model
    unchanged, and a kernel claiming the create SUCCEEDED is refused.
    [openat_body_spec] answers the empty path before it reaches any arm,
    so this is a statement about the ORDER of two tests rather than about
    either one, and a spec that let O_CREAT run first would mint a key
    under the empty name and still pass every other case in this file. *)
Example openat_empty_path_beats_o_creat :
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) in
  let open eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 wr_create_flags; 420; 0; 0]
           (open_path_mem []) (fun _ => None))
        (with_copyins [(8192, 1%nat)] eff) m0 in
  open (mkEffect (errno_ret ENOENT) [] []) = CheckOk m0 []
  /\ open (mkEffect 3 [] []) = CheckReject.
Proof. vm_compute. split; reflexivity. Qed.

(* ================================ openat's O_DIRECTORY arm

   [Fs.Open.openat_dir_spec] answers O_RDONLY|O_DIRECTORY.  Three claims
   about it that a real run cannot make: an equality between two FLAG
   WORDS, a decline that must not depend on what the kernel said, and a
   file-system image whose keys hold a separator — no modeled syscall
   puts one there. *)

(** THE ARM'S FOUR ANSWERS, AND THE FLAG IS REALLY READ.  The last two
    conjuncts are what make the first four evidence of anything: a
    claimed SUCCESS on a name the map holds is refused, so the -ENOTDIR
    is not a spec that admits everything; and the SAME name under bare
    O_RDONLY is a readable file fd rather than -ENOTDIR, so the errno is
    O_DIRECTORY's doing and not the name's.  A real run issues one flag
    word per call and cannot state either. *)
Example openat_directory_answers :
  let m0 fs := init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof) in
  let open fs bs n fl eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 0; 0; 0]
           (open_path_mem bs) (fun _ => None))
        (with_copyins [(8192, n)] eff) (m0 fs) in
  let dir_word := (O_DIRECTORY + O_LARGEFILE + O_CLOEXEC)%Z in
  let have := [([Z_to_bv 8 97], [104])] in
  (* "." and "..": a directory fd at the lowest free slot, the same
     [FdDir] the plain read arm hands back *)
  (match open [] [46%Z] 2%nat dir_word (mkEffect 3 [] []) with
   | CheckOk m [] => fd_lookup (m_fds m) (Z_to_bv 64 3) = Some FdDir
   | _ => False end)
  /\ (match open [] [46%Z; 46%Z] 3%nat dir_word (mkEffect 3 [] []) with
      | CheckOk m [] => fd_lookup (m_fds m) (Z_to_bv 64 3) = Some FdDir
      | _ => False end)
  (* a name the map holds is not a directory: -ENOTDIR, model unchanged *)
  /\ open have [97%Z] 2%nat dir_word (mkEffect (errno_ret ENOTDIR) [] [])
     = CheckOk (m0 have) []
  (* an absent name never reaches the directory test: -ENOENT *)
  /\ open [] [97%Z] 2%nat dir_word (mkEffect (errno_ret ENOENT) [] [])
     = CheckOk (m0 []) []
  (* ...and a claimed descriptor for the name the map holds is REFUSED *)
  /\ open have [97%Z] 2%nat dir_word (mkEffect 3 [] []) = CheckReject
  (* ...while the same name under bare O_RDONLY is a file fd, so the
     -ENOTDIR above is the flag's answer and not the name's *)
  /\ (match open have [97%Z] 2%nat 0%Z (mkEffect 3 [] []) with
      | CheckOk m [] => fd_lookup (m_fds m) (Z_to_bv 64 3)
                        = Some (FdFile [Z_to_bv 8 97] (Z_to_bv 64 0))
      | _ => False end).
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE IGNORED BITS ARE IGNORED HERE TOO, which is an EQUALITY BETWEEN
    TWO FLAG WORDS and so cannot be a real run: a run issues one word,
    and could show the four-bit word conforming without showing
    that it lands where the two-bit word lands.  Stated over all four of
    the arm's answers at once, since a mask applied in one branch and
    not another is exactly the mistake this catches. *)
Example openat_directory_ignores_largefile_and_cloexec :
  let m0 fs := init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof) in
  let open fs bs n fl eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 0; 0; 0]
           (open_path_mem bs) (fun _ => None))
        (with_copyins [(8192, n)] eff) (m0 fs) in
  let wide := (O_DIRECTORY + O_LARGEFILE + O_CLOEXEC)%Z in
  let have := [([Z_to_bv 8 97], [104])] in
  open [] [46%Z] 2%nat wide (mkEffect 3 [] [])
    = open [] [46%Z] 2%nat O_DIRECTORY (mkEffect 3 [] [])
  /\ open [] [46%Z; 46%Z] 3%nat wide (mkEffect 3 [] [])
     = open [] [46%Z; 46%Z] 3%nat O_DIRECTORY (mkEffect 3 [] [])
  /\ open have [97%Z] 2%nat wide (mkEffect (errno_ret ENOTDIR) [] [])
     = open have [97%Z] 2%nat O_DIRECTORY (mkEffect (errno_ret ENOTDIR) [] [])
  /\ open [] [97%Z] 2%nat wide (mkEffect (errno_ret ENOENT) [] [])
     = open [] [97%Z] 2%nat O_DIRECTORY (mkEffect (errno_ret ENOENT) [] []).
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE IMPLIED-DIRECTORY DECLINE, and the half no real run reaches: the
    claim is over two kernel answers that could not both be right.  A
    key "a/b" means reality has a directory "a", so Linux hands back a
    directory fd where the map would answer -ENOENT — and the arm
    declines whichever of the two the kernel is offered as having given,
    so it is not quietly agreeing with one of them.

    The control is the same call on the same NAME with nothing under it,
    which IS answered.  Without it a decline here would be satisfied
    just as well by an arm that declines every ordinary name.

    This guard is on the O_DIRECTORY arm and not on the read arm, and
    the asymmetry is deliberate: [Fs.Open.openat_dir_spec] records why
    this one can take it.  The write-create
    arms neither guard nor mint: they ANSWER the implied directory
    ([openat_implied_directory_create_eisdir] above). *)
Example openat_directory_implied_directory_unmodeled :
  let m0 fs := init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof) in
  let open fs eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192;
                     Z_to_bv 64 (O_DIRECTORY + O_LARGEFILE + O_CLOEXEC);
                     0; 0; 0]
           (open_path_mem [97%Z]) (fun _ => None))
        (with_copyins [(8192, 2%nat)] eff) (m0 fs) in
  let under := [([Z_to_bv 8 97; Z_to_bv 8 47; Z_to_bv 8 98], [104])] in
  open under (mkEffect 3 [] []) = CheckUnmodeled
  /\ open under (mkEffect (errno_ret ENOENT) [] []) = CheckUnmodeled
  /\ open [] (mkEffect (errno_ret ENOENT) [] []) = CheckOk (m0 []) [].
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE NAME_MAX BOUNDARY, stated as the pair a boundary claim needs: a
    256-byte component is declined and a 255-byte one is answered.  Over
    [Uapi.NAME_MAX] the -ENAMETOOLONG belongs to the FILESYSTEM
    ([ext4_lookup]'s EXT4_NAME_LEN test, [simple_lookup]'s NAME_MAX
    test), and a model with no filesystem type would be inventing one;
    a real run cannot make the claim, because the kernel it runs on has a
    filesystem and simply answers. *)
Example openat_directory_name_max_boundary :
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) in
  let open bs n eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192;
                     Z_to_bv 64 (O_DIRECTORY + O_LARGEFILE + O_CLOEXEC);
                     0; 0; 0]
           (open_path_mem bs) (fun _ => None))
        (with_copyins [(8192, n)] eff) m0 in
  open (repeat 97%Z 256) 257%nat (mkEffect (errno_ret ENOENT) [] [])
    = CheckUnmodeled
  /\ open (repeat 97%Z 255) 256%nat (mkEffect (errno_ret ENOENT) [] [])
     = CheckOk m0 [].
Proof. vm_compute. split; reflexivity. Qed.

(** THE EXCLUSIVE APPEND WORD AT ITS EDGES: each is a change a wrong arm
    could make in [Fs.Open.openat_append_spec] and its checker
    alike, closing every proof.
    - A 256-byte name is declined and a 255-byte one is created: no name
      over [Uapi.NAME_MAX] can exist, so the create would reach the
      filesystem's own -ENAMETOOLONG, which a model with no filesystem
      type does not invent (the pair above states it for O_DIRECTORY).
    - Without O_CREAT nothing is created: Linux answers an absent name
      with the lookup's -ENOENT, since [lookup_open] creates only under
      O_CREAT (fs/namei.c, Linux v6.18.46), and
      [Fs.Open.modeled_open_flags] declines the word before the path.
    - /tmp/<n> and /etc/localtime keep declining it: their arms answer
      only the words they name. *)
Example openat_excl_append_edges :
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) in
  let open bs fl eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           (open_path_mem bs) (fun _ => None))
        (with_copyins [(8192, S (length bs))] eff) m0 in
  let ok r := match r with CheckOk _ _ => true | _ => false end in
  (* NAME_MAX: 256 bytes declined, whatever is offered; 255 created *)
  open (repeat 97%Z 256) excl_append_create_flags (mkEffect 3 [] [])
    = CheckUnmodeled
  /\ open (repeat 97%Z 256) excl_append_create_flags
       (mkEffect (errno_ret EEXIST) [] [])
     = CheckUnmodeled
  /\ ok (open (repeat 97%Z 255) excl_append_create_flags (mkEffect 3 [] []))
     = true
  (* no O_CREAT: not this word, and declined before the path *)
  /\ open [102%Z] (O_WRONLY + O_EXCL + O_APPEND)%Z (mkEffect 3 [] [])
     = CheckUnmodeled
  /\ open [102%Z] (O_WRONLY + O_EXCL + O_APPEND)%Z
       (mkEffect (errno_ret ENOENT) [] [])
     = CheckUnmodeled
  (* the /tmp and /etc/localtime arms do not answer it *)
  /\ open [47; 116; 109; 112; 47; 100]%Z excl_append_create_flags
       (mkEffect 3 [] [])
     = CheckUnmodeled
  /\ open localtime_bytes excl_append_create_flags
       (mkEffect (errno_ret ENOENT) [] [])
     = CheckUnmodeled.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ================================================ faccessat2 (439)

   Four claims, over the one thing faccessat2 adds to faccessat: the flag
   word.  A real run cannot make these four claims: it cannot run TWO
   flag words against one another (it gets the answer for the word it
   passed), vary the kernel's answer under a decline, or build a
   file-system image whose keys hold a separator. *)

(** The model both faccessat2 examples below run against: one present
    key "a", nothing else. *)
Definition fa2_model : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input [([97], [])] IEof).

(** ACCEPTED FLAGS CHANGE NO ANSWER, which is the sharpest claim
    [Fs.Open.faccessat2_spec] makes and the one no real run reaches: it is
    an EQUALITY BETWEEN FLAG WORDS, and a run is shown the answer for the
    word it passed.  The same call under 0, AT_EACCESS,
    AT_SYMLINK_NOFOLLOW and both lands in exactly the same place —
    accepted, model untouched, no events — because under F_OK neither bit
    reaches anything the model holds: AT_EACCESS only picks which cred
    the walk runs under, and every DAC comparison narrows a zero mask
    away first; AT_SYMLINK_NOFOLLOW only stops a trailing symlink being
    followed, and a resolvable key here is a regular file. *)
Example faccessat2_accepted_flags_change_no_answer :
  let call flags := check_syscall
        (mkInput 439 [AT_FDCWD; 8192; 0; Z_to_bv 64 flags; 0; 0] fa_mem_name_a
           (fun _ => None))
        (with_copyins [(8192, 2%nat)] (mkEffect 0 [] []))
        fa2_model in
  call 0%Z = CheckOk fa2_model []
  /\ call AT_EACCESS = CheckOk fa2_model []
  /\ call AT_SYMLINK_NOFOLLOW = CheckOk fa2_model []
  /\ call (Z.lor AT_EACCESS AT_SYMLINK_NOFOLLOW) = CheckOk fa2_model [].
Proof. vm_compute. repeat split. Qed.

(** AT_EMPTY_PATH IS DECLINED, AND THE DECLINE DOES NOT DEPEND ON WHAT
    THE KERNEL SAID — the half no real run reaches, since a run is shown
    one answer and the claim here is over two that could not both be
    right.  The kernel really answers 0 (LOOKUP_EMPTY makes the dirfd
    itself the target, so an empty pathname becomes the working
    directory and a nonempty one resolves as usual), and the model
    declines whichever answer is offered rather than quietly agreeing
    with one.  The pathname here is present and resolvable, so nothing
    but the flag can be what the decline is about. *)
Example faccessat2_empty_path_flag_declined_either_way :
  let call eff := check_syscall
        (mkInput 439 [AT_FDCWD; 8192; 0; Z_to_bv 64 AT_EMPTY_PATH; 0; 0]
           fa_mem_name_a (fun _ => None))
        (with_copyins [(8192, 2%nat)] eff)
        fa2_model in
  call (mkEffect 0 [] []) = CheckUnmodeled
  /\ call (mkEffect (errno_ret ENOENT) [] []) = CheckUnmodeled.
Proof. vm_compute. split; reflexivity. Qed.

(** THE FLAG -EINVAL READS NO USER MEMORY, for the reason the mode
    -EINVAL does not: [do_faccessat] tests the flag word in its SECOND
    statement, before [user_path_at] is called, so a ledger claimed on
    that arm is a read Linux did not perform.  This is the case a spec
    that wrapped the whole body in [record_copyins] gets wrong.
    AT_SYMLINK_FOLLOW (0x400) is a real AT_ constant OUTSIDE the three
    faccessat2 accepts, so the -EINVAL is the kernel's own answer and
    not a decline; the pair differs in the ledger alone. *)
Example faccessat2_bad_flag_records_no_copyin :
  let call eff := check_syscall
        (mkInput 439 [AT_FDCWD; 8192; 0; Z_to_bv 64 1024; 0; 0] fa_mem_name_a
           (fun _ => None))
        eff fa2_model in
  call (mkEffect (errno_ret EINVAL) [] []) = CheckOk fa2_model []
  /\ call (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EINVAL) [] []))
     = CheckReject.
Proof. vm_compute. split; reflexivity. Qed.

(** The implied-directory decline reaches the 439 arm too, and it is the
    one faccessat decline only the starting image can set up: a key living
    UNDER a name means reality has a DIRECTORY the flat map only
    implies, and F_OK of a directory is 0 where the map would answer
    -ENOENT.  Stated again here because [Fs.Open.faccessat2_spec] is a
    separate arm — sharing [Fs.Open.faccessat_body_spec] is what makes
    it hold, and this is what says the sharing survived. *)
Example faccessat2_implied_directory_unmodeled :
  check_syscall
    (mkInput 439 [AT_FDCWD; 8192; 0; Z_to_bv 64 AT_EACCESS; 0; 0]
       fa_mem_name_a (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect 0 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], []); ([97; 47; 98], [104])] IEof))
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(* ============================== "/tmp/<one component>", the answered family

   [Fs.Open.openat_tmp_spec] answers two flag words for a path of the
   shape "/tmp/<one component>", over the run's declared private /tmp
   ([State.in_tmp], seeded under absolute keys by [State.fs_seed_tmp]).
   The premise it rests on — /tmp is writable and PRIVATE to this run —
   is an assumption of the model, stated on the arm. *)

(** The bytes of "/tmp/out.gif". *)
Definition tmp_gif_bytes : list Z :=
  [47; 116; 109; 112; 47; 111; 117; 116; 46; 103; 105; 102]%Z.

(** The same path as a model KEY, which is what the seeding produces and
    what the arms look up. *)
Definition tmp_gif_key : Fs.path :=
  map (fun z => Z_to_bv 8 z) tmp_gif_bytes.

(** THE ROUND TRIP, on a run whose declared /tmp is EMPTY: create the
    name, then read it back at a second descriptor, then remove it.
    This is the shape a program makes when it writes a temporary file,
    reads it back and removes it.  The create records the key EMPTY,
    exactly as [Fs.Open.create_wronly] does; the descriptor is an
    ordinary [State.FdFileW] on the absolute key, so nothing later in the
    run needs an arm of its own. *)
Example openat_tmp_create_read_unlink :
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) in
  let open fl eff m := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           (open_path_mem tmp_gif_bytes) (fun _ => None))
        (with_copyins [(8192, 13%nat)] eff) m in
  match open wr_create_flags (mkEffect 3 [] []) m0 with
  | CheckOk m1 [] =>
      (* the key is there, empty, and the descriptor is write-only on it *)
      m_fs m1 = [(tmp_gif_key, [])]
      /\ fd_lookup (m_fds m1) (Z_to_bv 64 3) = Some (FdFileW tmp_gif_key (Z_to_bv 64 0))
      (* the read shape now answers, at the next free descriptor *)
      /\ match open 0%Z (mkEffect 4 [] []) m1 with
         | CheckOk m2 [] =>
             fd_lookup (m_fds m2) (Z_to_bv 64 4) = Some (FdFile tmp_gif_key (Z_to_bv 64 0))
         | _ => False end
      (* ...and the removal takes the key away, once no fd names it *)
      /\ match check_syscall
                 (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0]
                    (open_path_mem tmp_gif_bytes) (fun _ => None))
                 (with_copyins [(8192, 13%nat)] (mkEffect 0 [] []))
                 (with_fds [] m1) with
         | CheckOk m3 [] => m_fs m3 = []
         | _ => False end
      (* THE IGNORED BITS COME THROUGH.  The word is matched past
         [Open.open_ignored_flags] — O_CLOEXEC, O_LARGEFILE and
         O_NONBLOCK, the file's shared mask — not past O_CLOEXEC alone,
         so the create word carrying any of them reaches the same arm
         and records the same key.  A real run cannot separate this
         from the bare word; only a literal can. *)
      /\ open (wr_create_flags + O_CLOEXEC)%Z (mkEffect 3 [] []) m0
         = CheckOk m1 []
      /\ open (wr_create_flags + O_NONBLOCK)%Z (mkEffect 3 [] []) m0
         = CheckOk m1 []
      /\ open (wr_create_flags + O_LARGEFILE)%Z (mkEffect 3 [] []) m0
         = CheckOk m1 []
      (* ...and so does the read word *)
      /\ match open (0 + O_CLOEXEC)%Z (mkEffect 4 [] []) m1 with
         | CheckOk m2 [] =>
             fd_lookup (m_fds m2) (Z_to_bv 64 4)
               = Some (FdFile tmp_gif_key (Z_to_bv 64 0))
         | _ => False end
  | _ => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** A read of a name the ENVIRONMENT declared rather than the run
    created.  The declaration is keyed by the one component ("out.gif")
    and the program names the whole path; [State.fs_seed_tmp] is what
    makes those the same file, and this is the case that says so. *)
Example openat_tmp_declared_name_reads :
  match check_syscall
          (mkInput 56 [AT_FDCWD; 8192; 0; 420; 0; 0]
             (open_path_mem tmp_gif_bytes) (fun _ => None))
          (with_copyins [(8192, 13%nat)] (mkEffect 3 [] []))
          (init_model [] 0 0 demo_sp demo_limit
             (demo_input_tmp [] [([111; 117; 116; 46; 103; 105; 102], [104; 105])] IEof)) with
  | CheckOk m [] =>
      fd_lookup (m_fds m) (Z_to_bv 64 3) = Some (FdFile tmp_gif_key (Z_to_bv 64 0))
      /\ Fs.fs_lookup (m_fs m) tmp_gif_key = Some [104; 105]
  | _ => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE DECLARATION NEEDS NO VALIDITY CLAUSE, which is the point of
    seeding it one entry at a time through [Fs.fs_set]: an unsorted
    declaration with a repeat in it still seeds the canonical form, and
    the later entry wins.  [State.fs_seed_tmp_valid] is the general
    statement; this is it on a literal the [Fs.valid_fs] of an image
    would have refused outright. *)
Example openat_tmp_unsorted_declaration_is_canonical :
  let fs := m_fs (init_model [] 0 0 demo_sp demo_limit
                    (demo_input_tmp []
                       [([98], [1]); ([97], [2]); ([98], [3])] IEof)) in
  (* the canonical form, out of a declaration that was not in it *)
  Fs.fs_sorted fs = true
  /\ length fs = 2%nat
  (* each declared name under its absolute key, the later "b" winning *)
  /\ Fs.fs_lookup fs (tmp_key [97]) = Some [2]
  /\ Fs.fs_lookup fs (tmp_key [98]) = Some [3]
  (* AND THE COLLISION: an IMAGE that already holds the absolute key,
     beside a declaration that names the component, resolves to the
     DECLARATION's bytes.  [Fs.valid_fs] admits such an image — its keys
     are only sorted and NUL-free, and nothing forbids one beginning
     "/tmp/" — and the seeding's [Fs.fs_set] replaces rather than
     appends, so the run holds one file at that name and it is the
     declared one.  Which way the collision falls is a choice; this is
     where it is written down. *)
  /\ Fs.fs_lookup
       (m_fs (init_model [] 0 0 demo_sp demo_limit
                (demo_input_tmp [(tmp_gif_key, [1])]
                   [([111; 117; 116; 46; 103; 105; 102], [2])] IEof)))
       tmp_gif_key = Some [2].
Proof. vm_compute. repeat split; reflexivity. Qed.

(** WHAT STAYS DECLINED, each on a model that HOLDS the key, so that
    none of them is declining for want of the file.  A read of a name
    the run does NOT hold is the one decline the privacy premise could
    have answered -ENOENT; the model declines it, and it is stated on
    the empty model beside the rest. *)
Example openat_tmp_excluded_shapes_unmodeled :
  let held := init_model [] 0 0 demo_sp demo_limit
                (demo_input_tmp [] [([111; 117; 116; 46; 103; 105; 102], [104])] IEof) in
  let empty := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) in
  let open bs n fl eff m := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           (open_path_mem bs) (fun _ => None))
        (with_copyins [(8192, n)] eff) m in
  (* a read of a name the run does not hold *)
  open tmp_gif_bytes 13%nat 0%Z (mkEffect (errno_ret ENOENT) [] []) empty
    = CheckUnmodeled
  (* the flag words the arm leaves out, at a name that IS held *)
  /\ open tmp_gif_bytes 13%nat (O_RDWR + O_CREAT + O_TRUNC)%Z
       (mkEffect 3 [] []) held = CheckUnmodeled
  /\ open tmp_gif_bytes 13%nat append_create_flags (mkEffect 3 [] []) held
     = CheckUnmodeled
  /\ open tmp_gif_bytes 13%nat excl_create_flags
       (mkEffect (errno_ret EEXIST) [] []) held = CheckUnmodeled
  /\ open tmp_gif_bytes 13%nat O_DIRECTORY
       (mkEffect (errno_ret ENOTDIR) [] []) held = CheckUnmodeled
  (* a second component *)
  /\ open [47; 116; 109; 112; 47; 100; 47; 102]%Z 9%nat wr_create_flags
       (mkEffect 3 [] []) empty = CheckUnmodeled
  (* the directory itself, and the two references inside it *)
  /\ open [47; 116; 109; 112]%Z 5%nat 0%Z (mkEffect 3 [] []) held
     = CheckUnmodeled
  /\ open [47; 116; 109; 112; 47]%Z 6%nat 0%Z (mkEffect 3 [] []) held
     = CheckUnmodeled
  /\ open [47; 116; 109; 112; 47; 46]%Z 7%nat 0%Z (mkEffect 3 [] []) held
     = CheckUnmodeled
  /\ open [47; 116; 109; 112; 47; 46; 46]%Z 8%nat 0%Z (mkEffect 3 [] []) held
     = CheckUnmodeled
  (* a name that merely BEGINS like the prefix: "/tmpfoo" is not under
     /tmp at all, and the separator decline still stands for it *)
  /\ open [47; 116; 109; 112; 102; 111; 111]%Z 8%nat wr_create_flags
       (mkEffect 3 [] []) empty = CheckUnmodeled.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE [Uapi.NAME_MAX] BOUNDARY, from both sides.  The decline is this
    arm's own — the plain arms cannot afford it (see
    [Open.openat_plain_name]'s note) and this one can — so nothing else
    in the tree reaches it, and a boundary claimed on one side only is
    satisfied by an arm that declines everything.  A component of 255
    bytes is ANSWERED and a component of 256 is DECLINED, at both flag
    words the arm takes.

    The -ENAMETOOLONG a longer component really gets comes out of the
    FILESYSTEM's own lookup rather than out of fs/namei.c, so the guard
    is one-sided: it defends against a filesystem whose limit is larger
    than 255 and not against one whose limit is smaller. *)
Example openat_tmp_name_max_boundary :
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) in
  (* "/tmp/" followed by n copies of 'a' *)
  let name n := List.repeat 97%Z n in
  let open n fl eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           (open_path_mem ([47; 116; 109; 112; 47]%Z ++ name n)) (fun _ => None))
        (with_copyins [(8192, (6 + n)%nat)] eff) m0 in
  (* 255: answered — the create mints the key, and the read of a key the
     run does not hold is the arm's OTHER decline, not this one *)
  match open 255%nat wr_create_flags (mkEffect 3 [] []) with
  | CheckOk _ [] => True | _ => False end
  (* 256: declined, at the create word and at the read word alike *)
  /\ open 256%nat wr_create_flags (mkEffect 3 [] []) = CheckUnmodeled
  /\ open 256%nat 0%Z (mkEffect (errno_ret ENOENT) [] []) = CheckUnmodeled.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** A DIRECTORY INSIDE /tmp, which the flat map only implies: the
    declaration names "d/f", so a key lives under "/tmp/d" and
    [Fs.Namei.fs_under] sees it there.  THE CREATE WORD ANSWERS and the
    READ WORD DECLINES.

    The create word reaches [Fs.Open.openat_create_spec] — the same arm
    a working-directory name takes — so the answer is [do_open]'s
    deterministic -EISDIR (fs/namei.c, Linux v6.18.46), the model does
    not move, and the descriptor the arm would otherwise have minted is
    refused beside it.  The -ENOENT a flat map would have reached for is
    refused too, which is what separates this answer from a lookup miss.

    The read word still declines: answering means a directory
    descriptor, and the model has no directory semantics to give one. *)
Example openat_tmp_implied_directory_create_eisdir :
  let m0 := init_model [] 0 0 demo_sp demo_limit
              (demo_input_tmp [] [([100; 47; 102], [104])] IEof) in
  let open fl eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           (open_path_mem [47; 116; 109; 112; 47; 100]%Z) (fun _ => None))
        (with_copyins [(8192, 7%nat)] eff) m0 in
  open wr_create_flags (mkEffect (errno_ret EISDIR) [] []) = CheckOk m0 []
  /\ open wr_create_flags (mkEffect 3 [] []) = CheckReject
  /\ open wr_create_flags (mkEffect (errno_ret ENOENT) [] []) = CheckReject.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** ...and the read word at the same name, on the same image, still
    fails closed — at the descriptor Linux would hand back and at the
    -EISDIR the create gets, so the decline is the arm's and not a
    disagreement about the errno.  The nested name "/tmp/d/f" itself is
    unchanged too: it carries a second component, which [Fs.Namei.tmp_name]
    refuses, so it is still the separator gate's decline and NOT this
    arm's. *)
Example openat_tmp_implied_directory_read_unmodeled :
  let m0 := init_model [] 0 0 demo_sp demo_limit
              (demo_input_tmp [] [([100; 47; 102], [104])] IEof) in
  let open bs n fl eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           (open_path_mem bs) (fun _ => None))
        (with_copyins [(8192, n)] eff) m0 in
  open [47; 116; 109; 112; 47; 100]%Z 7%nat 0%Z (mkEffect 3 [] [])
    = CheckUnmodeled
  /\ open [47; 116; 109; 112; 47; 100]%Z 7%nat 0%Z
       (mkEffect (errno_ret EISDIR) [] []) = CheckUnmodeled
  /\ open [47; 116; 109; 112; 47; 100; 47; 102]%Z 9%nat 0%Z
       (mkEffect 3 [] []) = CheckUnmodeled
  /\ open [47; 116; 109; 112; 47; 100; 47; 102]%Z 9%nat wr_create_flags
       (mkEffect 3 [] []) = CheckUnmodeled.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE READ BRANCH'S GUARD, exercised where it decides.  On the image
    above "/tmp/d" is not a key, so the read declines through the
    not-held branch whether or not [Fs.Namei.fs_under] is tested first,
    and the case above cannot tell the two orderings apart.  [Fs.valid_fs]
    admits an image holding BOTH "/tmp/d" and "/tmp/d/f" — no reality has
    both, but nothing refuses it — and there the lookup of "/tmp/d" would
    SUCCEED: without the guard the read word would mint an [FdFile] on a
    name reality makes a directory.  This is the only image on which the
    guard changes an answer, so it is the one that pins it.  The read
    still declines, at the descriptor and at the -ENOENT a lookup miss
    would have given; the create answers -EISDIR ahead of the lookup that
    would otherwise have truncated a held key, and refuses the
    descriptor.  Drop the read branch's guard and the first open below
    becomes a [CheckOk] minting fd 3; move the create's guard after the
    lookup and the -EISDIR becomes a [CheckReject]. *)
Example openat_tmp_implied_directory_unrealizable_image :
  let m0 := init_model [] 0 0 demo_sp demo_limit
              (demo_input [([47; 116; 109; 112; 47; 100], [104]);
                           ([47; 116; 109; 112; 47; 100; 47; 102], [104])] IEof) in
  let open fl eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           (open_path_mem [47; 116; 109; 112; 47; 100]%Z) (fun _ => None))
        (with_copyins [(8192, 7%nat)] eff) m0 in
  (* the image really holds both: the name is a key AND has a key under it *)
  fs_lookup (m_fs m0) [47; 116; 109; 112; 47; 100] = Some [104]
  /\ fs_under (m_fs m0) [47; 116; 109; 112; 47; 100] = true
  (* the read declines, at the descriptor and at the lookup miss's errno *)
  /\ open 0%Z (mkEffect 3 [] []) = CheckUnmodeled
  /\ open 0%Z (mkEffect (errno_ret ENOENT) [] []) = CheckUnmodeled
  (* the create answers -EISDIR ahead of the lookup; the descriptor is refused *)
  /\ open wr_create_flags (mkEffect (errno_ret EISDIR) [] []) = CheckOk m0 []
  /\ open wr_create_flags (mkEffect 3 [] []) = CheckReject.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE HONEST TWINS, without which the cases above are consistent
    with an arm that answers -EISDIR for everything under a /tmp holding
    a subdirectory.  The declaration is still SEEDED at its own key, so
    a name with a separator in it stays declarable — [State.in_tmp] has
    no slash-free condition — and a plain sibling name in
    the same declared /tmp still creates, since [Fs.Namei.fs_under] is a
    COMPONENT prefix and nothing lives under "/tmp/out.gif". *)
Example openat_tmp_implied_directory_sibling_still_creates :
  let m0 := init_model [] 0 0 demo_sp demo_limit
              (demo_input_tmp [] [([100; 47; 102], [104])] IEof) in
  let open bs n fl eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           (open_path_mem bs) (fun _ => None))
        (with_copyins [(8192, n)] eff) m0 in
  (* the nested declaration reaches the image at its own key *)
  fs_lookup (m_fs m0) [47; 116; 109; 112; 47; 100; 47; 102] = Some [104]
  (* ...and a plain sibling in the same declared /tmp still creates *)
  /\ match open tmp_gif_bytes 13%nat wr_create_flags (mkEffect 3 [] []) with
     | CheckOk m [] => fs_lookup (m_fs m) tmp_gif_key = Some []
     | _ => False
     end.
Proof. vm_compute. split; reflexivity. Qed.

(* =========================================================================
   THE PATHNAME WALK THAT WALKED OFF THE TOP OF THE ADDRESS SPACE

   [State.read_cstr_aux] stepped [a + 1] in the 64-bit word and tested
   nothing, so a pathname pointer in the last bytes of the address
   space read the bytes below the wrap and then the bytes from 0 on,
   said [CstrOk], and [Fs.Open.openat_spec] then ANSWERED the call on
   that name — a wrong answer, not a decline.  Linux refuses it:
   [strncpy_from_user] (lib/strncpy_from_user.c, [strncpy_from_user])
   returns -EFAULT for a source at or above [TASK_SIZE_MAX] and clamps
   every other scan to end below it, and [getname_flags] (fs/namei.c)
   returns that -EFAULT.  The walk now tests [State.access_okb a 1] in
   front of each byte; [State.read_cstr_aux] says why per byte and not
   once over PATH_MAX.

   The groups follow [Checks.Cases.Net.Socket]'s wrap groups: the
   wrapping call refused, a neighbouring call at the top of what
   [State.access_okb] accepts still answered, and the control that the
   bare walk really would have passed.  The last group is the case the
   per-byte test exists for: a name that STARTS below [TASK_SIZE] and
   reaches it faults there, and the ledger records only the byte below.

   THE MEMORIES MAP EXACTLY THEIR OWN BYTES and nothing else, so no
   refusal can pass because the memory stopped short; [wmem_open] would
   answer at every address and could not tell a wrapping pointer from
   any other.

   Every call is a read-only open of "a" on an image that HOLDS "a", so
   what the bare walk produced on the wrapping pointer was not an errno
   but a SUCCESS at fd 3.
   ========================================================================= *)

Definition open_a_model : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input [([97], [])] IEof).

(* ---- the wrap: 'a' in the last byte of the address space, NUL at 0 ----- *)

Definition open_wrap_pathp : word := Z_to_bv 64 (2 ^ 64 - 1).

Definition open_wrap_mem : word -> option byte :=
  fun a => if bv_eqb a open_wrap_pathp then Some 97   (* 'a' *)
           else if bv_eqb a 0 then Some 0             (* NUL *)
           else None.

Definition open_wrap_input : SyscallInput :=
  mkInput 56 [AT_FDCWD; open_wrap_pathp; 0; 0; 0; 0] open_wrap_mem (fun _ => None).

(** THE CONTROL.  The old walk read [mp a] and then [mp (a + 1)]; here
    [a + 1] is 0, and the two bytes at those addresses are 'a' and the
    NUL.  [read_bytes_map] steps the same wrapping [a + 1], so its
    answer is the byte sequence the old walk consumed, NUL included:
    the bare walk would have answered [CstrOk "a"]. *)
Example openat_wrap_would_pass_the_bare_walk :
  open_wrap_pathp + 1 = Z_to_bv 64 0
  /\ read_bytes_map open_wrap_mem open_wrap_pathp (Z_to_bv 64 2)
     = Some [Z_to_bv 8 97; Z_to_bv 8 0].
Proof. split; check_eq. Qed.

(** The walk refuses at its first byte, and the ledger counts nothing:
    [strncpy_from_user] returns before it fetches a byte. *)
Example openat_wrap_path_is_a_fault :
  read_cstr open_wrap_mem open_wrap_pathp = CstrFault
  /\ cstr_access_len_aux open_wrap_mem open_wrap_pathp path_max = 0%nat.
Proof. split; check_eq. Qed.

(** -EFAULT with an empty range is the model's answer.  The success the
    bare walk admitted — fd 3 on "a", with the two bytes it claimed
    across the wrap as the ledger — is refused, and so is an -EFAULT
    that claims those two bytes. *)
Example openat_wrapping_path_is_efault :
  check_syscall open_wrap_input
    (with_copyins [(open_wrap_pathp, 0%nat)] (mkEffect (errno_ret EFAULT) [] []))
    open_a_model
  = CheckOk open_a_model []
  /\ check_syscall open_wrap_input
       (with_copyins [(open_wrap_pathp, 2%nat)] (mkEffect 3 [] []))
       open_a_model
     = CheckReject
  /\ check_syscall open_wrap_input
       (with_copyins [(open_wrap_pathp, 2%nat)] (mkEffect (errno_ret EFAULT) [] []))
       open_a_model
     = CheckReject.
Proof. split; [|split]; check_eq. Qed.

(* ---- the neighbour: the last two bytes [State.access_okb] accepts ------- *)

(** 'a' at [TASK_SIZE - 2] and the NUL at [TASK_SIZE - 1], the last
    byte of the user address space, and nothing else.  Linux clamps the
    scan to these two bytes and finds the NUL inside them. *)
Definition open_top_pathp : word := Z_to_bv 64 (TASK_SIZE - 2).

Definition open_top_mem : word -> option byte :=
  fun a => if bv_eqb a open_top_pathp then Some 97                     (* 'a' *)
           else if bv_eqb a (Z_to_bv 64 (TASK_SIZE - 1)) then Some 0  (* NUL *)
           else None.

Definition open_top_input : SyscallInput :=
  mkInput 56 [AT_FDCWD; open_top_pathp; 0; 0; 0; 0] open_top_mem (fun _ => None).

(** The walk reads "a" and counts both bytes.  The last conjunct is why
    the test sits in front of each byte: [State.access_okb] over the
    whole PATH_MAX bound refuses this pointer, so one test placed in
    front of the walk would answer -EFAULT where Linux opens the file. *)
Example openat_path_at_the_top_reads :
  read_cstr open_top_mem open_top_pathp = CstrOk [Z_to_bv 8 97]
  /\ cstr_access_len_aux open_top_mem open_top_pathp path_max = 2%nat
  /\ access_okb open_top_pathp (Z.of_nat path_max) = false.
Proof. split; [|split]; check_eq. Qed.

(** THE NEIGHBOUR, the half that says the guard is not a blanket refusal
    of high pointers: the same read-only open of "a" is answered, with
    the success at fd 3 and the two-byte ledger, and -EFAULT is refused
    there. *)
Example openat_path_at_the_top_still_answers :
  match check_syscall open_top_input
          (with_copyins [(open_top_pathp, 2%nat)] (mkEffect 3 [] []))
          open_a_model with
  | CheckOk m [] =>
      fd_lookup (m_fds m) (Z_to_bv 64 3)
      = Some (FdFile [Z_to_bv 8 97] (Z_to_bv 64 0))
  | _ => False
  end
  /\ check_syscall open_top_input
       (with_copyins [(open_top_pathp, 2%nat)] (mkEffect (errno_ret EFAULT) [] []))
       open_a_model
     = CheckReject.
Proof. split; check_eq. Qed.

(* ---- the crossing: a name that starts below [TASK_SIZE] and reaches it -- *)

(** 'a' at [TASK_SIZE - 1] and the NUL at [TASK_SIZE] itself.  Linux
    maps no user page at [TASK_SIZE], but the memory map handed to the
    model is arbitrary, and this one answers there.  Linux clamps the
    scan to the one byte below [TASK_SIZE], reads 'a', reaches [max]
    short of [count], and returns -EFAULT (lib/strncpy_from_user.c,
    [do_strncpy_from_user]).  The walk faults at [TASK_SIZE] the same
    way, and the ledger is the one byte it read. *)
Definition open_cross_pathp : word := Z_to_bv 64 (TASK_SIZE - 1).

Definition open_cross_mem : word -> option byte :=
  fun a => if bv_eqb a open_cross_pathp then Some 97              (* 'a' *)
           else if bv_eqb a (Z_to_bv 64 TASK_SIZE) then Some 0   (* NUL *)
           else None.

Definition open_cross_input : SyscallInput :=
  mkInput 56 [AT_FDCWD; open_cross_pathp; 0; 0; 0; 0] open_cross_mem (fun _ => None).

(** THE CONTROL for the crossing: the bare walk's two bytes, NUL
    included, are there. *)
Example openat_crossing_would_pass_the_bare_walk :
  read_bytes_map open_cross_mem open_cross_pathp (Z_to_bv 64 2)
  = Some [Z_to_bv 8 97; Z_to_bv 8 0].
Proof. check_eq. Qed.

(** -EFAULT with the one byte below [TASK_SIZE] on the ledger; the
    success the bare walk admitted, and an -EFAULT whose ledger claims
    the byte AT [TASK_SIZE], are both refused. *)
Example openat_crossing_path_is_efault :
  read_cstr open_cross_mem open_cross_pathp = CstrFault
  /\ cstr_access_len_aux open_cross_mem open_cross_pathp path_max = 1%nat
  /\ check_syscall open_cross_input
       (with_copyins [(open_cross_pathp, 1%nat)] (mkEffect (errno_ret EFAULT) [] []))
       open_a_model
     = CheckOk open_a_model []
  /\ check_syscall open_cross_input
       (with_copyins [(open_cross_pathp, 2%nat)] (mkEffect 3 [] []))
       open_a_model
     = CheckReject
  /\ check_syscall open_cross_input
       (with_copyins [(open_cross_pathp, 2%nat)] (mkEffect (errno_ret EFAULT) [] []))
       open_a_model
     = CheckReject.
Proof. split; [|split; [|split; [|split]]]; check_eq. Qed.
