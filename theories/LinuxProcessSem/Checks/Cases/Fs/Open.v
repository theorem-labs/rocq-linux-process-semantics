(** * LinuxProcessSem.Checks.Cases.Fs.Open — worked examples over openat (56), close (57), ftruncate (46), faccessat (48), faccessat2 (439)

    Mirrors [Sys/Fs/Open.v], which answers to Linux [fs/open.c]: this
    file holds the worked examples for the syscalls defined there, and
    no others.

    Split out of [Checks/Examples.v], which keeps what is not
    per-syscall and re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary.

    Every pathname is resolved by [Fs.resolve]: the device pins are
    keyed by ENTRY KIND, the "/tmp/..." pins are ordinary absolute-path
    pins, and a missing or non-directory prefix is a real -ENOENT or
    -ENOTDIR.

    Ported from theorem-labs/linux-process-semantics
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
  Prelude Fs.ReadWrite.

(** Path bytes at 8192, NUL-terminated, for the examples below. *)
Definition open_path_mem (bs : list Z) : word -> option byte :=
  fun a => if (8192 <=? bv_unsigned a)%Z
           then nth_error (map (fun z => Z_to_bv 8 z) (bs ++ [0%Z]))
                  (Z.to_nat (bv_unsigned a - 8192))
           else None.

(** THE IMAGES.  [demo_fs] ships the standard root and the chain to the
    working directory, and puts each plain name at the key it resolves
    to, which is what makes these NAMESPACES a walk can reach. *)
Definition ns_open_empty : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof).

Definition ns_open_f : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input (demo_fs [([102], SFile [104; 105])]) IEof).

Definition ns_open_dir_a : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input (demo_fs [([97], SDir)]) IEof).

(* ---------------------------------------------------------- the dirfd *)

(** A LIVE fd as dirfd is still an unmodeled relative-to-a-dirfd open,
    and still fails closed.  Truncation does not widen AT_FDCWD to "any
    dirfd whose low half looks plausible". *)
Example openat_live_dirfd_still_unmodeled :
  check_syscall
    (mkInput 56 [1; 8192; 0; 0; 0; 0] (open_path_mem [102%Z]) (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret ENOENT) [] []))
    ns_open_empty
  = CheckUnmodeled.
Proof. check_eq. Qed.

Example at_fdcwd32_is_the_low_half_of_minus_100_open :
  AT_FDCWD32 = Z_to_bv 64 4294967196.
Proof. check_eq. Qed.

(** The EMPTY pathname is -ENOENT ahead of resolution, so an image that
    held an empty key would still not be reached by it — and under the
    namespace an empty key is not a key at all. *)
Example openat_empty_path_enoent :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
       (fun a => if bv_eqb a 8192 then Some 0 else None)
       (fun _ => None))
    (with_copyins [(8192, 1%nat)] (mkEffect (errno_ret ENOENT) [] []))
    ns_open_empty
  = CheckOk ns_open_empty [].
Proof. check_eq. Qed.

(** ...and O_CREAT does not rescue it: the -ENOENT is [getname_flags]'s
    and precedes every flag. *)
Example openat_empty_path_beats_o_creat :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 wr_create_flags; 420; 0; 0]
       (fun a => if bv_eqb a 8192 then Some 0 else None)
       (fun _ => None))
    (with_copyins [(8192, 1%nat)] (mkEffect (errno_ret ENOENT) [] []))
    ns_open_empty
  = CheckOk ns_open_empty []
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 wr_create_flags; 420; 0; 0]
          (fun a => if bv_eqb a 8192 then Some 0 else None)
          (fun _ => None))
       (with_copyins [(8192, 1%nat)] (mkEffect 3 [] []))
       ns_open_empty
     = CheckReject.
Proof. split; check_eq. Qed.

(** ...and beside it, [getname_flags]' -ENOMEM: [getname_flags]
    allocates the name before it copies a byte (fs/namei.c:146-148,
    Linux v6.18.46), so the -ENOMEM stands where the copy then answers
    the empty name's -ENOENT (167-171) or an unmapped byte's -EFAULT
    (161-165), and beside every answer past them, with nothing copied in
    ([Fs.Namei.getname_refusals]).  [faccessat] fetches through the same
    [getname_flags], in [user_path_at] (fs/namei.c:3211-3219), so its
    arms admit it too. *)
Example openat_getname_enomem_copies_nothing :
  let call (nr : word) mp := check_syscall
        (mkInput nr [AT_FDCWD; 8192; 0; 0; 0; 0] mp (fun _ => None))
        (mkEffect (errno_ret ENOMEM) [] []) ns_open_empty in
  call 56 (open_path_mem []) = CheckOk ns_open_empty []
  /\ call 56 (fun _ => None) = CheckOk ns_open_empty []
  /\ call 56 (open_path_mem [102%Z]) = CheckOk ns_open_empty []
  /\ call 48 (open_path_mem []) = CheckOk ns_open_empty []
  /\ call 48 (fun _ => None) = CheckOk ns_open_empty []
  /\ call 48 (open_path_mem [102%Z]) = CheckOk ns_open_empty [].
Proof. vm_compute; split_conj; check_eq. Qed.

(** ...and not with the copy-in on "" or on an unmapped pointer, where
    no answer reads the name and then fails for memory. *)
Example openat_getname_enomem_with_the_copyin_rejected :
  let call (nr : word) mp := check_syscall
        (mkInput nr [AT_FDCWD; 8192; 0; 0; 0; 0] mp (fun _ => None))
        (with_copyins [(8192, 1%nat)] (mkEffect (errno_ret ENOMEM) [] []))
        ns_open_empty in
  call 56 (open_path_mem []) = CheckReject
  /\ call 56 (fun _ => None) = CheckReject
  /\ call 48 (open_path_mem []) = CheckReject
  /\ call 48 (fun _ => None) = CheckReject.
Proof. vm_compute; split_conj; check_eq. Qed.

(** ...and nothing the walk or the descriptor table adds there: the
    walk's -EACCES needs a component neither "" nor a fault hands it,
    and the -EMFILE of [get_unused_fd_flags] comes only after [getname]
    in [do_sys_openat2] (fs/open.c:1431-1435).  [do_faccessat] tests the
    mode before [user_path_at] (fs/open.c, Linux v6.18.46), so a bad
    mode's -EINVAL has no -ENOMEM beside it. *)
Example openat_getname_enomem_needs_getname :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0] (open_path_mem []) (fun _ => None))
    (with_copyins [(8192, 1%nat)] (mkEffect (errno_ret EACCES) [] []))
    ns_open_empty
  = CheckReject
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0] (open_path_mem []) (fun _ => None))
       (with_copyins [(8192, 1%nat)] (mkEffect (errno_ret EMFILE) [] []))
       ns_open_empty
     = CheckReject
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (with_copyins [(8192, 1%nat)] (mkEffect (errno_ret EACCES) [] []))
       ns_open_empty
     = CheckReject
  /\ check_syscall
       (mkInput 48 [AT_FDCWD; 8192; 8; 0; 0; 0] (open_path_mem []) (fun _ => None))
       (mkEffect (errno_ret ENOMEM) [] [])
       ns_open_empty
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(* ------------------------------------------------------ the flag words *)

(** O_NONBLOCK is an IGNORED bit, on every modeled shape: the open lands
    in exactly the model the same open without it lands in.  Only a Rocq
    literal can say that, because it is an EQUALITY BETWEEN TWO FLAG
    WORDS — a probe runs the words it runs, so it can show the
    O_NONBLOCK open succeeds but never that the two agree. *)
Example o_nonblock_is_an_ignored_open_flag :
  let open m fl := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           (open_path_mem [102%Z]) (fun _ => None))
        (with_copyins [(8192, 2%nat)] (mkEffect 3 [] [])) m in
  let ok r := match r with CheckOk _ _ => true | _ => false end in
  open ns_open_f (0 + O_NONBLOCK)%Z = open ns_open_f 0%Z
  /\ open ns_open_f (wr_create_flags + O_NONBLOCK)%Z
     = open ns_open_f wr_create_flags
  /\ open ns_open_empty (excl_create_flags + O_NONBLOCK)%Z
     = open ns_open_empty excl_create_flags
  /\ open ns_open_empty (excl_create_flags + O_TRUNC + O_NONBLOCK)%Z
     = open ns_open_empty (excl_create_flags + O_TRUNC)%Z
  /\ open ns_open_f (O_RDWR + O_NONBLOCK)%Z = open ns_open_f O_RDWR
  (* every one of those five is a SUCCESS at fd 3, not two matching refusals *)
  /\ ok (open ns_open_f (0 + O_NONBLOCK)%Z) = true
  /\ ok (open ns_open_f (wr_create_flags + O_NONBLOCK)%Z) = true
  /\ ok (open ns_open_empty (excl_create_flags + O_NONBLOCK)%Z) = true
  /\ ok (open ns_open_empty (excl_create_flags + O_TRUNC + O_NONBLOCK)%Z) = true
  /\ ok (open ns_open_f (O_RDWR + O_NONBLOCK)%Z) = true
  (* and the flags next to them are still declined, O_NONBLOCK or not *)
  /\ open ns_open_f 256%Z = CheckUnmodeled                 (* O_NOCTTY *)
  /\ open ns_open_f (256 + O_NONBLOCK)%Z = CheckUnmodeled
  /\ open ns_open_f 1024%Z = CheckUnmodeled                (* O_APPEND *)
  /\ open ns_open_f (O_RDWR + O_APPEND)%Z = CheckUnmodeled
  /\ open ns_open_f (O_RDWR + O_EXCL)%Z = CheckUnmodeled
  /\ open ns_open_f (O_RDWR + O_DIRECTORY)%Z = CheckUnmodeled.
Proof. vm_compute. repeat split; check_eq. Qed.

(* ------------------------------------------- the separator gate is gone *)

(** AN ABSOLUTE PATH IS RESOLVED, where the pre-namespace arm declined
    every path with a separator.  "/work/f" is the key "f" resolves to,
    so the two opens land in the same model — which is the equality only
    a Rocq literal can state. *)
Definition abs_work_f : list Z := [47; 119; 111; 114; 107; 47; 102]%Z.

Example openat_absolute_path_reads_the_key_it_names :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
       (open_path_mem abs_work_f) (fun _ => None))
    (with_copyins [(8192, 8%nat)] (mkEffect 3 [] []))
    ns_open_f
  = CheckOk (with_fds (fd_insert (m_fds ns_open_f) 3
                         (FdFile 1 (Z_to_bv 64 0))) ns_open_f) []
  (* ...which is exactly where the relative spelling lands *)
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem [102%Z]) (fun _ => None))
       (with_copyins [(8192, 2%nat)] (mkEffect 3 [] []))
       ns_open_f
     = CheckOk (with_fds (fd_insert (m_fds ns_open_f) 3
                            (FdFile 1 (Z_to_bv 64 0))) ns_open_f) [].
Proof. split; check_eq. Qed.

(** A CREATE UNDER A MISSING PARENT is -ENOENT, where the pre-namespace
    arm minted a key spelled "/a/b".  That admission is what the
    separator gate existed to stop, and resolution replaces both. *)
Example openat_create_under_a_missing_parent_is_enoent :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 wr_create_flags; 420; 0; 0]
       (open_path_mem [97; 47; 98]%Z) (fun _ => None))
    (with_copyins [(8192, 4%nat)] (mkEffect (errno_ret ENOENT) [] []))
    ns_open_empty
  = CheckOk ns_open_empty []
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 wr_create_flags; 420; 0; 0]
          (open_path_mem [97; 47; 98]%Z) (fun _ => None))
       (with_copyins [(8192, 4%nat)] (mkEffect 3 [] []))
       ns_open_empty
     = CheckReject.
Proof. split; check_eq. Qed.

(** A NAME UNDER A FILE is -ENOTDIR, which is the real errno the
    [unmodeled] separator pin used to stand in for. *)
Example openat_under_a_file_is_enotdir :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
       (open_path_mem [102; 47; 98]%Z) (fun _ => None))
    (with_copyins [(8192, 4%nat)] (mkEffect (errno_ret ENOTDIR) [] []))
    ns_open_f
  = CheckOk ns_open_f []
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem [102; 47; 98]%Z) (fun _ => None))
       (with_copyins [(8192, 4%nat)] (mkEffect (errno_ret ENOENT) [] []))
       ns_open_f
     = CheckReject.
Proof. split; check_eq. Qed.

(** THE CREATE LANDS AT THE RESOLVED KEY, not at the pathname.  A spec
    that kept keying the map by the raw name would mint "g" here and
    this pin would catch it. *)
Example openat_create_mints_the_resolved_key :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 wr_create_flags; 420; 0; 0]
       (open_path_mem [103%Z]) (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect 3 [] []))
    ns_open_empty
  = CheckOk (with_fds (fd_insert (m_fds ns_open_empty) 3
                         (FdFileW 1 (Z_to_bv 64 0)))
               (with_fs (Fs.fs_create_file (m_fs ns_open_empty) (wk [103]) [])
                  ns_open_empty)) [].
Proof. check_eq. Qed.

(** THE OTHER WAY INTO THE SAME EXIT: a regular file that is ALREADY
    THERE is truncated, at the key it was found under, and the
    descriptor is the one the create hands back.  The two ways in are
    the two rows of [Fs.Open.openat_create_spec] that mint a
    descriptor, and pinning only the absent one would leave every copy
    onto an existing destination unchecked — which is the whole of what
    a [cp onto a file that exists] does.

    The bytes are what say TRUNCATION happened rather than a reopen:
    [ns_open_f] holds two bytes at this key and the model the checker
    accepts holds none. *)
Example openat_create_onto_an_existing_file_truncates :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 wr_create_flags; 420; 0; 0]
       (open_path_mem [102%Z]) (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect 3 [] []))
    ns_open_f
  = CheckOk (with_fds (fd_insert (m_fds ns_open_f) 3
                         (FdFileW 1 (Z_to_bv 64 0)))
               (with_fs (Fs.fs_set_ino_data (m_fs ns_open_f) 1 [])
                  ns_open_f)) []
  (* DOCUMENTARY, not an independent check: [check_syscall] is a
     function and this call's arguments are the first conjunct's, so
     this follows from it.  It is kept because naming the model that
     KEPT the old bytes is what makes the line above readable as a
     statement about truncation rather than about reopening. *)
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 wr_create_flags; 420; 0; 0]
          (open_path_mem [102%Z]) (fun _ => None))
       (with_copyins [(8192, 2%nat)] (mkEffect 3 [] []))
       ns_open_f
     <> CheckOk (with_fds (fd_insert (m_fds ns_open_f) 3
                             (FdFileW 1 (Z_to_bv 64 0))) ns_open_f) [].
Proof. split; [check_eq | vm_compute; discriminate]. Qed.

(** A WRITE OPEN OF A FILE THAT EXISTS ADMITS -ETXTBSY beside its own
    answers ([Fs.Open.open_write_existing]): the file may be the one an
    [execve] runs, whose write access [exe_file_deny_write_access] denies
    (fs/exec.c:798, Linux v6.18.46), and [do_dentry_open]'s
    [get_write_access] answers -ETXTBSY (fs/open.c:925-928, :883-885)
    before [handle_truncate] runs, both in [do_open] (fs/namei.c:3974-3979).  So the model
    is left as it was, the two bytes of "f" included, on the clobbering
    word, the append word, O_RDWR and O_RDWR|O_TRUNC, and on a reopen of
    "f" through "/proc/self/fd/3" where descriptor 3 reads it.  Refused:
    on an O_RDONLY open (no write access is taken), on a file the open
    CREATES (a fresh inode nothing executes), and on an O_EXCL open of
    an existing name (-EEXIST comes first, fs/namei.c:3949-3950). *)
Example openat_write_open_of_an_existing_file_admits_etxtbsy :
  let call (fl : Z) (p : list Z) (m : Model) :=
        check_syscall
          (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
             (open_path_mem p) (fun _ => None))
          (with_copyins [(8192, S (length p))] (mkEffect (errno_ret ETXTBSY) [] [])) m in
  let m3 := with_fds (fd_insert (m_fds ns_open_f) 3 (FdFile 1 (Z_to_bv 64 0))) ns_open_f in
  let procfd3 := [47; 112; 114; 111; 99; 47; 115; 101; 108; 102; 47; 102; 100; 47; 51]%Z in
  call wr_create_flags [102]%Z ns_open_f = CheckOk ns_open_f []
  /\ call append_create_flags [102]%Z ns_open_f = CheckOk ns_open_f []
  /\ call O_RDWR [102]%Z ns_open_f = CheckOk ns_open_f []
  /\ call (O_RDWR + O_TRUNC)%Z [102]%Z ns_open_f = CheckOk ns_open_f []
  /\ call wr_create_flags procfd3 m3 = CheckOk m3 []
  /\ call append_create_flags procfd3 m3 = CheckOk m3 []
  /\ call 0%Z [102]%Z ns_open_f = CheckReject
  /\ call wr_create_flags [103]%Z ns_open_empty = CheckReject
  /\ call excl_create_flags [102]%Z ns_open_f = CheckReject.
Proof. vm_compute; split_conj; check_eq. Qed.

(** Two files, "f" (inode 1) and "g" (inode 2). *)
Definition ns_open_fg : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input (demo_fs [([102], SFile [104; 105]); ([103], SFile [106])]) IEof).

(** A LIVE WRITER RULES -ETXTBSY OUT ([Fs.Open.ino_write_held]).  The
    deny an [execve] holds and a writer share the inode's
    [i_writecount]: [get_write_access] fails only while it is negative
    (include/linux/fs.h:3217, Linux v6.18.46) and [deny_write_access]
    takes a deny only while it is not positive (:3222), and
    [do_dentry_open] (fs/open.c:926-929) took write access for
    descriptor 3 when it opened, which it keeps to its last fput, where
    [__fput] (fs/file_table.c:512) drops it.  So while descriptor 3
    writes inode 1, a write open of that inode refuses -ETXTBSY: by the
    name "f", by a second name "g" of the same inode, and through
    "/proc/self/fd/3", for a descriptor of each of the three write kinds.
    A writer of ANOTHER inode, and a reader of this one, leave it
    admitted. *)
Example openat_write_open_beside_a_live_writer_refuses_etxtbsy :
  let call (fl : Z) (p : list Z) (m : Model) :=
        check_syscall
          (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
             (open_path_mem p) (fun _ => None))
          (with_copyins [(8192, S (length p))] (mkEffect (errno_ret ETXTBSY) [] [])) m in
  let with3 (e : FdEntry) (m : Model) := with_fds (fd_insert (m_fds m) 3 e) m in
  let mw := with3 (FdFileW 1 (Z_to_bv 64 0)) ns_open_f in
  let ma := with3 (FdFileA 1 (Z_to_bv 64 0)) ns_open_f in
  let mrw := with3 (FdFileRW 1 (Z_to_bv 64 0)) ns_open_f in
  let mg := with3 (FdFileW 1 (Z_to_bv 64 0))
              (with_fs (Fs.fs_set (m_fs ns_open_f) (wk [103]) (EFile 1)) ns_open_f) in
  let mo := with3 (FdFileW 2 (Z_to_bv 64 0)) ns_open_fg in
  let mr := with3 (FdFile 1 (Z_to_bv 64 0)) ns_open_f in
  let procfd3 := [47; 112; 114; 111; 99; 47; 115; 101; 108; 102; 47; 102; 100; 47; 51]%Z in
  call wr_create_flags [102]%Z mw = CheckReject
  /\ call append_create_flags [102]%Z ma = CheckReject
  /\ call O_RDWR [102]%Z mrw = CheckReject
  /\ call (O_RDWR + O_TRUNC)%Z [102]%Z mw = CheckReject
  /\ call wr_create_flags [103]%Z mg = CheckReject
  /\ call wr_create_flags procfd3 mw = CheckReject
  /\ call append_create_flags procfd3 mrw = CheckReject
  /\ call wr_create_flags [102]%Z mo = CheckOk mo []
  /\ call wr_create_flags [102]%Z mr = CheckOk mr [].
Proof. vm_compute; split_conj; check_eq. Qed.

(* ------------------------------------------------ directories as entries *)

(** A DIRECTORY OPENS READ-ONLY, as a descriptor on its key.  That is
    where "." and ".." land, and where an ordinary directory name lands
    too — the pre-namespace arm could answer only the two dot spellings
    and only because [State.FdDir] carried no path. *)
Example openat_directory_answers :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
       (open_path_mem [97%Z]) (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect 3 [] []))
    ns_open_dir_a
  = CheckOk (with_fds (fd_insert (m_fds ns_open_dir_a) 3
                         (FdDir (wk [97]))) ns_open_dir_a) []
  (* "." is the working directory *)
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem [46%Z]) (fun _ => None))
       (with_copyins [(8192, 2%nat)] (mkEffect 3 [] []))
       ns_open_dir_a
     = CheckOk (with_fds (fd_insert (m_fds ns_open_dir_a) 3
                            (FdDir Fs.default_cwd)) ns_open_dir_a) []
  (* ".." is its parent *)
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem [46; 46]%Z) (fun _ => None))
       (with_copyins [(8192, 3%nat)] (mkEffect 3 [] []))
       ns_open_dir_a
     = CheckOk (with_fds (fd_insert (m_fds ns_open_dir_a) 3
                            (FdDir Fs.root)) ns_open_dir_a) [].
Proof. repeat split; check_eq. Qed.

(** A DIRECTORY IS -EISDIR ON THE WRITE WORDS and -EEXIST on the
    exclusive ones, which is [do_open]'s order: the O_EXCL test runs
    before the [d_is_dir] test. *)
Example openat_directory_write_words :
  let open fl := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           (open_path_mem [97%Z]) (fun _ => None))
        (with_copyins [(8192, 2%nat)]
           (mkEffect (errno_ret EISDIR) [] [])) ns_open_dir_a in
  let opex fl := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           (open_path_mem [97%Z]) (fun _ => None))
        (with_copyins [(8192, 2%nat)]
           (mkEffect (errno_ret EEXIST) [] [])) ns_open_dir_a in
  open wr_create_flags = CheckOk ns_open_dir_a []
  /\ open append_create_flags = CheckOk ns_open_dir_a []
  /\ open O_RDWR = CheckOk ns_open_dir_a []
  /\ opex excl_create_flags = CheckOk ns_open_dir_a []
  /\ opex (O_RDWR + O_CREAT + O_EXCL)%Z = CheckOk ns_open_dir_a []
  (* and the two answers are not interchangeable *)
  /\ opex wr_create_flags = CheckReject
  /\ open excl_create_flags = CheckReject.
Proof. repeat split; check_eq. Qed.

(** O_DIRECTORY opens a directory and is -ENOTDIR on a file, with the
    -ENOTDIR type-blind: it does not turn on which kind of
    non-directory the entry is. *)
Example openat_o_directory_answers :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 O_DIRECTORY; 0; 0; 0]
       (open_path_mem [97%Z]) (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect 3 [] []))
    ns_open_dir_a
  = CheckOk (with_fds (fd_insert (m_fds ns_open_dir_a) 3
                         (FdDir (wk [97]))) ns_open_dir_a) []
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 O_DIRECTORY; 0; 0; 0]
          (open_path_mem [102%Z]) (fun _ => None))
       (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret ENOTDIR) [] []))
       ns_open_f
     = CheckOk ns_open_f []
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 O_DIRECTORY; 0; 0; 0]
          (open_path_mem [103%Z]) (fun _ => None))
       (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret ENOENT) [] []))
       ns_open_f
     = CheckOk ns_open_f [].
Proof. repeat split; check_eq. Qed.

(* ------------------------------------------- the trailing-slash table *)

(** WITH O_CREAT a trailing separator is -EISDIR BEFORE any lookup, so
    it is the answer on a MISSING name as well as on a present one, and
    nothing is created.  Without O_CREAT the same separator is -ENOTDIR
    on a non-directory and nothing at all on a directory. *)
Example openat_trailing_slash_table :
  (* O_CREAT on an absent name: -EISDIR, and no key minted *)
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 wr_create_flags; 420; 0; 0]
       (open_path_mem [103; 47]%Z) (fun _ => None))
    (with_copyins [(8192, 3%nat)] (mkEffect (errno_ret EISDIR) [] []))
    ns_open_empty
  = CheckOk ns_open_empty []
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 wr_create_flags; 420; 0; 0]
          (open_path_mem [103; 47]%Z) (fun _ => None))
       (with_copyins [(8192, 3%nat)] (mkEffect 3 [] []))
       ns_open_empty
     = CheckReject
  (* O_CREAT|O_EXCL on a present FILE: still -EISDIR, not the -EEXIST the
     same word gives without the separator *)
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 excl_create_flags; 420; 0; 0]
          (open_path_mem [102; 47]%Z) (fun _ => None))
       (with_copyins [(8192, 3%nat)] (mkEffect (errno_ret EISDIR) [] []))
       ns_open_f
     = CheckOk ns_open_f []
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 excl_create_flags; 420; 0; 0]
          (open_path_mem [102; 47]%Z) (fun _ => None))
       (with_copyins [(8192, 3%nat)] (mkEffect (errno_ret EEXIST) [] []))
       ns_open_f
     = CheckReject
  (* without O_CREAT: -ENOTDIR on the file *)
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem [102; 47]%Z) (fun _ => None))
       (with_copyins [(8192, 3%nat)] (mkEffect (errno_ret ENOTDIR) [] []))
       ns_open_f
     = CheckOk ns_open_f []
  (* ...and nothing at all on the directory *)
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem [97; 47]%Z) (fun _ => None))
       (with_copyins [(8192, 3%nat)] (mkEffect 3 [] []))
       ns_open_dir_a
     = CheckOk (with_fds (fd_insert (m_fds ns_open_dir_a) 3
                            (FdDir (wk [97]))) ns_open_dir_a) [].
Proof. repeat split; check_eq. Qed.

(** THE LAST COMPONENT'S KIND IS WHAT SEPARATES "./" FROM "d/" under
    O_EXCL, and it is the cell [Fs.resolve]'s [LastKind] exists for:
    [open_last_lookups] sends "." to [handle_dots] before
    [lookup_fast_for_open] is called, so the -EISDIR never fires and
    [do_open]'s -EEXIST answers instead. *)
Example openat_creat_trailing_slash_reads_the_last_kind :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 excl_create_flags; 420; 0; 0]
       (open_path_mem [46; 47]%Z) (fun _ => None))
    (with_copyins [(8192, 3%nat)] (mkEffect (errno_ret EEXIST) [] []))
    ns_open_dir_a
  = CheckOk ns_open_dir_a []
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 excl_create_flags; 420; 0; 0]
          (open_path_mem [97; 47]%Z) (fun _ => None))
       (with_copyins [(8192, 3%nat)] (mkEffect (errno_ret EISDIR) [] []))
       ns_open_dir_a
     = CheckOk ns_open_dir_a [].
Proof. split; check_eq. Qed.

(* ------------------------------------------------ the devices, by kind *)

(** THE DEVICES ARE ENTRIES.  [Fs.standard_root] puts an
    [Fs.EDev DevNull] at "/dev/null" and an [Fs.EDev DevUrandom] at
    "/dev/urandom", and the arm reaches them by WALKING rather than by
    matching a byte string — so "/dev//null" and "/dev/./null" reach the
    same entry. *)
Definition devnull_bytes : list Z := [47; 100; 101; 118; 47; 110; 117; 108; 108]%Z.
Definition devnull_dotted : list Z :=
  [47; 100; 101; 118; 47; 46; 47; 110; 117; 108; 108]%Z.
Definition urandom_bytes : list Z :=
  [47; 100; 101; 118; 47; 117; 114; 97; 110; 100; 111; 109]%Z.

Example devnull_opens_by_entry_kind :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
       (open_path_mem devnull_bytes) (fun _ => None))
    (with_copyins [(8192, 10%nat)] (mkEffect 3 [] []))
    ns_open_empty
  = CheckOk (with_fds (fd_insert (m_fds ns_open_empty) 3
                         (FdDevNull true false)) ns_open_empty) []
  (* the dotted spelling reaches the same entry, which the byte-string
     match could not *)
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem devnull_dotted) (fun _ => None))
       (with_copyins [(8192, 12%nat)] (mkEffect 3 [] []))
       ns_open_empty
     = CheckOk (with_fds (fd_insert (m_fds ns_open_empty) 3
                            (FdDevNull true false)) ns_open_empty) [].
Proof. split; check_eq. Qed.

(** The write words mint the write-only entry, O_EXCL is -EEXIST and
    O_DIRECTORY is -ENOTDIR — the flag table the kind carries. *)
Example devnull_flag_table :
  let open fl eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           (open_path_mem devnull_bytes) (fun _ => None))
        (with_copyins [(8192, 10%nat)] eff) ns_open_empty in
  open wr_create_flags (mkEffect 3 [] [])
  = CheckOk (with_fds (fd_insert (m_fds ns_open_empty) 3
                         (FdDevNull false true)) ns_open_empty) []
  /\ open append_create_flags (mkEffect 3 [] [])
     = CheckOk (with_fds (fd_insert (m_fds ns_open_empty) 3
                            (FdDevNull false true)) ns_open_empty) []
  /\ open O_RDWR (mkEffect 3 [] [])
     = CheckOk (with_fds (fd_insert (m_fds ns_open_empty) 3
                            (FdDevNull true true)) ns_open_empty) []
  /\ open excl_create_flags (mkEffect (errno_ret EEXIST) [] [])
     = CheckOk ns_open_empty []
  /\ open O_DIRECTORY (mkEffect (errno_ret ENOTDIR) [] [])
     = CheckOk ns_open_empty [].
Proof. repeat split; check_eq. Qed.

(** /dev/urandom opens read-only on the read word, answers the same
    -EEXIST and -ENOTDIR, and gives a descriptor on every write word,
    with the access mode the word asks for: [devlist] gives the device
    mode 0666 (drivers/char/mem.c:701, Linux v6.18.46) and
    [urandom_fops] has a [write_iter] (drivers/char/random.c:1572-1574),
    so the write words open it.  The mode the descriptor carries is
    what the later [read] and [write] arms read. *)
Example urandom_flag_table :
  let open fl eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           (open_path_mem urandom_bytes) (fun _ => None))
        (with_copyins [(8192, 13%nat)] eff) ns_open_empty in
  open 0%Z (mkEffect 3 [] [])
  = CheckOk (with_fds (fd_insert (m_fds ns_open_empty) 3 (FdUrandom true false))
               ns_open_empty) []
  /\ open excl_create_flags (mkEffect (errno_ret EEXIST) [] [])
     = CheckOk ns_open_empty []
  /\ open O_DIRECTORY (mkEffect (errno_ret ENOTDIR) [] [])
     = CheckOk ns_open_empty []
  /\ open wr_create_flags (mkEffect 3 [] [])
     = CheckOk (with_fds (fd_insert (m_fds ns_open_empty) 3 (FdUrandom false true))
                  ns_open_empty) []
  /\ open append_create_flags (mkEffect 3 [] [])
     = CheckOk (with_fds (fd_insert (m_fds ns_open_empty) 3 (FdUrandom false true))
                  ns_open_empty) []
  /\ open O_RDWR (mkEffect 3 [] [])
     = CheckOk (with_fds (fd_insert (m_fds ns_open_empty) 3 (FdUrandom true true))
                  ns_open_empty) []
  (* a write word does not mint the read-only descriptor *)
  /\ open wr_create_flags (mkEffect 3 [] [])
     <> CheckOk (with_fds (fd_insert (m_fds ns_open_empty) 3 (FdUrandom true false))
                  ns_open_empty) [].
Proof.
  cbv zeta; split_conj; [check_eq .. | vm_compute; intro Hc; discriminate Hc].
Qed.

(** AN IMAGE THAT PUTS A FILE AT THE DEVICE'S KEY simply has a file
    there, and the file arms answer it: the kind carries the device. *)
Definition ns_file_at_devnull : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input
       (Fs.fs_create_file (demo_fs []) devnull_path [122]) IEof).

Example a_file_at_the_device_key_takes_the_file_arm :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
       (open_path_mem devnull_bytes) (fun _ => None))
    (with_copyins [(8192, 10%nat)] (mkEffect 3 [] []))
    ns_file_at_devnull
  = CheckOk (with_fds (fd_insert (m_fds ns_file_at_devnull) 3
                         (FdFile 1 (Z_to_bv 64 0)))
               ns_file_at_devnull) [].
Proof. check_eq. Qed.

(* ------------------------------------------------- /tmp is an ordinary key *)

(** "/tmp/out.gif" is a key like any other: [Fs.standard_root] ships
    "/tmp" as a directory, so the create resolves. *)
Definition tmp_out_gif : list Z :=
  [47; 116; 109; 112; 47; 111; 117; 116; 46; 103; 105; 102]%Z.

Definition tmp_out_gif_key : Fs.path :=
  Fs.child_key Fs.tmp_dir
    (map (fun z => Z_to_bv 8 z) [111; 117; 116; 46; 103; 105; 102]%Z).

Example openat_tmp_is_an_ordinary_absolute_key :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 wr_create_flags; 420; 0; 0]
       (open_path_mem tmp_out_gif) (fun _ => None))
    (with_copyins [(8192, 13%nat)] (mkEffect 3 [] []))
    ns_open_empty
  = CheckOk (with_fds (fd_insert (m_fds ns_open_empty) 3
                         (FdFileW 1 (Z_to_bv 64 0)))
               (with_fs (Fs.fs_create_file (m_fs ns_open_empty) tmp_out_gif_key [])
                  ns_open_empty)) []
  (* ...and a read of a key /tmp does NOT hold is a real -ENOENT, where
     the pre-namespace arm declined it *)
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem tmp_out_gif) (fun _ => None))
       (with_copyins [(8192, 13%nat)] (mkEffect (errno_ret ENOENT) [] []))
       ns_open_empty
     = CheckOk ns_open_empty [].
Proof. split; check_eq. Qed.

(* ------------------------------------- an absence under /dev is -ENOENT *)

(** A NAME THE WALK DOES NOT FIND UNDER /dev IS -ENOENT, and the create
    word creates there.  The image describes /dev completely at launch
    and the kernel makes no device node during the run ([Fs.dev_dir]
    carries the argument; in Linux v6.18.46 a devtmpfs node is made by
    [devtmpfs_create_node], drivers/base/devtmpfs.c:129-154, when a
    driver-core device is registered), so /dev is an ordinary folder
    here.  Both flag halves are pinned, each with the answer beside it
    refused. *)
Definition devzero_bytes : list Z := [47; 100; 101; 118; 47; 122; 101; 114; 111]%Z.
Definition tmpzero_bytes : list Z := [47; 116; 109; 112; 47; 122; 101; 114; 111]%Z.

Definition devzero_key : Fs.path :=
  Fs.child_key Fs.dev_dir (map (fun z => Z_to_bv 8 z) [122; 101; 114; 111]%Z).
Definition tmpzero_key : Fs.path :=
  Fs.child_key Fs.tmp_dir (map (fun z => Z_to_bv 8 z) [122; 101; 114; 111]%Z).

Example devzero_open_is_enoent_and_create_succeeds :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
       (open_path_mem devzero_bytes) (fun _ => None))
    (with_copyins [(8192, 10%nat)] (mkEffect (errno_ret ENOENT) [] []))
    ns_open_empty
  = CheckOk ns_open_empty []
  (* a descriptor on the read word is refused *)
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem devzero_bytes) (fun _ => None))
       (with_copyins [(8192, 10%nat)] (mkEffect 3 [] []))
       ns_open_empty
     = CheckReject
  (* the create word creates the name, a regular file *)
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 wr_create_flags; 420; 0; 0]
          (open_path_mem devzero_bytes) (fun _ => None))
       (with_copyins [(8192, 10%nat)] (mkEffect 3 [] []))
       ns_open_empty
     = CheckOk (with_fds (fd_insert (m_fds ns_open_empty) 3
                            (FdFileW 1 (Z_to_bv 64 0)))
                  (with_fs (Fs.fs_create_file (m_fs ns_open_empty) devzero_key [])
                     ns_open_empty)) []
  (* and its -ENOENT is refused *)
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 wr_create_flags; 420; 0; 0]
          (open_path_mem devzero_bytes) (fun _ => None))
       (with_copyins [(8192, 10%nat)] (mkEffect (errno_ret ENOENT) [] []))
       ns_open_empty
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** THE TWIN: the same name under /tmp answers the same way. *)
Example absent_under_tmp_still_answers :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
       (open_path_mem tmpzero_bytes) (fun _ => None))
    (with_copyins [(8192, 10%nat)] (mkEffect (errno_ret ENOENT) [] []))
    ns_open_empty
  = CheckOk ns_open_empty []
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 wr_create_flags; 420; 0; 0]
          (open_path_mem tmpzero_bytes) (fun _ => None))
       (with_copyins [(8192, 10%nat)] (mkEffect 3 [] []))
       ns_open_empty
     = CheckOk (with_fds (fd_insert (m_fds ns_open_empty) 3
                            (FdFileW 1 (Z_to_bv 64 0)))
                  (with_fs (Fs.fs_create_file (m_fs ns_open_empty) tmpzero_key [])
                     ns_open_empty)) [].
Proof. split; check_eq. Qed.

(** ONE LEVEL DOWN, the same.  A numbered node under /dev/pts is made by
    [devpts_pty_new] (fs/devpts/inode.c:512-547), which [ptmx_open]
    (drivers/tty/pty.c:790-869) calls at drivers/tty/pty.c:842, and the
    image has no entry kind an open of /dev/ptmx could reach, so an
    image that DECLARES /dev/pts and nothing in it answers -ENOENT
    there.  The control beside it is a regular file the image declares
    under /dev, which opens as a file. *)
Definition devpts_key : Fs.path :=
  Fs.child_key Fs.dev_dir (map (fun z => Z_to_bv 8 z) [112; 116; 115]%Z).
Definition devfoo_key : Fs.path :=
  Fs.child_key Fs.dev_dir (map (fun z => Z_to_bv 8 z) [102; 111; 111]%Z).

Definition ns_open_devpts : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input (Fs.fs_set (demo_fs []) devpts_key EDir) IEof).

Definition ns_open_devfoo : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input (Fs.fs_create_file (demo_fs []) devfoo_key [104]) IEof).

Example open_under_a_declared_devpts_is_enoent :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
       (open_path_mem [47; 100; 101; 118; 47; 112; 116; 115; 47; 48]%Z)
       (fun _ => None))
    (with_copyins [(8192, 11%nat)] (mkEffect (errno_ret ENOENT) [] []))
    ns_open_devpts
  = CheckOk ns_open_devpts []
  (* and a DECLARED regular file under /dev opens as a file *)
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem [47; 100; 101; 118; 47; 102; 111; 111]%Z)
          (fun _ => None))
       (with_copyins [(8192, 9%nat)] (mkEffect 3 [] []))
       ns_open_devfoo
     = CheckOk (with_fds (fd_insert (m_fds ns_open_devfoo) 3
                            (FdFile 1 (Z_to_bv 64 0)))
                  ns_open_devfoo) [].
Proof. split; check_eq. Qed.

(** ... AND THE TWO DECLARED DEVICES ANSWER beside the absent names. *)
Example the_declared_devices_answer_beside_an_absent_name :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
       (open_path_mem devnull_bytes) (fun _ => None))
    (with_copyins [(8192, 10%nat)] (mkEffect 3 [] []))
    ns_open_empty
  = CheckOk (with_fds (fd_insert (m_fds ns_open_empty) 3
                         (FdDevNull true false)) ns_open_empty) []
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem urandom_bytes) (fun _ => None))
       (with_copyins [(8192, 13%nat)] (mkEffect 3 [] []))
       ns_open_empty
     = CheckOk (with_fds (fd_insert (m_fds ns_open_empty) 3 (FdUrandom true false))
                  ns_open_empty) [].
Proof. split; check_eq. Qed.

(* ---------------------------------------------------- what still declines *)

(** /proc and /sys at the root are outside the surface, whatever
    spelling led there, and the open declines. *)
Example openat_proc_is_outside :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
       (open_path_mem [47; 112; 114; 111; 99; 47; 120]%Z) (fun _ => None))
    (with_copyins [(8192, 8%nat)] (mkEffect (errno_ret ENOENT) [] []))
    ns_open_empty
  = CheckUnmodeled
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem [47; 115; 121; 115; 47; 120]%Z) (fun _ => None))
          (with_copyins [(8192, 7%nat)] (mkEffect (errno_ret ENOENT) [] []))
       ns_open_empty
     = CheckUnmodeled.
Proof. split; check_eq. Qed.

(* ------------------------------------------ the ns_perimeter shapes, pinned *)

(** [Common.FileSim.ns_perimeter] names the shapes an ARGV OPERAND can
    take beyond "a file that is there or a name that is not".  The
    predicate is a claim about what the arms do, so it is pinned here:
    each case below is the operand shape a conjunct names, spelled as a
    plain name resolved from the working directory, which is exactly
    how an argv entry reaches the walk.

    In [ns_perimeter]'s own order: the working directory off the root,
    the working directory outside the "/dev" subtree, the operand within
    [Fs.name_max], the operand not a device, the source not a
    directory. *)

Definition ns_open_dev_n : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input (demo_fs [([110], SDev DevNull)]) IEof).

Definition ns_open_at_root : Model := with_cwd Fs.root ns_open_empty.

(** A 256-byte operand, one byte over [Fs.name_max].  [Run.valid_argv]
    admits it -- it bounds an argv entry by PATH_MAX, not by NAME_MAX --
    and it has no separator, so it is a plain name the walk reaches and
    hands to the file system's [->lookup].  Beside it, the LONGEST
    operand within the limit, so the pin below brackets [Fs.name_max]
    rather than testing one side of it. *)
Definition long_operand : list Z := List.repeat 97%Z 256.
Definition max_operand : list Z := List.repeat 97%Z 255.

(** CONJUNCT ONE, the working directory off the root.  At the root a
    first component "proc" is [Fs.ROutside] and the call declines; one
    step down the same operand is an ordinary missing name.  The guard
    is a WALK-STATE test, which is why the perimeter carries the
    working directory and not just the operand. *)
Example ns_perimeter_root_cwd_is_the_reason :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
       (open_path_mem [112; 114; 111; 99]%Z) (fun _ => None))
    (with_copyins [(8192, 5%nat)] (mkEffect (errno_ret ENOENT) [] []))
    ns_open_at_root
  = CheckUnmodeled
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem [112; 114; 111; 99]%Z) (fun _ => None))
       (with_copyins [(8192, 5%nat)] (mkEffect (errno_ret ENOENT) [] []))
       ns_open_empty
     = CheckOk ns_open_empty [].
Proof. split; check_eq. Qed.

(** CONJUNCT TWO, the working directory outside the "/dev" SUBTREE.
    Standing there, an operand the image does not hold is an ordinary
    missing name, as it is one step away, and the create makes a file;
    but a DECLARED name there may be a device, which is the case the
    conjunct is for ([Common.FileSim.operand_is_not_a_device]).  A
    working directory of a DECLARED /dev/pts reads the same way. *)
Definition ns_open_at_dev : Model := with_cwd Fs.dev_dir ns_open_empty.
Definition ns_open_at_devpts : Model := with_cwd devpts_key ns_open_devpts.

Example ns_perimeter_dev_cwd_is_the_reason :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
       (open_path_mem [122; 101; 114; 111]%Z) (fun _ => None))
    (with_copyins [(8192, 5%nat)] (mkEffect (errno_ret ENOENT) [] []))
    ns_open_at_dev
  = CheckOk ns_open_at_dev []
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 wr_create_flags; 420; 0; 0]
          (open_path_mem [122; 101; 114; 111]%Z) (fun _ => None))
       (with_copyins [(8192, 5%nat)] (mkEffect 3 [] []))
       ns_open_at_dev
     = CheckOk (with_fds (fd_insert (m_fds ns_open_at_dev) 3
                            (FdFileW 1 (Z_to_bv 64 0)))
                  (with_fs (Fs.fs_create_file (m_fs ns_open_at_dev) devzero_key [])
                     ns_open_at_dev)) []
  (* off /dev the same operand is an ordinary missing name *)
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem [122; 101; 114; 111]%Z) (fun _ => None))
       (with_copyins [(8192, 5%nat)] (mkEffect (errno_ret ENOENT) [] []))
       ns_open_empty
     = CheckOk ns_open_empty []
  (* and a DECLARED name under /dev is the device, from there *)
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem [110; 117; 108; 108]%Z) (fun _ => None))
       (with_copyins [(8192, 5%nat)] (mkEffect 3 [] []))
       ns_open_at_dev
     = CheckOk (with_fds (fd_insert (m_fds ns_open_at_dev) 3
                            (FdDevNull true false)) ns_open_at_dev) []
  (* one level deeper, in a DECLARED /dev/pts, an absent operand is -ENOENT *)
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem [48]%Z) (fun _ => None))
       (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret ENOENT) [] []))
       ns_open_at_devpts
     = CheckOk ns_open_at_devpts [].
Proof. split_conj; check_eq. Qed.

(** CONJUNCT THREE, the operand within [Fs.name_max].  Past it, the
    file system's [->lookup] refuses the name with -ENAMETOOLONG
    ([simple_lookup], fs/libfs.c:71-72, which tmpfs uses at
    mm/shmem.c:5285 and ramfs at fs/ramfs/inode.c:193), and the walk
    also admits what a file system with a larger limit would answer
    without the check, which no supported kernel gives (a priority-2
    gap: [Fs.comp_too_long]).  So BOTH answers are admitted, on every
    flag word: the read's -ENOENT and the create's descriptor beside
    -ENAMETOOLONG.  That is the hole in a whole-program theorem: two
    answers where a named operand has one.

    THE LIMIT IS BRACKETED, not merely exceeded: the last cells are a
    255-byte operand, the longest [Fs.name_max] admits, and on it
    -ENAMETOOLONG is refused. *)
Example ns_perimeter_long_operand_admits_both_answers :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
       (open_path_mem long_operand) (fun _ => None))
    (with_copyins [(8192, 257%nat)] (mkEffect (errno_ret ENOENT) [] []))
    ns_open_empty
  = CheckOk ns_open_empty []
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem long_operand) (fun _ => None))
       (with_copyins [(8192, 257%nat)] (mkEffect (errno_ret ENAMETOOLONG) [] []))
       ns_open_empty
     = CheckOk ns_open_empty []
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 577; 0; 0; 0]
          (open_path_mem long_operand) (fun _ => None))
       (with_copyins [(8192, 257%nat)] (mkEffect 3 [] []))
       ns_open_empty
     = CheckOk (with_fds (fd_insert (m_fds ns_open_empty) 3
                            (FdFileW 1 (Z_to_bv 64 0)))
                  (with_fs (Fs.fs_create_file (m_fs ns_open_empty)
                              (wk (map (Z_to_bv 8) long_operand)) [])
                     ns_open_empty)) []
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 577; 0; 0; 0]
          (open_path_mem long_operand) (fun _ => None))
       (with_copyins [(8192, 257%nat)] (mkEffect (errno_ret ENAMETOOLONG) [] []))
       ns_open_empty
     = CheckOk ns_open_empty []
  (* one byte inside the limit is an ordinary missing name, and the
     length errno is refused there *)
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem max_operand) (fun _ => None))
       (with_copyins [(8192, 256%nat)] (mkEffect (errno_ret ENOENT) [] []))
       ns_open_empty
     = CheckOk ns_open_empty []
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem max_operand) (fun _ => None))
       (with_copyins [(8192, 256%nat)] (mkEffect (errno_ret ENAMETOOLONG) [] []))
       ns_open_empty
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** CONJUNCT FOUR, no device at the operand — and this conjunct
    constrains BOTH operands, so both halves are pinned.  A device
    entry at a plain name opens as a DEVICE descriptor under the read
    word and under the write-create word alike, so the copy that
    follows runs against the device's answer table and not against a
    file's bytes: a different outcome set, not a different errno.  The
    two descriptors differ in the mode they carry, which is what says
    the arm read the flag word and not just the entry.  A device lives
    under /dev on every valid image ([Run.devices_in_dev_subtree]), so
    the plain name is "null" from a working directory of /dev; the same
    entry at "/work/n", an image no valid input holds, opens as the
    device too. *)
Example ns_perimeter_device_at_an_operand_is_a_device :
  (* the SOURCE half: O_RDONLY *)
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
       (open_path_mem [110; 117; 108; 108]%Z) (fun _ => None))
    (with_copyins [(8192, 5%nat)] (mkEffect 3 [] []))
    ns_open_at_dev
  = CheckOk (with_fds (fd_insert (m_fds ns_open_at_dev) 3
                         (FdDevNull true false)) ns_open_at_dev) []
  (* the DESTINATION half: the write-create word mints the same kind
     with the other mode, and creates nothing — the image is untouched,
     where a file at this name would have been truncated *)
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 577; 0; 0; 0]
          (open_path_mem [110; 117; 108; 108]%Z) (fun _ => None))
       (with_copyins [(8192, 5%nat)] (mkEffect 3 [] []))
       ns_open_at_dev
     = CheckOk (with_fds (fd_insert (m_fds ns_open_at_dev) 3
                            (FdDevNull false true)) ns_open_at_dev) []
  (* DOCUMENTARY, not an independent check: [check_syscall] is a
     function, so this follows from the first conjunct.  It is kept
     because the contrast is the point — a reader comparing the two
     lines sees which descriptor the file lane would have expected. *)
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem [110; 117; 108; 108]%Z) (fun _ => None))
       (with_copyins [(8192, 5%nat)] (mkEffect 3 [] []))
       ns_open_at_dev
     <> CheckOk (with_fds (fd_insert (m_fds ns_open_at_dev) 3
                             (FdFile 1 (Z_to_bv 64 0))) ns_open_at_dev) []
  (* a device entry outside /dev, which no valid image holds, opens as
     the device too: the arm reads the entry's kind, not its key *)
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem [110%Z]) (fun _ => None))
       (with_copyins [(8192, 2%nat)] (mkEffect 3 [] []))
       ns_open_dev_n
     = CheckOk (with_fds (fd_insert (m_fds ns_open_dev_n) 3
                            (FdDevNull true false)) ns_open_dev_n) [].
Proof. split; [|split; [|split]]; [check_eq | check_eq | vm_compute; discriminate | check_eq]. Qed.

(** CONJUNCT FIVE, THE SOURCE not a directory — and the source ONLY,
    which is worth saying because the neighbouring conjunct constrains
    both operands and this one does not.  A directory at the operand
    opens read-only and yields a DIRECTORY descriptor, so the read that
    follows is the directory lane rather than the file lane the
    examples' loop is about.

    A DIRECTORY AT THE DESTINATION IS INSIDE THE PERIMETER, not
    excluded by it: [Common.FileSim.ns_dst_cases] splits the
    destination three ways for exactly that reason, and its header says
    so — the -EISDIR lane is one the examples already have.  The second
    cell below is therefore a pin on an ANSWER the perimeter admits,
    not on a shape it excludes, and it is here because it is the other
    thing a directory at an operand can be asked. *)
Example ns_perimeter_directory_at_the_source_is_a_dirfd :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
       (open_path_mem [97%Z]) (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect 3 [] []))
    ns_open_dir_a
  = CheckOk (with_fds (fd_insert (m_fds ns_open_dir_a) 3
                         (FdDir (wk [97]))) ns_open_dir_a) []
  (* the write-create word on the same operand is -EISDIR: a
     DESTINATION the perimeter admits, answered rather than excluded *)
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 577; 0; 0; 0]
          (open_path_mem [97%Z]) (fun _ => None))
       (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EISDIR) [] []))
       ns_open_dir_a
     = CheckOk ns_open_dir_a [].
Proof. split; check_eq. Qed.

(** THE RANDOM DEVICE AT AN OPERAND, ON THE WRITE-CREATE WORD.
    [Fs.EDev Fs.DevUrandom] answers the read word and the write-create
    word alike, each with the descriptor of its access mode: [devlist]
    gives the device mode 0666 (drivers/char/mem.c:701, Linux v6.18.46)
    and [urandom_fops] has a [write_iter]
    (drivers/char/random.c:1572-1574), so the open succeeds and creates
    nothing.  An -EISDIR for it is refused.

    The model is [ns_open_at_dev] above: from a working directory of
    /dev the operand "urandom" names the device, which is the shape
    [Common.FileSim.operand_is_not_a_device] excludes by its
    working-directory hypotheses. *)
Example create_on_the_random_device_gives_a_descriptor :
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; 577; 0; 0; 0]
       (open_path_mem [117;114;97;110;100;111;109]%Z) (fun _ => None))
    (with_copyins [(8192, 8%nat)] (mkEffect 3 [] []))
    ns_open_at_dev
  = CheckOk (with_fds (fd_insert (m_fds ns_open_at_dev) 3 (FdUrandom false true))
               ns_open_at_dev) []
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 577; 0; 0; 0]
          (open_path_mem [117;114;97;110;100;111;109]%Z) (fun _ => None))
       (with_copyins [(8192, 8%nat)] (mkEffect (errno_ret EISDIR) [] []))
       ns_open_at_dev
     = CheckReject
  (* the READ word on the same operand mints the read-only kind *)
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem [117;114;97;110;100;111;109]%Z) (fun _ => None))
       (with_copyins [(8192, 8%nat)] (mkEffect 3 [] []))
       ns_open_at_dev
     = CheckOk (with_fds (fd_insert (m_fds ns_open_at_dev) 3 (FdUrandom true false))
                  ns_open_at_dev) []
  (* and /dev/null answers BOTH words from the same working directory *)
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 577; 0; 0; 0]
          (open_path_mem [110;117;108;108]%Z) (fun _ => None))
       (with_copyins [(8192, 5%nat)] (mkEffect 3 [] []))
       ns_open_at_dev
     = CheckOk (with_fds (fd_insert (m_fds ns_open_at_dev) 3
                            (FdDevNull false true)) ns_open_at_dev) [].
Proof. split_conj; check_eq. Qed.

(* --------------------------------------------------------------- ftruncate *)

(** A FILE UNLINKED WHILE OPEN IS STILL TRUNCATED.  [do_ftruncate]
    reads the inode off the descriptor's own dentry,
    [inode = dentry->d_inode] (fs/open.c:173-174, Linux v6.18.46), and an
    open file keeps its inode until the last [iput] ([iput_final],
    fs/inode.c:1874-1915), so the name being gone changes nothing.  In
    the model the descriptor holds the inode number and the inode keeps
    its row while a descriptor holds it ([Fs.fs_unlink_file]); the new
    size is that row's, and no name comes back. *)
Definition ftruncate_unlinked_model : Model :=
  with_fds [(3, FdFileW 1 (Z_to_bv 64 0))]
    (with_fs (Fs.fs_unlink_file (m_fs ns_open_f) (wk [102]) 1 true) ns_open_f).

Example ftruncate_of_a_file_unlinked_while_open_is_answered :
  match check_syscall (mkInput 46 [3; 1; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
          (mkEffect 0 [] []) ftruncate_unlinked_model with
  | CheckOk m [] =>
      Fs.fs_ino_data (m_fs m) 1 = [104] /\ Fs.fs_lookup (m_fs m) (wk [102]) = None
  | _ => False
  end.
Proof. vm_compute. split; reflexivity. Qed.


(** "f" = "abcd", inode 1, open O_RDWR at fd 3, and "f" = "abcdef" open in
    APPEND MODE at fd 3, both at offset 0. *)
Definition ftruncate_rdwr_model : Model :=
  mkModel [(3, FdFileRW 1 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    (raw_files [([102], [97; 98; 99; 100])]) None None None.

Definition ftruncate_append_model : Model :=
  mkModel [(3, FdFileA 1 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    (raw_files [([102], [97; 98; 99; 100; 101; 102])]) None None None.

(** THE READ-WRITE AND APPEND KINDS TAKE THE WRITABLE ARM.
    [do_ftruncate] (fs/open.c:175-176, Linux v6.18.46) refuses only
    [!S_ISREG(inode->i_mode) || !(file->f_mode & FMODE_WRITE)], and both
    kinds carry FMODE_WRITE -- O_RDWR sets it as O_WRONLY does, and
    O_APPEND rides on O_WRONLY -- so [ftruncate(fd, 2)] answers 0 and
    shrinks inode 1 to "ab", the descriptor's offset left at 0: nothing
    on this path reads the append bit or writes [f_pos].  The -EINVAL
    the read-only kind gets is refused. *)
Example ftruncate_rdwr_fd_shrinks_the_file :
  check_syscall (mkInput 46 [3; 2; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) ftruncate_rdwr_model
  = CheckOk (with_fs (Fs.fs_set_ino_data (m_fs ftruncate_rdwr_model) 1 [97; 98])
               ftruncate_rdwr_model) []
  /\ check_syscall (mkInput 46 [3; 2; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) ftruncate_rdwr_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** ...and the append kind the same way, on "abcdef".  Its arm keeps the
    writable arm's decline as well: a grow past the file's length plus
    [Uaccess.rw_bytes_max] is a zero-fill the model does not build, where
    Linux makes the file sparse ([Open.modeled_truncate_gap]).  The
    descriptor holds the inode itself, so no dangling path is left to
    decline. *)
Example ftruncate_append_fd_shrinks_the_file :
  check_syscall (mkInput 46 [3; 2; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) ftruncate_append_model
  = CheckOk (with_fs (Fs.fs_set_ino_data (m_fs ftruncate_append_model) 1 [97; 98])
               ftruncate_append_model) []
  /\ check_syscall (mkInput 46 [3; 2; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) ftruncate_append_model
     = CheckReject
  /\ check_syscall (mkInput 46 [3; Z_to_bv 64 (6 + rw_bytes_max + 1); 0; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) ftruncate_append_model
     = CheckUnmodeled.
Proof. split_conj; check_eq. Qed.

(* --------------------------------------------------------------- faccessat *)

(** EXISTENCE IS RESOLUTION: a directory answers 0, and an -ENOENT for
    it is refused. *)
Example faccessat_directory_exists :
  check_syscall
    (mkInput 48 [AT_FDCWD; 8192; 0; 0; 0; 0]
       (open_path_mem [97%Z]) (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect 0 [] []))
    ns_open_dir_a
  = CheckOk ns_open_dir_a []
  /\ check_syscall
       (mkInput 48 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem [97%Z]) (fun _ => None))
       (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret ENOENT) [] []))
       ns_open_dir_a
     = CheckReject.
Proof. split; check_eq. Qed.

(** A TRAILING SEPARATOR SPLITS THE TWO ENTRY KINDS.  [lookup_last]
    adds LOOKUP_DIRECTORY for a LAST_NORM component a separator follows,
    and [path_lookupat] ends with [d_can_lookup], so "f/" on a regular
    file is -ENOTDIR and "a/" on a directory is 0.  Both halves are
    pinned: the second is what says a trailing separator is not always
    an error. *)
Example faccessat_trailing_separator_needs_a_directory :
  check_syscall
    (mkInput 48 [AT_FDCWD; 8192; 0; 0; 0; 0]
       (open_path_mem [102%Z; 47%Z]) (fun _ => None))
    (with_copyins [(8192, 3%nat)] (mkEffect (errno_ret ENOTDIR) [] []))
    ns_open_f
  = CheckOk ns_open_f []
  /\ check_syscall
       (mkInput 48 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem [102%Z; 47%Z]) (fun _ => None))
       (with_copyins [(8192, 3%nat)] (mkEffect 0 [] []))
       ns_open_f
     = CheckReject
  /\ check_syscall
       (mkInput 48 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem [97%Z; 47%Z]) (fun _ => None))
       (with_copyins [(8192, 3%nat)] (mkEffect 0 [] []))
       ns_open_dir_a
     = CheckOk ns_open_dir_a [].
Proof. split; [|split]; check_eq. Qed.

(** EXISTENCE IN THE /dev SUBTREE IS READ OFF THE IMAGE like anywhere
    else: [faccessat(F_OK)] of /dev/zero, a name the image does not
    hold, is -ENOENT, and a 0 for it is refused.  The same name under
    /tmp is the twin, and the declared device declines
    ([faccessat_of_a_device_declines]). *)
Example faccessat_under_dev_absent_is_enoent :
  check_syscall
    (mkInput 48 [AT_FDCWD; 8192; 0; 0; 0; 0]
       (open_path_mem devzero_bytes) (fun _ => None))
    (with_copyins [(8192, 10%nat)] (mkEffect (errno_ret ENOENT) [] []))
    ns_open_empty
  = CheckOk ns_open_empty []
  /\ check_syscall
       (mkInput 48 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem devzero_bytes) (fun _ => None))
       (with_copyins [(8192, 10%nat)] (mkEffect 0 [] []))
       ns_open_empty
     = CheckReject
  /\ check_syscall
       (mkInput 48 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem tmpzero_bytes) (fun _ => None))
       (with_copyins [(8192, 10%nat)] (mkEffect (errno_ret ENOENT) [] []))
       ns_open_empty
     = CheckOk ns_open_empty []
  (* and the declared device declines, whatever the answer *)
  /\ check_syscall
       (mkInput 48 [AT_FDCWD; 8192; 0; 0; 0; 0]
          (open_path_mem devnull_bytes) (fun _ => None))
       (with_copyins [(8192, 10%nat)] (mkEffect 0 [] []))
       ns_open_empty
     = CheckUnmodeled.
Proof. split_conj; check_eq. Qed.

(** A DEVICE DECLINES, WHATEVER THE ANSWER.  [do_faccessat]'s
    [inode_permission] reaches [devcgroup_inode_permission] for a
    character node (fs/namei.c:597-599, Linux v6.18.46), where a cgroup
    BPF device program answers whatever value it set through
    [bpf_set_retval] (kernel/bpf/cgroup.c:84-115, :1839-1846).  SCOPE.md's
    premise on device cgroups covers the opens of the two nodes, not
    F_OK's empty access set, which such a program can refuse alone:
    [Fs.Open.faccessat_errnos]'s device-cgroup paragraph.  So F_OK of
    /dev/null or /dev/urandom is [CheckUnmodeled] beside 0 and beside
    -EPERM alike, through [faccessat] and through [faccessat2] with
    either accepted flag.  A regular file still answers 0 and still
    refuses -EPERM: [devcgroup_inode_permission] returns 0 for a
    non-device inode (include/linux/device_cgroup.h:21-22), and F_OK
    reaches no other -EPERM ([Fs.Open.faccessat_errnos]). *)
Example faccessat_of_a_device_declines :
  let fa (p : list Z) (n : nat) (e : word) (m : Model) := check_syscall
        (mkInput 48 [AT_FDCWD; 8192; 0; 0; 0; 0] (open_path_mem p) (fun _ => None))
        (with_copyins [(8192, n)] (mkEffect e [] [])) m in
  let fa2 (p : list Z) (n : nat) (fl : Z) (e : word) (m : Model) := check_syscall
        (mkInput 439 [AT_FDCWD; 8192; 0; Z_to_bv 64 fl; 0; 0] (open_path_mem p)
           (fun _ => None))
        (with_copyins [(8192, n)] (mkEffect e [] [])) m in
  fa devnull_bytes 10%nat 0 ns_open_empty = CheckUnmodeled
  /\ fa devnull_bytes 10%nat (errno_ret EPERM) ns_open_empty = CheckUnmodeled
  /\ fa urandom_bytes 13%nat 0 ns_open_empty = CheckUnmodeled
  /\ fa urandom_bytes 13%nat (errno_ret EPERM) ns_open_empty = CheckUnmodeled
  /\ fa2 devnull_bytes 10%nat 0%Z 0 ns_open_empty = CheckUnmodeled
  /\ fa2 devnull_bytes 10%nat AT_EACCESS (errno_ret EPERM) ns_open_empty
     = CheckUnmodeled
  /\ fa2 urandom_bytes 13%nat AT_SYMLINK_NOFOLLOW (errno_ret EPERM) ns_open_empty
     = CheckUnmodeled
  (* a regular file: 0 still, and -EPERM still refused *)
  /\ fa [102%Z] 2%nat 0 ns_open_f = CheckOk ns_open_f []
  /\ fa [102%Z] 2%nat (errno_ret EPERM) ns_open_f = CheckReject
  /\ fa2 [102%Z] 2%nat 0%Z (errno_ret EPERM) ns_open_f = CheckReject.
Proof. vm_compute; split_conj; check_eq. Qed.

(** F_OK OF "/" ADMITS NO -EACCES.  A pathname of separators alone
    returns from [link_path_walk] before its loop (fs/namei.c:2451-2458,
    Linux v6.18.46), so [may_lookup] (:2466-2468) never runs, and the
    final [inode_permission(..., MAY_ACCESS)] of [do_faccessat]
    (fs/open.c:509) cannot refuse a zero mask on tmpfs or ramfs.  So "/"
    and "//" answer 0 and refuse -EACCES, through [faccessat] and
    through [faccessat2] under flags 0, AT_EACCESS and
    AT_SYMLINK_NOFOLLOW; the walk's -ENOMEM is still admitted, the
    over-admission [Fs.Namei.walk_errnos] records for a walk that
    allocates nothing.  A pathname with a component still admits
    -EACCES: "/." searches "/", and "a" the working directory. *)
Example faccessat_of_the_root_admits_no_eacces :
  let fa (p : list Z) (n : nat) (e : word) (m : Model) := check_syscall
        (mkInput 48 [AT_FDCWD; 8192; 0; 0; 0; 0] (open_path_mem p) (fun _ => None))
        (with_copyins [(8192, n)] (mkEffect e [] [])) m in
  let fa2 (p : list Z) (n : nat) (fl : Z) (e : word) (m : Model) := check_syscall
        (mkInput 439 [AT_FDCWD; 8192; 0; Z_to_bv 64 fl; 0; 0] (open_path_mem p)
           (fun _ => None))
        (with_copyins [(8192, n)] (mkEffect e [] [])) m in
  fa [47%Z] 2%nat 0 ns_open_empty = CheckOk ns_open_empty []
  /\ fa [47%Z] 2%nat (errno_ret EACCES) ns_open_empty = CheckReject
  /\ fa [47%Z; 47%Z] 3%nat (errno_ret EACCES) ns_open_empty = CheckReject
  /\ fa2 [47%Z] 2%nat 0%Z (errno_ret EACCES) ns_open_empty = CheckReject
  /\ fa2 [47%Z] 2%nat AT_EACCESS (errno_ret EACCES) ns_open_empty = CheckReject
  /\ fa2 [47%Z] 2%nat AT_SYMLINK_NOFOLLOW (errno_ret EACCES) ns_open_empty
     = CheckReject
  /\ fa [47%Z] 2%nat (errno_ret ENOMEM) ns_open_empty = CheckOk ns_open_empty []
  (* a component: may_lookup runs, and -EACCES stands beside the 0 *)
  /\ fa [47%Z; 46%Z] 3%nat (errno_ret EACCES) ns_open_empty = CheckOk ns_open_empty []
  /\ fa [97%Z] 2%nat (errno_ret EACCES) ns_open_dir_a = CheckOk ns_open_dir_a []
  /\ fa2 [97%Z] 2%nat AT_EACCESS (errno_ret EACCES) ns_open_dir_a
     = CheckOk ns_open_dir_a [].
Proof. vm_compute; split_conj; check_eq. Qed.

(** A bad MODE beats an unreadable path: [do_faccessat]'s first
    statement runs before [getname]. *)
Example faccessat_bad_mode_beats_an_unreadable_path :
  check_syscall
    (mkInput 48 [AT_FDCWD; 0; 8; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] [])
    ns_open_empty
  = CheckOk ns_open_empty [].
Proof. check_eq. Qed.

(** ...and that arm records NO copy-in, because the kernel decides it
    before [user_path_at]. *)
Example faccessat_bad_mode_records_no_copyin :
  check_syscall
    (mkInput 48 [AT_FDCWD; 8192; 8; 0; 0; 0]
       (open_path_mem [97%Z]) (fun _ => None))
    (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EINVAL) [] []))
    ns_open_dir_a
  = CheckReject.
Proof. check_eq. Qed.

(** Past the mode test the ledger is REQUIRED. *)
Example faccessat_existence_needs_the_copyin :
  check_syscall
    (mkInput 48 [AT_FDCWD; 8192; 0; 0; 0; 0]
       (open_path_mem [97%Z]) (fun _ => None))
    (mkEffect 0 [] [])
    ns_open_dir_a
  = CheckReject.
Proof. check_eq. Qed.

(* -------------------------------------------------------------- faccessat2 *)

(** The two accepted flags change no answer, and AT_EMPTY_PATH is
    declined because the kernel ACCEPTS it and the model does not
    interpret it. *)
Example faccessat2_accepted_flags_change_no_answer :
  let fa2 fl := check_syscall
        (mkInput 439 [AT_FDCWD; 8192; 0; Z_to_bv 64 fl; 0; 0]
           (open_path_mem [97%Z]) (fun _ => None))
        (with_copyins [(8192, 2%nat)] (mkEffect 0 [] [])) ns_open_dir_a in
  fa2 0%Z = CheckOk ns_open_dir_a []
  /\ fa2 AT_EACCESS = CheckOk ns_open_dir_a []
  /\ fa2 AT_SYMLINK_NOFOLLOW = CheckOk ns_open_dir_a []
  /\ fa2 (AT_EACCESS + AT_SYMLINK_NOFOLLOW)%Z = CheckOk ns_open_dir_a []
  /\ fa2 AT_EMPTY_PATH = CheckUnmodeled
  (* a bit outside the mask is the kernel's own -EINVAL *)
  /\ check_syscall
       (mkInput 439 [AT_FDCWD; 8192; 0; 4; 0; 0]
          (open_path_mem [97%Z]) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) ns_open_dir_a
     = CheckOk ns_open_dir_a [].
Proof. repeat split; check_eq. Qed.

(* =========================================================================
   THE FLAG WORDS, THE DEVICES, AND THE PATHNAME FAULTS, on the image
   ========================================================================= *)

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
                | CheckOk m _ => file_at (m_fs m) (wk [102])
                | _ => None
                end in
  let have := demo_fs [([102], SFile [104; 105])] in
  let absent := demo_fs [] in
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
  let have := demo_fs [([102], SFile [104; 105])] in
  let absent := demo_fs [] in
  let base fs := init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof) in
  let fd3 := mkEffect 3 [] [] in
  let kept r := match r with
                | CheckOk m _ => file_at (m_fs m) (wk [102])
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
     = Some (FdFileA 1 0)
  (* ...where the exclusive shape mints the plain write-only kind *)
  /\ kind (open absent mem_open_write excl_create_flags fd3)
     = Some (FdFileW 1 0)
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
                | CheckOk m _ => file_at (m_fs m) (wk [102])
                | _ => None
                end in
  let have := demo_fs [([102], SFile [104; 105])] in
  let absent := demo_fs [] in
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
     | CheckOk m _ => fd_lookup (m_fds m) 3 = Some (FdFileRW 1 0)
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
  let have := demo_fs [([102], SFile [104; 105])] in
  let absent := demo_fs [] in
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

(* ======================================== close (57), ftruncate (46) on
   a stream-pair end *)

(** One AF_UNIX stream pair, id 0: side [false] at fd 3 holds two bytes
    its peer wrote and nobody has read, side [true] at fd 4 holds
    nothing.  Both ends block and neither is shut down; the buffer sizes
    are [State.default_kernel]'s, and nothing below reads them. *)
Definition close_pair_end (rx : list byte) : StreamEnd :=
  mkStreamEnd rx false 212992%Z 212992%Z false false RsUnknown.

Definition close_pair_model : Model :=
  mkModel [(0, FdChannel 0); (1, FdChannel 1);
           (3, FdStream 0 false (close_pair_end [104; 105]));
           (4, FdStream 0 true (close_pair_end []))]
    (mkVmMaps [] [] 0 0 demo_limit) IEof Fs.fs_empty None None None.

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

(* ================================ "/etc/localtime", answered by the walk

   [Run.localtime_absent] is the validity clause that says the image
   holds no /etc/localtime (/etc absent, or a folder without it), so
   every open of that path reaches the walk's -ENOENT.  These pin it on
   the standard root, which has no /etc. *)

(** The bytes of "/etc/localtime". *)
Definition localtime_bytes : list Z :=
  [47; 101; 116; 99; 47; 108; 111; 99; 97; 108; 116; 105; 109; 101]%Z.

(** THE -ENOENT IS AN ANSWER, NOT A DECLINE, and the model insists on
    it: every word the model interprets is a [CheckOk] in the unchanged
    model when the kernel reports -ENOENT, and a kernel that reports a
    descriptor instead is REJECTED.  The O_CLOEXEC|O_NONBLOCK row is the
    word musl's [__map_file] issues for this path (musl 1.2.6,
    src/time/__map_file.c); both bits are in
    [Fs.Open.open_ignored_flags], so it is the O_RDONLY arm.  The words
    with O_CREAT get the same -ENOENT: the walk stops at the absent
    folder /etc before the last component, which is [filename_create]'s
    and [open_last_lookups]' -ENOENT for a missing parent. *)
Example openat_localtime_enoent :
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof) in
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
  (* a claimed success is refused *)
  /\ open 0%Z (mkEffect 3 [] []) = CheckReject
  (* with O_CREAT: the same -ENOENT, and a create is refused *)
  /\ open wr_create_flags enoent = CheckOk m0 []
  /\ open excl_create_flags enoent = CheckOk m0 []
  /\ open append_create_flags enoent = CheckOk m0 []
  /\ open (O_RDWR + O_CREAT)%Z enoent = CheckOk m0 []
  /\ open rdwr_excl_create_flags enoent = CheckOk m0 []
  /\ open wr_create_flags (mkEffect 3 [] []) = CheckReject.
Proof. vm_compute. split_conj; check_eq. Qed.

(** EVERY WORD WITHOUT O_CREAT, ON BOTH VALID SHAPES OF THE CLAUSE: no
    /etc (the standard root), and a folder /etc that does not hold
    localtime.  A word [Fs.Open.modeled_open_flags] admits without
    O_CREAT has one of four residues once [Fs.Open.open_ignored_flags]
    is taken off -- O_RDONLY, O_RDONLY|O_DIRECTORY, O_RDWR and
    O_RDWR|O_TRUNC -- and any of the three ignored bits beside it, so
    the lemma is over all 32 words and both images; each image is valid
    ([localtime_images_valid]). *)
Definition etc_dir_key : Fs.path := map (Z_to_bv 8) [47; 101; 116; 99]%Z.

Definition etc_dir_image : Fs.Fs := Fs.fs_set (demo_fs []) etc_dir_key Fs.EDir.

Example localtime_images_valid :
  valid_image (demo_input (demo_fs []) IEof)
  /\ valid_image (demo_input etc_dir_image IEof).
Proof.
  split; unfold valid_image; cbn [in_fs in_cwd]; repeat split; valid_image_vm.
Qed.

Lemma openat_localtime_enoent_every_word : forall fs r (c l n : bool),
  In fs [demo_fs []; etc_dir_image] ->
  In r [0; O_DIRECTORY; O_RDWR; O_RDWR + O_TRUNC]%Z ->
  let fl := (r + (if c then O_CLOEXEC else 0) + (if l then O_LARGEFILE else 0)
             + (if n then O_NONBLOCK else 0))%Z in
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof) in
  let open eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           (open_path_mem localtime_bytes) (fun _ => None))
        (with_copyins [(8192, 15%nat)] eff) m0 in
  open (mkEffect (errno_ret ENOENT) [] []) = CheckOk m0 []
  /\ open (mkEffect 3 [] []) = CheckReject.
Proof.
  intros fs r c l n Hfs Hr.
  destruct Hfs as [<-|[<-|[]]]; destruct Hr as [<-|[<-|[<-|[<-|[]]]]];
    destruct c, l, n; cbv zeta; split; check_eq.
Qed.

(* ================================ "/dev/null", the device by kind

   The walk reaches the [EDev DevNull] entry and the open mints
   [State.FdDevNull], the kind whose every answer comes from [null_fops]
   (drivers/char/mem.c) rather than from the file system.  These pin
   the open under each admitted word, the open, write, read, close
   sequence, and the answers the kind forces at every fd-kind dispatch
   site outside fs/open.c. *)

Definition devnull_m0 : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof).

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
                          /\ m_fs m = m_fs devnull_m0
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
Proof. vm_compute. split_conj; check_eq. Qed.

(** A SECOND NULL-DEVICE NODE ANSWERS AS THE DEVICE.  A null-device
    entry at a key other than "/dev/null" opens the null device: Linux
    opens a character device through its inode's device number, whatever
    the name ([chrdev_open], fs/char_dev.c:373-424, Linux v6.18.46), and
    the descriptor carries no key.  Beside it, the spellings the walk
    reads: a doubled separator reaches the device, a truncated name is an
    absent one, and a FILE at the device's key opens as a file. *)
Definition devnull2_key : Fs.path :=
  Fs.child_key Fs.dev_dir (map (fun z => Z_to_bv 8 z) [110; 117; 108; 108; 50]%Z).

Example devnull_open_at_any_node :
  let open fs bs n eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; 0; 420; 0; 0]
           (open_path_mem bs) (fun _ => None))
        (with_copyins [(8192, n)] eff)
        (init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof)) in
  let base fs := init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof) in
  let other := Fs.fs_set (demo_fs []) devnull2_key (EDev DevNull) in
  (* the null-device kind at another key: the device, at the lowest free fd *)
  (match open other ([47; 100; 101; 118; 47; 110; 117; 108; 108; 50]%Z) 11%nat
              (mkEffect 3 [] []) with
   | CheckOk m [] => fd_lookup (m_fds m) 3 = Some (FdDevNull true false)
   | _ => False end)
  /\ open other ([47; 100; 101; 118; 47; 110; 117; 108; 108; 50]%Z) 11%nat
       (mkEffect 4 [] []) = CheckReject
  (* "/dev//null" is the device *)
  /\ (match open (demo_fs []) ([47; 100; 101; 118; 47; 47; 110; 117; 108; 108]%Z)
              11%nat (mkEffect 3 [] []) with
      | CheckOk m [] => fd_lookup (m_fds m) 3 = Some (FdDevNull true false)
      | _ => False end)
  (* "/dev/nul" is an absent name *)
  /\ open (demo_fs []) ([47; 100; 101; 118; 47; 110; 117; 108]%Z) 9%nat
       (mkEffect (errno_ret ENOENT) [] []) = CheckOk (base (demo_fs [])) []
  (* a FILE at the device's key opens as a file *)
  /\ (match open (Fs.fs_create_file (demo_fs []) devnull_path [104])
              devnull_bytes 10%nat (mkEffect 3 [] []) with
      | CheckOk m [] => fd_lookup (m_fds m) 3 = Some (FdFile 1 0)
      | _ => False end).
Proof. vm_compute. split_conj; check_eq. Qed.

(** A table with one descriptor of each access mode, for the dispatch
    sites below: 3 read-only, 4 write-only, 5 read-write, over the
    standard root, whose /dev/null is the image's one null-device node
    the descriptors came from ([Fs.Stat.fstat_devfd_spec]). *)
Definition devnull_model : Model :=
  mkModel [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
           (3, FdDevNull true false); (4, FdDevNull false true);
           (5, FdDevNull true true)]
    (mkVmMaps [] [] 0 0 demo_limit) IEof (Fs.standard_root Fs.default_cwd) None None None.

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
    given, the page size as [st_blksize] (asserted too), zero everywhere
    else. *)
Definition dev_stat (mode rdev size : Z) : list byte :=
  Z_to_le_bytes 16 0 ++ Z_to_le_bytes 4 mode ++ Z_to_le_bytes 12 0
  ++ Z_to_le_bytes 8 rdev ++ Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 size
  ++ Z_to_le_bytes 4 4096 ++ Z_to_le_bytes 68 0.

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
       statpin_lookup (m_statpins m) (IdDev devnull_path) = Some (mkStatPin good None false)
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

   The walk reaches the [EDev DevUrandom] entry and the open mints
   [State.FdUrandom] with the access mode of the word, whose reads hand
   out the run's DECLARED stream ([State.in_urandom]: arbitrary but
   fixed, a parameter of the execution like argv and envp).  These pin
   the open under each word, the open, read, close sequence with a
   stream long enough, the decline when the stream runs out, the
   answers at every dispatch site, the fstat delivery, and — the point
   of the declared stream — that two models seeded from one stream read
   the same bytes. *)

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
    (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)).

(** THE OPEN, under every word: O_RDONLY (with or without O_CLOEXEC)
    mints the read-only kind and leaves the image and the stream alone;
    the O_EXCL words are -EEXIST and the O_DIRECTORY word -ENOTDIR (a
    claimed success is rejected on both); the WRITE words — clobbering,
    appending, read-write — mint the kind with the word's access mode
    ([urandom_flag_table] above has the same rows on another fixture). *)
Example urandom_open_by_word :
  let open fl eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           (open_path_mem urandom_bytes) (fun _ => None))
        (with_copyins [(8192, 13%nat)] eff) urandom_m0 in
  let minted fl rd wr :=
        match open fl (mkEffect 3 [] []) with
        | CheckOk m [] => fd_lookup (m_fds m) 3 = Some (FdUrandom rd wr)
                          /\ m_fs m = m_fs urandom_m0
                          /\ m_urandom m = urandom_stream urandom_decl
        | _ => False
        end in
  minted 0%Z true false
  /\ minted (0 + O_CLOEXEC)%Z true false
  /\ open excl_create_flags (mkEffect (errno_ret EEXIST) [] []) = CheckOk urandom_m0 []
  /\ open rdwr_excl_create_flags (mkEffect (errno_ret EEXIST) [] []) = CheckOk urandom_m0 []
  /\ open excl_append_create_flags (mkEffect (errno_ret EEXIST) [] []) = CheckOk urandom_m0 []
  /\ open (excl_append_create_flags + O_TRUNC)%Z (mkEffect (errno_ret EEXIST) [] [])
     = CheckOk urandom_m0 []
  /\ open O_DIRECTORY (mkEffect (errno_ret ENOTDIR) [] []) = CheckOk urandom_m0 []
  /\ open excl_create_flags (mkEffect 3 [] []) = CheckReject
  /\ open excl_append_create_flags (mkEffect 3 [] []) = CheckReject
  /\ open O_DIRECTORY (mkEffect 3 [] []) = CheckReject
  /\ minted wr_create_flags false true
  /\ minted append_create_flags false true
  /\ minted O_RDWR true true
  /\ minted (O_RDWR + O_CREAT + O_TRUNC)%Z true true.
Proof. vm_compute. split_conj; check_eq. Qed.

(** A SECOND RANDOM-DEVICE NODE ANSWERS AS THE DEVICE, as the null
    device's does; "/dev//urandom" is the device; "/dev/random", which
    this image does not hold, is an absent name. *)
Definition urandom2_key : Fs.path :=
  Fs.child_key Fs.dev_dir
    (map (fun z => Z_to_bv 8 z) [117; 114; 97; 110; 100; 111; 109; 50]%Z).

Example urandom_open_at_any_node :
  let open fs bs n eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; 0; 420; 0; 0]
           (open_path_mem bs) (fun _ => None))
        (with_copyins [(8192, n)] eff)
        (init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof)) in
  let base fs := init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof) in
  let other := Fs.fs_set (demo_fs []) urandom2_key (EDev DevUrandom) in
  (match open other ([47; 100; 101; 118; 47; 117; 114; 97; 110; 100; 111; 109; 50]%Z)
              14%nat (mkEffect 3 [] []) with
   | CheckOk m [] => fd_lookup (m_fds m) 3 = Some (FdUrandom true false)
   | _ => False end)
  /\ open other ([47; 100; 101; 118; 47; 117; 114; 97; 110; 100; 111; 109; 50]%Z)
       14%nat (mkEffect 4 [] []) = CheckReject
  /\ (match open (demo_fs [])
              ([47; 100; 101; 118; 47; 47; 117; 114; 97; 110; 100; 111; 109]%Z)
              14%nat (mkEffect 3 [] []) with
      | CheckOk m [] => fd_lookup (m_fds m) 3 = Some (FdUrandom true false)
      | _ => False end)
  /\ open (demo_fs []) ([47; 100; 101; 118; 47; 114; 97; 110; 100; 111; 109]%Z)
       12%nat (mkEffect (errno_ret ENOENT) [] []) = CheckOk (base (demo_fs [])) [].
Proof. vm_compute. split_conj; check_eq. Qed.

(** THE LAUNCH THAT USED TO DECLINE: working folder /dev, the standard
    root plus /dev/x as a second node of one device kind, and a relative
    open of "x".  [Run.valid_input] admits it (devices stay under /dev,
    and an argv operand may be a relative name), so the open must
    answer: it mints the device's descriptor at the lowest free fd, as
    at the device's own name ([Fs.Open.open_devnull],
    [Fs.Open.open_urandom]; [chrdev_open], fs/char_dev.c:373-424, Linux
    v6.18.46, opens by the inode's device number). *)
Definition devx_key : Fs.path := Fs.child_key Fs.dev_dir [Z_to_bv 8 120].

Definition dev_cwd_model (fs0 : Fs.Fs) : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (mkProcInput_full [] [] fs0 Fs.dev_dir IEof demo_uid demo_gid demo_groups
                      net_silent default_nofile (Z_to_bv 64 0) demo_hwcap false
                      Sv48 default_urandom default_kernel default_execfn
                      true true false).

Example second_device_node_opens_from_dev :
  let open fs eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; 0; 420; 0; 0] (open_path_mem [120]%Z) (fun _ => None))
        (with_copyins [(8192, 2%nat)] eff) (dev_cwd_model fs) in
  let null2 := Fs.fs_set (Fs.standard_root Fs.default_cwd) devx_key (EDev DevNull) in
  let urandom2 := Fs.fs_set (Fs.standard_root Fs.default_cwd) devx_key (EDev DevUrandom) in
  (match open null2 (mkEffect 3 [] []) with
   | CheckOk m [] => fd_lookup (m_fds m) 3 = Some (FdDevNull true false)
   | _ => False end)
  /\ (match open urandom2 (mkEffect 3 [] []) with
      | CheckOk m [] => fd_lookup (m_fds m) 3 = Some (FdUrandom true false)
      | _ => False end).
Proof. vm_compute. split_conj; check_eq. Qed.


(* ========================= a key that is also a directory another key lives in

   An image with the files "a" and "a/b" says that "a" is a regular
   file AND the directory "b" lives in.  No file system holds both: one
   name in one directory is one inode.  [Fs.wf_fs] refuses it, because
   a key's parent must be a directory in the image.

   THE CONTROL IS THE POINT: the refused image and the admitted one
   differ by the one separator that makes "a" a directory ("a" and "ab"
   nest nowhere). *)
Definition prefix_key_image : Fs.Fs :=
  demo_fs [([97], SFile [104]); ([97; 47; 98], SFile [104])].

Definition flat_key_image : Fs.Fs :=
  demo_fs [([97], SFile [104]); ([97; 98], SFile [104])].

Example fs_prefix_key_image_is_not_real :
  Fs.wf_fsb prefix_key_image = false
  /\ Fs.wf_fsb flat_key_image = true.
Proof. split; vm_compute; reflexivity. Qed.

(** …so no run has it: the fixture over the image is refused by
    [Run.valid_image], while the fixture over the flat image is
    admitted. *)
Example fs_prefix_key_input_is_not_valid :
  ~ valid_image (demo_input prefix_key_image IEof).
Proof.
  intros (Hwf & _). apply Fs.wf_fsb_iff in Hwf. vm_compute in Hwf. discriminate.
Qed.

Example fs_flat_key_input_is_valid :
  valid_image (demo_input flat_key_image IEof).
Proof. unfold valid_image; cbn [in_fs in_cwd]; repeat split; valid_image_vm. Qed.

(** A non-canonical key is refused by the same clause: "./a", "a/",
    "a//b" and the empty key each spell no canonical key, and a
    directory entry named "." cannot exist. *)
Example fs_noncanonical_keys_are_not_real :
  Fs.wf_fsb (Fs.fs_create_file (demo_fs []) [Z_to_bv 8 46; Z_to_bv 8 47; Z_to_bv 8 97]
               []) = false
  /\ Fs.wf_fsb (Fs.fs_create_file (demo_fs []) (wk [97] ++ [Z_to_bv 8 47]) [])
     = false
  /\ Fs.wf_fsb (Fs.fs_create_file (demo_fs []) (wk [97] ++ [Z_to_bv 8 47; Z_to_bv 8 47;
                                                   Z_to_bv 8 98]) [])
     = false
  /\ Fs.wf_fsb (Fs.fs_create_file (demo_fs []) [] []) = false.
Proof. split_conj; vm_compute; reflexivity. Qed.

(** And on a valid image the three opens are ANSWERED: /dev/null mints
    [State.FdDevNull], /dev/urandom mints [State.FdUrandom], and
    /etc/localtime is the -ENOENT [Run.localtime_absent] promises. *)
Example device_opens_answer_on_a_valid_image :
  let open bs n eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; 0; 420; 0; 0]
           (open_path_mem bs) (fun _ => None))
        (with_copyins [(8192, n)] eff)
        (init_model [] 0 0 demo_sp demo_limit (demo_input flat_key_image IEof)) in
  (match open devnull_bytes 10%nat (mkEffect 3 [] []) with
   | CheckOk m [] => fd_lookup (m_fds m) 3 = Some (FdDevNull true false)
   | _ => False
   end)
  /\ (match open urandom_bytes 13%nat (mkEffect 3 [] []) with
      | CheckOk m [] => fd_lookup (m_fds m) 3 = Some (FdUrandom true false)
      | _ => False
      end)
  /\ (match open localtime_bytes 15%nat (mkEffect (errno_ret ENOENT) [] []) with
      | CheckOk _ [] => True
      | _ => False
      end).
Proof. vm_compute. split_conj; reflexivity. Qed.


(** A table with the device at 3, over the declared stream and the
    standard root, whose /dev/urandom is the image's one random-device
    node ([Fs.Stat.fstat_devfd_spec]). *)
Definition urandom_model : Model :=
  with_urandom (urandom_stream urandom_decl)
    (mkModel [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
              (3, (FdUrandom true false))]
       (mkVmMaps [] [] 0 0 demo_limit) IEof (Fs.standard_root Fs.default_cwd)
       None None None).

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
      | CheckOk m [] => fd_lookup (m_fds m) 4 = Some (FdUrandom true false)
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
       statpin_lookup (m_statpins m) (IdDev urandom_path) = Some (mkStatPin good None false)
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
  let inp := mkProcInput_full [[]] [] (demo_fs []) Fs.default_cwd IEof
               demo_uid demo_gid demo_groups net_silent
               default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48
               (urandom_stream urandom_decl) default_kernel default_execfn
               true true false in
  let src := with_fds (fd_insert (m_fds (init_model [] 0 0 demo_sp demo_limit inp))
                         3 (FdUrandom true false))
               (init_model [] 0 0 demo_sp demo_limit inp) in
  let tgt := with_fds (fd_insert (fd_insert (m_fds (init_model [] 0 0 demo_sp demo_limit inp))
                                    4 (FdDir Fs.root)) 5 (FdUrandom true false))
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

(** In general, at one return: how many bytes a read of the device
    takes is chosen ([Sys.Fs.ReadWrite.random_page_stopb]), and which
    bytes they are is not. *)
Lemma urandom_same_bytes_in_general :
  forall i buf count eff1 eff2 m1 m2 m1' m2' evs1 evs2,
  m_urandom m1 = m_urandom m2 ->
  check_read_urandom i buf count eff1 m1 = CheckOk m1' evs1 ->
  check_read_urandom i buf count eff2 m2 = CheckOk m2' evs2 ->
  eff_ret eff1 = eff_ret eff2 ->
  eff_writes eff1 = eff_writes eff2 /\ m_urandom m1' = m_urandom m2'.
Proof.
  intros. exact (check_read_urandom_same_stream _ _ _ _ _ _ _ _ _ _ _ H H0 H1 H2).
Qed.

(* ================ /dev/urandom written, and either direction cut at a page

   [Sys.Fs.ReadWrite.random_write] and [Sys.Fs.ReadWrite.read_urandom]
   (drivers/char/random.c, Linux v6.18.46).  [write_pool_user]
   (:1420-1446) copies 64-byte blocks and stops at the first short one
   (:1430-1434), each copy taking exactly the readable bytes in front of
   the first unreadable one ([Sys.Fs.ReadWrite.random_write_countb] says
   why); [get_random_bytes_user] (:434-482) fills the request.
   Both stop after a block that leaves a positive multiple of PAGE_SIZE
   done with bytes still to move when [signal_pending(current)]
   (:1437-1439, :471-473), which [freeze_task]'s [fake_signal_wake_up]
   makes true of any user task (kernel/freezer.c:164-175). *)

(** The device at 3, open for writing only. *)
Definition urandom_wr_model : Model :=
  with_urandom (urandom_stream urandom_decl)
    (mkModel [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
              (3, (FdUrandom false true))]
       (mkVmMaps [] [] 0 0 demo_limit) IEof Fs.fs_empty None None None).

(** [n] readable source bytes at 4096, and one iovec at 16384 naming
    eight of them. *)
Definition urandom_src (n : Z) : word -> option byte :=
  fun a =>
    let x := bv_unsigned a in
    if ((4096 <=? x) && (x <? 4096 + n))%Z then Some (Z_to_bv 8 7)
    else if ((16384 <=? x) && (x <? 16400))%Z
    then nth_error (Z_to_le_bytes 8 4096 ++ Z_to_le_bytes 8 8) (Z.to_nat (x - 16384))
    else None.

(** THE WRITE'S ANSWERS.  A source readable in full: the full count, or
    4096 (the page stop), and nothing else -- not 4097, not 6000, not
    the -EFAULT.  Exactly one page: the full count and nothing short of
    it.  A source readable for 5000 of 8192 bytes: the copy of the block
    holding the first unreadable byte stops exactly at it, so 5000, or
    the page stop below it; not 4992 (the last whole block, 64 * 78),
    not 4999, not 4991, not 5001, not -EFAULT.  A source readable for 10
    of 8192 bytes: 10, and not the -EFAULT, which the first block gives
    only when it copies nothing.  A source with nothing readable:
    -EFAULT, and no count.  A count of 0 is 0 (:1426-1427).  The model
    is the same on every answer. *)
Example urandom_write_answers :
  let write n count eff := check_syscall
        (mkInput 64 [3; 4096; count; 0; 0; 0] (urandom_src n) (fun _ => None))
        eff urandom_wr_model in
  let wrote r := with_copyins [(4096, Z.to_nat r)] (mkEffect (Z_to_bv 64 r) [] []) in
  write 8192%Z 8192 (wrote 8192%Z) = CheckOk urandom_wr_model []
  /\ write 8192%Z 8192 (wrote 4096%Z) = CheckOk urandom_wr_model []
  /\ write 8192%Z 8192 (wrote 4097%Z) = CheckReject
  /\ write 8192%Z 8192 (wrote 6000%Z) = CheckReject
  /\ write 8192%Z 8192 (mkEffect (errno_ret EFAULT) [] []) = CheckReject
  /\ write 4096%Z 4096 (wrote 4096%Z) = CheckOk urandom_wr_model []
  /\ write 4096%Z 4096 (wrote 2048%Z) = CheckReject
  /\ write 5000%Z 8192 (wrote 5000%Z) = CheckOk urandom_wr_model []
  /\ write 5000%Z 8192 (wrote 4992%Z) = CheckReject
  /\ write 5000%Z 8192 (wrote 4999%Z) = CheckReject
  /\ write 5000%Z 8192 (wrote 4096%Z) = CheckOk urandom_wr_model []
  /\ write 5000%Z 8192 (wrote 4991%Z) = CheckReject
  /\ write 5000%Z 8192 (wrote 5001%Z) = CheckReject
  /\ write 5000%Z 8192 (mkEffect (errno_ret EFAULT) [] []) = CheckReject
  /\ write 10%Z 8192 (wrote 10%Z) = CheckOk urandom_wr_model []
  /\ write 10%Z 8192 (mkEffect (errno_ret EFAULT) [] []) = CheckReject
  /\ write 0%Z 8192 (mkEffect (errno_ret EFAULT) [] []) = CheckOk urandom_wr_model []
  /\ write 0%Z 8192 (wrote 64%Z) = CheckReject
  /\ write 0%Z 0 (mkEffect 0 [] []) = CheckOk urandom_wr_model [].
Proof. vm_compute. split_conj; reflexivity. Qed.

(** A WRITE OF EXACTLY ONE PAGE DOES NOT STOP EARLY: no count below it
    is one [write_pool_user] can return for a fully readable source,
    because the page test runs only with bytes still to move
    (:1437-1439). *)
Lemma urandom_page_write_does_not_stop_early : forall r,
  (0 <= r < 4096)%Z -> random_write_countb 4096 4096 r = false.
Proof.
  intros r Hr.
  assert (H : forallb (fun z => negb (random_write_countb 4096 4096 z))
                (map Z.of_nat (seq 0 4096)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H.
  apply Bool.negb_true_iff. apply H. apply in_map_iff.
  exists (Z.to_nat r). split; [lia|]. apply in_seq. lia.
Qed.

(** THE OTHER WRITE CALLS on a writable descriptor: [pwrite64] and
    [writev] give [write]'s answers.  A descriptor open only for reading
    is -EBADF on all four ([vfs_write]'s and [vfs_writev]'s FMODE_WRITE
    test). *)
Example urandom_write_calls :
  let call no args eff := check_syscall
        (mkInput no args (urandom_src 8) (fun _ => None)) eff urandom_wr_model in
  let ro no args eff := check_syscall
        (mkInput no args (urandom_src 8) (fun _ => None)) eff urandom_model in
  let iov_read := [(16384, 16%nat)] in
  call 68 [3; 4096; 8; 100; 0; 0] (with_copyins [(4096, 8%nat)] (mkEffect 8 [] []))
    = CheckOk urandom_wr_model []
  /\ call 68 [3; 4096; 8; 100; 0; 0] (with_copyins [(4096, 4%nat)] (mkEffect 4 [] []))
     = CheckReject
  /\ call 66 [3; 16384; 1; 0; 0; 0]
       (with_copyins (iov_read ++ [(4096, 8%nat)]) (mkEffect 8 [] []))
     = CheckOk urandom_wr_model []
  /\ ro 64 [3; 4096; 8; 0; 0; 0] (mkEffect (errno_ret EBADF) [] []) = CheckOk urandom_model []
  /\ ro 68 [3; 4096; 8; 100; 0; 0] (mkEffect (errno_ret EBADF) [] []) = CheckOk urandom_model []
  /\ ro 66 [3; 16384; 1; 0; 0; 0] (mkEffect (errno_ret EBADF) [] []) = CheckOk urandom_model []
  /\ ro 287 [3; 16384; 1; 100; 0; 32] (mkEffect (errno_ret EBADF) [] [])
     = CheckOk urandom_model [].
Proof. vm_compute. split_conj; reflexivity. Qed.

(** [pwritev2] ANSWERS AS [write] UNDER BOTH FLAG WORDS.  The one
    refusal RWF_NOAPPEND can add, [kiocb_set_rw_flags]' -EPERM
    (include/linux/fs.h:3890-3894, Linux v6.18.46), needs an
    append-only inode, which SCOPE.md's attribute premise excludes: so
    the -EPERM is refused under RWF_NOAPPEND as under 0, and the
    device's answer under the same words is the accepting control. *)
Example urandom_pwritev2_eperm_rejected :
  let call fl eff := check_syscall
        (mkInput 287 [3; 16384; 1; 100; 0; Z_to_bv 64 fl] (urandom_src 8) (fun _ => None))
        eff urandom_wr_model in
  let iov_read := [(16384, 16%nat)] in
  call RWF_NOAPPEND (with_copyins iov_read (mkEffect (errno_ret EPERM) [] []))
    = CheckReject
  /\ call RWF_NOAPPEND (with_copyins (iov_read ++ [(4096, 8%nat)]) (mkEffect 8 [] []))
     = CheckOk urandom_wr_model []
  /\ call 0%Z (with_copyins iov_read (mkEffect (errno_ret EPERM) [] []))
     = CheckReject
  /\ call 0%Z (with_copyins (iov_read ++ [(4096, 8%nat)]) (mkEffect 8 [] []))
     = CheckOk urandom_wr_model [].
Proof. vm_compute. split_conj; reflexivity. Qed.

(** 8192 writable bytes at 4096, and a stream of 8192 declared bytes. *)
Definition urandom_page_wmem : word -> option byte :=
  fun a => if ((4096 <=? bv_unsigned a) && (bv_unsigned a <? 12288))%Z
           then Some (Z_to_bv 8 0) else None.

Definition urandom_page_model : Model :=
  with_urandom (urandom_stream (repeat 5%Z 8192)) urandom_model.

(** A READ OF MORE THAN A PAGE MAY RETURN A PAGE, the first 4096 bytes
    of the stream, which then holds the rest; the full count is the
    other answer, and 4097 or 2048 are refused. *)
Example urandom_read_stops_at_a_page :
  let read eff := check_syscall
        (mkInput 63 [3; 4096; 8192; 0; 0; 0] (fun _ => None) urandom_page_wmem)
        eff urandom_page_model in
  let got k := mkEffect (Z_to_bv 64 (Z.of_nat k)) [(4096, repeat (Z_to_bv 8 5) k)] [] in
  (match read (got 4096%nat) with
   | CheckOk m [] => m_urandom m = urandom_stream (repeat 5%Z 4096)
   | _ => False
   end)
  /\ (match read (got 8192%nat) with
      | CheckOk m [] => m_urandom m = IEof
      | _ => False
      end)
  /\ read (got 4097%nat) = CheckReject
  /\ read (got 2048%nat) = CheckReject
  (* pread64 at any position: the same page stop, the same remainder *)
  /\ (match check_syscall
              (mkInput 67 [3; 4096; 8192; 100; 0; 0] (fun _ => None) urandom_page_wmem)
              (got 4096%nat) urandom_page_model with
      | CheckOk m [] => m_urandom m = urandom_stream (repeat 5%Z 4096)
      | _ => False
      end).
Proof. vm_compute. split_conj; reflexivity. Qed.

(** ".." AND "." GET THE SAME ANSWER ON EVERY ARM, which is a claim
    about two flag words and two pathnames at once and so is a literal
    rather than a real run: a run makes the one call it makes.  Both are
    directory references the walk answers without a lookup, so the
    clobbering shape is -EISDIR for each and the read shape hands back a
    directory fd for each.

    Without the walk's ".." row ([Fs.walk_comps]' [LastDotDot]), the
    second of each pair would be wrong: the
    create shape would MINT A KEY SPELLED "..", and the read shape would
    answer -ENOENT, which Linux never returns for "..".  The last conjunct is
    the control that keeps the first four from being satisfied by a
    model that declines everything — a claimed SUCCESS on the create
    shape is rejected, for ".." exactly as for ".". *)
Example openat_dotdot_answers_as_dot_does :
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof) in
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
     | CheckOk m [] => fd_lookup (m_fds m) (Z_to_bv 64 3) = Some (FdDir Fs.default_cwd)
     | _ => False end
  /\ match open dotdot 3%nat 0%Z (mkEffect 3 [] []) with
     | CheckOk m [] => fd_lookup (m_fds m) (Z_to_bv 64 3) = Some (FdDir Fs.root)
     | _ => False end
  (* ...and neither is answered by declining: a claimed success on the
     create shape is REFUSED, which is what makes the four above real *)
  /\ open dot 2%nat wr_create_flags (mkEffect 3 [] []) = CheckReject
  /\ open dotdot 3%nat wr_create_flags (mkEffect 3 [] []) = CheckReject.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE OVER-MATCH GUARD FOR [Fs.comp_kind], and the most load-bearing
    of the three below.  "..." is an ORDINARY NAME: it is not a directory
    reference, so the create arm mints a key for it exactly as it would
    for "f".  [Fs.comp_kind] uses [path_eqb] against [Fs.dot_comp] and
    [Fs.dotdot_comp] and nothing else, so this holds — but nothing else in the tree
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
          (init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof)) with
  | CheckOk m [] => file_at (m_fs m) (wk [46; 46; 46]) = Some []
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.


(* ================================ openat's O_DIRECTORY arm

   [Fs.Open.openat_dir_spec] answers O_RDONLY|O_DIRECTORY.  Three claims
   about it that a real run cannot make: an equality between two FLAG
   WORDS, a decline that must not depend on what the kernel said, and a
   file-system image whose keys hold a separator — no modeled syscall
   puts one there. *)

(** THE ARM'S FOUR ANSWERS, AND THE FLAG IS REALLY READ.  The last two
    conjuncts are what make the first four evidence of anything: a
    claimed SUCCESS on a name the image holds as a file is refused, so
    the -ENOTDIR is not a spec that admits everything; and the SAME name
    under bare O_RDONLY is a readable file fd rather than -ENOTDIR, so
    the errno is O_DIRECTORY's doing and not the name's. *)
Example openat_directory_word_answers :
  let m0 fs := init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof) in
  let open fs bs n fl eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 0; 0; 0]
           (open_path_mem bs) (fun _ => None))
        (with_copyins [(8192, n)] eff) (m0 fs) in
  let dir_word := (O_DIRECTORY + O_LARGEFILE + O_CLOEXEC)%Z in
  let have := demo_fs [([97], SFile [104])] in
  let absent := demo_fs [] in
  (* "." and "..": a directory fd at the lowest free slot *)
  (match open absent [46%Z] 2%nat dir_word (mkEffect 3 [] []) with
   | CheckOk m [] => fd_lookup (m_fds m) (Z_to_bv 64 3) = Some (FdDir Fs.default_cwd)
   | _ => False end)
  /\ (match open absent [46%Z; 46%Z] 3%nat dir_word (mkEffect 3 [] []) with
      | CheckOk m [] => fd_lookup (m_fds m) (Z_to_bv 64 3) = Some (FdDir Fs.root)
      | _ => False end)
  (* a file the image holds is not a directory: -ENOTDIR, model unchanged *)
  /\ open have [97%Z] 2%nat dir_word (mkEffect (errno_ret ENOTDIR) [] [])
     = CheckOk (m0 have) []
  (* an absent name never reaches the directory test: -ENOENT *)
  /\ open absent [97%Z] 2%nat dir_word (mkEffect (errno_ret ENOENT) [] [])
     = CheckOk (m0 absent) []
  (* ...and a claimed descriptor for the file is REFUSED *)
  /\ open have [97%Z] 2%nat dir_word (mkEffect 3 [] []) = CheckReject
  (* ...while the same name under bare O_RDONLY is a file fd *)
  /\ (match open have [97%Z] 2%nat 0%Z (mkEffect 3 [] []) with
      | CheckOk m [] => fd_lookup (m_fds m) (Z_to_bv 64 3)
                        = Some (FdFile 1 (Z_to_bv 64 0))
      | _ => False end).
Proof. vm_compute. split_conj; check_eq. Qed.

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
  let have := demo_fs [([97], SFile [104])] in
  let absent := demo_fs [] in
  open absent [46%Z] 2%nat wide (mkEffect 3 [] [])
    = open absent [46%Z] 2%nat O_DIRECTORY (mkEffect 3 [] [])
  /\ open absent [46%Z; 46%Z] 3%nat wide (mkEffect 3 [] [])
     = open absent [46%Z; 46%Z] 3%nat O_DIRECTORY (mkEffect 3 [] [])
  /\ open have [97%Z] 2%nat wide (mkEffect (errno_ret ENOTDIR) [] [])
     = open have [97%Z] 2%nat O_DIRECTORY (mkEffect (errno_ret ENOTDIR) [] [])
  /\ open absent [97%Z] 2%nat wide (mkEffect (errno_ret ENOENT) [] [])
     = open absent [97%Z] 2%nat O_DIRECTORY (mkEffect (errno_ret ENOENT) [] []).
Proof. vm_compute. repeat split; reflexivity. Qed.

(** THE NAME_MAX BOUNDARY, stated as the pair a boundary claim needs: a
    256-byte component admits -ENAMETOOLONG beside the answer a larger
    limit would give, and a 255-byte one admits only the answer.  Over
    [Uapi.NAME_MAX] the -ENAMETOOLONG belongs to the FILESYSTEM (the
    NAME_MAX test of [simple_lookup], fs/libfs.c:71-72, the lookup of
    tmpfs and ramfs).  No supported run is on a file system with a
    larger limit, so the walk's answer beside it is a priority-2 gap
    ([Fs.comp_too_long]). *)
Example openat_directory_name_max_boundary :
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof) in
  let open bs n eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192;
                     Z_to_bv 64 (O_DIRECTORY + O_LARGEFILE + O_CLOEXEC);
                     0; 0; 0]
           (open_path_mem bs) (fun _ => None))
        (with_copyins [(8192, n)] eff) m0 in
  open (repeat 97%Z 256) 257%nat (mkEffect (errno_ret ENOENT) [] [])
    = CheckOk m0 []
  /\ open (repeat 97%Z 256) 257%nat (mkEffect (errno_ret ENAMETOOLONG) [] [])
    = CheckOk m0 []
  /\ open (repeat 97%Z 255) 256%nat (mkEffect (errno_ret ENOENT) [] [])
     = CheckOk m0 []
  /\ open (repeat 97%Z 255) 256%nat (mkEffect (errno_ret ENAMETOOLONG) [] [])
     = CheckReject.
Proof. vm_compute. split_conj; reflexivity. Qed.

(** THE EXCLUSIVE APPEND WORD AT ITS EDGES: each is a change a wrong arm
    could make in [Fs.Open.openat_append_spec] and its checker
    alike, closing every proof.
    - A 256-byte name is created as a 255-byte one is, and
      -ENAMETOOLONG is admitted beside it: the limit is the file
      system's (the pair above states it for O_DIRECTORY).
    - Without O_CREAT nothing is created: Linux answers an absent name
      with the lookup's -ENOENT, since [lookup_open] creates only under
      O_CREAT (fs/namei.c, Linux v6.18.46), and
      [Fs.Open.modeled_open_flags] declines the word before the path.
    - A name under /tmp is created like any other, and /etc/localtime,
      under an absent /etc, is the walk's -ENOENT. *)
Example openat_excl_append_edges :
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof) in
  let open bs fl eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           (open_path_mem bs) (fun _ => None))
        (with_copyins [(8192, S (length bs))] eff) m0 in
  let ok r := match r with CheckOk _ _ => true | _ => false end in
  (* NAME_MAX: 256 bytes created, and -ENAMETOOLONG beside it; 255
     created *)
  ok (open (repeat 97%Z 256) excl_append_create_flags (mkEffect 3 [] []))
    = true
  /\ open (repeat 97%Z 256) excl_append_create_flags
       (mkEffect (errno_ret ENAMETOOLONG) [] [])
     = CheckOk m0 []
  /\ ok (open (repeat 97%Z 255) excl_append_create_flags (mkEffect 3 [] []))
     = true
  (* no O_CREAT: not this word, and declined before the path *)
  /\ open [102%Z] (O_WRONLY + O_EXCL + O_APPEND)%Z (mkEffect 3 [] [])
     = CheckUnmodeled
  /\ open [102%Z] (O_WRONLY + O_EXCL + O_APPEND)%Z
       (mkEffect (errno_ret ENOENT) [] [])
     = CheckUnmodeled
  (* under /tmp it creates; at /etc/localtime it is -ENOENT *)
  /\ ok (open [47; 116; 109; 112; 47; 100]%Z excl_append_create_flags
           (mkEffect 3 [] [])) = true
  /\ open localtime_bytes excl_append_create_flags
       (mkEffect (errno_ret ENOENT) [] [])
     = CheckOk m0 [].
Proof. vm_compute. split_conj; check_eq. Qed.


(* ================================================ faccessat2 (439)

   Two claims, over the one thing faccessat2 adds to faccessat: the
   flag word.  [faccessat2_accepted_flags_change_no_answer] above is
   the third. *)

(** 'a', NUL at 8192. *)
Definition fa_mem_name_a : word -> option byte := open_path_mem [97%Z].

(** The model both faccessat2 examples below run against: one present
    file "a" in the working directory. *)
Definition fa2_model : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs [([97], SFile [])]) IEof).

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
Proof. split; check_eq. Qed.

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
Proof. split; check_eq. Qed.


(* ============================== "/tmp/<name>", keys of the image

   /tmp is a folder of the standard root, so "/tmp/out.gif" is an
   absolute key the walk reaches like any other: the open, read and
   unlink arms answer it with nothing of their own. *)

(** The bytes of "/tmp/out.gif". *)
Definition tmp_gif_bytes : list Z :=
  [47; 116; 109; 112; 47; 111; 117; 116; 46; 103; 105; 102]%Z.

(** The same path as an image KEY. *)
Definition tmp_gif_key : Fs.path :=
  map (fun z => Z_to_bv 8 z) tmp_gif_bytes.

(** THE ROUND TRIP, on an image whose /tmp is EMPTY: create the name,
    then read it back at a second descriptor, then remove it.  This is
    the shape a program makes when it writes a temporary file, reads it
    back and removes it.  The create records the key EMPTY, exactly as
    [Fs.Open.create_wronly] does; the descriptor is an ordinary
    [State.FdFileW] on the absolute key. *)
Example openat_tmp_create_read_unlink :
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof) in
  let open fl eff m := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           (open_path_mem tmp_gif_bytes) (fun _ => None))
        (with_copyins [(8192, 13%nat)] eff) m in
  match open wr_create_flags (mkEffect 3 [] []) m0 with
  | CheckOk m1 [] =>
      (* the key is there, empty, and the descriptor is write-only on it *)
      file_at (m_fs m1) tmp_gif_key = Some []
      /\ fd_lookup (m_fds m1) (Z_to_bv 64 3) = Some (FdFileW 1 (Z_to_bv 64 0))
      (* the read shape now answers, at the next free descriptor *)
      /\ match open 0%Z (mkEffect 4 [] []) m1 with
         | CheckOk m2 [] =>
             fd_lookup (m_fds m2) (Z_to_bv 64 4) = Some (FdFile 1 (Z_to_bv 64 0))
         | _ => False end
      (* ...and the removal takes the key away, once no fd names it *)
      /\ match check_syscall
                 (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0]
                    (open_path_mem tmp_gif_bytes) (fun _ => None))
                 (with_copyins [(8192, 13%nat)] (mkEffect 0 [] []))
                 (with_fds [] m1) with
         | CheckOk m3 [] => m_fs m3 = m_fs m0
         | _ => False end
      (* THE IGNORED BITS COME THROUGH: the word is matched past
         [Open.open_ignored_flags] — O_CLOEXEC, O_LARGEFILE and
         O_NONBLOCK — so the create word carrying any of them lands in
         the same model.  A real run cannot separate this from the bare
         word; only a literal can. *)
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
               = Some (FdFile 1 (Z_to_bv 64 0))
         | _ => False end
  | _ => False
  end.
Proof. vm_compute. split_conj; check_eq. Qed.

(** THE OPEN AFTER THE UNLINK IS -ENOENT (issue #2111), on an image
    whose /tmp is EMPTY: create "/tmp/x", close the descriptor, unlink
    the name, then open the same name O_RDONLY.  This is the shape a
    program makes when it removes a temporary file and later looks for
    it again.  Linux answers the last open -ENOENT: the walk finds /tmp
    and no "x" in it, and without O_CREAT [lookup_fast_for_open] or
    [lookup_open] hands back a negative dentry, which [step_into]
    receives from [open_last_lookups] (fs/namei.c:3922, Linux
    v6.18.46); its [handle_mounts] calls [traverse_mounts], which
    answers -ENOENT for a negative dentry (:1537-1538).  That is
    [Open.openat_read_spec]'s [Fs.RMissing] row.  The /tmp arm that the
    walk replaced declined this open.

    EACH CALL STARTS FROM THE MODEL THE CALL BEFORE IT LEFT, and each
    line names that model: "opened" after the create, "held" after the
    close, and the launch model again after the unlink.  So the last
    group is about the run's own state and not about a second image.

    THE ANSWER FOLLOWS THE UNLINK, and the middle group is what shows
    it.  After the close and before the unlink, the same call gets a
    descriptor on the file, and -ENOENT is refused there.  After the
    unlink, -ENOENT is accepted and the model does not move.
    Descriptor 3 is refused there: it is the lowest free number, the
    answer a model that still held the name would accept, and no kernel
    gives it.  The last two lines are the word that musl's open()
    issues, with [Uapi.O_LARGEFILE] set.

    NOT PINNED HERE: the walk's own -ENOMEM and -EACCES.  They stay
    admitted beside the -ENOENT, as beside every walk with a last name
    ([Namei.walk_errnos]). *)
Example openat_tmp_reopen_after_unlink_is_enoent :
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof) in
  (* "/tmp/x", NUL at 8192 + 6, and the key the walk gives it *)
  let x_mem := open_path_mem [47; 116; 109; 112; 47; 120]%Z in
  let x_key := Fs.child_key Fs.tmp_dir [Z_to_bv 8 120] in
  let open fl mode eff m := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; mode; 0; 0]
           x_mem (fun _ => None))
        (with_copyins [(8192, 7%nat)] eff) m in
  (* the launch model with the empty file at the key, and no descriptor on it *)
  let held := with_fs (Fs.fs_create_file (m_fs m0) x_key []) m0 in
  (* ...and with descriptor 3 write-only on it *)
  let opened := with_fds (fd_insert (m_fds m0) 3 (FdFileW 1 (Z_to_bv 64 0))) held in
  (* open("/tmp/x", O_WRONLY|O_CREAT|O_TRUNC, 0600) = 3 *)
  open wr_create_flags 384 (mkEffect 3 [] []) m0 = CheckOk opened []
  (* close(3) = 0 *)
  /\ check_syscall
       (mkInput 57 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) opened
     = CheckOk held []
  (* WHILE THE NAME IS HELD the read word opens it... *)
  /\ open 0%Z 0 (mkEffect 3 [] []) held
     = CheckOk (with_fds (fd_insert (m_fds held) 3 (FdFile 1 (Z_to_bv 64 0)))
                  held) []
  (* ...and -ENOENT is refused *)
  /\ open 0%Z 0 (mkEffect (errno_ret ENOENT) [] []) held = CheckReject
  (* unlink("/tmp/x") = 0: the run is at the launch model again *)
  /\ check_syscall
       (mkInput 35 [AT_FDCWD; 8192; 0; 0; 0; 0] x_mem (fun _ => None))
       (with_copyins [(8192, 7%nat)] (mkEffect 0 [] [])) held
     = CheckOk m0 []
  (* open("/tmp/x", O_RDONLY) = -ENOENT, and the model does not move *)
  /\ open 0%Z 0 (mkEffect (errno_ret ENOENT) [] []) m0 = CheckOk m0 []
  (* a descriptor for the removed name is refused *)
  /\ open 0%Z 0 (mkEffect 3 [] []) m0 = CheckReject
  (* the same two answers under O_LARGEFILE *)
  /\ open O_LARGEFILE 0 (mkEffect (errno_ret ENOENT) [] []) m0 = CheckOk m0 []
  /\ open O_LARGEFILE 0 (mkEffect 3 [] []) m0 = CheckReject.
Proof. split_conj; check_eq. Qed.

(** A read of a name the IMAGE holds rather than the run created: the
    program names the whole path, and the walk reaches the file under
    /tmp. *)
Example openat_tmp_declared_name_reads :
  match check_syscall
          (mkInput 56 [AT_FDCWD; 8192; 0; 420; 0; 0]
             (open_path_mem tmp_gif_bytes) (fun _ => None))
          (with_copyins [(8192, 13%nat)] (mkEffect 3 [] []))
          (init_model [] 0 0 demo_sp demo_limit
             (demo_input (Fs.fs_create_file (demo_fs []) tmp_gif_key [104; 105]) IEof)) with
  | CheckOk m [] =>
      fd_lookup (m_fds m) (Z_to_bv 64 3) = Some (FdFile 1 (Z_to_bv 64 0))
      /\ file_at (m_fs m) tmp_gif_key = Some [104; 105]
  | _ => False
  end.
Proof. vm_compute. split_conj; check_eq. Qed.

(** THE [Uapi.NAME_MAX] BOUNDARY under /tmp, from both sides: a
    component of 255 bytes is answered, and a component of 256 is
    answered too, with -ENAMETOOLONG admitted beside it, at the create
    word and at the read word.  The -ENAMETOOLONG a longer component
    may get comes out of the FILESYSTEM's own lookup rather than out of
    fs/namei.c ([simple_lookup], fs/libfs.c:71-72, Linux v6.18.46). *)
Example openat_tmp_name_max_boundary :
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs []) IEof) in
  (* "/tmp/" followed by n copies of 'a' *)
  let name n := List.repeat 97%Z n in
  let open n fl eff := check_syscall
        (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
           (open_path_mem ([47; 116; 109; 112; 47]%Z ++ name n)) (fun _ => None))
        (with_copyins [(8192, (6 + n)%nat)] eff) m0 in
  (* 255: answered, and the length errno refused *)
  match open 255%nat wr_create_flags (mkEffect 3 [] []) with
  | CheckOk _ [] => True | _ => False end
  /\ open 255%nat 0%Z (mkEffect (errno_ret ENOENT) [] []) = CheckOk m0 []
  /\ open 255%nat 0%Z (mkEffect (errno_ret ENAMETOOLONG) [] []) = CheckReject
  (* 256: answered, and -ENAMETOOLONG admitted beside it, at the create
     word and at the read word alike *)
  /\ match open 256%nat wr_create_flags (mkEffect 3 [] []) with
     | CheckOk _ [] => True | _ => False end
  /\ open 256%nat wr_create_flags (mkEffect (errno_ret ENAMETOOLONG) [] [])
     = CheckOk m0 []
  /\ open 256%nat 0%Z (mkEffect (errno_ret ENOENT) [] []) = CheckOk m0 []
  /\ open 256%nat 0%Z (mkEffect (errno_ret ENAMETOOLONG) [] []) = CheckOk m0 [].
Proof. vm_compute. split_conj; try exact I; check_eq. Qed.


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
  init_model [] 0 0 demo_sp demo_limit (demo_input (demo_fs [([97], SFile [])]) IEof).

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
      = Some (FdFile 1 (Z_to_bv 64 0))
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

(* ================================ a file three folders down, opened by name

   An absolute pathname "/usr/local/<d>/<f>" walked from the root, for
   every pair of names [d], [f] a directory can hold, over two kinds of
   image: N, where the walk of that pathname, every link on it
   followed, ends at a component that is not there, and S, where /usr,
   /usr/local and /usr/local/<d> are folders and /usr/local/<d>/<f>
   names a regular file (inode [i]) of any content, everything else in
   the image free.
   Over N the open is -ENOENT; over S it gives a descriptor on the
   file's inode that [fstat] calls a regular file of the content's length
   and of the file's link count, that [read] hands the content out of in
   order and then 0, and that [close] releases.

   N IS STATED OVER THE WALK because a link on the way is walked
   through: [step_into] (fs/namei.c:2013-2021) hands a link that is not
   the last component to [pick_link], and the walk goes on through its
   body (:1945-1973).  So an image whose /usr is a link to a folder with
   no "local" in it is in N, and one whose /usr is a link to a folder
   holding local/<d>/<f> opens the file (both below).
   Linux v6.18.46: [link_path_walk] (fs/namei.c:2441) hands each
   component to [walk_component] (:2134-2157), whose [step_into]
   (:1984-1992) runs [handle_mounts]; on a negative dentry its
   [traverse_mounts] is -ENOENT (:1536-1538), for a missing folder on
   the way and, through [open_last_lookups]' own [step_into]
   (:3922), for a missing last component of an open without O_CREAT.
   [vfs_fstat] (fs/stat.c:276-281) fills the [struct stat] from
   [generic_fillattr] (:90 the mode, :91 the link count, :95 the size)
   and [cp_new_stat] copies the three (:488, :489, :495).  A regular
   file's read returns what lies
   between the position and [i_size], 0 at or past it
   ([shmem_file_read_iter], mm/shmem.c:3384-3388, :3417-3423).  [close]
   is [close_fd] (fs/file.c:711-720). *)

Definition r1_usr : Fs.path := map (Z_to_bv 8) [117; 115; 114]%Z.
Definition r1_local : Fs.path := map (Z_to_bv 8) [108; 111; 99; 97; 108]%Z.

(** A name a directory can hold: 1 to 255 bytes, no "/", no NUL, not
    "." and not "..". *)
Definition r1_name_ok (c : Fs.path) : Prop :=
  Fs.comp_ok c = true /\ (length c <= Fs.name_max)%nat.

(** "/usr/local/<d>/<f>", which is also the key the file sits at. *)
Definition r1_path (d f : Fs.path) : Fs.path :=
  Fs.path_join [r1_usr; r1_local; d; f].

Definition r1_usr_key : Fs.path := Fs.path_join [r1_usr].
Definition r1_local_key : Fs.path := Fs.path_join [r1_usr; r1_local].
Definition r1_dir_key (d : Fs.path) : Fs.path := Fs.path_join [r1_usr; r1_local; d].

(** Image S: the standard root, the three folders and the file, whose
    name holds inode [i] and whose inode holds [c]. *)
Definition r1_image_s (fs : Fs.Fs) (d f : Fs.path) (i : Fs.ino) (c : list byte)
    : Prop :=
  Fs.standard_root_present fs
  /\ fs_lookup fs Fs.root = Some EDir
  /\ fs_lookup fs r1_usr_key = Some EDir
  /\ fs_lookup fs r1_local_key = Some EDir
  /\ fs_lookup fs (r1_dir_key d) = Some EDir
  /\ fs_lookup fs (r1_path d f) = Some (EFile i)
  /\ Fs.fs_ino_data fs i = c.

(** The walk an open with flag word 0 or O_LARGEFILE asks for
    ([Open.open_walk_mode]): the last link followed, no folder demanded. *)
Definition r1_md : Fs.WalkMode := Fs.WalkFull true false.

(** Image N: the standard root, and the walk of "/usr/local/<d>/<f>",
    every link on it followed, ends at a component that is not there:
    [Fs.RAbsent] for one on the way, [Fs.RMissing] for the last. *)
Definition r1_image_n (fs : Fs.Fs) (d f : Fs.path) : Prop :=
  Fs.standard_root_present fs
  /\ match Fs.resolve r1_md fs Fs.root (r1_path d f) with
     | (Fs.RAbsent _, _, _) => True
     | (Fs.RMissing _ _, _, _) => True
     | _ => False
     end.

(** One step of the walk from a folder onto a name that is there and is
    not a link, with more of the path after it ... *)
Lemma r1_comps_mid : forall fs md fd next fl dr k c r e' lk ts lg,
  r1_name_ok c -> Fs.comps_done r = false ->
  Fs.mode_parent md = false -> Fs.mode_create md = false ->
  Fs.at_outside k c = false ->
  fs_lookup fs (Fs.child_key k c) = Some e' -> Fs.entry_is_link e' = false ->
  Fs.walk_comps fs md fd next fl dr k EDir (c :: r) lk ts lg
  = Fs.walk_comps fs md fd next fl dr (Fs.child_key k c) e' r lk ts lg.
Proof.
  intros fs md fd next fl dr k c r e' lk ts lg [Hc Hl] Hdone Hp Hcr Hout Hk Hnl.
  assert (Hkind : Fs.comp_kind c = Fs.LastNorm).
  { unfold Fs.comp_kind.
    rewrite (Fs.comp_ok_not_dot c Hc), (Fs.comp_ok_not_dotdot c Hc). reflexivity. }
  assert (Hlong : Fs.comp_too_long c = false)
    by (unfold Fs.comp_too_long; apply Nat.ltb_ge; exact Hl).
  assert (Hlast : Fs.last_slash r = false)
    by (unfold Fs.last_slash; rewrite Hdone; reflexivity).
  cbn [Fs.walk_comps].
  rewrite (Fs.comp_ok_nonempty c Hc), Hp, Hkind, Hout, Hcr. cbn [negb andb].
  rewrite Hk.
  unfold Fs.upd_kind, Fs.upd_slash. rewrite Hdone, Hlast, Hlong, !orb_false_r.
  destruct e' as [i| |dk|b]; [reflexivity | reflexivity | reflexivity | discriminate Hnl].
Qed.

(** ... and onto the LAST name, which is there and is not a link. *)
Lemma r1_comps_last : forall fs md fd next fl dr k c r e' lk ts lg,
  r1_name_ok c -> r = [] ->
  Fs.mode_parent md = false -> Fs.mode_create md = false ->
  Fs.at_outside k c = false ->
  fs_lookup fs (Fs.child_key k c) = Some e' -> Fs.entry_is_link e' = false ->
  Fs.walk_comps fs md fd next fl dr k EDir (c :: r) lk ts lg
  = Fs.walk_comps fs md fd next fl dr (Fs.child_key k c) e' r Fs.LastNorm false lg.
Proof.
  intros fs md fd next fl dr k c r e' lk ts lg [Hc Hl] Hr Hp Hcr Hout Hk Hnl.
  assert (Hkind : Fs.comp_kind c = Fs.LastNorm).
  { unfold Fs.comp_kind.
    rewrite (Fs.comp_ok_not_dot c Hc), (Fs.comp_ok_not_dotdot c Hc). reflexivity. }
  assert (Hlong : Fs.comp_too_long c = false)
    by (unfold Fs.comp_too_long; apply Nat.ltb_ge; exact Hl).
  cbn [Fs.walk_comps].
  rewrite (Fs.comp_ok_nonempty c Hc), Hp, Hkind, Hout, Hcr. cbn [negb andb].
  rewrite Hk. subst r.
  replace (Fs.last_slash []) with false by reflexivity.
  unfold Fs.upd_kind, Fs.upd_slash.
  replace (Fs.comps_done []) with true by reflexivity.
  cbv iota. rewrite Hkind, Hlong, !orb_false_r.
  destruct e' as [i| |dk|b]; [reflexivity | reflexivity | reflexivity | discriminate Hnl].
Qed.

Lemma r1_path_split : forall d f, r1_name_ok d -> r1_name_ok f ->
  Fs.path_split (r1_path d f) = [] :: [r1_usr; r1_local; d; f].
Proof.
  intros d f [Hd _] [Hf _]. apply Fs.path_split_join.
  constructor; [reflexivity|]. constructor; [reflexivity|].
  constructor; [exact Hd|]. constructor; [exact Hf|]. constructor.
Qed.

Lemma r1_last_kind : forall d f, r1_name_ok d -> r1_name_ok f ->
  Fs.path_last_kind (r1_path d f) = Fs.LastNorm.
Proof.
  intros d f Hd Hf. unfold Fs.path_last_kind. rewrite (r1_path_split d f Hd Hf).
  destruct Hf as [Hf _]. cbn [Fs.last_comp].
  rewrite (Fs.comp_ok_nonempty f Hf). cbv beta iota. unfold Fs.comp_kind.
  rewrite (Fs.comp_ok_not_dot f Hf), (Fs.comp_ok_not_dotdot f Hf). reflexivity.
Qed.

Lemma r1_ends_slash : forall d f, r1_name_ok f ->
  Fs.path_ends_slash (r1_path d f) = false.
Proof.
  intros d f [Hf _]. unfold Fs.path_ends_slash, r1_path.
  assert (E : Fs.path_join [r1_usr; r1_local; d; f]
              = (Fs.path_join [r1_usr; r1_local; d] ++ [Fs.path_slash_byte]) ++ f).
  { cbn [Fs.path_join]. rewrite !app_nil_r, <- !app_assoc. reflexivity. }
  rewrite E, rev_app_distr. destruct (rev f) as [|b r] eqn:Hr.
  - apply (f_equal (@rev _)) in Hr. rewrite rev_involutive in Hr. subst f.
    discriminate Hf.
  - cbn [app]. apply (Fs.comp_ok_no_slash f b Hf). apply in_rev. rewrite Hr. now left.
Qed.

Lemma r1_dir_child : forall d f, r1_name_ok d -> r1_name_ok f ->
  Fs.child_key (r1_dir_key d) f = r1_path d f.
Proof.
  intros d f [Hd _] [Hf _]. unfold Fs.child_key.
  change (r1_dir_key d) with (Fs.key_of_comps [r1_usr; r1_local; d]).
  rewrite Fs.key_comps_of_comps; [reflexivity|].
  constructor; [reflexivity|]. constructor; [reflexivity|].
  constructor; [exact Hd|]. constructor.
Qed.

(** The walk starts at the root, and its first piece is the empty one in
    front of the leading separator. *)
Lemma r1_resolve_head : forall md fs cwd d f, r1_name_ok d -> r1_name_ok f ->
  fs_lookup fs Fs.root = Some EDir ->
  Fs.resolve_res md fs cwd (r1_path d f)
  = Fs.walk_comps fs md false (Fs.walk_next fs md Fs.link_max) (Fs.mode_follow md)
      (Fs.mode_dir md) Fs.root EDir [r1_usr; r1_local; d; f] Fs.LastRoot false false.
Proof.
  intros md fs cwd d f Hd Hf Hroot. unfold Fs.resolve_res, Fs.walk_from.
  replace (Fs.resolve_start cwd (r1_path d f)) with Fs.root by reflexivity.
  rewrite Hroot. cbv beta iota.
  rewrite Fs.walk_unfold, (r1_path_split d f Hd Hf). reflexivity.
Qed.

(** The pathname is absolute, so the working directory is not read. *)
Lemma r1_start : forall md fs cwd d f,
  Fs.resolve md fs cwd (r1_path d f) = Fs.resolve md fs Fs.root (r1_path d f).
Proof.
  intros md fs cwd d f. unfold Fs.resolve, Fs.resolve_res.
  replace (Fs.resolve_start cwd (r1_path d f)) with Fs.root by reflexivity.
  replace (Fs.resolve_start Fs.root (r1_path d f)) with Fs.root by reflexivity.
  reflexivity.
Qed.

Lemma r1_len_ok : forall c, c = r1_usr \/ c = r1_local -> (length c <= Fs.name_max)%nat.
Proof. intros c [->| ->]; apply Nat.leb_le; reflexivity. Qed.

(** Over S the walk reaches the file, at its own key. *)
Lemma r1_resolve_found : forall fs cwd d f i c,
  r1_name_ok d -> r1_name_ok f -> r1_image_s fs d f i c ->
  Fs.resolve r1_md fs cwd (r1_path d f)
  = (Fs.RFound (r1_path d f) (EFile i), Fs.LastNorm, false).
Proof.
  intros fs cwd d f i c Hd Hf (_ & Hroot & Hu & Hl & Hdk & Hfk & _).
  pose proof Hd as [Hd1 Hd2]. pose proof Hf as [Hf1 Hf2].
  unfold Fs.resolve. cbv zeta.
  rewrite (r1_resolve_head r1_md fs cwd d f Hd Hf Hroot).
  rewrite (r1_comps_mid fs r1_md _ _ _ _ Fs.root r1_usr _ EDir);
    [| split; [reflexivity | apply r1_len_ok; now left]
     | reflexivity | reflexivity | reflexivity | reflexivity | exact Hu | reflexivity].
  rewrite (r1_comps_mid fs r1_md _ _ _ _ _ r1_local _ EDir);
    [| split; [reflexivity | apply r1_len_ok; now right]
     | unfold Fs.comps_done; cbn [forallb]; rewrite (Fs.comp_ok_nonempty d Hd1); reflexivity
     | reflexivity | reflexivity | reflexivity | exact Hl | reflexivity].
  rewrite (r1_comps_mid fs r1_md _ _ _ _ _ d _ EDir);
    [| exact Hd
     | unfold Fs.comps_done; cbn [forallb]; rewrite (Fs.comp_ok_nonempty f Hf1); reflexivity
     | reflexivity | reflexivity | reflexivity | exact Hdk | reflexivity].
  change (Fs.child_key (Fs.child_key (Fs.child_key Fs.root r1_usr) r1_local) d)
    with (r1_dir_key d).
  rewrite (r1_comps_last fs r1_md _ _ _ _ _ f _ (EFile i));
    [| exact Hf | reflexivity | reflexivity | reflexivity | reflexivity
     | rewrite (r1_dir_child d f Hd Hf); exact Hfk | reflexivity].
  rewrite (r1_dir_child d f Hd Hf). reflexivity.
Qed.

(** Over N the walk stops short: [Fs.RAbsent] at a component on the way
    that is not there, [Fs.RMissing] at a last one that is not there. *)
Lemma r1_resolve_absent : forall fs cwd d f,
  r1_image_n fs d f ->
  exists r lk ts, Fs.resolve r1_md fs cwd (r1_path d f) = (r, lk, ts)
            /\ ((exists pre, r = Fs.RAbsent pre)
                \/ (exists par nm, r = Fs.RMissing par nm)).
Proof.
  intros fs cwd d f (_ & Hn). rewrite r1_start. revert Hn.
  destruct (Fs.resolve r1_md fs Fs.root (r1_path d f)) as [[r lk] ts]. intros Hn.
  exists r, lk, ts. split; [reflexivity|].
  destruct r as [k e|par nm|k|pre| | |dir nm]; cbn in Hn; try contradiction.
  - right. exists par, nm. reflexivity.
  - left. exists pre. reflexivity.
Qed.

(** The open call, its pathname's copy-in, and the two flag words. *)
Definition r1_reads (mem : word -> option byte) (pathp : word) : list (word * nat) :=
  [(pathp, cstr_access_len_aux mem pathp path_max)].

Definition r1_open_in (mem wmem : word -> option byte) (pathp fl a3 a4 a5 : word)
    : SyscallInput :=
  mkInput 56 [AT_FDCWD; pathp; fl; a3; a4; a5] mem wmem.

Lemma r1_proc_self_fd : forall d f, proc_self_fd (r1_path d f) = None.
Proof. intros d f. vm_compute. reflexivity. Qed.

Lemma r1_flags_ok : forall fl : word,
  fl = Z_to_bv 64 0 \/ fl = Z_to_bv 64 O_LARGEFILE ->
  open_shape fl = 0%Z /\ open_walk_mode fl = r1_md.
Proof. intros fl [-> | ->]; split; reflexivity. Qed.

(** Every refusal of a walk is an errno ([Fs.Namei.walk_errnos]). *)
Lemma r1_walk_errnos_ok : forall lk w, errnos_ok (walk_errnos lk w) = true.
Proof.
  intros lk w. unfold walk_errnos.
  destruct lk, (Fs.wr_followed w), (Fs.wr_res w), (Fs.wr_long w); reflexivity.
Qed.

Lemma r1_walk_reached : forall mem wmem pathp fl a3 a4 a5 m d f,
  read_cstr mem pathp = CstrOk (r1_path d f) ->
  r1_name_ok d -> r1_name_ok f ->
  walk_reached r1_md (r1_open_in mem wmem pathp fl a3 a4 a5) m pathp
  = Some (walk_errnos Fs.LastNorm
            (Fs.resolve_res r1_md (m_fs m) (m_cwd m) (r1_path d f))).
Proof.
  intros mem wmem pathp fl a3 a4 a5 m d f Hpath Hd Hf. unfold walk_reached.
  cbn [r1_open_in in_mem]. rewrite Hpath.
  replace (path_eqb (r1_path d f) []) with false by reflexivity.
  rewrite (r1_last_kind d f Hd Hf). reflexivity.
Qed.

Lemma r1_open_unfold : forall mem wmem pathp fl a3 a4 a5 m d f eff,
  read_cstr mem pathp = CstrOk (r1_path d f) ->
  open_shape fl = 0%Z ->
  fd_lookup (m_fds m) (alloc_fd (m_fds m)) = None ->
  check_syscall (r1_open_in mem wmem pathp fl a3 a4 a5) eff m
  = check_getname_refusals (r1_open_in mem wmem pathp fl a3 a4 a5) [] pathp eff m
      (check_copyins_after (r1_reads mem pathp) eff
         (check_walk_refusals (open_walk_mode fl) (r1_open_in mem wmem pathp fl a3 a4 a5)
            pathp (clear_copyins eff) m
            (Open.check_openat_resolved (r1_path d f) fl (clear_copyins eff) m))).
Proof.
  intros mem wmem pathp fl a3 a4 a5 m d f eff Hpath Hfl Hfree.
  change (check_syscall (r1_open_in mem wmem pathp fl a3 a4 a5) eff m)
    with (check_openat (r1_open_in mem wmem pathp fl a3 a4 a5) (fd32 AT_FDCWD)
            pathp fl eff m).
  unfold check_openat. rewrite (modeled_open_flags_rd fl Hfl). cbn [negb].
  cbv beta iota zeta.
  unfold openat_name_fetched, Open.check_openat_body. cbn [r1_open_in in_mem]. rewrite Hpath.
  rewrite (lowest_fd_none_free _ Hfree).
  replace (path_eqb (r1_path d f) []) with false by reflexivity.
  replace (bv_eqb (fd32 AT_FDCWD) AT_FDCWD32) with true by (vm_compute; reflexivity).
  cbn [negb]. cbv beta iota. reflexivity.
Qed.

(** [getname_flags]' own refusals ([check_getname_refusals]) add no
    descriptor: a number below 2^31 is no errno of [getname_errnos]. *)
Lemma r1_getname_fd_reject : forall i lead pathp reads fd m c,
  (bv_unsigned fd < 2 ^ 31)%Z -> c = CheckReject ->
  check_getname_refusals i lead pathp (with_copyins reads (mkEffect fd [] [])) m c
  = CheckReject.
Proof.
  intros i lead pathp reads fd m c Hfd ->.
  change (with_copyins reads (mkEffect fd [] [])) with (mkEffectU fd [] [] [] [] reads).
  unfold check_getname_refusals. cbv beta iota.
  rewrite (errno_ret_in_fd getname_errnos fd eq_refl Hfd). reflexivity.
Qed.

(** OVER N, with flag word 0 and with O_LARGEFILE, on a table with a
    free descriptor: -ENOENT with the model unchanged, and a descriptor
    is refused. *)
Lemma r1_open_absent_enoent : forall mem wmem pathp fl a3 a4 a5 m d f,
  read_cstr mem pathp = CstrOk (r1_path d f) ->
  fl = Z_to_bv 64 0 \/ fl = Z_to_bv 64 O_LARGEFILE ->
  r1_name_ok d -> r1_name_ok f -> r1_image_n (m_fs m) d f ->
  fd_lookup (m_fds m) (alloc_fd (m_fds m)) = None ->
  check_syscall (r1_open_in mem wmem pathp fl a3 a4 a5)
    (with_copyins (r1_reads mem pathp) (mkEffect (errno_ret ENOENT) [] [])) m
  = CheckOk m []
  /\ (forall fd, (bv_unsigned fd < 2 ^ 31)%Z ->
      check_syscall (r1_open_in mem wmem pathp fl a3 a4 a5)
        (with_copyins (r1_reads mem pathp) (mkEffect fd [] [])) m
      = CheckReject).
Proof.
  intros mem wmem pathp fl a3 a4 a5 m d f Hpath Hfl Hd Hf Hn Hfree.
  destruct (r1_flags_ok fl Hfl) as [Hfl0 Hmd].
  destruct (r1_resolve_absent (m_fs m) (m_cwd m) d f Hn) as (r & lk & ts & Hres & Hr).
  assert (Hrd : forall e,
    Open.check_openat_resolved (r1_path d f) fl e m
    = check_ret_only e (errno_ret ENOENT) m []).
  { intro e. unfold Open.check_openat_resolved. rewrite r1_proc_self_fd, Hmd, Hres.
    cbv beta iota zeta. rewrite Hfl0, Z.eqb_refl. cbv beta iota.
    unfold Open.check_openat_read.
    destruct Hr as [(pre & ->) | (par & nm & ->)]; reflexivity. }
  split.
  - rewrite (r1_open_unfold mem wmem pathp fl a3 a4 a5 m d f _ Hpath Hfl0 Hfree), Hrd.
    apply check_getname_refusals_of_ok.
    apply check_copyins_after_ok_iff. split; [reflexivity|].
    change (clear_copyins (with_copyins (r1_reads mem pathp)
                             (mkEffect (errno_ret ENOENT) [] [])))
      with (mkEffect (errno_ret ENOENT) [] []).
    replace (check_ret_only (mkEffect (errno_ret ENOENT) [] []) (errno_ret ENOENT) m [])
      with (CheckOk m []) by (symmetry; apply check_ret_only_ok_iff; auto).
    reflexivity.
  - intros fd Hfd.
    rewrite (r1_open_unfold mem wmem pathp fl a3 a4 a5 m d f _ Hpath Hfl0 Hfree), Hrd.
    apply r1_getname_fd_reject; [exact Hfd|].
    change (clear_copyins (with_copyins (r1_reads mem pathp) (mkEffect fd [] [])))
      with (mkEffect fd [] []).
    assert (Hne : check_ret_only (mkEffect fd [] []) (errno_ret ENOENT) m [] = CheckReject).
    { cbn [check_ret_only]. destruct (bv_eqb fd (errno_ret ENOENT)) eqn:E; [|reflexivity].
      apply bv_eqb_eq in E. subst fd. exfalso. vm_compute in Hfd. discriminate Hfd. }
    rewrite Hne, Hmd. unfold check_walk_refusals.
    rewrite (r1_walk_reached mem wmem pathp fl a3 a4 a5 m d f Hpath Hd Hf).
    cbv beta iota.
    rewrite (errno_ret_in_fd _ fd (r1_walk_errnos_ok _ _) Hfd).
    unfold check_copyins_after, check_copyins.
    destruct (access_ranges_eqb _ _); reflexivity.
Qed.

(** OVER S, with the same two words: a descriptor on the file's inode at
    offset 0, the lowest free one. *)
Lemma r1_open_found_descriptor : forall mem wmem pathp fl a3 a4 a5 m d f i c,
  read_cstr mem pathp = CstrOk (r1_path d f) ->
  fl = Z_to_bv 64 0 \/ fl = Z_to_bv 64 O_LARGEFILE ->
  r1_name_ok d -> r1_name_ok f -> r1_image_s (m_fs m) d f i c ->
  fd_lookup (m_fds m) (alloc_fd (m_fds m)) = None ->
  check_syscall (r1_open_in mem wmem pathp fl a3 a4 a5)
    (with_copyins (r1_reads mem pathp) (mkEffect (alloc_fd (m_fds m)) [] [])) m
  = CheckOk (with_fds (fd_insert (m_fds m) (alloc_fd (m_fds m))
                         (FdFile i (Z_to_bv 64 0))) m) [].
Proof.
  intros mem wmem pathp fl a3 a4 a5 m d f i c Hpath Hfl Hd Hf Hs Hfree.
  destruct (r1_flags_ok fl Hfl) as [Hfl0 Hmd].
  rewrite (r1_open_unfold mem wmem pathp fl a3 a4 a5 m d f _ Hpath Hfl0 Hfree).
  apply check_getname_refusals_of_ok.
  unfold Open.check_openat_resolved.
  rewrite r1_proc_self_fd, Hmd, (r1_resolve_found (m_fs m) (m_cwd m) d f i c Hd Hf Hs).
  cbv beta iota zeta. rewrite Hfl0, Z.eqb_refl. cbv beta iota.
  unfold Open.check_openat_read. cbv beta iota.
  unfold Open.check_open_result_mk, check_open_result, check_new_fd_result.
  change (clear_copyins (with_copyins (r1_reads mem pathp)
                           (mkEffect (alloc_fd (m_fds m)) [] [])))
    with (mkEffect (alloc_fd (m_fds m)) [] []).
  cbv beta iota.
  rewrite (errno_ret_in_alloc_fd openat_errnos (m_fds m) eq_refl), Hfree, bv_eqb_refl.
  apply check_copyins_after_ok_iff. split; reflexivity.
Qed.

(** [fstat] of a descriptor on the file, wherever its offset is: a
    well-formed [struct stat] is accepted exactly when its type is
    S_IFREG, its [st_rdev] 0, its [st_blksize] the page size, its
    [st_size] the content's length and its [st_nlink] the file's link
    count ([Fs.fs_ino_nlink]).  The first [fstat] of the inode (no pin
    yet) pins what it accepts. *)
Lemma r1_fstat_answers : forall mem wmem fd statbuf a2 a3 a4 a5 m i off c bs,
  (bv_unsigned fd < 2 ^ 31)%Z ->
  fd_lookup (m_fds m) fd = Some (FdFile i off) ->
  Fs.fs_ino_data (m_fs m) i = c ->
  (Z.of_nat (length c) < 2 ^ 64)%Z ->
  access_okb statbuf STAT_SIZE = true ->
  read_bytes_map wmem statbuf (Z_to_bv 64 STAT_SIZE) <> None ->
  statpin_lookup (m_statpins m) (IdIno i) = None ->
  stat_buf_wf bs = true ->
  let nl := bv_unsigned (Z_to_bv 32 (Z.of_nat (Fs.fs_ino_nlink (m_fs m) i))) in
  let call := check_syscall (mkInput 80 [fd; statbuf; a2; a3; a4; a5] mem wmem)
                (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] []) m in
  (stat_ifmt bs = S_IFREG ->
   stat_field_le ST_RDEV_OFF 8 bs = 0%Z ->
   stat_field_le ST_BLKSIZE_OFF 4 bs = page_size ->
   stat_field_le ST_SIZE_OFF 8 bs = Z.of_nat (length c) ->
   stat_field_le ST_NLINK_OFF 4 bs = nl ->
   call = CheckOk (with_statpin (IdIno i) (mkStatPin bs None false) m) [])
  /\ (stat_ifmt bs <> S_IFREG -> call = CheckReject)
  /\ (stat_field_le ST_SIZE_OFF 8 bs <> Z.of_nat (length c) -> call = CheckReject)
  /\ (stat_field_le ST_NLINK_OFF 4 bs <> nl -> call = CheckReject)
  /\ (stat_field_le ST_RDEV_OFF 8 bs <> 0%Z -> call = CheckReject)
  /\ (stat_field_le ST_BLKSIZE_OFF 4 bs <> page_size -> call = CheckReject).
Proof.
  intros mem wmem fd statbuf a2 a3 a4 a5 m i off c bs Hfd Hlk Hfs Hlen Hacc Hmap Hpin Hwf.
  cbv zeta.
  change (check_syscall (mkInput 80 [fd; statbuf; a2; a3; a4; a5] mem wmem)
            (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] []) m)
    with (check_fstat (mkInput 80 [fd; statbuf; a2; a3; a4; a5] mem wmem) (fd32 fd)
            statbuf (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] []) m).
  rewrite (fd32_lt31 fd Hfd).
  unfold check_fstat. rewrite Hlk. unfold check_fstat_file.
  rewrite Hacc. cbn [negb]. cbv beta iota.
  cbn [in_wmem]. destruct (read_bytes_map wmem statbuf (Z_to_bv 64 STAT_SIZE));
    [|exfalso; now apply Hmap].
  rewrite Hpin.
  unfold check_fstat_deliver_gen.
  rewrite !bv_eqb_refl. cbn [andb negb]. cbv beta iota.
  rewrite Hwf.
  unfold stat_reg_ok, stat_reg_fixed, stat_no_rdev, stat_page_blksize, stat_size_ok,
    stat_is_reg, stat_nlink_ok.
  rewrite Hfs.
  rewrite (bv_unsigned_Z_to_bv_u64 (Z.of_nat (length c)))
    by (unfold two_pow_64; lia).
  split; [|split; [|split; [|split; [|split]]]].
  - intros Ht Hr Hb Hsz Hnl. rewrite Ht, Hr, Hb, Hsz, Hnl, !Z.eqb_refl. reflexivity.
  - intros Ht. apply Z.eqb_neq in Ht. rewrite Ht. reflexivity.
  - intros Hsz. apply Z.eqb_neq in Hsz. rewrite Hsz.
    destruct (Z.eqb (stat_ifmt bs) S_IFREG), (Z.eqb (stat_field_le ST_RDEV_OFF 8 bs) 0),
      (Z.eqb (stat_field_le ST_BLKSIZE_OFF 4 bs) page_size); reflexivity.
  - intros Hnl. apply Z.eqb_neq in Hnl. rewrite Hnl, !andb_false_r. reflexivity.
  - intros Hr. apply Z.eqb_neq in Hr. rewrite Hr, andb_false_r. reflexivity.
  - intros Hb. apply Z.eqb_neq in Hb. rewrite Hb, andb_false_r. reflexivity.
Qed.

(** [read] of it: the content from the descriptor's offset, as much as
    the (clamped) count asks and the file holds, and the offset moves
    past it ... *)
Lemma r1_read_chunk : forall mem wmem fd buf count a3 a4 a5 m i off c,
  (bv_unsigned fd < 2 ^ 31)%Z ->
  fd_lookup (m_fds m) fd = Some (FdFile i off) ->
  Fs.fs_ino_data (m_fs m) i = c ->
  access_okb buf (bv_unsigned count) = true ->
  (* and [rw_verify_area]'s position test passes: [off + count] stays at
     or below [LLONG_MAX] *)
  rw_pos_einvalb off (bv_unsigned count) = false ->
  let bs := firstn (word_to_nat (Z_to_bv 64 (rw_count_clamp count)))
              (skipn (word_to_nat off) c) in
  read_bytes_map wmem buf (len_word bs) <> None ->
  bs <> [] ->
  check_syscall (mkInput 63 [fd; buf; count; a3; a4; a5] mem wmem)
    (mkEffect (len_word bs) [(buf, bs)] []) m
  = CheckOk (with_fds (fd_insert (m_fds m) fd (FdFile i (off + len_word bs))) m) [].
Proof.
  intros mem wmem fd buf count a3 a4 a5 m i off c Hfd Hlk Hfs Hacc Hpos bs Hmap Hne.
  change (check_syscall (mkInput 63 [fd; buf; count; a3; a4; a5] mem wmem)
            (mkEffect (len_word bs) [(buf, bs)] []) m)
    with (check_read (mkInput 63 [fd; buf; count; a3; a4; a5] mem wmem) (fd32 fd)
            buf count (mkEffect (len_word bs) [(buf, bs)] []) m).
  rewrite (fd32_lt31 fd Hfd).
  unfold check_read. rewrite Hlk, Hacc. cbn [negb]. cbv beta iota.
  rewrite Hpos. cbv beta iota zeta. rewrite Hfs. rewrite file_read_unguarded. fold bs.
  cbn [in_wmem]. clearbody bs.
  destruct (read_bytes_map wmem buf (len_word bs)); [|exfalso; now apply Hmap].
  destruct bs as [|b0 bs0]; [exfalso; now apply Hne|].
  cbv beta iota. rewrite !bv_eqb_refl.
  rewrite (proj2 (listN_eqb_eq (b0 :: bs0) (b0 :: bs0)) eq_refl).
  reflexivity.
Qed.

(** ... and at or past the end of the content, 0 with nothing written. *)
Lemma r1_read_end : forall mem wmem fd buf count a3 a4 a5 m i off c,
  (bv_unsigned fd < 2 ^ 31)%Z ->
  fd_lookup (m_fds m) fd = Some (FdFile i off) ->
  Fs.fs_ino_data (m_fs m) i = c ->
  access_okb buf (bv_unsigned count) = true ->
  rw_pos_einvalb off (bv_unsigned count) = false ->
  (Z.of_nat (length c) <= bv_unsigned off)%Z ->
  check_syscall (mkInput 63 [fd; buf; count; a3; a4; a5] mem wmem)
    (mkEffect (Z_to_bv 64 0) [] []) m
  = CheckOk (with_fds (fd_insert (m_fds m) fd (FdFile i (off + Z_to_bv 64 0))) m) [].
Proof.
  intros mem wmem fd buf count a3 a4 a5 m i off c Hfd Hlk Hfs Hacc Hpos Hend.
  change (check_syscall (mkInput 63 [fd; buf; count; a3; a4; a5] mem wmem)
            (mkEffect (Z_to_bv 64 0) [] []) m)
    with (check_read (mkInput 63 [fd; buf; count; a3; a4; a5] mem wmem) (fd32 fd)
            buf count (mkEffect (Z_to_bv 64 0) [] []) m).
  rewrite (fd32_lt31 fd Hfd).
  unfold check_read. rewrite Hlk, Hacc. cbn [negb]. cbv beta iota.
  rewrite Hpos. cbv beta iota zeta. rewrite Hfs. rewrite file_read_unguarded.
  rewrite (skipn_all2 c) by (unfold word_to_nat; lia).
  rewrite firstn_nil. cbn [in_wmem len_word length].
  replace (read_bytes_map wmem buf (Z_to_bv 64 (Z.of_nat 0))) with (Some (@nil byte))
    by (vm_compute; reflexivity).
  cbv beta iota. cbn [len_word length].
  apply check_ret_only_ok_iff. auto.
Qed.

(** [close] of it succeeds and removes it. *)
Lemma r1_close : forall mem wmem fd a1 a2 a3 a4 a5 m e,
  (bv_unsigned fd < 2 ^ 31)%Z ->
  fd_lookup (m_fds m) fd = Some e ->
  check_syscall (mkInput 57 [fd; a1; a2; a3; a4; a5] mem wmem)
    (mkEffect (Z_to_bv 64 0) [] []) m
  = CheckOk (with_fds (fd_remove (m_fds m) fd) m) [].
Proof.
  intros mem wmem fd a1 a2 a3 a4 a5 m e Hfd Hlk.
  change (check_syscall (mkInput 57 [fd; a1; a2; a3; a4; a5] mem wmem)
            (mkEffect (Z_to_bv 64 0) [] []) m)
    with (check_close (fd32 fd) (mkEffect (Z_to_bv 64 0) [] []) m).
  rewrite (fd32_lt31 fd Hfd). unfold check_close. rewrite Hlk.
  apply check_ret_only_ok_iff. auto.
Qed.

(* ---- the two images, concretely: "/usr/local/etc/app.conf" ---- *)

Definition r1_etc : Fs.path := map (Z_to_bv 8) [101; 116; 99]%Z.
Definition r1_app : Fs.path := map (Z_to_bv 8) [97; 112; 112; 46; 99; 111; 110; 102]%Z.

(** The pathname's bytes at 8192, for [open_path_mem]. *)
Definition r1_ex_bytes : list Z :=
  [47; 117; 115; 114; 47; 108; 111; 99; 97; 108; 47; 101; 116; 99; 47;
   97; 112; 112; 46; 99; 111; 110; 102]%Z.

(** 12787 bytes: twelve reads of 1024, then one of 499. *)
Definition r1_content : list byte :=
  map (fun n => Z_to_bv 8 (Z.of_nat n mod 256)) (seq 0 12787).

(** N: /usr and /usr/local are folders and /usr/local/etc is absent.
    S: that folder and the file in it as well. *)
Definition r1_n_fs : Fs.Fs :=
  Fs.fs_set (Fs.fs_set (demo_fs []) r1_usr_key EDir) r1_local_key EDir.

Definition r1_s_fs : Fs.Fs :=
  Fs.fs_create_file (Fs.fs_set r1_n_fs (r1_dir_key r1_etc) EDir)
    (r1_path r1_etc r1_app) r1_content.

Definition r1_n_m0 : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input r1_n_fs IEof).
Definition r1_s_m0 : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input r1_s_fs IEof).

(** Both images are valid, and each is an instance of the lemmas above. *)
Example r1_example_images :
  valid_image (demo_input r1_n_fs IEof)
  /\ valid_image (demo_input r1_s_fs IEof)
  /\ r1_name_ok r1_etc /\ r1_name_ok r1_app
  /\ map (Z_to_bv 8) r1_ex_bytes = r1_path r1_etc r1_app
  /\ r1_image_n (m_fs r1_n_m0) r1_etc r1_app
  /\ r1_image_s (m_fs r1_s_m0) r1_etc r1_app 1 r1_content
  /\ length r1_content = 12787%nat.
Proof.
  split; [unfold valid_image; cbn [in_fs in_cwd]; repeat split; valid_image_vm|].
  split; [unfold valid_image; cbn [in_fs in_cwd]; repeat split; valid_image_vm|].
  split; [split; [vm_compute; reflexivity|apply Nat.leb_le; vm_compute; reflexivity]|].
  split; [split; [vm_compute; reflexivity|apply Nat.leb_le; vm_compute; reflexivity]|].
  split; [vm_compute; reflexivity|].
  split.
  { split; [apply Fs.standard_root_presentb_iff; vm_compute; reflexivity|].
    vm_compute. exact I. }
  split.
  { split; [apply Fs.standard_root_presentb_iff; vm_compute; reflexivity|].
    vm_compute. repeat split; reflexivity. }
  vm_compute. reflexivity.
Qed.

(** A sequence of calls, each accepted with no event, from [m]. *)
Fixpoint r1_run (steps : list (SyscallInput * SyscallEffect)) (m : Model)
    : option Model :=
  match steps with
  | [] => Some m
  | (i, e) :: r =>
      match check_syscall i e m with
      | CheckOk m' [] => r1_run r m'
      | _ => None
      end
  end.

(** 128 writable bytes at 4096 for the [struct stat], 1024 at 65536 for
    the reads. *)
Definition r1_wmem (a : word) : option byte :=
  if ((4096 <=? bv_unsigned a) && (bv_unsigned a <? 4224))%Z then Some (Z_to_bv 8 0)
  else if ((65536 <=? bv_unsigned a) && (bv_unsigned a <? 66560))%Z
  then Some (Z_to_bv 8 0) else None.

Definition r1_open_step (fl : Z) (ret : word) : SyscallInput * SyscallEffect :=
  (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 0; 0; 0]
     (open_path_mem r1_ex_bytes) (fun _ => None),
   with_copyins [(8192, 24%nat)] (mkEffect ret [] [])).

Definition r1_fstat_step (bs : list byte) : SyscallInput * SyscallEffect :=
  (mkInput 80 [3; 4096; 0; 0; 0; 0] (fun _ => None) r1_wmem,
   mkEffect 0 [(4096, bs)] []).

(** A regular file's [struct stat] with the asserted members as given:
    the mode, the link count and the size, the page size as
    [st_blksize] ([Uapi.stat_page_blksize]), zero everywhere else. *)
Definition file_stat (mode nlink size : Z) : list byte :=
  Z_to_le_bytes 16 0 ++ Z_to_le_bytes 4 mode ++ Z_to_le_bytes 4 nlink
  ++ Z_to_le_bytes 24 0 ++ Z_to_le_bytes 8 size ++ Z_to_le_bytes 4 page_size
  ++ Z_to_le_bytes 68 0.

Definition r1_read_step (bs : list byte) : SyscallInput * SyscallEffect :=
  (mkInput 63 [3; 65536; 1024; 0; 0; 0] (fun _ => None) r1_wmem,
   match bs with
   | [] => mkEffect 0 [] []
   | _ => mkEffect (len_word bs) [(65536, bs)] []
   end).

Definition r1_close_step : SyscallInput * SyscallEffect :=
  (mkInput 57 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None), mkEffect 0 [] []).

Definition r1_chunk (k : nat) : list byte := firstn 1024 (skipn (1024 * k) r1_content).

(** OVER N: -ENOENT under both words, and descriptor 3 refused. *)
Example r1_absent_folder_is_enoent :
  let open fl ret := let '(i, e) := r1_open_step fl ret in check_syscall i e r1_n_m0 in
  open 0%Z (errno_ret ENOENT) = CheckOk r1_n_m0 []
  /\ open O_LARGEFILE (errno_ret ENOENT) = CheckOk r1_n_m0 []
  /\ open 0%Z 3 = CheckReject
  /\ open O_LARGEFILE 3 = CheckReject.
Proof. vm_compute. split_conj; reflexivity. Qed.

(** OVER S, under both words: open gives 3; fstat is S_IFREG with
    [st_nlink] 1 and [st_size] 12787; twelve reads of 1024 bytes, one of
    499, one of 0; close; and 3 is free again. *)
Example r1_open_fstat_read_close :
  forall fl, In fl [0; O_LARGEFILE]%Z ->
  match r1_run
          ([r1_open_step fl 3; r1_fstat_step (file_stat (S_IFREG + 420) 1 12787)]
           ++ map (fun k => r1_read_step (r1_chunk k)) (seq 0 12)
           ++ [r1_read_step (skipn 12288 r1_content); r1_read_step [];
               r1_close_step])
          r1_s_m0 with
  | Some m => fd_lookup (m_fds m) 3 = None
  | None => False
  end.
Proof. intros fl [<-|[<-|[]]]; vm_compute; reflexivity. Qed.

(** ... and any other type, size or link count is refused. *)
Example r1_fstat_other_type_or_size_rejected :
  match r1_run [r1_open_step O_LARGEFILE 3] r1_s_m0 with
  | Some m =>
      let fstat bs := let '(i, e) := r1_fstat_step bs in check_syscall i e m in
      fstat (file_stat (S_IFCHR + 420) 1 12787) = CheckReject
      /\ fstat (file_stat (S_IFDIR + 420) 1 12787) = CheckReject
      /\ fstat (file_stat (S_IFREG + 420) 1 12786) = CheckReject
      /\ fstat (file_stat (S_IFREG + 420) 1 12788) = CheckReject
      /\ fstat (file_stat (S_IFREG + 420) 1 0) = CheckReject
      /\ fstat (file_stat (S_IFREG + 420) 0 12787) = CheckReject
      /\ fstat (file_stat (S_IFREG + 420) 2 12787) = CheckReject
  | None => False
  end.
Proof. vm_compute. split_conj; reflexivity. Qed.

(* ---- /usr as a link: the walk goes through it ---- *)

(** /usr is a link whose body is "/opt", and /opt/local is a folder
    holding no "etc": the image is in N, read through the link.  Beside
    it the same image with /opt/local/etc/app.conf there, which the
    open reaches through the same link.  A followed link also admits
    -ELOOP ([pick_link]'s nosymfollow refusal, fs/namei.c:1927-1929, and
    a count not reset on a retried walk, :2705-2709), so that errno
    stands beside both answers. *)
Definition r1_opt : Fs.path := map (Z_to_bv 8) [111; 112; 116]%Z.          (* "opt" *)

Definition r1_ln_fs : Fs.Fs :=
  Fs.fs_set
    (Fs.fs_set (Fs.fs_set (demo_fs []) (Fs.path_join [r1_opt]) EDir)
       (Fs.path_join [r1_opt; r1_local]) EDir)
    r1_usr_key (ELink (map (Z_to_bv 8) [47; 111; 112; 116]%Z)).          (* "/opt" *)

Definition r1_ls_fs : Fs.Fs :=
  Fs.fs_create_file
    (Fs.fs_set r1_ln_fs (Fs.path_join [r1_opt; r1_local; r1_etc]) EDir)
    (Fs.path_join [r1_opt; r1_local; r1_etc; r1_app]) r1_content.

Example r1_usr_link_is_walked_through :
  let ln := init_model [] 0 0 demo_sp demo_limit (demo_input r1_ln_fs IEof) in
  let ls := init_model [] 0 0 demo_sp demo_limit (demo_input r1_ls_fs IEof) in
  let open m ret := let '(i, e) := r1_open_step 0%Z ret in check_syscall i e m in
  r1_image_n r1_ln_fs r1_etc r1_app
  /\ open ln (errno_ret ENOENT) = CheckOk ln []
  /\ open ln 3 = CheckReject
  /\ open ln (errno_ret ELOOP) = CheckOk ln []
  (* through the same link the file opens, on its inode *)
  /\ open ls 3 = CheckOk (with_fds (fd_insert (m_fds ls) 3 (FdFile 1 (Z_to_bv 64 0))) ls) []
  /\ open ls (errno_ret ELOOP) = CheckOk ls []
  /\ open ls (errno_ret ENOENT) = CheckReject.
Proof.
  cbv zeta. split.
  - split; [apply Fs.standard_root_presentb_iff; vm_compute; reflexivity|].
    vm_compute. exact I.
  - split_conj; check_eq.
Qed.

(* ---- every reading word, and the calls around the read ----

   [r1_open_absent_enoent] and [r1_open_found_descriptor] are stated for
   the words 0 and O_LARGEFILE, and what their proofs read of the word
   is two facts: its shape is 0 ([Open.open_shape]) and its walk is
   [r1_md] ([Open.open_walk_mode]: no O_CREAT, no O_DIRECTORY, no
   O_NOFOLLOW).  The [_rd] lemmas below are stated over those two
   facts, so every word that has them is an instance; [r1_rd_words_ok]
   gives them for the eight words that add any of O_CLOEXEC,
   O_LARGEFILE and O_NONBLOCK to O_RDONLY, among them
   O_LARGEFILE|O_NONBLOCK, 0x8800 ([r1_rdnb]).  The kernel reads those
   words as it reads O_RDONLY: [build_open_flags] (fs/open.c:1238-1258,
   Linux v6.18.46) strips O_CLOEXEC before it reads the word and
   refuses only bits outside VALID_OPEN_FLAGS, which holds O_NONBLOCK;
   the 64-bit openat sets O_LARGEFILE on every call
   (fs/open.c:1463-1469); and a regular file's read never looks at
   O_NONBLOCK: [iocb_flags] (include/linux/fs.h:3839-3851) maps
   O_APPEND, O_DIRECT, O_DSYNC and __O_SYNC into the read and nothing
   else. *)
Definition r1_rd_words : list Z :=
  [0; O_LARGEFILE; O_NONBLOCK; O_LARGEFILE + O_NONBLOCK; O_CLOEXEC;
   O_CLOEXEC + O_LARGEFILE; O_CLOEXEC + O_NONBLOCK;
   O_CLOEXEC + O_LARGEFILE + O_NONBLOCK]%Z.

Lemma r1_rd_words_ok : forall z, In z r1_rd_words ->
  open_shape (Z_to_bv 64 z) = 0%Z /\ open_walk_mode (Z_to_bv 64 z) = r1_md.
Proof.
  intros z [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; split; vm_compute; reflexivity.
Qed.

(** OVER N, under every word of shape 0 whose walk is [r1_md], on a
    table with a free descriptor: -ENOENT with the process unchanged,
    and every descriptor refused. *)
Lemma r1_open_absent_enoent_rd : forall mem wmem pathp fl a3 a4 a5 m d f,
  read_cstr mem pathp = CstrOk (r1_path d f) ->
  open_shape fl = 0%Z -> open_walk_mode fl = r1_md ->
  r1_name_ok d -> r1_name_ok f -> r1_image_n (m_fs m) d f ->
  fd_lookup (m_fds m) (alloc_fd (m_fds m)) = None ->
  check_syscall (r1_open_in mem wmem pathp fl a3 a4 a5)
    (with_copyins (r1_reads mem pathp) (mkEffect (errno_ret ENOENT) [] [])) m
  = CheckOk m []
  /\ (forall fd, (bv_unsigned fd < 2 ^ 31)%Z ->
      check_syscall (r1_open_in mem wmem pathp fl a3 a4 a5)
        (with_copyins (r1_reads mem pathp) (mkEffect fd [] [])) m
      = CheckReject).
Proof.
  intros mem wmem pathp fl a3 a4 a5 m d f Hpath Hfl0 Hmd Hd Hf Hn Hfree.
  destruct (r1_resolve_absent (m_fs m) (m_cwd m) d f Hn) as (r & lk & ts & Hres & Hr).
  assert (Hrd : forall e,
    Open.check_openat_resolved (r1_path d f) fl e m
    = check_ret_only e (errno_ret ENOENT) m []).
  { intro e. unfold Open.check_openat_resolved. rewrite r1_proc_self_fd, Hmd, Hres.
    cbv beta iota zeta. rewrite Hfl0, Z.eqb_refl. cbv beta iota.
    unfold Open.check_openat_read.
    destruct Hr as [(pre & ->) | (par & nm & ->)]; reflexivity. }
  split.
  - rewrite (r1_open_unfold mem wmem pathp fl a3 a4 a5 m d f _ Hpath Hfl0 Hfree), Hrd.
    apply check_getname_refusals_of_ok.
    apply check_copyins_after_ok_iff. split; [reflexivity|].
    change (clear_copyins (with_copyins (r1_reads mem pathp)
                             (mkEffect (errno_ret ENOENT) [] [])))
      with (mkEffect (errno_ret ENOENT) [] []).
    replace (check_ret_only (mkEffect (errno_ret ENOENT) [] []) (errno_ret ENOENT) m [])
      with (CheckOk m []) by (symmetry; apply check_ret_only_ok_iff; auto).
    reflexivity.
  - intros fd Hfd.
    rewrite (r1_open_unfold mem wmem pathp fl a3 a4 a5 m d f _ Hpath Hfl0 Hfree), Hrd.
    apply r1_getname_fd_reject; [exact Hfd|].
    change (clear_copyins (with_copyins (r1_reads mem pathp) (mkEffect fd [] [])))
      with (mkEffect fd [] []).
    assert (Hne : check_ret_only (mkEffect fd [] []) (errno_ret ENOENT) m [] = CheckReject).
    { cbn [check_ret_only]. destruct (bv_eqb fd (errno_ret ENOENT)) eqn:E; [|reflexivity].
      apply bv_eqb_eq in E. subst fd. exfalso. vm_compute in Hfd. discriminate Hfd. }
    rewrite Hne, Hmd. unfold check_walk_refusals.
    rewrite (r1_walk_reached mem wmem pathp fl a3 a4 a5 m d f Hpath Hd Hf).
    cbv beta iota.
    rewrite (errno_ret_in_fd _ fd (r1_walk_errnos_ok _ _) Hfd).
    unfold check_copyins_after, check_copyins.
    destruct (access_ranges_eqb _ _); reflexivity.
Qed.

(** OVER S, under every word of shape 0 whose walk is [r1_md]: a
    descriptor on the file's inode at offset 0, the lowest free one. *)
Lemma r1_open_found_descriptor_rd : forall mem wmem pathp fl a3 a4 a5 m d f i c,
  read_cstr mem pathp = CstrOk (r1_path d f) ->
  open_shape fl = 0%Z -> open_walk_mode fl = r1_md ->
  r1_name_ok d -> r1_name_ok f -> r1_image_s (m_fs m) d f i c ->
  fd_lookup (m_fds m) (alloc_fd (m_fds m)) = None ->
  check_syscall (r1_open_in mem wmem pathp fl a3 a4 a5)
    (with_copyins (r1_reads mem pathp) (mkEffect (alloc_fd (m_fds m)) [] [])) m
  = CheckOk (with_fds (fd_insert (m_fds m) (alloc_fd (m_fds m))
                         (FdFile i (Z_to_bv 64 0))) m) [].
Proof.
  intros mem wmem pathp fl a3 a4 a5 m d f i c Hpath Hfl0 Hmd Hd Hf Hs Hfree.
  rewrite (r1_open_unfold mem wmem pathp fl a3 a4 a5 m d f _ Hpath Hfl0 Hfree).
  apply check_getname_refusals_of_ok.
  unfold Open.check_openat_resolved.
  rewrite r1_proc_self_fd, Hmd, (r1_resolve_found (m_fs m) (m_cwd m) d f i c Hd Hf Hs).
  cbv beta iota zeta. rewrite Hfl0, Z.eqb_refl. cbv beta iota.
  unfold Open.check_openat_read. cbv beta iota.
  unfold Open.check_open_result_mk, check_open_result, check_new_fd_result.
  change (clear_copyins (with_copyins (r1_reads mem pathp)
                           (mkEffect (alloc_fd (m_fds m)) [] [])))
    with (mkEffect (alloc_fd (m_fds m)) [] []).
  cbv beta iota.
  rewrite (errno_ret_in_alloc_fd openat_errnos (m_fds m) eq_refl), Hfree, bv_eqb_refl.
  apply check_copyins_after_ok_iff. split; reflexivity.
Qed.

(* ---- a folder at the last name ----

   Image D: as S, but "/usr/local/<d>/<f>" names a folder.  A
   read-only open of a folder is a descriptor on it: [do_open]
   (fs/namei.c:3931-3987, Linux v6.18.46) tests O_CREAT and the walk's
   LOOKUP_DIRECTORY, neither set here, and [may_open]
   (fs/namei.c:3527-3545) refuses a folder only for MAY_WRITE or
   MAY_EXEC, which a read-only word does not ask.  Its [struct stat] is
   the folder's: [generic_fillattr] copies the inode's mode, S_IFDIR
   (fs/stat.c:90). *)
Definition r1_image_d (fs : Fs.Fs) (d f : Fs.path) : Prop :=
  Fs.standard_root_present fs
  /\ fs_lookup fs Fs.root = Some EDir
  /\ fs_lookup fs r1_usr_key = Some EDir
  /\ fs_lookup fs r1_local_key = Some EDir
  /\ fs_lookup fs (r1_dir_key d) = Some EDir
  /\ fs_lookup fs (r1_path d f) = Some EDir.

(** Over D the walk reaches the folder, at its own key. *)
Lemma r1_resolve_found_dir : forall fs cwd d f,
  r1_name_ok d -> r1_name_ok f -> r1_image_d fs d f ->
  Fs.resolve r1_md fs cwd (r1_path d f)
  = (Fs.RFound (r1_path d f) EDir, Fs.LastNorm, false).
Proof.
  intros fs cwd d f Hd Hf (_ & Hroot & Hu & Hl & Hdk & Hfk).
  pose proof Hd as [Hd1 Hd2]. pose proof Hf as [Hf1 Hf2].
  unfold Fs.resolve. cbv zeta.
  rewrite (r1_resolve_head r1_md fs cwd d f Hd Hf Hroot).
  rewrite (r1_comps_mid fs r1_md _ _ _ _ Fs.root r1_usr _ EDir);
    [| split; [reflexivity | apply r1_len_ok; now left]
     | reflexivity | reflexivity | reflexivity | reflexivity | exact Hu | reflexivity].
  rewrite (r1_comps_mid fs r1_md _ _ _ _ _ r1_local _ EDir);
    [| split; [reflexivity | apply r1_len_ok; now right]
     | unfold Fs.comps_done; cbn [forallb]; rewrite (Fs.comp_ok_nonempty d Hd1); reflexivity
     | reflexivity | reflexivity | reflexivity | exact Hl | reflexivity].
  rewrite (r1_comps_mid fs r1_md _ _ _ _ _ d _ EDir);
    [| exact Hd
     | unfold Fs.comps_done; cbn [forallb]; rewrite (Fs.comp_ok_nonempty f Hf1); reflexivity
     | reflexivity | reflexivity | reflexivity | exact Hdk | reflexivity].
  change (Fs.child_key (Fs.child_key (Fs.child_key Fs.root r1_usr) r1_local) d)
    with (r1_dir_key d).
  rewrite (r1_comps_last fs r1_md _ _ _ _ _ f _ EDir);
    [| exact Hf | reflexivity | reflexivity | reflexivity | reflexivity
     | rewrite (r1_dir_child d f Hd Hf); exact Hfk | reflexivity].
  rewrite (r1_dir_child d f Hd Hf). reflexivity.
Qed.

(** OVER D, under every word of shape 0 whose walk is [r1_md]: a
    descriptor on the folder, the lowest free one. *)
Lemma r1_open_found_dir_rd : forall mem wmem pathp fl a3 a4 a5 m d f,
  read_cstr mem pathp = CstrOk (r1_path d f) ->
  open_shape fl = 0%Z -> open_walk_mode fl = r1_md ->
  r1_name_ok d -> r1_name_ok f -> r1_image_d (m_fs m) d f ->
  fd_lookup (m_fds m) (alloc_fd (m_fds m)) = None ->
  check_syscall (r1_open_in mem wmem pathp fl a3 a4 a5)
    (with_copyins (r1_reads mem pathp) (mkEffect (alloc_fd (m_fds m)) [] [])) m
  = CheckOk (with_fds (fd_insert (m_fds m) (alloc_fd (m_fds m))
                         (FdDir (r1_path d f))) m) [].
Proof.
  intros mem wmem pathp fl a3 a4 a5 m d f Hpath Hfl0 Hmd Hd Hf Hs Hfree.
  rewrite (r1_open_unfold mem wmem pathp fl a3 a4 a5 m d f _ Hpath Hfl0 Hfree).
  apply check_getname_refusals_of_ok.
  unfold Open.check_openat_resolved.
  rewrite r1_proc_self_fd, Hmd, (r1_resolve_found_dir (m_fs m) (m_cwd m) d f Hd Hf Hs).
  cbv beta iota zeta. rewrite Hfl0, Z.eqb_refl. cbv beta iota.
  unfold Open.check_openat_read. cbv beta iota.
  unfold Open.check_open_result_mk, check_open_result, check_new_fd_result.
  change (clear_copyins (with_copyins (r1_reads mem pathp)
                           (mkEffect (alloc_fd (m_fds m)) [] [])))
    with (mkEffect (alloc_fd (m_fds m)) [] []).
  cbv beta iota.
  rewrite (errno_ret_in_alloc_fd openat_errnos (m_fds m) eq_refl), Hfree, bv_eqb_refl.
  apply check_copyins_after_ok_iff. split; reflexivity.
Qed.

(* ---- the calls, concretely: "/usr/local/etc/app.conf" under 0x8800 ---- *)

(** O_RDONLY|O_LARGEFILE|O_NONBLOCK, 0x8800. *)
Definition r1_rdnb : Z := (O_LARGEFILE + O_NONBLOCK)%Z.

(** One call checked from [m]. *)
Definition r1_call (s : SyscallInput * SyscallEffect) (m : Model) : check_result :=
  check_syscall (fst s) (snd s) m.

(** 128 writable bytes at 4096 for the [struct stat], 4096 at 65536 for
    the reads. *)
Definition r1_wmem4k (a : word) : option byte :=
  if ((4096 <=? bv_unsigned a) && (bv_unsigned a <? 4224))%Z then Some (Z_to_bv 8 0)
  else if ((65536 <=? bv_unsigned a) && (bv_unsigned a <? 69632))%Z
  then Some (Z_to_bv 8 0) else None.

Definition r1_read4k_step (bs : list byte) : SyscallInput * SyscallEffect :=
  (mkInput 63 [3; 65536; 4096; 0; 0; 0] (fun _ => None) r1_wmem4k,
   match bs with
   | [] => mkEffect 0 [] []
   | _ => mkEffect (len_word bs) [(65536, bs)] []
   end).

Definition r1_chunk4k (k : nat) : list byte := firstn 4096 (skipn (4096 * k) r1_content).

(** [fcntl(3, cmd, 0)] answering [ret]. *)
Definition r1_fcntl_step (cmd ret : word) : SyscallInput * SyscallEffect :=
  (mkInput 25 [3; cmd; 0; 0; 0; 0] (fun _ => None) (fun _ => None), mkEffect ret [] []).

(** [fstat(3, 4096)] answering a bare [ret]. *)
Definition r1_fstat_ret_step (ret : word) : SyscallInput * SyscallEffect :=
  (mkInput 80 [3; 4096; 0; 0; 0; 0] (fun _ => None) r1_wmem, mkEffect ret [] []).

(** [newfstatat(3, "", 4096, AT_EMPTY_PATH)] delivering [bs]: the empty
    pathname is its NUL at 8192. *)
Definition r1_fstatat_empty_step (bs : list byte) : SyscallInput * SyscallEffect :=
  (mkInput 79 [3; 8192; 4096; Z_to_bv 64 AT_EMPTY_PATH; 0; 0] (open_path_mem []) r1_wmem,
   with_copyins [(8192, 1%nat)] (mkEffect 0 [(4096, bs)] [])).

(** S with descriptor 3 open on the file at offset 0. *)
Definition r1_s_m3 : Model :=
  with_fds (fd_insert (m_fds r1_s_m0) 3 (FdFile 1 (Z_to_bv 64 0))) r1_s_m0.

(** OVER S, under 0x8800: open gives 3; fstat is S_IFREG with
    [st_nlink] 1 and [st_size] 12787; three reads of 4096 bytes, one of
    499, one of 0; close; and 3 is free again. *)
Example r1_open_fstat_read4k_close :
  match r1_run
          ([r1_open_step r1_rdnb 3; r1_fstat_step (file_stat (S_IFREG + 420) 1 12787)]
           ++ map (fun k => r1_read4k_step (r1_chunk4k k)) (seq 0 3)
           ++ [r1_read4k_step (skipn 12288 r1_content); r1_read4k_step [];
               r1_close_step])
          r1_s_m0 with
  | Some m => fd_lookup (m_fds m) 3 = None
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** A C library's [fstat] that is answered -EBADF goes on to
    [fcntl(fd, F_GETFD)] and then [newfstatat(fd, "", buf,
    AT_EMPTY_PATH)] (musl 1.2.6, src/stat/fstatat.c:81-84), and only
    then.  From descriptor 3 no run reaches either: the [fstat] of it
    answering -EBADF is refused (the second conjunct; [vfs_fstat],
    fs/stat.c:276-281, Linux v6.18.46, answers -EBADF only when the
    table holds no file at the number).  Read on their own, F_GETFD
    answers 0 ([do_fcntl], fs/fcntl.c:465-466: FD_CLOEXEC only when the
    close-on-exec bit is set, and these words carry no O_CLOEXEC), and
    the model's F_GETFD arm admits it; the empty-path newfstatat is the
    descriptor's [vfs_fstat] in Linux ([vfs_fstatat], fs/stat.c:365-373),
    and the model declines it, since it answers an empty pathname only
    against AT_FDCWD ([check_newfstatat_body]). *)
Example r1_fstat_fallback_not_reached :
  r1_call (r1_open_step r1_rdnb 3) r1_s_m0 = CheckOk r1_s_m3 []
  /\ r1_call (r1_fstat_ret_step (errno_ret EBADF)) r1_s_m3 = CheckReject
  /\ r1_call (r1_fcntl_step F_GETFD 0) r1_s_m3 = CheckOk r1_s_m3 []
  /\ r1_call (r1_fstatat_empty_step (file_stat (S_IFREG + 420) 1 12787)) r1_s_m3
     = CheckUnmodeled.
Proof. split_conj; check_eq. Qed.

(** D, concretely: /usr/local/etc/app.conf a folder. *)
Definition r1_d_fs : Fs.Fs :=
  Fs.fs_set (Fs.fs_set r1_n_fs (r1_dir_key r1_etc) EDir) (r1_path r1_etc r1_app) EDir.

Definition r1_d_m0 : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input r1_d_fs IEof).

Definition r1_d_m3 : Model :=
  with_fds (fd_insert (m_fds r1_d_m0) 3 (FdDir (r1_path r1_etc r1_app))) r1_d_m0.

(** A folder's [struct stat]: S_IFDIR|0755, two links, size 0, the page
    size as [st_blksize], zero everywhere else. *)
Definition r1_dir_stat : list byte :=
  Z_to_le_bytes 16 0 ++ Z_to_le_bytes 4 (S_IFDIR + 493) ++ Z_to_le_bytes 4 2
  ++ Z_to_le_bytes 32 0 ++ Z_to_le_bytes 4 4096 ++ Z_to_le_bytes 68 0.

(** The pin an accepted call with no event leaves at [id]; [None] for
    any other verdict. *)
Definition r1_ok_pin (r : check_result) (id : StatId) : option StatPin :=
  match r with
  | CheckOk m' [] => statpin_lookup (m_statpins m') id
  | _ => None
  end.

(** OVER D, under 0x8800: the image is valid and an instance of D; open
    gives 3 on the folder and -EISDIR is refused; fstat of 3 admits the
    folder's [struct stat] and pins it, and refuses a regular file's;
    close answers 0. *)
Example r1_folder_at_the_name :
  valid_image (demo_input r1_d_fs IEof)
  /\ r1_image_d r1_d_fs r1_etc r1_app
  /\ r1_call (r1_open_step r1_rdnb 3) r1_d_m0 = CheckOk r1_d_m3 []
  /\ r1_call (r1_open_step r1_rdnb (errno_ret EISDIR)) r1_d_m0 = CheckReject
  /\ r1_ok_pin (r1_call (r1_fstat_step r1_dir_stat) r1_d_m3) (IdDir (r1_path r1_etc r1_app))
     = Some (mkStatPin r1_dir_stat (Some DirCounting) false)
  /\ r1_call (r1_fstat_step (file_stat (S_IFREG + 420) 1 0)) r1_d_m3 = CheckReject
  /\ r1_call r1_close_step r1_d_m3
     = CheckOk (with_fds (fd_remove (m_fds r1_d_m3) 3) r1_d_m3) [].
Proof.
  split; [unfold valid_image; cbn [in_fs in_cwd]; repeat split; valid_image_vm|].
  split.
  { split; [apply Fs.standard_root_presentb_iff; vm_compute; reflexivity|].
    vm_compute. repeat split; reflexivity. }
  split_conj; check_eq.
Qed.

(* ---- a file on the way, and a link to the null device at the last name ----

   Image F: /usr/local/etc is a regular file.  The walk meets it with
   "app.conf" still to go and stops: [link_path_walk] answers -ENOTDIR
   for a component that cannot be looked up in (fs/namei.c:2529-2534,
   Linux v6.18.46).

   Image L: /usr/local/etc is a folder and app.conf in it a symbolic
   link whose body is "/dev/null", the standard root's null device.
   The open follows the last link: [step_into] (fs/namei.c:1984-2021,
   Linux v6.18.46) hands it to [pick_link] under the LOOKUP_FOLLOW every
   word here keeps.  It then opens the device: [may_open] lets a
   character device through for a read (fs/namei.c:3546-3556).  Its
   [struct stat] is the device's,
   S_IFCHR with [st_rdev] 1:3 ([generic_fillattr], fs/stat.c:90 and
   :94; [cp_new_stat], fs/stat.c:494).

   A FIFO at the last name has no image here: [Fs.Entry] holds a
   regular file, a folder, the two character devices and a link, and
   nothing else, so no launch image the model accepts carries one. *)
Definition r1_f_fs : Fs.Fs :=
  Fs.fs_create_file r1_n_fs (r1_dir_key r1_etc) [].

Definition r1_f_m0 : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input r1_f_fs IEof).

(** OVER F, under 0x8800: -ENOTDIR with the process unchanged; neither
    descriptor 3 nor -ENOENT is admitted. *)
Example r1_file_on_the_way_is_enotdir :
  valid_image (demo_input r1_f_fs IEof)
  /\ r1_call (r1_open_step r1_rdnb (errno_ret ENOTDIR)) r1_f_m0 = CheckOk r1_f_m0 []
  /\ r1_call (r1_open_step r1_rdnb 3) r1_f_m0 = CheckReject
  /\ r1_call (r1_open_step r1_rdnb (errno_ret ENOENT)) r1_f_m0 = CheckReject.
Proof.
  split; [unfold valid_image; cbn [in_fs in_cwd]; repeat split; valid_image_vm|].
  split_conj; check_eq.
Qed.

Definition r1_l_fs : Fs.Fs :=
  Fs.fs_set (Fs.fs_set r1_n_fs (r1_dir_key r1_etc) EDir) (r1_path r1_etc r1_app)
    (ELink Fs.devnull_key).

Definition r1_l_m0 : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input r1_l_fs IEof).

Definition r1_l_m3 : Model :=
  with_fds (fd_insert (m_fds r1_l_m0) 3 (FdDevNull true false)) r1_l_m0.

(** A character device's [struct stat]: the mode, one link, the device
    number, the page size as [st_blksize], zero everywhere else. *)
Definition r1_chr_stat (mode rdev : Z) : list byte :=
  Z_to_le_bytes 16 0 ++ Z_to_le_bytes 4 mode ++ Z_to_le_bytes 4 1 ++ Z_to_le_bytes 8 0
  ++ Z_to_le_bytes 8 rdev ++ Z_to_le_bytes 16 0 ++ Z_to_le_bytes 4 4096
  ++ Z_to_le_bytes 68 0.

(** OVER L, under 0x8800: open gives 3 on the null device, read-only;
    fstat of 3 admits the null device's [struct stat] and pins it, and
    refuses a regular file's; close answers 0. *)
Example r1_link_to_the_null_device :
  valid_image (demo_input r1_l_fs IEof)
  /\ r1_call (r1_open_step r1_rdnb 3) r1_l_m0 = CheckOk r1_l_m3 []
  /\ r1_ok_pin (r1_call (r1_fstat_step (r1_chr_stat (S_IFCHR + 438) DEVNULL_RDEV)) r1_l_m3)
       (IdDev devnull_path)
     = Some (mkStatPin (r1_chr_stat (S_IFCHR + 438) DEVNULL_RDEV) None false)
  /\ r1_call (r1_fstat_step (file_stat (S_IFREG + 420) 1 0)) r1_l_m3 = CheckReject
  /\ r1_call r1_close_step r1_l_m3
     = CheckOk (with_fds (fd_remove (m_fds r1_l_m3) 3) r1_l_m3) [].
Proof.
  split; [unfold valid_image; cbn [in_fs in_cwd]; repeat split; valid_image_vm|].
  split_conj; check_eq.
Qed.

(* ================================ two files created in opposite orders

   A run that creates "f" and then "g", writing one byte into each, and a
   run that creates them the other way round, leave Linux in the same
   state: the same two names, each a file of one link holding its byte.
   What differs is the inode numbers: the file created first gets the
   lower one ([__shmem_get_inode], mm/shmem.c:3084 and :3094, takes it
   from [shmem_reserve_inode], which draws the next number of a counter,
   as [get_next_ino] does, fs/inode.c:1105-1125), and [st_ino] is the
   environment's, not part of the image.  The model
   numbers its inodes the same way ([Fs.fs_fresh_ino]), so the two images
   the runs leave are NOT equal; the image an exit or a kill reports is
   [Fs.fs_observe] of it ([Run.sstep_exit], [Run.sstep_killed]), and THAT
   is equal.  Without the observation two runs Linux cannot tell apart
   would end in different [ExitEv]s. *)
Definition oo_create (name : Z) (fd : word) : SyscallInput * SyscallEffect :=
  (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 wr_create_flags; 420; 0; 0]
     (open_path_mem [name]) (fun _ => None),
   with_copyins [(8192, 2%nat)] (mkEffect fd [] [])).

Definition oo_write (fd : word) (b : Z) : SyscallInput * SyscallEffect :=
  (mkInput 64 [fd; 4096; 1; 0; 0; 0]
     (fun a => if bv_eqb a 4096 then Some (Z_to_bv 8 b) else None) (fun _ => None),
   with_copyins [(4096, 1%nat)] (mkEffect 1 [] [])).

(** "f" (102) gets "x" (120) and "g" (103) gets "y" (121), in both runs. *)
Definition oo_f_then_g : list (SyscallInput * SyscallEffect) :=
  [oo_create 102 3; oo_write 3 120; oo_create 103 4; oo_write 4 121].
Definition oo_g_then_f : list (SyscallInput * SyscallEffect) :=
  [oo_create 103 3; oo_write 3 121; oo_create 102 4; oo_write 4 120].

Example opposite_order_creation_observes_one_image :
  match r1_run oo_f_then_g ns_open_empty, r1_run oo_g_then_f ns_open_empty with
  | Some m1, Some m2 =>
      Fs.fs_observe (m_fs m1) = Fs.fs_observe (m_fs m2)
      (* ...the same two files, with their bytes *)
      /\ file_at (m_fs m1) (wk [102]) = Some [Z_to_bv 8 120]
      /\ file_at (m_fs m1) (wk [103]) = Some [Z_to_bv 8 121]
      /\ file_at (m_fs m2) (wk [102]) = Some [Z_to_bv 8 120]
      /\ file_at (m_fs m2) (wk [103]) = Some [Z_to_bv 8 121]
      (* ...under different inode numbers, so the raw images differ *)
      /\ Fs.fs_lookup (m_fs m1) (wk [102]) = Some (EFile 1)
      /\ Fs.fs_lookup (m_fs m2) (wk [102]) = Some (EFile 2)
      /\ m_fs m1 <> m_fs m2
  | _, _ => False
  end.
Proof.
  vm_compute. split_conj; try reflexivity. intros H. discriminate H.
Qed.

(* ================================ symbolic links at the open arm

   Linux v6.18.46.  [open] follows its last link unless O_NOFOLLOW
   ([build_open_flags], fs/open.c:1339-1340), and O_CREAT|O_EXCL sets
   O_NOFOLLOW itself (:1329-1334).  A last link that is not followed is
   [may_open]'s -ELOOP (fs/namei.c:3538-3539), unless O_DIRECTORY asked
   for a folder first ([path_lookupat]'s -ENOTDIR, :2685-2687); a
   trailing separator forces the follow whatever the flags
   ([lookup_last], :2647-2652).  O_CREAT through a link to nothing
   creates the name the body ends in ([lookup_open], :3787-3799), and
   O_CREAT|O_EXCL on a link is -EEXIST ([do_open], :3949-3950).  Every
   follow also admits -ELOOP ([pick_link], :1927-1929). *)

(** "f" a file (inode 1), "d" a folder, "l" -> "f", "ld" -> "d",
    "dang" -> "new". *)
Definition ln_open_m0 : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input (demo_fs [([102], SFile [104; 105]); ([100], SDir);
                          ([108], SLink [102]); ([108; 100], SLink [100]);
                          ([100; 97; 110; 103], SLink [110; 101; 119])]) IEof).

Definition ln_open (bs : list Z) (fl : Z) (eff : SyscallEffect) : check_result :=
  check_syscall
    (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0] (open_path_mem bs)
       (fun _ => None))
    (with_copyins [(8192, S (length bs))] eff) ln_open_m0.

(** A LINK ON THE PATH IS FOLLOWED: "l" opens the file, on its inode,
    and -ELOOP stands beside the descriptor. *)
Example openat_follows_a_link :
  ln_open [108]%Z 0%Z (mkEffect 3 [] [])
  = CheckOk (with_fds (fd_insert (m_fds ln_open_m0) 3 (FdFile 1 (Z_to_bv 64 0)))
               ln_open_m0) []
  /\ ln_open [108]%Z 0%Z (mkEffect (errno_ret ELOOP) [] []) = CheckOk ln_open_m0 []
  /\ ln_open [108]%Z 0%Z (mkEffect (errno_ret ENOENT) [] []) = CheckReject
  (* a file reached by no link admits no -ELOOP *)
  /\ ln_open [102]%Z 0%Z (mkEffect (errno_ret ELOOP) [] []) = CheckReject.
Proof. split_conj; check_eq. Qed.

(** O_NOFOLLOW ON A LINK IS -ELOOP, and with O_DIRECTORY it is -ENOTDIR,
    where -ELOOP is refused: nothing was followed.  A trailing separator
    still forces the follow: "l/" under O_NOFOLLOW is the file's
    -ENOTDIR. *)
Example openat_nofollow_on_a_link :
  ln_open [108]%Z O_NOFOLLOW (mkEffect (errno_ret ELOOP) [] []) = CheckOk ln_open_m0 []
  /\ ln_open [108]%Z O_NOFOLLOW (mkEffect 3 [] []) = CheckReject
  /\ ln_open [108]%Z (O_NOFOLLOW + O_DIRECTORY)%Z (mkEffect (errno_ret ENOTDIR) [] [])
     = CheckOk ln_open_m0 []
  /\ ln_open [108]%Z (O_NOFOLLOW + O_DIRECTORY)%Z (mkEffect (errno_ret ELOOP) [] [])
     = CheckReject
  /\ ln_open [108; 47]%Z O_NOFOLLOW (mkEffect (errno_ret ENOTDIR) [] [])
     = CheckOk ln_open_m0 []
  /\ ln_open [108; 47]%Z O_NOFOLLOW (mkEffect (errno_ret ELOOP) [] []) = CheckOk ln_open_m0 []
  (* "ld/" under O_NOFOLLOW is the folder *)
  /\ ln_open [108; 100; 47]%Z O_NOFOLLOW (mkEffect 3 [] [])
     = CheckOk (with_fds (fd_insert (m_fds ln_open_m0) 3 (FdDir (wk [100])))
                  ln_open_m0) [].
Proof. split_conj; check_eq. Qed.

(** O_CREAT THROUGH A LINK TO NOTHING CREATES THE TARGET: "dang" makes
    "new" in the folder holding the link, a fresh inode 2; the link
    stays.  O_CREAT|O_EXCL on the same link, and on a link to a file,
    is -EEXIST, and creates nothing. *)
Example openat_creat_through_a_dangling_link :
  ln_open [100; 97; 110; 103]%Z wr_create_flags (mkEffect 3 [] [])
  = CheckOk (with_fds (fd_insert (m_fds ln_open_m0) 3 (FdFileW 2 (Z_to_bv 64 0)))
               (with_fs (Fs.fs_create_file (m_fs ln_open_m0) (wk [110; 101; 119]) [])
                  ln_open_m0)) []
  /\ ln_open [100; 97; 110; 103]%Z wr_create_flags (mkEffect (errno_ret ELOOP) [] [])
     = CheckOk ln_open_m0 []
  /\ ln_open [100; 97; 110; 103]%Z excl_create_flags (mkEffect (errno_ret EEXIST) [] [])
     = CheckOk ln_open_m0 []
  /\ ln_open [100; 97; 110; 103]%Z excl_create_flags (mkEffect 3 [] []) = CheckReject
  /\ ln_open [108]%Z excl_create_flags (mkEffect (errno_ret EEXIST) [] [])
     = CheckOk ln_open_m0 []
  /\ ln_open [108]%Z excl_create_flags (mkEffect (errno_ret ELOOP) [] []) = CheckReject.
Proof. split_conj; check_eq. Qed.

(* ===================================== a table with no free descriptor

   Linux v6.18.46.  [do_sys_openat2] takes the descriptor with
   [get_unused_fd_flags] after [getname] and before [do_filp_open]
   (fs/open.c:1431-1437), and [alloc_fd] answers -EMFILE when the
   lowest free descriptor is at or above the soft RLIMIT_NOFILE, before
   it allocates anything (fs/file.c:591-593).  So on a table with no
   free slot below the limit, every name [getname] hands on is -EMFILE,
   whatever the walk would have answered: the dirfd is read in
   [path_init] and the walk runs in [path_openat], both inside
   [do_filp_open].  [getname]'s own answers come first, and its -ENOMEM
   stands beside the -EMFILE. *)

(** Every descriptor 0 to 4096 held, each on the stdin channel: the
    table [File.lowest_fd] has no slot in ([File.lowest_fd_none]), under
    a soft RLIMIT_NOFILE of [n].  At [n] = 4097 the run launched with
    that limit and opened 4094 descriptors, and the lowest free one, 4097,
    is at the limit. *)
Definition full_fds : list (word * FdEntry) :=
  map (fun k => (Z_to_bv 64 (Z.of_nat k), FdChannel (Z_to_bv 64 0))) (seq 0 4097).

Definition full_table (n : Z) (m : Model) : Model :=
  with_nofile (Z_to_bv 64 n) (with_fds full_fds m).

(** THE ANSWER IS -EMFILE, BEFORE THE WALK AND EVERY PATH ERROR: for a
    missing name (not its -ENOENT), for a walk that follows the link "l"
    (not the walk's -ELOOP or -EACCES), for a write open of the existing
    file "f" (not -ETXTBSY, and "f" keeps its bytes), for
    "/proc/self/fd/3" (a channel there, which the reopen arm declines)
    and under a dirfd the model declines; never a descriptor, and with
    the pathname's copy-in, which [getname] made first.  [getname]'s
    own answers stay first: the empty name is -ENOENT, and its -ENOMEM,
    which copied nothing, stands beside the -EMFILE.  Under a soft limit
    of 4098 Linux may hand out descriptor 4097, which no spec here
    returns, and the call declines. *)
Example openat_with_no_free_descriptor_answers_emfile_first :
  let call (fl : Z) (p : list Z) (r : word) (m : Model) :=
        check_syscall
          (mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 fl; 420; 0; 0]
             (open_path_mem p) (fun _ => None))
          (with_copyins [(8192, S (length p))] (mkEffect r [] [])) m in
  let mf := full_table 4097 ns_open_f in
  let ml := full_table 4097 ln_open_m0 in
  let procfd3 := [47; 112; 114; 111; 99; 47; 115; 101; 108; 102; 47; 102; 100; 47; 51]%Z in
  lowest_fd_none (m_fds mf) = true
  /\ call 0%Z [103]%Z (errno_ret EMFILE) mf = CheckOk mf []
  /\ call 0%Z [103]%Z (errno_ret ENOENT) mf = CheckReject
  /\ call 0%Z [108]%Z (errno_ret EMFILE) ml = CheckOk ml []
  /\ call 0%Z [108]%Z (errno_ret ELOOP) ml = CheckReject
  /\ call 0%Z [108]%Z (errno_ret EACCES) ml = CheckReject
  /\ call wr_create_flags [102]%Z (errno_ret EMFILE) mf = CheckOk mf []
  /\ call wr_create_flags [102]%Z (errno_ret ETXTBSY) mf = CheckReject
  /\ call 0%Z [102]%Z 4097 mf = CheckReject
  /\ call 0%Z procfd3 (errno_ret EMFILE) mf = CheckOk mf []
  /\ check_syscall
       (mkInput 56 [5; 8192; 0; 420; 0; 0] (open_path_mem [102%Z]) (fun _ => None))
       (with_copyins [(8192, 2%nat)] (mkEffect (errno_ret EMFILE) [] [])) mf
     = CheckOk mf []
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 420; 0; 0] (open_path_mem [103%Z]) (fun _ => None))
       (mkEffect (errno_ret EMFILE) [] []) mf
     = CheckReject
  /\ call 0%Z [] (errno_ret ENOENT) mf = CheckOk mf []
  /\ call 0%Z [] (errno_ret EMFILE) mf = CheckReject
  /\ check_syscall
       (mkInput 56 [AT_FDCWD; 8192; 0; 420; 0; 0] (open_path_mem [103%Z]) (fun _ => None))
       (mkEffect (errno_ret ENOMEM) [] []) mf
     = CheckOk mf []
  /\ call 0%Z [103]%Z (errno_ret EMFILE) (full_table 4098 ns_open_f) = CheckUnmodeled.
Proof. vm_compute; split_conj; check_eq. Qed.
