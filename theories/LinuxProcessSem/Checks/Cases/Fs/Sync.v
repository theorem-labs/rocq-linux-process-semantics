(** * LinuxProcessSem.Checks.Cases.Fs.Sync — worked examples over fsync (82), fdatasync (83)

    Mirrors [Sys/Fs/Sync.v], which answers to Linux [fs/sync.c]: this
    file holds the worked examples for the syscalls defined there, and
    no others.

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
  Prelude Fs.ReadWrite.

Definition fsync_model : Model :=
  mkModel
    [ (0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
      (3, FdFile 1 7); (4, FdFileW 2 9); (5, FdDir Fs.default_cwd) ]
    (mkVmMaps [] [] 0 0 demo_limit) IEof
    (raw_files [([102], [120]); ([103], [121])]) None None None.

(** THE CHANNEL ARM ON fd 0.

    The second conjunct is what makes the first non-vacuous: a kernel
    claiming SUCCESS is rejected, so this pins -EINVAL rather than
    merely admitting it. *)

Example fsync_on_a_channel_is_einval :
  check_syscall (mkInput 82 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) fsync_model
  = CheckOk fsync_model []
  /\ check_syscall (mkInput 82 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fsync_model
     = CheckReject
  (* and [fdatasync] answers fd 0 identically *)
  /\ check_syscall (mkInput 83 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) fsync_model
     = CheckOk fsync_model []
  /\ check_syscall (mkInput 83 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fsync_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** One end of an AF_UNIX stream pair: empty, blocking, open both ways,
    with the default 212992-byte buffers and its reset state still
    undecided -- the end [Checks/Cases/Fs/File.v]'s [dup_pair_end] is. *)
Definition fsync_stream_end : StreamEnd :=
  mkStreamEnd [] false 212992%Z 212992%Z false false RsUnknown.

(** [fsync_model] with three more kinds: side [false] of AF_UNIX stream
    pair 0 at fd 12, an unconnected AF_UNIX (1) datagram socket at fd 13
    and an eventfd holding 0 at fd 14. *)
Definition fsync_sock_kinds_model : Model :=
  mkModel
    [ (0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
      (3, FdFile 1 7); (4, FdFileW 2 9); (5, FdDir Fs.default_cwd);
      (12, FdStream 0 false fsync_stream_end); (13, FdDgram 1%Z);
      (14, FdEventfd (mkEventfdCtx 0%Z false false)) ]
    (mkVmMaps [] [] 0 0 demo_limit) IEof
    (raw_files [([102], [120]); ([103], [121])]) None None None.

(** THE SOCKET-TABLE AND EVENTFD ARMS, on fds 12 to 14.

    [vfs_fsync_range] (fs/sync.c:183-184, Linux v6.18.46) answers
    -EINVAL when the file's table has no [.fsync], before it reads
    [datasync], so the errno comes from the table and not from the
    object's state.  In each example the second conjunct refuses the 0
    a table with an [.fsync] would give, which makes the first a pin
    rather than an admission.

    A stream-pair end: [__sys_socketpair] (net/socket.c:1769, Linux
    v6.18.46) gives each end the file [sock_alloc_file] makes (:1835,
    :1842), with [socket_file_ops] (:483-485), and that table
    (:156-173) has no [.fsync]. *)
Example fsync_on_a_stream_pair_end_is_einval :
  check_syscall (mkInput 82 [12; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) fsync_sock_kinds_model
  = CheckOk fsync_sock_kinds_model []
  /\ check_syscall (mkInput 82 [12; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fsync_sock_kinds_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** A datagram socket, by the same table: [__sys_socket]
    (net/socket.c:1743-1758, Linux v6.18.46) hands the new socket to
    [sock_map_fd] (:1757), whose file is the one [sock_alloc_file] makes
    (:513), with [socket_file_ops] (:483-485).  The family plays no
    part: every socket's file gets that one table. *)
Example fsync_on_a_datagram_socket_is_einval :
  check_syscall (mkInput 82 [13; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) fsync_sock_kinds_model
  = CheckOk fsync_sock_kinds_model []
  /\ check_syscall (mkInput 82 [13; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fsync_sock_kinds_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** An eventfd: [do_eventfd] (fs/eventfd.c:379-421, Linux v6.18.46) makes
    its file over [eventfd_fops] (:409-410), and that table (:302-311)
    lists [.show_fdinfo], [.release], [.poll], [.read_iter], [.write] and
    [.llseek] and no [.fsync].  [anon_inode_getfile_fmode]
    (fs/anon_inodes.c:226-232, Linux v6.18.46) installs the table it is
    given unchanged (:166-167). *)
Example fsync_on_an_eventfd_is_einval :
  check_syscall (mkInput 82 [14; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) fsync_sock_kinds_model
  = CheckOk fsync_sock_kinds_model []
  /\ check_syscall (mkInput 82 [14; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fsync_sock_kinds_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** THE fd32 TRUNCATION ALIASES ONTO fd 0.

    What is worth pinning is that truncation ALIASES rather than
    REJECTS — a model comparing the full 64-bit register would have
    found no such fd and answered -EBADF.  The third conjunct rules that
    out.

    The first conjunct is an equation between two checker calls, so on
    its own it would hold vacuously if BOTH sides were [CheckReject].
    The second names the shared value outright, which is what makes the
    first say what it reads as saying. *)

Example fsync_fd_truncates_to_32_bits :
  check_syscall (mkInput 82 [Z_to_bv 64 (2 ^ 32); 0; 0; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) fsync_model
  = check_syscall (mkInput 82 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
      (mkEffect (errno_ret EINVAL) [] []) fsync_model
  (* ...and that shared value is an ACCEPTANCE, not a shared rejection *)
  /\ check_syscall (mkInput 82 [Z_to_bv 64 (2 ^ 32); 0; 0; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) fsync_model
     = CheckOk fsync_model []
  /\ check_syscall (mkInput 82 [Z_to_bv 64 (2 ^ 32); 0; 0; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) fsync_model
     = CheckReject.
Proof. split_conj; check_eq. Qed.

(** SUCCESS IS INERT.  ADMISSION REASON: it pins model-internal state
    that no observation reveals.

    A real run sees only the 0.  That the fd's offset (7 and 9 here) and
    the file's contents came back UNCHANGED, and that no event was
    emitted, is a statement about the model's own state, and the
    equalities below are the whole of it: the returned model is the SAME
    model, and the event list is empty. *)

Example fsync_success_is_inert_on_every_file_kind :
  check_syscall (mkInput 82 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) fsync_model = CheckOk fsync_model []
  /\ check_syscall (mkInput 82 [4; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fsync_model = CheckOk fsync_model []
  /\ check_syscall (mkInput 82 [5; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fsync_model = CheckOk fsync_model []
  /\ check_syscall (mkInput 83 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fsync_model = CheckOk fsync_model [].
Proof. split_conj; check_eq. Qed.


(** "f" = "x" (byte 120), inode 1, open O_RDWR at fd 3, and the same file
    open in APPEND MODE at fd 3, both at offset 0: the two file kinds
    [fsync_model] does not hold. *)
Definition fsync_rdwr_model : Model :=
  mkModel [(3, FdFileRW 1 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    (raw_files [([102], [120])]) None None None.

Definition fsync_append_model : Model :=
  mkModel [(3, FdFileA 1 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    (raw_files [([102], [120])]) None None None.

(** ...AND ON THE TWO FILE KINDS [fsync_model] DOES NOT HOLD.  ADMISSION
    REASON: as above, it pins model-internal state that no observation
    reveals.

    An append fd and a read-write fd answer 0 as the read-only and
    write-only ones do: [vfs_fsync_range] (fs/sync.c:183-184, Linux
    v6.18.46) tests [f_op->fsync] and reads neither the access mode nor
    O_APPEND.  What a probe cannot see is that the model comes back the
    SAME model -- the offset at 0, the file untouched, no event -- which
    is the first conjunct of each example.  The second refuses the
    -EINVAL of a kind with no [.fsync]. *)
Example fsync_append_fd_is_zero :
  check_syscall (mkInput 82 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) fsync_append_model = CheckOk fsync_append_model []
  /\ check_syscall (mkInput 82 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) fsync_append_model = CheckReject.
Proof. split_conj; check_eq. Qed.

Example fsync_rdwr_fd_is_zero :
  check_syscall (mkInput 82 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) fsync_rdwr_model = CheckOk fsync_rdwr_model []
  /\ check_syscall (mkInput 82 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) fsync_rdwr_model = CheckReject.
Proof. split_conj; check_eq. Qed.

(* -------------------------------------------------------------------------
   prlimit64 (261): the pin, and what no real run can show.

   Nearly all of this spec's fail-closed surface IS reachable from a
   real run — it just calls prlimit64 with a nonzero pid or an unmodeled
   resource id.  Three things a run cannot show are left, and they are
   the whole of this group:

   - THE ENVIRONMENT CANNOT PRODUCE a kernel reporting soft > hard.
     Linux maintains soft <= hard on every path that writes a limit.
     So [Kernel.Sys.rlim64_wf]'s ordering conjunct is stated here or
     nowhere.
   - Nor can it produce a later read delivering a DIFFERENT well-formed
     pair.
   - The rest pin MODEL-INTERNAL STATE — the recorded limit, and that a
     set REPLACES it.  A run reveals only the pair it happened to
     inherit, never that the model is holding it, so the claim is pinned
     here, where the recorded pair is chosen rather than inherited.
   ------------------------------------------------------------------------- *)

(** A [struct rlimit64] with single-byte soft and hard limits. *)
