(** * LinuxProcessSem.Checks.Cases.Fs.Readdir — worked examples over getdents64 (61)

    Mirrors [Sys/Fs/Readdir.v], which answers to Linux [fs/readdir.c]:
    this file holds the worked examples for the syscalls defined there,
    and no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary.

    ALMOST NOTHING ABOUT THIS SYSCALL BELONGS HERE, and that is the
    point of saying so: every arm of [Fs.Readdir.getdents64_spec] is
    reachable from a real run, and so is the decline, by giving a
    directory fd a buffer with room in it.  What is left is the two
    things a real run reveals nothing about.

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

(** fd 3 is an O_RDONLY file parked at offset 7, fd 4 an O_WRONLY one at
    offset 9, fd 5 the directory.  The two offsets and the two file
    bodies are what the inertness check below has to find unchanged. *)
Definition getdents64_model : Model :=
  mkModel
    [ (0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
      (3, FdFile 1 7); (4, FdFileW 2 9); (5, FdDir Fs.default_cwd) ]
    (mkVmMaps [] [] 0 0 demo_limit) IEof
    (raw_files [([102], [120]); ([103], [121])]) None None None.

(** One getdents64 call, with [buf] parked at a mapped-looking address
    that no arm below reads: the spec does not take the pointer, so
    every answer here is settled without it. *)
Definition getdents64_in (fd count : Z) : SyscallInput :=
  mkInput 61 [Z_to_bv 64 fd; Z_to_bv 64 4096; Z_to_bv 64 count; 0; 0; 0]
    (fun _ => None) (fun _ => None).

(** WHERE THE BUFFER-SIZE EDGE IS.  ADMISSION REASON: it pins a model
    constant that no observation of a real execution reveals.

    A real run learns that the kernel said -EINVAL at some count and
    listed the directory at some larger one; it never learns where the
    MODEL puts the boundary between them, and a spec whose edge sat one
    byte either side would pass every run that lands clear of it.  [Fs.Readdir.dirent64_min_reclen] is 24 — the aligned size of a
    one-byte name's record — so 23 is answered and 24 is declined, and
    naming the two together is the whole of the claim.

    The third and fourth conjuncts are what make the first two say what
    they read as saying: without them, "23 is -EINVAL" would hold just
    as well of a checker that accepted every return at that count, and
    "24 declines" of one that declined every count. *)
Example getdents64_edge_is_the_minimum_reclen :
  check_syscall (getdents64_in 5 23) (mkEffect (errno_ret EINVAL) [] [])
    getdents64_model = CheckOk getdents64_model []
  /\ check_syscall (getdents64_in 5 24) (mkEffect (errno_ret EINVAL) [] [])
       getdents64_model = CheckUnmodeled
  (* ...and 23 admits that errno rather than any return *)
  /\ check_syscall (getdents64_in 5 23) (mkEffect (Z_to_bv 64 0) [] [])
       getdents64_model = CheckReject
  (* ...while 24 declines the very return 23 would have accepted, so the
     decline is the COUNT's doing and not the effect's *)
  /\ check_syscall (getdents64_in 5 24) (mkEffect (Z_to_bv 64 24) [] [])
       getdents64_model = CheckUnmodeled.
Proof. split_conj; check_eq. Qed.

(** THE SAME EDGE, ON THE OTHER SIDE OF THE SIGN.  ADMISSION REASON: as
    above — it is where the model reads [count] as
    [struct dir_context]'s [int] rather than as the [unsigned int] the
    prototype declares, and no single run separates the two readings.

    2^31 - 1 is the largest positive [ctx->count], and has room; 2^31 is
    the smallest negative one, and has none.  A model comparing the
    unsigned low half would have declined BOTH, so the second conjunct
    is the one that carries the reading, and the fourth rules out the
    other mistake — that the model simply accepts -EINVAL everywhere
    above the boundary. *)
Example getdents64_count_is_a_signed_int :
  check_syscall (getdents64_in 5 (2 ^ 31 - 1)) (mkEffect (errno_ret EINVAL) [] [])
    getdents64_model = CheckUnmodeled
  /\ check_syscall (getdents64_in 5 (2 ^ 31)) (mkEffect (errno_ret EINVAL) [] [])
       getdents64_model = CheckOk getdents64_model []
  /\ check_syscall (getdents64_in 5 (2 ^ 32 - 1)) (mkEffect (errno_ret EINVAL) [] [])
       getdents64_model = CheckOk getdents64_model []
  (* the high half is discarded first, so 2^32 | 24 has room again *)
  /\ check_syscall (getdents64_in 5 (2 ^ 32 + 24)) (mkEffect (errno_ret EINVAL) [] [])
       getdents64_model = CheckUnmodeled.
Proof. split_conj; check_eq. Qed.

(** EVERY ANSWER IS INERT.  ADMISSION REASON: it pins model-internal
    state that no observation reveals.

    A real run sees only the errno.  That the fds' offsets (7 and 9 here),
    the file bodies and the fd table itself came back UNCHANGED, and
    that no event was emitted, is a statement about the model's own
    state, and the equalities below are the whole of it: the returned
    model is the SAME model, and the event list is empty.

    This is not the same claim as "the effect carries no writes".
    That one is about what the checker refuses to accept; this one is
    about what it DOES with an answer it accepts. *)
Example getdents64_answers_are_inert :
  check_syscall (getdents64_in 5 0) (mkEffect (errno_ret EINVAL) [] [])
    getdents64_model = CheckOk getdents64_model []
  /\ check_syscall (getdents64_in 3 0) (mkEffect (errno_ret ENOTDIR) [] [])
       getdents64_model = CheckOk getdents64_model []
  /\ check_syscall (getdents64_in 4 0) (mkEffect (errno_ret ENOTDIR) [] [])
       getdents64_model = CheckOk getdents64_model []
  /\ check_syscall (getdents64_in 0 0) (mkEffect (errno_ret ENOTDIR) [] [])
       getdents64_model = CheckOk getdents64_model []
  /\ check_syscall (getdents64_in 99 0) (mkEffect (errno_ret EBADF) [] [])
       getdents64_model = CheckOk getdents64_model []
  (* and the injected failure, which leaves the model alone too *)
  /\ check_syscall (getdents64_in 5 0) (mkEffect (errno_ret ENOENT) [] [])
       getdents64_model = CheckOk getdents64_model [].
Proof. split_conj; check_eq. Qed.

(** "f" = "x" (byte 120), inode 1, open O_RDWR at fd 3, and the same file
    open in APPEND MODE at fd 3, both at offset 0: the two file kinds
    [getdents64_model] does not hold. *)
Definition getdents64_rdwr_model : Model :=
  mkModel [(3, FdFileRW 1 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    (raw_files [([102], [120])]) None None None.

Definition getdents64_append_model : Model :=
  mkModel [(3, FdFileA 1 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    (raw_files [([102], [120])]) None None None.

(** ...AND THE TWO FILE KINDS [getdents64_model] DOES NOT HOLD ARE
    -ENOTDIR AND INERT.  ADMISSION REASON: as above, it pins
    model-internal state that no observation reveals.

    [iterate_dir] (fs/readdir.c:88-91, Linux v6.18.46) answers -ENOTDIR
    for a file with no [.iterate_shared], and neither O_RDWR nor
    O_APPEND gives a regular file one.  What a probe cannot see is that
    the model comes back the SAME model, the offset at 0.  The counts
    (64 and 256) have room, and on a non-directory the spec reads
    neither the count nor the buffer, so the -ENOTDIR is the kind's
    alone.  The second conjunct of each refuses the 0 a directory read
    to its end would answer. *)
Example getdents64_rdwr_fd_is_enotdir :
  check_syscall (getdents64_in 3 64) (mkEffect (errno_ret ENOTDIR) [] [])
    getdents64_rdwr_model = CheckOk getdents64_rdwr_model []
  /\ check_syscall (getdents64_in 3 64) (mkEffect (Z_to_bv 64 0) [] [])
       getdents64_rdwr_model = CheckReject.
Proof. split_conj; check_eq. Qed.

Example getdents64_append_fd_is_enotdir :
  check_syscall (getdents64_in 3 256) (mkEffect (errno_ret ENOTDIR) [] [])
    getdents64_append_model = CheckOk getdents64_append_model []
  /\ check_syscall (getdents64_in 3 256) (mkEffect (Z_to_bv 64 0) [] [])
       getdents64_append_model = CheckReject.
Proof. split_conj; check_eq. Qed.
