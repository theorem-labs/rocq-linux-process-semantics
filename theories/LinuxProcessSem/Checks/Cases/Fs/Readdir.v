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
    things a real run reveals nothing about. *)

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
      (3, FdFile [102] 7); (4, FdFileW [103] 9); (5, FdDir) ]
    (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [120]); ([103], [121])] None None None.

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
Proof. repeat split; check_eq. Qed.

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
Proof. repeat split; check_eq. Qed.

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
Proof. repeat split; check_eq. Qed.

(* =========================================================================
   The /proc/self/fd listing ([State.OProcFdDir], [Fs.Readdir.procfd_getdents_spec])

   bubblewrap's monitor process walks /proc/self/fd with musl's
   [readdir], which calls getdents64 with a 2048-byte buffer, and closes
   every descriptor it does not keep.  Before this arm the model
   declined getdents64 on every opaque descriptor.
   ========================================================================= *)

(** fds 0-2 the launch's channels, fd 3 an O_PATH descriptor on "/proc",
    fd 4 the /proc/self/fd directory at position 0, fd 5 an eventfd. *)
Definition procfd_list_model : Model :=
  let m := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) in
  with_fds (fd_insert (fd_insert (fd_insert (m_fds m)
              3 (FdOpaque (OProcPath [47; 112; 114; 111; 99])))
              4 (FdOpaque (OProcFdDir (Z_to_bv 64 0x98900) (Some (Z_to_bv 64 0)))))
              5 (FdOpaque (OEventFd (Z_to_bv 64 0x80800)))) m.

(** [m] with fd 4's directory position set to [p]. *)
Definition procfd_at (m : Model) (p : option word) : Model :=
  with_fds (fd_insert (m_fds m) 4 (FdOpaque (OProcFdDir (Z_to_bv 64 0x98900) p))) m.

(** [getdents64(fd, dirent, count)] into the 4079 writable bytes at 0x10000. *)
Definition procfd_list_in (fd dirent count : word) : SyscallInput :=
  mkInput 61 [fd; dirent; count; 0; 0; 0] (fun _ => None) sysctl_buf_wmem.

(** One [linux_dirent64] record as [filldir64] writes it, up to its NUL:
    [d_ino], [d_off], [d_reclen] 24 (every name here is one or two
    bytes), [d_type], the name. *)
Definition drec (ino off ty : Z) (name : list byte) : list byte :=
  Z_to_le_bytes 8 ino ++ Z_to_le_bytes 8 off ++ Z_to_le_bytes 2 24
  ++ [Z_to_bv 8 ty] ++ name ++ [Z_to_bv 8 0].

(** The whole listing from position 0: ".", "..", then "0" to "5" in
    ascending order, each [d_off] the next entry's position (fd k sits at
    position k + 2), and the last [d_off] the end position, here 66 (a
    table of 64 slots: [max_fds + 2]). *)
Definition procfd_listing (endpos : Z) : list (word * list byte) :=
  [ (0x10000, drec 1 1 DT_DIR [46]);
    (0x10018, drec 1 2 DT_DIR [46; 46]);
    (0x10030, drec 7 3 DT_LNK [48]);
    (0x10048, drec 8 4 DT_LNK [49]);
    (0x10060, drec 9 5 DT_LNK [50]);
    (0x10078, drec 10 6 DT_LNK [51]);
    (0x10090, drec 11 7 DT_LNK [52]);
    (0x100a8, drec 12 endpos DT_LNK [53]) ].

(** THE LISTING IS THE MODEL'S OWN TABLE: 192 bytes, eight records, and
    the directory left at the end position.  [d_ino] is the
    environment's (any value is admitted), the rest is exact: a wrong
    [d_off], a missing descriptor and a short count are rejected, and an
    end position at or below the last listed descriptor's is rejected
    too.  A second call from the end answers 0, and the position is then
    the kernel's [max_fds + 2], which the model does not know: a third
    call is declined.

    THE CONTROL is answered alike by the old text and the new:
    getdents64 on the O_PATH descriptor at fd 3 is declined. *)
Example getdents64_proc_self_fd_listing :
  check_syscall (procfd_list_in 4 0x10000 4079)
    (mkEffect 192 (procfd_listing 66) []) procfd_list_model
  = CheckOk (procfd_at procfd_list_model (Some (Z_to_bv 64 66))) []
  (* a wrong [d_off] on "." *)
  /\ check_syscall (procfd_list_in 4 0x10000 4079)
       (mkEffect 192 ((0x10000, drec 1 2 DT_DIR [46]) :: tl (procfd_listing 66)) [])
       procfd_list_model
     = CheckReject
  (* the eventfd at fd 5 left out *)
  /\ check_syscall (procfd_list_in 4 0x10000 4079)
       (mkEffect 168 (firstn 7 (procfd_listing 66)) []) procfd_list_model
     = CheckReject
  (* an end position that does not lie past fd 5's *)
  /\ check_syscall (procfd_list_in 4 0x10000 4079)
       (mkEffect 192 (procfd_listing 7) []) procfd_list_model
     = CheckReject
  (* a byte count that is not the records' *)
  /\ check_syscall (procfd_list_in 4 0x10000 4079)
       (mkEffect 191 (procfd_listing 66) []) procfd_list_model
     = CheckReject
  (* from the end: 0, and the position is no longer known *)
  /\ check_syscall (procfd_list_in 4 0x10000 4079) (mkEffect 0 [] [])
       (procfd_at procfd_list_model (Some (Z_to_bv 64 66)))
     = CheckOk (procfd_at (procfd_at procfd_list_model (Some (Z_to_bv 64 66))) None) []
  /\ check_syscall (procfd_list_in 4 0x10000 4079) (mkEffect 0 [] [])
       (procfd_at procfd_list_model None)
     = CheckUnmodeled
  (* the control *)
  /\ check_syscall (procfd_list_in 3 0x10000 4079) (mkEffect (errno_ret ENOTDIR) [] [])
       procfd_list_model
     = CheckUnmodeled.
Proof. repeat split; check_eq. Qed.

(** A BUFFER WITH ROOM FOR ONE RECORD stops after it, and the position
    is the next entry's; a buffer with room for none is -EINVAL, and one
    [access_ok] refuses is -EFAULT, both leaving the position at the
    first unlisted entry. *)
Example getdents64_proc_self_fd_short_buffers :
  check_syscall (procfd_list_in 4 0x10000 30)
    (mkEffect 24 [(0x10000, drec 5 1 DT_DIR [46])] []) procfd_list_model
  = CheckOk (procfd_at procfd_list_model (Some (Z_to_bv 64 1))) []
  /\ check_syscall (procfd_list_in 4 0x10000 10) (mkEffect (errno_ret EINVAL) [] [])
       procfd_list_model
     = CheckOk (procfd_at procfd_list_model (Some (Z_to_bv 64 0))) []
  /\ check_syscall (procfd_list_in 4 (Z_to_bv 64 (2 ^ 63)) 4079)
       (mkEffect (errno_ret EFAULT) [] []) procfd_list_model
     = CheckOk (procfd_at procfd_list_model (Some (Z_to_bv 64 0))) []
  (* from position 1: "..", then the descriptors *)
  /\ check_syscall (procfd_list_in 4 0x10000 4079)
       (mkEffect 168
          (map (fun '(a, r) => (Z_to_bv 64 (bv_unsigned a - 24), r)) (tl (procfd_listing 66)))
          [])
       (procfd_at procfd_list_model (Some (Z_to_bv 64 1)))
     = CheckOk (procfd_at (procfd_at procfd_list_model (Some (Z_to_bv 64 1)))
                  (Some (Z_to_bv 64 66))) [].
Proof. repeat split; check_eq. Qed.
