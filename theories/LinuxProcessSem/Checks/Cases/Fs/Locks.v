(** * LinuxProcessSem.Checks.Cases.Fs.Locks — worked examples over flock (32)

    Mirrors [Sys/Fs/Locks.v], which answers to Linux [fs/locks.c]: this
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

(** One opener per file: fd 3 reads "f" (inode 1), fd 4 writes "g"
    (inode 2), fd 5 is a directory reference. *)
Definition flock_model : Model :=
  mkModel
    [ (0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
      (3, FdFile 1 7); (4, FdFileW 2 9); (5, FdDir Fs.default_cwd) ]
    (mkVmMaps [] [] 0 0 demo_limit) IEof
    (raw_files [([102], [120]); ([103], [121])]) None None None.

(** The same table with a SECOND descriptor on "f" — what a second
    [openat] of the same name produces.  Only fd 6 differs. *)
Definition flock_two_openers_model : Model :=
  mkModel
    [ (0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
      (3, FdFile 1 7); (4, FdFileW 2 9); (5, FdDir Fs.default_cwd);
      (6, FdFile 1 0) ]
    (mkVmMaps [] [] 0 0 demo_limit) IEof
    (raw_files [([102], [120]); ([103], [121])]) None None None.

(** SUCCESS IS INERT.  ADMISSION REASON: it pins model-internal state
    that no observation reveals.

    A real run sees only the 0.  That the descriptors' offsets (7 and 9
    here) and the files' contents came back UNCHANGED, and that no event
    was emitted, is a statement about the model's own state, and the
    equalities below are the whole of it: the returned model is the SAME
    model, and the event list is empty.  It is worth pinning for flock
    in particular, because the syscall a program is issuing here is one
    that CHANGES kernel state — the whole point of taking a lock — and
    the model's answer is that none of the state it carries moves.

    Three arms are covered because they reach the answer by three
    different routes: LOCK_EX on the sole opener of "f" goes through the
    sole-opener gate, LOCK_UN on a directory reference skips the fd-kind
    match entirely, and LOCK_MAND (32) answers before the descriptor is
    resolved at all — which is why its case uses a descriptor that is
    not open.

    Each is paired with a rejection of a DIFFERENT return, so that "the
    model accepts this" is not the vacuous reading of a checker that
    accepts everything. *)

Example flock_success_is_inert :
  (* LOCK_EX on the sole opener of "f" *)
  check_syscall (mkInput 32 [3; 2; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) flock_model = CheckOk flock_model []
  /\ check_syscall (mkInput 32 [3; 2; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EAGAIN) [] []) flock_model = CheckReject
  (* LOCK_UN on a directory reference: 0 without consulting the fd kind *)
  /\ check_syscall (mkInput 32 [5; 8; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) flock_model = CheckOk flock_model []
  /\ check_syscall (mkInput 32 [5; 8; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) flock_model = CheckReject
  (* LOCK_MAND on a descriptor that is NOT OPEN: still 0, because the bit
     is tested before the lookup.  A model that resolved the fd first
     would answer -EBADF, which the second conjunct rules out. *)
  /\ check_syscall (mkInput 32 [9999; 32; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) flock_model = CheckOk flock_model []
  /\ check_syscall (mkInput 32 [9999; 32; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) flock_model = CheckReject.
Proof. split_conj; check_eq. Qed.

(** THE SOLE-OPENER GATE IS WHAT DECIDES THE GRANT.  ADMISSION REASON:
    it compares two models, and no run holds two.

    A program can reach the decline — it opens the same name twice and the
    run stops fail-closed — but a fail-closed verdict says only that the
    model left its surface, not WHICH fact took it there.  The contrast
    is what carries the argument, and it needs the two tables side by
    side: identical but for fd 6, one granting and one declining.

    The third and fourth conjuncts are what keep this from reading as
    "the second model declines everything".  LOCK_UN on the very same
    descriptor of the very same two-opener table still answers 0, and a
    different return is still rejected there — which is the claim that
    an unlock needs no premise about who else holds the file, stated
    where it can be compared against the request that does. *)

(** EVERY FILE KIND COUNTS AS AN OPENER, and this is the claim the
    enumeration in [Fs.Locks.ino_openers] cannot make.

    That fixpoint names every [State.FdEntry] constructor so that a
    later kind is a build error rather than a silent miscount, and the
    argument is sound as far as it goes -- but it is an argument about a
    missing ARM, not about an arm's ANSWER.  Replacing any counting arm
    with the skipping one the four non-file kinds take
    (`ino_openers r i`) compiles and closes every proof in the flock
    stack.  [flock_sole_opener] then answers TRUE with a second
    descriptor of that kind already on the path, and [flock_spec]
    returns 0 for a lock the kernel makes conflict: an unsound ACCEPT,
    with nothing red anywhere.

    Of the four counting arms, only [FdFile] is pinned elsewhere, by
    [flock_two_openers_model] holding two [FdFile] descriptors on one
    inode.  Without this example, the [FdFileW], [FdFileA] and [FdFileRW]
    arms could each take the skip with every proof still closing.

    So the example is over all four kinds rather than over one.
    For each: the sole opener is answered, a SECOND descriptor of the
    same kind on the same inode is declined, and a second descriptor of a
    DIFFERENT kind is declined too -- which is what says the count is
    over openers rather than over kinds, and is the half a per-kind
    counter would still pass.

    [sys_flock] reads neither [f_mode] nor [f_flags] on the path to
    [flock_lock_inode_wait]: the lock is on the inode, and which
    directions a description may transfer is not one of its inputs
    (fs/locks.c, Linux v6.18.46).  That is the one kernel fact all four
    arms rest on. *)
Definition flock_openers_model (es : list (word * FdEntry)) : Model :=
  mkModel ([(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2)] ++ es)
    (mkVmMaps [] [] 0 0 demo_limit) IEof
    (raw_files [([102], [120])]) None None None.

(** LOCK_EX on fd 3, which is the descriptor each model below puts on
    "f"; the effect claims the success, so a decline shows up as
    [CheckUnmodeled] and a wrong success as [CheckReject]. *)
Definition flock_ex_on_3 (m : Model) : check_result :=
  check_syscall (mkInput 32 [3; 2; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) m.

Example flock_every_file_kind_counts_as_an_opener :
  let sole (k : Fs.ino -> word -> FdEntry) :=
    flock_openers_model [(3, k 1%Z (Z_to_bv 64 0))] in
  let pair (k : Fs.ino -> word -> FdEntry) :=
    flock_openers_model [(3, k 1%Z (Z_to_bv 64 0)); (4, k 1%Z (Z_to_bv 64 5))] in
  let mixed (k : Fs.ino -> word -> FdEntry) :=
    flock_openers_model [(3, k 1%Z (Z_to_bv 64 0)); (4, FdFile 1 (Z_to_bv 64 5))] in
  (* the sole opener of "f" is provably uncontended, on every kind *)
  flock_ex_on_3 (sole FdFile) = CheckOk (sole FdFile) []
  /\ flock_ex_on_3 (sole FdFileW) = CheckOk (sole FdFileW) []
  /\ flock_ex_on_3 (sole FdFileA) = CheckOk (sole FdFileA) []
  /\ flock_ex_on_3 (sole FdFileRW) = CheckOk (sole FdFileRW) []
  (* a SECOND descriptor of the same kind on the same name: declined *)
  /\ flock_ex_on_3 (pair FdFile) = CheckUnmodeled
  /\ flock_ex_on_3 (pair FdFileW) = CheckUnmodeled
  /\ flock_ex_on_3 (pair FdFileA) = CheckUnmodeled
  /\ flock_ex_on_3 (pair FdFileRW) = CheckUnmodeled
  (* ...and a second descriptor of a DIFFERENT kind contends just the
     same, which a counter that counted each kind only against its own
     would still get wrong *)
  /\ flock_ex_on_3 (mixed FdFileW) = CheckUnmodeled
  /\ flock_ex_on_3 (mixed FdFileA) = CheckUnmodeled
  /\ flock_ex_on_3 (mixed FdFileRW) = CheckUnmodeled
  (* the decline is the sole-opener gate and not the KIND: LOCK_UN on the
     very same two-descriptor table still answers 0, since an unlock
     spends no premise about other holders *)
  /\ check_syscall (mkInput 32 [3; 8; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) (pair FdFileRW) = CheckOk (pair FdFileRW) []
  (* and a kernel claiming the sole opener conflicted is refused *)
  /\ check_syscall (mkInput 32 [3; 2; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EAGAIN) [] []) (sole FdFileRW) = CheckReject.
Proof. split_conj; check_eq. Qed.

Example flock_second_opener_declines :
  check_syscall (mkInput 32 [3; 2; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) flock_model = CheckOk flock_model []
  /\ check_syscall (mkInput 32 [3; 2; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) flock_two_openers_model = CheckUnmodeled
  /\ check_syscall (mkInput 32 [3; 8; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) flock_two_openers_model
     = CheckOk flock_two_openers_model []
  /\ check_syscall (mkInput 32 [3; 8; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EAGAIN) [] []) flock_two_openers_model = CheckReject.
Proof. split_conj; check_eq. Qed.
