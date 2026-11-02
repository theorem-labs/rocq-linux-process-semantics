(** * LinuxProcessSem.Checks.Cases.Fs.File — worked examples over dup (23), dup3 (24), close_range (436), and the [State.ONsFile] kind

    Mirrors [Sys/Fs/File.v], which answers to Linux [fs/file.c]: this
    file holds the worked examples for the syscalls defined there, and
    no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary.

    What a real run cannot show, and these therefore carry: the fd TABLE
    the model is left with (a real run reveals only the return value),
    the DECLINES, which hold for every claimed return rather than for
    the one return a given execution happened to produce, and the two
    facts about dup3's RLIMIT_NOFILE gate that need a SECOND model to
    state — that it is read from the run rather than written into the
    spec, and that it beats a descriptor the process already holds. *)

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

(** The three channels, a read-only file "f" = "hi" at fd 3 positioned
    one byte in, and the directory fd at 4 — one fd of every kind, so
    both sides of [File.dup_modeled_entry] are in reach.  The lowest
    free fd is 5. *)
Definition dup_model : Model :=
  mkModel [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
           (3, FdFile [102] 1); (4, FdDir)]
    (mkVmMaps [] [] 0 0 demo_limit) IEof [([102], [104; 105])] None None
    None.

(** dup hands out the lowest free fd and binds it to a COPY of the
    entry, which is the whole of what "share the description" means for
    a channel: the read position is [m_stdin] and the writes are trace
    events, so both fds already name the same thing.  No kernel can be
    made to hand out a non-lowest fd, so the second conjunct — the model
    REJECTS fd 6 — is only reachable here. *)
Example dup_installs_a_copy_at_the_lowest_free_fd :
  check_syscall (mkInput 23 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 5 [] []) dup_model
  = CheckOk (with_fds (fd_insert (m_fds dup_model) 5 (FdChannel 0)) dup_model) []
  /\ check_syscall (mkInput 23 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 6 [] []) dup_model
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** A directory fd duplicates too: [FdDir] is nullary, so a copy carries
    no position that could drift. *)
Example dup_of_a_directory_fd_duplicates :
  check_syscall (mkInput 23 [4; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 5 [] []) dup_model
  = CheckOk (with_fds (fd_insert (m_fds dup_model) 5 FdDir) dup_model) [].
Proof. check_eq. Qed.

(** The offset-sharing gap, stated as the model's answer rather than as
    a comment: duplicating a FILE fd declines WHATEVER the kernel
    claims.  A real run pins one claimed return; this pins all of them,
    which is what makes it a fail-closed gap rather than a wrong
    answer. *)
Lemma dup_of_a_file_fd_declines_whatever_the_kernel_claims : forall eff,
  check_syscall (mkInput 23 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    eff dup_model
  = CheckUnmodeled.
Proof. intro eff. vm_compute. reflexivity. Qed.

(** dup3 returns the fd it was GIVEN, silently closing what was there:
    fd 1 stops naming channel 1 and names channel 0, so it stops being
    WRITABLE — [write_spec]'s channel arm answers -EBADF for channel 0.
    That the entry moved is model-internal state no return value
    reveals. *)
Example dup3_replaces_the_target_and_returns_it :
  check_syscall (mkInput 24 [0; 1; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 1 [] []) dup_model
  = CheckOk (with_fds (fd_insert (m_fds dup_model) 1 (FdChannel 0)) dup_model) []
  /\ check_syscall (mkInput 24 [0; 1; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 5 [] []) dup_model
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** O_CLOEXEC is accepted and leaves the same state as flags 0 — nothing
    in [Specs.modeled_sysnos] can observe a close-on-exec bit's value
    (F_GETFD admits both answers; see [File.dup3_spec]).  Any OTHER bit
    is [ksys_dup3]'s -EINVAL, so claiming the successful return there is
    rejected. *)
Example dup3_ignores_o_cloexec_but_not_another_bit :
  check_syscall (mkInput 24 [0; 1; 524288; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 1 [] []) dup_model
  = CheckOk (with_fds (fd_insert (m_fds dup_model) 1 (FdChannel 0)) dup_model) []
  /\ check_syscall (mkInput 24 [0; 1; 4; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 1 [] []) dup_model
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** [oldfd == newfd] is -EINVAL even for a FILE fd, which is a place
    the model is deliberately MORE precise than its own decline: the
    equality test precedes every kind test, as [ksys_dup3] orders them,
    so the entry that carries an offset is never reached.  Declining
    here instead would be fail-closed but wrong-shaped — Linux answers
    -EINVAL whatever the fd is. *)
Example dup3_eq_beats_the_file_fd_decline :
  check_syscall (mkInput 24 [3; 3; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) dup_model
  = CheckOk dup_model []
  /\ check_syscall (mkInput 24 [3; 3; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 3 [] []) dup_model
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** A FREE [newfd] below [Uapi.NR_OPEN_DEFAULT] is installed at the
    number given, not at the lowest free one — which is the difference
    between dup3 and dup, and is why the rejected conjunct claims fd 5,
    the number [dup] would have answered.  [dup_model]'s limit is
    [State.default_nofile], so 7 is under it. *)
Example dup3_takes_a_free_newfd_below_the_embedded_table :
  check_syscall (mkInput 24 [0; 7; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 7 [] []) dup_model
  = CheckOk (with_fds (fd_insert (m_fds dup_model) 7 (FdChannel 0)) dup_model) []
  /\ check_syscall (mkInput 24 [0; 7; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 5 [] []) dup_model
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** A FREE [newfd] at or above it is declined for every claimed return.
    Linux decides 100 here out of the descriptor table's current
    [max_fds] and the [sysctl_nr_open] ceiling, neither of which the
    model carries: it may return 100, or -EBADF (from the -EMFILE
    [ksys_dup3] rewrites), or -ENOMEM.  Three answers, no way to choose
    — see [File.dup3_spec]. *)
Lemma dup3_declines_a_free_newfd_above_the_embedded_table : forall eff,
  check_syscall (mkInput 24 [0; 100; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    eff dup_model
  = CheckUnmodeled.
Proof. intro eff. vm_compute. reflexivity. Qed.

(** THE LIMIT IS READ FROM THE RUN, not written into the spec, and this
    is the pair that says so.  [dup_model] carries
    [State.default_nofile]; this is the same model, same descriptors,
    under a soft limit of 4 — which a parent that lowered RLIMIT_NOFILE
    really can hand a process, since [execve] closes only the
    close-on-exec descriptors and the rest stay open however low the
    limit is.  Every check below runs the SAME input against both
    models, so only the limit can separate the answers: replace
    [File.dup3_newfd_under_limit]'s [m_nofile m] with any constant and
    one of the two sides breaks. *)
Definition dup_model_nofile4 : Model := with_nofile (Z_to_bv 64 4) dup_model.

(** fd 5 is free and below [Uapi.NR_OPEN_DEFAULT], so nothing but the
    limit can separate the two answers: under [State.default_nofile] the
    free-[newfd] arm installs it, and under 4 the gate answers first. *)
Example dup3_free_newfd_is_decided_by_the_run_s_limit :
  check_syscall (mkInput 24 [0; 5; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 5 [] []) dup_model
  = CheckOk (with_fds (fd_insert (m_fds dup_model) 5 (FdChannel 0)) dup_model) []
  /\ check_syscall (mkInput 24 [0; 5; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) dup_model_nofile4
     = CheckOk dup_model_nofile4 []
  /\ check_syscall (mkInput 24 [0; 5; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 5 [] []) dup_model_nofile4
     = CheckReject.
Proof. split; [check_eq|split; [check_eq | vm_compute; reflexivity]]. Qed.

(** The gate beats the descriptor the process ALREADY HOLDS, which is
    the case a spec can answer wrongly rather than decline: fd 4 is
    open (it is the directory fd) and sits AT the limit, so dup3 onto it
    is -EBADF where a spec that only looked the fd up would have
    returned 4.  fd 3 beside it, open and under the limit, is the
    ordinary replacement — so the pair also pins the comparison as
    STRICT, since [newfd <= limit] would make 4 succeed. *)
Example dup3_limit_beats_an_fd_the_process_holds :
  check_syscall (mkInput 24 [0; 3; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 3 [] []) dup_model_nofile4
  = CheckOk (with_fds (fd_insert (m_fds dup_model_nofile4) 3 (FdChannel 0))
               dup_model_nofile4) []
  /\ check_syscall (mkInput 24 [0; 4; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) dup_model_nofile4
     = CheckOk dup_model_nofile4 []
  /\ check_syscall (mkInput 24 [0; 4; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 4 [] []) dup_model_nofile4
     = CheckReject.
Proof. split; [check_eq|split; [check_eq | vm_compute; reflexivity]]. Qed.

(** [Uapi.NR_OPEN_DEFAULT]'s own boundary, adjacent values either side:
    63 is answered and 64 is declined.  The examples above do not reach
    it — they sit at 5, 7 and 100 — so an off-by-one
    in that one comparison would otherwise pass everything, the spec and
    the checker sharing the test. *)
Example dup3_free_newfd_just_below_the_embedded_table :
  check_syscall (mkInput 24 [0; 63; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 63 [] []) dup_model
  = CheckOk (with_fds (fd_insert (m_fds dup_model) 63 (FdChannel 0)) dup_model) [].
Proof. check_eq. Qed.

Lemma dup3_declines_a_free_newfd_at_the_embedded_table : forall eff,
  check_syscall (mkInput 24 [0; 64; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    eff dup_model
  = CheckUnmodeled.
Proof. intro eff. vm_compute. reflexivity. Qed.

(** The RLIMIT_NOFILE gate, and its PLACEMENT.  [ksys_dup3] tests
    [newfd >= rlimit(RLIMIT_NOFILE)] before it looks [oldfd] up, so the
    answer is -EBADF even for an [oldfd] whose kind the model refuses to
    duplicate — 3 is [FdFile], which [File.dup_modeled_entry] rejects.
    Reorder the spec to test the kind first and the second conjunct
    turns into [CheckUnmodeled].  The order holds for EVERY claimed
    return and needs no run.  2000 is above
    [State.default_nofile]. *)
Example dup3_over_the_limit_is_ebadf_before_the_oldfd_lookup :
  check_syscall (mkInput 24 [0; 2000; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EBADF) [] []) dup_model
  = CheckOk dup_model []
  /\ check_syscall (mkInput 24 [3; 2000; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) dup_model
     = CheckOk dup_model []
  /\ check_syscall (mkInput 24 [0; 2000; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 2000 [] []) dup_model
     = CheckReject.
Proof. split; [check_eq|split; [check_eq | vm_compute; reflexivity]]. Qed.

(** dup AND dup3 DECLINE the /proc/self/fd directory
    ([State.OProcFdDir]) and a signalfd ([State.OSignalFd]), as they
    decline every opaque kind ([File.dup_modeled_entry]).  For the
    directory a copied entry would be wrong: it would carry its own
    position, where Linux's two descriptors share one [f_pos].  THE
    CONTROL is answered alike by the text before these kinds and after:
    dup3 of the channel at 0 onto 7 installs a copy. *)
Definition dup_opaque_model : Model :=
  with_fds (fd_insert (fd_insert (m_fds dup_model) 5
              (FdOpaque (OProcFdDir (Z_to_bv 64 0x98900) (Some (Z_to_bv 64 0)))))
            6 (FdOpaque (OSignalFd (Z_to_bv 64 0x10000) (Z_to_bv 64 0x80800))))
    dup_model.

Example dup3_declines_procfd_dir_and_signalfd :
  check_syscall (mkInput 24 [5; 7; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 7 [] []) dup_opaque_model = CheckUnmodeled
  /\ check_syscall (mkInput 24 [6; 7; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 7 [] []) dup_opaque_model = CheckUnmodeled
  /\ check_syscall (mkInput 23 [5; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 7 [] []) dup_opaque_model = CheckUnmodeled
  /\ check_syscall (mkInput 23 [6; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 7 [] []) dup_opaque_model = CheckUnmodeled
  (* the control *)
  /\ check_syscall (mkInput 24 [0; 7; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 7 [] []) dup_opaque_model
     = CheckOk (with_fds (fd_insert (m_fds dup_opaque_model) 7 (FdChannel 0))
                  dup_opaque_model) [].
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(* -------------------------------------------------------------------------
   close_range (436)

   The model before this arm declined every [close_range].  The pairs
   below pin what is now answered against what still declines, on
   [dup_model]: three channels, a file at 3 and a directory at 4.
   ------------------------------------------------------------------------- *)

Definition close_range_in (fd max_fd flags : word) : SyscallInput :=
  mkInput 436 [fd; max_fd; flags; 0; 0; 0] (fun _ => None) (fun _ => None).

(** [close_range(3, ~0U, 0)] closes every descriptor from 3 up -- the
    file and the directory alike, since the arm is kind-blind as
    [close] is -- keeps 0, 1 and 2, and answers 0.  The fds are
    [unsigned int]s, so a0 = 2^32 + 3 is the same call, and an empty
    range ([close_range(5, 9, 0)]) is still 0 with nothing removed.  No
    other answer is admitted. *)
Example close_range_removes_the_range :
  check_syscall (close_range_in 3 4294967295 0) (mkEffect 0 [] []) dup_model
    = CheckOk (with_fds [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2)]
                        dup_model) []
  /\ check_syscall (close_range_in 4294967299 4294967295 0) (mkEffect 0 [] [])
       dup_model
     = CheckOk (with_fds [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2)]
                         dup_model) []
  /\ check_syscall (close_range_in 5 9 0) (mkEffect 0 [] []) dup_model
     = CheckOk dup_model []
  /\ check_syscall (close_range_in 3 4294967295 0)
       (mkEffect (errno_ret EBADF) [] []) dup_model = CheckReject.
Proof. repeat split; solve [ check_eq | vm_compute; reflexivity ]. Qed.

(** [close_range(5, 3, 0)] is -EINVAL and closes nothing, and so is an
    unknown flag bit -- tested FIRST, so even a well-ordered range with
    flag 8 is -EINVAL -- and an inverted range with a KNOWN flag: the
    range test comes before the flag is acted on, so that -EINVAL is
    answered rather than declined. *)
Example close_range_refuses_an_inverted_range :
  check_syscall (close_range_in 5 3 0) (mkEffect (errno_ret EINVAL) [] [])
    dup_model = CheckOk dup_model []
  /\ check_syscall (close_range_in 5 3 0) (mkEffect 0 [] []) dup_model
     = CheckReject
  /\ check_syscall (close_range_in 3 4294967295 8)
       (mkEffect (errno_ret EINVAL) [] []) dup_model = CheckOk dup_model []
  /\ check_syscall (close_range_in 5 3 4) (mkEffect (errno_ret EINVAL) [] [])
       dup_model = CheckOk dup_model [].
Proof. repeat split; solve [ check_eq | vm_compute; reflexivity ]. Qed.

(** THE CONTROL, which the model before this arm passed too:
    [CLOSE_RANGE_CLOEXEC] (4) and [CLOSE_RANGE_UNSHARE] (2) on a valid
    range decline, whatever the kernel claims. *)
Lemma close_range_declines_known_flags : forall eff,
  check_syscall (close_range_in 3 4294967295 4) eff dup_model = CheckUnmodeled
  /\ check_syscall (close_range_in 3 4294967295 2) eff dup_model = CheckUnmodeled
  /\ check_syscall (close_range_in 3 4294967295 6) eff dup_model = CheckUnmodeled.
Proof. intro eff. repeat split; vm_compute; reflexivity. Qed.

(* =========================================================================
   [State.ONsFile]: a descriptor on an open file that the namespace and
   mount model holds under a handle.  These
   examples span the descriptor-level calls, not only fs/file.c's,
   because what they pin is the KIND's rule: the object behind the handle
   may be a directory, a regular file, a procfs file, an eventfd or a
   socket, so only the answers Linux gives every open file alike are
   given (close, and fcntl's F_SETFD and F_GETFD), and every other call
   on it declines.  No arm mints one, so a run from [init_config] never
   meets these; the model before this kind had no way to hold one.
   ========================================================================= *)

(** fd 3 holds a namespace and mount model file under handle 7, fd 4 the read-only file
    "f" = "hi", fd 5 the directory.  The lowest free fd is 6. *)
Definition ns_model : Model :=
  mkModel [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
           (3, FdOpaque (ONsFile 7)); (4, FdFile [102] 1); (5, FdDir)]
    (mkVmMaps [] [] 0 0 demo_limit) IEof [([102], [104; 105])] None None
    None.

Definition fd_call (no a0 a1 a2 : word) : SyscallInput :=
  mkInput no [a0; a1; a2; 0; 0; 0] (fun _ => None) (fun _ => None).

(** DECLINED on fd 3: read, write, fstat, fcntl(F_GETFL), dup,
    ioctl(TIOCGWINSZ) and lseek, whatever errno the kernel claims. *)
Example ns_file_declines_every_kind_dependent_call :
  check_syscall (fd_call 63 3 0x10000 16) (mkEffect (errno_ret EBADF) [] []) ns_model
  = CheckUnmodeled
  /\ check_syscall (fd_call 64 3 0x10000 16) (mkEffect (errno_ret EBADF) [] []) ns_model
     = CheckUnmodeled
  /\ check_syscall (fd_call 80 3 0x10000 0) (mkEffect (errno_ret EBADF) [] []) ns_model
     = CheckUnmodeled
  /\ check_syscall (fd_call 25 3 F_GETFL 0) (mkEffect 0 [] []) ns_model
     = CheckUnmodeled
  /\ check_syscall (fd_call 23 3 0 0) (mkEffect 6 [] []) ns_model
     = CheckUnmodeled
  /\ check_syscall (fd_call 29 3 TIOCGWINSZ 0x10000) (mkEffect (errno_ret ENOTTY) [] [])
       ns_model
     = CheckUnmodeled
  /\ check_syscall (fd_call 62 3 0 0) (mkEffect 0 [] []) ns_model
     = CheckUnmodeled.
Proof. repeat split; check_eq. Qed.

(** ANSWERED on fd 3: fcntl(F_SETFD) is 0, fcntl(F_GETFD) is 0 or
    FD_CLOEXEC, and close is 0 and removes the entry.  THE CONTROLS,
    which the model before this kind answered the same way: the same
    calls on fd 4, a closed fd's -EBADF for the declined ones, and dup of
    the directory at fd 5. *)
Example ns_file_answers_the_kind_blind_calls :
  check_syscall (fd_call 25 3 F_SETFD FD_CLOEXEC) (mkEffect 0 [] []) ns_model
  = CheckOk ns_model []
  /\ check_syscall (fd_call 25 3 F_GETFD 0) (mkEffect 0 [] []) ns_model
     = CheckOk ns_model []
  /\ check_syscall (fd_call 25 3 F_GETFD 0) (mkEffect FD_CLOEXEC [] []) ns_model
     = CheckOk ns_model []
  /\ check_syscall (fd_call 57 3 0 0) (mkEffect 0 [] []) ns_model
     = CheckOk (with_fds (fd_remove (m_fds ns_model) 3) ns_model) []
  (* the controls *)
  /\ check_syscall (fd_call 25 4 F_SETFD FD_CLOEXEC) (mkEffect 0 [] []) ns_model
     = CheckOk ns_model []
  /\ check_syscall (fd_call 57 4 0 0) (mkEffect 0 [] []) ns_model
     = CheckOk (with_fds (fd_remove (m_fds ns_model) 4) ns_model) []
  /\ check_syscall (fd_call 63 9 0x10000 16) (mkEffect (errno_ret EBADF) [] []) ns_model
     = CheckOk ns_model []
  /\ check_syscall (fd_call 80 9 0x10000 0) (mkEffect (errno_ret EBADF) [] []) ns_model
     = CheckOk ns_model []
  /\ check_syscall (fd_call 23 5 0 0) (mkEffect 6 [] []) ns_model
     = CheckOk (with_fds (fd_insert (m_fds ns_model) 6 FdDir) ns_model) [].
Proof. repeat split; check_eq. Qed.

(** A LOCK IT MAY HOLD.  The file behind handle 7 may be "f" itself, so
    while fd 3 is open flock on fd 4 declines ([Locks.path_openers]
    counts the handle for every path).  THE CONTROL is the old answer:
    with no such descriptor ([dup_model], where fd 3 is the only opener
    of "f"), the same shared lock is 0. *)
Example ns_file_blocks_the_sole_opener_flock :
  (* 1 is LOCK_SH *)
  check_syscall (fd_call 32 4 1 0) (mkEffect 0 [] []) ns_model
  = CheckUnmodeled
  /\ check_syscall (fd_call 32 3 1 0) (mkEffect 0 [] []) dup_model
     = CheckOk dup_model [].
Proof. split; check_eq. Qed.

(** THE REST OF THE KIND-BLIND CALLS on an [ONsFile].  [close_range]
    over fd 3 removes it and answers 0 ([__range_close] discards the
    per-file close result), and [dup3] onto fd 3 replaces it.  THE
    CONTROLS, answered alike before this kind: the same two calls over
    the directory at fd 5. *)
Example ns_file_close_range_and_dup3_onto_it :
  check_syscall (close_range_in 3 3 0) (mkEffect 0 [] []) ns_model
  = CheckOk (with_fds (fd_remove (m_fds ns_model) 3) ns_model) []
  /\ check_syscall (fd_call 24 0 3 0) (mkEffect 3 [] []) ns_model
     = CheckOk (with_fds (fd_insert (m_fds ns_model) 3 (FdChannel 0)) ns_model) []
  (* the controls *)
  /\ check_syscall (close_range_in 5 5 0) (mkEffect 0 [] []) ns_model
     = CheckOk (with_fds (fd_remove (m_fds ns_model) 5) ns_model) []
  /\ check_syscall (fd_call 24 0 5 0) (mkEffect 5 [] []) ns_model
     = CheckOk (with_fds (fd_insert (m_fds ns_model) 5 (FdChannel 0)) ns_model) [].
Proof. repeat split; check_eq. Qed.

(** AN UNLINK IT MAY WATCH.  The file behind handle 7 may be the one
    unlinked, so while fd 3 is open [unlinkat] of a held name declines
    ([Namei.fd_names_path] is true on the handle).  THE CONTROL is the
    old answer: with no such descriptor the same unlink answers 0 and
    removes the key. *)
Definition ns_unlink_model : Model :=
  mkModel [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
           (3, FdOpaque (ONsFile 7))]
    (mkVmMaps [] [] 0 0 demo_limit) IEof [([103], [104])] None None None.

Definition unlink_g_in : SyscallInput :=
  mkInput 35 [AT_FDCWD; 0x2000; 0; 0; 0; 0] (bytes_at 0x2000 [103; 0]) (fun _ => None).

Example ns_file_blocks_unlinkat :
  check_syscall unlink_g_in (with_copyins [(0x2000, 2%nat)] (mkEffect 0 [] []))
    ns_unlink_model
  = CheckUnmodeled
  /\ match check_syscall unlink_g_in
             (with_copyins [(0x2000, 2%nat)] (mkEffect 0 [] []))
             (with_fds (fd_remove (m_fds ns_unlink_model) 3) ns_unlink_model) with
     | CheckOk m [] => m_fs m = []
     | _ => False
     end.
Proof. split; vm_compute; reflexivity. Qed.
