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
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Import
  Fs.Stat.

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
  = CheckOk (with_cloexec [(5, false)]
               (with_fds (fd_insert (m_fds dup_model) 5 (FdChannel 0)) dup_model)) []
  /\ check_syscall (mkInput 23 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 6 [] []) dup_model
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** A directory fd duplicates too: [FdDir] is nullary, so a copy carries
    no position that could drift. *)
Example dup_of_a_directory_fd_duplicates :
  check_syscall (mkInput 23 [4; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 5 [] []) dup_model
  = CheckOk (with_cloexec [(5, false)]
               (with_fds (fd_insert (m_fds dup_model) 5 FdDir) dup_model)) [].
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
  = CheckOk (with_cloexec [(1, false)]
               (with_fds (fd_insert (m_fds dup_model) 1 (FdChannel 0)) dup_model)) []
  /\ check_syscall (mkInput 24 [0; 1; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 5 [] []) dup_model
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** O_CLOEXEC is accepted, and leaves the same table as flags 0 with the
    new descriptor's close-on-exec bit SET where flags 0 clears it
    ([File.dup3_spec]: [do_dup2]'s [__set_open_fd]).  Any OTHER bit is
    [ksys_dup3]'s -EINVAL, so claiming the successful return there is
    rejected. *)
Example dup3_ignores_o_cloexec_but_not_another_bit :
  check_syscall (mkInput 24 [0; 1; 524288; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 1 [] []) dup_model
  = CheckOk (with_cloexec [(1, true)]
               (with_fds (fd_insert (m_fds dup_model) 1 (FdChannel 0)) dup_model)) []
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
  = CheckOk (with_cloexec [(7, false)]
               (with_fds (fd_insert (m_fds dup_model) 7 (FdChannel 0)) dup_model)) []
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
  = CheckOk (with_cloexec [(5, false)]
               (with_fds (fd_insert (m_fds dup_model) 5 (FdChannel 0)) dup_model)) []
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
  = CheckOk (with_cloexec [(3, false)]
               (with_fds (fd_insert (m_fds dup_model_nofile4) 3 (FdChannel 0))
                  dup_model_nofile4)) []
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
  = CheckOk (with_cloexec [(63, false)]
               (with_fds (fd_insert (m_fds dup_model) 63 (FdChannel 0)) dup_model)) [].
Proof. check_eq. Qed.

Lemma dup3_declines_a_free_newfd_at_the_embedded_table : forall eff,
  check_syscall (mkInput 24 [0; 64; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    eff dup_model
  = CheckUnmodeled.
Proof. intro eff. vm_compute. reflexivity. Qed.

(** The RLIMIT_NOFILE gate, and its PLACEMENT.  [ksys_dup3] tests
    [newfd >= rlimit(RLIMIT_NOFILE)] before it looks [oldfd] up, so the
    answer is -EBADF even for an [oldfd] whose kind the model would
    decline to put at 2000 — 3 is [FdFile], which [File.dup3_spec]
    moves only onto a free [newfd] below [Uapi.NR_OPEN_DEFAULT].
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
    dup3 of the channel at 0 onto 7 in [dup_model], which holds neither
    kind, installs a copy. *)
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
       (mkEffect 7 [] []) dup_model
     = CheckOk (with_cloexec [(7, false)]
                  (with_fds (fd_insert (m_fds dup_model) 7 (FdChannel 0)) dup_model)) [].
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

(** ANSWERED on fd 3: fcntl(F_SETFD) is 0 and records the bit,
    fcntl(F_GETFD) is 0 or FD_CLOEXEC (no bit is known in [ns_model]),
    and close is 0 and removes the entry.  THE CONTROLS, which the model
    before this kind answered the same way: the same calls on fd 4, a
    closed fd's -EBADF for the declined ones, and dup of the directory at
    fd 5. *)
Example ns_file_answers_the_kind_blind_calls :
  check_syscall (fd_call 25 3 F_SETFD FD_CLOEXEC) (mkEffect 0 [] []) ns_model
  = CheckOk (with_cloexec [(3, true)] ns_model) []
  /\ check_syscall (fd_call 25 3 F_GETFD 0) (mkEffect 0 [] []) ns_model
     = CheckOk ns_model []
  /\ check_syscall (fd_call 25 3 F_GETFD 0) (mkEffect FD_CLOEXEC [] []) ns_model
     = CheckOk ns_model []
  /\ check_syscall (fd_call 57 3 0 0) (mkEffect 0 [] []) ns_model
     = CheckOk (with_fds (fd_remove (m_fds ns_model) 3) ns_model) []
  (* the controls *)
  /\ check_syscall (fd_call 25 4 F_SETFD FD_CLOEXEC) (mkEffect 0 [] []) ns_model
     = CheckOk (with_cloexec [(4, true)] ns_model) []
  /\ check_syscall (fd_call 57 4 0 0) (mkEffect 0 [] []) ns_model
     = CheckOk (with_fds (fd_remove (m_fds ns_model) 4) ns_model) []
  /\ check_syscall (fd_call 63 9 0x10000 16) (mkEffect (errno_ret EBADF) [] []) ns_model
     = CheckOk ns_model []
  /\ check_syscall (fd_call 80 9 0x10000 0) (mkEffect (errno_ret EBADF) [] []) ns_model
     = CheckOk ns_model []
  /\ check_syscall (fd_call 23 5 0 0) (mkEffect 6 [] []) ns_model
     = CheckOk (with_cloexec [(6, false)]
                  (with_fds (fd_insert (m_fds ns_model) 6 FdDir) ns_model)) [].
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
     = CheckOk (with_cloexec [(3, false)]
                  (with_fds (fd_insert (m_fds ns_model) 3 (FdChannel 0)) ns_model)) []
  (* the controls *)
  /\ check_syscall (close_range_in 5 5 0) (mkEffect 0 [] []) ns_model
     = CheckOk (with_fds (fd_remove (m_fds ns_model) 5) ns_model) []
  /\ check_syscall (fd_call 24 0 5 0) (mkEffect 5 [] []) ns_model
     = CheckOk (with_cloexec [(5, false)]
                  (with_fds (fd_insert (m_fds ns_model) 5 (FdChannel 0)) ns_model)) [].
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

(* =========================================================================
   dup3 MOVES a regular file ([File.dup3_moves_entry], [State.OAlias])

   Before the move every [dup3] of a regular file declined
   ([File.dup_modeled_entry]).  Now [newfd] takes the entry, offset and
   all, and [oldfd] holds an alias of it, which declines every call but
   close, close_range and F_SETFD/F_GETFD.  Each example carries a
   CONTROL that the text before the move answers alike: a call on a
   table that holds no alias.
   ========================================================================= *)

(** [dup_model] after the launcher's [dup3(3, 0, 0)]: fd 0 holds the
    file "f" one byte in, fd 3 the alias of fd 0, and fd 0's
    close-on-exec bit is known clear. *)
Definition moved_model : Model :=
  with_cloexec [(0, false)]
    (with_fds (fd_insert (fd_insert (m_fds dup_model) 0 (FdFile [102] 1)) 3
                 (FdOpaque (OAlias 0))) dup_model).

(** ...and after the [close_range(3, ~0U, 0)] that follows: the alias
    and the directory at 4 are gone, and fd 0 keeps the file and its
    bit. *)
Definition ranged_model : Model :=
  with_fds [(0, FdFile [102] 1); (1, FdChannel 1); (2, FdChannel 2)] moved_model.

(** [read(fd, 4096, 1)] into one writable byte. *)
Definition read1_in (fd : word) : SyscallInput :=
  mkInput 63 [fd; 4096; 1; 0; 0; 0] (fun _ => None)
    (fun a => if bv_eqb a 4096 then Some 0 else None).

(** THE LAUNCHER'S SEQUENCE.  fd 3 stands for the read-only file a
    launcher holds as its input, at any offset (here 1).
    [dup3(3, 0, 0)] answers 0 and moves the file to fd 0;
    [close_range(3, ~0U, 0)] answers 0, closing the alias and keeping
    its partner; and [read(0, buf, 1)] answers "i", the byte at the
    offset the file had at fd 3, and moves that offset to 2.  "h", the
    byte at offset 0, is refused.  THE CONTROL: [dup3(0, 1, 0)] of the
    channel at 0. *)
Example dup3_moves_the_launcher_s_input_file :
  check_syscall (fd_call 24 3 0 0) (mkEffect 0 [] []) dup_model
  = CheckOk moved_model []
  /\ check_syscall (close_range_in 3 4294967295 0) (mkEffect 0 [] []) moved_model
     = CheckOk ranged_model []
  /\ match check_syscall (read1_in 0) (mkEffect 1 [(4096, [105])] []) ranged_model with
     | CheckOk m [] => fd_lookup (m_fds m) 0 = Some (FdFile [102] 2)
     | _ => False
     end
  /\ check_syscall (read1_in 0) (mkEffect 1 [(4096, [104])] []) ranged_model
     = CheckReject
  (* the control *)
  /\ check_syscall (fd_call 24 0 1 0) (mkEffect 1 [] []) dup_model
     = CheckOk (with_cloexec [(1, false)]
                  (with_fds (fd_insert (m_fds dup_model) 1 (FdChannel 0)) dup_model)) [].
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(** Path bytes "f" at 8192, NUL-terminated. *)
Definition f_path_mem : word -> option byte :=
  fun a => if bv_eqb a 8192 then Some 102
           else if bv_eqb a 8193 then Some 0
           else None.

Definition open_f_in (flags : Z) : SyscallInput :=
  mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 flags; 0; 0; 0] f_path_mem (fun _ => None).

(** THE KEY SETUP.  [openat] of the read-only file "f" with O_CLOEXEC
    answers the lowest free fd, 5, with its bit known set;
    [dup3(5, 7, 0)] moves the file to the key number 7 with its bit
    clear and leaves the alias at 5, whose key stays set;
    [F_SETFD(7, 0)] answers 0; and [F_GETFD(7)] answers 0 and nothing
    else.  THE CONTROL: the same [F_SETFD] and [F_GETFD] on fd 5 straight
    after the [openat]. *)
Example dup3_moves_a_key_whose_bit_reads_clear :
  match check_syscall (open_f_in O_CLOEXEC)
          (with_copyins [(8192, 2%nat)] (mkEffect 5 [] [])) dup_model with
  | CheckOk m1 [] =>
      fd_lookup (m_fds m1) 5 = Some (FdFile [102] 0)
      /\ cloexec_lookup (m_cloexec m1) 5 = Some true
      /\ match check_syscall (fd_call 24 5 7 0) (mkEffect 7 [] []) m1 with
         | CheckOk m2 [] =>
             fd_lookup (m_fds m2) 7 = Some (FdFile [102] 0)
             /\ fd_lookup (m_fds m2) 5 = Some (FdOpaque (OAlias 7))
             /\ cloexec_lookup (m_cloexec m2) 7 = Some false
             /\ cloexec_lookup (m_cloexec m2) 5 = Some true
             /\ match check_syscall (fd_call 25 7 F_SETFD 0) (mkEffect 0 [] []) m2 with
                | CheckOk m3 [] =>
                    check_syscall (fd_call 25 7 F_GETFD 0) (mkEffect 0 [] []) m3
                    = CheckOk m3 []
                    /\ check_syscall (fd_call 25 7 F_GETFD 0) (mkEffect FD_CLOEXEC [] []) m3
                       = CheckReject
                | _ => False
                end
         | _ => False
         end
      (* the control *)
      /\ match check_syscall (fd_call 25 5 F_SETFD 0) (mkEffect 0 [] []) m1 with
         | CheckOk m3 [] =>
             check_syscall (fd_call 25 5 F_GETFD 0) (mkEffect 0 [] []) m3
             = CheckOk m3 []
             /\ check_syscall (fd_call 25 5 F_GETFD 0) (mkEffect FD_CLOEXEC [] []) m3
                = CheckReject
         | _ => False
         end
  | _ => False
  end.
Proof. vm_compute. repeat split; solve [ reflexivity | check_eq ]. Qed.

(** THE PARTNER MAY GO FIRST, and the alias then DANGLES.  On
    [moved_model], [close(0)] answers 0 and leaves the alias at 3;
    [close_range(0, 2, 0)] answers 0 and leaves it too; and [dup3(1, 0,
    0)] onto the partner answers 1 with the channel copied to 0, the
    alias still naming 0.  The dangling alias then closes as any
    descriptor does.  [dup3] FROM the alias declines.  THE CONTROL:
    [close(0)] on [dup_model], which holds no alias, answers alike. *)
Example dup3_partner_close_leaves_the_alias_dangling :
  let m1 := with_cloexec [] (with_fds (fd_remove (m_fds moved_model) 0) moved_model) in
  check_syscall (fd_call 57 0 0 0) (mkEffect 0 [] []) moved_model = CheckOk m1 []
  /\ fd_lookup (m_fds m1) 3 = Some (FdOpaque (OAlias 0))
  /\ check_syscall (fd_call 57 3 0 0) (mkEffect 0 [] []) m1
     = CheckOk (with_fds (fd_remove (m_fds m1) 3) m1) []
  /\ (match check_syscall (close_range_in 0 2 0) (mkEffect 0 [] []) moved_model with
      | CheckOk m2 [] => fd_lookup (m_fds m2) 3 = Some (FdOpaque (OAlias 0))
      | _ => False end)
  /\ (match check_syscall (fd_call 24 1 0 0) (mkEffect 0 [] []) moved_model with
      | CheckOk m2 [] => fd_lookup (m_fds m2) 0 = Some (FdChannel 1)
                         /\ fd_lookup (m_fds m2) 3 = Some (FdOpaque (OAlias 0))
      | _ => False end)
  /\ check_syscall (fd_call 24 3 7 0) (mkEffect 7 [] []) moved_model = CheckUnmodeled
  (* the control *)
  /\ check_syscall (fd_call 57 0 0 0) (mkEffect 0 [] []) dup_model
     = CheckOk (with_fds (fd_remove (m_fds dup_model) 0) dup_model) [].
Proof. vm_compute. repeat split; solve [ reflexivity | check_eq ]. Qed.

(** THE ALIAS DECLINES what would read or move its description: read,
    lseek and fstat, whatever errno the kernel claims.  THE CONTROL: the
    same calls on the partner, fd 0, are answered. *)
Example dup3_alias_declines_the_description :
  check_syscall (read1_in 3) (mkEffect (errno_ret EBADF) [] []) moved_model
  = CheckUnmodeled
  /\ check_syscall (fd_call 62 3 0 0) (mkEffect 0 [] []) moved_model
     = CheckUnmodeled
  /\ check_syscall (fd_call 80 3 0x10000 0) (mkEffect (errno_ret EBADF) [] []) moved_model
     = CheckUnmodeled
  (* the control *)
  /\ check_syscall (fd_call 62 0 0 0) (mkEffect 0 [] []) moved_model
     = CheckOk (with_fds (fd_insert (m_fds moved_model) 0 (FdFile [102] 0)) moved_model) [].
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(** CLOSING THE ALIAS answers 0, drops its entry and touches nothing
    else, after which [close(0)] answers; [close_range(0, 3, 0)], which
    closes partner and alias together, answers 0; [F_SETFD] on the alias
    records its bit, and [F_GETFD] on it, whose bit is unknown, admits
    both answers.  THE CONTROLS, answered alike before the move and
    after: [close(0)] and [close_range(0, 2, 0)] on [dup_model]. *)
Example dup3_alias_close_frees_the_partner :
  check_syscall (fd_call 57 3 0 0) (mkEffect 0 [] []) moved_model
  = CheckOk (with_fds (fd_remove (m_fds moved_model) 3) moved_model) []
  /\ check_syscall (fd_call 57 0 0 0) (mkEffect 0 [] [])
       (with_fds (fd_remove (m_fds moved_model) 3) moved_model)
     = CheckOk (with_cloexec []
                  (with_fds (fd_remove (fd_remove (m_fds moved_model) 3) 0) moved_model)) []
  /\ check_syscall (close_range_in 0 3 0) (mkEffect 0 [] []) moved_model
     = CheckOk (with_cloexec [] (with_fds [(4, FdDir)] moved_model)) []
  /\ check_syscall (fd_call 25 3 F_SETFD FD_CLOEXEC) (mkEffect 0 [] []) moved_model
     = CheckOk (with_cloexec [(3, true); (0, false)] moved_model) []
  /\ check_syscall (fd_call 25 3 F_GETFD 0) (mkEffect 0 [] []) moved_model
     = CheckOk moved_model []
  /\ check_syscall (fd_call 25 3 F_GETFD 0) (mkEffect FD_CLOEXEC [] []) moved_model
     = CheckOk moved_model []
  (* the controls *)
  /\ check_syscall (fd_call 57 0 0 0) (mkEffect 0 [] []) dup_model
     = CheckOk (with_fds (fd_remove (m_fds dup_model) 0) dup_model) []
  /\ check_syscall (close_range_in 0 2 0) (mkEffect 0 [] []) dup_model
     = CheckOk (with_fds [(3, FdFile [102] 1); (4, FdDir)] dup_model) [].
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

Definition clone_sigchld_in : SyscallInput :=
  mkInput 220 [Z_to_bv 64 SIGCHLD; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None).

(** CLONE DECLINES WHILE AN ALIAS IS OPEN ([Kernel.Fork.clone_no_shared_file_b];
    [clone3] shares the gate): the child would hold a third descriptor
    of the moved file's description.  On [moved_model] the partner's
    regular file declines the clone as well, so the gate is also shown
    on a table holding the alias and a channel alone.  THE CONTROL: the
    same clone on the channel alone answers a pid. *)
Example clone_declines_with_an_alias :
  check_syscall clone_sigchld_in (mkEffect 4242 [] []) moved_model = CheckUnmodeled
  /\ clone_no_shared_file_b [(0, FdChannel 0); (3, FdOpaque (OAlias 0))] = false
  /\ check_syscall clone_sigchld_in (mkEffect 4242 [] [])
       (with_fds [(0, FdChannel 0); (3, FdOpaque (OAlias 0))] dup_model)
     = CheckUnmodeled
  (* the control *)
  /\ clone_no_shared_file_b [(0, FdChannel 0)] = true
  /\ check_syscall clone_sigchld_in (mkEffect 4242 [] [])
       (with_fds [(0, FdChannel 0)] dup_model)
     = CheckOk (with_child (Z_to_bv 64 4242) (with_fds [(0, FdChannel 0)] dup_model)) [].
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(** FLOCK DECLINES WHILE AN ALIAS EXISTS ([Locks.path_openers] counts
    every alias as an opener of every path): a description an alias
    keeps alive may hold a lock no entry shows.  THE CONTROL, answered
    alike before the move and after: the same LOCK_EX on [dup_model]'s
    sole opener of "f". *)
Example flock_declines_with_an_alias :
  check_syscall (fd_call 32 0 2 0) (mkEffect 0 [] []) moved_model = CheckUnmodeled
  (* the control *)
  /\ check_syscall (fd_call 32 3 2 0) (mkEffect 0 [] []) dup_model
     = CheckOk dup_model [].
Proof. split; solve [ vm_compute; reflexivity | check_eq ]. Qed.

(** THE /proc/self/fd LISTING NAMES THE ALIAS: [Readdir.procfd_plan]
    lists every key of the table, the alias at 3 included, as a
    descriptor entry, whose record [Readdir.dirent64_rec_ok] types
    [DT_LNK] (or [DT_UNKNOWN] with [d_ino] 1) whatever the kind.  THE
    CONTROL: the same entry for the file at 3 of [dup_model]. *)
Example procfd_listing_names_the_alias :
  In (mkProcfdEnt (procfd_name 3) 5 true) (procfd_plan (m_fds moved_model) 0)
  (* the control *)
  /\ In (mkProcfdEnt (procfd_name 3) 5 true) (procfd_plan (m_fds dup_model) 0).
Proof.
  split; vm_compute; repeat (first [left; solve [ reflexivity | check_eq ] | right]).
Qed.

(** "/proc/self/fd/3" and "/proc/self/fd/4". *)
Definition s_self_fd3 : list byte :=
  [47; 112; 114; 111; 99; 47; 115; 101; 108; 102; 47; 102; 100; 47; 51].
Definition s_self_fd4 : list byte :=
  [47; 112; 114; 111; 99; 47; 115; 101; 108; 102; 47; 102; 100; 47; 52].

Definition proc_fd_open_in (bs : list byte) : SyscallInput :=
  mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 0x208000; 0; 0; 0]
    (bytes_at 8192 (bs ++ [0])) (fun _ => None).

(** NO OPEN THROUGH THE ALIAS'S LINK, AND NO READLINK OF IT: O_PATH on
    "/proc/self/fd/3", where 3 is the alias, declines whatever it
    answers ([Open.proc_fd_alias_b]), and so does [readlinkat] of the
    name ([Stat.readlinkat_spec] declines every procfs name).  THE
    CONTROLS, answered alike before the move and after: the same O_PATH
    open of "/proc/self/fd/4", the directory, and [readlinkat] of "f",
    a regular file, -EINVAL. *)
Example alias_link_declines_open_and_readlink :
  check_syscall (proc_fd_open_in s_self_fd3)
    (with_copyins [(8192, 16%nat)] (mkEffect (errno_ret ENOENT) [] [])) moved_model
  = CheckUnmodeled
  /\ check_syscall (rl_in s_self_fd3 64)
       (with_copyins [(0x2000, 16%nat)] (mkEffect (errno_ret EINVAL) [] [])) moved_model
     = CheckUnmodeled
  (* the controls *)
  /\ check_syscall (proc_fd_open_in s_self_fd4)
       (with_copyins [(8192, 16%nat)] (mkEffect (errno_ret ENOENT) [] [])) moved_model
     = CheckOk moved_model []
  /\ check_syscall (rl_in [102] 64)
       (with_copyins [(0x2000, 2%nat)] (mkEffect (errno_ret EINVAL) [] [])) moved_model
     = CheckOk moved_model [].
Proof. repeat split; solve [ vm_compute; reflexivity | check_eq ]. Qed.

(** THE ALIAS HAS ITS OWN CLOSE-ON-EXEC BIT: [F_SETFD] on the alias
    writes the alias's key and not its partner's, and [F_GETFD] on each
    then answers its own.  THE CONTROL: [F_GETFD] on the partner before
    the [F_SETFD], answered alike before and after. *)
Example alias_close_on_exec_bit_is_its_own :
  let m1 := with_cloexec [(3, true); (0, false)] moved_model in
  check_syscall (fd_call 25 3 F_SETFD FD_CLOEXEC) (mkEffect 0 [] []) moved_model
  = CheckOk m1 []
  /\ check_syscall (fd_call 25 3 F_GETFD 0) (mkEffect FD_CLOEXEC [] []) m1 = CheckOk m1 []
  /\ check_syscall (fd_call 25 3 F_GETFD 0) (mkEffect 0 [] []) m1 = CheckReject
  /\ check_syscall (fd_call 25 0 F_GETFD 0) (mkEffect 0 [] []) m1 = CheckOk m1 []
  /\ check_syscall (fd_call 25 0 F_GETFD 0) (mkEffect FD_CLOEXEC [] []) m1 = CheckReject
  (* the control *)
  /\ check_syscall (fd_call 25 0 F_GETFD 0) (mkEffect 0 [] []) moved_model
     = CheckOk moved_model [].
Proof. repeat split; solve [ vm_compute; reflexivity | check_eq ]. Qed.

(** AN UNLINK UNDER A DANGLING ALIAS: once the partner of the alias at 3
    closed, nothing in the table but the alias holds "f", and [unlinkat]
    of it is answered and drops the key ([Namei.fd_names_path] says why
    no answer of the alias can tell that from Linux keeping the inode
    alive).  THE CONTROL: while the partner lives the same unlink
    declines, as it does on [dup_model], whose fd 3 reads "f". *)
Definition unlink_f_in : SyscallInput :=
  mkInput 35 [AT_FDCWD; 0x2000; 0; 0; 0; 0] (bytes_at 0x2000 [102; 0]) (fun _ => None).

Example unlink_under_a_dangling_alias :
  let m1 := with_cloexec [] (with_fds (fd_remove (m_fds moved_model) 0) moved_model) in
  (match check_syscall unlink_f_in (with_copyins [(0x2000, 2%nat)] (mkEffect 0 [] [])) m1 with
   | CheckOk m2 [] => fs_lookup (m_fs m2) [102] = None
                      /\ fd_lookup (m_fds m2) 3 = Some (FdOpaque (OAlias 0))
   | _ => False end)
  (* the controls *)
  /\ check_syscall unlink_f_in (with_copyins [(0x2000, 2%nat)] (mkEffect 0 [] [])) moved_model
     = CheckUnmodeled
  /\ check_syscall unlink_f_in (with_copyins [(0x2000, 2%nat)] (mkEffect 0 [] [])) dup_model
     = CheckUnmodeled.
Proof. vm_compute. repeat split; solve [ reflexivity | check_eq ]. Qed.

(* =========================================================================
   The harness's descriptor setup and the launcher's hand-off

   [hand(file, fd)] is [o = openat(AT_FDCWD, file, O_RDONLY|O_CLOEXEC)],
   then [fcntl(o, F_SETFD, 0)] if [o = fd], else [dup3(o, fd, 0)] and
   [close(o)].  The harness hands the input file first, to [stdin_fd] =
   3, which [openat] gives at once, then [fstat]s it, then hands a key
   to 7 ([openat] gives 4).  The launcher then [dup3(stdin_fd, 0, 0)]s
   and [close_range(3, ~0U, 0)]s.  At the end [fstat(0)] is answered from
   the file and [fcntl(stdin_fd, F_GETFD)] is -EBADF.
   ========================================================================= *)

(** "f" = "hi" is the input, "k" = "x" the key. *)
Definition hand_model : Model :=
  init_model [] 0 0 demo_sp demo_limit
    (demo_input [([102], [104; 105]); ([107], [120])] IEof).

Definition hand_open_in (name : byte) : SyscallInput :=
  mkInput 56 [AT_FDCWD; 8192; Z_to_bv 64 O_CLOEXEC; 0; 0; 0]
    (bytes_at 8192 [name; 0]) (fun _ => None).

Definition hand_fstat_in (fd : word) : SyscallInput :=
  mkInput 80 [fd; 4096; 0; 0; 0; 0] (fun _ => None) stat_out.

(** The truthful [struct stat] of the two-byte file "f". *)
Definition f_stat : list byte := stat_of 4711 S_IFREG 2 8 1700000000.

Example harness_setup_and_launcher_hand_off :
  match check_syscall (hand_open_in 102)
          (with_copyins [(8192, 2%nat)] (mkEffect 3 [] [])) hand_model with
  | CheckOk m1 [] =>
    match check_syscall (fd_call 25 3 F_SETFD 0) (mkEffect 0 [] []) m1 with
    | CheckOk m2 [] =>
      match check_syscall (hand_fstat_in 3) (mkEffect 0 [(4096, f_stat)] []) m2 with
      | CheckOk m3 [] =>
        match check_syscall (hand_open_in 107)
                (with_copyins [(8192, 2%nat)] (mkEffect 4 [] [])) m3 with
        | CheckOk m4 [] =>
          match check_syscall (fd_call 24 4 7 0) (mkEffect 7 [] []) m4 with
          | CheckOk m5 [] =>
            match check_syscall (fd_call 57 4 0 0) (mkEffect 0 [] []) m5 with
            | CheckOk m6 [] =>
              (* the launcher *)
              match check_syscall (fd_call 24 3 0 0) (mkEffect 0 [] []) m6 with
              | CheckOk m7 [] =>
                match check_syscall (close_range_in 3 4294967295 0) (mkEffect 0 [] []) m7 with
                | CheckOk m8 [] =>
                    (* the harness's checks *)
                    (match check_syscall (hand_fstat_in 0)
                             (mkEffect 0 [(4096, f_stat)] []) m8 with
                     | CheckOk _ [] => True
                     | _ => False end)
                    /\ check_syscall (hand_fstat_in 0)
                         (mkEffect 0 [(4096, stat_of 4711 S_IFREG 3 8 1700000000)] []) m8
                       = CheckReject
                    /\ check_syscall (fd_call 25 3 F_GETFD 0)
                         (mkEffect (errno_ret EBADF) [] []) m8
                       = CheckOk m8 []
                    /\ fd_lookup (m_fds m8) 0 = Some (FdFile [102] 0)
                    /\ cloexec_lookup (m_cloexec m8) 0 = Some false
                    (* the key's own checks, before the launcher closes it *)
                    /\ fd_lookup (m_fds m6) 7 = Some (FdFile [107] 0)
                    /\ fd_lookup (m_fds m6) 4 = None
                    /\ check_syscall (fd_call 25 7 F_GETFD 0) (mkEffect 0 [] []) m6
                       = CheckOk m6 []
                | _ => False end
              | _ => False end
            | _ => False end
          | _ => False end
        | _ => False end
      | _ => False end
    | _ => False end
  | _ => False end.
Proof. vm_compute. repeat split; solve [ reflexivity | check_eq ]. Qed.

(** THE CONTROL: the same hand-off of a CHANNEL, which the text before
    the move answered alike: [dup3(1, 0, 0)] copies the channel and
    leaves fd 1 as it was. *)
Example hand_off_of_a_channel_copies :
  check_syscall (fd_call 24 1 0 0) (mkEffect 0 [] []) hand_model
  = CheckOk (with_cloexec (cloexec_set (m_cloexec hand_model) 0 false)
               (with_fds (fd_insert (m_fds hand_model) 0 (FdChannel 1)) hand_model)) [].
Proof. check_eq. Qed.

(* =========================================================================
   [State.FdSeqpacket]: one end of an AF_UNIX SOCK_SEQPACKET pair.  As for
   [State.ONsFile] above, these examples span the descriptor-level calls,
   because what they pin is the KIND's rule: an end answers what a socket
   answers from the socket inode and [socket_file_ops] alone, and every
   call whose answer would need more of the end (its queue, a second
   reference to it) declines.
   ========================================================================= *)

(** fd 3 and fd 4 are the two ends of pair 0, fd 5 the directory.  The
    lowest free fd is 6. *)
Definition seqp_model : Model :=
  mkModel [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
           (3, FdSeqpacket 0 false seq_fresh); (4, FdSeqpacket 0 true seq_fresh);
           (5, FdDir)]
    (mkVmMaps [] [] 0 0 demo_limit) IEof [] None None None.

(** D1.  DUP AND DUP3 OF AN END DECLINE ([File.dup_modeled_entry]): the
    socket is released only when its LAST reference goes, so after a dup
    a close of one descriptor must not end the peer's reads, and the
    model keeps one descriptor per end.  THE CONTROL: dup of the
    directory at 5 installs a copy at 6. *)
Example seqpacket_end_dup_declines :
  check_syscall (fd_call 23 3 0 0) (mkEffect 6 [] []) seqp_model = CheckUnmodeled
  /\ check_syscall (fd_call 23 4 0 0) (mkEffect 6 [] []) seqp_model = CheckUnmodeled
  /\ check_syscall (fd_call 24 3 7 0) (mkEffect 7 [] []) seqp_model = CheckUnmodeled
  /\ check_syscall (fd_call 23 5 0 0) (mkEffect 6 [] []) seqp_model
     = CheckOk (with_cloexec [(6, false)]
                  (with_fds (fd_insert (m_fds seqp_model) 6 FdDir) seqp_model)) [].
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.

(** DECLINED on an end: read, write, fstat, fcntl(F_GETFL),
    ioctl(TIOCGWINSZ) and lseek(SEEK_SET), whatever errno the kernel
    claims. *)
Example seqpacket_end_declines_the_kind_dependent_calls :
  check_syscall (fd_call 63 3 0x10000 16) (mkEffect (errno_ret EBADF) [] []) seqp_model
  = CheckUnmodeled
  /\ check_syscall (fd_call 64 3 0x10000 16) (mkEffect (errno_ret EBADF) [] []) seqp_model
     = CheckUnmodeled
  /\ check_syscall (fd_call 80 3 0x10000 0) (mkEffect (errno_ret EBADF) [] []) seqp_model
     = CheckUnmodeled
  /\ check_syscall (fd_call 25 3 F_GETFL 0) (mkEffect 2 [] []) seqp_model
     = CheckUnmodeled
  /\ check_syscall (fd_call 29 3 TIOCGWINSZ 0x10000) (mkEffect (errno_ret ENOTTY) [] [])
       seqp_model
     = CheckUnmodeled
  /\ check_syscall (fd_call 62 3 0 0) (mkEffect (errno_ret ESPIPE) [] []) seqp_model
     = CheckUnmodeled.
Proof. repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity. Qed.

(** ANSWERED on an end, each the answer an AF_INET socket gets: ftruncate
    is -EINVAL (the inode is S_IFSOCK, net/socket.c:644, and
    [do_ftruncate] tests S_ISREG first, fs/open.c:175, v6.18.46); fsync is
    -EINVAL ([socket_file_ops], net/socket.c:156, has no [.fsync]:
    fs/sync.c:183-184); getdents64 is -ENOTDIR (nor an [.iterate_shared]).
    And the kind-blind calls: fcntl(F_SETFD) is 0, close is 0 and removes
    the entry.  THE CONTROLS: 0 for each of the three errnos. *)
Example seqpacket_end_answers_the_socket_errnos :
  check_syscall (fd_call 46 3 0 0) (mkEffect (errno_ret EINVAL) [] []) seqp_model
  = CheckOk seqp_model []
  /\ check_syscall (fd_call 46 3 0 0) (mkEffect 0 [] []) seqp_model = CheckReject
  /\ check_syscall (fd_call 82 3 0 0) (mkEffect (errno_ret EINVAL) [] []) seqp_model
     = CheckOk seqp_model []
  /\ check_syscall (fd_call 82 3 0 0) (mkEffect 0 [] []) seqp_model = CheckReject
  /\ check_syscall (fd_call 61 3 0x10000 4096) (mkEffect (errno_ret ENOTDIR) [] [])
       seqp_model
     = CheckOk seqp_model []
  /\ check_syscall (fd_call 61 3 0x10000 4096) (mkEffect 0 [] []) seqp_model
     = CheckReject
  /\ check_syscall (fd_call 25 3 F_SETFD FD_CLOEXEC) (mkEffect 0 [] []) seqp_model
     = CheckOk (with_cloexec [(3, true)] seqp_model) []
  /\ check_syscall (fd_call 57 3 0 0) (mkEffect 0 [] []) seqp_model
     = CheckOk (with_fds (fd_remove (m_fds seqp_model) 3) seqp_model) [].
Proof. repeat match goal with |- _ /\ _ => split end; check_eq. Qed.
(** One AF_UNIX stream pair beside the three channels: id 0, side
    [false] at fd 3 and side [true] at fd 4, both empty, blocking and
    open both ways.  The lowest free fd is 5. *)
Definition dup_pair_end : StreamEnd :=
  mkStreamEnd [] false 212992%Z 212992%Z false false RsUnknown.

Definition dup_pair_model : Model :=
  mkModel [(0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
           (3, FdStream 0 false dup_pair_end); (4, FdStream 0 true dup_pair_end)]
    (mkVmMaps [] [] 0 0 demo_limit) IEof [] None None None.

(** A STREAM-PAIR END IS NEVER DUPLICATED.  [File.dup_modeled_entry]
    declines it as a source -- a second fd naming one end would make a
    close of either look like the peer going away, and would let two
    copies of its O_NONBLOCK drift apart -- so dup(3) and dup3(3, 7)
    decline for every claimed return. *)
Lemma dup_and_dup3_decline_on_a_stream_end : forall eff,
  check_syscall (mkInput 23 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    eff dup_pair_model
  = CheckUnmodeled
  /\ check_syscall (mkInput 24 [3; 7; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       eff dup_pair_model
     = CheckUnmodeled.
Proof. intro eff. split; vm_compute; reflexivity. Qed.

(** ...and the twin in the same model: dup(0), a channel, answers the
    lowest free fd, so the decline above is about the stream end and
    not about the table it sits in. *)
Example dup_of_a_channel_beside_the_pair_answers :
  check_syscall (mkInput 23 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 5 [] []) dup_pair_model
  = CheckOk (with_cloexec [(5, false)]
               (with_fds (fd_insert (m_fds dup_pair_model) 5 (FdChannel 0)) dup_pair_model)) [].
Proof. check_eq. Qed.
