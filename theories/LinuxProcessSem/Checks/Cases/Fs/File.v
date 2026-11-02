(** * LinuxProcessSem.Checks.Cases.Fs.File — worked examples over dup (23), dup3 (24)

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
  = CheckOk (with_fds (fd_insert (m_fds dup_pair_model) 5 (FdChannel 0)) dup_pair_model) [].
Proof. check_eq. Qed.
