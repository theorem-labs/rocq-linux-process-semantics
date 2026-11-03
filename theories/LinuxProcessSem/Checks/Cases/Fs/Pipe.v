(** * LinuxProcessSem.Checks.Cases.Fs.Pipe — worked examples over pipe2 (59) and a pipe-end fd

    Mirrors [Sys/Fs/Pipe.v], which answers to Linux [fs/pipe.c]: this
    file holds the worked examples for the syscalls defined there, and
    the pipe-end arms of the vectored calls that no truthful run can
    reach.

    It also carries the arms [State.FdPipe] forces at fd-kind dispatch
    sites OUTSIDE fs/pipe.c, because a constructor is answered wherever
    the tree dispatches on fd kind and those answers have nowhere else
    to be pinned: [Sys/Fs/Select.v], [Sys/Fs/Stat.v], [Sys/Fs/Ioctl.v],
    [Sys/Fs/Open.v], [Sys/Fs/File.v], [Sys/Fs/Fcntl.v],
    [Sys/Fs/Namei.v], [Sys/Kernel/Fork.v] and [Sys/Net/Socket.v].

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary.

    THE DECLINES HERE ARE THE SITES THAT DO NOT ANSWER FOR A PIPE END.
    A pipe end is reachable from a run — [Pipe.pipe2_spec] constructs
    one — so these are ordinary examples rather than hand-built
    unreachable ones.  Where an arm declines it is because this development has no
    derivation for that site (whether a pipe end is pollable, what
    [fstat] reports, what [clone] or [dup] may do with one), not because
    no pipe exists.

    Both directions are pinned throughout.  For an arm that ANSWERS, the
    positive pin names the answer and the negative pin offers a
    different one and requires [CheckReject].  For an arm that DECLINES,
    a [CheckReject] pin would say nothing — a declining spec rejects
    nothing — so the negative pin instead OFFERS THE ANSWER THE ARM
    REFUSED TO GIVE and requires [CheckUnmodeled], which is the shape
    [Checks/ExecutableSpecs.v]'s completeness biconditional makes
    load-bearing: it separates "the model declines" from "the model
    agrees", which a positive pin alone cannot. *)

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

(** A model holding BOTH ENDS of one pipe, plus a regular file for
    contrast.  fd 3 is the read end and fd 4 the write end of pipe id 0
    — the [fd[0] = fdr], [fd[1] = fdw] split [pipe2] itself makes
    (fs/pipe.c [__do_pipe_flags], v6.18.46).  fd 5 is an [FdFileW] so
    the checks below can show a pipe end answering DIFFERENTLY from a
    file at the same site rather than merely answering.

    The two ends carry the SAME id on purpose: a check that used two
    ids could not tell a spec that reads [writer] from one that reads
    [id].

    THIS FIXTURE CARRIES NO [m_pipes] ENTRY, unlike [one_pipe_model]
    below, and every pin taken over it is at a site that never reaches
    the queue: the fd's KIND decides the answer and the bytes behind it
    do not.  A pin that needs the queue belongs on [one_pipe_model],
    which [pipe2_spec] builds and which therefore satisfies the
    table invariant [Pipe.pipe2_spec] establishes. *)
Definition pipe_model : Model :=
  mkModel
    [ (0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
      (3, FdPipe 0 false); (4, FdPipe 0 true);
      (5, FdFileW [102] 0) ]
    (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [120])] None None None.

(** WHY THE DECLINES BELOW CARRY A CONTRAST.  A pin reading
    [CheckUnmodeled] says much less than it looks like it says: it also
    passes when the call declines for a reason having nothing to do with
    the fd — a syscall number outside [Specs.modeled_sysnos], an
    argument shape the spec refuses before it reaches the fd at all.
    Such a pin holds forever and pins nothing.

    So every decline that can have one is paired with the SAME call on a
    NEIGHBOURING fd of this same model, answering: fd 0 the channel, fd 5
    the write-only file.  That fixes the syscall number, the argument
    shape and the model, and leaves the fd's kind as the only thing that
    differs — which is what the decline is supposed to be about.

    Two pins show why.  The clone one passes SIGCHLD, because with
    [flags = 0] [Fork.clone_spec] tests [clone_fork_flags_b] before it
    ever looks at the descriptor table.  And pselect6's contrast is
    taken at [Select.pselect_core], because at the syscall the timeout
    and signal-mask arguments could decide the gap. *)

(* =========================================================================
   The arms that ANSWER: -ENOTTY, -EINVAL, -ENOTSOCK
   ========================================================================= *)

(** ioctl (29) — PATTERN-CONFORMANCE, and the pin that says so: a pipe
    end answers each of the eight terminal-only requests exactly as
    every other open fd kind does.  [pipe_ioctl] takes its default arm
    for all eight and returns -ENOIOCTLCMD, which [vfs_ioctl] maps to
    -ENOTTY (fs/pipe.c, fs/ioctl.c, v6.18.46). *)
Example ioctl_on_a_pipe_end_is_enotty :
  Forall (fun req =>
    check_syscall (mkInput 29 [3; req; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
      (mkEffect (errno_ret ENOTTY) [] []) pipe_model = CheckOk pipe_model []
    /\ check_syscall (mkInput 29 [4; req; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
         (mkEffect (errno_ret ENOTTY) [] []) pipe_model = CheckOk pipe_model [])
    [TCGETS; TCSETS; TIOCSCTTY; TIOCGWINSZ;
     TIOCSWINSZ; TIOCNOTTY; TIOCGPTN; TIOCSPTLCK].
Proof. repeat constructor; check_eq. Qed.

(** ...and the negative half: a kernel claiming SUCCESS for one of them
    is refused, so the pin above is a claim rather than an admission. *)
Example ioctl_on_a_pipe_end_rejects_success :
  check_syscall (mkInput 29 [3; TIOCGWINSZ; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) pipe_model = CheckReject
  /\ check_syscall (mkInput 29 [4; TIOCGWINSZ; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) pipe_model = CheckReject.
Proof. repeat split; check_eq. Qed.

(** ...and a request outside the eight still declines on a pipe end, as
    on every other kind — the conformance is to the WHOLE arm, not to
    its -ENOTTY half. *)
Example ioctl_other_request_on_a_pipe_end_declines :
  check_syscall (mkInput 29 [3; Z_to_bv 64 21531; 4096; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) pipe_model = CheckUnmodeled.   (* FIONREAD 0x541B *)
Proof. check_eq. Qed.

(** ftruncate (46) — PATTERN-CONFORMANCE with the four other non-[FdFileW]
    kinds: a pipe inode is S_IFIFO, so [do_ftruncate]'s
    [!S_ISREG(inode->i_mode) || !(f_mode & FMODE_WRITE)] answers -EINVAL
    on its FIRST disjunct (fs/open.c, v6.18.46).  BOTH ENDS, which is
    what makes the point: the write end holds FMODE_WRITE and is still
    -EINVAL, so the answer comes from S_ISREG rather than from the mode. *)
Example ftruncate_on_a_pipe_end_is_einval :
  check_syscall (mkInput 46 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) pipe_model = CheckOk pipe_model []
  /\ check_syscall (mkInput 46 [4; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) pipe_model = CheckOk pipe_model [].
Proof. repeat split; check_eq. Qed.

(** The negative half, in the sharpest available form: the write end is
    refused the SUCCESS that the [FdFileW] at fd 5 really gets, so this
    separates "a writable fd" from "a writable REGULAR FILE fd". *)
Example ftruncate_on_a_pipe_write_end_rejects_success :
  check_syscall (mkInput 46 [4; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) pipe_model = CheckReject
  /\ check_syscall (mkInput 46 [4; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) pipe_model = CheckReject.
Proof. repeat split; check_eq. Qed.

(** The socket family — PATTERN-CONFORMANCE with every other non-socket
    kind.  [sock_from_file] returns NULL unless the file's [f_op] is
    [socket_file_ops], and a pipe end's is [pipeanon_fops], so -ENOTSOCK
    (net/socket.c, fs/pipe.c, v6.18.46).  bind (200) reaches it through
    [Net.Socket.bind_spec]'s open-fd arm and recvfrom (207) through
    [Net.Socket.sockfd_lookup_errno], which are the two SHAPES the file
    has — one a wildcard over non-socket kinds, one an enumeration. *)
Example socket_calls_on_a_pipe_end_are_enotsock :
  check_syscall (mkInput 200 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ENOTSOCK) [] []) pipe_model = CheckOk pipe_model []
  /\ check_syscall (mkInput 207 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ENOTSOCK) [] []) pipe_model = CheckOk pipe_model []
  /\ check_syscall (mkInput 207 [4; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ENOTSOCK) [] []) pipe_model = CheckOk pipe_model [].
Proof. repeat split; check_eq. Qed.

(** The negative half, and the errno that matters: -EBADF is what an fd
    that is NOT OPEN gets, so refusing it here pins that a pipe end is
    an open descriptor which merely is not a socket. *)
Example socket_calls_on_a_pipe_end_reject_ebadf :
  check_syscall (mkInput 207 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EBADF) [] []) pipe_model = CheckReject
  /\ check_syscall (mkInput 200 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) pipe_model = CheckReject.
Proof. repeat split; check_eq. Qed.

(* =========================================================================
   The arms that DECLINE

   Each pin below OFFERS the answer the arm refused and requires
   [CheckUnmodeled].  That is the negative direction here: an arm that
   had quietly acquired the answer would return [CheckOk] and fail the
   pin, and one that answered something ELSE would return [CheckReject]
   and fail it too.
   ========================================================================= *)

(** readv (65) — THE GATE, and the pin that guards [readv_spec]'s
    split.

    [readable_fd] hands a pipe READ end a [RdPipe] and turns the WRITE
    end away, so the two ends part company here.  The write end's [None]
    becomes the kernel's own -EBADF, exact rather than a gap; the read
    end never reaches that arm at all.

    THE SECOND CONJUNCT IS THE WHOLE POINT.  Offer -EBADF on the read end
    and it is REFUSED, because the read end passes FMODE_READ (O_RDONLY,
    [create_pipe_files]).  A gate that answered [None] for it would make
    that -EBADF admissible, which is the confidently wrong modeled answer
    [readable_fd]'s own socket paragraph describes; this conjunct fails
    the moment anything puts the read end back on the -EBADF side.

    What the read end answers INSTEAD is deliberately not pinned here:
    past the gate it imports the descriptor array, and on this unreadable
    vector the answer carries a copy-in ledger this file would have to
    spell out in full. *)
Example readv_pipe_gate_splits_the_two_ends :
  (* the WRITE end is O_WRONLY: a real -EBADF, before any iovec is read *)
  check_syscall (mkInput 65 [4; 4096; 1; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EBADF) [] []) pipe_model = CheckOk pipe_model []
  (* the READ end passes the gate, so -EBADF is refused there *)
  /\ check_syscall (mkInput 65 [3; 4096; 1; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) pipe_model = CheckReject
  (* the contrast: a write-only FILE really does fail the gate, so its
     -EBADF stands — the refusal above is about the pipe end's direction
     and not about readv *)
  /\ check_syscall (mkInput 65 [5; 4096; 1; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) pipe_model = CheckOk pipe_model [].
Proof. repeat split; check_eq. Qed.

(** lseek (62) — -ESPIPE on both ends, and the ordering beside it.
    [vfs_llseek] answers -ESPIPE when FMODE_LSEEK is absent, and an
    anonymous pipe misses that bit twice over; see
    [ReadWrite.lseek_spec]'s pipe arm for the derivation.

    The whence error still comes FIRST, and the second and third
    conjuncts pin that ordering: [ksys_lseek] tests [whence <= SEEK_MAX]
    before the fd's kind is consulted, so a bad whence on a pipe end is
    -EINVAL and NOT -ESPIPE. *)
Example lseek_on_a_pipe_end_is_espipe_but_whence_wins :
  check_syscall (mkInput 62 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret ESPIPE) [] []) pipe_model = CheckOk pipe_model []
  /\ check_syscall (mkInput 62 [4; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ESPIPE) [] []) pipe_model = CheckOk pipe_model []
  (* the negative half: a successful seek is refused *)
  /\ check_syscall (mkInput 62 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) pipe_model = CheckReject
  /\ check_syscall (mkInput 62 [3; 0; 42; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) pipe_model = CheckOk pipe_model []
  /\ check_syscall (mkInput 62 [3; 0; 42; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ESPIPE) [] []) pipe_model = CheckReject.
Proof. repeat split; check_eq. Qed.

(** fstat (80) — the decline every open-fd kind takes here, so this arm
    is uniform-pattern and fail-closed at once.  The offer is a plain
    success, which is what an arm that had started inventing [struct
    stat] fields would produce.

    NO CONTRAST IS AVAILABLE and none is missing: [Stat.fstat_spec]
    declines on all six open kinds, so there is no fd in any model that
    answers here.  What keeps the pin from being vacuous is the third
    conjunct: fstat on a CLOSED fd is a real -EBADF, so the number 80
    reaches a modeled arm and the declines above are the arm's answer
    rather than the dispatcher's fallback. *)
Example fstat_on_a_pipe_end_declines :
  check_syscall (mkInput 80 [3; 4096; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) pipe_model = CheckUnmodeled
  /\ check_syscall (mkInput 80 [4; 4096; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) pipe_model = CheckUnmodeled
  /\ check_syscall (mkInput 80 [9; 4096; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) pipe_model = CheckOk pipe_model [].
Proof. repeat split; check_eq. Qed.

(** fsync (82) and fdatasync (83) — -EINVAL on both ends, because
    neither file-operations table an anonymous pipe can carry defines
    [.fsync], so [vfs_fsync_range]'s opening
    [if (!file->f_op->fsync) return -EINVAL] fires before anything else
    and before the [datasync] read (see [Sync.fsync_spec]'s header).

    THE DIRECTORY ARM IS THE CONTRAST WORTH HAVING, and the last
    conjunct is it: three of this site's kinds answer 0, so -EINVAL is
    not the answer a pipe end could have inherited by being in the
    majority. *)
Example fsync_on_a_pipe_end_is_einval :
  check_syscall (mkInput 82 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EINVAL) [] []) pipe_model = CheckOk pipe_model []
  /\ check_syscall (mkInput 83 [4; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) pipe_model = CheckOk pipe_model []
  (* the negative half: the success three other kinds get is refused here *)
  /\ check_syscall (mkInput 82 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) pipe_model = CheckReject
  (* the same call on the CHANNEL at fd 0 is -EINVAL too... *)
  /\ check_syscall (mkInput 82 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) pipe_model = CheckOk pipe_model []
  (* ...while the FILE at fd 5 succeeds, so the errno is per-kind *)
  /\ check_syscall (mkInput 82 [5; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) pipe_model = CheckOk pipe_model [].
Proof. repeat split; check_eq. Qed.

(** dup (23) and dup3 (24) — the offer is the ordinary dup success, a
    second descriptor at the lowest free fd.  [File.dup_modeled_entry]
    declines a pipe end because duplicating one needs an end COUNT the
    model does not keep; a change that copied the entry instead would
    make these [CheckOk]. *)
Example dup_of_a_pipe_end_declines :
  check_syscall (mkInput 23 [3; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 6 [] []) pipe_model = CheckUnmodeled
  /\ check_syscall (mkInput 23 [4; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 6 [] []) pipe_model = CheckUnmodeled
  /\ check_syscall (mkInput 24 [3; 9; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 9 [] []) pipe_model = CheckUnmodeled
  (* the contrast: duplicating the CHANNEL at fd 0 is modeled, and lands
     at the lowest free fd — so [dup] itself works on this model and the
     declines above are [File.dup_modeled_entry]'s answer *)
  /\ check_syscall (mkInput 23 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 6 [] []) pipe_model
     = CheckOk (with_fds (fd_insert (m_fds pipe_model) 6 (FdChannel 0))
                  pipe_model) [].
Proof. repeat split; check_eq. Qed.

(** fcntl (25), F_SETFL — THE ENUMERATION, pinned from both sides, and
    the one arm in this file where a wildcard would be an unsound ACCEPT
    rather than a gap.

    With a [| _ => Z.eqb ... 0] catch-all in [Fcntl.setfl_noop_on], a
    pipe end would fall into it and be told F_SETFL changes nothing
    here — [CheckOk] with a 0.  It declines instead.  The third conjunct
    is what keeps the enumeration honest: the same call on the [FdFileW]
    at fd 5 STILL answers 0, so the enumeration narrows the arm exactly
    at the pipe end and nowhere else. *)
Example fcntl_setfl_on_a_pipe_end_declines :
  check_syscall (mkInput 25 [3; F_SETFL; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) pipe_model = CheckUnmodeled
  /\ check_syscall (mkInput 25 [4; F_SETFL; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) pipe_model = CheckUnmodeled
  /\ check_syscall (mkInput 25 [5; F_SETFL; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) pipe_model = CheckOk pipe_model [].
Proof. repeat split; check_eq. Qed.

(** ...while F_SETFD is KIND-BLIND by construction — [Fcntl.fcntl_spec]
    answers it before it looks at the entry at all — so a pipe end gets
    the same 0 every other fd does.  Pinned because "the pipe end
    declines at fcntl" would otherwise read as covering this too. *)
Example fcntl_setfd_on_a_pipe_end_is_zero :
  check_syscall (mkInput 25 [3; F_SETFD; 1; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) pipe_model = CheckOk pipe_model []
  /\ check_syscall (mkInput 25 [3; F_SETFD; 1; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) pipe_model = CheckReject.
Proof. repeat split; check_eq. Qed.

(* =========================================================================
   The two arms that are predicates rather than syscall answers
   ========================================================================= *)

(** pselect6 (72) — [Select.bits_all_pollable] refuses a pipe end, so
    the whole call declines ([PsCoreGap]).  The offer is the answer a
    [Some _ => true] catch-all would have given: the descriptor reported
    ready for reading, which is what "unconditionally pollable" means at
    this site.  fd 3 is bit 3 of the read set, so the first argument is
    4 and the set word is 8. *)
Example pselect6_over_a_pipe_end_declines :
  check_syscall (mkInput 72 [4; 4096; 0; 0; 0; 0]
                   (fun a => if bv_eqb a 4096 then Some (Z_to_bv 8 8)
                             else Some (Z_to_bv 8 0))
                   (fun _ => Some (Z_to_bv 8 0)))
    (mkEffect 1 [] []) pipe_model = CheckUnmodeled.
Proof. check_eq. Qed.

(** ...and the contrast that keeps the line above from being vacuous,
    taken at [Select.pselect_core] rather than at the syscall so that
    the timeout and signal-mask arguments cannot be what decides it.
    Same model, same sets, only the polled fd changed: bit 3 is the pipe
    read end and gives [PsCoreGap], bit 5 is the [FdFileW] and gives an
    answer.  So the gap comes from the fd's KIND, through
    [bits_all_pollable], and from nothing else in the call. *)
Example pselect_core_gaps_on_a_pipe_end_only :
  let i := mkInput 72 [4; 4096; 0; 0; 0; 0]
             (fun a => if bv_eqb a 4096 then Some (Z_to_bv 8 8)
                       else Some (Z_to_bv 8 0))
             (fun _ => Some (Z_to_bv 8 0)) in
  let i5 := mkInput 72 [6; 4096; 0; 0; 0; 0]
              (fun a => if bv_eqb a 4096 then Some (Z_to_bv 8 32)
                        else Some (Z_to_bv 8 0))
              (fun _ => Some (Z_to_bv 8 0)) in
  pselect_core i pipe_model 4 4096 0 0 = PsCoreGap
  /\ pselect_core i5 pipe_model 6 4096 0 0 <> PsCoreGap.
Proof.
  (* The answer is [PsCoreDone] with a function of the choice in it, so
     the second conjunct is decided on its constructor alone: a full
     [vm_compute] would normalize that function under its binder. *)
  cbv zeta; split; [check_eq|].
  intro H.
  apply (f_equal (fun c => match c with PsCoreGap => true | _ => false end)) in H.
  vm_compute in H. discriminate H.
Qed.

(** ...and the same shape over the CHANNEL at fd 0 also declines, which
    is what says the pipe end joined an existing decline rather than
    creating a new one; while the [FdFileW] at fd 5 is pollable, so the
    predicate is not simply refusing everything. *)
Example pselect6_pollability_is_per_kind :
  bits_all_pollable (m_fds pipe_model) 8 6 = false          (* fd 3: pipe read end *)
  /\ bits_all_pollable (m_fds pipe_model) 16 6 = false      (* fd 4: pipe write end *)
  /\ bits_all_pollable (m_fds pipe_model) 1 6 = false       (* fd 0: channel *)
  /\ bits_all_pollable (m_fds pipe_model) 32 6 = true.      (* fd 5: FdFileW *)
Proof. repeat split; check_eq. Qed.

(** clone (220) — [Fork.clone_no_shared_file_b] refuses a descriptor
    table holding a pipe end, so a clone made with one open declines.

    THIS PIN NEEDS ITS OWN MODEL, and the reason is the shape of the
    predicate rather than anything about pipes.  [clone_no_shared_file_b]
    is a [forallb] over the WHOLE table, so ANY entry answering [false]
    decides it — and [pipe_model] carries an [FdFileW] at fd 5, which
    [Fork.v] already maps to [false].  Pinned over [pipe_model] the gate
    would read [false] with no pipe end present at all, and the flipped
    pipe answer would go uncaught.  [clone_model] therefore holds
    channels and ONE pipe end and nothing else, so the pipe arm is the
    only thing that can make the gate refuse.

    (There is a second independent cause of vacuity: [flags = 0], which
    [Fork.clone_spec] rejects at [clone_fork_flags_b] before it ever
    looks at the descriptor table; hence SIGCHLD below.  A forallb over a
    table with a [false] in it already is the subtler one, and the
    reason every conjunct here names the table it quantifies over.) *)
Definition clone_model : Model :=
  mkModel
    [ (0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2);
      (3, FdPipe 0 false) ]
    (mkVmMaps [] [] 0 0 demo_limit) IEof [] None None None.

Example clone_with_a_pipe_end_open_declines :
  (* the syscall declines, over a table whose ONLY non-channel entry is
     the pipe end *)
  check_syscall (mkInput 220 [Z_to_bv 64 SIGCHLD; 0; 0; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect 4242 [] []) clone_model = CheckUnmodeled
  (* the gate itself, on the smallest table that isolates the arm: flip
     [Fork.clone_no_shared_file_b]'s pipe answer to [true] and this
     conjunct becomes [true] and fails *)
  /\ clone_no_shared_file_b [ (0, FdChannel 0); (3, FdPipe 0 false) ] = false
  /\ clone_no_shared_file_b [ (0, FdChannel 0); (4, FdPipe 0 true) ] = false
  (* ...and the contrast: drop the pipe end and the same table passes, so
     the gate is not refusing every table *)
  /\ clone_no_shared_file_b [ (0, FdChannel 0) ] = true
  /\ clone_no_shared_file_b
       [ (0, FdChannel 0); (1, FdChannel 1); (5, FdDir) ] = true.
Proof. repeat split; check_eq. Qed.

(** ...and the syscall-level contrast the conjuncts above still cannot
    give, because [CheckUnmodeled] alone never proves the decline came
    from the fd table: the same call on [clone_model] WITHOUT the pipe
    end is admitted.  Together with the first conjunct above this is what
    makes the decline a fact about the pipe end rather than about
    [clone]. *)
Example clone_without_a_pipe_end_is_admitted :
  check_syscall (mkInput 220 [Z_to_bv 64 SIGCHLD; 0; 0; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect 4242 [] [])
    (with_fds [ (0, FdChannel 0); (1, FdChannel 1); (2, FdChannel 2) ]
       clone_model)
  <> CheckUnmodeled.
Proof. vm_compute. discriminate. Qed.

(** unlinkat (35), through [Namei.fd_names_path] — a site that is easy
    to miss, because its constructors sit inside a cons pattern rather
    than at the head of an arm, so the match does not look like fd-kind
    dispatch at all.  Its arms enumerate the constructors rather than end
    in a [| _ :: r =>] catch-all.

    Unlike every other decline in this file the answer here is EXACT
    rather than fail-closed: [false], because a pipe end names no
    filesystem path.  So this pin is an equality both ways rather than a
    decline and an offer.

    ALL FOUR CONJUNCTS ARE ON THE PREDICATE, not on [unlinkat], and that
    is a choice rather than an omission.  [Namei.fd_names_path] is where
    the fd-kind decision lives; the syscall around it adds a pathname to
    encode in guest memory, a dirfd and a flags word, none of which has
    anything to do with which [FdEntry] constructor the table holds.  A
    syscall-level pin would be testing the path encoding as much as the
    arm, and it would not discriminate the arm any more sharply than the
    third and fourth conjuncts already do.

    What the four say, in order: neither end of a pipe names the path;
    an [FdFileW] on that same path does, so [false] above is about the
    fd's KIND and not about the path being absent; and a pipe end
    sitting BESIDE that file does not change the file's answer.  The
    last is the one worth having — [fd_names_path] is an or-fold down
    the table, so an arm that answered [true] would mask nothing but an
    arm that short-circuited would, and the conjunct pins that the pipe
    arm recurses rather than deciding. *)
Example fd_names_path_ignores_a_pipe_end :
  fd_names_path [ (3, FdPipe 0 false) ] [102] = false
  /\ fd_names_path [ (4, FdPipe 0 true) ] [102] = false
  (* the contrast, on the same path: a file fd DOES name it *)
  /\ fd_names_path [ (5, FdFileW [102] 0) ] [102] = true
  (* ...and a pipe end alongside it does not mask the file's answer *)
  /\ fd_names_path [ (3, FdPipe 0 false); (5, FdFileW [102] 0) ] [102] = true.
Proof. repeat split; check_eq. Qed.

(* =========================================================================
   Where a pipe end comes from
   ========================================================================= *)

(** PIPE2 IS THE ONLY THING THAT MAKES ONE, and that is what
    [Pipe.pipe_end_live] rests on: it derives whether a pipe still has a
    reader or a writer by scanning the fd table, which is sound only
    because no other syscall can put a second reference to an end into
    that table.  [openat] resolves against [m_fs] and yields an [FdFile]
    or an [FdFileW], never an [FdPipe].

    The half of that a proof can state is the STARTING table:
    [State.init_model] seeds three channels and nothing else, so a pipe
    end is absent before the first instruction and every one below comes
    from a [pipe2] the run made. *)
Example init_model_holds_no_pipe_end :
  Forall (fun e => match snd e with FdPipe _ _ => False | _ => True end)
    (m_fds (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))).
Proof. repeat constructor. Qed.

(* =========================================================================
   pipe2 (59) itself
   ========================================================================= *)

(** A model holding one pipe, made the way [pipe2_spec] makes one: the
    read end takes the lowest free descriptor and the write end the
    next, so over [init_model]'s three channels they are 3 and 4. *)

Definition one_pipe_model : Model :=
  let m := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) in
  pipe2_model m (pipe_new_id (m_pipes m)).

(** THE MODEL ADMITS BOTH KERNELS' COUNT VALIDATION for a vectored write
    to a pipe write end whose raw [iovcnt] is over [IOV_MAX] and whose
    low 32 bits are zero — [2 ^ 32] is the smallest such count.

    Linux >= 4.1 narrows the count at [import_iovec]'s [unsigned nr_segs]
    parameter, truncates to ZERO segments, and [vfs_writev] returns 0 at
    [if (!tot_len) goto out;] (fs/read_write.c:1048-1049, v6.18.46) —
    above the file kind, so [anon_pipe_write] is never entered and no pipe
    state is consulted.  Linux <= 4.0 validated the full 64-bit count
    instead and answered -EINVAL (qemu-user still does), which is
    REJECTED here.

    THE REASON THIS IS HERE: Linux >= 4.1 produces the truncating 0, so
    that the 0 is the ONLY admissible answer is a fact about the model
    no truthful run of any binary can demonstrate, which is what this
    file is for.

    No memory is readable in either input, which is itself part of the
    claim: zero segments inspect no buffer, so the answer cannot depend
    on one.

    The second and third conjuncts keep the first from being vacuous —
    neither the full-count -EINVAL nor a DELIVERED count is admissible — and the
    last two put the read end's -EBADF beside them, decided before any
    iovec is looked at. *)

Example pipe_writev_zero_count_truncates :
  (* the kernel's 0 *)
  check_syscall (mkInput 66 [4; 8192; Z_to_bv 64 (2 ^ 32); 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) one_pipe_model
  = CheckOk one_pipe_model []
  (* the full-count -EINVAL is refused *)
  /\ check_syscall (mkInput 66 [4; 8192; Z_to_bv 64 (2 ^ 32); 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) one_pipe_model
     = CheckReject
  (* and so is a delivered count *)
  /\ check_syscall (mkInput 66 [4; 8192; Z_to_bv 64 (2 ^ 32); 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect 5 [] []) one_pipe_model
     = CheckReject
  (* the READ end is O_RDONLY: -EBADF, before the count is consulted *)
  /\ check_syscall (mkInput 66 [3; 8192; Z_to_bv 64 (2 ^ 32); 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) one_pipe_model
     = CheckOk one_pipe_model []
  (* so the zero the write end answers is inadmissible there *)
  /\ check_syscall (mkInput 66 [3; 8192; Z_to_bv 64 (2 ^ 32); 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) one_pipe_model
     = CheckReject.
Proof. split; [|split; [|split; [|split]]]; check_eq. Qed.

(* =========================================================================
   A [fildes] THAT WALKS OFF THE TOP OF THE ADDRESS SPACE
   ========================================================================= *)

(** WHY THIS GROUP IS HERE: the THIRD of the four reasons listed at
    the top of [Checks.Examples].  It pins MODEL-INTERNAL STATE no
    observation of a real execution reveals, and the state is [in_wmem].
    No Linux user mapping reaches the very top of the address space, and
    the walk below wraps only because its FIRST four bytes sit there.  So
    no real run can present the memory this defect needs.

    What a real run CAN reach is the guard on the real path, where Linux
    answers -EFAULT for the ordinary reason that nothing is mapped that
    high, and that holds whether or not the guard exists.  What the
    guard PREVENTS is visible only here.

    [Equivalence.strong_universal] quantifies over the image freely and
    nothing in [pipe2_spec] constrains [fildes] — the flag mask is read
    off [flags] alone — so the disagreement is in the DEFINITIONS, which
    is what matters.

    Same shape and same order as [Checks.Cases.Net.Socket]'s
    [socketpair_wrap_*] group, which is the precedent for this guard;
    the argument for the guard itself is on [Pipe.pipe2_spec]'s own arm
    and is not restated here. *)

(** The last four bytes of the address space, so the 8-byte copy-out
    covers them and then the four at 0. *)
Definition pipe2_wrap_fildes : word := Z_to_bv 64 (2 ^ 64 - 4).

Definition pipe2_wrap_mem : word -> option byte :=
  fun a => if ((bv_unsigned a <? 4)%Z || (2 ^ 64 - 4 <=? bv_unsigned a)%Z)%bool
           then Some (Z_to_bv 8 0) else None.

(** THE WALK ALONE, which is what [pipe2_spec] would consult without
    the guard: the walk WRAPS because [State.read_bytes_map] advances in
    word arithmetic, and it reads all eight bytes back off a memory
    mapping only those eight.  It says "writable", and without the guard
    the spec would answer SUCCESS — a pipe made, two descriptors
    installed, both numbers stored — where
    Linux's [copy_to_user] is refused by [access_ok] and the call is
    -EFAULT with nothing done.

    Pinning it beside the guard is what stops the three Examples below
    from going vacuous: each would also pass if [pipe2_wrap_fildes]
    stopped wrapping or [pipe2_wrap_mem] stopped mapping the range, and
    then they would be testing nothing.  With this beside them they can
    only hold together when the range really is mapped end to end AND the
    guard declines it anyway. *)
Example pipe2_wrap_would_pass_the_bare_walk :
  read_bytes_map pipe2_wrap_mem pipe2_wrap_fildes (Z_to_bv 64 8) <> None.
Proof. vm_compute. discriminate. Qed.

(** The guard declines it, because [State.access_okb] — the model's
    transcription of [__access_ok], written as a subtraction so the
    wrapping sum is never formed — refuses the range on its
    [addr <= TASK_SIZE - size] half.  Delete the guard from
    [Pipe.pipe2_spec] and the [CheckReject] below becomes a [CheckOk]. *)
Example pipe2_wrap_fildes_is_not_access_ok :
  access_okb pipe2_wrap_fildes 8 = false.
Proof. vm_compute. reflexivity. Qed.

(** THE NEGATIVE HALF, AND THE ONE THAT MATTERS: the effect offered here
    is EXACTLY the answer the model gives without the guard — return 0,
    with the two
    descriptor numbers stored as one 8-byte range at [2^64 - 4] and, once
    the word wrapped, at 0.  Linux cannot produce it: [do_pipe2]'s single
    [copy_to_user] of [int fildes[2]] (fs/pipe.c:1040, v6.18.46) is
    refused by [access_ok] before a byte moves, and the [fput] /
    [put_unused_fd] pair at :1041-1045 undoes both reservations.

    3 and 4 are the descriptors [init_model]'s three channels leave free,
    which is what [alloc_fd] hands out at each of the two steps; the pair
    is spelled as bytes rather than through [pipe_fd_bytes] so the
    rejection is of a concrete stored value and not of whatever that
    function currently computes. *)
Example pipe2_wrapping_fildes_rejects_the_pair :
  check_syscall (mkInput 59 [pipe2_wrap_fildes; 0; 0; 0; 0; 0]
                   (fun _ => None) pipe2_wrap_mem)
    (mkEffect (Z_to_bv 64 0) [(pipe2_wrap_fildes, [3;0;0;0;4;0;0;0])] [])
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckReject.
Proof. check_eq. Qed.

(** ...and the positive half, which is Linux's own answer: -EFAULT, no
    write, and the model unchanged — no pipe in [m_pipes] and no
    descriptor in [m_fds].  The unchanged model is carried by the
    equality itself, since the [CheckOk] names the model it started
    from. *)
Example pipe2_wrapping_fildes_is_efault :
  check_syscall (mkInput 59 [pipe2_wrap_fildes; 0; 0; 0; 0; 0]
                   (fun _ => None) pipe2_wrap_mem)
    (mkEffect (errno_ret EFAULT) [] [])
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [].
Proof. check_eq. Qed.

(** WHERE THE NARROWING LANDS, which is the conjunct the two above cannot
    supply: they would BOTH still pass if the guard had been written to
    refuse every [fildes], and refusing every [fildes] is the failure
    mode a guard on an address has.  So the same call on an UNWRAPPED
    destination, with the same eight bytes backed and nothing else, still
    succeeds and still installs the pair.

    [pipe2_flat_mem] maps exactly its own range, for the reason
    [socketpair_wrap_mem] does: a view answering [Some] everywhere could
    not tell this destination from the wrapping one.  4096 is not load
    bearing — any address [access_okb] accepts would do — and the width
    is 8 so that the mapped range and the copy-out are the same range. *)
Definition pipe2_flat_fildes : word := Z_to_bv 64 4096.

Definition pipe2_flat_mem : word -> option byte :=
  fun a => if ((4096 <=? bv_unsigned a)%Z && (bv_unsigned a <? 4096 + 8)%Z)%bool
           then Some (Z_to_bv 8 0) else None.

Example pipe2_flat_fildes_is_access_ok :
  access_okb pipe2_flat_fildes 8 = true.
Proof. vm_compute. reflexivity. Qed.

Example pipe2_unwrapped_fildes_still_installs_the_pair :
  check_syscall (mkInput 59 [pipe2_flat_fildes; 0; 0; 0; 0; 0]
                   (fun _ => None) pipe2_flat_mem)
    (mkEffect (Z_to_bv 64 0) [(pipe2_flat_fildes, [3;0;0;0;4;0;0;0])] [])
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckOk one_pipe_model [].
Proof. check_eq. Qed.

(** ...and -EFAULT is inadmissible THERE, which is the other direction of
    the same discrimination: the errno the wrapping destination earns is
    refused on the destination the guard accepts, so the two Examples
    above are separated by the guard rather than by anything [pipe2] does
    to every call. *)
Example pipe2_unwrapped_fildes_rejects_efault :
  check_syscall (mkInput 59 [pipe2_flat_fildes; 0; 0; 0; 0; 0]
                   (fun _ => None) pipe2_flat_mem)
    (mkEffect (errno_ret EFAULT) [] [])
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = CheckReject.
Proof. check_eq. Qed.
