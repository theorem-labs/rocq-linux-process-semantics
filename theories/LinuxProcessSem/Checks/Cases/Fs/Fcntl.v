(** * LinuxProcessSem.Checks.Cases.Fs.Fcntl — worked examples over fcntl (25)

    Mirrors [Sys/Fs/Fcntl.v], which answers to Linux [fs/fcntl.c]: this
    file holds the worked examples for the syscalls defined there, and
    no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary.

    What is here: (a) an unknown cmd on a closed fd and (d) F_GETFL on
    a socket, each with the other answer as its reject twin; (b) fcntl
    on fds 0 and 1, channels whose flag words come from the environment
    and are not the model's to assert; (c) the exact boundary of the
    F_SETFL mask, which needs two neighbouring flag words compared
    against each other; and (e) F_GETFD, which admits both of Linux's
    answers on an open fd and nothing else, and is -EBADF on a closed
    one.

    The directory fd and the socket fd are here because
    [Fcntl.setfl_noop_on] ENUMERATES its fd kinds, so each kind's answer
    is a spelled-out arm rather than a consequence of one, and a reader
    checking that enumeration should find all five values in one place.
    These read the arms back. *)

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

Definition fcntl_model : Model :=
  mkModel [(0, FdChannel 0); (1, FdChannel 1); (3, FdFile [102] 0);
           (4, FdFileW [103] 0); (5, FdDir); (6, FdSocket SkFresh);
           (7, FdPipe 0 false); (8, FdPipe 0 true)]
    (mkVmMaps [] [] 0 0 demo_limit) IEof [([102], [104; 105])] None None
    None.

(** The same table with an APPEND fd (from
    O_WRONLY|O_CREAT|O_APPEND) at fd 10, beside the ordinary write-only
    fd at 4.  Two kinds, one call, one model: that pairing is what makes
    the contrast below a claim about the fd KIND. *)
Definition fcntl_append_model : Model :=
  mkModel [(0, FdChannel 0); (1, FdChannel 1); (3, FdFile [102] 0);
           (4, FdFileW [103] 0); (5, FdDir); (6, FdSocket SkFresh);
           (7, FdPipe 0 false); (8, FdPipe 0 true); (10, FdFileA [104] 0)]
    (mkVmMaps [] [] 0 0 demo_limit) IEof [([102], [104; 105])] None None
    None.

(** F_SETFL AND F_GETFL DECLINE ON AN APPEND FD, and no real run can
    say that the way this does: the interesting half is the CONTRAST with
    fd 4, an ordinary [State.FdFileW] taking the identical call in the
    identical model state and answering 0.  A real run reaches the
    decline but cannot put the two fds side by side, and it is the side-by-side that says the
    decline is about the fd KIND rather than about the argument.

    The [arg] of 0 is deliberate, and it is the case
    [Fs.Fcntl.setfl_noop_on]'s own comment calls the dangerous one: an
    empty word passes its [Z.land arg setfl_acted_on =? 0] test, so on
    every other fd kind it is the cheapest possible 0.  On an append fd
    it must still decline, because [setfl]'s closing assignment CLEARS
    O_APPEND for exactly such an [arg] and every later write then lands
    at [f_pos] instead of at end-of-file.

    F_SETFD is the boundary next door: it is kind-blind, so it still
    answers 0 on the append fd, which is what keeps the two declines
    above confined to the flag word. *)
Example fcntl_flag_commands_decline_on_an_append_fd :
  (* F_SETFL, arg 0 -- a no-op everywhere else *)
  check_syscall (mkInput 25 [10; 4; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) fcntl_append_model = CheckUnmodeled
  /\ check_syscall (mkInput 25 [4; 4; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_append_model = CheckOk fcntl_append_model []
  (* F_SETFL, arg O_DSYNC -- a bit [setfl] never reads *)
  /\ check_syscall (mkInput 25 [10; 4; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_append_model = CheckUnmodeled
  /\ check_syscall (mkInput 25 [4; 4; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_append_model = CheckOk fcntl_append_model []
  (* F_GETFL declines on both, and for the same reason it always has *)
  /\ check_syscall (mkInput 25 [10; 3; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_append_model = CheckUnmodeled
  (* ...while the kind-blind F_SETFD still answers 0 on the append fd *)
  /\ check_syscall (mkInput 25 [10; 2; 1; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_append_model = CheckOk fcntl_append_model [].
Proof. repeat split; solve [ check_eq | vm_compute; reflexivity ]. Qed.

(** A cmd the kernel does not recognise, on an fd that is NOT open, is
    -EBADF: [SYSCALL_DEFINE3(fcntl, ...)] resolves the descriptor before
    it dispatches (fs/fcntl.c, v6.18.46).  The model's ordering claim
    is pinned here from both sides. *)
Example fcntl_unknown_cmd_on_closed_fd_is_ebadf :
  check_syscall (mkInput 25 [9; 57005; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EBADF) [] []) fcntl_model
  = CheckOk fcntl_model []
  /\ check_syscall (mkInput 25 [9; 57005; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) fcntl_model
     = CheckReject.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** F_SETFD is 0 on a CHANNEL as well as on a file: its return does not
    depend on the file's status flags, only on the fd resolving. *)
Example fcntl_setfd_on_channel_is_zero :
  check_syscall (mkInput 25 [1; 2; 1; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) fcntl_model
  = CheckOk fcntl_model [].
Proof. check_eq. Qed.

(** ...and the arg is not consulted beyond FD_CLOEXEC, so a garbage one
    is the same 0.  [F_SETFD, 2] is the trap: it CLEARS close-on-exec
    rather than being an unknown-flag error, and the model's answer is
    the same either way because it records no bit at all. *)
Example fcntl_setfd_ignores_its_arg :
  check_syscall (mkInput 25 [3; 2; 3735928559; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) fcntl_model
  = CheckOk fcntl_model []
  /\ check_syscall (mkInput 25 [3; 2; 2; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model
     = CheckOk fcntl_model [].
Proof. split; check_eq. Qed.

(** The same empty F_SETFL that answers 0 on the file DECLINES on fd 1.
    A channel's status flags come from whoever ran the binary, so
    "this changes nothing" is not the model's to say there. *)
Example fcntl_setfl_empty_file_vs_channel :
  check_syscall (mkInput 25 [3; 4; 32768; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) fcntl_model
  = CheckOk fcntl_model []
  /\ check_syscall (mkInput 25 [1; 4; 32768; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model
     = CheckUnmodeled.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** The F_SETFL mask, at its edge.  O_DSYNC (010000) is a real open flag
    that [setfl] never reads, so it answers 0; FASYNC (020000) is the
    adjacent bit, is absent from SETFL_MASK, and is read all the same by
    the [f_op->fasync] test — so it declines.  A mask copied from
    SETFL_MASK alone would answer 0 for both. *)
Example fcntl_setfl_mask_edge :
  check_syscall (mkInput 25 [3; 4; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) fcntl_model
  = CheckOk fcntl_model []
  /\ check_syscall (mkInput 25 [3; 4; 8192; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model
     = CheckUnmodeled.
Proof. split; [check_eq | vm_compute; reflexivity]. Qed.

(** cmd is 32 bits ([Syscall.cmd32]), and BIT 31 IS PART OF IT: a high
    half still names F_SETFD, while [2^31 | F_SETFD] names no command at
    all — the kernel's [unsigned int cmd] is 2147483650, [do_fcntl] falls
    to [default: break] and returns its pre-set -EINVAL.  A [cmd32] that
    kept only 31 bits would answer 0 to a call Linux refuses.

    ([arg]'s width needs no case: [Fcntl.setfl_acted_on_fits_32] settles
    it, and no input can witness it — masking commutes with the kernel's
    [int argi = (int)arg] precisely because the mask stays under 2^32.) *)
Example fcntl_cmd32_keeps_bit_31 :
  check_syscall (mkInput 25 [3; 4294967298; 1; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) fcntl_model
  = CheckOk fcntl_model []
  /\ check_syscall (mkInput 25 [3; 2147483650; 1; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model
     = CheckUnmodeled
  /\ check_syscall (mkInput 25 [3; 18446744073709551615; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) fcntl_model
     = CheckUnmodeled.
Proof. split; [check_eq | split; vm_compute; reflexivity]. Qed.

(** THE MASK, BIT BY BIT — the declining half.  Each of the five bits
    [setfl] reads declines on its own.  O_DIRECT (16384) and O_NOATIME
    (262144) are the two nothing else in the development reaches: with
    either deleted from [Fcntl.setfl_acted_on] every other case here
    still passes, and the model would then answer
    0 for a call that really does change the open file description.  For
    O_DIRECT that is not merely a lost decline — the fd becomes
    O_DIRECT, and the NEXT unaligned [write] is -EINVAL on the kernel
    where [ReadWrite.write_spec] promises a count, so the checker would
    reject a conforming trace at the write, having admitted the call that
    caused it. *)
Example fcntl_setfl_every_mask_bit_declines :
  check_syscall (mkInput 25 [3; 4; 1024; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) fcntl_model = CheckUnmodeled
  /\ check_syscall (mkInput 25 [3; 4; 2048; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model = CheckUnmodeled
  /\ check_syscall (mkInput 25 [3; 4; 8192; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model = CheckUnmodeled
  /\ check_syscall (mkInput 25 [3; 4; 16384; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model = CheckUnmodeled
  /\ check_syscall (mkInput 25 [3; 4; 262144; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model = CheckUnmodeled
  (* the whole mask at once, and a high half over one of its bits: the
     kernel's own truncation cannot rescue that either *)
  /\ check_syscall (mkInput 25 [3; 4; 289792; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model = CheckUnmodeled
  /\ check_syscall (mkInput 25 [3; 4; 4294969344; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model = CheckUnmodeled
  (* AND THE BIT BETWEEN TWO OF THEM, ANSWERING, which is what makes the
     seven above a boundary rather than a list.  Every one of them is
     [CheckUnmodeled], so on their own they stay green under any change
     that only ever declines MORE -- [Fcntl.setfl_acted_on] growing past
     these bits, or F_SETFL going quiet altogether, which is the change
     this lemma exists to notice.  O_DSYNC (4096) lies between O_NONBLOCK
     (2048) and FASYNC (8192), both declined above, and the arm still
     answers 0 for it, so absorbing it into [setfl_acted_on] turns this
     conjunct red on the same fd and the same model state.

     An [arg] of 0 would NOT do, which is why it is not what is here:
     [Fs.Fcntl.setfl_noop_on]'s test is [Z.land arg setfl_acted_on =? 0],
     and the empty word passes it however wide the mask grows.  It would
     catch F_SETFL going quiet and nothing else. *)
  /\ check_syscall (mkInput 25 [3; 4; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model = CheckOk fcntl_model [].
Proof. repeat split; solve [ check_eq | vm_compute; reflexivity ]. Qed.

(** ...and the accepting half: every neighbouring open flag [setfl] never
    reads answers 0.  O_DSYNC (4096) and FASYNC (8192) are adjacent bits
    on opposite sides of the line; O_DIRECTORY (65536) and O_NOFOLLOW
    (131072) bracket O_LARGEFILE; O_SYNC (1052672) and O_PATH (2097152)
    are the whole words a caller is likeliest to OR in by accident; and
    2^31 is [arg]'s sign bit, which the kernel reads back through an
    [unsigned int] and which unsigned [Z.land] must therefore not treat
    as special. *)
Example fcntl_setfl_unread_flags_are_zero :
  check_syscall (mkInput 25 [3; 4; 4096; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) fcntl_model = CheckOk fcntl_model []
  /\ check_syscall (mkInput 25 [3; 4; 65536; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model = CheckOk fcntl_model []
  /\ check_syscall (mkInput 25 [3; 4; 131072; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model = CheckOk fcntl_model []
  /\ check_syscall (mkInput 25 [3; 4; 1052672; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model = CheckOk fcntl_model []
  /\ check_syscall (mkInput 25 [3; 4; 2097152; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model = CheckOk fcntl_model []
  /\ check_syscall (mkInput 25 [3; 4; 2147483648; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model = CheckOk fcntl_model [].
Proof. repeat split; check_eq. Qed.

(** [fd] is 32 bits ([Syscall.fd32]) — pinned on the arm that SUCCEEDS.
    On a CLOSED fd both spellings answer -EBADF whether or not the high half was dropped,
    because the fd-not-found arm short-circuits before [cmd] is looked
    at.  Only a LIVE fd separates [fd32] from the identity, and the
    channel exclusion has to survive the truncation too. *)
Example fcntl_fd32_on_a_live_fd :
  check_syscall (mkInput 25 [4294967299; 2; 1; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) fcntl_model
  = CheckOk fcntl_model []
  /\ check_syscall (mkInput 25 [4294967299; 2; 1; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) fcntl_model
     = CheckReject
  /\ check_syscall (mkInput 25 [4294967297; 4; 32768; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model
     = CheckUnmodeled.
Proof. split; [check_eq | split; vm_compute; reflexivity]. Qed.

(** The other two shapes [openat] can mint.  [Fcntl.setfl_noop_on]
    excludes CHANNELS and nothing else, so a write-created file and a
    directory fd take the file answer — right, because
    [ext4_dir_operations] defines neither [check_flags] nor [fasync], but
    stated nowhere else, and [FdDir] is the entry a reader is likeliest
    to expect beside [FdChannel] on the declining side. *)
Example fcntl_on_a_write_fd_and_a_directory_fd :
  check_syscall (mkInput 25 [4; 4; 32768; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) fcntl_model = CheckOk fcntl_model []
  /\ check_syscall (mkInput 25 [5; 4; 32768; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model = CheckOk fcntl_model []
  /\ check_syscall (mkInput 25 [5; 2; 1; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model = CheckOk fcntl_model []
  /\ check_syscall (mkInput 25 [5; 4; 2048; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model = CheckUnmodeled.
Proof. split; [check_eq|split; [check_eq|split; [check_eq|vm_compute; reflexivity]]]. Qed.

(** THE FIFTH [State.FdEntry] CONSTRUCTOR, which the four cases above
    leave unpinned.  A socket fd takes the file answer, and it is the one
    kind reaching this spec that [openat] never mints, so nothing else in
    this file puts it through [Fcntl.setfl_noop_on] at all.  Both sides
    of the mask are here, and the declining one is why it is worth
    spending three lines on a kind that takes the same answer as a file:
    FASYNC is the bit [Net.Socket.setfl_noop_declines_fasync] turns into
    the standing guarantee that no modeled [F_SETFL] can put a socket on
    a fasync list, and a socket is the descriptor that guarantee is
    about.  F_SETFD is 0 here as on every other kind, since it never
    consults the entry.

    THERE IS NO NEGATIVE TEST FOR THE ENUMERATION ITSELF, and there
    cannot be one.  What the enumeration buys is that a NEW [FdEntry]
    constructor fails to COMPILE in [Sys/Fs/Fcntl.v]: there is no model
    value to hand [check_syscall] for a constructor that does not exist
    yet, and no [CheckReject] to assert.  Replacing the enumeration with
    a wildcard leaves every case in this file passing — which is exactly the property that makes the
    wildcard worth refusing. *)
Example fcntl_setfl_on_a_socket_fd :
  check_syscall (mkInput 25 [6; 4; 32768; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) fcntl_model = CheckOk fcntl_model []
  /\ check_syscall (mkInput 25 [6; 4; 8192; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model = CheckUnmodeled
  /\ check_syscall (mkInput 25 [6; 2; 1; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model = CheckOk fcntl_model [].
Proof. split; [check_eq|split; [vm_compute; reflexivity|check_eq]]. Qed.

(** F_GETFL ON A SOCKET is O_RDWR exactly: net/socket.c [sock_alloc_file]
    builds the file from O_RDWR and the two SOCK_ flags and never goes
    near [build_open_flags], whose [force_o_largefile()] is what puts
    O_LARGEFILE on a path-opened file for a 64-bit process (fs/open.c,
    v6.18.46).  The checker accepts the 2 and rejects 32770, the
    O_RDWR|O_LARGEFILE word a 64-bit libc wrapper (or a translating
    emulator) would report.

    THE SECOND CONJUNCT IS THE ONE THAT MATTERS, and it is here for the
    reason [Checks/ExecutableSpecs.v]'s biconditionals cannot cover: a
    change made to [Fcntl.fcntl_spec] AND [check_fcntl] the same wrong
    way leaves every proof closing by the same tactic.  Only a concrete
    answer from outside separates them, so this offers the checker
    32770 and requires [CheckReject].  A model that ORed O_LARGEFILE into
    a socket's answer — the obvious wrong fix if a real run ever
    disagreed here — accepts that effect and fails this line.

    The answer does not depend on the socket's [State.SockState]:
    [Fcntl.getfl_f_flags] matches [FdSocket _], and every state is
    reached from a [socket] or [accept4] that declined SOCK_NONBLOCK, so
    all five carry the same [Fcntl.socket_f_flags]. *)
Example fcntl_getfl_on_a_socket_fd_is_o_rdwr :
  check_syscall (mkInput 25 [6; 3; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 2 [] []) fcntl_model = CheckOk fcntl_model []
  /\ check_syscall (mkInput 25 [6; 3; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 32770 [] []) fcntl_model = CheckReject.
Proof. split; [check_eq|vm_compute; reflexivity]. Qed.

(** ...and the four kinds it still declines, in one place, because the
    value of an enumerated [Fcntl.getfl_f_flags] is that a reader can
    check every arm against the argument beside it.  fd 0 is a channel
    (reason (b)), and the other kinds are here for completeness of the
    enumeration.

    [arg] is 0 throughout and is not part of the question: [do_fcntl]'s
    [case F_GETFL] is [err = filp->f_flags] and never reads [argp] or
    [argi], so the decline is a property of the fd kind alone.

    THE FIFTH CONJUNCT IS THE SOCKET, ANSWERING, and it is here for the
    reason [fcntl_getfl_declines_on_both_pipe_ends] below states at
    length: the four above are all [CheckUnmodeled], so on their own
    they stay green under any change that only ever declines MORE --
    including [Fcntl.getfl_f_flags] widening its decline past these
    kinds, which is the change this lemma exists to notice.  Four
    declines describe where the boundary is; they do not fail when
    someone moves it.  Pinning the one kind that ANSWERS, over the same
    model state, is what makes the boundary part of what these conjuncts
    assert. *)
Example fcntl_getfl_declines_on_every_other_fd_kind :
  check_syscall (mkInput 25 [0; 3; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) fcntl_model = CheckUnmodeled
  /\ check_syscall (mkInput 25 [3; 3; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model = CheckUnmodeled
  /\ check_syscall (mkInput 25 [4; 3; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model = CheckUnmodeled
  /\ check_syscall (mkInput 25 [5; 3; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model = CheckUnmodeled
  /\ check_syscall (mkInput 25 [6; 3; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 2 [] []) fcntl_model = CheckOk fcntl_model [].
Proof.
  split; [vm_compute; reflexivity|split; [vm_compute; reflexivity|
    split; [vm_compute; reflexivity|split; [vm_compute; reflexivity|check_eq]]]].
Qed.

(** F_GETFD on the SAME socket fd that F_GETFL answers exactly: 0 and
    FD_CLOEXEC are both accepted, and 2 is rejected.  The contrast with
    F_GETFL is the point: a socket's [f_flags] is a function of the
    constructor, its close-on-exec bit is not ([Net.Socket.socket_spec]
    and [Net.Socket.accept4_spec] ignore SOCK_CLOEXEC), so
    [Fcntl.fcntl_spec] admits the two answers [do_fcntl] can give
    rather than one (fs/fcntl.c, v6.18.46).  The 2 is the reject twin:
    an arm that accepted ANY word "because the bit is unknown" fails
    here. *)
Example fcntl_getfd_on_a_socket_fd_admits_either_answer :
  check_syscall (mkInput 25 [6; 1; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) fcntl_model = CheckOk fcntl_model []
  /\ check_syscall (mkInput 25 [6; 1; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 1 [] []) fcntl_model = CheckOk fcntl_model []
  /\ check_syscall (mkInput 25 [6; 1; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 2 [] []) fcntl_model = CheckReject.
Proof. split; [check_eq|split; [check_eq|vm_compute; reflexivity]]. Qed.

(** ...and on a regular-file fd, the kind [openat] mints.  [arg] is not
    read: musl's riscv64 [dup2(fd, fd)] probes with
    [__syscall(SYS_fcntl, old, F_GETFD)] and leaves the third register
    as it finds it, so the second conjunct passes garbage there.  The
    errno is the reject twin: the fd is open, so no error is admitted. *)
Example fcntl_getfd_on_a_file_fd_admits_either_answer :
  check_syscall (mkInput 25 [3; 1; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) fcntl_model = CheckOk fcntl_model []
  /\ check_syscall (mkInput 25 [3; 1; 3735928559; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 1 [] []) fcntl_model = CheckOk fcntl_model []
  /\ check_syscall (mkInput 25 [3; 1; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EBADF) [] []) fcntl_model = CheckReject.
Proof. split; [check_eq|split; [check_eq|vm_compute; reflexivity]]. Qed.

(** -EBADF STILL WINS on a closed fd: the lookup runs before [cmd] is
    examined, so neither of F_GETFD's two answers is admitted there. *)
Example fcntl_getfd_on_a_closed_fd_is_ebadf :
  check_syscall (mkInput 25 [9; 1; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EBADF) [] []) fcntl_model = CheckOk fcntl_model []
  /\ check_syscall (mkInput 25 [9; 1; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model = CheckReject
  /\ check_syscall (mkInput 25 [9; 1; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 1 [] []) fcntl_model = CheckReject.
Proof. split; [check_eq|split; vm_compute; reflexivity]. Qed.

(** BOTH PIPE ENDS, which [getfl_f_flags] declines even though it could
    answer them.  The arm's own comment argues that, and this reads the
    decision back on both constructors rather than on one of them:
    the ends differ in [f_flags] on a real
    kernel — O_WRONLY on the writer, O_RDONLY on the reader — so an arm
    that answered would have to distinguish them, and one that declines
    must decline both.

    The negative half is the second and third conjuncts, and they are
    the answers a future arm would most plausibly give: offer the
    checker the exact word Linux produces for each end and require
    [CheckUnmodeled] anyway.  An arm added later without also landing
    the pipe2 change its comment names would turn these two green, which
    is the point of writing them as the true values rather than as
    arbitrary ones.

    THE FOURTH CONJUNCT MAKES THIS LEMMA DISCRIMINATE ON ITS OWN.  The
    three above are all [CheckUnmodeled], so they stay green under any
    change that only ever declines MORE -- including the one worth
    catching, [getfl_f_flags] widening its decline past pipes.  Pinning
    the socket fd still ANSWERING, in this lemma over this model state,
    is what makes the boundary part of what these conjuncts assert
    rather than something a reader has to go and find.
    BEING PRECISE ABOUT WHAT THAT BUYS, because the obvious stronger
    claim is false:
    [fcntl_getfl_on_a_socket_fd_is_o_rdwr] above ALSO fails on that
    widening, and being earlier in the file it fails first -- planting
    [| FdSocket _ => None] breaks it at its own line, not at this one.
    So the conjunct is not what stands between the tree and that
    change.  What it buys is that this lemma does not depend on that
    one surviving: delete or weaken the earlier case while widening the
    arm and these four still fail, where the three alone would not.
    ([Checks.Cases.Fs.Pipe]'s [fcntl_setfl_on_a_pipe_end_declines] uses
    the same pattern, and it is the better of the two to copy:
    its discriminating conjunct is over an fd kind no other lemma in
    that file pins, so there the stronger claim does hold.) *)
Example fcntl_getfl_declines_on_both_pipe_ends :
  check_syscall (mkInput 25 [7; 3; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) fcntl_model = CheckUnmodeled
  /\ check_syscall (mkInput 25 [8; 3; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 1 [] []) fcntl_model = CheckUnmodeled
  /\ check_syscall (mkInput 25 [8; 3; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) fcntl_model = CheckUnmodeled
  /\ check_syscall (mkInput 25 [6; 3; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 2 [] []) fcntl_model = CheckOk fcntl_model [].
Proof.
  split; [vm_compute; reflexivity|split; [vm_compute; reflexivity|
    split; [vm_compute; reflexivity|check_eq]]].
Qed.
