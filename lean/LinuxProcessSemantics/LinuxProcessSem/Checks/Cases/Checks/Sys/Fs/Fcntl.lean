import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Fcntl
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Fcntl
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! # Checks.Cases.Checks.Sys.Fs.Fcntl — what the fcntl checker accepts and refuses, read off against Linux

Pins over `Checks.Sys.Fs.Fcntl.check_fcntl`, the twin of
`theories/LinuxProcessSem/Checks/Sys/Fs/Fcntl.v`, and over its witness.
Not part of the trusted specification: this file is QA on the checker,
written to be READ, and every claim in it is a claim about what the kernel
does, with the citation beside it.  Line numbers are Linux v6.18.46
(commit 1f99e9ab748f).

WHAT THIS TWINS.  Rocq keeps the checker's worked examples for this
syscall in `Checks/Cases/Fs/Fcntl.v`, beside the spec's, as `Example`s
over `check_syscall (mkInput 25 …)`, one conjunct per call.  The Lean
tree keeps spec pins and checker pins apart — `Checks/Cases/Fs/Fcntl.lean`
pins the spec, this file the checker — and this file is where those
conjuncts land, one theorem each, stated on `check_fcntl` with the three
words the call decodes to rather than through `check_syscall`: the
dispatcher twin and the arm record are in the tree
(`Checks/ExecutableSpecs.lean`, `Checks/Sys/Dispatch.lean`).
Pins through `check_syscall` are in the `V_Fs_Fcntl` section at the end of
this file.
What the arm adds to the checker is the decode: Rocq's `Dispatch.arm_fcntl`
applies `fd32` to a0 and `cmd32` to a1 and passes a2 as it is, so the direct
checker pins about the narrowing apply `fd32` or `cmd32` (`Sys/Syscall.lean`)
to the word explicitly, and the other direct pins hand the checker the word
the narrowing leaves alone.  `tools/check_lean_cases_parity.py` pairs a Cases
file with the Rocq file at its mirrored path and none sits at this one, so
this file is listed `unmirrored` — a status, not a finding — and no pin
carries `rocq-twin:`; the Rocq example each one restates is named in its
prose.

Rocq's `fcntl_flag_commands_decline_on_an_append_fd` is restated
conjunct by conjunct over the spec Cases file's `fcntl_append_model`,
after `check_setfl_o_dsync_on_write_fd_is_zero`.  The
two fcntl examples of Rocq's `Checks/Cases/Fs/Pipe.v` ARE restated here:
their spec-level Lean twins are `Checks/Cases/Fs/Pipe.lean`'s (F_SETFD, on
`pipe_model`) and `Checks/Cases/Fs/Fcntl.lean`'s (F_SETFL), and their
checker-level conjuncts land in this file because the checker-level pipe
file pins `check_pipe2`, not `check_fcntl`, while `fcntl_model` holds both
ends at fds 7 and 8.

WHY A CHECKER NEEDS PINS OF ITS OWN.  The lemmas of the checker's file tie
`check_fcntl` to `fcntl_spec` in both directions, and a checker that
declined every input, or accepted every one, would still meet them if the
spec were changed to match.  What the lemmas cannot see is a lie told from
OUTSIDE: an errno the kernel would not return, a ledger beside the one it
does, a return that agrees only in its low half, or the flag word a
translating libc reports, offered to the checker and required to be
refused.  That is what the `CheckReject` pins below do, beside the answer
the kernel does give required to be `CheckOk` with the model unchanged and
no event.  The `CheckOk` pins beside each group of declines are what make
the declines a boundary rather than a list — every `CheckUnmodeled` stays
green under a change that only ever declines more, and the answering pin
over the same fixture is what goes red then (the argument of Rocq's
`fcntl_setfl_every_mask_bit_declines`).

HOW THEY CLOSE.  Every closed pin closes by `rfl`: `check_result` carries
a `Model`, which has no `DecidableEq`, so `decide` is not available and the
kernel's own evaluation of the closed term is what settles each.  The
quantified theorems of the witness section range over every call and model
and close by the checker's own case split instead.

WHAT MEASURES THESE PINS.  The build, first: each is a closed term or a
case split and either elaborates or does not.  Then
`tools/check_lean_pins.py`, whose rules keyed on a `_spec` name have
nothing to read here — no statement in this file names one — so only its
shape rules apply; `tools/check_lean_pin_evidence.py`, which resolves
every `kernel:` line's symbols against the pinned tree and, on a positive
pin, requires each errno constant the statement names to be spelled in
the cited function, and compares a cited macro's value with this tree's
Lean definition of the same name, reading a numeral in the statement only
for a macro that has none, which no macro cited here is — so whether 2,
32770 or 98304 is the word Linux really holds is settled by the citation
beside each and by nothing mechanical; and
`tools/check_kernel_citations.py --only lean`, which pairs each
backticked kernel name with the `file:lines` beside it.  NOT
`tools/check_lean_cases_parity.py`: this file is unmirrored, so the
restatement of Rocq's `Example`s is a reading a reviewer repeats, on no
register.  NOT the mutation gate, which scores spec twins alone: a
mutation pass over this module is a review-time measurement, recorded
with the review that ran it and not here.

THE FIXTURES of the sections above `V_Fs_Fcntl` are
`Checks/Cases/Fs/Fcntl.lean`'s `fcntl_model` (Rocq's),
`fcntl_devnull_model` and `fcntl_urandom_model`, so that spec and checker
are pinned on the same tables; which fd holds which kind is that file's to
say, and each pin below names the kind it relies on.  A fourth table,
`fcntl_listening_model`, is this file's own and sits beside the pins that
read it.  The two device kinds have no Rocq conjunct — Rocq's case file
predates them — and carry the citation of the spec pin they read against.

THE WITNESS IS PINNED HERE TOO.  `fcntl_witness`, in the checker's file,
is the one outcome the arm the V ticket builds over this checker offers at
every call and model, and `fcntl_witness_ok` proves the spec admits it —
through the spec, which is also the only way the four checker lemmas tie
the witness to the checker.  A spec, checker and witness changed the same
wrong way keep all of that closing, so the witness section names the
witness's answer on the fixture arm by arm, feeds the witness back to the
checker at every call and model without opening the spec, proves that
every acceptance of the checker is the witness's answer on the same model
with no event, and proves the witness declines exactly where the checker
does, the way `Checks/Cases/Checks/Sys/Fs/Sync.lean` pins `fsync_witness`.

NOTHING HERE COMPARES THE LEAN CHECKER TO THE ROCQ ONE.  What these pins
prove is that this checker and a named line of Linux agree on what is
accepted and what is refused. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Fcntl

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Fcntl
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Fcntl
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude (fixture_of)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Fcntl
  (fcntl_fds fcntl_model fcntl_append_model fcntl_devnull_model fcntl_urandom_model)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude (ret_outcome)

/-! ## Rocq's examples, one conjunct each

Each pin restates one conjunct of the Rocq `Example` its prose names; the
kernel reading is on that example and on the spec pin of the same call in
`Checks/Cases/Fs/Fcntl.lean`, and is not repeated beyond the line the
evidence names. -/

/-- The unknown command on a closed fd is -EBADF, and the checker admits it.
Rocq's `fcntl_unknown_cmd_on_closed_fd_is_ebadf`.
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem check_unknown_cmd_on_closed_fd_is_ebadf :
    check_fcntl 9 57005 0 (mkEffect (errno_ret EBADF) [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- …and `do_fcntl`'s -EINVAL for the unknown command, which a closed fd never
reaches under Linux, is refused.  Refused, not declined: the checker
mirrors the spec twin's EBADF-certain answer, and that answer is Linux's
alone.  qemu-user translates the command before it resolves the
descriptor — `do_fcntl` (linux-user/syscall.c:7452, QEMU v11.1.1) calls
`target_to_host_fcntl_cmd` (:7175), whose `default:` is -TARGET_EINVAL
(:7262-7263), and returns that errno at :7462-7463 before any host
`fcntl(fd, …)` could report the closed fd — so on that supported
implementation the very call pinned here answers -EINVAL.  The pin stands
because this checker restates the Rocq one and every register of the
answer moves together;
`bugs/fcntl-unknown-cmd-on-closed-fd-admits-linux-alone.md` records the
divergence and what closes it.
Rocq's `fcntl_unknown_cmd_on_closed_fd_is_ebadf`.
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem check_unknown_cmd_on_closed_fd_einval_rejected :
    check_fcntl 9 57005 0 (mkEffect (errno_ret EINVAL) [] []) fcntl_model
      = CheckReject := rfl

/-- F_SETFD is 0 on a channel.
Rocq's `fcntl_setfd_on_channel_is_zero`.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem check_setfd_on_channel_is_zero :
    check_fcntl 1 2 1 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- F_SETFD does not read its arg beyond FD_CLOEXEC: a garbage word is 0.
The bit IS set here — `argi & FD_CLOEXEC` is 1 for 0xDEADBEEF — and the
model records no close-on-exec flag; that dropping the unrecorded bit is
sound is the spec twin's argument, on `fcntl_spec`, not this pin's.
Rocq's `fcntl_setfd_ignores_its_arg`.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem check_setfd_garbage_arg_is_zero :
    check_fcntl 3 2 3735928559 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- …and so is 2, the value that CLEARS close-on-exec rather than erring.
Rocq's `fcntl_setfd_ignores_its_arg`.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem check_setfd_arg_two_is_zero :
    check_fcntl 3 2 2 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- The empty F_SETFL (O_LARGEFILE alone) answers 0 on a file.
Rocq's `fcntl_setfl_empty_file_vs_channel`.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_empty_on_file_is_zero :
    check_fcntl 3 4 32768 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- …and the same call DECLINES on fd 1, the channel.
Rocq's `fcntl_setfl_empty_file_vs_channel`.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_empty_on_channel_declines :
    check_fcntl 1 4 32768 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- The mask's edge, answering side: O_DSYNC (4096) is a bit `setfl` never
reads, so 0.
Rocq's `fcntl_setfl_mask_edge`.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_o_dsync_is_zero :
    check_fcntl 3 4 4096 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- …and its declining side: FASYNC (8192), the adjacent bit, is read by the
`f_op->fasync` test and declines.
Rocq's `fcntl_setfl_mask_edge`.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_fasync_declines :
    check_fcntl 3 4 8192 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- `cmd32` is 32 bits wide (`unsigned int cmd`, fs/fcntl.c:574, Linux
v6.18.46): the high half of `2^32 + 2` is dropped, so it still names
F_SETFD and answers 0.  That bit 31 is KEPT is the next pin.
Rocq's `fcntl_cmd32_keeps_bit_31`.
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem check_cmd32_high_half_is_setfd :
    check_fcntl 3 (cmd32 4294967298) 1 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- …while `2^31 + 2` names no command, and the 0 a 31-bit `cmd32` would
answer is declined.
Rocq's `fcntl_cmd32_keeps_bit_31`.
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem check_cmd32_bit_31_declines :
    check_fcntl 3 (cmd32 2147483650) 1 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- …and bit 31 is kept on the other two commands too: `cmd32 (2^31 + 3)`
is not F_GETFL and `cmd32 (2^31 + 4)` is not F_SETFL, so the socket's 2 and
the file's empty-word 0 are declined.  `fcntl`'s `unsigned int cmd`
(fs/fcntl.c:574, Linux v6.18.46) keeps the bit and `do_fcntl`'s switch
has no such case (:553-555); a checker that narrowed `cmd` to 31 bits on
the F_GETFL or F_SETFL path alone would answer here.
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem check_cmd32_bit_31_declines_getfl_and_setfl :
    check_fcntl 6 (cmd32 2147483651) 0 (mkEffect 2 [] []) fcntl_model = CheckUnmodeled
    ∧ check_fcntl 3 (cmd32 2147483652) 32768 (mkEffect 0 [] []) fcntl_model = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- An all-ones cmd is unrecognized, and even `do_fcntl`'s own -EINVAL for it
is declined rather than admitted.
Rocq's `fcntl_cmd32_keeps_bit_31`.
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem check_cmd_all_ones_declines_its_einval :
    check_fcntl 3 (cmd32 18446744073709551615) 0 (mkEffect (errno_ret EINVAL) [] [])
      fcntl_model = CheckUnmodeled := rfl

/-- The mask, bit by bit: O_APPEND (1024) declines.
Rocq's `fcntl_setfl_every_mask_bit_declines`.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_o_append_declines :
    check_fcntl 3 4 1024 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- O_NONBLOCK (2048) declines.
Rocq's `fcntl_setfl_every_mask_bit_declines`.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_o_nonblock_declines :
    check_fcntl 3 4 2048 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- O_DIRECT (16384) declines — one of the two bits nothing else in the
development reaches.
Rocq's `fcntl_setfl_every_mask_bit_declines`.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_o_direct_declines :
    check_fcntl 3 4 16384 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- O_NOATIME (262144) declines — the other.
Rocq's `fcntl_setfl_every_mask_bit_declines`.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_o_noatime_declines :
    check_fcntl 3 4 262144 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- …and the errnos `setfl` itself can answer on the file for two of those
bits are declined as well, not refused: -EINVAL for O_DIRECT on a file
whose `f_mode` lacks FMODE_CAN_ODIRECT (fs/fcntl.c:62-65, Linux v6.18.46;
the setter is `do_dentry_open`'s, fs/open.c:978-979, and depends on the
filesystem), and -EPERM for O_NOATIME from a caller who is not the
inode's owner (fs/fcntl.c:52-54).  The model knows neither the filesystem
nor the owner, so it takes no side between these and the 0 declined
above.
kernel: fs/fcntl.c:do_fcntl,setfl; fs/open.c:do_dentry_open@v6.18.46 -/
theorem check_setfl_o_direct_einval_and_o_noatime_eperm_on_file_decline :
    check_fcntl 3 4 16384 (mkEffect (errno_ret EINVAL) [] []) fcntl_model = CheckUnmodeled
    ∧ check_fcntl 3 4 262144 (mkEffect (errno_ret EPERM) [] []) fcntl_model = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- The whole mask at once declines.
Rocq's `fcntl_setfl_every_mask_bit_declines`.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_whole_mask_declines :
    check_fcntl 3 4 289792 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- …and a high half over one of its bits (`2^32 + 2048`): the kernel's own
truncation cannot rescue it, and neither does the model.
Rocq's `fcntl_setfl_every_mask_bit_declines`.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_high_half_over_mask_bit_declines :
    check_fcntl 3 4 4294969344 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- The accepting half of the neighbourhood: O_DIRECTORY (65536) is 0.
Rocq's `fcntl_setfl_unread_flags_are_zero`.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_o_directory_is_zero :
    check_fcntl 3 4 65536 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- O_NOFOLLOW (131072) is 0.
Rocq's `fcntl_setfl_unread_flags_are_zero`.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_o_nofollow_is_zero :
    check_fcntl 3 4 131072 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- O_SYNC (1052672, the whole word) is 0.
Rocq's `fcntl_setfl_unread_flags_are_zero`.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_o_sync_is_zero :
    check_fcntl 3 4 1052672 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- O_PATH (2097152) is 0.
Rocq's `fcntl_setfl_unread_flags_are_zero`.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_o_path_is_zero :
    check_fcntl 3 4 2097152 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- `arg`'s sign bit (`2^31`) is 0: `do_fcntl` narrows through a SIGNED
`int argi = (int)arg` (fs/fcntl.c:448, Linux v6.18.46) and `setfl`'s
`unsigned int arg` (:39) reads the bit pattern back, so no path tests the
sign.
Rocq's `fcntl_setfl_unread_flags_are_zero`.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_sign_bit_is_zero :
    check_fcntl 3 4 2147483648 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- `fd32` on a LIVE fd: `2^32 + 3` is fd 3, and F_SETFD on it is 0.
Rocq's `fcntl_fd32_on_a_live_fd`.
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem check_fd32_on_a_live_fd_is_zero :
    check_fcntl (fd32 4294967299) 2 1 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- …and the -EBADF an untruncated fd would earn is refused.
Rocq's `fcntl_fd32_on_a_live_fd`.
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem check_fd32_on_a_live_fd_ebadf_rejected :
    check_fcntl (fd32 4294967299) 2 1 (mkEffect (errno_ret EBADF) [] []) fcntl_model
      = CheckReject := rfl

/-- …and the channel exclusion survives the truncation: `2^32 + 1` is fd 1.
Rocq's `fcntl_fd32_on_a_live_fd`.
kernel: fs/fcntl.c:fcntl,do_fcntl,setfl@v6.18.46 -/
theorem check_fd32_channel_exclusion_survives :
    check_fcntl (fd32 4294967297) 4 32768 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- A write-created file takes the file answer: the empty F_SETFL is 0.
Rocq's `fcntl_on_a_write_fd_and_a_directory_fd`.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_empty_on_write_fd_is_zero :
    check_fcntl 4 4 32768 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- So does a directory fd.
Rocq's `fcntl_on_a_write_fd_and_a_directory_fd`.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_empty_on_directory_is_zero :
    check_fcntl 5 4 32768 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- F_SETFD is 0 on the directory fd.
Rocq's `fcntl_on_a_write_fd_and_a_directory_fd`.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem check_setfd_on_directory_is_zero :
    check_fcntl 5 2 1 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- …and O_NONBLOCK on the directory fd declines like on every file kind.
Rocq's `fcntl_on_a_write_fd_and_a_directory_fd`.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_o_nonblock_on_directory_declines :
    check_fcntl 5 4 2048 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- The socket, the fifth `FdEntry` kind: the empty F_SETFL is 0.
Rocq's `fcntl_setfl_on_a_socket_fd`.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_empty_on_socket_is_zero :
    check_fcntl 6 4 32768 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- FASYNC on the socket declines — the bit that keeps a modeled F_SETFL
off every fasync list.
Rocq's `fcntl_setfl_on_a_socket_fd`.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_fasync_on_socket_declines :
    check_fcntl 6 4 8192 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- F_SETFD is 0 on the socket, as on every kind.
Rocq's `fcntl_setfl_on_a_socket_fd`.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem check_setfd_on_socket_is_zero :
    check_fcntl 6 2 1 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- F_GETFL on a socket is O_RDWR exactly, and the checker admits the 2.
Rocq's `fcntl_getfl_on_a_socket_fd_is_o_rdwr`.
kernel: fs/fcntl.c:do_fcntl; net/socket.c:sock_alloc_file; include/uapi/asm-generic/fcntl.h:O_RDWR@v6.18.46 -/
theorem check_getfl_on_socket_is_o_rdwr :
    check_fcntl 6 3 0 (mkEffect 2 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- THE CONJUNCT THAT MATTERS: 32770, the O_RDWR|O_LARGEFILE word a
glibc-hosted qemu-user reports — the one read source of it, per the spec
twin's `socket_f_flags` and `bugs/fcntl-getfl-socket-arm-admits-linux-alone.md`
— is refused.  A model that
ORed O_LARGEFILE into the socket's answer accepts it and fails here.
Rocq's `fcntl_getfl_on_a_socket_fd_is_o_rdwr`.
kernel: fs/fcntl.c:do_fcntl; net/socket.c:sock_alloc_file; fs/open.c:openat; include/uapi/asm-generic/fcntl.h:O_LARGEFILE@v6.18.46 -/
theorem check_getfl_on_socket_o_largefile_rejected :
    check_fcntl 6 3 0 (mkEffect 32770 [] []) fcntl_model
      = CheckReject := rfl

/-- F_GETFL declines on a channel.
Rocq's `fcntl_getfl_declines_on_every_other_fd_kind`.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem check_getfl_on_channel_declines :
    check_fcntl 0 3 0 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- F_GETFL declines on a read-only file.
Rocq's `fcntl_getfl_declines_on_every_other_fd_kind`.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem check_getfl_on_file_declines :
    check_fcntl 3 3 0 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- F_GETFL declines on a write-only file.
Rocq's `fcntl_getfl_declines_on_every_other_fd_kind`.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem check_getfl_on_write_fd_declines :
    check_fcntl 4 3 0 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- F_GETFL declines on a directory fd.
Rocq's `fcntl_getfl_declines_on_every_other_fd_kind`.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem check_getfl_on_directory_declines :
    check_fcntl 5 3 0 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- F_GETFD still declines on the socket F_GETFL answers: a socket's
`f_flags` is a function of the constructor, its close-on-exec bit is not.
Rocq's `fcntl_getfd_still_declines_on_a_socket_fd`.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:get_close_on_exec@v6.18.46 -/
theorem check_getfd_on_socket_declines_zero :
    check_fcntl 6 1 0 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- …for the 1 as well as the 0.
Rocq's `fcntl_getfd_still_declines_on_a_socket_fd`.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:get_close_on_exec@v6.18.46 -/
theorem check_getfd_on_socket_declines_one :
    check_fcntl 6 1 0 (mkEffect 1 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- F_GETFL declines on the pipe's read end.
Rocq's `fcntl_getfl_declines_on_both_pipe_ends`.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem check_getfl_on_pipe_reader_declines :
    check_fcntl 7 3 0 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- …and on the write end, offered the O_WRONLY (1) Linux really reports:
`create_pipe_files` builds that end from `O_WRONLY | (flags & (O_NONBLOCK |
O_DIRECT))` (fs/pipe.c:944-946, Linux v6.18.46) and the model's `pipe2`
admits flags 0 alone.
Rocq's `fcntl_getfl_declines_on_both_pipe_ends`.
kernel: fs/fcntl.c:do_fcntl; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem check_getfl_on_pipe_writer_declines_o_wronly :
    check_fcntl 8 3 0 (mkEffect 1 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- …and offered 0.
Rocq's `fcntl_getfl_declines_on_both_pipe_ends`.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem check_getfl_on_pipe_writer_declines_zero :
    check_fcntl 8 3 0 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- /dev/null: the empty F_SETFL declines at the checker as at the spec.
kernel: fs/fcntl.c:setfl@v6.18.46 -/
theorem check_setfl_empty_on_devnull_declines :
    check_fcntl 11 4 0 (mkEffect 0 [] []) fcntl_devnull_model
      = CheckUnmodeled := rfl

/-- …and F_SETFD is 0 there.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem check_setfd_on_devnull_is_zero :
    check_fcntl 11 2 1 (mkEffect 0 [] []) fcntl_devnull_model
      = CheckOk fcntl_devnull_model [] := rfl

/-- O_NONBLOCK on /dev/null declines too, the pair of the /dev/urandom
decline below: `setfl` stores the bit through `SETFL_MASK` (fs/fcntl.c:37,
:83, Linux v6.18.46) into an `f_flags` word the `FdDevNull` entry does not
record, and the arm declines the device on every word.  Not because the
device reads the bit: `read_null` (drivers/char/mem.c:412-416, Linux
v6.18.46) and `write_null` (drivers/char/mem.c:418-422) test nothing at
all.
kernel: fs/fcntl.c:setfl; drivers/char/mem.c:read_null,write_null@v6.18.46 -/
theorem check_setfl_o_nonblock_on_devnull_declines :
    check_fcntl 11 4 2048 (mkEffect 0 [] []) fcntl_devnull_model
      = CheckUnmodeled := rfl

/-- /dev/urandom: the empty F_SETFL declines at the checker as at the spec:
the `FdUrandom` arm of `setfl_noop_on` is `false` for every word, which
the twin labels fail-closed — on a mask-clear word no branch of `setfl`
fires, so a 0 would be derivable, and is not written — and what the twin
holds against calling the device
inert under `setfl` at large is `urandom_fops`'s `.fasync = random_fasync`
(drivers/char/random.c:1577, Linux v6.18.46), reached on a FASYNC toggle
(fs/fcntl.c:75-76).  No per-word answer is written.
kernel: fs/fcntl.c:setfl; drivers/char/random.c:random_fasync@v6.18.46 -/
theorem check_setfl_empty_on_urandom_declines :
    check_fcntl 12 4 0 (mkEffect 0 [] []) fcntl_urandom_model
      = CheckUnmodeled := rfl

/-- …and F_SETFD is 0 there.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem check_setfd_on_urandom_is_zero :
    check_fcntl 12 2 1 (mkEffect 0 [] []) fcntl_urandom_model
      = CheckOk fcntl_urandom_model [] := rfl


/-! ## The refusing half of `check_ret_only`, and the calls Rocq pins elsewhere

The pins above restate Rocq's `Checks/Cases/Fs/Fcntl.v` conjunct for
conjunct.  The rest of this file's checker pins are Lean-side: what the
adversarial pass over the checker asked for and Rocq's case file never
stated, section by section, and then the witness.

THE EFFECT'S SHAPE.  `check_ret_only` (`Checks/Sys/Prelude.lean`) is the
whole of what the accepting arms compare against, so the shape a lying
kernel can offer — a nonzero success, an errno `setfl` really returns on
OTHER arguments (`-EPERM`, `-EINVAL`) and never on the empty word, a
ledger entry of each kind on a command that touches no user memory, and,
on F_GETFL, the `O_NONBLOCK`-bearing word a `SOCK_NONBLOCK` socket would
carry, the 0 a `f_flags`-less checker would echo, and an `-EBADF` on a
live fd — is pinned refused below, one pin per shape.

THE PIPE ENDS AND THE DEVICES.  Why the two fcntl `Example`s of Rocq's
`Checks/Cases/Fs/Pipe.v` land here is in the header; what they pin, on
`fcntl_model`'s ends at fds 7 and 8, is that F_SETFL declines on both ends
even at `arg = 0` while the same word answers on a file, and that F_SETFD
is 0 with `-EBADF` refused on the read end — the write end's 0, and the 1
refused there, are this file's additions.  The two device fixtures get the
same treatment: their empty-F_SETFL, F_GETFL and O_NONBLOCK declines are
paired with an answering pin over the SAME fixture, so a checker that has
gone quiet across the whole table fails here rather than passing on
declines alone.

WHAT THE HIGH HALF ANSWERS.  Every high-half pin above declines; none says
that a high half can ANSWER.  Linux narrows `arg` to `int argi = (int)arg`
(`do_fcntl`, fs/fcntl.c:448, Linux v6.18.46, commit 1f99e9ab748f) and
`setfl` reads only the five bits of `setfl_acted_on` in that int —
SETFL_MASK's four distinct bits, O_NDELAY being O_NONBLOCK on riscv64,
plus FASYNC — on the modeled kinds (the one `check_flags` in the tree is
NFS's; `check_setfl_empty_einval_rejected` below carries that claim and
the condition that falsifies it), so a word whose low 32 bits are clear,
or whose set bits all lie outside the mask, is the empty F_SETFL and
answers 0 — the model's `bv_and` with the 64-bit mask agrees without
truncating.  On the fd side, `fd32` keeps bit 31, and Linux's
`unsigned int fd` keeps it too: the lookup that decides is
`files_lookup_fd_raw` (include/linux/fdtable.h:72-86, Linux v6.18.46) on
an unshared table and `__fget_files_rcu` (fs/file.c:989-1063) on a shared
one — `__fget_light` (fs/file.c:1167-1173) picks by `files->count` — and
each masks with array_index_mask_nospec(fd, fdt->max_fds)
(include/linux/fdtable.h:75; fs/file.c:999), zero for every fd at or above the table's max_fds, and the
table never grows past
`sysctl_nr_open_max` (fs/file.c:100-101, Linux v6.18.46), below 2^31 — so
2^31+3 names no
live descriptor and is `-EBADF`, not fd 3, and an all-ones word is fd
4294967295, `-EBADF` as well.  `cmd32` keeps bit 31 for F_GETFL and F_SETFL as it does for F_SETFD
(the pins beside Rocq's `fcntl_cmd32_keeps_bit_31` above).  The narrowing itself is the arm's and not the checker's,
and one pin says so by feeding the checker the raw word: 2^32+3 unnarrowed
names no descriptor of the fixture, so the checker admits `-EBADF` where
the narrowed word makes it refuse the same errno.  F_GETOWN, a real command the model does not know,
declines even when offered the 0 Linux really answers on a fresh socket
(`f_getown`, fs/fcntl.c:195-214, Linux v6.18.46). -/

/-- F_SETFD answers 0 and nothing else: an F_GETFD-style echo of the arg is
refused.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem check_setfd_one_rejected :
    check_fcntl 3 2 1 (mkEffect 1 [] []) fcntl_model
      = CheckReject := rfl

/-- `do_fcntl`'s -EINVAL never reaches F_SETFD; offered on it, refused.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem check_setfd_einval_rejected :
    check_fcntl 3 2 2 (mkEffect (errno_ret EINVAL) [] []) fcntl_model
      = CheckReject := rfl

/-- `setfl`'s -EPERM needs an O_APPEND delta on an append-only inode, or
O_NOATIME from a caller who does not own the inode; the empty word has
neither, so the errno is refused on it.  Refused under the spec twin's LSM
stance, which commits to `setfl`'s answers absolutely although the LSM
hook at fs/fcntl.c:587, `security_file_fcntl` (security/security.c:3223,
Linux v6.18.46), runs first: of the three hand-written in-tree hooks,
SELinux's `selinux_file_fcntl` (security/selinux/hooks.c:4158-4196, Linux
v6.18.46) asks FILE__WRITE on the inode only when F_SETFL CLEARS an
O_APPEND the file holds (:4166-4169) — a word no answered kind can carry,
`openat_resolved_spec` sending the append word to `unmodeled` — and
otherwise FD__USE, gated on the caller's SID differing from the opener's
(`__file_has_perm`, security/selinux/hooks.c:1776-1780), and either
denial is -EACCES (`avc_denied`, security/selinux/avc.c:999-1004), never
the -EPERM refused here; Smack's `smack_file_fcntl`
(security/smack/smack_lsm.c:1797, Linux v6.18.46) has no F_SETFL case,
and TOMOYO's `tomoyo_file_fcntl` (security/tomoyo/tomoyo.c:312-319, Linux
v6.18.46) acts only on an O_APPEND toggle, which the empty word is not.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_empty_eperm_rejected :
    check_fcntl 3 4 32768 (mkEffect (errno_ret EPERM) [] []) fcntl_model
      = CheckReject := rfl

/-- …and `setfl`'s -EINVAL needs O_DIRECT on a file without
FMODE_CAN_ODIRECT, or a `check_flags` refusal — and the only `check_flags`
any `file_operations` in the tree sets, NFS's `nfs_check_flags`
(fs/nfs/file.c:50-56, Linux v6.18.46), installed by `nfs_file_operations`
(fs/nfs/file.c:965) and `nfs4_file_operations` (fs/nfs/nfs4file.c:449),
refuses O_APPEND|O_DIRECT together, both inside the mask, so the empty
word passes it on every filesystem the file could be on; refused here too.
This claim stops being true the day a second `file_operations` sets
`.check_flags`: `grep -rn '\.check_flags' ` over v6.18.46 finds NFS's two
installs and `struct intel_gtt_driver`'s unrelated member of the same
name, and nothing else.  The other two pins that lean on it,
`check_setfl_empty_on_directory_einval_rejected` and the section header
above, point here rather than repeating it.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_empty_einval_rejected :
    check_fcntl 3 4 32768 (mkEffect (errno_ret EINVAL) [] []) fcntl_model
      = CheckReject := rfl

/-- F_SETFD touches no user memory: a reported write is refused.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem check_setfd_with_a_write_rejected :
    check_fcntl 3 2 1 (mkEffect 0 [(Z_to_bv 64 4096, [0])] []) fcntl_model
      = CheckReject := rfl

/-- …and so is a reported zero-fill.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem check_setfd_with_a_zero_range_rejected :
    check_fcntl 3 2 1 (mkEffect 0 [] [(Z_to_bv 64 4096, Z_to_bv 64 8)])
      fcntl_model = CheckReject := rfl

/-- F_GETFL reads no user memory either: the right word with a copy-in
ledger is refused — the shape a future F_GETLK arm must NOT inherit.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem check_getfl_on_socket_with_a_copyin_rejected :
    check_fcntl 6 3 0 (with_copyins [(Z_to_bv 64 4096, 8)] (mkEffect 2 [] []))
      fcntl_model = CheckReject := rfl

/-- 2050 is O_RDWR|O_NONBLOCK, the word a SOCK_NONBLOCK socket carries; the
fixture's socket is a plain one and the word is refused.
kernel: fs/fcntl.c:do_fcntl; net/socket.c:sock_alloc_file; include/uapi/asm-generic/fcntl.h:O_RDWR,O_NONBLOCK@v6.18.46 -/
theorem check_getfl_on_socket_o_nonblock_word_rejected :
    check_fcntl 6 3 0 (mkEffect 2050 [] []) fcntl_model
      = CheckReject := rfl

/-- …and 0, the echo of a checker with no `f_flags` at all, is refused.
kernel: fs/fcntl.c:do_fcntl; net/socket.c:sock_alloc_file; include/uapi/asm-generic/fcntl.h:O_RDWR@v6.18.46 -/
theorem check_getfl_on_socket_zero_rejected :
    check_fcntl 6 3 0 (mkEffect 0 [] []) fcntl_model
      = CheckReject := rfl

/-- …and -EBADF on a live socket fd is refused: `fd_empty` is false.
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem check_getfl_on_socket_ebadf_rejected :
    check_fcntl 6 3 0 (mkEffect (errno_ret EBADF) [] []) fcntl_model
      = CheckReject := rfl

/-- F_SETFL declines on the pipe's read end even at `arg = 0`: not a gap —
every pipe end the model can build was made by `pipe2(…, 0)`, so its
`f_flags` is O_RDONLY (0) on the read end and O_WRONLY (1) on the write end
(`create_pipe_files`, fs/pipe.c:944-946 and :956-957, Linux v6.18.46),
neither inside `SETFL_MASK`, and Linux answers 0 here — but the spec twin's
CHOICE (`setfl_noop_on`'s `FdPipe` bullet):
O_DIRECT is the live packet-mode bit, `is_packetized` being
`(file->f_flags & O_DIRECT) != 0` (fs/pipe.c:415-418, Linux v6.18.46),
and `pipeanon_fops` carries `.fasync = pipe_fasync` (:1264), so the kind
is not inert under `setfl` and no per-word answer is written for it.
kernel: fs/fcntl.c:setfl; fs/pipe.c:is_packetized,pipe_fasync@v6.18.46 -/
theorem check_setfl_arg_zero_on_pipe_reader_declines :
    check_fcntl 7 4 0 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- …and on the write end, the same choice.
kernel: fs/fcntl.c:setfl; fs/pipe.c:is_packetized,pipe_fasync@v6.18.46 -/
theorem check_setfl_arg_zero_on_pipe_writer_declines :
    check_fcntl 8 4 0 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- …and the two bits whose pipe meaning the pins above cite are declined
on the words that carry them: O_DIRECT (16384), which `setfl` exempts a
FIFO from the FMODE_CAN_ODIRECT test for (fs/fcntl.c:62, Linux v6.18.46)
and stores as packet mode (`is_packetized`, fs/pipe.c:415-418), on the
writer; and FASYNC (8192), which reaches `pipe_fasync` (fs/pipe.c:748-765,
installed as `pipeanon_fops`'s `.fasync` at :1264) from the toggle at
fs/fcntl.c:75-76, on the reader.  Both
are stored changes to a pipe the model records no `f_flags` for, declined
offered the 0 Linux answers.
kernel: fs/fcntl.c:do_fcntl,setfl; fs/pipe.c:is_packetized,pipe_fasync@v6.18.46 -/
theorem check_setfl_o_direct_and_fasync_on_pipe_ends_decline :
    check_fcntl 8 4 16384 (mkEffect 0 [] []) fcntl_model = CheckUnmodeled
    ∧ check_fcntl 7 4 8192 (mkEffect 0 [] []) fcntl_model = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- …while the same `arg = 0` answers 0 on a write-created file: the
decline is the pipe's, not the argument's.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_arg_zero_on_write_fd_is_zero :
    check_fcntl 4 4 0 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- …and O_DSYNC (4096) on the same write-created file is 0 as well: the
bit is outside `SETFL_MASK` (fs/fcntl.c:37, Linux v6.18.46), so the closing
`f_flags = (arg & SETFL_MASK) | (f_flags & ~SETFL_MASK)` (:83) leaves the
word as it was and `setfl` returns 0.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_o_dsync_on_write_fd_is_zero :
    check_fcntl 4 4 4096 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- Rocq's `fcntl_flag_commands_decline_on_an_append_fd`, its first
conjunct: F_SETFL with `arg` 0 on the append fd 10 of `fcntl_append_model`
declines.  `f_flags` carries O_APPEND, so `setfl` answers -EPERM on an
append-only inode (fs/fcntl.c:48, Linux v6.18.46) and otherwise CLEARS
O_APPEND at :83.
kernel: fs/fcntl.c:setfl@v6.18.46 -/
theorem check_setfl_arg_zero_on_append_fd_declines :
    check_fcntl 10 4 0 (mkEffect 0 [] []) fcntl_append_model
      = CheckUnmodeled := rfl

/-- …the second: the identical call on fd 4 of the same model answers 0,
which is what makes the decline a claim about the fd kind.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_arg_zero_beside_append_fd_is_zero :
    check_fcntl 4 4 0 (mkEffect 0 [] []) fcntl_append_model
      = CheckOk fcntl_append_model [] := rfl

/-- …the third: O_DSYNC, a bit `setfl` never reads, declines on fd 10 as
well, since a word without O_APPEND clears it (fs/fcntl.c:37, :83, Linux
v6.18.46).
kernel: fs/fcntl.c:setfl@v6.18.46 -/
theorem check_setfl_o_dsync_on_append_fd_declines :
    check_fcntl 10 4 4096 (mkEffect 0 [] []) fcntl_append_model
      = CheckUnmodeled := rfl

/-- …the fourth: the same word on fd 4 is 0.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_o_dsync_beside_append_fd_is_zero :
    check_fcntl 4 4 4096 (mkEffect 0 [] []) fcntl_append_model
      = CheckOk fcntl_append_model [] := rfl

/-- …the fifth: F_GETFL declines on fd 10 (`getfl_f_flags`).
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem check_getfl_on_append_fd_declines :
    check_fcntl 10 3 0 (mkEffect 0 [] []) fcntl_append_model
      = CheckUnmodeled := rfl

/-- …and the sixth: F_SETFD, which never reads `f_flags`, answers 0 on
fd 10, keeping the declines above confined to the flag word.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem check_setfd_on_append_fd_is_zero :
    check_fcntl 10 2 1 (mkEffect 0 [] []) fcntl_append_model
      = CheckOk fcntl_append_model [] := rfl

/-- F_SETFD is 0 on the pipe's read end, as on every kind.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem check_setfd_on_pipe_reader_is_zero :
    check_fcntl 7 2 1 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- …and -EBADF on that live end is refused.
kernel: fs/fcntl.c:fcntl,do_fcntl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem check_setfd_on_pipe_reader_ebadf_rejected :
    check_fcntl 7 2 1 (mkEffect (errno_ret EBADF) [] []) fcntl_model
      = CheckReject := rfl

/-- F_SETFD is 0 on the write end too.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem check_setfd_on_pipe_writer_is_zero :
    check_fcntl 8 2 1 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- F_GETFL declines on /dev/null, offered the O_RDWR|O_LARGEFILE word its
fixture entry would carry (O_LARGEFILE is `openat`'s, ORed in at
fs/open.c:1466-1467, Linux v6.18.46).
kernel: fs/fcntl.c:do_fcntl; fs/open.c:openat; include/uapi/asm-generic/fcntl.h:O_LARGEFILE@v6.18.46 -/
theorem check_getfl_on_devnull_declines :
    check_fcntl 11 3 0 (mkEffect 32770 [] []) fcntl_devnull_model
      = CheckUnmodeled := rfl

/-- …and on /dev/urandom, offered O_RDONLY|O_LARGEFILE (32768), the word
`openat` gives a path-opened file (fs/open.c:1466-1467, Linux v6.18.46).
kernel: fs/fcntl.c:do_fcntl; fs/open.c:openat; include/uapi/asm-generic/fcntl.h:O_LARGEFILE@v6.18.46 -/
theorem check_getfl_on_urandom_declines :
    check_fcntl 12 3 0 (mkEffect 32768 [] []) fcntl_urandom_model
      = CheckUnmodeled := rfl

/-- …and the bare 0 is declined on both devices as well, so the two
declines above are not "the checker knows the word and it is not this
one": `getfl_f_flags` has no arm for either device.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem check_getfl_on_devices_declines_zero :
    check_fcntl 11 3 0 (mkEffect 0 [] []) fcntl_devnull_model = CheckUnmodeled
    ∧ check_fcntl 12 3 0 (mkEffect 0 [] []) fcntl_urandom_model = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- O_NONBLOCK on /dev/urandom declines: `setfl` stores the bit through
`SETFL_MASK` (fs/fcntl.c:37, :83, Linux v6.18.46) into an `f_flags` word
the `FdUrandom` entry does not record, and the arm declines the device on
every word.  Not because the device reads the bit: `urandom_read_iter`
(drivers/char/random.c:1453-1475) tests no flag, and the O_NONBLOCK test
at :1481-1484 is `random_read_iter`'s, /dev/random's.
kernel: fs/fcntl.c:setfl; drivers/char/random.c:urandom_read_iter,random_read_iter@v6.18.46 -/
theorem check_setfl_o_nonblock_on_urandom_declines :
    check_fcntl 12 4 2048 (mkEffect 0 [] []) fcntl_urandom_model
      = CheckUnmodeled := rfl

/-- …and FASYNC (8192) declines there on the word that carries the reason
the empty-word pin gives: `random_fasync` (drivers/char/random.c:1555-1558,
Linux v6.18.46) is `urandom_fops`'s `.fasync` (:1577), which the toggle at
fs/fcntl.c:75-76 calls, and the model records neither the FASYNC bit nor
the owner it would signal.
kernel: fs/fcntl.c:do_fcntl,setfl; drivers/char/random.c:random_fasync@v6.18.46 -/
theorem check_setfl_fasync_on_urandom_declines :
    check_fcntl 12 4 8192 (mkEffect 0 [] []) fcntl_urandom_model
      = CheckUnmodeled := rfl

/-- The answering pin beside the /dev/null declines: the empty F_SETFL on
the file at fd 3 of the SAME fixture is 0.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_empty_on_file_beside_devnull_is_zero :
    check_fcntl 3 4 32768 (mkEffect 0 [] []) fcntl_devnull_model
      = CheckOk fcntl_devnull_model [] := rfl

/-- …and F_GETFL on the socket at fd 6 of the /dev/null fixture is O_RDWR.
kernel: fs/fcntl.c:do_fcntl; net/socket.c:sock_alloc_file; include/uapi/asm-generic/fcntl.h:O_RDWR@v6.18.46 -/
theorem check_getfl_on_socket_beside_devnull_is_o_rdwr :
    check_fcntl 6 3 0 (mkEffect 2 [] []) fcntl_devnull_model
      = CheckOk fcntl_devnull_model [] := rfl

/-- The same two answers over the /dev/urandom fixture.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_empty_on_file_beside_urandom_is_zero :
    check_fcntl 3 4 32768 (mkEffect 0 [] []) fcntl_urandom_model
      = CheckOk fcntl_urandom_model [] := rfl

/-- …and F_GETFL on the socket at fd 6 of the /dev/urandom fixture is O_RDWR.
kernel: fs/fcntl.c:do_fcntl; net/socket.c:sock_alloc_file; include/uapi/asm-generic/fcntl.h:O_RDWR@v6.18.46 -/
theorem check_getfl_on_socket_beside_urandom_is_o_rdwr :
    check_fcntl 6 3 0 (mkEffect 2 [] []) fcntl_urandom_model
      = CheckOk fcntl_urandom_model [] := rfl

/-- A high half alone (`2^32`) is the empty F_SETFL after `(int)arg`, and
answers 0.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_high_half_alone_is_zero :
    check_fcntl 3 4 4294967296 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- So is bit 63 alone.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_bit_63_is_zero :
    check_fcntl 3 4 9223372036854775808 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- So is every bit but the five of the mask (`2^64 - 1 - 289792`): `setfl`
has no "unknown flag" test.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_all_but_mask_is_zero :
    check_fcntl 3 4 18446744073709261823 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- So is the whole mask shifted above the int (`289792 <<< 32`).
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_mask_above_the_int_is_zero :
    check_fcntl 3 4 1244647162642432 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- fd `2^31 + 3` keeps its bit 31 through `fd32` and names no descriptor:
-EBADF is admitted…
kernel: fs/fcntl.c:fcntl@v6.18.46 -/
theorem check_fd_bit_31_is_ebadf :
    check_fcntl (fd32 2147483651) 2 1 (mkEffect (errno_ret EBADF) [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- …and the 0 a 31-bit narrowing would earn on fd 3 is refused.
kernel: fs/fcntl.c:fcntl@v6.18.46 -/
theorem check_fd_bit_31_zero_rejected :
    check_fcntl (fd32 2147483651) 2 1 (mkEffect 0 [] []) fcntl_model
      = CheckReject := rfl

/-- An all-ones fd is 4294967295 after `fd32`, and -EBADF.
kernel: fs/fcntl.c:fcntl@v6.18.46 -/
theorem check_fd_all_ones_is_ebadf :
    check_fcntl (fd32 18446744073709551615) 2 1 (mkEffect (errno_ret EBADF) [] [])
      fcntl_model = CheckOk fcntl_model [] := rfl

/-- `cmd32` on F_GETFL: `2^32 + 3` is F_GETFL and answers O_RDWR on the
socket.
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem check_cmd32_high_half_is_getfl :
    check_fcntl 6 (cmd32 4294967299) 0 (mkEffect 2 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- …and `2^32 + 4` is F_SETFL, answering 0 on the empty word.
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem check_cmd32_high_half_is_setfl :
    check_fcntl 3 (cmd32 4294967300) 32768 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- F_GETOWN (9) on the socket declines, even offered the 0 Linux answers
on a socket nobody has set an owner on.
kernel: fs/fcntl.c:do_fcntl,f_getown@v6.18.46 -/
theorem check_getown_on_socket_declines :
    check_fcntl 6 9 0 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- F_DUPFD (0) declines, even offered the 2 a lowest-free-fd answer gives
on this table.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:f_dupfd,alloc_fd@v6.18.46 -/
theorem check_dupfd_declines :
    check_fcntl 3 0 0 (mkEffect 2 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- F_GETFD (1) on a file declines, offered the 1 a close-on-exec file would
answer.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:get_close_on_exec@v6.18.46 -/
theorem check_getfd_on_file_declines :
    check_fcntl 3 1 0 (mkEffect 1 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- F_GETFL on the read-only file declines even offered O_RDONLY|O_LARGEFILE
(32768), one of the two words a read-only open may leave in `f_flags` — the
other carries O_NONBLOCK — which is why no word is derivable for the kind.
kernel: fs/fcntl.c:do_fcntl; fs/open.c:openat; include/uapi/asm-generic/fcntl.h:O_LARGEFILE@v6.18.46 -/
theorem check_getfl_on_file_declines_its_true_word :
    check_fcntl 3 3 0 (mkEffect 32768 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- The narrowing is the arm's, not the checker's: fed the RAW 2^32+3, the
checker finds no descriptor and admits `-EBADF`, the answer Linux's
`unsigned int fd` never gives to this word; fed the narrowed one it refuses
the same errno (`check_fd32_on_a_live_fd_ebadf_rejected`).  A checker that
narrowed on its own would make the first conjunct false and the arm's
`fd32` redundant.
kernel: fs/fcntl.c:fcntl@v6.18.46 -/
theorem check_fd_narrowing_is_the_arms :
    check_fcntl 4294967299 2 1 (mkEffect (errno_ret EBADF) [] []) fcntl_model
        = CheckOk fcntl_model []
    ∧ check_fcntl (fd32 4294967299) 2 1 (mkEffect (errno_ret EBADF) [] []) fcntl_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-! ## The other side of each arm, and the lies a narrower checker would pass

An adversarial pass over the pins above mutated the checker and the spec
together and asked which pin went red.  These are the pins that were
missing: the DECLINING side of `setfl_noop_on`'s `FdFileW` and `FdSocket`
arms, the fd-before-cmd order on a closed fd for F_GETFL and F_SETFL, a
return that agrees with the right one only in its low 32 bits, a socket in
a state other than `SkFresh`, the positive and echoed returns F_SETFL never
gives, the ledgers no arm may carry, `-EBADF` on a live channel, the `cmd`
narrowing, and the two arguments F_SETFD and F_GETFL ignore.  Each names the
lie it refuses or the answer it keeps, with the line of Linux that decides
it. -/

/-- The `FdFileW` arm of `setfl_noop_on` on its DECLINING side, which no fd-3
pin reaches: `O_APPEND | O_LARGEFILE` (33792), the word musl passes for
`F_SETFL, O_APPEND`, on the write-created fd.  `setfl` stores O_APPEND
through `SETFL_MASK` (fs/fcntl.c:37, :83, Linux v6.18.46) and its one
O_APPEND error is for an append-only inode (`IS_APPEND`, :48-49), so
`setfl` answers 0 here — and under the spec twin's LSM stance so does the
syscall, though this word, unlike the empty one, IS the O_APPEND toggle
`tomoyo_file_fcntl` acts on (security/tomoyo/tomoyo.c:315-318, Linux
v6.18.46), asking an APPEND permission an enforcing policy denies with
-EPERM (security/tomoyo/common.c:2182-2183) ahead of `do_fcntl` — and no
arm turns the descriptor into an `FdFileA` to record it in; the arm
declines.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_o_append_largefile_on_write_fd_declines :
    check_fcntl 4 4 33792 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- O_NONBLOCK (2048) on the SOCKET declines, and this decline is what
`getfl_f_flags`'s socket arm rests on: `setfl` stores the bit through
`SETFL_MASK` (fs/fcntl.c:37, :83, Linux v6.18.46), so a 0 admitted here
would leave the socket's `f_flags` at `O_RDWR | O_NONBLOCK` (2050) while
the model went on answering F_GETFL with 2.  No mask bit is merely wide on
a socket: FASYNC (pinned above) reaches `sock_fasync` (net/socket.c:1471-1490,
the `socket_file_ops` entry at :168) from the toggle at fs/fcntl.c:75-76;
O_APPEND is stored the same way, since the inode `sock_alloc`
(net/socket.c:632-650) gives a socket carries no S_APPEND, so the
IS_APPEND test at fs/fcntl.c:48-49 does not fire; O_NOATIME is stored for
the inode's owner (fs/fcntl.c:52-54), and the owner is the fsuid of the
CREATING task (net/socket.c:645) — the caller, on the model's premise that
no arm changes fsuid between the socket's creation and this call;
O_DIRECT is -EINVAL (fs/fcntl.c:62-65), since the generic FMODE_CAN_ODIRECT
setter is `do_dentry_open`'s (fs/open.c:978-979), a path `alloc_file_pseudo`
never enters, and no socket open method sets it.  O_NONBLOCK is the one
named here because it is also the bit a socket-creating arm could set.
kernel: fs/fcntl.c:do_fcntl,setfl; net/socket.c:sock_alloc_file,sock_alloc,sock_fasync@v6.18.46 -/
theorem check_setfl_o_nonblock_on_socket_declines :
    check_fcntl 6 4 2048 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- F_GETFL on the CLOSED fd 9 is -EBADF although F_GETFL on the open file
at fd 3 is declined: `SYSCALL_DEFINE3(fcntl, …)` resolves the descriptor
and returns -EBADF on an empty slot (fs/fcntl.c:576-580, Linux v6.18.46)
before `do_fcntl` reads `cmd`.  A checker that dispatched on F_GETFL first
would fail closed here and lose a determined answer.
kernel: fs/fcntl.c:fcntl@v6.18.46 -/
theorem check_getfl_on_closed_fd_is_ebadf :
    check_fcntl 9 3 0 (mkEffect (errno_ret EBADF) [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- …and the 0 a live fd could earn is refused there: `cmd` is never read.
kernel: fs/fcntl.c:fcntl@v6.18.46 -/
theorem check_getfl_on_closed_fd_zero_rejected :
    check_fcntl 9 3 0 (mkEffect 0 [] []) fcntl_model
      = CheckReject := rfl

/-- F_SETFL with a MASK bit (O_NONBLOCK) on the closed fd 9 is -EBADF, not
the decline the same word earns on every open kind: the mask is `setfl`'s
(fs/fcntl.c:39-89, Linux v6.18.46) and `setfl` is never reached.  A checker
that tested the mask before the lookup fails here.
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem check_setfl_o_nonblock_on_closed_fd_is_ebadf :
    check_fcntl 9 4 2048 (mkEffect (errno_ret EBADF) [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- F_SETFD on the closed fd 9 answering 0 is refused: the `err = 0`
(fs/fcntl.c:469, Linux v6.18.46) is `do_fcntl`'s and a closed fd never
reaches it.
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem check_setfd_on_closed_fd_zero_rejected :
    check_fcntl 9 2 1 (mkEffect 0 [] []) fcntl_model
      = CheckReject := rfl

/-- A return that agrees with F_SETFD's 0 only in its low half (`2^32`) is
refused: `do_fcntl` returns its `long err` whole (`err = 0` at
fs/fcntl.c:469, `return err` at :556, Linux v6.18.46), and a checker that
compared the low 32 bits alone would accept it; the two pins that follow
refuse the same lie on the F_GETFL and -EBADF arms.
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem check_setfd_high_half_return_rejected :
    check_fcntl 3 2 1 (mkEffect 4294967296 [] []) fcntl_model
      = CheckReject := rfl

/-- `2^32 + 2` on F_GETFL of the socket is refused: `err = filp->f_flags`
(fs/fcntl.c:473, Linux v6.18.46) promotes an `unsigned int` to `long`
value for value, so the high half of the answer is clear.
kernel: fs/fcntl.c:do_fcntl; net/socket.c:sock_alloc_file@v6.18.46 -/
theorem check_getfl_on_socket_high_half_return_rejected :
    check_fcntl 6 3 0 (mkEffect 4294967298 [] []) fcntl_model
      = CheckReject := rfl

/-- -EBADF wrapped to 32 bits (`0xFFFFFFF7`, 4294967287) on the closed fd
is refused: `return -EBADF` (fs/fcntl.c:579-580, Linux v6.18.46) widens the
`int` constant to the syscall's `long`, and riscv's `syscall_handler`
(arch/riscv/include/asm/syscall.h:101-113) stores that whole word into a0,
so a0 is `0xFFFFFFFFFFFFFFF7` and never the zero-extended word a
32-bit-minded checker would take for the same errno.  That word is what
`errno_ret` encodes, and `errno_ret_EBADF_in_a0` in
`Checks/Cases/Sys/Syscall.lean` pins the encoding once for every arm.
kernel: fs/fcntl.c:fcntl; arch/riscv/include/asm/syscall.h:syscall_handler@v6.18.46 -/
theorem check_closed_fd_32bit_ebadf_rejected :
    check_fcntl 9 57005 0 (mkEffect 4294967287 [] []) fcntl_model
      = CheckReject := rfl

/-- The same table with a LISTENING socket at fd 13: a second `SockState`
for the F_GETFL arm to answer on, so that "the answer does not depend on
the state" is pinned on a state other than `SkFresh`, which is the only
one the three fixtures of `Checks/Cases/Fs/Fcntl.lean` hold.
model: a fixture; what it pins is stated on the theorems that read it. -/
def fcntl_listening_model : Model :=
  fixture_of (fds := (13, .FdSocket .SkListening) :: fcntl_fds) (fs := [([102], [104, 105])])

/-- F_GETFL on a LISTENING socket is still O_RDWR: `sock_alloc_file` fixed
the word at creation (net/socket.c:483-485, Linux v6.18.46), `listen`
touches the socket and not its file, and every later use of
`sock->file->f_flags` in net/socket.c is a read.
kernel: fs/fcntl.c:do_fcntl; net/socket.c:sock_alloc_file@v6.18.46 -/
theorem check_getfl_on_listening_socket_is_o_rdwr :
    check_fcntl 13 3 0 (mkEffect 2 [] []) fcntl_listening_model
      = CheckOk fcntl_listening_model [] := rfl

/-- …and the O_RDWR|O_NONBLOCK word (2050) is refused there too: no modeled
path sets the bit on a socket of any state.
kernel: fs/fcntl.c:do_fcntl; net/socket.c:sock_alloc_file@v6.18.46 -/
theorem check_getfl_on_listening_socket_o_nonblock_word_rejected :
    check_fcntl 13 3 0 (mkEffect 2050 [] []) fcntl_listening_model
      = CheckReject := rfl

/-- The empty F_SETFL is 0 on the listening socket as on the fresh one.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_empty_on_listening_socket_is_zero :
    check_fcntl 13 4 32768 (mkEffect 0 [] []) fcntl_listening_model
      = CheckOk fcntl_listening_model [] := rfl

/-- …and the listening socket declines where the fresh one does, so "the
state does not matter" is pinned on a decline as well as on the three
answers: F_GETFD offered the 0 a socket without close-on-exec answers
(`get_close_on_exec`, fs/file.c, Linux v6.18.46), and F_SETFL O_NONBLOCK
(2048) offered the 0 `setfl` answers after storing the bit (fs/fcntl.c:83)
into an `f_flags` no `SockState` records.
kernel: fs/fcntl.c:do_fcntl,setfl; fs/file.c:get_close_on_exec@v6.18.46 -/
theorem check_listening_socket_declines_like_the_fresh_one :
    check_fcntl 13 1 0 (mkEffect 0 [] []) fcntl_listening_model = CheckUnmodeled
    ∧ check_fcntl 13 4 2048 (mkEffect 0 [] []) fcntl_listening_model = CheckUnmodeled :=
  ⟨rfl, rfl⟩

/-- F_SETFL never returns positive: on the empty word no branch of `setfl`
fires and `int error = 0` (fs/fcntl.c:42, Linux v6.18.46) is what `return
error` (:88) hands back; on a FASYNC toggle a positive `->fasync` return is
clamped (`if (error > 0) error = 0;`, :79-80); every other path returns 0
or an errno.  A 1 on the empty word is refused.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_empty_positive_rejected :
    check_fcntl 3 4 32768 (mkEffect 1 [] []) fcntl_model
      = CheckReject := rfl

/-- …and so is the arg echoed back (32768): `setfl` answers 0, not the word
it was handed — the F_GETFL-shaped confusion `check_setfd_one_rejected`
pins for F_SETFD.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_empty_arg_echo_rejected :
    check_fcntl 3 4 32768 (mkEffect 32768 [] []) fcntl_model
      = CheckReject := rfl

/-- The empty F_SETFL touches no user memory: the right 0 with a reported
write is refused.  `setfl` (fs/fcntl.c:39-89, Linux v6.18.46) reads the
inode and `filp`, calls `f_op->check_flags` and `f_op->fasync`, and
stores into `filp`; nothing in it reaches user memory.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_empty_with_a_write_rejected :
    check_fcntl 3 4 32768 (mkEffect 0 [(Z_to_bv 64 4096, [0])] []) fcntl_model
      = CheckReject := rfl

/-- -EBADF on the closed fd with a reported write is refused: the empty-slot
return (fs/fcntl.c:579-580, Linux v6.18.46) precedes every arm that could
touch memory.
kernel: fs/fcntl.c:fcntl@v6.18.46 -/
theorem check_closed_fd_ebadf_with_a_write_rejected :
    check_fcntl 9 57005 0 (mkEffect (errno_ret EBADF) [(Z_to_bv 64 4096, [0])] []) fcntl_model
      = CheckReject := rfl

/-- F_GETFL on the socket with a reported write is refused: `err =
filp->f_flags` (fs/fcntl.c:473, Linux v6.18.46) copies nothing out.
kernel: fs/fcntl.c:do_fcntl; net/socket.c:sock_alloc_file@v6.18.46 -/
theorem check_getfl_on_socket_with_a_write_rejected :
    check_fcntl 6 3 0 (mkEffect 2 [(Z_to_bv 64 4096, [0])] []) fcntl_model
      = CheckReject := rfl

/-- F_SETFD with a reported unmap, and with a reported memory copy, are
refused: the arm writes one bit of the fd table (`set_close_on_exec`,
fs/file.c:1248-1254, Linux v6.18.46) and nothing of the address space.
One conjunct per ledger, so the acceptor cannot be widened one field at a
time.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem check_setfd_with_an_unmap_or_copy_rejected :
    check_fcntl 3 2 1 (SyscallEffect.mkEffectU 0 [] [] [(Z_to_bv 64 4096, Z_to_bv 64 4096)] [] [])
        fcntl_model = CheckReject
    ∧ check_fcntl 3 2 1 (SyscallEffect.mkEffectU 0 [] [] [] [MemCopy.mkCopy 4096 8192 16] [])
        fcntl_model = CheckReject :=
  ⟨rfl, rfl⟩

/-- F_SETFD reads no user memory: a copy-in ledger beside the right 0 is
refused, as it is on F_GETFL above.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem check_setfd_with_a_copyin_rejected :
    check_fcntl 3 2 1 (with_copyins [(Z_to_bv 64 4096, 8)] (mkEffect 0 [] [])) fcntl_model
      = CheckReject := rfl

/-- The empty F_SETFL refuses the zero, unmap, copy and copy-in ledgers as
F_SETFD does above, one conjunct per ledger: `setfl` (fs/fcntl.c:39-89,
Linux v6.18.46) reaches no user memory.  Pinned per arm so that an
acceptor widened on this arm alone goes red here, not only on F_SETFD.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_empty_other_ledgers_rejected :
    check_fcntl 3 4 32768 (mkEffect 0 [] [(Z_to_bv 64 4096, Z_to_bv 64 8)]) fcntl_model
        = CheckReject
    ∧ check_fcntl 3 4 32768 (SyscallEffect.mkEffectU 0 [] [] [(Z_to_bv 64 4096, Z_to_bv 64 4096)] [] [])
        fcntl_model = CheckReject
    ∧ check_fcntl 3 4 32768 (SyscallEffect.mkEffectU 0 [] [] [] [MemCopy.mkCopy 4096 8192 16] [])
        fcntl_model = CheckReject
    ∧ check_fcntl 3 4 32768 (with_copyins [(Z_to_bv 64 4096, 8)] (mkEffect 0 [] [])) fcntl_model
        = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- …and so does the closed fd's -EBADF: the empty-slot return
(fs/fcntl.c:579-580, Linux v6.18.46) precedes every arm that could touch
memory, so no ledger of any shape accompanies it.
kernel: fs/fcntl.c:fcntl@v6.18.46 -/
theorem check_closed_fd_ebadf_other_ledgers_rejected :
    check_fcntl 9 57005 0 (mkEffect (errno_ret EBADF) [] [(Z_to_bv 64 4096, Z_to_bv 64 8)])
        fcntl_model = CheckReject
    ∧ check_fcntl 9 57005 0
        (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [(Z_to_bv 64 4096, Z_to_bv 64 4096)] [] [])
        fcntl_model = CheckReject
    ∧ check_fcntl 9 57005 0
        (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [] [MemCopy.mkCopy 4096 8192 16] [])
        fcntl_model = CheckReject
    ∧ check_fcntl 9 57005 0 (with_copyins [(Z_to_bv 64 4096, 8)] (mkEffect (errno_ret EBADF) [] []))
        fcntl_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- …and F_GETFL on the socket, whose `err = filp->f_flags` (fs/fcntl.c:473,
Linux v6.18.46) copies nothing out: the zero, unmap and copy ledgers
beside the right 2 (the copy-in is refused above).
kernel: fs/fcntl.c:do_fcntl; net/socket.c:sock_alloc_file@v6.18.46 -/
theorem check_getfl_on_socket_other_ledgers_rejected :
    check_fcntl 6 3 0 (mkEffect 2 [] [(Z_to_bv 64 4096, Z_to_bv 64 8)]) fcntl_model
        = CheckReject
    ∧ check_fcntl 6 3 0 (SyscallEffect.mkEffectU 2 [] [] [(Z_to_bv 64 4096, Z_to_bv 64 4096)] [] [])
        fcntl_model = CheckReject
    ∧ check_fcntl 6 3 0 (SyscallEffect.mkEffectU 2 [] [] [] [MemCopy.mkCopy 4096 8192 16] [])
        fcntl_model = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- -EBADF on fd 1, a live channel, is refused: the descriptor resolved
(fs/fcntl.c:576-580, Linux v6.18.46) and F_SETFD's arm has no errno.
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem check_setfd_on_channel_ebadf_rejected :
    check_fcntl 1 2 1 (mkEffect (errno_ret EBADF) [] []) fcntl_model
      = CheckReject := rfl

/-- F_GETFL on the channel declines BEFORE any errno is judged: offered
-EBADF, the verdict is still `CheckUnmodeled` and not `CheckReject` — the
model records no word for a channel and takes no position on the answer,
though the descriptor did resolve and Linux's own answer is not -EBADF.
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem check_getfl_on_channel_declines_ebadf :
    check_fcntl 0 3 0 (mkEffect (errno_ret EBADF) [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- The cmd narrowing is the arm's too: fed the RAW `2^32 + 2`, the checker
names no command and declines; fed `cmd32` of it, it answers F_SETFD's 0.
Linux's `unsigned int cmd` (fs/fcntl.c:574, Linux v6.18.46) is the
narrowing the arm supplies.
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem check_cmd_narrowing_is_the_arms :
    check_fcntl 3 4294967298 1 (mkEffect 0 [] []) fcntl_model
        = CheckUnmodeled
    ∧ check_fcntl 3 (cmd32 4294967298) 1 (mkEffect 0 [] []) fcntl_model
        = CheckOk fcntl_model [] :=
  ⟨rfl, rfl⟩

/-- F_SETFD with only high-half bits (`2^32`) is 0: `int argi = (int)arg`
(fs/fcntl.c:448, Linux v6.18.46) hands `set_close_on_exec` a 0 and the
answer does not depend on it.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem check_setfd_high_half_arg_is_zero :
    check_fcntl 3 2 4294967296 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- F_GETFL reads no `arg`: with 32768 in a2 the socket still answers
O_RDWR (`err = filp->f_flags`, fs/fcntl.c:472-474, Linux v6.18.46).
kernel: fs/fcntl.c:do_fcntl; net/socket.c:sock_alloc_file@v6.18.46 -/
theorem check_getfl_on_socket_ignores_arg :
    check_fcntl 6 3 32768 (mkEffect 2 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- F_DUPFD_CLOEXEC (1030, `F_LINUX_SPECIFIC_BASE + 6`) declines even
offered the 2 Linux would answer: `f_dupfd(argi, filp, O_CLOEXEC)`
(fs/fcntl.c:459-461; fs/file.c:1472-1484, Linux v6.18.46) installs the
lowest free descriptor at or above `argi`, and fd 2 is the fixture's hole.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:f_dupfd@v6.18.46 -/
theorem check_dupfd_cloexec_declines :
    check_fcntl 3 1030 0 (mkEffect 2 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- F_GETPIPE_SZ (1032) on the pipe's read end, a real command on a kind
the fixture holds, declines even offered the 65536 an unconstrained pipe
answers: `pipe_fcntl` (fs/pipe.c:1428-1453, Linux v6.18.46) answers
F_GETPIPE_SZ with `pipe->max_usage * PAGE_SIZE` (:1444, returned at
:1452), and `alloc_pipe_info` starts
`max_usage` at `PIPE_DEF_BUFFERS` = 16 pages (fs/pipe.c:795, :824;
include/linux/pipe_fs_i.h:5) — unless the task lacks CAP_SYS_RESOURCE and
`pipe_max_size` is below that (:804-805), or the user is over the soft
limit and the task holds neither CAP_SYS_RESOURCE nor CAP_SYS_ADMIN
(`pipe_is_unprivileged_user`, fs/pipe.c:787-790), which drops it to
PIPE_MIN_DEF_BUFFERS (:809-812); 65536 is the unconstrained word.
kernel: fs/fcntl.c:do_fcntl; fs/pipe.c:pipe_fcntl,alloc_pipe_info@v6.18.46 -/
theorem check_getpipe_sz_on_pipe_reader_declines :
    check_fcntl 7 1032 0 (mkEffect 65536 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- The socket's word on the wrong fd: 2 on F_GETFL of the read-only file is
a decline, not an answer — `getfl_f_flags` derives no word for `FdFile`.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem check_socket_word_on_file_declines :
    check_fcntl 3 3 0 (mkEffect 2 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- fd 2, the hole `alloc_fd` would fill, is closed in the fixture and is
-EBADF like fd 9: the fixture shape the F_DUPFD pins rely on, pinned.
kernel: fs/fcntl.c:fcntl@v6.18.46 -/
theorem check_fd_two_hole_is_ebadf :
    check_fcntl 2 2 1 (mkEffect (errno_ret EBADF) [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl


/-! ## The cells that had one side

A table of fd kind against command showed the accepting F_SETFD and F_SETFL
arms with a `CheckReject` beside them on fd 3 alone, F_SETFD with no pin at
all on the write-created file and the listening socket, the fd-before-mask
order on a closed fd pinned only through a mask word, and the F_GETFL
declines on the write-created file and the directory offered 0 rather than
a word Linux reports.  Each pin below is a lie the kernel cannot tell on
that cell, or the kernel's own answer on a cell that had none. -/

/-- F_SETFD on the write-created file is 0: `do_fcntl` sets the flag and
answers `err = 0` without reading the file (fs/fcntl.c:468-471, Linux
v6.18.46).
kernel: fs/fcntl.c:do_fcntl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem check_setfd_on_write_fd_is_zero :
    check_fcntl 4 2 1 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- …and on the listening socket.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem check_setfd_on_listening_socket_is_zero :
    check_fcntl 13 2 1 (mkEffect 0 [] []) fcntl_listening_model
      = CheckOk fcntl_listening_model [] := rfl

/-- F_SETFD has no error path once the fd resolved: the LSM hook at
fs/fcntl.c:587, `security_file_fcntl` (security/security.c:3223, Linux
v6.18.46), sits between, and none of the three in-tree hooks has an
F_SETFD case (`selinux_file_fcntl`, security/selinux/hooks.c:4158-4196;
`smack_file_fcntl`, security/smack/smack_lsm.c:1797; `tomoyo_file_fcntl`,
security/tomoyo/tomoyo.c:312-319; all Linux v6.18.46); then
`do_fcntl` answers `err = 0` (fs/fcntl.c:469, Linux v6.18.46) and the
setter it calls, `set_close_on_exec` (fs/file.c), returns nothing — so a
nonzero success or
an errno is refused on every open kind and not on fd 3 alone: 1 on the
write-created file…
kernel: fs/fcntl.c:do_fcntl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem check_setfd_on_write_fd_one_rejected :
    check_fcntl 4 2 1 (mkEffect 1 [] []) fcntl_model
      = CheckReject := rfl

/-- …-EINVAL on the directory fd…
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem check_setfd_on_directory_einval_rejected :
    check_fcntl 5 2 1 (mkEffect (errno_ret EINVAL) [] []) fcntl_model
      = CheckReject := rfl

/-- …-EBADF on the socket…
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem check_setfd_on_socket_ebadf_rejected :
    check_fcntl 6 2 1 (mkEffect (errno_ret EBADF) [] []) fcntl_model
      = CheckReject := rfl

/-- …1 on the pipe's write end…
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem check_setfd_on_pipe_writer_one_rejected :
    check_fcntl 8 2 1 (mkEffect 1 [] []) fcntl_model
      = CheckReject := rfl

/-- …-EBADF on /dev/null…
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem check_setfd_on_devnull_ebadf_rejected :
    check_fcntl 11 2 1 (mkEffect (errno_ret EBADF) [] []) fcntl_devnull_model
      = CheckReject := rfl

/-- …1 on /dev/urandom…
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem check_setfd_on_urandom_one_rejected :
    check_fcntl 12 2 1 (mkEffect 1 [] []) fcntl_urandom_model
      = CheckReject := rfl

/-- …and -EINVAL on the listening socket.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem check_setfd_on_listening_socket_einval_rejected :
    check_fcntl 13 2 1 (mkEffect (errno_ret EINVAL) [] []) fcntl_listening_model
      = CheckReject := rfl

/-- The empty F_SETFL on the write-created file cannot earn `setfl`'s
-EPERM either: the O_APPEND test (fs/fcntl.c:48-49, Linux v6.18.46) fires
on an O_APPEND DELTA, and no `FdFileW` carries O_APPEND — `Sys/Fs/Open.lean`'s
`openat_resolved_spec` sends the append word to `unmodeled` — so on the
empty word the delta is 0 whatever IS_APPEND says of the inode; the
O_NOATIME test (:52-54) needs the bit in `arg`.  Refused.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_empty_on_write_fd_eperm_rejected :
    check_fcntl 4 4 32768 (mkEffect (errno_ret EPERM) [] []) fcntl_model
      = CheckReject := rfl

/-- …nor -EINVAL on the directory fd: the O_DIRECT test (fs/fcntl.c:62-65)
needs the bit in `arg`, and the one `check_flags` in the tree needs
O_APPEND|O_DIRECT together (`check_setfl_empty_einval_rejected` above
carries that claim and its falsifying condition).
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_empty_on_directory_einval_rejected :
    check_fcntl 5 4 32768 (mkEffect (errno_ret EINVAL) [] []) fcntl_model
      = CheckReject := rfl

/-- …nor a positive return on the socket: no branch of `setfl` fires on
the empty word and `int error = 0` (fs/fcntl.c:42) is what `return error`
(:88) hands back.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_empty_on_socket_positive_rejected :
    check_fcntl 6 4 32768 (mkEffect 1 [] []) fcntl_model
      = CheckReject := rfl

/-- …nor -EINVAL on the listening socket.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem check_setfl_empty_on_listening_socket_einval_rejected :
    check_fcntl 13 4 32768 (mkEffect (errno_ret EINVAL) [] []) fcntl_listening_model
      = CheckReject := rfl

/-- The fd-before-mask order pinned on the ACCEPTING word too: F_SETFL with
the empty word on the closed fd 9 is -EBADF (fs/fcntl.c:579-580, Linux
v6.18.46), not the 0 the same word earns on every file kind.  A checker
that answered the no-op before the lookup passes the mask-word pin above
and fails here.
kernel: fs/fcntl.c:fcntl,do_fcntl@v6.18.46 -/
theorem check_setfl_empty_on_closed_fd_is_ebadf :
    check_fcntl 9 4 32768 (mkEffect (errno_ret EBADF) [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- …and that 0 is refused there.
kernel: fs/fcntl.c:fcntl@v6.18.46 -/
theorem check_setfl_empty_on_closed_fd_zero_rejected :
    check_fcntl 9 4 32768 (mkEffect 0 [] []) fcntl_model
      = CheckReject := rfl

/-- F_GETFL on the write-created file declines even offered a word Linux
reports for it, O_WRONLY|O_LARGEFILE (32769): `openat` ORs in O_LARGEFILE
(fs/open.c:1466-1467, Linux v6.18.46) and `do_dentry_open` clears
O_CREAT|O_EXCL|O_NOCTTY|O_TRUNC (:981), leaving the access mode and
O_LARGEFILE — plus O_NONBLOCK when the open carried it, which the spec's
`openat` arm does not record, so 32769 + 2048 is the other word.
kernel: fs/fcntl.c:do_fcntl; fs/open.c:openat,do_dentry_open; include/uapi/asm-generic/fcntl.h:O_LARGEFILE@v6.18.46 -/
theorem check_getfl_on_write_fd_declines_its_true_word :
    check_fcntl 4 3 0 (mkEffect 32769 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- …and the directory fd offered O_RDONLY|O_DIRECTORY|O_LARGEFILE (98304):
O_DIRECTORY is not among the bits `do_dentry_open` clears.  One of two
words an `FdDir` can carry, since `openat_read_spec` (`Sys/Fs/Open.lean`)
mints the kind for `.` and `..` opened without O_DIRECTORY too, at
O_RDONLY|O_LARGEFILE (32768); either, plus O_NONBLOCK when the open
carried it, is the other.
kernel: fs/fcntl.c:do_fcntl; fs/open.c:openat,do_dentry_open; include/uapi/asm-generic/fcntl.h:O_DIRECTORY@v6.18.46 -/
theorem check_getfl_on_directory_declines_its_true_word :
    check_fcntl 5 3 0 (mkEffect 98304 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-! ## The F_GETLK ledger, the fd whose low half is 0, and the socket's whole mask

Three cells an adversarial pass over this file found unpinned: the one
neighbouring command that DOES touch user memory, the fd whose low half
is exactly 0, and the socket's mask beyond the two bits pinned on it. -/

/-- F_GETLK (5) on a file declines: `do_fcntl` (fs/fcntl.c:482-488, Linux
v6.18.46) copies a `struct flock` in, calls `fcntl_getlk` (fs/locks.c:2281)
and copies it back out, so the command reads AND writes user memory — the
shape `check_getfl_on_socket_with_a_copyin_rejected` says a future arm
must not inherit from F_GETFL — and the checker has no arm for it.
Offered the bare 0 an unlocked file answers…
kernel: fs/fcntl.c:do_fcntl; fs/locks.c:fcntl_getlk@v6.18.46 -/
theorem check_getlk_on_file_declines :
    check_fcntl 3 5 4096 (mkEffect 0 [] []) fcntl_model = CheckUnmodeled := rfl

/-- …and offered a ledger of its SHAPE — a 32-byte copy-in of the
`struct flock` (include/uapi/asm-generic/fcntl.h:194-206; 32 bytes on
riscv64, `__kernel_off_t` being `long`) and a 32-byte write back to the
same address — it declines the same way: the decline is on the command,
not on the effect.  The bytes are not the true ones: `fcntl_getlk` stores
the tested type (`flock->l_type = fl->c.flc_type`, fs/locks.c:2311), and
on an unlocked file that is F_UNLCK = 2 (`posix_test_lock`,
fs/locks.c:961-963, fs/locks.c:984), so Linux's write-back leads 0x02 0x00 and
echoes the other 30 bytes.
kernel: fs/fcntl.c:do_fcntl; fs/locks.c:fcntl_getlk@v6.18.46 -/
theorem check_getlk_on_file_declines_with_a_ledger_of_its_shape :
    check_fcntl 3 5 4096
      (with_copyins [(Z_to_bv 64 4096, 32)]
        (mkEffect 0 [(Z_to_bv 64 4096, List.replicate 32 0)] []))
      fcntl_model = CheckUnmodeled := rfl

/-- fd `2^32` exactly is fd 0 after `fd32`, the read channel
(`fd32_two_pow_32_is_stdin`, `Checks/Cases/Sys/Syscall.lean`), and F_SETFD
answers 0 there as it does on fd 1…
kernel: fs/fcntl.c:fcntl,do_fcntl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem check_fd_two_pow_32_setfd_is_zero :
    check_fcntl (fd32 4294967296) 2 1 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-- …the empty F_SETFL declines there, the channel exclusion once more…
kernel: fs/fcntl.c:fcntl,do_fcntl,setfl@v6.18.46 -/
theorem check_fd_two_pow_32_setfl_empty_declines :
    check_fcntl (fd32 4294967296) 4 32768 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- …and the raw word, unnarrowed, names no descriptor of the fixture, so
the checker admits `-EBADF` on it while the narrowed word refuses the same
errno: the two conjuncts read together are the arm's narrowing, the shape
of `check_fd_narrowing_is_the_arms`, and neither alone is a claim about
Linux — `unsigned int fd` (fs/fcntl.c:574) makes this word fd 0, on which
`-EBADF` is never the answer.  A dispatcher that forgot `fd32` would
refuse the 0 Linux answers on fd 0 while admitting the `-EBADF` the first
conjunct pins.
kernel: fs/fcntl.c:fcntl@v6.18.46 -/
theorem check_fd_two_pow_32_raw_is_ebadf :
    check_fcntl 4294967296 2 1 (mkEffect (errno_ret EBADF) [] []) fcntl_model
        = CheckOk fcntl_model []
    ∧ check_fcntl (fd32 4294967296) 2 1 (mkEffect (errno_ret EBADF) [] []) fcntl_model
        = CheckReject :=
  ⟨rfl, rfl⟩

/-- The socket's whole mask (289792) declines: every bit of
`setfl_acted_on` is a delta on `O_RDWR`, and F_SETFL on `FdSocket` is
`setfl_noop_on`'s mask test.  The word is not a stored change, though:
`setfl` refuses it at the O_DIRECT test (fs/fcntl.c:62-65, Linux
v6.18.46) before the store at :83, so 0 is not Linux's answer here
either — the decline is on the model recording no `f_flags` for a
socket, not on which word is right.
kernel: fs/fcntl.c:do_fcntl,setfl; net/socket.c:sock_alloc_file@v6.18.46 -/
theorem check_setfl_whole_mask_on_socket_declines :
    check_fcntl 6 4 289792 (mkEffect 0 [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- …and Linux's own answer for the word, `setfl`'s -EINVAL, is declined
too: the socket's inode is `S_IFSOCK` (`sock_alloc`, net/socket.c:644,
Linux v6.18.46), not a FIFO, the word carries O_DIRECT, and no socket
file has FMODE_CAN_ODIRECT (its setter is `do_dentry_open`'s,
fs/open.c:978-979, a path `alloc_file_pseudo` never enters), so the test
at fs/fcntl.c:62-65 fires — after the IS_APPEND test (:48-49) passes on
an inode carrying no S_APPEND and the O_NOATIME test (:52-54) passes for
the socket's creator — and nothing is stored.  Under an enforcing TOMOYO
the O_APPEND toggle would be -EPERM ahead of `do_fcntl` instead; the
model takes no side.
kernel: fs/fcntl.c:do_fcntl,setfl; net/socket.c:sock_alloc; fs/open.c:do_dentry_open@v6.18.46 -/
theorem check_setfl_whole_mask_on_socket_declines_einval :
    check_fcntl 6 4 289792 (mkEffect (errno_ret EINVAL) [] []) fcntl_model
      = CheckUnmodeled := rfl

/-- …while bit 31 alone, inside the `int` and outside the mask, is the
empty F_SETFL on the socket and answers 0, as it does on the file.
kernel: fs/fcntl.c:do_fcntl,setfl; net/socket.c:sock_alloc_file@v6.18.46 -/
theorem check_setfl_sign_bit_on_socket_is_zero :
    check_fcntl 6 4 2147483648 (mkEffect 0 [] []) fcntl_model
      = CheckOk fcntl_model [] := rfl

/-! ## The witness

The concrete pins fix `fcntl_witness`'s answer on one call per arm of the
checker; the quantified theorems after them tie it to the checker at every
call and model without opening the spec. -/

/-- On a closed fd the witness offers `-EBADF`, the `fd_empty` answer
(fs/fcntl.c:579-580, Linux v6.18.46).
kernel: fs/fcntl.c:fcntl@v6.18.46 -/
theorem witness_closed_fd_is_ebadf :
    fcntl_witness 9 57005 0 fcntl_model = Ok (mkEffect (errno_ret EBADF) [] []) fcntl_model [] :=
  rfl

/-- F_SETFD offers 0 on a file: `do_fcntl`'s case for it (fs/fcntl.c:468-471,
Linux v6.18.46) sets `err = 0` and writes the close-on-exec bit, which is
all it does.
kernel: fs/fcntl.c:do_fcntl; fs/file.c:set_close_on_exec@v6.18.46 -/
theorem witness_setfd_is_zero :
    fcntl_witness 3 2 1 fcntl_model = Ok (mkEffect 0 [] []) fcntl_model [] :=
  rfl

/-- The empty F_SETFL offers 0 on a file: `setfl` finds no delta on the
five bits it reads and returns its 0.
kernel: fs/fcntl.c:do_fcntl,setfl@v6.18.46 -/
theorem witness_setfl_empty_is_zero :
    fcntl_witness 3 4 32768 fcntl_model = Ok (mkEffect 0 [] []) fcntl_model [] :=
  rfl

/-- F_GETFL on the socket offers O_RDWR, the `f_flags` `sock_alloc_file`
gave it.
kernel: fs/fcntl.c:do_fcntl; net/socket.c:sock_alloc_file; include/uapi/asm-generic/fcntl.h:O_RDWR@v6.18.46 -/
theorem witness_getfl_on_socket_is_o_rdwr :
    fcntl_witness 6 3 0 fcntl_model = Ok (mkEffect 2 [] []) fcntl_model [] :=
  rfl

/-- The witness declines where the checker does: the empty F_SETFL on a
channel, F_GETFL on a file, and F_GETOWN — each a call whose Linux answer
is definite and whose state the model lacks (the spec twin's argument).
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem witness_declines_on_the_checkers_declines :
    fcntl_witness 1 4 32768 fcntl_model = Unmodeled
    ∧ fcntl_witness 3 3 0 fcntl_model = Unmodeled
    ∧ fcntl_witness 6 9 0 fcntl_model = Unmodeled :=
  ⟨rfl, rfl, rfl⟩

/-- The checker accepts its own witness at every call and model: the
receptive field and the complete field of the arm meet on the same triple,
which is what makes the arm's `ca_receptive` a statement about
`check_fcntl` and not only about the spec.  The proof opens none of the
checker's four lemmas — it is the checker's own case split with
`check_ret_only_ok_iff` on every accepting arm — so a witness that answered
an arm differently from the checker fails here, on that arm.
model: `fcntl_witness` fed to `check_fcntl`, no spec named -/
theorem check_fcntl_accepts_its_witness (fd cmd arg : word) (m : Model) (e : SyscallEffect)
    (m' : Model) (evs : List event)
    (h : fcntl_witness fd cmd arg m = Ok e m' evs) :
    check_fcntl fd cmd arg e m = CheckOk m' evs := by
  unfold fcntl_witness at h
  unfold check_fcntl
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    simp only [hfd] at h ⊢
    unfold ret_outcome at h
    injection h with he hm hevs
    subst he hm hevs
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | some k =>
    simp only [hfd] at h ⊢
    cases hd : bv_eqb cmd F_SETFD with
    | true =>
      simp only [hd, ↓reduceIte] at h ⊢
      unfold ret_outcome at h
      injection h with he hm hevs
      subst he hm hevs
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    | false =>
      simp only [hd, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hl : (bv_eqb cmd F_SETFL && setfl_noop_on k arg) with
      | true =>
        simp only [hl, ↓reduceIte] at h ⊢
        unfold ret_outcome at h
        injection h with he hm hevs
        subst he hm hevs
        exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
      | false =>
        simp only [hl, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hg : bv_eqb cmd F_GETFL with
        | true =>
          simp only [hg, ↓reduceIte] at h ⊢
          cases hgf : getfl_f_flags k with
          | some fl =>
            simp only [hgf] at h ⊢
            unfold ret_outcome at h
            injection h with he hm hevs
            subst he hm hevs
            exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
          | none =>
            simp only [hgf] at h
            cases h
        | false =>
          simp only [hg, Bool.false_eq_true, ↓reduceIte] at h
          cases h

/-- …and only its witness: whatever effect the checker accepts, at any call
and model, is the witness's, with the model handed back unchanged and no
events.  The theorem above says the witness's answer is accepted; without
this one a checker that accepted a SECOND effect on some arm — 32770 beside
2 on the socket's F_GETFL, say — would satisfy it and the decline iff below,
and only the concrete `CheckReject` pins would notice.  The same case split,
with the forward half of `check_ret_only_ok_iff` on every accepting arm.
model: `check_fcntl`'s acceptances read back into `fcntl_witness`, no spec named -/
theorem check_fcntl_accepts_only_its_witness (fd cmd arg : word) (m : Model) (e : SyscallEffect)
    (m' : Model) (evs : List event)
    (h : check_fcntl fd cmd arg e m = CheckOk m' evs) :
    fcntl_witness fd cmd arg m = Ok e m' evs := by
  unfold check_fcntl at h
  unfold fcntl_witness
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    simp only [hfd] at h ⊢
    obtain ⟨he, hm, hevs⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    subst he hm hevs
    rfl
  | some k =>
    simp only [hfd] at h ⊢
    cases hd : bv_eqb cmd F_SETFD with
    | true =>
      simp only [hd, ↓reduceIte] at h ⊢
      obtain ⟨he, hm, hevs⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      subst he hm hevs
      rfl
    | false =>
      simp only [hd, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hl : (bv_eqb cmd F_SETFL && setfl_noop_on k arg) with
      | true =>
        simp only [hl, ↓reduceIte] at h ⊢
        obtain ⟨he, hm, hevs⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
        subst he hm hevs
        rfl
      | false =>
        simp only [hl, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hg : bv_eqb cmd F_GETFL with
        | true =>
          simp only [hg, ↓reduceIte] at h ⊢
          cases hgf : getfl_f_flags k with
          | some fl =>
            simp only [hgf] at h ⊢
            obtain ⟨he, hm, hevs⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
            subst he hm hevs
            rfl
          | none =>
            simp only [hgf] at h
            cases h
        | false =>
          simp only [hg, Bool.false_eq_true, ↓reduceIte] at h
          cases h

/-- …and the witness declines exactly where the checker does, at every
call and model: an `Unmodeled` from the witness is a `CheckUnmodeled` from
the checker and back, whatever effect the checker is shown.  With the two
theorems above this is the whole relation between the two — the effects
the checker accepts are exactly the witness's answers, on the same model
with no events, and the declines coincide — and no half opens the spec.
model: `fcntl_witness` against `check_fcntl`, arm by arm, no spec named -/
theorem fcntl_witness_declines_where_the_checker_does (fd cmd arg : word) (eff : SyscallEffect)
    (m : Model) :
    fcntl_witness fd cmd arg m = Unmodeled ↔ check_fcntl fd cmd arg eff m = CheckUnmodeled := by
  unfold fcntl_witness check_fcntl
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    simp only
    exact ⟨(fun h => by unfold ret_outcome at h; cases h),
                   fun h => absurd h (check_ret_only_no_unmodeled _ _ _ _)⟩
  | some k =>
    simp only
    cases hd : bv_eqb cmd F_SETFD with
    | true =>
      simp only [↓reduceIte]
      exact ⟨(fun h => by unfold ret_outcome at h; cases h),
                   fun h => absurd h (check_ret_only_no_unmodeled _ _ _ _)⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases hl : (bv_eqb cmd F_SETFL && setfl_noop_on k arg) with
      | true =>
        simp only [↓reduceIte]
        exact ⟨(fun h => by unfold ret_outcome at h; cases h),
                   fun h => absurd h (check_ret_only_no_unmodeled _ _ _ _)⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases hg : bv_eqb cmd F_GETFL with
        | true =>
          simp only [↓reduceIte]
          cases hgf : getfl_f_flags k with
          | some fl =>
            simp only
            exact ⟨(fun h => by unfold ret_outcome at h; cases h),
                   fun h => absurd h (check_ret_only_no_unmodeled _ _ _ _)⟩
          | none =>
            simp only
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Fcntl

-- lean-port sentinel: ticket V-Fs-Fcntl appends below this line

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Fcntl

section V_Fs_Fcntl

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Fcntl
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Fcntl
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude (fixture_of)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Fcntl (fcntl_in)

/-! The fixtures put the descriptor kinds at the numbers in the recordings.
`openat_rdwr`, `openat_append` and the read-write half of
`scenarios/file_size_offset` open with words `Sys/Fs/Open.lean` declines
(its header), so their post-open states have no fixture here;
`setfl_one_rejected_over_the_real_table` tests the recorded return lie on
an available regular-file kind, without claiming a replay of those states.
`openat_nonblock` and `eventfd2` have no recorded syscall 25.

The socket and unknown-command pins inherit the two supported-implementation
limits already documented above in `check_unknown_cmd_on_closed_fd_einval_rejected`
and the socket pins; this registration changes neither checker decision. -/

/-- Descriptor 3 after the write-create in `fcntl_spec`; descriptor 2 is
the inherited channel. The descriptor kinds, rather than the file contents,
are what fs/fcntl.c:468-477 (`do_fcntl`, Linux v6.18.46) consults here. -/
def corpus_file : Model := fixture_of
  (fds := [(2, .FdChannel 2), (3, .FdFileW [102] 0)])

/-- The read-only reopening in `nbsetfl`; `setfl` (fs/fcntl.c:39-89,
Linux v6.18.46) uses the same status-bit tests on this access mode. -/
def corpus_read : Model := fixture_of (fds := [(3, .FdFile [102] 0)])

/-- The fresh socket at fd 3 in `sockgetfl`, `sockfl` and `sockgetfd`;
`do_fcntl` reads its flag word at fs/fcntl.c:472-474 (Linux v6.18.46). -/
def corpus_socket : Model := fixture_of (fds := [(3, .FdSocket .SkFresh)])

/-- The directory and its copy, as numbered in `dirfd` and
`scenarios/dir_name_unlink`; `do_fcntl`'s F_SETFD branch at
fs/fcntl.c:468-471 (Linux v6.18.46) uses the descriptor number. -/
def corpus_dirs : Model := fixture_of (fds := [(3, .FdDir), (4, .FdDir)])

/-- The pipe ends at fds 3/4 in `pipegetfl` and `pipe2_spec`;
`do_fcntl` reaches `setfl` at fs/fcntl.c:475-476 (Linux v6.18.46). -/
def corpus_pipe : Model := fixture_of
  (fds := [(3, .FdPipe 0 false), (4, .FdPipe 0 true)])

/-- The lookup the dispatcher performs on a `fcntl_in`, computed once:
`in_sysno` is 25 whatever the three words hold.
model: `lookup_ca` over `checked_table` at a closed number; the table's own
contents, not a kernel claim. -/
theorem lookup_fcntl_in (fd cmd arg : word) :
    lookup_ca checked_table (bv_unsigned (fcntl_in fd cmd arg).in_sysno) = some arm_fcntl :=
  lookup_ca_checked_table_fcntl

/-- The `badfd` and `unkcmd` recordings: `fcntl` resolves the descriptor
before dispatching the command (fs/fcntl.c:576-580, Linux v6.18.46).
The last call uses the existing fixture with fd 3 removed, as after close.
kernel: fs/fcntl.c:fcntl@v6.18.46 -/
theorem closed_fd_ebadf_accepted_over_the_real_table :
    check_syscall (fcntl_in 999 3 0) (mkEffect (errno_ret EBADF) [] []) corpus_file = CheckOk corpus_file []
    ∧ check_syscall (fcntl_in 999 1 0) (mkEffect (errno_ret EBADF) [] []) corpus_file = CheckOk corpus_file []
    ∧ check_syscall (fcntl_in 999 2 1) (mkEffect (errno_ret EBADF) [] []) corpus_file = CheckOk corpus_file []
    ∧ check_syscall (fcntl_in 999 4 2048) (mkEffect (errno_ret EBADF) [] []) corpus_file = CheckOk corpus_file []
    ∧ check_syscall (fcntl_in 999 0 0) (mkEffect (errno_ret EBADF) [] []) corpus_file = CheckOk corpus_file []
    ∧ check_syscall (fcntl_in (Z_to_bv 64 (-1)) 3 0) (mkEffect (errno_ret EBADF) [] []) corpus_file = CheckOk corpus_file []
    ∧ check_syscall (fcntl_in 4294968295 3 0) (mkEffect (errno_ret EBADF) [] []) corpus_file = CheckOk corpus_file []
    ∧ check_syscall (fcntl_in 999 4294967299 0) (mkEffect (errno_ret EBADF) [] []) corpus_file = CheckOk corpus_file []
    ∧ check_syscall (fcntl_in 2147483649 2 1) (mkEffect (errno_ret EBADF) [] []) corpus_file = CheckOk corpus_file []
    ∧ check_syscall (fcntl_in 999 2147483647 0) (mkEffect (errno_ret EBADF) [] []) corpus_file = CheckOk corpus_file []
    ∧ check_syscall (fcntl_in 3 2 1) (mkEffect (errno_ret EBADF) [] []) (fixture_of (fds := [(2, .FdChannel 2)])) = CheckOk (fixture_of (fds := [(2, .FdChannel 2)])) [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The `setfd`, `dirfd`, `sockfl` and directory-copy calls: `do_fcntl`
sets `err = 0` and masks the argument with FD_CLOEXEC
(fs/fcntl.c:468-471, Linux v6.18.46).
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem setfd_zero_accepted_over_the_real_table :
    check_syscall (fcntl_in 3 2 1) (mkEffect 0 [] []) corpus_file = CheckOk corpus_file []
    ∧ check_syscall (fcntl_in 3 2 0) (mkEffect 0 [] []) corpus_file = CheckOk corpus_file []
    ∧ check_syscall (fcntl_in 3 2 3735928559) (mkEffect 0 [] []) corpus_file = CheckOk corpus_file []
    ∧ check_syscall (fcntl_in 3 2 4294967296) (mkEffect 0 [] []) corpus_file = CheckOk corpus_file []
    ∧ check_syscall (fcntl_in 2 2 0) (mkEffect 0 [] []) corpus_file = CheckOk corpus_file []
    ∧ check_syscall (fcntl_in 3 2 1) (mkEffect 0 [] []) corpus_dirs = CheckOk corpus_dirs []
    ∧ check_syscall (fcntl_in 4 2 1) (mkEffect 0 [] []) corpus_dirs = CheckOk corpus_dirs []
    ∧ check_syscall (fcntl_in 3 2 1) (mkEffect 0 [] []) corpus_socket = CheckOk corpus_socket [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The `setfl`, `nbsetfl`, `dirfd` and `sockfl` arguments: `do_fcntl`
narrows arg at fs/fcntl.c:448 and calls `setfl` at :476; its mask
assignment at :83 and return at :88 give zero on these paths
(Linux v6.18.46). The high-half-only argument becomes zero.
kernel: fs/fcntl.c:setfl,do_fcntl@v6.18.46 -/
theorem setfl_noop_zero_accepted_over_the_real_table :
    check_syscall (fcntl_in 3 4 0) (mkEffect 0 [] []) corpus_file = CheckOk corpus_file []
    ∧ check_syscall (fcntl_in 3 4 32768) (mkEffect 0 [] []) corpus_file = CheckOk corpus_file []
    ∧ check_syscall (fcntl_in 3 4 33281) (mkEffect 0 [] []) corpus_file = CheckOk corpus_file []
    ∧ check_syscall (fcntl_in 3 4 524288) (mkEffect 0 [] []) corpus_file = CheckOk corpus_file []
    ∧ check_syscall (fcntl_in 3 4 4294967296) (mkEffect 0 [] []) corpus_file = CheckOk corpus_file []
    ∧ check_syscall (fcntl_in 3 4 0) (mkEffect 0 [] []) corpus_read = CheckOk corpus_read []
    ∧ check_syscall (fcntl_in 3 4 32768) (mkEffect 0 [] []) corpus_dirs = CheckOk corpus_dirs []
    ∧ check_syscall (fcntl_in 3 4 32768) (mkEffect 0 [] []) corpus_socket = CheckOk corpus_socket [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The `sockgetfl` answer: `do_fcntl` returns f_flags at fs/fcntl.c:472-474
(Linux v6.18.46). For the blocking socket, net/socket.c:483-485
(`sock_alloc_file`, same version) supplies O_RDWR. The flag word passes
through fs/file_table.c:420 (`alloc_file_pseudo`) and :391 (`alloc_file`)
to :239-277 (`alloc_empty_file`); :198 (`init_file`) stores it
(Linux v6.18.46).
kernel: fs/fcntl.c:do_fcntl; net/socket.c:sock_alloc_file@v6.18.46 -/
theorem socket_getfl_flags_accepted_over_the_real_table :
    check_syscall (fcntl_in 3 3 0) (mkEffect 2 [] []) corpus_socket = CheckOk corpus_socket [] :=
  rfl

/-- The `nonblock`, `append`, `fasync`, `direct`, `noatime` and two
argument mutations: `setfl` reads these bits at fs/fcntl.c:48, :52,
:62-65, :75-76 and :83 (Linux v6.18.46). The checker declines their
state changes or tests, including the recorded zero answers.
kernel: fs/fcntl.c:setfl,do_fcntl@v6.18.46 -/
theorem recorded_setfl_declines_over_the_real_table :
    check_syscall (fcntl_in 3 4 34816) (mkEffect 0 [] []) corpus_file = CheckUnmodeled
    ∧ check_syscall (fcntl_in 3 4 33792) (mkEffect 0 [] []) corpus_file = CheckUnmodeled
    ∧ check_syscall (fcntl_in 3 4 40960) (mkEffect 0 [] []) corpus_file = CheckUnmodeled
    ∧ check_syscall (fcntl_in 3 4 49152) (mkEffect 0 [] []) corpus_file = CheckUnmodeled
    ∧ check_syscall (fcntl_in 3 4 294912) (mkEffect 0 [] []) corpus_file = CheckUnmodeled
    ∧ check_syscall (fcntl_in 3 4 16384) (mkEffect 0 [] []) corpus_file = CheckUnmodeled
    ∧ check_syscall (fcntl_in 3 4 262144) (mkEffect 0 [] []) corpus_file = CheckUnmodeled
    ∧ check_syscall (fcntl_in 3 4 40960) (mkEffect 0 [] []) corpus_socket = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The `getfl`, `nbgetfl`, `getfd` and `sockgetfd` recordings: `do_fcntl`
reads f_flags or the close-on-exec bit at fs/fcntl.c:465-474 (Linux
v6.18.46). The file fixture lacks the status word and the socket fixture
lacks the descriptor flag, so these answers are declined.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem recorded_flag_getters_declined_over_the_real_table :
    check_syscall (fcntl_in 3 3 0) (mkEffect 32769 [] []) corpus_file = CheckUnmodeled
    ∧ check_syscall (fcntl_in 3 3 0) (mkEffect 34817 [] []) corpus_file = CheckUnmodeled
    ∧ check_syscall (fcntl_in 3 1 0) (mkEffect 0 [] []) corpus_file = CheckUnmodeled
    ∧ check_syscall (fcntl_in 3 1 0) (mkEffect 1 [] []) corpus_socket = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The `dupfd` recording: `do_fcntl` calls f_dupfd at fs/fcntl.c:456-458
(Linux v6.18.46). The checker declines the shared description rather
than installing another entry with an independent offset.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem recorded_dupfd_declined_over_the_real_table :
    check_syscall (fcntl_in 3 0 0) (mkEffect 4 [] []) corpus_file = CheckUnmodeled :=
  rfl

/-- The channel `chanfl`, pipe `pipegetfl` and `pipe2_spec` calls:
`setfl` reads existing flags at fs/fcntl.c:48 and :75, while `do_fcntl`
reads f_flags at :473 (Linux v6.18.46). Channel flags are environmental;
the pipe refusal is the deliberate coverage bound on `setfl_noop_on`
and `getfl_f_flags`, rather than a claim that Linux rejects the calls.
kernel: fs/fcntl.c:setfl,do_fcntl@v6.18.46 -/
theorem recorded_channel_pipe_declines_over_the_real_table :
    check_syscall (fcntl_in 2 4 32768) (mkEffect 0 [] []) corpus_file = CheckUnmodeled
    ∧ check_syscall (fcntl_in 3 3 0) (mkEffect 0 [] []) corpus_pipe = CheckUnmodeled
    ∧ check_syscall (fcntl_in 3 4 0) (mkEffect 0 [] []) corpus_pipe = CheckUnmodeled
    ∧ check_syscall (fcntl_in 4 4 0) (mkEffect 0 [] []) corpus_pipe = CheckUnmodeled :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The `ret=0`, `ret=-EINVAL -- unkcmd` and `arg0=999 -- setfd` lies
are refused: fs/fcntl.c:579-580 (`fcntl`, Linux v6.18.46) returns EBADF
before `do_fcntl`. The unknown-command pin carries the existing
Linux-alone limitation documented above, not a new supported-set claim.
kernel: fs/fcntl.c:fcntl@v6.18.46 -/
theorem closed_fd_mutations_rejected_over_the_real_table :
    check_syscall (fcntl_in 999 3 0) (mkEffect 0 [] []) corpus_file = CheckReject
    ∧ check_syscall (fcntl_in 999 2147483647 0) (mkEffect (errno_ret EINVAL) [] []) corpus_file = CheckReject
    ∧ check_syscall (fcntl_in 999 2 1) (mkEffect 0 [] []) corpus_file = CheckReject :=
  ⟨rfl, rfl, rfl⟩

/-- The `setfd`, `setfl`, `sockfl` and `nbsetfl` return mutations:
`do_fcntl` sets zero at fs/fcntl.c:469 or calls `setfl` at :476, whose
zero path ends at :88 (Linux v6.18.46). These effects substitute the
recorded EBADF, EINVAL, ENOTSOCK and EPERM lies for that zero.
kernel: fs/fcntl.c:setfl,do_fcntl; include/uapi/asm-generic/errno-base.h:EBADF; include/uapi/asm-generic/errno.h:ENOTSOCK@v6.18.46 -/
theorem live_fd_mutations_rejected_over_the_real_table :
    check_syscall (fcntl_in 3 2 1) (mkEffect (errno_ret EBADF) [] []) corpus_file = CheckReject
    ∧ check_syscall (fcntl_in 3 4 0) (mkEffect (errno_ret EINVAL) [] []) corpus_file = CheckReject
    ∧ check_syscall (fcntl_in 3 2 1) (mkEffect (errno_ret ENOTSOCK) [] []) corpus_socket = CheckReject
    ∧ check_syscall (fcntl_in 3 4 32768) (mkEffect (errno_ret EPERM) [] []) corpus_file = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The `sockgetfl` return mutation adds O_LARGEFILE to the Linux answer.
`do_fcntl` reads f_flags at fs/fcntl.c:473 (Linux v6.18.46).
The socket creation in net/socket.c:483-485 (`sock_alloc_file`, same
version) supplies O_RDWR without that bit. This
retains the checker's documented qemu-user limitation; it is a Linux pin.
kernel: fs/fcntl.c:do_fcntl; net/socket.c:sock_alloc_file@v6.18.46 -/
theorem socket_largefile_mutation_rejected_over_the_real_table :
    check_syscall (fcntl_in 3 3 0) (mkEffect 32770 [] []) corpus_socket = CheckReject :=
  rfl

/-- The `openat_rdwr` mutation's return 1, tested here on the representable
write-file kind: `setfl` returns its zero error variable at
fs/fcntl.c:42, :88 (Linux v6.18.46). This is the same return lie, not
a substitute fixture for the absent read-write constructor.
kernel: fs/fcntl.c:setfl,do_fcntl@v6.18.46 -/
theorem setfl_one_rejected_over_the_real_table :
    check_syscall (fcntl_in 3 4 0) (mkEffect 1 [] []) corpus_file = CheckReject :=
  rfl

/-- The `trunc` calls and their EBADF lies: `fcntl` declares unsigned int
fd at fs/fcntl.c:574 (Linux v6.18.46). `__SC_CAST`
(include/linux/syscalls.h:132, same version) drops the high half before
the lookup at :576; bit 31 remains part of the descriptor.
kernel: fs/fcntl.c:fcntl@v6.18.46 -/
theorem fd_low32_over_the_real_table :
    check_syscall (fcntl_in 4294967299 2 1) (mkEffect 0 [] []) corpus_file = CheckOk corpus_file []
    ∧ check_syscall (fcntl_in 4294967299 4 32768) (mkEffect 0 [] []) corpus_file = CheckOk corpus_file []
    ∧ check_syscall (fcntl_in 4294967298 2 0) (mkEffect 0 [] []) corpus_file = CheckOk corpus_file []
    ∧ check_syscall (fcntl_in 4294967299 2 1) (mkEffect (errno_ret EBADF) [] []) corpus_file = CheckReject
    ∧ check_syscall (fcntl_in 2147483651 2 1) (mkEffect 0 [] []) corpus_file = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The command is unsigned int in `fcntl` (fs/fcntl.c:574, Linux
v6.18.46), narrowed by `__SC_CAST` (include/linux/syscalls.h:132).
The `trunc` F_SETFD spelling reaches zero at fs/fcntl.c:469; the high
F_GETFL spelling on a socket reaches its flags at :473. A whole-word
command comparison would decline these positive pins.
kernel: fs/fcntl.c:do_fcntl; include/uapi/asm-generic/errno-base.h:EBADF@v6.18.46 -/
theorem cmd_low32_over_the_real_table :
    check_syscall (fcntl_in 3 4294967298 0) (mkEffect 0 [] []) corpus_file = CheckOk corpus_file []
    ∧ check_syscall (fcntl_in 3 4294967298 0) (mkEffect (errno_ret EBADF) [] []) corpus_file = CheckReject
    ∧ check_syscall (fcntl_in 3 4294967299 0) (mkEffect 2 [] []) corpus_socket = CheckOk corpus_socket []
    ∧ check_syscall (fcntl_in 3 4294967299 0) (mkEffect 0 [] []) corpus_socket = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The parameter order in `fcntl` (fs/fcntl.c:574, Linux v6.18.46)
is preserved by `SC_RISCV_REGS_TO_ARGS`
(arch/riscv/include/asm/syscall_wrapper.h:21-24, same version).
Reading cmd from a2 would answer F_GETFL's 2 for (3,2,3), refused here
by `do_fcntl`'s zero at :469. Swapping fd and cmd in (3,4,0) would
look up absent fd 4 and answer EBADF at :580, also refused.
kernel: fs/fcntl.c:fcntl,do_fcntl; arch/riscv/include/asm/syscall_wrapper.h:SC_RISCV_REGS_TO_ARGS@v6.18.46 -/
theorem register_positions_over_the_real_table :
    check_syscall (fcntl_in 3 2 3) (mkEffect 0 [] []) corpus_socket = CheckOk corpus_socket []
    ∧ check_syscall (fcntl_in 3 2 3) (mkEffect 2 [] []) corpus_socket = CheckReject
    ∧ check_syscall (fcntl_in 3 4 0) (mkEffect 0 [] []) corpus_socket = CheckOk corpus_socket []
    ∧ check_syscall (fcntl_in 3 4 0) (mkEffect (errno_ret EBADF) [] []) corpus_socket = CheckReject :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The witness receives the unsigned-int fd/cmd and unsigned-long arg
from `fcntl`'s declaration (fs/fcntl.c:574, Linux v6.18.46), through
`SC_RISCV_REGS_TO_ARGS` (arch/riscv/include/asm/syscall_wrapper.h:21-24)
and `__SC_CAST` (include/linux/syscalls.h:132, same version).
The symbolic equality pins the full a2 word even where the checker masks it.
kernel: fs/fcntl.c:fcntl; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem witness_over_the_real_table (fd cmd arg : word) (m : Model) :
    syscall_spec_witness (fcntl_in fd cmd arg) m =
      fcntl_witness (fd32 fd) (cmd32 cmd) arg m := rfl

end V_Fs_Fcntl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.Fcntl
