-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Sys/Net/Socket.v theories/LinuxProcessSem/Checks/Witness/Net/Socket.v
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Progress
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Net.Socket
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Net.Socket

/-! # Checks.Cases.Checks.Sys.Net.Socket — what the socket-lifecycle, option-call and I/O CHECKERS answer and their WITNESSES name, read off against Linux

Pins over `Checks.Sys.Net.Socket`, the twin of
`theories/LinuxProcessSem/Checks/Sys/Net/Socket.v` and of
`theories/LinuxProcessSem/Checks/Witness/Net/Socket.v`: the lifecycle
checkers first, in the order their gates fire, then their witnesses.  Not part
of the trusted specification: this file is QA on the definitions, written to
be READ, and every claim in it is a claim about what the kernel does, with
the citation beside it.  Every kernel line below was read at Linux v6.18.46
(commit 1f99e9ab748f).  The setsockopt and getsockopt checkers' pins are
the options section, the socket and accept4 checkers' the section after
it, and the sendto, recvfrom, sendmsg and recvmsg checkers' the I/O
section at the end of this file, each appended by its own ticket and each
carrying its own Rocq mapping.

WHAT A CHECKER PIN IS.  `Checks/Cases/Net/Socket.lean` states, for each
decision of the specs, an `iff` over every outcome and refutes the
lie a kernel could not tell.  The checker is that spec made executable —
the four `_sound_`/`_complete_` lemmas beside it say the two agree on
every input — so a pin here does not restate those `iff`s.  It hands the
checker a concrete `(input, effect)` pair, the shape a trace hands it, and
states the verdict: `CheckOk` on the kernel's answer, `CheckReject` on the
lie, `CheckUnmodeled` where the spec declines.  That is the question a
trace asks, and the one the four lemmas cannot: soundness and completeness
are biconditionals between two definitions of this tree, and hold as well
of a wrong spec beside a matching wrong checker.  Only a verdict on a value
named from outside tells the two apart, which is what each pin below is.

THE MODEL IS AN OUTPUT.  bind's fresh-socket success and listen's fresh-
and bound-socket successes return a model other than the one they were
given, and a trace offers the checker an effect, never a model: the pins on
those arms name the model the checker returns, with the moved entry
reseated at the head of the table as `State.fd_insert` leaves it.

WHAT THIS RESTATES.  Rocq keeps the worked examples for these checkers in
`Checks/Cases/Net/Socket.v`, beside the spec's, as `Example`s over
`check_syscall`.  The dispatcher twin and the arm record are the
registration step's, so each is restated here on the ROW — `check_bind_row
i eff m` and its siblings below, the application of each checker to
the registers as `Sys/Registry/Net/Socket.lean` narrows them.  The mapping, Rocq
name first: `bind_input_reaches_the_state_match` is
`check_bind_input_reaches_the_state_match`;
`bind_on_a_reset_connection_declines` and
`bind_copyin_ledger_marks_the_copy` keep their names with `check_` in
front; the fourteen connect examples from
`connect_on_a_listening_socket_is_eisconn` to
`connect_af_unspec_precedes_the_state_switch` keep their names with
`check_` in front; `socket_calls_decline_every_non_socket_fd_kind` is
`check_getsockname_declines_every_non_socket_fd_kind`,
`check_getpeername_declines_every_non_socket_fd_kind` and
`check_shutdown_declines_every_non_socket_fd_kind`, one per call, the
208 and 209 cells being the options section's below;
`socket_calls_unknown_level_never_beats_the_fd` is
`check_socket_calls_fd_first_on_a_closed_and_a_live_descriptor`, whose
refused lie is the errno of each call's OWN next gate — the -EFAULT of
`move_addr_to_user` for 204 and 205, the -EINVAL of `inet_shutdown` for
210 — rather than Rocq's -ENOPROTOOPT, which belongs to 208 and 209 and
which no function these three calls reach ever spells; the claim, that
the descriptor is resolved before any argument is read, is the same;
`socket_calls_null_pointers_never_beat_the_fd` is
`check_socket_calls_null_pointers_never_beat_the_fd` for its 204 and 205
cells; `getpeername_enotconn_covers_reset_but_not_close_wait`,
`getpeername_success_on_a_reset_socket_is_rejected`,
`getsockname_declines_on_every_socket_state`,
`shutdown_rejects_a_bad_how_on_every_socket_state`,
`shut_wr_on_a_listener_is_zero_and_a_no_op`,
`shutdown_declines_where_it_would_have_to_drop_the_bits`,
`socketpair_writes_the_descriptors_before_it_fails`,
`socketpair_flag_check_precedes_the_writes`,
`socketpair_declines_the_partial_destination`,
`socketpair_wrapping_destination_is_efault`,
`socketpair_past_long_max_at_the_checker` and
`socketpair_dest_width_is_eight` keep their names with `check_` in front.
Rocq's `Forall` over a list of descriptors or `how` values is a
conjunction here, one conjunct per cell.  What a restatement loses is
the register file — which of a0..a3 an arm reads, and where the table
sends each number — and those facts are the registration's to pin, and go
with it; the `_row_is_the_arm` theorems below hold each row to the
registry arm's narrowing.  That list is prose: nothing
reads it, and it goes stale on a rename with nothing going red.  Its
mechanical home would be the coverage header
`check_lean_cases_parity.py` reads, but that header lives on
`Checks/Cases/Net/Socket.lean`, the Lean mirror of the Rocq file that
holds these examples; this file mirrors no Rocq Cases file — Rocq's
worked cases over these checkers are that file's, bar the bind and
recvfrom cells of `Checks/Cases/Fs/Pipe.v`'s two socket-call examples,
which the I/O section twins at the end of its recv pins — so it carries
no such header and that checker would refuse one here.

WHAT IS PINNED BEYOND ROCQ'S EXAMPLES.  Rocq has no `check_syscall`
example for listen at all, and states the arms its bind and connect
examples do not reach — every non-socket descriptor kind, the AF_UNIX and
AF_UNSPEC families on bind, the specific address and port declines, the
fresh success's post-state, the bound and listening -EINVAL, the
connected decline — through the spec's `iff`s alone.  Each of those arms
gets a checker pin here, so that every leaf of every checker is reached
by some closed call in this file, with one exception named in place: the
`socketpair_fds … = none` arm, the exhausted descriptor table, has no
fixture in this tree (it needs every descriptor below 4096 open), and the
spec file pins that decline symbolically over every table instead
(`socketpair_exhausted_declines`).  The register narrowings the rows
perform — `fd32` on every descriptor a0 (socketpair's a0 is the family
and goes through whole), `int32` on shutdown's a1 and, in the options
section, on both option calls' a1 and on setsockopt's a4 —
are pinned at the row on a value whose high half would change the
answer, the way the spec file's "narrowings" section does at the
dispatcher, with one exception: no verdict separates setsockopt's a4
narrowing from a row handing a4 whole, since `int32_neg` reads the low
half itself, and the PROOF of its `_row_is_the_arm` theorem holds it
instead — the direct application of `check_setsockopt_sound_ok`
elaborates only against the registry's `int32 a4`, while the statement
would survive a row handing a4 whole.

PROBES.  The harness runs the EXTRACTED ROCQ model
(`check.sh` extracts it), so a probe's verdict is the Rocq checker's.  The probe cases
that state the same facts of the Rocq side are
`testing/syscall-check/tests/bind_listen_spec.c`,
`testing/syscall-check/tests/connect_spec.c`,
`testing/syscall-check/tests/socket_calls.c`,
`testing/syscall-check/tests/socketpair_spec.c`,
`testing/syscall-check/tests/socket_spec.c`,
`testing/syscall-check/tests/accept_spec.c`,
`testing/syscall-check/tests/send_spec.c`,
`testing/syscall-check/tests/recv_spec.c`,
`testing/syscall-check/tests/socket_read_peer.c`,
`testing/syscall-check/tests/errno_socket.c` and
`testing/syscall-check/tests/unmodeled_sockets.c`, which between them
carry `conform`, `reject --mutate` and `fail-closed` cases.  Each pin
below cites the kernel line and not the probe, because the probe's
verdict is about the Rocq checker and this file is about the Lean one.

HOW THE PINS ARE PROVED.  A closed pin runs `check_norm`, or its
section's sibling — `options_norm` in the options section, `alloc_norm`
in the socket and accept4 section, `io_norm` in the I/O section — each
the same passes over its own section's rows, checkers and acceptors, which
that section's header names: one `simp
+decide only` pass that opens the row, the checker and the acceptors,
decides every closed gate and reads the fixtures with the `sys_simp` set;
then, if a goal is left, the ground pass of `sys_norm` (`sys_simp_pass
+ground +decide`), which evaluates the descriptor lookups and the memory
walks no rewrite covers; and then, if a goal is still left, the first
pass again with `+ground`, because the ground pass exposes acceptors —
`check_ret_only` behind a resolved `fd_lookup`, `check_socketpair_written`
behind a decided `socketpair_dest_writable` — that only the opening set
reduces.  The acceptors with a wildcard arm (`check_ret_only`,
`check_errno_or_success`, the two socketpair acceptors, and in the
socket and accept4 section `check_new_fd_result` and `check_errno_only`)
enter the set by name, and a mismatched effect lands in the wildcard arm
by the same pass.  A `≠` pin runs `check_refute`, which is `check_norm` and then
`done`; `ne_eq` is in the first pass so the verdicts' injectivity is
reached under the negation.  The closed witness pins run `witness_norm`,
or its section's sibling — `options_witness_norm`, `alloc_witness_norm`,
`io_witness_norm` — the same passes over the witnesses.  None is `rfl`:
the unifier behind
`rfl` walks into `Int.pow 2 64` and the fixture models and does not come
back, where the kernel-routed `decide` does.

NOTHING HERE COMPARES THE LEAN CHECKER TO THE ROCQ ONE.  What these pins
prove is that this checker and a named line of Linux agree. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Net.Socket

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Net.Socket
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Net.Socket
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Net.Socket
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! ## The dispatcher's application of each checker

Each row applies its checker to the registers as `Sys/Registry/Net/Socket.lean`
narrows them — Rocq's `arm_<name>` in `Checks/Sys/Dispatch.v` and the rows
for 199, 200, 201, 203, 204, 205, 208, 209 and 210 in
`Sys/SyscallTable.lean`.  The narrowing is the kernel's own: every one of
these is a `SYSCALL_DEFINEn`
whose `fd` is an `int`, so a0 reaches the `__sys_*` entry through
`__SC_CAST` low-32; shutdown's `how` is an `int` too, and so is bind's and
connect's `addrlen`, which the checker narrows ITSELF through `sint32`
because `move_addr_to_kernel` tests its sign; the pointers and socketpair's
three `int`s arrive whole or are narrowed inside the spec.  When an arm
file under `Checks/Arms/` registers one of these numbers, its arm unfolds
to the row here.  The rows for 198, 202 and 242 sit with their own section
at the end of this file. -/

def check_bind_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_bind i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m

def check_listen_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_listen (fd32 (in_arg i 0)) (in_arg i 1) eff m

def check_connect_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_connect i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m

def check_getsockname_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_getsockname (fd32 (in_arg i 0)) eff m

def check_getpeername_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_getpeername (fd32 (in_arg i 0)) eff m

def check_shutdown_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_shutdown (fd32 (in_arg i 0)) (int32 (in_arg i 1)) eff m

def check_socketpair_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_socketpair i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m

/-- The row IS the registry arm's application: `check_bind_sound_ok` lands
in `bind_arm`'s `sa_spec` only if the row narrows each argument as
`Sys/Registry/Net/Socket.lean` does — a0 through `fd32`, a1 and a2 whole —
so a row that handed a0 over whole or narrowed a1 fails here at `h` with a
type mismatch.  `SYSCALL_DEFINE3(bind, int, fd, struct sockaddr __user *,
umyaddr, int, addrlen)` (net/socket.c:1909, Linux v6.18.46) is where the
`int` narrowing of `fd` happens.
kernel: net/socket.c:bind,__sys_bind@v6.18.46 -/
theorem bind_row_is_the_arm (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_bind_row i eff m = CheckOk m' evs) :
    (Sys.Registry.Net.Socket.bind_arm).sa_spec i m (Ok eff m' evs) :=
  check_bind_sound_ok _ _ _ _ _ _ _ _ h

/-- listen's row: a0 through `fd32`, a1 whole (`__sys_listen_socket` clamps
the backlog as an `unsigned int`, so the spec ignores it).
`SYSCALL_DEFINE2(listen, int, fd, int, backlog)` is net/socket.c:1947.
kernel: net/socket.c:listen,__sys_listen@v6.18.46 -/
theorem listen_row_is_the_arm (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_listen_row i eff m = CheckOk m' evs) :
    (Sys.Registry.Net.Socket.listen_arm).sa_spec i m (Ok eff m' evs) :=
  check_listen_sound_ok _ _ _ _ _ _ _ h

/-- connect's row: a0 through `fd32`, a1 and a2 whole.  `SYSCALL_DEFINE3(
connect, int, fd, struct sockaddr __user *, uservaddr, int, addrlen)` is
net/socket.c:2125.
kernel: net/socket.c:connect,__sys_connect@v6.18.46 -/
theorem connect_row_is_the_arm (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_connect_row i eff m = CheckOk m' evs) :
    (Sys.Registry.Net.Socket.connect_arm).sa_spec i m (Ok eff m' evs) :=
  check_connect_sound_ok _ _ _ _ _ _ _ _ h

/-- getsockname's row: a0 through `fd32`; the address pair is never read by
the arm.  `SYSCALL_DEFINE3(getsockname, …)` is net/socket.c:2162.
kernel: net/socket.c:getsockname,__sys_getsockname@v6.18.46 -/
theorem getsockname_row_is_the_arm (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_getsockname_row i eff m = CheckOk m' evs) :
    (Sys.Registry.Net.Socket.getsockname_arm).sa_spec i m (Ok eff m' evs) :=
  check_getsockname_sound_ok _ _ _ _ _ _ h

/-- getpeername's row: a0 through `fd32`.  `SYSCALL_DEFINE3(getpeername, …)`
is net/socket.c:2199.
kernel: net/socket.c:getpeername,__sys_getpeername@v6.18.46 -/
theorem getpeername_row_is_the_arm (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_getpeername_row i eff m = CheckOk m' evs) :
    (Sys.Registry.Net.Socket.getpeername_arm).sa_spec i m (Ok eff m' evs) :=
  check_getpeername_sound_ok _ _ _ _ _ _ h

/-- shutdown's row: a0 through `fd32`, a1 through `int32` — `SYSCALL_DEFINE2(
shutdown, int, fd, int, how)` (net/socket.c:2490) takes both as `int`, so a
`how` whose low word is 1 is SHUT_WR whatever its high half holds, and the
pin `check_shutdown_how_high_half_is_discarded` below says so.
kernel: net/socket.c:shutdown,__sys_shutdown@v6.18.46 -/
theorem shutdown_row_is_the_arm (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_shutdown_row i eff m = CheckOk m' evs) :
    (Sys.Registry.Net.Socket.shutdown_arm).sa_spec i m (Ok eff m' evs) :=
  check_shutdown_sound_ok _ _ _ _ _ _ _ h

/-- socketpair's row: all four registers whole; the spec narrows `family`,
`type` and `protocol` itself through `abi_low32`, and `sv` is a pointer.
`SYSCALL_DEFINE4(socketpair, int, family, int, type, int, protocol, int
__user *, usockvec)` is net/socket.c:1861.
kernel: net/socket.c:socketpair,__sys_socketpair@v6.18.46 -/
theorem socketpair_row_is_the_arm (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_socketpair_row i eff m = CheckOk m' evs) :
    (Sys.Registry.Net.Socket.socketpair_arm).sa_spec i m (Ok eff m' evs) :=
  check_socketpair_sound_ok _ _ _ _ _ _ _ _ _ h

/-! ## The two spellings of a call, Rocq's

Rocq's `bind_answering_at` and `connect_answering`/`connect_answering_c`,
kept because the ledger boundary is what half the examples are about: an
effect that claims a copy-in range where the copy never ran, or none where
it did, is `CheckReject`, and a shared helper that filled the ledger in
would hide that from every example that used it. -/

/-- `bind(3, addrp, addrlen)` over the sixteen readable bytes of
`sockaddr_in_any_mem`, answering `r` with the copy-in ledger `cis`.
`mkEffectU` rather than `mkEffect`, because `mkEffect` fixes an EMPTY
ledger and the ledger is the point. -/
def bind_answering_at (m : Model) (addrp addrlen r : word) (cis : List (word × Nat))
    : check_result :=
  check_bind_row (bind_in 3 addrp addrlen sockaddr_in_any_mem)
    (SyscallEffect.mkEffectU r [] [] [] [] cis) m

/-- `bind(3, <that address>, 16)` answering `r`, the sixteen bytes ledgered. -/
def bind_answering (m : Model) (r : word) : check_result :=
  bind_answering_at m 4096 16 r [(4096, 16)]

/-- `connect(fd, addrp, addrlen)` over `mp`, answering `r` and claiming NO
copy-in range: the spelling for the arms ABOVE the copy. -/
def connect_answering (mp : word → Option byte) (m : Model) (fd addrp addrlen r : word)
    : check_result :=
  check_connect_row (connect_in fd addrp addrlen mp) (mkEffect r [] []) m

/-- The same call claiming a copy-in range of `n` bytes at `addrp`: the
spelling for the arms BELOW the copy — which, because `__sys_connect`
copies before `__sys_connect_file` resolves the socket, includes
-ENOTSOCK. -/
def connect_answering_c (mp : word → Option byte) (m : Model) (fd addrp addrlen : word)
    (n : Nat) (r : word) : check_result :=
  check_connect_row (connect_in fd addrp addrlen mp)
    (with_copyins [(addrp, n)] (mkEffect r [] [])) m

/-- Open the rows, the checkers, the acceptors and the spec's own readers
of a socket call, and decide what is closed.  The header says why this
and not `rfl`.

`scoped`, as `Mm/Mprotect.lean`'s are and for the reason its `check_norm`
docstring gives: `Kernel/Groups.lean`, `Kernel/Signal.lean` and
`Mm/Madvise.lean` declare a `check_norm` and a `witness_norm` unscoped,
Signal a `check_refute` too, and a tactic macro is not namespaced — two
declarations of one name become a `choice` node that Lean tries in parser
order and abandons at the first alternative that ERRORS, so a module
importing this file beside one of those would run the other file's body
on every goal here.  Scoping keeps every macro of this file inside
`open` of its namespace, which every pin below is under. -/
scoped macro "check_open" cfg:Lean.Parser.Tactic.optConfig : tactic =>
  `(tactic| simp $cfg:optConfig only [check_bind_row, check_listen_row, check_connect_row,
      check_getsockname_row, check_getpeername_row, check_shutdown_row, check_socketpair_row,
      bind_answering_at, bind_answering, connect_answering, connect_answering_c,
      check_bind, check_listen, check_connect, check_getsockname, check_getpeername,
      check_shutdown, check_socketpair, check_socketpair_written, check_socketpair_faulted, sockaddr_in_any_mem128,
      check_errno_or_success, check_ret_only_copyins, check_ret_only, check_copyins,
      clear_copyins, with_copyins, errno_ret_in, sock_fd, shut_how_ok, socketpair_flags_ok,
      socketpair_modeled_b, socketpair_fds, socketpair_dest_writable, socketpair_writes,
      Bool.and_eq_true, Bool.or_eq_true, bv_eqb_eq, writes_eqb_eq, access_ranges_eqb_eq,
      check_result.CheckOk.injEq, ne_eq, reduceCtorEq, sys_simp, ↓reduceIte])

/-- Evaluate a closed call of one of the lifecycle checkers: `check_open`, the
ground pass of `sys_norm`, and `check_open +ground` for what the ground
pass exposed. -/
scoped macro "check_norm" : tactic =>
  `(tactic| (check_open +decide;
             first | done | sys_simp_pass +ground +decide -failIfUnchanged;
             first | done | check_open +ground +decide))

/-- Refute: `check_norm`, and the goal must be closed by it. -/
scoped macro "check_refute" : tactic => `(tactic| (check_norm; done))

/-! ## bind

`__sys_bind` (net/socket.c:1889, Linux v6.18.46): `fd_empty` → -EBADF;
`sock_from_file` null → -ENOTSOCK; then `move_addr_to_kernel` — `ulen < 0
|| ulen > sizeof(struct sockaddr_storage)` → -EINVAL, `ulen == 0` → 0 with
nothing copied, a failed copy → -EFAULT — and then `inet_bind_sk`:
`addr_len <
sizeof(struct sockaddr_in)` → -EINVAL, `__inet_bind`'s family gate →
-EAFNOSUPPORT, and its `sk_state != TCP_CLOSE || inet_num` → -EINVAL on a
socket already bound.  The checker's gates fire in that order, and the
ledger a `CheckOk` needs is exactly the copy `move_addr_to_kernel` made:
`ulen` bytes when it copied, nothing when it returned before the copy. -/

/-- The fd gate is first: a closed descriptor is -EBADF with nothing
copied, and an effect that ledgers the sixteen bytes anyway is a lie —
`fd_empty(f)` returns before `move_addr_to_kernel` is reached.
kernel: net/socket.c:__sys_bind@v6.18.46 -/
theorem check_bind_on_a_closed_fd_is_ebadf :
    check_bind_row (bind_in 9 4096 16 sockaddr_in_any_mem)
      (mkEffect (errno_ret EBADF) [] []) fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_bind_row (bind_in 9 4096 16 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [] [] [(4096, 16)]) fresh_socket_model
      = CheckReject ∧
    check_bind_row (bind_in 9 4096 16 sockaddr_in_any_mem)
      (mkEffect (errno_ret ENOTSOCK) [] []) fresh_socket_model = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- Every non-socket descriptor kind is -ENOTSOCK before the address is
read: a channel, a read-only file, a write-only file and a directory
(`socket_call_model`), the read end of a pipe, /dev/null and /dev/urandom
(`socket_kinds_model`).  `sock_from_file` answers NULL for every file
whose `f_op` is not `socket_file_ops`, and `__sys_bind` returns before
`move_addr_to_kernel`, so the ledger is empty and -EBADF is the lie.
kernel: net/socket.c:__sys_bind,sock_from_file@v6.18.46 -/
theorem check_bind_declines_every_non_socket_fd_kind :
    check_bind_row (bind_in 0 4096 16 sockaddr_in_any_mem)
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model = CheckOk socket_call_model [] ∧
    check_bind_row (bind_in 3 4096 16 sockaddr_in_any_mem)
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model = CheckOk socket_call_model [] ∧
    check_bind_row (bind_in 4 4096 16 sockaddr_in_any_mem)
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model = CheckOk socket_call_model [] ∧
    check_bind_row (bind_in 5 4096 16 sockaddr_in_any_mem)
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model = CheckOk socket_call_model [] ∧
    check_bind_row (bind_in 6 4096 16 sockaddr_in_any_mem)
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_bind_row (bind_in 7 4096 16 sockaddr_in_any_mem)
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_bind_row (bind_in 8 4096 16 sockaddr_in_any_mem)
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_bind_row (bind_in 3 4096 16 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret ENOTSOCK) [] [] [] [] [(4096, 16)]) socket_call_model
      = CheckReject ∧
    check_bind_row (bind_in 3 4096 16 sockaddr_in_any_mem)
      (mkEffect (errno_ret EBADF) [] []) socket_call_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `bind_input_reaches_the_state_match`: the well-formed call on a
fresh socket is a MODELED answer — the guard, before anything about the
verdict is stated, that the input threads every gate above the state
match; the first conjunct is the verdict itself, the post-state with the
socket reseated as bound.  `inet_csk_get_port` hands out a port for
INADDR_ANY:0 and `__inet_bind` returns 0.
kernel: net/socket.c:__sys_bind; net/ipv4/af_inet.c:__inet_bind@v6.18.46 -/
theorem check_bind_input_reaches_the_state_match :
    bind_answering fresh_socket_model 0
      = CheckOk (fixture_of (fds := [ (3, .FdSocket .SkBound), (0, .FdChannel 0),
                                      (1, .FdChannel 1), (2, .FdChannel 2) ])) [] ∧
    bind_answering fresh_socket_model 0 ≠ CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- The same call spelled the way the checker spells its post-state: the
model it returns IS `with_fds (fd_insert …)` of the input, and this pin
holds the fixture spelling above to that one.
kernel: net/socket.c:__sys_bind; net/ipv4/af_inet.c:__inet_bind@v6.18.46 -/
theorem check_bind_fresh_success_reseats_the_socket :
    bind_answering fresh_socket_model 0
      = CheckOk (with_fds (fd_insert (m_fds fresh_socket_model) 3 (.FdSocket .SkBound))
                          fresh_socket_model) [] := by
  check_norm

/-- Rocq's `bind_on_a_reset_connection_declines`: a socket whose connection
the peer reset is UNBOUND AGAIN in Linux, not -EINVAL.  `tcp_done`
(net/ipv4/tcp.c:5020, Linux v6.18.46) ran `tcp_set_state` to TCP_CLOSE
(:5033), whose TCP_CLOSE arm (:2993) calls `inet_put_port`
(net/ipv4/inet_hashtables.c:244; its `__inet_put_port`, :212, clears
`inet_num` at :227) unless the socket holds SOCK_BINDPORT_LOCK
(net/ipv4/tcp.c:2998-3000), and
`sk_clone_lock` (net/core/sock.c:2515) cleared that bit on the accepted
child — so both halves of `__inet_bind`'s
`sk->sk_state != TCP_CLOSE || inet->inet_num` (net/ipv4/af_inet.c:528)
are false and Linux autobinds and returns 0.  Answering -EINVAL would be
a modeled answer Linux does not give; the spec declines both answers
rather than model the port autobind draws, and the checker follows.  The
accepted socket (fd 4 of `accepted_socket_model`, TCP_ESTABLISHED)
declines the same way: every connected head does.
kernel: net/ipv4/af_inet.c:__inet_bind; net/ipv4/tcp.c:tcp_done,tcp_set_state; net/core/sock.c:sk_clone_lock; net/ipv4/inet_hashtables.c:inet_put_port@v6.18.46 -/
theorem check_bind_on_a_reset_connection_declines :
    bind_answering reset_socket_model (errno_ret EINVAL) = CheckUnmodeled ∧
    bind_answering reset_socket_model 0 = CheckUnmodeled ∧
    check_bind_row (bind_in 4 4096 16 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 16)]) accepted_socket_model
      = CheckUnmodeled ∧
    check_bind_row (bind_in 4 4096 16 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 16)]) accepted_socket_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The connected heads that are not the read-out reset: a script whose
head is a reset the program has not read yet (`connected_socket_model
NRst`) or a timeout (`connected_socket_model NTimedOut`) is `SkConnected`,
and `bind_spec` declines every `SkConnected` head because the kernel may
already have run `tcp_done` on it and put the port back — the segment
resets the socket when it ARRIVES (`tcp_validate_incoming`,
net/ipv4/tcp_input.c:6117, Linux v6.18.46: the RST test at :6183, the
in-order test at :6193-6195 jumping to `reset:` at :6264, `tcp_reset` at
:6265), not when the program reads it — so neither -EINVAL nor 0 is the
one answer.  Both decline on both heads.
kernel: net/ipv4/af_inet.c:__inet_bind; net/ipv4/tcp_input.c:tcp_validate_incoming@v6.18.46 -/
theorem check_bind_on_an_unread_reset_or_a_timeout_declines :
    check_bind_row (bind_in 4 4096 16 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 16)])
      (connected_socket_model NRst) = CheckUnmodeled ∧
    check_bind_row (bind_in 4 4096 16 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 16)])
      (connected_socket_model NRst) = CheckUnmodeled ∧
    check_bind_row (bind_in 4 4096 16 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 16)])
      (connected_socket_model NTimedOut) = CheckUnmodeled ∧
    check_bind_row (bind_in 4 4096 16 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 16)])
      (connected_socket_model NTimedOut) = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The one leaf where this checker and Rocq's part: a connected socket
whose script still holds a byte (`NCons`) or the FIN (`NFin`) is -EINVAL
in Rocq's `check_bind` — `__inet_bind`'s `sk_state != TCP_CLOSE` gate on
an established connection — and declined here, because the Lean
`bind_spec` declines every connected head: its docstring says why the
model cannot tell a byte-then-reset, which `tcp_done` has made TCP_CLOSE
— `tcp_set_state`'s TCP_CLOSE arm releasing the port unless
`SOCK_BINDPORT_LOCK` holds it (net/ipv4/tcp.c:2998-3000) — from a byte on
a live connection.  Pinned on
Rocq's -EINVAL, with the ledger and without, and on the 0 a reset-then-
autobind would give, so a checker that quietly restored Rocq's answer
here would go red.
kernel: net/ipv4/af_inet.c:__inet_bind; net/ipv4/tcp.c:tcp_done,tcp_set_state; net/ipv4/inet_hashtables.c:__inet_put_port@v6.18.46 -/
theorem check_bind_on_a_byte_or_the_fin_declines_where_rocq_answers :
    check_bind_row (bind_in 4 4096 16 sockaddr_in_any_mem) (mkEffect (errno_ret EINVAL) [] [])
      (connected_socket_model (NCons (Z_to_bv 8 65) NRst)) = CheckUnmodeled ∧
    check_bind_row (bind_in 4 4096 16 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 16)])
      (connected_socket_model (NCons (Z_to_bv 8 65) NRst)) = CheckUnmodeled ∧
    check_bind_row (bind_in 4 4096 16 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 16)])
      (connected_socket_model NFin) = CheckUnmodeled ∧
    check_bind_row (bind_in 4 4096 16 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 16)])
      (connected_socket_model NFin) = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `bind_copyin_ledger_marks_the_copy`: the ledger is `CheckOk`
exactly when it names the bytes `move_addr_to_kernel` copied.  Sixteen
bytes on a fresh socket answering -EADDRINUSE: ledgered `CheckOk`, bare
`CheckReject`.  Eight bytes: `move_addr_to_kernel` copies them and
`inet_bind_sk` answers -EINVAL, so the eight are ledgered and a bare
effect is the lie.  Length 0: `move_addr_to_kernel` returns 0 before the
copy and `inet_bind_sk` answers -EINVAL — nothing is ledgered, and a
zero-length range is the lie.  Length 129: -EINVAL before the copy, so
the same.  An unreadable address: -EFAULT with nothing copied, and a
ledger of the range that faulted is the lie.
kernel: net/socket.c:__sys_bind,move_addr_to_kernel; net/ipv4/af_inet.c:inet_bind_sk; net/ipv4/inet_connection_sock.c:inet_csk_get_port@v6.18.46 -/
theorem check_bind_copyin_ledger_marks_the_copy :
    bind_answering fresh_socket_model (errno_ret EADDRINUSE) = CheckOk fresh_socket_model [] ∧
    bind_answering_at fresh_socket_model 4096 16 (errno_ret EADDRINUSE) [] = CheckReject ∧
    bind_answering_at fresh_socket_model 4096 8 (errno_ret EINVAL) [(4096, 8)]
      = CheckOk fresh_socket_model [] ∧
    bind_answering_at fresh_socket_model 4096 8 (errno_ret EINVAL) [] = CheckReject ∧
    bind_answering_at fresh_socket_model 4096 0 (errno_ret EINVAL) []
      = CheckOk fresh_socket_model [] ∧
    bind_answering_at fresh_socket_model 4096 0 (errno_ret EINVAL) [(4096, 0)] = CheckReject ∧
    bind_answering_at fresh_socket_model 4096 129 (errno_ret EINVAL) []
      = CheckOk fresh_socket_model [] ∧
    bind_answering_at fresh_socket_model 4096 129 (errno_ret EINVAL) [(4096, 129)]
      = CheckReject ∧
    bind_answering_at fresh_socket_model 8192 16 (errno_ret EFAULT) []
      = CheckOk fresh_socket_model [] ∧
    bind_answering_at fresh_socket_model 8192 16 (errno_ret EFAULT) [(8192, 16)]
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- `addrlen` reaches `move_addr_to_kernel` as an `int`: 2^32-1 and 2^64-1
both narrow to -1, `ulen < 0` fires, and the answer is -EINVAL with
nothing copied — a checker that tested the 64-bit register would find
2^32-1 over the 128 ceiling too, so this pin holds the sign half of the
gate by a value that is -EINVAL by either reading and the ledger by a
success it must refuse.
kernel: net/socket.c:__sys_bind,move_addr_to_kernel@v6.18.46 -/
theorem check_bind_negative_addrlen_is_einval :
    bind_answering_at fresh_socket_model 4096 (Z_to_bv 64 (2 ^ 32 - 1)) (errno_ret EINVAL) []
      = CheckOk fresh_socket_model [] ∧
    bind_answering_at fresh_socket_model 4096 (Z_to_bv 64 (2 ^ 64 - 1)) (errno_ret EINVAL) []
      = CheckOk fresh_socket_model [] ∧
    bind_answering_at fresh_socket_model 4096 (Z_to_bv 64 (2 ^ 64 - 1)) 0 [] = CheckReject ∧
    bind_answering_at fresh_socket_model 4096 128 (errno_ret EINVAL) [] = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- `addrlen` is the `int` of `__sys_bind`'s signature (net/socket.c:1889,
Linux v6.18.46), so its high half is gone before `move_addr_to_kernel`
(:248) tests it: 2^32+16 is 16, sixteen bytes are copied and the ledger
names sixteen — a ledger carrying the wide length names bytes the kernel
never read, and a ledger of eight, or at the next address, names the
wrong ones.  At exactly 128, `sizeof(struct sockaddr_storage)`, the copy
still runs (the -EINVAL band is `ulen > 128`, :250-251), so 128 readable
bytes bind with a 128-byte ledger and the bare effect is refused.
kernel: net/socket.c:__sys_bind,move_addr_to_kernel; net/ipv4/inet_connection_sock.c:inet_csk_get_port@v6.18.46 -/
theorem check_bind_ledger_length_is_the_narrowed_copy :
    bind_answering_at fresh_socket_model 4096 (Z_to_bv 64 (2 ^ 32 + 16)) 0 [(4096, 16)]
      = CheckOk (with_fds (fd_insert (m_fds fresh_socket_model) 3 (.FdSocket .SkBound))
                          fresh_socket_model) [] ∧
    bind_answering_at fresh_socket_model 4096 (Z_to_bv 64 (2 ^ 32 + 16)) 0
      [(4096, 2 ^ 32 + 16)] = CheckReject ∧
    bind_answering_at fresh_socket_model 4096 16 (errno_ret EADDRINUSE) [(4096, 8)]
      = CheckReject ∧
    bind_answering_at fresh_socket_model 4096 16 (errno_ret EADDRINUSE) [(4097, 16)]
      = CheckReject ∧
    check_bind_row (bind_in 3 4096 128 sockaddr_in_any_mem128)
      (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 128)]) fresh_socket_model
      = CheckOk (with_fds (fd_insert (m_fds fresh_socket_model) 3 (.FdSocket .SkBound))
                          fresh_socket_model) [] ∧
    check_bind_row (bind_in 3 4096 128 sockaddr_in_any_mem128)
      (SyscallEffect.mkEffectU 0 [] [] [] [] []) fresh_socket_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The family gate: AF_UNIX at an AF_INET socket is -EAFNOSUPPORT, and so
is AF_UNSPEC with any address but INADDR_ANY — `__inet_bind` admits
AF_UNSPEC only when `addr->sin_addr.s_addr == htonl(INADDR_ANY)`.  The
sixteen bytes were copied, so the ledger carries them and a bare effect
is the lie; -EINVAL is the lie of a checker that ran the state check
first.
kernel: net/ipv4/af_inet.c:__inet_bind,inet_bind_sk@v6.18.46 -/
theorem check_bind_family_gate_is_eafnosupport :
    check_bind_row (bind_in 3 4096 16 sockaddr_unix_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EAFNOSUPPORT) [] [] [] [] [(4096, 16)])
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_bind_row (bind_in 3 4096 16 sockaddr_unspec_loopback_mem)
      (SyscallEffect.mkEffectU (errno_ret EAFNOSUPPORT) [] [] [] [] [(4096, 16)])
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_bind_row (bind_in 3 4096 16 sockaddr_unix_any_mem)
      (mkEffect (errno_ret EAFNOSUPPORT) [] []) fresh_socket_model = CheckReject ∧
    check_bind_row (bind_in 3 4096 16 sockaddr_unix_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 16)])
      bound_socket_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The family gate is BEFORE the state gate: AF_UNIX on a bound socket is
-EAFNOSUPPORT, not the -EINVAL the bound state would answer, because
`__inet_bind` tests `addr->sin_family` before `sk->sk_state`.
kernel: net/ipv4/af_inet.c:__inet_bind@v6.18.46 -/
theorem check_bind_family_gate_precedes_the_state_gate :
    check_bind_row (bind_in 3 4096 16 sockaddr_unix_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EAFNOSUPPORT) [] [] [] [] [(4096, 16)])
      bound_socket_model = CheckOk bound_socket_model [] := by
  check_norm

/-- AF_UNSPEC with INADDR_ANY:0 is the compatibility case `__inet_bind`
admits, and on a fresh socket it binds like AF_INET would: the same
post-state, and -EADDRINUSE admitted beside it.
kernel: net/ipv4/af_inet.c:__inet_bind; net/ipv4/inet_connection_sock.c:inet_csk_get_port@v6.18.46 -/
theorem check_bind_af_unspec_any_binds_like_af_inet :
    check_bind_row (bind_in 3 4096 16 sockaddr_unspec_any_mem)
      (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 16)]) fresh_socket_model
      = CheckOk (fixture_of (fds := [ (3, .FdSocket .SkBound), (0, .FdChannel 0),
                                      (1, .FdChannel 1), (2, .FdChannel 2) ])) [] ∧
    check_bind_row (bind_in 3 4096 16 sockaddr_unspec_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EADDRINUSE) [] [] [] [] [(4096, 16)]) fresh_socket_model
      = CheckOk fresh_socket_model [] := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- A specific address or a specific port declines: 127.0.0.1:0 and
INADDR_ANY:80 are both `CheckUnmodeled` whatever the answer, because the
model has no interface table to check the address against (the
-EADDRNOTAVAIL `__inet_bind` answers when `inet_addr_valid_or_nonlocal`
fails — an errno this tree does not even name) and no port table or
capability set (`inet_csk_get_port`'s -EADDRINUSE, the -EACCES behind
`inet_port_requires_bind_service`).
kernel: net/ipv4/af_inet.c:__inet_bind; net/ipv4/inet_connection_sock.c:inet_csk_get_port@v6.18.46 -/
theorem check_bind_specific_address_or_port_declines :
    check_bind_row (bind_in 3 4096 16 sockaddr_in_loopback_mem)
      (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 16)]) fresh_socket_model
      = CheckUnmodeled ∧
    check_bind_row (bind_in 3 4096 16 sockaddr_in_loopback_mem)
      (SyscallEffect.mkEffectU (errno_ret EADDRINUSE) [] [] [] [] [(4096, 16)])
      fresh_socket_model = CheckUnmodeled ∧
    check_bind_row (bind_in 3 4096 16 sockaddr_in_port80_mem)
      (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 16)]) fresh_socket_model
      = CheckUnmodeled ∧
    check_bind_row (bind_in 3 4096 16 sockaddr_in_port80_mem)
      (SyscallEffect.mkEffectU (errno_ret EACCES) [] [] [] [] [(4096, 16)]) fresh_socket_model
      = CheckUnmodeled ∧
    check_bind_row (bind_in 3 4096 16 sockaddr_in_port80_mem)
      (SyscallEffect.mkEffectU (errno_ret EADDRINUSE) [] [] [] [] [(4096, 16)]) fresh_socket_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The errno pool of the fresh arm is -EADDRINUSE alone: -EACCES, which
`__inet_bind` answers only for a privileged port and never for port 0,
is refused; so is -EINVAL, the bound state's answer, and -EAFNOSUPPORT,
the family gate's, which this address passed.
kernel: net/ipv4/af_inet.c:__inet_bind; net/ipv4/inet_connection_sock.c:inet_csk_get_port@v6.18.46 -/
theorem check_bind_fresh_refuses_errnos_outside_the_pool :
    bind_answering fresh_socket_model (errno_ret EACCES) = CheckReject ∧
    bind_answering fresh_socket_model (errno_ret EINVAL) = CheckReject ∧
    bind_answering fresh_socket_model (errno_ret EAFNOSUPPORT) = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- A bound or a listening socket is -EINVAL: `__inet_bind` tests `sk->sk_state
!= TCP_CLOSE || inet->inet_num`, and both have a local port.  The
sixteen bytes were copied, so the ledger carries them; success and
-EADDRINUSE are the lies, and the model is unchanged.
kernel: net/ipv4/af_inet.c:__inet_bind; net/ipv4/inet_connection_sock.c:inet_csk_get_port@v6.18.46 -/
theorem check_bind_twice_is_einval :
    bind_answering bound_socket_model (errno_ret EINVAL) = CheckOk bound_socket_model [] ∧
    bind_answering listening_socket_model (errno_ret EINVAL)
      = CheckOk listening_socket_model [] ∧
    bind_answering_at bound_socket_model 4096 16 (errno_ret EINVAL) [] = CheckReject ∧
    bind_answering bound_socket_model 0 = CheckReject ∧
    bind_answering bound_socket_model (errno_ret EADDRINUSE) = CheckReject ∧
    bind_answering listening_socket_model 0 = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-! ## connect

`__sys_connect` (net/socket.c:2109, Linux v6.18.46): `fd_empty` → -EBADF, then
`move_addr_to_kernel` — the same three answers as bind's — and only then
`__sys_connect_file`, whose `sock_from_file` null is -ENOTSOCK: the one
ordering that is not bind's, and the reason connect's -ENOTSOCK carries
the copy in its ledger where bind's carries nothing.  Then
`__inet_stream_connect`: `addr_len < sizeof(uaddr->sa_family)` → -EINVAL;
AF_UNSPEC → `tcp_disconnect`; SS_CONNECTED, or SS_UNCONNECTED with
`sk_state != TCP_CLOSE`, → -EISCONN; else `tcp_v4_connect`, whose
`addr_len < sizeof(struct sockaddr_in)` is -EINVAL and whose `sin_family
!= AF_INET` is -EAFNOSUPPORT.  The attempt itself is declined. -/

/-- Rocq's `connect_on_a_listening_socket_is_eisconn`: a listening socket
has `sk_state == TCP_LISTEN`, so `__inet_stream_connect`'s SS_UNCONNECTED
arm answers -EISCONN, with the sixteen copied bytes in the ledger; -EINVAL
is the lie.
kernel: net/ipv4/af_inet.c:__inet_stream_connect@v6.18.46 -/
theorem check_connect_on_a_listening_socket_is_eisconn :
    connect_answering_c connect_addr_mem listening_socket_model 3 8192 16 16 (errno_ret EISCONN)
      = CheckOk listening_socket_model [] ∧
    connect_answering_c connect_addr_mem listening_socket_model 3 8192 16 16 (errno_ret EINVAL)
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- Rocq's `connect_eisconn_must_carry_its_copy`: the same answer offered
without its copy-in range is rejected — the placement of the ledger above
the state switch is a checked fact.
kernel: net/socket.c:__sys_connect,move_addr_to_kernel; net/ipv4/af_inet.c:__inet_stream_connect@v6.18.46 -/
theorem check_connect_eisconn_must_carry_its_copy :
    connect_answering connect_addr_mem listening_socket_model 3 8192 16 (errno_ret EISCONN)
      = CheckReject := by
  check_refute

/-- Rocq's `connect_on_an_accepted_socket_is_eisconn`: `__inet_accept`
leaves `newsock->state = SS_CONNECTED`, so fd 4 is -EISCONN from the
SS_CONNECTED arm.
kernel: net/ipv4/af_inet.c:__inet_stream_connect,__inet_accept@v6.18.46 -/
theorem check_connect_on_an_accepted_socket_is_eisconn :
    connect_answering_c connect_addr_mem accepted_socket_model 4 8192 16 16 (errno_ret EISCONN)
      = CheckOk accepted_socket_model [] := by
  check_norm

/-- Rocq's `connect_on_a_reset_connection_is_eisconn`: `tcp_done` moves
`sk_state` to TCP_CLOSE and leaves `sock->state` at SS_CONNECTED, so the
switch still takes its SS_CONNECTED arm and the reset socket is -EISCONN;
-EINVAL and success are lies, and AF_UNSPEC on it is declined rather than
answered 0.
kernel: net/ipv4/af_inet.c:__inet_stream_connect; net/ipv4/tcp.c:tcp_done@v6.18.46 -/
theorem check_connect_on_a_reset_connection_is_eisconn :
    connect_answering_c connect_addr_mem reset_socket_model 3 8192 16 16 (errno_ret EISCONN)
      = CheckOk reset_socket_model [] ∧
    connect_answering_c connect_addr_mem reset_socket_model 3 8192 16 16 (errno_ret EINVAL)
      = CheckReject ∧
    connect_answering_c connect_addr_mem reset_socket_model 3 8192 16 16 0 = CheckReject ∧
    connect_answering_c connect_unspec_mem reset_socket_model 3 8192 2 2 0 = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `connect_is_eisconn_whatever_the_peer_has_left_to_say`: the
peer's script does not enter — connect reads `sock->state`, which no
segment from the peer touches.
kernel: net/ipv4/af_inet.c:__inet_stream_connect@v6.18.46 -/
theorem check_connect_is_eisconn_whatever_the_peer_has_left_to_say :
    connect_answering_c connect_addr_mem (connected_socket_model NFin) 4 8192 16 16
      (errno_ret EISCONN) = CheckOk (connected_socket_model NFin) [] ∧
    connect_answering_c connect_addr_mem (connected_socket_model NRst) 4 8192 16 16
      (errno_ret EISCONN) = CheckOk (connected_socket_model NRst) [] ∧
    connect_answering_c connect_addr_mem (connected_socket_model NTimedOut) 4 8192 16 16
      (errno_ret EISCONN) = CheckOk (connected_socket_model NTimedOut) [] ∧
    connect_answering_c connect_addr_mem (connected_socket_model (NCons (Z_to_bv 8 65) NFin))
      4 8192 16 16 (errno_ret EISCONN)
      = CheckOk (connected_socket_model (NCons (Z_to_bv 8 65) NFin)) [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `connect_faults_before_it_reaches_enotsock`: `__sys_connect`
copies the address before `__sys_connect_file` resolves the socket, so an
unreadable address on a channel descriptor is -EFAULT and -ENOTSOCK is the
lie; the same call to bind is -ENOTSOCK, because `__sys_bind` resolves the
socket first.  The -EFAULT carries no ledger: that arm IS the copy failing.
kernel: net/socket.c:__sys_connect,__sys_connect_file,move_addr_to_kernel,__sys_bind@v6.18.46 -/
theorem check_connect_faults_before_it_reaches_enotsock :
    connect_answering (fun _ => none) listening_socket_model 1 8192 16 (errno_ret EFAULT)
      = CheckOk listening_socket_model [] ∧
    connect_answering (fun _ => none) listening_socket_model 1 8192 16 (errno_ret ENOTSOCK)
      = CheckReject ∧
    check_bind_row (bind_in 1 8192 16 (fun _ => none)) (mkEffect (errno_ret ENOTSOCK) [] [])
      listening_socket_model = CheckOk listening_socket_model [] := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `connect_on_a_channel_fd_is_enotsock`: with a readable address
-ENOTSOCK still wins, and it carries the ledger, because the copy already
happened.
kernel: net/socket.c:__sys_connect,__sys_connect_file@v6.18.46 -/
theorem check_connect_on_a_channel_fd_is_enotsock :
    connect_answering_c connect_addr_mem listening_socket_model 1 8192 16 16 (errno_ret ENOTSOCK)
      = CheckOk listening_socket_model [] ∧
    connect_answering connect_addr_mem listening_socket_model 1 8192 16 (errno_ret ENOTSOCK)
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- Every non-socket descriptor kind is -ENOTSOCK with the copy ledgered:
the four kinds of `socket_call_model` and the three of
`socket_kinds_model`.  `sock_from_file` answers NULL for each.
kernel: net/socket.c:__sys_connect,__sys_connect_file,sock_from_file@v6.18.46 -/
theorem check_connect_declines_every_non_socket_fd_kind :
    connect_answering_c connect_addr_mem socket_call_model 0 8192 16 16 (errno_ret ENOTSOCK)
      = CheckOk socket_call_model [] ∧
    connect_answering_c connect_addr_mem socket_call_model 3 8192 16 16 (errno_ret ENOTSOCK)
      = CheckOk socket_call_model [] ∧
    connect_answering_c connect_addr_mem socket_call_model 4 8192 16 16 (errno_ret ENOTSOCK)
      = CheckOk socket_call_model [] ∧
    connect_answering_c connect_addr_mem socket_call_model 5 8192 16 16 (errno_ret ENOTSOCK)
      = CheckOk socket_call_model [] ∧
    connect_answering_c connect_addr_mem socket_kinds_model 6 8192 16 16 (errno_ret ENOTSOCK)
      = CheckOk socket_kinds_model [] ∧
    connect_answering_c connect_addr_mem socket_kinds_model 7 8192 16 16 (errno_ret ENOTSOCK)
      = CheckOk socket_kinds_model [] ∧
    connect_answering_c connect_addr_mem socket_kinds_model 8 8192 16 16 (errno_ret ENOTSOCK)
      = CheckOk socket_kinds_model [] ∧
    connect_answering_c connect_addr_mem socket_call_model 3 8192 16 16 (errno_ret EBADF)
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `connect_on_a_closed_fd_is_ebadf`: -EBADF before the address is
touched, so an unreadable address on a closed descriptor is still -EBADF
and claims no copy.
kernel: net/socket.c:__sys_connect@v6.18.46 -/
theorem check_connect_on_a_closed_fd_is_ebadf :
    connect_answering (fun _ => none) listening_socket_model 9 8192 16 (errno_ret EBADF)
      = CheckOk listening_socket_model [] ∧
    connect_answering_c connect_addr_mem listening_socket_model 9 8192 16 16 (errno_ret EBADF)
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- A length of 0 on a non-socket descriptor: `move_addr_to_kernel`
returns 0 having copied nothing (`if (ulen == 0) return 0;`), and only then
does `__sys_connect_file` reach `sock_from_file`'s NULL — so -ENOTSOCK
carries an EMPTY ledger, over a readable address and over an unreadable
one alike (nothing was read, so nothing can fault and -EFAULT is a lie),
and a zero-length entry at the address — what a checker that ledgered
every copy below the length gate would demand — is refused.  The
pins-only mutation pass over f97a1738b found the `al = 0` selector of
this leaf pinned by nothing: every other connect pin on a non-socket
passes a length of 16.
kernel: net/socket.c:__sys_connect,move_addr_to_kernel,__sys_connect_file,sock_from_file@v6.18.46 -/
theorem check_connect_on_a_non_socket_with_no_length_copies_nothing :
    connect_answering connect_addr_mem socket_call_model 3 8192 0 (errno_ret ENOTSOCK)
      = CheckOk socket_call_model [] ∧
    connect_answering (fun _ => none) socket_call_model 3 8192 0 (errno_ret ENOTSOCK)
      = CheckOk socket_call_model [] ∧
    connect_answering_c connect_addr_mem socket_call_model 3 8192 0 0 (errno_ret ENOTSOCK)
      = CheckReject ∧
    connect_answering (fun _ => none) socket_call_model 3 8192 0 (errno_ret EFAULT)
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `connect_length_thresholds`, in the order the kernel applies
them: `move_addr_to_kernel` rejects above 128 and below 0 (2^32-1 is -1
as an `int`); `__inet_stream_connect` rejects below 2, and a length of 0
copies nothing and cannot fault, so over an unreadable address it lands
on that minimum and not on -EFAULT; a length of 1 over a readable
address copies one byte and is -EINVAL from the same minimum, so -EFAULT
is the lie.
kernel: net/socket.c:__sys_connect,move_addr_to_kernel; net/ipv4/af_inet.c:__inet_stream_connect@v6.18.46 -/
theorem check_connect_length_thresholds :
    connect_answering connect_addr_mem listening_socket_model 3 8192 129 (errno_ret EINVAL)
      = CheckOk listening_socket_model [] ∧
    connect_answering connect_addr_mem listening_socket_model 3 8192 (Z_to_bv 64 (2 ^ 32 - 1))
      (errno_ret EINVAL) = CheckOk listening_socket_model [] ∧
    connect_answering (fun _ => none) listening_socket_model 3 8192 0 (errno_ret EINVAL)
      = CheckOk listening_socket_model [] ∧
    connect_answering connect_addr_mem listening_socket_model 3 8192 1 (errno_ret EFAULT)
      = CheckReject ∧
    connect_answering_c connect_addr_mem listening_socket_model 3 8192 1 1 (errno_ret EINVAL)
      = CheckOk listening_socket_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The lies the thresholds pin leaves open, each alone: on the listener,
129 answered 0 and 129 answered -EFAULT are refused — the band gate fires
before anything is read, so no ledger is due on either — and a length of
1 over a readable address with its one byte LEDGERED is still not -EFAULT,
the errno half by itself.  And the narrowing to `int` in both directions,
as bind's `check_bind_ledger_length_is_the_narrowed_copy` has it: 2^32+16
is sixteen bytes to `move_addr_to_kernel`, -EISCONN on the listener with a
16-byte ledger, and the -EINVAL an unnarrowed `ulen > 128` would answer
is refused with the ledger and without.
kernel: net/socket.c:__sys_connect,move_addr_to_kernel; net/ipv4/af_inet.c:__inet_stream_connect@v6.18.46 -/
theorem check_connect_length_band_lies_and_the_narrowing :
    connect_answering connect_addr_mem listening_socket_model 3 8192 129 0 = CheckReject ∧
    connect_answering connect_addr_mem listening_socket_model 3 8192 129 (errno_ret EFAULT)
      = CheckReject ∧
    connect_answering_c connect_addr_mem listening_socket_model 3 8192 1 1 (errno_ret EFAULT)
      = CheckReject ∧
    connect_answering_c connect_addr_mem listening_socket_model 3 8192 (Z_to_bv 64 (2 ^ 32 + 16))
      16 (errno_ret EISCONN) = CheckOk listening_socket_model [] ∧
    connect_answering connect_addr_mem listening_socket_model 3 8192 (Z_to_bv 64 (2 ^ 32 + 16))
      (errno_ret EINVAL) = CheckReject ∧
    connect_answering_c connect_addr_mem listening_socket_model 3 8192 (Z_to_bv 64 (2 ^ 32 + 16))
      16 (errno_ret EINVAL) = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The ledger connect carries is the copy `move_addr_to_kernel` made —
sixteen bytes at the address given — and not merely "a copy": fifteen
bytes, sixteen at the next address, or the range twice are refused on the
-ENOTSOCK arm and on the -EISCONN arm alike, as bind's
`check_bind_ledger_length_is_the_narrowed_copy` refuses its own.
kernel: net/socket.c:__sys_connect,move_addr_to_kernel,__sys_connect_file; net/ipv4/af_inet.c:__inet_stream_connect@v6.18.46 -/
theorem check_connect_ledger_is_the_exact_copy :
    check_connect_row (connect_in 1 8192 16 connect_addr_mem)
      (with_copyins [(8192, 15)] (mkEffect (errno_ret ENOTSOCK) [] [])) listening_socket_model
      = CheckReject ∧
    check_connect_row (connect_in 1 8192 16 connect_addr_mem)
      (with_copyins [(8193, 16)] (mkEffect (errno_ret ENOTSOCK) [] [])) listening_socket_model
      = CheckReject ∧
    check_connect_row (connect_in 3 8192 16 connect_addr_mem)
      (with_copyins [(8192, 15)] (mkEffect (errno_ret EISCONN) [] [])) listening_socket_model
      = CheckReject ∧
    check_connect_row (connect_in 3 8192 16 connect_addr_mem)
      (with_copyins [(8193, 16)] (mkEffect (errno_ret EISCONN) [] [])) listening_socket_model
      = CheckReject ∧
    check_connect_row (connect_in 3 8192 16 connect_addr_mem)
      (with_copyins [(8192, 16), (8192, 16)] (mkEffect (errno_ret EISCONN) [] []))
      listening_socket_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

set_option maxRecDepth 4096 in
/-- The top of the band is inclusive: 128 bytes, `sizeof(struct
sockaddr_storage)`, is copied whole by `move_addr_to_kernel` — `ulen >
sizeof(...)` refuses 129 and admits 128 — so on the listener it is
-EISCONN with a 128-byte ledger, and -EINVAL, with the ledger or bare, is
the lie.  bind's `check_bind_ledger_length_is_the_narrowed_copy` has the
same edge; the pins-only mutation pass over f97a1738b found connect's
`SOCKADDR_STORAGE_SIZE < al` gate flippable to `≤` with nothing going
red.  `maxRecDepth` is raised as `Fs/Select.lean` raises it: the ledger's
`bs.length` is the length of a 128-element list `read_bytes_map` built,
and `simp` walks it one cell per level.
kernel: net/socket.c:__sys_connect,move_addr_to_kernel; net/ipv4/af_inet.c:__inet_stream_connect@v6.18.46 -/
theorem check_connect_full_storage_length_is_copied :
    connect_answering_c connect_addr_mem128 listening_socket_model 3 8192 128 128
      (errno_ret EISCONN) = CheckOk listening_socket_model [] ∧
    connect_answering connect_addr_mem128 listening_socket_model 3 8192 128 (errno_ret EINVAL)
      = CheckReject ∧
    connect_answering_c connect_addr_mem128 listening_socket_model 3 8192 128 128
      (errno_ret EINVAL) = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `connect_on_a_fresh_socket_reaches_tcp_v4_connect`: the 16-byte
minimum and the family check are `tcp_v4_connect`'s, so a 4-byte address
is -EINVAL and a full-length AF_UNIX address is -EAFNOSUPPORT, not
-EINVAL.
kernel: net/ipv4/tcp_ipv4.c:tcp_v4_connect@v6.18.46 -/
theorem check_connect_on_a_fresh_socket_reaches_tcp_v4_connect :
    connect_answering_c connect_addr_mem fresh_socket_model 3 8192 4 4 (errno_ret EINVAL)
      = CheckOk fresh_socket_model [] ∧
    connect_answering_c connect_unix_family_mem fresh_socket_model 3 8192 16 16
      (errno_ret EAFNOSUPPORT) = CheckOk fresh_socket_model [] ∧
    connect_answering_c connect_unix_family_mem fresh_socket_model 3 8192 16 16
      (errno_ret EINVAL) = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- `tcp_v4_connect` tests the length before the family — `addr_len <
sizeof(struct sockaddr_in)` is -EINVAL at :236, `sin_family != AF_INET`
-EAFNOSUPPORT at :239 — so eight AF_UNIX bytes on the fresh socket and
fifteen on the bound one are -EINVAL with the copy ledgered, and
-EAFNOSUPPORT is the lie at both; fifteen AF_INET bytes on the fresh
socket are -EINVAL too, not the decline the sixteen-byte address earns.
`inet_bind_sk` has the same order (its :453 before `__inet_bind`'s
:484-491 family gate and the `get_port` behind it), so at fifteen bytes
bind's success and its -EADDRINUSE, ledger and all, are refused: the port
lookup is never reached.  The pins-only mutation pass over f97a1738b let
the checker's `al < SOCKADDR_IN_SIZE` test move behind the family test,
and slide to `al < 15`, with nothing going red.
kernel: net/ipv4/tcp_ipv4.c:tcp_v4_connect; net/ipv4/af_inet.c:inet_bind_sk,__inet_bind,__inet_stream_connect; net/ipv4/inet_connection_sock.c:inet_csk_get_port; net/socket.c:move_addr_to_kernel@v6.18.46 -/
theorem check_short_address_length_precedes_the_family :
    connect_answering_c connect_unix_family_mem fresh_socket_model 3 8192 8 8 (errno_ret EINVAL)
      = CheckOk fresh_socket_model [] ∧
    connect_answering_c connect_unix_family_mem fresh_socket_model 3 8192 8 8
      (errno_ret EAFNOSUPPORT) = CheckReject ∧
    connect_answering_c connect_unix_family_mem bound_socket_model 3 8192 15 15
      (errno_ret EINVAL) = CheckOk bound_socket_model [] ∧
    connect_answering_c connect_unix_family_mem bound_socket_model 3 8192 15 15
      (errno_ret EAFNOSUPPORT) = CheckReject ∧
    connect_answering_c connect_addr_mem fresh_socket_model 3 8192 15 15 (errno_ret EINVAL)
      = CheckOk fresh_socket_model [] ∧
    check_bind_row (bind_in 3 4096 15 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 15)]) fresh_socket_model = CheckReject ∧
    bind_answering_at fresh_socket_model 4096 15 (errno_ret EADDRINUSE) [(4096, 15)]
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `connect_attempt_is_declined_not_refused`: a well-formed AF_INET
connect on a fresh socket is `CheckUnmodeled` — the model has no peer to
answer with — and every return is declined alike, so no errno is smuggled
in on this arm: 0, the -ECONNREFUSED `tcp_reset` records on a RST in
SYN_SENT and the -ETIMEDOUT `tcp_write_err` records when the SYN
retransmits run out all land here.
kernel: net/ipv4/af_inet.c:__inet_stream_connect; net/ipv4/tcp_input.c:tcp_reset; net/ipv4/tcp_timer.c:tcp_write_err@v6.18.46 -/
theorem check_connect_attempt_is_declined_not_refused :
    connect_answering_c connect_addr_mem fresh_socket_model 3 8192 16 16 0 = CheckUnmodeled ∧
    connect_answering_c connect_addr_mem fresh_socket_model 3 8192 16 16 (errno_ret ECONNREFUSED)
      = CheckUnmodeled ∧
    connect_answering_c connect_addr_mem fresh_socket_model 3 8192 16 16 (errno_ret ETIMEDOUT)
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `connect_af_unspec_is_a_disconnect`: `tcp_disconnect` has one
return statement, `return 0`, and on a socket with no port, no queue and
no connection every branch inside it is dead, so the fresh socket's is
answered 0 with the two bytes ledgered; on a listening socket the same
call would run `inet_csk_listen_stop` and empty the accept queue, which
`SockState` cannot say, and on the accepted socket it would reset a
connection — both declined.
kernel: net/ipv4/tcp.c:tcp_disconnect; net/ipv4/af_inet.c:__inet_stream_connect@v6.18.46 -/
theorem check_connect_af_unspec_is_a_disconnect :
    connect_answering_c connect_unspec_mem fresh_socket_model 3 8192 2 2 0
      = CheckOk fresh_socket_model [] ∧
    connect_answering_c connect_unspec_mem listening_socket_model 3 8192 2 2 0
      = CheckUnmodeled ∧
    connect_answering_c connect_unspec_mem accepted_socket_model 4 8192 2 2 0
      = CheckUnmodeled ∧
    connect_answering connect_unspec_mem fresh_socket_model 3 8192 2 0 = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The bound socket's disconnect declines too: `tcp_disconnect`
(net/ipv4/tcp.c:3346, Linux v6.18.46) on a socket that holds a port skips
`tcp_set_state` (`old_state` is TCP_CLOSE, :3355-3356) but runs
`inet_bhash2_reset_saddr` (:3388) — port bookkeeping `SockState` has no
field for — so `connect_spec` answers AF_UNSPEC on the fresh socket alone,
and the checker declines 0 and -EINVAL alike here.
kernel: net/ipv4/tcp.c:tcp_disconnect; net/ipv4/af_inet.c:__inet_stream_connect@v6.18.46 -/
theorem check_connect_af_unspec_on_a_bound_socket_declines :
    connect_answering_c connect_unspec_mem bound_socket_model 3 8192 2 2 0 = CheckUnmodeled ∧
    connect_answering_c connect_unspec_mem bound_socket_model 3 8192 2 2 (errno_ret EINVAL)
      = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- The connect declines on a second offered answer: the disconnect on a
listening, an accepted and a reset socket declines the -EINVAL
`tcp_disconnect`'s callers never produce as it declines the 0 they do,
ledger and all.  A decline that held for one return only would be a
checker answering the rest.
kernel: net/ipv4/af_inet.c:__inet_stream_connect; net/ipv4/tcp.c:tcp_disconnect@v6.18.46 -/
theorem check_connect_declines_hold_on_a_second_answer :
    connect_answering_c connect_unspec_mem listening_socket_model 3 8192 2 2 (errno_ret EINVAL)
      = CheckUnmodeled ∧
    connect_answering_c connect_unspec_mem accepted_socket_model 4 8192 2 2 (errno_ret EINVAL)
      = CheckUnmodeled ∧
    connect_answering_c connect_unspec_mem reset_socket_model 3 8192 2 2 (errno_ret EINVAL)
      = CheckUnmodeled ∧
    connect_answering connect_unspec_mem reset_socket_model 3 8192 2 0 = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `connect_on_a_bound_socket_is_not_eisconn`: `__inet_bind` never
calls `tcp_set_state`, so a bound socket is still TCP_CLOSE and
`__inet_stream_connect`'s SS_UNCONNECTED arm sends it to
`tcp_v4_connect` — the length and family checks it reaches are pinned,
the attempt is declined, and AF_UNSPEC is declined too, since the port
`__inet_bind` took is what `tcp_disconnect` might release.
kernel: net/ipv4/af_inet.c:__inet_stream_connect,__inet_bind; net/ipv4/tcp_ipv4.c:tcp_v4_connect@v6.18.46 -/
theorem check_connect_on_a_bound_socket_is_not_eisconn :
    connect_answering_c connect_addr_mem bound_socket_model 3 8192 4 4 (errno_ret EINVAL)
      = CheckOk bound_socket_model [] ∧
    connect_answering_c connect_addr_mem bound_socket_model 3 8192 4 4 (errno_ret EISCONN)
      = CheckReject ∧
    connect_answering_c connect_unix_family_mem bound_socket_model 3 8192 16 16
      (errno_ret EAFNOSUPPORT) = CheckOk bound_socket_model [] ∧
    connect_answering_c connect_addr_mem bound_socket_model 3 8192 16 16 0 = CheckUnmodeled ∧
    connect_answering_c connect_unspec_mem bound_socket_model 3 8192 2 2 0 = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `connect_af_unspec_precedes_the_state_switch`: a 2-byte AF_UNSPEC
address on a listening socket is declined — the -EISCONN arm never sees
it — while the same 2 bytes with `sin_family` AF_INET are -EISCONN on that
socket and -EINVAL on a fresh one, from `tcp_v4_connect`'s 16-byte
minimum a step further down.
kernel: net/ipv4/af_inet.c:__inet_stream_connect; net/ipv4/tcp_ipv4.c:tcp_v4_connect@v6.18.46 -/
theorem check_connect_af_unspec_precedes_the_state_switch :
    connect_answering_c connect_unspec_mem listening_socket_model 3 8192 2 2 (errno_ret EISCONN)
      = CheckUnmodeled ∧
    connect_answering_c connect_addr_mem listening_socket_model 3 8192 2 2 (errno_ret EISCONN)
      = CheckOk listening_socket_model [] ∧
    connect_answering_c connect_addr_mem fresh_socket_model 3 8192 2 2 (errno_ret EINVAL)
      = CheckOk fresh_socket_model [] := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-! ## listen

`__sys_listen` (net/socket.c:1933, Linux v6.18.46): `fd_empty` → -EBADF,
`sock_from_file` null → -ENOTSOCK, then `inet_listen`: `sock->state !=
SS_UNCONNECTED || sock->type != SOCK_STREAM` → -EINVAL, then
`__inet_listen_sk`: a state other than TCP_CLOSE or TCP_LISTEN → -EINVAL,
TCP_LISTEN → 0 with nothing done, TCP_CLOSE → `inet_csk_listen_start`, whose
`inet_csk_get_port` on a socket with no port yet can answer -EADDRINUSE.
Rocq has no `check_syscall` example over listen; the pins here are the
Lean file's own. -/

/-- The fd gate and the kind gate: a closed descriptor is -EBADF and every
non-socket kind is -ENOTSOCK, each refusing the other's errno.
kernel: net/socket.c:__sys_listen,sock_from_file@v6.18.46 -/
theorem check_listen_declines_every_non_socket_fd_kind :
    check_listen_row (listen_in 9 128) (mkEffect (errno_ret EBADF) [] []) fresh_socket_model
      = CheckOk fresh_socket_model [] ∧
    check_listen_row (listen_in 0 128) (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model
      = CheckOk socket_call_model [] ∧
    check_listen_row (listen_in 3 128) (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model
      = CheckOk socket_call_model [] ∧
    check_listen_row (listen_in 4 128) (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model
      = CheckOk socket_call_model [] ∧
    check_listen_row (listen_in 5 128) (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model
      = CheckOk socket_call_model [] ∧
    check_listen_row (listen_in 6 128) (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model
      = CheckOk socket_kinds_model [] ∧
    check_listen_row (listen_in 7 128) (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model
      = CheckOk socket_kinds_model [] ∧
    check_listen_row (listen_in 8 128) (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model
      = CheckOk socket_kinds_model [] ∧
    check_listen_row (listen_in 9 128) (mkEffect (errno_ret ENOTSOCK) [] []) fresh_socket_model
      = CheckReject ∧
    check_listen_row (listen_in 3 128) (mkEffect (errno_ret EBADF) [] []) socket_call_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- listen on a FRESH socket: `inet_csk_listen_start` runs `get_port` on a
socket with no port, so -EADDRINUSE is admitted beside success; success
reseats the socket as listening at the head of the table — the first
conjunct names that model exactly, which is what holds the checker to
moving the entry.  -EINVAL, the answer of the states `__inet_listen_sk`
refuses, is the lie; and the call is modeled, which is the guard the
verdicts above rest on.
kernel: net/ipv4/inet_connection_sock.c:inet_csk_listen_start,inet_csk_get_port; net/ipv4/af_inet.c:__inet_listen_sk@v6.18.46 -/
theorem check_listen_on_a_fresh_socket :
    check_listen_row (listen_in 3 128) (mkEffect 0 [] []) fresh_socket_model
      = CheckOk (fixture_of (fds := [ (3, .FdSocket .SkListening), (0, .FdChannel 0),
                                      (1, .FdChannel 1), (2, .FdChannel 2) ])) [] ∧
    check_listen_row (listen_in 3 128) (mkEffect (errno_ret EADDRINUSE) [] []) fresh_socket_model
      = CheckOk fresh_socket_model [] ∧
    check_listen_row (listen_in 3 128) (mkEffect (errno_ret EINVAL) [] []) fresh_socket_model
      = CheckReject ∧
    check_listen_row (listen_in 3 128) (mkEffect 0 [] []) fresh_socket_model
      ≠ CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- listen on a BOUND socket: the port is already held, so
`inet_csk_listen_start` answers 0 and the socket is reseated as listening;
-EADDRINUSE, the fresh socket's other answer, is the lie here.
kernel: net/ipv4/inet_connection_sock.c:inet_csk_listen_start,inet_csk_get_port; net/ipv4/af_inet.c:__inet_listen_sk@v6.18.46 -/
theorem check_listen_on_a_bound_socket :
    check_listen_row (listen_in 3 128) (mkEffect 0 [] []) bound_socket_model
      = CheckOk (fixture_of (fds := [ (3, .FdSocket .SkListening), (0, .FdChannel 0),
                                      (1, .FdChannel 1), (2, .FdChannel 2) ])) [] ∧
    check_listen_row (listen_in 3 128) (mkEffect 0 [] []) bound_socket_model
      = CheckOk (with_fds (fd_insert (m_fds bound_socket_model) 3 (.FdSocket .SkListening))
                          bound_socket_model) [] ∧
    check_listen_row (listen_in 3 128) (mkEffect (errno_ret EADDRINUSE) [] []) bound_socket_model
      = CheckReject ∧
    check_listen_row (listen_in 3 128) (mkEffect (errno_ret EINVAL) [] []) bound_socket_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- listen on a LISTENING socket: `__inet_listen_sk`'s `old_state ==
TCP_LISTEN` arm only refreshes the backlog, so the answer is 0 and the
model is unchanged.
kernel: net/ipv4/af_inet.c:__inet_listen_sk; net/ipv4/inet_connection_sock.c:inet_csk_get_port@v6.18.46 -/
theorem check_listen_twice_is_a_no_op :
    check_listen_row (listen_in 3 128) (mkEffect 0 [] []) listening_socket_model
      = CheckOk listening_socket_model [] ∧
    check_listen_row (listen_in 3 128) (mkEffect (errno_ret EADDRINUSE) [] [])
      listening_socket_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- listen on a connected or a reset socket is -EINVAL from `inet_listen`:
`sock->state` is SS_CONNECTED on both (`tcp_done` does not touch it), so
the `!= SS_UNCONNECTED` test fires; success is the lie.
kernel: net/ipv4/af_inet.c:inet_listen; net/ipv4/tcp.c:tcp_done@v6.18.46 -/
theorem check_listen_on_a_connection_is_einval :
    check_listen_row (listen_in 4 128) (mkEffect (errno_ret EINVAL) [] []) accepted_socket_model
      = CheckOk accepted_socket_model [] ∧
    check_listen_row (listen_in 3 128) (mkEffect (errno_ret EINVAL) [] []) reset_socket_model
      = CheckOk reset_socket_model [] ∧
    check_listen_row (listen_in 4 128) (mkEffect 0 [] []) accepted_socket_model = CheckReject ∧
    check_listen_row (listen_in 3 128) (mkEffect 0 [] []) reset_socket_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The backlog never enters: `__sys_listen_socket` clamps it as an
`unsigned int` against `somaxconn` and every value reaches the same
answer, 0 and -1 included.
kernel: net/socket.c:__sys_listen,__sys_listen_socket@v6.18.46 -/
theorem check_listen_ignores_the_backlog :
    check_listen_row (listen_in 3 0) (mkEffect 0 [] []) listening_socket_model
      = CheckOk listening_socket_model [] ∧
    check_listen_row (listen_in 3 (Z_to_bv 64 (2 ^ 64 - 1))) (mkEffect 0 [] [])
      listening_socket_model = CheckOk listening_socket_model [] := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-! ## getsockname, getpeername and shutdown: the fd first

All three resolve the descriptor first — `CLASS(fd, f)` then
`sock_from_file` in `__sys_getsockname`, `__sys_getpeername` and
`__sys_shutdown` — so no argument changes the answer on a closed or a
non-socket descriptor.  Rocq spells those calls with the registers a
translating emulator once answered ahead of the fd: a level no protocol
registers in a1, an unmapped pointer in a3.  On 204 and 205 the same
registers are the address pair, on 210 a `how` outside {0, 1, 2}. -/

/-- Rocq's `[fd; 999; 999; 4096; 4; 0]`: the register shape of
`socket_calls_decline_every_non_socket_fd_kind`. -/
def socket_call_in (sysno fd : word) : SyscallInput :=
  SyscallInput.mkInput sysno [fd, 999, 999, 4096, 4, 0] (fun _ => none) (fun _ => none)

/-- Rocq's `[3; 0; 0; 0; 0; 0]`: every pointer NULL, on the live non-socket
descriptor. -/
def socket_call_null_in (sysno : word) : SyscallInput :=
  SyscallInput.mkInput sysno [3, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- Rocq's `socket_calls_decline_every_non_socket_fd_kind`, the 204 column,
all twelve of its cells: a channel, a file, a write-only file and a
directory are -ENOTSOCK, and on each of the four -EBADF and success are
lies.  The three kinds Rocq's table never held answer the same.
kernel: net/socket.c:__sys_getsockname,sock_from_file@v6.18.46 -/
theorem check_getsockname_declines_every_non_socket_fd_kind :
    check_getsockname_row (socket_call_in 204 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_getsockname_row (socket_call_in 204 3) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_getsockname_row (socket_call_in 204 4) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_getsockname_row (socket_call_in 204 5) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_getsockname_row (socket_call_in 204 6) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_getsockname_row (socket_call_in 204 7) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_getsockname_row (socket_call_in 204 8) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_getsockname_row (socket_call_in 204 0) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_getsockname_row (socket_call_in 204 0) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_getsockname_row (socket_call_in 204 3) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_getsockname_row (socket_call_in 204 3) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_getsockname_row (socket_call_in 204 4) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_getsockname_row (socket_call_in 204 4) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_getsockname_row (socket_call_in 204 5) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_getsockname_row (socket_call_in 204 5) (mkEffect 0 [] []) socket_call_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The 205 column of the same.
kernel: net/socket.c:__sys_getpeername,sock_from_file@v6.18.46 -/
theorem check_getpeername_declines_every_non_socket_fd_kind :
    check_getpeername_row (socket_call_in 205 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_getpeername_row (socket_call_in 205 3) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_getpeername_row (socket_call_in 205 4) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_getpeername_row (socket_call_in 205 5) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_getpeername_row (socket_call_in 205 6) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_getpeername_row (socket_call_in 205 7) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_getpeername_row (socket_call_in 205 8) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_getpeername_row (socket_call_in 205 0) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_getpeername_row (socket_call_in 205 0) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_getpeername_row (socket_call_in 205 3) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_getpeername_row (socket_call_in 205 3) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_getpeername_row (socket_call_in 205 4) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_getpeername_row (socket_call_in 205 4) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_getpeername_row (socket_call_in 205 5) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_getpeername_row (socket_call_in 205 5) (mkEffect 0 [] []) socket_call_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The 210 column of the same, with a `how` of 999 in a1 that would be
-EINVAL on a socket and is not reached.
kernel: net/socket.c:__sys_shutdown,sock_from_file@v6.18.46 -/
theorem check_shutdown_declines_every_non_socket_fd_kind :
    check_shutdown_row (socket_call_in 210 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_shutdown_row (socket_call_in 210 3) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_shutdown_row (socket_call_in 210 4) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_shutdown_row (socket_call_in 210 5) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_shutdown_row (socket_call_in 210 6) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_shutdown_row (socket_call_in 210 7) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_shutdown_row (socket_call_in 210 8) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_shutdown_row (socket_call_in 210 0) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_shutdown_row (socket_call_in 210 0) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_shutdown_row (socket_call_in 210 3) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_shutdown_row (socket_call_in 210 3) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_shutdown_row (socket_call_in 210 4) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_shutdown_row (socket_call_in 210 4) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_shutdown_row (socket_call_in 210 5) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_shutdown_row (socket_call_in 210 5) (mkEffect 0 [] []) socket_call_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `socket_calls_unknown_level_never_beats_the_fd`, for 204, 205
and 210: a closed descriptor is -EBADF and a live file is -ENOTSOCK
whatever sits in a1 and a3, and the errno of each call's own next gate —
`move_addr_to_user`'s -EFAULT on the two address calls, `inet_shutdown`'s
-EINVAL on a `how` of 999 — is refused, because that gate sits behind the
lookup.
kernel: net/socket.c:__sys_getsockname,__sys_getpeername,__sys_shutdown,move_addr_to_user; net/ipv4/af_inet.c:inet_shutdown@v6.18.46 -/
theorem check_socket_calls_fd_first_on_a_closed_and_a_live_descriptor :
    check_getsockname_row (socket_call_in 204 9) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_getpeername_row (socket_call_in 205 9) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_shutdown_row (socket_call_in 210 9) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_getsockname_row (socket_call_in 204 3) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_getpeername_row (socket_call_in 205 3) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_shutdown_row (socket_call_in 210 3) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_getsockname_row (socket_call_in 204 3) (mkEffect (errno_ret EFAULT) [] [])
      socket_call_model = CheckReject ∧
    check_getpeername_row (socket_call_in 205 3) (mkEffect (errno_ret EFAULT) [] [])
      socket_call_model = CheckReject ∧
    check_shutdown_row (socket_call_in 210 3) (mkEffect (errno_ret EINVAL) [] [])
      socket_call_model = CheckReject ∧
    check_getsockname_row (socket_call_in 204 9) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckReject ∧
    check_shutdown_row (socket_call_in 210 9) (mkEffect (errno_ret EINVAL) [] [])
      socket_call_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `socket_calls_null_pointers_never_beat_the_fd`, the 204 and 205
cells: NULL address and length pointers on a live file are -ENOTSOCK, and
the -EFAULT `move_addr_to_user` would give them is refused.
kernel: net/socket.c:__sys_getsockname,__sys_getpeername,move_addr_to_user@v6.18.46 -/
theorem check_socket_calls_null_pointers_never_beat_the_fd :
    check_getsockname_row (socket_call_null_in 204) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_getpeername_row (socket_call_null_in 205) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_getsockname_row (socket_call_null_in 204) (mkEffect (errno_ret EFAULT) [] [])
      socket_call_model = CheckReject ∧
    check_getpeername_row (socket_call_null_in 205) (mkEffect (errno_ret EFAULT) [] [])
      socket_call_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `getpeername_enotconn_covers_reset_but_not_close_wait`:
`inet_getname` with `peer` set answers -ENOTCONN when `!inet->inet_dport`
or the state is TCP_CLOSE or SYN_SENT — the fresh, bound and listening
sockets have no `inet_dport`, and the reset socket is TCP_CLOSE — while
the connected socket (fd 9), whose peer the kernel would report, is
declined, since the model would have to name the sixteen bytes
`move_addr_to_user` writes.
kernel: net/ipv4/af_inet.c:inet_getname@v6.18.46 -/
theorem check_getpeername_enotconn_covers_reset_but_not_close_wait :
    check_getpeername_row (getpeername_in 6) (mkEffect (errno_ret ENOTCONN) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_getpeername_row (getpeername_in 7) (mkEffect (errno_ret ENOTCONN) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_getpeername_row (getpeername_in 8) (mkEffect (errno_ret ENOTCONN) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_getpeername_row (getpeername_in 10) (mkEffect (errno_ret ENOTCONN) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_getpeername_row (getpeername_in 9) (mkEffect (errno_ret ENOTCONN) [] [])
      socket_states_model = CheckUnmodeled ∧
    check_getpeername_row (getpeername_in 9) (mkEffect 16 [] []) socket_states_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `getpeername_success_on_a_reset_socket_is_rejected`: the sixteen
bytes `move_addr_to_user` would have reported are inadmissible on a
socket `inet_getname` answers -ENOTCONN for — the reset one, and the
bound and listening ones, which have no `inet_dport` — and so is a 0
there; -EINVAL, which no line of `inet_getname` produces, likewise.
kernel: net/ipv4/af_inet.c:inet_getname@v6.18.46 -/
theorem check_getpeername_success_on_a_reset_socket_is_rejected :
    check_getpeername_row (getpeername_in 10) (mkEffect 16 [] []) socket_states_model
      = CheckReject ∧
    check_getpeername_row (getpeername_in 6) (mkEffect 0 [] []) socket_states_model
      = CheckReject ∧
    check_getpeername_row (getpeername_in 7) (mkEffect 16 [] []) socket_states_model
      = CheckReject ∧
    check_getpeername_row (getpeername_in 8) (mkEffect 0 [] []) socket_states_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `getsockname_declines_on_every_socket_state`: `inet_getname` with
`peer = 0` has no error return, and the address it reports carries a
port `inet_csk_find_open_port` drew at random on every state past
`SkFresh`, and a zero the model could report on `SkFresh` but does not —
the whole call is declined on every socket state, the sixteen bytes as
much as the -EFAULT `move_addr_to_user` answers for an unwritable
destination.
kernel: net/ipv4/af_inet.c:inet_getname; net/ipv4/inet_connection_sock.c:inet_csk_find_open_port; net/socket.c:__sys_getsockname,move_addr_to_user@v6.18.46 -/
theorem check_getsockname_declines_on_every_socket_state :
    check_getsockname_row (getsockname_in 6) (mkEffect 16 [] []) socket_states_model
      = CheckUnmodeled ∧
    check_getsockname_row (getsockname_in 7) (mkEffect 16 [] []) socket_states_model
      = CheckUnmodeled ∧
    check_getsockname_row (getsockname_in 8) (mkEffect 16 [] []) socket_states_model
      = CheckUnmodeled ∧
    check_getsockname_row (getsockname_in 9) (mkEffect 16 [] []) socket_states_model
      = CheckUnmodeled ∧
    check_getsockname_row (getsockname_in 10) (mkEffect 16 [] []) socket_states_model
      = CheckUnmodeled ∧
    check_getsockname_row (getsockname_in 6) (mkEffect (errno_ret EFAULT) [] [])
      socket_states_model = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The same decline on a second offered answer, the -EFAULT
`move_addr_to_user` gives an unwritable destination, on the bound,
listening, connected and reset sockets — the fresh one has it above.
kernel: net/socket.c:__sys_getsockname,move_addr_to_user; net/ipv4/af_inet.c:inet_getname@v6.18.46 -/
theorem check_getsockname_declines_hold_on_a_second_answer :
    check_getsockname_row (getsockname_in 7) (mkEffect (errno_ret EFAULT) [] [])
      socket_states_model = CheckUnmodeled ∧
    check_getsockname_row (getsockname_in 8) (mkEffect (errno_ret EFAULT) [] [])
      socket_states_model = CheckUnmodeled ∧
    check_getsockname_row (getsockname_in 9) (mkEffect (errno_ret EFAULT) [] [])
      socket_states_model = CheckUnmodeled ∧
    check_getsockname_row (getsockname_in 10) (mkEffect (errno_ret EFAULT) [] [])
      socket_states_model = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `shutdown_rejects_a_bad_how_on_every_socket_state`: `inet_shutdown`
increments `how` and tests `(how & ~SHUTDOWN_MASK) || !how`, so 3, 99,
-1 and INT_MAX are -EINVAL on every socket state, before the state
switch; 2^64-1 reaches it as the `int` -1.
kernel: net/ipv4/af_inet.c:inet_shutdown@v6.18.46 -/
theorem check_shutdown_rejects_a_bad_how_on_every_socket_state :
    (check_shutdown_row (shutdown_in 6 3) (mkEffect (errno_ret EINVAL) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
     check_shutdown_row (shutdown_in 6 99) (mkEffect (errno_ret EINVAL) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
     check_shutdown_row (shutdown_in 6 (Z_to_bv 64 (2 ^ 64 - 1))) (mkEffect (errno_ret EINVAL) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
     check_shutdown_row (shutdown_in 6 (Z_to_bv 64 (2 ^ 31 - 1))) (mkEffect (errno_ret EINVAL) [] [])
      socket_states_model = CheckOk socket_states_model []) ∧
    (check_shutdown_row (shutdown_in 7 3) (mkEffect (errno_ret EINVAL) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
     check_shutdown_row (shutdown_in 7 99) (mkEffect (errno_ret EINVAL) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
     check_shutdown_row (shutdown_in 7 (Z_to_bv 64 (2 ^ 64 - 1))) (mkEffect (errno_ret EINVAL) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
     check_shutdown_row (shutdown_in 7 (Z_to_bv 64 (2 ^ 31 - 1))) (mkEffect (errno_ret EINVAL) [] [])
      socket_states_model = CheckOk socket_states_model []) ∧
    (check_shutdown_row (shutdown_in 8 3) (mkEffect (errno_ret EINVAL) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
     check_shutdown_row (shutdown_in 8 99) (mkEffect (errno_ret EINVAL) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
     check_shutdown_row (shutdown_in 8 (Z_to_bv 64 (2 ^ 64 - 1))) (mkEffect (errno_ret EINVAL) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
     check_shutdown_row (shutdown_in 8 (Z_to_bv 64 (2 ^ 31 - 1))) (mkEffect (errno_ret EINVAL) [] [])
      socket_states_model = CheckOk socket_states_model []) ∧
    (check_shutdown_row (shutdown_in 9 3) (mkEffect (errno_ret EINVAL) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
     check_shutdown_row (shutdown_in 9 99) (mkEffect (errno_ret EINVAL) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
     check_shutdown_row (shutdown_in 9 (Z_to_bv 64 (2 ^ 64 - 1))) (mkEffect (errno_ret EINVAL) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
     check_shutdown_row (shutdown_in 9 (Z_to_bv 64 (2 ^ 31 - 1))) (mkEffect (errno_ret EINVAL) [] [])
      socket_states_model = CheckOk socket_states_model []) ∧
    (check_shutdown_row (shutdown_in 10 3) (mkEffect (errno_ret EINVAL) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
     check_shutdown_row (shutdown_in 10 99) (mkEffect (errno_ret EINVAL) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
     check_shutdown_row (shutdown_in 10 (Z_to_bv 64 (2 ^ 64 - 1))) (mkEffect (errno_ret EINVAL) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
     check_shutdown_row (shutdown_in 10 (Z_to_bv 64 (2 ^ 31 - 1))) (mkEffect (errno_ret EINVAL) [] [])
      socket_states_model = CheckOk socket_states_model []) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
    <;> check_norm

/-- Rocq's `shut_wr_on_a_listener_is_zero_and_a_no_op`: `inet_shutdown`'s
`case TCP_LISTEN:` arm is `if (!(how & RCV_SHUTDOWN)) break;`, and for
SHUT_WR the incremented `how` is 2, so the `break` fires and the
`default:` arm never runs — 0, and the model comes back identical.
-ENOTCONN and -EINVAL are lies here.
kernel: net/ipv4/af_inet.c:inet_shutdown@v6.18.46 -/
theorem check_shut_wr_on_a_listener_is_zero_and_a_no_op :
    check_shutdown_row (shutdown_in 8 1) (mkEffect 0 [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_shutdown_row (shutdown_in 8 1) (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model
      = CheckReject ∧
    check_shutdown_row (shutdown_in 8 1) (mkEffect (errno_ret EINVAL) [] []) socket_states_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- `how` reaches `__sys_shutdown` as an `int`: 2^32+1 is SHUT_WR, so on the
listener it is the same 0, and the -EINVAL a 64-bit reading would give is
refused.
kernel: net/socket.c:__sys_shutdown; net/ipv4/af_inet.c:inet_shutdown@v6.18.46 -/
theorem check_shutdown_how_high_half_is_discarded :
    check_shutdown_row (shutdown_in 8 (Z_to_bv 64 (2 ^ 32 + 1))) (mkEffect 0 [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_shutdown_row (shutdown_in 8 (Z_to_bv 64 (2 ^ 32 + 1))) (mkEffect (errno_ret EINVAL) [] [])
      socket_states_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- The narrowing in the other direction: 2^32+3 is `how` 3, outside
`SHUT_RD..SHUT_RDWR`, so the listener answers `inet_shutdown`'s -EINVAL
(net/ipv4/af_inet.c:896, :899-900, Linux v6.18.46) where 2^32+1 answered 0;
and 2^32 is SHUT_RD, which on a listener falls through `case TCP_LISTEN`
(:927-930) into `tcp_disconnect` (:931-933) — declined on either answer.
kernel: net/ipv4/af_inet.c:inet_shutdown@v6.18.46 -/
theorem check_shutdown_how_high_half_selects_the_low_arm :
    check_shutdown_row (shutdown_in 8 (Z_to_bv 64 (2 ^ 32 + 3))) (mkEffect (errno_ret EINVAL) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_shutdown_row (shutdown_in 8 (Z_to_bv 64 (2 ^ 32 + 3))) (mkEffect 0 [] [])
      socket_states_model = CheckReject ∧
    check_shutdown_row (shutdown_in 8 (Z_to_bv 64 (2 ^ 32))) (mkEffect 0 [] [])
      socket_states_model = CheckUnmodeled ∧
    check_shutdown_row (shutdown_in 8 (Z_to_bv 64 (2 ^ 32))) (mkEffect (errno_ret EINVAL) [] [])
      socket_states_model = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `shutdown_declines_where_it_would_have_to_drop_the_bits`:
`inet_shutdown`'s `case TCP_CLOSE:` sets `err = -ENOTCONN` and then FALLS
THROUGH into `default:`, ORing the bits into `sk_shutdown` anyway, and
`tcp_recvmsg_locked` tests `RCV_SHUTDOWN` before its TCP_CLOSE arm — so
the errno is right and the successor state is not, and `SockState` has
nowhere to put the bits.  Every well-formed `how` on the fresh, bound,
connected and reset sockets is declined, and so are SHUT_RD and
SHUT_RDWR on the listener, which fall through `case TCP_LISTEN`
(:927-930) into `tcp_disconnect` (:931-933).  The two answers
that survive follow, so the declines read as a boundary and not as
shutdown having gone quiet.
kernel: net/ipv4/af_inet.c:inet_shutdown; net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem check_shutdown_declines_where_it_would_have_to_drop_the_bits :
    (check_shutdown_row (shutdown_in 6 0) (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model
      = CheckUnmodeled ∧
     check_shutdown_row (shutdown_in 6 1) (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model
      = CheckUnmodeled ∧
     check_shutdown_row (shutdown_in 6 2) (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model
      = CheckUnmodeled) ∧
    (check_shutdown_row (shutdown_in 7 0) (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model
      = CheckUnmodeled ∧
     check_shutdown_row (shutdown_in 7 1) (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model
      = CheckUnmodeled ∧
     check_shutdown_row (shutdown_in 7 2) (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model
      = CheckUnmodeled) ∧
    (check_shutdown_row (shutdown_in 9 0) (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model
      = CheckUnmodeled ∧
     check_shutdown_row (shutdown_in 9 1) (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model
      = CheckUnmodeled ∧
     check_shutdown_row (shutdown_in 9 2) (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model
      = CheckUnmodeled) ∧
    (check_shutdown_row (shutdown_in 10 0) (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model
      = CheckUnmodeled ∧
     check_shutdown_row (shutdown_in 10 1) (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model
      = CheckUnmodeled ∧
     check_shutdown_row (shutdown_in 10 2) (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model
      = CheckUnmodeled) ∧
    (check_shutdown_row (shutdown_in 8 0) (mkEffect 0 [] []) socket_states_model
      = CheckUnmodeled ∧
     check_shutdown_row (shutdown_in 8 2) (mkEffect 0 [] []) socket_states_model
      = CheckUnmodeled) ∧
    (check_shutdown_row (shutdown_in 6 3) (mkEffect (errno_ret EINVAL) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
     check_shutdown_row (shutdown_in 8 1) (mkEffect 0 [] []) socket_states_model
      = CheckOk socket_states_model []) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    <;> check_norm

/-- The shutdown declines on a second offered answer: the fresh, bound,
connected and reset sockets decline the 0 and the -EINVAL `inet_shutdown`
would not give them as they decline its -ENOTCONN, and the listener's
SHUT_RD and SHUT_RDWR — the arms that fall through to `tcp_disconnect` —
decline -ENOTCONN and -EINVAL as they decline the 0 they really return;
the `how` of 2^32, SHUT_RD once narrowed, declines -EINVAL as it declines
0.
kernel: net/ipv4/af_inet.c:inet_shutdown; net/ipv4/tcp.c:tcp_disconnect@v6.18.46 -/
theorem check_shutdown_declines_hold_on_a_second_answer :
    check_shutdown_row (shutdown_in 6 0) (mkEffect 0 [] []) socket_states_model
      = CheckUnmodeled ∧
    check_shutdown_row (shutdown_in 7 1) (mkEffect 0 [] []) socket_states_model
      = CheckUnmodeled ∧
    check_shutdown_row (shutdown_in 9 2) (mkEffect 0 [] []) socket_states_model
      = CheckUnmodeled ∧
    check_shutdown_row (shutdown_in 10 0) (mkEffect (errno_ret EINVAL) [] []) socket_states_model
      = CheckUnmodeled ∧
    check_shutdown_row (shutdown_in 8 0) (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model
      = CheckUnmodeled ∧
    check_shutdown_row (shutdown_in 8 2) (mkEffect (errno_ret EINVAL) [] []) socket_states_model
      = CheckUnmodeled ∧
    check_shutdown_row (shutdown_in 8 (Z_to_bv 64 (2 ^ 32))) (mkEffect (errno_ret EINVAL) [] [])
      socket_states_model = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The descriptor reaches every one of these calls as an `int`: 2^32+3 is
fd 3 on each row, so bind on the fresh socket, connect on the listener,
listen on the bound socket, getpeername on the fresh `socket_states_model`
socket at 2^32+6, getsockname there, and shutdown on the listener at
2^32+8 all answer as their low word does — and the -EBADF a 64-bit reading
would give is refused on each.
kernel: net/socket.c:__sys_bind,__sys_connect,__sys_listen,__sys_getsockname,__sys_getpeername,__sys_shutdown; net/ipv4/af_inet.c:inet_getname,__inet_stream_connect,__inet_listen_sk@v6.18.46 -/
theorem check_rows_narrow_the_descriptor_to_its_low_word :
    check_bind_row (bind_in (Z_to_bv 64 (2 ^ 32 + 3)) 4096 16 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 16)]) fresh_socket_model
      = CheckOk (fixture_of (fds := [ (3, .FdSocket .SkBound), (0, .FdChannel 0),
                                      (1, .FdChannel 1), (2, .FdChannel 2) ])) [] ∧
    connect_answering_c connect_addr_mem listening_socket_model (Z_to_bv 64 (2 ^ 32 + 3)) 8192 16 16
      (errno_ret EISCONN) = CheckOk listening_socket_model [] ∧
    check_listen_row (listen_in (Z_to_bv 64 (2 ^ 32 + 3)) 128) (mkEffect 0 [] []) bound_socket_model
      = CheckOk (fixture_of (fds := [ (3, .FdSocket .SkListening), (0, .FdChannel 0),
                                      (1, .FdChannel 1), (2, .FdChannel 2) ])) [] ∧
    check_getpeername_row (getpeername_in (Z_to_bv 64 (2 ^ 32 + 6))) (mkEffect (errno_ret ENOTCONN) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_getsockname_row (getsockname_in (Z_to_bv 64 (2 ^ 32 + 6))) (mkEffect 16 [] [])
      socket_states_model = CheckUnmodeled ∧
    check_shutdown_row (shutdown_in (Z_to_bv 64 (2 ^ 32 + 8)) 1) (mkEffect 0 [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_bind_row (bind_in (Z_to_bv 64 (2 ^ 32 + 3)) 4096 16 sockaddr_in_any_mem)
      (mkEffect (errno_ret EBADF) [] []) fresh_socket_model = CheckReject ∧
    connect_answering connect_addr_mem listening_socket_model (Z_to_bv 64 (2 ^ 32 + 3)) 8192 16
      (errno_ret EBADF) = CheckReject ∧
    check_listen_row (listen_in (Z_to_bv 64 (2 ^ 32 + 3)) 128) (mkEffect (errno_ret EBADF) [] [])
      bound_socket_model = CheckReject ∧
    check_getpeername_row (getpeername_in (Z_to_bv 64 (2 ^ 32 + 6))) (mkEffect (errno_ret EBADF) [] [])
      socket_states_model = CheckReject ∧
    check_shutdown_row (shutdown_in (Z_to_bv 64 (2 ^ 32 + 8)) 1) (mkEffect (errno_ret EBADF) [] [])
      socket_states_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The errno half of six answering arms, each refused ALONE — the effect
offered is right in every other respect, so only the return can be what
the checker refuses: bind at length 0 is not -EFAULT (nothing was copied
to fault); bind over an unreadable address is not -EINVAL (the copy fails
before `inet_bind_sk`'s length gate); bind at 8 bytes with the 8 bytes
ledgered is not -EFAULT; connect on a closed descriptor is neither
-ENOTSOCK nor 0; the AF_UNSPEC disconnect on a fresh socket, ledgered, is
not -EINVAL.  AF_INET STREAM socketpair cannot return -EOPNOTSUPP with only
the first descriptor written: Linux stores both before that error
(net/socket.c `__sys_socketpair`, v6.18.46), while QEMU 11.1.1
linux-user/syscall.c `do_socketpair` (:3618-3633) copies neither on error.
kernel: net/socket.c:__sys_bind,move_addr_to_kernel,__sys_connect,__sys_socketpair; net/ipv4/af_inet.c:inet_bind_sk,__inet_stream_connect; net/core/sock.c:sock_no_socketpair@v6.18.46 -/
theorem check_errno_lies_are_refused_alone :
    bind_answering_at fresh_socket_model 4096 0 (errno_ret EFAULT) [] = CheckReject ∧
    check_bind_row (bind_in 3 4096 16 (fun _ => none)) (mkEffect (errno_ret EINVAL) [] [])
      fresh_socket_model = CheckReject ∧
    bind_answering_at fresh_socket_model 4096 8 (errno_ret EFAULT) [(4096, 8)] = CheckReject ∧
    connect_answering (fun _ => none) listening_socket_model 9 8192 16 (errno_ret ENOTSOCK)
      = CheckReject ∧
    connect_answering (fun _ => none) listening_socket_model 9 8192 16 0 = CheckReject ∧
    connect_answering_c connect_unspec_mem fresh_socket_model 3 8192 2 2 (errno_ret EINVAL)
      = CheckReject ∧
    check_socketpair_row (socketpair_in 2 1 0 4096 wmem_open)
      (mkEffect (errno_ret EOPNOTSUPP) [(4096, [3, 0, 0, 0])] []) socketpair_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The lifecycle calls write, zero and unmap nothing, and socketpair reads
no user memory: a byte written or a range zeroed beside bind's 0 or its
-EADDRINUSE, a range unmapped or a byte written beside listen's 0, a range
zeroed beside socketpair's two stores, and a copy-in ledgered on
socketpair's bare -EMFILE are each refused.  The acceptors match the
effect's five other fields empty; this is the pin that fails if one is
made a wildcard.
kernel: net/socket.c:__sys_bind,__sys_listen_socket,__sys_socketpair; net/ipv4/inet_connection_sock.c:inet_csk_get_port; fs/file.c:alloc_fd; net/core/sock.c:sock_no_socketpair@v6.18.46 -/
theorem check_lifecycle_effects_carry_nothing_else :
    check_bind_row (bind_in 3 4096 16 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU 0 [(4096, [0])] [] [] [] [(4096, 16)]) fresh_socket_model
      = CheckReject ∧
    check_bind_row (bind_in 3 4096 16 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EADDRINUSE) [] [(4096, 16)] [] [] [(4096, 16)])
      fresh_socket_model = CheckReject ∧
    check_listen_row (listen_in 3 128) (SyscallEffect.mkEffectU 0 [] [] [(4096, 4096)] [] [])
      bound_socket_model = CheckReject ∧
    check_listen_row (listen_in 3 128) (SyscallEffect.mkEffectU 0 [(4096, [0])] [] [] [] [])
      fresh_socket_model = CheckReject ∧
    check_socketpair_row (socketpair_in 2 1 0 4096 wmem_open)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])]
        [(4104, 4)] [] [] []) socketpair_model = CheckReject ∧
    check_socketpair_row (socketpair_in 2 1 0 4096 wmem_open)
      (SyscallEffect.mkEffectU (errno_ret EMFILE) [] [] [] [] [(4096, 8)]) socketpair_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Boundaries of the descriptor and the length on the kernel's own types,
each decided by the rows and pinned here for the first time.  A descriptor
of 2^32-1 is the `int` -1 on every row — `fd_empty`, -EBADF — and 2^63 is
the `int` 0, the channel, -ENOTSOCK on bind.  A bind length of 1, 2 or 15
is copied and then -EINVAL at `inet_bind_sk`'s gate with exactly that many
bytes ledgered; 17 and 127 over a 128-byte address bind with that many
ledgered (`inet_bind_sk` demands sixteen, and `__inet_bind` reads
`sin_family`, `sin_port` and `sin_addr` from them); 17 over the 16-byte
address is the copy faulting, -EFAULT bare; 2^31-1 and 2^31 — INT_MAX and
INT_MIN once narrowed — are -EINVAL uncopied alike, and 2^32 and 2^63 are
the `int` 0.
kernel: net/socket.c:__sys_bind,__sys_connect,__sys_listen,__sys_getsockname,__sys_getpeername,__sys_shutdown,move_addr_to_kernel; net/ipv4/af_inet.c:inet_bind_sk,__inet_bind@v6.18.46 -/
theorem check_descriptor_and_length_boundaries :
    check_bind_row (bind_in (Z_to_bv 64 (2 ^ 32 - 1)) 4096 16 sockaddr_in_any_mem)
      (mkEffect (errno_ret EBADF) [] []) fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_listen_row (listen_in (Z_to_bv 64 (2 ^ 32 - 1)) 128) (mkEffect (errno_ret EBADF) [] [])
      bound_socket_model = CheckOk bound_socket_model [] ∧
    connect_answering (fun _ => none) listening_socket_model (Z_to_bv 64 (2 ^ 32 - 1)) 8192 16
      (errno_ret EBADF) = CheckOk listening_socket_model [] ∧
    check_getsockname_row (socket_call_in 204 (Z_to_bv 64 (2 ^ 32 - 1)))
      (mkEffect (errno_ret EBADF) [] []) socket_call_model = CheckOk socket_call_model [] ∧
    check_getpeername_row (socket_call_in 205 (Z_to_bv 64 (2 ^ 32 - 1)))
      (mkEffect (errno_ret EBADF) [] []) socket_call_model = CheckOk socket_call_model [] ∧
    check_shutdown_row (socket_call_in 210 (Z_to_bv 64 (2 ^ 32 - 1)))
      (mkEffect (errno_ret EBADF) [] []) socket_call_model = CheckOk socket_call_model [] ∧
    check_bind_row (bind_in (Z_to_bv 64 (2 ^ 63)) 4096 16 sockaddr_in_any_mem)
      (mkEffect (errno_ret ENOTSOCK) [] []) fresh_socket_model = CheckOk fresh_socket_model [] ∧
    bind_answering_at fresh_socket_model 4096 1 (errno_ret EINVAL) [(4096, 1)]
      = CheckOk fresh_socket_model [] ∧
    bind_answering_at fresh_socket_model 4096 2 (errno_ret EINVAL) [(4096, 2)]
      = CheckOk fresh_socket_model [] ∧
    bind_answering_at fresh_socket_model 4096 15 (errno_ret EINVAL) [(4096, 15)]
      = CheckOk fresh_socket_model [] ∧
    check_bind_row (bind_in 3 4096 17 sockaddr_in_any_mem128)
      (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 17)]) fresh_socket_model
      = CheckOk (with_fds (fd_insert (m_fds fresh_socket_model) 3 (.FdSocket .SkBound))
                          fresh_socket_model) [] ∧
    check_bind_row (bind_in 3 4096 127 sockaddr_in_any_mem128)
      (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 127)]) fresh_socket_model
      = CheckOk (with_fds (fd_insert (m_fds fresh_socket_model) 3 (.FdSocket .SkBound))
                          fresh_socket_model) [] ∧
    bind_answering_at fresh_socket_model 4096 17 (errno_ret EFAULT) []
      = CheckOk fresh_socket_model [] ∧
    bind_answering_at fresh_socket_model 4096 (Z_to_bv 64 (2 ^ 31 - 1)) (errno_ret EINVAL) []
      = CheckOk fresh_socket_model [] ∧
    bind_answering_at fresh_socket_model 4096 (Z_to_bv 64 (2 ^ 31)) (errno_ret EINVAL) []
      = CheckOk fresh_socket_model [] ∧
    bind_answering_at fresh_socket_model 4096 (Z_to_bv 64 (2 ^ 32)) (errno_ret EINVAL) []
      = CheckOk fresh_socket_model [] ∧
    bind_answering_at fresh_socket_model 4096 (Z_to_bv 64 (2 ^ 63)) (errno_ret EINVAL) []
      = CheckOk fresh_socket_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Boundaries of shutdown's `how` and socketpair's arguments on the
kernel's types: a `how` of 2^31 is INT_MIN, whose increment `inet_shutdown`
masks to a nonzero value — -EINVAL, like INT_MAX; a type of 16, the bit
above `SOCK_TYPE_MASK`, is -EINVAL bare before any reservation; a type of
2^32+1 with a protocol of 2^32 is the `int` pair (1, 0), the modeled
triple; a destination of 2^64-8 fails the first store's `access_ok` —
-EFAULT bare; and an unaligned destination stores the two `int`s at `sv`
and `sv + 4`, `access_ok` having no alignment test.
kernel: net/ipv4/af_inet.c:inet_shutdown; net/socket.c:__sys_socketpair; net/core/sock.c:sock_no_socketpair; include/asm-generic/access_ok.h:__access_ok; arch/riscv/include/asm/uaccess.h:put_user@v6.18.46 -/
theorem check_how_and_socketpair_boundaries :
    check_shutdown_row (shutdown_in 8 (Z_to_bv 64 (2 ^ 31))) (mkEffect (errno_ret EINVAL) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_socketpair_row (socketpair_in 2 16 0 4096 wmem_open)
      (mkEffect (errno_ret EINVAL) [] []) socketpair_model = CheckOk socketpair_model [] ∧
    check_socketpair_row (socketpair_in 2 (Z_to_bv 64 (2 ^ 32 + 1)) (Z_to_bv 64 (2 ^ 32)) 4096
        wmem_open)
      (mkEffect (errno_ret EOPNOTSUPP) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
      socketpair_model = CheckOk socketpair_model [] ∧
    check_socketpair_row (socketpair_in 2 1 0 (Z_to_bv 64 (2 ^ 64 - 8)) wmem_open)
      (mkEffect (errno_ret EFAULT) [] []) socketpair_model = CheckOk socketpair_model [] ∧
    check_socketpair_row (socketpair_in 2 1 0 4097 wmem_open)
      (mkEffect (errno_ret EOPNOTSUPP) [(4097, [3, 0, 0, 0]), (4101, [4, 0, 0, 0])] [])
      socketpair_model = CheckOk socketpair_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-! ## socketpair

`__sys_socketpair` (net/socket.c:1769, Linux v6.18.46): the flag test →
-EINVAL before anything is reserved; two `get_unused_fd_flags` reservations,
each able to fail with -EMFILE or -ENOMEM before either `put_user`;
`put_user(fd1)` and `put_user(fd2)`, the first of which failing is -EFAULT
with nothing stored; then `sock_create` and `->socketpair`, which for every
AF_INET `proto_ops` is `sock_no_socketpair`'s -EOPNOTSUPP — with both
descriptors already written.  The spec models AF_INET SOCK_STREAM and
SOCK_DGRAM at protocol 0 and declines the rest.  The exhausted-table arm has
no fixture here, as the header says. -/

/-- Rocq's `socketpair_writes_the_descriptors_before_it_fails`: over a
fully writable destination, -EOPNOTSUPP carries the two 4-byte stores of
the descriptors the table hands out, 3 and 4; the same errno with nothing
written, the wrong descriptor numbers, and a success with the writes are
all lies.
kernel: net/socket.c:__sys_socketpair,__sock_create; net/core/sock.c:sock_no_socketpair; fs/file.c:alloc_fd,alloc_fdtable@v6.18.46 -/
theorem check_socketpair_writes_the_descriptors_before_it_fails :
    check_socketpair_row (socketpair_in 2 1 0 4096 wmem_open)
      (mkEffect (errno_ret EOPNOTSUPP) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
      socketpair_model = CheckOk socketpair_model [] ∧
    check_socketpair_row (socketpair_in 2 1 0 4096 wmem_open)
      (mkEffect (errno_ret EOPNOTSUPP) [] []) socketpair_model = CheckReject ∧
    check_socketpair_row (socketpair_in 2 1 0 4096 wmem_open)
      (mkEffect (errno_ret EOPNOTSUPP) [(4096, [4, 0, 0, 0]), (4100, [5, 0, 0, 0])] [])
      socketpair_model = CheckReject ∧
    check_socketpair_row (socketpair_in 2 1 0 4096 wmem_open)
      (mkEffect 0 [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] []) socketpair_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The two errno pools of the written arm: -EMFILE and -ENOMEM with
nothing written are the reservations failing (`alloc_fd` past
`RLIMIT_NOFILE`, `alloc_fdtable` out of memory), -ENFILE and -ENOMEM with
both writes are `__sock_create` and `sk_alloc` failing after the stores.
-EMFILE with the writes and -EFAULT over a writable destination are lies.
kernel: net/socket.c:__sys_socketpair,__sock_create; net/core/sock.c:sock_no_socketpair; fs/file.c:alloc_fd,alloc_fdtable; arch/riscv/include/asm/uaccess.h:put_user@v6.18.46 -/
theorem check_socketpair_errno_pools_split_at_the_writes :
    check_socketpair_row (socketpair_in 2 1 0 4096 wmem_open)
      (mkEffect (errno_ret EMFILE) [] []) socketpair_model = CheckOk socketpair_model [] ∧
    check_socketpair_row (socketpair_in 2 1 0 4096 wmem_open)
      (mkEffect (errno_ret ENOMEM) [] []) socketpair_model = CheckOk socketpair_model [] ∧
    check_socketpair_row (socketpair_in 2 1 0 4096 wmem_open)
      (mkEffect (errno_ret ENFILE) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
      socketpair_model = CheckOk socketpair_model [] ∧
    check_socketpair_row (socketpair_in 2 1 0 4096 wmem_open)
      (mkEffect (errno_ret ENOMEM) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
      socketpair_model = CheckOk socketpair_model [] ∧
    check_socketpair_row (socketpair_in 2 1 0 4096 wmem_open)
      (mkEffect (errno_ret EMFILE) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
      socketpair_model = CheckReject ∧
    check_socketpair_row (socketpair_in 2 1 0 4096 wmem_open)
      (mkEffect (errno_ret ENFILE) [] []) socketpair_model = CheckReject ∧
    check_socketpair_row (socketpair_in 2 1 0 4096 wmem_open)
      (mkEffect (errno_ret EFAULT) [] []) socketpair_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- SOCK_DGRAM, and SOCK_STREAM with SOCK_CLOEXEC and SOCK_NONBLOCK set, are
modeled triples too: `__sys_socketpair` masks the flags off before
`sock_create`, and the stream and datagram `proto_ops` tables of
net/ipv4/af_inet.c (:1055 and :1090 at v6.18.46) both carry
`sock_no_socketpair`.
kernel: net/socket.c:__sys_socketpair; net/core/sock.c:sock_no_socketpair@v6.18.46 -/
theorem check_socketpair_dgram_and_flagged_stream_are_modeled :
    check_socketpair_row (socketpair_in 2 2 0 4096 wmem_open)
      (mkEffect (errno_ret EOPNOTSUPP) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
      socketpair_model = CheckOk socketpair_model [] ∧
    check_socketpair_row (socketpair_in 2 (Z_to_bv 64 (1 + 524288 + 2048)) 0 4096 wmem_open)
      (mkEffect (errno_ret EOPNOTSUPP) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
      socketpair_model = CheckOk socketpair_model [] := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- Rocq's `socketpair_flag_check_precedes_the_writes`: the first gate
answers -EINVAL before anything is reserved, whatever the family.
`__sys_socketpair` tests the flag bits (net/socket.c:1771-1773, Linux
v6.18.46) before the two `get_unused_fd_flags` reservations, so AF_INET
and AF_UNIX at `SOCK_STREAM|0x100` are both -EINVAL with nothing
written, and the same errno carrying the two descriptor stores is
refused.  AF_UNIX at a legal type still declines: the family is outside
the model, and the flag gate has let it through.
kernel: net/socket.c:__sys_socketpair; net/core/sock.c:sock_no_socketpair@v6.18.46 -/
theorem check_socketpair_flag_check_precedes_the_writes :
    check_socketpair_row (socketpair_in 2 257 0 4096 wmem_open)
      (mkEffect (errno_ret EINVAL) [] []) socketpair_model = CheckOk socketpair_model [] ∧
    check_socketpair_row (socketpair_in 2 257 0 4096 wmem_open)
      (mkEffect (errno_ret EINVAL) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
      socketpair_model = CheckReject ∧
    check_socketpair_row (socketpair_in 1 257 0 4096 wmem_open)
      (mkEffect (errno_ret EINVAL) [] []) socketpair_model = CheckOk socketpair_model [] ∧
    check_socketpair_row (socketpair_in 1 1 0 4096 wmem_open)
      (mkEffect 0 [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] []) socketpair_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The triples outside the model decline whatever the answer: AF_INET
SOCK_RAW, AF_INET SOCK_STREAM at IPPROTO_TCP, and a family of 2^32+2,
which the spec narrows to AF_INET and so MODELS — the register reaches
`__sys_socketpair` as an `int`.
kernel: net/socket.c:__sys_socketpair,socketpair; net/core/sock.c:sock_no_socketpair; fs/file.c:alloc_fd@v6.18.46 -/
theorem check_socketpair_declines_the_unmodeled_triples :
    check_socketpair_row (socketpair_in 2 3 0 4096 wmem_open)
      (mkEffect (errno_ret EOPNOTSUPP) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
      socketpair_model = CheckUnmodeled ∧
    check_socketpair_row (socketpair_in 2 1 6 4096 wmem_open)
      (mkEffect (errno_ret EOPNOTSUPP) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
      socketpair_model = CheckUnmodeled ∧
    check_socketpair_row (socketpair_in 2 1 6 4096 wmem_open)
      (mkEffect (errno_ret EMFILE) [] []) socketpair_model = CheckUnmodeled ∧
    check_socketpair_row (socketpair_in (Z_to_bv 64 (2 ^ 32 + 2)) 1 0 4096 wmem_open)
      (mkEffect (errno_ret EOPNOTSUPP) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
      socketpair_model = CheckOk socketpair_model [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- Rocq's `socketpair_declines_the_partial_destination`: `sv = TASK_SIZE`
is refused at the first `put_user`'s own `access_ok`, so -EFAULT with
nothing written is the answer and a write there is refused; `sv =
TASK_SIZE - 5` is not — the first store's 4-byte range ends inside the
address space and the second's past it, a partial outcome the model does
not express — so it declines.  The reservation errnos are admitted at the
faulting destination too, since the reservations come first, and
-EOPNOTSUPP is not, since `sock_create` is never reached.
kernel: arch/riscv/include/asm/uaccess.h:put_user; include/asm-generic/access_ok.h:__access_ok; fs/file.c:alloc_fd,alloc_fdtable; net/socket.c:__sys_socketpair; net/core/sock.c:sock_no_socketpair@v6.18.46 -/
theorem check_socketpair_declines_the_partial_destination :
    check_socketpair_row (socketpair_in 2 1 0 140737488355328 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) socketpair_model = CheckOk socketpair_model [] ∧
    check_socketpair_row (socketpair_in 2 1 0 140737488355328 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [(140737488355328, [3, 0, 0, 0])] []) socketpair_model
      = CheckReject ∧
    check_socketpair_row (socketpair_in 2 1 0 140737488355323 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) socketpair_model = CheckUnmodeled ∧
    check_socketpair_row (socketpair_in 2 1 0 140737488355328 (fun _ => none))
      (mkEffect (errno_ret EMFILE) [] []) socketpair_model = CheckOk socketpair_model [] ∧
    check_socketpair_row (socketpair_in 2 1 0 140737488355328 (fun _ => none))
      (mkEffect (errno_ret EOPNOTSUPP) [] []) socketpair_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- An unmapped destination inside the address space declines: `access_ok`
passes both stores, and whether the page faults is the mapping's to say,
which `in_wmem` answers `none` for — so neither -EFAULT nor the writes
are admitted, and the call is `CheckUnmodeled`.
kernel: arch/riscv/include/asm/uaccess.h:put_user; include/asm-generic/access_ok.h:__access_ok; net/core/sock.c:sock_no_socketpair@v6.18.46 -/
theorem check_socketpair_unmapped_destination_declines :
    check_socketpair_row (socketpair_in 2 1 0 4096 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) socketpair_model = CheckUnmodeled ∧
    check_socketpair_row (socketpair_in 2 1 0 4096 (fun _ => none))
      (mkEffect (errno_ret EOPNOTSUPP) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
      socketpair_model = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- Rocq's `socketpair_wrapping_destination_is_efault`: a destination four
bytes below 2^64, over a memory that maps exactly its eight bytes, is
-EFAULT — the bare walk would pass, but `__access_ok` refuses a range
that wraps — and the two stores at `sv` and 0 are refused.
kernel: arch/riscv/include/asm/uaccess.h:put_user; include/asm-generic/access_ok.h:__access_ok; fs/file.c:alloc_fd,alloc_fdtable; net/core/sock.c:sock_no_socketpair@v6.18.46 -/
theorem check_socketpair_wrapping_destination_is_efault :
    check_socketpair_row (socketpair_in 2 1 0 socketpair_wrap_sv socketpair_wrap_mem)
      (mkEffect (errno_ret EFAULT) [] []) socketpair_model = CheckOk socketpair_model [] ∧
    check_socketpair_row (socketpair_in 2 1 0 socketpair_wrap_sv socketpair_wrap_mem)
      (mkEffect (errno_ret EOPNOTSUPP) [(socketpair_wrap_sv, [3, 0, 0, 0]), (0, [4, 0, 0, 0])] [])
      socketpair_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- Rocq's `socketpair_past_long_max_at_the_checker`: `sv = 2^63` with an
8-byte destination sums to 2^63 + 8, under 2^64, so the walk visits the
bytes and a bare no-wrap test would accept it; riscv64's `__access_ok`
tests `addr <= TASK_SIZE - size` and refuses it.
kernel: arch/riscv/include/asm/uaccess.h:put_user; include/asm-generic/access_ok.h:__access_ok; fs/file.c:alloc_fd,alloc_fdtable; net/core/sock.c:sock_no_socketpair@v6.18.46 -/
theorem check_socketpair_past_long_max_at_the_checker :
    check_socketpair_row (socketpair_in 2 1 0 (Z_to_bv 64 (2 ^ 63)) socketpair_high_mem)
      (mkEffect (errno_ret EFAULT) [] []) socketpair_model = CheckOk socketpair_model [] ∧
    check_socketpair_row (socketpair_in 2 1 0 (Z_to_bv 64 (2 ^ 63)) socketpair_high_mem)
      (mkEffect (errno_ret EOPNOTSUPP)
        [(Z_to_bv 64 (2 ^ 63), [3, 0, 0, 0]), (Z_to_bv 64 (2 ^ 63 + 4), [4, 0, 0, 0])] [])
      socketpair_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- Rocq's `socketpair_dest_width_is_eight`: three destinations a step apart
at the top of the address space, over `wmem_open` so only the `TASK_SIZE`
test separates them.  `TASK_SIZE - 8` is the last `sv` whose two stores
both pass: -EOPNOTSUPP with the writes, and -EFAULT the lie.  `TASK_SIZE -
7` passes the first store and fails the second: declined.  `TASK_SIZE - 3`
fails the first: -EFAULT.  A check written over 8 bytes for the fault
would answer -EFAULT for the middle one; this is the pin that fails if
the width is widened back.
kernel: arch/riscv/include/asm/uaccess.h:put_user; include/asm-generic/access_ok.h:__access_ok; fs/file.c:alloc_fd,alloc_fdtable; net/core/sock.c:sock_no_socketpair@v6.18.46 -/
theorem check_socketpair_dest_width_is_eight :
    check_socketpair_row (socketpair_in 2 1 0 140737488355320 wmem_open)
      (mkEffect (errno_ret EOPNOTSUPP)
        [(140737488355320, [3, 0, 0, 0]), (140737488355324, [4, 0, 0, 0])] [])
      socketpair_model = CheckOk socketpair_model [] ∧
    check_socketpair_row (socketpair_in 2 1 0 140737488355320 wmem_open)
      (mkEffect (errno_ret EFAULT) [] []) socketpair_model = CheckReject ∧
    check_socketpair_row (socketpair_in 2 1 0 140737488355321 wmem_open)
      (mkEffect (errno_ret EOPNOTSUPP)
        [(140737488355321, [3, 0, 0, 0]), (140737488355325, [4, 0, 0, 0])] [])
      socketpair_model = CheckUnmodeled ∧
    check_socketpair_row (socketpair_in 2 1 0 140737488355325 wmem_open)
      (mkEffect (errno_ret EFAULT) [] []) socketpair_model = CheckOk socketpair_model [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The exact edge of the first store: `sv = TASK_SIZE - 4` is the last `sv`
whose first 4-byte store `__access_ok` passes — `addr <= limit - size`
with equality — and the first whose second store it refuses, so it is
declined on both answers.  A first-store test written strict
(`sv < TASK_SIZE - 4`) would answer -EFAULT here and go red; `TASK_SIZE -
3`, the pin above, is the -EFAULT.
kernel: arch/riscv/include/asm/uaccess.h:put_user; include/asm-generic/access_ok.h:__access_ok; fs/file.c:alloc_fd,alloc_fdtable; net/core/sock.c:sock_no_socketpair@v6.18.46 -/
theorem check_socketpair_first_store_edge_is_inclusive :
    check_socketpair_row (socketpair_in 2 1 0 140737488355324 wmem_open)
      (mkEffect (errno_ret EFAULT) [] []) socketpair_model = CheckUnmodeled ∧
    check_socketpair_row (socketpair_in 2 1 0 140737488355324 wmem_open)
      (mkEffect (errno_ret EOPNOTSUPP)
        [(140737488355324, [3, 0, 0, 0]), (140737488355328, [4, 0, 0, 0])] [])
      socketpair_model = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- The socketpair declines on a second offered answer: AF_UNIX at a legal
type declines -EOPNOTSUPP with the stores and -EMFILE bare as it declines
the 0 it really returns; AF_INET SOCK_RAW declines -EMFILE bare and
-EINVAL bare as it declines -EOPNOTSUPP with the stores; the destinations
at `TASK_SIZE - 5` and `TASK_SIZE - 7`, whose second store alone is
refused, decline -EOPNOTSUPP with both stores and -EFAULT bare alike.
kernel: net/socket.c:__sys_socketpair; net/core/sock.c:sock_no_socketpair; fs/file.c:alloc_fd; arch/riscv/include/asm/uaccess.h:put_user@v6.18.46 -/
theorem check_socketpair_declines_hold_on_a_second_answer :
    check_socketpair_row (socketpair_in 1 1 0 4096 wmem_open)
      (mkEffect (errno_ret EOPNOTSUPP) [(4096, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] [])
      socketpair_model = CheckUnmodeled ∧
    check_socketpair_row (socketpair_in 1 1 0 4096 wmem_open)
      (mkEffect (errno_ret EMFILE) [] []) socketpair_model = CheckUnmodeled ∧
    check_socketpair_row (socketpair_in 2 3 0 4096 wmem_open)
      (mkEffect (errno_ret EMFILE) [] []) socketpair_model = CheckUnmodeled ∧
    check_socketpair_row (socketpair_in 2 3 0 4096 wmem_open)
      (mkEffect (errno_ret EINVAL) [] []) socketpair_model = CheckUnmodeled ∧
    check_socketpair_row (socketpair_in 2 1 0 140737488355323 (fun _ => none))
      (mkEffect (errno_ret EOPNOTSUPP)
        [(140737488355323, [3, 0, 0, 0]), (140737488355327, [4, 0, 0, 0])] [])
      socketpair_model = CheckUnmodeled ∧
    check_socketpair_row (socketpair_in 2 1 0 140737488355321 wmem_open)
      (mkEffect (errno_ret EFAULT) [] []) socketpair_model = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-! ## The witnesses

Each witness names one outcome its spec admits on the input, or `Unmodeled`
where the spec declines every outcome; `<name>_witness_ok` beside it says
the named outcome is admitted.  The pins below name the outcome each arm
picks, on the fixtures above, so that a witness rewritten to pick an
outcome the kernel does not produce — or to pick one where the spec
declines — fails here rather than in the registration's progress
theorem.  Each is a kernel claim like the checker pins: the outcome named
is one Linux produces on that input. -/

/-- Open the witnesses and the spec's readers, and decide what is closed. -/
scoped macro "witness_open" cfg:Lean.Parser.Tactic.optConfig : tactic =>
  `(tactic| simp $cfg:optConfig only [bind_witness, listen_witness, connect_witness,
      getsockname_witness, getpeername_witness, shutdown_witness, socketpair_witness,
      ret_outcome, outcome_copyins, with_copyins, sock_fd, shut_how_ok, socketpair_flags_ok,
      socketpair_modeled_b, socketpair_fds, socketpair_dest_writable,
      Bool.and_eq_true, Bool.or_eq_true, ne_eq, reduceCtorEq, sys_simp, ↓reduceIte])

/-- Evaluate a closed call of one of the lifecycle witnesses, the way
`check_norm` evaluates a checker. -/
scoped macro "witness_norm" : tactic =>
  `(tactic| (witness_open +decide;
             first | done | sys_simp_pass +ground +decide -failIfUnchanged;
             first | done | witness_open +ground +decide))

/-- bind's witness, arm by arm: -EBADF on a closed descriptor, -ENOTSOCK on
a file, -EINVAL on a length of 129, of 2^32-1 (-1 as an `int`) and of 0 and
-EADDRINUSE with the whole 128 bytes ledgered on a length of 128, -EFAULT
on an unreadable address, -EINVAL with the copy ledgered on 8 bytes and
on 15 — `inet_bind_sk`'s length test, before the family and the port —
-EAFNOSUPPORT on AF_UNIX and on AF_UNSPEC with an address that is not
INADDR_ANY, `Unmodeled` on a specific address and on a specific port,
-EADDRINUSE on the fresh socket, -EINVAL on the bound and the listening
one, `Unmodeled` on the reset and the accepted one.
kernel: net/socket.c:__sys_bind,move_addr_to_kernel; net/ipv4/af_inet.c:inet_bind_sk,__inet_bind; net/ipv4/inet_connection_sock.c:inet_csk_get_port@v6.18.46 -/
theorem bind_witness_names_each_arm :
    bind_witness 9 4096 16 (bind_in 9 4096 16 sockaddr_in_any_mem) fresh_socket_model
      = Ok (mkEffect (errno_ret EBADF) [] []) fresh_socket_model [] ∧
    bind_witness 3 4096 16 (bind_in 3 4096 16 sockaddr_in_any_mem) socket_call_model
      = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] ∧
    bind_witness 3 4096 129 (bind_in 3 4096 129 sockaddr_in_any_mem) fresh_socket_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) fresh_socket_model [] ∧
    bind_witness 3 4096 (Z_to_bv 64 (2 ^ 32 - 1))
      (bind_in 3 4096 (Z_to_bv 64 (2 ^ 32 - 1)) sockaddr_in_any_mem) fresh_socket_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) fresh_socket_model [] ∧
    bind_witness 3 4096 0 (bind_in 3 4096 0 sockaddr_in_any_mem) fresh_socket_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) fresh_socket_model [] ∧
    bind_witness 3 4096 128 (bind_in 3 4096 128 sockaddr_in_any_mem128) fresh_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EADDRINUSE) [] [] [] [] [(4096, 128)])
           fresh_socket_model [] ∧
    bind_witness 3 8192 16 (bind_in 3 8192 16 sockaddr_in_any_mem) fresh_socket_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model [] ∧
    bind_witness 3 4096 8 (bind_in 3 4096 8 sockaddr_in_any_mem) fresh_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 8)])
           fresh_socket_model [] ∧
    bind_witness 3 4096 15 (bind_in 3 4096 15 sockaddr_in_any_mem) fresh_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 15)])
           fresh_socket_model [] ∧
    bind_witness 3 4096 16 (bind_in 3 4096 16 sockaddr_unix_any_mem) fresh_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EAFNOSUPPORT) [] [] [] [] [(4096, 16)])
           fresh_socket_model [] ∧
    bind_witness 3 4096 16 (bind_in 3 4096 16 sockaddr_unspec_loopback_mem) fresh_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EAFNOSUPPORT) [] [] [] [] [(4096, 16)])
           fresh_socket_model [] ∧
    bind_witness 3 4096 16 (bind_in 3 4096 16 sockaddr_in_loopback_mem) fresh_socket_model
      = Unmodeled ∧
    bind_witness 3 4096 16 (bind_in 3 4096 16 sockaddr_in_port80_mem) fresh_socket_model
      = Unmodeled ∧
    bind_witness 3 4096 16 (bind_in 3 4096 16 sockaddr_in_any_mem) fresh_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EADDRINUSE) [] [] [] [] [(4096, 16)])
           fresh_socket_model [] ∧
    bind_witness 3 4096 16 (bind_in 3 4096 16 sockaddr_in_any_mem) bound_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 16)])
           bound_socket_model [] ∧
    bind_witness 3 4096 16 (bind_in 3 4096 16 sockaddr_in_any_mem) listening_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 16)])
           listening_socket_model [] ∧
    bind_witness 3 4096 16 (bind_in 3 4096 16 sockaddr_in_any_mem) reset_socket_model
      = Unmodeled ∧
    bind_witness 4 4096 16 (bind_in 4 4096 16 sockaddr_in_any_mem) accepted_socket_model
      = Unmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> witness_norm

/-- listen's witness: -EBADF, -ENOTSOCK, -EINVAL on the accepted and the
reset socket, 0 on the listener with the model kept, 0 on the bound
socket with the socket reseated as listening, -EADDRINUSE on the fresh
one — the errno rather than the success, so that the witness never has
to name a port.
kernel: net/socket.c:__sys_listen; net/ipv4/af_inet.c:inet_listen,__inet_listen_sk; net/ipv4/inet_connection_sock.c:inet_csk_listen_start,inet_csk_get_port@v6.18.46 -/
theorem listen_witness_names_each_arm :
    listen_witness 9 fresh_socket_model = Ok (mkEffect (errno_ret EBADF) [] []) fresh_socket_model [] ∧
    listen_witness 3 socket_call_model = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] ∧
    listen_witness 4 accepted_socket_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) accepted_socket_model [] ∧
    listen_witness 3 reset_socket_model = Ok (mkEffect (errno_ret EINVAL) [] []) reset_socket_model [] ∧
    listen_witness 3 listening_socket_model = Ok (mkEffect 0 [] []) listening_socket_model [] ∧
    listen_witness 3 bound_socket_model
      = Ok (mkEffect 0 [] [])
           (fixture_of (fds := [ (3, .FdSocket .SkListening), (0, .FdChannel 0),
                                 (1, .FdChannel 1), (2, .FdChannel 2) ])) [] ∧
    listen_witness 3 fresh_socket_model
      = Ok (mkEffect (errno_ret EADDRINUSE) [] []) fresh_socket_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> witness_norm

/-- connect's witness: -EBADF; -EINVAL on 129 and on 2^32-1 (-1 as an
`int`); -EFAULT on an unreadable address; -ENOTSOCK with the copy ledgered
on a channel, and bare on a channel with a length of 0; -EINVAL with one
byte ledgered on a length of 1 and with nothing ledgered on a length of 0;
0 on AF_UNSPEC over the fresh socket and `Unmodeled` over the listener;
-EISCONN on the listener, the accepted and the reset socket; -EINVAL on
4 bytes, on 15 and on 8 AF_UNIX bytes — `tcp_v4_connect`'s length test
before its family test — and -EAFNOSUPPORT on AF_UNIX over the fresh and
the bound socket; `Unmodeled` on the well-formed attempt.
kernel: net/socket.c:__sys_connect,__sys_connect_file,move_addr_to_kernel; net/ipv4/af_inet.c:__inet_stream_connect; net/ipv4/tcp_ipv4.c:tcp_v4_connect; net/ipv4/tcp.c:tcp_disconnect@v6.18.46 -/
theorem connect_witness_names_each_arm :
    connect_witness 9 8192 16 (connect_in 9 8192 16 connect_addr_mem) listening_socket_model
      = Ok (mkEffect (errno_ret EBADF) [] []) listening_socket_model [] ∧
    connect_witness 3 8192 129 (connect_in 3 8192 129 connect_addr_mem) listening_socket_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] ∧
    connect_witness 3 8192 (Z_to_bv 64 (2 ^ 32 - 1))
      (connect_in 3 8192 (Z_to_bv 64 (2 ^ 32 - 1)) connect_addr_mem) listening_socket_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] ∧
    connect_witness 3 8192 128 (connect_in 3 8192 128 connect_addr_mem128) listening_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EISCONN) [] [] [] [] [(8192, 128)])
           listening_socket_model [] ∧
    connect_witness 1 8192 16 (connect_in 1 8192 16 (fun _ => none)) listening_socket_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) listening_socket_model [] ∧
    connect_witness 1 8192 16 (connect_in 1 8192 16 connect_addr_mem) listening_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret ENOTSOCK) [] [] [] [] [(8192, 16)])
           listening_socket_model [] ∧
    connect_witness 1 8192 0 (connect_in 1 8192 0 connect_addr_mem) listening_socket_model
      = Ok (mkEffect (errno_ret ENOTSOCK) [] []) listening_socket_model [] ∧
    connect_witness 3 8192 1 (connect_in 3 8192 1 connect_addr_mem) listening_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 1)])
           listening_socket_model [] ∧
    connect_witness 3 8192 0 (connect_in 3 8192 0 (fun _ => none)) listening_socket_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] ∧
    connect_witness 3 8192 2 (connect_in 3 8192 2 connect_unspec_mem) fresh_socket_model
      = Ok (SyscallEffect.mkEffectU 0 [] [] [] [] [(8192, 2)]) fresh_socket_model [] ∧
    connect_witness 3 8192 2 (connect_in 3 8192 2 connect_unspec_mem) listening_socket_model
      = Unmodeled ∧
    connect_witness 3 8192 16 (connect_in 3 8192 16 connect_addr_mem) listening_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EISCONN) [] [] [] [] [(8192, 16)])
           listening_socket_model [] ∧
    connect_witness 4 8192 16 (connect_in 4 8192 16 connect_addr_mem) accepted_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EISCONN) [] [] [] [] [(8192, 16)])
           accepted_socket_model [] ∧
    connect_witness 3 8192 16 (connect_in 3 8192 16 connect_addr_mem) reset_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EISCONN) [] [] [] [] [(8192, 16)])
           reset_socket_model [] ∧
    connect_witness 3 8192 4 (connect_in 3 8192 4 connect_addr_mem) fresh_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 4)])
           fresh_socket_model [] ∧
    connect_witness 3 8192 15 (connect_in 3 8192 15 connect_addr_mem) fresh_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 15)])
           fresh_socket_model [] ∧
    connect_witness 3 8192 8 (connect_in 3 8192 8 connect_unix_family_mem) fresh_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 8)])
           fresh_socket_model [] ∧
    connect_witness 3 8192 16 (connect_in 3 8192 16 connect_unix_family_mem) bound_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EAFNOSUPPORT) [] [] [] [] [(8192, 16)])
           bound_socket_model [] ∧
    connect_witness 3 8192 16 (connect_in 3 8192 16 connect_addr_mem) fresh_socket_model
      = Unmodeled ∧
    connect_witness 3 8192 16 (connect_in 3 8192 16 connect_addr_mem) bound_socket_model
      = Unmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    witness_norm

/-- getsockname's witness: the two descriptor errnos, and `Unmodeled` on
every socket state.
kernel: net/socket.c:__sys_getsockname,sock_from_file; net/ipv4/af_inet.c:inet_getname@v6.18.46 -/
theorem getsockname_witness_names_each_arm :
    getsockname_witness 11 socket_states_model
      = Ok (mkEffect (errno_ret EBADF) [] []) socket_states_model [] ∧
    getsockname_witness 3 socket_states_model
      = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_states_model [] ∧
    getsockname_witness 6 socket_states_model = Unmodeled ∧
    getsockname_witness 7 socket_states_model = Unmodeled ∧
    getsockname_witness 8 socket_states_model = Unmodeled ∧
    getsockname_witness 9 socket_states_model = Unmodeled ∧
    getsockname_witness 10 socket_states_model = Unmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> witness_norm

/-- getpeername's witness: the two descriptor errnos, -ENOTCONN on the
fresh, bound, listening and reset sockets, `Unmodeled` on the connected
one.
kernel: net/socket.c:__sys_getpeername,sock_from_file; net/ipv4/af_inet.c:inet_getname@v6.18.46 -/
theorem getpeername_witness_names_each_arm :
    getpeername_witness 11 socket_states_model
      = Ok (mkEffect (errno_ret EBADF) [] []) socket_states_model [] ∧
    getpeername_witness 3 socket_states_model
      = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_states_model [] ∧
    getpeername_witness 6 socket_states_model
      = Ok (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model [] ∧
    getpeername_witness 7 socket_states_model
      = Ok (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model [] ∧
    getpeername_witness 8 socket_states_model
      = Ok (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model [] ∧
    getpeername_witness 10 socket_states_model
      = Ok (mkEffect (errno_ret ENOTCONN) [] []) socket_states_model [] ∧
    getpeername_witness 9 socket_states_model = Unmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> witness_norm

/-- shutdown's witness: the two descriptor errnos, -EINVAL on a `how`
outside {0, 1, 2} on every state, 0 on SHUT_WR over the listener,
`Unmodeled` on SHUT_RD and SHUT_RDWR over it and on every `how` over the
other four states.
kernel: net/socket.c:__sys_shutdown,sock_from_file; net/ipv4/af_inet.c:inet_shutdown@v6.18.46 -/
theorem shutdown_witness_names_each_arm :
    shutdown_witness 11 1 socket_states_model
      = Ok (mkEffect (errno_ret EBADF) [] []) socket_states_model [] ∧
    shutdown_witness 3 1 socket_states_model
      = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_states_model [] ∧
    shutdown_witness 6 3 socket_states_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) socket_states_model [] ∧
    shutdown_witness 8 99 socket_states_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) socket_states_model [] ∧
    shutdown_witness 9 (Z_to_bv 64 (2 ^ 31 - 1)) socket_states_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) socket_states_model [] ∧
    shutdown_witness 8 1 socket_states_model = Ok (mkEffect 0 [] []) socket_states_model [] ∧
    shutdown_witness 8 0 socket_states_model = Unmodeled ∧
    shutdown_witness 8 2 socket_states_model = Unmodeled ∧
    shutdown_witness 6 1 socket_states_model = Unmodeled ∧
    shutdown_witness 7 0 socket_states_model = Unmodeled ∧
    shutdown_witness 9 2 socket_states_model = Unmodeled ∧
    shutdown_witness 10 1 socket_states_model = Unmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> witness_norm

/-- An unknown type-flag bit is -EINVAL, before the family is judged and
before either descriptor is reserved, so AF_INET and AF_UNIX answer it
alike.  For the destination arms, the reservation errno needs neither
writes nor a fault, so the witness can choose it before either store.
kernel: net/socket.c:__sys_socketpair; fs/file.c:alloc_fd,alloc_fdtable@v6.18.46 -/
theorem socketpair_witness_names_each_arm :
    socketpair_witness 2 257 0 4096 (socketpair_in 2 257 0 4096 wmem_open) socketpair_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) socketpair_model [] ∧
    socketpair_witness 1 257 0 4096 (socketpair_in 1 257 0 4096 wmem_open) socketpair_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) socketpair_model [] ∧
    socketpair_witness 1 1 0 4096 (socketpair_in 1 1 0 4096 wmem_open) socketpair_model
      = Unmodeled ∧
    socketpair_witness 2 1 0 4096 (socketpair_in 2 1 0 4096 wmem_open) socketpair_model
      = Ok (mkEffect (errno_ret EMFILE) [] []) socketpair_model [] ∧
    socketpair_witness 2 1 0 140737488355328 (socketpair_in 2 1 0 140737488355328 (fun _ => none))
      socketpair_model = Ok (mkEffect (errno_ret EMFILE) [] []) socketpair_model [] ∧
    socketpair_witness 2 1 0 140737488355323 (socketpair_in 2 1 0 140737488355323 (fun _ => none))
      socketpair_model = Unmodeled ∧
    socketpair_witness 2 1 0 4096 (socketpair_in 2 1 0 4096 (fun _ => none)) socketpair_model
      = Unmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> witness_norm

/-! ## setsockopt and getsockopt: the option calls' checkers

The OPTIONS group, appended by ticket C-Net-Socket-options below the
lifecycle checkers' pins and their witnesses.  What is pinned: the two rows
and their `_row_is_the_arm` theorems; Rocq's eight worked examples for 208
and 209, restated on the row cell for cell; and what those examples do not
reach — the four socket states beyond the fresh one, the lies on every
gate, the known-level decline under every ledger, the three register
narrowings and the one pointer that is not narrowed.

THE ROCQ MAPPING, Rocq name first: the 208 and 209 columns of
`socket_calls_decline_every_non_socket_fd_kind` are
`check_setsockopt_declines_every_non_socket_fd_kind` and
`check_getsockopt_declines_every_non_socket_fd_kind`; the 208 and 209
cells of `socket_calls_unknown_level_never_beats_the_fd` are
`check_option_calls_unknown_level_never_beats_the_fd`, and there the refused
lie IS Rocq's -ENOPROTOOPT, the errno of the set side's own next gate, with
the get side's -EOPNOTSUPP refused beside it;
`setsockopt_negative_optlen_never_beats_the_fd` and
`getsockopt_optlen_ledger_marks_the_read` keep their names with `check_`
in front, the latter over `getsockopt_answering`, Rocq's spelling of the
call; the 209 cell of `socket_calls_null_pointers_never_beat_the_fd` is
`check_getsockopt_null_pointers_never_beat_the_fd`; and the three past the
fd on the fresh socket 6 —
`unknown_level_is_enoprotoopt_setting_and_eopnotsupp_getting`,
`negative_optlen_beats_the_unknown_level` and `a_known_level_is_declined`
— keep their names with `check_` in front, in their own subsection.  The
header's caveat holds here too: this list is prose, and nothing reads it.

HOW THESE ARE PROVED.  `options_norm` is `check_norm` over the two option
checkers: the same three passes, opening the rows, the checkers, the
acceptors and the two gates the checkers test — `int32_neg`, a `decide`
over `sint32`, and `sock_level_known`, a `decide` over three equalities —
and deciding what is closed.  It is its own macro rather than its names
added to `check_open`'s list because that list is a literal the I/O
ticket's checkers will also want lines of: a per-group opener costs
one repeated acceptor list, a shared one a conflict on every append.  The
witness pins run `options_witness_norm`, the same over the two witnesses.
None is `rfl`, for the header's reason. -/

def check_setsockopt_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_setsockopt (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) eff m

def check_getsockopt_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_getsockopt i (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) eff m

/-- setsockopt's row: a0 through `fd32`, a1 and a4 through `int32`, a2 and
a3 unread.  `SYSCALL_DEFINE5(setsockopt, int, fd, int, level, int,
optname, char __user *, optval, int, optlen)` (net/socket.c:2389-2390,
Linux v6.18.46) takes `fd`, `level` and `optlen` as `int`, so each reaches
`__sys_setsockopt` low-32 — which is why `optlen = 2^32 - 1` is the `int`
-1 and -EINVAL, and `optlen = 2^32 + 4` is 4 and not.  The fd and level
narrowings are pinned at the row below; a4's is held by this theorem's
PROOF alone, since `int32_neg` reads the low half whether or not the row
does: the direct application of `check_setsockopt_sound_ok` fails to
elaborate against a row handing a4 whole, where the statement — still
true, since `int32_neg` reads only `abi_low32` of its argument — would
not.  The hold
lasts exactly as long as the proof stays that application.
kernel: net/socket.c:setsockopt,__sys_setsockopt@v6.18.46 -/
theorem setsockopt_row_is_the_arm (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_setsockopt_row i eff m = CheckOk m' evs) :
    (Sys.Registry.Net.Socket.setsockopt_arm).sa_spec i m (Ok eff m' evs) :=
  check_setsockopt_sound_ok _ _ _ _ _ _ _ _ h

/-- getsockopt's row: a0 through `fd32`, a1 through `int32`, a4 WHOLE —
`int __user *optlen` in `SYSCALL_DEFINE5(getsockopt, …)`
(net/socket.c:2455-2456, Linux v6.18.46) is a pointer, handed to
`__sys_getsockopt` as one and read at its full address by
`do_sock_getsockopt` (:2409-2410); `check_getsockopt_optlen_pointer_is_not_narrowed`
below is the value that separates this row from one that narrowed it.
kernel: net/socket.c:getsockopt,__sys_getsockopt,do_sock_getsockopt@v6.18.46 -/
theorem getsockopt_row_is_the_arm (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_getsockopt_row i eff m = CheckOk m' evs) :
    (Sys.Registry.Net.Socket.getsockopt_arm).sa_spec i m (Ok eff m' evs) :=
  check_getsockopt_sound_ok _ _ _ _ _ _ _ _ h

/-- Rocq's `getsockopt_answering`: `getsockopt(3, level, 4, 4096, optlenp)`
over `sockaddr_in_any_mem` — reused purely as a MEMORY MAP, so that 4096 is
a readable four-byte `optlen`, 8192 an unreadable one and 4109 one that
straddles the mapped boundary with three readable bytes — answering `r`
with the copy-in ledger `cis`.  `mkEffectU` rather than `mkEffect`, because
the ledger is the point. -/
def getsockopt_answering (m : Model) (level optlenp r : word) (cis : List (word × Nat))
    : check_result :=
  check_getsockopt_row (getsockopt_in 3 level 4 4096 optlenp sockaddr_in_any_mem)
    (SyscallEffect.mkEffectU r [] [] [] [] cis) m

/-- Open the two rows, the two checkers, the acceptors and the gates, and
decide what is closed; `scoped` for `check_open`'s reason. -/
scoped macro "options_open" cfg:Lean.Parser.Tactic.optConfig : tactic =>
  `(tactic| simp $cfg:optConfig only [check_setsockopt_row, check_getsockopt_row,
      getsockopt_answering, check_setsockopt, check_getsockopt,
      check_ret_only_copyins, check_ret_only, clear_copyins, with_copyins,
      sock_fd, sock_level_known, int32_neg,
      Bool.and_eq_true, Bool.or_eq_true, bv_eqb_eq, writes_eqb_eq, access_ranges_eqb_eq,
      check_result.CheckOk.injEq, ne_eq, reduceCtorEq, sys_simp, ↓reduceIte])

/-- Evaluate a closed call of one of the two option checkers, the way
`check_norm` evaluates a lifecycle one. -/
scoped macro "options_norm" : tactic =>
  `(tactic| (options_open +decide;
             first | done | sys_simp_pass +ground +decide -failIfUnchanged;
             first | done | options_open +ground +decide))

/-! ### The fd first, on both calls

`__sys_setsockopt` (net/socket.c:2372-2387, Linux v6.18.46) and
`__sys_getsockopt` (:2439-2453) reach `CLASS(fd, f)(fd)` before any test:
`fd_empty`
is -EBADF, a file `sock_from_file` finds no socket in is -ENOTSOCK, and
only then is `do_sock_setsockopt` or `do_sock_getsockopt` entered.  So
nothing in a1..a4 — the level, the length, the pointers — is read on a
descriptor that fails here, and the checker accepts the descriptor errno
with an empty ledger and refuses every answer from behind the lookup. -/

/-- Rocq's `socket_calls_decline_every_non_socket_fd_kind`, the 208 column,
all twelve of its cells: a channel, a file, a write-only file and a
directory are -ENOTSOCK from `sock_from_file` in `__sys_setsockopt`, and
on each of the four -EBADF and success are lies.  The three kinds Rocq's
table never held — the pipe end at 6, /dev/null at 7, /dev/urandom at 8 —
answer the same and refuse the same two lies.
kernel: net/socket.c:__sys_setsockopt,sock_from_file@v6.18.46 -/
theorem check_setsockopt_declines_every_non_socket_fd_kind :
    check_setsockopt_row (socket_call_in 208 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_setsockopt_row (socket_call_in 208 3) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_setsockopt_row (socket_call_in 208 4) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_setsockopt_row (socket_call_in 208 5) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_setsockopt_row (socket_call_in 208 6) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_setsockopt_row (socket_call_in 208 7) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_setsockopt_row (socket_call_in 208 8) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_setsockopt_row (socket_call_in 208 0) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_setsockopt_row (socket_call_in 208 0) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_setsockopt_row (socket_call_in 208 3) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_setsockopt_row (socket_call_in 208 3) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_setsockopt_row (socket_call_in 208 4) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_setsockopt_row (socket_call_in 208 4) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_setsockopt_row (socket_call_in 208 5) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_setsockopt_row (socket_call_in 208 5) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_setsockopt_row (socket_call_in 208 6) (mkEffect (errno_ret EBADF) [] [])
      socket_kinds_model = CheckReject ∧
    check_setsockopt_row (socket_call_in 208 6) (mkEffect 0 [] []) socket_kinds_model
      = CheckReject ∧
    check_setsockopt_row (socket_call_in 208 7) (mkEffect (errno_ret EBADF) [] [])
      socket_kinds_model = CheckReject ∧
    check_setsockopt_row (socket_call_in 208 7) (mkEffect 0 [] []) socket_kinds_model
      = CheckReject ∧
    check_setsockopt_row (socket_call_in 208 8) (mkEffect (errno_ret EBADF) [] [])
      socket_kinds_model = CheckReject ∧
    check_setsockopt_row (socket_call_in 208 8) (mkEffect 0 [] []) socket_kinds_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    options_norm

/-- The 209 column of the same, with a4 pointing at 4, unmapped in the
fixture: nothing is read on a descriptor that is not a socket, so the
accepted ledger is empty; the same twenty-one cells, the three kinds Rocq
never held refusing the same two lies.
kernel: net/socket.c:__sys_getsockopt,sock_from_file@v6.18.46 -/
theorem check_getsockopt_declines_every_non_socket_fd_kind :
    check_getsockopt_row (socket_call_in 209 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_getsockopt_row (socket_call_in 209 3) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_getsockopt_row (socket_call_in 209 4) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_getsockopt_row (socket_call_in 209 5) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_getsockopt_row (socket_call_in 209 6) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_getsockopt_row (socket_call_in 209 7) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_getsockopt_row (socket_call_in 209 8) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_getsockopt_row (socket_call_in 209 0) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_getsockopt_row (socket_call_in 209 0) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_getsockopt_row (socket_call_in 209 3) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_getsockopt_row (socket_call_in 209 3) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_getsockopt_row (socket_call_in 209 4) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_getsockopt_row (socket_call_in 209 4) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_getsockopt_row (socket_call_in 209 5) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_getsockopt_row (socket_call_in 209 5) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_getsockopt_row (socket_call_in 209 6) (mkEffect (errno_ret EBADF) [] [])
      socket_kinds_model = CheckReject ∧
    check_getsockopt_row (socket_call_in 209 6) (mkEffect 0 [] []) socket_kinds_model
      = CheckReject ∧
    check_getsockopt_row (socket_call_in 209 7) (mkEffect (errno_ret EBADF) [] [])
      socket_kinds_model = CheckReject ∧
    check_getsockopt_row (socket_call_in 209 7) (mkEffect 0 [] []) socket_kinds_model
      = CheckReject ∧
    check_getsockopt_row (socket_call_in 209 8) (mkEffect (errno_ret EBADF) [] [])
      socket_kinds_model = CheckReject ∧
    check_getsockopt_row (socket_call_in 209 8) (mkEffect 0 [] []) socket_kinds_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    options_norm

/-- Rocq's `socket_calls_unknown_level_never_beats_the_fd`, its 208 and 209
cells: a1 holds 999, a level no protocol registers, and on a socket the
level test would fire — `ip_setsockopt`'s -ENOPROTOOPT
(net/ipv4/ip_sockglue.c:1414-1415) on the set side, `do_ip_getsockopt`'s
-EOPNOTSUPP (:1515-1516) on the get side.  Both sit behind the lookup in
`__sys_setsockopt` and `__sys_getsockopt`, so a closed descriptor is -EBADF
and a live file -ENOTSOCK on both calls, and each side's level errno is
refused on the live file — Rocq's -ENOPROTOOPT on both, and here the get
side's own -EOPNOTSUPP beside it.  On the closed 9 the file's errno and
success are lies as well: `__sys_setsockopt` and `__sys_getsockopt`
return -EBADF on an empty descriptor (net/socket.c:2380-2381, :2445-2446)
before `sock_from_file` is asked anything, so -ENOTSOCK there is an answer
about a file the lookup never produced.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem check_option_calls_unknown_level_never_beats_the_fd :
    check_setsockopt_row (socket_call_in 208 9) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_getsockopt_row (socket_call_in 209 9) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_setsockopt_row (socket_call_in 208 3) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_getsockopt_row (socket_call_in 209 3) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_setsockopt_row (socket_call_in 208 3) (mkEffect (errno_ret ENOPROTOOPT) [] [])
      socket_call_model = CheckReject ∧
    check_getsockopt_row (socket_call_in 209 3) (mkEffect (errno_ret ENOPROTOOPT) [] [])
      socket_call_model = CheckReject ∧
    check_getsockopt_row (socket_call_in 209 3) (mkEffect (errno_ret EOPNOTSUPP) [] [])
      socket_call_model = CheckReject ∧
    check_setsockopt_row (socket_call_in 208 9) (mkEffect (errno_ret ENOPROTOOPT) [] [])
      socket_call_model = CheckReject ∧
    check_getsockopt_row (socket_call_in 209 9) (mkEffect (errno_ret EOPNOTSUPP) [] [])
      socket_call_model = CheckReject ∧
    check_setsockopt_row (socket_call_in 208 9) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckReject ∧
    check_setsockopt_row (socket_call_in 208 9) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_getsockopt_row (socket_call_in 209 9) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckReject ∧
    check_getsockopt_row (socket_call_in 209 9) (mkEffect 0 [] []) socket_call_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> options_norm

/-- Rocq's `setsockopt_negative_optlen_never_beats_the_fd`: a4 holds
`2^64 - 1`, the `int` -1, and the -EINVAL it earns is the first statement
of `do_sock_setsockopt` (net/socket.c:2335-2336), which `__sys_setsockopt`
enters only once the descriptor has resolved to a socket (:2386).  A closed
descriptor is -EBADF, a live file -ENOTSOCK, and -EINVAL is a lie on the
file.  That order is v6.7 and later — up to v6.6 the test sat in
`__sys_setsockopt` ahead of the lookup
(bugs/setsockopt-getsockopt-orders-rest-on-v6.7-and-v6.11.md); at the
pinned version this is where it sits.
kernel: net/socket.c:__sys_setsockopt,do_sock_setsockopt@v6.18.46 -/
theorem check_setsockopt_negative_optlen_never_beats_the_fd :
    check_setsockopt_row (setsockopt_in 9 1 2 4096 (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect (errno_ret EBADF) [] []) socket_call_model = CheckOk socket_call_model [] ∧
    check_setsockopt_row (setsockopt_in 3 1 2 4096 (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model = CheckOk socket_call_model [] ∧
    check_setsockopt_row (setsockopt_in 3 1 2 4096 (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect (errno_ret EINVAL) [] []) socket_call_model = CheckReject ∧
    check_setsockopt_row (setsockopt_in 9 1 2 4096 (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect (errno_ret EINVAL) [] []) socket_call_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> options_norm

/-- Rocq's `socket_calls_null_pointers_never_beat_the_fd`, the 209 cell: NULL
`optval` and `optlen` on a live file are -ENOTSOCK from `__sys_getsockopt`,
and the two errnos a socket could earn behind the lookup are refused.  The
input's level is 0, SOL_IP, so on a socket the NULL `optlen` would draw
-EFAULT from `do_ip_getsockopt`'s own length copy
(net/ipv4/ip_sockglue.c:1521-1522), reached once `do_sock_getsockopt`'s
discarded copy (net/socket.c:2409-2410) has run; -EINVAL is what that
table gives a NEGATIVE length it could read
(net/ipv4/ip_sockglue.c:1523-1524), which a NULL pointer never earns at
all.  `sk_getsockopt`'s copies of the same two
tests (net/core/sock.c:1743-1746) are SOL_SOCKET's and not on this
input's path.
kernel: net/socket.c:__sys_getsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:do_ip_getsockopt@v6.18.46 -/
theorem check_getsockopt_null_pointers_never_beat_the_fd :
    check_getsockopt_row (socket_call_null_in 209) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_getsockopt_row (socket_call_null_in 209) (mkEffect (errno_ret EFAULT) [] [])
      socket_call_model = CheckReject ∧
    check_getsockopt_row (socket_call_null_in 209) (mkEffect (errno_ret EINVAL) [] [])
      socket_call_model = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> options_norm

/-- -ENOTSOCK reads nothing even when it could: with the `int` -1 readable
at 4096 under `optlen`, every non-socket kind — the file at 3 and the
channel at 0 of `socket_states_model`, the write-only file at 4 and the
directory at 5 of `socket_call_model`, the pipe end at 6, /dev/null at 7
and /dev/urandom at 8 of `socket_kinds_model` — is -ENOTSOCK with an EMPTY
ledger, and an effect ledgering the four bytes is refused on each —
`__sys_getsockopt` returns on a file that is no socket
(net/socket.c:2447-2449) before `do_sock_getsockopt` reaches its `optlen`
copy (:2409-2410).  The pins above cannot tell: their `optlen` is
unreadable or NULL, so the ledger is empty whether or not the checker
read.
kernel: net/socket.c:__sys_getsockopt,do_sock_getsockopt@v6.18.46 -/
theorem check_getsockopt_enotsock_reads_nothing_even_when_it_could :
    check_getsockopt_row (getsockopt_in 3 999 2 4104 4096 optlen_minus_one_mem)
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_getsockopt_row (getsockopt_in 3 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret ENOTSOCK) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in 0 999 2 4104 4096 optlen_minus_one_mem)
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_getsockopt_row (getsockopt_in 0 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret ENOTSOCK) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in 4 999 2 4104 4096 optlen_minus_one_mem)
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model
      = CheckOk socket_call_model [] ∧
    check_getsockopt_row (getsockopt_in 4 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret ENOTSOCK) [] [] [] [] [(4096, 4)])
      socket_call_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in 5 999 2 4104 4096 optlen_minus_one_mem)
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model
      = CheckOk socket_call_model [] ∧
    check_getsockopt_row (getsockopt_in 5 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret ENOTSOCK) [] [] [] [] [(4096, 4)])
      socket_call_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in 6 999 2 4104 4096 optlen_minus_one_mem)
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model
      = CheckOk socket_kinds_model [] ∧
    check_getsockopt_row (getsockopt_in 6 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret ENOTSOCK) [] [] [] [] [(4096, 4)])
      socket_kinds_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in 7 999 2 4104 4096 optlen_minus_one_mem)
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model
      = CheckOk socket_kinds_model [] ∧
    check_getsockopt_row (getsockopt_in 7 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret ENOTSOCK) [] [] [] [] [(4096, 4)])
      socket_kinds_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in 8 999 2 4104 4096 optlen_minus_one_mem)
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model
      = CheckOk socket_kinds_model [] ∧
    check_getsockopt_row (getsockopt_in 8 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret ENOTSOCK) [] [] [] [] [(4096, 4)])
      socket_kinds_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> options_norm

/-! ### Rocq's examples past the fd, cell for cell

Rocq's three worked examples past the descriptor — `Example`s over
`check_syscall` in `Checks/Cases/Net/Socket.v`, on the fresh socket 6 of
`socket_states_model` with nothing mapped — restated on the row with their
cells unchanged, so the checker twin is held to the Rocq checker's own
answers before the sections below vary the state, the length and the
ledger. -/

/-- Rocq's `unknown_level_is_enoprotoopt_setting_and_eopnotsupp_getting`:
level 999 on the fresh socket is `ip_setsockopt`'s -ENOPROTOOPT
(net/ipv4/ip_sockglue.c:1414-1415) on the set side and `do_ip_getsockopt`'s
-EOPNOTSUPP (:1515-1516) on the get side — two functions, one file, two
errnos — and each side refuses the other's.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem check_unknown_level_is_enoprotoopt_setting_and_eopnotsupp_getting :
    check_setsockopt_row (setsockopt_in 6 999 2 4096 4) (mkEffect (errno_ret ENOPROTOOPT) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in 6 999 2 4096 4) (mkEffect (errno_ret EOPNOTSUPP) [] [])
      socket_states_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in 6 999 2 4096 4104 (fun _ => none))
      (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_getsockopt_row (getsockopt_in 6 999 2 4096 4104 (fun _ => none))
      (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> options_norm

/-- Rocq's `negative_optlen_beats_the_unknown_level`: the call that is
-ENOPROTOOPT at length 4 is -EINVAL at the `int` -1, because
`do_sock_setsockopt` tests the length first (net/socket.c:2335-2336), and
-ENOPROTOOPT is then a lie.
kernel: net/socket.c:do_sock_setsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt@v6.18.46 -/
theorem check_negative_optlen_beats_the_unknown_level :
    check_setsockopt_row (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect (errno_ret EINVAL) [] []) socket_states_model = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> options_norm

/-- Rocq's `a_known_level_is_declined`: SOL_IP (0), SOL_SOCKET (1) and
SOL_TCP (6) are declined on both calls — the option tables, `sk_setsockopt`
and `sk_getsockopt`, `ip_setsockopt` and `do_ip_getsockopt` past their
level tests, `do_tcp_setsockopt` and `do_tcp_getsockopt`, are not modeled
— and the unknown level 999 is still answered on both, so the declines are
not a checker that stopped answering every level.
kernel: net/core/sock.c:sk_setsockopt,sk_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt; net/ipv4/tcp.c:do_tcp_setsockopt,do_tcp_getsockopt@v6.18.46 -/
theorem check_a_known_level_is_declined :
    check_setsockopt_row (setsockopt_in 6 0 2 4096 4) (mkEffect 0 [] []) socket_states_model
      = CheckUnmodeled ∧
    check_getsockopt_row (getsockopt_in 6 0 2 4096 4104 (fun _ => none)) (mkEffect 0 [] [])
      socket_states_model = CheckUnmodeled ∧
    check_setsockopt_row (setsockopt_in 6 1 2 4096 4) (mkEffect 0 [] []) socket_states_model
      = CheckUnmodeled ∧
    check_getsockopt_row (getsockopt_in 6 1 2 4096 4104 (fun _ => none)) (mkEffect 0 [] [])
      socket_states_model = CheckUnmodeled ∧
    check_setsockopt_row (setsockopt_in 6 6 2 4096 4) (mkEffect 0 [] []) socket_states_model
      = CheckUnmodeled ∧
    check_getsockopt_row (getsockopt_in 6 6 2 4096 4104 (fun _ => none)) (mkEffect 0 [] [])
      socket_states_model = CheckUnmodeled ∧
    check_setsockopt_row (setsockopt_in 6 999 2 4096 4) (mkEffect (errno_ret ENOPROTOOPT) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_getsockopt_row (getsockopt_in 6 999 2 4096 4104 (fun _ => none))
      (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model
      = CheckOk socket_states_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> options_norm

/-! ### setsockopt on a socket: the length, then the level

`do_sock_setsockopt` (net/socket.c:2328-2366, Linux v6.18.46) tests
`optlen < 0` first (:2335-2336) and dispatches on the level after: a level
other than SOL_SOCKET goes through `inet_stream_ops`'s
`sock_common_setsockopt` to `tcp_setsockopt`, which hands a level other
than SOL_TCP to `ip_setsockopt`, whose first test is `level != SOL_IP` →
-ENOPROTOOPT (net/ipv4/ip_sockglue.c:1414-1415, v6.18.46).  Neither test
reads the
socket's state, so every `SockState` answers alike; the fixture is
`socket_states_model`, fresh at 6, bound at 7, listening at 8, connected
at 9, reset at 10. -/

/-- The `int` -1 is -EINVAL on every socket state, and the two answers a
reader of the level would give — -ENOPROTOOPT for the unknown level 999
in a1, and 0 — are refused, -ENOPROTOOPT on the fresh and the connected
socket, success and -EBADF on the fresh one.
kernel: net/socket.c:__sys_setsockopt,do_sock_setsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt@v6.18.46 -/
theorem check_setsockopt_negative_optlen_is_einval_on_every_state :
    check_setsockopt_row (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect (errno_ret EINVAL) [] []) socket_states_model = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in 7 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect (errno_ret EINVAL) [] []) socket_states_model = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in 8 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect (errno_ret EINVAL) [] []) socket_states_model = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in 9 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect (errno_ret EINVAL) [] []) socket_states_model = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in 10 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect (errno_ret EINVAL) [] []) socket_states_model = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model = CheckReject ∧
    check_setsockopt_row (setsockopt_in 9 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model = CheckReject ∧
    check_setsockopt_row (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect 0 [] []) socket_states_model = CheckReject ∧
    check_setsockopt_row (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect (errno_ret EBADF) [] []) socket_states_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> options_norm

/-- The length test precedes the level dispatch: with SOL_TCP in a1 — a
KNOWN level, declined when the length is fine — the `int` -1 is still
-EINVAL and not a decline, and INT_MIN (`2^31`) is the same.  A twin that
dispatched on the level first would answer `CheckUnmodeled` here.
kernel: net/socket.c:do_sock_setsockopt@v6.18.46 -/
theorem check_setsockopt_negative_optlen_beats_the_known_level :
    check_setsockopt_row (setsockopt_in 6 6 1 4096 (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect (errno_ret EINVAL) [] []) socket_states_model = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in 6 6 1 4096 (Z_to_bv 64 (2 ^ 31)))
      (mkEffect (errno_ret EINVAL) [] []) socket_states_model = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in 8 1 2 4096 (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect (errno_ret EINVAL) [] []) socket_states_model = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in 6 6 1 4096 (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect 0 [] []) socket_states_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> options_norm

/-- The unknown level 999 is -ENOPROTOOPT on every socket state, from
`ip_setsockopt`, with `optlen` 4; 0 and INT_MAX (`2^31 - 1`) as the length
reach the same answer, since neither is negative.
kernel: net/socket.c:__sys_setsockopt,do_sock_setsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt@v6.18.46 -/
theorem check_setsockopt_unknown_level_is_enoprotoopt_on_every_state :
    check_setsockopt_row (setsockopt_in 6 999 2 4096 4) (mkEffect (errno_ret ENOPROTOOPT) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in 7 999 2 4096 4) (mkEffect (errno_ret ENOPROTOOPT) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in 8 999 2 4096 4) (mkEffect (errno_ret ENOPROTOOPT) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in 9 999 2 4096 4) (mkEffect (errno_ret ENOPROTOOPT) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in 10 999 2 4096 4) (mkEffect (errno_ret ENOPROTOOPT) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in 6 999 2 4096 0) (mkEffect (errno_ret ENOPROTOOPT) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 31 - 1)))
      (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model
      = CheckOk socket_states_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> options_norm

/-- The lies on the unknown level: the get side's -EOPNOTSUPP — which
`do_sock_setsockopt` itself spells only for an ops table with no
`setsockopt` (net/socket.c:2358-2359), never for a level — success,
-EINVAL from a length that is not negative, -ENOTSOCK from a descriptor
that is a socket, and -EBADF from one that is open.
kernel: net/socket.c:__sys_setsockopt,do_sock_setsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt@v6.18.46 -/
theorem check_setsockopt_unknown_level_lies_rejected :
    check_setsockopt_row (setsockopt_in 6 999 2 4096 4) (mkEffect (errno_ret EOPNOTSUPP) [] [])
      socket_states_model = CheckReject ∧
    check_setsockopt_row (setsockopt_in 9 999 2 4096 4) (mkEffect (errno_ret EOPNOTSUPP) [] [])
      socket_states_model = CheckReject ∧
    check_setsockopt_row (setsockopt_in 6 999 2 4096 4) (mkEffect 0 [] []) socket_states_model
      = CheckReject ∧
    check_setsockopt_row (setsockopt_in 6 999 2 4096 4) (mkEffect (errno_ret EINVAL) [] [])
      socket_states_model = CheckReject ∧
    check_setsockopt_row (setsockopt_in 6 999 2 4096 0) (mkEffect (errno_ret EINVAL) [] [])
      socket_states_model = CheckReject ∧
    check_setsockopt_row (setsockopt_in 6 999 2 4096 4) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_states_model = CheckReject ∧
    check_setsockopt_row (setsockopt_in 6 999 2 4096 4) (mkEffect (errno_ret EBADF) [] [])
      socket_states_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> options_norm

/-- No arm of `setsockopt` reads user memory: with sixteen readable bytes
under `optval` at 4096, the unknown level is still -ENOPROTOOPT with an
EMPTY ledger, and an effect claiming the copy is refused — `ip_setsockopt`
answers before any option table's `copy_from_sockptr` runs, and on the
negative length `do_sock_setsockopt` returns before the dispatch.  The fd
errnos read nothing either, and the fd pins above cannot tell, their
memory being empty: over the same sixteen bytes the file at 3 is -ENOTSOCK
and, on `fresh_socket_model`, where 9 is closed, -EBADF with an empty
ledger, and the ledgered copy is refused on each — `__sys_setsockopt` returns (net/socket.c:2380-2384)
before `do_sock_setsockopt` is entered (:2386).
kernel: net/socket.c:__sys_setsockopt,do_sock_setsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt@v6.18.46 -/
theorem check_setsockopt_reads_nothing_even_when_it_could :
    check_setsockopt_row (setsockopt_in_mem 6 999 2 4096 4 sockaddr_in_any_mem)
      (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in_mem 6 999 2 4096 4 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret ENOPROTOOPT) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject ∧
    check_setsockopt_row (setsockopt_in_mem 6 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1))
        sockaddr_in_any_mem)
      (mkEffect (errno_ret EINVAL) [] []) socket_states_model = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in_mem 6 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1))
        sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject ∧
    check_setsockopt_row (setsockopt_in_mem 3 999 2 4096 4 sockaddr_in_any_mem)
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in_mem 3 999 2 4096 4 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret ENOTSOCK) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject ∧
    check_setsockopt_row (setsockopt_in_mem 9 999 2 4096 4 sockaddr_in_any_mem)
      (mkEffect (errno_ret EBADF) [] []) fresh_socket_model
      = CheckOk fresh_socket_model [] ∧
    check_setsockopt_row (setsockopt_in_mem 9 999 2 4096 4 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [] [] [(4096, 4)])
      fresh_socket_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> options_norm

/-- A KNOWN level with a length that is not negative is the option table
— `sk_setsockopt` (net/core/sock.c:1186, behind `sock_setsockopt`'s
wrapper) for SOL_SOCKET, `ip_setsockopt`
past its level test for SOL_IP, `do_tcp_setsockopt` for SOL_TCP — and the
checker declines it on every state, whatever it is shown: the spec file
says why that intersection is empty (its "a known level is declined"
section).  Two effects per input, so the decline is seen not to depend on
the answer offered.
kernel: net/core/sock.c:sk_setsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt; net/ipv4/tcp.c:do_tcp_setsockopt@v6.18.46 -/
theorem check_setsockopt_known_level_declines_on_every_state :
    check_setsockopt_row (setsockopt_in 6 1 2 4096 4) (mkEffect 0 [] []) socket_states_model
      = CheckUnmodeled ∧
    check_setsockopt_row (setsockopt_in 6 1 2 4096 4) (mkEffect (errno_ret ENOPROTOOPT) [] [])
      socket_states_model = CheckUnmodeled ∧
    check_setsockopt_row (setsockopt_in 7 0 1 4096 4) (mkEffect 0 [] []) socket_states_model
      = CheckUnmodeled ∧
    check_setsockopt_row (setsockopt_in 7 0 1 4096 4) (mkEffect (errno_ret ENOPROTOOPT) [] [])
      socket_states_model = CheckUnmodeled ∧
    check_setsockopt_row (setsockopt_in 8 6 1 4096 4) (mkEffect 0 [] []) socket_states_model
      = CheckUnmodeled ∧
    check_setsockopt_row (setsockopt_in 8 6 1 4096 4) (mkEffect (errno_ret ENOPROTOOPT) [] [])
      socket_states_model = CheckUnmodeled ∧
    check_setsockopt_row (setsockopt_in 9 6 1 4096 4) (mkEffect 0 [] []) socket_states_model
      = CheckUnmodeled ∧
    check_setsockopt_row (setsockopt_in 9 6 1 4096 4) (mkEffect (errno_ret ENOPROTOOPT) [] [])
      socket_states_model = CheckUnmodeled ∧
    check_setsockopt_row (setsockopt_in 10 1 2 4096 4) (mkEffect (errno_ret EINVAL) [] [])
      socket_states_model = CheckUnmodeled ∧
    check_setsockopt_row (setsockopt_in 10 1 2 4096 4) (mkEffect 0 [] []) socket_states_model
      = CheckUnmodeled ∧
    check_setsockopt_row (setsockopt_in 6 6 1 4096 0) (mkEffect 0 [] []) socket_states_model
      = CheckUnmodeled ∧
    check_setsockopt_row (setsockopt_in 6 6 1 4096 0) (mkEffect (errno_ret ENOPROTOOPT) [] [])
      socket_states_model = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> options_norm

/-! ### getsockopt on a socket: the `optlen` read, then the level

`do_sock_getsockopt` (net/socket.c:2398-2432, Linux v6.18.46) runs the LSM
hook and then `copy_from_sockptr(&max_optlen, optlen, sizeof(int))`
(:2409-2410) with no level test between and its result discarded; only
then does it dispatch — SOL_SOCKET to `sk_getsockopt`, every other level
through `sock_common_getsockopt` to `tcp_getsockopt`
(net/ipv4/tcp.c:4841-4845, v6.18.46), which keeps SOL_TCP for
`do_tcp_getsockopt` and hands the rest to `do_ip_getsockopt`, whose first
test is `level != SOL_IP` →
-EOPNOTSUPP (net/ipv4/ip_sockglue.c:1515-1516, v6.18.46).  So every
-EOPNOTSUPP has moved four bytes when the four are readable and none when
they are not, and the errno is the same either way: the ledger is the only
thing the read leaves behind, and the pins below state it in both
directions, since accepting-with-a-ledger alone is satisfied by a checker
that ledgers unconditionally and refusing-a-ledger alone by one that never
ledgers.

THE COPY IS v6.11's.  Before commit 33f339a1ba54 the read ran only under a
cgroup getsockopt program, so on a v6.6.50 or a 6.1.y kernel an unknown
level answers -EOPNOTSUPP with NO copy-in in its trace — a trace a
supported kernel really produces, and one the rows below that refuse an
empty ledger on a readable `optlen` refuse.  That is the spec's decision,
inherited here: the premise and its cost are
bugs/setsockopt-getsockopt-orders-rest-on-v6.7-and-v6.11.md's, and the
harness boots the pinned kernel, which carries the commit. -/

/-- Rocq's `getsockopt_optlen_ledger_marks_the_read`, all ten rows: past the
fd on an unknown level the four bytes at 4096 are required and their
absence refused; an unreadable `optlen` at 8192 is the copy failing, which
transfers nothing, the errno unchanged because the copy's result is
discarded, and a ledger there refused; 4109 straddles the mapped boundary
and is unreadable AS A WHOLE, so it is the same; before the fd verdict,
-EBADF on the closed 9 never reached `do_sock_getsockopt`, so a ledger
there is a read the kernel did not perform; and a KNOWN level, SOL_TCP, is
the option table, declined whatever the ledger — so no row above is the
level test in disguise.  No probe reaches the unreadable rows, as Rocq's
example says: the copy's result is discarded, so no kernel return says
whether `copy_from_user` ran, and an unreadable `optlen` is unreachable
from testing/syscall-check by construction; the readable rows' ledger is
what `socket_calls.c`'s `getsockopt#1:drop-copyins` reject case pins on
the Rocq side.  Rows 5-6 are the residue Rocq names, stated on the
fixture's byte-granular memory: no Linux mapping ends at 4112,
mid-page, but at a real page boundary a `copy_from_user` of a range that
straddles it reads the mapped bytes before faulting on the first unmapped
one, while the model records nothing — an under-record of at most one
page, which `State.syscall_effect_accesses` can only under-charge.
kernel: net/socket.c:__sys_getsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:do_ip_getsockopt@v6.18.46 -/
theorem check_getsockopt_optlen_ledger_marks_the_read :
    getsockopt_answering fresh_socket_model 17 4096 (errno_ret EOPNOTSUPP) [(4096, 4)]
      = CheckOk fresh_socket_model [] ∧
    getsockopt_answering fresh_socket_model 17 4096 (errno_ret EOPNOTSUPP) [] = CheckReject ∧
    getsockopt_answering fresh_socket_model 17 8192 (errno_ret EOPNOTSUPP) []
      = CheckOk fresh_socket_model [] ∧
    getsockopt_answering fresh_socket_model 17 8192 (errno_ret EOPNOTSUPP) [(8192, 4)]
      = CheckReject ∧
    getsockopt_answering fresh_socket_model 17 4109 (errno_ret EOPNOTSUPP) []
      = CheckOk fresh_socket_model [] ∧
    getsockopt_answering fresh_socket_model 17 4109 (errno_ret EOPNOTSUPP) [(4109, 4)]
      = CheckReject ∧
    check_getsockopt_row (getsockopt_in 9 17 4 4096 4096 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [] [] []) fresh_socket_model
      = CheckOk fresh_socket_model [] ∧
    check_getsockopt_row (getsockopt_in 9 17 4 4096 4096 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [] [] [(4096, 4)]) fresh_socket_model
      = CheckReject ∧
    getsockopt_answering fresh_socket_model 6 4096 (errno_ret EOPNOTSUPP) [(4096, 4)]
      = CheckUnmodeled ∧
    getsockopt_answering fresh_socket_model 6 4096 (errno_ret EOPNOTSUPP) [] = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> options_norm

/-- The ledger is exactly the four bytes at `optlen` and nothing else: with
the `int` -1 readable at 4096 and 4104 in a3, the unknown level 999 is
-EOPNOTSUPP with `[(4096, 4)]` on every socket state — the read precedes
the dispatch and never looks at the state — and a ledger shifted to 4100,
grown to five bytes, cut to three, doubled, or naming `optval` instead is
refused on the fresh socket.  The last readable `optlen`, 4108 over
`sockaddr_in_any_mem`, is ledgered too: the bound is on the whole range.
kernel: net/socket.c:__sys_getsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:do_ip_getsockopt@v6.18.46 -/
theorem check_getsockopt_unknown_level_ledgers_the_read_on_every_state :
    check_getsockopt_row (getsockopt_in 6 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_getsockopt_row (getsockopt_in 7 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_getsockopt_row (getsockopt_in 8 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_getsockopt_row (getsockopt_in 9 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_getsockopt_row (getsockopt_in 10 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_getsockopt_row (getsockopt_in 6 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4100, 4)])
      socket_states_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in 6 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4096, 5)])
      socket_states_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in 6 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4096, 3)])
      socket_states_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in 6 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4096, 4), (4096, 4)])
      socket_states_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in 6 999 2 4096 8192 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in 6 999 2 4096 8192 sockaddr_in_any_mem)
      (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    getsockopt_answering fresh_socket_model 17 4108 (errno_ret EOPNOTSUPP) [(4108, 4)]
      = CheckOk fresh_socket_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> options_norm

/-- The lies on the unknown level, with the read ledgered as it must be: the
set side's -ENOPROTOOPT, which `do_ip_getsockopt` spells for an OPTNAME
under SOL_IP — the unknown one (net/ipv4/ip_sockglue.c:1733), and
IP_PKTOPTIONS on a socket that is no stream
(net/ipv4/ip_sockglue.c:1648-1649) — and never for the
level; success; -EFAULT and -EINVAL, which every option table gives an
unreadable or a negative length — `sk_getsockopt` under SOL_SOCKET
(net/core/sock.c:1743-1746), `do_ip_getsockopt` past its level test
(net/ipv4/ip_sockglue.c:1521-1524), `do_tcp_getsockopt` under SOL_TCP
(net/ipv4/tcp.c:4468-4472) — and 999 reaches none of them: the -1 at 4096
is not read as a length on this path at all; -ENOTSOCK and -EBADF from a
live socket.
kernel: net/socket.c:__sys_getsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:do_ip_getsockopt; net/core/sock.c:sk_getsockopt; net/ipv4/tcp.c:do_tcp_getsockopt@v6.18.46 -/
theorem check_getsockopt_unknown_level_lies_rejected :
    check_getsockopt_row (getsockopt_in 6 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret ENOPROTOOPT) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in 9 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret ENOPROTOOPT) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in 6 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 4)]) socket_states_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in 6 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in 6 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in 6 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret ENOTSOCK) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in 6 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in 6 999 2 4096 8192 sockaddr_in_any_mem)
      (mkEffect (errno_ret EFAULT) [] []) socket_states_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> options_norm

/-- getsockopt's a4 is a pointer, and no gate reads its sign or tests it
for NULL: `2^64 - 1` and `2^31`, the two values `int32_neg` would call
negative on the set side, and NULL, which no length test minds, all reach
the level on the fresh socket, -EOPNOTSUPP with nothing readable and so
nothing ledgered.  -EFAULT, the option tables' answer to an unreadable
length, and -EINVAL, their answer to a negative one, are refused:
`sk_getsockopt`'s pair (net/core/sock.c:1743-1746) runs under SOL_SOCKET
only, and `do_ip_getsockopt`'s (net/ipv4/ip_sockglue.c:1521-1524) sits
past the level test that answers 999 first (:1515-1516).  A checker that
copied the set side's length test onto the pointer would invert the third
through the sixth; one that faulted on NULL, the first two; and the
seventh refuses a four-byte ledger at NULL, which no fixture memory holds
and `read_bytes_map` therefore never yields — the empty ledger is the
read's whole content there too.
kernel: net/socket.c:__sys_getsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:do_ip_getsockopt; net/core/sock.c:sk_getsockopt@v6.18.46 -/
theorem check_getsockopt_optlen_pointer_sign_is_not_read :
    check_getsockopt_row (getsockopt_in 6 999 2 4096 0 (fun _ => none))
      (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_getsockopt_row (getsockopt_in 6 999 2 4096 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) socket_states_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1)) (fun _ => none))
      (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_getsockopt_row (getsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1)) (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) socket_states_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 31)) (fun _ => none))
      (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_getsockopt_row (getsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 31)) (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) socket_states_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in 6 999 2 4096 0 (fun _ => none))
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(0, 4)])
      socket_states_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> options_norm

/-- A KNOWN level is the option table — `sk_getsockopt` for SOL_SOCKET,
`do_ip_getsockopt` past its level test for SOL_IP, `do_tcp_getsockopt` for
SOL_TCP, each of which rewrites `*optlen`, a write the model does not
export — and the checker declines it on every state, with the read
ledgered and without, on an errno and on success.
kernel: net/core/sock.c:sk_getsockopt; net/ipv4/ip_sockglue.c:do_ip_getsockopt; net/ipv4/tcp.c:do_tcp_getsockopt@v6.18.46 -/
theorem check_getsockopt_known_level_declines_on_every_state :
    check_getsockopt_row (getsockopt_in 6 1 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 4)]) socket_states_model
      = CheckUnmodeled ∧
    check_getsockopt_row (getsockopt_in 6 1 2 4104 4096 optlen_minus_one_mem)
      (mkEffect 0 [] []) socket_states_model = CheckUnmodeled ∧
    check_getsockopt_row (getsockopt_in 7 0 1 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckUnmodeled ∧
    check_getsockopt_row (getsockopt_in 8 6 1 4104 4096 optlen_minus_one_mem)
      (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model = CheckUnmodeled ∧
    check_getsockopt_row (getsockopt_in 9 1 2 4104 4096 optlen_minus_one_mem)
      (mkEffect 0 [] []) socket_states_model = CheckUnmodeled ∧
    check_getsockopt_row (getsockopt_in 10 6 1 4104 4096 optlen_minus_one_mem)
      (mkEffect (errno_ret EINVAL) [] []) socket_states_model = CheckUnmodeled ∧
    check_getsockopt_row (getsockopt_in 6 6 1 4096 8192 sockaddr_in_any_mem)
      (mkEffect 0 [] []) socket_states_model = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> options_norm

/-! ### The narrowings, at the row

`SYSCALL_DEFINE5(setsockopt, int, fd, int, level, int, optname, char __user
*, optval, int, optlen)` (net/socket.c:2389-2390, Linux v6.18.46) and
`SYSCALL_DEFINE5(getsockopt, int, fd, int, level, int, optname, char __user
*, optval, int __user *, optlen)` (:2455-2456) take `fd` and `level` as
`int` on both calls, and `optlen` as an `int` on the set side and as a
POINTER on the get side.  The rows narrow what the kernel narrows and hand
the pointer on whole.  The fd and level pins below are values whose high
half would change the answer under the other choice; setsockopt's a4 pin
is not — `int32_neg` reads the low half itself, through `sint32`'s
`abi_low32`, so a row handing a4 over whole answers the same, and that
narrowing is `setsockopt_row_is_the_arm`'s alone.  What the a4 pin
separates is a checker testing the 64-bit sign. -/

/-- `2^32 + 6` in a0 names fd 6, the fresh socket, on both calls: the
unknown level answers, and -EBADF is a lie.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem check_option_calls_fd_high_half_is_discarded :
    check_setsockopt_row (setsockopt_in (Z_to_bv 64 (2 ^ 32 + 6)) 999 2 4096 4)
      (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in (Z_to_bv 64 (2 ^ 32 + 6)) 999 2 4096 4)
      (mkEffect (errno_ret EBADF) [] []) socket_states_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in (Z_to_bv 64 (2 ^ 32 + 6)) 999 2 4096 4104 (fun _ => none))
      (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_getsockopt_row (getsockopt_in (Z_to_bv 64 (2 ^ 32 + 6)) 999 2 4096 4104 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) socket_states_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> options_norm

/-- `2^32 + 17` in a1 is SOL_UDP, unknown, on both calls: each side's level
errno.  `2^32 + 6` is SOL_TCP, KNOWN: declined, not the unknown level's
errno — a row that handed a1 over whole would find both unknown.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem check_option_calls_level_high_half_is_discarded :
    check_setsockopt_row (setsockopt_in 6 (Z_to_bv 64 (2 ^ 32 + 17)) 2 4096 4)
      (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_getsockopt_row (getsockopt_in 6 (Z_to_bv 64 (2 ^ 32 + 17)) 2 4096 4104 (fun _ => none))
      (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in 6 (Z_to_bv 64 (2 ^ 32 + 6)) 2 4096 4)
      (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model = CheckUnmodeled ∧
    check_getsockopt_row (getsockopt_in 6 (Z_to_bv 64 (2 ^ 32 + 6)) 2 4096 4104 (fun _ => none))
      (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> options_norm

/-- setsockopt's a4 is an `int`: `2^32 + 4` is 4, not negative, and the
level answers with -EINVAL refused; `2^63` has bit 63 set and a clear low
half, so the `int` is 0, the same; `2^32 - 1` is the `int` -1 with a clear
high half, -EINVAL with -ENOPROTOOPT refused.  A CHECKER testing the
64-bit sign of the word the row hands it would invert the fifth and the
sixth — the `int` -1 has bit 63 clear — and one handed the raw word the
third through the sixth as well, since `2^63` has it set; the row's
`int32` on a4 is not what separates either — `int32_neg` goes through
`sint32`'s `abi_low32`, so a row handing a4 over whole answers the same
six — and is held by `setsockopt_row_is_the_arm`'s proof alone, as its
docstring says.
kernel: net/socket.c:__sys_setsockopt,do_sock_setsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt@v6.18.46 -/
theorem check_setsockopt_optlen_high_half_is_discarded :
    check_setsockopt_row (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 32 + 4)))
      (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 32 + 4)))
      (mkEffect (errno_ret EINVAL) [] []) socket_states_model = CheckReject ∧
    check_setsockopt_row (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 63)))
      (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 63)))
      (mkEffect (errno_ret EINVAL) [] []) socket_states_model = CheckReject ∧
    check_setsockopt_row (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 32 - 1)))
      (mkEffect (errno_ret EINVAL) [] []) socket_states_model = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 32 - 1)))
      (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> options_norm

/-- THE ONE ARGUMENT THAT IS NOT NARROWED: getsockopt's a4 is `int __user
*optlen`, handed to `do_sock_getsockopt` whole as a `USER_SOCKPTR`
(net/socket.c:2451-2452) and read at its full address (:2409-2410).  Over
`optlen_high_mem`, four readable bytes at `2^32 + 4096` and nothing at
4096, the unknown level is -EOPNOTSUPP with the HIGH address ledgered; an
empty ledger is a truncated read that found nothing, refused, and a ledger
at the low half is a read of unmapped bytes, refused.  A row that put a4
through `int32` would ledger nothing on every real `&optlen` on the stack
while passing every pin below 2^32.
kernel: net/socket.c:__sys_getsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:do_ip_getsockopt@v6.18.46 -/
theorem check_getsockopt_optlen_pointer_is_not_narrowed :
    check_getsockopt_row (getsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 32 + 4096)) optlen_high_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(Z_to_bv 64 (2 ^ 32 + 4096), 4)])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_getsockopt_row (getsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 32 + 4096)) optlen_high_mem)
      (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 32 + 4096)) optlen_high_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> options_norm

/-- The known set is three equalities, not a bound: a level BESIDE one of
them — 2, between SOL_SOCKET and SOL_TCP, 5 and 7 on either side of
SOL_TCP — is unknown like 999, -ENOPROTOOPT setting and -EOPNOTSUPP
getting on the fresh socket.  A TCP socket's ops tables fix the chain —
`sock_common_setsockopt` (net/core/sock.c:3910), then `tcp_setsockopt`
(net/ipv4/tcp.c:4157), then `ip_setsockopt`
(net/ipv4/ip_sockglue.c:1414-1415), and the getting twin down to
`do_ip_getsockopt` (net/ipv4/ip_sockglue.c:1515-1516) — and each hop
compares the `int` against one constant, so a checker whose level test
was `≤ SOL_TCP` would decline the three.  A level whose `int` is NEGATIVE — `2^32 - 1` is -1, `2^31` is
INT_MIN — is unknown the same way, `-1 != SOL_IP`, and -EINVAL is refused
on it: no gate reads a1's sign, and a checker that copied setsockopt's
length test onto the level would invert the last six.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem check_option_calls_levels_beside_the_known_ones_are_unknown :
    check_setsockopt_row (setsockopt_in 6 2 2 4096 4) (mkEffect (errno_ret ENOPROTOOPT) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_getsockopt_row (getsockopt_in 6 2 2 4096 4104 (fun _ => none))
      (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in 6 5 2 4096 4) (mkEffect (errno_ret ENOPROTOOPT) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_getsockopt_row (getsockopt_in 6 5 2 4096 4104 (fun _ => none))
      (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in 6 7 2 4096 4) (mkEffect (errno_ret ENOPROTOOPT) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_getsockopt_row (getsockopt_in 6 7 2 4096 4104 (fun _ => none))
      (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in 6 (Z_to_bv 64 (2 ^ 32 - 1)) 2 4096 4)
      (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_setsockopt_row (setsockopt_in 6 (Z_to_bv 64 (2 ^ 32 - 1)) 2 4096 4)
      (mkEffect (errno_ret EINVAL) [] []) socket_states_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in 6 (Z_to_bv 64 (2 ^ 32 - 1)) 2 4096 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_getsockopt_row (getsockopt_in 6 (Z_to_bv 64 (2 ^ 32 - 1)) 2 4096 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject ∧
    check_setsockopt_row (setsockopt_in 6 (Z_to_bv 64 (2 ^ 31)) 2 4096 4)
      (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_getsockopt_row (getsockopt_in 6 (Z_to_bv 64 (2 ^ 31)) 2 4096 4104 (fun _ => none))
      (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model
      = CheckOk socket_states_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> options_norm

/-- Three boundaries the cells above state in one direction only, stated
in the other.  At 4108, the last `optlen` whose four bytes fit under
`sockaddr_in_any_mem`'s 4112, the empty ledger is refused: the read
happened.  On the set side INT_MAX, `2^31 - 1`, is the largest
non-negative `int`, so -EINVAL is the lie there that it is at 0.  And on
the get side a KNOWN level on the closed descriptor 9 is -EBADF, as on
the set side (`check_setsockopt_negative_optlen_never_beats_the_fd`):
`__sys_getsockopt` answers (net/socket.c:2445-2446) before
`do_sock_getsockopt` looks at the level.
kernel: net/socket.c:__sys_getsockopt,do_sock_setsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt@v6.18.46 -/
theorem check_option_calls_boundaries_stated_the_other_way :
    getsockopt_answering fresh_socket_model 17 4108 (errno_ret EOPNOTSUPP) [] = CheckReject ∧
    check_setsockopt_row (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 31 - 1)))
      (mkEffect (errno_ret EINVAL) [] []) socket_states_model = CheckReject ∧
    check_getsockopt_row (getsockopt_in 9 1 2 4096 4104 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) socket_call_model = CheckOk socket_call_model [] := by
  refine ⟨?_, ?_, ?_⟩ <;> options_norm

/-! ### The two witnesses

Each names, for the option calls, the outcome its arm is proved to
satisfy; every one below is an outcome Linux produces on that input, and
the known-level cells are the declines. -/

/-- Open the two witnesses and the gates, and decide what is closed. -/
scoped macro "options_witness_open" cfg:Lean.Parser.Tactic.optConfig : tactic =>
  `(tactic| simp $cfg:optConfig only [setsockopt_witness, getsockopt_witness,
      ret_outcome, outcome_copyins, with_copyins, sock_fd, sock_level_known, int32_neg,
      Bool.and_eq_true, Bool.or_eq_true, ne_eq, reduceCtorEq, sys_simp, ↓reduceIte])

/-- Evaluate a closed call of one of the two option witnesses. -/
scoped macro "options_witness_norm" : tactic =>
  `(tactic| (options_witness_open +decide;
             first | done | sys_simp_pass +ground +decide -failIfUnchanged;
             first | done | options_witness_open +ground +decide))

/-- setsockopt's witness, arm by arm: -EBADF on the closed 11, -ENOTSOCK on
the file at 3, -EINVAL on the `int` -1 whatever the level, -ENOPROTOOPT on
the unknown level 999 on a fresh and on a connected socket, `Unmodeled` on
SOL_SOCKET, SOL_IP and SOL_TCP.
kernel: net/socket.c:__sys_setsockopt,do_sock_setsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt@v6.18.46 -/
theorem setsockopt_witness_names_each_arm :
    setsockopt_witness 11 999 4 socket_states_model
      = Ok (mkEffect (errno_ret EBADF) [] []) socket_states_model [] ∧
    setsockopt_witness 3 999 4 socket_states_model
      = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_states_model [] ∧
    setsockopt_witness 6 999 (Z_to_bv 64 (2 ^ 64 - 1)) socket_states_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) socket_states_model [] ∧
    setsockopt_witness 6 6 (Z_to_bv 64 (2 ^ 64 - 1)) socket_states_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) socket_states_model [] ∧
    setsockopt_witness 6 999 4 socket_states_model
      = Ok (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model [] ∧
    setsockopt_witness 9 999 0 socket_states_model
      = Ok (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model [] ∧
    setsockopt_witness 6 1 4 socket_states_model = Unmodeled ∧
    setsockopt_witness 7 0 4 socket_states_model = Unmodeled ∧
    setsockopt_witness 8 6 4 socket_states_model = Unmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> options_witness_norm

/-- getsockopt's witness, arm by arm: -EBADF and -ENOTSOCK with nothing
read even over a readable `optlen`, -EOPNOTSUPP with the four bytes
ledgered on the unknown level over a readable `optlen` and bare over an
unreadable one, on a fresh and on a connected socket, and `Unmodeled` on
the three known levels, ledger or no ledger.
kernel: net/socket.c:__sys_getsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:do_ip_getsockopt@v6.18.46 -/
theorem getsockopt_witness_names_each_arm :
    getsockopt_witness 11 999 4096 (getsockopt_in 11 999 2 4104 4096 optlen_minus_one_mem)
      socket_states_model = Ok (mkEffect (errno_ret EBADF) [] []) socket_states_model [] ∧
    getsockopt_witness 3 999 4096 (getsockopt_in 3 999 2 4104 4096 optlen_minus_one_mem)
      socket_states_model = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_states_model [] ∧
    getsockopt_witness 6 999 4096 (getsockopt_in 6 999 2 4104 4096 optlen_minus_one_mem)
      socket_states_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4096, 4)])
           socket_states_model [] ∧
    getsockopt_witness 9 999 4096 (getsockopt_in 9 999 2 4104 4096 optlen_minus_one_mem)
      socket_states_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4096, 4)])
           socket_states_model [] ∧
    getsockopt_witness 6 999 8192 (getsockopt_in 6 999 2 4096 8192 sockaddr_in_any_mem)
      socket_states_model = Ok (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model [] ∧
    getsockopt_witness 6 1 4096 (getsockopt_in 6 1 2 4104 4096 optlen_minus_one_mem)
      socket_states_model = Unmodeled ∧
    getsockopt_witness 7 0 8192 (getsockopt_in 7 0 1 4096 8192 sockaddr_in_any_mem)
      socket_states_model = Unmodeled ∧
    getsockopt_witness 8 6 4096 (getsockopt_in 8 6 1 4104 4096 optlen_minus_one_mem)
      socket_states_model = Unmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> options_witness_norm

/-! ## socket and accept4: the checkers that hand back a descriptor

The two lifecycle checkers ported by ticket C-Net-Socket-socket-accept4,
appended below the options section.  What is pinned: the three rows
(`socket`, `accept`, `accept4`) and their `_row_is_the_arm` theorems;
Rocq's closed `check_syscall` examples for 198 and 242, restated on the
row with `check_` in front of their names; the leaves of both checkers
on closed calls, with refused lies beside the answers; and stores beside
the acceptors the two reach, refused (`check_socket_stores_nothing`,
`check_accept4_stores_nothing`).

THE ROCQ MAPPING.  What is not restated is Rocq's FILTERS —
`accept_errno_set_is_exactly_these_three`,
`accept_success_return_is_exactly_the_lowest_free_fd`,
`accept_at_the_wrap_hands_over_no_descriptor_at_all`,
`accept_one_below_the_wrap_still_hands_over`,
`accept_at_the_wrap_errno_set_is_still_exactly_these_three` and
`accept_at_the_wrap_never_declines` — which run the checker over every
value the error window or the 4096-candidate scan can name.  Here the spec
file's `iff`s (`accept4_listening_iff`, `accept_at_the_wrap_iff`,
`accept_one_below_the_wrap_iff`) state each over every outcome,
`check_accept4_sound_ok` and `check_accept4_complete_ok` carry them to
the checker, and the pins name the members and the nearest refused
neighbours.  Like the file header's
list, this one is prose, and nothing reads it.

THE MODEL IS AN OUTPUT here too.  A success binds the new descriptor at
the head of the table, and accept's also pops the queue and advances the
channel counter (`State.with_accepted`), so each success pin names the
model the checker returns: the spec file's `socket_created_model`,
`socket_hole_filled_model`, `accepted_socket_model` and
`last_usable_accepted_model`, and this file's `stdin_closed_socket_model`
and `stdin_closed_accepted_model`.  Those fixtures all read the silent
network, whose every connection is the same one and whose tail is itself,
so on them a checker that read a constant peer or left the queue alone
would still pass, and so would a `with_accepted` that moved the counter
by another step, since the accepted ones are built through it.
`check_accept_hands_over_a_scripted_head` is the pin that catches those:
a queue of two different connections, and post-states written field by
field.  A checker that left the table alone fails the success pins, each
of whose post-states holds the new descriptor.

THE PREMISES UNDER THE REFUSALS.  A `kernel:` pin below that refuses an
answer argues from Linux's source that Linux does not give it in the
environment the model quantifies over, and claims no other supported
implementation gives it there either; a docstring below that says Linux
does not give an answer means that environment.  Premises bound it, and
no pin states them; among them:
- No seccomp filter answers the call: a `SECCOMP_RET_ERRNO` filter
  answers any errno it names (`__seccomp_filter`, kernel/seccomp.c:1259,
  at :1279-1285, Linux v6.18.46).  The model states this premise nowhere
  else.
- No return is overridden.  `__SYSCALL_DEFINEx` emits
  `ALLOW_ERROR_INJECTION(..., ERRNO)` for the syscall it defines
  (arch/riscv/include/asm/syscall_wrapper.h:84, Linux v6.18.46), socket,
  accept and accept4 among them, which on a kernel built with
  `CONFIG_FUNCTION_ERROR_INJECTION` puts it on the error-injection list
  (include/asm-generic/error-injection.h:20-40, Linux v6.18.46), so a
  `BPF_MODIFY_RETURN` program can answer the call for the kernel, and
  `bpf_override_return` and `fail_function` are two more routes, each
  behind an option of its own.  The note on `sched_yield_spec`
  (`Sys/Kernel/Sched/Syscalls.lean`) walks the three routes and their
  reach, and names the first two's options; `fail_function`'s is
  `CONFIG_FAIL_FUNCTION` (lib/Kconfig.debug:2059-2061, Linux v6.18.46).
- No tracer rewrites the return: the closed world of the README's
  "Signals and outside control" row and of
  bugs/access-okb-closed-world.md.  A tracer that attaches with
  `PTRACE_SEIZE` sends the tracee no SIGSTOP (`ptrace_set_stopped`,
  kernel/ptrace.c:388, at :392-394, Linux v6.18.46), so the no-signal
  premise below does not cover it.
- No LSM denies the call, which the spec's note on `sock_fd` puts outside
  the modeled environment.
- No signal is delivered, the premise `Sys/Kernel/Signal.lean`'s header
  names; without it accept's -EINTR is a real answer
  (`check_accept_refuses_errnos_outside_the_set` says how).
- No BPF program is attached to `update_socket_protocol`
  (net/socket.c:1736-1739, Linux v6.18.46), which the spec's note on that
  hook puts outside the modeled environment, and which could hand
  socket's later gates a protocol other than the argument
  (`check_socket_protocol_range_is_einval`,
  `check_socket_still_answers_its_pure_argument_errors` and
  `check_socket_sign_bit_is_negative` refuse on that premise).
- No socket was inherited on fds 0 to 2.  `State.init_model` starts the
  process with a channel on each, the direction piped stdio has;
  bugs/channel-fds-assume-unidirectional-stdio.md puts a program that
  reads its connection from fd 0 outside the modeled environment, and
  Rocq's note on `FdChannel` (`State.v`) names that direction an
  assumption about the environment.  Under inetd's `nowait` fd 0 is a
  connected socket, whose accept is the not-listening -EINVAL
  (`inet_csk_accept`, net/ipv4/inet_connection_sock.c:649, at :662-664,
  Linux v6.18.46), the answer
  `check_accept4_is_enotsock_on_every_non_socket_fd_kind` refuses on fd 0.
- Nothing outside the model acts on a socket the model holds.  `clone`
  and `clone3` decline while the table holds one
  (`clone_no_shared_file_b`, `Sys/Kernel/Fork.lean`), so a child the
  model creates does not inherit one; but another process, or a child
  forked before the socket was made, can take the same file through
  `pidfd_getfd` when the ptrace access check in `__pidfd_fget`
  (kernel/pid.c:830, at :839, Linux v6.18.46) lets it, and set O_NONBLOCK
  on it (`setfl`, fs/fcntl.c:83, Linux v6.18.46), which `do_accept` hands
  the listener's accept (net/socket.c:1988, Linux v6.18.46), so that an
  empty queue is -EAGAIN.  And on a kernel built with
  `CONFIG_INET_DIAG_DESTROY`, a process holding `CAP_NET_ADMIN` over the
  socket's network namespace needs no access to this process to stop the
  listener (`sock_diag_destroy`, net/core/sock_diag.c:313, at :315, Linux
  v6.18.46; `tcp_abort`, net/ipv4/tcp.c:5047, at :5081-5084, Linux
  v6.18.46), whose accept is then -EINVAL.  Nor, from v6.5 on, does
  stopping it need that option: a BPF program on the TCP socket iterator
  can call the kfunc `bpf_sock_destroy` (net/core/filter.c:12502,
  at :12515, Linux v6.18.46; v6.4 has no such kfunc), which reaches the
  same `tcp_abort` through `tcp_prot` (net/ipv4/tcp_ipv4.c:3503,
  at :3550, Linux v6.18.46).
HOW THESE ARE PROVED.  `alloc_norm` is `check_norm` over the two
checkers: the same three passes, opening the three rows, the two checkers,
the acceptors — `check_ret_only`, `check_errno_only` and
`Checks/Sys/Fs/Open.lean`'s `check_new_fd_result` — and the counter's
guard `conn_ix_exhausted`, and deciding what is closed; its own macro for
the options section's reason.  The witness pins run `alloc_witness_norm`.
None of them is `rfl`, for the header's reason. -/

def check_socket_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_socket (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m

def check_accept_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_accept4 (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) eff m

def check_accept4_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_accept4 (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m

/-- socket's row: the three registers whole — `SYSCALL_DEFINE3(socket, int,
family, int, type, int, protocol)` (net/socket.c:1760, Linux v6.18.46)
takes three `int`s, and the spec narrows each itself (`sint32` on the
family and the protocol, `abi_low32` on the type), so a row that narrowed
them again would change nothing and a row that dropped one fails here.
kernel: net/socket.c:socket,__sys_socket@v6.18.46 -/
theorem socket_row_is_the_arm (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_socket_row i eff m = CheckOk m' evs) :
    (Sys.Registry.Net.Socket.socket_arm).sa_spec i m (Ok eff m' evs) :=
  check_socket_sound_ok _ _ _ _ _ _ _ _ h

/-- accept's row: a0 through `fd32`, a1 and a2 whole, and the flags the
literal 0 `SYSCALL_DEFINE3(accept, …)` (net/socket.c:2068, Linux v6.18.46)
hands `__sys_accept4` — a3 is not read, which
`check_accept_ignores_a3` below holds at a value that would change the
answer.
kernel: net/socket.c:accept,__sys_accept4@v6.18.46 -/
theorem accept_row_is_the_arm (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_accept_row i eff m = CheckOk m' evs) :
    (Sys.Registry.Net.Socket.accept_arm).sa_spec i m (Ok eff m' evs) :=
  check_accept4_sound_ok _ _ _ _ _ _ _ _ _ h

/-- accept4's row: a0 through `fd32`, a1..a3 whole; `SYSCALL_DEFINE4(accept4,
int, fd, …, int, flags)` (net/socket.c:2062, Linux v6.18.46) takes the
flags as an `int` too, and the spec narrows them itself (`abi_low32`).
kernel: net/socket.c:accept4,__sys_accept4@v6.18.46 -/
theorem accept4_row_is_the_arm (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_accept4_row i eff m = CheckOk m' evs) :
    (Sys.Registry.Net.Socket.accept4_arm).sa_spec i m (Ok eff m' evs) :=
  check_accept4_sound_ok _ _ _ _ _ _ _ _ _ h

/-- Open the three rows, the two checkers, the acceptors and the counter's
guard, and decide what is closed; `scoped` for `check_open`'s reason. -/
scoped macro "alloc_open" cfg:Lean.Parser.Tactic.optConfig : tactic =>
  `(tactic| simp $cfg:optConfig only [check_socket_row, check_accept_row, check_accept4_row,
      check_socket, check_accept4, check_new_fd_result, check_errno_only, check_ret_only,
      errno_ret_in, conn_ix_exhausted,
      Bool.and_eq_true, Bool.or_eq_true, bv_eqb_eq,
      check_result.CheckOk.injEq, ne_eq, reduceCtorEq, sys_simp, ↓reduceIte])

/-- Evaluate a closed call of `socket` or `accept4`, the way `check_norm`
evaluates a lifecycle one. -/
scoped macro "alloc_norm" : tactic =>
  `(tactic| (alloc_open +decide;
             first | done | sys_simp_pass +ground +decide -failIfUnchanged;
             first | done | alloc_open +ground +decide))

/-! ### socket: the flags, the family, the type, the protocol, the descriptor

`__sys_socket_create` (net/socket.c:1686, Linux v6.18.46) refuses an
unknown flag bit first (:1697-1698); `__sock_create` (net/socket.c:1535,
Linux v6.18.46) refuses the family range, then the type range
(:1545-1548); `inet_create` (net/ipv4/af_inet.c:254, Linux v6.18.46)
refuses the protocol range (:265-266) and walks `inetsw` (:272-291); and
`sock_map_fd` (net/socket.c:504, Linux v6.18.46) reserves the descriptor
last.  The fixture is `listening_socket_model`, whose lowest free
descriptor is 4. -/

/-- THE HAND-OVER: `socket(AF_INET, SOCK_STREAM, 0)` on the listening
fixture is the lowest free descriptor, 4, bound to a fresh socket at the
head of the table — the first conjunct names that model — and the call is
modeled.  5, a free descriptor that is not the lowest, and 3, the open
listener, are lies: `alloc_fd` (fs/file.c:570, Linux v6.18.46) scans from
the bottom and hands out only an empty slot.
kernel: net/socket.c:__sys_socket,sock_map_fd; fs/file.c:alloc_fd@v6.18.46 -/
theorem check_socket_hands_over_the_lowest_free_fd :
    check_socket_row (socket_in 2 1 0) (mkEffect 4 [] []) listening_socket_model
      = CheckOk socket_created_model [] ∧
    check_socket_row (socket_in 2 1 0) (mkEffect 4 [] []) listening_socket_model
      ≠ CheckUnmodeled ∧
    check_socket_row (socket_in 2 1 0) (mkEffect 5 [] []) listening_socket_model
      = CheckReject ∧
    check_socket_row (socket_in 2 1 0) (mkEffect 3 [] []) listening_socket_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> alloc_norm

/-- THE THREE FAILURES, each leaving the table alone.  -EMFILE comes from
`alloc_fd` (fs/file.c:570, Linux v6.18.46, at :591-593) once the new
number reaches `RLIMIT_NOFILE`, which for fd 4 means a limit of 4 or
less, and the fixture records a limit of 1024 (`m_nofile_fixture_of`,
`Checks/Cases/Prelude.lean`).  So here -EMFILE takes something outside the
process: another process lowering the limit with `prlimit64`, which
`check_prlimit_permission` (kernel/sys.c:1707, at :1717-1724, Linux
v6.18.46) allows when the caller's real uid and gid equal each of the
target's real, effective and saved ones, or the caller holds
`CAP_SYS_RESOURCE` in the target's user namespace, and whose store is in
`do_prlimit` (:1536); or, from v6.1, the cgroup program of the next pin
answering -EMFILE itself through `bpf_set_retval`
(kernel/bpf/cgroup.c:1839, Linux v6.18.46).  -ENOMEM comes from
`sk_alloc` in `inet_create`
(net/ipv4/af_inet.c:327-330, same version) or from `sock_alloc_file` in
`sock_map_fd` (net/socket.c:513), whose `alloc_file_pseudo` fails with it
in `alloc_path_pseudo` (fs/file_table.c:397-402) or `alloc_empty_file`
(:260).  -ENFILE comes from `sock_alloc` in `__sock_create`
(net/socket.c:1570-1575) or from `alloc_empty_file`'s file limit
(fs/file_table.c:278).  The descriptor table does not grow for fd 4:
`alloc_fd` calls `expand_files` only once the number reaches `max_fds`
(fs/file.c:595-601), and no table is smaller than `NR_OPEN_DEFAULT`
(fs/file.c:401 in `dup_fd`; include/linux/fdtable.h:24), 64 on riscv64.
kernel: fs/file.c:alloc_fd,dup_fd; net/socket.c:__sock_create,sock_map_fd,sock_alloc_file; net/ipv4/af_inet.c:inet_create; fs/file_table.c:alloc_path_pseudo,alloc_empty_file@v6.18.46 -/
theorem check_socket_errno_arms_leave_the_table_alone :
    check_socket_row (socket_in 2 1 0) (mkEffect (errno_ret EMFILE) [] []) listening_socket_model
      = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 2 1 0) (mkEffect (errno_ret ENOMEM) [] []) listening_socket_model
      = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 2 1 0) (mkEffect (errno_ret ENFILE) [] []) listening_socket_model
      = CheckOk listening_socket_model [] := by
  refine ⟨?_, ?_, ?_⟩ <;> alloc_norm

/-- -EPERM IS REFUSED, AND THE REFUSAL IS THE SPEC'S GAP: Linux can answer
it here.  `inet_create` (net/ipv4/af_inet.c:254, Linux v6.18.46) raises
-EPERM itself only for SOCK_RAW without CAP_NET_RAW (:315-318), but on
SOCK_STREAM a cgroup `inet_sock_create` program answers it too, which
`BPF_CGROUP_RUN_PROG_INET_SOCK` runs in `inet_create`
(net/ipv4/af_inet.c:391-394, Linux v6.18.46).  The spec's LSM note names
the cgroups only for their sockopt programs, so the refusal pinned here
is the spec's, and the premise that would justify it is the spec's to
state.  A denying LSM hook, `security_socket_create` or
`security_socket_post_create` in `__sock_create` (net/socket.c:1561 and
:1629, Linux v6.18.46), and a seccomp `SECCOMP_RET_ERRNO` filter answer
it as well, but those two are premises of the environment the section
header bounds, and the cgroup program is not.
model: the spec's refusal of -EPERM on socket(AF_INET, SOCK_STREAM, 0), which Linux answers under a cgroup inet_sock_create program; a gap restated on the checker so that closing it is a visible flip -/
theorem check_socket_refuses_the_hook_eperm :
    check_socket_row (socket_in 2 1 0) (mkEffect (errno_ret EPERM) [] []) listening_socket_model
      = CheckReject := by
  alloc_norm

/-- THE LOWEST FREE NUMBER FILLS A HOLE: with 3 closed and 4 open the new
socket is 3, not 5 — the probe's `close` followed by a second `socket` —
and 5 and the open 4 are refused.
kernel: fs/file.c:alloc_fd; net/socket.c:sock_map_fd@v6.18.46 -/
theorem check_socket_fills_the_hole :
    check_socket_row (socket_in 2 1 0) (mkEffect 3 [] []) socket_hole_model
      = CheckOk socket_hole_filled_model [] ∧
    check_socket_row (socket_in 2 1 0) (mkEffect 5 [] []) socket_hole_model = CheckReject ∧
    check_socket_row (socket_in 2 1 0) (mkEffect 4 [] []) socket_hole_model = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> alloc_norm

/-- SOCKET STORES NOTHING: its three arguments are integers and it takes
no user pointer (`SYSCALL_DEFINE3(socket, int, family, int, type, int,
protocol)`, net/socket.c:1760, Linux v6.18.46), so a store or a zeroed
range beside the descriptor, beside an allocation errno or beside a
gate's errno is refused — each kind of acceptor the checker reaches
(`check_new_fd_result`, `check_ret_only`) refuses a ledger.
kernel: net/socket.c:socket,__sys_socket; fs/file.c:alloc_fd; net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem check_socket_stores_nothing :
    check_socket_row (socket_in 2 1 0) (mkEffect 4 [(4096, [4, 0, 0, 0])] [])
      listening_socket_model = CheckReject ∧
    check_socket_row (socket_in 2 1 0) (mkEffect 4 [] [(4096, 16)]) listening_socket_model
      = CheckReject ∧
    check_socket_row (socket_in 2 1 0) (mkEffect (errno_ret EMFILE) [(4096, [0])] [])
      listening_socket_model = CheckReject ∧
    check_socket_row (socket_in 2 1 263) (mkEffect (errno_ret EINVAL) [(4096, [0])] [])
      listening_socket_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> alloc_norm

/-- SOCK_CLOEXEC changes nothing the model carries: it reaches the new
descriptor's close-on-exec bit through `sock_map_fd`, which no arm reads,
so `SOCK_STREAM | SOCK_CLOEXEC` lands on the plain call's state.
kernel: net/socket.c:__sys_socket,__sys_socket_create,sock_map_fd@v6.18.46 -/
theorem check_socket_cloexec_changes_nothing :
    check_socket_row (socket_in 2 524289 0) (mkEffect 4 [] []) listening_socket_model
      = CheckOk socket_created_model [] := by
  alloc_norm

/-- THE THREE ARGUMENTS ARE 32 BITS: a register-negative family whose low
half is AF_INET, and a type and protocol with garbage above bit 31, are
the call `(2, 1, 6)` and hand over 4.  The narrowing is the spec's, on the
whole register the row hands it; 5 is still refused.
kernel: net/socket.c:socket,__sys_socket@v6.18.46 -/
theorem check_socket_arguments_are_32_bits :
    check_socket_row (socket_in (Z_to_bv 64 (-(2 ^ 32) + 2)) (Z_to_bv 64 (2 ^ 32 + 1))
                                (Z_to_bv 64 (2 ^ 32 + 6)))
      (mkEffect 4 [] []) listening_socket_model = CheckOk socket_created_model [] ∧
    check_socket_row (socket_in (Z_to_bv 64 (-(2 ^ 32) + 2)) (Z_to_bv 64 (2 ^ 32 + 1))
                                (Z_to_bv 64 (2 ^ 32 + 6)))
      (mkEffect 5 [] []) listening_socket_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> alloc_norm

/-- AN UNKNOWN FLAG BIT IS -EINVAL, and it is answered before the family,
the type and the protocol are read: `__sys_socket_create` tests
`type & ~SOCK_TYPE_MASK & ~(SOCK_CLOEXEC|SOCK_NONBLOCK)` first
(net/socket.c:1697-1698, Linux v6.18.46).  So `socket(AF_INET,
SOCK_STREAM|0x100, IPPROTO_UDP)` is -EINVAL and not the walk's answer,
and the same bit beside SOCK_NONBLOCK is -EINVAL too, the unknown bit
being tested before SOCK_NONBLOCK is looked at.
kernel: net/socket.c:__sys_socket_create@v6.18.46 -/
theorem check_socket_flag_bit_is_einval_first :
    check_socket_row (socket_in 2 257 17) (mkEffect (errno_ret EINVAL) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 2 2305 0) (mkEffect (errno_ret EINVAL) [] [])
      listening_socket_model = CheckOk listening_socket_model [] := by
  refine ⟨?_, ?_⟩ <;> alloc_norm

/-- …and the walk's answer is refused at that input, since the flag test
answers first.
kernel: net/socket.c:__sys_socket_create; net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem check_socket_flag_bit_refuses_the_walk_answer :
    check_socket_row (socket_in 2 257 17)
      (mkEffect (errno_ret EPROTONOSUPPORT) [] []) listening_socket_model = CheckReject := by
  alloc_norm

/-- SOCK_NONBLOCK DECLINES: the model has no O_NONBLOCK to set on the new
file, so neither the descriptor nor an errno is the checker's to accept.
kernel: net/socket.c:__sys_socket,sock_map_fd; fs/file.c:alloc_fd@v6.18.46 -/
theorem check_socket_nonblock_declines :
    check_socket_row (socket_in 2 2049 0) (mkEffect 4 [] []) listening_socket_model
      = CheckUnmodeled ∧
    check_socket_row (socket_in 2 2049 0) (mkEffect (errno_ret EMFILE) [] [])
      listening_socket_model = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> alloc_norm

/-- THE FAMILY RANGE, then the type range: family 46 (`NPROTO`, which
include/uapi/linux/net.h defines as include/linux/socket.h's `AF_MAX`: 46
at v6.18.46, 45 from v4.18 through v5.14, 44 at v4.17) and the
register-negative family -1 are -EAFNOSUPPORT, before the type range —
family 46 with type 11 is -EAFNOSUPPORT, not -EINVAL; type 11 (SOCK_MAX)
and 15 on AF_INET are -EINVAL, and so is type 11 on AF_UNIX, whose
registration does not matter here, because the range is tested before
the family's entry is looked up (net/socket.c:1545-1548, Linux v6.18.46).
The verdicts here are the same at `AF_MAX` 44 and 45: the families they
name, 1, 2, 46 and -1, sit on the same side of each.  The older
values open cells this pin does not reach: families 44 and 45 with an
out-of-range type are -EAFNOSUPPORT where `AF_MAX` is at or below them, and
the spec, whose `NPROTO` is the constant 46 (`Sys/Uapi/Net.lean`),
proves -EINVAL certain there.  That is the spec's inherited gap, and no
pin here or in the spec's Cases file asserts one of those cells.
kernel: net/socket.c:__sock_create@v6.18.46 -/
theorem check_socket_family_then_type_range :
    check_socket_row (socket_in 46 1 0) (mkEffect (errno_ret EAFNOSUPPORT) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in (Z_to_bv 64 (2 ^ 64 - 1)) 1 0)
      (mkEffect (errno_ret EAFNOSUPPORT) [] []) listening_socket_model
      = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 46 11 0) (mkEffect (errno_ret EAFNOSUPPORT) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 46 11 0) (mkEffect (errno_ret EINVAL) [] [])
      listening_socket_model = CheckReject ∧
    check_socket_row (socket_in 2 11 0) (mkEffect (errno_ret EINVAL) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 2 15 0) (mkEffect (errno_ret EINVAL) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 1 11 0) (mkEffect (errno_ret EINVAL) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 2 11 0) (mkEffect (errno_ret EAFNOSUPPORT) [] [])
      listening_socket_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> alloc_norm

/-- A FAMILY IN RANGE OTHER THAN AF_INET DECLINES.  AF_UNIX (1) is
answered by whatever the kernel build registered in `net_families`
(net/socket.c:229, Linux v6.18.46), or, where the family is a module,
by the one `__sock_create` asks for (net/socket.c:1586-1587,
Linux v6.18.46); CONFIG_UNIX is a bool at v6.18.46 and a tristate at
v5.15 (net/unix/Kconfig).  Family 45 (AF_MCTP; CONFIG_MCTP,
net/mctp/Kconfig) is answered the same way from v5.15 on.  So for
neither is the descriptor or -EAFNOSUPPORT the checker's to accept.
AF_UNSPEC (0) is -EAFNOSUPPORT at v6.18.46: no `net_proto_family` in
that tree names family 0 (their family fields, read under net/), so
the lookup finds nothing (net/socket.c:1586-1594, Linux v6.18.46), and
it declines only because `socket_spec` declines any family other than
AF_INET — a priority-3 cost, not a kernel ambiguity.  Below v5.15, 45 is past `AF_MAX` and -EAFNOSUPPORT
too, which the decline covers as well.
kernel: net/socket.c:__sock_create@v6.18.46 -/
theorem check_socket_other_families_decline :
    check_socket_row (socket_in 1 1 0) (mkEffect 4 [] []) listening_socket_model
      = CheckUnmodeled ∧
    check_socket_row (socket_in 1 1 0) (mkEffect (errno_ret EAFNOSUPPORT) [] [])
      listening_socket_model = CheckUnmodeled ∧
    check_socket_row (socket_in 0 1 0) (mkEffect (errno_ret EAFNOSUPPORT) [] [])
      listening_socket_model = CheckUnmodeled ∧
    check_socket_row (socket_in 45 1 0) (mkEffect (errno_ret EAFNOSUPPORT) [] [])
      listening_socket_model = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> alloc_norm

/-- THE PROTOCOL RANGE on SOCK_STREAM: 263 (IPPROTO_MAX), the
register-negative -1 and `2^32 + 263` (263 after the narrowing) are
-EINVAL, and -EPROTONOSUPPORT, the walk's answer, is the lie
(net/ipv4/af_inet.c:265-266, Linux v6.18.46).
kernel: net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem check_socket_protocol_range_is_einval :
    check_socket_row (socket_in 2 1 263) (mkEffect (errno_ret EINVAL) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 2 1 (Z_to_bv 64 (2 ^ 64 - 1))) (mkEffect (errno_ret EINVAL) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 2 1 (Z_to_bv 64 (2 ^ 32 + 263)))
      (mkEffect (errno_ret EINVAL) [] []) listening_socket_model
      = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 2 1 263) (mkEffect (errno_ret EPROTONOSUPPORT) [] [])
      listening_socket_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> alloc_norm

/-- Rocq's `socket_packet_declines_at_every_protocol`: SOCK_PACKET is
decided above the protocol range — `__sock_create` rewrites the family to
PF_PACKET for it before `inet_create` runs — so -EINVAL at protocol 0, -1
and 263, and -EPERM, are declined; SOCK_DGRAM at the same -1 still
takes the range and answers -EINVAL.
kernel: net/socket.c:__sock_create; net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem check_socket_packet_declines_at_every_protocol :
    check_socket_row (socket_in 2 10 0) (mkEffect (errno_ret EINVAL) [] []) listening_socket_model
      = CheckUnmodeled ∧
    check_socket_row (socket_in 2 10 4294967295) (mkEffect (errno_ret EINVAL) [] [])
      listening_socket_model = CheckUnmodeled ∧
    check_socket_row (socket_in 2 10 263) (mkEffect (errno_ret EINVAL) [] [])
      listening_socket_model = CheckUnmodeled ∧
    check_socket_row (socket_in 2 10 4294967295) (mkEffect (errno_ret EPERM) [] [])
      listening_socket_model = CheckUnmodeled ∧
    check_socket_row (socket_in 2 2 4294967295) (mkEffect (errno_ret EINVAL) [] [])
      listening_socket_model = CheckOk listening_socket_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> alloc_norm

/-- Rocq's `socket_dgram_and_raw_still_take_the_protocol_range`: SOCK_DGRAM
and SOCK_RAW keep AF_INET into `inet_create`, so the protocol range is
-EINVAL for them, and SOCK_DGRAM inside the range declines: it would
succeed with a UDP socket, a protocol the model does not have.
kernel: net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem check_socket_dgram_and_raw_still_take_the_protocol_range :
    check_socket_row (socket_in 2 2 4294967295) (mkEffect (errno_ret EINVAL) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 2 3 263) (mkEffect (errno_ret EINVAL) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 2 2 0) (mkEffect (errno_ret EINVAL) [] [])
      listening_socket_model = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_⟩ <;> alloc_norm

/-- SCTP (132) and MPTCP (262) under SOCK_STREAM, and SOCK_SEQPACKET,
are each answered by what the kernel build registered, so their
-EPROTONOSUPPORT or -ESOCKTNOSUPPORT is declined;
UDP under SOCK_STREAM and SOCK_RDM, which no AF_INET protosw in the
v6.18.46 tree registers (the `inet_register_protosw` callers under net/
register types 1, 2, 3 and 5, and no type-1 entry takes protocol 17),
are still answered.  SOCK_DCCP declines on account of the older supported
kernels that could build DCCP, whose module registered `dccp_v4_protosw`
with type SOCK_DCCP (read at v5.4 and v6.15, in the ipv4.c of the DCCP
directory those trees have): at v6.18.46 the tree has no `net/dccp`
directory and no type-6 protosw, so type 6 is -ESOCKTNOSUPPORT there,
the spec twin's priority-3 cost.  SMC (256) is answered, not declined:
the pin below this one states it with the rest of 256-262.
kernel: net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem check_socket_kernel_build_answers_are_declined :
    check_socket_row (socket_in 2 1 132) (mkEffect (errno_ret EPROTONOSUPPORT) [] [])
      listening_socket_model = CheckUnmodeled ∧
    check_socket_row (socket_in 2 1 262) (mkEffect (errno_ret EPROTONOSUPPORT) [] [])
      listening_socket_model = CheckUnmodeled ∧
    check_socket_row (socket_in 2 5 0) (mkEffect (errno_ret ESOCKTNOSUPPORT) [] [])
      listening_socket_model = CheckUnmodeled ∧
    check_socket_row (socket_in 2 6 0) (mkEffect (errno_ret ESOCKTNOSUPPORT) [] [])
      listening_socket_model = CheckUnmodeled ∧
    check_socket_row (socket_in 2 1 17) (mkEffect (errno_ret EPROTONOSUPPORT) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 2 4 0) (mkEffect (errno_ret ESOCKTNOSUPPORT) [] [])
      listening_socket_model = CheckOk listening_socket_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> alloc_norm

/-- PROTOCOLS 256-262 ARE INSIDE THE PROTOCOL RANGE: `IPPROTO_MAX` is the
enumerator after `IPPROTO_MPTCP`, 263 (include/uapi/linux/in.h:88-90,
Linux v6.18.46), so `inet_create`'s range test lets 256, 257 and 261
through to the `inetsw` walk, which answers -EPROTONOSUPPORT for each;
262 is IPPROTO_MPTCP and declines with SCTP, the pin above; on types the
walk never reaches, 4 and 0, the last arm answers -ESOCKTNOSUPPORT at 256
and at 262 alike.  255 and 263 on either side of the band keep their
answers, and -ENFILE, which no validation arm offers, is refused on each
of the three: the errno pool is the descriptor arm's alone.
kernel: net/socket.c:__sock_create; net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem check_socket_protocols_above_255_are_answered :
    check_socket_row (socket_in 2 1 257) (mkEffect (errno_ret EPROTONOSUPPORT) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 2 1 257) (mkEffect (errno_ret EINVAL) [] [])
      listening_socket_model = CheckReject ∧
    check_socket_row (socket_in 2 1 256) (mkEffect (errno_ret EPROTONOSUPPORT) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 2 1 256) (mkEffect 4 [] []) listening_socket_model
      = CheckReject ∧
    check_socket_row (socket_in 2 1 (Z_to_bv 64 (2 ^ 32 + 261)))
      (mkEffect (errno_ret EPROTONOSUPPORT) [] []) listening_socket_model
      = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 2 4 256) (mkEffect (errno_ret ESOCKTNOSUPPORT) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 2 0 262) (mkEffect (errno_ret ESOCKTNOSUPPORT) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 2 0 262) (mkEffect (errno_ret EINVAL) [] [])
      listening_socket_model = CheckReject ∧
    check_socket_row (socket_in 2 1 255) (mkEffect (errno_ret EPROTONOSUPPORT) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 2 1 255) (mkEffect (errno_ret EINVAL) [] [])
      listening_socket_model = CheckReject ∧
    check_socket_row (socket_in 2 4 255) (mkEffect (errno_ret ESOCKTNOSUPPORT) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 2 4 263) (mkEffect (errno_ret EINVAL) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 2 1 255) (mkEffect (errno_ret ENFILE) [] [])
      listening_socket_model = CheckReject ∧
    check_socket_row (socket_in 2 4 255) (mkEffect (errno_ret ENFILE) [] [])
      listening_socket_model = CheckReject ∧
    check_socket_row (socket_in 2 4 263) (mkEffect (errno_ret ENFILE) [] [])
      listening_socket_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> alloc_norm

/-- Rocq's `socket_still_answers_its_pure_argument_errors`: UDP under
SOCK_STREAM is -EPROTONOSUPPORT, and SOCK_RDM (4) and type 0, whose
`inetsw` lists no in-tree protosw fills at v6.18.46 (the pin above says
which types those fill), are -ESOCKTNOSUPPORT; the success the fixture
would allow is refused on each.
kernel: net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem check_socket_still_answers_its_pure_argument_errors :
    check_socket_row (socket_in 2 1 17) (mkEffect (errno_ret EPROTONOSUPPORT) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 2 4 0) (mkEffect (errno_ret ESOCKTNOSUPPORT) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 2 0 0) (mkEffect (errno_ret ESOCKTNOSUPPORT) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 2 1 17) (mkEffect 4 [] []) listening_socket_model
      = CheckReject ∧
    check_socket_row (socket_in 2 4 0) (mkEffect 4 [] []) listening_socket_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> alloc_norm

/-! ### accept and accept4: the fd, the flags, the socket, the state, the counter

`__sys_accept4` (net/socket.c:2051, Linux v6.18.46) resolves the fd first
(:2054-2057); `__sys_accept4_file` (net/socket.c:2012, Linux v6.18.46)
refuses an unknown flag bit (:2019-2020); `do_accept` (net/socket.c:1952,
Linux v6.18.46) answers -ENOTSOCK (:1962-1964); `inet_csk_accept`
(net/ipv4/inet_connection_sock.c:649, Linux v6.18.46) is -EINVAL off
TCP_LISTEN (:662-664) and otherwise dequeues the head connection. -/

/-- Rocq's `accept_hands_over_the_head_connection`: on the listening
fixture `accept4(3, NULL, NULL, 0)` is 4, carrying the head connection's
peer on channel 3 with the queue advanced and the counter at 1 — the
whole post-state in one equality — and `accept(3, NULL, NULL)` is the same
call.  The call is modeled.
kernel: net/socket.c:do_accept,__sys_accept4_file; net/ipv4/inet_connection_sock.c:inet_csk_accept@v6.18.46 -/
theorem check_accept_hands_over_the_head_connection :
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect 4 [] []) listening_socket_model
      = CheckOk accepted_socket_model [] ∧
    check_accept_row (accept_in 3 0 0) (mkEffect 4 [] []) listening_socket_model
      = CheckOk accepted_socket_model [] ∧
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect 4 [] []) listening_socket_model
      ≠ CheckUnmodeled := by
  refine ⟨?_, ?_, ?_⟩ <;> alloc_norm

/-- Rocq's `accept_errno_arms_leave_the_queue_alone`: each errno leaves
the model — queue, counter and table — as it was.  -EMFILE comes from
`get_unused_fd_flags` in `__sys_accept4_file` (net/socket.c:2025-2027,
Linux v6.18.46), which for fd 4 means an `RLIMIT_NOFILE` of 4 or less
where the fixture records a limit of 1024 (`m_nofile_fixture_of`,
`Checks/Cases/Prelude.lean`), so here it takes another process lowering the
limit with `prlimit64`, which `check_prlimit_permission`
(kernel/sys.c:1707, at :1717-1724, Linux v6.18.46) allows when the
caller's real uid and gid equal each of the target's real, effective and
saved ones, or the caller holds `CAP_SYS_RESOURCE` in the target's user
namespace;
-ENOMEM from `sock_alloc_file` in `do_accept` (net/socket.c:1980-1982),
whose `alloc_file_pseudo` fails with it in `alloc_path_pseudo`
(fs/file_table.c:397-402) or `alloc_empty_file` (:260); -ENFILE from
`sock_alloc` in `do_accept` (net/socket.c:1966-1968) or from
`alloc_empty_file`'s file limit (fs/file_table.c:278).
kernel: fs/file.c:alloc_fd; net/socket.c:do_accept,__sys_accept4_file,sock_alloc_file; fs/file_table.c:alloc_path_pseudo,alloc_empty_file@v6.18.46 -/
theorem check_accept_errno_arms_leave_the_queue_alone :
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect (errno_ret ENOMEM) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect (errno_ret EMFILE) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect (errno_ret ENFILE) [] [])
      listening_socket_model = CheckOk listening_socket_model [] := by
  refine ⟨?_, ?_, ?_⟩ <;> alloc_norm

/-- Rocq's `accept_refuses_errnos_outside_the_set`: -EAGAIN and -EINTR
are answers to an EMPTY accept queue — `inet_csk_accept`
(net/ipv4/inet_connection_sock.c:649, Linux v6.18.46) tests the queue at
:667 and then returns -EAGAIN on a zero timeout (:671-673) or waits in
`inet_csk_wait_for_connect` (:601), whose four exits are 0 once a
connection is queued (:629-631), -EINVAL once the socket has left
TCP_LISTEN (:632-634), `sock_intr_errno` on a pending signal (:635-637) —
-ERESTARTSYS for an infinite timeout, which `sk_rcvtimeo` is by default
(include/net/sock.h:2682-2685; net/core/sock.c:3685), and -EINTR for a
finite one — and -EAGAIN once the timeout has run out
(net/ipv4/inet_connection_sock.c:638-640).  The
model's queue, `NetQueue` (`State/Streams.lean`), is a function from
`Nat` with no empty case: a listener waiting for its next connection is
not a state it has, and `accept4_spec` answers from the next connection.
So the two refusals rest on what the model leaves out of that wait,
which are Rocq's reasons (`Checks/Cases/Net/Socket.v`).  -EAGAIN needs
O_NONBLOCK or a finite SO_RCVTIMEO, and a modeled run sets neither:
SOCK_NONBLOCK declines, `setsockopt_spec` declines past the level, and
`Sys/Fs/Fcntl.lean`'s `socket_f_flags` says why no socket file the model
opens carries O_NONBLOCK; that nothing outside the model sets either —
O_NONBLOCK by F_SETFL or by FIONBIO (`ioctl_fionbio`, fs/ioctl.c:340,
Linux v6.18.46), or a finite SO_RCVTIMEO by `setsockopt`
(`sk_setsockopt`, net/core/sock.c:1186, at :1297-1300, Linux v6.18.46) —
is the section header's premise on a socket the model holds.  -EINTR
needs a signal during the wait, and the environment the model
quantifies over delivers none, the section header's no-signal premise,
on which this refusal stands.  Without it -EINTR is a real
answer: riscv's `arch_do_signal_or_restart`
(arch/riscv/kernel/signal.c:396, at :437-443, Linux v6.18.46) turns the
-ERESTARTSYS of the default timeout into -EINTR for a handler installed
without SA_RESTART, and `rt_sigaction_spec` accepts a handler only
without it (`sa_flags_accepted`, `Sys/Kernel/Signal.lean`).
-EOPNOTSUPP is `sock_no_accept`'s, the `accept`
of a socket type with no listen support, and `FdSocket` records a TCP
state and no type: `socket_spec`'s one success is AF_INET SOCK_STREAM at
protocol 0 or TCP, whose `inet_stream_ops` names `inet_accept` instead
(net/ipv4/af_inet.c:1056).
kernel: net/ipv4/inet_connection_sock.c:inet_csk_accept,inet_csk_wait_for_connect; include/net/sock.h:sock_intr_errno; net/core/sock.c:sock_no_accept@v6.18.46 -/
theorem check_accept_refuses_errnos_outside_the_set :
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect (errno_ret EAGAIN) [] [])
      listening_socket_model = CheckReject ∧
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect (errno_ret EINTR) [] [])
      listening_socket_model = CheckReject ∧
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect (errno_ret EOPNOTSUPP) [] [])
      listening_socket_model = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> alloc_norm

/-- THE DESCRIPTOR IS THE LOWEST FREE ONE: 5, with 4 free, is refused, and
so are 3, the listener, and 0, stdin, both live: `alloc_fd`
(fs/file.c:570, Linux v6.18.46) hands out an empty slot only.
kernel: fs/file.c:alloc_fd; net/socket.c:__sys_accept4_file@v6.18.46 -/
theorem check_accept_success_is_the_lowest_free_fd :
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect 5 [] []) listening_socket_model
      = CheckReject ∧
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect 3 [] []) listening_socket_model
      = CheckReject ∧
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect 0 [] []) listening_socket_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> alloc_norm

/-- WITH A NULL ADDRESS ACCEPT STORES NOTHING: `do_accept` reaches
`ops->getname` and `move_addr_to_user` only when `upeer_sockaddr` is
non-NULL (net/socket.c:1993, Linux v6.18.46), and a non-NULL one is
declined, so `accept4_spec`'s answers are `ret_only` and `err_ret`
effects, which carry no store — and a store or a zeroed range beside the
descriptor, beside an allocation errno, beside the exhausted counter's
errno (`check_errno_only`) or beside -EBADF is refused.
kernel: net/socket.c:do_accept,__sys_accept4_file,__sys_accept4,sock_alloc_file; fs/file_table.c:alloc_path_pseudo,alloc_empty_file@v6.18.46 -/
theorem check_accept4_stores_nothing :
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect 4 [(4096, [2, 0])] [])
      listening_socket_model = CheckReject ∧
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect 4 [] [(4096, 16)]) listening_socket_model
      = CheckReject ∧
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect (errno_ret ENOMEM) [(4096, [0])] [])
      listening_socket_model = CheckReject ∧
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect (errno_ret ENOMEM) [(4096, [0])] [])
      exhausted_listening_model = CheckReject ∧
    check_accept4_row (accept4_in 9 0 0 0) (mkEffect (errno_ret EBADF) [] [(4096, 16)])
      listening_socket_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> alloc_norm

/-- kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept; fs/file.c:alloc_fd,alloc_fdtable,expand_files@v6.18.46 -/
theorem check_accept_arms_around_the_accepted_state :
    check_accept4_row (accept4_in 4 0 0 0) (mkEffect (errno_ret EINVAL) [] [])
      accepted_socket_model = CheckOk accepted_socket_model [] ∧
    check_accept4_row (accept4_in 1 0 0 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_accept4_row (accept4_in 9 0 0 1) (mkEffect (errno_ret EBADF) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_accept4_row (accept4_in 3 0 0 1) (mkEffect (errno_ret EINVAL) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_accept4_row (accept4_in 3 0 0 524288) (mkEffect 4 [] []) listening_socket_model
      = CheckOk accepted_socket_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> alloc_norm

/-- Rocq's `accept_declined_arguments_are_unmodeled`: SOCK_NONBLOCK and a
non-NULL address decline on the listener, and SOCK_CLOEXEC, their
neighbour, does not.  Neither decline is an empty intersection; each is a
limit of the model, which the spec's WHAT IS DECLINED names.
SOCK_NONBLOCK reaches `sock_alloc_file` through `do_accept` and opens the
new file `O_NONBLOCK` (net/socket.c:1980 and :483-485, Linux v6.18.46),
and the model has no such notion; a non-NULL address hands the call to
`move_addr_to_user` (:1993-2003, same version), whose stores the model
does not produce: `accept4_spec` declines there rather than render the
connection's `PeerAddr` (`State/Streams.lean`) as the `sockaddr_in`
bytes `SyscallEffect`'s `eff_writes` could carry.
kernel: net/socket.c:__sys_accept4_file,do_accept,sock_alloc_file@v6.18.46 -/
theorem check_accept_declined_arguments_are_unmodeled :
    check_accept4_row (accept4_in 3 0 0 2048) (mkEffect 4 [] []) listening_socket_model
      = CheckUnmodeled ∧
    check_accept4_row (accept4_in 3 4096 4104 0) (mkEffect 4 [] []) listening_socket_model
      = CheckUnmodeled ∧
    check_accept4_row (accept4_in 3 0 0 524288) (mkEffect 4 [] []) listening_socket_model
      = CheckOk accepted_socket_model [] := by
  refine ⟨?_, ?_, ?_⟩ <;> alloc_norm

/-- …but a bad bit beside SOCK_NONBLOCK is -EINVAL rather than the
decline, in each implementation read: the flag test comes before
anything reads SOCK_NONBLOCK — in `__sys_accept4_file`
(net/socket.c:2019-2020, Linux v6.18.46, and lines 1704-1705 of that
file at v5.5), in the older kernels' `__sys_accept4`, which tested the
flags itself (read at v4.17, lines 1550-1551, and at v5.4, lines
1713-1714), and in qemu-user's `do_accept4`
(linux-user/syscall.c:3512-3514, QEMU v11.1.1).
kernel: net/socket.c:__sys_accept4_file@v6.18.46 -/
theorem check_accept_flag_bit_beside_nonblock_is_einval :
    check_accept4_row (accept4_in 3 0 0 2049) (mkEffect (errno_ret EINVAL) [] [])
      listening_socket_model = CheckOk listening_socket_model [] := by
  alloc_norm

/-- THE FLAGS COME BEFORE THE KIND, AND THE ADDRESS AFTER NEITHER: on the
non-socket at 3 a bad flag bit is -EINVAL and -ENOTSOCK is the lie,
while with the flag word empty the same descriptor is -ENOTSOCK whatever
the address argument is — `do_accept` reaches `move_addr_to_user` only
past `sock_from_file` (net/socket.c:1962-1964 and :1993, Linux v6.18.46),
so a non-NULL address changes no answer here.
kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept; fs/file.c:alloc_fd,alloc_fdtable,expand_files@v6.18.46 -/
theorem check_accept4_flags_then_kind :
    check_accept4_row (accept4_in 3 0 0 1) (mkEffect (errno_ret EINVAL) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_accept4_row (accept4_in 3 0 0 1) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckReject ∧
    check_accept4_row (accept4_in 3 4096 4104 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] := by
  refine ⟨?_, ?_, ?_⟩ <;> alloc_norm

/-- A CLOSED DESCRIPTOR IS -EBADF BEFORE THE FLAGS ARE READ:
`__sys_accept4` resolves the fd (net/socket.c:2054-2057, Linux v6.18.46)
and only `__sys_accept4_file` tests the flag word (:2019-2020), so the
-EINVAL Linux v4.17's `__sys_accept4` answered there (lines 1550-1551 of
that tree's net/socket.c) is refused.
kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept@v6.18.46 -/
theorem check_accept4_closed_fd_refuses_the_flag_einval :
    check_accept4_row (accept4_in 9 0 0 1) (mkEffect (errno_ret EINVAL) [] [])
      listening_socket_model = CheckReject := by
  alloc_norm

/-- kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept; fs/file.c:alloc_fd,alloc_fdtable,expand_files@v6.18.46 -/
theorem check_accept4_is_enotsock_on_every_non_socket_fd_kind :
    check_accept4_row (accept4_in 0 0 0 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_accept4_row (accept4_in 4 0 0 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_accept4_row (accept4_in 5 0 0 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_accept4_row (accept4_in 6 0 0 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_accept4_row (accept4_in 7 0 0 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_accept4_row (accept4_in 8 0 0 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_accept4_row (accept4_in 0 0 0 0) (mkEffect (errno_ret EINVAL) [] [])
      socket_call_model = CheckReject ∧
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect (errno_ret EINVAL) [] [])
      socket_call_model = CheckReject ∧
    check_accept4_row (accept4_in 4 0 0 0) (mkEffect (errno_ret EINVAL) [] [])
      socket_call_model = CheckReject ∧
    check_accept4_row (accept4_in 5 0 0 0) (mkEffect (errno_ret EINVAL) [] [])
      socket_call_model = CheckReject ∧
    check_accept4_row (accept4_in 6 0 0 0) (mkEffect (errno_ret EINVAL) [] [])
      socket_kinds_model = CheckReject ∧
    check_accept4_row (accept4_in 7 0 0 0) (mkEffect (errno_ret EINVAL) [] [])
      socket_kinds_model = CheckReject ∧
    check_accept4_row (accept4_in 8 0 0 0) (mkEffect (errno_ret EINVAL) [] [])
      socket_kinds_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> alloc_norm

/-- kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept; fs/file.c:alloc_fd,alloc_fdtable,expand_files@v6.18.46 -/
theorem check_accept4_off_listen_is_einval :
    check_accept4_row (accept4_in 6 0 0 0) (mkEffect (errno_ret EINVAL) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_accept4_row (accept4_in 7 0 0 0) (mkEffect (errno_ret EINVAL) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_accept4_row (accept4_in 9 0 0 0) (mkEffect (errno_ret EINVAL) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_accept4_row (accept4_in 10 0 0 0) (mkEffect (errno_ret EINVAL) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_accept4_row (accept4_in 6 0 0 0) (mkEffect 1 [] []) socket_states_model
      = CheckReject ∧
    check_accept4_row (accept4_in 7 0 0 0) (mkEffect 1 [] []) socket_states_model
      = CheckReject ∧
    check_accept4_row (accept4_in 9 0 0 0) (mkEffect 1 [] []) socket_states_model
      = CheckReject ∧
    check_accept4_row (accept4_in 10 0 0 0) (mkEffect 1 [] []) socket_states_model
      = CheckReject ∧
    check_accept4_row (accept4_in 6 0 0 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_states_model = CheckReject ∧
    check_accept4_row (accept4_in 7 0 0 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_states_model = CheckReject ∧
    check_accept4_row (accept4_in 9 0 0 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_states_model = CheckReject ∧
    check_accept4_row (accept4_in 10 0 0 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_states_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> alloc_norm

/-- THE ALLOCATION ERRNOS ARE REFUSED OFF THE SUCCESS PATH: -ENOTSOCK and
the not-listening -EINVAL are plain returns, so the -EMFILE and -ENFILE
`get_unused_fd_flags` and `sock_alloc` can raise before `do_accept`
reaches either test are not the checker's to accept there.  Linux can
answer them: `__sys_accept4_file` reserves the descriptor
(net/socket.c:2025-2027, Linux v6.18.46) before `do_accept` looks at the
file's kind (:1962-1964), so the refusals here are the model's order and
not the kernel's, and closing that gap flips these four verdicts.
model: the spec's order, which answers -ENOTSOCK and the not-listening -EINVAL before any allocation errno, refusing the -EMFILE and -ENFILE Linux reserves the descriptor early enough to answer; a divergence restated on the checker so that closing it is a visible flip -/
theorem check_accept4_refuses_the_narrowed_allocation_errnos :
    check_accept4_row (accept4_in 1 0 0 0) (mkEffect (errno_ret EMFILE) [] [])
      listening_socket_model = CheckReject ∧
    check_accept4_row (accept4_in 0 0 0 0) (mkEffect (errno_ret EMFILE) [] [])
      socket_call_model = CheckReject ∧
    check_accept4_row (accept4_in 4 0 0 0) (mkEffect (errno_ret ENFILE) [] [])
      accepted_socket_model = CheckReject ∧
    check_accept4_row (accept4_in 6 0 0 0) (mkEffect (errno_ret ENFILE) [] [])
      socket_states_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> alloc_norm

/-- A NON-NULL ADDRESS DECLINES above the socket's state, not only on
the listener: the spec's address test sits above its state switch, so a fresh
socket with an address is `CheckUnmodeled` and not the -EINVAL it would
answer with a NULL one.  That order is the model's, not Linux's: `do_accept`
calls `ops->accept` (net/socket.c:1989, Linux v6.18.46), which is
`inet_csk_accept`'s -EINVAL on a socket that is not listening, before it
touches the address (:1993), so Linux answers -EINVAL here unless an
exit before :1989 fires first: an allocation errno, or an LSM denial,
`security_socket_accept`'s at :1984-1986 among them.  The decline
is sound, since it asserts nothing, and costs that coverage.
kernel: net/socket.c:do_accept; net/ipv4/inet_connection_sock.c:inet_csk_accept@v6.18.46 -/
theorem check_accept4_address_declines_above_the_state :
    check_accept4_row (accept4_in 6 4096 4104 0) (mkEffect (errno_ret EINVAL) [] [])
      socket_states_model = CheckUnmodeled := by
  alloc_norm

/-- kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept; fs/file.c:alloc_fd,alloc_fdtable,expand_files@v6.18.46 -/
theorem check_accept4_declines_ahead_of_the_narrowing :
    check_accept4_row (accept4_in 3 0 0 2048) (mkEffect (errno_ret EMFILE) [] [])
      socket_call_model = CheckUnmodeled ∧
    check_accept4_row (accept4_in 6 4096 4104 0) (mkEffect (errno_ret EMFILE) [] [])
      socket_states_model = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> alloc_norm

/-- accept DOES NOT READ a3: `SYSCALL_DEFINE3(accept)` (net/socket.c:2068-2072,
Linux v6.18.46) hands `__sys_accept4` a literal 0, so SOCK_NONBLOCK|1 left
in the fourth register is neither -EINVAL nor the decline — the row
answers the plain call.
kernel: net/socket.c:accept,__sys_accept4@v6.18.46 -/
theorem check_accept_ignores_a3 :
    check_accept_row (SyscallInput.mkInput 202 [3, 0, 0, 2049, 0, 0] (fun _ => none)
        (fun _ => none)) (mkEffect 4 [] []) listening_socket_model
      = CheckOk accepted_socket_model [] ∧
    check_accept_row (SyscallInput.mkInput 202 [3, 0, 0, 2049, 0, 0] (fun _ => none)
        (fun _ => none)) (mkEffect (errno_ret EINVAL) [] []) listening_socket_model
      = CheckReject ∧
    check_accept_row (SyscallInput.mkInput 202 [3, 0, 0, 2048, 0, 0] (fun _ => none)
        (fun _ => none)) (mkEffect 4 [] []) listening_socket_model ≠ CheckUnmodeled := by
  refine ⟨?_, ?_, ?_⟩ <;> alloc_norm

/-- THE FD IS 32 BITS, at the row: `accept4(2^32 + 3, …)` and
`accept(2^32 + 3, …)` are the listener's call and hand over 4, and the
-EBADF a table comparing the whole register would find is the lie.
kernel: net/socket.c:accept4,accept,__sys_accept4@v6.18.46 -/
theorem check_accept4_fd_is_32_bits :
    check_accept4_row (accept4_in (Z_to_bv 64 (2 ^ 32 + 3)) 0 0 0) (mkEffect 4 [] [])
      listening_socket_model = CheckOk accepted_socket_model [] ∧
    check_accept_row (accept_in (Z_to_bv 64 (2 ^ 32 + 3)) 0 0) (mkEffect 4 [] [])
      listening_socket_model = CheckOk accepted_socket_model [] ∧
    check_accept4_row (accept4_in (Z_to_bv 64 (2 ^ 32 + 3)) 0 0 0)
      (mkEffect (errno_ret EBADF) [] []) listening_socket_model = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> alloc_norm

/-- THE FLAGS ARE 32 BITS: bit 32 alone is the empty flag word and hands
over 4, its -EINVAL the lie; and `2^32 + SOCK_NONBLOCK` declines as
SOCK_NONBLOCK does.
kernel: net/socket.c:accept4,__sys_accept4_file@v6.18.46 -/
theorem check_accept4_flags_are_32_bits :
    check_accept4_row (accept4_in 3 0 0 (Z_to_bv 64 (2 ^ 32))) (mkEffect 4 [] [])
      listening_socket_model = CheckOk accepted_socket_model [] ∧
    check_accept4_row (accept4_in 3 0 0 (Z_to_bv 64 (2 ^ 32))) (mkEffect (errno_ret EINVAL) [] [])
      listening_socket_model = CheckReject ∧
    check_accept4_row (accept4_in 3 0 0 (Z_to_bv 64 (2 ^ 32 + 2048))) (mkEffect 4 [] [])
      listening_socket_model = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_⟩ <;> alloc_norm

/-- Rocq's `accept_at_the_wrap_rejects_the_allocated_fd`, and its
neighbours: with the counter at `2^64 - 3` the descriptor Linux would
allocate, 4, is refused, and so is 5, and neither is declined.  Linux
keeps no such counter and hands 4 over at any value of it
(bugs/socket-conn-channel-wraps-at-2-64.md), so the refusal of 4 is the
model's own bound, `conn_ix_exhausted`, and a divergence: the pin
restates it on the checker so that closing it flips this verdict.  5 is
refused as Linux refuses it: `alloc_fd` (fs/file.c:570, Linux v6.18.46)
hands out the lowest free slot.
model: the model's `conn_ix_exhausted` bound refusing the fd Linux hands over at any counter value; a divergence restated on the checker so that closing it is a visible flip -/
theorem check_accept_at_the_wrap_rejects_the_allocated_fd :
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect 4 [] []) exhausted_listening_model
      = CheckReject ∧
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect 5 [] []) exhausted_listening_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> alloc_norm

/-- Rocq's `accept_at_the_wrap_still_answers_its_errnos`: the three errnos
are still accepted at the wrap, each leaving the exhausted model as it was
(-EMFILE once another process has lowered the file limit, as
`check_accept_errno_arms_leave_the_queue_alone` says); -EAGAIN is still
refused, so the wrap has not widened the set.
kernel: fs/file.c:alloc_fd; net/socket.c:do_accept,sock_alloc_file; fs/file_table.c:alloc_path_pseudo,alloc_empty_file; net/ipv4/inet_connection_sock.c:inet_csk_accept@v6.18.46 -/
theorem check_accept_at_the_wrap_still_answers_its_errnos :
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect (errno_ret ENOMEM) [] [])
      exhausted_listening_model = CheckOk exhausted_listening_model [] ∧
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect (errno_ret EMFILE) [] [])
      exhausted_listening_model = CheckOk exhausted_listening_model [] ∧
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect (errno_ret ENFILE) [] [])
      exhausted_listening_model = CheckOk exhausted_listening_model [] ∧
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect (errno_ret EAGAIN) [] [])
      exhausted_listening_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> alloc_norm

/-- ONE BELOW THE WRAP THE HAND-OVER STILL HAPPENS: at `2^64 - 4` fd 4 is
handed over on channel `2^64 - 1`, the last that is not a standard stream,
with the counter moved onto the boundary — so the pins above are the
guard's and not a broken fixture's.
kernel: net/socket.c:do_accept,__sys_accept4_file; net/ipv4/inet_connection_sock.c:inet_csk_accept@v6.18.46 -/
theorem check_accept_hands_over_at_the_last_usable_channel :
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect 4 [] []) last_usable_listening_model
      = CheckOk last_usable_accepted_model [] := by
  alloc_norm

/-! ### The edges the pins above do not name

Where a narrowing or a range changes its answer and no pin above stands:
the sign bit of a narrowed register, the upper half of the returned one, a
negative descriptor, the smallest non-NULL address, the length pointer on
its own, descriptor 0, and the counters past the first one
`conn_ix_exhausted` fires on.  The descriptor table past `alloc_fd`'s
4096-candidate scan has no pin, as the file header says of socketpair's:
no fixture in this tree holds that many descriptors, and
bugs/fd-allocation-ignores-rlimit-nofile.md records what the model
answers there. -/

/-- `listening_socket_model` with stdin closed, so that the lowest free
descriptor is 0. -/
def stdin_closed_listening_model : Model :=
  fixture_of (fds := [ (1, .FdChannel 1), (2, .FdChannel 2), (3, .FdSocket .SkListening) ])

/-- What `socket(AF_INET, SOCK_STREAM, 0)` leaves of it: a fresh socket at 0. -/
def stdin_closed_socket_model : Model :=
  fixture_of (fds := [ (0, .FdSocket .SkFresh), (1, .FdChannel 1), (2, .FdChannel 2),
                       (3, .FdSocket .SkListening) ])

/-- What `accept4(3, NULL, NULL, 0)` leaves of it: the head connection at 0,
on channel 3, the queue advanced. -/
def stdin_closed_accepted_model : Model :=
  with_accepted
    [ (0, .FdSocket (.SkConnected peer0 3 NFin)),
      (1, .FdChannel 1), (2, .FdChannel 2), (3, .FdSocket .SkListening) ]
    stdin_closed_listening_model

/-- `listening_socket_model` with the handed-over counter at `n`, written
field by field for `exhausted_listening_model`'s reason. -/
def listening_at_counter (n : Int) : Model :=
  Model.mkModelOf
    (FdState.mkFdState (m_fds listening_socket_model) (m_pipes listening_socket_model))
    listening_socket_model.m_vm
    (IoState.mkIoState (m_stdin listening_socket_model) (m_urandom listening_socket_model)
                       (m_net listening_socket_model) (Z_to_bv 64 n))
    listening_socket_model.m_fsys listening_socket_model.m_proc
    listening_socket_model.m_lim listening_socket_model.m_time

attribute [local sys_simp low] stdin_closed_listening_model.eq_1
  stdin_closed_socket_model.eq_1 stdin_closed_accepted_model.eq_1 listening_at_counter.eq_1

/-- THE SIGN BIT OF A NARROWED REGISTER: family `2^31` is `INT_MIN` once
`sint32` has read it, below the family range, so -EAFNOSUPPORT
(net/socket.c:1545-1546, Linux v6.18.46), and the type range's -EINVAL
beside an out-of-range type is the lie; protocol `2^31` is below
`inet_create`'s range, so -EINVAL (net/ipv4/af_inet.c:265-266, same
version), and the walk's -EPROTONOSUPPORT is the lie.  The pins above
name -1, the other end of the negative half.
kernel: net/socket.c:__sock_create; net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem check_socket_sign_bit_is_negative :
    check_socket_row (socket_in (Z_to_bv 64 (2 ^ 31)) 1 0)
      (mkEffect (errno_ret EAFNOSUPPORT) [] []) listening_socket_model
      = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in (Z_to_bv 64 (2 ^ 31)) 11 0)
      (mkEffect (errno_ret EINVAL) [] []) listening_socket_model = CheckReject ∧
    check_socket_row (socket_in 2 1 (Z_to_bv 64 (2 ^ 31)))
      (mkEffect (errno_ret EINVAL) [] []) listening_socket_model
      = CheckOk listening_socket_model [] ∧
    check_socket_row (socket_in 2 1 (Z_to_bv 64 (2 ^ 31)))
      (mkEffect (errno_ret EPROTONOSUPPORT) [] []) listening_socket_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> alloc_norm

/-- THE RETURN IS THE WHOLE REGISTER: `__sys_socket` (net/socket.c:1743,
Linux v6.18.46) and `__sys_accept4` (:2051) return the descriptor as an
`int`, which the syscall's `long` return sign-extends, so a register
holding 4 in its low half and a bit above it is an answer Linux does
not give: the checker compares the whole register and refuses
`2^32 + 4` from both calls.
kernel: net/socket.c:__sys_socket,__sys_accept4@v6.18.46 -/
theorem check_socket_and_accept4_return_is_the_whole_register :
    check_socket_row (socket_in 2 1 0) (mkEffect (Z_to_bv 64 (2 ^ 32 + 4)) [] [])
      listening_socket_model = CheckReject ∧
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect (Z_to_bv 64 (2 ^ 32 + 4)) [] [])
      listening_socket_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> alloc_norm

/-- A NEGATIVE DESCRIPTOR IS -EBADF: `fd32` keeps the low 32 bits,
`0xffffffff`, zero-extended; the -1 is the kernel's reading of them, since
`SYSCALL_DEFINE4(accept4, int, fd, …)` (net/socket.c:2062, Linux
v6.18.46) takes the descriptor as an `int`.  `__sys_accept4`'s lookup
finds nothing there (:2054-2057), so with the flag word 0 the answer is
-EBADF; the descriptor the listener would hand over, and `do_accept`'s
-ENOTSOCK, are lies.
kernel: net/socket.c:accept4,__sys_accept4,do_accept@v6.18.46 -/
theorem check_accept4_negative_fd_is_ebadf :
    check_accept4_row (accept4_in (Z_to_bv 64 (2 ^ 32 - 1)) 0 0 0)
      (mkEffect (errno_ret EBADF) [] []) listening_socket_model
      = CheckOk listening_socket_model [] ∧
    check_accept4_row (accept4_in (Z_to_bv 64 (2 ^ 32 - 1)) 0 0 0) (mkEffect 4 [] [])
      listening_socket_model = CheckReject ∧
    check_accept4_row (accept4_in (Z_to_bv 64 (2 ^ 32 - 1)) 0 0 0)
      (mkEffect (errno_ret ENOTSOCK) [] []) listening_socket_model = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> alloc_norm

/-- THE SMALLEST NON-NULL ADDRESS DECLINES: `do_accept`
(net/socket.c:1993-2003, Linux v6.18.46) hands any non-NULL
`upeer_sockaddr` to `move_addr_to_user`, whose stores the model does not
produce, so address 1 declines as 4096 does above, whatever the effect.
On this input Linux does not hand a descriptor over: `move_addr_to_user`
(net/socket.c:276, same version) reads the NULL length pointer beside the
address at :288 and faults, so the call is -EFAULT unless an exit before
that read fires first.  So the descriptor declined beside it is not an
answer Linux gives here.
kernel: net/socket.c:do_accept,move_addr_to_user@v6.18.46 -/
theorem check_accept4_smallest_address_declines :
    check_accept4_row (accept4_in 3 1 0 0) (mkEffect 4 [] []) listening_socket_model
      = CheckUnmodeled ∧
    check_accept4_row (accept4_in 3 1 0 0) (mkEffect (errno_ret EFAULT) [] [])
      listening_socket_model = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> alloc_norm

/-- THE LENGTH POINTER ALONE IS NOT READ: `do_accept` passes
`upeer_addrlen` to `move_addr_to_user` only inside its `upeer_sockaddr`
branch (net/socket.c:1993-2003, Linux v6.18.46), so `accept4(3, NULL, 1,
0)` is the plain call, handing over 4 with nothing stored, and the
-EFAULT a kernel reading the pointer would give is the lie.
kernel: net/socket.c:do_accept,move_addr_to_user@v6.18.46 -/
theorem check_accept4_length_pointer_alone_is_never_read :
    check_accept4_row (accept4_in 3 0 1 0) (mkEffect 4 [] []) listening_socket_model
      = CheckOk accepted_socket_model [] ∧
    check_accept4_row (accept4_in 3 0 1 0) (mkEffect (errno_ret EFAULT) [] [])
      listening_socket_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> alloc_norm

/-- DESCRIPTOR 0 IS HANDED OUT WHEN IT IS FREE: `alloc_fd` (fs/file.c:570,
Linux v6.18.46) scans up from 0, so with stdin closed both calls hand
over 0, and 4, the full fixture's answer, is the lie.
kernel: fs/file.c:alloc_fd; net/socket.c:sock_map_fd,__sys_accept4_file@v6.18.46 -/
theorem check_socket_and_accept4_hand_over_fd_zero :
    check_socket_row (socket_in 2 1 0) (mkEffect 0 [] []) stdin_closed_listening_model
      = CheckOk stdin_closed_socket_model [] ∧
    check_socket_row (socket_in 2 1 0) (mkEffect 4 [] []) stdin_closed_listening_model
      = CheckReject ∧
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect 0 [] []) stdin_closed_listening_model
      = CheckOk stdin_closed_accepted_model [] ∧
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect 4 [] []) stdin_closed_listening_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> alloc_norm

/-- PAST THE FIRST EXHAUSTED COUNTER THE BOUND STILL HOLDS: at `2^64 - 2`
and `2^64 - 1` the checker still refuses the 4 Linux hands over at any
counter value, and still accepts -ENOMEM, so `conn_ix_exhausted` covers
the top of the range and not only the one value
`check_accept_at_the_wrap_rejects_the_allocated_fd` names.  The refusal
is the model's bound, as there.
model: the model's `conn_ix_exhausted` bound over the counters above the first it fires on, refusing the fd Linux hands over at any counter value; a divergence restated on the checker so that closing it is a visible flip -/
theorem check_accept_past_the_wrap_the_bound_still_holds :
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect 4 [] [])
      (listening_at_counter (2 ^ 64 - 2)) = CheckReject ∧
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect (errno_ret ENOMEM) [] [])
      (listening_at_counter (2 ^ 64 - 2)) = CheckOk (listening_at_counter (2 ^ 64 - 2)) [] ∧
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect 4 [] [])
      (listening_at_counter (2 ^ 64 - 1)) = CheckReject ∧
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect (errno_ret ENOMEM) [] [])
      (listening_at_counter (2 ^ 64 - 1)) = CheckOk (listening_at_counter (2 ^ 64 - 1)) [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> alloc_norm

/-! ### The queue's order, the address's width and the wrap's place

Three facts the fixtures above cannot tell apart from a wrong spec
matched by a wrong checker, since `check_accept4_sound_ok` and
`check_accept4_complete_ok` hold of such a pair as well.  The silent
network's every connection is the same one and its tail is itself, so on
it a peer read from a constant and a queue left unpopped leave the
post-states above unchanged, and those post-states are built through
`with_accepted`, so a `with_accepted` that moved the counter by two would
move them with it; every address above is 0,
1 or 4096, so a test on the address register's low half answers as the
whole-register test does; and every wrap pin above calls on the listener,
so `conn_ix_exhausted` asked before the descriptor answers there as it
does asked after.  Each pin below names a value that separates the two. -/

/-- A listener whose queue holds two different connections: 1.2.3.4:443
with a pending reset, then `peer0` with a timeout, then silence. -/
def listening_scripted_model : Model :=
  fixture_of (fds := [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
                       (3, .FdSocket .SkListening) ])
             (net := NConn peer_1234 NRst (NConn peer0 NTimedOut net_silent))

/-- What `accept4(3, NULL, NULL, 0)` leaves of it, written field by field
rather than through `with_accepted`: the head connection at 4 on channel
3, the second connection now at the queue's head, the counter at 1. -/
def scripted_accepted_model : Model :=
  Model.mkModelOf
    (FdState.mkFdState
      [ (4, .FdSocket (.SkConnected peer_1234 3 NRst)),
        (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2), (3, .FdSocket .SkListening) ]
      (m_pipes listening_scripted_model))
    listening_scripted_model.m_vm
    (IoState.mkIoState (m_stdin listening_scripted_model) (m_urandom listening_scripted_model)
                       (NConn peer0 NTimedOut net_silent) (Z_to_bv 64 1))
    listening_scripted_model.m_fsys listening_scripted_model.m_proc
    listening_scripted_model.m_lim listening_scripted_model.m_time

/-- What a second `accept4(3, NULL, NULL, 0)` leaves: the second
connection at 5 on channel 4, the queue silent, the counter at 2. -/
def scripted_twice_accepted_model : Model :=
  Model.mkModelOf
    (FdState.mkFdState
      [ (5, .FdSocket (.SkConnected peer0 4 NTimedOut)),
        (4, .FdSocket (.SkConnected peer_1234 3 NRst)),
        (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2), (3, .FdSocket .SkListening) ]
      (m_pipes listening_scripted_model))
    listening_scripted_model.m_vm
    (IoState.mkIoState (m_stdin listening_scripted_model) (m_urandom listening_scripted_model)
                       net_silent (Z_to_bv 64 2))
    listening_scripted_model.m_fsys listening_scripted_model.m_proc
    listening_scripted_model.m_lim listening_scripted_model.m_time

/-- The listener at 3 beside a fresh socket at 6, with the counter at
`2^64 - 3`, the first value `conn_ix_exhausted` fires on; 9 is closed. -/
def exhausted_states_model : Model :=
  Model.mkModelOf
    (FdState.mkFdState [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
                         (3, .FdSocket .SkListening), (6, .FdSocket .SkFresh) ] [])
    listening_socket_model.m_vm
    (IoState.mkIoState (m_stdin listening_socket_model) (m_urandom listening_socket_model)
                       (m_net listening_socket_model) (Z_to_bv 64 (2 ^ 64 - 3)))
    listening_socket_model.m_fsys listening_socket_model.m_proc
    listening_socket_model.m_lim listening_socket_model.m_time

attribute [local sys_simp low] listening_scripted_model.eq_1 scripted_accepted_model.eq_1
  scripted_twice_accepted_model.eq_1 exhausted_states_model.eq_1

/-- THE HEAD CONNECTION IS READ AND POPPED: on a queue of two different
connections, accept4 and accept each hand over 1.2.3.4:443 with its
pending reset at 4 on channel 3, leaving `peer0` at the head and the
counter at 1; a second accept4 hands over `peer0` with its timeout at 5
on channel 4, leaving the silent tail and the counter at 2.
`inet_csk_accept` (net/ipv4/inet_connection_sock.c:649, Linux v6.18.46)
takes its request at :679 and hands over that request's socket at :681.
The request comes from `reqsk_queue_remove`
(include/net/request_sock.h:210, Linux v6.18.46), which reads the
queue's head, `rskq_accept_head` (declared at :193), and unlinks it
(:216-219).
kernel: net/ipv4/inet_connection_sock.c:inet_csk_accept; include/net/request_sock.h:reqsk_queue_remove; net/socket.c:do_accept,__sys_accept4_file@v6.18.46 -/
theorem check_accept_hands_over_a_scripted_head :
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect 4 [] []) listening_scripted_model
      = CheckOk scripted_accepted_model [] ∧
    check_accept_row (accept_in 3 0 0) (mkEffect 4 [] []) listening_scripted_model
      = CheckOk scripted_accepted_model [] ∧
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect 5 [] []) scripted_accepted_model
      = CheckOk scripted_twice_accepted_model [] := by
  refine ⟨?_, ?_, ?_⟩ <;> alloc_norm

/-- THE ADDRESS IS COMPARED WHOLE: `2^32` is a non-NULL pointer whose low
half is 0, and both calls decline it rather than hand the descriptor
over.  The pointer arrives as the whole register — `__SC_LONG` and
`__SC_CAST` (include/linux/syscalls.h:131-132, Linux v6.18.46) under
riscv's `__SYSCALL_DEFINEx` (arch/riscv/include/asm/syscall_wrapper.h:88)
— and `do_accept` tests `upeer_sockaddr` against NULL as a pointer
(net/socket.c:1993), as qemu-user's `do_accept4` tests `target_addr == 0`
(linux-user/syscall.c:3524, QEMU v11.1.1), so each takes the address
branch here.
kernel: net/socket.c:do_accept,__sys_accept4@v6.18.46 -/
theorem check_accept4_address_is_compared_whole :
    check_accept4_row (accept4_in 3 4294967296 0 0) (mkEffect 4 [] []) listening_socket_model
      = CheckUnmodeled ∧
    check_accept_row (accept_in 3 4294967296 0) (mkEffect 4 [] []) listening_socket_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> alloc_norm

/-- kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept; fs/file.c:alloc_fd,alloc_fdtable,expand_files@v6.18.46 -/
theorem check_accept_the_wrap_is_asked_last :
    check_accept4_row (accept4_in 9 0 0 0) (mkEffect (errno_ret EBADF) [] [])
      exhausted_states_model = CheckOk exhausted_states_model [] ∧
    check_accept4_row (accept4_in 9 0 0 0) (mkEffect (errno_ret ENOMEM) [] [])
      exhausted_states_model = CheckReject ∧
    check_accept4_row (accept4_in 6 0 0 0) (mkEffect (errno_ret EINVAL) [] [])
      exhausted_states_model = CheckOk exhausted_states_model [] ∧
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect (errno_ret ENOMEM) [] [])
      exhausted_states_model = CheckOk exhausted_states_model [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> alloc_norm

/-- THE STATES FIXTURE IS AT THE WRAP: on it the checker refuses the 4
the listener's accept would hand over, as it does on
`exhausted_listening_model`, so the pin above runs past the exhausted
counter and not beside it.  The refusal is the model's
`conn_ix_exhausted` bound, as in
`check_accept_at_the_wrap_rejects_the_allocated_fd`: Linux keeps no such
counter and hands 4 over at any value of it
(bugs/socket-conn-channel-wraps-at-2-64.md).
model: the model's `conn_ix_exhausted` bound on the fixture of `check_accept_the_wrap_is_asked_last`, refusing the fd Linux hands over at any counter value; a divergence restated on the checker so that closing it is a visible flip -/
theorem check_accept_the_states_fixture_is_at_the_wrap :
    check_accept4_row (accept4_in 3 0 0 0) (mkEffect 4 [] []) exhausted_states_model
      = CheckReject := by
  alloc_norm

/-! ### The two witnesses -/

/-- Open the two witnesses and decide what is closed. -/
scoped macro "alloc_witness_open" cfg:Lean.Parser.Tactic.optConfig : tactic =>
  `(tactic| simp $cfg:optConfig only [socket_witness, accept4_witness, ret_outcome,
      Bool.and_eq_true, Bool.or_eq_true, ne_eq, reduceCtorEq, sys_simp, ↓reduceIte])

/-- Evaluate a closed call of one of the two witnesses. -/
scoped macro "alloc_witness_norm" : tactic =>
  `(tactic| (alloc_witness_open +decide;
             first | done | sys_simp_pass +ground +decide -failIfUnchanged;
             first | done | alloc_witness_open +ground +decide))

/-- socket's witness, arm by arm: -EINVAL on a bad flag bit, `Unmodeled`
on SOCK_NONBLOCK, -EAFNOSUPPORT past the family range, -EINVAL past the
type range, `Unmodeled` on AF_UNIX and on SOCK_PACKET, -EINVAL past the
protocol range, `Unmodeled` on SCTP and on MPTCP, -EPROTONOSUPPORT on
SMC and on UDP, and on the passing call -ENOMEM, the head of
`socket_errnos` — an answer the call can give, from `sk_alloc` or
`sock_alloc_file`, and not the descriptor — then `Unmodeled` on
SOCK_DGRAM and SOCK_SEQPACKET and -ESOCKTNOSUPPORT on SOCK_RDM.
kernel: net/socket.c:__sys_socket_create,__sock_create,sock_alloc_file; net/ipv4/af_inet.c:inet_create; fs/file_table.c:alloc_path_pseudo,alloc_empty_file@v6.18.46 -/
theorem socket_witness_names_each_arm :
    socket_witness 2 257 17 listening_socket_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] ∧
    socket_witness 2 2049 0 listening_socket_model = Unmodeled ∧
    socket_witness 46 1 0 listening_socket_model
      = Ok (mkEffect (errno_ret EAFNOSUPPORT) [] []) listening_socket_model [] ∧
    socket_witness 2 11 0 listening_socket_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] ∧
    socket_witness 1 1 0 listening_socket_model = Unmodeled ∧
    socket_witness 2 10 0 listening_socket_model = Unmodeled ∧
    socket_witness 2 1 263 listening_socket_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] ∧
    socket_witness 2 1 132 listening_socket_model = Unmodeled ∧
    socket_witness 2 1 262 listening_socket_model = Unmodeled ∧
    socket_witness 2 1 256 listening_socket_model
      = Ok (mkEffect (errno_ret EPROTONOSUPPORT) [] []) listening_socket_model [] ∧
    socket_witness 2 1 17 listening_socket_model
      = Ok (mkEffect (errno_ret EPROTONOSUPPORT) [] []) listening_socket_model [] ∧
    socket_witness 2 1 0 listening_socket_model
      = Ok (mkEffect (errno_ret ENOMEM) [] []) listening_socket_model [] ∧
    socket_witness 2 2 0 listening_socket_model = Unmodeled ∧
    socket_witness 2 5 0 listening_socket_model = Unmodeled ∧
    socket_witness 2 4 0 listening_socket_model
      = Ok (mkEffect (errno_ret ESOCKTNOSUPPORT) [] []) listening_socket_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> alloc_witness_norm

/-- accept4's witness, arm by arm: -EBADF on a closed fd, -EINVAL on a bad
flag bit, `Unmodeled` on SOCK_NONBLOCK, -ENOTSOCK on a file, `Unmodeled`
on a non-NULL address, -EINVAL on a fresh socket, and on the listener
-ENOMEM, the head of `accept_errnos`, on either side of the counter's
wrap — which is why the witness does not need a descriptor or the
accepted state.
kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept,sock_alloc_file; net/ipv4/inet_connection_sock.c:inet_csk_accept; fs/file_table.c:alloc_path_pseudo,alloc_empty_file@v6.18.46 -/
theorem accept4_witness_names_each_arm :
    accept4_witness 9 0 0 listening_socket_model
      = Ok (mkEffect (errno_ret EBADF) [] []) listening_socket_model [] ∧
    accept4_witness 3 0 1 listening_socket_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) listening_socket_model [] ∧
    accept4_witness 3 0 2048 listening_socket_model = Unmodeled ∧
    accept4_witness 3 0 0 socket_call_model
      = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] ∧
    accept4_witness 3 4096 0 listening_socket_model = Unmodeled ∧
    accept4_witness 6 0 0 socket_states_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) socket_states_model [] ∧
    accept4_witness 3 0 0 listening_socket_model
      = Ok (mkEffect (errno_ret ENOMEM) [] []) listening_socket_model [] ∧
    accept4_witness 3 0 0 exhausted_listening_model
      = Ok (mkEffect (errno_ret ENOMEM) [] []) exhausted_listening_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> alloc_witness_norm

/-! ## sendto, sendmsg, recvfrom and recvmsg: the I/O checkers

The four I/O checkers ported by ticket C-Net-Socket-io, appended below the
socket and accept4 section.  What is pinned: the four rows and their
`_row_is_the_arm` theorems; Rocq's closed `check_syscall` examples for
206, 207, 211 and 212, restated on the row; every leaf of the four
checkers on some closed call, the lie beside each answer; and the five
witnesses, arm by arm.  The two halves the pairs share,
`check_send_on_socket` and `check_recv_fd_answer`, are reached through
their callers, every arm of each by some pin below.

THE ROCQ MAPPING.  `recv_declines_a_socket_descriptor`,
`recv_argument_order_is_opposite` and
`sendmsg_resolves_the_fd_before_the_header` keep their names with
`check_` in front, on the spec file's fixtures: `socket_states_model` as
in Rocq, `socket_call_model` for the closed 999 of the order example, and
`accepted_socket_model` for the sendmsg one.
`recv_on_a_non_socket_descriptor` keeps its name too, on
`listening_socket_model`: Rocq runs it on `init_model … (demo_input [] IEof)`,
of which this tree has no Lean fixture, and the one descriptor the
example names, the channel at 1, is a channel in both tables.
`send_flag_word_must_be_exactly_nosignal` and
`sendmsg_reads_the_argument_never_the_struct_field` keep their names,
with the cells that ran on a connection moved, as the next paragraph
says.  `Checks/Cases/Fs/Pipe.v`'s `socket_calls_on_a_pipe_end_are_enotsock`
and `socket_calls_on_a_pipe_end_reject_ebadf` keep their names with
`check_` in front, at the end of the recv pins, their bind cells beside
their recvfrom ones: Rocq's `pipe_model` holds a pipe's read end at 3 and
its write end at 4, and the twins ask the read end at
`socket_kinds_model`'s 6 and the write end at `pipe_write_end_model`'s 6,
the spec file's fixtures for the two ends.  As the file header says of
its own list, this one is prose, and nothing reads it.

THE CONNECTED SOCKET DECLINES.  Rocq's checker sends on a connection, or
answers and consumes its pending error; this twin declines every
connected state (`check_send_on_socket`, whose docstring names the
departure, and the spec's send section the reason).  So the Rocq examples
that run on `accepted_socket_model` or on a connection with a pending
reset cannot keep their verdicts, and each is restated as the decline on
Rocq's own `(input, effect)` pairs under a name that says so, because a
name claiming a delivery over a verdict that declines it would mislead:
`send_emits_on_the_connections_channel`,
`send_short_is_a_prefix_and_zero_is_not` and `send_errno_return_rejected`
are `check_sendto_on_close_wait_declines`;
`send_consumes_the_pending_reset_once`'s first and third cells are
`check_sendto_on_a_pending_reset_declines`;
`sendmsg_gathers_onto_the_same_channel` is
`check_sendmsg_on_a_connection_declines`.  What those examples REFUSE is twinned wherever the twin
still models the call: the consumed reset's -EPIPE, and its -ECONNRESET
refused, on `reset_consumed_socket_model`, Rocq's fixture, at fd 4 and on
`reset_socket_model` at fd 3, where sendmsg's are pinned too
(`check_send_on_a_consumed_reset_is_epipe`, Rocq's second cell of
`send_consumes_the_pending_reset_once` with that refusal beside it); and a
delivery, a short delivery, a zero and -EINTR on a dead socket
(`check_send_on_a_dead_socket_refuses_every_delivery`).  The third cell of
`send_flag_word_must_be_exactly_nosignal`, the exact word still going out
on the accepted socket, would decline here for the state's reason and so
no longer show the gate passing MSG_NOSIGNAL: the pin keeps Rocq's two
declines and adds the gate's two sides on `fresh_socket_model`, where the
exact word reaches -EPIPE and the other two words decline.
`sendmsg_reads_the_argument_never_the_struct_field` moves the same way.

HOW THESE ARE PROVED.  `io_norm` is `check_norm` over the four checkers:
the same three passes, opening the four rows, the four checkers, the two
shared halves, the range verdict `check_access_ok_zero` and the acceptors
`check_ret_only` and `check_ret_only_copyins`, and deciding what is
closed; its own macro for the options section's reason.  The header walk
behind a sendmsg pin, `read_bytes_map` over the spec file's
`send_msghdr_mem`, and the import behind it are evaluated by the ground
pass.  The two pipe-end twins run `check_norm` on their bind cells, bind
being a lifecycle checker.  The witness pins run `io_witness_norm`.  None
is `rfl`, for the file header's reason. -/

section IO

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Uaccess
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Uaccess

def check_sendto_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_sendto i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) eff m

def check_recvfrom_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_recvfrom i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m

def check_sendmsg_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_sendmsg i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m

def check_recvmsg_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_recvmsg (fd32 (in_arg i 0)) (in_arg i 2) eff m

/-- sendto's row: a0 through `fd32`, a1 to a4 whole, and a5 — the address
length — read by no arm, since the checker takes no `addrlen` argument.
`SYSCALL_DEFINE6(sendto, int, fd, …)` (net/socket.c:2248, Linux v6.18.46)
takes the fd as an `int`; the flags are an `unsigned int`, which the spec
narrows itself (`sendflags32`), and the spec still reads a5, which is why
`check_sendto_sound_ok` is applied to it here.
kernel: net/socket.c:sendto,__sys_sendto@v6.18.46 -/
theorem sendto_row_is_the_arm (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_sendto_row i eff m = CheckOk m' evs) :
    (Sys.Registry.Net.Socket.sendto_arm).sa_spec i m (Ok eff m' evs) :=
  check_sendto_sound_ok _ _ _ _ _ _ (in_arg i 5) _ _ _ _ h

/-- recvfrom's row: a0 through `fd32`, a1 and a2 whole; a3's flags and
the address pair in a4 and a5 are read by no arm.
`SYSCALL_DEFINE6(recvfrom, int, fd, …)` is net/socket.c:2306 (Linux
v6.18.46).
kernel: net/socket.c:recvfrom,__sys_recvfrom@v6.18.46 -/
theorem recvfrom_row_is_the_arm (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_recvfrom_row i eff m = CheckOk m' evs) :
    (Sys.Registry.Net.Socket.recvfrom_arm).sa_spec i m (Ok eff m' evs) :=
  check_recvfrom_sound_ok _ _ _ _ _ _ _ _ h

/-- sendmsg's row: a0 through `fd32`, a1 and a2 whole.
`SYSCALL_DEFINE3(sendmsg, int, fd, …, unsigned int, flags)` is
net/socket.c:2720 (Linux v6.18.46).
kernel: net/socket.c:sendmsg,__sys_sendmsg@v6.18.46 -/
theorem sendmsg_row_is_the_arm (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_sendmsg_row i eff m = CheckOk m' evs) :
    (Sys.Registry.Net.Socket.sendmsg_arm).sa_spec i m (Ok eff m' evs) :=
  check_sendmsg_sound_ok _ _ _ _ _ _ _ _ h

/-- recvmsg's row: a0 through `fd32` and the flags from a2 whole; a1, the
header pointer, is read by no arm, because `__sys_recvmsg` resolves the
fd before `___sys_recvmsg` copies the header.
`SYSCALL_DEFINE3(recvmsg, int, fd, …)` is net/socket.c:2929 (Linux
v6.18.46).
kernel: net/socket.c:recvmsg,__sys_recvmsg@v6.18.46 -/
theorem recvmsg_row_is_the_arm (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_recvmsg_row i eff m = CheckOk m' evs) :
    (Sys.Registry.Net.Socket.recvmsg_arm).sa_spec i m (Ok eff m' evs) :=
  check_recvmsg_sound_ok _ _ _ _ _ _ _ h

/-- Open the four rows, the four checkers, the two shared halves, the range
verdict and the acceptors, and decide what is closed; `scoped` for
`check_open`'s reason. -/
scoped macro "io_open" cfg:Lean.Parser.Tactic.optConfig : tactic =>
  `(tactic| simp $cfg:optConfig only [check_sendto_row, check_recvfrom_row, check_sendmsg_row,
      check_recvmsg_row, check_sendto, check_recvfrom, check_sendmsg, check_recvmsg,
      check_send_on_socket, check_recv_fd_answer, check_access_ok_zero,
      check_ret_only_copyins, check_ret_only, clear_copyins, with_copyins,
      Bool.and_eq_true, Bool.or_eq_true, bv_eqb_eq, access_ranges_eqb_eq,
      check_result.CheckOk.injEq, ne_eq, reduceCtorEq, sys_simp, ↓reduceIte])

/-- Evaluate a closed call of one of the four I/O checkers, the way
`check_norm` evaluates a lifecycle one. -/
scoped macro "io_norm" : tactic =>
  `(tactic| (io_open +decide;
             first | done | sys_simp_pass +ground +decide -failIfUnchanged;
             first | done | io_open +ground +decide))

/-! ### sendto: the flag word, the address, the count, the range, the fd, the state

`__sys_sendto` (net/socket.c:2210, Linux v6.18.46) imports the buffer
through `import_ubuf` (:2218) before it resolves the fd (:2222-2227),
and validates a destination address through `move_addr_to_kernel` only
after both (:2235); the model's own gates — the flag word, a non-NULL
address, the count's bound — decline first.  On a socket with no
connection `tcp_sendmsg_locked` reaches `sk_stream_wait_connect`
(net/core/stream.c:60, Linux v6.18.46), whose state test (:70-71) answers
-EPIPE before its timeout (:72-73) and signal (:74-75) tests are read. -/

/-- Rocq's `send_flag_word_must_be_exactly_nosignal`: a flagless send and
MSG_NOSIGNAL|MSG_DONTWAIT decline on Rocq's accepted connection — and,
since that connection declines on any word here, the gate's own two sides
are pinned on the fresh socket, where the same two words decline and
MSG_NOSIGNAL alone reaches the dead socket's -EPIPE (the mapping above).
Without MSG_NOSIGNAL the -EPIPE comes with SIGPIPE (`sk_stream_error`),
which the model does not deliver.
kernel: net/socket.c:__sys_sendto; net/core/stream.c:sk_stream_wait_connect,sk_stream_error@v6.18.46 -/
theorem check_send_flag_word_must_be_exactly_nosignal :
    check_sendto_row (sendto_in 4 4096 2 0 0 0 mem_ab)
      (SyscallEffect.mkEffectU 2 [] [] [] [] [(4096, 2)]) accepted_socket_model
      = CheckUnmodeled ∧
    check_sendto_row (sendto_in 4 4096 2 16448 0 0 mem_ab)
      (SyscallEffect.mkEffectU 2 [] [] [] [] [(4096, 2)]) accepted_socket_model
      = CheckUnmodeled ∧
    check_sendto_row (sendto_in 3 4096 2 0 0 0 mem_ab) (mkEffect (errno_ret EPIPE) [] [])
      fresh_socket_model = CheckUnmodeled ∧
    check_sendto_row (sendto_in 3 4096 2 16448 0 0 mem_ab) (mkEffect (errno_ret EPIPE) [] [])
      fresh_socket_model = CheckUnmodeled ∧
    check_sendto_row (sendto_in 3 4096 2 16384 0 0 mem_ab) (mkEffect (errno_ret EPIPE) [] [])
      fresh_socket_model = CheckOk fresh_socket_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> io_norm

/-- THE FLAGS ARE 32 BITS: `2^32 + MSG_NOSIGNAL` is MSG_NOSIGNAL, so the
fresh socket answers -EPIPE, and -EAGAIN — the timeout test the state test
precedes — is the lie.
kernel: net/socket.c:sendto,__sys_sendto; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem check_sendto_flags_are_32_bits :
    check_sendto_row (sendto_in 3 4096 1 (Z_to_bv 64 (2 ^ 32 + 16384)) 0 0 mem_ab)
      (mkEffect (errno_ret EPIPE) [] []) fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendto_row (sendto_in 3 4096 1 (Z_to_bv 64 (2 ^ 32 + 16384)) 0 0 mem_ab)
      (mkEffect (errno_ret EAGAIN) [] []) fresh_socket_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> io_norm

/-- A DESTINATION ADDRESS DECLINES: `move_addr_to_kernel` would validate it
and TCP would then ignore it, two errnos for a value nothing reads.  At
8192, which `mem_ab` leaves unmapped, Linux's answer is the address
copy's -EFAULT (net/socket.c:254-255, Linux v6.18.46), and qemu-user's
too, from `target_to_host_sockaddr`'s lock; with `addrlen` 129 it is the
length test's -EINVAL (:250-251); and a readable address would reach the
dead socket's -EPIPE.  None of the three is the checker's to accept.
kernel: net/socket.c:__sys_sendto,move_addr_to_kernel; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem check_sendto_address_declines :
    check_sendto_row (sendto_in 3 4096 1 16384 8192 16 mem_ab) (mkEffect (errno_ret EFAULT) [] [])
      fresh_socket_model = CheckUnmodeled ∧
    check_sendto_row (sendto_in 3 4096 1 16384 8192 129 mem_ab)
      (mkEffect (errno_ret EINVAL) [] []) fresh_socket_model = CheckUnmodeled ∧
    check_sendto_row (sendto_in 3 4096 1 16384 8192 16 mem_ab) (mkEffect (errno_ret EPIPE) [] [])
      fresh_socket_model = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_⟩ <;> io_norm

/-- THE ADDRESS LENGTH IS NOT READ WITHOUT AN ADDRESS: with `addrp` NULL
the checker never looks at a5, so the `int` -1 beside it is the plain
call and the dead socket answers -EPIPE; the -EINVAL qemu-user's
`do_sendto` answers for `(int)addrlen < 0` before its host call is the
lie here, and Linux does not answer it either —
`__sys_sendto` hands `move_addr_to_kernel` the length only inside its
`addr != NULL` branch (net/socket.c:2235, Linux v6.18.46).
kernel: net/socket.c:__sys_sendto,move_addr_to_kernel; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem check_sendto_negative_addrlen_is_not_read :
    check_sendto_row (sendto_in 3 4096 1 16384 0 (Z_to_bv 64 (-1)) mem_ab)
      (mkEffect (errno_ret EPIPE) [] []) fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendto_row (sendto_in 3 4096 1 16384 0 (Z_to_bv 64 (-1)) mem_ab)
      (mkEffect (errno_ret EINVAL) [] []) fresh_socket_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> io_norm

/-- THE COUNT'S BOUND: one byte past `Uaccess.rw_bytes_max` declines before
the buffer and the fd are read — the model's bound, not Linux's, whose
answer there is the dead socket's -EPIPE — and the bound itself is
modeled.  Every byte is readable (`rmem_open`), as in the spec file's pin
of the bound, so the -EPIPE accepted is qemu-user's answer too: it locks
the whole buffer before the host call.
kernel: net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem check_sendto_count_bound :
    check_sendto_row (sendto_in 3 4096 131073 16384 0 0 rmem_open)
      (mkEffect (errno_ret EPIPE) [] []) fresh_socket_model = CheckUnmodeled ∧
    check_sendto_row (sendto_in 3 4096 131072 16384 0 0 rmem_open)
      (mkEffect (errno_ret EPIPE) [] []) fresh_socket_model = CheckOk fresh_socket_model [] := by
  refine ⟨?_, ?_⟩
  · io_norm
  · exact check_sendto_complete_ok _ 3 4096 131072 16384 0 0 _ _ _ _
      ((sendto_count_at_the_bound_is_epipe _).mpr rfl)

/-- THE MODEL'S THREE GATES PRECEDE THE RANGE AND THE FD: a flagless send,
a destination address and a count past the bound each decline beside a
buffer at `2^63` and the closed 9, where, once all three pass,
`import_ubuf`'s -EFAULT answers ahead of `__sys_sendto`'s -EBADF.  Each
gate's reason is its own pin's above; what this one fixes is that the
reason holds whatever the buffer and the fd are.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem check_sendto_model_gates_precede_the_range :
    check_sendto_row (sendto_in 9 (Z_to_bv 64 (2 ^ 63)) 1 0 0 0 mem_ab)
      (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model = CheckUnmodeled ∧
    check_sendto_row (sendto_in 9 (Z_to_bv 64 (2 ^ 63)) 1 16384 8192 16 mem_ab)
      (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model = CheckUnmodeled ∧
    check_sendto_row (sendto_in 9 (Z_to_bv 64 (2 ^ 63)) 131073 16384 0 0 mem_ab)
      (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model = CheckUnmodeled ∧
    check_sendto_row (sendto_in 9 (Z_to_bv 64 (2 ^ 63)) 1 16384 0 0 mem_ab)
      (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model = CheckOk fresh_socket_model [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> io_norm

/-- The -EFAULT
copies nothing, so a ledger beside it is refused.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem check_sendto_range_verdict_precedes_the_fd :
    check_sendto_row (sendto_in (Z_to_bv 64 (-1)) (Z_to_bv 64 (2 ^ 63)) 1 16384 0 0 mem_ab)
      (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendto_row (sendto_in (Z_to_bv 64 (-1)) (Z_to_bv 64 (2 ^ 63)) 1 16384 0 0 mem_ab)
      (mkEffect (errno_ret EBADF) [] []) fresh_socket_model = CheckReject ∧
    check_sendto_row (sendto_in (Z_to_bv 64 (-1)) (Z_to_bv 64 (2 ^ 63)) 1 16384 0 0 mem_ab)
      (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(Z_to_bv 64 (2 ^ 63), 1)])
      fresh_socket_model = CheckReject ∧
    check_sendto_row (sendto_in (Z_to_bv 64 (-1)) (Z_to_bv 64 (2 ^ 47 - 7)) 8 16384 0 0 mem_ab)
      (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendto_row (sendto_in 9 (Z_to_bv 64 (2 ^ 47 - 7)) 7 16384 0 0 mem_ab)
      (mkEffect (errno_ret EBADF) [] []) fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendto_row (sendto_in 9 (Z_to_bv 64 (2 ^ 47 - 7)) 7 16384 0 0 mem_ab)
      (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> io_norm

/-- A ZERO-LENGTH BUFFER IS STILL PUT THROUGH THE RANGE TEST:
`import_ubuf` calls `access_ok` on every count (lib/iov_iter.c:1437-1438,
Linux v6.18.46), so at `2^63` and at `2^47 + 1` the answer is -EFAULT and
the closed fd's -EBADF is the lie, while `2^47` itself — `TASK_SIZE`
with nothing to read — passes, and fd 9 answers -EBADF.  qemu-user's
`do_sendto` never locks a zero-length buffer and hands the host call a
NULL one (linux-user/syscall.c:3648 and :3671, QEMU v11.1.1), so at
`2^63` it answers whatever the host's fd 9 does: that is the cell the
-EFAULT here costs.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto@v6.18.46 -/
theorem check_sendto_zero_length_range_is_tested :
    check_sendto_row (sendto_in 9 (Z_to_bv 64 (2 ^ 63)) 0 16384 0 0 mem_ab)
      (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendto_row (sendto_in 9 (Z_to_bv 64 (2 ^ 63)) 0 16384 0 0 mem_ab)
      (mkEffect (errno_ret EBADF) [] []) fresh_socket_model = CheckReject ∧
    check_sendto_row (sendto_in 9 (Z_to_bv 64 (2 ^ 47 + 1)) 0 16384 0 0 mem_ab)
      (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendto_row (sendto_in 9 (Z_to_bv 64 (2 ^ 47 + 1)) 0 16384 0 0 mem_ab)
      (mkEffect (errno_ret EBADF) [] []) fresh_socket_model = CheckReject ∧
    check_sendto_row (sendto_in 9 (Z_to_bv 64 (2 ^ 47)) 0 16384 0 0 mem_ab)
      (mkEffect (errno_ret EBADF) [] []) fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendto_row (sendto_in 9 (Z_to_bv 64 (2 ^ 47)) 0 16384 0 0 mem_ab)
      (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> io_norm

/-- A CLOSED FD IS -EBADF and an open non-socket -ENOTSOCK, each in place of
the dead socket's -EPIPE and neither the other's: `__sys_sendto`'s
`fd_empty` and `sock_from_file` tests (net/socket.c:2223-2227, Linux
v6.18.46).
kernel: net/socket.c:__sys_sendto,sock_from_file; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem check_sendto_closed_and_channel_fds :
    check_sendto_row (sendto_in 9 4096 1 16384 0 0 mem_ab) (mkEffect (errno_ret EBADF) [] [])
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendto_row (sendto_in 9 4096 1 16384 0 0 mem_ab) (mkEffect (errno_ret EPIPE) [] [])
      fresh_socket_model = CheckReject ∧
    check_sendto_row (sendto_in 1 4096 1 16384 0 0 mem_ab) (mkEffect (errno_ret ENOTSOCK) [] [])
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendto_row (sendto_in 1 4096 1 16384 0 0 mem_ab) (mkEffect (errno_ret EBADF) [] [])
      fresh_socket_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> io_norm

/-- EVERY OTHER NON-SOCKET KIND is -ENOTSOCK — a regular file, a write-only
file, a directory, a pipe's read end, /dev/null and /dev/urandom — and a
delivery on the file is refused, since nothing is sent.
kernel: net/socket.c:__sys_sendto,sock_from_file@v6.18.46 -/
theorem check_sendto_every_non_socket_kind_is_enotsock :
    check_sendto_row (sendto_in 3 4096 1 16384 0 0 mem_ab) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_sendto_row (sendto_in 4 4096 1 16384 0 0 mem_ab) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_sendto_row (sendto_in 5 4096 1 16384 0 0 mem_ab) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_sendto_row (sendto_in 6 4096 1 16384 0 0 mem_ab) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_sendto_row (sendto_in 7 4096 1 16384 0 0 mem_ab) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_sendto_row (sendto_in 8 4096 1 16384 0 0 mem_ab) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_sendto_row (sendto_in 3 4096 1 16384 0 0 mem_ab)
      (SyscallEffect.mkEffectU 1 [] [] [] [] [(4096, 1)]) socket_call_model = CheckReject ∧
    check_sendto_row (sendto_in 6 4096 1 16384 0 0 mem_ab) (mkEffect (errno_ret EBADF) [] [])
      socket_kinds_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> io_norm

/-- EVERY STATE WITHOUT A CONNECTION IS -EPIPE, on the table holding one
socket per state: fresh at 6, bound at 7, listening at 8 and reset at 10,
each leaving the model alone.  -EAGAIN is refused on each side of the
walk: `sk_stream_wait_connect`'s state test precedes its timeout test.
kernel: net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem check_sendto_every_dead_state_is_epipe :
    check_sendto_row (sendto_in 6 4096 1 16384 0 0 mem_ab) (mkEffect (errno_ret EPIPE) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_sendto_row (sendto_in 7 4096 1 16384 0 0 mem_ab) (mkEffect (errno_ret EPIPE) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_sendto_row (sendto_in 8 4096 1 16384 0 0 mem_ab) (mkEffect (errno_ret EPIPE) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_sendto_row (sendto_in 10 4096 1 16384 0 0 mem_ab) (mkEffect (errno_ret EPIPE) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_sendto_row (sendto_in 6 4096 1 16384 0 0 mem_ab) (mkEffect (errno_ret EAGAIN) [] [])
      socket_states_model = CheckReject ∧
    check_sendto_row (sendto_in 10 4096 1 16384 0 0 mem_ab) (mkEffect (errno_ret EAGAIN) [] [])
      socket_states_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> io_norm

/-- A DEAD SOCKET DELIVERS NOTHING: on the fresh socket the two bytes with
their ledger, one byte of them, a zero and -EINTR are each refused, and so
is the -EPIPE carrying the payload's range — the state test answers
before the copy loop and before `sock_intr_errno` is reached.  The
refusals of Rocq's `send_short_is_a_prefix_and_zero_is_not` and
`send_errno_return_rejected`, on the socket where this twin still answers.
kernel: net/core/stream.c:sk_stream_wait_connect; include/net/sock.h:sock_intr_errno@v6.18.46 -/
theorem check_send_on_a_dead_socket_refuses_every_delivery :
    check_sendto_row (sendto_in 3 4096 2 16384 0 0 mem_ab)
      (SyscallEffect.mkEffectU 2 [] [] [] [] [(4096, 2)]) fresh_socket_model = CheckReject ∧
    check_sendto_row (sendto_in 3 4096 2 16384 0 0 mem_ab)
      (SyscallEffect.mkEffectU 1 [] [] [] [] [(4096, 1)]) fresh_socket_model = CheckReject ∧
    check_sendto_row (sendto_in 3 4096 2 16384 0 0 mem_ab) (mkEffect 0 [] [])
      fresh_socket_model = CheckReject ∧
    check_sendto_row (sendto_in 3 4096 2 16384 0 0 mem_ab) (mkEffect (errno_ret EINTR) [] [])
      fresh_socket_model = CheckReject ∧
    check_sendto_row (sendto_in 3 4096 2 16384 0 0 mem_ab)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(4096, 2)]) fresh_socket_model
      = CheckReject ∧
    check_sendto_row (sendto_in 3 4096 2 16384 0 0 mem_ab) (mkEffect (errno_ret EPIPE) [] [])
      fresh_socket_model = CheckOk fresh_socket_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> io_norm

/-- A ZERO-LENGTH SEND ON A DEAD SOCKET IS STILL -EPIPE, never 0:
`tcp_sendmsg_locked` waits for the connection before it looks at the
length.
kernel: net/ipv4/tcp.c:tcp_sendmsg_locked; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem check_sendto_zero_length_on_a_dead_socket_is_epipe :
    check_sendto_row (sendto_in 3 4096 0 16384 0 0 mem_ab) (mkEffect (errno_ret EPIPE) [] [])
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendto_row (sendto_in 3 4096 0 16384 0 0 mem_ab) (mkEffect 0 [] [])
      fresh_socket_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> io_norm

/-- Rocq's `reset_consumed_socket_model`: `accepted_socket_model`'s table
with fd 4 the connection whose reset the program has already read, the
state a send's `SendErr` arm leaves behind.  `reset_socket_model` holds
the same connection at fd 3 and no listener; this one keeps Rocq's table,
so Rocq's cell runs on Rocq's descriptor. -/
def reset_consumed_socket_model : Model :=
  with_accepted
    [ (4, .FdSocket (.SkReset peer0 3)),
      (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
      (3, .FdSocket .SkListening) ]
    listening_socket_model

attribute [local sys_simp low] reset_consumed_socket_model.eq_1

/-- Rocq's `send_consumes_the_pending_reset_once`, second cell: once the
reset has been read (`SkReset`), a send is -EPIPE with the model left
alone, and the -ECONNRESET already consumed is refused — on Rocq's own
table at fd 4, and on `reset_socket_model`'s fd 3 for sendto and for
sendmsg, whose -EPIPE carries the header and the descriptor it read.
`tcp_reset` (net/ipv4/tcp_input.c) set the error `sock_error` took.
kernel: net/core/stream.c:sk_stream_wait_connect; net/ipv4/tcp_input.c:tcp_reset@v6.18.46 -/
theorem check_send_on_a_consumed_reset_is_epipe :
    check_sendto_row (sendto_in 4 4096 2 16384 0 0 mem_ab) (mkEffect (errno_ret EPIPE) [] [])
      reset_consumed_socket_model = CheckOk reset_consumed_socket_model [] ∧
    check_sendto_row (sendto_in 4 4096 2 16384 0 0 mem_ab)
      (mkEffect (errno_ret ECONNRESET) [] []) reset_consumed_socket_model = CheckReject ∧
    check_sendto_row (sendto_in 3 4096 2 16384 0 0 mem_ab) (mkEffect (errno_ret EPIPE) [] [])
      reset_socket_model = CheckOk reset_socket_model [] ∧
    check_sendto_row (sendto_in 3 4096 2 16384 0 0 mem_ab)
      (mkEffect (errno_ret ECONNRESET) [] []) reset_socket_model = CheckReject ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_ab)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
      reset_socket_model = CheckOk reset_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_ab)
      (SyscallEffect.mkEffectU (errno_ret ECONNRESET) [] [] [] [] [(8192, 56), (8320, 16)])
      reset_socket_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> io_norm

/-- Rocq's `sendto_unmapped_buffer_in_range_faults_on_the_copy`, whose
third cell this twin keeps: at the address from the failing qemu run an
unmapped buffer passes `import_ubuf`'s range test, so the fd is resolved
and the listening socket answers -EPIPE before any byte is copied, with
-EFAULT refused.  Rocq's first two cells send on the connection and
fault on the copy; this twin declines every connected state (the
mapping above), so the connection's two answers are declines here and
not the -EFAULT.  qemu-user locks the buffer before its host call and
answers -EFAULT on the listener too, which is what the -EPIPE costs.
kernel: lib/iov_iter.c:import_ubuf; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem check_sendto_unlockable_in_range_buffer_is_not_faulted :
    check_sendto_row (sendto_in 4 46912512909312 1 16384 0 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) accepted_socket_model = CheckUnmodeled ∧
    check_sendto_row (sendto_in 4 46912512909312 1 16384 0 0 (fun _ => none))
      (mkEffect (errno_ret EPIPE) [] []) accepted_socket_model = CheckUnmodeled ∧
    check_sendto_row (sendto_in 3 46912512909312 1 16384 0 0 (fun _ => none))
      (mkEffect (errno_ret EPIPE) [] []) listening_socket_model
      = CheckOk listening_socket_model [] ∧
    check_sendto_row (sendto_in 3 46912512909312 1 16384 0 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) listening_socket_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> io_norm

/-- Rocq's `send_emits_on_the_connections_channel`,
`send_short_is_a_prefix_and_zero_is_not` and `send_errno_return_rejected`,
on their own `(input, effect)` pairs: CLOSE_WAIT, the connection `accept`
really hands over, declines every answer — the delivery with and without
its ledger, the short one, the one past the request, the zero and
-EINTR — because a reset behind the FIN would already have made the send
`tcp_reset`'s -EPIPE (the mapping above).
kernel: net/ipv4/tcp.c:tcp_sendmsg_locked; net/ipv4/tcp_input.c:tcp_reset; include/net/sock.h:sock_intr_errno@v6.18.46 -/
theorem check_sendto_on_close_wait_declines :
    check_sendto_row (sendto_in 4 4096 2 16384 0 0 mem_ab)
      (SyscallEffect.mkEffectU 2 [] [] [] [] [(4096, 2)]) accepted_socket_model
      = CheckUnmodeled ∧
    check_sendto_row (sendto_in 4 4096 2 16384 0 0 mem_ab) (mkEffect 2 [] [])
      accepted_socket_model = CheckUnmodeled ∧
    check_sendto_row (sendto_in 4 4096 2 16384 0 0 mem_ab)
      (SyscallEffect.mkEffectU 1 [] [] [] [] [(4096, 1)]) accepted_socket_model
      = CheckUnmodeled ∧
    check_sendto_row (sendto_in 4 4096 2 16384 0 0 mem_ab)
      (SyscallEffect.mkEffectU 3 [] [] [] [] [(4096, 3)]) accepted_socket_model
      = CheckUnmodeled ∧
    check_sendto_row (sendto_in 4 4096 2 16384 0 0 mem_ab) (mkEffect 0 [] [])
      accepted_socket_model = CheckUnmodeled ∧
    check_sendto_row (sendto_in 4 4096 2 16384 0 0 mem_ab) (mkEffect (errno_ret EINTR) [] [])
      accepted_socket_model = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> io_norm

/-- Rocq's `send_consumes_the_pending_reset_once`, first and third cells: a
connection whose peer has reset it (`NRst` at the head of the script, the
connection at fd 4 as Rocq's `reset_pending_socket_model` holds it)
declines both -ECONNRESET and -EPIPE, because whether the kernel has
processed the RST yet is not in the model.
kernel: net/ipv4/tcp_input.c:tcp_reset; include/net/sock.h:sock_error@v6.18.46 -/
theorem check_sendto_on_a_pending_reset_declines :
    check_sendto_row (sendto_in 4 4096 2 16384 0 0 mem_ab)
      (mkEffect (errno_ret ECONNRESET) [] []) (connected_socket_model NRst) = CheckUnmodeled ∧
    check_sendto_row (sendto_in 4 4096 2 16384 0 0 mem_ab)
      (mkEffect (errno_ret EPIPE) [] []) (connected_socket_model NRst) = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> io_norm

/-- The two other connected scripts decline as well, beyond Rocq's
examples: a byte at the head (ESTABLISHED) with a short delivery offered,
and a pending timeout with its -ETIMEDOUT offered.
kernel: net/ipv4/tcp.c:tcp_sendmsg_locked; net/ipv4/tcp_timer.c:tcp_write_err@v6.18.46 -/
theorem check_sendto_on_an_established_or_timed_out_connection_declines :
    check_sendto_row (sendto_in 4 4096 2 16384 0 0 mem_ab)
      (SyscallEffect.mkEffectU 1 [] [] [] [] [(4096, 1)])
      (connected_socket_model (NCons 97 NFin)) = CheckUnmodeled ∧
    check_sendto_row (sendto_in 4 4096 2 16384 0 0 mem_ab)
      (mkEffect (errno_ret ETIMEDOUT) [] []) (connected_socket_model NTimedOut)
      = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> io_norm

/-- THE FD IS 32 BITS, at the row: `sendto(2^32 + 3, …)` is the fresh
socket's call and answers -EPIPE; the -EBADF a table comparing the whole
register would find is the lie.
kernel: net/socket.c:sendto,__sys_sendto; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem check_sendto_fd_is_32_bits :
    check_sendto_row (sendto_in (Z_to_bv 64 (2 ^ 32 + 3)) 4096 1 16384 0 0 mem_ab)
      (mkEffect (errno_ret EPIPE) [] []) fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendto_row (sendto_in (Z_to_bv 64 (2 ^ 32 + 3)) 4096 1 16384 0 0 mem_ab)
      (mkEffect (errno_ret EBADF) [] []) fresh_socket_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> io_norm

/-! ### sendmsg: the argument, the fd, the header, the import, the state

`__sys_sendmsg` (net/socket.c:2700, Linux v6.18.46) resolves the fd
(:2709-2715) before `___sys_sendmsg` copies the header, the opposite
nesting to `__sys_sendto`'s.  `copy_msghdr_from_user` (net/socket.c:2553,
Linux v6.18.46) copies the 56 header bytes, `__copy_msghdr`
(net/socket.c:2507, Linux v6.18.46) refuses `msg_iovlen` past
`UIO_MAXIOV`, and `__import_iovec` (lib/iov_iter.c, Linux v6.18.46)
imports the descriptors.  Every -EPIPE, -EFAULT and -EINVAL past the
header carries the header's 56 bytes and each 16-byte descriptor read as
its ledger. -/

/-- THE FD IS RESOLVED BEFORE THE HEADER: the closed 9 is -EBADF and the
channel at 1 -ENOTSOCK whatever the header is, an unreadable one
included, where `copy_msghdr_from_user`'s -EFAULT is the lie; and
neither answer carries the header's bytes, nothing having been copied.
kernel: net/socket.c:__sys_sendmsg,copy_msghdr_from_user@v6.18.46 -/
theorem check_sendmsg_resolves_the_fd_before_the_header :
    check_sendmsg_row (sendmsg_in 9 8192 16384 msg_ab) (mkEffect (errno_ret EBADF) [] [])
      accepted_socket_model = CheckOk accepted_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 1 8192 16384 msg_ab) (mkEffect (errno_ret ENOTSOCK) [] [])
      accepted_socket_model = CheckOk accepted_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 9 8192 16384 (fun _ => none)) (mkEffect (errno_ret EFAULT) [] [])
      accepted_socket_model = CheckReject ∧
    check_sendmsg_row (sendmsg_in 1 8192 16384 msg_ab)
      (SyscallEffect.mkEffectU (errno_ret ENOTSOCK) [] [] [] [] [(8192, 56)])
      accepted_socket_model = CheckReject ∧
    check_sendmsg_row (sendmsg_in 9 8192 16384 (fun _ => none)) (mkEffect (errno_ret EBADF) [] [])
      accepted_socket_model = CheckOk accepted_socket_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> io_norm

/-- Rocq's `sendmsg_reads_the_argument_never_the_struct_field`: its two
cells on the accepted connection decline here (the mapping above), and
the claim is pinned on the fresh socket instead — argument MSG_NOSIGNAL
with the field clear is the dead socket's ledgered -EPIPE, argument 0
with MSG_NOSIGNAL in `msg_flags` declines, and MSG_DONTWAIT in the field
beside the argument's MSG_NOSIGNAL changes nothing; so does an argument
of MSG_NOSIGNAL|MSG_DONTWAIT decline.  `____sys_sendmsg` overwrites the
field with the argument.
kernel: net/socket.c:____sys_sendmsg,__sys_sendmsg; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem check_sendmsg_reads_the_argument_never_the_struct_field :
    check_sendmsg_row (sendmsg_in 4 8192 16384 msg_ab)
      (SyscallEffect.mkEffectU 2 [] [] [] [] [(8192, 56), (8320, 16), (4096, 2)])
      accepted_socket_model = CheckUnmodeled ∧
    check_sendmsg_row (sendmsg_in 4 8192 0 msg_ab_field_nosignal)
      (SyscallEffect.mkEffectU 2 [] [] [] [] [(8192, 56), (8320, 16), (4096, 2)])
      accepted_socket_model = CheckUnmodeled ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_ab)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 3 8192 0 msg_ab_field_nosignal)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
      fresh_socket_model = CheckUnmodeled ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_ab_field_dontwait)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 3 8192 16448 msg_ab)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
      fresh_socket_model = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> io_norm

/-- THE FLAGS ARE 32 BITS here too: `2^32 + MSG_NOSIGNAL` is the ledgered
-EPIPE, and -EAGAIN is the lie.
kernel: net/socket.c:sendmsg,__sys_sendmsg; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem check_sendmsg_flags_are_32_bits :
    check_sendmsg_row (sendmsg_in 3 8192 (Z_to_bv 64 (2 ^ 32 + 16384)) msg_ab)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 3 8192 (Z_to_bv 64 (2 ^ 32 + 16384)) msg_ab)
      (SyscallEffect.mkEffectU (errno_ret EAGAIN) [] [] [] [] [(8192, 56), (8320, 16)])
      fresh_socket_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> io_norm

/-- THE FLAG WORD DECLINES FIRST, before the fd and the header: a flagless
`sendmsg` declines on the closed 9, where the same call under MSG_NOSIGNAL
is -EBADF, and on the fresh socket with nothing readable, where under
MSG_NOSIGNAL it is `copy_msghdr_from_user`'s -EFAULT.  MSG_CMSG_COMPAT is
one of the words the gate refuses, and `__sys_sendmsg` tests it before
`CLASS(fd, f)`: -EINVAL where CONFIG_COMPAT gives the flag its bit, the
closed fd's -EBADF where the flag is 0, so neither is the checker's to
accept.
kernel: net/socket.c:__sys_sendmsg,copy_msghdr_from_user@v6.18.46 -/
theorem check_sendmsg_flag_word_declines_first :
    check_sendmsg_row (sendmsg_in 9 8192 0 msg_ab) (mkEffect (errno_ret EBADF) [] [])
      fresh_socket_model = CheckUnmodeled ∧
    check_sendmsg_row (sendmsg_in 9 8192 16384 msg_ab) (mkEffect (errno_ret EBADF) [] [])
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 3 8192 0 (fun _ => none)) (mkEffect (errno_ret EFAULT) [] [])
      fresh_socket_model = CheckUnmodeled ∧
    check_sendmsg_row (sendmsg_in 9 8192 (Z_to_bv 64 (2 ^ 31 + 16384)) msg_ab)
      (mkEffect (errno_ret EINVAL) [] []) fresh_socket_model = CheckUnmodeled ∧
    check_sendmsg_row (sendmsg_in 9 8192 (Z_to_bv 64 (2 ^ 31 + 16384)) msg_ab)
      (mkEffect (errno_ret EBADF) [] []) fresh_socket_model = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> io_norm

/-- EVERY NON-SOCKET KIND, ONE ARM EACH: the checker spells the seven
kinds out, and each is -ENOTSOCK with nothing ledgered — the channel at 0,
the regular file, the write-only file and the directory of
`socket_call_model`, and the pipe, /dev/null and /dev/urandom of
`socket_kinds_model` — and each arm has a refusal beside it, so no one arm
can be rewritten alone: -EBADF on six of them, and a copied header on the
regular file.
kernel: net/socket.c:__sys_sendmsg,sock_from_file@v6.18.46 -/
theorem check_sendmsg_every_non_socket_kind_is_enotsock :
    check_sendmsg_row (sendmsg_in 0 8192 16384 msg_ab) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_ab) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_sendmsg_row (sendmsg_in 4 8192 16384 msg_ab) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_sendmsg_row (sendmsg_in 5 8192 16384 msg_ab) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_sendmsg_row (sendmsg_in 6 8192 16384 msg_ab) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_sendmsg_row (sendmsg_in 7 8192 16384 msg_ab) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_sendmsg_row (sendmsg_in 8 8192 16384 msg_ab) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_ab)
      (SyscallEffect.mkEffectU (errno_ret ENOTSOCK) [] [] [] [] [(8192, 56)]) socket_call_model
      = CheckReject ∧
    check_sendmsg_row (sendmsg_in 7 8192 16384 msg_ab) (mkEffect (errno_ret EBADF) [] [])
      socket_kinds_model = CheckReject ∧
    check_sendmsg_row (sendmsg_in 0 8192 16384 msg_ab) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_sendmsg_row (sendmsg_in 4 8192 16384 msg_ab) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_sendmsg_row (sendmsg_in 5 8192 16384 msg_ab) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_sendmsg_row (sendmsg_in 6 8192 16384 msg_ab) (mkEffect (errno_ret EBADF) [] [])
      socket_kinds_model = CheckReject ∧
    check_sendmsg_row (sendmsg_in 8 8192 16384 msg_ab) (mkEffect (errno_ret EBADF) [] [])
      socket_kinds_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> io_norm

/-- THE HEADER, ON A SOCKET: nothing readable at 8192 is
`copy_msghdr_from_user`'s -EFAULT with nothing ledgered, and the dead
socket's -EPIPE and a ledger beside the fault are refused.  The read
carries no range test of its own — `read_bytes_map` walks the 56 bytes
in word arithmetic and wraps at 2^64 — so over a memory that maps
everything a header eight bytes below the top of the address space, one
whose 56 bytes end one past `TASK_SIZE`, and one whose 56 bytes end
exactly at it, are all READ, and each is a send of nothing on the dead
socket: -EPIPE with its own 56 bytes ledgered, -EFAULT the lie.  Linux
answers -EFAULT for the first two, `copy_from_user`'s `access_ok`
refusing the range, so those cells are the model's own.
model: the header read, which walks 56 bytes with no `access_ok` and wraps at 2^64, answering the socket's -EPIPE where Linux answers -EFAULT; a divergence restated on the checker so that closing it is a visible flip -/
theorem check_sendmsg_header_is_copied_at_the_socket :
    check_sendmsg_row (sendmsg_in 3 8192 16384 (fun _ => none)) (mkEffect (errno_ret EFAULT) [] [])
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 (fun _ => none)) (mkEffect (errno_ret EPIPE) [] [])
      fresh_socket_model = CheckReject ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 (fun _ => none))
      (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 56)]) fresh_socket_model
      = CheckReject ∧
    check_sendmsg_row (sendmsg_in 3 (Z_to_bv 64 (2 ^ 64 - 8)) 16384 rmem_open)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] []
        [(Z_to_bv 64 (2 ^ 64 - 8), 56)]) fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 3 (Z_to_bv 64 (2 ^ 64 - 8)) 16384 rmem_open)
      (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model = CheckReject ∧
    check_sendmsg_row (sendmsg_in 3 (Z_to_bv 64 (2 ^ 47 - 55)) 16384 rmem_open)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] []
        [(Z_to_bv 64 (2 ^ 47 - 55), 56)]) fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 3 (Z_to_bv 64 (2 ^ 47 - 55)) 16384 rmem_open)
      (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model = CheckReject ∧
    check_sendmsg_row (sendmsg_in 3 (Z_to_bv 64 (2 ^ 47 - 56)) 16384 rmem_open)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(Z_to_bv 64 (2 ^ 47 - 56), 56)])
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 3 (Z_to_bv 64 (2 ^ 47 - 56)) 16384 rmem_open)
      (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> io_norm

/-- A DESTINATION IN THE HEADER DECLINES, as sendto's does, while a NULL
`msg_name` beside a negative `msg_namelen` is never validated — a NULL
name's length is zeroed (net/socket.c:2520-2521, Linux v6.18.46) — and is
the plain ledgered -EPIPE.  It declines ahead of what follows it:
`__copy_msghdr` answers a named header's negative `msg_namelen` itself
with -EINVAL (:2523-2524), clamps one past 128 (:2526-2527), and hands
the name to `move_addr_to_kernel` (:2534), whose -EFAULT answers before
the `UIO_MAXIOV` test's -EMSGSIZE (:2545-2546) and before the import, so
beside `msg_iovlen` 1025, or a descriptor naming a kernel address, the
header still declines.
kernel: net/socket.c:__copy_msghdr,move_addr_to_kernel; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem check_sendmsg_named_header_declines :
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_named)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
      fresh_socket_model = CheckUnmodeled ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_negnamelen)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 (send_msghdr_mem 4096 16 1025 0 0 0 [(4096, 2)]))
      (SyscallEffect.mkEffectU (errno_ret EMSGSIZE) [] [] [] [] [(8192, 56)])
      fresh_socket_model = CheckUnmodeled ∧
    check_sendmsg_row
      (sendmsg_in 3 8192 16384 (send_msghdr_mem 4096 16 1 0 0 0 [(Z_to_bv 64 (2 ^ 63), 1)]))
      (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 56), (8320, 16)])
      fresh_socket_model = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> io_norm

/-- `msg_iovlen` PAST `UIO_MAXIOV` IS -EMSGSIZE with the header alone
ledgered — with a control block beside it, and on the full 64-bit
`2^32 + 1` whose low half is 1 — and -EINVAL, or -EMSGSIZE with nothing
ledgered, is the lie.
kernel: net/socket.c:__copy_msghdr@v6.18.46 -/
theorem check_sendmsg_iovlen_past_uio_maxiov_is_emsgsize :
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_iovlen_1025)
      (SyscallEffect.mkEffectU (errno_ret EMSGSIZE) [] [] [] [] [(8192, 56)])
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_iovlen_1025)
      (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 56)])
      fresh_socket_model = CheckReject ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_iovlen_1025)
      (mkEffect (errno_ret EMSGSIZE) [] []) fresh_socket_model = CheckReject ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_iovlen_1025_ctl)
      (SyscallEffect.mkEffectU (errno_ret EMSGSIZE) [] [] [] [] [(8192, 56)])
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_iovlen_wide)
      (SyscallEffect.mkEffectU (errno_ret EMSGSIZE) [] [] [] [] [(8192, 56)])
      fresh_socket_model = CheckOk fresh_socket_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> io_norm

/-- THE HEAP BAND DECLINES: from nine descriptors up to `UIO_MAXIOV`
itself `__import_iovec` allocates the array, which the model cannot see
fail, so neither the dead socket's -EPIPE nor -EMSGSIZE is accepted; eight,
`UIO_FASTIOV`, stays on the stack path and is the -EPIPE with the header
and all eight descriptors ledgered.
kernel: lib/iov_iter.c:__import_iovec,iovec_from_user; net/socket.c:__copy_msghdr; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem check_sendmsg_heap_band_declines :
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_iovlen_9)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56)])
      fresh_socket_model = CheckUnmodeled ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_iovlen_1024)
      (SyscallEffect.mkEffectU (errno_ret EMSGSIZE) [] [] [] [] [(8192, 56)])
      fresh_socket_model = CheckUnmodeled ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_eight)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] []
        [(8192, 56), (8320, 16), (8336, 16), (8352, 16), (8368, 16),
         (8384, 16), (8400, 16), (8416, 16), (8432, 16)])
      fresh_socket_model = CheckOk fresh_socket_model [] := by
  refine ⟨?_, ?_, ?_⟩ <;> io_norm

/-- AN UNREADABLE DESCRIPTOR ARRAY IS -EFAULT, and the ledger carries the
descriptor the walk attempted: `copy_iovec_from_user` reads each entry in
index order and stops at the first it cannot load (lib/iov_iter.c, Linux
v6.18.46), so an array on a page of its own, an array at a kernel
address, one straddling `TASK_SIZE`, one ending exactly at it, and an
array of two that nothing maps, are each -EFAULT with the header and
that one sixteen-byte entry ledgered, the header alone refused beside
them.  The walk carries no range test, which is why the array at `2^63`
is attempted and ledgered at all: Linux refuses that range in
`user_access_begin` before any load and ledgers nothing.
model: the descriptor walk, which attempts an array `access_ok` would refuse and ledgers it, where Linux refuses the range before any load; a divergence restated on the checker so that closing it is a visible flip -/
theorem check_sendmsg_fault_at_the_head_is_efault :
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_noarray)
      (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 56), (12288, 16)])
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_noarray)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (12288, 16)])
      fresh_socket_model = CheckReject ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 (msg_array_at (Z_to_bv 64 (2 ^ 63)) 1))
      (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] []
        [(8192, 56), (Z_to_bv 64 (2 ^ 63), 16)]) fresh_socket_model
      = CheckOk fresh_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 (msg_array_at (Z_to_bv 64 (2 ^ 63)) 1))
      (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 56)])
      fresh_socket_model = CheckReject ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 (msg_array_at (Z_to_bv 64 (2 ^ 47 - 8)) 1))
      (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] []
        [(8192, 56), (Z_to_bv 64 (2 ^ 47 - 8), 16)]) fresh_socket_model
      = CheckOk fresh_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 (msg_array_at (Z_to_bv 64 (2 ^ 47 - 16)) 1))
      (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] []
        [(8192, 56), (Z_to_bv 64 (2 ^ 47 - 16), 16)]) fresh_socket_model
      = CheckOk fresh_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 (msg_array_at (Z_to_bv 64 (2 ^ 47 - 16)) 1))
      (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 56)])
      fresh_socket_model = CheckReject ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 (msg_array_at 12288 2))
      (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 56), (12288, 16)])
      fresh_socket_model = CheckOk fresh_socket_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> io_norm

/-- A DESCRIPTOR'S OWN BASE IS NEVER TESTED: the walk loads the two
fields and refuses only a negative length, so a base no user mapping can
hold — `2^63`, alone, under a zero length, first of two or at index 1 —
is imported as it stands, and the dead socket answers -EPIPE with the
header and each entry read in the ledger; the -EFAULT is the lie.  Linux
refuses each of them from `__import_iovec`'s per-segment `access_ok`
(lib/iov_iter.c:1377-1392, Linux v6.18.46), and from `import_ubuf`'s
(:1437-1438) for a vector of one, which `__import_iovec_ubuf` calls
(:1346, :1360-1361), so every cell here is the model's own.
model: the import, which admits a descriptor base Linux's per-segment `access_ok` refuses and answers the socket's -EPIPE where Linux answers -EFAULT; a divergence restated on the checker so that closing it is a visible flip -/
theorem check_sendmsg_kernel_address_segments_are_not_tested :
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_kbase)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_kbase)
      (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 56), (8320, 16)])
      fresh_socket_model = CheckReject ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_kbase_zero)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_kbase_first_of_two)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16), (8336, 16)])
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_kbase_second)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16), (8336, 16)])
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_kbase_second)
      (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 56), (8320, 16), (8336, 16)])
      fresh_socket_model = CheckReject ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_kbase_zero_first_of_two)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16), (8336, 16)])
      fresh_socket_model = CheckOk fresh_socket_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> io_norm

/-- A NEGATIVE `iov_len` IS -EINVAL, header and descriptor ledgered, and
-EFAULT is the lie.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem check_sendmsg_negative_segment_is_einval :
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_neglen)
      (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 56), (8320, 16)])
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_neglen)
      (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 56), (8320, 16)])
      fresh_socket_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> io_norm

/-- THE TWO GATES AFTER THE IMPORT: a control block declines, while a
control pointer under a zero length is the plain ledgered -EPIPE; a
total one byte past `Uaccess.rw_bytes_max` declines, while the bound
itself is modeled.  The control gate follows the import as the kernel's
own test does: `____sys_sendmsg` tests `msg_controllen` and copies the
block only after `___sys_sendmsg`'s `sendmsg_copy_msghdr` has imported
the vector, so a control block beside a descriptor whose length is
negative is the import's ledgered -EINVAL.
kernel: net/socket.c:____sys_sendmsg,___sys_sendmsg,sendmsg_copy_msghdr; lib/iov_iter.c:__import_iovec,import_ubuf; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem check_sendmsg_control_and_total_gates :
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_ctl)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
      fresh_socket_model = CheckUnmodeled ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_ctlptr)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_big)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
      fresh_socket_model = CheckUnmodeled ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_at_max)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_neglen_ctl)
      (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 56), (8320, 16)])
      fresh_socket_model = CheckOk fresh_socket_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · io_norm
  · io_norm
  · io_norm
  · exact check_sendmsg_complete_ok _ 3 8192 16384 _ _ _ _
      ((sendmsg_total_at_the_bound_is_epipe _).mpr rfl)
  · io_norm

/-- THE DEAD SOCKET'S -EPIPE CARRIES WHAT WAS READ: the header and the one
descriptor for "ab", the header and both descriptors for two, the header
alone for none, on the fresh and the listening socket.  Refused beside
them: -EFAULT and -EAGAIN under the same ledger, the header alone where a
descriptor was read, one descriptor where two were, a zero, and Rocq's
delivery with the payload ledgered.
kernel: net/core/stream.c:sk_stream_wait_connect; lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem check_sendmsg_dead_socket_epipe_carries_the_ledger :
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_ab)
      (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(8192, 56), (8320, 16)])
      fresh_socket_model = CheckReject ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_ab)
      (SyscallEffect.mkEffectU (errno_ret EAGAIN) [] [] [] [] [(8192, 56), (8320, 16)])
      fresh_socket_model = CheckReject ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_ab)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56)])
      fresh_socket_model = CheckReject ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_ab)
      (SyscallEffect.mkEffectU 2 [] [] [] [] [(8192, 56), (8320, 16), (4096, 2)])
      fresh_socket_model = CheckReject ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_two)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16), (8336, 16)])
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_two)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
      fresh_socket_model = CheckReject ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_none)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56)])
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_none)
      (SyscallEffect.mkEffectU 0 [] [] [] [] [(8192, 56)]) fresh_socket_model = CheckReject ∧
    check_sendmsg_row (sendmsg_in 3 8192 16384 msg_ab)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
      listening_socket_model = CheckOk listening_socket_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> io_norm

/-- Rocq's `sendmsg_gathers_onto_the_same_channel`, on its own
`(input, effect)` pair: the gather on the accepted connection declines,
and so does a pending reset's -ECONNRESET, the header and descriptor
ledgered (the mapping above).
kernel: net/ipv4/tcp.c:tcp_sendmsg_locked; net/ipv4/tcp_input.c:tcp_reset@v6.18.46 -/
theorem check_sendmsg_on_a_connection_declines :
    check_sendmsg_row (sendmsg_in 4 8192 16384 msg_ab)
      (SyscallEffect.mkEffectU 2 [] [] [] [] [(8192, 56), (8320, 16), (4096, 2)])
      accepted_socket_model = CheckUnmodeled ∧
    check_sendmsg_row (sendmsg_in 4 8192 16384 msg_ab)
      (SyscallEffect.mkEffectU (errno_ret ECONNRESET) [] [] [] [] [(8192, 56), (8320, 16)])
      (connected_socket_model NRst) = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> io_norm

/-- THE FD IS 32 BITS, at the row: `sendmsg(2^32 + 3, …)` is the fresh
socket's ledgered -EPIPE, and -EBADF is the lie.
kernel: net/socket.c:sendmsg,__sys_sendmsg; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem check_sendmsg_fd_is_32_bits :
    check_sendmsg_row (sendmsg_in (Z_to_bv 64 (2 ^ 32 + 3)) 8192 16384 msg_ab)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_sendmsg_row (sendmsg_in (Z_to_bv 64 (2 ^ 32 + 3)) 8192 16384 msg_ab)
      (mkEffect (errno_ret EBADF) [] []) fresh_socket_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> io_norm

/-! ### recvfrom and recvmsg: the order, then the descriptor

`__sys_recvfrom` (net/socket.c:2270, Linux v6.18.46) imports the buffer
through `import_ubuf` before it resolves the fd; `__sys_recvmsg`
(net/socket.c:2909, Linux v6.18.46) refuses MSG_CMSG_COMPAT, then resolves
the fd before `___sys_recvmsg` copies the header.  Both decline on a
socket — the spec's recv section says why — so every modeled answer is
an argument's or a non-socket descriptor's, and none writes a byte. -/

/-- Rocq's `recv_on_a_non_socket_descriptor`, on `listening_socket_model`
(the mapping above): the channel at 1 is -ENOTSOCK on both calls, never
with a byte written, and MSG_CMSG_COMPAT declines, since its value turns
on CONFIG_COMPAT and nothing a binary can observe says which kernel it
runs on.
kernel: net/socket.c:__sys_recvfrom,__sys_recvmsg@v6.18.46 -/
theorem check_recv_on_a_non_socket_descriptor :
    check_recvfrom_row (recvfrom_in 1 4096 8 0 wmem_open) (mkEffect (errno_ret ENOTSOCK) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_recvfrom_row (recvfrom_in 1 4096 8 0 wmem_open)
      (mkEffect (errno_ret ENOTSOCK) [(4096, [97])] []) listening_socket_model = CheckReject ∧
    check_recvmsg_row (recvmsg_in 1 4096 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      listening_socket_model = CheckOk listening_socket_model [] ∧
    check_recvmsg_row (recvmsg_in 1 4096 (Z_to_bv 64 (2 ^ 31)))
      (mkEffect (errno_ret ENOTSOCK) [] []) listening_socket_model = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> io_norm

/-- Rocq's `recv_declines_a_socket_descriptor`: a socket declines on both
calls whatever its state — fresh at 6 and connected at 9, and here the
reset one at 10 too — offered exactly the -ENOTSOCK a wildcard folding
sockets in would give, while the channel at 0 and the file at 3 still
answer it.
kernel: net/socket.c:__sys_recvfrom,__sys_recvmsg,sock_from_file@v6.18.46 -/
theorem check_recv_declines_a_socket_descriptor :
    check_recvfrom_row (recvfrom_in 6 4096 8 0 wmem_open) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_states_model = CheckUnmodeled ∧
    check_recvmsg_row (recvmsg_in 9 4096 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_states_model = CheckUnmodeled ∧
    check_recvfrom_row (recvfrom_in 10 4096 8 0 wmem_open) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_states_model = CheckUnmodeled ∧
    check_recvfrom_row (recvfrom_in 0 4096 8 0 wmem_open) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_recvmsg_row (recvmsg_in 3 4096 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_states_model = CheckOk socket_states_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> io_norm

/-- Rocq's `recv_argument_order_is_opposite`: the closed 999 with the
pointer `2^63` is -EFAULT from recvfrom, which imports the buffer first,
and -EBADF from recvmsg, which resolves the fd first; each answer is
refused where the other belongs.
kernel: net/socket.c:__sys_recvfrom,__sys_recvmsg; lib/iov_iter.c:import_ubuf@v6.18.46 -/
theorem check_recv_argument_order_is_opposite :
    check_recvfrom_row (recvfrom_in 999 (Z_to_bv 64 (2 ^ 63)) 1 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) socket_call_model = CheckOk socket_call_model [] ∧
    check_recvfrom_row (recvfrom_in 999 (Z_to_bv 64 (2 ^ 63)) 1 0 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) socket_call_model = CheckReject ∧
    check_recvmsg_row (recvmsg_in 999 (Z_to_bv 64 (2 ^ 63)) 0)
      (mkEffect (errno_ret EBADF) [] []) socket_call_model = CheckOk socket_call_model [] ∧
    check_recvmsg_row (recvmsg_in 999 (Z_to_bv 64 (2 ^ 63)) 0)
      (mkEffect (errno_ret EFAULT) [] []) socket_call_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> io_norm

/-- recvfrom's COUNT BOUND, the model's `Uaccess.rw_bytes_max` and not
Linux's, declines before the buffer and the fd — one byte past it the
closed 999 with a destination at `2^63` declines too, where at the bound
itself `import_ubuf`'s -EFAULT answers — and the bound itself is the
channel's -ENOTSOCK.  The channel's destination is readable and writable
throughout (`recvfrom_rw_in`), so qemu-user's `do_recvfrom` locks it
(linux-user/syscall.c:3695-3697, QEMU v11.1.1) and reaches the host's
-ENOTSOCK on either side of the bound: the decline costs that answer.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem check_recvfrom_count_bound :
    check_recvfrom_row (recvfrom_rw_in 0 4096 131073 0 wmem_open)
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model = CheckUnmodeled ∧
    check_recvfrom_row (recvfrom_rw_in 0 4096 131072 0 wmem_open)
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model = CheckOk socket_call_model [] ∧
    check_recvfrom_row (recvfrom_in 999 (Z_to_bv 64 (2 ^ 63)) 131073 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) socket_call_model = CheckUnmodeled ∧
    check_recvfrom_row (recvfrom_in 999 (Z_to_bv 64 (2 ^ 63)) 131072 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) socket_call_model = CheckOk socket_call_model [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> io_norm

/-- THE RANGE, NOT THE MAPPING: a destination whose eight bytes end past
`TASK_SIZE` is -EFAULT on a closed fd, -EBADF the lie, and so is a
zero-length one past `TASK_SIZE` on the channel, -ENOTSOCK refused; a
zero-length one on `TASK_SIZE`'s last page, an unmapped destination in
range, and a readable one nothing may write pass `import_ubuf`, and the
channel is -ENOTSOCK, -EFAULT refused.  Four of those refusals are
qemu-user's answers on some host — `do_recvfrom` locks the destination
for writing before the host call, and hands the host a zero-length
destination whose range the host's own `import_ubuf` tests against the
host's own limit — the Linux-order residuals `recvfrom_spec`'s docstring
reports.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem check_recvfrom_range_not_the_mapping :
    check_recvfrom_row (recvfrom_in 999 (Z_to_bv 64 (2 ^ 47 - 7)) 8 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) socket_call_model = CheckOk socket_call_model [] ∧
    check_recvfrom_row (recvfrom_in 999 (Z_to_bv 64 (2 ^ 47 - 7)) 8 0 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) socket_call_model = CheckReject ∧
    check_recvfrom_row (recvfrom_in 0 (Z_to_bv 64 (2 ^ 47 + 4096)) 0 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) socket_call_model = CheckOk socket_call_model [] ∧
    check_recvfrom_row (recvfrom_in 0 (Z_to_bv 64 (2 ^ 47 + 4096)) 0 0 (fun _ => none))
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model = CheckReject ∧
    check_recvfrom_row (recvfrom_in 0 (Z_to_bv 64 (2 ^ 47 - 8)) 0 0 (fun _ => none))
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model = CheckOk socket_call_model [] ∧
    check_recvfrom_row (recvfrom_in 0 (Z_to_bv 64 (2 ^ 47 - 8)) 0 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) socket_call_model = CheckReject ∧
    check_recvfrom_row (recvfrom_in 0 46912512909312 8 0 (fun _ => none))
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model = CheckOk socket_call_model [] ∧
    check_recvfrom_row (recvfrom_in 0 46912512909312 8 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) socket_call_model = CheckReject ∧
    check_recvfrom_row
      (SyscallInput.mkInput 207 [0, 4096, 8, 0, 0, 0] (fun _ => some 0) (fun _ => none))
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model = CheckOk socket_call_model [] ∧
    check_recvfrom_row
      (SyscallInput.mkInput 207 [0, 4096, 8, 0, 0, 0] (fun _ => some 0) (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) socket_call_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> io_norm

/-- recvfrom's DESCRIPTOR ANSWER: the closed 9 is -EBADF, -ENOTSOCK the
lie; every non-socket kind is -ENOTSOCK, -EBADF the lie beside the pipe;
MSG_PEEK in a3 is never read; and a zero is refused, since no byte is
read at all.
kernel: net/socket.c:__sys_recvfrom,sock_from_file@v6.18.46 -/
theorem check_recvfrom_descriptor_answer :
    check_recvfrom_row (recvfrom_in 9 4096 8 0 wmem_open) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_recvfrom_row (recvfrom_in 9 4096 8 0 wmem_open) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckReject ∧
    check_recvfrom_row (recvfrom_in 3 4096 8 0 wmem_open) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_recvfrom_row (recvfrom_in 4 4096 8 0 wmem_open) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_recvfrom_row (recvfrom_in 5 4096 8 0 wmem_open) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_recvfrom_row (recvfrom_in 6 4096 8 0 wmem_open) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_recvfrom_row (recvfrom_in 7 4096 8 0 wmem_open) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_recvfrom_row (recvfrom_in 8 4096 8 0 wmem_open) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_recvfrom_row (recvfrom_in 6 4096 8 0 wmem_open) (mkEffect (errno_ret EBADF) [] [])
      socket_kinds_model = CheckReject ∧
    check_recvfrom_row (recvfrom_in 0 4096 8 2 wmem_open) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_recvfrom_row (recvfrom_in 0 4096 8 0 wmem_open) (mkEffect 0 [] [])
      socket_call_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> io_norm

/-- recvmsg's DESCRIPTOR ANSWER: the closed 9 is -EBADF; the file at 3 is
-ENOTSOCK with the header pointer at `2^63`, never read, so -EFAULT is the
lie; the pipe, /dev/null and /dev/urandom are -ENOTSOCK; and a byte
written beside the channel's -ENOTSOCK is refused.
kernel: net/socket.c:__sys_recvmsg,sock_from_file,copy_msghdr_from_user@v6.18.46 -/
theorem check_recvmsg_descriptor_answer :
    check_recvmsg_row (recvmsg_in 9 4096 0) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_recvmsg_row (recvmsg_in 3 (Z_to_bv 64 (2 ^ 63)) 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_recvmsg_row (recvmsg_in 3 (Z_to_bv 64 (2 ^ 63)) 0) (mkEffect (errno_ret EFAULT) [] [])
      socket_call_model = CheckReject ∧
    check_recvmsg_row (recvmsg_in 6 4096 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_recvmsg_row (recvmsg_in 7 4096 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_recvmsg_row (recvmsg_in 8 4096 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_recvmsg_row (recvmsg_in 0 4096 0) (mkEffect (errno_ret ENOTSOCK) [(4096, [97])] [])
      socket_call_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> io_norm

/-- MSG_CMSG_COMPAT DECLINES BEFORE THE FD — `__sys_recvmsg` tests it
(net/socket.c:2915-2916, Linux v6.18.46) before `CLASS(fd, f)` (:2918),
so the closed 9 declines under it as the channel does — while bit 32
alone is the empty flag word and the channel's -ENOTSOCK.
kernel: net/socket.c:recvmsg,__sys_recvmsg@v6.18.46 -/
theorem check_recvmsg_cmsg_compat_declines :
    check_recvmsg_row (recvmsg_in 0 4096 (Z_to_bv 64 (2 ^ 31)))
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model = CheckUnmodeled ∧
    check_recvmsg_row (recvmsg_in 9 4096 (Z_to_bv 64 (2 ^ 31)))
      (mkEffect (errno_ret EBADF) [] []) socket_call_model = CheckUnmodeled ∧
    check_recvmsg_row (recvmsg_in 0 4096 (Z_to_bv 64 (2 ^ 32)))
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model = CheckOk socket_call_model [] := by
  refine ⟨?_, ?_, ?_⟩ <;> io_norm

/-- THE FD IS 32 BITS on both receives, at the row: `recvfrom(2^32, …)` is
the channel at 0 and `recvmsg(2^32 + 3, …)` the file at 3, each -ENOTSOCK,
and the -EBADF a whole-register lookup would find is the lie.  recvfrom's
destination is readable and writable (`recvfrom_rw_in`), which qemu-user's
`do_recvfrom` locks before its host call (linux-user/syscall.c:3695-3697,
QEMU v11.1.1), and its fd parameter is an int (:3683), so -ENOTSOCK is
qemu-user's answer there as well.
kernel: net/socket.c:recvfrom,recvmsg,__sys_recvfrom,__sys_recvmsg@v6.18.46 -/
theorem check_recv_fd_is_32_bits :
    check_recvfrom_row (recvfrom_rw_in (Z_to_bv 64 (2 ^ 32)) 4096 8 0 wmem_open)
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model = CheckOk socket_call_model [] ∧
    check_recvfrom_row (recvfrom_rw_in (Z_to_bv 64 (2 ^ 32)) 4096 8 0 wmem_open)
      (mkEffect (errno_ret EBADF) [] []) socket_call_model = CheckReject ∧
    check_recvmsg_row (recvmsg_in (Z_to_bv 64 (2 ^ 32 + 3)) 4096 0)
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model = CheckOk socket_call_model [] ∧
    check_recvmsg_row (recvmsg_in (Z_to_bv 64 (2 ^ 32 + 3)) 4096 0)
      (mkEffect (errno_ret EBADF) [] []) socket_call_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> io_norm

/-- THE RANGE TEST'S EDGES on recvfrom: eight bytes ending exactly at
`TASK_SIZE`, at `2^47 - 8`, pass `import_ubuf`'s range test
(lib/iov_iter.c:1437-1438, Linux v6.18.46), so the closed 999 is -EBADF,
-EFAULT the lie; a zero-length destination at `TASK_SIZE` itself passes
too, the channel's -ENOTSOCK with -EFAULT refused, and one byte past it
does not, -EFAULT with -ENOTSOCK refused.  Each refusal is qemu-user's
answer on some host, as four in `check_recvfrom_range_not_the_mapping`
are: the eight-byte lock fails on the unmapped page, and the host's own
`import_ubuf` refuses a zero-length `2^47` on a 4-level x86-64 host,
whose limit is `2^47 - 4096`, and passes `2^47 + 1` on an LA57 one — the
Linux-order residuals `recvfrom_spec`'s docstring reports.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem check_recvfrom_range_edges :
    check_recvfrom_row (recvfrom_in 999 (Z_to_bv 64 (2 ^ 47 - 8)) 8 0 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) socket_call_model = CheckOk socket_call_model [] ∧
    check_recvfrom_row (recvfrom_in 999 (Z_to_bv 64 (2 ^ 47 - 8)) 8 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) socket_call_model = CheckReject ∧
    check_recvfrom_row (recvfrom_in 0 (Z_to_bv 64 (2 ^ 47)) 0 0 (fun _ => none))
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model = CheckOk socket_call_model [] ∧
    check_recvfrom_row (recvfrom_in 0 (Z_to_bv 64 (2 ^ 47)) 0 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) socket_call_model = CheckReject ∧
    check_recvfrom_row (recvfrom_in 0 (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) socket_call_model = CheckOk socket_call_model [] ∧
    check_recvfrom_row (recvfrom_in 0 (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 (fun _ => none))
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> io_norm

/-- Rocq's `socket_calls_on_a_pipe_end_are_enotsock`, from
`Checks/Cases/Fs/Pipe.v`: a pipe end is open and is not a socket, its
`f_op` `pipeanon_fops` and not `socket_file_ops`, so `sock_from_file`
(net/socket.c:530-536, Linux v6.18.46) answers NULL and bind on the read
end, and recvfrom on either end, are -ENOTSOCK — bind through its
non-socket arm and recvfrom through `sockfd_lookup_errno`'s enumeration,
the two shapes Rocq's example asks.  Rocq's read end at 3 is
`socket_kinds_model`'s 6, and its write end at 4 `pipe_write_end_model`'s
(the mapping above).
kernel: net/socket.c:__sys_bind,__sys_recvfrom,sock_from_file; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem check_socket_calls_on_a_pipe_end_are_enotsock :
    check_bind_row (bind_in 6 0 0 (fun _ => none)) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_recvfrom_row (recvfrom_in 6 0 0 0 (fun _ => none))
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_recvfrom_row (recvfrom_in 6 0 0 0 (fun _ => none))
      (mkEffect (errno_ret ENOTSOCK) [] []) pipe_write_end_model
      = CheckOk pipe_write_end_model [] := by
  refine ⟨?_, ?_, ?_⟩
  · check_norm
  · io_norm
  · io_norm

/-- Rocq's `socket_calls_on_a_pipe_end_reject_ebadf`: -EBADF is the answer
of a descriptor that is not open (`fd_empty`, ahead of `sock_from_file`
in both `__sys_bind` and `__sys_recvfrom`), so refusing it on the pipe
ends pins that a pipe end is an open descriptor which merely is not a
socket — on the read end for both calls, as Rocq's example asks, and on
the write end for recvfrom.
kernel: net/socket.c:__sys_bind,__sys_recvfrom,sock_from_file@v6.18.46 -/
theorem check_socket_calls_on_a_pipe_end_reject_ebadf :
    check_recvfrom_row (recvfrom_in 6 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) socket_kinds_model = CheckReject ∧
    check_bind_row (bind_in 6 0 0 (fun _ => none)) (mkEffect (errno_ret EBADF) [] [])
      socket_kinds_model = CheckReject ∧
    check_recvfrom_row (recvfrom_in 6 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) pipe_write_end_model = CheckReject := by
  refine ⟨?_, ?_, ?_⟩
  · io_norm
  · check_norm
  · io_norm

/-! ### The five witnesses -/

/-- Open the five witnesses and the range verdict's, and decide what is
closed. -/
scoped macro "io_witness_open" cfg:Lean.Parser.Tactic.optConfig : tactic =>
  `(tactic| simp $cfg:optConfig only [sendto_witness, sendmsg_witness, recvfrom_witness,
      recvmsg_witness, send_on_socket_witness, access_ok_zero_witness,
      ret_outcome, outcome_copyins, with_copyins, List.append_nil, List.nil_append,
      List.cons_append,
      Bool.and_eq_true, Bool.or_eq_true, ne_eq, reduceCtorEq, sys_simp, ↓reduceIte])

/-- Evaluate a closed call of one of the five witnesses. -/
scoped macro "io_witness_norm" : tactic =>
  `(tactic| (io_witness_open +decide;
             first | done | sys_simp_pass +ground +decide -failIfUnchanged;
             first | done | io_witness_open +ground +decide))

/-- The socket half both sends share, arm by arm: a socket with no
connection is -EPIPE with `pre` as its whole ledger, and a connection —
a pending reset, or a FIN at the head — is `Unmodeled`.
kernel: net/core/stream.c:sk_stream_wait_connect; net/ipv4/tcp_input.c:tcp_reset@v6.18.46 -/
theorem send_on_socket_witness_names_each_arm :
    send_on_socket_witness [(8192, 56)] (fun _ => []) 3 .SkFresh 1 [97] fresh_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56)])
           fresh_socket_model [] ∧
    send_on_socket_witness [] (fun _ => []) 4 (.SkConnected peer0 3 NRst) 1 [97]
      (connected_socket_model NRst) = Unmodeled ∧
    send_on_socket_witness [] (fun _ => []) 4 (.SkConnected peer0 3 NFin) 1 [97]
      accepted_socket_model = Unmodeled := by
  refine ⟨?_, ?_, ?_⟩ <;> io_witness_norm

/-- sendto's witness, arm by arm: `Unmodeled` on a flagless send, on a
destination address and on a count past the bound, each also beside a
buffer at `2^63` and the closed 9; -EFAULT on that buffer, before the
closed fd, once the three pass; -EBADF on the closed fd; -ENOTSOCK on the
channel; -EPIPE on the fresh socket, and at the count's bound itself;
`Unmodeled` on the accepted connection.  The witness takes no `addrlen`,
as the checker does not: the length reaches the spec and no arm of it.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_sendto; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendto_witness_names_each_arm :
    sendto_witness 3 4096 1 0 0 (sendto_in 3 4096 1 0 0 0 mem_ab) fresh_socket_model
      = Unmodeled ∧
    sendto_witness 3 4096 1 16384 8192 (sendto_in 3 4096 1 16384 8192 16 mem_ab)
      fresh_socket_model = Unmodeled ∧
    sendto_witness 3 4096 131073 16384 0 (sendto_in 3 4096 131073 16384 0 0 mem_ab)
      fresh_socket_model = Unmodeled ∧
    sendto_witness 9 (Z_to_bv 64 (2 ^ 63)) 1 0
      0 (sendto_in 9 (Z_to_bv 64 (2 ^ 63)) 1 0 0 0 mem_ab) fresh_socket_model = Unmodeled ∧
    sendto_witness 9 (Z_to_bv 64 (2 ^ 63)) 1 16384
      8192 (sendto_in 9 (Z_to_bv 64 (2 ^ 63)) 1 16384 8192 16 mem_ab) fresh_socket_model
      = Unmodeled ∧
    sendto_witness 9 (Z_to_bv 64 (2 ^ 63)) 131073 16384
      0 (sendto_in 9 (Z_to_bv 64 (2 ^ 63)) 131073 16384 0 0 mem_ab) fresh_socket_model
      = Unmodeled ∧
    sendto_witness 9 (Z_to_bv 64 (2 ^ 63)) 1 16384
      0 (sendto_in 9 (Z_to_bv 64 (2 ^ 63)) 1 16384 0 0 mem_ab) fresh_socket_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model [] ∧
    sendto_witness 9 4096 1 16384 0 (sendto_in 9 4096 1 16384 0 0 mem_ab) fresh_socket_model
      = Ok (mkEffect (errno_ret EBADF) [] []) fresh_socket_model [] ∧
    sendto_witness 1 4096 1 16384 0 (sendto_in 1 4096 1 16384 0 0 mem_ab) fresh_socket_model
      = Ok (mkEffect (errno_ret ENOTSOCK) [] []) fresh_socket_model [] ∧
    sendto_witness 3 4096 1 16384 0 (sendto_in 3 4096 1 16384 0 0 mem_ab) fresh_socket_model
      = Ok (mkEffect (errno_ret EPIPE) [] []) fresh_socket_model [] ∧
    sendto_witness 3 4096 131072 16384 0 (sendto_in 3 4096 131072 16384 0 0 rmem_open)
      fresh_socket_model = Ok (mkEffect (errno_ret EPIPE) [] []) fresh_socket_model [] ∧
    sendto_witness 4 4096 2 16384 0 (sendto_in 4 4096 2 16384 0 0 mem_ab) accepted_socket_model
      = Unmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · io_witness_norm
  · io_witness_norm
  · io_witness_norm
  · io_witness_norm
  · io_witness_norm
  · io_witness_norm
  · io_witness_norm
  · io_witness_norm
  · io_witness_norm
  · io_witness_norm
  · simp only [sendto_witness, sendto_in.eq_1]
    rfl
  · io_witness_norm

/-- sendmsg's witness at the flag word and the descriptor, arm by arm:
`Unmodeled` on a flagless send, on the socket and ahead of the closed fd;
-EBADF on the closed fd; -ENOTSOCK on each of the seven other kinds, one
arm each.  The header arms, the heap band and the import and socket
arms are the next three pins, one pin split in four for the elaborator's
heartbeat budget.
kernel: net/socket.c:__sys_sendmsg@v6.18.46 -/
theorem sendmsg_witness_names_each_descriptor_arm :
    sendmsg_witness 3 8192 0 (sendmsg_in 3 8192 0 msg_ab) fresh_socket_model = Unmodeled ∧
    sendmsg_witness 9 8192 0 (sendmsg_in 9 8192 0 msg_ab) fresh_socket_model = Unmodeled ∧
    sendmsg_witness 9 8192 16384 (sendmsg_in 9 8192 16384 msg_ab) fresh_socket_model
      = Ok (mkEffect (errno_ret EBADF) [] []) fresh_socket_model [] ∧
    sendmsg_witness 1 8192 16384 (sendmsg_in 1 8192 16384 msg_ab) fresh_socket_model
      = Ok (mkEffect (errno_ret ENOTSOCK) [] []) fresh_socket_model [] ∧
    sendmsg_witness 3 8192 16384 (sendmsg_in 3 8192 16384 msg_ab) socket_call_model
      = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] ∧
    sendmsg_witness 4 8192 16384 (sendmsg_in 4 8192 16384 msg_ab) socket_call_model
      = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] ∧
    sendmsg_witness 5 8192 16384 (sendmsg_in 5 8192 16384 msg_ab) socket_call_model
      = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] ∧
    sendmsg_witness 6 8192 16384 (sendmsg_in 6 8192 16384 msg_ab) socket_kinds_model
      = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model [] ∧
    sendmsg_witness 7 8192 16384 (sendmsg_in 7 8192 16384 msg_ab) socket_kinds_model
      = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model [] ∧
    sendmsg_witness 8 8192 16384 (sendmsg_in 8 8192 16384 msg_ab) socket_kinds_model
      = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_kinds_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> io_witness_norm

/-- sendmsg's witness at the header, arm by arm: -EFAULT on an unreadable
header; `Unmodeled` on a named header, beside `msg_iovlen` 1025 or a
kernel descriptor too, and the ledgered -EPIPE on a NULL `msg_name`
beside a negative `msg_namelen`, so the gate reads the pointer and not
the length; -EMSGSIZE past `UIO_MAXIOV`, on the full 64-bit `2^32 + 1`
too, the header ledgered.
kernel: net/socket.c:copy_msghdr_from_user,__copy_msghdr; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_witness_names_each_header_arm :
    sendmsg_witness 3 8192 16384 (sendmsg_in 3 8192 16384 (fun _ => none)) fresh_socket_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) fresh_socket_model [] ∧
    sendmsg_witness 3 8192 16384 (sendmsg_in 3 8192 16384 msg_named) fresh_socket_model
      = Unmodeled ∧
    sendmsg_witness 3 8192 16384
      (sendmsg_in 3 8192 16384 (send_msghdr_mem 4096 16 1025 0 0 0 [(4096, 2)]))
      fresh_socket_model = Unmodeled ∧
    sendmsg_witness 3 8192 16384
      (sendmsg_in 3 8192 16384 (send_msghdr_mem 4096 16 1 0 0 0 [(Z_to_bv 64 (2 ^ 63), 1)]))
      fresh_socket_model = Unmodeled ∧
    sendmsg_witness 3 8192 16384 (sendmsg_in 3 8192 16384 msg_negnamelen) fresh_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
           fresh_socket_model [] ∧
    sendmsg_witness 3 8192 16384 (sendmsg_in 3 8192 16384 msg_iovlen_1025) fresh_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EMSGSIZE) [] [] [] [] [(8192, 56)])
           fresh_socket_model [] ∧
    sendmsg_witness 3 8192 16384 (sendmsg_in 3 8192 16384 msg_iovlen_wide) fresh_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EMSGSIZE) [] [] [] [] [(8192, 56)])
           fresh_socket_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> io_witness_norm

/-- sendmsg's witness in the heap band, `check_sendmsg_heap_band_declines`'s
cells as the witness names them: `Unmodeled` from nine descriptors up to
`UIO_MAXIOV` itself, and at `UIO_FASTIOV`, eight, the -EPIPE with the
header and all eight descriptors ledgered.
kernel: lib/iov_iter.c:__import_iovec,iovec_from_user; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_witness_heap_band_declines :
    sendmsg_witness 3 8192 16384 (sendmsg_in 3 8192 16384 msg_iovlen_9) fresh_socket_model
      = Unmodeled ∧
    sendmsg_witness 3 8192 16384 (sendmsg_in 3 8192 16384 msg_iovlen_1024) fresh_socket_model
      = Unmodeled ∧
    sendmsg_witness 3 8192 16384 (sendmsg_in 3 8192 16384 msg_eight) fresh_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] []
             [(8192, 56), (8320, 16), (8336, 16), (8352, 16), (8368, 16),
              (8384, 16), (8400, 16), (8416, 16), (8432, 16)])
           fresh_socket_model [] := by
  refine ⟨?_, ?_, ?_⟩ <;> io_witness_norm

/-- sendmsg's witness at the import and the socket, arm by arm: the
ledgered -EPIPE on a descriptor naming a kernel address, which the
import does not test, and `Unmodeled` where a control block follows one;
-EINVAL on a negative length; `Unmodeled` on a control block, and the
ledgered -EPIPE on a control pointer under a zero length, so the gate
reads the length and not the pointer; `Unmodeled` on a total past the
bound, and the ledgered -EPIPE at the bound itself; the ledgered -EPIPE
on the fresh socket; `Unmodeled` on the accepted connection.
kernel: net/socket.c:____sys_sendmsg; lib/iov_iter.c:__import_iovec,copy_iovec_from_user,import_ubuf; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem sendmsg_witness_names_each_import_arm :
    sendmsg_witness 3 8192 16384 (sendmsg_in 3 8192 16384 msg_kbase) fresh_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
           fresh_socket_model [] ∧
    sendmsg_witness 3 8192 16384
      (sendmsg_in 3 8192 16384 (send_msghdr_mem 0 0 1 8400 16 0 [(Z_to_bv 64 (2 ^ 63), 1)]))
      fresh_socket_model = Unmodeled ∧
    sendmsg_witness 3 8192 16384 (sendmsg_in 3 8192 16384 msg_kbase_second) fresh_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] []
             [(8192, 56), (8320, 16), (8336, 16)]) fresh_socket_model [] ∧
    sendmsg_witness 3 8192 16384 (sendmsg_in 3 8192 16384 msg_neglen) fresh_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(8192, 56), (8320, 16)])
           fresh_socket_model [] ∧
    sendmsg_witness 3 8192 16384 (sendmsg_in 3 8192 16384 msg_ctl) fresh_socket_model
      = Unmodeled ∧
    sendmsg_witness 3 8192 16384 (sendmsg_in 3 8192 16384 msg_ctlptr) fresh_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
           fresh_socket_model [] ∧
    sendmsg_witness 3 8192 16384 (sendmsg_in 3 8192 16384 msg_big) fresh_socket_model
      = Unmodeled ∧
    sendmsg_witness 3 8192 16384 (sendmsg_in 3 8192 16384 msg_at_max) fresh_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
           fresh_socket_model [] ∧
    sendmsg_witness 3 8192 16384 (sendmsg_in 3 8192 16384 msg_ab) fresh_socket_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8192, 56), (8320, 16)])
           fresh_socket_model [] ∧
    sendmsg_witness 4 8192 16384 (sendmsg_in 4 8192 16384 msg_ab) accepted_socket_model
      = Unmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · io_witness_norm
  · io_witness_norm
  · io_witness_norm
  · io_witness_norm
  · io_witness_norm
  · io_witness_norm
  · io_witness_norm
  · simp only [sendmsg_witness, sendmsg_in.eq_1,
      show fd_lookup (m_fds fresh_socket_model) 3 = some (.FdSocket .SkFresh) from rfl,
      show read_bytes_map msg_at_max 8192 (Z_to_bv 64 MSGHDR_SIZE)
        = some (msghdr_bytes 0 0 1 0 0 0) by decide]
    simp only [show le_bytes_to_word ((msghdr_bytes 0 0 1 0 0 0).take 8) = 0 by decide,
      show le_bytes_to_word (((msghdr_bytes 0 0 1 0 0 0).drop 16).take 8) = 8320 by decide,
      show le_bytes_to_word (((msghdr_bytes 0 0 1 0 0 0).drop 24).take 8) = 1 by decide,
      show le_bytes_to_word (((msghdr_bytes 0 0 1 0 0 0).drop 40).take 8) = 0 by decide,
      show copy_iovecs_aux msg_at_max 8320 (word_to_nat 1) = .ImpOk [(16384, 131072)] by decide,
      show copy_iovecs_accesses msg_at_max 8320 (word_to_nat 1) = [(8320, 16)] by decide]
    rfl
  · io_witness_norm
  · io_witness_norm

/-- recvfrom's witness, arm by arm: `Unmodeled` past the count's bound,
also beside a destination at `2^63` and the closed 999; -EFAULT on that
destination, before the closed fd, within the bound, on one whose eight
bytes end past `TASK_SIZE`, and on a zero-length one past it; -EBADF on
the closed fd; -ENOTSOCK on the channel, at the count's bound itself, and
on a zero-length destination on `TASK_SIZE`'s last page; `Unmodeled` on a
socket.
kernel: lib/iov_iter.c:import_ubuf; net/socket.c:__sys_recvfrom@v6.18.46 -/
theorem recvfrom_witness_names_each_arm :
    recvfrom_witness 0 4096 131073 (recvfrom_in 0 4096 131073 0 wmem_open) socket_call_model
      = Unmodeled ∧
    recvfrom_witness 999 (Z_to_bv 64 (2 ^ 63)) 131073
      (recvfrom_in 999 (Z_to_bv 64 (2 ^ 63)) 131073 0 (fun _ => none)) socket_call_model
      = Unmodeled ∧
    recvfrom_witness 999 (Z_to_bv 64 (2 ^ 63)) 1
      (recvfrom_in 999 (Z_to_bv 64 (2 ^ 63)) 1 0 (fun _ => none)) socket_call_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) socket_call_model [] ∧
    recvfrom_witness 999 (Z_to_bv 64 (2 ^ 47 - 7)) 8
      (recvfrom_in 999 (Z_to_bv 64 (2 ^ 47 - 7)) 8 0 (fun _ => none)) socket_call_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) socket_call_model [] ∧
    recvfrom_witness 0 (Z_to_bv 64 (2 ^ 47 + 4096)) 0
      (recvfrom_in 0 (Z_to_bv 64 (2 ^ 47 + 4096)) 0 0 (fun _ => none)) socket_call_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) socket_call_model [] ∧
    recvfrom_witness 0 (Z_to_bv 64 (2 ^ 47 - 8)) 0
      (recvfrom_in 0 (Z_to_bv 64 (2 ^ 47 - 8)) 0 0 (fun _ => none)) socket_call_model
      = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] ∧
    recvfrom_witness 9 4096 8 (recvfrom_in 9 4096 8 0 wmem_open) socket_call_model
      = Ok (mkEffect (errno_ret EBADF) [] []) socket_call_model [] ∧
    recvfrom_witness 0 4096 8 (recvfrom_in 0 4096 8 0 wmem_open) socket_call_model
      = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] ∧
    recvfrom_witness 0 4096 131072 (recvfrom_in 0 4096 131072 0 wmem_open) socket_call_model
      = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] ∧
    recvfrom_witness 6 4096 8 (recvfrom_in 6 4096 8 0 wmem_open) socket_states_model
      = Unmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> io_witness_norm

/-- recvmsg's witness, arm by arm: `Unmodeled` under MSG_CMSG_COMPAT, on
the channel and ahead of the closed fd; -EBADF on the closed fd;
-ENOTSOCK on the channel, with bit 32 alone set too; `Unmodeled` on a
socket.
kernel: net/socket.c:__sys_recvmsg@v6.18.46 -/
theorem recvmsg_witness_names_each_arm :
    recvmsg_witness 0 (Z_to_bv 64 (2 ^ 31)) socket_call_model = Unmodeled ∧
    recvmsg_witness 9 (Z_to_bv 64 (2 ^ 31)) socket_call_model = Unmodeled ∧
    recvmsg_witness 9 0 socket_call_model
      = Ok (mkEffect (errno_ret EBADF) [] []) socket_call_model [] ∧
    recvmsg_witness 0 0 socket_call_model
      = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] ∧
    recvmsg_witness 0 (Z_to_bv 64 (2 ^ 32)) socket_call_model
      = Ok (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model [] ∧
    recvmsg_witness 9 0 socket_states_model = Unmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> io_witness_norm

end IO

-- lean-port sentinel: ticket V-Net-Socket-options appends below this line
section V_Net_Socket_options

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Progress

/-! ## V-Net-Socket-options — option calls over the real table

Rocq's option examples are restated at their existing row fixtures with
`_over_the_real_table` appended to the Rocq name. The multi-call
`socket_calls_decline_every_non_socket_fd_kind` is split into its 208
and 209 columns (including the row twins' additional fd kinds);
`socket_calls_unknown_level_never_beats_the_fd` keeps its 208/209 cells;
`socket_calls_null_pointers_never_beat_the_fd` has only a 209 cell in
Rocq's option group. Their suffixes name those columns. The ledger twin
expands `getsockopt_answering` at the same arguments to expose
`check_syscall`, reusing its input and memory fixtures.

The row's existing normalization machinery runs after a table-lookup
rewrite. These pins also hold the arm's argument reading: a0 through
`fd32`, a1 through `int32`, and getsockopt's a4 whole. No verdict
separates setsockopt's `int32 a4` from a whole a4, because `int32_neg`
reads the low half itself; `arm_setsockopt` holds the narrowing and
`setsockopt_optlen_high_half_is_discarded_over_the_real_table` pins the
observable length test.

The kernel citations below refer to Linux v6.18.46, commit 1f99e9ab748f.
The checker's documented version premises still apply: registering the
arm does not remove the pre-v6.7 length-order or pre-v6.11 copy-in gap
recorded in bugs/setsockopt-getsockopt-orders-rest-on-v6.7-and-v6.11.md. -/

/-- The table lookup is independent of registers and memory.
model: lookup_ca over checked_table at 208 -/
theorem lookup_setsockopt_input (args : List word) (mem wmem : word → Option byte) :
    lookup_ca checked_table (bv_unsigned (SyscallInput.mkInput 208 args mem wmem).in_sysno)
      = some arm_setsockopt :=
  lookup_ca_checked_table_setsockopt

/-- Cross the lookup once, leaving the existing row normalizer its input.
model: check_syscall dispatches the registered 208 arm at the same input -/
theorem dispatch_setsockopt_input (args : List word) (mem wmem : word → Option byte)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (SyscallInput.mkInput 208 args mem wmem) eff m
      = check_setsockopt_row (SyscallInput.mkInput 208 args mem wmem) eff m := rfl

/-- The table lookup is independent of registers and memory.
model: lookup_ca over checked_table at 209 -/
theorem lookup_getsockopt_input (args : List word) (mem wmem : word → Option byte) :
    lookup_ca checked_table (bv_unsigned (SyscallInput.mkInput 209 args mem wmem).in_sysno)
      = some arm_getsockopt :=
  lookup_ca_checked_table_getsockopt

/-- Cross the lookup once, leaving the existing row normalizer its input.
model: check_syscall dispatches the registered 209 arm at the same input -/
theorem dispatch_getsockopt_input (args : List word) (mem wmem : word → Option byte)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (SyscallInput.mkInput 209 args mem wmem) eff m
      = check_getsockopt_row (SyscallInput.mkInput 209 args mem wmem) eff m := rfl

/-- Reuse the option normalizer after resolving the real table lookup. -/
scoped macro "options_table_norm" : tactic =>
  `(tactic| (simp only [setsockopt_in, setsockopt_in_mem, getsockopt_in,
      socket_call_in, socket_call_null_in, dispatch_setsockopt_input, dispatch_getsockopt_input]; options_norm))

/-- The 208 column: net/socket.c:2380-2384 resolves the fd before the option.
The accepted non-socket errno and the EBADF/success lies are the row twin above.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt,do_sock_setsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem socket_calls_decline_every_non_socket_fd_kind_208_over_the_real_table :
    check_syscall (socket_call_in 208 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_syscall (socket_call_in 208 3) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_syscall (socket_call_in 208 4) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_syscall (socket_call_in 208 5) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_syscall (socket_call_in 208 6) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_syscall (socket_call_in 208 7) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_syscall (socket_call_in 208 8) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_syscall (socket_call_in 208 0) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_syscall (socket_call_in 208 0) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_syscall (socket_call_in 208 3) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_syscall (socket_call_in 208 3) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_syscall (socket_call_in 208 4) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_syscall (socket_call_in 208 4) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_syscall (socket_call_in 208 5) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_syscall (socket_call_in 208 5) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_syscall (socket_call_in 208 6) (mkEffect (errno_ret EBADF) [] [])
      socket_kinds_model = CheckReject ∧
    check_syscall (socket_call_in 208 6) (mkEffect 0 [] []) socket_kinds_model
      = CheckReject ∧
    check_syscall (socket_call_in 208 7) (mkEffect (errno_ret EBADF) [] [])
      socket_kinds_model = CheckReject ∧
    check_syscall (socket_call_in 208 7) (mkEffect 0 [] []) socket_kinds_model
      = CheckReject ∧
    check_syscall (socket_call_in 208 8) (mkEffect (errno_ret EBADF) [] [])
      socket_kinds_model = CheckReject ∧
    check_syscall (socket_call_in 208 8) (mkEffect 0 [] []) socket_kinds_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    options_table_norm

/-- The 209 column: net/socket.c:2445-2449 resolves the fd before the option.
The accepted non-socket errno and the EBADF/success lies are the row twin above.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt,do_sock_setsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem socket_calls_decline_every_non_socket_fd_kind_209_over_the_real_table :
    check_syscall (socket_call_in 209 0) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_syscall (socket_call_in 209 3) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_syscall (socket_call_in 209 4) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_syscall (socket_call_in 209 5) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_syscall (socket_call_in 209 6) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_syscall (socket_call_in 209 7) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_syscall (socket_call_in 209 8) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_kinds_model = CheckOk socket_kinds_model [] ∧
    check_syscall (socket_call_in 209 0) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_syscall (socket_call_in 209 0) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_syscall (socket_call_in 209 3) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_syscall (socket_call_in 209 3) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_syscall (socket_call_in 209 4) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_syscall (socket_call_in 209 4) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_syscall (socket_call_in 209 5) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckReject ∧
    check_syscall (socket_call_in 209 5) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_syscall (socket_call_in 209 6) (mkEffect (errno_ret EBADF) [] [])
      socket_kinds_model = CheckReject ∧
    check_syscall (socket_call_in 209 6) (mkEffect 0 [] []) socket_kinds_model
      = CheckReject ∧
    check_syscall (socket_call_in 209 7) (mkEffect (errno_ret EBADF) [] [])
      socket_kinds_model = CheckReject ∧
    check_syscall (socket_call_in 209 7) (mkEffect 0 [] []) socket_kinds_model
      = CheckReject ∧
    check_syscall (socket_call_in 209 8) (mkEffect (errno_ret EBADF) [] [])
      socket_kinds_model = CheckReject ∧
    check_syscall (socket_call_in 209 8) (mkEffect 0 [] []) socket_kinds_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    options_table_norm

/-- Rocq's fd precedence cells, with the row twin's additional lies:
net/socket.c:2380-2386 and :2445-2452 return the descriptor errno
before entering the option path.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt,do_sock_setsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem socket_calls_unknown_level_never_beats_the_fd_208_209_over_the_real_table :
    check_syscall (socket_call_in 208 9) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_syscall (socket_call_in 209 9) (mkEffect (errno_ret EBADF) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_syscall (socket_call_in 208 3) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_syscall (socket_call_in 209 3) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_syscall (socket_call_in 208 3) (mkEffect (errno_ret ENOPROTOOPT) [] [])
      socket_call_model = CheckReject ∧
    check_syscall (socket_call_in 209 3) (mkEffect (errno_ret ENOPROTOOPT) [] [])
      socket_call_model = CheckReject ∧
    check_syscall (socket_call_in 209 3) (mkEffect (errno_ret EOPNOTSUPP) [] [])
      socket_call_model = CheckReject ∧
    check_syscall (socket_call_in 208 9) (mkEffect (errno_ret ENOPROTOOPT) [] [])
      socket_call_model = CheckReject ∧
    check_syscall (socket_call_in 209 9) (mkEffect (errno_ret EOPNOTSUPP) [] [])
      socket_call_model = CheckReject ∧
    check_syscall (socket_call_in 208 9) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckReject ∧
    check_syscall (socket_call_in 208 9) (mkEffect 0 [] []) socket_call_model
      = CheckReject ∧
    check_syscall (socket_call_in 209 9) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckReject ∧
    check_syscall (socket_call_in 209 9) (mkEffect 0 [] []) socket_call_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> options_table_norm

/-- The negative length test at net/socket.c:2335-2336 follows fd lookup
at :2380-2386. This is the pinned kernel's order, with the version
premise recorded in the section header.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt,do_sock_setsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem setsockopt_negative_optlen_never_beats_the_fd_over_the_real_table :
    check_syscall (setsockopt_in 9 1 2 4096 (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect (errno_ret EBADF) [] []) socket_call_model = CheckOk socket_call_model [] ∧
    check_syscall (setsockopt_in 3 1 2 4096 (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_call_model = CheckOk socket_call_model [] ∧
    check_syscall (setsockopt_in 3 1 2 4096 (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect (errno_ret EINVAL) [] []) socket_call_model = CheckReject ∧
    check_syscall (setsockopt_in 9 1 2 4096 (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect (errno_ret EINVAL) [] []) socket_call_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> options_table_norm

/-- Rocq's sole option-call cell in this example: net/socket.c:2447-2449
returns ENOTSOCK before the copy at :2409-2410.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt,do_sock_setsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem socket_calls_null_pointers_never_beat_the_fd_209_over_the_real_table :
    check_syscall (socket_call_null_in 209) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_call_model = CheckOk socket_call_model [] ∧
    check_syscall (socket_call_null_in 209) (mkEffect (errno_ret EFAULT) [] [])
      socket_call_model = CheckReject ∧
    check_syscall (socket_call_null_in 209) (mkEffect (errno_ret EINVAL) [] [])
      socket_call_model = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> options_table_norm

/-- The two errnos are net/ipv4/ip_sockglue.c:1414-1415 and :1515-1516,
reached through tcp_setsockopt and tcp_getsockopt
(net/ipv4/tcp.c:4162-4166, :4841-4846) and ipv4_specific
(net/ipv4/tcp_ipv4.c:2501-2502); the swapped errnos are refused.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt,do_sock_setsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem unknown_level_is_enoprotoopt_setting_and_eopnotsupp_getting_over_the_real_table :
    check_syscall (setsockopt_in 6 999 2 4096 4) (mkEffect (errno_ret ENOPROTOOPT) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_syscall (setsockopt_in 6 999 2 4096 4) (mkEffect (errno_ret EOPNOTSUPP) [] [])
      socket_states_model = CheckReject ∧
    check_syscall (getsockopt_in 6 999 2 4096 4104 (fun _ => none))
      (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_syscall (getsockopt_in 6 999 2 4096 4104 (fun _ => none))
      (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> options_table_norm

/-- The length test at net/socket.c:2335-2336 precedes the dispatch at
:2355-2362 and the unknown-level errno at net/ipv4/ip_sockglue.c:1414-1415.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt,do_sock_setsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem negative_optlen_beats_the_unknown_level_over_the_real_table :
    check_syscall (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect (errno_ret EINVAL) [] []) socket_states_model = CheckOk socket_states_model [] ∧
    check_syscall (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1)))
      (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> options_table_norm

/-- Known levels enter the option tables at net/socket.c:2356-2362,
:2413-2423 and net/ipv4/tcp.c:4162-4166, :4841-4846. The checker
docstrings explain the coverage boundary; unknown level 999 reaches
net/ipv4/ip_sockglue.c:1414-1415 and :1515-1516.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt,do_sock_setsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem a_known_level_is_declined_over_the_real_table :
    check_syscall (setsockopt_in 6 0 2 4096 4) (mkEffect 0 [] []) socket_states_model
      = CheckUnmodeled ∧
    check_syscall (getsockopt_in 6 0 2 4096 4104 (fun _ => none)) (mkEffect 0 [] [])
      socket_states_model = CheckUnmodeled ∧
    check_syscall (setsockopt_in 6 1 2 4096 4) (mkEffect 0 [] []) socket_states_model
      = CheckUnmodeled ∧
    check_syscall (getsockopt_in 6 1 2 4096 4104 (fun _ => none)) (mkEffect 0 [] [])
      socket_states_model = CheckUnmodeled ∧
    check_syscall (setsockopt_in 6 6 2 4096 4) (mkEffect 0 [] []) socket_states_model
      = CheckUnmodeled ∧
    check_syscall (getsockopt_in 6 6 2 4096 4104 (fun _ => none)) (mkEffect 0 [] [])
      socket_states_model = CheckUnmodeled ∧
    check_syscall (setsockopt_in 6 999 2 4096 4) (mkEffect (errno_ret ENOPROTOOPT) [] [])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_syscall (getsockopt_in 6 999 2 4096 4104 (fun _ => none))
      (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model
      = CheckOk socket_states_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> options_table_norm

/-- The same ten inputs as getsockopt_answering above, now through the
table. net/socket.c:2409-2410 discards the copy result; :2445-2446
returns EBADF before that copy. The row twin explains the unreadable
and byte-granular boundary fixtures and their under-recording limit.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt,do_sock_setsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem getsockopt_optlen_ledger_marks_the_read_over_the_real_table :
    check_syscall (getsockopt_in 3 17 4 4096 4096 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4096, 4)]) fresh_socket_model
      = CheckOk fresh_socket_model [] ∧
    check_syscall (getsockopt_in 3 17 4 4096 4096 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] []) fresh_socket_model = CheckReject ∧
    check_syscall (getsockopt_in 3 17 4 4096 8192 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] []) fresh_socket_model
      = CheckOk fresh_socket_model [] ∧
    check_syscall (getsockopt_in 3 17 4 4096 8192 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(8192, 4)]) fresh_socket_model
      = CheckReject ∧
    check_syscall (getsockopt_in 3 17 4 4096 4109 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] []) fresh_socket_model
      = CheckOk fresh_socket_model [] ∧
    check_syscall (getsockopt_in 3 17 4 4096 4109 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4109, 4)]) fresh_socket_model
      = CheckReject ∧
    check_syscall (getsockopt_in 9 17 4 4096 4096 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [] [] []) fresh_socket_model
      = CheckOk fresh_socket_model [] ∧
    check_syscall (getsockopt_in 9 17 4 4096 4096 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [] [] [(4096, 4)]) fresh_socket_model
      = CheckReject ∧
    check_syscall (getsockopt_in 3 6 4 4096 4096 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4096, 4)]) fresh_socket_model
      = CheckUnmodeled ∧
    check_syscall (getsockopt_in 3 6 4 4096 4096 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] []) fresh_socket_model = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> options_table_norm

/-- The int fd in net/socket.c:2389-2390 and :2455-2456 keeps the low
32 bits through __SC_CAST (include/linux/syscalls.h:132); the
unknown-level answers and forged EBADF test both directions.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt,do_sock_setsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem option_calls_fd_high_half_is_discarded_over_the_real_table :
    check_syscall (setsockopt_in (Z_to_bv 64 (2 ^ 32 + 6)) 999 2 4096 4)
      (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_syscall (setsockopt_in (Z_to_bv 64 (2 ^ 32 + 6)) 999 2 4096 4)
      (mkEffect (errno_ret EBADF) [] []) socket_states_model = CheckReject ∧
    check_syscall (getsockopt_in (Z_to_bv 64 (2 ^ 32 + 6)) 999 2 4096 4104 (fun _ => none))
      (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_syscall (getsockopt_in (Z_to_bv 64 (2 ^ 32 + 6)) 999 2 4096 4104 (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) socket_states_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> options_table_norm

/-- The int level in net/socket.c:2389-2390 and :2455-2456 keeps the
low 32 bits through __SC_CAST (include/linux/syscalls.h:132). Thus
2^32 + SOL_TCP enters the known-level coverage boundary, as the
probe's level-hi input does; 2^32 + 17 reaches the unknown-level errno.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt,do_sock_setsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem option_calls_level_high_half_is_discarded_over_the_real_table :
    check_syscall (setsockopt_in 6 (Z_to_bv 64 (2 ^ 32 + 17)) 2 4096 4)
      (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_syscall (getsockopt_in 6 (Z_to_bv 64 (2 ^ 32 + 17)) 2 4096 4104 (fun _ => none))
      (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_syscall (setsockopt_in 6 (Z_to_bv 64 (2 ^ 32 + 6)) 2 4096 4)
      (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model = CheckUnmodeled ∧
    check_syscall (getsockopt_in 6 (Z_to_bv 64 (2 ^ 32 + 6)) 2 4096 4104 (fun _ => none))
      (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> options_table_norm

/-- The int length at net/socket.c:2389-2390 is tested at :2335-2336.
These are the observable signed-low-half cases; arm_setsockopt holds
the a4 narrowing, for the inseparability reason in the section header.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt,do_sock_setsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem setsockopt_optlen_high_half_is_discarded_over_the_real_table :
    check_syscall (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 32 + 4)))
      (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_syscall (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 32 + 4)))
      (mkEffect (errno_ret EINVAL) [] []) socket_states_model = CheckReject ∧
    check_syscall (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 63)))
      (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_syscall (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 63)))
      (mkEffect (errno_ret EINVAL) [] []) socket_states_model = CheckReject ∧
    check_syscall (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 32 - 1)))
      (mkEffect (errno_ret EINVAL) [] []) socket_states_model = CheckOk socket_states_model [] ∧
    check_syscall (setsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 32 - 1)))
      (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> options_table_norm

/-- The pointer at net/socket.c:2455-2456 goes whole through :2451-2452
to the copy at :2409-2410. The row twin's high-address memory makes
the correct, missing and truncated ledgers distinct.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt,do_sock_setsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem getsockopt_optlen_pointer_is_not_narrowed_over_the_real_table :
    check_syscall (getsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 32 + 4096)) optlen_high_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(Z_to_bv 64 (2 ^ 32 + 4096), 4)])
      socket_states_model = CheckOk socket_states_model [] ∧
    check_syscall (getsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 32 + 4096)) optlen_high_mem)
      (mkEffect (errno_ret EOPNOTSUPP) [] []) socket_states_model = CheckReject ∧
    check_syscall (getsockopt_in 6 999 2 4096 (Z_to_bv 64 (2 ^ 32 + 4096)) optlen_high_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> options_table_norm

/-- Smuggled copy-ins on the unknown level, negative length and fd errnos:
net/ipv4/ip_sockglue.c:1414-1415 and net/socket.c:2335-2336,
:2380-2384 return before an option-table copy. The accepted empty
ledgers alongside them are the row twin's positive half.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt,do_sock_setsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem setsockopt_copyin_lies_over_the_real_table :
    check_syscall (setsockopt_in_mem 6 999 2 4096 4 sockaddr_in_any_mem)
      (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_syscall (setsockopt_in_mem 6 999 2 4096 4 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret ENOPROTOOPT) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject ∧
    check_syscall (setsockopt_in_mem 6 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1))
        sockaddr_in_any_mem)
      (mkEffect (errno_ret EINVAL) [] []) socket_states_model = CheckOk socket_states_model [] ∧
    check_syscall (setsockopt_in_mem 6 999 2 4096 (Z_to_bv 64 (2 ^ 64 - 1))
        sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject ∧
    check_syscall (setsockopt_in_mem 3 999 2 4096 4 sockaddr_in_any_mem)
      (mkEffect (errno_ret ENOTSOCK) [] []) socket_states_model
      = CheckOk socket_states_model [] ∧
    check_syscall (setsockopt_in_mem 3 999 2 4096 4 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret ENOTSOCK) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject ∧
    check_syscall (setsockopt_in_mem 9 999 2 4096 4 sockaddr_in_any_mem)
      (mkEffect (errno_ret EBADF) [] []) fresh_socket_model
      = CheckOk fresh_socket_model [] ∧
    check_syscall (setsockopt_in_mem 9 999 2 4096 4 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [] [] [(4096, 4)])
      fresh_socket_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> options_table_norm

/-- Unknown-level success, swapped errno and length/fd errno lies:
net/ipv4/ip_sockglue.c:1414-1415 returns ENOPROTOOPT before the
option is read; net/socket.c:2335-2336 tests the nonnegative length.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt,do_sock_setsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem setsockopt_unknown_level_lies_rejected_over_the_real_table :
    check_syscall (setsockopt_in 6 999 2 4096 4) (mkEffect (errno_ret EOPNOTSUPP) [] [])
      socket_states_model = CheckReject ∧
    check_syscall (setsockopt_in 9 999 2 4096 4) (mkEffect (errno_ret EOPNOTSUPP) [] [])
      socket_states_model = CheckReject ∧
    check_syscall (setsockopt_in 6 999 2 4096 4) (mkEffect 0 [] []) socket_states_model
      = CheckReject ∧
    check_syscall (setsockopt_in 6 999 2 4096 4) (mkEffect (errno_ret EINVAL) [] [])
      socket_states_model = CheckReject ∧
    check_syscall (setsockopt_in 6 999 2 4096 0) (mkEffect (errno_ret EINVAL) [] [])
      socket_states_model = CheckReject ∧
    check_syscall (setsockopt_in 6 999 2 4096 4) (mkEffect (errno_ret ENOTSOCK) [] [])
      socket_states_model = CheckReject ∧
    check_syscall (setsockopt_in 6 999 2 4096 4) (mkEffect (errno_ret EBADF) [] [])
      socket_states_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> options_table_norm

/-- Unknown-level success, swapped errno and length/fd errno lies:
net/ipv4/ip_sockglue.c:1515-1516 returns EOPNOTSUPP before the
length tests at :1521-1524, after net/socket.c:2409-2410 records its copy.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt,do_sock_setsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem getsockopt_unknown_level_lies_rejected_over_the_real_table :
    check_syscall (getsockopt_in 6 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret ENOPROTOOPT) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject ∧
    check_syscall (getsockopt_in 9 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret ENOPROTOOPT) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject ∧
    check_syscall (getsockopt_in 6 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU 0 [] [] [] [] [(4096, 4)]) socket_states_model = CheckReject ∧
    check_syscall (getsockopt_in 6 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject ∧
    check_syscall (getsockopt_in 6 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret EINVAL) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject ∧
    check_syscall (getsockopt_in 6 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret ENOTSOCK) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject ∧
    check_syscall (getsockopt_in 6 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject ∧
    check_syscall (getsockopt_in 6 999 2 4096 8192 sockaddr_in_any_mem)
      (mkEffect (errno_ret EFAULT) [] []) socket_states_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> options_table_norm

/-- The rejecting half for high level registers: net/ipv4/ip_sockglue.c:
1414-1415 and :1515-1516 return the unknown-level errnos, after
the int casts in net/socket.c:2389-2390 and :2455-2456.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt,do_sock_setsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem option_level_high_success_rejected_over_the_real_table :
    check_syscall (setsockopt_in 6 (Z_to_bv 64 (2 ^ 32 + 17)) 2 4096 4)
      (mkEffect 0 [] []) socket_states_model = CheckReject ∧
    check_syscall (getsockopt_in 6 (Z_to_bv 64 (2 ^ 32 + 17)) 2 4096 4104 (fun _ => none))
      (mkEffect 0 [] []) socket_states_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> options_table_norm

/-- The probe's shift-copyins:1 lie: net/socket.c:2409-2410 reads at
optlen itself. The readable ledger's positive half is
getsockopt_optlen_ledger_marks_the_read_over_the_real_table.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt,do_sock_setsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem getsockopt_shifted_copyin_rejected_over_the_real_table :
    check_syscall (getsockopt_in 3 17 4 4096 4096 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4097, 4)])
      fresh_socket_model = CheckReject := by
  options_table_norm

/-- The probe's grow-copyins:1 lie: net/socket.c:2409-2410 requests
sizeof(int), four bytes. The positive ledger is pinned above.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt,do_sock_setsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem getsockopt_grown_copyin_rejected_over_the_real_table :
    check_syscall (getsockopt_in 3 17 4 4096 4096 sockaddr_in_any_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4096, 5)])
      fresh_socket_model = CheckReject := by
  options_table_norm

/-- The probe's smuggle-write:a3:4 and smuggle-write:a4:4 lies.
net/socket.c:2447-2449 returns before the option path on a file;
net/ipv4/ip_sockglue.c:1515-1516 returns before option copy-out
on the unknown level. The matching accepted effects are pinned above.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt,do_sock_setsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem getsockopt_enotsock_smuggled_writes_rejected_over_the_real_table :
    check_syscall (getsockopt_in 3 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret ENOTSOCK)
        [(4104, [Z_to_bv 8 65, 65, 65, 65])] [] [] [] [])
      socket_states_model = CheckReject ∧
    check_syscall (getsockopt_in 3 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret ENOTSOCK)
        [(4096, [Z_to_bv 8 65, 65, 65, 65])] [] [] [] [])
      socket_states_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> options_table_norm

/-- The probe's smuggle-write:a3:4 and smuggle-write:a4:4 lies.
net/socket.c:2447-2449 returns before the option path on a file;
net/ipv4/ip_sockglue.c:1515-1516 returns before option copy-out
on the unknown level. The matching accepted effects are pinned above.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt,do_sock_setsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem getsockopt_unknown_level_smuggled_writes_rejected_over_the_real_table :
    check_syscall (getsockopt_in 6 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP)
        [(4104, [Z_to_bv 8 65, 65, 65, 65])] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject ∧
    check_syscall (getsockopt_in 6 999 2 4104 4096 optlen_minus_one_mem)
      (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP)
        [(4096, [Z_to_bv 8 65, 65, 65, 65])] [] [] [] [(4096, 4)])
      socket_states_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> options_table_norm

/-- The fdfirst and optlen-short mutations offer EINVAL or EFAULT
before the descriptor has resolved: net/socket.c:2380-2384 and
:2445-2449 return the fd errno first. These complement Rocq's
fd-first twins above at the probe's null and short argument shapes.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt,do_sock_setsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem option_fd_first_additional_lies_rejected_over_the_real_table :
    check_syscall (setsockopt_in 3 1 2 4096 0)
      (mkEffect (errno_ret EINVAL) [] []) socket_call_model = CheckReject ∧
    check_syscall (setsockopt_in 3 1 9999 0 4)
      (mkEffect (errno_ret EFAULT) [] []) socket_call_model = CheckReject ∧
    check_syscall (getsockopt_in 9 1 2 4096 4096 optlen_minus_one_mem)
      (mkEffect (errno_ret EINVAL) [] []) socket_call_model = CheckReject ∧
    check_syscall (getsockopt_in 9 0 0 0 0 (fun _ => none))
      (mkEffect (errno_ret EFAULT) [] []) socket_call_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> options_table_norm

/-- Resolve the witness lookup on abstract arguments before normalizing
concrete words and fixture models. The argument reading follows
net/socket.c:2389-2390 and __SC_CAST (include/linux/syscalls.h:132,
Linux v6.18.46), as arm_setsockopt's docstring derives.
kernel: net/socket.c:setsockopt; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem setsockopt_witness_input (fd level optname optval optlen : word)
    (m : Model) :
    syscall_spec_witness (setsockopt_in fd level optname optval optlen) m
      = setsockopt_witness (fd32 fd) (int32 level) (int32 optlen) m := rfl

/-- The closed-fd errno (net/socket.c:2380-2381) and the fresh-socket
unknown-level errno (net/ipv4/ip_sockglue.c:1414-1415), through
the witness dispatched by the registered arm.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt,do_sock_setsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem setsockopt_witness_over_the_real_table :
    syscall_spec_witness (setsockopt_in 11 999 2 4096 4) socket_states_model
      = Ok (mkEffect (errno_ret EBADF) [] []) socket_states_model [] ∧
    syscall_spec_witness (setsockopt_in 6 999 2 4096 4) socket_states_model
      = Ok (mkEffect (errno_ret ENOPROTOOPT) [] []) socket_states_model [] := by
  constructor <;> rw [setsockopt_witness_input] <;> options_witness_norm

/-- Resolve the witness lookup on abstract arguments before normalizing
concrete words and fixture models. The argument reading follows
net/socket.c:2455-2456 and __SC_CAST (include/linux/syscalls.h:132,
Linux v6.18.46), as arm_getsockopt's docstring derives.
kernel: net/socket.c:getsockopt; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem getsockopt_witness_input (fd level optname optval optlen : word) (mem : word → Option byte)
    (m : Model) :
    syscall_spec_witness (getsockopt_in fd level optname optval optlen mem) m
      = getsockopt_witness (fd32 fd) (int32 level) optlen (getsockopt_in fd level optname optval optlen mem) m := rfl

/-- The closed-fd errno (net/socket.c:2445-2446) and the fresh-socket
unknown-level errno (net/ipv4/ip_sockglue.c:1515-1516), through
the witness dispatched by the registered arm.
kernel: net/socket.c:__sys_setsockopt,__sys_getsockopt,do_sock_setsockopt,do_sock_getsockopt; net/ipv4/ip_sockglue.c:ip_setsockopt,do_ip_getsockopt@v6.18.46 -/
theorem getsockopt_witness_over_the_real_table :
    syscall_spec_witness (getsockopt_in 11 999 2 4104 4096 optlen_minus_one_mem) socket_states_model
      = Ok (mkEffect (errno_ret EBADF) [] []) socket_states_model [] ∧
    syscall_spec_witness (getsockopt_in 6 999 2 4104 4096 optlen_minus_one_mem) socket_states_model
      = Ok (SyscallEffect.mkEffectU (errno_ret EOPNOTSUPP) [] [] [] [] [(4096, 4)]) socket_states_model [] := by
  constructor <;> rw [getsockopt_witness_input] <;> options_witness_norm

end V_Net_Socket_options

-- lean-port sentinel: ticket V-Net-Socket-lifecycle appends below this line
section V_Net_Socket_lifecycle

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs

/-! ## V-Net-Socket-lifecycle — rejection twins over the real dispatcher

A fabricated success is rejected by the registered arm rather than lost
behind a missing table row, through `check_syscall` over
`Checks.Sys.Table.checked_table`, the real dispatcher every trace runs
against, and not a re-derivation of the arm's own `check_*` function (the
narrow pins above this file's `section`, in `Checks.Cases.Net.Socket`,
already cover that). -/

/-- Expose the registered socket checker before evaluating concrete fixtures.
model: registered socket arm reduction through check_syscall -/
private theorem socket_dispatch (domain type protocol : word) (eff : SyscallEffect) (m : Model) :
    check_syscall (socket_in domain type protocol) eff m =
      check_socket domain type protocol eff m := by
  rfl

/-- UDP under STREAM reaches the protocol walk; this answered input pins registration.
kernel: net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem dispatcher_socket_errno_reproduced :
    check_syscall (socket_in 2 1 17) (mkEffect (errno_ret EPROTONOSUPPORT) [] []) socket_call_model
      = CheckOk socket_call_model [] := by
  rw [socket_dispatch]
  alloc_norm

/-- A fabricated success at that same input must be rejected by the
registered arm, rather than lost behind a missing table row.
kernel: net/ipv4/af_inet.c:inet_create@v6.18.46 -/
theorem dispatcher_socket_success_rejected :
    check_syscall (socket_in 2 1 17) (mkEffect 0 [] []) socket_call_model = CheckReject := by
  rw [socket_dispatch]
  alloc_norm

/-- Descriptor reservation may fail with EMFILE before either write.
kernel: net/socket.c:__sys_socketpair; fs/file.c:alloc_fd@v6.18.46 -/
theorem dispatcher_socketpair_errno_reproduced :
    check_syscall (socketpair_in 2 1 0 4096 wmem_open) (mkEffect (errno_ret EMFILE) [] []) socket_call_model
      = CheckOk socket_call_model [] := by
  rfl

/-- A fabricated success at that same input must be rejected by the
registered arm, rather than lost behind a missing table row.
kernel: net/socket.c:__sys_socketpair@v6.18.46 -/
theorem dispatcher_socketpair_success_rejected :
    check_syscall (socketpair_in 2 1 0 4096 wmem_open) (mkEffect 0 [] []) socket_call_model = CheckReject := by
  rfl

/-- The closed descriptor is refused before reading the address.
kernel: net/socket.c:__sys_bind@v6.18.46 -/
theorem dispatcher_bind_errno_reproduced :
    check_syscall (bind_in 999 0 0 (fun _ => none)) (mkEffect (errno_ret EBADF) [] []) socket_call_model
      = CheckOk socket_call_model [] := by
  rfl

/-- A fabricated success at that same input must be rejected by the
registered arm, rather than lost behind a missing table row.
kernel: net/socket.c:__sys_bind@v6.18.46 -/
theorem dispatcher_bind_success_rejected :
    check_syscall (bind_in 999 0 0 (fun _ => none)) (mkEffect 0 [] []) socket_call_model = CheckReject := by
  rfl

/-- The closed descriptor is refused before the protocol operation.
kernel: net/socket.c:__sys_listen@v6.18.46 -/
theorem dispatcher_listen_errno_reproduced :
    check_syscall (listen_in 999 0) (mkEffect (errno_ret EBADF) [] []) socket_call_model
      = CheckOk socket_call_model [] := by
  rfl

/-- A fabricated success at that same input must be rejected by the
registered arm, rather than lost behind a missing table row.
kernel: net/socket.c:__sys_listen@v6.18.46 -/
theorem dispatcher_listen_success_rejected :
    check_syscall (listen_in 999 0) (mkEffect 0 [] []) socket_call_model = CheckReject := by
  rfl

/-- The closed descriptor is refused by the shared accept entry point.
kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept@v6.18.46 -/
theorem dispatcher_accept_errno_reproduced :
    check_syscall (accept_in 999 0 0) (mkEffect (errno_ret EBADF) [] []) socket_call_model
      = CheckOk socket_call_model [] := by
  rfl

/-- A fabricated success at that same input must be rejected by the
registered arm, rather than lost behind a missing table row.
kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept@v6.18.46 -/
theorem dispatcher_accept_success_rejected :
    check_syscall (accept_in 999 0 0) (mkEffect 0 [] []) socket_call_model = CheckReject := by
  rfl

/-- The closed descriptor is refused before copying the address.
kernel: net/socket.c:__sys_connect@v6.18.46 -/
theorem dispatcher_connect_errno_reproduced :
    check_syscall (connect_in 999 0 0 (fun _ => none)) (mkEffect (errno_ret EBADF) [] []) socket_call_model
      = CheckOk socket_call_model [] := by
  rfl

/-- A fabricated success at that same input must be rejected by the
registered arm, rather than lost behind a missing table row.
kernel: net/socket.c:__sys_connect@v6.18.46 -/
theorem dispatcher_connect_success_rejected :
    check_syscall (connect_in 999 0 0 (fun _ => none)) (mkEffect 0 [] []) socket_call_model = CheckReject := by
  rfl

/-- The closed descriptor is refused before copying a name out.
kernel: net/socket.c:__sys_getsockname@v6.18.46 -/
theorem dispatcher_getsockname_errno_reproduced :
    check_syscall (getsockname_in 999) (mkEffect (errno_ret EBADF) [] []) socket_call_model
      = CheckOk socket_call_model [] := by
  rfl

/-- A fabricated success at that same input must be rejected by the
registered arm, rather than lost behind a missing table row.
kernel: net/socket.c:__sys_getsockname@v6.18.46 -/
theorem dispatcher_getsockname_success_rejected :
    check_syscall (getsockname_in 999) (mkEffect 0 [] []) socket_call_model = CheckReject := by
  rfl

/-- The closed descriptor is refused before copying a peer name out.
kernel: net/socket.c:__sys_getpeername@v6.18.46 -/
theorem dispatcher_getpeername_errno_reproduced :
    check_syscall (getpeername_in 999) (mkEffect (errno_ret EBADF) [] []) socket_call_model
      = CheckOk socket_call_model [] := by
  rfl

/-- A fabricated success at that same input must be rejected by the
registered arm, rather than lost behind a missing table row.
kernel: net/socket.c:__sys_getpeername@v6.18.46 -/
theorem dispatcher_getpeername_success_rejected :
    check_syscall (getpeername_in 999) (mkEffect 0 [] []) socket_call_model = CheckReject := by
  rfl

/-- The closed descriptor is refused before interpreting how.
kernel: net/socket.c:__sys_shutdown@v6.18.46 -/
theorem dispatcher_shutdown_errno_reproduced :
    check_syscall (shutdown_in 999 0) (mkEffect (errno_ret EBADF) [] []) socket_call_model
      = CheckOk socket_call_model [] := by
  rfl

/-- A fabricated success at that same input must be rejected by the
registered arm, rather than lost behind a missing table row.
kernel: net/socket.c:__sys_shutdown@v6.18.46 -/
theorem dispatcher_shutdown_success_rejected :
    check_syscall (shutdown_in 999 0) (mkEffect 0 [] []) socket_call_model = CheckReject := by
  rfl

/-- kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept@v6.18.46 -/
theorem dispatcher_accept4_errno_reproduced :
    check_syscall (accept4_in 999 0 0 0) (mkEffect (errno_ret EBADF) [] []) socket_call_model
      = CheckOk socket_call_model [] := by
  rfl

/-- A fabricated success at that same input must be rejected by the
registered arm, rather than lost behind a missing table row.
kernel: net/socket.c:__sys_accept4,__sys_accept4_file,do_accept@v6.18.46 -/
theorem dispatcher_accept4_success_rejected :
    check_syscall (accept4_in 999 0 0 0) (mkEffect 0 [] []) socket_call_model = CheckReject := by
  rfl

/-- The accept4 call Rocq's `accept4_answering` asks, through the real
dispatcher: `accept4(3, NULL, NULL, 0)` offered the return `r`. -/
def accept4_answering (m : Model) (r : word) : check_result :=
  check_syscall (SyscallInput.mkInput 242 [3, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect r [] []) m

/-- Rocq's `accept4_declines_at`. -/
def accept4_declines_at (m : Model) (r : word) : Bool :=
  match accept4_answering m r with
  | CheckUnmodeled => true
  | _ => false

/-- Rocq's `accept_at_the_wrap_never_declines`, over EVERY return rather
than Rocq's first 4096: at the exhausted counter the checker declines
nothing.  The guard sends the listening arm to `check_errno_only
accept_errnos`, which answers `CheckOk` on the three allocation errnos
and `CheckReject` on everything else, so the wrap costs the descriptor
and no coverage beside it.  Rocq states this of the returns 0 to 4095
and the errnos 1 to 4095 by `vm_compute`; the quantified form holds of
those and of every other register value too.
kernel: fs/file.c:alloc_fd; net/socket.c:do_accept,sock_alloc_file; fs/file_table.c:alloc_path_pseudo,alloc_empty_file@v6.18.46 -/
theorem accept_at_the_wrap_never_declines (r : word) :
    accept4_declines_at exhausted_listening_model r = false := by
  have h : accept4_answering exhausted_listening_model r
      = check_errno_only accept_errnos (mkEffect r [] []) exhausted_listening_model := rfl
  cases hb : errno_ret_in accept_errnos r <;>
    simp [accept4_declines_at, h, check_errno_only, hb]

end V_Net_Socket_lifecycle

-- lean-port sentinel: ticket V-Net-Socket-io appends below this line
section V_Net_Socket_io

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs

/-! ## V-Net-Socket-io — the scenario's verdicts over the real dispatcher

Every `// CASE:` of testing/syscall-check/tests/scenarios/socket_send_recv.c
that mutates or declines one of the four I/O calls, restated through
`check_syscall` over `Checks.Sys.Table.checked_table` — the dispatcher the
recorded corpus replays through — on the slot-3 state the walk holds at
that call: fresh, bound and listening sockets
(`fresh_socket_model`, `bound_socket_model`, `listening_socket_model`),
the emptied slot (`io_slot_empty_model`) and the stderr channel's copy
(`io_slot_channel_model`).  Each `_rejected` theorem is the probe's
mutated answer, and a `_reproduced` theorem states the kernel's own
answer on the same input and state, so the reject is a reject of THAT
lie and not of the input.  The kernel
reasons are the probe's header and the checkers' docstrings in
`Checks/Sys/Net/Socket.lean`; the arguments are the probe's: a one-byte
`sendto` from 4096 with exactly MSG_NOSIGNAL, a one-descriptor `sendmsg`
whose 56-byte header sits at 8192 and its descriptor at 8320, a 16-byte
`recvfrom` into a buffer both readable and writable, and a `recvmsg` with
flags 0. -/

/-- Slot 3 after `close`: the three channels and nothing at 3. -/
def io_slot_empty_model : Model :=
  fixture_of (fds := [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2) ])

/-- Slot 3 after `dup(2)`: the stderr channel's copy at 3. -/
def io_slot_channel_model : Model :=
  fixture_of (fds := [ (3, .FdChannel 2), (0, .FdChannel 0), (1, .FdChannel 1),
                       (2, .FdChannel 2) ])

/-- The probe's `send_to(3)`. -/
def io_sendto3 : SyscallInput := sendto_in 3 4096 1 16384 0 0 mem_ab
/-- The probe's `send_msg(3)`, over `msg_ab`'s header at 8192. -/
def io_sendmsg3 : SyscallInput := sendmsg_in 3 8192 16384 msg_ab
/-- The probe's `recv_from(3)`. -/
def io_recvfrom3 : SyscallInput := recvfrom_rw_in 3 4096 16 0 wmem_open
/-- The probe's `recv_msg(3)`. -/
def io_recvmsg3 : SyscallInput := recvmsg_in 3 8192 0

/-- The header and the one descriptor `___sys_sendmsg` copied. -/
def io_msg_ledger : List (word × Nat) := [(8192, 56), (8320, 16)]

/-- The six sends the walk makes on its first socket: fresh, bound and
listening, each answering both sends -EPIPE, sendmsg's after its header
and descriptor were copied.
kernel: net/core/stream.c:sk_stream_wait_connect; net/ipv4/tcp.c:tcp_sendmsg_locked@v6.18.46 -/
theorem dispatcher_io_dead_socket_epipe_reproduced :
    check_syscall io_sendto3 (mkEffect (errno_ret EPIPE) [] []) fresh_socket_model
      = CheckOk fresh_socket_model [] ∧
    check_syscall io_sendmsg3 (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] io_msg_ledger)
      fresh_socket_model = CheckOk fresh_socket_model [] ∧
    check_syscall io_sendto3 (mkEffect (errno_ret EPIPE) [] []) bound_socket_model
      = CheckOk bound_socket_model [] ∧
    check_syscall io_sendmsg3 (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] io_msg_ledger)
      bound_socket_model = CheckOk bound_socket_model [] ∧
    check_syscall io_sendto3 (mkEffect (errno_ret EPIPE) [] []) listening_socket_model
      = CheckOk listening_socket_model [] ∧
    check_syscall io_sendmsg3 (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] io_msg_ledger)
      listening_socket_model = CheckOk listening_socket_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- `--mutate sendto#1:ret=-EBADF`: the slot socket() returned is open.
kernel: net/socket.c:__sys_sendto@v6.18.46 -/
theorem dispatcher_io_sendto_fresh_ebadf_rejected :
    check_syscall io_sendto3 (mkEffect (errno_ret EBADF) [] []) fresh_socket_model
      = CheckReject := by
  rfl

/-- `--mutate sendmsg#1:ret=-EAGAIN`: a never-bound TCP socket does not
autobind on the sendmsg path (`tcp_prot`'s `.no_autobind`), so -EPIPE
comes before -EAGAIN.
kernel: net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem dispatcher_io_sendmsg_fresh_eagain_rejected :
    check_syscall io_sendmsg3 (SyscallEffect.mkEffectU (errno_ret EAGAIN) [] [] [] [] io_msg_ledger)
      fresh_socket_model = CheckReject := by
  rfl

/-- `--mutate sendto#2:ret=-EAGAIN`: bound is still TCP_CLOSE.
kernel: net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem dispatcher_io_sendto_bound_eagain_rejected :
    check_syscall io_sendto3 (mkEffect (errno_ret EAGAIN) [] []) bound_socket_model
      = CheckReject := by
  rfl

/-- `--mutate sendmsg#3:ret=-ENOTCONN`: the listener's -ENOTCONN is the
receive direction's; a send is -EPIPE.
kernel: net/ipv4/tcp.c:tcp_sendmsg_locked,tcp_recvmsg_locked@v6.18.46 -/
theorem dispatcher_io_sendmsg_listener_enotconn_rejected :
    check_syscall io_sendmsg3 (SyscallEffect.mkEffectU (errno_ret ENOTCONN) [] [] [] [] io_msg_ledger)
      listening_socket_model = CheckReject := by
  rfl

/-- `--mutate sendto#3:ret=0`: nothing is sent from a listener.
kernel: net/ipv4/tcp.c:tcp_sendmsg_locked@v6.18.46 -/
theorem dispatcher_io_sendto_listener_zero_rejected :
    check_syscall io_sendto3 (mkEffect 0 [] []) listening_socket_model = CheckReject := by
  rfl

/-- The emptied slot: each of the four entry points meets `fd_empty(f)`
and answers -EBADF, sendmsg before it copies the header.
kernel: net/socket.c:__sys_sendto,__sys_recvfrom,__sys_sendmsg,__sys_recvmsg@v6.18.46 -/
theorem dispatcher_io_empty_slot_ebadf_reproduced :
    check_syscall io_sendto3 (mkEffect (errno_ret EBADF) [] []) io_slot_empty_model
      = CheckOk io_slot_empty_model [] ∧
    check_syscall io_recvfrom3 (mkEffect (errno_ret EBADF) [] []) io_slot_empty_model
      = CheckOk io_slot_empty_model [] ∧
    check_syscall io_sendmsg3 (mkEffect (errno_ret EBADF) [] []) io_slot_empty_model
      = CheckOk io_slot_empty_model [] ∧
    check_syscall io_recvmsg3 (mkEffect (errno_ret EBADF) [] []) io_slot_empty_model
      = CheckOk io_slot_empty_model [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- `sendto#4`, `recvfrom#1`, `sendmsg#4` and `recvmsg#1` mutated: the
socket's last answer is gone with it, and an empty slot is -EBADF, not
-ENOTSOCK; and `--mutate sendmsg#4:smuggle-copyin:a1:56`, the header
claimed copied before the fd was refused.
kernel: net/socket.c:__sys_sendto,__sys_recvfrom,__sys_sendmsg,__sys_recvmsg; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem dispatcher_io_empty_slot_lies_rejected :
    check_syscall io_sendto3 (mkEffect (errno_ret EPIPE) [] []) io_slot_empty_model
      = CheckReject ∧
    check_syscall io_recvfrom3 (mkEffect (errno_ret ENOTSOCK) [] []) io_slot_empty_model
      = CheckReject ∧
    check_syscall io_sendmsg3 (mkEffect (errno_ret EPIPE) [] []) io_slot_empty_model
      = CheckReject ∧
    check_syscall io_recvmsg3 (mkEffect (errno_ret ENOTSOCK) [] []) io_slot_empty_model
      = CheckReject ∧
    check_syscall io_sendmsg3 (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [] [] [(8192, 56)])
      io_slot_empty_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- The channel copy: `sock_from_file` answers NULL for anything but a
socket's file, and each entry point returns -ENOTSOCK.
kernel: net/socket.c:sock_from_file,__sys_sendto,__sys_recvfrom,__sys_sendmsg,__sys_recvmsg@v6.18.46 -/
theorem dispatcher_io_channel_slot_enotsock_reproduced :
    check_syscall io_sendto3 (mkEffect (errno_ret ENOTSOCK) [] []) io_slot_channel_model
      = CheckOk io_slot_channel_model [] ∧
    check_syscall io_recvfrom3 (mkEffect (errno_ret ENOTSOCK) [] []) io_slot_channel_model
      = CheckOk io_slot_channel_model [] ∧
    check_syscall io_sendmsg3 (mkEffect (errno_ret ENOTSOCK) [] []) io_slot_channel_model
      = CheckOk io_slot_channel_model [] ∧
    check_syscall io_recvmsg3 (mkEffect (errno_ret ENOTSOCK) [] []) io_slot_channel_model
      = CheckOk io_slot_channel_model [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- `sendto#5`, `recvfrom#2`, `sendmsg#5` and `recvmsg#2` mutated: the
slot is open again, holding a non-socket; and
`--mutate sendmsg#5:smuggle-copyin:a1:56`, the header claimed copied
before the non-socket was refused.
kernel: net/socket.c:sock_from_file,__sys_sendto,__sys_recvfrom,__sys_sendmsg,__sys_recvmsg; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem dispatcher_io_channel_slot_lies_rejected :
    check_syscall io_sendto3 (mkEffect (errno_ret EBADF) [] []) io_slot_channel_model
      = CheckReject ∧
    check_syscall io_recvfrom3 (mkEffect (errno_ret EBADF) [] []) io_slot_channel_model
      = CheckReject ∧
    check_syscall io_sendmsg3 (mkEffect (errno_ret EPIPE) [] []) io_slot_channel_model
      = CheckReject ∧
    check_syscall io_recvmsg3 (mkEffect (errno_ret EBADF) [] []) io_slot_channel_model
      = CheckReject ∧
    check_syscall io_sendmsg3 (SyscallEffect.mkEffectU (errno_ret ENOTSOCK) [] [] [] [] [(8192, 56)])
      io_slot_channel_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- `--mutate sendto#6:ret=-ENOTSOCK`: the second socket took slot 3
back, so it is a socket again.
kernel: net/socket.c:__sys_sendto; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem dispatcher_io_sendto_second_socket_enotsock_rejected :
    check_syscall io_sendto3 (mkEffect (errno_ret ENOTSOCK) [] []) fresh_socket_model
      = CheckReject := by
  rfl

/-- The ledger mutations: `sendmsg#1:drop-copyins` (the -EPIPE without
the header and descriptor it came after), `sendmsg#3:shift-copyins:1`
(both ranges one byte off), and `sendto#1:smuggle-copyin:a1:1` (a payload
byte read before the wait for a connection answered).
kernel: net/socket.c:___sys_sendmsg; net/ipv4/tcp.c:tcp_sendmsg_locked@v6.18.46 -/
theorem dispatcher_io_ledger_lies_rejected :
    check_syscall io_sendmsg3 (mkEffect (errno_ret EPIPE) [] []) fresh_socket_model
      = CheckReject ∧
    check_syscall io_sendmsg3
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(8193, 56), (8321, 16)])
      listening_socket_model = CheckReject ∧
    check_syscall io_sendto3 (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] [(4096, 1)])
      fresh_socket_model = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- The fail-closed modes: `recvlisten` and `msglisten`, recvfrom and
recvmsg on the listener, decline whatever the return — the -EBADF lie
too, since the decline comes before the return is looked at — and
`msgaddr`, a named sendmsg destination on the bound socket, declines.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked; net/socket.c:__copy_msghdr,__sys_recvfrom; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem dispatcher_io_fail_closed_modes :
    check_syscall io_recvfrom3 (mkEffect (errno_ret ENOTCONN) [] []) listening_socket_model
      = CheckUnmodeled ∧
    check_syscall io_recvfrom3 (mkEffect (errno_ret EBADF) [] []) listening_socket_model
      = CheckUnmodeled ∧
    check_syscall io_recvmsg3 (mkEffect (errno_ret ENOTCONN) [] []) listening_socket_model
      = CheckUnmodeled ∧
    check_syscall (sendmsg_in 3 8192 16384 msg_named)
      (SyscallEffect.mkEffectU (errno_ret EPIPE) [] [] [] [] io_msg_ledger)
      bound_socket_model = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

end V_Net_Socket_io

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Net.Socket
