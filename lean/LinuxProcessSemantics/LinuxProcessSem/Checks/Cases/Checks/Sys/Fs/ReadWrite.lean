import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.ReadWrite
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs

/-! # Checks.Cases.Checks.Sys.Fs.ReadWrite — what the ReadWrite CHECKERS answer and what their WITNESSES name, read off against Linux

Pins over `Checks.Sys.Fs.ReadWrite.check_read`, the twin of
`theories/LinuxProcessSem/Checks/Sys/Fs/ReadWrite.v`'s read checker, and
over `read_witness`, the twin of
`theories/LinuxProcessSem/Checks/Witness/Fs/ReadWrite.v`'s: the checker
first, the witness last.  The write (64) pins follow the read ones under
their own heading; the section `PositionalAndSeek` after them pins the
`pread64`, `pwrite64` and `lseek` checkers and witnesses the same way, and
its own header says where it departs from the read pins; the two sections
after it, `WriteThroughTheTable` and then `ReadThroughTheTable`, restate
the Rocq write and read examples through `check_syscall`; and the section
`Vectored` at the end pins the `readv` and `writev` checkers and
witnesses, its own header saying where it departs from what follows.  Not part of
the trusted specification: this file is QA on the definitions, written to
be READ, and every claim in it is a claim about what the kernel does, with
the citation beside it.  Every
kernel line below was read at Linux v6.18.46 (commit 1f99e9ab748f).

TWO LEAN FILES COVER ONE ROCQ FILE, and the split is by what is being
tested.  `Checks/Cases/Fs/ReadWrite.lean` states, for each decision of
`read_spec`, an `iff` over every outcome and refutes the lie a kernel could
not tell; the KERNEL argument for every answer is beside the spec-level pin
of the same call there.  The checker is that spec made executable — the
four `_sound_`/`_complete_` lemmas beside it say the two agree on every
input — so a pin here does not restate those `iff`s.  It hands the checker
a concrete `(input, effect)` pair, the shape a trace hands it, and states
the verdict: `CheckOk` on the kernel's answer, `CheckReject` on the lie,
`CheckUnmodeled` where the spec declines.  That is the question a trace
asks, and the one the four lemmas cannot: soundness and completeness are
biconditionals between two definitions of this tree, and hold as well of a
wrong spec beside a matching wrong checker.  Only a verdict on a value
named from outside tells the two apart, which is what each pin below is —
and it is what refuses the checker that answers `CheckUnmodeled`
everywhere, which the four lemmas would accept beside an always-`unmodeled`
spec.  Each docstring here keeps only the reading its own verdict rests on.

HOW THESE ARE STATED.  Each pin applies the checker the way the
dispatcher does: `check_read_row` below is the argument narrowing of
Rocq's `arm_read` (`theories/LinuxProcessSem/Checks/Sys/Dispatch.v`) and
of the row for 63 in `Sys/SyscallTable.lean`, spelled once;
`the_row_is_the_arm` holds it to `Sys/Registry/Fs/ReadWrite.lean`'s
`read_arm`, and `check_syscall_read_in`, in `ReadThroughTheTable`, to the
checked table's row (`Checks/Arms/Fs/ReadWrite.lean`),
through which that section restates the Rocq examples.  The inputs are
the fixtures of `Checks/Cases/Fs/ReadWrite.lean`,
imported rather than copied, so the two files cannot drift apart on a
descriptor, an address or a byte; the three fixtures added for `read` are
`hello_stdin`, Rocq's five closed bytes, because a verdict pin spells the
delivered bytes and the spec-level file keeps its stream symbolic on
purpose (its header says why), `llong_max_model`, fd 3 rewritten to the
offset LLONG_MAX for the recorded LLONG_MAX divergence pinned below, and
`zeros_forever`, a random stream that never ends, for the one pin whose
subject is the closers.  Every closed equality is closed by
`check_norm` (`witness_norm` over the witness; `PositionalAndSeek`'s
`rwp_norm` and `rwp_witness_norm` and `Vectored`'s `rwv_norm` and
`rwv_witness_norm` are the same pass over their rows): one
`simp only` pass, `zeta` off, that opens the row and reads the two `positive`-indexed
stream takes back to the unary ones, then `rfl`, which evaluates the
checker on the closed input down to a constructor.  Its docstring says
why the pass is needed at all — `positive.ofNat` is well-founded
recursion, which evaluation does not unfold — and why `zeta` is off: a
count that clamps to `MAX_RW_COUNT` on any descriptor but the random
device itself otherwise costs the kernel the whole clamped take off a
random stream that never ends — the fixture's own `default_urandom`,
infinite since #1190 — in an arm the row never takes;
`the_closers_survive_an_infinite_random_stream` pins that on an explicit
stream, `zeros_forever_never_ends` holds the stream to never ending, so
the reason is shown at this head whatever the fixture's slot.  The
section `Vectored` adds two more, `one_iovec_zero_mem` and
`invalid_first_iovec_zero_mem`, and its header says why.
Nothing here is `decide` on a `check_result`: `Model`
has no `DecidableEq`, so no such equation can be decided, and none needs
to be.  The one pin stated on `check_read` itself rather than the row,
`the_checker_itself_reads_the_whole_word`, is a closed descriptor lookup
with no stream in reach and closes by `rfl` alone.  The two symbolic
twins in the section `Clamp`
(`read_ret_over_clamp_rejected`, `read_delivery_clamped`) are Rocq's own
lemmas over `check_read`, proved the way Rocq proves them: by walking the
checker's arms.

WHAT IS NOT HERE.  Outside the decline pins of the section `Vectored`,
which its own header covers, no pin carries a `probe:` line, although
`testing/syscall-check/tests/read_spec.c`, `fd_truncation.c`,
`read_window.c`, `zero_len_fault.c`, `dev_urandom_decline.c`,
`pipe2_spec.c`, `socket_rw.c` and `socket_read_peer.c` run most of these
shapes against the kernel.  What stands in the way is
`tools/check_lean_pin_evidence.py`'s polarity reading, which classes a
statement by `¬`, `≠`, `False` and the word `Unmodeled`: a `= CheckReject`
or `= CheckUnmodeled` verdict reads as positive there, so the
`reject --mutate` or `fail-closed` case that matches it would be refused
as the wrong polarity — and a `≠ CheckUnmodeled` pin reads as negative
there, so the `conform` case that is the right evidence for "not
declined" would be refused too; the reader is wrong in both directions.
Until that reader knows the checker's verdicts,
every evidence line below is a kernel reading, except the `model:` lines
on the claims that are about this tree and not about Linux, and the probe
that runs the same shape against the Rocq checker is named in the
spec-level pin beside it.  In the read sections, in `PositionalAndSeek`
and in `ReadThroughTheTable`, those claims are the recorded LLONG_MAX
divergence, a decline's indifference to the effect's shape, the ledger's
canonical one-run shape, the copy-in ledger being this tree's accounting,
the narrowing being the row's and not the checker's, the stream fixture
that never ends, and the witness-through-completeness facts.  The write
section's are the ones its own paragraph on `model:` lines names, and
`WriteThroughTheTable` restates write pins with theirs.
No pin here reaches `FdFileRW` or `FdFileA`: the spec twin declines a
read-write file in both directions and an append-mode one in every arm
but readv's gate (`Sys/Fs/ReadWrite.lean`'s header), so Rocq's
`rdwr_fd_refuses_ebadf_in_either_direction` and
`rdwr_read_then_write_shares_one_offset` are not restated here, and
`Checks/Cases/Fs/ReadWrite.lean` registers them `unpinned:`.

WHICH ROCQ EXAMPLE EACH THEOREM RESTATES.  This file mirrors no Rocq file,
so `tools/check_lean_cases_parity.py` would refuse a coverage register here
as a claim nothing could be held to; the register for
`Checks/Cases/Fs/ReadWrite.v` is at the top of `Checks/Cases/Fs/ReadWrite.lean`,
which lists `read_delivery_clamped` and `read_ret_over_clamp_rejected` as
`unpinned:`.  The first's reason still says the Lean checker has no
completeness lemma to walk, which `check_read_complete_ok` makes false:
`read_delivery_clamped` is proved on the checker, as this file's theorem
of the same name, which cannot be the line's `covers:` target because
this file mirrors no Rocq file.  That reason is stale until the next
change to that file rewords it — a byte changed there sends the lean
job's mutation duty (`tools/lean_mutation_duty.py`) to score the
`Fs/ReadWrite` twin in full whenever its committed cache does not bind,
which is why the change adding this file left it alone — and until then
this paragraph is the correct account.
The second's reason, that no fixture there holds more than MAX_RW_COUNT
bytes, stays true.  `check_lean_cases_parity.py` holds the NAME on each
`unpinned:` line; of the two reasons it reads only the second's, because
`read_ret_over_clamp_rejected` rejects a kernel answer and such a case's
reason must carry a kernel path and a version — the first's reason is
read by no guard.
The mapping is therefore prose, read by no guard, kept so a reader can
find the Rocq `Example` or `Lemma` a theorem restates.  Rocq states its
read examples through `check_syscall`, so each fixes the spec's answer and
the checker's verdict at once; the verdict half is what is restated here,
on the row, and again through the dispatch in `ReadThroughTheTable`: the
second name on each `Example`'s line below (the two `Lemma`s at the end
have no such twin).  It stops being complete the day a theorem restating
a Rocq conjunct is added without a line.

- `read_bad_fd_ebadf`: `check_read_bad_fd_ebadf`,
  `read_bad_fd_ebadf_over_the_real_table`
- `read_bad_fd_success_rejected`: `check_read_bad_fd_success_rejected`,
  `read_bad_fd_success_rejected_over_the_real_table`
- `read_fd_truncates_to_32_bits`: `check_read_fd_truncates_to_32_bits`,
  `read_fd_truncates_to_32_bits_over_the_real_table`
- `read_channel_eintr_rejected`: `check_read_channel_eintr_rejected`,
  `read_channel_eintr_rejected_over_the_real_table`
- `pipe_read_over_rw_bytes_max_is_judged`: `check_pipe_read_over_rw_bytes_max_is_judged`,
  `pipe_read_over_rw_bytes_max_is_judged_over_the_real_table`
- `partial_destination_on_a_pipe_declines`, its two `read` conjuncts:
  `check_stdin_partial_destination_declines`, its first and third
  conjuncts (the -EFAULT decline between them is this file's own), and
  `read_partial_destination_on_a_pipe_declines_over_the_real_table`
- `readv_at_llong_max_is_einval_not_eof`, its two `read` conjuncts:
  `check_file_at_llong_max_still_answers_zero`,
  `file_at_llong_max_still_answers_zero_over_the_real_table`
- `read_ret_over_clamp_rejected`: `read_ret_over_clamp_rejected`
- `read_delivery_clamped`: `read_delivery_clamped`

The groups that are this file's own — the row's narrowing, the lies about
the ledger, the per-arm verdicts and the witness — have no Rocq conjunct.

NOTHING HERE COMPARES THE LEAN CHECKER TO THE ROCQ ONE.  What these pins
prove is that this checker and a named line of Linux agree. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.ReadWrite

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.ReadWrite
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Uaccess
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.ReadWrite

/-! ## The dispatcher's application of the checker -/

/-- `check_read` as the dispatcher applies it: the descriptor narrowed to
its low 32 bits by `fd32` from a0 (`read` takes `unsigned int fd`,
fs/read_write.c:722, Linux v6.18.46), `buf` whole from a1, `count` whole
from a2 — Rocq's `arm_read` and the row for 63 in `Sys/SyscallTable.lean`.  The
checked arm, `arm_read` (`Checks/Arms/Fs/ReadWrite.lean`), unfolds to
this application: `check_syscall_read_in`, in `ReadThroughTheTable`. -/
def check_read_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_read i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m

/-- `read_witness` applied the same way. -/
def read_witness_row (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  read_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

/-- Rocq's `hello_stdin`: standard input holding "hello", closed, so the
verdict pins can spell the bytes a kernel delivered. -/
def hello_stdin : InputStream :=
  ICons 104 (ICons 101 (ICons 108 (ICons 108 (ICons 111 IEof))))

/-- Evaluate a closed call of the checker.  Not `rfl`: the two stream
takes, `stream_take_z` and `net_take_z`, index the take by a `positive`
digit string built by `positive.ofNat`, which is well-founded recursion
and does not unfold by evaluation, so `rfl` stalls at the first
`read_bytes_map` over a stream.  `StreamLaws.stream_take_z_eq` and
`net_take_z_eq` read the two back to the unary `stream_take` / `net_take`
at `n.toNat`, structural on the count, and `rfl` evaluates everything
else — the descriptor lookup, the gates, the byte walk, the effect
match and the post-model.  The channel fixtures leave the remaining
stream as a shifted `byte_at`, which `rfl` compares with the claimed
remainder by unfolding both to their bytes.  The pass opens
`check_read_urandom` too, since the /dev/urandom arm takes its stream
inside it.

`zeta` is off, so the pass leaves that arm's own `let r := stream_take_z
(m_urandom m) (rw_count_clamp count)` bound instead of inlining the take
into the arm's length test and its byte-map `match`.  The reason is what
the pass does to the arms the row does NOT take.  The descriptor `match`
is not reduced by simp (the lookup is an ordinary definition), so every
arm stays in the term until `rfl`, and simp rewrites inside all of them:
on a closed effect each arm's `match eff` collapses to `CheckReject`,
and the proof simp builds for that collapse in the /dev/urandom arm asks
the kernel to compare the two versions of that arm's byte-map `match`
outright — `ite_congr`'s `¬c → y = v` obligation, discharged by
`Eq.refl` of the reduced side.  The two applications share a matcher
head with abbrev hints, which the kernel unfolds instead of comparing
argument-wise, and unfolding whnf's the discriminant, `read_bytes_map …
(len_word r.1)` at the inlined `r`: the whole clamped take.  The
fixture's random stream is `default_urandom` (`State/Streams.lean`, the
zero byte at every index since #1190), so, under a pass with `zeta` on,
a row whose
count clamps to `MAX_RW_COUNT` — the sign-bit and all-ones counts, the
2^40 socket count, the out-of-range socket and pipe counts — costs the kernel 0x7ffff000 stream
steps on an arm the row never takes: `(kernel) deep recursion detected`,
and a deterministic timeout once the depth is raised, which is why
raising `maxRecDepth` was not the fix — the depth is the take's, not the
term's.  With `r` bound the same comparison runs under a variable and is
stuck at once, and `rfl` zeta-reduces the `let` itself when it evaluates
the arm actually taken.  What the switch does not reach is a take that
was never let-bound and reads its stream off the closed model: the
channel arm's `stream_take_z (m_stdin m) …` sits inline in its byte-map
discriminant, so the same comparison walks it to the end of the
fixture's standard input — bounded, because every standard input the
fixtures declare is finite.  The connected-socket arm's `net_take_z rx …`
is inline too, but `rx` is a pattern variable of the descriptor `match`,
which simp leaves unreduced, so in an arm the row does not take the walk
is stuck on the variable at once — as are the file arm's `data` and the
pipe arm's `q` — and no socket script is walked untaken.  Nor does the
switch reach the arm a row TAKES: `rfl` evaluates that one, its take
included — on the random device `check_read_urandom` bounds nothing
before its take but `access_okb` and the one-byte probe (the `FdUrandom`
arm of `check_read` and `check_read_urandom` in
`Checks/Sys/Fs/ReadWrite.lean`), and the channel and connected-socket
arms likewise — so a row whose own descriptor reads a stream that never
ends, with a count that clamps to `MAX_RW_COUNT` and a writable first
byte, would compute the whole clamped take under any simp setting.  No
row here does: every fd-24 row runs on an explicit finite stream, every
standard input and socket script is finite, and the clamped take is
stated symbolically instead (`read_delivery_clamped`, over
`check_read_urandom_delivery_clamped`).  This stops working the day a
fixture declares an infinite standard input and a row on another
descriptor carries a count that clamps to `MAX_RW_COUNT`, or a row's own
descriptor — the random device, standard input or a connected socket —
carries one on a stream that never ends; that row needs its own
closer. -/
scoped macro "check_norm" : tactic =>
  `(tactic| (simp -zeta only [check_read_row, check_read, check_read_urandom, stream_take_z_eq, net_take_z_eq]; first | done | rfl))

/-- The same pass over the witness, `zeta` off as well.
`read_urandom_witness` binds the same `r`, but the collapse above has
nothing to fire on here: the witness matches no effect, so the only
rewrite simp makes inside that arm on a closed input is `stream_take_z_eq`
on the take itself — a proper equation, whose congruence proof the kernel
checks argument for argument — and no `match eff` collapses to leave an
`Eq.refl` obligation between two reduced matcher applications.  The old
pass closed every witness row on the stream that never ends — the clamped
socket row of `read_witness_is_unmodeled_where_the_spec_declines`
included, and the row of `the_closers_survive_an_infinite_random_stream`
under `simp only` with `zeta` on, its rewrite trace showing that one
`stream_take_z_eq` on `m_urandom`, one on `m_stdin` and one `net_take_z_eq`
on the socket arm's `rx`.  The switch is precautionary: it keeps the two
closers in step, so that a rewrite inside that arm cannot reintroduce the
comparison here alone. -/
scoped macro "witness_norm" : tactic =>
  `(tactic| (simp -zeta only [read_witness_row, read_witness, read_urandom_witness, stream_take_z_eq, net_take_z_eq]; first | done | rfl))

/-- A random stream that never ends: byte 0 at every index.  Not a fixture
of the spec-level file, and read by no verdict below: it exists for
`the_closers_survive_an_infinite_random_stream` alone, so that the reason
`check_norm` runs with `zeta` off is shown at this head, on a stream this
file owns, and not only on the fixture's `default_urandom`, which a change
to `State/Streams.lean` could make finite. -/
def zeros_forever : InputStream := ⟨fun _ => some 0, fun _ h => nomatch h⟩

/-- …and it never ends: byte 0 at every index, so the take the pin below
holds the closers to is the whole clamped one and not a short stop at an
end of input, as it is on `IEof`.  This is the premise that pin rests on
and nothing else holds: a rewrite of the fixture to a finite stream
would leave `the_closers_survive_an_infinite_random_stream` closing under
both closers and holding nothing, since the old closer closes the same
row on a finite slot such as `IEof`, which `read_model` held before #1190.
model: a fact about this file's own stream fixture, not a claim about Linux, which is never asked for these bytes -/
theorem zeros_forever_never_ends (i : Nat) : zeros_forever.byte_at i = some 0 := rfl

/-- THE CLOSERS SURVIVE A RANDOM STREAM THAT NEVER ENDS.  The row is the
conjunct of `unconnected_socket_verdicts_on_the_checker` whose count
clamps to `MAX_RW_COUNT`, on `read_model` with its random device replaced
by `zeros_forever`.  The verdict is the socket arm's and reads no random
byte: `tcp_recvmsg_locked` answers -ENOTCONN on a socket in `TCP_CLOSE`
(net/ipv4/tcp.c, Linux v6.18.46), reached through `sock_read_iter` before
any byte moves, so `CheckOk` and the witness's `Ok` are the kernel's
answer whatever the random stream holds.  What the theorem holds is the
closer: under `simp only` with `zeta` on, the pass hands the kernel the
/dev/urandom arm's byte-map `match` at the inlined 0x7ffff000-byte take
of `zeros_forever`, and this proof stops with `(kernel) deep recursion
detected` — the failure the five pins holding `MAX_RW_COUNT` rows meet
under that closer on the fixture's own `default_urandom`, reproduced here
on a stream this file owns.  It stops being
needed the day `check_norm` no longer opens `check_read_urandom`.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked; net/socket.c:sock_read_iter@v6.18.46 -/
theorem the_closers_survive_an_infinite_random_stream :
    check_read_row (read_in 10 4096 (Z_to_bv 64 (2 ^ 40)) wmem_none)
        (mkEffect (errno_ret ENOTCONN) [] []) (urandom_model zeros_forever)
      = CheckOk (urandom_model zeros_forever) []
    ∧ read_witness_row (read_in 10 4096 (Z_to_bv 64 (2 ^ 40)) wmem_none)
        (urandom_model zeros_forever)
      = Ok (mkEffect (errno_ret ENOTCONN) [] []) (urandom_model zeros_forever) [] := by
  refine ⟨?_, ?_⟩
  · check_norm
  · witness_norm

/-- The row IS the registry arm's application.  `check_read_sound_ok` lands
in `read_arm`'s `sa_spec` only if the row narrows each argument as
`Sys/Registry/Fs/ReadWrite.lean` does — a0 through `fd32`, a1 and a2
whole — so a row that handed a0 over whole, or narrowed a1 too, fails here
at `h` with a type mismatch; `check_syscall_read_in` below is the same
fact on the checked side.  The narrowing is the kernel's own:
`SYSCALL_DEFINE3(read, unsigned int, fd, char __user *, buf, size_t, count)`
(fs/read_write.c:722, Linux v6.18.46) takes the descriptor as an
`unsigned int` and the other two whole, so a0 reaches `ksys_read` through
`__SC_CAST` low-32 and a1, a2 as they arrived.
kernel: fs/read_write.c:read,ksys_read@v6.18.46 -/
theorem the_row_is_the_arm (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_read_row i eff m = CheckOk m' evs) :
    (Sys.Registry.Fs.ReadWrite.read_arm).sa_spec i m (Ok eff m' evs) :=
  check_read_sound_ok _ _ _ _ _ _ _ _ h

section RocqExamples

/-! ## Rocq's read examples, on the checker

Each is the conjunction Rocq states, on Rocq's fixture where this tree has
it (`demo_model` is Rocq's `init_model [] 0 0 demo_sp demo_limit
(demo_input [] IEof)`, `hello_stdin` its `hello_stdin`) and on the
spec-level file's `read_model` where Rocq's fixture is a table this tree
spells differently, with the checker's verdict in place of
`check_syscall`'s. -/

/-- A CLOSED DESCRIPTOR IS -EBADF, the model unchanged and no event:
`ksys_read` resolves the fd first (fs/read_write.c:706, Linux v6.18.46) and
answers -EBADF (:707) on an empty slot before `vfs_read` (:715) is reached.
Rocq's `read_bad_fd_ebadf`, on fd 5 of the three-channel table.
kernel: fs/read_write.c:ksys_read@v6.18.46 -/
theorem check_read_bad_fd_ebadf :
    check_read_row (read_in 5 4096 16 wmem_none) (mkEffect (errno_ret EBADF) [] []) demo_model
      = CheckOk demo_model [] := by
  check_norm

/-- …and a kernel delivering four bytes on it is lying: nothing is read
through an empty slot.  Rocq's `read_bad_fd_success_rejected`.
kernel: fs/read_write.c:ksys_read@v6.18.46 -/
theorem check_read_bad_fd_success_rejected :
    check_read_row (read_in 5 4096 16 wmem_none) (mkEffect 4 [(4096, [1, 2, 3, 4])] []) demo_model
      = CheckReject := by
  check_norm

/-- THE DESCRIPTOR IS THE LOW 32 BITS OF a0: `read` takes `unsigned int fd`
(fs/read_write.c:722, Linux v6.18.46), so 2^32 arrives as 0 — standard
input at end of file, which answers 0 — and a kernel refusing it with
-EBADF compared the whole register.  Rocq's `read_fd_truncates_to_32_bits`.
kernel: fs/read_write.c:read,ksys_read@v6.18.46 -/
theorem check_read_fd_truncates_to_32_bits :
    check_read_row (read_in (Z_to_bv 64 (2 ^ 32)) 4096 16 wmem_none) (mkEffect 0 [] []) demo_model
      = CheckOk demo_model []
    ∧ check_read_row (read_in (Z_to_bv 64 (2 ^ 32)) 4096 16 wmem_none)
        (mkEffect (errno_ret EBADF) [] []) demo_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- THE NARROWING IS THE ROW'S, NOT THE CHECKER'S: handed the whole word,
`check_read` looks 2^32 up as it is, finds no such descriptor, and answers
-EBADF.  This pin states the bare checker, so it holds whatever the
registration does; what it shows is why the narrowing has to be the
row's.  A registration that skipped `fd32` fails elsewhere: at
`check_syscall_read_in` in `ReadThroughTheTable`, whose closing `rfl`
would no longer meet `check_read_row`'s `fd32` on a symbolic a0.
`read_fd_truncates_to_32_bits_over_the_real_table` is the pin through the
table that states what such a row would get wrong: it refuses at
a0 = 2^32 the -EBADF this checker accepts there.
model: `check_read` looks its descriptor argument up unnarrowed and the row's `fd32` does the narrowing; a claim about this tree, not about Linux -/
theorem the_checker_itself_reads_the_whole_word :
    check_read (read_in (Z_to_bv 64 (2 ^ 32)) 4096 16 wmem_none) (Z_to_bv 64 (2 ^ 32)) 4096 16
        (mkEffect (errno_ret EBADF) [] []) demo_model
      = CheckOk demo_model [] := rfl

/-- -EINTR ON A READ IS REFUSED: with one byte queued, `anon_pipe_read`
(fs/pipe.c:269, Linux v6.18.46) copies it out and returns 1 without ever
reaching the `wait_event_interruptible_exclusive` at fs/pipe.c:388 whose
-ERESTARTSYS `arch_do_signal_or_restart`
(arch/riscv/kernel/signal.c:396-442) turns into -EINTR when the handler
lacks `SA_RESTART` (:440-442; with it the call restarts); no model state
admits the interrupt.  The recorded cost is
bugs/read-write-reject-an-interrupted-transfer.md.  Rocq's
`read_channel_eintr_rejected`, over the one byte 120, on Rocq's fixture:
`demo_model` with that byte on standard input.
kernel: fs/pipe.c:anon_pipe_read; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem check_read_channel_eintr_rejected :
    check_read_row (read_in 0 4096 1 (wmem_first 1)) (mkEffect 1 [(4096, [120])] [])
        (with_stdin (ICons 120 IEof) demo_model)
      = CheckOk (with_stdin IEof demo_model) [ReadEv 0 120]
    ∧ check_read_row (read_in 0 4096 1 (wmem_first 1)) (mkEffect (errno_ret EINTR) [] [])
        (with_stdin (ICons 120 IEof) demo_model)
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- A PIPE READ PAST `rw_bytes_max` IS JUDGED, NOT DECLINED: the count is
`rw_bytes_max + 1` at an in-range destination, and `anon_pipe_read`
(fs/pipe.c:269, Linux v6.18.46) hands over the two queued bytes and
releases the buffer that held them (:343-360); the mark at 2 in the
post-model is `PipeBuf`'s own bookkeeping of the drained page, not a
kernel value.  The
one-byte answer is refused: a pipe read delivers all that is queued up to
the count.  Rocq's `pipe_read_over_rw_bytes_max_is_judged`, on
`read_model`'s pipe 0 ("ab", mark 2) through fd 14.
kernel: fs/pipe.c:anon_pipe_read; fs/read_write.c:vfs_read@v6.18.46 -/
theorem check_pipe_read_over_rw_bytes_max_is_judged :
    check_read_row (read_in 14 4096 (Z_to_bv 64 (rw_bytes_max + 1)) (wmem_first 2))
        (mkEffect 2 [(4096, [97, 98])] []) read_model
      = CheckOk (with_pipes [(0, ([], 2)), (1, ([], 0)), (2, ([], 3))] read_model) []
    ∧ check_read_row (read_in 14 4096 (Z_to_bv 64 (rw_bytes_max + 1)) (wmem_first 2))
        (mkEffect 1 [(4096, [97])] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- A PARTIALLY WRITABLE DESTINATION ON STANDARD INPUT IS DECLINED: five
bytes queued, four destination bytes writable, and `anon_pipe_read`
(fs/pipe.c:269, Linux v6.18.46) answers -EFAULT with up to four bytes
stored in user memory and NOTHING consumed if `copy_page_to_iter` falls short — the
`break` at :347 precedes the `buf->offset += chars` at :350, and the
-EFAULT stands only while `ret` is 0, so five bytes split across buffers
answer the count of the whole ones instead — a progress the model does
not describe, so no effect is accepted.  With the fifth byte writable the
whole prefix is delivered, one event per byte on channel 0.  Rocq's
`partial_destination_on_a_pipe_declines`, its two `read` conjuncts (the
first and third here; the -EFAULT decline between them is this file's
own), on Rocq's fixture: `demo_model` with "hello" on standard input.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem check_stdin_partial_destination_declines :
    check_read_row (read_in 0 4096 100 (wmem_first 4))
        (mkEffect 4 [(4096, [104, 101, 108, 108])] []) (with_stdin hello_stdin demo_model)
      = CheckUnmodeled
    ∧ check_read_row (read_in 0 4096 100 (wmem_first 4)) (mkEffect (errno_ret EFAULT) [] [])
        (with_stdin hello_stdin demo_model)
      = CheckUnmodeled
    ∧ check_read_row (read_in 0 4096 100 (wmem_first 5))
        (mkEffect 5 [(4096, [104, 101, 108, 108, 111])] []) (with_stdin hello_stdin demo_model)
      = CheckOk (with_stdin IEof demo_model)
          [ReadEv 0 104, ReadEv 0 101, ReadEv 0 108, ReadEv 0 108, ReadEv 0 111] := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- `read_model` with the regular file's descriptor moved to offset
`LLONG_MAX`, the position `lseek(fd, LLONG_MAX, SEEK_SET)` reaches on tmpfs.
Rocq's `readv_abcde_model` at the same offset holds "abcde" where this
file's holds "hi"; both reads are past end of file with a count of 1, so
the verdicts below do not depend on the contents. -/
def llong_max_model : Model :=
  with_fds (fd_insert read_fds 3 (.FdFile [102] (Z_to_bv 64 (2 ^ 63 - 1)))) read_model

/-- THE READ AT `LLONG_MAX` STILL ANSWERS 0 IN THE MODEL, where
`rw_verify_area` (fs/read_write.c:451, Linux v6.18.46), called by
`vfs_read` (:563) after `access_ok` and before the read, answers -EINVAL for
`(loff_t)(pos + count) < 0` (:467-469; its `pos < 0` branch at :462-464 is
the same missing test, reached only behind this one: `lseek_dest` stores
only destinations in [0, 2^63) and no read moves an offset past its
file's length, so a descriptor's offset passes 2^63 only through a read
that starts below it with `pos + count` at or past 2^63 — this divergence,
delivering where Linux answers -EINVAL — on a file longer than 2^63 - 1
bytes, which a run builds only through `write_spec`'s write-only arm,
whose position test is missing as well (an image may hold one: `valid_fs`
bounds no length); `modeled_file_gap` bounds how far
past its end one write starts, not how long a file grows).  This is the recorded divergence of
bugs/read-write-position-past-llong-max-answers-zero.md, pinned as Rocq
pins it — the read half of `readv_at_llong_max_is_einval_not_eof` — so
that closing it is a visible flip here rather than a silent one: the day
the file arm gains the position test, the first conjunct turns
`CheckReject` and the second `CheckOk`.  The descriptor is written back
at its unmoved offset, as the model's end-of-file answer does.
model: the recorded divergence bugs/read-write-position-past-llong-max-answers-zero.md, restated on the checker so that closing it flips this pin; not a claim about Linux, which answers -EINVAL here -/
theorem check_file_at_llong_max_still_answers_zero :
    check_read_row (read_in 3 4096 1 (wmem_first 1)) (mkEffect 0 [] []) llong_max_model
      = CheckOk llong_max_model []
    ∧ check_read_row (read_in 3 4096 1 (wmem_first 1)) (mkEffect (errno_ret EINVAL) [] [])
        llong_max_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

end RocqExamples

section Ledger

/-! ## The ledger: nothing rides along with the return

`read` writes the delivered bytes and nothing else: no zero-filled range,
no unmap, no pre-effect copy, no range charged as read from user memory —
`vfs_read` (fs/read_write.c:552-581, Linux v6.18.46) touches user memory
through `copy_to_user`-family copies inside the read operation alone.  A
trace that claims one beside the kernel's answer is refused on the
accepting path, where a checker comparing the return alone would have
passed it. -/

/-- On the -EBADF path: a zero-fill, an unmap, a copy, a copy-in and an
empty write entry beside the errno are each refused where the bare errno
is accepted.
kernel: fs/read_write.c:ksys_read@v6.18.46 -/
theorem closed_fd_ebadf_rejects_other_ledgers :
    check_read_row (read_in 30 4096 16 wmem_none) (mkEffect (errno_ret EBADF) [] [(4096, 16)])
        read_model = CheckReject
    ∧ check_read_row (read_in 30 4096 16 wmem_none)
        (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [(4096, 16)] [] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 30 4096 16 wmem_none)
        (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [] [MemCopy.mkCopy 4096 4096 16] [])
        read_model
      = CheckReject
    ∧ check_read_row (read_in 30 4096 16 wmem_none)
        (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [] [] [(4096, 16)]) read_model
      = CheckReject
    ∧ check_read_row (read_in 30 4096 16 wmem_none) (mkEffect (errno_ret EBADF) [(4096, [])] [])
        read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- On the delivering path: the same four beside the five delivered bytes,
and a second write entry, are each refused where the bare delivery is
accepted (`check_stdin_partial_destination_declines`, third conjunct).
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem stdin_delivery_rejects_other_ledgers :
    check_read_row (read_in 0 4096 100 (wmem_first 5))
        (mkEffect 5 [(4096, [104, 101, 108, 108, 111])] [(8192, 16)]) (with_stdin hello_stdin demo_model)
      = CheckReject
    ∧ check_read_row (read_in 0 4096 100 (wmem_first 5))
        (SyscallEffect.mkEffectU 5 [(4096, [104, 101, 108, 108, 111])] [] [(8192, 16)] [] [])
        (with_stdin hello_stdin demo_model)
      = CheckReject
    ∧ check_read_row (read_in 0 4096 100 (wmem_first 5))
        (SyscallEffect.mkEffectU 5 [(4096, [104, 101, 108, 108, 111])] [] []
          [MemCopy.mkCopy 8192 4096 5] [])
        (with_stdin hello_stdin demo_model)
      = CheckReject
    ∧ check_read_row (read_in 0 4096 100 (wmem_first 5))
        (SyscallEffect.mkEffectU 5 [(4096, [104, 101, 108, 108, 111])] [] [] [] [(4096, 5)])
        (with_stdin hello_stdin demo_model)
      = CheckReject
    ∧ check_read_row (read_in 0 4096 100 (wmem_first 5))
        (mkEffect 5 [(4096, [104, 101, 108]), (4099, [108, 111])] []) (with_stdin hello_stdin demo_model)
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- A DECLINED CALL IS DECLINED WHATEVER THE EFFECT SHAPE: on a descriptor
onto a path the file system does not hold — a model state no run builds —
the verdict is computed before the effect is looked at, so an odd-shaped
effect there is `CheckUnmodeled`, not `CheckReject`.
model: the file arm's decline on a path the file system does not hold precedes the effect match in `check_read`, so no effect shape reaches `CheckReject`; a claim about the checker's order, not about Linux, which never sees this model state -/
theorem a_declined_call_is_declined_whatever_the_effect_shape :
    check_read_row (read_in 7 4096 16 (wmem_first 16))
        (SyscallEffect.mkEffectU 0 [(4096, [1])] [(0, 0)] [] [] []) read_model
      = CheckUnmodeled
    ∧ check_read_row (read_in 7 4096 16 (wmem_first 16)) (mkEffect (errno_ret EFAULT) [] [])
        read_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> check_norm

end Ledger

section Descriptor

/-! ## `ksys_read`, then `vfs_read`'s mode test

`ksys_read` (fs/read_write.c:704-720, Linux v6.18.46) answers -EBADF on an
empty slot (:707) before `vfs_read` (:552-581) tests `FMODE_READ`
(:556-557) and answers -EBADF again on a descriptor opened without it.
Both come before `access_ok` (:560-561), so an unwritable or out-of-range
destination changes nothing on either. -/

/-- A closed descriptor: -EBADF with the model unchanged is the one accepted
answer; 0 and a delivery are refused; and the decline is refused too, since
-EBADF is the kernel's exact answer and not a coverage gap.  The -EFAULT
refused at the out-of-range destination is `vfs_read`'s (:560-561),
which the empty slot never reaches.
kernel: fs/read_write.c:ksys_read,vfs_read@v6.18.46 -/
theorem closed_fd_is_ebadf_on_the_checker :
    check_read_row (read_in 30 4096 16 wmem_none) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 30 4096 16 wmem_none) (mkEffect 0 [] []) read_model = CheckReject
    ∧ check_read_row (read_in 30 4096 16 (wmem_first 16)) (mkEffect 1 [(4096, [104])] [])
        read_model
      = CheckReject
    ∧ check_read_row (read_in 30 (Z_to_bv 64 (2 ^ 47 + 1)) 16 wmem_none)
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 30 (Z_to_bv 64 (2 ^ 47 + 1)) 16 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- …and never declined.
kernel: fs/read_write.c:ksys_read@v6.18.46 -/
theorem closed_fd_is_not_declined :
    check_read_row (read_in 30 4096 16 wmem_none) (mkEffect (errno_ret EBADF) [] []) read_model
      ≠ CheckUnmodeled := by
  rw [closed_fd_is_ebadf_on_the_checker.1]; exact fun h => nomatch h

/-- A descriptor opened write-only (fd 4): -EBADF from `vfs_read`'s
`FMODE_READ` test, the delivery and the 0 refused, and the range not yet
consulted — -EBADF is accepted at a destination past the limit too.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem write_only_fd_is_ebadf_on_the_checker :
    check_read_row (read_in 4 4096 16 (wmem_first 16)) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 4 4096 16 (wmem_first 16)) (mkEffect 1 [(4096, [106])] [])
        read_model
      = CheckReject
    ∧ check_read_row (read_in 4 4096 16 (wmem_first 16)) (mkEffect 0 [] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 4 (Z_to_bv 64 (2 ^ 47 + 1)) 16 wmem_none)
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 4 (Z_to_bv 64 (2 ^ 47 + 1)) 16 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- THE OTHER EDGES OF THE 32-BIT DESCRIPTOR: 2^31 and 2^32 - 1 arrive as
themselves — `unsigned int fd` (fs/read_write.c:722, Linux v6.18.46) holds
both — and name no slot of the table, so `ksys_read` answers -EBADF
(:706-707); 2^64 - 1 arrives as 2^32 - 1, the same empty slot; and
2^32 + 3 arrives as 3, the regular file, whose two bytes are delivered
with the offset moved.  0 on an empty slot and -EBADF on the file are
refused.
kernel: fs/read_write.c:read,ksys_read@v6.18.46 -/
theorem fd_edges_on_the_checker :
    check_read_row (read_in (Z_to_bv 64 (2 ^ 31)) 4096 16 (wmem_first 16))
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in (Z_to_bv 64 (2 ^ 32 - 1)) 4096 16 (wmem_first 16))
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in (Z_to_bv 64 (2 ^ 64 - 1)) 4096 16 (wmem_first 16))
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in (Z_to_bv 64 (2 ^ 31)) 4096 16 (wmem_first 16)) (mkEffect 0 [] [])
        read_model
      = CheckReject
    ∧ check_read_row (read_in (Z_to_bv 64 (2 ^ 64 - 1)) 4096 16 (wmem_first 16)) (mkEffect 0 [] [])
        read_model
      = CheckReject
    ∧ check_read_row (read_in (Z_to_bv 64 (2 ^ 32 + 3)) 4096 100 (wmem_first 2))
        (mkEffect 2 [(4096, [104, 105])] []) read_model
      = CheckOk (with_fds (fd_insert read_fds 3 (.FdFile [102] 2)) read_model) []
    ∧ check_read_row (read_in (Z_to_bv 64 (2 ^ 32 + 3)) 4096 100 (wmem_first 2))
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

end Descriptor

section Channel

/-! ## Standard input: the range, the zero count, then the stream

`vfs_read`'s access_ok test (fs/read_write.c:560-561, Linux v6.18.46) runs
on the count as named, before any byte is consulted, and `__access_ok`
(include/asm-generic/access_ok.h:31-40) is
`size <= TASK_SIZE && addr <= TASK_SIZE - size`: a zero count still faces
the range test.  Past it, `anon_pipe_read` (fs/pipe.c:269, Linux v6.18.46) returns 0 for
`total_len == 0` (:277-279) before looking at the queue, returns 0 on an
empty queue whose writers are gone (:370-371), and otherwise copies a
nonempty prefix of what is queued, up to the count (:343-360), answering
-EFAULT if not one byte can land (:346-347). -/

/-- The range verdict, three ways: a zero count one past the limit is
-EFAULT and never 0; a zero count at the limit is 0 and never -EFAULT; a
range ending one past the limit with input waiting is -EFAULT — not the 0 of
end of file, and not a delivery of the byte that is there.
kernel: fs/read_write.c:vfs_read; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem stdin_range_verdicts_on_the_checker :
    check_read_row (read_in 0 (Z_to_bv 64 (2 ^ 47 + 1)) 0 wmem_none) (mkEffect (errno_ret EFAULT) [] [])
        (stdin_model hello_stdin)
      = CheckOk (stdin_model hello_stdin) []
    ∧ check_read_row (read_in 0 (Z_to_bv 64 (2 ^ 47 + 1)) 0 wmem_none) (mkEffect 0 [] [])
        (stdin_model hello_stdin)
      = CheckReject
    ∧ check_read_row (read_in 0 (Z_to_bv 64 (2 ^ 47)) 0 wmem_none) (mkEffect 0 [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 0 (Z_to_bv 64 (2 ^ 47)) 0 wmem_none) (mkEffect (errno_ret EFAULT) [] [])
        read_model
      = CheckReject
    ∧ check_read_row (read_in 0 (Z_to_bv 64 (2 ^ 47 - 1)) 2 wmem_none) (mkEffect (errno_ret EFAULT) [] [])
        (stdin_model hello_stdin)
      = CheckOk (stdin_model hello_stdin) []
    ∧ check_read_row (read_in 0 (Z_to_bv 64 (2 ^ 47 - 1)) 2 wmem_none) (mkEffect 0 [] [])
        (stdin_model hello_stdin)
      = CheckReject
    ∧ check_read_row (read_in 0 (Z_to_bv 64 (2 ^ 47 - 1)) 2 wmem_all)
        (mkEffect 1 [(Z_to_bv 64 (2 ^ 47 - 1), [104])] []) (stdin_model hello_stdin)
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- A zero count in range is 0 with input waiting and nothing consumed —
`anon_pipe_read`'s `total_len == 0` return (fs/pipe.c:277-279) — never a
byte and never -EFAULT, whatever the destination holds.
kernel: fs/pipe.c:anon_pipe_read; fs/read_write.c:vfs_read@v6.18.46 -/
theorem stdin_zero_count_is_zero_on_the_checker :
    check_read_row (read_in 0 4096 0 wmem_none) (mkEffect 0 [] []) (stdin_model hello_stdin)
      = CheckOk (stdin_model hello_stdin) []
    ∧ check_read_row (read_in 0 4096 0 (wmem_first 5)) (mkEffect 1 [(4096, [104])] [])
        (stdin_model hello_stdin)
      = CheckReject
    ∧ check_read_row (read_in 0 4096 0 wmem_none) (mkEffect (errno_ret EFAULT) [] [])
        (stdin_model hello_stdin)
      = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- At end of file the answer is 0 — the `!pipe->writers` break at
fs/pipe.c:370-371 — with the destination never inspected: 0 is accepted on
an unwritable buffer, -EFAULT is refused there, and a delivered byte is
refused on a writable one.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem stdin_at_eof_is_zero_on_the_checker :
    check_read_row (read_in 0 4096 16 wmem_none) (mkEffect 0 [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 0 4096 16 wmem_none) (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 0 4096 16 (wmem_first 16)) (mkEffect 1 [(4096, [0])] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- With input waiting and not one destination byte writable, -EFAULT
(fs/pipe.c:346-347) with nothing consumed; 0 and the delivery are refused.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem stdin_unwritable_is_efault_on_the_checker :
    check_read_row (read_in 0 4096 16 wmem_none) (mkEffect (errno_ret EFAULT) [] [])
        (stdin_model hello_stdin)
      = CheckOk (stdin_model hello_stdin) []
    ∧ check_read_row (read_in 0 4096 16 wmem_none) (mkEffect 0 [] []) (stdin_model hello_stdin)
      = CheckReject
    ∧ check_read_row (read_in 0 4096 16 wmem_none) (mkEffect 5 [(4096, [104, 101, 108, 108, 111])] [])
        (stdin_model hello_stdin)
      = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- THE DELIVERY IS A NONEMPTY PREFIX, UP TO THE COUNT, AND EXACTLY WHAT WAS
COPIED: a two-byte prefix of the five is accepted with the stream advanced
past exactly those two and one event per byte; a byte the stream does not
hold, six bytes out of five, a return other than the delivered length, a
write at another address, and an empty write entry are each refused.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem stdin_delivers_a_prefix_on_the_checker :
    check_read_row (read_in 0 4096 100 (wmem_first 5)) (mkEffect 2 [(4096, [104, 101])] [])
        (stdin_model hello_stdin)
      = CheckOk (stdin_model (ICons 108 (ICons 108 (ICons 111 IEof)))) [ReadEv 0 104, ReadEv 0 101]
    ∧ check_read_row (read_in 0 4096 100 (wmem_first 5)) (mkEffect 2 [(4096, [104, 102])] [])
        (stdin_model hello_stdin)
      = CheckReject
    ∧ check_read_row (read_in 0 4096 100 (wmem_first 6))
        (mkEffect 6 [(4096, [104, 101, 108, 108, 111, 0])] []) (stdin_model hello_stdin)
      = CheckReject
    ∧ check_read_row (read_in 0 4096 100 (wmem_first 5)) (mkEffect 3 [(4096, [104, 101])] [])
        (stdin_model hello_stdin)
      = CheckReject
    ∧ check_read_row (read_in 0 4096 100 (wmem_first 5)) (mkEffect 2 [(4097, [104, 101])] [])
        (stdin_model hello_stdin)
      = CheckReject
    ∧ check_read_row (read_in 0 4096 100 (wmem_first 5)) (mkEffect 0 [(4096, [])] [])
        (stdin_model hello_stdin)
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- THE COUNT BOUNDS THE DELIVERY: asked for three of five, three are
accepted and four refused — `anon_pipe_read` copies `min(chars, total_len)`
per buffer (fs/pipe.c:327-334).
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem stdin_count_bounds_the_delivery_on_the_checker :
    check_read_row (read_in 0 4096 3 (wmem_first 5)) (mkEffect 3 [(4096, [104, 101, 108])] [])
        (stdin_model hello_stdin)
      = CheckOk (stdin_model (ICons 108 (ICons 111 IEof))) [ReadEv 0 104, ReadEv 0 101, ReadEv 0 108]
    ∧ check_read_row (read_in 0 4096 3 (wmem_first 5))
        (mkEffect 4 [(4096, [104, 101, 108, 108])] []) (stdin_model hello_stdin)
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- The channels that are not standard input (fd 1, fd 2) are -EBADF on a
read: the tracer's stdout and stderr pipes are held write-only — the
assumption bugs/channel-fds-assume-unidirectional-stdio.md records, since
the model reads the direction off the channel number — so `vfs_read`'s
`FMODE_READ` test (fs/read_write.c:556-557) fires.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem output_channels_are_ebadf_on_the_checker :
    check_read_row (read_in 1 4096 16 (wmem_first 16)) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 2 4096 16 (wmem_first 16)) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 1 4096 16 (wmem_first 16)) (mkEffect 0 [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- A COUNT WITH THE SIGN BIT SET fails `__access_ok`'s `size <= TASK_SIZE_MAX`
(include/asm-generic/access_ok.h:31-40, Linux v6.18.46) inside `vfs_read`'s
access_ok test, before any kind-specific code runs: on a channel it is
-EFAULT and never -EINVAL; on a socket, where `modeled_rw_range` is off for
a count that size, the checker declines rather than guess.
kernel: fs/read_write.c:vfs_read; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem sign_bit_count_on_the_checker :
    check_read_row (read_in 0 4096 (Z_to_bv 64 (2 ^ 63)) wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) (stdin_model hello_stdin)
      = CheckOk (stdin_model hello_stdin) []
    ∧ check_read_row (read_in 0 4096 (Z_to_bv 64 (2 ^ 63)) wmem_none)
        (mkEffect (errno_ret EINVAL) [] []) (stdin_model hello_stdin)
      = CheckReject
    ∧ check_read_row (read_in 10 4096 (Z_to_bv 64 (2 ^ 63)) wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- A COUNT WITH EVERY BIT SET IS -EFAULT, NOT -EINVAL: `__access_ok`'s
`size <= TASK_SIZE_MAX` fails inside `vfs_read`'s access_ok test
(fs/read_write.c:560-561, Linux v6.18.46) before `rw_verify_area` (:563)
can see `(ssize_t) count < 0` (:456-457) — on standard input with bytes
queued and on the regular file alike, -EINVAL refused on both.
kernel: fs/read_write.c:vfs_read,rw_verify_area@v6.18.46 -/
theorem all_ones_count_is_efault_on_the_checker :
    check_read_row (read_in 0 4096 (Z_to_bv 64 (2 ^ 64 - 1)) wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) (stdin_model hello_stdin)
      = CheckOk (stdin_model hello_stdin) []
    ∧ check_read_row (read_in 0 4096 (Z_to_bv 64 (2 ^ 64 - 1)) wmem_none)
        (mkEffect (errno_ret EINVAL) [] []) (stdin_model hello_stdin)
      = CheckReject
    ∧ check_read_row (read_in 3 4096 (Z_to_bv 64 (2 ^ 64 - 1)) wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 3 4096 (Z_to_bv 64 (2 ^ 64 - 1)) wmem_none)
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- THE ALL-ONES DESTINATION DOES NOT WRAP: `__access_ok`
(include/asm-generic/access_ok.h:31-41, Linux v6.18.46) tests
`addr <= limit - size` with `size <= limit` already established, so
neither side wraps and the address `2^64 - 1` with a count of 1 is
-EFAULT on standard input and on the regular file alike, 0 refused; a
checker that formed `addr + size` in 64 bits would see 0 and accept the
read.
kernel: include/asm-generic/access_ok.h:__access_ok; fs/read_write.c:vfs_read@v6.18.46 -/
theorem all_ones_destination_is_efault_on_the_checker :
    check_read_row (read_in 0 (Z_to_bv 64 (2 ^ 64 - 1)) 1 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) (stdin_model hello_stdin)
      = CheckOk (stdin_model hello_stdin) []
    ∧ check_read_row (read_in 0 (Z_to_bv 64 (2 ^ 64 - 1)) 1 wmem_none) (mkEffect 0 [] [])
        (stdin_model hello_stdin)
      = CheckReject
    ∧ check_read_row (read_in 3 (Z_to_bv 64 (2 ^ 64 - 1)) 1 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckOk read_model [] := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- A NULL DESTINATION PASSES THE RANGE TEST AND FAULTS IN THE COPY:
`__access_ok` (include/asm-generic/access_ok.h:31-40, Linux v6.18.46)
admits address 0 with a count of 16, so the verdict is the copy's, and no
byte can land: -EFAULT with nothing consumed on standard input
(`anon_pipe_read`, fs/pipe.c:344-347), on the regular file (offset
unmoved), on the pipe (queue unmoved) and on /dev/urandom
(`get_random_bytes_user`'s `ret ? ret : -EFAULT`, drivers/char/random.c:481);
0 is refused on each.
kernel: fs/read_write.c:vfs_read; fs/pipe.c:anon_pipe_read; drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem null_destination_is_efault_on_the_checker :
    check_read_row (read_in 0 0 16 wmem_none) (mkEffect (errno_ret EFAULT) [] [])
        (stdin_model hello_stdin)
      = CheckOk (stdin_model hello_stdin) []
    ∧ check_read_row (read_in 0 0 16 wmem_none) (mkEffect 0 [] []) (stdin_model hello_stdin)
      = CheckReject
    ∧ check_read_row (read_in 3 0 16 wmem_none) (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 3 0 16 wmem_none) (mkEffect 0 [] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 14 0 16 wmem_none) (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 14 0 16 wmem_none) (mkEffect 0 [] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 24 0 2 wmem_none) (mkEffect (errno_ret EFAULT) [] [])
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckOk (urandom_model (ICons 1 (ICons 2 IEof))) []
    ∧ check_read_row (read_in 24 0 2 wmem_none) (mkEffect 0 [] [])
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

end Channel

section Devices

/-! ## /dev/null, a directory, /dev/urandom -/

/-- /dev/null open read-only (fd 8) answers 0 without inspecting the
destination — `read_null` (drivers/char/mem.c:412-416, Linux v6.18.46) is
`return 0` — so 0 is accepted on an unwritable buffer and -EFAULT and a
byte are refused there; the range verdict still comes first, from
`vfs_read`'s `access_ok`.  Open write-only (fd 9) it is -EBADF.
kernel: drivers/char/mem.c:read_null; fs/read_write.c:vfs_read@v6.18.46 -/
theorem devnull_verdicts_on_the_checker :
    check_read_row (read_in 8 4096 16 wmem_none) (mkEffect 0 [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 8 4096 16 wmem_none) (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 8 4096 16 (wmem_first 16)) (mkEffect 1 [(4096, [0])] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 8 (Z_to_bv 64 (2 ^ 47 + 1)) 16 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 8 (Z_to_bv 64 (2 ^ 47 + 1)) 16 wmem_none) (mkEffect 0 [] [])
        read_model
      = CheckReject
    ∧ check_read_row (read_in 9 4096 16 (wmem_first 16)) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 9 4096 16 (wmem_first 16)) (mkEffect 0 [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- A directory (fd 5) is -EISDIR — `generic_read_dir` (fs/libfs.c:224-227,
Linux v6.18.46) — after the range verdict: at a destination past the limit
`vfs_read`'s access_ok test (fs/read_write.c:560-561) answers -EFAULT first
and -EISDIR is refused there.  0 is refused in range.
kernel: fs/libfs.c:generic_read_dir; fs/read_write.c:vfs_read@v6.18.46 -/
theorem directory_verdicts_on_the_checker :
    check_read_row (read_in 5 4096 16 (wmem_first 16)) (mkEffect (errno_ret EISDIR) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 5 4096 16 (wmem_first 16)) (mkEffect 0 [] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 5 (Z_to_bv 64 (2 ^ 47 + 1)) 16 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 5 (Z_to_bv 64 (2 ^ 47 + 1)) 16 wmem_none)
        (mkEffect (errno_ret EISDIR) [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- A ZERO COUNT ON A DIRECTORY IS STILL -EISDIR: `vfs_read`
(fs/read_write.c:552-581, Linux v6.18.46) has no zero-count short-circuit,
so the call reaches `generic_read_dir` (fs/libfs.c:224-227) and 0 is
refused; past the top of the range the zero count is -EFAULT from
`access_ok` (:560-561) first, and -EISDIR is refused there.
kernel: fs/libfs.c:generic_read_dir; fs/read_write.c:vfs_read@v6.18.46 -/
theorem directory_zero_count_on_the_checker :
    check_read_row (read_in 5 4096 0 wmem_none) (mkEffect (errno_ret EISDIR) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 5 4096 0 wmem_none) (mkEffect 0 [] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 5 (Z_to_bv 64 (2 ^ 47 + 1)) 0 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 5 (Z_to_bv 64 (2 ^ 47 + 1)) 0 wmem_none)
        (mkEffect (errno_ret EISDIR) [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- …and -EISDIR is never declined.
kernel: fs/libfs.c:generic_read_dir@v6.18.46 -/
theorem directory_eisdir_is_not_declined :
    check_read_row (read_in 5 4096 16 (wmem_first 16)) (mkEffect (errno_ret EISDIR) [] []) read_model
      ≠ CheckUnmodeled := by
  rw [directory_verdicts_on_the_checker.1]; exact fun h => nomatch h

/-- /dev/urandom (fd 24) over a declared two-byte stream: exactly the
count is delivered — `get_random_bytes_user` (drivers/char/random.c:434,
Linux v6.18.46) fills the whole request, short only on a signal between
pages (:471-473) or a copy that falls short (:456 for a request of at
most CHACHA_KEY_SIZE bytes, which these are; :465-467 in the loop past
it) — and the stream
advances past them, no event; one byte out of two is refused.  A count
the declared stream cannot fill is declined for every effect, since the
bytes Linux would deliver are ones the run never declared.  A zero count
is 0; an unwritable destination is -EFAULT with no byte delivered
(`get_random_bytes_user`'s two copies, drivers/char/random.c:456 and :465,
land nothing on a page none of which can take a byte, and :481 returns
-EFAULT for a zero `ret`); a partially writable one — the short copy of
:456, its partial count returned at :481 — is declined.
kernel: drivers/char/random.c:urandom_read_iter,get_random_bytes_user; fs/read_write.c:vfs_read@v6.18.46 -/
theorem urandom_verdicts_on_the_checker :
    check_read_row (read_in 24 4096 2 (wmem_first 2)) (mkEffect 2 [(4096, [1, 2])] [])
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckOk (urandom_model IEof) []
    ∧ check_read_row (read_in 24 4096 2 (wmem_first 2)) (mkEffect 1 [(4096, [1])] [])
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckReject
    ∧ check_read_row (read_in 24 4096 3 (wmem_first 3)) (mkEffect 2 [(4096, [1, 2])] [])
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckUnmodeled
    ∧ check_read_row (read_in 24 4096 3 (wmem_first 3)) (mkEffect 3 [(4096, [1, 2, 0])] [])
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckUnmodeled
    ∧ check_read_row (read_in 24 4096 0 wmem_none) (mkEffect 0 [] [])
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckOk (urandom_model (ICons 1 (ICons 2 IEof))) []
    ∧ check_read_row (read_in 24 4096 2 wmem_none) (mkEffect (errno_ret EFAULT) [] [])
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckOk (urandom_model (ICons 1 (ICons 2 IEof))) []
    ∧ check_read_row (read_in 24 4096 2 (wmem_first 1)) (mkEffect 2 [(4096, [1, 2])] [])
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- ORDER ON /dev/urandom: `vfs_read`'s access_ok test (fs/read_write.c:560-561,
Linux v6.18.46) runs before `urandom_read_iter` (drivers/char/random.c:1453)
is reached, so a destination past the top of the range is -EFAULT even
where the declared two-byte stream could not fill the count of 16 — the
decline never fires — and 0 or a delivery there is refused, the stream
unmoved.
kernel: fs/read_write.c:vfs_read; drivers/char/random.c:urandom_read_iter@v6.18.46 -/
theorem urandom_past_top_is_efault_on_the_checker :
    check_read_row (read_in 24 (Z_to_bv 64 (2 ^ 47 + 1)) 16 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckOk (urandom_model (ICons 1 (ICons 2 IEof))) []
    ∧ check_read_row (read_in 24 (Z_to_bv 64 (2 ^ 47 + 1)) 16 wmem_none) (mkEffect 0 [] [])
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckReject
    ∧ check_read_row (read_in 24 (Z_to_bv 64 (2 ^ 47 + 1)) 16 wmem_none)
        (mkEffect 2 [(Z_to_bv 64 (2 ^ 47 + 1), [1, 2])] []) (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- LIES ON /dev/urandom'S JUDGED ROWS: a zero count answers 0 and nothing
else — a byte and -EFAULT are refused; an unwritable destination answers
-EFAULT and nothing else — 0 and the delivery are refused; and on the
delivering row a bare 0, -EFAULT, the bytes at the wrong address, a wrong
byte of the right length, the right bytes under a wrong return and a
zero-fill beside the delivery are each refused where the exact delivery is
accepted (`urandom_verdicts_on_the_checker`, first conjunct).
kernel: drivers/char/random.c:get_random_bytes_user; fs/read_write.c:vfs_read@v6.18.46 -/
theorem urandom_lies_on_the_checker :
    check_read_row (read_in 24 4096 0 wmem_none) (mkEffect 1 [(4096, [1])] [])
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckReject
    ∧ check_read_row (read_in 24 4096 0 wmem_none) (mkEffect (errno_ret EFAULT) [] [])
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckReject
    ∧ check_read_row (read_in 24 4096 2 wmem_none) (mkEffect 0 [] [])
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckReject
    ∧ check_read_row (read_in 24 4096 2 wmem_none) (mkEffect 2 [(4096, [1, 2])] [])
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckReject
    ∧ check_read_row (read_in 24 4096 2 (wmem_first 2)) (mkEffect 0 [] [])
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckReject
    ∧ check_read_row (read_in 24 4096 2 (wmem_first 2)) (mkEffect (errno_ret EFAULT) [] [])
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckReject
    ∧ check_read_row (read_in 24 4096 2 (wmem_first 2)) (mkEffect 2 [(4097, [1, 2])] [])
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckReject
    ∧ check_read_row (read_in 24 4096 2 (wmem_first 2)) (mkEffect 2 [(4096, [1, 3])] [])
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckReject
    ∧ check_read_row (read_in 24 4096 2 (wmem_first 2)) (mkEffect 1 [(4096, [1, 2])] [])
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckReject
    ∧ check_read_row (read_in 24 4096 2 (wmem_first 2)) (mkEffect 2 [(4096, [1, 2])] [(8192, 16)])
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

end Devices

section Sockets

/-! ## Sockets: the range gate, then `tcp_recvmsg_locked`

The socket arm carries `Uaccess.modeled_rw_range`, which admits every
count at or below `rw_bytes_max` and, above it, a range inside the
address space; a count past the bound whose range leaves the address space
is DECLINED where Linux answers -EFAULT (bugs/write-out-of-range-short-write.md).
That entry has a second half, inherited here unchanged from the spec: a
count AT OR BELOW the bound whose range leaves the address space, with
writable memory under it, is ADMITTED as a delivery where `vfs_read`'s
access_ok (fs/read_write.c:560-561, Linux v6.18.46) answers -EFAULT before
the arm is reached.  The spec-level file states that half in its header
and pins it nowhere on purpose — a pin would pin the divergence — and this
file follows that choice; the two `*_big_out_of_range_count_*` pins below
mark where the gate takes over.
Past the gate, `sock_read_iter` (net/socket.c:1154-1174, Linux v6.18.46)
returns 0 on an empty iterator and otherwise hands the count to
`tcp_recvmsg_locked` (net/ipv4/tcp.c:2634), whose tests fire in order:
`TCP_LISTEN` → -ENOTCONN (:2651-2653); then, with nothing copied,
`SOCK_DONE` → 0 (:2741-2742), `sk_err` → the pending error (:2744-2747),
`RCV_SHUTDOWN` → 0 (:2749-2750), `TCP_CLOSE` → -ENOTCONN (:2752-2757).
`sock_error` (include/net/sock.h, Linux v6.18.46) reads `sk_err` with an `xchg` that
clears it, which is why a reported reset is reported once; `tcp_reset`
(net/ipv4/tcp_input.c:4678, Linux v6.18.46) stores ECONNRESET on an
established connection's RST and `tcp_write_err` (net/ipv4/tcp_timer.c:76-80,
Linux v6.18.46) `sk_err_soft ?: ETIMEDOUT` on the retransmit timer's
expiry — ETIMEDOUT itself only while no soft error, such as an
ICMP-reported EHOSTUNREACH, is pending, which is the case `NTimedOut`
models. -/

/-- A fresh, bound or listening socket is -ENOTCONN however large the
in-range request; 0 is refused; and a zero count is 0 before the state is
looked at — `sock_read_iter`'s empty-iterator return — with -ENOTCONN
refused there.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked; net/socket.c:sock_read_iter@v6.18.46 -/
theorem unconnected_socket_verdicts_on_the_checker :
    check_read_row (read_in 10 4096 16 (wmem_first 16)) (mkEffect (errno_ret ENOTCONN) [] [])
        read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 11 4096 16 (wmem_first 16)) (mkEffect (errno_ret ENOTCONN) [] [])
        read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 12 4096 16 (wmem_first 16)) (mkEffect (errno_ret ENOTCONN) [] [])
        read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 10 4096 16 (wmem_first 16)) (mkEffect 0 [] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 10 4096 (Z_to_bv 64 (2 ^ 40)) wmem_none)
        (mkEffect (errno_ret ENOTCONN) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 10 4096 0 wmem_none) (mkEffect 0 [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 10 4096 0 wmem_none) (mkEffect (errno_ret ENOTCONN) [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- …and -ENOTCONN on a fresh socket is never declined.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem fresh_socket_enotconn_is_not_declined :
    check_read_row (read_in 10 4096 16 (wmem_first 16)) (mkEffect (errno_ret ENOTCONN) [] [])
        read_model
      ≠ CheckUnmodeled := by
  rw [unconnected_socket_verdicts_on_the_checker.1]; exact fun h => nomatch h

/-- A count past `rw_bytes_max` at an address past the limit declines on a
socket for every effect, Linux's own -EFAULT from `vfs_read`'s `access_ok`
included: the gap is a decline, not a guess.
kernel: fs/read_write.c:vfs_read; net/socket.c:sock_read_iter; net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem socket_big_out_of_range_count_declines_on_the_checker :
    check_read_row (read_in 10 (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 40)) wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckUnmodeled
    ∧ check_read_row (read_in 10 (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 40)) wmem_none)
        (mkEffect (errno_ret ENOTCONN) [] []) read_model
      = CheckUnmodeled
    ∧ check_read_row (read_in 10 (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 40)) wmem_none)
        (mkEffect 0 [] []) read_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- A connection whose peer has finished (fd 20, `NFin`): 0, the
destination never inspected; a byte and -EFAULT are refused.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem socket_fin_is_zero_on_the_checker :
    check_read_row (read_in 20 4096 16 wmem_none) (mkEffect 0 [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 20 4096 16 (wmem_first 16)) (mkEffect 1 [(4096, [0])] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 20 4096 16 wmem_none) (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- A PENDING RESET IS REPORTED ONCE: on fd 21 (`NRst`) the accepted answer
is -ECONNRESET WITH the descriptor rewritten to `SkReset`, the state whose
next read is 0; 0 and a byte are refused on the first read, and on fd 13
(already `SkReset`) 0 is accepted and -ECONNRESET refused — `sock_error`'s
`xchg` cleared `sk_err`.
kernel: net/ipv4/tcp_input.c:tcp_reset; net/ipv4/tcp.c:tcp_recvmsg_locked; include/net/sock.h:sock_error@v6.18.46 -/
theorem socket_reset_verdicts_on_the_checker :
    check_read_row (read_in 21 4096 16 (wmem_first 16)) (mkEffect (errno_ret ECONNRESET) [] [])
        read_model
      = CheckOk (with_fds (fd_insert read_fds 21 (.FdSocket (.SkReset peer_a 7))) read_model) []
    ∧ check_read_row (read_in 21 4096 16 (wmem_first 16)) (mkEffect 0 [] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 21 4096 16 (wmem_first 16)) (mkEffect 1 [(4096, [0])] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 13 4096 16 (wmem_first 16)) (mkEffect 0 [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 13 4096 16 (wmem_first 16)) (mkEffect (errno_ret ECONNRESET) [] [])
        read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The timeout the same way: -ETIMEDOUT once — `tcp_write_err`'s
`sk_err_soft ?: ETIMEDOUT` with no soft error pending — with the descriptor
rewritten to `SkReset`; 0 refused on that read.
kernel: net/ipv4/tcp_timer.c:tcp_write_err; net/ipv4/tcp.c:tcp_recvmsg_locked; include/net/sock.h:sock_error@v6.18.46 -/
theorem socket_timeout_verdicts_on_the_checker :
    check_read_row (read_in 22 4096 16 (wmem_first 16)) (mkEffect (errno_ret ETIMEDOUT) [] [])
        read_model
      = CheckOk (with_fds (fd_insert read_fds 22 (.FdSocket (.SkReset peer_a 7))) read_model) []
    ∧ check_read_row (read_in 22 4096 16 (wmem_first 16)) (mkEffect 0 [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- QUEUED BYTES PREEMPT A PENDING ERROR: with a byte ahead of the reset,
the byte is delivered on channel 7, the script advanced to the reset, and
-ECONNRESET is refused; the terminal is never read as a byte, so two bytes
out of `b, RST` are refused too.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked; net/ipv4/tcp_input.c:tcp_reset@v6.18.46 -/
theorem socket_byte_before_reset_on_the_checker :
    check_read_row (read_in 25 4096 4 (wmem_first 5)) (mkEffect 1 [(4096, [5])] [])
        (socket_model (NCons 5 NRst))
      = CheckOk (with_fds (fd_insert (socket_fds (NCons 5 NRst)) 25
                  (.FdSocket (.SkConnected peer_a 7 NRst)))
                (socket_model (NCons 5 NRst)))
          [ReadEv 7 5]
    ∧ check_read_row (read_in 25 4096 4 (wmem_first 5)) (mkEffect (errno_ret ECONNRESET) [] [])
        (socket_model (NCons 5 NRst))
      = CheckReject
    ∧ check_read_row (read_in 25 4096 4 (wmem_first 5)) (mkEffect 2 [(4096, [5, 5])] [])
        (socket_model (NCons 5 NRst))
      = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- A connected socket delivers a nonempty prefix of what is queued, up to
the count, and the script advances past exactly that: two of two are
accepted, one of two is accepted, three are refused, and 0 is refused
while bytes are queued.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem socket_delivers_a_prefix_on_the_checker :
    check_read_row (read_in 25 4096 4 (wmem_first 5)) (mkEffect 2 [(4096, [1, 2])] [])
        (socket_model (NCons 1 (NCons 2 NFin)))
      = CheckOk (with_fds (fd_insert (socket_fds (NCons 1 (NCons 2 NFin))) 25
                  (.FdSocket (.SkConnected peer_a 7 NFin)))
                (socket_model (NCons 1 (NCons 2 NFin))))
          [ReadEv 7 1, ReadEv 7 2]
    ∧ check_read_row (read_in 25 4096 4 (wmem_first 5)) (mkEffect 1 [(4096, [1])] [])
        (socket_model (NCons 1 (NCons 2 NFin)))
      = CheckOk (with_fds (fd_insert (socket_fds (NCons 1 (NCons 2 NFin))) 25
                  (.FdSocket (.SkConnected peer_a 7 (NCons 2 NFin))))
                (socket_model (NCons 1 (NCons 2 NFin))))
          [ReadEv 7 1]
    ∧ check_read_row (read_in 25 4096 4 (wmem_first 5)) (mkEffect 3 [(4096, [1, 2, 0])] [])
        (socket_model (NCons 1 (NCons 2 NFin)))
      = CheckReject
    ∧ check_read_row (read_in 25 4096 4 (wmem_first 5)) (mkEffect 0 [] [])
        (socket_model (NCons 1 (NCons 2 NFin)))
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- THE COUNT BOUNDS THE DELIVERY ON A SOCKET: asked for one byte of the
two queued, `tcp_recvmsg_locked` copies `used = min(skb->len - offset, len)`
(net/ipv4/tcp.c:2794-2796, Linux v6.18.46), so one byte is delivered with
the script advanced past it alone, and both bytes are refused.  The
standard-input twin is `stdin_count_bounds_the_delivery_on_the_checker`.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem socket_count_bounds_the_delivery_on_the_checker :
    check_read_row (read_in 25 4096 1 (wmem_first 5)) (mkEffect 1 [(4096, [1])] [])
        (socket_model (NCons 1 (NCons 2 NFin)))
      = CheckOk (with_fds (fd_insert (socket_fds (NCons 1 (NCons 2 NFin))) 25
                  (.FdSocket (.SkConnected peer_a 7 (NCons 2 NFin))))
                (socket_model (NCons 1 (NCons 2 NFin))))
          [ReadEv 7 1]
    ∧ check_read_row (read_in 25 4096 1 (wmem_first 5)) (mkEffect 2 [(4096, [1, 2])] [])
        (socket_model (NCons 1 (NCons 2 NFin)))
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- ORDER ON A FRESH SOCKET: `vfs_read`'s access_ok test (fs/read_write.c:560-561,
Linux v6.18.46) runs before `sock_read_iter` hands the call to
`tcp_recvmsg_locked`, so a destination past the top of the range is -EFAULT
even though the socket has no peer, and -ENOTCONN there is refused.
kernel: fs/read_write.c:vfs_read; net/socket.c:sock_read_iter; net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem fresh_socket_past_top_is_efault_on_the_checker :
    check_read_row (read_in 10 (Z_to_bv 64 (2 ^ 47 + 1)) 16 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 10 (Z_to_bv 64 (2 ^ 47 + 1)) 16 wmem_none)
        (mkEffect (errno_ret ENOTCONN) [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- THE PENDING ERROR IS REPORTED ALONE: `tcp_recvmsg_locked` reads
`sock_error` only on the branch where nothing was copied, so on fd 21
(`NRst`) a byte beside -ECONNRESET is a lie; and past the top of the range
the answer is `vfs_read`'s -EFAULT with the reset still pending, so
-ECONNRESET there is refused too.
kernel: net/ipv4/tcp_input.c:tcp_reset; net/ipv4/tcp.c:tcp_recvmsg_locked; include/net/sock.h:sock_error; fs/read_write.c:vfs_read@v6.18.46 -/
theorem pending_error_reports_alone_on_the_checker :
    check_read_row (read_in 21 4096 16 (wmem_first 16))
        (mkEffect (errno_ret ECONNRESET) [(4096, [0])] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 21 (Z_to_bv 64 (2 ^ 47 + 1)) 16 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 21 (Z_to_bv 64 (2 ^ 47 + 1)) 16 wmem_none)
        (mkEffect (errno_ret ECONNRESET) [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- THE PENDING ERROR IS THE PEER'S, NOT A CLASS: on fd 21 (`NRst`) the
answer is `tcp_reset`'s ECONNRESET and -ETIMEDOUT is refused; on fd 22
(`NTimedOut`) it is `tcp_write_err`'s ETIMEDOUT and -ECONNRESET is refused.
A checker that reported "a pending error" without reading which one would
accept both.
kernel: net/ipv4/tcp_input.c:tcp_reset; net/ipv4/tcp_timer.c:tcp_write_err; include/net/sock.h:sock_error@v6.18.46 -/
theorem pending_error_errno_is_the_peers_on_the_checker :
    check_read_row (read_in 21 4096 16 (wmem_first 16)) (mkEffect (errno_ret ETIMEDOUT) [] [])
        read_model
      = CheckReject
    ∧ check_read_row (read_in 22 4096 16 (wmem_first 16)) (mkEffect (errno_ret ECONNRESET) [] [])
        read_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- A ZERO COUNT LEAVES THE PENDING ERROR PENDING: `sock_read_iter`
(net/socket.c:1168-1169, Linux v6.18.46) returns 0 on an empty iterator
before `sock_recvmsg` is called, so `sock_error`'s `xchg` never runs; on
fd 21 the zero count is 0 with the descriptor unchanged — the next read
still finds the reset — and -ECONNRESET is refused there.
kernel: net/socket.c:sock_read_iter; net/ipv4/tcp_input.c:tcp_reset; include/net/sock.h:sock_error@v6.18.46 -/
theorem pending_error_survives_a_zero_count_on_the_checker :
    check_read_row (read_in 21 4096 0 wmem_none) (mkEffect 0 [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 21 4096 0 wmem_none) (mkEffect (errno_ret ECONNRESET) [] [])
        read_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- THE DESTINATION ON A CONNECTED SOCKET WITH BYTES QUEUED: not one byte
writable is -EFAULT — `tcp_recvmsg_locked` (net/ipv4/tcp.c:2634, Linux
v6.18.46) turns a failed `skb_copy_datagram_msg` with nothing yet copied
into -EFAULT (:2822-2828) — the script unmoved, 0 and the delivery refused
there; the first byte writable and the second not is declined for every
effect, since the copy's progress is not described.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked; fs/read_write.c:vfs_read@v6.18.46 -/
theorem socket_destination_verdicts_on_the_checker :
    check_read_row (read_in 25 4096 4 wmem_none) (mkEffect (errno_ret EFAULT) [] [])
        (socket_model (NCons 1 (NCons 2 NFin)))
      = CheckOk (socket_model (NCons 1 (NCons 2 NFin))) []
    ∧ check_read_row (read_in 25 4096 4 wmem_none) (mkEffect 0 [] [])
        (socket_model (NCons 1 (NCons 2 NFin)))
      = CheckReject
    ∧ check_read_row (read_in 25 4096 4 wmem_none) (mkEffect 2 [(4096, [1, 2])] [])
        (socket_model (NCons 1 (NCons 2 NFin)))
      = CheckReject
    ∧ check_read_row (read_in 25 4096 4 (wmem_first 1)) (mkEffect 2 [(4096, [1, 2])] [])
        (socket_model (NCons 1 (NCons 2 NFin)))
      = CheckUnmodeled
    ∧ check_read_row (read_in 25 4096 4 (wmem_first 1)) (mkEffect 1 [(4096, [1])] [])
        (socket_model (NCons 1 (NCons 2 NFin)))
      = CheckUnmodeled
    ∧ check_read_row (read_in 25 4096 4 (wmem_first 1)) (mkEffect (errno_ret EFAULT) [] [])
        (socket_model (NCons 1 (NCons 2 NFin)))
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- LIES BESIDE A SOCKET DELIVERY: the two queued bytes at the wrong
address, under the wrong return, as an empty write entry, or with a
zero-fill, an unmap, a copy or a copy-in beside them are each refused where
the bare delivery is accepted (`socket_delivers_a_prefix_on_the_checker`,
first conjunct): the copy into `msg` is the call's only touch of user
memory.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked; fs/read_write.c:vfs_read@v6.18.46 -/
theorem socket_delivery_rejects_lies_on_the_checker :
    check_read_row (read_in 25 4096 4 (wmem_first 5)) (mkEffect 2 [(4097, [1, 2])] [])
        (socket_model (NCons 1 (NCons 2 NFin)))
      = CheckReject
    ∧ check_read_row (read_in 25 4096 4 (wmem_first 5)) (mkEffect 1 [(4096, [1, 2])] [])
        (socket_model (NCons 1 (NCons 2 NFin)))
      = CheckReject
    ∧ check_read_row (read_in 25 4096 4 (wmem_first 5)) (mkEffect 0 [(4096, [])] [])
        (socket_model (NCons 1 (NCons 2 NFin)))
      = CheckReject
    ∧ check_read_row (read_in 25 4096 4 (wmem_first 5)) (mkEffect 2 [(4096, [1, 2])] [(8192, 16)])
        (socket_model (NCons 1 (NCons 2 NFin)))
      = CheckReject
    ∧ check_read_row (read_in 25 4096 4 (wmem_first 5))
        (SyscallEffect.mkEffectU 2 [(4096, [1, 2])] [] [(8192, 16)] [] [])
        (socket_model (NCons 1 (NCons 2 NFin)))
      = CheckReject
    ∧ check_read_row (read_in 25 4096 4 (wmem_first 5))
        (SyscallEffect.mkEffectU 2 [(4096, [1, 2])] [] [] [MemCopy.mkCopy 8192 4096 2] [])
        (socket_model (NCons 1 (NCons 2 NFin)))
      = CheckReject
    ∧ check_read_row (read_in 25 4096 4 (wmem_first 5))
        (SyscallEffect.mkEffectU 2 [(4096, [1, 2])] [] [] [] [(4096, 2)])
        (socket_model (NCons 1 (NCons 2 NFin)))
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

end Sockets

section RegularFile

/-! ## A regular file

Deterministic: the file's bytes at the fd's offset, truncated at end of
file (`shmem_file_read_iter`, mm/shmem.c:3370 at Linux v6.18.46, breaks
at `iocb->ki_pos >= i_size`, :3388-3389) and at the `MAX_RW_COUNT` clamp
(fs/read_write.c:566-567); the offset advances by the delivered length
(`ksys_read` writes `f_pos` back, :716-717); no trace events. -/

/-- The whole file is delivered when the count allows: "hi" from offset 0
with the descriptor advanced to 2.  One byte, three bytes, a return of 1
with two bytes, and a bare 0 are each refused.
kernel: fs/read_write.c:ksys_read,vfs_read; mm/shmem.c:shmem_file_read_iter@v6.18.46 -/
theorem file_delivery_on_the_checker :
    check_read_row (read_in 3 4096 100 (wmem_first 16)) (mkEffect 2 [(4096, [104, 105])] [])
        read_model
      = CheckOk (with_fds (fd_insert read_fds 3 (.FdFile [102] 2)) read_model) []
    ∧ check_read_row (read_in 3 4096 100 (wmem_first 16)) (mkEffect 1 [(4096, [104])] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 3 4096 100 (wmem_first 16)) (mkEffect 3 [(4096, [104, 105, 0])] [])
        read_model
      = CheckReject
    ∧ check_read_row (read_in 3 4096 100 (wmem_first 16)) (mkEffect 1 [(4096, [104, 105])] [])
        read_model
      = CheckReject
    ∧ check_read_row (read_in 3 4096 100 (wmem_first 16)) (mkEffect 0 [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The count and the offset bound it: one byte asked from offset 0 is "h"
with the descriptor at 1; from offset 1 (fd 23) the rest is "i" with the
descriptor at 2.
kernel: fs/read_write.c:ksys_read,vfs_read; mm/shmem.c:shmem_file_read_iter@v6.18.46 -/
theorem file_count_and_offset_on_the_checker :
    check_read_row (read_in 3 4096 1 (wmem_first 1)) (mkEffect 1 [(4096, [104])] []) read_model
      = CheckOk (with_fds (fd_insert read_fds 3 (.FdFile [102] 1)) read_model) []
    ∧ check_read_row (read_in 23 4096 100 (wmem_first 16)) (mkEffect 1 [(4096, [105])] []) read_model
      = CheckOk (with_fds (fd_insert read_fds 23 (.FdFile [102] 2)) read_model) [] := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- At end of file (fd 6) the answer is 0, the descriptor written back with
its offset unmoved and the unmapped destination never inspected; -EFAULT
and a byte from past the end are refused.
kernel: fs/read_write.c:ksys_read; mm/shmem.c:shmem_file_read_iter@v6.18.46 -/
theorem file_at_eof_on_the_checker :
    check_read_row (read_in 6 4096 100 wmem_none) (mkEffect 0 [] []) read_model
      = CheckOk (with_fds (fd_insert read_fds 6 (.FdFile [102] 2)) read_model) []
    ∧ check_read_row (read_in 6 4096 100 wmem_none) (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 6 4096 100 (wmem_first 16)) (mkEffect 1 [(4096, [0])] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- Not one delivered byte writable: -EFAULT with the offset unchanged, the
delivery refused; the first byte writable and the second not: declined for
every effect, since the copy's rounded progress is not described.  A
descriptor onto a path the file system does not hold (fd 7) is declined.
kernel: fs/read_write.c:vfs_read; mm/shmem.c:shmem_file_read_iter@v6.18.46 -/
theorem file_destination_verdicts_on_the_checker :
    check_read_row (read_in 3 4096 100 wmem_none) (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 3 4096 100 wmem_none) (mkEffect 2 [(4096, [104, 105])] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 3 4096 100 (wmem_first 1)) (mkEffect 2 [(4096, [104, 105])] [])
        read_model
      = CheckUnmodeled
    ∧ check_read_row (read_in 3 4096 100 (wmem_first 1)) (mkEffect 1 [(4096, [104])] []) read_model
      = CheckUnmodeled
    ∧ check_read_row (read_in 3 4096 100 (wmem_first 1)) (mkEffect (errno_ret EFAULT) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_read_row (read_in 7 4096 16 (wmem_first 16)) (mkEffect 0 [] []) read_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- THE RANGE TEST IS `<=`: at TASK_SIZE - 2 with a count of 2 the sum is
TASK_SIZE exactly, which `__access_ok`'s `addr <= limit - size`
(include/asm-generic/access_ok.h:31-40, Linux v6.18.46) admits, so the
file's two bytes are delivered at the top of the address space — `wmem_all`
declaring the top writable, the copy not being what is at issue — and
-EFAULT there is refused.  A checker written `<` would swap the two
verdicts.
kernel: fs/read_write.c:vfs_read; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem file_range_at_top_delivers_on_the_checker :
    check_read_row (read_in 3 (Z_to_bv 64 (2 ^ 47 - 2)) 2 wmem_all)
        (mkEffect 2 [(Z_to_bv 64 (2 ^ 47 - 2), [104, 105])] []) read_model
      = CheckOk (with_fds (fd_insert read_fds 3 (.FdFile [102] 2)) read_model) []
    ∧ check_read_row (read_in 3 (Z_to_bv 64 (2 ^ 47 - 2)) 2 wmem_all)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- ORDER ON A REGULAR FILE: `vfs_read`'s access_ok test (fs/read_write.c:560-561,
Linux v6.18.46) runs before the file is read, so a destination past the
top of the range is -EFAULT with the offset unmoved — from the file's
start (fd 3), where 0 and the delivery are refused; at end of file (fd 6),
where the in-range answer is 0 and 0 is refused here; and on the
descriptor onto a path the file system does not hold (fd 7), where the
in-range verdict is a decline and the range verdict still comes first.
kernel: fs/read_write.c:vfs_read; mm/shmem.c:shmem_file_read_iter@v6.18.46 -/
theorem file_past_top_is_efault_on_the_checker :
    check_read_row (read_in 3 (Z_to_bv 64 (2 ^ 47 + 1)) 100 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 3 (Z_to_bv 64 (2 ^ 47 + 1)) 100 wmem_none) (mkEffect 0 [] [])
        read_model
      = CheckReject
    ∧ check_read_row (read_in 3 (Z_to_bv 64 (2 ^ 47 + 1)) 100 wmem_none)
        (mkEffect 2 [(Z_to_bv 64 (2 ^ 47 + 1), [104, 105])] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 6 (Z_to_bv 64 (2 ^ 47 + 1)) 100 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 6 (Z_to_bv 64 (2 ^ 47 + 1)) 100 wmem_none) (mkEffect 0 [] [])
        read_model
      = CheckReject
    ∧ check_read_row (read_in 7 (Z_to_bv 64 (2 ^ 47 + 1)) 16 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckOk read_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- A ZERO COUNT ON A REGULAR FILE: in range it is 0 with the descriptor
written back at its offset — `shmem_file_read_iter` (mm/shmem.c:3370,
Linux v6.18.46) finds `nr = 0` (:3428-3430), copies nothing and leaves
the loop at :3477-3478 with `retval` 0, and `ksys_read`
(fs/read_write.c:716-717) stores the unmoved position — and -EFAULT is
refused, there being nothing to inspect; past the top of the range it is
`vfs_read`'s -EFAULT (:560-561) before the file is reached, 0 refused
there.
kernel: fs/read_write.c:ksys_read,vfs_read; mm/shmem.c:shmem_file_read_iter@v6.18.46 -/
theorem file_zero_count_on_the_checker :
    check_read_row (read_in 3 4096 0 wmem_none) (mkEffect 0 [] []) read_model
      = CheckOk (with_fds (fd_insert read_fds 3 (.FdFile [102] 0)) read_model) []
    ∧ check_read_row (read_in 3 4096 0 wmem_none) (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 3 (Z_to_bv 64 (2 ^ 47 + 1)) 0 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 3 (Z_to_bv 64 (2 ^ 47 + 1)) 0 wmem_none) (mkEffect 0 [] [])
        read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- LIES BESIDE A FILE DELIVERY: the two bytes at the wrong address, a
wrong byte of the right length, and a zero-fill, an unmap, a copy or a
copy-in beside the exact delivery are each refused where the delivery is
accepted (`file_delivery_on_the_checker`, first conjunct).
kernel: fs/read_write.c:vfs_read; mm/shmem.c:shmem_file_read_iter@v6.18.46 -/
theorem file_delivery_rejects_lies_on_the_checker :
    check_read_row (read_in 3 4096 100 (wmem_first 16)) (mkEffect 2 [(4097, [104, 105])] [])
        read_model
      = CheckReject
    ∧ check_read_row (read_in 3 4096 100 (wmem_first 16)) (mkEffect 2 [(4096, [104, 106])] [])
        read_model
      = CheckReject
    ∧ check_read_row (read_in 3 4096 100 (wmem_first 16))
        (mkEffect 2 [(4096, [104, 105])] [(8192, 16)]) read_model
      = CheckReject
    ∧ check_read_row (read_in 3 4096 100 (wmem_first 16))
        (SyscallEffect.mkEffectU 2 [(4096, [104, 105])] [] [(8192, 16)] [] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 3 4096 100 (wmem_first 16))
        (SyscallEffect.mkEffectU 2 [(4096, [104, 105])] [] [] [MemCopy.mkCopy 8192 4096 2] [])
        read_model
      = CheckReject
    ∧ check_read_row (read_in 3 4096 100 (wmem_first 16))
        (SyscallEffect.mkEffectU 2 [(4096, [104, 105])] [] [] [] [(4096, 2)]) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

end RegularFile

section Pipes

/-! ## A pipe's read end

`anon_pipe_read` (fs/pipe.c:269, Linux v6.18.46): the write end is
-EBADF from `vfs_read`'s `FMODE_READ` test before it is reached; queued
bytes are delivered up to the count and consumed, the page mark left where
it was; an empty pipe with a live writer sleeps at :388, which the model
declines; an empty pipe with no writer is 0 at :370-371 before any copy.
The range gate is the socket arm's, with the same admitted half below the
bound; the Sockets header above says where that is recorded and why no pin
states it. -/

/-- Pipe 0 ("ab", fd 14): both bytes delivered and consumed, the mark
unmoved; one byte out of two refused; asked for one, one is delivered and
the other stays queued.  A zero count is 0 with nothing consumed.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem pipe_delivery_on_the_checker :
    check_read_row (read_in 14 4096 16 (wmem_first 16)) (mkEffect 2 [(4096, [97, 98])] []) read_model
      = CheckOk (with_pipes [(0, ([], 2)), (1, ([], 0)), (2, ([], 3))] read_model) []
    ∧ check_read_row (read_in 14 4096 16 (wmem_first 16)) (mkEffect 1 [(4096, [97])] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 14 4096 16 (wmem_first 16)) (mkEffect 2 [] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 14 4096 1 (wmem_first 16)) (mkEffect 1 [(4096, [97])] []) read_model
      = CheckOk (with_pipes [(0, ([98], 2)), (1, ([], 0)), (2, ([], 3))] read_model) []
    ∧ check_read_row (read_in 14 4096 0 wmem_none) (mkEffect 0 [] []) read_model
      = CheckOk read_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- The write end (fd 15) is -EBADF, a byte refused.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem pipe_write_end_is_ebadf_on_the_checker :
    check_read_row (read_in 15 4096 16 (wmem_first 16)) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 15 4096 16 (wmem_first 16)) (mkEffect 1 [(4096, [97])] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> check_norm

/-- AN EMPTY PIPE WITH A LIVE WRITER HAS NO ANSWER (fd 16, writer fd 17):
`anon_pipe_read` sleeps at fs/pipe.c:388, the model never waits and no
modeled pipe is O_NONBLOCK, so 0, -EAGAIN and a byte are each declined
rather than judged.  A pipe id the table does not hold (fd 19) is
declined too.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem pipe_empty_with_writer_declines_on_the_checker :
    check_read_row (read_in 16 4096 16 (wmem_first 16)) (mkEffect 0 [] []) read_model
      = CheckUnmodeled
    ∧ check_read_row (read_in 16 4096 16 (wmem_first 16)) (mkEffect (errno_ret EAGAIN) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_read_row (read_in 16 4096 16 (wmem_first 16)) (mkEffect 1 [(4096, [0])] []) read_model
      = CheckUnmodeled
    ∧ check_read_row (read_in 19 4096 16 (wmem_first 16)) (mkEffect 0 [] []) read_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- …BUT NOT BEFORE THE ZERO COUNT, AND AHEAD OF THE RANGE VERDICT:
`anon_pipe_read`'s null read (fs/pipe.c:277-279, Linux v6.18.46) returns 0
before the mutex at :282 is taken, so a zero count on fd 16 is 0 and
-EAGAIN is refused; a destination past the top of the range, where
`vfs_read`'s access_ok (fs/read_write.c:560-561) answers -EFAULT before
the pipe is reached, is declined here all the same — on this arm the
decline sits ahead of the range verdict, fail-closed where Linux has an
answer.
kernel: fs/pipe.c:anon_pipe_read; fs/read_write.c:vfs_read@v6.18.46 -/
theorem pipe_empty_with_writer_edges_on_the_checker :
    check_read_row (read_in 16 4096 0 wmem_none) (mkEffect 0 [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 16 4096 0 wmem_none) (mkEffect (errno_ret EAGAIN) [] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 16 (Z_to_bv 64 (2 ^ 47 + 1)) 16 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- With no writer left (fd 18) an empty pipe is end of file: 0 with the
destination never inspected, a byte and -EFAULT refused.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem pipe_empty_without_writer_is_eof_on_the_checker :
    check_read_row (read_in 18 4096 16 wmem_none) (mkEffect 0 [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 18 4096 16 (wmem_first 16)) (mkEffect 1 [(4096, [0])] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 18 4096 16 wmem_none) (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> check_norm

/-- The destination on a queued pipe: not one byte writable is -EFAULT
(fs/pipe.c:346-347) with nothing consumed; the first writable and the
second not is declined.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem pipe_destination_verdicts_on_the_checker :
    check_read_row (read_in 14 4096 16 wmem_none) (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 14 4096 16 wmem_none) (mkEffect 2 [(4096, [97, 98])] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 14 4096 16 (wmem_first 1)) (mkEffect 2 [(4096, [97, 98])] [])
        read_model
      = CheckUnmodeled
    ∧ check_read_row (read_in 14 4096 16 (wmem_first 1)) (mkEffect 1 [(4096, [97])] []) read_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> check_norm

/-- THE RANGE GATE ON A PIPE, AND WHAT PRECEDES IT: a count past
`rw_bytes_max` whose range leaves the address space declines on the read
end (fd 14) for every effect, Linux's own -EFAULT from `vfs_read`'s
access_ok test included — the pipe twin of
`socket_big_out_of_range_count_declines_on_the_checker`, the declined half
of what bugs/write-out-of-range-short-write.md records for both arms (the
admitted half below the bound is the Sockets header's); on the write
end (fd 15) the same call is -EBADF and -EFAULT is refused, since
`vfs_read`'s `FMODE_READ` test (fs/read_write.c:556-557, Linux v6.18.46)
runs before its access_ok test (:560-561).
kernel: fs/read_write.c:vfs_read; fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem pipe_big_out_of_range_count_on_the_checker :
    check_read_row (read_in 14 (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 40)) wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckUnmodeled
    ∧ check_read_row (read_in 14 (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 40)) wmem_none)
        (mkEffect 0 [] []) read_model
      = CheckUnmodeled
    ∧ check_read_row (read_in 14 (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 40)) wmem_none)
        (mkEffect 2 [(Z_to_bv 64 (2 ^ 63), [97, 98])] []) read_model
      = CheckUnmodeled
    ∧ check_read_row (read_in 15 (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 40)) wmem_none)
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 15 (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 40)) wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- LIES BESIDE A PIPE DELIVERY: the two bytes under the wrong return, at
the wrong address, a wrong byte of the right length, and a zero-fill, an
unmap, a copy or a copy-in beside the exact delivery are each refused
where the delivery is accepted (`pipe_delivery_on_the_checker`, first
conjunct); a zero count answers 0 and nothing else — a byte and -EFAULT
are refused there.
kernel: fs/pipe.c:anon_pipe_read; fs/read_write.c:vfs_read@v6.18.46 -/
theorem pipe_delivery_rejects_lies_on_the_checker :
    check_read_row (read_in 14 4096 16 (wmem_first 16)) (mkEffect 1 [(4096, [97, 98])] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 14 4096 16 (wmem_first 16)) (mkEffect 2 [(4097, [97, 98])] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 14 4096 16 (wmem_first 16)) (mkEffect 2 [(4096, [97, 99])] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 14 4096 16 (wmem_first 16))
        (mkEffect 2 [(4096, [97, 98])] [(8192, 16)]) read_model
      = CheckReject
    ∧ check_read_row (read_in 14 4096 16 (wmem_first 16))
        (SyscallEffect.mkEffectU 2 [(4096, [97, 98])] [] [(8192, 16)] [] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 14 4096 16 (wmem_first 16))
        (SyscallEffect.mkEffectU 2 [(4096, [97, 98])] [] [] [MemCopy.mkCopy 8192 4096 2] [])
        read_model
      = CheckReject
    ∧ check_read_row (read_in 14 4096 16 (wmem_first 16))
        (SyscallEffect.mkEffectU 2 [(4096, [97, 98])] [] [] [] [(4096, 2)]) read_model
      = CheckReject
    ∧ check_read_row (read_in 14 4096 0 wmem_none) (mkEffect 1 [(4096, [97])] []) read_model
      = CheckReject
    ∧ check_read_row (read_in 14 4096 0 wmem_none) (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> check_norm

/-- A SPLIT LEDGER IS A LIE ABOUT THE SHAPE, NOT THE BYTES: the same two
bytes at the same two addresses, written as two one-byte runs, are refused
— the checker compares the ledger to `Sys.Uaccess.delivered_writes`, one
run per delivery, which is the shape the tracer records and the shape the
`split-writes` mutation of `testing/syscall-check/main.ml` lies against
(`read_spec.c`'s `reject --mutate read:split-writes` case, on the channel
arm of the Rocq checker; `stdin_delivery_rejects_other_ledgers` above is
that arm's twin here).
model: `Sys.Uaccess.delivered_writes`'s one-run shape, held by `writes_eqb` on the pipe arm; a claim about the ledger's canonical form, not about Linux, which stores the same bytes either way -/
theorem pipe_delivery_rejects_a_split_ledger_on_the_checker :
    check_read_row (read_in 14 4096 16 (wmem_first 16))
        (mkEffect 2 [(4096, [97]), (4097, [98])] []) read_model
      = CheckReject := by
  check_norm

end Pipes

section Clamp

/-! ## The `MAX_RW_COUNT` clamp, symbolically

`vfs_read` clamps the count to `MAX_RW_COUNT` (fs/read_write.c:566-567,
Linux v6.18.46; include/linux/fs.h:2838) after `access_ok` and before the
read, so no kernel acknowledges a byte past it.  No fixture in this tree
holds more than `MAX_RW_COUNT` bytes, so both facts are stated as Rocq
states them: over every file, model and count, on `check_read` itself. -/

/-- Rocq's `read_ret_over_clamp_rejected`: a kernel that read one byte past
the clamp and returned the RAW count `MAX_RW_COUNT + 1` beside the clamped
delivery is refused — the accepted return is the delivered length, which
`file_read_clamped_len` holds at or below `MAX_RW_COUNT`.  The hypotheses
are Rocq's: a held file, its data, a count of exactly `MAX_RW_COUNT + 1`
whose range passes `access_ok` (the clamp is only reached past it), a
writable destination for the clamped delivery, and a nonempty delivery.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem read_ret_over_clamp_rejected (i : SyscallInput) (m : Model) (fd : word) (p : path)
    (data : List byte) (buf count off : word) (w : List byte)
    (hfd : fd_lookup (m_fds m) fd = some (.FdFile p off))
    (hfs : fs_lookup (m_fs m) p = some data)
    (hc : bv_unsigned count = MAX_RW_COUNT + 1)
    (hok : access_okb buf (bv_unsigned count) = true)
    (hw : read_bytes_map i.in_wmem buf
      (len_word (file_read data off (Z_to_bv 64 (rw_count_clamp count)))) = some w)
    (hne : file_read data off (Z_to_bv 64 (rw_count_clamp count)) ≠ []) :
    check_read i fd buf count
      (mkEffect count [(buf, file_read data off (Z_to_bv 64 (rw_count_clamp count)))] []) m
      = CheckReject := by
  have hlen := file_read_clamped_len data off count
  unfold check_read
  rw [hfd]
  dsimp only
  rw [hok]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hfs]
  dsimp only
  generalize hbs : file_read data off (Z_to_bv 64 (rw_count_clamp count)) = bs at hw hne hlen ⊢
  rw [hw]
  dsimp only
  cases bs with
  | nil => exact absurd rfl hne
  | cons b bs0 =>
    dsimp only
    cases hb : bv_eqb count (len_word (b :: bs0)) with
    | true =>
      exfalso
      have h1 := (bv_eqb_eq _ _).mp hb
      have h2 := len_word_unsigned (b :: bs0)
        (by unfold two_pow_64; unfold MAX_RW_COUNT at hlen; omega)
      rw [← h1] at h2
      omega
    | false =>
      simp only [bv_eqb_refl, listN_eqb_refl, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

/-- Rocq's `read_delivery_clamped`: whatever `read_spec` admits with a
single write entry, that entry holds at most `MAX_RW_COUNT` bytes — on
every descriptor kind, every model and every count.  Proved as Rocq
proves it, through `check_read_complete_ok` and a walk of the checker's
arms: every non-delivering arm is a `check_ret_only`, whose accepted
effect has no write entry; the channel and socket arms carry the bound
in their own `≤ rw_count_clamp count` test; the file arm delivers
`file_read` at the clamped count (`file_read_clamped_len`); the pipe arm
`pipe_take` at it (`pipe_take_length`); /dev/urandom is
`check_read_urandom_delivery_clamped`.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem read_delivery_clamped (fd buf count : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event) (a : word) (bs : List byte)
    (hspec : read_spec fd buf count i m (Ok eff m' evs)) (hws : eff.eff_writes = [(a, bs)]) :
    (bs.length : Int) ≤ MAX_RW_COUNT := by
  have h := check_read_complete_ok i fd buf count eff m m' evs hspec
  have hclamp := (rw_count_clamp_range count).2
  have hro : ∀ (v : word) (mk : Model) (k : List event),
      check_ret_only eff v mk k = CheckOk m' evs → (bs.length : Int) ≤ MAX_RW_COUNT := by
    intro v mk k hz
    obtain ⟨heq, -, -⟩ := (check_ret_only_ok_iff eff v mk k m' evs).mp hz
    subst heq
    simp only [reduceCtorEq] at hws
  have hnodel : ∀ (v : word) (mk mk2 : Model) (k : List event),
      check_access_ok_zero buf count eff mk (check_ret_only eff v mk2 k) = CheckOk m' evs →
      (bs.length : Int) ≤ MAX_RW_COUNT := by
    intro v mk mk2 k hz
    unfold check_access_ok_zero at hz
    generalize access_okb buf (bv_unsigned count) = ok at hz
    cases ok with
    | true => simp only [↓reduceIte] at hz; exact hro _ _ _ hz
    | false => simp only [Bool.false_eq_true, ↓reduceIte] at hz; exact hro _ _ _ hz
  unfold check_read at h
  generalize fd_lookup (m_fds m) fd = r at h
  cases r with
  | none => exact hro _ _ _ h
  | some e =>
    cases e with
    | FdFileA _ _ => cases h
    | FdFileRW _ _ => cases h
    | FdFileW _ _ => exact hro _ _ _ h
    | FdDir =>
      dsimp only at h
      generalize (!access_okb buf (bv_unsigned count)) = g at h
      cases g with
      | true => simp only [↓reduceIte] at h; exact hro _ _ _ h
      | false => simp only [Bool.false_eq_true, ↓reduceIte] at h; exact hro _ _ _ h
    | FdDevNull rd _ =>
      dsimp only at h
      cases rd with
      | false => simp only [Bool.not_false, ↓reduceIte] at h; exact hro _ _ _ h
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        exact hnodel _ _ _ _ h
    | FdUrandom =>
      dsimp only at h
      generalize (!access_okb buf (bv_unsigned count)) = g at h
      cases g with
      | true => simp only [↓reduceIte] at h; exact hro _ _ _ h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        exact check_read_urandom_delivery_clamped i buf count eff m m' evs a bs h hws
    | FdChannel ch =>
      dsimp only at h
      generalize (!w_is0 ch) = g1 at h
      cases g1 with
      | true => simp only [↓reduceIte] at h; exact hro _ _ _ h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        generalize (!access_okb buf (bv_unsigned count)) = g2 at h
        cases g2 with
        | true => simp only [↓reduceIte] at h; exact hro _ _ _ h
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          generalize w_is0 count = g3 at h
          cases g3 with
          | true => simp only [↓reduceIte] at h; exact hro _ _ _ h
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at h
            generalize (m_stdin m).uncons = u at h
            cases u with
            | none => exact hro _ _ _ h
            | some _ =>
              dsimp only at h
              generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h
              cases w1 with
              | none => exact hro _ _ _ h
              | some _ =>
                dsimp only at h
                generalize read_bytes_map i.in_wmem buf
                  (len_word (stream_take_z (m_stdin m) (rw_count_clamp count)).1) = w2 at h
                cases w2 with
                | none => cases h
                | some _ =>
                  dsimp only at h
                  split at h
                  · simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hws
                    obtain ⟨rfl, rfl⟩ := hws
                    split at h
                    · rename_i hg
                      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
                      obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hle⟩, -⟩, -⟩ := hg
                      exact Int.le_trans hle hclamp
                    · cases h
                  · cases h
    | FdSocket sk =>
      dsimp only at h
      generalize (!modeled_rw_range buf count) = g1 at h
      cases g1 with
      | true => simp only [↓reduceIte] at h; cases h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        generalize w_is0 count = g3 at h
        cases g3 with
        | true => simp only [↓reduceIte] at h; exact hnodel _ _ _ _ h
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          cases sk with
          | SkFresh => exact hnodel _ _ _ _ h
          | SkBound => exact hnodel _ _ _ _ h
          | SkListening => exact hnodel _ _ _ _ h
          | SkReset _ _ => exact hnodel _ _ _ _ h
          | SkConnected peer ch rx =>
            dsimp only at h
            generalize rx.cell_at 0 = c at h
            cases c with
            | NFin => exact hnodel _ _ _ _ h
            | NRst => unfold check_socket_pending_error at h; exact hnodel _ _ _ _ h
            | NTimedOut => unfold check_socket_pending_error at h; exact hnodel _ _ _ _ h
            | NByte _ =>
              dsimp only at h
              generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h
              cases w1 with
              | none => exact hro _ _ _ h
              | some _ =>
                dsimp only at h
                generalize read_bytes_map i.in_wmem buf
                  (len_word (net_take_z rx (rw_count_clamp count)).1) = w2 at h
                cases w2 with
                | none => cases h
                | some _ =>
                  dsimp only at h
                  split at h
                  · simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hws
                    obtain ⟨rfl, rfl⟩ := hws
                    split at h
                    · rename_i hg
                      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
                      obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hle⟩, -⟩, -⟩ := hg
                      exact Int.le_trans hle hclamp
                    · cases h
                  · cases h
    | FdFile p off =>
      dsimp only at h
      generalize (!access_okb buf (bv_unsigned count)) = g at h
      cases g with
      | true => simp only [↓reduceIte] at h; exact hro _ _ _ h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        generalize fs_lookup (m_fs m) p = fl at h
        cases fl with
        | none => cases h
        | some data =>
          dsimp only at h
          have hlen := file_read_clamped_len data off count
          generalize hbsF : file_read data off (Z_to_bv 64 (rw_count_clamp count)) = bsF at h hlen
          generalize read_bytes_map i.in_wmem buf (len_word bsF) = w1 at h
          cases w1 with
          | none =>
            dsimp only at h
            generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w2 at h
            cases w2 with
            | none => exact hro _ _ _ h
            | some _ => cases h
          | some _ =>
            dsimp only at h
            cases bsF with
            | nil => exact hro _ _ _ h
            | cons b bs0 =>
              dsimp only at h
              split at h
              · simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hws
                obtain ⟨rfl, rfl⟩ := hws
                split at h
                · rename_i hg
                  simp only [Bool.and_eq_true, listN_eqb_eq] at hg
                  obtain ⟨⟨-, rfl⟩, -⟩ := hg
                  exact hlen
                · cases h
              · cases h
    | FdPipe id w =>
      dsimp only at h
      cases w with
      | true => simp only [↓reduceIte] at h; exact hro _ _ _ h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        generalize (!modeled_rw_range buf count) = g1 at h
        cases g1 with
        | true => simp only [↓reduceIte] at h; cases h
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          generalize w_is0 count = g3 at h
          cases g3 with
          | true => simp only [↓reduceIte] at h; exact hnodel _ _ _ _ h
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at h
            generalize pipe_lookup (m_pipes m) id = pl at h
            rcases pl with _ | ⟨_ | ⟨b, q0⟩, used⟩
            · cases h
            · dsimp only at h
              generalize pipe_end_live (m_fds m) id true = lv at h
              cases lv with
              | true => simp only [↓reduceIte] at h; cases h
              | false => simp only [Bool.false_eq_true, ↓reduceIte] at h; exact hnodel _ _ _ _ h
            · dsimp only at h
              have hpt := pipe_take_length (b :: q0) (rw_count_clamp count)
              have h0 := (rw_count_clamp_range count).1
              generalize hdel : pipe_take (b :: q0) (rw_count_clamp count) = del at h hpt
              generalize read_bytes_map i.in_wmem buf (len_word del) = w1 at h
              cases w1 with
              | none =>
                dsimp only at h
                generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w2 at h
                cases w2 with
                | none => exact hro _ _ _ h
                | some _ => cases h
              | some _ =>
                dsimp only at h
                split at h
                · dsimp only at hws
                  subst hws
                  split at h
                  · rename_i hg
                    simp only [Bool.and_eq_true, writes_eqb_eq] at hg
                    obtain ⟨hweq, -⟩ := hg
                    unfold delivered_writes at hweq
                    cases del with
                    | nil => cases hweq
                    | cons d ds =>
                      simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hweq
                      obtain ⟨-, rfl⟩ := hweq
                      omega
                  · cases h
                · cases h

end Clamp

section Witness

/-! ## The witness: which outcome it names

`read_witness_ok` says the witness is an outcome the spec admits; what it
cannot say is WHICH.  Each pin below names the outcome for one call, on the
same fixtures the verdict pins use, and the last two say the checker
accepts whatever the witness names, on every call, by proof rather than
by inspection. -/

/-- On the deterministic arms the witness is the kernel's answer: -EBADF
on a closed fd and on the write-only kinds, -EISDIR on a directory, 0 on
/dev/null, -ENOTCONN on a fresh socket, 0 at a finished peer and at end of
file, -ECONNRESET once with the descriptor rewritten, and -EFAULT where the
range or the whole destination refuses.
kernel: fs/read_write.c:ksys_read,vfs_read; fs/libfs.c:generic_read_dir; drivers/char/mem.c:read_null; net/ipv4/tcp.c:tcp_recvmsg_locked; net/ipv4/tcp_input.c:tcp_reset; fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem read_witness_names_the_deterministic_answer :
    read_witness_row (read_in 30 4096 16 wmem_none) read_model
      = Ok (mkEffect (errno_ret EBADF) [] []) read_model []
    ∧ read_witness_row (read_in 4 4096 16 (wmem_first 16)) read_model
      = Ok (mkEffect (errno_ret EBADF) [] []) read_model []
    ∧ read_witness_row (read_in 15 4096 16 (wmem_first 16)) read_model
      = Ok (mkEffect (errno_ret EBADF) [] []) read_model []
    ∧ read_witness_row (read_in 5 4096 16 (wmem_first 16)) read_model
      = Ok (mkEffect (errno_ret EISDIR) [] []) read_model []
    ∧ read_witness_row (read_in 8 4096 16 wmem_none) read_model
      = Ok (mkEffect 0 [] []) read_model []
    ∧ read_witness_row (read_in 10 4096 16 (wmem_first 16)) read_model
      = Ok (mkEffect (errno_ret ENOTCONN) [] []) read_model []
    ∧ read_witness_row (read_in 20 4096 16 wmem_none) read_model
      = Ok (mkEffect 0 [] []) read_model []
    ∧ read_witness_row (read_in 0 4096 16 wmem_none) read_model
      = Ok (mkEffect 0 [] []) read_model []
    ∧ read_witness_row (read_in 18 4096 16 wmem_none) read_model
      = Ok (mkEffect 0 [] []) read_model []
    ∧ read_witness_row (read_in 6 4096 100 wmem_none) read_model
      = Ok (mkEffect 0 [] []) (with_fds (fd_insert read_fds 6 (.FdFile [102] 2)) read_model) []
    ∧ read_witness_row (read_in 21 4096 16 (wmem_first 16)) read_model
      = Ok (mkEffect (errno_ret ECONNRESET) [] [])
          (with_fds (fd_insert read_fds 21 (.FdSocket (.SkReset peer_a 7))) read_model) []
    ∧ read_witness_row (read_in 0 (Z_to_bv 64 (2 ^ 47 + 1)) 0 wmem_none) (stdin_model hello_stdin)
      = Ok (mkEffect (errno_ret EFAULT) [] []) (stdin_model hello_stdin) []
    ∧ read_witness_row (read_in 0 4096 16 wmem_none) (stdin_model hello_stdin)
      = Ok (mkEffect (errno_ret EFAULT) [] []) (stdin_model hello_stdin) []
    ∧ read_witness_row (read_in 3 4096 100 wmem_none) read_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> witness_norm

/-- Where the spec CHOOSES — a channel or a connected socket with bytes
queued — the witness names the shortest admitted delivery, one byte, with
the stream advanced past it and its one event; where the delivery is
computed — a file, a pipe, /dev/urandom — it names the whole of it.
kernel: fs/pipe.c:anon_pipe_read; net/ipv4/tcp.c:tcp_recvmsg_locked; mm/shmem.c:shmem_file_read_iter; drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem read_witness_names_a_delivery :
    read_witness_row (read_in 0 4096 100 (wmem_first 5)) (stdin_model hello_stdin)
      = Ok (mkEffect 1 [(4096, [104])] [])
          (stdin_model (ICons 101 (ICons 108 (ICons 108 (ICons 111 IEof))))) [ReadEv 0 104]
    ∧ read_witness_row (read_in 25 4096 4 (wmem_first 5)) (socket_model (NCons 5 NRst))
      = Ok (mkEffect 1 [(4096, [5])] [])
          (with_fds (fd_insert (socket_fds (NCons 5 NRst)) 25
              (.FdSocket (.SkConnected peer_a 7 NRst)))
            (socket_model (NCons 5 NRst)))
          [ReadEv 7 5]
    ∧ read_witness_row (read_in 3 4096 100 (wmem_first 16)) read_model
      = Ok (mkEffect 2 [(4096, [104, 105])] [])
          (with_fds (fd_insert read_fds 3 (.FdFile [102] 2)) read_model) []
    ∧ read_witness_row (read_in 14 4096 16 (wmem_first 16)) read_model
      = Ok (mkEffect 2 [(4096, [97, 98])] [])
          (with_pipes [(0, ([], 2)), (1, ([], 0)), (2, ([], 3))] read_model) []
    ∧ read_witness_row (read_in 24 4096 2 (wmem_first 2)) (urandom_model (ICons 1 (ICons 2 IEof)))
      = Ok (mkEffect 2 [(4096, [1, 2])] []) (urandom_model IEof) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> witness_norm

/-- Where the spec declines, the witness is `Unmodeled`: a path the file
system does not hold, an empty pipe with a live writer, a pipe id the
table does not hold, a partially writable destination on a file, on
standard input and on a pipe, a random stream shorter than the count, and
a socket count past `rw_bytes_max` out of range.
kernel: fs/read_write.c:vfs_read; fs/pipe.c:anon_pipe_read; drivers/char/random.c:get_random_bytes_user@v6.18.46 -/
theorem read_witness_is_unmodeled_where_the_spec_declines :
    read_witness_row (read_in 7 4096 16 (wmem_first 16)) read_model = Unmodeled
    ∧ read_witness_row (read_in 16 4096 16 (wmem_first 16)) read_model = Unmodeled
    ∧ read_witness_row (read_in 19 4096 16 (wmem_first 16)) read_model = Unmodeled
    ∧ read_witness_row (read_in 3 4096 100 (wmem_first 1)) read_model = Unmodeled
    ∧ read_witness_row (read_in 0 4096 100 (wmem_first 4)) (stdin_model hello_stdin) = Unmodeled
    ∧ read_witness_row (read_in 14 4096 16 (wmem_first 1)) read_model = Unmodeled
    ∧ read_witness_row (read_in 24 4096 3 (wmem_first 3)) (urandom_model (ICons 1 (ICons 2 IEof)))
      = Unmodeled
    ∧ read_witness_row (read_in 10 (Z_to_bv 64 (2 ^ 63)) (Z_to_bv 64 (2 ^ 40)) wmem_none) read_model
      = Unmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> witness_norm

/-- THE CHECKER ACCEPTS WHAT THE WITNESS NAMES, on every call: an `Ok` the
witness names is `CheckOk` with the same post-model and events, and an
`Unmodeled` it names is `CheckUnmodeled` on every effect.  Both are the
witness's `_ok` lemma read through the checker's completeness, so the two
sides of this file agree by proof and not by inspection.
model: `read_witness_ok` through `check_read_complete_ok` and `check_read_complete_unmodeled` -/
theorem check_read_accepts_the_witness (fd buf count : word) (i : SyscallInput) (m : Model) :
    (∀ (eff : SyscallEffect) (m' : Model) (evs : List event),
        read_witness fd buf count i m = Ok eff m' evs →
        check_read i fd buf count eff m = CheckOk m' evs)
    ∧ (∀ eff : SyscallEffect,
        read_witness fd buf count i m = Unmodeled →
        check_read i fd buf count eff m = CheckUnmodeled) := by
  refine ⟨?_, ?_⟩
  · intro eff m' evs h
    have hw := read_witness_ok fd buf count i m
    rw [h] at hw
    exact check_read_complete_ok i fd buf count eff m m' evs hw
  · intro eff h
    have hw := read_witness_ok fd buf count i m
    rw [h] at hw
    exact check_read_complete_unmodeled i fd buf count eff m hw

/-- …and through the rows, with the same narrowing on both sides.
model: `check_read_accepts_the_witness` under the rows' shared `fd32` narrowing -/
theorem check_read_row_accepts_the_witness_row (i : SyscallInput) (m : Model) :
    (∀ (eff : SyscallEffect) (m' : Model) (evs : List event),
        read_witness_row i m = Ok eff m' evs → check_read_row i eff m = CheckOk m' evs)
    ∧ (∀ eff : SyscallEffect,
        read_witness_row i m = Unmodeled → check_read_row i eff m = CheckUnmodeled) :=
  check_read_accepts_the_witness _ _ _ i m

/-- …and on the fixtures, by evaluation rather than by the lemma: the
one-byte delivery the witness names on standard input is accepted, and so
is the whole file it names on the regular file.
kernel: fs/pipe.c:anon_pipe_read; mm/shmem.c:shmem_file_read_iter@v6.18.46 -/
theorem check_read_accepts_the_witness_delivery :
    check_read_row (read_in 0 4096 100 (wmem_first 5)) (mkEffect 1 [(4096, [104])] [])
        (stdin_model hello_stdin)
      = CheckOk (stdin_model (ICons 101 (ICons 108 (ICons 108 (ICons 111 IEof))))) [ReadEv 0 104]
    ∧ check_read_row (read_in 3 4096 100 (wmem_first 16)) (mkEffect 2 [(4096, [104, 105])] [])
        read_model
      = CheckOk (with_fds (fd_insert read_fds 3 (.FdFile [102] 2)) read_model) [] := by
  refine ⟨?_, ?_⟩ <;> check_norm

end Witness

-- lean-port sentinel: ticket C-Fs-ReadWrite-write appends below this line

/-! ## write (64): what the checker answers and what its witness names

Appended by ticket C-Fs-ReadWrite-write.  Pins over
`Checks.Sys.Fs.ReadWrite.check_write` and `write_witness`, stated as the
read pins above are: the row applies the checker as the dispatcher will,
each pin hands it a concrete `(input, effect)` pair and states the
verdict, and every kernel line below was read at Linux v6.18.46 (commit
1f99e9ab748f).  The fixtures are the spec-level file's write fixtures
(`write_in`, the `mem_*` views, `near_top`/`at_top`/`past_top`,
`write_model`, `wend_model`, `readv_write_only_model`) and the prelude's
`demo_model`, `mem_ab` and `wpast_model`, imported rather than copied.

EVERY CLOSED EQUALITY HERE IS CLOSED BY `rfl`.  The read pins need
`check_norm` because two stream takes index by a `positive` built by
well-founded recursion; `check_write` reads no stream — the channel arm
judges bytes read from `in_mem`, the file and pipe arms compute over the
model's own lists — so evaluation reaches a constructor unaided.  What
bounds that is the byte walk: `write_source` walks the readable prefix of
the clamped count and stops at the first unreadable byte, so every
memory view named below keeps its readable bytes few.  This stops being
true the day a pin hands the row a view readable over a large count
(`mem_below_top`, say, beside a count of 2^20 at a low address): the walk
is then the whole clamp.  The file arm has a second walk, `file_write`'s
zero-fill out to the offset, which `modeled_file_gap` lets run to
`rw_bytes_max` bytes; fd 33's hole lies past that bound and declines
before the fill is built, and a pin opening a hole just inside it would
build the whole fill.

THE `model:` LINES HERE are on the claims that are about this tree and
not about Linux: the checker's order where it declines, the inherited
`rw_bytes_max` bound and, beside it on a pipe, the one-page ring of
`State.pipe_write_room`, the narrowing being the row's and not the
checker's, the witness-through-completeness facts, and the recorded
divergences, each named where it is pinned.  `WriteThroughTheTable`
restates some of these pins through the dispatch, and each of its
`model:` lines is that of a pin it restates.  Of the recorded
divergences, two accept an
answer the kernel does not give on the call pinned
(`bugs/write-channel-pipebuf-short-write.md`, a pipe's,
`bugs/write-out-of-range-short-write.md`, any file's), and a third
accepts one only some supported kernels give
(`bugs/write-file-prefault-before-v5-18-answers-a-chunk.md`: the file
arm's readable prefix is v5.18's, where v4.17 through v5.17 answer
-EFAULT).  Three refuse an answer a supported implementation gives
(`bugs/read-write-reject-an-interrupted-transfer.md`,
`bugs/write-file-never-falls-short.md`, and
`bugs/read-write-transfer-answers-are-linux-order-not-qemu-user.md`,
qemu-user's -EFAULT where Linux never reads the buffer).  Two do both.
`bugs/write-channel-partial-source-efault-refused.md` accepts a short
write a pipe does not give and refuses its -EFAULT.
`bugs/write-channel-assumes-its-reader-is-alive.md` accepts a delivery
where the reader may be gone, which is the defect that entry records,
and refuses the -EPIPE a program that has blocked SIGPIPE sees: a
blocked signal is never ignored (`sig_ignored`, kernel/signal.c:106-125,
Linux v6.18.46), so `anon_pipe_write`'s -EPIPE (fs/pipe.c:460-465)
returns to the program.  Two more are premises the verdicts rest on
rather than answers: `bugs/channel-fds-assume-unidirectional-stdio.md`
makes standard input read-only, and
`bugs/openat-devnull-assumed-null-device.md` stands behind the /dev/null
descriptors.  A pin on one of them states what the checker answers
today, so a change that closes the divergence fails here and has to say
so; it is not a claim that Linux answers the same.  No pin carries a
`probe:` line, for the polarity reason the file header gives.

WHICH ROCQ EXAMPLE EACH THEOREM RESTATES.  Prose, read by no guard, for
the reason the header's mapping for read is.  Rocq states its write
examples through `check_syscall`, so each fixes the spec's answer and the
checker's verdict at once; the verdict half is restated here, on the row.
A Rocq conjunction whose halves rest on different evidence is split in
two, since a docstring carries one evidence line: the accepting half is a
kernel reading and the refusing half a recorded divergence.

- `write_ab_events`: `check_write_ab_events`
- `write_ab_short_delivery`: `check_write_ab_short_delivery`
- `write_a_then_b_events`: `check_write_a_then_b_events`
- `write_fd_truncates_to_32_bits`: `check_write_fd_truncates_to_32_bits`
- `write_fd_high_bits_ebadf_rejected`: `check_write_fd_high_bits_ebadf_rejected`
- `bit31_is_part_of_the_32_bit_arguments`, its `write` conjunct:
  `check_write_bit31_fd_is_ebadf`
- `write_count_bound_declines_on_every_file_kind`, its three `FdFileW`
  conjuncts: `check_write_count_bound_declines_on_the_write_only_kind`
  (the first two) and `check_write_over_the_bound_at_a_mapped_buffer_is_judged`
  (the third), on `write_model`'s fd 4 in place of Rocq's one-descriptor
  model, and each naming the verdict where Rocq says only that it is not
  a decline
- `write_range_boundary_pins_the_three_file_kinds`, its `FdFileW`
  conjunct: `check_write_range_boundary_pins_the_write_only_kind`
- `create_write_updates_fs`, its `write` half:
  `check_create_write_updates_fs_write_half`, on `write_model`'s "j"
  through fd 4 as the spec-level twin states it; the `openat` half needs
  the `openat` checker, which is not this ticket's
- `write_zero_len_past_eof_leaves_file_alone`:
  `check_write_zero_len_past_eof_leaves_file_alone`
- `write_zero_len_rejects_zero_length_copyin`:
  `check_write_zero_len_rejects_zero_length_copyin`
- `write_one_byte_past_eof_zero_fills`: `check_write_one_byte_past_eof_zero_fills`
- `write_zero_len_within_file_is_a_noop`: `check_write_zero_len_within_file_is_a_noop`
- `write_channel_eintr_rejected`: `check_write_ab_events` (the first
  conjunct) and `check_write_channel_eintr_rejected` (the second)
- `write_channel_epipe_rejected`: `check_write_ab_short_delivery`'s first
  conjunct and `check_write_channel_epipe_rejected`
- `file_write_short_rejected`: `check_file_write_fills_an_empty_file` (the
  first conjunct) and `check_file_write_short_rejected` (the second)
- `non_append_write_at_the_same_offset_differs`:
  `check_write_one_byte_past_eof_zero_fills`, which makes the same call on
  the same model and names the whole post-model where Rocq names the file
  and the offset
- `writev_two_iovecs_equals_one_write`: its `write` side is the call
  `check_write_ab_events` pins, and the section `Vectored` pins the two
  together as `check_writev_two_iovecs_equals_one_write`

Rocq's `rdwr_*` and `append_*` examples and the `FdFileA`/`FdFileRW`
conjuncts are not restated, for the reason the header gives for read's.
The groups after the Rocq examples are this section's own. -/

/-! ## The dispatcher's application of the write checker -/

/-- `check_write` as the dispatcher applies it: the descriptor narrowed to
its low 32 bits by `fd32` from a0, `buf` whole from a1, `count` whole from
a2 — Rocq's `arm_write` (`theories/LinuxProcessSem/Checks/Sys/Dispatch.v`)
and the row for 64 in `Sys/SyscallTable.lean`. -/
def check_write_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_write i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m

/-- `write_witness` applied the same way. -/
def write_witness_row (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  write_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

/-- The write row IS the registry arm's application.  `check_write_sound_ok`
lands in `write_arm`'s `sa_spec` only if the row narrows each argument as
`Sys/Registry/Fs/ReadWrite.lean` does — a0 through `fd32`, a1 and a2
whole — so a row that handed a0 over whole, or narrowed a1 too, fails
here at `h` with a type mismatch.  The narrowing is the kernel's own:
`SYSCALL_DEFINE3(write, unsigned int, fd, const char __user *, buf, size_t, count)`
(fs/read_write.c:746-750, Linux v6.18.46) takes the descriptor as an
`unsigned int` and the other two whole, and hands all three to
`ksys_write` (fs/read_write.c:727, Linux v6.18.46).
kernel: fs/read_write.c:write,ksys_write@v6.18.46 -/
theorem the_write_row_is_the_arm (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_write_row i eff m = CheckOk m' evs) :
    (Sys.Registry.Fs.ReadWrite.write_arm).sa_spec i m (Ok eff m' evs) :=
  check_write_sound_ok _ _ _ _ _ _ _ _ h

section WriteRocqExamples

/-! ## Rocq's write examples, on the checker

On Rocq's fixtures where this tree has them (`demo_model` is Rocq's
`init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)`, `mem_ab`,
`wpast_model` and `readv_write_only_model` its namesakes), and on the
spec-level file's `write_model` where Rocq builds a one-descriptor model
this tree spells differently. -/

/-- "ab" TO STANDARD OUTPUT, WHOLE: two bytes, one `WriteEv` each, the
model unchanged — `anon_pipe_write` (fs/pipe.c:431, Linux v6.18.46)
copies a request that fits the ring into it and returns the count.
Rocq's `write_ab_events`.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem check_write_ab_events :
    check_write_row (write_in 1 4096 2 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        demo_model
      = CheckOk demo_model [WriteEv 1 97, WriteEv 1 98] := rfl

/-- A ONE-BYTE DELIVERY OF "ab" IS ACCEPTED, THREE BYTES AND ZERO ARE NOT.
The acceptance is the channel's any-nonempty-prefix rule, which is wider
than a pipe: a blocking pipe write of two bytes copies both or none, so
the one-byte answer is a real answer only of the other kinds a channel
may be (`bugs/write-channel-pipebuf-short-write.md` records the cost).
The two refusals are the rule's bounds, a delivery longer than the
request and a zero delivery of a nonempty one.  Rocq's
`write_ab_short_delivery`.
model: the channel's prefix rule in `check_write`, whose one-byte acceptance is the recorded divergence bugs/write-channel-pipebuf-short-write.md -/
theorem check_write_ab_short_delivery :
    check_write_row (write_in 1 4096 2 mem_ab) (with_copyins [(4096, 1)] (mkEffect 1 [] []))
        demo_model
      = CheckOk demo_model [WriteEv 1 97]
    ∧ check_write_row (write_in 1 4096 2 mem_ab) (with_copyins [(4096, 3)] (mkEffect 3 [] []))
        demo_model
      = CheckReject
    ∧ check_write_row (write_in 1 4096 2 mem_ab) (with_copyins [(4096, 0)] (mkEffect 0 [] []))
        demo_model
      = CheckReject := ⟨rfl, rfl, rfl⟩

/-- ONE BYTE AT A TIME, THE SAME EVENTS: "a" from 4096, then "b" from
4097, each a whole one-byte request `anon_pipe_write` (fs/pipe.c:431,
Linux v6.18.46) copies and returns 1 for.  Rocq's `write_a_then_b_events`.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem check_write_a_then_b_events :
    check_write_row (write_in 1 4096 1 mem_ab) (with_copyins [(4096, 1)] (mkEffect 1 [] []))
        demo_model
      = CheckOk demo_model [WriteEv 1 97]
    ∧ check_write_row (write_in 1 4097 1 mem_ab) (with_copyins [(4097, 1)] (mkEffect 1 [] []))
        demo_model
      = CheckOk demo_model [WriteEv 1 98] := ⟨rfl, rfl⟩

/-- THE DESCRIPTOR IS THE LOW 32 BITS OF a0: `write` takes `unsigned int
fd` (fs/read_write.c:746, Linux v6.18.46), so 2^32 + 1 arrives as 1 and
the call is the same call as on fd 1.  Rocq's
`write_fd_truncates_to_32_bits`.
kernel: fs/read_write.c:write,ksys_write@v6.18.46 -/
theorem check_write_fd_truncates_to_32_bits :
    check_write_row (write_in (Z_to_bv 64 (2 ^ 32 + 1)) 4096 2 mem_ab)
        (with_copyins [(4096, 2)] (mkEffect 2 [] [])) demo_model
      = check_write_row (write_in 1 4096 2 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
          demo_model
    ∧ check_write_row (write_in (Z_to_bv 64 (2 ^ 32 + 1)) 4096 2 mem_ab)
        (with_copyins [(4096, 2)] (mkEffect 2 [] [])) demo_model
      = CheckOk demo_model [WriteEv 1 97, WriteEv 1 98] := ⟨rfl, rfl⟩

/-- …so a kernel refusing it with -EBADF compared the whole register:
`ksys_write` (fs/read_write.c:727-744, Linux v6.18.46) looks up the
narrowed descriptor, which is open.  Rocq's
`write_fd_high_bits_ebadf_rejected`.
kernel: fs/read_write.c:write,ksys_write@v6.18.46 -/
theorem check_write_fd_high_bits_ebadf_rejected :
    check_write_row (write_in (Z_to_bv 64 (2 ^ 32 + 1)) 4096 2 mem_ab)
        (with_copyins [(4096, 2)] (mkEffect (errno_ret EBADF) [] [])) demo_model
      = CheckReject := rfl

/-- BIT 31 IS PART OF THE DESCRIPTOR: 2^31 + 1 arrives as itself, an
`unsigned int` (fs/read_write.c:746, Linux v6.18.46) no slot holds, and
`ksys_write` answers -EBADF (:730).  Rocq's
`bit31_is_part_of_the_32_bit_arguments`, its `write` conjunct.
kernel: fs/read_write.c:write,ksys_write@v6.18.46 -/
theorem check_write_bit31_fd_is_ebadf :
    check_write_row (write_in (Z_to_bv 64 (2 ^ 31 + 1)) 4096 2 mem_ab)
        (mkEffect (errno_ret EBADF) [] []) demo_model
      = CheckOk demo_model [] := rfl

/-- THE NARROWING IS THE ROW'S, NOT THE CHECKER'S: handed the whole word,
`check_write` looks 2^32 + 1 up as it is, finds no such descriptor, and
answers -EBADF.  This is the pin that separates the row from its body: a
checker that narrowed the descriptor itself would take this call to
standard output and fail here.  A registration that skipped `fd32` fails
elsewhere, at `the_write_row_is_the_arm` and
`check_write_fd_truncates_to_32_bits`.  Linux never makes this call, since
the syscall takes its descriptor as an unsigned int (fs/read_write.c:746,
Linux v6.18.46), so the verdict is a claim about the checker alone.
model: `check_write` looks its descriptor argument up unnarrowed and the row's `fd32` does the narrowing; a claim about this tree, not about Linux -/
theorem the_write_checker_itself_reads_the_whole_word :
    check_write (write_in (Z_to_bv 64 (2 ^ 32 + 1)) 4096 2 mem_ab) (Z_to_bv 64 (2 ^ 32 + 1))
        4096 2 (mkEffect (errno_ret EBADF) [] []) demo_model
      = CheckOk demo_model [] := rfl

/-- THE COUNT BOUND ON THE WRITE-ONLY KIND, where the range test cannot
pass the call: at `near_top` a count of `rw_bytes_max + 1` runs past the
limit, so only the count test could pass it, and the arm declines; at
`rw_bytes_max` itself it judges.  The judged answer is the readable
prefix, one byte of "z" landing over "j" with the offset at 1 — the
divergence `bugs/write-out-of-range-short-write.md` records, since the
range is out of `access_ok`'s reach and Linux answers -EFAULT.  Rocq's
`write_count_bound_declines_on_every_file_kind`, its first two `FdFileW`
conjuncts, with the verdict named where Rocq states only that the second
is not a decline.
model: the decline is the inherited `rw_bytes_max` bound of Sys/Uaccess.lean and the at-bound answer the recorded divergence bugs/write-out-of-range-short-write.md -/
theorem check_write_count_bound_declines_on_the_write_only_kind :
    check_write_row (write_in 4 near_top (Z_to_bv 64 (rw_bytes_max + 1)) (mem_z_at near_top))
        (with_copyins [(near_top, 1)] (mkEffect 1 [] [])) write_model
      = CheckUnmodeled
    ∧ check_write_row (write_in 4 near_top (Z_to_bv 64 rw_bytes_max) (mem_z_at near_top))
        (with_copyins [(near_top, 1)] (mkEffect 1 [] [])) write_model
      = CheckOk (with_fds (fd_insert write_fds 4 (.FdFileW [103] 1))
          (with_fs (fs_set write_fs [103] [122]) write_model)) [] := ⟨rfl, rfl⟩

/-- THE SAME OVERSIZED COUNT AT A MAPPED BUFFER IS JUDGED: `rw_bytes_max +
1` bytes from 4096 stay below the limit, `access_ok` passes (`vfs_write`,
fs/read_write.c:674-675, Linux v6.18.46), and the arm judges the readable
prefix, the one byte of "z".  That prefix is the answer
`generic_perform_write` (mm/filemap.c:4244-4335) is written to give from
v5.18 on, returning what was written before a copy faulted (:4331-4334).
v4.17 through v5.17 pre-fault each chunk and answer -EFAULT when any of
it fails, and qemu-user's lock answers -EFAULT as well.  So the one
accepted answer is the choice
`bugs/write-file-prefault-before-v5-18-answers-a-chunk.md` records.
Rocq's `write_count_bound_declines_on_every_file_kind`, its third
`FdFileW` conjunct: the half that says the gate is the disjunction and
not the count alone, with the verdict named where Rocq states only that
it is not a decline.
model: the file arm's readable-prefix answer, the recorded divergence bugs/write-file-prefault-before-v5-18-answers-a-chunk.md -/
theorem check_write_over_the_bound_at_a_mapped_buffer_is_judged :
    check_write_row (write_in 4 4096 (Z_to_bv 64 (rw_bytes_max + 1)) (mem_z_at 4096))
        (with_copyins [(4096, 1)] (mkEffect 1 [] [])) write_model
      = CheckOk (with_fds (fd_insert write_fds 4 (.FdFileW [103] 1))
          (with_fs (fs_set write_fs [103] [122]) write_model)) [] := rfl

/-- EIGHT BYTES AT FOUR BELOW THE LIMIT land as one: the range fails
`access_ok` by four bytes and Linux answers -EFAULT (`vfs_write`,
fs/read_write.c:674-675, Linux v6.18.46), where the write-only arm judges
the readable prefix — the divergence `bugs/write-out-of-range-short-write.md`
records.  Rocq's `write_range_boundary_pins_the_three_file_kinds`, its
`FdFileW` conjunct.
model: the recorded divergence bugs/write-out-of-range-short-write.md, the write-only arm judging an out-of-range source by its readable prefix -/
theorem check_write_range_boundary_pins_the_write_only_kind :
    check_write_row (write_in 4 near_top 8 (mem_z_at near_top))
        (with_copyins [(near_top, 1)] (mkEffect 1 [] [])) write_model
      = CheckOk (with_fds (fd_insert write_fds 4 (.FdFileW [103] 1))
          (with_fs (fs_set write_fs [103] [122]) write_model)) [] := rfl

/-- "ab" INTO "j" AT OFFSET 0 leaves "ab" and the offset at 2:
`generic_perform_write` (mm/filemap.c:4244-4335, Linux v6.18.46) copies
the whole readable source, and `ksys_write` writes the position back
(fs/read_write.c:739-740).  Rocq's `create_write_updates_fs`, its
`write` half.
kernel: mm/filemap.c:generic_perform_write; fs/read_write.c:ksys_write@v6.18.46 -/
theorem check_create_write_updates_fs_write_half :
    check_write_row (write_in 4 4096 2 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        write_model
      = CheckOk (with_fds (fd_insert write_fds 4 (.FdFileW [103] 2))
          (with_fs (fs_set write_fs [103] [97, 98]) write_model)) [] := rfl

/-- ZERO BYTES TWO PAST THE END OF "hi" are 0, the file and the offset
untouched: `generic_write_checks_count` returns before any byte moves on
a zero count (fs/read_write.c:1744-1745, Linux v6.18.46), so no hole is
opened.  Rocq's `write_zero_len_past_eof_leaves_file_alone`.
kernel: fs/read_write.c:generic_write_checks_count@v6.18.46 -/
theorem check_write_zero_len_past_eof_leaves_file_alone :
    check_write_row (write_in 3 4096 0 mem_none) (mkEffect 0 [] []) wpast_model
      = CheckOk wpast_model [] := rfl

/-- …and a zero-length copy-in beside it claims a read that never
happened: nothing reads the source on that path.  Rocq's
`write_zero_len_rejects_zero_length_copyin`.
kernel: fs/read_write.c:generic_write_checks_count@v6.18.46 -/
theorem check_write_zero_len_rejects_zero_length_copyin :
    check_write_row (write_in 3 4096 0 mem_none) (with_copyins [(4096, 0)] (mkEffect 0 [] []))
        wpast_model
      = CheckReject := rfl

/-- ONE BYTE TWO PAST THE END zero-fills the hole: "z" at offset 4 of "hi"
leaves "hi", two zero bytes, "z", and the offset at 5 — the page cache
reads the unwritten range as zeros and `shmem_write_end`
(mm/shmem.c:3346-3368, Linux v6.18.46) moves `i_size` to the end of the
byte `generic_perform_write` copied.  Rocq's
`write_one_byte_past_eof_zero_fills`.
kernel: mm/filemap.c:generic_perform_write; mm/shmem.c:shmem_write_end@v6.18.46 -/
theorem check_write_one_byte_past_eof_zero_fills :
    check_write_row (write_in 3 4096 1 (mem_z_at 4096)) (with_copyins [(4096, 1)] (mkEffect 1 [] []))
        wpast_model
      = CheckOk (with_fds (fd_insert (m_fds wpast_model) 3 (.FdFileW [102] 5))
          (with_fs (fs_set (m_fs wpast_model) [102] [104, 105, 0, 0, 122]) wpast_model)) [] :=
  rfl

/-- ZERO BYTES ONE INTO "hi" are a no-op, for the same early return.
Rocq's `write_zero_len_within_file_is_a_noop`.
kernel: fs/read_write.c:generic_write_checks_count@v6.18.46 -/
theorem check_write_zero_len_within_file_is_a_noop :
    check_write_row (write_in 3 4096 0 mem_none) (mkEffect 0 [] [])
        (with_fds (fd_insert (m_fds wpast_model) 3 (.FdFileW [102] 1)) wpast_model)
      = CheckOk (with_fds (fd_insert (m_fds wpast_model) 3 (.FdFileW [102] 1)) wpast_model) [] :=
  rfl

/-- -EINTR ON A CHANNEL WRITE IS REFUSED, and Linux can give it:
`anon_pipe_write` answers -ERESTARTSYS once the ring is full and a signal
is pending with nothing written (fs/pipe.c:557-560, Linux v6.18.46),
which `arch_do_signal_or_restart` (arch/riscv/kernel/signal.c:396-442)
turns into -EINTR for a handler without `SA_RESTART`.  The model carries
neither the ring's fill nor a pending signal, and refuses the answer:
`bugs/read-write-reject-an-interrupted-transfer.md`.  Rocq's
`write_channel_eintr_rejected`, its second conjunct.
model: the recorded divergence bugs/read-write-reject-an-interrupted-transfer.md, no channel outcome being an interrupted transfer -/
theorem check_write_channel_eintr_rejected :
    check_write_row (write_in 1 4096 2 mem_ab) (mkEffect (errno_ret EINTR) [] []) demo_model
      = CheckReject := rfl

/-- -EPIPE ON A CHANNEL WRITE IS REFUSED, and Linux gives it to a pipe
with no reader, beside SIGPIPE (fs/pipe.c:460-465, Linux v6.18.46).  The
channel arm assumes its reader alive:
`bugs/write-channel-assumes-its-reader-is-alive.md`.  Rocq's
`write_channel_epipe_rejected`, its second conjunct.
model: the recorded divergence bugs/write-channel-assumes-its-reader-is-alive.md -/
theorem check_write_channel_epipe_rejected :
    check_write_row (write_in 1 4096 2 mem_ab) (mkEffect (errno_ret EPIPE) [] []) demo_model
      = CheckReject := rfl

/-- "ab" INTO THE EMPTY FILE through its write-only fd 3: both bytes land
and the offset moves to 2 (`generic_perform_write`, mm/filemap.c:4244-4335;
the position write-back, fs/read_write.c:739-740, Linux v6.18.46).
Rocq's `file_write_short_rejected`, its first conjunct.
kernel: mm/filemap.c:generic_perform_write; fs/read_write.c:ksys_write@v6.18.46 -/
theorem check_file_write_fills_an_empty_file :
    check_write_row (write_in 3 4096 2 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        readv_write_only_model
      = CheckOk (with_fds (fd_insert (m_fds readv_write_only_model) 3 (.FdFileW [102] 2))
          (with_fs (fs_set (m_fs readv_write_only_model) [102] [97, 98]) readv_write_only_model))
          [] := rfl

/-- …and a short count is refused.  No store that fills gives one on
this call: for two bytes into one empty folio, -ENOSPC comes from
`write_begin` with nothing written and is the whole call's answer
(mm/filemap.c:4331-4332, Linux v6.18.46), and `shmem_write_end` returns
every byte copied (mm/shmem.c:3346-3368).  The one route to 1 here is
`generic_write_check_limits` cutting the count to a finite
`RLIMIT_FSIZE` (fs/read_write.c:1709-1732), which the harness refuses at
the exec stop — the premise `Sys/Fs/Open.lean`'s ftruncate note states.
The refusal belongs to the recorded divergence below, whose route is a
store that fills partway through a longer write.  Rocq's
`file_write_short_rejected`, its second conjunct.
model: the recorded divergence bugs/write-file-never-falls-short.md -/
theorem check_file_write_short_rejected :
    check_write_row (write_in 3 4096 2 mem_ab) (with_copyins [(4096, 1)] (mkEffect 1 [] []))
        readv_write_only_model
      = CheckReject := rfl

end WriteRocqExamples

section WriteLedger

/-! ## The write ledger: the copy-in the kernel made, and nothing else

`write` reads the delivered bytes from user memory and writes none:
`vfs_write` (fs/read_write.c:666-696, Linux v6.18.46) touches user memory
only through the write operation's `copy_from_user`-family copies.  A
trace claiming a zero-fill, an unmap, a copy, a user-memory write, or a
copy-in the kernel did not make is refused on the accepting path. -/

/-- On the -EBADF path nothing is read: a zero-fill, an unmap, a copy, a
copy-in and a write entry beside the errno are each refused.
kernel: fs/read_write.c:ksys_write@v6.18.46 -/
theorem write_closed_fd_ebadf_rejects_other_ledgers :
    check_write_row (write_in 30 4096 2 mem_ab) (mkEffect (errno_ret EBADF) [] [(4096, 16)])
        write_model
      = CheckReject
    ∧ check_write_row (write_in 30 4096 2 mem_ab)
        (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [(4096, 16)] [] []) write_model
      = CheckReject
    ∧ check_write_row (write_in 30 4096 2 mem_ab)
        (SyscallEffect.mkEffectU (errno_ret EBADF) [] [] [] [MemCopy.mkCopy 8192 4096 2] [])
        write_model
      = CheckReject
    ∧ check_write_row (write_in 30 4096 2 mem_ab)
        (with_copyins [(4096, 2)] (mkEffect (errno_ret EBADF) [] [])) write_model
      = CheckReject
    ∧ check_write_row (write_in 30 4096 2 mem_ab) (mkEffect (errno_ret EBADF) [(4096, [])] [])
        write_model
      = CheckReject := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- On a channel delivery the ledger is exactly the range the return
names: none, one shifted a byte, one a byte longer, the same two bytes
split in two entries, the right entry with a second copy-in after it,
and a user-memory write, a zero-fill, an unmap or a copy beside the
copy-in are each refused where `check_write_ab_events` accepts.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem channel_write_rejects_other_ledgers :
    check_write_row (write_in 1 4096 2 mem_ab) (mkEffect 2 [] []) demo_model = CheckReject
    ∧ check_write_row (write_in 1 4096 2 mem_ab) (with_copyins [(4097, 2)] (mkEffect 2 [] []))
        demo_model
      = CheckReject
    ∧ check_write_row (write_in 1 4096 2 mem_ab) (with_copyins [(4096, 3)] (mkEffect 2 [] []))
        demo_model
      = CheckReject
    ∧ check_write_row (write_in 1 4096 2 mem_ab)
        (with_copyins [(4096, 1), (4097, 1)] (mkEffect 2 [] [])) demo_model
      = CheckReject
    ∧ check_write_row (write_in 1 4096 2 mem_ab)
        (with_copyins [(4096, 2)] (mkEffect 2 [(4096, [97, 98])] [])) demo_model
      = CheckReject
    ∧ check_write_row (write_in 1 4096 2 mem_ab)
        (with_copyins [(4096, 2)] (mkEffect 2 [] [(8192, 16)])) demo_model
      = CheckReject
    ∧ check_write_row (write_in 1 4096 2 mem_ab)
        (SyscallEffect.mkEffectU 2 [] [] [(8192, 16)] [] [(4096, 2)]) demo_model
      = CheckReject
    ∧ check_write_row (write_in 1 4096 2 mem_ab)
        (SyscallEffect.mkEffectU 2 [] [] [] [MemCopy.mkCopy 8192 4096 2] [(4096, 2)]) demo_model
      = CheckReject
    ∧ check_write_row (write_in 1 4096 2 mem_ab)
        (with_copyins [(4096, 2), (8192, 1)] (mkEffect 2 [] [])) demo_model
      = CheckReject := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- On a file delivery likewise: no copy-in, a copy-in of one byte beside
a return of two, and a user-memory write or a zero-fill beside the
copy-in are each refused where `check_create_write_updates_fs_write_half`
accepts.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem file_write_rejects_other_ledgers :
    check_write_row (write_in 4 4096 2 mem_ab) (mkEffect 2 [] []) write_model = CheckReject
    ∧ check_write_row (write_in 4 4096 2 mem_ab) (with_copyins [(4096, 1)] (mkEffect 2 [] []))
        write_model
      = CheckReject
    ∧ check_write_row (write_in 4 4096 2 mem_ab)
        (with_copyins [(4096, 2)] (mkEffect 2 [(4096, [97, 98])] [])) write_model
      = CheckReject
    ∧ check_write_row (write_in 4 4096 2 mem_ab)
        (with_copyins [(4096, 2)] (mkEffect 2 [] [(8192, 16)])) write_model
      = CheckReject := ⟨rfl, rfl, rfl, rfl⟩

/-- A DECLINED WRITE IS DECLINED WHATEVER THE EFFECT SHAPE: on a
descriptor onto a path the file system does not hold, and on a socket,
the verdict is computed before the effect is looked at, so an odd-shaped
effect there is `CheckUnmodeled`, not `CheckReject`.
model: the path-absent and socket declines precede the effect match in `check_write`, so no effect shape reaches `CheckReject`; a claim about the checker's order, not about Linux -/
theorem a_declined_write_is_declined_whatever_the_effect_shape :
    check_write_row (write_in 27 4096 2 mem_ab)
        (SyscallEffect.mkEffectU 0 [(4096, [1])] [(0, 0)] [] [] []) write_model
      = CheckUnmodeled
    ∧ check_write_row (write_in 27 4096 2 mem_ab) (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckUnmodeled
    ∧ check_write_row (write_in 20 4096 2 mem_ab)
        (SyscallEffect.mkEffectU 0 [(4096, [1])] [(0, 0)] [] [] []) write_model
      = CheckUnmodeled := ⟨rfl, rfl, rfl⟩

end WriteLedger

section WriteDescriptor

/-! ## `ksys_write`, then `vfs_write`'s mode test

`ksys_write` (fs/read_write.c:727-744, Linux v6.18.46) answers -EBADF on
an empty slot (:730) before `vfs_write` (:666-696) tests `FMODE_WRITE`
(:670-671) and answers -EBADF again on a descriptor opened without it.
Both come before `access_ok` (:674-675), so on Linux neither a buffer
past the limit nor a zero count changes either.  qemu-user locks the
buffer before it resolves the descriptor and answers -EFAULT past the
limit; the arms answer in Linux's order, and the refusal that choice
makes is pinned under `model:` in the devices section below. -/

/-- A closed descriptor: -EBADF with the model unchanged is the one
accepted answer, at a mapped buffer and past the limit alike; the full
count and a delivery are refused.
kernel: fs/read_write.c:ksys_write,vfs_write@v6.18.46 -/
theorem write_closed_fd_is_ebadf_on_the_checker :
    check_write_row (write_in 30 4096 2 mem_ab) (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 30 4096 2 mem_ab) (mkEffect 2 [] []) write_model = CheckReject
    ∧ check_write_row (write_in 30 4096 2 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        write_model
      = CheckReject
    ∧ check_write_row (write_in 30 past_top 2 mem_none) (mkEffect (errno_ret EBADF) [] [])
        write_model
      = CheckOk write_model [] := ⟨rfl, rfl, rfl, rfl⟩

/-- …and never declined.
kernel: fs/read_write.c:ksys_write@v6.18.46 -/
theorem write_closed_fd_is_not_declined :
    check_write_row (write_in 30 4096 2 mem_ab) (mkEffect (errno_ret EBADF) [] []) write_model
      ≠ CheckUnmodeled := by
  rw [write_closed_fd_is_ebadf_on_the_checker.1]; exact fun h => nomatch h

/-- EVERY KIND OPEN WITHOUT `FMODE_WRITE` IS -EBADF: a read-only file
(fd 3), a directory (fd 5, which `may_open` never opens for writing,
fs/namei.c:3540-3542, Linux v6.18.46), the random device the model mints
read-only (fd 24), /dev/null open read-only (fd 8), standard input (fd 0)
and its duplicate (fd 26), and a pipe's read end (fd 14) — each from
`vfs_write`'s mode test, ahead of `access_ok`, so -EBADF holds past the
limit too; a delivery through the read-only file is refused.  Standard
input is read-only by assumption: the tracer hands the probe a pipe's
read end, and the model reads the direction off the channel number, the
premise bugs/channel-fds-assume-unidirectional-stdio.md records, since a
terminal on fd 0 is open for writing too.
kernel: fs/read_write.c:vfs_write; fs/namei.c:may_open@v6.18.46 -/
theorem write_non_writable_kinds_are_ebadf_on_the_checker :
    check_write_row (write_in 3 4096 2 mem_ab) (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 5 4096 2 mem_ab) (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 24 4096 2 mem_ab) (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 8 4096 2 mem_ab) (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 0 4096 2 mem_ab) (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 26 4096 2 mem_ab) (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 14 4096 2 mem_ab) (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 0 past_top (Z_to_bv 64 (2 ^ 20)) mem_none)
        (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 14 past_top (Z_to_bv 64 (2 ^ 20)) mem_none)
        (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 3 past_top (Z_to_bv 64 (2 ^ 20)) mem_none)
        (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 5 past_top (Z_to_bv 64 (2 ^ 20)) mem_none)
        (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 24 past_top (Z_to_bv 64 (2 ^ 20)) mem_none)
        (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 8 past_top (Z_to_bv 64 (2 ^ 20)) mem_none)
        (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 3 4096 2 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        write_model
      = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A ZERO COUNT GETS NO FURTHER THAN THE DESCRIPTOR: `ksys_write`'s empty
slot (fs/read_write.c:730, Linux v6.18.46) and `vfs_write`'s mode test
(:670-671) come before anything that looks at the count, so a closed
descriptor (fd 30), a read-only file (fd 3), a directory (fd 5), the
random device (fd 24), /dev/null open read-only (fd 8) and a pipe's read
end (fd 14) answer -EBADF to a zero count, at a mapped buffer and one past
the limit, where `access_ok` would say -EFAULT; 0 is refused on each.
Standard input answers -EBADF too, under the premise the pin above names;
no conjunct refuses 0 there, since a terminal on fd 0 would give it.
kernel: fs/read_write.c:ksys_write,vfs_write@v6.18.46 -/
theorem write_zero_count_is_ebadf_where_the_descriptor_fails :
    check_write_row (write_in 30 4096 0 mem_none) (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 3 4096 0 mem_none) (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 5 4096 0 mem_none) (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 24 4096 0 mem_none) (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 8 4096 0 mem_none) (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 14 4096 0 mem_none) (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 0 4096 0 mem_none) (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 30 past_top 0 mem_none) (mkEffect (errno_ret EBADF) [] [])
        write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 3 past_top 0 mem_none) (mkEffect (errno_ret EBADF) [] [])
        write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 5 past_top 0 mem_none) (mkEffect (errno_ret EBADF) [] [])
        write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 24 past_top 0 mem_none) (mkEffect (errno_ret EBADF) [] [])
        write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 8 past_top 0 mem_none) (mkEffect (errno_ret EBADF) [] [])
        write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 14 past_top 0 mem_none) (mkEffect (errno_ret EBADF) [] [])
        write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 30 4096 0 mem_none) (mkEffect 0 [] []) write_model = CheckReject
    ∧ check_write_row (write_in 3 4096 0 mem_none) (mkEffect 0 [] []) write_model = CheckReject
    ∧ check_write_row (write_in 5 4096 0 mem_none) (mkEffect 0 [] []) write_model = CheckReject
    ∧ check_write_row (write_in 24 4096 0 mem_none) (mkEffect 0 [] []) write_model = CheckReject
    ∧ check_write_row (write_in 8 4096 0 mem_none) (mkEffect 0 [] []) write_model = CheckReject
    ∧ check_write_row (write_in 14 4096 0 mem_none) (mkEffect 0 [] []) write_model = CheckReject :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- THE OTHER EDGES OF THE 32-BIT DESCRIPTOR: 2^32 - 1 arrives as itself
and 2^64 - 1 as 2^32 - 1, an `unsigned int` (fs/read_write.c:746, Linux
v6.18.46) no slot holds, so `ksys_write` answers -EBADF (:730); and
2^32 + 4 arrives as 4, the write-only file, where "ab" lands.
kernel: fs/read_write.c:write,ksys_write@v6.18.46 -/
theorem write_fd_edges_on_the_checker :
    check_write_row (write_in (Z_to_bv 64 (2 ^ 32 - 1)) 4096 2 mem_ab)
        (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in (Z_to_bv 64 (2 ^ 64 - 1)) 4096 2 mem_ab)
        (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in (Z_to_bv 64 (2 ^ 32 + 4)) 4096 2 mem_ab)
        (with_copyins [(4096, 2)] (mkEffect 2 [] [])) write_model
      = CheckOk (with_fds (fd_insert write_fds 4 (.FdFileW [103] 2))
          (with_fs (fs_set write_fs [103] [97, 98]) write_model)) []
    ∧ check_write_row (write_in (Z_to_bv 64 (2 ^ 32 + 4)) 4096 2 mem_ab)
        (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckReject := ⟨rfl, rfl, rfl, rfl⟩

end WriteDescriptor

section WriteChannel

/-! ## Standard output: the range, the zero count, then the source

After the mode test the channel arm runs the range gate, then the zero
count (`access_ok` alone decides it: `vfs_write`, fs/read_write.c:674-675,
Linux v6.18.46, then `anon_pipe_write`'s null-write return, fs/pipe.c:454-456),
then the source: nothing readable at `buf` is -EFAULT from the copy
(fs/pipe.c:489-492, :522-527), anything readable is judged by the
prefix rule `check_write_ab_short_delivery` pins. -/

/-- The range: a count of 2^20 from `near_top` runs past the limit and
declines rather than answer the -EFAULT itself; a zero count at the limit
is 0; a zero count one past it is `access_ok`'s -EFAULT, and 0 is refused
there.
kernel: fs/read_write.c:vfs_write; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem channel_write_range_verdicts_on_the_checker :
    check_write_row (write_in 1 near_top (Z_to_bv 64 (2 ^ 20)) mem_none)
        (mkEffect (errno_ret EFAULT) [] []) write_model
      = CheckUnmodeled
    ∧ check_write_row (write_in 1 at_top 0 mem_none) (mkEffect 0 [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 1 past_top 0 mem_none) (mkEffect (errno_ret EFAULT) [] [])
        write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 1 past_top 0 mem_none) (mkEffect 0 [] []) write_model
      = CheckReject := ⟨rfl, rfl, rfl, rfl⟩

/-- A zero count at a mapped buffer is 0 with no event and no copy-in;
a copy-in of zero bytes and -EFAULT are refused.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem channel_write_zero_count_on_the_checker :
    check_write_row (write_in 1 4096 0 mem_ab) (mkEffect 0 [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 1 4096 0 mem_ab) (with_copyins [(4096, 0)] (mkEffect 0 [] []))
        write_model
      = CheckReject
    ∧ check_write_row (write_in 1 4096 0 mem_ab) (mkEffect (errno_ret EFAULT) [] []) write_model
      = CheckReject := ⟨rfl, rfl, rfl⟩

/-- Nothing readable is -EFAULT with no event: the first copy faults with
nothing counted (fs/pipe.c:489-492, :522-527, Linux v6.18.46); a delivery
and 0 are refused.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem channel_write_unreadable_source_is_efault_on_the_checker :
    check_write_row (write_in 1 4096 2 mem_none) (mkEffect (errno_ret EFAULT) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 1 4096 2 mem_none) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        write_model
      = CheckReject
    ∧ check_write_row (write_in 1 4096 2 mem_none) (mkEffect 0 [] []) write_model
      = CheckReject := ⟨rfl, rfl, rfl⟩

/-- A SOURCE READABLE IN ITS FIRST BYTE ONLY is judged by its readable
prefix: one byte of "a" is accepted, the two-byte count refused.  On a
pipe Linux answers -EFAULT here, from whichever copy site takes the two
bytes: a short copy merging into the last page (fs/pipe.c:489-492, Linux
v6.18.46) and one onto a fresh page, which is dropped with nothing
counted (:522-527), are both -EFAULT — so the acceptance is the recorded divergence
`bugs/write-channel-partial-source-efault-refused.md`, which refuses that
-EFAULT; the refusal of the two-byte count is the prefix rule's bound.
model: the channel's prefix rule over a partial source, the recorded divergence bugs/write-channel-partial-source-efault-refused.md -/
theorem channel_write_partial_source_on_the_checker :
    check_write_row (write_in 1 4096 2 mem_a) (with_copyins [(4096, 1)] (mkEffect 1 [] []))
        write_model
      = CheckOk write_model [WriteEv 1 97]
    ∧ check_write_row (write_in 1 4096 2 mem_a) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        write_model
      = CheckReject
    ∧ check_write_row (write_in 1 4096 2 mem_a) (mkEffect (errno_ret EFAULT) [] []) write_model
      = CheckReject := ⟨rfl, rfl, rfl⟩

/-- A return of 2^64 - 1 is refused.  And standard error's delivery is its
own: fd 2 names `WriteEv 2` for the bytes standard output's pins name as
`WriteEv 1`, so a checker that put every write on one channel fails
here.  The events are computed, not offered, so this is an acceptance
naming them; `channel_write_events_name_the_channel` separates the
channel from the descriptor number.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem channel_write_rejects_lies_on_the_checker :
    check_write_row (write_in 1 4096 2 mem_ab)
        (with_copyins [(4096, 2)] (mkEffect (Z_to_bv 64 (2 ^ 64 - 1)) [] [])) write_model
      = CheckReject
    ∧ check_write_row (write_in 2 4096 2 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        write_model
      = CheckOk write_model [WriteEv 2 97, WriteEv 2 98] := ⟨rfl, rfl⟩

/-- THE EVENTS NAME THE CHANNEL, NOT THE DESCRIPTOR: a duplicate of
standard output at fd 40 delivers "ab" as `WriteEv 1`.  A duplicate
holds the same open file, and `ksys_write` writes through whatever file
the slot resolves to (fs/read_write.c:727-744, Linux v6.18.46), so the
bytes reach standard output's pipe.  Every other writable channel in the
fixtures sits at the fd of its own number, so this is the one pin where
keying the events by the fd would show.
kernel: fs/read_write.c:ksys_write; fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem channel_write_events_name_the_channel :
    check_write_row (write_in 40 4096 2 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        (with_fds (fd_insert write_fds 40 (.FdChannel 1)) write_model)
      = CheckOk (with_fds (fd_insert write_fds 40 (.FdChannel 1)) write_model)
          [WriteEv 1 97, WriteEv 1 98] := rfl

end WriteChannel

section WriteDevices

/-! ## /dev/null and a socket

`write_null` (drivers/char/mem.c:418-422, Linux v6.18.46) returns the
count without reading the source, after `vfs_write` (fs/read_write.c:666-696)
has applied `access_ok` (:674-675) and the `MAX_RW_COUNT` clamp (:680-681).
A socket write is declined permanently: the spec's docstring gives
`sk_stream_error`'s SIGPIPE as the reason. -/

/-- /dev/null open for writing (fd 9): the count back with no copy-in,
the clamp at `MAX_RW_COUNT` for a count of 2^40 and for one byte over it,
0 for a zero count, and `access_ok`'s -EFAULT for eight bytes from
`near_top`; the unclamped count and a copy-in are refused; and a count
of 2^20 from `near_top` declines at the range gate.
kernel: fs/read_write.c:vfs_write; drivers/char/mem.c:write_null@v6.18.46 -/
theorem write_devnull_verdicts_on_the_checker :
    check_write_row (write_in 9 4096 5 mem_none) (mkEffect 5 [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 9 4096 (Z_to_bv 64 (2 ^ 40)) mem_none)
        (mkEffect (Z_to_bv 64 MAX_RW_COUNT) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 9 4096 (Z_to_bv 64 (MAX_RW_COUNT + 1)) mem_none)
        (mkEffect (Z_to_bv 64 MAX_RW_COUNT) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 9 4096 0 mem_none) (mkEffect 0 [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 9 near_top 8 mem_none) (mkEffect (errno_ret EFAULT) [] [])
        write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 9 4096 (Z_to_bv 64 (2 ^ 40)) mem_none)
        (mkEffect (Z_to_bv 64 (2 ^ 40)) [] []) write_model
      = CheckReject
    ∧ check_write_row (write_in 9 4096 5 mem_none) (with_copyins [(4096, 5)] (mkEffect 5 [] []))
        write_model
      = CheckReject
    ∧ check_write_row (write_in 9 near_top (Z_to_bv 64 (2 ^ 20)) mem_none) (mkEffect 0 [] [])
        write_model
      = CheckUnmodeled := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- -EFAULT IS REFUSED WHERE LINUX NEVER READS THE BUFFER: past the limit
on a closed descriptor, where `ksys_write`'s -EBADF (fs/read_write.c:730,
Linux v6.18.46) comes before `vfs_write`'s `access_ok` (:674-675), and
on /dev/null over a buffer where nothing is readable, which `write_null`
(drivers/char/mem.c:418-422) never reads.  qemu-user locks the whole
buffer before it resolves the descriptor and answers -EFAULT to both, so
each refusal is the choice
`bugs/read-write-transfer-answers-are-linux-order-not-qemu-user.md`
records: the arms answer in Linux's order.
model: the recorded divergence bugs/read-write-transfer-answers-are-linux-order-not-qemu-user.md, the arms answering in Linux's order where qemu-user locks the buffer first -/
theorem write_efault_refusals_follow_linux_order :
    check_write_row (write_in 30 past_top 2 mem_none) (mkEffect (errno_ret EFAULT) [] [])
        write_model
      = CheckReject
    ∧ check_write_row (write_in 9 4096 5 mem_none) (mkEffect (errno_ret EFAULT) [] []) write_model
      = CheckReject := ⟨rfl, rfl⟩

/-- Every socket write declines, the zero count included — `sock_write_iter`
(net/socket.c:1176-1199, Linux v6.18.46) has no early return for it —
and the -EPIPE a reset peer would give, beside the SIGPIPE
`sk_stream_error` raises (net/core/stream.c:190-197), is declined with
the rest rather than accepted or refused.
kernel: net/socket.c:sock_write_iter; net/core/stream.c:sk_stream_error@v6.18.46 -/
theorem write_socket_declines_on_the_checker :
    check_write_row (write_in 20 4096 2 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        write_model
      = CheckUnmodeled
    ∧ check_write_row (write_in 10 4096 0 mem_none) (mkEffect 0 [] []) write_model
      = CheckUnmodeled
    ∧ check_write_row (write_in 21 4096 2 mem_ab) (mkEffect (errno_ret EPIPE) [] []) write_model
      = CheckUnmodeled := ⟨rfl, rfl, rfl⟩

end WriteDevices

section WriteFile

/-! ## A write-only file

`generic_perform_write` (mm/filemap.c:4244-4335, Linux v6.18.46) is
written to copy the readable prefix: a chunk that copies nothing and
faults in no byte sets -EFAULT (:4321-4323), and the call returns it
only when nothing was written (:4331-4332).  v4.17 through v5.17
pre-fault each chunk and answer -EFAULT when any of it fails, which is
the recorded choice
`bugs/write-file-prefault-before-v5-18-answers-a-chunk.md`.  `ksys_write`
writes the position back (fs/read_write.c:739-740, Linux v6.18.46). -/

/-- Half readable: the one byte lands, the ledger names it, the offset
moves by one; the full count is refused — no kernel claims the byte it
could not read.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem file_write_partial_source_on_the_checker :
    check_write_row (write_in 4 4096 2 mem_a) (with_copyins [(4096, 1)] (mkEffect 1 [] []))
        write_model
      = CheckOk (with_fds (fd_insert write_fds 4 (.FdFileW [103] 1))
          (with_fs (fs_set write_fs [103] [97]) write_model)) []
    ∧ check_write_row (write_in 4 4096 2 mem_a) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        write_model
      = CheckReject := ⟨rfl, rfl⟩

/-- Nothing readable at offset 0 of "j": -EFAULT with the file and the
offset untouched; 0 is refused.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem file_write_unreadable_source_is_efault_on_the_checker :
    check_write_row (write_in 4 4096 2 mem_none) (mkEffect (errno_ret EFAULT) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 4 4096 2 mem_none) (mkEffect 0 [] []) write_model
      = CheckReject := ⟨rfl, rfl⟩

/-- Lies on a readable source: three bytes for a two-byte request, and
-EINTR, which `generic_perform_write` raises only for a FATAL signal
(mm/filemap.c:4267-4269, Linux v6.18.46), whose task never returns to its
program.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem file_write_rejects_lies_on_the_checker :
    check_write_row (write_in 4 4096 2 mem_ab) (with_copyins [(4096, 3)] (mkEffect 3 [] []))
        write_model
      = CheckReject
    ∧ check_write_row (write_in 4 4096 2 mem_ab) (mkEffect (errno_ret EINTR) [] []) write_model
      = CheckReject := ⟨rfl, rfl⟩

/-- THE EDGE OF `unreadable_source_past_eof`.  AT the end of "hi" an
unreadable source is -EFAULT with the file untouched: `shmem_write_end`
moves `i_size` only when `pos + copied` passes it (mm/shmem.c:3352-3353,
Linux v6.18.46), and at `copied` 0 from the end it does not.  ONE byte
past the end, and two, it does — the file grows to the offset and the
call still answers -EFAULT on v6.18.46, where v4.17 through v6.13 leave
the file alone — so no post-state is in the intersection and the arm
declines.  The spec twin's docstring carries the argument.
kernel: mm/filemap.c:generic_perform_write; mm/shmem.c:shmem_write_end@v6.18.46 -/
theorem file_write_past_eof_edge_on_the_checker :
    check_write_row (write_in 3 4096 1 mem_none) (mkEffect (errno_ret EFAULT) [] []) wend_model
      = CheckOk wend_model []
    ∧ check_write_row (write_in 4 4096 1 mem_none) (mkEffect (errno_ret EFAULT) [] []) wend_model
      = CheckUnmodeled
    ∧ check_write_row (write_in 3 4096 1 mem_none) (mkEffect (errno_ret EFAULT) [] []) wpast_model
      = CheckUnmodeled := ⟨rfl, rfl, rfl⟩

/-- A path the file system does not hold (fd 27) declines a delivery, and
a zero count in range; the source is read first, so an unreadable one is
-EFAULT (`generic_perform_write`'s, mm/filemap.c:4331, Linux v6.18.46)
and a zero count past the limit `access_ok`'s -EFAULT (`vfs_write`,
fs/read_write.c:674-675).
kernel: mm/filemap.c:generic_perform_write; fs/read_write.c:vfs_write@v6.18.46 -/
theorem file_write_path_absent_on_the_checker :
    check_write_row (write_in 27 4096 2 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        write_model
      = CheckUnmodeled
    ∧ check_write_row (write_in 27 4096 1 mem_none) (mkEffect (errno_ret EFAULT) [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 27 4096 0 mem_none) (mkEffect 0 [] []) write_model
      = CheckUnmodeled
    ∧ check_write_row (write_in 27 past_top 0 mem_none) (mkEffect (errno_ret EFAULT) [] [])
        write_model
      = CheckOk write_model [] := ⟨rfl, rfl, rfl, rfl⟩

/-- A HOLE ONE BYTE OVER `rw_bytes_max` declines: fd 33 sits 131075 bytes
into the two-byte "hi", and the model walks a zero-fill no further than
the bound (`modeled_file_gap`).
model: the inherited `rw_bytes_max` bound on the zero-fill walk, Sys/Uaccess.lean; a decline claims nothing about Linux -/
theorem file_write_gap_over_the_bound_declines_on_the_checker :
    check_write_row (write_in 33 4096 1 (mem_z_at 4096))
        (with_copyins [(4096, 1)] (mkEffect 1 [] [])) write_model
      = CheckUnmodeled := rfl

/-- A zero count at the limit is 0 on a file too, with "j" and the offset
as they were (the post-model re-inserts both, which moves fd 4 to the
head of the table and so is not `write_model` itself), and one past it is
`access_ok`'s -EFAULT, ahead of the file's own checks (`vfs_write`,
fs/read_write.c:674-675, Linux v6.18.46); a zero-length copy-in and 1
are refused at a mapped buffer.  So far past the end that the hole is
over the zero-fill bound (fd 33, 131075 bytes into "hi"), a zero count
is still 0 with "hi" as it was: `generic_write_checks_count` returns
before any byte moves (fs/read_write.c:1744-1745), and the model's gap
bound is not asked, as nothing is written.
kernel: fs/read_write.c:vfs_write,generic_write_checks_count@v6.18.46 -/
theorem file_write_zero_count_on_the_checker :
    check_write_row (write_in 4 at_top 0 mem_none) (mkEffect 0 [] []) write_model
      = CheckOk (with_fds (fd_insert write_fds 4 (.FdFileW [103] 0))
          (with_fs (fs_set write_fs [103] [106]) write_model)) []
    ∧ check_write_row (write_in 33 4096 0 mem_none) (mkEffect 0 [] []) write_model
      = CheckOk (with_fds (fd_insert write_fds 33 (.FdFileW [102] (Z_to_bv 64 131075)))
          (with_fs (fs_set write_fs [102] [104, 105]) write_model)) []
    ∧ check_write_row (write_in 4 past_top 0 mem_none) (mkEffect (errno_ret EFAULT) [] [])
        write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 4 4096 0 mem_none) (with_copyins [(4096, 0)] (mkEffect 0 [] []))
        write_model
      = CheckReject
    ∧ check_write_row (write_in 4 4096 0 mem_none) (mkEffect 1 [] []) write_model
      = CheckReject := ⟨rfl, rfl, rfl, rfl, rfl⟩

end WriteFile

section WritePipes

/-! ## A pipe's write end

`anon_pipe_write` (fs/pipe.c:431-601, Linux v6.18.46) copies the whole
request while the ring has room.  The model's ring is one page, so the
arm answers the whole count when the source is readable and the page has
room — and, into an empty ring, also the -ENOMEM of a fresh page that
fails to allocate before the copy — and declines the rest; the spec's
docstring gives each reason. -/

/-- "cd" after "ab" in pipe 0, into the empty pipe 1, and one byte into
the one byte of room pipe 5 has: appended, the count returned, the mark
carried.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_appends_on_the_checker :
    check_write_row (write_in 15 4096 2 mem_cd) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        write_model
      = CheckOk (with_pipes (pipe_insert write_pipes 0 ([97, 98, 99, 100], 4)) write_model) []
    ∧ check_write_row (write_in 17 4096 2 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        write_model
      = CheckOk (with_pipes (pipe_insert write_pipes 1 ([97, 98], 2)) write_model) []
    ∧ check_write_row (write_in 35 4096 1 (mem_z_at 4096))
        (with_copyins [(4096, 1)] (mkEffect 1 [] [])) write_model
      = CheckOk (with_pipes (pipe_insert write_pipes 5 ([120, 122], 4096)) write_model) [] :=
  ⟨rfl, rfl, rfl⟩

/-- Lies on a pipe with room and a reader: one byte of two, 0, no copy-in,
-EAGAIN (`O_NONBLOCK`'s answer, fs/pipe.c:551-556, Linux v6.18.46, on a
pipe opened without it) and -EPIPE (a reader is open, :460-465) are each
refused.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_rejects_lies_on_the_checker :
    check_write_row (write_in 15 4096 2 mem_cd) (with_copyins [(4096, 1)] (mkEffect 1 [] []))
        write_model
      = CheckReject
    ∧ check_write_row (write_in 15 4096 2 mem_cd) (mkEffect 0 [] []) write_model = CheckReject
    ∧ check_write_row (write_in 15 4096 2 mem_cd) (mkEffect 2 [] []) write_model = CheckReject
    ∧ check_write_row (write_in 15 4096 2 mem_cd) (mkEffect (errno_ret EAGAIN) [] []) write_model
      = CheckReject
    ∧ check_write_row (write_in 15 4096 2 mem_cd) (mkEffect (errno_ret EPIPE) [] []) write_model
      = CheckReject := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Where the one-page ring cannot answer, the arm declines: two bytes
into one byte of room (Linux takes a fresh page, fs/pipe.c:510-530,
Linux v6.18.46), a page and a byte into an empty pipe, a pipe whose read
end is closed (SIGPIPE beside -EPIPE, :460-465), a pipe id the table
does not hold, a source readable in part or not at all, and a count of
2^20 from `near_top`.  The source decline is conservative: under the
room test the write reaches one copy site only, and each answers
-EFAULT with the pipe unchanged (:489-492, :522-527), an answer the
spec's docstring declines to give while it rests on that bound.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_declines_on_the_checker :
    check_write_row (write_in 35 4096 2 mem_cd) (mkEffect 2 [] []) write_model = CheckUnmodeled
    ∧ check_write_row (write_in 17 4096 (Z_to_bv 64 4097) mem_none) (mkEffect 0 [] []) write_model
      = CheckUnmodeled
    ∧ check_write_row (write_in 28 4096 1 (mem_z_at 4096)) (mkEffect 1 [] []) write_model
      = CheckUnmodeled
    ∧ check_write_row (write_in 32 4096 1 (mem_z_at 4096)) (mkEffect 1 [] []) write_model
      = CheckUnmodeled
    ∧ check_write_row (write_in 15 4096 2 mem_a) (mkEffect 1 [] []) write_model = CheckUnmodeled
    ∧ check_write_row (write_in 15 4096 2 mem_none) (mkEffect 0 [] []) write_model
      = CheckUnmodeled
    ∧ check_write_row (write_in 15 near_top (Z_to_bv 64 (2 ^ 20)) mem_none) (mkEffect 0 [] [])
        write_model
      = CheckUnmodeled := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A zero count is the null write's 0, returned before the reader test
(fs/pipe.c:454-456, Linux v6.18.46): on the pipe with no reader too, where
-EPIPE is refused; one past the limit it is `access_ok`'s -EFAULT
(`vfs_write`, fs/read_write.c:674-675).
kernel: fs/pipe.c:anon_pipe_write; fs/read_write.c:vfs_write@v6.18.46 -/
theorem pipe_write_zero_count_on_the_checker :
    check_write_row (write_in 15 4096 0 mem_none) (mkEffect 0 [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 28 4096 0 mem_none) (mkEffect 0 [] []) write_model
      = CheckOk write_model []
    ∧ check_write_row (write_in 28 4096 0 mem_none) (mkEffect (errno_ret EPIPE) [] []) write_model
      = CheckReject
    ∧ check_write_row (write_in 15 past_top 0 mem_none) (mkEffect (errno_ret EFAULT) [] [])
        write_model
      = CheckOk write_model [] := ⟨rfl, rfl, rfl, rfl⟩

/-! ### T169 / #1349: fresh-page allocation and the merge control -/

/-- A failed fresh-page allocation returns before copying or changing state.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_empty_enomem_unchanged :
    check_write_row (write_in 17 4096 2 mem_cd)
      (mkEffect (errno_ret ENOMEM) [] []) write_model = CheckOk write_model [] := rfl

/-- A nonempty pipe merges into its existing page, without allocating.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_nonempty_enomem_rejected :
    check_write_row (write_in 15 4096 2 mem_cd)
      (mkEffect (errno_ret ENOMEM) [] []) write_model = CheckReject := rfl

/-- The copy-in ledger cannot precede the allocation that failed.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_empty_enomem_copyin_rejected :
    check_write_row (write_in 17 4096 2 mem_cd)
      (with_copyins [(4096, 2)] (mkEffect (errno_ret ENOMEM) [] []))
      write_model = CheckReject := rfl

/-- A successful fresh-page allocation delivers all source bytes.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_empty_delivery :
    check_write_row (write_in 17 4096 2 mem_cd)
      (with_copyins [(4096, 2)] (mkEffect 2 [] [])) write_model =
      CheckOk (with_pipes (pipe_insert write_pipes 1 ([99, 100], 2)) write_model) [] := rfl

/-- The merge keeps its previous complete-delivery answer.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem pipe_write_nonempty_delivery :
    check_write_row (write_in 15 4096 2 mem_cd)
      (with_copyins [(4096, 2)] (mkEffect 2 [] [])) write_model =
      CheckOk (with_pipes (pipe_insert write_pipes 0 ([97, 98, 99, 100], 4)) write_model) [] := rfl

/-- Allocation failure after draining leaves the empty queue and its old mark unchanged.
Probe case: `testing/syscall-check/tests/pipe_write_enomem.c#conform --mutate write#2:ret=-ENOMEM,drop-copyins -- drained`.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46
-/
theorem pipe_write_drained_enomem_unchanged :
    check_write_row (write_in 17 4096 2 mem_cd)
      (mkEffect (errno_ret ENOMEM) [] [])
      (with_pipes (pipe_insert write_pipes 1 ([], 3)) write_model) =
      CheckOk (with_pipes (pipe_insert write_pipes 1 ([], 3)) write_model) [] := rfl

/-- Delivery after draining starts the new page's mark at the bytes written.
Probe case: `testing/syscall-check/tests/pipe_write_enomem.c#conform -- drained`.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46
-/
theorem pipe_write_drained_delivery :
    check_write_row (write_in 17 4096 2 mem_cd)
      (with_copyins [(4096, 2)] (mkEffect 2 [] []))
      (with_pipes (pipe_insert write_pipes 1 ([], 3)) write_model) =
      CheckOk (with_pipes
        (pipe_insert (pipe_insert write_pipes 1 ([], 3)) 1 ([99, 100], 2))
        (with_pipes (pipe_insert write_pipes 1 ([], 3)) write_model)) [] := rfl

/-- Allocation failure after draining still precedes any source copy-in.
Probe case: `testing/syscall-check/tests/pipe_write_enomem.c#reject --mutate write#2:ret=-ENOMEM,smuggle-copyin:a1:2 -- drained`.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46
-/
theorem pipe_write_drained_enomem_copyin_rejected :
    check_write_row (write_in 17 4096 2 mem_cd)
      (with_copyins [(4096, 2)] (mkEffect (errno_ret ENOMEM) [] []))
      (with_pipes (pipe_insert write_pipes 1 ([], 3)) write_model) = CheckReject := rfl

end WritePipes

section WriteWitness

/-! ## The write witness: which outcome it names

`write_witness_ok` says the witness is an outcome the spec admits; what
it cannot say is WHICH.  Each pin below names the outcome for one call,
and the last three say the checker accepts whatever the witness names. -/

/-- On the deterministic arms the witness is the kernel's answer: -EBADF
on a closed fd and a read-only file, the count on /dev/null, 0 for a zero
count on a pipe, and -EFAULT for an unreadable source on a file and on
standard output.
kernel: fs/read_write.c:ksys_write,vfs_write; drivers/char/mem.c:write_null; fs/pipe.c:anon_pipe_write; mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem write_witness_names_the_deterministic_answer :
    write_witness_row (write_in 30 4096 2 mem_ab) write_model
      = Ok (mkEffect (errno_ret EBADF) [] []) write_model []
    ∧ write_witness_row (write_in 3 4096 2 mem_ab) write_model
      = Ok (mkEffect (errno_ret EBADF) [] []) write_model []
    ∧ write_witness_row (write_in 9 4096 5 mem_none) write_model
      = Ok (mkEffect 5 [] []) write_model []
    ∧ write_witness_row (write_in 15 4096 0 mem_none) write_model
      = Ok (mkEffect 0 [] []) write_model []
    ∧ write_witness_row (write_in 4 4096 2 mem_none) write_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) write_model []
    ∧ write_witness_row (write_in 1 4096 2 mem_none) write_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) write_model [] := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Where the spec CHOOSES — a channel — the witness names the whole
readable prefix with one event per byte; where the delivery is computed —
a file, a pipe — it names that.
kernel: fs/pipe.c:anon_pipe_write; mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem write_witness_names_a_delivery :
    write_witness_row (write_in 1 4096 2 mem_ab) demo_model
      = Ok (with_copyins [(4096, 2)] (mkEffect 2 [] [])) demo_model [WriteEv 1 97, WriteEv 1 98]
    ∧ write_witness_row (write_in 4 4096 2 mem_ab) write_model
      = Ok (with_copyins [(4096, 2)] (mkEffect 2 [] []))
          (with_fds (fd_insert write_fds 4 (.FdFileW [103] 2))
            (with_fs (fs_set write_fs [103] [97, 98]) write_model)) []
    ∧ write_witness_row (write_in 15 4096 2 mem_cd) write_model
      = Ok (with_copyins [(4096, 2)] (mkEffect 2 [] []))
          (with_pipes (pipe_insert write_pipes 0 ([97, 98, 99, 100], 4)) write_model) [] :=
  ⟨rfl, rfl, rfl⟩

/-- Where the spec declines, the witness is `Unmodeled`: a socket, a path
the file system does not hold, an unreadable source one past the end of
file, a pipe with no reader, a pipe id the table does not hold, and a
pipe source readable in part.
kernel: net/socket.c:sock_write_iter; mm/shmem.c:shmem_write_end; fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem write_witness_is_unmodeled_where_the_spec_declines :
    write_witness_row (write_in 20 4096 2 mem_ab) write_model = Unmodeled
    ∧ write_witness_row (write_in 27 4096 2 mem_ab) write_model = Unmodeled
    ∧ write_witness_row (write_in 4 4096 1 mem_none) wend_model = Unmodeled
    ∧ write_witness_row (write_in 28 4096 1 (mem_z_at 4096)) write_model = Unmodeled
    ∧ write_witness_row (write_in 32 4096 1 (mem_z_at 4096)) write_model = Unmodeled
    ∧ write_witness_row (write_in 15 4096 2 mem_a) write_model = Unmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Where the decline is the model's own bound, the witness is `Unmodeled`
too: a count of 2^20 from `near_top` on standard output, the file and
/dev/null, which only the inherited `rw_bytes_max` bound declines; the
hole one byte over that bound behind fd 33; and two bytes into pipe 5's
one byte of room, which the one-page ring cannot answer.
model: the inherited `rw_bytes_max` bound of Sys/Uaccess.lean and the one-page ring of `State.pipe_write_room`; a decline claims nothing about Linux -/
theorem write_witness_declines_at_the_model_bounds :
    write_witness_row (write_in 1 near_top (Z_to_bv 64 (2 ^ 20)) mem_none) write_model
      = Unmodeled
    ∧ write_witness_row (write_in 4 near_top (Z_to_bv 64 (2 ^ 20)) mem_none) write_model
      = Unmodeled
    ∧ write_witness_row (write_in 9 near_top (Z_to_bv 64 (2 ^ 20)) mem_none) write_model
      = Unmodeled
    ∧ write_witness_row (write_in 33 4096 1 (mem_z_at 4096)) write_model = Unmodeled
    ∧ write_witness_row (write_in 35 4096 2 mem_cd) write_model = Unmodeled :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- EVERY NON-WRITABLE KIND NAMES -EBADF, at a mapped buffer and past the
limit alike: standard input (fd 0, read-only under the premise
bugs/channel-fds-assume-unidirectional-stdio.md records), a directory
(fd 5), the random device (fd 24), /dev/null open read-only (fd 8) and a
pipe's read end (fd 14), from `vfs_write`'s mode test
(fs/read_write.c:670-671, Linux v6.18.46) ahead of `access_ok` (:674-675).
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_witness_names_ebadf_on_every_non_writable_kind :
    write_witness_row (write_in 0 4096 2 mem_ab) write_model
      = Ok (mkEffect (errno_ret EBADF) [] []) write_model []
    ∧ write_witness_row (write_in 5 4096 2 mem_ab) write_model
      = Ok (mkEffect (errno_ret EBADF) [] []) write_model []
    ∧ write_witness_row (write_in 24 4096 2 mem_ab) write_model
      = Ok (mkEffect (errno_ret EBADF) [] []) write_model []
    ∧ write_witness_row (write_in 8 4096 2 mem_ab) write_model
      = Ok (mkEffect (errno_ret EBADF) [] []) write_model []
    ∧ write_witness_row (write_in 14 4096 2 mem_ab) write_model
      = Ok (mkEffect (errno_ret EBADF) [] []) write_model []
    ∧ write_witness_row (write_in 0 past_top (Z_to_bv 64 (2 ^ 20)) mem_none) write_model
      = Ok (mkEffect (errno_ret EBADF) [] []) write_model []
    ∧ write_witness_row (write_in 8 past_top (Z_to_bv 64 (2 ^ 20)) mem_none) write_model
      = Ok (mkEffect (errno_ret EBADF) [] []) write_model []
    ∧ write_witness_row (write_in 14 past_top (Z_to_bv 64 (2 ^ 20)) mem_none) write_model
      = Ok (mkEffect (errno_ret EBADF) [] []) write_model [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A ZERO COUNT names 0 on standard output and on the file at a mapped
buffer, the file's post-model re-inserting "j" and fd 4 as they were;
`access_ok`'s -EFAULT on the file one past the limit (`vfs_write`,
fs/read_write.c:674-675, Linux v6.18.46), ahead of the file's own
checks; and 0 on the pipe with no reader, whose null-write return comes
before the reader test (fs/pipe.c:454-456).
kernel: fs/read_write.c:vfs_write,generic_write_checks_count; fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem write_witness_names_the_zero_count_answer :
    write_witness_row (write_in 1 4096 0 mem_none) write_model
      = Ok (mkEffect 0 [] []) write_model []
    ∧ write_witness_row (write_in 4 4096 0 mem_none) write_model
      = Ok (mkEffect 0 [] []) (with_fds (fd_insert write_fds 4 (.FdFileW [103] 0))
          (with_fs (fs_set write_fs [103] [106]) write_model)) []
    ∧ write_witness_row (write_in 4 past_top 0 mem_none) write_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) write_model []
    ∧ write_witness_row (write_in 28 4096 0 mem_none) write_model
      = Ok (mkEffect 0 [] []) write_model [] := ⟨rfl, rfl, rfl, rfl⟩

/-- AN OUT-OF-RANGE SOURCE ON THE FILE names its readable prefix: eight
bytes from `near_top` with "z" readable there name the one-byte write,
where Linux answers `access_ok`'s -EFAULT.  The witness follows the
divergence `check_write_range_boundary_pins_the_write_only_kind` pins on
the checker, so closing it moves this pin too.
model: the recorded divergence bugs/write-out-of-range-short-write.md, the write-only arm judging an out-of-range source by its readable prefix -/
theorem write_witness_follows_the_out_of_range_divergence :
    write_witness_row (write_in 4 near_top 8 (mem_z_at near_top)) write_model
      = Ok (with_copyins [(near_top, 1)] (mkEffect 1 [] []))
          (with_fds (fd_insert write_fds 4 (.FdFileW [103] 1))
            (with_fs (fs_set write_fs [103] [122]) write_model)) [] := rfl

/-- THE CHECKER ACCEPTS WHAT THE WITNESS NAMES, on every call: an `Ok`
the witness names is `CheckOk` with the same post-model and events, and
an `Unmodeled` it names is `CheckUnmodeled` on every effect.  Both are
the witness's `_ok` lemma read through the checker's completeness.
model: `write_witness_ok` through `check_write_complete_ok` and `check_write_complete_unmodeled` -/
theorem check_write_accepts_the_witness (fd buf count : word) (i : SyscallInput) (m : Model) :
    (∀ (eff : SyscallEffect) (m' : Model) (evs : List event),
        write_witness fd buf count i m = Ok eff m' evs →
        check_write i fd buf count eff m = CheckOk m' evs)
    ∧ (∀ eff : SyscallEffect,
        write_witness fd buf count i m = Unmodeled →
        check_write i fd buf count eff m = CheckUnmodeled) := by
  refine ⟨?_, ?_⟩
  · intro eff m' evs h
    have hw := write_witness_ok fd buf count i m
    rw [h] at hw
    exact check_write_complete_ok i fd buf count eff m m' evs hw
  · intro eff h
    have hw := write_witness_ok fd buf count i m
    rw [h] at hw
    exact check_write_complete_unmodeled i fd buf count eff m hw

/-- …and through the rows, with the same narrowing on both sides.
model: `check_write_accepts_the_witness` under the rows' shared `fd32` narrowing -/
theorem check_write_row_accepts_the_witness_row (i : SyscallInput) (m : Model) :
    (∀ (eff : SyscallEffect) (m' : Model) (evs : List event),
        write_witness_row i m = Ok eff m' evs → check_write_row i eff m = CheckOk m' evs)
    ∧ (∀ eff : SyscallEffect,
        write_witness_row i m = Unmodeled → check_write_row i eff m = CheckUnmodeled) :=
  check_write_accepts_the_witness _ _ _ i m

/-- …and on the fixtures, by evaluation rather than by the lemma: the
whole-prefix delivery the witness names on standard output is accepted,
and so is the file write it names.
kernel: fs/pipe.c:anon_pipe_write; mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem check_write_accepts_the_witness_delivery :
    check_write_row (write_in 1 4096 2 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        demo_model
      = CheckOk demo_model [WriteEv 1 97, WriteEv 1 98]
    ∧ check_write_row (write_in 4 4096 2 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        write_model
      = CheckOk (with_fds (fd_insert write_fds 4 (.FdFileW [103] 2))
          (with_fs (fs_set write_fs [103] [97, 98]) write_model)) [] := ⟨rfl, rfl⟩

end WriteWitness

-- lean-port sentinel: ticket C-Fs-ReadWrite-pread-pwrite-lseek appends below this line

section PositionalAndSeek

/-! ## pread64 (67), pwrite64 (68) and lseek (62): the checkers and their witnesses

Pins over `check_pread64`, `check_pwrite64` and `check_lseek` and over
`pread64_witness`, `pwrite64_witness` and `lseek_witness`, the twins of the
same names in the two Rocq files, ported by ticket
C-Fs-ReadWrite-pread-pwrite-lseek.  The method is the read section's and
the file header's account of it holds here unchanged: a concrete
`(input, effect)` pair on the row the dispatcher will apply, the verdict
stated, and beside it the kernel line the verdict rests on.  Only
`kernel:` and `model:` evidence lines appear, for the polarity reason the
header gives; the probes that run these shapes against the Rocq checker
are `testing/syscall-check/tests/pread_pwrite_spec.c`, `lseek_probe.c` and
`dirfd_spec.c`, named in the spec-level pin of the same call.  The
fixtures are the spec-level file's, imported: `read_model` for pread64 and
lseek on every kind, `urandom_model` for the random device,
`readv_write_only_model` (the empty file held for writing through fd 3)
and `write_model` for pwrite64, and `lseek_model`, which is Rocq's own.
The KERNEL argument for each answer is at the spec-level pin of the same
call in `Checks/Cases/Fs/ReadWrite.lean`, and each docstring here keeps
only the line its own verdict rests on.  Those probes run some of these
shapes, not all: no probe hands the checker a socket through these
three calls.

TWO RECORDED LIMITS ARE PINNED HERE AS THE MODEL ANSWERS THEM, and move
with the model when either is closed.  The order is Linux's: every
`CheckReject` of an -EFAULT where an earlier test answers first (the
position, the descriptor, the kind, the mode) refuses the answer
qemu-user gives, since it locks the whole buffer before the call
(bugs/read-write-transfer-answers-are-linux-order-not-qemu-user.md).
And a channel is a pipe: the -ESPIPE verdicts on fds 0, 1 and 2 rest on
the piped-stdio assumption, which shell redirection onto a regular file
falsifies (bugs/channel-fds-assume-unidirectional-stdio.md, and
`Sys/Fs/ReadWrite.lean`'s docstring beside the three specs).

THE CLOSERS.  `rwp_norm` and `rwp_witness_norm` are `check_norm` and
`witness_norm` over the new rows: one `simp only` pass with `zeta` off,
opening the row, the checker and `check_read_urandom`, which pread64's
random-device arm hands over to, and reading the stream takes back to
the unary ones, then `rfl`.  `zeta` is off for the reason `check_norm`'s
docstring gives, and the condition it names holds here too: every row
that reaches pread64's random-device arm runs on an explicit finite
stream; the rows whose count clamps to `MAX_RW_COUNT` are /dev/null's
(`check_pwrite64_devnull_clamp_and_order`,
`pwrite64_witness_names_every_gate`) and read no stream at all; and the
rows with a count past `MAX_RW_COUNT` on the random device answer at the
range or the position, before any stream is read.  The lseek rows that
land at or past `LLONG_MAX` close by the same pass: `lseek_dest`'s
`d < 2 ^ 63` is decided on a closed sum.

WHICH ROCQ EXAMPLE EACH THEOREM RESTATES.  Prose, read by no guard, for
the reason the file header gives.  Rocq states these examples through
`check_syscall`; the verdict half is restated here, on the row.  It stops
being complete the day a theorem restating a Rocq conjunct is added
without a line.

- `lseek_channel_espipe`: `check_lseek_channel_espipe`
- `lseek_channel_bad_whence_is_einval_not_espipe`:
  `check_lseek_channel_bad_whence_is_einval_not_espipe`
- `lseek_channel_seek_hole_is_espipe`: `check_lseek_channel_seek_hole_is_espipe`
- `lseek_seek_data_on_a_file_is_unmodeled`: `check_lseek_seek_data_on_a_file_is_unmodeled`
- `lseek_whence_high_bits_einval_rejected`: `check_lseek_whence_high_bits_einval_rejected`
- `lseek_bad_fd_beats_a_bad_whence`: `check_lseek_bad_fd_beats_a_bad_whence`
- `bit31_is_part_of_the_32_bit_arguments`, its `lseek` conjunct:
  `check_lseek_bit31_whence_is_einval`
- `lseek_on_a_pipe_end_is_espipe_but_whence_wins`, from
  `Checks/Cases/Fs/Pipe.v`: `check_lseek_on_a_pipe_end_is_espipe_but_whence_wins`,
  on this file's pipe ends 14 and 15 where Rocq's `pipe_model` has 3 and 4
- `pwrite64_negative_pos_rejects_ebadf`: `check_pwrite64_negative_pos_rejects_ebadf`
- `pwrite64_writes_at_the_named_position`: `check_pwrite64_writes_at_the_named_position`,
  which states the whole post-model where Rocq's `match` states the file
  and the descriptor
- `pwrite64_over_rw_bytes_max_is_judged`: `check_pwrite64_over_rw_bytes_max_is_judged`

The rest — the rows' narrowing, the per-arm verdicts, the one decline
beyond Rocq's, the witnesses and the symbolic clamp facts at the end —
have no Rocq conjunct. -/

/-- `check_pread64` as the dispatcher applies it: the descriptor narrowed
by `fd32` from a0, `buf`, `count` and `pos` whole from a1..a3 — the row
for 67 in `Sys/SyscallTable.lean`. -/
def check_pread64_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_pread64 i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m

/-- `check_pwrite64` the same way — the row for 68. -/
def check_pwrite64_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_pwrite64 i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m

/-- `check_lseek` as the dispatcher applies it: the descriptor through
`fd32` from a0, the offset whole from a1, the whence through `whence32`
from a2 — the row for 62. -/
def check_lseek_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_lseek (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) eff m

/-- `pread64_witness` applied the same way. -/
def pread64_witness_row (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  pread64_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m

/-- `pwrite64_witness` applied the same way. -/
def pwrite64_witness_row (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  pwrite64_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m

/-- `lseek_witness` applied the same way. -/
def lseek_witness_row (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  lseek_witness (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) m

/-- `check_norm` over the three rows; the section header says why the pass
is the same. -/
scoped macro "rwp_norm" : tactic =>
  `(tactic| (simp -zeta only [check_pread64_row, check_pwrite64_row, check_lseek_row,
    check_pread64, check_pwrite64, check_lseek, check_read_urandom, stream_take_z_eq,
    net_take_z_eq]; first | done | rfl))

/-- `witness_norm` over the three witness rows. -/
scoped macro "rwp_witness_norm" : tactic =>
  `(tactic| (simp -zeta only [pread64_witness_row, pwrite64_witness_row, lseek_witness_row,
    pread64_witness, pwrite64_witness, lseek_witness, read_urandom_witness, stream_take_z_eq,
    net_take_z_eq]; first | done | rfl))

/-! ### The rows are the registry arms -/

/-- The pread64 row IS `pread64_arm`'s application: `check_pread64_sound_ok`
lands in that arm's `sa_spec` only if the row narrows each argument as
`Sys/Registry/Fs/ReadWrite.lean` does.  `SYSCALL_DEFINE4(pread64, unsigned
int, fd, char __user *, buf, size_t, count, loff_t, pos)`
(fs/read_write.c:768, Linux v6.18.46) takes the descriptor as an
`unsigned int` and the other three whole.
kernel: fs/read_write.c:pread64,ksys_pread64@v6.18.46 -/
theorem pread64_row_is_the_arm (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_pread64_row i eff m = CheckOk m' evs) :
    (Sys.Registry.Fs.ReadWrite.pread64_arm).sa_spec i m (Ok eff m' evs) :=
  check_pread64_sound_ok _ _ _ _ _ _ _ _ _ h

/-- The pwrite64 row IS `pwrite64_arm`'s application, by the same
argument: `SYSCALL_DEFINE4(pwrite64, unsigned int, fd, …)`
(fs/read_write.c:798, Linux v6.18.46).
kernel: fs/read_write.c:pwrite64,ksys_pwrite64@v6.18.46 -/
theorem pwrite64_row_is_the_arm (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_pwrite64_row i eff m = CheckOk m' evs) :
    (Sys.Registry.Fs.ReadWrite.pwrite64_arm).sa_spec i m (Ok eff m' evs) :=
  check_pwrite64_sound_ok _ _ _ _ _ _ _ _ _ h

/-- The lseek row IS `lseek_arm`'s application: `SYSCALL_DEFINE3(lseek,
unsigned int, fd, off_t, offset, unsigned int, whence)`
(fs/read_write.c:410, Linux v6.18.46) narrows the descriptor AND the
whence, so a row that handed a2 over whole fails here at `h`.
kernel: fs/read_write.c:lseek,ksys_lseek@v6.18.46 -/
theorem lseek_row_is_the_arm (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_lseek_row i eff m = CheckOk m' evs) :
    (Sys.Registry.Fs.ReadWrite.lseek_arm).sa_spec i m (Ok eff m' evs) :=
  check_lseek_sound_ok _ _ _ _ _ _ _ i h

/-! ### pread64 on the checker -/

/-- THE NEGATIVE POSITION PRECEDES THE DESCRIPTOR: `ksys_pread64` tests
`pos < 0` (fs/read_write.c:755-756, Linux v6.18.46) above the fetch of the
descriptor (:758), so on the closed fd 30 the answer is -EINVAL, and the
-EBADF a descriptor-first reading gives is refused.
kernel: fs/read_write.c:ksys_pread64@v6.18.46 -/
theorem check_pread64_negative_pos_precedes_the_descriptor :
    check_pread64_row (pread_in 30 4096 16 (Z_to_bv 64 (-1)) wmem_none)
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 30 4096 16 (Z_to_bv 64 (-1)) wmem_none)
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwp_norm

/-- A closed descriptor at a valid position is -EBADF (fs/read_write.c:759-760,
Linux v6.18.46), and nothing else.
kernel: fs/read_write.c:ksys_pread64@v6.18.46 -/
theorem check_pread64_closed_fd_is_ebadf :
    check_pread64_row (pread_in 30 4096 16 0 wmem_none) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 30 4096 16 0 wmem_none) (mkEffect (errno_ret EINVAL) [] [])
        read_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwp_norm

/-- A CHANNEL, BOTH PIPE ENDS AND A SOCKET ARE -ESPIPE: none carries
`FMODE_PREAD` (the channel by the piped-stdio assumption the section
header names), so `ksys_pread64` answers -ESPIPE (fs/read_write.c:762-765,
Linux v6.18.46) before `vfs_read` is reached — which is why the write end
of a pipe, whose `read` is -EBADF, refuses that -EBADF here.
kernel: fs/read_write.c:ksys_pread64; fs/pipe.c:create_pipe_files; net/socket.c:sock_alloc_file@v6.18.46 -/
theorem check_pread64_unseekable_kinds_are_espipe :
    check_pread64_row (pread_in 0 4096 16 0 (wmem_first 16)) (mkEffect (errno_ret ESPIPE) [] [])
        read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 14 4096 16 0 (wmem_first 16)) (mkEffect (errno_ret ESPIPE) [] [])
        read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 15 4096 16 0 (wmem_first 16)) (mkEffect (errno_ret ESPIPE) [] [])
        read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 10 4096 16 0 (wmem_first 16)) (mkEffect (errno_ret ESPIPE) [] [])
        read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 15 4096 16 0 (wmem_first 16)) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rwp_norm

/-- A WRITE-ONLY FILE IS -EBADF, AND THE MODE PRECEDES THE RANGE:
`vfs_read` tests `FMODE_READ` (fs/read_write.c:556-557, Linux v6.18.46)
before its range check (:560-561), so with nothing writable the -EFAULT
is refused, and with the destination past the top as well the answer is
still -EBADF and -EFAULT is refused again.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem check_pread64_write_only_file_is_ebadf :
    check_pread64_row (pread_in 4 4096 16 0 wmem_none) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 4 4096 16 0 wmem_none) (mkEffect (errno_ret EFAULT) [] [])
        read_model
      = CheckReject
    ∧ check_pread64_row (pread_in 4 (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 wmem_none)
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 4 (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rwp_norm

/-- /DEV/NULL: the write-only open is -EBADF; the read-only one answers 0
(`read_null`, drivers/char/mem.c:412-416, Linux v6.18.46) and never 16;
a range past the top is -EFAULT (`vfs_read`'s range check,
fs/read_write.c:560-561, which is `__access_ok` of
include/asm-generic/access_ok.h);
a position whose sum passes `LLONG_MAX` is -EINVAL (`rw_verify_area`,
fs/read_write.c:467-469); and with both wrong the range wins, since
the range check is tested first.
kernel: fs/read_write.c:vfs_read,rw_verify_area; drivers/char/mem.c:read_null; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem check_pread64_devnull_verdicts :
    check_pread64_row (pread_in 9 4096 16 0 wmem_none) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 8 4096 16 0 wmem_none) (mkEffect 0 [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 8 4096 16 0 wmem_none) (mkEffect 16 [] []) read_model
      = CheckReject
    ∧ check_pread64_row (pread_in 8 (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 8 4096 1 (Z_to_bv 64 (2 ^ 63 - 1)) wmem_none)
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 8 (Z_to_bv 64 (2 ^ 47 + 1)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 8 (Z_to_bv 64 (2 ^ 47 + 1)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) wmem_none)
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwp_norm

/-- /DEV/NULL'S MODE PRECEDES THE RANGE: on the write-only open, fd 9,
with a destination past the top, `vfs_read` answers -EBADF from its
`FMODE_READ` test (fs/read_write.c:556-557, Linux v6.18.46) before its
range check (:560-561) can say -EFAULT, so -EFAULT is refused.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem check_pread64_devnull_mode_precedes_the_range :
    check_pread64_row (pread_in 9 (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 wmem_none)
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 9 (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwp_norm

/-- /DEV/URANDOM AT A POSITION IS A READ: `urandom_read_iter`
(drivers/char/random.c:1453, Linux v6.18.46) reads no position, so the
two bytes the declared stream holds are delivered and the stream
advances past them — any other two bytes are refused.
kernel: drivers/char/random.c:urandom_read_iter@v6.18.46 -/
theorem check_pread64_urandom_delivers_and_advances :
    check_pread64_row (pread_in 24 4096 2 7 (wmem_first 2)) (mkEffect 2 [(4096, [1, 2])] [])
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckOk (urandom_model IEof) []
    ∧ check_pread64_row (pread_in 24 4096 2 7 (wmem_first 2)) (mkEffect 2 [(4096, [2, 1])] [])
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwp_norm

/-- /DEV/URANDOM PASSES `vfs_read`'S GATES FIRST: a destination past the
top is -EFAULT (fs/read_write.c:560-561, Linux v6.18.46), and a position
whose sum with the count passes `LLONG_MAX` is -EINVAL from
`rw_verify_area` (fs/read_write.c:467-469), since `unsigned_offsets`
(fs/read_write.c:37-40) is false for a device whose `urandom_fops`
(drivers/char/random.c:1572-1581) sets no `fop_flags`.  `urandom_read_iter`
reads no position, but it is never reached, so the one-byte delivery is
refused, and the declared stream is untouched either way.
kernel: fs/read_write.c:vfs_read,rw_verify_area; drivers/char/random.c:urandom_read_iter@v6.18.46 -/
theorem check_pread64_urandom_range_and_position :
    check_pread64_row (pread_in 24 (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckOk (urandom_model (ICons 1 (ICons 2 IEof))) []
    ∧ check_pread64_row (pread_in 24 4096 1 (Z_to_bv 64 (2 ^ 63 - 1)) (wmem_first 1))
        (mkEffect (errno_ret EINVAL) [] []) (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckOk (urandom_model (ICons 1 (ICons 2 IEof))) []
    ∧ check_pread64_row (pread_in 24 4096 1 (Z_to_bv 64 (2 ^ 63 - 1)) (wmem_first 1))
        (mkEffect 1 [(4096, [1])] []) (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> rwp_norm

/-- A DIRECTORY IS -EISDIR, the range first: tmpfs's
`simple_offset_dir_operations` read through `generic_read_dir`
(fs/libfs.c:224-227, Linux v6.18.46), reached past `vfs_read`'s
range check (fs/read_write.c:560-561), so a range past the top is -EFAULT
there.  -ESPIPE is refused: `do_dentry_open` sets `FMODE_PREAD` on every
open (fs/open.c:961, Linux v6.18.46) and `simple_offset_dir_operations`
has no `.open` to clear it (fs/libfs.c:568-573), so `ksys_pread64` (fs/read_write.c:762-765)
passes the directory on to `vfs_read` rather than answering -ESPIPE.
kernel: fs/read_write.c:ksys_pread64,vfs_read; fs/libfs.c:generic_read_dir; fs/open.c:do_dentry_open@v6.18.46 -/
theorem check_pread64_dir_is_eisdir :
    check_pread64_row (pread_in 5 4096 16 0 (wmem_first 16)) (mkEffect (errno_ret EISDIR) [] [])
        read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 5 4096 16 0 (wmem_first 16)) (mkEffect (errno_ret ESPIPE) [] [])
        read_model
      = CheckReject
    ∧ check_pread64_row (pread_in 5 (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckOk read_model [] := by
  refine ⟨?_, ?_, ?_⟩ <;> rwp_norm

/-- ON A DIRECTORY THE POSITION TEST PRECEDES -EISDIR: `vfs_read`
(fs/read_write.c:563-565, Linux v6.18.46) calls `rw_verify_area` before
the file's own `read`, and position 2^63 - 1 with one byte passes
`LLONG_MAX`, so the answer is -EINVAL (fs/read_write.c:467-469) and
`generic_read_dir`'s -EISDIR (fs/libfs.c:224-227) is refused;
`simple_offset_dir_operations` (fs/libfs.c:568-573) sets no `fop_flags`.
kernel: fs/read_write.c:vfs_read,rw_verify_area; fs/libfs.c:generic_read_dir@v6.18.46 -/
theorem check_pread64_dir_position_past_llong_max :
    check_pread64_row (pread_in 5 4096 1 (Z_to_bv 64 (2 ^ 63 - 1)) (wmem_first 1))
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 5 4096 1 (Z_to_bv 64 (2 ^ 63 - 1)) (wmem_first 1))
        (mkEffect (errno_ret EISDIR) [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwp_norm

/-- A FILE IS READ AT THE POSITION THE CALL NAMES.  `ksys_pread64` hands
`vfs_read` the address of its own `pos` (fs/read_write.c:763, Linux
v6.18.46): "hi" at position 1 is "i", the descriptor's offset 0 is
neither read nor moved, so the model is `read_model` itself; "h" and the
whole file are refused.  fd 6 holds the same file at offset 2, its end,
and position 0 still delivers both bytes, refusing the 0 a read at the
descriptor's offset would give.
kernel: fs/read_write.c:ksys_pread64,vfs_read; mm/shmem.c:shmem_file_read_iter@v6.18.46 -/
theorem check_pread64_file_at_the_named_position :
    check_pread64_row (pread_in 3 4096 100 1 (wmem_first 1)) (mkEffect 1 [(4096, [105])] [])
        read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 3 4096 100 1 (wmem_first 1)) (mkEffect 1 [(4096, [104])] [])
        read_model
      = CheckReject
    ∧ check_pread64_row (pread_in 3 4096 100 1 (wmem_first 2)) (mkEffect 2 [(4096, [104, 105])] [])
        read_model
      = CheckReject
    ∧ check_pread64_row (pread_in 6 4096 100 0 (wmem_first 2)) (mkEffect 2 [(4096, [104, 105])] [])
        read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 6 4096 100 0 (wmem_first 2)) (mkEffect 0 [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rwp_norm

/-- THE DELIVERY IS COMPARED WHOLE: "hi" read from position 1 with room
asked for 100 bytes is one byte, "i", at the buffer's own address,
returned as 1.  `ksys_pread64` (fs/read_write.c:762-763, Linux v6.18.46)
hands `vfs_read` the buffer and its own `pos`; tmpfs reads through
`shmem_file_read_iter` (mm/shmem.c:3388-3389 and :3423), which stops at
`i_size`.  The same byte one address later is refused, as is a return of
the count asked for; at position 2, the end of the file, the answer is 0
with nothing written, so a two-byte delivery there is refused.
kernel: fs/read_write.c:ksys_pread64,vfs_read,new_sync_read; mm/shmem.c:shmem_file_read_iter@v6.18.46 -/
theorem check_pread64_delivery_address_and_return :
    check_pread64_row (pread_in 3 4096 100 1 (wmem_first 1)) (mkEffect 1 [(4096, [105])] [])
        read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 3 4096 100 1 (wmem_first 1)) (mkEffect 1 [(4097, [105])] [])
        read_model
      = CheckReject
    ∧ check_pread64_row (pread_in 3 4096 100 1 (wmem_first 1)) (mkEffect 100 [(4096, [105])] [])
        read_model
      = CheckReject
    ∧ check_pread64_row (pread_in 3 4096 100 2 (wmem_first 2)) (mkEffect 0 [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 3 4096 100 2 (wmem_first 2)) (mkEffect 2 [(4096, [104, 105])] [])
        read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rwp_norm

/-- …at the end of the file it is 0 with nothing delivered; a destination
with no writable byte is -EFAULT, not 0; and a position whose sum passes
`LLONG_MAX` is -EINVAL from `rw_verify_area` (fs/read_write.c:467-469,
Linux v6.18.46).
kernel: fs/read_write.c:vfs_read,rw_verify_area; mm/shmem.c:shmem_file_read_iter@v6.18.46 -/
theorem check_pread64_file_edges :
    check_pread64_row (pread_in 3 4096 100 2 wmem_none) (mkEffect 0 [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 3 4096 100 0 wmem_none) (mkEffect (errno_ret EFAULT) [] [])
        read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 3 4096 100 0 wmem_none) (mkEffect 0 [] []) read_model
      = CheckReject
    ∧ check_pread64_row (pread_in 3 4096 1 (Z_to_bv 64 (2 ^ 63 - 1)) (wmem_first 1))
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckOk read_model [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rwp_norm

/-- ON A FILE THE RANGE PRECEDES THE POSITION: a destination past the top
is -EFAULT (`vfs_read`'s range check, fs/read_write.c:560-561, Linux
v6.18.46) even with a zero count, where a read would otherwise answer 0;
and at position 2^63 - 1 as well the range check still answers first,
ahead of the -EINVAL of `rw_verify_area` (fs/read_write.c:467-469),
which `vfs_read` calls only after it.
kernel: fs/read_write.c:vfs_read,rw_verify_area@v6.18.46 -/
theorem check_pread64_file_range_past_top :
    check_pread64_row (pread_in 3 (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 3 (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 wmem_none)
        (mkEffect 0 [] []) read_model
      = CheckReject
    ∧ check_pread64_row (pread_in 3 (Z_to_bv 64 (2 ^ 47 + 1)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 3 (Z_to_bv 64 (2 ^ 47 + 1)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) wmem_none)
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rwp_norm

/-- WHERE THE SPEC DECLINES, THE CHECKER DOES, whatever the effect: a
destination writable for one byte of the two the file holds (the count
Linux answers is the copy routine's rounded progress), a path the file
system does not hold (no `openat` mints one), and a declared random
stream shorter than the count.
kernel: fs/read_write.c:vfs_read; mm/shmem.c:shmem_file_read_iter; drivers/char/random.c:urandom_read_iter@v6.18.46 -/
theorem check_pread64_declines :
    check_pread64_row (pread_in 3 4096 100 0 (wmem_first 1)) (mkEffect 1 [(4096, [104])] [])
        read_model
      = CheckUnmodeled
    ∧ check_pread64_row (pread_in 7 4096 16 0 (wmem_first 16)) (mkEffect 0 [] []) read_model
      = CheckUnmodeled
    ∧ check_pread64_row (pread_in 24 4096 3 0 (wmem_first 3)) (mkEffect 2 [(4096, [1, 2])] [])
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_⟩ <;> rwp_norm

/-- THE DESCRIPTOR IS THE LOW 32 BITS OF a0: 2^32 + 3 is fd 3 through the
row, while `check_pread64` handed the whole word finds no such descriptor
— so a registration that skipped `fd32` fails here.
kernel: fs/read_write.c:pread64,ksys_pread64@v6.18.46 -/
theorem check_pread64_fd_truncates_to_32_bits :
    check_pread64_row (pread_in (Z_to_bv 64 (2 ^ 32 + 3)) 4096 100 1 (wmem_first 1))
        (mkEffect 1 [(4096, [105])] []) read_model
      = CheckOk read_model []
    ∧ check_pread64 (pread_in (Z_to_bv 64 (2 ^ 32 + 3)) 4096 100 1 (wmem_first 1))
        (Z_to_bv 64 (2 ^ 32 + 3)) 4096 100 1 (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model [] := by
  refine ⟨?_, ?_⟩
  · rwp_norm
  · rfl

/-- THE POSITION IS SIGNED AT ITS TOP BIT TOO: `SYSCALL_DEFINE4(pread64, …,
loff_t, pos)` (fs/read_write.c:768-772, Linux v6.18.46) hands
`ksys_pread64` a signed position, so 2^63 is `LLONG_MIN`, and
`ksys_pread64` (fs/read_write.c:755-756) answers -EINVAL before it fetches
the descriptor: on the closed fd 30 the -EBADF is refused, as it is at -1.
kernel: fs/read_write.c:pread64,ksys_pread64@v6.18.46 -/
theorem check_pread64_position_2_pow_63_is_negative :
    check_pread64_row (pread_in 30 4096 16 (Z_to_bv 64 (2 ^ 63)) wmem_none)
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 30 4096 16 (Z_to_bv 64 (2 ^ 63)) wmem_none)
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwp_norm

/-- ON THE RANDOM DEVICE AND ON A DIRECTORY TOO THE RANGE PRECEDES THE
POSITION: with a destination past the top and a position whose sum with
the count passes `LLONG_MAX`, `vfs_read` (fs/read_write.c:560-563, Linux
v6.18.46) answers its range check's -EFAULT before it calls
`rw_verify_area`, whose -EINVAL (fs/read_write.c:467-469) is refused.
kernel: fs/read_write.c:vfs_read,rw_verify_area@v6.18.46 -/
theorem check_pread64_range_precedes_the_position_on_every_kind :
    check_pread64_row (pread_in 24 (Z_to_bv 64 (2 ^ 47 + 1)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckOk (urandom_model (ICons 1 (ICons 2 IEof))) []
    ∧ check_pread64_row (pread_in 24 (Z_to_bv 64 (2 ^ 47 + 1)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) wmem_none)
        (mkEffect (errno_ret EINVAL) [] []) (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckReject
    ∧ check_pread64_row (pread_in 5 (Z_to_bv 64 (2 ^ 47 + 1)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 5 (Z_to_bv 64 (2 ^ 47 + 1)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) wmem_none)
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rwp_norm

/-- THE RANGE AND THE POSITION ARE JUDGED ON THE COUNT THE CALL NAMED, NOT
THE CLAMPED ONE: `vfs_read` (fs/read_write.c:560-567, Linux v6.18.46)
tests the range and calls `rw_verify_area` on `count` before it clamps
`count` to `MAX_RW_COUNT`.  So 2^48 bytes at 4096 are -EFAULT on
/dev/null, the random device, a directory and a file, though
`MAX_RW_COUNT` bytes there fit below the top — the answer each would give
the clamped count is refused; and 2^32 bytes at position 2^63 - 2^31 are
the -EINVAL of `rw_verify_area` (fs/read_write.c:467-469), though the
clamped count ends below `LLONG_MAX` — /dev/null's 0, the directory's
-EISDIR and the file's 0 past its end are refused.
kernel: fs/read_write.c:vfs_read,rw_verify_area; fs/libfs.c:generic_read_dir; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem check_pread64_gates_read_the_unclamped_count :
    check_pread64_row (pread_in 8 4096 (Z_to_bv 64 (2 ^ 48)) 0 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 8 4096 (Z_to_bv 64 (2 ^ 48)) 0 wmem_none) (mkEffect 0 [] [])
        read_model
      = CheckReject
    ∧ check_pread64_row (pread_in 24 4096 (Z_to_bv 64 (2 ^ 48)) 0 (wmem_first 2))
        (mkEffect (errno_ret EFAULT) [] []) (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckOk (urandom_model (ICons 1 (ICons 2 IEof))) []
    ∧ check_pread64_row (pread_in 5 4096 (Z_to_bv 64 (2 ^ 48)) 0 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 5 4096 (Z_to_bv 64 (2 ^ 48)) 0 wmem_none)
        (mkEffect (errno_ret EISDIR) [] []) read_model
      = CheckReject
    ∧ check_pread64_row (pread_in 3 4096 (Z_to_bv 64 (2 ^ 48)) 0 (wmem_first 2))
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 3 4096 (Z_to_bv 64 (2 ^ 48)) 0 (wmem_first 2))
        (mkEffect 2 [(4096, [104, 105])] []) read_model
      = CheckReject
    ∧ check_pread64_row (pread_in 8 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) wmem_none)
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 8 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) wmem_none)
        (mkEffect 0 [] []) read_model
      = CheckReject
    ∧ check_pread64_row
        (pread_in 24 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) (wmem_first 2))
        (mkEffect (errno_ret EINVAL) [] []) (urandom_model (ICons 1 (ICons 2 IEof)))
      = CheckOk (urandom_model (ICons 1 (ICons 2 IEof))) []
    ∧ check_pread64_row (pread_in 5 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) wmem_none)
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 5 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) wmem_none)
        (mkEffect (errno_ret EISDIR) [] []) read_model
      = CheckReject
    ∧ check_pread64_row
        (pread_in 3 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) (wmem_first 2))
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row
        (pread_in 3 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) (wmem_first 2))
        (mkEffect 0 [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwp_norm


/-- THE DELIVERY IS THE ONE WRITE AND NOTHING ELSE: a pread of "i" from
"hi" at position 1 lands one byte through `shmem_file_read_iter`
(mm/shmem.c:3388-3389 and :3423, Linux v6.18.46), which copies the page
into the destination and does nothing else to user memory, and `vfs_read`
(fs/read_write.c:552-581) adds no transfer of its own.  So the delivered
byte followed by a second write, or beside a zero-filled range, an unmap,
a memory-to-memory copy or a recorded copy-in, is refused: each is an
effect on memory the kernel never has.
kernel: fs/read_write.c:vfs_read; mm/shmem.c:shmem_file_read_iter@v6.18.46 -/
theorem check_pread64_delivery_carries_nothing_else :
    check_pread64_row (pread_in 3 4096 100 1 (wmem_first 2))
        (mkEffect 1 [(4096, [105]), (4097, [0])] []) read_model
      = CheckReject
    ∧ check_pread64_row (pread_in 3 4096 100 1 (wmem_first 2))
        (mkEffect 1 [(4096, [105])] [(4097, 1)]) read_model
      = CheckReject
    ∧ check_pread64_row (pread_in 3 4096 100 1 (wmem_first 2))
        (SyscallEffect.mkEffectU 1 [(4096, [105])] [] [(4097, 1)] [] []) read_model
      = CheckReject
    ∧ check_pread64_row (pread_in 3 4096 100 1 (wmem_first 2))
        (SyscallEffect.mkEffectU 1 [(4096, [105])] [] [] [MemCopy.mkCopy 4096 4097 1] [])
        read_model
      = CheckReject
    ∧ check_pread64_row (pread_in 3 4096 100 1 (wmem_first 2))
        (with_copyins [(4096, 1)] (mkEffect 1 [(4096, [105])] [])) read_model
      = CheckReject
    ∧ check_pread64_row (pread_in 3 4096 100 1 (wmem_first 2)) (mkEffect 1 [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwp_norm

/-- THE KIND PRECEDES THE RANGE: `ksys_pread64` answers -ESPIPE
(fs/read_write.c:762-765, Linux v6.18.46) before it calls `vfs_read`, so
`vfs_read`'s range check (fs/read_write.c:560-561) never runs on an
unseekable descriptor.  With the destination past the top, the channel,
the read end of a pipe and a socket are still -ESPIPE, and the -EFAULT
of a range-first reading is refused on each.
kernel: fs/read_write.c:ksys_pread64,vfs_read@v6.18.46 -/
theorem check_pread64_unseekable_precedes_the_range :
    check_pread64_row (pread_in 0 (Z_to_bv 64 (2 ^ 47 + 1)) 16 0 wmem_none)
        (mkEffect (errno_ret ESPIPE) [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 0 (Z_to_bv 64 (2 ^ 47 + 1)) 16 0 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckReject
    ∧ check_pread64_row (pread_in 14 (Z_to_bv 64 (2 ^ 47 + 1)) 16 0 wmem_none)
        (mkEffect (errno_ret ESPIPE) [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 14 (Z_to_bv 64 (2 ^ 47 + 1)) 16 0 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckReject
    ∧ check_pread64_row (pread_in 10 (Z_to_bv 64 (2 ^ 47 + 1)) 16 0 wmem_none)
        (mkEffect (errno_ret ESPIPE) [] []) read_model
      = CheckOk read_model []
    ∧ check_pread64_row (pread_in 10 (Z_to_bv 64 (2 ^ 47 + 1)) 16 0 wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwp_norm

/-! ### pwrite64 on the checker -/

/-- Rocq's `pwrite64_negative_pos_rejects_ebadf`: fd 5 is closed in
`readv_write_only_model`, and `ksys_pwrite64` tests `pos < 0`
(fs/read_write.c:785-786, Linux v6.18.46) above the descriptor's fetch
(:788), so -EINVAL is the answer and -EBADF is refused.
kernel: fs/read_write.c:ksys_pwrite64@v6.18.46 -/
theorem check_pwrite64_negative_pos_rejects_ebadf :
    check_pwrite64_row (pwrite_in 5 4096 2 (Z_to_bv 64 (-1)) mem_ab)
        (mkEffect (errno_ret EINVAL) [] []) readv_write_only_model
      = CheckOk readv_write_only_model []
    ∧ check_pwrite64_row (pwrite_in 5 4096 2 (Z_to_bv 64 (-1)) mem_ab)
        (mkEffect (errno_ret EBADF) [] []) readv_write_only_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwp_norm

/-- …and at a valid position the closed fd is -EBADF (fs/read_write.c:789-790,
Linux v6.18.46); the two-byte write a descriptor there would take is
refused.
kernel: fs/read_write.c:ksys_pwrite64@v6.18.46 -/
theorem check_pwrite64_closed_fd_is_ebadf :
    check_pwrite64_row (pwrite_in 5 4096 2 0 mem_ab) (mkEffect (errno_ret EBADF) [] [])
        readv_write_only_model
      = CheckOk readv_write_only_model []
    ∧ check_pwrite64_row (pwrite_in 5 4096 2 0 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        readv_write_only_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwp_norm

/-- A CHANNEL, BOTH PIPE ENDS AND A SOCKET ARE -ESPIPE: none carries
`FMODE_PWRITE` (fs/read_write.c:792-795, Linux v6.18.46; the channel by
the piped-stdio assumption the section header names), so the read end
of a pipe, whose `write` is -EBADF, refuses that -EBADF here.
kernel: fs/read_write.c:ksys_pwrite64; fs/pipe.c:create_pipe_files; net/socket.c:sock_alloc_file@v6.18.46 -/
theorem check_pwrite64_unseekable_kinds_are_espipe :
    check_pwrite64_row (pwrite_in 1 4096 2 0 mem_ab) (mkEffect (errno_ret ESPIPE) [] []) write_model
      = CheckOk write_model []
    ∧ check_pwrite64_row (pwrite_in 14 4096 2 0 mem_ab) (mkEffect (errno_ret ESPIPE) [] [])
        write_model
      = CheckOk write_model []
    ∧ check_pwrite64_row (pwrite_in 15 4096 2 0 mem_ab) (mkEffect (errno_ret ESPIPE) [] [])
        write_model
      = CheckOk write_model []
    ∧ check_pwrite64_row (pwrite_in 10 4096 2 0 mem_ab) (mkEffect (errno_ret ESPIPE) [] [])
        write_model
      = CheckOk write_model []
    ∧ check_pwrite64_row (pwrite_in 14 4096 2 0 mem_ab) (mkEffect (errno_ret EBADF) [] [])
        write_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rwp_norm

/-- THE KINDS OPENED WITHOUT WRITE ARE -EBADF: a read-only file, the random
device, a directory and the read-only /dev/null all fail `vfs_write`'s
`FMODE_WRITE` test (fs/read_write.c:670-671, Linux v6.18.46), and a
transfer claimed through the read-only file is refused.  So are the two
bytes the random device's `random_write_iter` would take, since
`urandom_fops` (drivers/char/random.c:1572-1581) has one but the test
precedes it, and the -EISDIR `generic_read_dir` (fs/libfs.c:224-227)
gives a read of the directory.
kernel: fs/read_write.c:vfs_write; drivers/char/random.c:random_write_iter; fs/libfs.c:generic_read_dir@v6.18.46 -/
theorem check_pwrite64_read_only_kinds_are_ebadf :
    check_pwrite64_row (pwrite_in 3 4096 2 0 mem_ab) (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckOk write_model []
    ∧ check_pwrite64_row (pwrite_in 24 4096 2 0 mem_ab) (mkEffect (errno_ret EBADF) [] [])
        write_model
      = CheckOk write_model []
    ∧ check_pwrite64_row (pwrite_in 5 4096 2 0 mem_ab) (mkEffect (errno_ret EBADF) [] [])
        write_model
      = CheckOk write_model []
    ∧ check_pwrite64_row (pwrite_in 8 4096 2 0 mem_ab) (mkEffect (errno_ret EBADF) [] [])
        write_model
      = CheckOk write_model []
    ∧ check_pwrite64_row (pwrite_in 3 4096 2 0 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        write_model
      = CheckReject
    ∧ check_pwrite64_row (pwrite_in 24 4096 2 0 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        write_model
      = CheckReject
    ∧ check_pwrite64_row (pwrite_in 5 4096 2 0 mem_ab) (mkEffect (errno_ret EISDIR) [] [])
        write_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwp_norm

/-- /DEV/NULL SWALLOWS THE COUNT: `write_null` (drivers/char/mem.c:418-422,
Linux v6.18.46) returns `count` and reads no source, so two bytes from an
unreadable buffer are 2, not -EFAULT; a range past the top is -EFAULT
(`vfs_write`'s range check, fs/read_write.c:674-675) and a position whose sum passes
`LLONG_MAX` -EINVAL (`rw_verify_area`, :467-469).
kernel: fs/read_write.c:vfs_write,rw_verify_area; drivers/char/mem.c:write_null; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem check_pwrite64_devnull_verdicts :
    check_pwrite64_row (pwrite_in 9 4096 2 0 mem_none) (mkEffect 2 [] []) write_model
      = CheckOk write_model []
    ∧ check_pwrite64_row (pwrite_in 9 4096 2 0 mem_none) (mkEffect (errno_ret EFAULT) [] [])
        write_model
      = CheckReject
    ∧ check_pwrite64_row (pwrite_in 9 (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 mem_none)
        (mkEffect (errno_ret EFAULT) [] []) write_model
      = CheckOk write_model []
    ∧ check_pwrite64_row (pwrite_in 9 4096 1 (Z_to_bv 64 (2 ^ 63 - 1)) mem_none)
        (mkEffect (errno_ret EINVAL) [] []) write_model
      = CheckOk write_model [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rwp_norm

/-- /DEV/NULL ON THE WRITE SIDE: `vfs_write` (fs/read_write.c:680-681,
Linux v6.18.46) clamps the count to `MAX_RW_COUNT` before `write_null`
(drivers/char/mem.c:418-422) returns it, so 2^40 bytes asked of the
write-only open, fd 9, answer 0x7ffff000 and never 2^40.  The read-only
open, fd 8, is -EBADF from `vfs_write`'s `FMODE_WRITE` test
(fs/read_write.c:670-671) before its range check (:674-675) can say
-EFAULT; and on fd 9 a source past the top is -EFAULT even at position
2^63 - 1, since the range check precedes the -EINVAL of `rw_verify_area`
(fs/read_write.c:467-469).
kernel: fs/read_write.c:vfs_write,rw_verify_area; drivers/char/mem.c:write_null@v6.18.46 -/
theorem check_pwrite64_devnull_clamp_and_order :
    check_pwrite64_row (pwrite_in 9 4096 (Z_to_bv 64 (2 ^ 40)) 0 mem_none)
        (mkEffect (Z_to_bv 64 0x7ffff000) [] []) write_model
      = CheckOk write_model []
    ∧ check_pwrite64_row (pwrite_in 9 4096 (Z_to_bv 64 (2 ^ 40)) 0 mem_none)
        (mkEffect (Z_to_bv 64 (2 ^ 40)) [] []) write_model
      = CheckReject
    ∧ check_pwrite64_row (pwrite_in 8 (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 mem_none)
        (mkEffect (errno_ret EBADF) [] []) write_model
      = CheckOk write_model []
    ∧ check_pwrite64_row (pwrite_in 8 (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 mem_none)
        (mkEffect (errno_ret EFAULT) [] []) write_model
      = CheckReject
    ∧ check_pwrite64_row (pwrite_in 9 (Z_to_bv 64 (2 ^ 47 + 1)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) mem_none)
        (mkEffect (errno_ret EFAULT) [] []) write_model
      = CheckOk write_model []
    ∧ check_pwrite64_row (pwrite_in 9 (Z_to_bv 64 (2 ^ 47 + 1)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) mem_none)
        (mkEffect (errno_ret EINVAL) [] []) write_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwp_norm

/-- Rocq's `pwrite64_writes_at_the_named_position`: "ab" at position 4
into the empty file leaves `[0, 0, 0, 0, 97, 98]` — `generic_perform_write`
(mm/filemap.c:4244, Linux v6.18.46) lands the bytes at the position
`ksys_pwrite64` passes by address (fs/read_write.c:793), the hole before
it reading as zeros — with the two-byte copy-in recorded and fd 3 still
at offset 0; the return a short write of one byte would give is refused.
kernel: fs/read_write.c:ksys_pwrite64,vfs_write; mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem check_pwrite64_writes_at_the_named_position :
    check_pwrite64_row (pwrite_in 3 4096 2 4 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        readv_write_only_model
      = CheckOk (with_fs (fs_set write_only_fs [102] [0, 0, 0, 0, 97, 98]) readv_write_only_model) []
    ∧ check_pwrite64_row (pwrite_in 3 4096 2 4 mem_ab) (with_copyins [(4096, 2)] (mkEffect 1 [] []))
        readv_write_only_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwp_norm

/-- ON A WRITE-ONLY FILE THE RANGE AND THE POSITION ARE `vfs_write`'S: a
source past the top is -EFAULT (fs/read_write.c:674-675, Linux v6.18.46)
even with a zero count, where the write would otherwise answer 0; and a
readable one-byte source at position 2^63 - 1 is -EINVAL from
`rw_verify_area` (fs/read_write.c:467-469), `shmem_file_operations`
(mm/shmem.c:5255-5268) setting no `fop_flags`, so the one-byte write is
refused.
kernel: fs/read_write.c:vfs_write,rw_verify_area@v6.18.46 -/
theorem check_pwrite64_file_range_and_position :
    check_pwrite64_row (pwrite_in 3 (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 mem_none)
        (mkEffect (errno_ret EFAULT) [] []) readv_write_only_model
      = CheckOk readv_write_only_model []
    ∧ check_pwrite64_row (pwrite_in 3 (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 mem_none)
        (mkEffect 0 [] []) readv_write_only_model
      = CheckReject
    ∧ check_pwrite64_row (pwrite_in 3 4096 1 (Z_to_bv 64 (2 ^ 63 - 1)) mem_a)
        (mkEffect (errno_ret EINVAL) [] []) readv_write_only_model
      = CheckOk readv_write_only_model []
    ∧ check_pwrite64_row (pwrite_in 3 4096 1 (Z_to_bv 64 (2 ^ 63 - 1)) mem_a)
        (with_copyins [(4096, 1)] (mkEffect 1 [] [])) readv_write_only_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rwp_norm

/-- THE LEDGER HAS ONE SHAPE PER RUN: the transfer that read two user bytes
without saying so is refused, and a zero count, which reads none, is
refused a zero-length entry — the empty ledger is its only one.
model: the copy-in ledger is this tree's accounting of the user bytes a call read, not a kernel value -/
theorem check_pwrite64_ledger_lies_rejected :
    check_pwrite64_row (pwrite_in 3 4096 2 4 mem_ab) (mkEffect 2 [] []) readv_write_only_model
      = CheckReject
    ∧ check_pwrite64_row (pwrite_in 3 4096 0 4 mem_ab) (with_copyins [(4096, 0)] (mkEffect 0 [] []))
        readv_write_only_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwp_norm

/-- A ZERO COUNT WRITES NOTHING AND OPENS NO HOLE: `generic_write_checks`
(fs/read_write.c:1766-1777, Linux v6.18.46) returns the iterator's count,
0 — `generic_write_checks_count` stops early on it (:1744-1745) — and
tmpfs's `shmem_file_write_iter` leaves on `ret <= 0` (mm/shmem.c:3497-3499)
before `generic_perform_write`, whose `do … while` loop
(mm/filemap.c:4254-4329) would otherwise hand `write_end` a zero-byte
copy at position 4, which `shmem_write_end` (mm/shmem.c:3352-3353)
answers by raising `i_size`.  So at position 4 the empty file stays empty.
kernel: fs/read_write.c:generic_write_checks,generic_write_checks_count; mm/shmem.c:shmem_file_write_iter@v6.18.46 -/
theorem check_pwrite64_zero_count_opens_no_hole :
    check_pwrite64_row (pwrite_in 3 4096 0 4 mem_ab) (mkEffect 0 [] []) readv_write_only_model
      = CheckOk (with_fs (fs_set write_only_fs [102] []) readv_write_only_model) [] := by
  rwp_norm

/-- Rocq's `pwrite64_over_rw_bytes_max_is_judged`: a count one past
`rw_bytes_max` from the two readable bytes is the two-byte write the
readable prefix makes, and the one-byte short write is refused.  The
prefix is the contract of `generic_perform_write`'s loop
(mm/filemap.c:4244-4335, Linux v6.18.46): it keeps what the atomic copy
reports and faults the source in only after a copy of nothing
(:4321-4323).  Not every supported implementation meets it on this
shape — v4.17 through v5.17 pre-fault the whole chunk and answer
-EFAULT, qemu-user locks the whole source and answers -EFAULT, and
riscv64's word copier can report no progress, looping forever —
and bugs/write-file-prefault-before-v5-18-answers-a-chunk.md records
each, with the model's answer beside them.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem check_pwrite64_over_rw_bytes_max_is_judged :
    check_pwrite64_row (pwrite_in 3 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 mem_ab)
        (with_copyins [(4096, 2)] (mkEffect 2 [] [])) readv_write_only_model
      = CheckOk (with_fs (fs_set write_only_fs [102] [97, 98]) readv_write_only_model) []
    ∧ check_pwrite64_row (pwrite_in 3 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 mem_ab)
        (with_copyins [(4096, 1)] (mkEffect 1 [] [])) readv_write_only_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwp_norm

/-- AN UNREADABLE SOURCE AT THE END OF THE FILE IS -EFAULT:
`generic_perform_write` copies nothing and answers -EFAULT
(mm/filemap.c:4322, Linux v6.18.46), and a claimed 0 is refused…
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem check_pwrite64_unreadable_source_at_eof_is_efault :
    check_pwrite64_row (pwrite_in 3 4096 1 0 mem_none) (mkEffect (errno_ret EFAULT) [] [])
        readv_write_only_model
      = CheckOk readv_write_only_model []
    ∧ check_pwrite64_row (pwrite_in 3 4096 1 0 mem_none) (mkEffect 0 [] []) readv_write_only_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwp_norm

/-- …while ONE BYTE PAST the end it is declined, on the -EFAULT effect
Rocq's checker accepts there: the verdict that separates this checker
from Rocq's, mirroring `unreadable_source_past_eof`.  The supported
implementations all answer -EFAULT but do not agree on the file:
`generic_perform_write` (mm/filemap.c:4244-4335, Linux v6.18.46) calls
`write_end` before it faults the source in, and tmpfs's `shmem_write_end`
(mm/shmem.c:3352-3353) has by then raised `i_size` to the position with
nothing copied, while the older kernels and qemu-user refuse before the
file moves.  No post-model is in the intersection;
`unreadable_source_past_eof`'s docstring in `Sys/Fs/ReadWrite.lean`
walks both halves line by line.
kernel: mm/filemap.c:generic_perform_write; mm/shmem.c:shmem_write_end@v6.18.46 -/
theorem check_pwrite64_unreadable_source_past_eof_declines :
    check_pwrite64_row (pwrite_in 3 4096 1 1 mem_none) (mkEffect (errno_ret EFAULT) [] [])
        readv_write_only_model
      = CheckUnmodeled := by
  rwp_norm

/-- WHERE THE SPEC DECLINES, THE CHECKER DOES: a hole one byte over the
bound `modeled_file_gap` walks, and a write-only descriptor on a path the
tables do not hold (fd 27 of `write_model`, which no `openat` mints).
kernel: fs/read_write.c:vfs_write; mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem check_pwrite64_declines :
    check_pwrite64_row (pwrite_in 3 4096 1 (Z_to_bv 64 (rw_bytes_max + 1)) mem_a)
        (with_copyins [(4096, 1)] (mkEffect 1 [] [])) readv_write_only_model
      = CheckUnmodeled
    ∧ check_pwrite64_row (pwrite_in 27 4096 1 0 mem_a) (with_copyins [(4096, 1)] (mkEffect 1 [] []))
        write_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> rwp_norm

/-- THE DESCRIPTOR IS THE LOW 32 BITS OF a0: 2^32 + 3 writes through fd 3,
while `check_pwrite64` handed the whole word finds no such descriptor.
kernel: fs/read_write.c:pwrite64,ksys_pwrite64@v6.18.46 -/
theorem check_pwrite64_fd_truncates_to_32_bits :
    check_pwrite64_row (pwrite_in (Z_to_bv 64 (2 ^ 32 + 3)) 4096 2 4 mem_ab)
        (with_copyins [(4096, 2)] (mkEffect 2 [] [])) readv_write_only_model
      = CheckOk (with_fs (fs_set write_only_fs [102] [0, 0, 0, 0, 97, 98]) readv_write_only_model) []
    ∧ check_pwrite64 (pwrite_in (Z_to_bv 64 (2 ^ 32 + 3)) 4096 2 4 mem_ab)
        (Z_to_bv 64 (2 ^ 32 + 3)) 4096 2 4 (mkEffect (errno_ret EBADF) [] []) readv_write_only_model
      = CheckOk readv_write_only_model [] := by
  refine ⟨?_, ?_⟩
  · rwp_norm
  · rfl

/-- THE POSITION IS SIGNED AT ITS TOP BIT TOO: `SYSCALL_DEFINE4(pwrite64,
…, loff_t, pos)` (fs/read_write.c:798-802, Linux v6.18.46) hands
`ksys_pwrite64` a signed position, so 2^63 is `LLONG_MIN`, and
`ksys_pwrite64` (fs/read_write.c:785-786) answers -EINVAL before it
fetches the descriptor: on the closed fd 5 the -EBADF is refused.
kernel: fs/read_write.c:pwrite64,ksys_pwrite64@v6.18.46 -/
theorem check_pwrite64_position_2_pow_63_is_negative :
    check_pwrite64_row (pwrite_in 5 4096 2 (Z_to_bv 64 (2 ^ 63)) mem_ab)
        (mkEffect (errno_ret EINVAL) [] []) readv_write_only_model
      = CheckOk readv_write_only_model []
    ∧ check_pwrite64_row (pwrite_in 5 4096 2 (Z_to_bv 64 (2 ^ 63)) mem_ab)
        (mkEffect (errno_ret EBADF) [] []) readv_write_only_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwp_norm

/-- ON A WRITE-ONLY FILE THE RANGE PRECEDES THE POSITION: with a source
past the top and a position whose sum with the count passes `LLONG_MAX`,
`vfs_write` (fs/read_write.c:674-677, Linux v6.18.46) answers its range
check's -EFAULT before it calls `rw_verify_area`, whose -EINVAL
(fs/read_write.c:467-469) is refused.
kernel: fs/read_write.c:vfs_write,rw_verify_area@v6.18.46 -/
theorem check_pwrite64_file_range_precedes_the_position :
    check_pwrite64_row (pwrite_in 3 (Z_to_bv 64 (2 ^ 47 + 1)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) mem_none)
        (mkEffect (errno_ret EFAULT) [] []) readv_write_only_model
      = CheckOk readv_write_only_model []
    ∧ check_pwrite64_row (pwrite_in 3 (Z_to_bv 64 (2 ^ 47 + 1)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) mem_none)
        (mkEffect (errno_ret EINVAL) [] []) readv_write_only_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwp_norm

/-- THE PAST-THE-END DECLINE COMES AFTER THE RANGE AND THE POSITION: the
decline stands in for what `generic_perform_write` does with an unreadable
source, and `vfs_write` (fs/read_write.c:674-679, Linux v6.18.46) never
reaches it when its range check or `rw_verify_area` answers first.  So an
unreadable one-byte source one byte past the empty file's end is still the
range check's -EFAULT when the source is past the top, and still the
-EINVAL of `rw_verify_area` (fs/read_write.c:467-469) at position
2^63 - 1; the one-byte write is refused at both.
kernel: fs/read_write.c:vfs_write,rw_verify_area@v6.18.46 -/
theorem check_pwrite64_decline_follows_the_range_and_position :
    check_pwrite64_row (pwrite_in 3 (Z_to_bv 64 (2 ^ 47 + 1)) 1 1 mem_none)
        (mkEffect (errno_ret EFAULT) [] []) readv_write_only_model
      = CheckOk readv_write_only_model []
    ∧ check_pwrite64_row (pwrite_in 3 (Z_to_bv 64 (2 ^ 47 + 1)) 1 1 mem_none)
        (with_copyins [(Z_to_bv 64 (2 ^ 47 + 1), 1)] (mkEffect 1 [] [])) readv_write_only_model
      = CheckReject
    ∧ check_pwrite64_row (pwrite_in 3 4096 1 (Z_to_bv 64 (2 ^ 63 - 1)) mem_none)
        (mkEffect (errno_ret EINVAL) [] []) readv_write_only_model
      = CheckOk readv_write_only_model []
    ∧ check_pwrite64_row (pwrite_in 3 4096 1 (Z_to_bv 64 (2 ^ 63 - 1)) mem_none)
        (with_copyins [(4096, 1)] (mkEffect 1 [] [])) readv_write_only_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rwp_norm

/-- A ZERO COUNT OPENS NO HOLE AT ANY POSITION: `shmem_file_write_iter`
(mm/shmem.c:3497-3499, Linux v6.18.46) leaves before anything is
positioned, so a zero count one byte past the hole bound
`check_pwrite64_declines` declines a one-byte write at is still 0 with
the empty file untouched, and is not declined.
kernel: fs/read_write.c:generic_write_checks; mm/shmem.c:shmem_file_write_iter@v6.18.46 -/
theorem check_pwrite64_zero_count_opens_no_hole_anywhere :
    check_pwrite64_row (pwrite_in 3 4096 0 (Z_to_bv 64 (rw_bytes_max + 1)) mem_none)
        (mkEffect 0 [] []) readv_write_only_model
      = CheckOk (with_fs (fs_set write_only_fs [102] []) readv_write_only_model) []
    ∧ check_pwrite64_row (pwrite_in 3 4096 0 (Z_to_bv 64 (rw_bytes_max + 1)) mem_none)
        (mkEffect 1 [] []) readv_write_only_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwp_norm

/-- THE RANGE AND THE POSITION ARE JUDGED ON THE COUNT THE CALL NAMED, NOT
THE CLAMPED ONE: `vfs_write` (fs/read_write.c:674-681, Linux v6.18.46)
tests the range and calls `rw_verify_area` on `count` before it clamps
`count` to `MAX_RW_COUNT`.  So 2^48 bytes from 4096 are -EFAULT on the
write-only /dev/null and on the write-only file, and the clamped count
/dev/null would swallow and the two-byte write the file would take are
refused; and 2^32 bytes at position 2^63 - 2^31 are the -EINVAL of
`rw_verify_area` (fs/read_write.c:467-469) on both, though the clamped
count ends below `LLONG_MAX`.
kernel: fs/read_write.c:vfs_write,rw_verify_area; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem check_pwrite64_gates_read_the_unclamped_count :
    check_pwrite64_row (pwrite_in 9 4096 (Z_to_bv 64 (2 ^ 48)) 0 mem_none)
        (mkEffect (errno_ret EFAULT) [] []) write_model
      = CheckOk write_model []
    ∧ check_pwrite64_row (pwrite_in 9 4096 (Z_to_bv 64 (2 ^ 48)) 0 mem_none)
        (mkEffect (Z_to_bv 64 0x7ffff000) [] []) write_model
      = CheckReject
    ∧ check_pwrite64_row (pwrite_in 3 4096 (Z_to_bv 64 (2 ^ 48)) 0 mem_ab)
        (mkEffect (errno_ret EFAULT) [] []) readv_write_only_model
      = CheckOk readv_write_only_model []
    ∧ check_pwrite64_row (pwrite_in 3 4096 (Z_to_bv 64 (2 ^ 48)) 0 mem_ab)
        (with_copyins [(4096, 2)] (mkEffect 2 [] [])) readv_write_only_model
      = CheckReject
    ∧ check_pwrite64_row (pwrite_in 9 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) mem_none)
        (mkEffect (errno_ret EINVAL) [] []) write_model
      = CheckOk write_model []
    ∧ check_pwrite64_row (pwrite_in 9 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) mem_none)
        (mkEffect (Z_to_bv 64 0x7ffff000) [] []) write_model
      = CheckReject
    ∧ check_pwrite64_row (pwrite_in 3 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) mem_ab)
        (mkEffect (errno_ret EINVAL) [] []) readv_write_only_model
      = CheckOk readv_write_only_model []
    ∧ check_pwrite64_row (pwrite_in 3 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) mem_ab)
        (with_copyins [(4096, 2)] (mkEffect 2 [] [])) readv_write_only_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwp_norm

/-- THE KIND PRECEDES THE RANGE: `ksys_pwrite64` answers -ESPIPE
(fs/read_write.c:792-795, Linux v6.18.46) before it calls `vfs_write`, so
`vfs_write`'s range check (fs/read_write.c:674-675) never runs on an
unseekable descriptor.  With the source past the top, the channel, the
write end of a pipe and a socket are still -ESPIPE, and the -EFAULT of a
range-first reading is refused on each.
kernel: fs/read_write.c:ksys_pwrite64,vfs_write@v6.18.46 -/
theorem check_pwrite64_unseekable_precedes_the_range :
    check_pwrite64_row (pwrite_in 1 (Z_to_bv 64 (2 ^ 47 + 1)) 2 0 mem_none)
        (mkEffect (errno_ret ESPIPE) [] []) write_model
      = CheckOk write_model []
    ∧ check_pwrite64_row (pwrite_in 1 (Z_to_bv 64 (2 ^ 47 + 1)) 2 0 mem_none)
        (mkEffect (errno_ret EFAULT) [] []) write_model
      = CheckReject
    ∧ check_pwrite64_row (pwrite_in 15 (Z_to_bv 64 (2 ^ 47 + 1)) 2 0 mem_none)
        (mkEffect (errno_ret ESPIPE) [] []) write_model
      = CheckOk write_model []
    ∧ check_pwrite64_row (pwrite_in 15 (Z_to_bv 64 (2 ^ 47 + 1)) 2 0 mem_none)
        (mkEffect (errno_ret EFAULT) [] []) write_model
      = CheckReject
    ∧ check_pwrite64_row (pwrite_in 10 (Z_to_bv 64 (2 ^ 47 + 1)) 2 0 mem_none)
        (mkEffect (errno_ret ESPIPE) [] []) write_model
      = CheckOk write_model []
    ∧ check_pwrite64_row (pwrite_in 10 (Z_to_bv 64 (2 ^ 47 + 1)) 2 0 mem_none)
        (mkEffect (errno_ret EFAULT) [] []) write_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwp_norm

/-! ### lseek on the checker -/

/-- Rocq's `lseek_channel_espipe`: the channel, a pipe by the piped-stdio
assumption the section header names, went through `stream_open`
(fs/open.c:1656-1661, Linux v6.18.46), which clears `FMODE_LSEEK`, and
`vfs_llseek` answers -ESPIPE on that bit (fs/read_write.c:387-388); the 0
a seekable file would report is refused.
kernel: fs/read_write.c:ksys_lseek,vfs_llseek; fs/open.c:stream_open@v6.18.46 -/
theorem check_lseek_channel_espipe :
    check_lseek_row (lseek_in 0 0 0) (mkEffect (errno_ret ESPIPE) [] []) lseek_model
      = CheckOk lseek_model []
    ∧ check_lseek_row (lseek_in 0 0 0) (mkEffect 0 [] []) lseek_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwp_norm

/-- Rocq's `lseek_channel_bad_whence_is_einval_not_espipe`: `ksys_lseek`
tests `whence <= SEEK_MAX` (fs/read_write.c:401, Linux v6.18.46) before
`vfs_llseek` (:402), so whence 42 on a channel is -EINVAL and -ESPIPE is
refused.
kernel: fs/read_write.c:ksys_lseek,vfs_llseek@v6.18.46 -/
theorem check_lseek_channel_bad_whence_is_einval_not_espipe :
    check_lseek_row (lseek_in 0 0 42) (mkEffect (errno_ret EINVAL) [] []) lseek_model
      = CheckOk lseek_model []
    ∧ check_lseek_row (lseek_in 0 0 42) (mkEffect (errno_ret ESPIPE) [] []) lseek_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwp_norm

/-- Rocq's `lseek_channel_seek_hole_is_espipe`: SEEK_HOLE is 4, `SEEK_MAX`
itself, so it passes the gate (fs/read_write.c:401, Linux v6.18.46) and
the channel's kind answers -ESPIPE.
kernel: fs/read_write.c:ksys_lseek,vfs_llseek@v6.18.46 -/
theorem check_lseek_channel_seek_hole_is_espipe :
    check_lseek_row (lseek_in 0 0 4) (mkEffect (errno_ret ESPIPE) [] []) lseek_model
      = CheckOk lseek_model [] := by
  rwp_norm

/-- Rocq's `lseek_seek_data_on_a_file_is_unmodeled`, all four conjuncts:
SEEK_DATA and SEEK_HOLE on the file decline — `shmem_file_llseek`
(mm/shmem.c:3669-3687, Linux v6.18.46) answers them from the filesystem's
own notion of a hole — whatever effect is offered; SEEK_HOLE on the
channel is still -ESPIPE, and SEEK_END on the file still reports the size
and moves the offset, so the pair of declines is a boundary.
kernel: mm/shmem.c:shmem_file_llseek; fs/read_write.c:ksys_lseek,vfs_llseek,generic_file_llseek_size@v6.18.46 -/
theorem check_lseek_seek_data_on_a_file_is_unmodeled :
    check_lseek_row (lseek_in 3 0 3) (mkEffect (errno_ret EINVAL) [] []) lseek_model = CheckUnmodeled
    ∧ check_lseek_row (lseek_in 3 0 4) (mkEffect 2 [] []) lseek_model = CheckUnmodeled
    ∧ check_lseek_row (lseek_in 0 0 4) (mkEffect (errno_ret ESPIPE) [] []) lseek_model
      = CheckOk lseek_model []
    ∧ check_lseek_row (lseek_in 3 0 2) (mkEffect 2 [] []) lseek_model
      = CheckOk (with_fds (fd_insert lseek_fds 3 (.FdFile [102] 2)) lseek_model) [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rwp_norm

/-- Rocq's `lseek_whence_high_bits_einval_rejected`: `SYSCALL_DEFINE3(lseek,
…, unsigned int, whence)` (fs/read_write.c:410, Linux v6.18.46) hands
`ksys_lseek` the low 32 bits, so 2^32 + SEEK_END is a SEEK_END — the size
reported and the offset moved — and -EINVAL is refused.
kernel: fs/read_write.c:lseek,ksys_lseek,generic_file_llseek_size@v6.18.46 -/
theorem check_lseek_whence_high_bits_einval_rejected :
    check_lseek_row (lseek_in 3 0 (Z_to_bv 64 (2 ^ 32 + 2))) (mkEffect 2 [] []) lseek_model
      = CheckOk (with_fds (fd_insert lseek_fds 3 (.FdFile [102] 2)) lseek_model) []
    ∧ check_lseek_row (lseek_in 3 0 (Z_to_bv 64 (2 ^ 32 + 2))) (mkEffect (errno_ret EINVAL) [] [])
        lseek_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwp_norm

/-- THE WHENCE NARROWING IS THE ROW'S, NOT THE CHECKER'S: `check_lseek`
handed the whole word 2^32 + 2 compares it with `SEEK_MAX` as it is and
answers -EINVAL, so the SEEK_END verdict of
`check_lseek_whence_high_bits_einval_rejected` rests on the row's
`whence32`, and a registration that skipped it fails there.
kernel: fs/read_write.c:lseek,ksys_lseek@v6.18.46 -/
theorem the_lseek_checker_itself_reads_the_whole_whence :
    check_lseek 3 0 (Z_to_bv 64 (2 ^ 32 + 2)) (mkEffect (errno_ret EINVAL) [] []) lseek_model
      = CheckOk lseek_model [] := by
  simp -zeta only [check_lseek]; first | done | rfl

/-- Rocq's `lseek_bad_fd_beats_a_bad_whence`: the descriptor is fetched
first (fs/read_write.c:396-398, Linux v6.18.46), so closed fd 9 with
whence 42 is -EBADF and -EINVAL is refused.
kernel: fs/read_write.c:ksys_lseek@v6.18.46 -/
theorem check_lseek_bad_fd_beats_a_bad_whence :
    check_lseek_row (lseek_in 9 0 42) (mkEffect (errno_ret EBADF) [] []) lseek_model
      = CheckOk lseek_model []
    ∧ check_lseek_row (lseek_in 9 0 42) (mkEffect (errno_ret EINVAL) [] []) lseek_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwp_norm

/-- Rocq's `bit31_is_part_of_the_32_bit_arguments`, its `lseek` conjunct:
bit 31 is inside the `unsigned int` whence (fs/read_write.c:410, Linux
v6.18.46), so 2^31 + 2 is past `SEEK_MAX` and -EINVAL.
kernel: fs/read_write.c:lseek,ksys_lseek@v6.18.46 -/
theorem check_lseek_bit31_whence_is_einval :
    check_lseek_row (lseek_in 3 5 (Z_to_bv 64 (2 ^ 31 + 2))) (mkEffect (errno_ret EINVAL) [] [])
        lseek_model
      = CheckOk lseek_model [] := by
  rwp_norm

/-- A FILE SEEKS AND THE DESCRIPTOR MOVES: SEEK_SET to 1 reports 1 with fd
3 rewritten there, and the 0 an unmoved offset reports is refused; SEEK_CUR
by -1 from fd 6's offset 2 is 1; by -3 it lands below 0, which
`vfs_setpos_cookie` refuses with -EINVAL (fs/read_write.c:58-59, Linux
v6.18.46), the offset unmoved — the 0 a clamp to the start would report
is refused.
kernel: fs/read_write.c:generic_file_llseek_size,vfs_setpos_cookie; mm/shmem.c:shmem_file_llseek@v6.18.46 -/
theorem check_lseek_file_seeks :
    check_lseek_row (lseek_in 3 1 0) (mkEffect 1 [] []) lseek_model
      = CheckOk (with_fds (fd_insert lseek_fds 3 (.FdFile [102] 1)) lseek_model) []
    ∧ check_lseek_row (lseek_in 3 1 0) (mkEffect 0 [] []) lseek_model = CheckReject
    ∧ check_lseek_row (lseek_in 6 (Z_to_bv 64 (-1)) 1) (mkEffect 1 [] []) read_model
      = CheckOk (with_fds (fd_insert read_fds 6 (.FdFile [102] 1)) read_model) []
    ∧ check_lseek_row (lseek_in 6 (Z_to_bv 64 (-3)) 1) (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckOk read_model []
    ∧ check_lseek_row (lseek_in 6 (Z_to_bv 64 (-3)) 1) (mkEffect 0 [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rwp_norm

/-- THE CEILING IS `LLONG_MAX`: SEEK_END by 2^63 - 3 from the two-byte end
lands on 2^63 - 1, which `vfs_setpos_cookie`'s `offset > maxsize`
(fs/read_write.c:60-61, Linux v6.18.46) accepts at tmpfs's
`MAX_LFS_FILESIZE`; one further wraps negative in `loff_t` and is
-EINVAL, and the 2^63 a wider sum would name is refused.  A filesystem
with a smaller `s_maxbytes` answers -EINVAL at the first row, which the
arm does not accept (bugs/lseek-destination-ceiling-is-tmpfs.md).
kernel: fs/read_write.c:vfs_setpos_cookie,generic_file_llseek_size; mm/shmem.c:shmem_file_llseek@v6.18.46 -/
theorem check_lseek_file_ceiling :
    check_lseek_row (lseek_in 3 (Z_to_bv 64 (2 ^ 63 - 3)) 2) (mkEffect (Z_to_bv 64 (2 ^ 63 - 1)) [] [])
        lseek_model
      = CheckOk (with_fds (fd_insert lseek_fds 3 (.FdFile [102] (Z_to_bv 64 (2 ^ 63 - 1))))
          lseek_model) []
    ∧ check_lseek_row (lseek_in 3 (Z_to_bv 64 (2 ^ 63 - 2)) 2) (mkEffect (errno_ret EINVAL) [] [])
        lseek_model
      = CheckOk lseek_model []
    ∧ check_lseek_row (lseek_in 3 (Z_to_bv 64 (2 ^ 63 - 2)) 2) (mkEffect (Z_to_bv 64 (2 ^ 63)) [] [])
        lseek_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> rwp_norm

/-- THE WRITE-ONLY KIND SEEKS THE SAME WAY and stays write-only: fd 4 of
`read_model` holds "j", SEEK_END reports 1 with the entry rewritten as
`FdFileW [103] 1`, and the 0 an unmoved offset reports is refused.
kernel: fs/read_write.c:generic_file_llseek_size@v6.18.46 -/
theorem check_lseek_write_only_file_seek_end :
    check_lseek_row (lseek_in 4 0 2) (mkEffect 1 [] []) read_model
      = CheckOk (with_fds (fd_insert read_fds 4 (.FdFileW [103] 1)) read_model) []
    ∧ check_lseek_row (lseek_in 4 0 2) (mkEffect 0 [] []) read_model = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwp_norm

/-- A WRITE-ONLY FILE SEEKS AS A READ-ONLY ONE DOES: `do_dentry_open` sets
`FMODE_LSEEK` whatever the access mode (fs/open.c:961, Linux v6.18.46),
so `vfs_llseek` reaches `shmem_file_llseek` (mm/shmem.c:3669-3687) on
fd 4 too.  A negative SEEK_SET goes through `generic_file_llseek_size`
(fs/read_write.c:158-186) to `vfs_setpos_cookie`, whose -EINVAL
(fs/read_write.c:58-59) refuses a return of 0; SEEK_DATA declines as on
fd 3 (`check_lseek_seek_data_on_a_file_is_unmodeled`); and fd 27 of
`write_model`, a write-only descriptor on a path the fs does not hold,
declines whatever the effect, as `lseek_spec`'s `FdFileW` arm does.
kernel: fs/read_write.c:ksys_lseek,generic_file_llseek_size,vfs_setpos_cookie; mm/shmem.c:shmem_file_llseek; fs/open.c:do_dentry_open@v6.18.46 -/
theorem check_lseek_write_only_file_edges :
    check_lseek_row (lseek_in 4 (Z_to_bv 64 (-1)) 0) (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckOk read_model []
    ∧ check_lseek_row (lseek_in 4 (Z_to_bv 64 (-1)) 0) (mkEffect 0 [] []) read_model
      = CheckReject
    ∧ check_lseek_row (lseek_in 4 0 3) (mkEffect 0 [] []) read_model = CheckUnmodeled
    ∧ check_lseek_row (lseek_in 27 0 2) (mkEffect 0 [] []) write_model = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rwp_norm

/-- THE DEVICES ANSWER 0 AND MOVE NOTHING: `null_lseek`
(drivers/char/mem.c:561-564, Linux v6.18.46) stores and returns 0, on
either open of /dev/null, and `noop_llseek` (fs/read_write.c:324-327)
returns the random device's unmoved position; on either device the
offset asked for is refused.
kernel: drivers/char/mem.c:null_lseek; fs/read_write.c:noop_llseek@v6.18.46 -/
theorem check_lseek_devices_are_zero :
    check_lseek_row (lseek_in 8 5 0) (mkEffect 0 [] []) read_model = CheckOk read_model []
    ∧ check_lseek_row (lseek_in 8 5 0) (mkEffect 5 [] []) read_model = CheckReject
    ∧ check_lseek_row (lseek_in 9 (Z_to_bv 64 (-1)) 1) (mkEffect 0 [] []) read_model
      = CheckOk read_model []
    ∧ check_lseek_row (lseek_in 24 5 0) (mkEffect 0 [] []) read_model = CheckOk read_model []
    ∧ check_lseek_row (lseek_in 24 5 0) (mkEffect 5 [] []) read_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rwp_norm

/-- PIPE ENDS AND SOCKETS ARE -ESPIPE: their files carry no `FMODE_LSEEK`,
and `vfs_llseek` answers -ESPIPE on that bit (fs/read_write.c:387-388,
Linux v6.18.46).
kernel: fs/read_write.c:vfs_llseek; fs/pipe.c:create_pipe_files; net/socket.c:sock_alloc_file@v6.18.46 -/
theorem check_lseek_unseekable_kinds_are_espipe :
    check_lseek_row (lseek_in 14 0 0) (mkEffect (errno_ret ESPIPE) [] []) read_model
      = CheckOk read_model []
    ∧ check_lseek_row (lseek_in 15 0 0) (mkEffect (errno_ret ESPIPE) [] []) read_model
      = CheckOk read_model []
    ∧ check_lseek_row (lseek_in 10 0 0) (mkEffect (errno_ret ESPIPE) [] []) read_model
      = CheckOk read_model [] := by
  refine ⟨?_, ?_, ?_⟩ <;> rwp_norm

/-- Rocq's `lseek_on_a_pipe_end_is_espipe_but_whence_wins`
(Checks/Cases/Fs/Pipe.v), on this file's pipe: fd 14 reads and fd 15
writes pipe 0.  `create_pipe_files` (fs/pipe.c:966-967, Linux v6.18.46)
puts both ends through `stream_open`, and `stream_open`
(fs/open.c:1656-1661) clears `FMODE_LSEEK`, so `vfs_llseek` answers
-ESPIPE on that bit (fs/read_write.c:387-388) and the 0 a seekable file
would report is refused on either end.  `ksys_lseek` tests
`whence <= SEEK_MAX` (fs/read_write.c:401) before `vfs_llseek` (:402), so
whence 42 on a pipe end is -EINVAL and -ESPIPE is refused.
kernel: fs/read_write.c:ksys_lseek,vfs_llseek; fs/pipe.c:create_pipe_files; fs/open.c:stream_open@v6.18.46 -/
theorem check_lseek_on_a_pipe_end_is_espipe_but_whence_wins :
    check_lseek_row (lseek_in 14 0 0) (mkEffect (errno_ret ESPIPE) [] []) read_model
      = CheckOk read_model []
    ∧ check_lseek_row (lseek_in 15 0 0) (mkEffect (errno_ret ESPIPE) [] []) read_model
      = CheckOk read_model []
    ∧ check_lseek_row (lseek_in 14 0 0) (mkEffect 0 [] []) read_model = CheckReject
    ∧ check_lseek_row (lseek_in 15 0 0) (mkEffect 0 [] []) read_model = CheckReject
    ∧ check_lseek_row (lseek_in 14 0 42) (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckOk read_model []
    ∧ check_lseek_row (lseek_in 14 0 42) (mkEffect (errno_ret ESPIPE) [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwp_norm

/-- A SOCKET REFUSES A SEEK TOO, AND THE WHENCE STILL COMES FIRST:
`sock_alloc_file` builds the file through `alloc_file_pseudo` with
`socket_file_ops`, which has no `llseek`, and `file_init_path`
(fs/file_table.c:364-365, Linux v6.18.46) grants `FMODE_LSEEK` only to a
file whose operations have one.  So `vfs_llseek` answers -ESPIPE
(fs/read_write.c:387-388) and the 0 a seekable file would report is
refused; and whence 42 is `ksys_lseek`'s -EINVAL (fs/read_write.c:401),
with -ESPIPE refused.
kernel: fs/read_write.c:ksys_lseek,vfs_llseek; net/socket.c:sock_alloc_file; fs/file_table.c:file_init_path@v6.18.46 -/
theorem check_lseek_socket_refuses_a_seek :
    check_lseek_row (lseek_in 10 0 0) (mkEffect 0 [] []) read_model = CheckReject
    ∧ check_lseek_row (lseek_in 10 0 42) (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckOk read_model []
    ∧ check_lseek_row (lseek_in 10 0 42) (mkEffect (errno_ret ESPIPE) [] []) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> rwp_norm

/-- A DIRECTORY DECLINES EVERY WHENCE THE GATE LETS THROUGH, and the gate
still comes first: tmpfs's `offset_dir_llseek` (fs/libfs.c:433-448, Linux
v6.18.46) moves a cursor the model does not hold, so SEEK_CUR declines
whatever effect is offered, while whence 42 is `ksys_lseek`'s -EINVAL
(fs/read_write.c:401).  A file on a path the tables do not hold declines
too.
kernel: fs/libfs.c:offset_dir_llseek; fs/read_write.c:ksys_lseek@v6.18.46 -/
theorem check_lseek_declines :
    check_lseek_row (lseek_in 5 0 1) (mkEffect 0 [] []) read_model = CheckUnmodeled
    ∧ check_lseek_row (lseek_in 5 0 42) (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckOk read_model []
    ∧ check_lseek_row (lseek_in 7 0 2) (mkEffect 0 [] []) read_model = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_⟩ <;> rwp_norm

/-- THE DESCRIPTOR IS THE LOW 32 BITS OF a0: 2^32 + 3 is fd 3.
kernel: fs/read_write.c:lseek,ksys_lseek@v6.18.46 -/
theorem check_lseek_fd_truncates_to_32_bits :
    check_lseek_row (lseek_in (Z_to_bv 64 (2 ^ 32 + 3)) 0 2) (mkEffect 2 [] []) lseek_model
      = CheckOk (with_fds (fd_insert lseek_fds 3 (.FdFile [102] 2)) lseek_model) [] := by
  rwp_norm

/-- THE WHENCE GATE ENDS AT 4: `ksys_lseek` (fs/read_write.c:400-401,
Linux v6.18.46) calls `vfs_llseek` only for `whence <= SEEK_MAX`, and
`SEEK_MAX` is `SEEK_HOLE`, 4 (include/uapi/linux/fs.h:56-57).  So 5, one
past it, is -EINVAL on the channel, whose -ESPIPE is refused, and on the
file, whose unmoved offset 0 is refused.
kernel: fs/read_write.c:ksys_lseek,vfs_llseek@v6.18.46 -/
theorem check_lseek_whence_one_past_seek_max_is_einval :
    check_lseek_row (lseek_in 0 0 5) (mkEffect (errno_ret EINVAL) [] []) lseek_model
      = CheckOk lseek_model []
    ∧ check_lseek_row (lseek_in 0 0 5) (mkEffect (errno_ret ESPIPE) [] []) lseek_model
      = CheckReject
    ∧ check_lseek_row (lseek_in 3 0 5) (mkEffect (errno_ret EINVAL) [] []) lseek_model
      = CheckOk lseek_model []
    ∧ check_lseek_row (lseek_in 3 0 5) (mkEffect 0 [] []) lseek_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rwp_norm

/-- SEEK_CUR COUNTS FROM THE DESCRIPTOR'S OFFSET, on either file kind:
`generic_file_llseek_size` (fs/read_write.c:170-182, Linux v6.18.46)
sets `f_pos + offset`, and neither the size nor 0.  fd 23 of `read_model`
and fd 31 of `write_model` hold "hi" at offset 1, so SEEK_CUR by 1 is 2
on each, the entry rewritten there and still of its kind; the 3 a
size-based base would give is refused, as is the 1 a zero base would.
kernel: fs/read_write.c:generic_file_llseek_size; mm/shmem.c:shmem_file_llseek@v6.18.46 -/
theorem check_lseek_seek_cur_counts_from_the_descriptor_offset :
    check_lseek_row (lseek_in 23 1 1) (mkEffect 2 [] []) read_model
      = CheckOk (with_fds (fd_insert read_fds 23 (.FdFile [102] 2)) read_model) []
    ∧ check_lseek_row (lseek_in 23 1 1) (mkEffect 3 [] []) read_model = CheckReject
    ∧ check_lseek_row (lseek_in 23 1 1) (mkEffect 1 [] []) read_model = CheckReject
    ∧ check_lseek_row (lseek_in 31 1 1) (mkEffect 2 [] []) write_model
      = CheckOk (with_fds (fd_insert write_fds 31 (.FdFileW [102] 2)) write_model) []
    ∧ check_lseek_row (lseek_in 31 1 1) (mkEffect 3 [] []) write_model = CheckReject
    ∧ check_lseek_row (lseek_in 31 1 1) (mkEffect 1 [] []) write_model = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwp_norm

/-! ### The witnesses -/

/-- The pread64 witness names the kernel's answer on each deterministic
arm — -EINVAL at a negative position, -EBADF on a closed fd, -ESPIPE on a
pipe, -EISDIR on a directory, 0 on /dev/null — and the delivery on the
file and on the random device, the stream advanced.
kernel: fs/read_write.c:ksys_pread64,vfs_read; fs/libfs.c:generic_read_dir; drivers/char/mem.c:read_null; mm/shmem.c:shmem_file_read_iter; drivers/char/random.c:urandom_read_iter@v6.18.46 -/
theorem pread64_witness_names_the_answer :
    pread64_witness_row (pread_in 30 4096 16 (Z_to_bv 64 (-1)) wmem_none) read_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) read_model []
    ∧ pread64_witness_row (pread_in 30 4096 16 0 wmem_none) read_model
      = Ok (mkEffect (errno_ret EBADF) [] []) read_model []
    ∧ pread64_witness_row (pread_in 14 4096 16 0 (wmem_first 16)) read_model
      = Ok (mkEffect (errno_ret ESPIPE) [] []) read_model []
    ∧ pread64_witness_row (pread_in 5 4096 16 0 (wmem_first 16)) read_model
      = Ok (mkEffect (errno_ret EISDIR) [] []) read_model []
    ∧ pread64_witness_row (pread_in 8 4096 16 0 wmem_none) read_model
      = Ok (mkEffect 0 [] []) read_model []
    ∧ pread64_witness_row (pread_in 3 4096 100 1 (wmem_first 1)) read_model
      = Ok (mkEffect 1 [(4096, [105])] []) read_model []
    ∧ pread64_witness_row (pread_in 24 4096 2 7 (wmem_first 2)) (urandom_model (ICons 1 (ICons 2 IEof)))
      = Ok (mkEffect 2 [(4096, [1, 2])] []) (urandom_model IEof) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwp_witness_norm

/-- …and is `Unmodeled` where the spec declines, on each decline
`check_pread64_declines` pins: the partially writable destination, the
path the file system does not hold, and a declared random stream shorter
than the count.
kernel: fs/read_write.c:vfs_read; mm/shmem.c:shmem_file_read_iter; drivers/char/random.c:urandom_read_iter@v6.18.46 -/
theorem pread64_witness_is_unmodeled_where_the_spec_declines :
    pread64_witness_row (pread_in 3 4096 100 0 (wmem_first 1)) read_model = Unmodeled
    ∧ pread64_witness_row (pread_in 7 4096 16 0 (wmem_first 16)) read_model = Unmodeled
    ∧ pread64_witness_row (pread_in 24 4096 3 0 (wmem_first 3)) (urandom_model (ICons 1 (ICons 2 IEof)))
      = Unmodeled := by
  refine ⟨?_, ?_, ?_⟩ <;> rwp_witness_norm

/-- The pwrite64 witness names the transfer — the bytes landed at the
position, the copy-in recorded, fd 3 unmoved — /dev/null's swallowed
count, and -EFAULT for an unreadable source at the end of the file.
kernel: fs/read_write.c:ksys_pwrite64,vfs_write; mm/filemap.c:generic_perform_write; drivers/char/mem.c:write_null@v6.18.46 -/
theorem pwrite64_witness_names_the_answer :
    pwrite64_witness_row (pwrite_in 3 4096 2 4 mem_ab) readv_write_only_model
      = Ok (with_copyins [(4096, 2)] (mkEffect 2 [] []))
          (with_fs (fs_set write_only_fs [102] [0, 0, 0, 0, 97, 98]) readv_write_only_model) []
    ∧ pwrite64_witness_row (pwrite_in 9 4096 2 0 mem_none) write_model
      = Ok (mkEffect 2 [] []) write_model []
    ∧ pwrite64_witness_row (pwrite_in 3 4096 1 0 mem_none) readv_write_only_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) readv_write_only_model [] := by
  refine ⟨?_, ?_, ?_⟩ <;> rwp_witness_norm

/-- …and is `Unmodeled` where the spec declines: the unreadable source one
byte past the end, and the path the tables do not hold.
kernel: fs/read_write.c:vfs_write; mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem pwrite64_witness_is_unmodeled_where_the_spec_declines :
    pwrite64_witness_row (pwrite_in 3 4096 1 1 mem_none) readv_write_only_model = Unmodeled
    ∧ pwrite64_witness_row (pwrite_in 27 4096 1 0 mem_a) write_model = Unmodeled := by
  refine ⟨?_, ?_⟩ <;> rwp_witness_norm

/-- The lseek witness names SEEK_END's size with the offset moved, the
whence gate's -EINVAL and the channel's -ESPIPE, and is `Unmodeled` on
SEEK_DATA over a file and on a directory.
kernel: fs/read_write.c:ksys_lseek,vfs_llseek,generic_file_llseek_size; mm/shmem.c:shmem_file_llseek; fs/libfs.c:offset_dir_llseek@v6.18.46 -/
theorem lseek_witness_names_the_answer :
    lseek_witness_row (lseek_in 3 0 2) lseek_model
      = Ok (mkEffect 2 [] []) (with_fds (fd_insert lseek_fds 3 (.FdFile [102] 2)) lseek_model) []
    ∧ lseek_witness_row (lseek_in 0 0 42) lseek_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) lseek_model []
    ∧ lseek_witness_row (lseek_in 0 0 0) lseek_model
      = Ok (mkEffect (errno_ret ESPIPE) [] []) lseek_model []
    ∧ lseek_witness_row (lseek_in 3 0 3) lseek_model = Unmodeled
    ∧ lseek_witness_row (lseek_in 5 0 1) read_model = Unmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rwp_witness_norm

/-- `lseek_witness` ON A WRITE-ONLY FILE names -EINVAL for a negative
SEEK_SET (`vfs_setpos_cookie`, fs/read_write.c:58-59, Linux v6.18.46)
and, for SEEK_END, the file's length 1, with the descriptor moved there
and still write-only (`generic_file_llseek_size`, fs/read_write.c:158-186,
which `shmem_file_llseek` hands `i_size`, mm/shmem.c:3674-3676).
kernel: fs/read_write.c:vfs_setpos_cookie,generic_file_llseek_size; mm/shmem.c:shmem_file_llseek@v6.18.46 -/
theorem lseek_witness_write_only :
    lseek_witness_row (lseek_in 4 (Z_to_bv 64 (-1)) 0) read_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) read_model []
    ∧ lseek_witness_row (lseek_in 4 0 2) read_model
      = Ok (mkEffect 1 [] []) (with_fds (fd_insert read_fds 4 (.FdFileW [103] 1)) read_model) [] := by
  refine ⟨?_, ?_⟩ <;> rwp_witness_norm

/-- THE PREAD64 WITNESS NAMES EVERY GATE the first pin does not reach, the
checker's answers above: -EINVAL at position 2^63, `LLONG_MIN`, before
the closed fd 30's -EBADF (`ksys_pread64`, fs/read_write.c:755-760,
Linux v6.18.46); -ESPIPE on the channel, the pipe's write end and
a socket, which `ksys_pread64` gives (fs/read_write.c:762-765) before it
calls `vfs_read`; -EBADF on the write-only file
and on the write-only /dev/null, where `vfs_read`
(fs/read_write.c:556-561) tests the mode before the range; and on
/dev/null, the random device, a directory and a file, the range's
-EFAULT, the -EINVAL of `rw_verify_area` (fs/read_write.c:467-469) and,
with both wrong, the range's -EFAULT again; on a file with nothing
writable at all, -EFAULT.
kernel: fs/read_write.c:ksys_pread64,vfs_read,rw_verify_area; mm/shmem.c:shmem_file_read_iter@v6.18.46 -/
theorem pread64_witness_names_every_gate :
    pread64_witness_row (pread_in 30 4096 16 (Z_to_bv 64 (2 ^ 63)) wmem_none) read_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) read_model []
    ∧ pread64_witness_row (pread_in 0 4096 16 0 (wmem_first 16)) read_model
      = Ok (mkEffect (errno_ret ESPIPE) [] []) read_model []
    ∧ pread64_witness_row (pread_in 15 4096 16 0 (wmem_first 16)) read_model
      = Ok (mkEffect (errno_ret ESPIPE) [] []) read_model []
    ∧ pread64_witness_row (pread_in 10 4096 16 0 (wmem_first 16)) read_model
      = Ok (mkEffect (errno_ret ESPIPE) [] []) read_model []
    ∧ pread64_witness_row (pread_in 4 4096 16 0 wmem_none) read_model
      = Ok (mkEffect (errno_ret EBADF) [] []) read_model []
    ∧ pread64_witness_row (pread_in 9 (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 wmem_none) read_model
      = Ok (mkEffect (errno_ret EBADF) [] []) read_model []
    ∧ pread64_witness_row (pread_in 8 (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 wmem_none) read_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) read_model []
    ∧ pread64_witness_row (pread_in 8 4096 1 (Z_to_bv 64 (2 ^ 63 - 1)) wmem_none) read_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) read_model []
    ∧ pread64_witness_row (pread_in 8 (Z_to_bv 64 (2 ^ 47 + 1)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) wmem_none)
        read_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) read_model []
    ∧ pread64_witness_row (pread_in 24 (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 wmem_none)
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = Ok (mkEffect (errno_ret EFAULT) [] []) (urandom_model (ICons 1 (ICons 2 IEof))) []
    ∧ pread64_witness_row (pread_in 24 4096 1 (Z_to_bv 64 (2 ^ 63 - 1)) (wmem_first 1))
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = Ok (mkEffect (errno_ret EINVAL) [] []) (urandom_model (ICons 1 (ICons 2 IEof))) []
    ∧ pread64_witness_row (pread_in 24 (Z_to_bv 64 (2 ^ 47 + 1)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) wmem_none)
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = Ok (mkEffect (errno_ret EFAULT) [] []) (urandom_model (ICons 1 (ICons 2 IEof))) []
    ∧ pread64_witness_row (pread_in 5 (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 wmem_none) read_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) read_model []
    ∧ pread64_witness_row (pread_in 5 4096 1 (Z_to_bv 64 (2 ^ 63 - 1)) (wmem_first 1)) read_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) read_model []
    ∧ pread64_witness_row (pread_in 5 (Z_to_bv 64 (2 ^ 47 + 1)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) wmem_none)
        read_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) read_model []
    ∧ pread64_witness_row (pread_in 3 (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 wmem_none) read_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) read_model []
    ∧ pread64_witness_row (pread_in 3 4096 1 (Z_to_bv 64 (2 ^ 63 - 1)) (wmem_first 1)) read_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) read_model []
    ∧ pread64_witness_row (pread_in 3 (Z_to_bv 64 (2 ^ 47 + 1)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) wmem_none)
        read_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) read_model []
    ∧ pread64_witness_row (pread_in 3 4096 100 0 wmem_none) read_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) read_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rwp_witness_norm

/-- …and, like the checker, judges the range and the position on the count
the call named (`vfs_read`, fs/read_write.c:560-567, Linux v6.18.46):
2^48 bytes at 4096 are -EFAULT, and 2^32 bytes at position 2^63 - 2^31
the -EINVAL of `rw_verify_area` (fs/read_write.c:467-469), on /dev/null,
the random device, a directory and a file.
kernel: fs/read_write.c:vfs_read,rw_verify_area; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pread64_witness_gates_read_the_unclamped_count :
    pread64_witness_row (pread_in 8 4096 (Z_to_bv 64 (2 ^ 48)) 0 wmem_none) read_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) read_model []
    ∧ pread64_witness_row (pread_in 24 4096 (Z_to_bv 64 (2 ^ 48)) 0 (wmem_first 2))
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = Ok (mkEffect (errno_ret EFAULT) [] []) (urandom_model (ICons 1 (ICons 2 IEof))) []
    ∧ pread64_witness_row (pread_in 5 4096 (Z_to_bv 64 (2 ^ 48)) 0 wmem_none) read_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) read_model []
    ∧ pread64_witness_row (pread_in 3 4096 (Z_to_bv 64 (2 ^ 48)) 0 (wmem_first 2)) read_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) read_model []
    ∧ pread64_witness_row (pread_in 8 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) wmem_none)
        read_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) read_model []
    ∧ pread64_witness_row
        (pread_in 24 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) (wmem_first 2))
        (urandom_model (ICons 1 (ICons 2 IEof)))
      = Ok (mkEffect (errno_ret EINVAL) [] []) (urandom_model (ICons 1 (ICons 2 IEof))) []
    ∧ pread64_witness_row (pread_in 5 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) wmem_none)
        read_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) read_model []
    ∧ pread64_witness_row
        (pread_in 3 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) (wmem_first 2))
        read_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) read_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwp_witness_norm

/-- THE PWRITE64 WITNESS NAMES EVERY GATE the first pin does not reach, the
checker's answers above: -EINVAL at a negative position, 2^63 among
them, before the closed fd 5's -EBADF (`ksys_pwrite64`,
fs/read_write.c:785-790, Linux v6.18.46); -ESPIPE on the channel, both pipe ends and a socket
(fs/read_write.c:792-795); -EBADF on the read-only file, the random
device, a directory and the read-only /dev/null, whose mode `vfs_write`
(fs/read_write.c:670-675) tests before the range; on the write-only
/dev/null and the write-only file, the range's -EFAULT, the -EINVAL of
`rw_verify_area` (fs/read_write.c:467-469) and, with both wrong, the
range's -EFAULT again, each on the count the call named; and on the
write-only /dev/null 2^40 bytes swallowed as `MAX_RW_COUNT`, which
`vfs_write` (fs/read_write.c:680-681) clamps the count to before
`write_null` (drivers/char/mem.c:418-422) returns it.
kernel: fs/read_write.c:ksys_pwrite64,vfs_write,rw_verify_area; drivers/char/mem.c:write_null@v6.18.46 -/
theorem pwrite64_witness_names_every_gate :
    pwrite64_witness_row (pwrite_in 5 4096 2 (Z_to_bv 64 (-1)) mem_ab) readv_write_only_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) readv_write_only_model []
    ∧ pwrite64_witness_row (pwrite_in 5 4096 2 (Z_to_bv 64 (2 ^ 63)) mem_ab) readv_write_only_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) readv_write_only_model []
    ∧ pwrite64_witness_row (pwrite_in 5 4096 2 0 mem_ab) readv_write_only_model
      = Ok (mkEffect (errno_ret EBADF) [] []) readv_write_only_model []
    ∧ pwrite64_witness_row (pwrite_in 1 4096 2 0 mem_ab) write_model
      = Ok (mkEffect (errno_ret ESPIPE) [] []) write_model []
    ∧ pwrite64_witness_row (pwrite_in 14 4096 2 0 mem_ab) write_model
      = Ok (mkEffect (errno_ret ESPIPE) [] []) write_model []
    ∧ pwrite64_witness_row (pwrite_in 15 4096 2 0 mem_ab) write_model
      = Ok (mkEffect (errno_ret ESPIPE) [] []) write_model []
    ∧ pwrite64_witness_row (pwrite_in 10 4096 2 0 mem_ab) write_model
      = Ok (mkEffect (errno_ret ESPIPE) [] []) write_model []
    ∧ pwrite64_witness_row (pwrite_in 3 4096 2 0 mem_ab) write_model
      = Ok (mkEffect (errno_ret EBADF) [] []) write_model []
    ∧ pwrite64_witness_row (pwrite_in 24 4096 2 0 mem_ab) write_model
      = Ok (mkEffect (errno_ret EBADF) [] []) write_model []
    ∧ pwrite64_witness_row (pwrite_in 5 4096 2 0 mem_ab) write_model
      = Ok (mkEffect (errno_ret EBADF) [] []) write_model []
    ∧ pwrite64_witness_row (pwrite_in 8 (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 mem_none) write_model
      = Ok (mkEffect (errno_ret EBADF) [] []) write_model []
    ∧ pwrite64_witness_row (pwrite_in 9 4096 (Z_to_bv 64 (2 ^ 40)) 0 mem_none) write_model
      = Ok (mkEffect (Z_to_bv 64 0x7ffff000) [] []) write_model []
    ∧ pwrite64_witness_row (pwrite_in 9 (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 mem_none) write_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) write_model []
    ∧ pwrite64_witness_row (pwrite_in 9 4096 1 (Z_to_bv 64 (2 ^ 63 - 1)) mem_none) write_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) write_model []
    ∧ pwrite64_witness_row (pwrite_in 9 (Z_to_bv 64 (2 ^ 47 + 1)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) mem_none)
        write_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) write_model []
    ∧ pwrite64_witness_row (pwrite_in 3 (Z_to_bv 64 (2 ^ 47 + 1)) 0 0 mem_none) readv_write_only_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) readv_write_only_model []
    ∧ pwrite64_witness_row (pwrite_in 3 4096 1 (Z_to_bv 64 (2 ^ 63 - 1)) mem_a) readv_write_only_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) readv_write_only_model []
    ∧ pwrite64_witness_row (pwrite_in 3 (Z_to_bv 64 (2 ^ 47 + 1)) 1 (Z_to_bv 64 (2 ^ 63 - 1)) mem_none)
        readv_write_only_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) readv_write_only_model []
    ∧ pwrite64_witness_row (pwrite_in 9 4096 (Z_to_bv 64 (2 ^ 48)) 0 mem_none) write_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) write_model []
    ∧ pwrite64_witness_row (pwrite_in 3 4096 (Z_to_bv 64 (2 ^ 48)) 0 mem_ab) readv_write_only_model
      = Ok (mkEffect (errno_ret EFAULT) [] []) readv_write_only_model []
    ∧ pwrite64_witness_row (pwrite_in 9 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) mem_none)
        write_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) write_model []
    ∧ pwrite64_witness_row (pwrite_in 3 4096 (Z_to_bv 64 (2 ^ 32)) (Z_to_bv 64 (2 ^ 63 - 2 ^ 31)) mem_ab)
        readv_write_only_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) readv_write_only_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rwp_witness_norm

/-- …names a zero count's 0 with the file untouched and no copy-in
recorded, at position 4 and one byte past the hole bound alike
(`shmem_file_write_iter` leaves before anything is positioned,
mm/shmem.c:3497-3499, Linux v6.18.46), and is `Unmodeled` on the
one-byte write past that bound, as the spec is.
kernel: fs/read_write.c:generic_write_checks; mm/shmem.c:shmem_file_write_iter@v6.18.46 -/
theorem pwrite64_witness_zero_count_and_the_hole_bound :
    pwrite64_witness_row (pwrite_in 3 4096 0 4 mem_none) readv_write_only_model
      = Ok (mkEffect 0 [] []) (with_fs (fs_set write_only_fs [102] []) readv_write_only_model) []
    ∧ pwrite64_witness_row (pwrite_in 3 4096 0 (Z_to_bv 64 (rw_bytes_max + 1)) mem_none)
        readv_write_only_model
      = Ok (mkEffect 0 [] []) (with_fs (fs_set write_only_fs [102] []) readv_write_only_model) []
    ∧ pwrite64_witness_row (pwrite_in 3 4096 1 (Z_to_bv 64 (rw_bytes_max + 1)) mem_a)
        readv_write_only_model
      = Unmodeled := by
  refine ⟨?_, ?_, ?_⟩ <;> rwp_witness_norm

/-- BOTH WITNESSES NAME -ESPIPE BEFORE THE RANGE, as the checkers accept:
`ksys_pread64` (fs/read_write.c:762-765, Linux v6.18.46) and
`ksys_pwrite64` (fs/read_write.c:792-795) answer -ESPIPE on an
unseekable descriptor before they call `vfs_read` or `vfs_write`, so a
buffer past the top changes nothing on the channel, a pipe end or a
socket.
kernel: fs/read_write.c:ksys_pread64,ksys_pwrite64@v6.18.46 -/
theorem positional_witnesses_name_the_kind_before_the_range :
    pread64_witness_row (pread_in 0 (Z_to_bv 64 (2 ^ 47 + 1)) 16 0 wmem_none) read_model
      = Ok (mkEffect (errno_ret ESPIPE) [] []) read_model []
    ∧ pread64_witness_row (pread_in 14 (Z_to_bv 64 (2 ^ 47 + 1)) 16 0 wmem_none) read_model
      = Ok (mkEffect (errno_ret ESPIPE) [] []) read_model []
    ∧ pread64_witness_row (pread_in 10 (Z_to_bv 64 (2 ^ 47 + 1)) 16 0 wmem_none) read_model
      = Ok (mkEffect (errno_ret ESPIPE) [] []) read_model []
    ∧ pwrite64_witness_row (pwrite_in 1 (Z_to_bv 64 (2 ^ 47 + 1)) 2 0 mem_none) write_model
      = Ok (mkEffect (errno_ret ESPIPE) [] []) write_model []
    ∧ pwrite64_witness_row (pwrite_in 15 (Z_to_bv 64 (2 ^ 47 + 1)) 2 0 mem_none) write_model
      = Ok (mkEffect (errno_ret ESPIPE) [] []) write_model []
    ∧ pwrite64_witness_row (pwrite_in 10 (Z_to_bv 64 (2 ^ 47 + 1)) 2 0 mem_none) write_model
      = Ok (mkEffect (errno_ret ESPIPE) [] []) write_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwp_witness_norm

/-- THE LSEEK WITNESS NAMES EVERY KIND the first pin does not reach, the
checker's answers above: -EBADF on a closed fd (`ksys_lseek`,
fs/read_write.c:396-398, Linux v6.18.46), -EINVAL for whence 5 (:400-401)
while whence 4, `SEEK_MAX` itself, reaches the channel's -ESPIPE;
-ESPIPE on a socket and both pipe ends, whose files carry no
`FMODE_LSEEK` (`vfs_llseek`, fs/read_write.c:387-388); 0 on either
/dev/null open (`null_lseek`, drivers/char/mem.c:561-564) and on the random
device (`noop_llseek`, fs/read_write.c:324-327); on a file, SEEK_CUR from
the descriptor's own offset with the entry moved, and -EINVAL below 0
(`vfs_setpos_cookie`, fs/read_write.c:58-59); and `Unmodeled` on a path
the tables do not hold and on SEEK_DATA over the write-only file.
kernel: fs/read_write.c:ksys_lseek,vfs_llseek,noop_llseek,vfs_setpos_cookie,generic_file_llseek_size; drivers/char/mem.c:null_lseek@v6.18.46 -/
theorem lseek_witness_names_every_kind :
    lseek_witness_row (lseek_in 9 0 0) lseek_model
      = Ok (mkEffect (errno_ret EBADF) [] []) lseek_model []
    ∧ lseek_witness_row (lseek_in 0 0 5) lseek_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) lseek_model []
    ∧ lseek_witness_row (lseek_in 0 0 4) lseek_model
      = Ok (mkEffect (errno_ret ESPIPE) [] []) lseek_model []
    ∧ lseek_witness_row (lseek_in 10 0 0) read_model
      = Ok (mkEffect (errno_ret ESPIPE) [] []) read_model []
    ∧ lseek_witness_row (lseek_in 14 0 0) read_model
      = Ok (mkEffect (errno_ret ESPIPE) [] []) read_model []
    ∧ lseek_witness_row (lseek_in 15 0 0) read_model
      = Ok (mkEffect (errno_ret ESPIPE) [] []) read_model []
    ∧ lseek_witness_row (lseek_in 8 5 0) read_model = Ok (mkEffect 0 [] []) read_model []
    ∧ lseek_witness_row (lseek_in 9 5 0) read_model = Ok (mkEffect 0 [] []) read_model []
    ∧ lseek_witness_row (lseek_in 24 5 0) read_model = Ok (mkEffect 0 [] []) read_model []
    ∧ lseek_witness_row (lseek_in 23 1 1) read_model
      = Ok (mkEffect 2 [] []) (with_fds (fd_insert read_fds 23 (.FdFile [102] 2)) read_model) []
    ∧ lseek_witness_row (lseek_in 31 1 1) write_model
      = Ok (mkEffect 2 [] []) (with_fds (fd_insert write_fds 31 (.FdFileW [102] 2)) write_model) []
    ∧ lseek_witness_row (lseek_in 6 (Z_to_bv 64 (-3)) 1) read_model
      = Ok (mkEffect (errno_ret EINVAL) [] []) read_model []
    ∧ lseek_witness_row (lseek_in 7 0 2) read_model = Unmodeled
    ∧ lseek_witness_row (lseek_in 27 0 2) write_model = Unmodeled
    ∧ lseek_witness_row (lseek_in 4 0 3) read_model = Unmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwp_witness_norm

/-- THE CHECKERS ACCEPT WHAT THE WITNESSES NAME, on every call: each
witness's `_ok` lemma read through its checker's completeness.
model: `pread64_witness_ok` through `check_pread64_complete_ok` and `check_pread64_complete_unmodeled` -/
theorem check_pread64_accepts_the_witness (fd buf count pos : word) (i : SyscallInput) (m : Model) :
    (∀ (eff : SyscallEffect) (m' : Model) (evs : List event),
        pread64_witness fd buf count pos i m = Ok eff m' evs →
        check_pread64 i fd buf count pos eff m = CheckOk m' evs)
    ∧ (∀ eff : SyscallEffect,
        pread64_witness fd buf count pos i m = Unmodeled →
        check_pread64 i fd buf count pos eff m = CheckUnmodeled) := by
  refine ⟨?_, ?_⟩
  · intro eff m' evs h
    have hw := pread64_witness_ok fd buf count pos i m
    rw [h] at hw
    exact check_pread64_complete_ok i fd buf count pos eff m m' evs hw
  · intro eff h
    have hw := pread64_witness_ok fd buf count pos i m
    rw [h] at hw
    exact check_pread64_complete_unmodeled i fd buf count pos eff m hw

/-- …for pwrite64.
model: `pwrite64_witness_ok` through `check_pwrite64_complete_ok` and `check_pwrite64_complete_unmodeled` -/
theorem check_pwrite64_accepts_the_witness (fd buf count pos : word) (i : SyscallInput)
    (m : Model) :
    (∀ (eff : SyscallEffect) (m' : Model) (evs : List event),
        pwrite64_witness fd buf count pos i m = Ok eff m' evs →
        check_pwrite64 i fd buf count pos eff m = CheckOk m' evs)
    ∧ (∀ eff : SyscallEffect,
        pwrite64_witness fd buf count pos i m = Unmodeled →
        check_pwrite64 i fd buf count pos eff m = CheckUnmodeled) := by
  refine ⟨?_, ?_⟩
  · intro eff m' evs h
    have hw := pwrite64_witness_ok fd buf count pos i m
    rw [h] at hw
    exact check_pwrite64_complete_ok i fd buf count pos eff m m' evs hw
  · intro eff h
    have hw := pwrite64_witness_ok fd buf count pos i m
    rw [h] at hw
    exact check_pwrite64_complete_unmodeled i fd buf count pos eff m hw

/-- …for lseek, whose witness and checker take no input.
model: `lseek_witness_ok` through `check_lseek_complete_ok` and `check_lseek_complete_unmodeled` -/
theorem check_lseek_accepts_the_witness (fd off whence : word) (i : SyscallInput) (m : Model) :
    (∀ (eff : SyscallEffect) (m' : Model) (evs : List event),
        lseek_witness fd off whence m = Ok eff m' evs →
        check_lseek fd off whence eff m = CheckOk m' evs)
    ∧ (∀ eff : SyscallEffect,
        lseek_witness fd off whence m = Unmodeled →
        check_lseek fd off whence eff m = CheckUnmodeled) := by
  refine ⟨?_, ?_⟩
  · intro eff m' evs h
    have hw := lseek_witness_ok fd off whence i m
    rw [h] at hw
    exact check_lseek_complete_ok fd off whence eff m m' evs i hw
  · intro eff h
    have hw := lseek_witness_ok fd off whence i m
    rw [h] at hw
    exact check_lseek_complete_unmodeled fd off whence m i eff hw

/-! ### The `MAX_RW_COUNT` clamp, symbolically

`vfs_read` clamps the count to `MAX_RW_COUNT` (fs/read_write.c:566-567,
Linux v6.18.46) before the file's own read, so a pread delivers at most
that many bytes on every kind.  No fixture holds that many bytes, so no
concrete row above can tell a delivery read at the clamped count from
one read at the raw count; these three facts can, over every file, model
and count.  Each walks the text it is about rather than going through
completeness, so each fails the moment the checker or the witness reads
past the clamp. -/

/-- THE PREAD64 CHECKER ACCEPTS NO DELIVERY PAST THE CLAMP: whatever
`check_pread64` accepts with a single write entry, that entry holds at
most `MAX_RW_COUNT` bytes, on every descriptor kind, model, count and
position.  Every arm but two is a `check_ret_only`, whose accepted effect
has no write entry; the random-device arm is
`check_read_urandom_delivery_clamped`; the file arm compares the effect
with `file_read` at the clamped count, which `file_read_clamped_len`
holds at or below `MAX_RW_COUNT` — `vfs_read`'s clamp
(fs/read_write.c:566-567) ahead of `shmem_file_read_iter`.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem check_pread64_delivery_clamped (i : SyscallInput) (fd buf count pos : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event) (a : word) (bs : List byte)
    (h : check_pread64 i fd buf count pos eff m = CheckOk m' evs)
    (hws : eff.eff_writes = [(a, bs)]) :
    (bs.length : Int) ≤ MAX_RW_COUNT := by
  have hro : ∀ (v : word) (mk : Model) (k : List event),
      check_ret_only eff v mk k = CheckOk m' evs → (bs.length : Int) ≤ MAX_RW_COUNT := by
    intro v mk k hz
    obtain ⟨heq, -, -⟩ := (check_ret_only_ok_iff eff v mk k m' evs).mp hz
    subst heq
    simp only [reduceCtorEq] at hws
  have hgates : ∀ (tail : check_result),
      (tail = CheckOk m' evs → (bs.length : Int) ≤ MAX_RW_COUNT) →
      (if !access_okb buf (bv_unsigned count) then check_ret_only eff (errno_ret EFAULT) m []
       else if rw_pos_einvalb pos (bv_unsigned count) then
         check_ret_only eff (errno_ret EINVAL) m []
       else tail) = CheckOk m' evs → (bs.length : Int) ≤ MAX_RW_COUNT := by
    intro tail htail hz
    generalize (!access_okb buf (bv_unsigned count)) = g1 at hz
    cases g1 with
    | true => simp only [↓reduceIte] at hz; exact hro _ _ _ hz
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hz
      generalize rw_pos_einvalb pos (bv_unsigned count) = g2 at hz
      cases g2 with
      | true => simp only [↓reduceIte] at hz; exact hro _ _ _ hz
      | false => simp only [Bool.false_eq_true, ↓reduceIte] at hz; exact htail hz
  unfold check_pread64 at h
  generalize ppos_einvalb pos = bp at h
  cases bp with
  | true => simp only [↓reduceIte] at h; exact hro _ _ _ h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    generalize fd_lookup (m_fds m) fd = r at h
    cases r with
    | none => exact hro _ _ _ h
    | some e =>
      cases e with
      | FdFileA _ _ => cases h
      | FdFileRW _ _ => cases h
      | FdChannel _ => exact hro _ _ _ h
      | FdPipe _ _ => exact hro _ _ _ h
      | FdSocket _ => exact hro _ _ _ h
      | FdFileW _ _ => exact hro _ _ _ h
      | FdDevNull rd _ =>
        dsimp only at h
        cases rd with
        | false => simp only [Bool.not_false, ↓reduceIte] at h; exact hro _ _ _ h
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          exact hgates _ (hro _ _ _) h
      | FdUrandom =>
        exact hgates _
          (fun hz => check_read_urandom_delivery_clamped i buf count eff m m' evs a bs hz hws) h
      | FdDir => exact hgates _ (hro _ _ _) h
      | FdFile p _ =>
        refine hgates _ (fun hz => ?_) h
        generalize fs_lookup (m_fs m) p = fl at hz
        cases fl with
        | none => cases hz
        | some data =>
          dsimp only at hz
          have hlen := file_read_clamped_len data pos count
          generalize file_read data pos (Z_to_bv 64 (rw_count_clamp count)) = bsF at hz hlen
          generalize read_bytes_map i.in_wmem buf (len_word bsF) = w1 at hz
          cases w1 with
          | none =>
            dsimp only at hz
            generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w2 at hz
            cases w2 with
            | none => exact hro _ _ _ hz
            | some _ => cases hz
          | some _ =>
            dsimp only at hz
            cases bsF with
            | nil => exact hro _ _ _ hz
            | cons b bs0 =>
              dsimp only at hz
              split at hz
              · simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hws
                obtain ⟨rfl, rfl⟩ := hws
                split at hz
                · rename_i hg
                  simp only [Bool.and_eq_true, listN_eqb_eq] at hg
                  obtain ⟨⟨-, rfl⟩, -⟩ := hg
                  exact hlen
                · cases hz
              · cases hz

/-- …SO THE SPEC ADMITS NONE: whatever `pread64_spec` admits with a single
write entry, that entry holds at most `MAX_RW_COUNT` bytes — the model's
own answer to `vfs_read`'s clamp (fs/read_write.c:566-567), carried from
the checker by completeness.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem pread64_delivery_clamped (fd buf count pos : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event) (a : word) (bs : List byte)
    (hspec : pread64_spec fd buf count pos i m (Ok eff m' evs))
    (hws : eff.eff_writes = [(a, bs)]) :
    (bs.length : Int) ≤ MAX_RW_COUNT :=
  check_pread64_delivery_clamped i fd buf count pos eff m m' evs a bs
    (check_pread64_complete_ok i fd buf count pos eff m m' evs hspec) hws

/-- THE PREAD64 WITNESS NAMES NO DELIVERY PAST THE CLAMP either: whatever
`pread64_witness` answers with a single write entry, that entry holds at
most `MAX_RW_COUNT` bytes (`vfs_read`, fs/read_write.c:566-567).  The
random-device arm names exactly the clamped count or declines; the file
arm names `file_read` at the clamped count (`file_read_clamped_len`);
every other arm names a bare return.
kernel: fs/read_write.c:vfs_read@v6.18.46 -/
theorem pread64_witness_delivery_clamped (fd buf count pos : word) (i : SyscallInput)
    (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event) (a : word)
    (bs : List byte) (hw : pread64_witness fd buf count pos i m = Ok eff m' evs)
    (hws : eff.eff_writes = [(a, bs)]) :
    (bs.length : Int) ≤ MAX_RW_COUNT := by
  have hro : ∀ (v : word) (mk : Model), ret_outcome v mk = Ok eff m' evs →
      (bs.length : Int) ≤ MAX_RW_COUNT := by
    intro v mk hz
    unfold ret_outcome at hz
    injection hz with h1 _ _
    subst h1
    simp only [reduceCtorEq] at hws
  have hgates : ∀ (tail : outcome SyscallEffect),
      (tail = Ok eff m' evs → (bs.length : Int) ≤ MAX_RW_COUNT) →
      (if !access_okb buf (bv_unsigned count) then ret_outcome (errno_ret EFAULT) m
       else if rw_pos_einvalb pos (bv_unsigned count) then ret_outcome (errno_ret EINVAL) m
       else tail) = Ok eff m' evs → (bs.length : Int) ≤ MAX_RW_COUNT := by
    intro tail htail hz
    generalize (!access_okb buf (bv_unsigned count)) = g1 at hz
    cases g1 with
    | true => simp only [↓reduceIte] at hz; exact hro _ _ hz
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hz
      generalize rw_pos_einvalb pos (bv_unsigned count) = g2 at hz
      cases g2 with
      | true => simp only [↓reduceIte] at hz; exact hro _ _ hz
      | false => simp only [Bool.false_eq_true, ↓reduceIte] at hz; exact htail hz
  unfold pread64_witness at hw
  generalize ppos_einvalb pos = bp at hw
  cases bp with
  | true => simp only [↓reduceIte] at hw; exact hro _ _ hw
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hw
    generalize fd_lookup (m_fds m) fd = r at hw
    cases r with
    | none => exact hro _ _ hw
    | some e =>
      cases e with
      | FdFileA _ _ => cases hw
      | FdFileRW _ _ => cases hw
      | FdChannel _ => exact hro _ _ hw
      | FdPipe _ _ => exact hro _ _ hw
      | FdSocket _ => exact hro _ _ hw
      | FdFileW _ _ => exact hro _ _ hw
      | FdDevNull rd _ =>
        dsimp only at hw
        cases rd with
        | false => simp only [Bool.not_false, ↓reduceIte] at hw; exact hro _ _ hw
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw
          exact hgates _ (hro _ _) hw
      | FdDir => exact hgates _ (hro _ _) hw
      | FdUrandom =>
        refine hgates _ (fun hz => ?_) hw
        unfold read_urandom_witness at hz
        generalize w_is0 count = b0 at hz
        cases b0 with
        | true => simp only [↓reduceIte] at hz; exact hro _ _ hz
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hz
          generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at hz
          cases w1 with
          | none => exact hro _ _ hz
          | some _ =>
            dsimp only at hz
            have hclamp := (rw_count_clamp_range count).2
            generalize stream_take_z (m_urandom m) (rw_count_clamp count) = rr at hz
            by_cases hl : ((rr.1.length : Int) = rw_count_clamp count)
            · simp only [hl, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hz
              generalize read_bytes_map i.in_wmem buf (len_word rr.1) = w2 at hz
              cases w2 with
              | none => cases hz
              | some _ =>
                dsimp only at hz
                injection hz with h1 _ _
                subst h1
                simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hws
                obtain ⟨-, rfl⟩ := hws
                omega
            · simp only [hl, decide_false, Bool.not_false, ↓reduceIte] at hz
              cases hz
      | FdFile p _ =>
        refine hgates _ (fun hz => ?_) hw
        generalize fs_lookup (m_fs m) p = fl at hz
        cases fl with
        | none => cases hz
        | some data =>
          dsimp only at hz
          have hlen := file_read_clamped_len data pos count
          generalize file_read data pos (Z_to_bv 64 (rw_count_clamp count)) = bsF at hz hlen
          generalize read_bytes_map i.in_wmem buf (len_word bsF) = w1 at hz
          cases w1 with
          | none =>
            dsimp only at hz
            generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w2 at hz
            cases w2 with
            | none => exact hro _ _ hz
            | some _ => cases hz
          | some _ =>
            dsimp only at hz
            injection hz with h1 _ _
            subst h1
            unfold delivered_writes at hws
            cases bsF with
            | nil => cases hws
            | cons b bs0 =>
              simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hws
              obtain ⟨-, rfl⟩ := hws
              exact hlen

end PositionalAndSeek

section WriteThroughTheTable

/-! ## Rocq's write examples through the real table

Rocq states its write examples through `check_syscall`, and the section
above restates them on `check_write_row`, the arm's application written
out. Neither says that the table's row for 64 IS that application; this
section does. `check_syscall_write_in` finds `arm_write` at 64 and unfolds
its `ca_check` to `check_write_row`, and each Rocq example is then stated
through the dispatch under its Rocq name with `_over_the_real_table`.
Where a Rocq example has conjuncts on `FdFileA` or `FdFileRW`, kinds
whose write arms the spec twin declines, the twin keeps the `FdFileW`
conjuncts and its docstring says so; a Rocq example the section above
splits over two row theorems is split here the same way, named for the
part it keeps. The same restatement for eventfd2 is in
`Checks/Cases/Checks/Sys/Fs/EventFd.lean`.

`write_fd_truncates_to_32_bits_over_the_real_table` is the pin on the
narrowing: a0 = 2^32 + 1 is answered as fd 1 through the dispatch. A
table row that handed a0 over whole would find no descriptor there and
accept a bare -EBADF, as `the_write_checker_itself_reads_the_whole_word`
shows of the checker; `write_whole_word_ebadf_rejected_over_the_real_table`
refuses that answer. Rocq's `write_fd_high_bits_ebadf_rejected` does not
separate the two: its -EBADF carries a copy-in, which the no-descriptor
answer refuses as well. -/

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
  (arm_write ca_check_arm_write lookup_ca_checked_table_write)
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs (check_syscall check_syscall_of_found)

/-- The dispatch at 64 is the write row: `lookup_ca` finds `arm_write` for
the number `write_in` carries, and `arm_write.ca_check` is `check_write`
at `fd32 a0`, `a1`, `a2`, which is `check_write_row`. This is the table-side
reading of `SYSCALL_DEFINE3(write, unsigned int, fd, …)`
(fs/read_write.c:746, Linux v6.18.46).
kernel: fs/read_write.c:write@v6.18.46 -/
theorem check_syscall_write_in (fd buf count : word) (mem : word → Option byte)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (write_in fd buf count mem) eff m
      = check_write_row (write_in fd buf count mem) eff m := by
  rw [check_syscall_of_found (write_in fd buf count mem) eff m arm_write
        lookup_ca_checked_table_write, ca_check_arm_write]
  rfl

/-- Rocq's `write_ab_events` through `check_syscall`: `check_write_ab_events`'s
statement with the dispatch in place of the row, closed by
`check_syscall_write_in`.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem write_ab_events_over_the_real_table :
    check_syscall (write_in 1 4096 2 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        demo_model
      = CheckOk demo_model [WriteEv 1 97, WriteEv 1 98] := by
  simp only [check_syscall_write_in]
  exact check_write_ab_events

/-- Rocq's `write_ab_short_delivery` through `check_syscall`: `check_write_ab_short_delivery`'s
statement with the dispatch in place of the row, closed by
`check_syscall_write_in`.
model: the channel's prefix rule in `check_write`, whose one-byte acceptance is the recorded divergence bugs/write-channel-pipebuf-short-write.md -/
theorem write_ab_short_delivery_over_the_real_table :
    check_syscall (write_in 1 4096 2 mem_ab) (with_copyins [(4096, 1)] (mkEffect 1 [] []))
        demo_model
      = CheckOk demo_model [WriteEv 1 97]
    ∧ check_syscall (write_in 1 4096 2 mem_ab) (with_copyins [(4096, 3)] (mkEffect 3 [] []))
        demo_model
      = CheckReject
    ∧ check_syscall (write_in 1 4096 2 mem_ab) (with_copyins [(4096, 0)] (mkEffect 0 [] []))
        demo_model
      = CheckReject := by
  simp only [check_syscall_write_in]
  exact check_write_ab_short_delivery

/-- Rocq's `write_a_then_b_events` through `check_syscall`: `check_write_a_then_b_events`'s
statement with the dispatch in place of the row, closed by
`check_syscall_write_in`.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem write_a_then_b_events_over_the_real_table :
    check_syscall (write_in 1 4096 1 mem_ab) (with_copyins [(4096, 1)] (mkEffect 1 [] []))
        demo_model
      = CheckOk demo_model [WriteEv 1 97]
    ∧ check_syscall (write_in 1 4097 1 mem_ab) (with_copyins [(4097, 1)] (mkEffect 1 [] []))
        demo_model
      = CheckOk demo_model [WriteEv 1 98] := by
  simp only [check_syscall_write_in]
  exact check_write_a_then_b_events

/-- Rocq's `write_fd_truncates_to_32_bits` through `check_syscall`: `check_write_fd_truncates_to_32_bits`'s
statement with the dispatch in place of the row, closed by
`check_syscall_write_in`.
kernel: fs/read_write.c:write,ksys_write@v6.18.46 -/
theorem write_fd_truncates_to_32_bits_over_the_real_table :
    check_syscall (write_in (Z_to_bv 64 (2 ^ 32 + 1)) 4096 2 mem_ab)
        (with_copyins [(4096, 2)] (mkEffect 2 [] [])) demo_model
      = check_syscall (write_in 1 4096 2 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
          demo_model
    ∧ check_syscall (write_in (Z_to_bv 64 (2 ^ 32 + 1)) 4096 2 mem_ab)
        (with_copyins [(4096, 2)] (mkEffect 2 [] [])) demo_model
      = CheckOk demo_model [WriteEv 1 97, WriteEv 1 98] := by
  simp only [check_syscall_write_in]
  exact check_write_fd_truncates_to_32_bits

/-- Rocq's `write_fd_high_bits_ebadf_rejected` through `check_syscall`: `check_write_fd_high_bits_ebadf_rejected`'s
statement with the dispatch in place of the row, closed by
`check_syscall_write_in`.
kernel: fs/read_write.c:write,ksys_write@v6.18.46 -/
theorem write_fd_high_bits_ebadf_rejected_over_the_real_table :
    check_syscall (write_in (Z_to_bv 64 (2 ^ 32 + 1)) 4096 2 mem_ab)
        (with_copyins [(4096, 2)] (mkEffect (errno_ret EBADF) [] [])) demo_model
      = CheckReject := by
  simp only [check_syscall_write_in]
  exact check_write_fd_high_bits_ebadf_rejected

/-- THE NARROWING'S REFUSAL: a bare -EBADF at a0 = 2^32 + 1 is refused
through the dispatch.  `write` takes its descriptor as an `unsigned int`
(fs/read_write.c:746, Linux v6.18.46), so the call is `ksys_write` on fd 1,
which `demo_model` holds open, and `CLASS(fd_pos, f)(fd)` finds it (:729).  No kernel
answers -EBADF there while fd 1 is open for writing; `vfs_write` would answer
it for a file without `FMODE_WRITE` (:670-671), and the model's standard
output being writable is the premise bugs/channel-fds-assume-unidirectional-stdio.md
records.  A row that handed a0 to `check_write` whole would accept
this answer (`the_write_checker_itself_reads_the_whole_word`), so this is
the pin that fails when the row drops `fd32`.  Lean-only: Rocq's
`write_fd_high_bits_ebadf_rejected` offers the -EBADF with a copy-in.
kernel: fs/read_write.c:write,ksys_write@v6.18.46 -/
theorem write_whole_word_ebadf_rejected_over_the_real_table :
    check_syscall (write_in (Z_to_bv 64 (2 ^ 32 + 1)) 4096 2 mem_ab)
        (mkEffect (errno_ret EBADF) [] []) demo_model
      = CheckReject := by
  simp only [check_syscall_write_in]
  rfl

/-- The `write` conjunct of Rocq's `bit31_is_part_of_the_32_bit_arguments` through `check_syscall`: `check_write_bit31_fd_is_ebadf`'s
statement with the dispatch in place of the row, closed by
`check_syscall_write_in`.
kernel: fs/read_write.c:write,ksys_write@v6.18.46 -/
theorem bit31_is_part_of_the_32_bit_arguments_write_over_the_real_table :
    check_syscall (write_in (Z_to_bv 64 (2 ^ 31 + 1)) 4096 2 mem_ab)
        (mkEffect (errno_ret EBADF) [] []) demo_model
      = CheckOk demo_model [] := by
  simp only [check_syscall_write_in]
  exact check_write_bit31_fd_is_ebadf

/-- Rocq's `write_count_bound_declines_on_every_file_kind` through `check_syscall`, its
`FdFileW` conjuncts at `near_top` (over the bound, and at it); the mapped-buffer
`FdFileW` conjunct is the next theorem, and the `FdFileA`/`FdFileRW` ones are
not stated (file header). `check_write_count_bound_declines_on_the_write_only_kind`'s
statement with the dispatch in place of the row, closed by
`check_syscall_write_in`.
model: the decline is the inherited `rw_bytes_max` bound of Sys/Uaccess.lean and the at-bound answer the recorded divergence bugs/write-out-of-range-short-write.md -/
theorem write_count_bound_declines_on_every_file_kind_write_only_over_the_real_table :
    check_syscall (write_in 4 near_top (Z_to_bv 64 (rw_bytes_max + 1)) (mem_z_at near_top))
        (with_copyins [(near_top, 1)] (mkEffect 1 [] [])) write_model
      = CheckUnmodeled
    ∧ check_syscall (write_in 4 near_top (Z_to_bv 64 rw_bytes_max) (mem_z_at near_top))
        (with_copyins [(near_top, 1)] (mkEffect 1 [] [])) write_model
      = CheckOk (with_fds (fd_insert write_fds 4 (.FdFileW [103] 1))
          (with_fs (fs_set write_fs [103] [122]) write_model)) [] := by
  simp only [check_syscall_write_in]
  exact check_write_count_bound_declines_on_the_write_only_kind

/-- Rocq's `write_count_bound_declines_on_every_file_kind` through `check_syscall`, its
mapped-buffer `FdFileW` conjunct. `check_write_over_the_bound_at_a_mapped_buffer_is_judged`'s
statement with the dispatch in place of the row, closed by
`check_syscall_write_in`.
model: the file arm's readable-prefix answer, the recorded divergence bugs/write-file-prefault-before-v5-18-answers-a-chunk.md -/
theorem write_count_bound_declines_on_every_file_kind_mapped_over_the_real_table :
    check_syscall (write_in 4 4096 (Z_to_bv 64 (rw_bytes_max + 1)) (mem_z_at 4096))
        (with_copyins [(4096, 1)] (mkEffect 1 [] [])) write_model
      = CheckOk (with_fds (fd_insert write_fds 4 (.FdFileW [103] 1))
          (with_fs (fs_set write_fs [103] [122]) write_model)) [] := by
  simp only [check_syscall_write_in]
  exact check_write_over_the_bound_at_a_mapped_buffer_is_judged

/-- Rocq's `write_range_boundary_pins_the_three_file_kinds` through `check_syscall`, its
`FdFileW` conjunct; the `FdFileA`/`FdFileRW` ones are not stated (file
header). `check_write_range_boundary_pins_the_write_only_kind`'s
statement with the dispatch in place of the row, closed by
`check_syscall_write_in`.
model: the recorded divergence bugs/write-out-of-range-short-write.md, the write-only arm judging an out-of-range source by its readable prefix -/
theorem write_range_boundary_pins_the_three_file_kinds_write_only_over_the_real_table :
    check_syscall (write_in 4 near_top 8 (mem_z_at near_top))
        (with_copyins [(near_top, 1)] (mkEffect 1 [] [])) write_model
      = CheckOk (with_fds (fd_insert write_fds 4 (.FdFileW [103] 1))
          (with_fs (fs_set write_fs [103] [122]) write_model)) [] := by
  simp only [check_syscall_write_in]
  exact check_write_range_boundary_pins_the_write_only_kind

/-- The write half of Rocq's `create_write_updates_fs` (its `openat` half waits on that arm's registration) through `check_syscall`: `check_create_write_updates_fs_write_half`'s
statement with the dispatch in place of the row, closed by
`check_syscall_write_in`.
kernel: mm/filemap.c:generic_perform_write; fs/read_write.c:ksys_write@v6.18.46 -/
theorem create_write_updates_fs_write_half_over_the_real_table :
    check_syscall (write_in 4 4096 2 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        write_model
      = CheckOk (with_fds (fd_insert write_fds 4 (.FdFileW [103] 2))
          (with_fs (fs_set write_fs [103] [97, 98]) write_model)) [] := by
  simp only [check_syscall_write_in]
  exact check_create_write_updates_fs_write_half

/-- Rocq's `write_zero_len_past_eof_leaves_file_alone` through `check_syscall`: `check_write_zero_len_past_eof_leaves_file_alone`'s
statement with the dispatch in place of the row, closed by
`check_syscall_write_in`.
kernel: fs/read_write.c:generic_write_checks_count@v6.18.46 -/
theorem write_zero_len_past_eof_leaves_file_alone_over_the_real_table :
    check_syscall (write_in 3 4096 0 mem_none) (mkEffect 0 [] []) wpast_model
      = CheckOk wpast_model [] := by
  simp only [check_syscall_write_in]
  exact check_write_zero_len_past_eof_leaves_file_alone

/-- Rocq's `write_zero_len_rejects_zero_length_copyin` through `check_syscall`: `check_write_zero_len_rejects_zero_length_copyin`'s
statement with the dispatch in place of the row, closed by
`check_syscall_write_in`.
kernel: fs/read_write.c:generic_write_checks_count@v6.18.46 -/
theorem write_zero_len_rejects_zero_length_copyin_over_the_real_table :
    check_syscall (write_in 3 4096 0 mem_none) (with_copyins [(4096, 0)] (mkEffect 0 [] []))
        wpast_model
      = CheckReject := by
  simp only [check_syscall_write_in]
  exact check_write_zero_len_rejects_zero_length_copyin

/-- Rocq's `write_one_byte_past_eof_zero_fills` through `check_syscall`: `check_write_one_byte_past_eof_zero_fills`'s
statement with the dispatch in place of the row, closed by
`check_syscall_write_in`.
kernel: mm/filemap.c:generic_perform_write; mm/shmem.c:shmem_write_end@v6.18.46 -/
theorem write_one_byte_past_eof_zero_fills_over_the_real_table :
    check_syscall (write_in 3 4096 1 (mem_z_at 4096)) (with_copyins [(4096, 1)] (mkEffect 1 [] []))
        wpast_model
      = CheckOk (with_fds (fd_insert (m_fds wpast_model) 3 (.FdFileW [102] 5))
          (with_fs (fs_set (m_fs wpast_model) [102] [104, 105, 0, 0, 122]) wpast_model)) [] := by
  simp only [check_syscall_write_in]
  exact check_write_one_byte_past_eof_zero_fills

/-- Rocq's `write_zero_len_within_file_is_a_noop` through `check_syscall`: `check_write_zero_len_within_file_is_a_noop`'s
statement with the dispatch in place of the row, closed by
`check_syscall_write_in`.
kernel: fs/read_write.c:generic_write_checks_count@v6.18.46 -/
theorem write_zero_len_within_file_is_a_noop_over_the_real_table :
    check_syscall (write_in 3 4096 0 mem_none) (mkEffect 0 [] [])
        (with_fds (fd_insert (m_fds wpast_model) 3 (.FdFileW [102] 1)) wpast_model)
      = CheckOk (with_fds (fd_insert (m_fds wpast_model) 3 (.FdFileW [102] 1)) wpast_model) [] := by
  simp only [check_syscall_write_in]
  exact check_write_zero_len_within_file_is_a_noop

/-- Rocq's `write_channel_eintr_rejected` through `check_syscall`, both conjuncts:
`check_write_ab_events` and `check_write_channel_eintr_rejected` with the dispatch
in place of the row, closed by `check_syscall_write_in`.
model: the recorded divergence bugs/read-write-reject-an-interrupted-transfer.md, no channel outcome being an interrupted transfer -/
theorem write_channel_eintr_rejected_over_the_real_table :
    check_syscall (write_in 1 4096 2 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        demo_model
      = CheckOk demo_model [WriteEv 1 97, WriteEv 1 98]
    ∧ check_syscall (write_in 1 4096 2 mem_ab) (mkEffect (errno_ret EINTR) [] []) demo_model
      = CheckReject := by
  simp only [check_syscall_write_in]
  exact ⟨check_write_ab_events, check_write_channel_eintr_rejected⟩

/-- Rocq's `write_channel_epipe_rejected` through `check_syscall`, both conjuncts:
the one-byte delivery of `check_write_ab_short_delivery` and
`check_write_channel_epipe_rejected` with the dispatch in place of the row,
closed by `check_syscall_write_in`.
model: the recorded divergence bugs/write-channel-assumes-its-reader-is-alive.md -/
theorem write_channel_epipe_rejected_over_the_real_table :
    check_syscall (write_in 1 4096 2 mem_ab) (with_copyins [(4096, 1)] (mkEffect 1 [] []))
        demo_model
      = CheckOk demo_model [WriteEv 1 97]
    ∧ check_syscall (write_in 1 4096 2 mem_ab) (mkEffect (errno_ret EPIPE) [] []) demo_model
      = CheckReject := by
  simp only [check_syscall_write_in]
  exact ⟨check_write_ab_short_delivery.1, check_write_channel_epipe_rejected⟩

/-- Rocq's `file_write_short_rejected` through `check_syscall`, both conjuncts:
`check_file_write_fills_an_empty_file` (stating the whole post-model where Rocq
reads the file back) and `check_file_write_short_rejected` with the dispatch in
place of the row, closed by `check_syscall_write_in`.
model: the recorded divergence bugs/write-file-never-falls-short.md -/
theorem file_write_short_rejected_over_the_real_table :
    check_syscall (write_in 3 4096 2 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        readv_write_only_model
      = CheckOk (with_fds (fd_insert (m_fds readv_write_only_model) 3 (.FdFileW [102] 2))
          (with_fs (fs_set (m_fs readv_write_only_model) [102] [97, 98]) readv_write_only_model))
          []
    ∧ check_syscall (write_in 3 4096 2 mem_ab) (with_copyins [(4096, 1)] (mkEffect 1 [] []))
        readv_write_only_model
      = CheckReject := by
  simp only [check_syscall_write_in]
  exact ⟨check_file_write_fills_an_empty_file, check_file_write_short_rejected⟩

end WriteThroughTheTable

section PositionalThroughTheTable

/-! ## Rocq's pread64, pwrite64 and lseek examples through the real table

`check_syscall_lseek_in`, `check_syscall_pread64_in` and
`check_syscall_pwrite64_in` find `arm_lseek`, `arm_pread64` and
`arm_pwrite64` at their numbers and unfold to `PositionalAndSeek`'s
`check_lseek_row`, `check_pread64_row` and `check_pwrite64_row`.
Each Rocq example below is restated through the dispatch under its Rocq
name with `_over_the_real_table`, using the row-level twin's statement. -/

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
  (arm_lseek arm_pread64 arm_pwrite64 ca_check_arm_lseek ca_check_arm_pread64 ca_check_arm_pwrite64
    lookup_ca_checked_table_lseek lookup_ca_checked_table_pread64 lookup_ca_checked_table_pwrite64)
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs (check_syscall check_syscall_of_found)

/-- The dispatch at 62 is the lseek row: `lookup_ca` finds `arm_lseek` for
the number `lseek_in` carries, and `arm_lseek.ca_check` is `check_lseek` at
`fd32 a0`, `a1`, `whence32 a2`, which is `check_lseek_row`.
kernel: fs/read_write.c:lseek@v6.18.46 -/
theorem check_syscall_lseek_in (fd off whence : word)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (lseek_in fd off whence) eff m
      = check_lseek_row (lseek_in fd off whence) eff m := by
  rw [check_syscall_of_found (lseek_in fd off whence) eff m arm_lseek
        lookup_ca_checked_table_lseek, ca_check_arm_lseek]
  rfl

/-- The dispatch at 67 is the pread64 row: `lookup_ca` finds `arm_pread64`
for the number `pread_in` carries, and `arm_pread64.ca_check` is
`check_pread64` at `fd32 a0`, `a1`, `a2`, `a3`, which is `check_pread64_row`.
kernel: fs/read_write.c:pread64@v6.18.46 -/
theorem check_syscall_pread64_in (fd buf count pos : word) (wmem : word → Option byte)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (pread_in fd buf count pos wmem) eff m
      = check_pread64_row (pread_in fd buf count pos wmem) eff m := by
  rw [check_syscall_of_found (pread_in fd buf count pos wmem) eff m arm_pread64
        lookup_ca_checked_table_pread64, ca_check_arm_pread64]
  rfl

/-- The dispatch at 68 is the pwrite64 row: `lookup_ca` finds `arm_pwrite64`
for the number `pwrite_in` carries, and `arm_pwrite64.ca_check` is
`check_pwrite64` at `fd32 a0`, `a1`, `a2`, `a3`, which is `check_pwrite64_row`.
kernel: fs/read_write.c:pwrite64@v6.18.46 -/
theorem check_syscall_pwrite64_in (fd buf count pos : word) (mem : word → Option byte)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (pwrite_in fd buf count pos mem) eff m
      = check_pwrite64_row (pwrite_in fd buf count pos mem) eff m := by
  rw [check_syscall_of_found (pwrite_in fd buf count pos mem) eff m arm_pwrite64
        lookup_ca_checked_table_pwrite64, ca_check_arm_pwrite64]
  rfl

/-- Rocq's `lseek_channel_espipe` through `check_syscall`: the channel accepts -ESPIPE and refuses a successful seek.
kernel: fs/read_write.c:ksys_lseek,vfs_llseek; fs/open.c:stream_open@v6.18.46 -/
theorem lseek_channel_espipe_over_the_real_table :
    check_syscall (lseek_in 0 0 0) (mkEffect (errno_ret ESPIPE) [] []) lseek_model
      = CheckOk lseek_model []
    ∧ check_syscall (lseek_in 0 0 0) (mkEffect 0 [] []) lseek_model = CheckReject := by
  simp only [check_syscall_lseek_in]
  exact check_lseek_channel_espipe

/-- Rocq's `lseek_channel_bad_whence_is_einval_not_espipe` through `check_syscall`: a bad whence on the channel accepts -EINVAL and refuses -ESPIPE.
kernel: fs/read_write.c:ksys_lseek,vfs_llseek@v6.18.46 -/
theorem lseek_channel_bad_whence_is_einval_not_espipe_over_the_real_table :
    check_syscall (lseek_in 0 0 42) (mkEffect (errno_ret EINVAL) [] []) lseek_model
      = CheckOk lseek_model []
    ∧ check_syscall (lseek_in 0 0 42) (mkEffect (errno_ret ESPIPE) [] []) lseek_model
      = CheckReject := by
  simp only [check_syscall_lseek_in]
  exact check_lseek_channel_bad_whence_is_einval_not_espipe

/-- Rocq's `lseek_channel_seek_hole_is_espipe` through `check_syscall`: SEEK_HOLE passes the whence gate and reaches the channel's -ESPIPE.
kernel: fs/read_write.c:ksys_lseek,vfs_llseek@v6.18.46 -/
theorem lseek_channel_seek_hole_is_espipe_over_the_real_table :
    check_syscall (lseek_in 0 0 4) (mkEffect (errno_ret ESPIPE) [] []) lseek_model
      = CheckOk lseek_model [] := by
  simp only [check_syscall_lseek_in]
  exact check_lseek_channel_seek_hole_is_espipe

/-- Rocq's `lseek_seek_data_on_a_file_is_unmodeled` through `check_syscall`: SEEK_DATA and SEEK_HOLE on the file decline; the channel's SEEK_HOLE
and the file's SEEK_END retain their row-level answers.
kernel: mm/shmem.c:shmem_file_llseek; fs/read_write.c:ksys_lseek,vfs_llseek,generic_file_llseek_size@v6.18.46 -/
theorem lseek_seek_data_on_a_file_is_unmodeled_over_the_real_table :
    check_syscall (lseek_in 3 0 3) (mkEffect (errno_ret EINVAL) [] []) lseek_model = CheckUnmodeled
    ∧ check_syscall (lseek_in 3 0 4) (mkEffect 2 [] []) lseek_model = CheckUnmodeled
    ∧ check_syscall (lseek_in 0 0 4) (mkEffect (errno_ret ESPIPE) [] []) lseek_model
      = CheckOk lseek_model []
    ∧ check_syscall (lseek_in 3 0 2) (mkEffect 2 [] []) lseek_model
      = CheckOk (with_fds (fd_insert lseek_fds 3 (.FdFile [102] 2)) lseek_model) [] := by
  simp only [check_syscall_lseek_in]
  exact check_lseek_seek_data_on_a_file_is_unmodeled

/-- Rocq's `lseek_whence_high_bits_einval_rejected` through `check_syscall`: the high whence bits are discarded and the whole-word -EINVAL is refused.
kernel: fs/read_write.c:lseek,ksys_lseek,generic_file_llseek_size@v6.18.46 -/
theorem lseek_whence_high_bits_einval_rejected_over_the_real_table :
    check_syscall (lseek_in 3 0 (Z_to_bv 64 (2 ^ 32 + 2))) (mkEffect 2 [] []) lseek_model
      = CheckOk (with_fds (fd_insert lseek_fds 3 (.FdFile [102] 2)) lseek_model) []
    ∧ check_syscall (lseek_in 3 0 (Z_to_bv 64 (2 ^ 32 + 2))) (mkEffect (errno_ret EINVAL) [] [])
        lseek_model
      = CheckReject := by
  simp only [check_syscall_lseek_in]
  exact check_lseek_whence_high_bits_einval_rejected

/-- Rocq's `lseek_bad_fd_beats_a_bad_whence` through `check_syscall`: the closed descriptor's -EBADF precedes the invalid whence.
kernel: fs/read_write.c:ksys_lseek@v6.18.46 -/
theorem lseek_bad_fd_beats_a_bad_whence_over_the_real_table :
    check_syscall (lseek_in 9 0 42) (mkEffect (errno_ret EBADF) [] []) lseek_model
      = CheckOk lseek_model []
    ∧ check_syscall (lseek_in 9 0 42) (mkEffect (errno_ret EINVAL) [] []) lseek_model
      = CheckReject := by
  simp only [check_syscall_lseek_in]
  exact check_lseek_bad_fd_beats_a_bad_whence

/-- Rocq's `bit31_is_part_of_the_32_bit_arguments` through `check_syscall`: its lseek conjunct keeps bit 31 in the whence and accepts -EINVAL.
kernel: fs/read_write.c:lseek,ksys_lseek@v6.18.46 -/
theorem bit31_is_part_of_the_32_bit_arguments_lseek_over_the_real_table :
    check_syscall (lseek_in 3 5 (Z_to_bv 64 (2 ^ 31 + 2))) (mkEffect (errno_ret EINVAL) [] [])
        lseek_model
      = CheckOk lseek_model [] := by
  simp only [check_syscall_lseek_in]
  exact check_lseek_bit31_whence_is_einval

/-- Rocq's `lseek_on_a_pipe_end_is_espipe_but_whence_wins` through `check_syscall`: the row-level twin uses pipe ends 14 and 15 in `read_model`,
accepting -ESPIPE, refusing success, and testing the whence first.
kernel: fs/read_write.c:ksys_lseek,vfs_llseek; fs/pipe.c:create_pipe_files; fs/open.c:stream_open@v6.18.46 -/
theorem lseek_on_a_pipe_end_is_espipe_but_whence_wins_over_the_real_table :
    check_syscall (lseek_in 14 0 0) (mkEffect (errno_ret ESPIPE) [] []) read_model
      = CheckOk read_model []
    ∧ check_syscall (lseek_in 15 0 0) (mkEffect (errno_ret ESPIPE) [] []) read_model
      = CheckOk read_model []
    ∧ check_syscall (lseek_in 14 0 0) (mkEffect 0 [] []) read_model = CheckReject
    ∧ check_syscall (lseek_in 15 0 0) (mkEffect 0 [] []) read_model = CheckReject
    ∧ check_syscall (lseek_in 14 0 42) (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckOk read_model []
    ∧ check_syscall (lseek_in 14 0 42) (mkEffect (errno_ret ESPIPE) [] []) read_model
      = CheckReject := by
  simp only [check_syscall_lseek_in]
  exact check_lseek_on_a_pipe_end_is_espipe_but_whence_wins

/-- Rocq's `pwrite64_negative_pos_rejects_ebadf` through `check_syscall`: the negative position accepts -EINVAL before the closed descriptor
and refuses -EBADF.
kernel: fs/read_write.c:ksys_pwrite64@v6.18.46 -/
theorem pwrite64_negative_pos_rejects_ebadf_over_the_real_table :
    check_syscall (pwrite_in 5 4096 2 (Z_to_bv 64 (-1)) mem_ab)
        (mkEffect (errno_ret EINVAL) [] []) readv_write_only_model
      = CheckOk readv_write_only_model []
    ∧ check_syscall (pwrite_in 5 4096 2 (Z_to_bv 64 (-1)) mem_ab)
        (mkEffect (errno_ret EBADF) [] []) readv_write_only_model
      = CheckReject := by
  simp only [check_syscall_pwrite64_in]
  exact check_pwrite64_negative_pos_rejects_ebadf

/-- Rocq's `pwrite64_writes_at_the_named_position` through `check_syscall`: the row-level twin states the full post-model: the bytes land at
position 4 and the descriptor stays at offset 0; a one-byte return is refused.
kernel: fs/read_write.c:ksys_pwrite64,vfs_write; mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem pwrite64_writes_at_the_named_position_over_the_real_table :
    check_syscall (pwrite_in 3 4096 2 4 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        readv_write_only_model
      = CheckOk (with_fs (fs_set write_only_fs [102] [0, 0, 0, 0, 97, 98]) readv_write_only_model) []
    ∧ check_syscall (pwrite_in 3 4096 2 4 mem_ab) (with_copyins [(4096, 2)] (mkEffect 1 [] []))
        readv_write_only_model
      = CheckReject := by
  simp only [check_syscall_pwrite64_in]
  exact check_pwrite64_writes_at_the_named_position

/-- Rocq's `pwrite64_over_rw_bytes_max_is_judged` through `check_syscall`: the row-level twin accepts the two-byte readable prefix and refuses
a one-byte return, with the implementation limits documented beside that twin.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem pwrite64_over_rw_bytes_max_is_judged_over_the_real_table :
    check_syscall (pwrite_in 3 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 mem_ab)
        (with_copyins [(4096, 2)] (mkEffect 2 [] [])) readv_write_only_model
      = CheckOk (with_fs (fs_set write_only_fs [102] [97, 98]) readv_write_only_model) []
    ∧ check_syscall (pwrite_in 3 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 mem_ab)
        (with_copyins [(4096, 1)] (mkEffect 1 [] [])) readv_write_only_model
      = CheckReject := by
  simp only [check_syscall_pwrite64_in]
  exact check_pwrite64_over_rw_bytes_max_is_judged

/-- `check_pread64_fd_truncates_to_32_bits`'s first conjunct through
`check_syscall`: the dispatch answers a0 = 2^32 + 3 as fd 3.
kernel: fs/read_write.c:pread64,ksys_pread64@v6.18.46 -/
theorem pread64_fd_truncates_to_32_bits_over_the_real_table :
    check_syscall (pread_in (Z_to_bv 64 (2 ^ 32 + 3)) 4096 100 1 (wmem_first 1))
        (mkEffect 1 [(4096, [105])] []) read_model
      = CheckOk read_model [] := by
  simp only [check_syscall_pread64_in]
  exact check_pread64_fd_truncates_to_32_bits.1

/-- Through `check_syscall`, the bare -EBADF a row handing a0 over whole
would accept (no descriptor 2^32 + 3) is refused.
kernel: fs/read_write.c:pread64,ksys_pread64@v6.18.46 -/
theorem pread64_whole_word_ebadf_rejected_over_the_real_table :
    check_syscall (pread_in (Z_to_bv 64 (2 ^ 32 + 3)) 4096 100 1 (wmem_first 1))
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckReject := by
  simp only [check_syscall_pread64_in]
  rwp_norm

/-- `check_lseek_fd_truncates_to_32_bits` through `check_syscall`: the
dispatch answers a0 = 2^32 + 3 as fd 3.
kernel: fs/read_write.c:lseek,ksys_lseek@v6.18.46 -/
theorem lseek_fd_truncates_to_32_bits_over_the_real_table :
    check_syscall (lseek_in (Z_to_bv 64 (2 ^ 32 + 3)) 0 2) (mkEffect 2 [] []) lseek_model
      = CheckOk (with_fds (fd_insert lseek_fds 3 (.FdFile [102] 2)) lseek_model) [] := by
  simp only [check_syscall_lseek_in]
  exact check_lseek_fd_truncates_to_32_bits

/-- Through `check_syscall`, the bare -EBADF a row handing a0 over whole
would accept (no descriptor 2^32 + 3) is refused.
kernel: fs/read_write.c:lseek,ksys_lseek@v6.18.46 -/
theorem lseek_whole_word_ebadf_rejected_over_the_real_table :
    check_syscall (lseek_in (Z_to_bv 64 (2 ^ 32 + 3)) 0 2)
        (mkEffect (errno_ret EBADF) [] []) lseek_model
      = CheckReject := by
  simp only [check_syscall_lseek_in]
  rwp_norm

/-- Through `check_syscall`, a2 = 2^32 + SEEK_SET is answered as SEEK_SET:
the seek to offset 1 is accepted.
kernel: fs/read_write.c:lseek,ksys_lseek,generic_file_llseek_size@v6.18.46 -/
theorem lseek_whence_truncates_to_32_bits_over_the_real_table :
    check_syscall (lseek_in 3 1 (Z_to_bv 64 (2 ^ 32))) (mkEffect 1 [] []) lseek_model
      = CheckOk (with_fds (fd_insert lseek_fds 3 (.FdFile [102] 1)) lseek_model) [] := by
  simp only [check_syscall_lseek_in]
  rwp_norm

/-- Through `check_syscall`, the -EINVAL a row handing a2 over whole would
accept (2^32 is past `SEEK_MAX`) is refused.
kernel: fs/read_write.c:lseek,ksys_lseek,generic_file_llseek_size@v6.18.46 -/
theorem lseek_whole_word_einval_rejected_over_the_real_table :
    check_syscall (lseek_in 3 1 (Z_to_bv 64 (2 ^ 32)))
        (mkEffect (errno_ret EINVAL) [] []) lseek_model
      = CheckReject := by
  simp only [check_syscall_lseek_in]
  rwp_norm

end PositionalThroughTheTable
section ReadThroughTheTable

/-! ## Rocq's read examples through the real table

`RocqExamples` above restates on `check_read_row`, the arm's application
written out, the Rocq read `Example`s the header maps to a theorem (the
two `rdwr_` ones have no fixture yet, as the header says); this section
states them through `check_syscall`, as `WriteThroughTheTable` does the
write examples.  `check_syscall_read_in` finds `arm_read` at 63 and
unfolds its `ca_check` to `check_read_row`, and each of those examples is
then stated through the dispatch under its Rocq name with
`_over_the_real_table`, but for the one exception named below.  Two of
them also have `readv` conjuncts, which
the checked table has no row for; the section above leaves them out, and
so does this one.  The twin of `partial_destination_on_a_pipe_declines`
is named for the whole example although it states only the `read`
conjuncts (with this file's -EFAULT decline between them); the read half
of `readv_at_llong_max_is_einval_not_eof` is named for the row pin it
restates, `check_file_at_llong_max_still_answers_zero`, since that half
answers 0 and refuses -EINVAL, where the example's name speaks of its
`readv` half.

`read_fd_truncates_to_32_bits_over_the_real_table` is the pin on the
narrowing: a0 = 2^32 is answered as fd 0 through the dispatch, and a bare
-EBADF there is refused.  A table row that handed a0 over whole would
accept that -EBADF, as `the_checker_itself_reads_the_whole_word` shows of
the checker. -/

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table (arm_read ca_check_arm_read)
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs (check_syscall check_syscall_of_found)

/-- The dispatch at 63 is the read row: `lookup_ca` finds `arm_read` for
the number `read_in` carries, and `arm_read.ca_check` is `check_read` at
`fd32 a0`, `a1`, `a2`, which is `check_read_row`.  This is the table-side
reading of `SYSCALL_DEFINE3(read, unsigned int, fd, …)`
(fs/read_write.c:722, Linux v6.18.46).
kernel: fs/read_write.c:read@v6.18.46 -/
theorem check_syscall_read_in (fd buf count : word) (wmem : word → Option byte)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (read_in fd buf count wmem) eff m
      = check_read_row (read_in fd buf count wmem) eff m := by
  rw [check_syscall_of_found _ _ _ arm_read rfl, ca_check_arm_read]
  rfl

/-- Rocq's `read_bad_fd_ebadf` through `check_syscall`:
`check_read_bad_fd_ebadf`'s statement with the dispatch in place of the row,
closed by `check_syscall_read_in`.
kernel: fs/read_write.c:ksys_read@v6.18.46 -/
theorem read_bad_fd_ebadf_over_the_real_table :
    check_syscall (read_in 5 4096 16 wmem_none) (mkEffect (errno_ret EBADF) [] []) demo_model
      = CheckOk demo_model [] := by
  simp only [check_syscall_read_in]
  exact check_read_bad_fd_ebadf

/-- Rocq's `read_bad_fd_success_rejected` through `check_syscall`:
`check_read_bad_fd_success_rejected`'s statement with the dispatch in place
of the row, closed by `check_syscall_read_in`.
kernel: fs/read_write.c:ksys_read@v6.18.46 -/
theorem read_bad_fd_success_rejected_over_the_real_table :
    check_syscall (read_in 5 4096 16 wmem_none) (mkEffect 4 [(4096, [1, 2, 3, 4])] []) demo_model
      = CheckReject := by
  simp only [check_syscall_read_in]
  exact check_read_bad_fd_success_rejected

/-- Rocq's `read_fd_truncates_to_32_bits` through `check_syscall`:
`check_read_fd_truncates_to_32_bits`'s statement with the dispatch in place
of the row, closed by `check_syscall_read_in`.
kernel: fs/read_write.c:read,ksys_read@v6.18.46 -/
theorem read_fd_truncates_to_32_bits_over_the_real_table :
    check_syscall (read_in (Z_to_bv 64 (2 ^ 32)) 4096 16 wmem_none) (mkEffect 0 [] []) demo_model
      = CheckOk demo_model []
    ∧ check_syscall (read_in (Z_to_bv 64 (2 ^ 32)) 4096 16 wmem_none)
        (mkEffect (errno_ret EBADF) [] []) demo_model
      = CheckReject := by
  simp only [check_syscall_read_in]
  exact check_read_fd_truncates_to_32_bits

/-- Rocq's `read_channel_eintr_rejected` through `check_syscall`:
`check_read_channel_eintr_rejected`'s statement with the dispatch in place
of the row, closed by `check_syscall_read_in`.
kernel: fs/pipe.c:anon_pipe_read; arch/riscv/kernel/signal.c:arch_do_signal_or_restart@v6.18.46 -/
theorem read_channel_eintr_rejected_over_the_real_table :
    check_syscall (read_in 0 4096 1 (wmem_first 1)) (mkEffect 1 [(4096, [120])] [])
        (with_stdin (ICons 120 IEof) demo_model)
      = CheckOk (with_stdin IEof demo_model) [ReadEv 0 120]
    ∧ check_syscall (read_in 0 4096 1 (wmem_first 1)) (mkEffect (errno_ret EINTR) [] [])
        (with_stdin (ICons 120 IEof) demo_model)
      = CheckReject := by
  simp only [check_syscall_read_in]
  exact check_read_channel_eintr_rejected

/-- Rocq's `pipe_read_over_rw_bytes_max_is_judged` through `check_syscall`:
`check_pipe_read_over_rw_bytes_max_is_judged`'s statement with the dispatch
in place of the row, closed by `check_syscall_read_in`.
kernel: fs/pipe.c:anon_pipe_read; fs/read_write.c:vfs_read@v6.18.46 -/
theorem pipe_read_over_rw_bytes_max_is_judged_over_the_real_table :
    check_syscall (read_in 14 4096 (Z_to_bv 64 (rw_bytes_max + 1)) (wmem_first 2))
        (mkEffect 2 [(4096, [97, 98])] []) read_model
      = CheckOk (with_pipes [(0, ([], 2)), (1, ([], 0)), (2, ([], 3))] read_model) []
    ∧ check_syscall (read_in 14 4096 (Z_to_bv 64 (rw_bytes_max + 1)) (wmem_first 2))
        (mkEffect 1 [(4096, [97])] []) read_model
      = CheckReject := by
  simp only [check_syscall_read_in]
  exact check_pipe_read_over_rw_bytes_max_is_judged

/-- Rocq's `partial_destination_on_a_pipe_declines` through `check_syscall`,
its two `read` conjuncts: `check_stdin_partial_destination_declines`'s
statement with the dispatch in place of the row, closed by
`check_syscall_read_in`. They are the first and third conjuncts here; the
-EFAULT decline between them is this file's own.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem read_partial_destination_on_a_pipe_declines_over_the_real_table :
    check_syscall (read_in 0 4096 100 (wmem_first 4))
        (mkEffect 4 [(4096, [104, 101, 108, 108])] []) (with_stdin hello_stdin demo_model)
      = CheckUnmodeled
    ∧ check_syscall (read_in 0 4096 100 (wmem_first 4)) (mkEffect (errno_ret EFAULT) [] [])
        (with_stdin hello_stdin demo_model)
      = CheckUnmodeled
    ∧ check_syscall (read_in 0 4096 100 (wmem_first 5))
        (mkEffect 5 [(4096, [104, 101, 108, 108, 111])] []) (with_stdin hello_stdin demo_model)
      = CheckOk (with_stdin IEof demo_model)
          [ReadEv 0 104, ReadEv 0 101, ReadEv 0 108, ReadEv 0 108, ReadEv 0 111] := by
  simp only [check_syscall_read_in]
  exact check_stdin_partial_destination_declines

/-- Rocq's `readv_at_llong_max_is_einval_not_eof` through `check_syscall`,
its two `read` conjuncts: `check_file_at_llong_max_still_answers_zero`'s
statement with the dispatch in place of the row, closed by
`check_syscall_read_in`. This is the recorded divergence of
bugs/read-write-position-past-llong-max-answers-zero.md, and the twin flips
with its pin: the day the file arm gains the position test, the first
conjunct turns `CheckReject` and the second `CheckOk`.
model: the recorded divergence bugs/read-write-position-past-llong-max-answers-zero.md, restated through the dispatch so that closing it flips this pin; not a claim about Linux, which answers -EINVAL here -/
theorem file_at_llong_max_still_answers_zero_over_the_real_table :
    check_syscall (read_in 3 4096 1 (wmem_first 1)) (mkEffect 0 [] []) llong_max_model
      = CheckOk llong_max_model []
    ∧ check_syscall (read_in 3 4096 1 (wmem_first 1)) (mkEffect (errno_ret EINVAL) [] [])
        llong_max_model
      = CheckReject := by
  simp only [check_syscall_read_in]
  exact check_file_at_llong_max_still_answers_zero

end ReadThroughTheTable

-- lean-port sentinel: ticket C-Fs-ReadWrite-readv-writev appends below this line

section Vectored

/-! ## readv (65) and writev (66): the checkers and their witnesses

T139/#1439 changes the count and descriptor-order boundary. QEMU 11.1.1
runs `lock_iovec` before the host call in `TARGET_NR_readv` and
`TARGET_NR_writev` (linux-user/syscall.c), while Linux v6.18.46 resolves
the descriptor and, from v6.8, its mode before `import_iovec` (fs/read_write.c,
`do_readv`, `vfs_readv`, `do_writev`, `vfs_writev`). The shared -EBADF
shape for a closed fd uses a raw count in 1..IOV_MAX, a readable descriptor
array with nonnegative lengths, and an empty first entry; an open wrong-mode
fd additionally needs count ≤ 8 and every uncapped range in the address space. The first-entry bound
avoids claiming that a whole-buffer lock succeeds from a prefix read.
A count whose raw value exceeds IOV_MAX but whose low32 value fits is
also declined on an open descriptor.

Decline pins pair the all-effect verdict with a refutation of the former
certain answer. Still-answered controls keep the empty-first-entry
-EBADF and normal-count transfers observable. Each declaration cites either its matching probe or the kernel source;
the high-base probes accept failure from either kernel order.

Linux v4.17 through v6.7 imports an open descriptor's array before its mode
check (fs/read_write.c, vfs_readv / vfs_writev, read at v6.6:913,930;
do_iter_read / do_iter_write checks the mode afterwards). The moves
b8e1425bae85 and 1c8aa833034a put that check first in v6.8. Thus even an
empty first entry needs every uncapped range valid, including zero-length
ranges, and at most UIO_FASTIOV entries to avoid an import-first error.
The new pins below isolate that range test and the nine-entry allocation band.

The descriptor-copy and delivery ledgers remain explicit constants in
the pins. Computing them with the same helper as the checker would make
the test agree with a wrong helper. The older bulk-copy ledger and the
other inherited transfer limitations remain separate from T139; their
source arguments are in the corresponding spec and per-case comments.

`rwv_norm` and `rwv_witness_norm` unfold the checker or witness while
keeping the ground byte maps folded, then reduce their closed gates.
The raw count reaches the new gates before `iovcnt32` is used by the
ordinary import. -/

/-- `check_readv` as the dispatcher applies it: the descriptor narrowed
by `fd32` from a0, `iov` and `iovcnt` whole from a1 and a2 — the row for
65 in `Sys/SyscallTable.lean`.  The count is narrowed inside the checker
(`iovcnt32`), as it is inside the spec. -/
def check_readv_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_readv i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m

/-- `check_writev` the same way — the row for 66. -/
def check_writev_row (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_writev i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m

/-- `readv_witness` applied the same way. -/
def readv_witness_row (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  readv_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

/-- `writev_witness` applied the same way. -/
def writev_witness_row (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  writev_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

/-- `check_norm` over the two rows; the section header says why the pass
is the same. -/
scoped macro "rwv_norm" : tactic =>
  `(tactic| (simp -zeta only [check_readv_row, check_writev_row, check_readv, check_writev,
    check_readv_imported, stream_take_z_eq, net_take_z_eq]; first | done | rfl | (constructor <;> first | rfl | (intro h; cases h))))

/-- `witness_norm` over the two witness rows. -/
scoped macro "rwv_witness_norm" : tactic =>
  `(tactic| (simp -zeta only [readv_witness_row, writev_witness_row, readv_witness,
    writev_witness, stream_take_z_eq, net_take_z_eq]; first | done | rfl))

/-! ### The rows are the registry arms -/

/-- The readv row IS `readv_arm`'s application: `check_readv_sound_ok`
lands in that arm's `sa_spec` only if the row narrows each argument as
`Sys/Registry/Fs/ReadWrite.lean` does.  `SYSCALL_DEFINE3(readv, unsigned
long, fd, …, unsigned long, vlen)` (fs/read_write.c:1162, Linux v6.18.46)
takes all three whole; the descriptor is narrowed where `do_readv` hands
it to `CLASS(fd_pos, f)(fd)` (fs/read_write.c:1071), whose constructor
takes an `int` (include/linux/file.h:85, Linux v6.18.46), and the count
where `vfs_readv` hands it to `import_iovec`'s `unsigned nr_segs`
(lib/iov_iter.c:1424-1425, Linux v6.18.46), inside the spec.
kernel: fs/read_write.c:readv,do_readv@v6.18.46 -/
theorem readv_row_is_the_arm (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_readv_row i eff m = CheckOk m' evs) :
    (Sys.Registry.Fs.ReadWrite.readv_arm).sa_spec i m (Ok eff m' evs) :=
  check_readv_sound_ok _ _ _ _ _ _ _ _ h

/-- The writev row IS `writev_arm`'s application, by the same argument:
`SYSCALL_DEFINE3(writev, unsigned long, fd, …)` (fs/read_write.c:1168,
Linux v6.18.46) into `do_writev`'s `CLASS(fd_pos, f)(fd)`
(fs/read_write.c:1094).
kernel: fs/read_write.c:writev,do_writev@v6.18.46 -/
theorem writev_row_is_the_arm (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_writev_row i eff m = CheckOk m' evs) :
    (Sys.Registry.Fs.ReadWrite.writev_arm).sa_spec i m (Ok eff m' evs) :=
  check_writev_sound_ok _ _ _ _ _ _ _ _ h

/-- THE DESCRIPTOR IS NARROWED TO 32 BITS before it is looked up: 2^32 + 1
is standard output and 2^32 standard input, so the writev of "ab"
through 2^32 + 1 is the two-byte delivery on channel 1 and the readv
through 2^32 is standard input's end-of-input 0, and the -EBADF an
unnarrowed lookup would answer is refused on each.  `do_writev` and
`do_readv` hand their `unsigned long` to `CLASS(fd_pos, f)(fd)`
(fs/read_write.c:1094, :1071, Linux v6.18.46), whose constructor takes an
`int` (include/linux/file.h:85).  qemu-user locks the readv destination
before the read (`lock_iovec`, linux-user/syscall.c:11888, QEMU 11.1.1),
so on this unwritable one it answers -EFAULT where Linux reads end of
input and answers 0; the model refuses that in Linux's favour (the last
conjunct).  Linux's import has no -EFAULT for it: `import_ubuf` refuses
only a range `access_ok` rejects (lib/iov_iter.c:1437-1438, Linux
v6.18.46), and `{4096, 1}` lies inside the address space.
kernel: fs/read_write.c:do_writev,do_readv; lib/iov_iter.c:import_ubuf@v6.18.46 -/
theorem check_vectored_fd_truncates_to_32_bits :
    check_writev_row (writev_in (Z_to_bv 64 (2 ^ 32 + 1)) 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) demo_model
      = CheckOk demo_model [WriteEv 1 97, WriteEv 1 98]
    ∧ check_writev_row (writev_in (Z_to_bv 64 (2 ^ 32 + 1)) 8192 2 mem_writev_ab)
        (mkEffect (errno_ret EBADF) [] []) demo_model
      = CheckReject
    ∧ check_readv_row (readv_in (Z_to_bv 64 (2 ^ 32)) 8192 1 mem_readv_iov wmem_none)
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) demo_model
      = CheckOk demo_model []
    ∧ check_readv_row (readv_in (Z_to_bv 64 (2 ^ 32)) 8192 1 mem_readv_iov wmem_none)
        (mkEffect (errno_ret EBADF) [] []) demo_model
      = CheckReject
    ∧ check_readv_row (readv_in (Z_to_bv 64 (2 ^ 32)) 8192 1 mem_readv_iov wmem_none)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) demo_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-- Readv on closed fd 30 uses count 1 and a readable {0,0} entry at 8192. The empty entry lets
qemu-user reach the host fd check, matching Linux's -EBADF; the checker accepts -EBADF and
rejects 0.
probe: testing/syscall-check/tests/readv_spec.c#conform -- badfd -/
theorem check_readv_closed_fd_empty_first_entry_is_ebadf :
    check_readv_row (readv_in 30 8192 1 mem_readv_eight_zero wmem_none) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model []
    ∧ check_readv_row (readv_in 30 8192 1 mem_readv_eight_zero wmem_none) (mkEffect 0 [] []) read_model = CheckReject := by
  constructor <;> rwv_norm

/-- Readv on closed fd 30 uses count 0 and an unused unreadable array at 8192. Linux returns
-EBADF and qemu-user returns 0; the checker declines any supplied effect and cannot accept it as
an unchanged-model outcome.
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv -- badfdcnt0 -/
theorem check_readv_closed_zero_declines (eff : SyscallEffect) :
    (check_readv_row (readv_in 30 8192 0 mem_none wmem_none) eff read_model
      = CheckUnmodeled
      ∧ check_readv_row (readv_in 30 8192 0 mem_none wmem_none) eff read_model ≠ CheckOk read_model []) := by
  rwv_norm

/-- Readv on closed fd 30 uses count 0 and an unused unreadable array at 8192. Linux returns
-EBADF and qemu-user returns 0; the pin rules out a successful checker verdict for the offered
-EBADF effect, regardless of the resulting model or events.
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv -- badfdcnt0 -/
theorem check_readv_closed_zero_old_answer_refuted (m' : Model) (evs : List event) :
    check_readv_row (readv_in 30 8192 0 mem_none wmem_none) (mkEffect (errno_ret EBADF) [] []) read_model
      ≠ CheckOk m' evs := by
  rw [(check_readv_closed_zero_declines _).1]
  intro h
  cases h

/-- Readv on closed fd 30 uses count 2^32+2 beside eight readable {0,0} entries at 8192. Linux
returns -EBADF and qemu-user rejects the raw count with -EINVAL; the checker declines any
supplied effect and cannot accept it as an unchanged-model outcome.
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv -- badfdwide -/
theorem check_readv_closed_wide_declines (eff : SyscallEffect) :
    (check_readv_row (readv_in 30 8192 (Z_to_bv 64 (2 ^ 32 + 2)) mem_readv_eight_zero wmem_none) eff read_model
      = CheckUnmodeled
      ∧ check_readv_row (readv_in 30 8192 (Z_to_bv 64 (2 ^ 32 + 2)) mem_readv_eight_zero wmem_none) eff read_model ≠ CheckOk read_model []) := by
  rwv_norm

/-- Readv on closed fd 30 uses count 2^32+2 beside eight readable {0,0} entries at 8192. Linux
returns -EBADF and qemu-user rejects the raw count with -EINVAL; the pin rules out a successful
checker verdict for the offered -EBADF effect, regardless of the resulting model or events.
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv -- badfdwide -/
theorem check_readv_closed_wide_old_answer_refuted (m' : Model) (evs : List event) :
    check_readv_row (readv_in 30 8192 (Z_to_bv 64 (2 ^ 32 + 2)) mem_readv_eight_zero wmem_none) (mkEffect (errno_ret EBADF) [] []) read_model
      ≠ CheckOk m' evs := by
  rw [(check_readv_closed_wide_declines _).1]
  intro h
  cases h

/-- Readv on closed fd 30 uses count 1 and an unreadable array at 8192. Linux returns -EBADF and
qemu-user returns -EFAULT; the checker declines any supplied effect and cannot accept it as an
unchanged-model outcome.
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv -- badfdiov -/
theorem check_readv_closed_unreadable_declines (eff : SyscallEffect) :
    (check_readv_row (readv_in 30 8192 1 mem_none wmem_none) eff read_model
      = CheckUnmodeled
      ∧ check_readv_row (readv_in 30 8192 1 mem_none wmem_none) eff read_model ≠ CheckOk read_model []) := by
  rwv_norm

/-- Readv on closed fd 30 uses count 1 and an unreadable array at 8192. Linux returns -EBADF and
qemu-user returns -EFAULT; the pin rules out a successful checker verdict for the offered -EBADF
effect, regardless of the resulting model or events.
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv -- badfdiov -/
theorem check_readv_closed_unreadable_old_answer_refuted (m' : Model) (evs : List event) :
    check_readv_row (readv_in 30 8192 1 mem_none wmem_none) (mkEffect (errno_ret EBADF) [] []) read_model
      ≠ CheckOk m' evs := by
  rw [(check_readv_closed_unreadable_declines _).1]
  intro h
  cases h

/-- Readv on closed fd 30 uses count 2 and {4096,2},{4098,3} at 8192, with no writable
destination bytes. The checker declines any supplied effect and cannot accept it as an
unchanged-model outcome.
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv -- badfdnonempty -/
theorem check_readv_closed_nonempty_declines (eff : SyscallEffect) :
    (check_readv_row (readv_in 30 8192 2 iov_2_3 wmem_none) eff read_model
      = CheckUnmodeled
      ∧ check_readv_row (readv_in 30 8192 2 iov_2_3 wmem_none) eff read_model ≠ CheckOk read_model []) := by
  rwv_norm

/-- Readv on closed fd 30 uses count 2 and {4096,2},{4098,3} at 8192, with no writable
destination bytes. The pin rules out a successful checker verdict for the offered -EBADF effect,
regardless of the resulting model or events.
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv -- badfdnonempty -/
theorem check_readv_closed_nonempty_old_answer_refuted (m' : Model) (evs : List event) :
    check_readv_row (readv_in 30 8192 2 iov_2_3 wmem_none) (mkEffect (errno_ret EBADF) [] []) read_model
      ≠ CheckOk m' evs := by
  rw [(check_readv_closed_nonempty_declines _).1]
  intro h
  cases h

/-- Writev on closed fd 30 uses count 1 and a readable {0,0} entry at 8192. The empty entry lets
qemu-user reach the host fd check, matching Linux's -EBADF; the checker accepts -EBADF and
rejects 0.
probe: testing/syscall-check/tests/writev_adversarial.c#conform -- badfdempty -/
theorem check_writev_closed_fd_empty_first_entry_is_ebadf :
    check_writev_row (writev_in 30 8192 1 mem_readv_eight_zero) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model []
    ∧ check_writev_row (writev_in 30 8192 1 mem_readv_eight_zero) (mkEffect 0 [] []) read_model = CheckReject := by
  constructor <;> rwv_norm

/-- Writev on closed fd 30 uses count 0 and an unused unreadable array at 8192. Linux returns
-EBADF and qemu-user returns 0; the checker declines any supplied effect and cannot accept it as
an unchanged-model outcome.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- badfdcnt0 -/
theorem check_writev_closed_zero_declines (eff : SyscallEffect) :
    (check_writev_row (writev_in 30 8192 0 mem_none) eff read_model
      = CheckUnmodeled
      ∧ check_writev_row (writev_in 30 8192 0 mem_none) eff read_model ≠ CheckOk read_model []) := by
  rwv_norm

/-- Writev on closed fd 30 uses count 0 and an unused unreadable array at 8192. Linux returns
-EBADF and qemu-user returns 0; the pin rules out a successful checker verdict for the offered
-EBADF effect, regardless of the resulting model or events.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- badfdcnt0 -/
theorem check_writev_closed_zero_old_answer_refuted (m' : Model) (evs : List event) :
    check_writev_row (writev_in 30 8192 0 mem_none) (mkEffect (errno_ret EBADF) [] []) read_model
      ≠ CheckOk m' evs := by
  rw [(check_writev_closed_zero_declines _).1]
  intro h
  cases h

/-- Writev on closed fd 30 uses count 2^32+2 beside eight readable {0,0} entries at 8192. Linux
returns -EBADF and qemu-user rejects the raw count with -EINVAL; the checker declines any
supplied effect and cannot accept it as an unchanged-model outcome.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- badfdwide -/
theorem check_writev_closed_wide_declines (eff : SyscallEffect) :
    (check_writev_row (writev_in 30 8192 (Z_to_bv 64 (2 ^ 32 + 2)) mem_readv_eight_zero) eff read_model
      = CheckUnmodeled
      ∧ check_writev_row (writev_in 30 8192 (Z_to_bv 64 (2 ^ 32 + 2)) mem_readv_eight_zero) eff read_model ≠ CheckOk read_model []) := by
  rwv_norm

/-- Writev on closed fd 30 uses count 2^32+2 beside eight readable {0,0} entries at 8192. Linux
returns -EBADF and qemu-user rejects the raw count with -EINVAL; the pin rules out a successful
checker verdict for the offered -EBADF effect, regardless of the resulting model or events.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- badfdwide -/
theorem check_writev_closed_wide_old_answer_refuted (m' : Model) (evs : List event) :
    check_writev_row (writev_in 30 8192 (Z_to_bv 64 (2 ^ 32 + 2)) mem_readv_eight_zero) (mkEffect (errno_ret EBADF) [] []) read_model
      ≠ CheckOk m' evs := by
  rw [(check_writev_closed_wide_declines _).1]
  intro h
  cases h

/-- Writev on closed fd 30 uses count 1 and an unreadable array at 8192. Linux returns -EBADF
and qemu-user returns -EFAULT; the checker declines any supplied effect and cannot accept it as
an unchanged-model outcome.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- badfdiov -/
theorem check_writev_closed_unreadable_declines (eff : SyscallEffect) :
    (check_writev_row (writev_in 30 8192 1 mem_none) eff read_model
      = CheckUnmodeled
      ∧ check_writev_row (writev_in 30 8192 1 mem_none) eff read_model ≠ CheckOk read_model []) := by
  rwv_norm

/-- Writev on closed fd 30 uses count 1 and an unreadable array at 8192. Linux returns -EBADF
and qemu-user returns -EFAULT; the pin rules out a successful checker verdict for the offered
-EBADF effect, regardless of the resulting model or events.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- badfdiov -/
theorem check_writev_closed_unreadable_old_answer_refuted (m' : Model) (evs : List event) :
    check_writev_row (writev_in 30 8192 1 mem_none) (mkEffect (errno_ret EBADF) [] []) read_model
      ≠ CheckOk m' evs := by
  rw [(check_writev_closed_unreadable_declines _).1]
  intro h
  cases h

/-- Writev on closed fd 30 uses count 2 and {4096,2},{4098,3} at 8192, with no readable source
bytes. The checker declines any supplied effect and cannot accept it as an unchanged-model
outcome.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- badfdnonempty -/
theorem check_writev_closed_nonempty_declines (eff : SyscallEffect) :
    (check_writev_row (writev_in 30 8192 2 iov_2_3) eff read_model
      = CheckUnmodeled
      ∧ check_writev_row (writev_in 30 8192 2 iov_2_3) eff read_model ≠ CheckOk read_model []) := by
  rwv_norm

/-- Writev on closed fd 30 uses count 2 and {4096,2},{4098,3} at 8192, with no readable source
bytes. The pin rules out a successful checker verdict for the offered -EBADF effect, regardless
of the resulting model or events.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- badfdnonempty -/
theorem check_writev_closed_nonempty_old_answer_refuted (m' : Model) (evs : List event) :
    check_writev_row (writev_in 30 8192 2 iov_2_3) (mkEffect (errno_ret EBADF) [] []) read_model
      ≠ CheckOk m' evs := by
  rw [(check_writev_closed_nonempty_declines _).1]
  intro h
  cases h

/-- Readv on closed fd 30 uses count 2 and readable {0,0},{0,1} entries at 8192. The empty first
entry and nonnegative lengths let qemu-user reach the host fd check, matching Linux's -EBADF
despite the later positive length; the pin accepts -EBADF and rejects 0.
probe: testing/syscall-check/tests/readv_spec.c#conform -- badfdlater -/
theorem check_readv_closed_empty_first_positive_later_is_ebadf :
    check_readv_row (readv_in 30 8192 2 (mem_iov_pair 0 0 0 1) wmem_none) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model []
    ∧ check_readv_row (readv_in 30 8192 2 (mem_iov_pair 0 0 0 1) wmem_none) (mkEffect 0 [] []) read_model = CheckReject := by
  constructor <;> rwv_norm

/-- Readv on closed fd 30 uses count 2 and {0,0},{0,2^63} at 8192. Linux returns -EBADF but
qemu-user rejects the second entry's negative signed length with -EINVAL, so the checker
declines any supplied effect.
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv -- badfdlaterneg -/
theorem check_readv_closed_empty_first_negative_later_declines (eff : SyscallEffect) :
    (check_readv_row (readv_in 30 8192 2 (mem_iov_pair 0 0 0 (Z_to_bv 64 (2 ^ 63))) wmem_none) eff read_model
      = CheckUnmodeled
      ∧ check_readv_row (readv_in 30 8192 2 (mem_iov_pair 0 0 0 (Z_to_bv 64 (2 ^ 63))) wmem_none) eff read_model ≠ CheckOk read_model []) := by
  rwv_norm

/-- Writev on closed fd 30 uses count 2 and readable {0,0},{0,1} entries at 8192. The empty
first entry and nonnegative lengths let qemu-user reach the host fd check, matching Linux's
-EBADF despite the later positive length; the pin accepts -EBADF and rejects 0.
probe: testing/syscall-check/tests/writev_adversarial.c#conform -- badfdlater -/
theorem check_writev_closed_empty_first_positive_later_is_ebadf :
    check_writev_row (writev_in 30 8192 2 (mem_iov_pair 0 0 0 1)) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model []
    ∧ check_writev_row (writev_in 30 8192 2 (mem_iov_pair 0 0 0 1)) (mkEffect 0 [] []) read_model = CheckReject := by
  constructor <;> rwv_norm

/-- Writev on closed fd 30 uses count 2 and {0,0},{0,2^63} at 8192. Linux returns -EBADF but
qemu-user rejects the second entry's negative signed length with -EINVAL, so the checker
declines any supplied effect.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- badfdlaterneg -/
theorem check_writev_closed_empty_first_negative_later_declines (eff : SyscallEffect) :
    (check_writev_row (writev_in 30 8192 2 (mem_iov_pair 0 0 0 (Z_to_bv 64 (2 ^ 63)))) eff read_model
      = CheckUnmodeled
      ∧ check_writev_row (writev_in 30 8192 2 (mem_iov_pair 0 0 0 (Z_to_bv 64 (2 ^ 63)))) eff read_model ≠ CheckOk read_model []) := by
  rwv_norm

/-! ### Rocq's writev examples, on the checker -/

/-- WRITEV OF TWO ONE-BYTE DESCRIPTORS IS THE WRITE OF THEIR TWO BYTES: the
same verdict as `write(1, "ab", 2)`, one event per byte, the ledger the
two descriptor reads and the two source bytes.  The iterators differ —
`write` hands the file's `->write_iter` an `ITER_UBUF` over its one
buffer (`new_sync_write`, fs/read_write.c:591, Linux v6.18.46) and
`do_writev` (fs/read_write.c:1091-1112) an `ITER_IOVEC` over the two
entries (`__import_iovec`, lib/iov_iter.c:1394, into `iov_iter_init`,
:168) — but the write operation is the same one and copies the same
bytes in the same order through either, so the delivered bytes and the
events do not depend on how the source was split.
kernel: fs/read_write.c:do_writev,vfs_writev,new_sync_write; lib/iov_iter.c:__import_iovec,iov_iter_init@v6.18.46 -/
theorem check_writev_two_iovecs_equals_one_write :
    check_writev_row (writev_in 1 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) demo_model
      = check_write_row (write_in 1 4096 2 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
          demo_model
    ∧ check_writev_row (writev_in 1 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) demo_model
      = CheckOk demo_model [WriteEv 1 97, WriteEv 1 98] := by
  refine ⟨?_, ?_⟩ <;> rwv_norm

/-- On stdout fd 1 with {4096,1},{4097,1} over readable "ab", Linux narrows counts 2^32+2 and
2^32 to two and zero, whereas qemu-user returns -EINVAL; the checker declines the offered two-
byte and zero results. Counts 1025 and 2^64-1 exceed IOV_MAX in both readings, so their shared
-EINVAL controls are accepted.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- raw2 -/
theorem check_writev_wide_iovcnt_is_unmodeled :
    (check_writev_row (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 2)) mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) demo_model
      = CheckUnmodeled
      ∧ check_writev_row (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 2)) mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) demo_model ≠ CheckOk demo_model [WriteEv 1 97, WriteEv 1 98])
    ∧ check_writev_row (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32)) mem_writev_ab) (mkEffect 0 [] [])
        demo_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 1 8192 1025 mem_writev_ab) (mkEffect (errno_ret EINVAL) [] [])
        demo_model
      = CheckOk demo_model []
    ∧ check_writev_row (writev_in 1 8192 (Z_to_bv 64 (two_pow_64 - 1)) mem_writev_ab)
        (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckOk demo_model [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-- Writev with count 2^32 and an unreadable array at 8192 returns 0 on pipe write end fd 15 and
-EBADF on read end fd 14 in Linux, while qemu-user returns -EINVAL on either fd. The pin
declines the offered 0, -EINVAL and 5 on fd 15 and -EBADF, 0 and -EINVAL on fd 14.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- raw2 -/
theorem check_pipe_writev_wide_zero_count_is_unmodeled :
    (check_writev_row (writev_in 15 8192 (Z_to_bv 64 (2 ^ 32)) mem_none) (mkEffect 0 [] []) read_model
      = CheckUnmodeled
      ∧ check_writev_row (writev_in 15 8192 (Z_to_bv 64 (2 ^ 32)) mem_none) (mkEffect 0 [] []) read_model ≠ CheckOk read_model [])
    ∧ check_writev_row (writev_in 15 8192 (Z_to_bv 64 (2 ^ 32)) mem_none)
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 15 8192 (Z_to_bv 64 (2 ^ 32)) mem_none) (mkEffect 5 [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 14 8192 (Z_to_bv 64 (2 ^ 32)) mem_none)
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 14 8192 (Z_to_bv 64 (2 ^ 32)) mem_none) (mkEffect 0 [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 14 8192 (Z_to_bv 64 (2 ^ 32)) mem_none)
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-- Writev on stdout fd 1 with count 2^32+2 and {4096,1},{4097,1} over readable "ab" can deliver
two bytes in Linux, while qemu-user returns -EINVAL. The checker declines both offered answers
and rejects -EINVAL at the ordinary count-2 control.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- raw2 -/
theorem check_writev_over_max_with_small_low32_is_unmodeled :
    (check_writev_row (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 2)) mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) demo_model
      = CheckUnmodeled
      ∧ check_writev_row (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 2)) mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) demo_model ≠ CheckOk demo_model [WriteEv 1 97, WriteEv 1 98])
    ∧ check_writev_row (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 2)) mem_writev_ab)
        (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 1 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EINVAL) [] [])) demo_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> rwv_norm

/-- THE PER-SEGMENT `access_ok` RUNS BEFORE A BYTE IS GATHERED, on every
entry's uncapped length: a readable first entry followed by one whose
range leaves the user address space is -EFAULT at import
(`__import_iovec`'s loop, lib/iov_iter.c:1377-1385, Linux v6.18.46), not
the one-byte short write; and a lone zero-length entry based past the
ceiling is -EFAULT from `import_ubuf`'s range test (lib/iov_iter.c:1437),
not the 0 qemu-user answers.  The ledgers are the descriptors read: both
on the two-entry path, the one on the single-entry path.  The ceiling is
`__access_ok`'s `TASK_SIZE_MAX` (include/asm-generic/access_ok.h:15-16,
:33, Linux v6.18.46), the 2^47 of Sv48 the model fixes
(`task_size_is_the_sv48_top`), spelled `at_top`, Rocq's
`Z_to_bv 64 TASK_SIZE`.  The fifth refuses the first's -EFAULT with the
two descriptors read in one 32-byte range, the ledger v4.17 through v6.3
record, their range test failing the same second descriptor after that
copy (the copy at line 787 of v4.17's fs/read_write.c, the -EFAULT at
lines 812-814; the copy at line 1738 of v6.3's lib/iov_iter.c, the
-EFAULT at lines 1808-1812): a real answer, the fifth of the section
header's refusals with no entry to cite.
kernel: lib/iov_iter.c:__import_iovec,import_ubuf; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem check_writev_import_range_fault_beats_the_gather :
    check_writev_row (writev_in 1 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) demo_model
      = CheckOk demo_model []
    ∧ check_writev_row (writev_in 1 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (with_copyins [(8192, 16), (8208, 16), (4096, 1)] (mkEffect 1 [] [])) demo_model
      = CheckReject
    ∧ check_writev_row (writev_in 1 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 0 0))
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) demo_model
      = CheckOk demo_model []
    ∧ check_writev_row (writev_in 1 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 0 0))
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) demo_model
      = CheckReject
    ∧ check_writev_row (writev_in 1 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EFAULT) [] [])) demo_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-- A NONEMPTY WRITEV AT `LLONG_MAX` IS -EINVAL, the file and the offset
untouched: `vfs_writev` calls `rw_verify_area` on the aggregate
(fs/read_write.c:1051-1053, Linux v6.18.46), which refuses
`(loff_t)(pos + count) < 0` (:467-469) before `write_iter`; the two bytes
landing past it are refused.
kernel: fs/read_write.c:vfs_writev,rw_verify_area@v6.18.46 -/
theorem check_writev_at_llong_max_is_einval :
    check_writev_row (writev_in 3 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EINVAL) [] []))
        writev_llong_max_model
      = CheckOk writev_llong_max_model []
    ∧ check_writev_row (writev_in 3 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] []))
        writev_llong_max_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwv_norm

/-- A normal count keeps the aggregate-bound control on the answered surface.
kernel: lib/iov_iter.c:__import_iovec,__import_iovec_ubuf,import_ubuf@v6.18.46 -/
theorem check_writev_over_rw_bytes_max_total_is_judged :
    check_writev_row (writev_in 1 8192 1
          (mem_iov_pair 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 0))
        (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckReject
    ∧ check_writev_row (writev_in 1 8192 1
          (mem_iov_pair 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 0))
        (with_copyins [(8192, 16), (4096, 1)] (mkEffect 1 [] [])) demo_model
      = CheckOk demo_model [WriteEv 1 97]
    ∧ check_writev_row (writev_in 1 8192 1 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) demo_model
      = CheckReject
    ∧ check_writev_row (writev_in 1 8192 1
          (mem_iov_pair 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 0))
        (with_copyins [(8192, 16), (4096, 2)] (mkEffect 2 [] [])) demo_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-- Writev on stdout fd 1 uses count 2^32+1 with {4096,rw_bytes_max+1},{0,0}, only byte 97
readable, or with {4096,1},{4097,1} over "ab". The checker declines the offered -EINVAL, one-
byte and two-byte results, including the mismatched source ledgers, and refuses acceptance of
the former one-byte result.
probe: testing/syscall-check/tests/rw_bytes_bound.c#fail-closed --expect-unmodeled writev -- wv-over-max -/
theorem check_writev_wide_count_over_rw_bytes_max_is_unmodeled :
    (check_writev_row (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 1))
          (mem_iov_pair 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 0))
        (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckUnmodeled
      ∧ check_writev_row (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 1)) (mem_iov_pair 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 0)) (with_copyins [(8192, 16), (4096, 1)] (mkEffect 1 [] [])) demo_model ≠ CheckOk demo_model [WriteEv 1 97])
    ∧ check_writev_row (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 1))
          (mem_iov_pair 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 0))
        (with_copyins [(8192, 16), (4096, 1)] (mkEffect 1 [] [])) demo_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 1)) mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) demo_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 1))
          (mem_iov_pair 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 0))
        (with_copyins [(8192, 16), (4096, 2)] (mkEffect 2 [] [])) demo_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-- THE RETIRED BOUND IS IN FRONT OF NO FILE KIND: one descriptor of
`rw_bytes_max + 1` bytes at an unmapped source is imported and judged on
the write-only file (fd 4) — -EFAULT, `generic_perform_write` having
copied nothing (mm/filemap.c:4321-4323, :4331-4332, Linux v6.18.46), and
the claimed length of 1 refused — while the pipe write end (fd 15)
declines for its own reason, the control that shows the decline is
reachable in the fixture.  Rocq states only "not `CheckUnmodeled`" for
the file; the verdict is stated here.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem check_writev_aggregate_past_the_retired_bound_is_judged :
    check_writev_row (writev_in 4 8192 1 (iov_array [(4096, Z_to_bv 64 (rw_bytes_max + 1))]))
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckOk read_model []
    ∧ check_writev_row (writev_in 4 8192 1 (iov_array [(4096, Z_to_bv 64 (rw_bytes_max + 1))]))
        (with_copyins [(8192, 16), (4096, 1)] (mkEffect 1 [] [])) read_model
      = CheckReject
    ∧ check_writev_row (writev_in 15 8192 1 (iov_array [(4096, Z_to_bv 64 (rw_bytes_max + 1))]))
        (mkEffect 1 [] []) read_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_⟩ <;> rwv_norm

/-! ### Rocq's readv examples, on the checker -/

/-- THE SINGLE-DESCRIPTOR PATH CAPS BEFORE `access_ok`, the array path
after: a first entry `MAX_RW_COUNT` below the top of the address space
and one byte longer passes as the only entry — `import_ubuf` caps the
length first (lib/iov_iter.c:1435-1437, Linux v6.18.46), and standard
input at its end answers 0 — but faults as the first of two, where
`__import_iovec`'s loop tests the raw length (:1380) before the cap
(:1387-1388); the 0 is refused there.  The first conjunct is Linux v6.4
and later: commit 3b2deb0e46da gave a count of one `import_ubuf`, and
v4.17 through v6.3 send it through the same loop as the array, which
answers -EFAULT on the raw length — refused here (the last conjunct), a
cost no bugs entry records yet.  qemu-user's `lock_iovec` answers
-EFAULT there too, as it would at any length from 1 to 2^63-1, since it
locks the entry at its raw length and no writable guest memory backs it
(linux-user/syscall.c:3120, :3125-3128, QEMU 11.1.1); a zero length it
never locks (:3116-3118), and a length of 2^63 or more is a negative
`abi_long` it answers -EINVAL (:3113-3115).
kernel: lib/iov_iter.c:import_ubuf,__import_iovec@v6.18.46 -/
theorem check_readv_single_iovec_caps_before_access_ok :
    check_readv_row (readv_in 0 8192 1 mem_readv_cap_order wmem_none)
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) demo_model
      = CheckOk demo_model []
    ∧ check_readv_row (readv_in 0 8192 2 mem_readv_cap_order wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) demo_model
      = CheckOk demo_model []
    ∧ check_readv_row (readv_in 0 8192 2 mem_readv_cap_order wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) demo_model
      = CheckReject
    ∧ check_readv_row (readv_in 0 8192 1 mem_readv_cap_order wmem_none)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) demo_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-- A 2^62-BYTE DESCRIPTOR DELIVERS ONE BYTE: on standard input holding one
byte the delivery is bounded by the input, and on the one-byte file by
its length, the descriptor moving to 1.  `import_ubuf` caps the length at
`MAX_RW_COUNT` (lib/iov_iter.c:1435-1436, Linux v6.18.46), and neither
source has more than one byte to give.  That is Linux v6.4 and later
(commit 3b2deb0e46da): v4.17 through v6.3 test the raw 2^62 against the
address-space ceiling before any cap and answer -EFAULT, as qemu-user's
`lock_iovec` does, which the model refuses on both sources (the last two
conjuncts) and no bugs entry records yet.
kernel: lib/iov_iter.c:import_ubuf@v6.18.46 -/
theorem check_readv_huge_len_delivers_one_byte_without_unary_expansion :
    check_readv_row (readv_in 0 8192 1 mem_readv_huge wmem_readv_one)
        (with_copyins [(8192, 16)] (mkEffect 1 [(4096, [120])] []))
        (with_stdin (ICons 120 IEof) demo_model)
      = CheckOk (with_stdin IEof demo_model) [ReadEv 0 120]
    ∧ check_readv_row (readv_in 3 8192 1 mem_readv_huge wmem_readv_one)
        (with_copyins [(8192, 16)] (mkEffect 1 [(4096, [120])] [])) (readv_x_model 0)
      = CheckOk (readv_x_model 1) []
    ∧ check_readv_row (readv_in 0 8192 1 mem_readv_huge wmem_readv_one)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] []))
        (with_stdin (ICons 120 IEof) demo_model)
      = CheckReject
    ∧ check_readv_row (readv_in 3 8192 1 mem_readv_huge wmem_readv_one)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) (readv_x_model 0)
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-- AN OFFSET OF 2^62 ON A ONE-BYTE FILE IS END OF FILE: 0, the descriptor
unmoved.  `rw_verify_area` passes it — `pos + count` stays below 2^63
(fs/read_write.c:467, Linux v6.18.46) — and the read at an offset past
`i_size` delivers nothing (`shmem_file_read_iter`, mm/shmem.c:3388-3389,
Linux v6.18.46).  The descriptor's 2^62 length reaches `rw_verify_area`
capped only on Linux v6.4 and later (commit 3b2deb0e46da, which gave a
count of one `import_ubuf`); v4.17 through v6.3 answer -EFAULT on the
raw length at import, as qemu-user's `lock_iovec` does, which the model
refuses (the second conjunct) and no bugs entry records yet.
kernel: fs/read_write.c:rw_verify_area; mm/shmem.c:shmem_file_read_iter@v6.18.46 -/
theorem check_readv_huge_file_offset_is_bounded_by_file_length :
    check_readv_row (readv_in 3 8192 1 mem_readv_huge wmem_readv_one)
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (readv_x_model (Z_to_bv 64 (2 ^ 62)))
      = CheckOk (readv_x_model (Z_to_bv 64 (2 ^ 62))) []
    ∧ check_readv_row (readv_in 3 8192 1 mem_readv_huge wmem_readv_one)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] []))
        (readv_x_model (Z_to_bv 64 (2 ^ 62)))
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwv_norm

/-- Readv uses eight readable {0,0} entries at 8192: on stdin fd 0 both implementations return 0
at count 8 and -EINVAL at 1025, which the checker accepts while rejecting -ENOMEM at 8. The pin
declines counts 9, 1024 and 2^32+9 on stdin, count 9 on closed fd 5, and counts 9 and 1025 on
write-only file fd 3; the absent ninth entry and oversized count prevent the latter -EBADF cases
from being shared answers.
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv -- badfdiov -/
theorem check_readv_heap_iovec_boundary_fails_closed :
    check_readv_row (readv_in 0 8192 8 mem_readv_eight_zero wmem_none)
        (with_copyins [(8192, 16), (8208, 16), (8224, 16), (8240, 16), (8256, 16), (8272, 16),
            (8288, 16), (8304, 16)] (mkEffect 0 [] [])) demo_model
      = CheckOk demo_model []
    ∧ check_readv_row (readv_in 0 8192 8 mem_readv_eight_zero wmem_none)
        (with_copyins [(8192, 16), (8208, 16), (8224, 16), (8240, 16), (8256, 16), (8272, 16),
            (8288, 16), (8304, 16)] (mkEffect (errno_ret ENOMEM) [] [])) demo_model
      = CheckReject
    ∧ (check_readv_row (readv_in 0 8192 9 mem_readv_eight_zero wmem_none) (mkEffect 0 [] [])
        demo_model
      = CheckUnmodeled
      ∧ check_readv_row (readv_in 5 8192 9 mem_readv_eight_zero wmem_none) (mkEffect (errno_ret EBADF) [] []) demo_model ≠ CheckOk demo_model [])
    ∧ check_readv_row (readv_in 0 8192 9 mem_readv_eight_zero wmem_none)
        (mkEffect (errno_ret ENOMEM) [] []) demo_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 0 8192 1024 mem_readv_eight_zero wmem_none) (mkEffect 0 [] [])
        demo_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 5 8192 9 mem_readv_eight_zero wmem_none)
        (mkEffect (errno_ret EBADF) [] []) demo_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 3 8192 9 mem_readv_eight_zero wmem_none)
        (mkEffect (errno_ret EBADF) [] []) readv_write_only_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 0 8192 (Z_to_bv 64 (2 ^ 32 + 9)) mem_readv_eight_zero wmem_none)
        (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 0 8192 (Z_to_bv 64 (2 ^ 32 + 9)) mem_readv_eight_zero wmem_none)
        (mkEffect (errno_ret ENOMEM) [] []) demo_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 0 8192 1025 mem_readv_eight_zero wmem_none)
        (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckOk demo_model []
    ∧ check_readv_row (readv_in 3 8192 9 mem_readv_eight_zero wmem_none)
        (mkEffect (errno_ret ENOMEM) [] []) readv_write_only_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 3 8192 9 mem_readv_eight_zero wmem_none)
        (with_copyins [(8192, 16), (8208, 16), (8224, 16), (8240, 16), (8256, 16), (8272, 16),
            (8288, 16), (8304, 16), (8320, 16)] (mkEffect (errno_ret EFAULT) [] []))
        readv_write_only_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 3 8192 9 mem_readv_eight_zero wmem_none)
        (with_copyins [(8192, 144)] (mkEffect (errno_ret EFAULT) [] [])) readv_write_only_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 3 8192 1025 mem_readv_eight_zero wmem_none)
        (mkEffect (errno_ret EINVAL) [] []) readv_write_only_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-- Readv on stdin fd 0 at EOF with count 2^32+1 and one {4096,1} entry at 8192 returns 0 after
Linux narrows the count, but -EINVAL in qemu-user. The checker declines that zero effect,
accepts the count-1 EOF result despite the unwritable destination, and rejects a count-2 zero
result because the second descriptor is absent.
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv --stdin hello -- rawhigh -/
theorem check_readv_wide_iovcnt_is_unmodeled :
    (check_readv_row (readv_in 0 8192 (Z_to_bv 64 (2 ^ 32 + 1)) mem_readv_iov wmem_none)
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) demo_model
      = CheckUnmodeled
      ∧ check_readv_row (readv_in 0 8192 (Z_to_bv 64 (2 ^ 32 + 1)) mem_readv_iov wmem_none)
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) demo_model ≠ CheckOk demo_model [])
    ∧ check_readv_row (readv_in 0 8192 1 mem_readv_iov wmem_none)
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) demo_model
      = CheckOk demo_model []
    ∧ check_readv_row (readv_in 0 8192 2 mem_readv_iov wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) demo_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> rwv_norm

/-- Readv on stdin fd 0 at EOF with count 2^32+1 and one {4096,1} entry at 8192 gives Linux's 0
and qemu-user's -EINVAL. The checker declines both offered answers and rejects an import-count
-EINVAL at the ordinary count-1 control.
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv --stdin hello -- rawhigh -/
theorem check_readv_over_max_with_small_low32_is_unmodeled :
    (check_readv_row (readv_in 0 8192 (Z_to_bv 64 (2 ^ 32 + 1)) mem_readv_iov wmem_none)
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) demo_model
      = CheckUnmodeled
      ∧ check_readv_row (readv_in 0 8192 (Z_to_bv 64 (2 ^ 32 + 1)) mem_readv_iov wmem_none)
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) demo_model ≠ CheckOk demo_model [])
    ∧ check_readv_row (readv_in 0 8192 (Z_to_bv 64 (2 ^ 32 + 1)) mem_readv_iov wmem_none)
        (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 0 8192 1 mem_readv_iov wmem_none)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) demo_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> rwv_norm

/-- Readv on write-only stdout fd 1 with count 2 and an unreadable array at 8192 gives Linux v6.8+'s
-EBADF and qemu-user's -EFAULT. The checker declines the offered -EBADF and the -EFAULT effects
with empty, one-descriptor or whole-array copy-in ledgers.
kernel: fs/read_write.c:vfs_readv; lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem check_readv_write_only_fd_unreadable_array_is_unmodeled :
    (check_readv_row (readv_in 1 8192 2 mem_none wmem_none) (mkEffect (errno_ret EBADF) [] [])
        demo_model
      = CheckUnmodeled
      ∧ check_readv_row (readv_in 1 8192 2 mem_none wmem_none) (mkEffect (errno_ret EBADF) [] [])
        demo_model ≠ CheckOk demo_model [])
    ∧ check_readv_row (readv_in 1 8192 2 mem_none wmem_none)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) demo_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 1 8192 2 mem_none wmem_none)
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EFAULT) [] [])) demo_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 1 8192 2 mem_none wmem_none) (mkEffect (errno_ret EFAULT) [] [])
        demo_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-- The readable empty entry lets both implementations reach the fd's read mode.
probe: testing/syscall-check/tests/pipe2_spec.c#conform -- wrongend -/
theorem check_readv_pipe_gate_splits_the_two_ends :
    check_readv_row (readv_in 15 8192 1 mem_readv_eight_zero wmem_none) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckOk read_model []
    ∧ check_readv_row (readv_in 14 8192 1 mem_readv_eight_zero wmem_none) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckReject
    ∧ check_readv_row (readv_in 4 8192 1 mem_readv_eight_zero wmem_none) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckOk read_model []
    ∧ check_readv_row (readv_in 15 8192 1 mem_readv_eight_zero wmem_none)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckReject
    ∧ check_readv_row (readv_in 4 8192 1 mem_readv_eight_zero wmem_none)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckReject
    ∧ check_readv_row (readv_in 15 8192 1 mem_readv_eight_zero wmem_none) (mkEffect (errno_ret EFAULT) [] [])
        read_model
      = CheckReject
    ∧ check_readv_row (readv_in 4 8192 1 mem_readv_eight_zero wmem_none) (mkEffect (errno_ret EFAULT) [] [])
        read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-- Readv on pipe write end fd 15 or write-only file fd 4 uses count 1 and an unreadable array
at 4096. Linux returns -EBADF and qemu-user returns -EFAULT, so the pin declines the offered
-EBADF and rules out its acceptance on either fd.
kernel: fs/read_write.c:vfs_readv; lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem check_readv_pipe_wrong_mode_unreadable_array_is_unmodeled :
    check_readv_row (readv_in 15 4096 1 mem_none wmem_none)
      (mkEffect (errno_ret EBADF) [] []) read_model = CheckUnmodeled
    ∧ check_readv_row (readv_in 15 4096 1 mem_none wmem_none)
      (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk read_model []
    ∧ check_readv_row (readv_in 4 4096 1 mem_none wmem_none)
      (mkEffect (errno_ret EBADF) [] []) read_model = CheckUnmodeled
    ∧ check_readv_row (readv_in 4 4096 1 mem_none wmem_none)
      (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk read_model [] := by
  have h15 : check_readv_row (readv_in 15 4096 1 mem_none wmem_none)
      (mkEffect (errno_ret EBADF) [] []) read_model = CheckUnmodeled := by rwv_norm
  have h4 : check_readv_row (readv_in 4 4096 1 mem_none wmem_none)
      (mkEffect (errno_ret EBADF) [] []) read_model = CheckUnmodeled := by rwv_norm
  exact ⟨h15, (by rw [h15]; intro h; cases h), h4, (by rw [h4]; intro h; cases h)⟩


/-- A ZERO-LENGTH ENTRY, THEN A BAD BASE, ON A FILE: the empty entry is
skipped and the first byte lands at NULL, which is not writable, so
-EFAULT with nothing delivered and the offset unchanged — `shmem_file_read_iter`
sets -EFAULT when a page copy comes up short (mm/shmem.c:3479-3481, Linux
v6.18.46) and returns it when nothing was copied before (:3487).
qemu-user's 0 is refused, and so is the -EISDIR only a directory's
`generic_read_dir` answers (fs/libfs.c:224-227).
kernel: mm/shmem.c:shmem_file_read_iter; fs/libfs.c:generic_read_dir@v6.18.46 -/
theorem check_readv_zero_prefix_then_bad_base_is_efault_on_a_file :
    check_readv_row (readv_in 3 8192 2 (mem_iov_pair 0 0 0 1) wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] []))
        (readv_abcde_model 0)
      = CheckOk (readv_abcde_model 0) []
    ∧ check_readv_row (readv_in 3 8192 2 (mem_iov_pair 0 0 0 1) wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) (readv_abcde_model 0)
      = CheckReject
    ∧ check_readv_row (readv_in 3 8192 2 (mem_iov_pair 0 0 0 1) wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EISDIR) [] []))
        (readv_abcde_model 0)
      = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> rwv_norm

/-- THE SAME VECTOR ON A DIRECTORY NEVER REACHES A COPY: the entries
import — an in-range NULL base passes `access_ok` — and `generic_read_dir`
answers -EISDIR (fs/libfs.c:224, Linux v6.18.46) without touching the
destination, so 0 and -EFAULT are refused; with a writable first entry
ahead of the NULL one the answer is the same.  The only -EFAULT the
destination can raise here is the import's range test
(lib/iov_iter.c:1380-1384), which an in-range base passes.
kernel: fs/libfs.c:generic_read_dir; lib/iov_iter.c:__import_iovec@v6.18.46 -/
theorem check_readv_directory_never_consults_the_destination :
    check_readv_row (readv_in 5 8192 2 (mem_iov_pair 0 0 0 1) wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EISDIR) [] [])) read_model
      = CheckOk read_model []
    ∧ check_readv_row (readv_in 5 8192 2 (mem_iov_pair 0 0 0 1) wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) read_model
      = CheckReject
    ∧ check_readv_row (readv_in 5 8192 2 (mem_iov_pair 0 0 0 1) wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckReject
    ∧ check_readv_row (readv_in 5 8192 2 (mem_iov_pair 4096 1 0 1) wmem_readv_one)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EISDIR) [] [])) read_model
      = CheckOk read_model []
    ∧ check_readv_row (readv_in 5 8192 2 (mem_iov_pair 4096 1 0 1) wmem_readv_one)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-- WHAT THE DESTINATION CAN SAY ON A DIRECTORY, IT SAYS AT IMPORT: an
entry based at 1 with length `at_top`, 2^47, Sv48's `TASK_SIZE`
(`task_size_is_the_sv48_top`), fails `__import_iovec`'s
range test by one (lib/iov_iter.c:1380-1385, Linux v6.18.46) — the
ceiling `__access_ok` reads as `TASK_SIZE_MAX`
(include/asm-generic/access_ok.h:15-16, :33) — so -EFAULT comes ahead
of `generic_read_dir`'s -EISDIR (fs/libfs.c:224-227), which is refused.
kernel: lib/iov_iter.c:__import_iovec; include/asm-generic/access_ok.h:__access_ok; fs/libfs.c:generic_read_dir@v6.18.46 -/
theorem check_readv_directory_import_range_fault_beats_eisdir :
    check_readv_row (readv_in 5 8192 2 (mem_iov_pair 1 at_top 4096 3) wmem_readv_one)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckOk read_model []
    ∧ check_readv_row (readv_in 5 8192 2 (mem_iov_pair 1 at_top 4096 3) wmem_readv_one)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EISDIR) [] [])) read_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwv_norm

/-- THE BASE LOAD FAULTS BEFORE THE SIGN TEST: `copy_iovec_from_user`
loads `iov_len` then `iov_base` (lib/iov_iter.c:1272-1273, Linux
v6.18.46) and only then tests `len < 0` (:1276), so a readable length of
2^63 beside an unreadable base is -EFAULT, not -EINVAL, and the ledger is
the one descriptor attempted.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem check_readv_unreadable_base_faults_before_the_sign_test :
    import_iovecs_accesses mem_readv_len_only 8192 2 = [(8192, 16)]
    ∧ check_readv_row (readv_in 0 8192 2 mem_readv_len_only wmem_none)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) demo_model
      = CheckOk demo_model []
    ∧ check_readv_row (readv_in 0 8192 2 mem_readv_len_only wmem_none)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) demo_model
      = CheckReject := by
  refine ⟨rfl, ?_, ?_⟩ <;> rwv_norm

/-- A NONEMPTY READV AT `LLONG_MAX` IS -EINVAL, not end of file: `vfs_readv`
calls `rw_verify_area` on the aggregate (fs/read_write.c:1013-1015, Linux
v6.18.46), which refuses `(loff_t)(pos + count) < 0` (:467-469).  The
scalar `read` at the same offset still answers 0 in the model — the
recorded divergence `check_file_at_llong_max_still_answers_zero` pins.
kernel: fs/read_write.c:vfs_readv,rw_verify_area@v6.18.46 -/
theorem check_readv_at_llong_max_is_einval :
    check_readv_row (readv_in 3 8192 1 mem_readv_iov wmem_readv_one)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] []))
        (readv_abcde_model (Z_to_bv 64 (2 ^ 63 - 1)))
      = CheckOk (readv_abcde_model (Z_to_bv 64 (2 ^ 63 - 1))) []
    ∧ check_readv_row (readv_in 3 8192 1 mem_readv_iov wmem_readv_one)
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (readv_abcde_model (Z_to_bv 64 (2 ^ 63 - 1)))
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwv_norm

/-- A PARTIALLY WRITABLE DESTINATION ON A PIPE DECLINES: five bytes queued,
a two-and-three vector, four destination bytes writable.
`anon_pipe_read` answers -EFAULT with four stored if the five arrived in
one buffer and a count of whole buffers otherwise (fs/pipe.c:343-350,
Linux v6.18.46), a progress the model does not describe, so the
delivery, the -EFAULT and the four-byte short read all decline; with the
fifth byte writable the whole delivery is judged, standard input drained
and one event per byte.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem check_readv_stdin_partial_destination_declines :
    check_readv_row (readv_in 0 8192 2 (mem_iov_pair 4096 2 4098 3) (wmem_first 4))
        (with_copyins [(8192, 16), (8208, 16)]
          (mkEffect 5 [(4096, [104, 101]), (4098, [108, 108, 111])] []))
        (with_stdin hello_stdin demo_model)
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 0 8192 2 (mem_iov_pair 4096 2 4098 3) (wmem_first 4))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] []))
        (with_stdin hello_stdin demo_model)
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 0 8192 2 (mem_iov_pair 4096 2 4098 3) (wmem_first 4))
        (with_copyins [(8192, 16), (8208, 16)]
          (mkEffect 4 [(4096, [104, 101]), (4098, [108, 108])] []))
        (with_stdin hello_stdin demo_model)
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 0 8192 2 (mem_iov_pair 4096 2 4098 3) (wmem_first 5))
        (with_copyins [(8192, 16), (8208, 16)]
          (mkEffect 5 [(4096, [104, 101]), (4098, [108, 108, 111])] []))
        (with_stdin hello_stdin demo_model)
      = CheckOk (with_stdin IEof demo_model)
          [ReadEv 0 104, ReadEv 0 101, ReadEv 0 108, ReadEv 0 108, ReadEv 0 111] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-! ### Beyond Rocq's examples: each verdict and each decline, with its edge -/

/-- WHAT A CHANNEL WRITEV MAY ANSWER, one answer per conjunct: the whole
delivery is accepted, one event per byte and the ledger the descriptors
plus the gathered source; a count past the gathered total, a 0 for a
nonempty vector, a ledger short of the delivered bytes or missing the
descriptors, and any user-memory write are refused.  `anon_pipe_write`
(fs/pipe.c:431, Linux v6.18.46) copies a request that fits the ring into
the last buffer's tail (:477-497) or onto fresh pages (:522-547) and
returns the count, never more than it was given;
its only 0 is the empty write (:455-456), which a nonempty vector is not;
and it reads the source, never writes it.  The shorter delivery the
channel's prefix rule also accepts is `check_writev_ab_short_delivery`'s.
The seventh through tenth restate the delivery and three of those refusals —
the count past the total, the 0 and the ledger short a byte — on
`read_model`, the model `check_writev_enomem_is_refused_or_declined`
judges standard output on.  The eleventh refuses the same delivery with
the descriptors read in one 32-byte range, the ledger v4.17 through v6.3
record (line 787 of v4.17's fs/read_write.c, line 1738 of v6.3's
lib/iov_iter.c): a real answer, the fifth of the section header's
refusals with no entry to cite.
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem check_writev_channel_verdicts :
    check_writev_row (writev_in 1 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) demo_model
      = CheckOk demo_model [WriteEv 1 97, WriteEv 1 98]
    ∧ check_writev_row (writev_in 1 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 3 [] [])) demo_model
      = CheckReject
    ∧ check_writev_row (writev_in 1 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) demo_model
      = CheckReject
    ∧ check_writev_row (writev_in 1 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1)] (mkEffect 2 [] [])) demo_model
      = CheckReject
    ∧ check_writev_row (writev_in 1 8192 2 mem_writev_ab)
        (with_copyins [(4096, 1), (4097, 1)] (mkEffect 2 [] [])) demo_model
      = CheckReject
    ∧ check_writev_row (writev_in 1 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)]
          (mkEffect 2 [(4096, [97, 98])] [])) demo_model
      = CheckReject
    ∧ check_writev_row (writev_in 1 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) read_model
      = CheckOk read_model [WriteEv 1 97, WriteEv 1 98]
    ∧ check_writev_row (writev_in 1 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 3 [] [])) read_model
      = CheckReject
    ∧ check_writev_row (writev_in 1 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) read_model
      = CheckReject
    ∧ check_writev_row (writev_in 1 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1)] (mkEffect 2 [] [])) read_model
      = CheckReject
    ∧ check_writev_row (writev_in 1 8192 2 mem_writev_ab)
        (with_copyins [(8192, 32), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-- A ONE-BYTE DELIVERY OF THE GATHERED "ab" IS ACCEPTED.  The acceptance
is the channel's any-nonempty-prefix rule, which is wider than a pipe: a
blocking pipe write of two readable bytes copies both onto one page
(fs/pipe.c:522-547, Linux v6.18.46) or merges both into the last one
(:488-497), so the one-byte answer is a real answer only of the other
kinds a channel may be (`bugs/write-channel-pipebuf-short-write.md`
records the cost), as `check_write_ab_short_delivery` pins for the
scalar call.
model: the channel's prefix rule in `check_writev`, whose one-byte acceptance is the recorded divergence bugs/write-channel-pipebuf-short-write.md -/
theorem check_writev_ab_short_delivery :
    check_writev_row (writev_in 1 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1)] (mkEffect 1 [] [])) demo_model
      = CheckOk demo_model [WriteEv 1 97] := by
  rwv_norm

/-- Writev on read-only stdin fd 0 uses count 2 and {4096,1},{4097,1} over readable "ab"; the
checker declines the offered -EBADF and delivery effects, including the alternate import
ledgers. On stdout fd 1 it accepts -EFAULT for count 1 with {4096,1} and no source byte, and 0
for count 2 with {4096,0},{4096,0}, rejecting the swapped returns.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_writev_channel_edges :
    (check_writev_row (writev_in 0 8192 2 mem_writev_ab) (mkEffect (errno_ret EBADF) [] []) demo_model
      = CheckUnmodeled
      ∧ check_writev_row (writev_in 0 8192 2 mem_writev_ab) (mkEffect (errno_ret EBADF) [] []) demo_model ≠ CheckOk demo_model [])
    ∧ check_writev_row (writev_in 0 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) demo_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 1 8192 1 (iov_array [(4096, 1)]))
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) demo_model
      = CheckOk demo_model []
    ∧ check_writev_row (writev_in 1 8192 1 (iov_array [(4096, 1)]))
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) demo_model
      = CheckReject
    ∧ check_writev_row (writev_in 1 8192 2 (mem_iov_pair 4096 0 4096 0))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) demo_model
      = CheckOk demo_model []
    ∧ check_writev_row (writev_in 1 8192 2 (mem_iov_pair 4096 0 4096 0))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) demo_model
      = CheckReject
    ∧ check_writev_row (writev_in 0 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EBADF) [] [])) demo_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 0 8192 2 mem_writev_ab)
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EBADF) [] [])) demo_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-- A FILE WRITEV LANDS AT THE OFFSET AND MOVES IT: the two gathered bytes
become the empty file's contents and the offset 2, and from offset 2 the
same write leaves a two-byte hole of zeros ahead of them and the offset
at 4; the one-byte short count is refused, the source being readable
throughout.  `generic_perform_write` copies from `ki_pos` and advances it
by what it copied (mm/filemap.c:4244-4335, Linux v6.18.46).  The hole
lies in the same page the write lands in: `shmem_write_begin` allocates it
(mm/shmem.c:3331), `shmem_write_end` zeroes everything outside the copied
range of a page not yet up to date (mm/shmem.c:3355-3361), and
`shmem_file_read_iter` then reads the hole from that page (the folio
branch, mm/shmem.c:3431 and :3453-3454), not from its unallocated-page
branch.
kernel: mm/filemap.c:generic_perform_write; mm/shmem.c:shmem_write_begin,shmem_write_end,shmem_file_read_iter@v6.18.46 -/
theorem check_writev_file_lands_at_the_offset :
    check_writev_row (writev_in 3 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) writev_model
      = CheckOk (with_fds [(3, .FdFileW [102] 2)] (with_fs [([102], [97, 98])] writev_model)) []
    ∧ check_writev_row (writev_in 3 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1)] (mkEffect 1 [] [])) writev_model
      = CheckReject
    ∧ check_writev_row (writev_in 3 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] []))
        writev_hole_model
      = CheckOk (with_fds [(3, .FdFileW [102] 4)] (with_fs [([102], [0, 0, 97, 98])] writev_hole_model))
          [] := by
  refine ⟨?_, ?_, ?_⟩ <;> rwv_norm

/-- THE FIRST DECLINE BEYOND ROCQ'S, ON THE CHECKER, WITH BOTH EDGES: an
unreadable source at an offset past the file's end is declined — one
past a two-byte file, and two into an empty one — while the same source
at exactly the end is -EFAULT and 0 is refused.  Past the end,
`shmem_write_end` moves `i_size` to `pos + copied` (mm/shmem.c:3352-3353,
Linux v6.18.46) before `generic_perform_write`'s fault-in fails
(mm/filemap.c:4321-4323) and -EFAULT is returned (:4331-4332), where
kernels before the pre-fault's removal leave the file alone
(`Sys.Fs.ReadWrite.writev_file_arm`); at the end `pos + copied` does not
pass `i_size`, so every supported kernel answers the one -EFAULT.
kernel: mm/shmem.c:shmem_write_end; mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem check_writev_past_eof_unreadable_source_declines :
    check_writev_row (writev_in 4 8192 1 (iov_array [(4096, 1)]))
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) wend_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 3 8192 1 (iov_array [(4096, 1)]))
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) writev_hole_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 3 8192 1 (iov_array [(4096, 1)]))
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) wend_model
      = CheckOk wend_model []
    ∧ check_writev_row (writev_in 3 8192 1 (iov_array [(4096, 1)]))
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) wend_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-- THE SECOND DECLINE, ON THE CHECKER: a source readable at
its first byte and not its second is declined on the file — the one-byte
write and the -EFAULT alike, since no answer is
shared by every supported kernel (`Sys.Fs.ReadWrite.writev_file_arm`:
Linux v5.18 on writes what the fault-in reached, `generic_perform_write`
at mm/filemap.c:4321-4324, Linux v6.18.46; older kernels answer a whole
chunk or -EFAULT).  The same vector on the channel is judged, not
declined — `check_writev_channel_partial_source` — which is the control
that shows the decline belongs to the file arm.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem check_writev_partial_source_declines :
    check_writev_row (writev_in 3 8192 2 (mem_iov_pair 4096 1 4097 1))
        (with_copyins [(8192, 16), (8208, 16), (4096, 1)] (mkEffect 1 [] [])) writev_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 3 8192 2 (mem_iov_pair 4096 1 4097 1))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) writev_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> rwv_norm

/-- A CHANNEL SOURCE READABLE IN ITS FIRST BYTE ONLY is judged by its
readable prefix: the one-byte delivery is accepted, the two-byte count
and the -EFAULT refused.  On a pipe Linux answers -EFAULT here: the two
entries total two bytes, which `anon_pipe_write` either merges into the
last page, where the short copy is -EFAULT (fs/pipe.c:488-492, Linux
v6.18.46), or copies onto a fresh page, which it drops with nothing
counted and -EFAULT (:522-527).  So the acceptance is the recorded
divergence `bugs/write-channel-partial-source-efault-refused.md`, which
refuses that -EFAULT, as `channel_write_partial_source_on_the_checker`
pins for the scalar call; the refusal of the two-byte count is the prefix
rule's bound.
model: the channel's prefix rule over a partial source, the recorded divergence bugs/write-channel-partial-source-efault-refused.md -/
theorem check_writev_channel_partial_source :
    check_writev_row (writev_in 1 8192 2 (mem_iov_pair 4096 1 4097 1))
        (with_copyins [(8192, 16), (8208, 16), (4096, 1)] (mkEffect 1 [] [])) demo_model
      = CheckOk demo_model [WriteEv 1 97]
    ∧ check_writev_row (writev_in 1 8192 2 (mem_iov_pair 4096 1 4097 1))
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) demo_model
      = CheckReject
    ∧ check_writev_row (writev_in 1 8192 2 (mem_iov_pair 4096 1 4097 1))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) demo_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_⟩ <;> rwv_norm

/-- A readable empty first entry with in-range bases keeps -EBADF on every wrong-mode
kind. Linux v4.17 through v6.7 imports first (fs/read_write.c, vfs_writev,
v6.6), while v6.8+ tests the mode first (1c8aa833034a). The later rows
keep the invalid-count, incomplete-array and invalid-range declines separate.
kernel: fs/read_write.c:vfs_writev; fs/namei.c:may_open; lib/iov_iter.c:iovec_from_user,copy_iovec_from_user@v6.18.46 -/
theorem check_writev_kind_verdicts :
    (check_writev_row (writev_in 30 8192 1 (mem_iov_pair 4096 0 4096 0)) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model []
      ∧ check_writev_row (writev_in 30 8192 1 (mem_iov_pair 4096 0 4096 0)) (mkEffect 0 [] []) read_model = CheckReject)
    ∧ check_writev_row (writev_in 3 8192 1 (mem_iov_pair 4096 0 4096 0)) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model []
    ∧ check_writev_row (writev_in 5 8192 1 (mem_iov_pair 4096 0 4096 0)) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model []
    ∧ check_writev_row (writev_in 5 8192 1 (mem_iov_pair 4096 0 4096 0)) (mkEffect (errno_ret EISDIR) [] []) read_model
      = CheckReject
    ∧ check_writev_row (writev_in 24 8192 1 (mem_iov_pair 4096 0 4096 0)) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model []
    ∧ check_writev_row (writev_in 8 8192 1 (mem_iov_pair 4096 0 4096 0)) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model []
    ∧ check_writev_row (writev_in 14 8192 1 (mem_iov_pair 4096 0 4096 0)) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model []
    ∧ check_writev_row (writev_in 9 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 2 [] [])) read_model
      = CheckOk read_model []
    ∧ check_writev_row (writev_in 9 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) read_model
      = CheckReject
    ∧ check_writev_row (writev_in 3 8192 1025 mem_writev_ab) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 3 8192 9 mem_readv_eight_zero) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 3 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 3 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 5 8192 1025 mem_writev_ab) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 5 8192 9 mem_readv_eight_zero) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 5 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 5 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 24 8192 1025 mem_writev_ab) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 24 8192 9 mem_readv_eight_zero) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 24 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 24 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 8 8192 1025 mem_writev_ab) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 8 8192 9 mem_readv_eight_zero) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 8 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 8 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 14 8192 1025 mem_writev_ab) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 14 8192 9 mem_readv_eight_zero) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 14 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 14 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 0 8192 1025 mem_writev_ab) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 0 8192 9 mem_readv_eight_zero) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 0 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 0 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 3 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EBADF) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 3 8192 2 mem_writev_ab)
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EBADF) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 14 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EBADF) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 3 8192 1025 mem_writev_ab) (mkEffect (errno_ret EINVAL) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 3 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 14 8192 2 mem_writev_ab)
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EBADF) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 5 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EBADF) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 5 8192 2 mem_writev_ab)
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EBADF) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 24 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EBADF) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 24 8192 2 mem_writev_ab)
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EBADF) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 8 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EBADF) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 8 8192 2 mem_writev_ab)
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EBADF) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 3 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EINVAL) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 3 8192 9 mem_readv_eight_zero) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 3 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 3 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 5 8192 1025 mem_writev_ab) (mkEffect (errno_ret EINVAL) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 5 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 5 8192 9 mem_readv_eight_zero) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 5 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 24 8192 1025 mem_writev_ab) (mkEffect (errno_ret EINVAL) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 24 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 24 8192 9 mem_readv_eight_zero) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 24 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 8 8192 1025 mem_writev_ab) (mkEffect (errno_ret EINVAL) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 8 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 8 8192 9 mem_readv_eight_zero) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 8 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 14 8192 1025 mem_writev_ab) (mkEffect (errno_ret EINVAL) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 14 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 14 8192 9 mem_readv_eight_zero) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 14 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 0 8192 1025 mem_writev_ab) (mkEffect (errno_ret EINVAL) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 0 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 0 8192 9 mem_readv_eight_zero) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 0 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 0 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EBADF) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 0 8192 2 mem_writev_ab)
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EBADF) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 3 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 0 8192 1 (mem_iov_pair 4096 0 4096 0)) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckOk read_model []
    ∧ check_writev_row (writev_in 5 8192 1025 mem_writev_ab) (mkEffect (errno_ret EFAULT) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 3 8192 9 mem_readv_eight_zero)
        (with_copyins
          [(8192, 16), (8208, 16), (8224, 16), (8240, 16), (8256, 16), (8272, 16), (8288, 16),
          (8304, 16), (8320, 16)]
          (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 5 8192 9 mem_readv_eight_zero)
        (with_copyins
          [(8192, 16), (8208, 16), (8224, 16), (8240, 16), (8256, 16), (8272, 16), (8288, 16),
          (8304, 16), (8320, 16)]
          (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 24 8192 9 mem_readv_eight_zero)
        (with_copyins
          [(8192, 16), (8208, 16), (8224, 16), (8240, 16), (8256, 16), (8272, 16), (8288, 16),
          (8304, 16), (8320, 16)]
          (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 8 8192 9 mem_readv_eight_zero)
        (with_copyins
          [(8192, 16), (8208, 16), (8224, 16), (8240, 16), (8256, 16), (8272, 16), (8288, 16),
          (8304, 16), (8320, 16)]
          (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 14 8192 9 mem_readv_eight_zero)
        (with_copyins
          [(8192, 16), (8208, 16), (8224, 16), (8240, 16), (8256, 16), (8272, 16), (8288, 16),
          (8304, 16), (8320, 16)]
          (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 0 8192 9 mem_readv_eight_zero)
        (with_copyins
          [(8192, 16), (8208, 16), (8224, 16), (8240, 16), (8256, 16), (8272, 16), (8288, 16),
          (8304, 16), (8320, 16)]
          (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 3 8192 9 mem_readv_eight_zero)
        (with_copyins [(8192, 144)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 5 8192 9 mem_readv_eight_zero)
        (with_copyins [(8192, 144)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 24 8192 9 mem_readv_eight_zero)
        (with_copyins [(8192, 144)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 8 8192 9 mem_readv_eight_zero)
        (with_copyins [(8192, 144)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 14 8192 9 mem_readv_eight_zero)
        (with_copyins [(8192, 144)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 0 8192 9 mem_readv_eight_zero)
        (with_copyins [(8192, 144)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 3 8192 9 mem_readv_eight_zero) (mkEffect (errno_ret EFAULT) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 5 8192 9 mem_readv_eight_zero) (mkEffect (errno_ret EFAULT) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 24 8192 9 mem_readv_eight_zero) (mkEffect (errno_ret EFAULT) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 8 8192 9 mem_readv_eight_zero) (mkEffect (errno_ret EFAULT) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 14 8192 9 mem_readv_eight_zero) (mkEffect (errno_ret EFAULT) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 0 8192 9 mem_readv_eight_zero) (mkEffect (errno_ret EFAULT) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 5 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EINVAL) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 24 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EINVAL) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 8 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EINVAL) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 14 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EINVAL) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 0 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EINVAL) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 5 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 24 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 8 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 14 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 0 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 5 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 24 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 8 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 14 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 0 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 3 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 5 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 24 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 8 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 14 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 0 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-- The checker declines writev on closed fd 30 and on read-only file, directory, urandom, null,
pipe and stdin fds 3, 5, 24, 8, 14 and 0 with count 2 over readable "ab" in {4096,1},{4097,1}: a
nonempty first entry is a buffer qemu-user's `lock_iovec` locks before the host call, so its
-EFAULT can precede the -EBADF Linux gives. The positive rows of `check_writev_kind_verdicts`
are the same kinds with an empty first entry.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- closednonempty -/
theorem check_writev_kind_nonempty_first_entry_declines :
    (check_writev_row (writev_in 30 8192 2 mem_writev_ab) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
      ∧ check_writev_row (writev_in 30 8192 2 mem_writev_ab) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk read_model [])
    ∧ check_writev_row (writev_in 3 8192 2 mem_writev_ab) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 5 8192 2 mem_writev_ab) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 5 8192 2 mem_writev_ab) (mkEffect (errno_ret EISDIR) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 24 8192 2 mem_writev_ab) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 8 8192 2 mem_writev_ab) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 14 8192 2 mem_writev_ab) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 0 8192 2 mem_writev_ab) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-- Writev on read-only file fd 3, directory fd 5, /dev/urandom fd 24, /dev/null fd 8, pipe read
end fd 14 and stdin fd 0 uses count 2 and an unreadable array at 8192. Linux v6.8+ returns -EBADF and
qemu-user returns -EFAULT; the checker declines the offered errors with the listed empty, per-
descriptor and bulk-array ledgers.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_writev_read_only_fd_unreadable_array_is_unmodeled :
    (check_writev_row (writev_in 3 8192 2 mem_none) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
      ∧ check_writev_row (writev_in 3 8192 2 mem_none) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk read_model [])
    ∧ check_writev_row (writev_in 3 8192 2 mem_none)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 3 8192 2 mem_none) (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 3 8192 2 mem_none)
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 5 8192 2 mem_none) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 5 8192 2 mem_none)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 5 8192 2 mem_none) (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 24 8192 2 mem_none) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 24 8192 2 mem_none)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 24 8192 2 mem_none) (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 8 8192 2 mem_none) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 8 8192 2 mem_none)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 8 8192 2 mem_none) (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 14 8192 2 mem_none) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 14 8192 2 mem_none)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 14 8192 2 mem_none) (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 0 8192 2 mem_none) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 0 8192 2 mem_none)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 0 8192 2 mem_none) (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    <;> rwv_norm

/-- THE WRITEV AGGREGATE IS CLAMPED TO `MAX_RW_COUNT` AT IMPORT, and a
writable `/dev/null` answers it whole: one descriptor of 2^62 bytes at
4096 is capped by `import_ubuf` (lib/iov_iter.c:1435-1436, Linux
v6.18.46) to `MAX_RW_COUNT`, `INT_MAX & PAGE_MASK`
(include/linux/fs.h:2838), 2147479552 with riscv64's 4 KiB pages; two of
2^31 bytes each are clamped by `__import_iovec`'s loop
(lib/iov_iter.c:1387-1390) to the same total, the second entry to
nothing; and `write_iter_null` returns the iterator's count without
reading the source (drivers/char/mem.c:429-434).  The unclamped totals,
2^62 and 2^32, are refused, and the ledger is the descriptors alone.
The file and channel arms gather over the same capped vector
(`State.writev_gathered`), which no closed pin can fill with that many
readable bytes; this is the clamp end to end.  The first conjunct is
Linux v6.4 and later (3b2deb0e46da, which gave a count of one
`import_ubuf`); v4.17 through v6.3 test the raw 2^62 against the
address-space ceiling before any cap and answer -EFAULT, as qemu-user's
`lock_iovec` does.  The model refuses that (the fifth conjunct), and no
bugs entry records it yet.  qemu-user's `lock_iovec` also locks each
entry at its raw length before it clamps anything (QEMU 11.1.1,
linux-user/syscall.c:3120, the clamp at :3136), and `lock_user`
(QEMU 11.1.1, linux-user/uaccess.c:8-15) fails unless
`access_ok_untagged` (linux-user/qemu.h:187-195, the same version) finds
the range valid and `page_check_range` finds every page of it mapped for
the access; a first entry it cannot lock is -EFAULT (QEMU 11.1.1,
linux-user/syscall.c:3125-3128).  This memory maps nothing at 4096, the
page both entries begin on, so `lock_user` refuses the first entry at
any length from 1 to 2^63-1 — the raw 2^31 and whatever the clamp could
leave alike — and the two 2^31-byte entries are -EFAULT under it; the
model refuses that in Linux's favour (the last conjunct).
kernel: lib/iov_iter.c:import_ubuf,__import_iovec; drivers/char/mem.c:write_iter_null@v6.18.46 -/
theorem check_writev_devnull_answers_the_clamped_aggregate :
    check_writev_row (writev_in 9 8192 1 (iov_array [(4096, Z_to_bv 64 (2 ^ 62))]))
        (with_copyins [(8192, 16)] (mkEffect 2147479552 [] [])) read_model
      = CheckOk read_model []
    ∧ check_writev_row (writev_in 9 8192 1 (iov_array [(4096, Z_to_bv 64 (2 ^ 62))]))
        (with_copyins [(8192, 16)] (mkEffect (Z_to_bv 64 (2 ^ 62)) [] [])) read_model
      = CheckReject
    ∧ check_writev_row
        (writev_in 9 8192 2 (iov_array [(4096, Z_to_bv 64 (2 ^ 31)), (4096, Z_to_bv 64 (2 ^ 31))]))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 2147479552 [] [])) read_model
      = CheckOk read_model []
    ∧ check_writev_row
        (writev_in 9 8192 2 (iov_array [(4096, Z_to_bv 64 (2 ^ 31)), (4096, Z_to_bv 64 (2 ^ 31))]))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (Z_to_bv 64 (2 ^ 32)) [] [])) read_model
      = CheckReject
    ∧ check_writev_row (writev_in 9 8192 1 (iov_array [(4096, Z_to_bv 64 (2 ^ 62))]))
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckReject
    ∧ check_writev_row
        (writev_in 9 8192 2 (iov_array [(4096, Z_to_bv 64 (2 ^ 31)), (4096, Z_to_bv 64 (2 ^ 31))]))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-- THE VECTORED PIPE AND SOCKET WRITES DECLINE, and the empty vector does
not: a pipe write end with two bytes to write, a fresh socket and a
connected one decline whatever the effect (`writev_spec`'s
`writev_buf_gap`: the scalar pipe arm's atomicity argument is per
transfer, not per vector) — on the fresh socket even the -EPIPE
`sk_stream_wait_connect` answers an unconnected TCP sender
(net/core/stream.c:70-71, Linux v6.18.46) — while the pipe write end with an all-empty
vector is 0 — `vfs_writev` returns on a zero aggregate before the write
operation (fs/read_write.c:1047-1049, Linux v6.18.46), ahead of the
decline.
kernel: fs/read_write.c:vfs_writev; net/core/stream.c:sk_stream_wait_connect@v6.18.46 -/
theorem check_writev_declines :
    check_writev_row (writev_in 15 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 10 8192 2 mem_writev_ab) (mkEffect (errno_ret EPIPE) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 20 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 15 8192 2 (mem_iov_pair 4096 0 4096 0))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) read_model
      = CheckOk read_model [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-- -ENOMEM FROM WRITEV IS REFUSED OR DECLINED: nine descriptors overflow
`iovec_from_user`'s on-stack array of eight, so its allocation may
answer -ENOMEM before any descriptor is read (lib/iov_iter.c:1308-1311,
Linux v6.18.46), on any descriptor `vfs_writev` lets past its mode test
(fs/read_write.c:1037-1038).  No arm of `check_writev` accepts it: the
checker module names no -ENOMEM, and the counts its arms accept stay
below the error range, a channel's and a file's by their
`addr_is_error_b` tests and `/dev/null`'s by the `MAX_RW_COUNT` cap.
Where the arm judges the call it refuses the -ENOMEM: standard output,
the write-only file, a writable `/dev/null` and a pipe's write end over
an array whose ninth descriptor is unreadable, and a writable
`/dev/null` over one the import passes with its nine reads on the
ledger (the first five conjuncts) — the divergence
`bugs/writev-heap-iovec-enomem-not-admitted.md` records.  Where the arm
declines whatever the answer it declines the -ENOMEM too: a fresh socket
and a connected one, a pipe's write end with a nonzero aggregate at a
heap count and at a count of two (`writev_buf_gap`), and the write-only
file with a source shorter than the vector (the next five).
Beside the refusals the answer the kernel gives when the allocation
passes is accepted on each of the four arms (conjuncts eleven through
fifteen): over the unreadable ninth descriptor, the -EFAULT the import
gives with the nine reads, the load of that descriptor faulting in
`copy_iovec_from_user` (lib/iov_iter.c:1263, :1272, :1287-1289); and
over the array the import passes, the writable `/dev/null`'s count of 1
with the nine reads and no source byte read (`write_iter_null`,
drivers/char/mem.c:429-434).  qemu-user's `lock_iovec` answers -ENOMEM
at any count from one to `IOV_MAX` when `g_try_new0` cannot allocate the
host vector (linux-user/syscall.c:3091-3095, QEMU 11.1.1), with nothing
locked yet; the model refuses that in Linux's favour, with no bugs entry
recording it, on standard output at a count of two with the empty
ledger (the sixteenth conjunct), which no Linux records beside an
-ENOMEM there, since at that count the import allocates nothing and
reads both descriptors first.  The seventeenth refuses the -ENOMEM with
the two descriptor reads, and that is Linux's own answer: past the
import a pipe's `anon_pipe_write` answers -ENOMEM when
`anon_pipe_get_page` cannot get a page (fs/pipe.c:124, :515-519, Linux
v6.18.46), before the source is read at :522 — when the pipe is empty or
its last buffer cannot take the bytes, as the section header says — and
a terminal's
`iterate_tty_write` when it cannot allocate its bounce buffer
(drivers/tty/tty_io.c:988-991) — the third of the section header's
refusals with no entry to cite, which the scalar `check_write` makes on
standard output too (`check_write_read_transfer_enomem_is_refused`); beside it standard output's delivery of both bytes,
with the two descriptor reads and the two source bytes on the ledger,
is accepted on the same model (the twenty-second conjunct).  At a count of zero or past `UIO_MAXIOV` no
implementation answers -ENOMEM: `iovec_from_user` tests the count before
it allocates (lib/iov_iter.c:1304-1307), and `lock_iovec` returns before
`g_try_new0` (linux-user/syscall.c:3082-3089, QEMU 11.1.1), so the
eighteenth through twentieth conjuncts refuse it: on standard output at
a count of zero and past the limit, and on the directory past the
limit, where Linux v6.8 and later answer -EBADF first and the older
kernels and qemu-user the count test's -EINVAL.  Beside the count-zero
refusal the zero every implementation answers there is accepted (the
twenty-first conjunct): `vfs_writev` returns it on the empty aggregate
(fs/read_write.c:1047-1049), and qemu-user's `lock_iovec` returns no
vector with errno 0 at a count of zero (linux-user/syscall.c:3082-3085,
QEMU 11.1.1).  The twenty-third refuses the -ENOMEM with the two
descriptor reads on the write-only file of `writev_model`, which is
empty, so the write has a page to allocate, and that is Linux's own
answer as well: `generic_perform_write` returns the error of
`write_begin` when nothing was written yet (mm/filemap.c:4272-4275,
:4331-4332, Linux v6.18.46), and tmpfs's `shmem_write_begin`
(mm/shmem.c:3331-3333) passes on, through `shmem_get_folio` (:2678-2683)
and `shmem_get_folio_gfp` (:2575-2581, :2651), the -ENOMEM
`shmem_alloc_and_add_folio` gives when it cannot allocate that page
(:1942-1943) — the section
header's third class again, which the scalar `check_write` makes on a
file too, the refusal `bugs/write-file-never-falls-short.md` records for
the scalar call.  Beside it the delivery of both bytes into the file is
accepted (the twenty-fourth), as `check_writev_file_lands_at_the_offset`
pins.  The twenty-fifth and twenty-sixth restate the pair on
`read_model`'s write-only file (fd 4, holding one byte), the -ENOMEM
refused and the delivery over that byte accepted; that file holds the
page the write lands in, so its -ENOMEM is not the allocation above but,
for example, the swapped-out or evicted page's.  The
thirty-first refuses the one-byte short count there, the source being
readable throughout, as `check_writev_file_lands_at_the_offset` refuses
it on `writev_model`'s file.  The twenty-seventh
through thirtieth offer a source nothing maps, one entry at 4096 with
only the array readable, on `writev_model`'s file and on standard
output: from v6.14 the file write reaches `write_begin`
(mm/filemap.c:4272) before the copy at :4290 and faults the source in
only after a short copy (:4321), and on the path the section header
names, an empty pipe or a last buffer that cannot take the bytes,
`anon_pipe_write` gets its page (fs/pipe.c:515-519) before the copy at
:522, so the -ENOMEM there is Linux's own and is refused (the
twenty-seventh and twenty-ninth), while the -EFAULT each gives when the
page is had and the copy fails is accepted (the twenty-eighth and
thirtieth): the file write's (mm/filemap.c:4321-4323) and the pipe's
(fs/pipe.c:522-527).  v4.17 through v6.13 fault the source in before
`write_begin`, as the section header says, and give the twenty-eighth's
-EFAULT with no page there.  Beside each -EFAULT the thirty-second
through thirty-fifth refuse, on the file and then on standard output,
the 0 with the descriptor read, which no implementation gives over a
source it cannot copy, and the -EFAULT on the empty ledger, which Linux
never records there, its import reading the descriptor before the copy
fails.  The thirty-sixth and thirty-seventh refuse, on the file and on
standard output, a pipe by the piped-stdio assumption
(bugs/channel-fds-assume-unidirectional-stdio.md), the delivery of the
one byte over that source, which no implementation gives: Linux's copy
from it fails as above, and qemu-user's `lock_iovec` answers -EFAULT
when it cannot lock the first entry's buffer
(QEMU 11.1.1, linux-user/syscall.c:3120, :3125-3128), as
`check_write_read_transfer_enomem_is_refused` refuses it on the scalar
calls.  On Linux a /dev/null standard output answers 1 without reading
(`write_iter_null`), so the thirty-seventh rests on that assumption.
kernel: lib/iov_iter.c:iovec_from_user,copy_iovec_from_user; fs/read_write.c:vfs_writev; drivers/char/mem.c:write_iter_null; fs/pipe.c:anon_pipe_write,anon_pipe_get_page; drivers/tty/tty_io.c:iterate_tty_write; mm/filemap.c:generic_perform_write; mm/shmem.c:shmem_write_begin,shmem_get_folio,shmem_get_folio_gfp,shmem_alloc_and_add_folio@v6.18.46 -/
theorem check_writev_enomem_is_refused_or_declined :
    check_writev_row (writev_in 1 8192 9 mem_readv_eight_zero) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckReject
    ∧ check_writev_row (writev_in 4 8192 9 mem_readv_eight_zero) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckReject
    ∧ check_writev_row (writev_in 9 8192 9 mem_readv_eight_zero) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckReject
    ∧ check_writev_row (writev_in 15 8192 9 mem_readv_eight_zero) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckReject
    ∧ check_writev_row (writev_in 9 8192 9 (iov_array ((4096, 1) :: List.replicate 8 (0, 0))))
        (with_copyins [(8192, 16), (8208, 16), (8224, 16), (8240, 16), (8256, 16), (8272, 16),
          (8288, 16), (8304, 16), (8320, 16)] (mkEffect (errno_ret ENOMEM) [] [])) read_model
      = CheckReject
    ∧ check_writev_row (writev_in 10 8192 9 mem_readv_eight_zero) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 20 8192 9 mem_readv_eight_zero) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 15 8192 9 (iov_array ((4096, 1) :: List.replicate 8 (0, 0))))
        (mkEffect (errno_ret ENOMEM) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 15 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ENOMEM) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row
        (writev_in 4 8192 9 (fun a => if bv_eqb a 4096 then some 97
          else iov_array ((4096, 2) :: List.replicate 8 (0, 0)) a))
        (mkEffect (errno_ret ENOMEM) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 1 8192 9 mem_readv_eight_zero)
        (with_copyins [(8192, 16), (8208, 16), (8224, 16), (8240, 16), (8256, 16), (8272, 16),
          (8288, 16), (8304, 16), (8320, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckOk read_model []
    ∧ check_writev_row (writev_in 4 8192 9 mem_readv_eight_zero)
        (with_copyins [(8192, 16), (8208, 16), (8224, 16), (8240, 16), (8256, 16), (8272, 16),
          (8288, 16), (8304, 16), (8320, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckOk read_model []
    ∧ check_writev_row (writev_in 9 8192 9 mem_readv_eight_zero)
        (with_copyins [(8192, 16), (8208, 16), (8224, 16), (8240, 16), (8256, 16), (8272, 16),
          (8288, 16), (8304, 16), (8320, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckOk read_model []
    ∧ check_writev_row (writev_in 15 8192 9 mem_readv_eight_zero)
        (with_copyins [(8192, 16), (8208, 16), (8224, 16), (8240, 16), (8256, 16), (8272, 16),
          (8288, 16), (8304, 16), (8320, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckOk read_model []
    ∧ check_writev_row (writev_in 9 8192 9 (iov_array ((4096, 1) :: List.replicate 8 (0, 0))))
        (with_copyins [(8192, 16), (8208, 16), (8224, 16), (8240, 16), (8256, 16), (8272, 16),
          (8288, 16), (8304, 16), (8320, 16)] (mkEffect 1 [] [])) read_model
      = CheckOk read_model []
    ∧ check_writev_row (writev_in 1 8192 2 mem_writev_ab) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckReject
    ∧ check_writev_row (writev_in 1 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ENOMEM) [] [])) read_model
      = CheckReject
    ∧ check_writev_row (writev_in 1 8192 0 mem_writev_ab) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckReject
    ∧ check_writev_row (writev_in 1 8192 1025 mem_writev_ab) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckReject
    ∧ (check_writev_row (writev_in 5 8192 1025 mem_writev_ab) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckUnmodeled
      ∧ check_writev_row (writev_in 5 8192 1025 mem_writev_ab) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk read_model [])
    ∧ check_writev_row (writev_in 1 8192 0 mem_writev_ab) (mkEffect 0 [] []) read_model
      = CheckOk read_model []
    ∧ check_writev_row (writev_in 1 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) read_model
      = CheckOk read_model [WriteEv 1 97, WriteEv 1 98]
    ∧ check_writev_row (writev_in 3 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ENOMEM) [] [])) writev_model
      = CheckReject
    ∧ check_writev_row (writev_in 3 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) writev_model
      = CheckOk (with_fds [(3, .FdFileW [102] 2)] (with_fs [([102], [97, 98])] writev_model)) []
    ∧ check_writev_row (writev_in 4 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ENOMEM) [] [])) read_model
      = CheckReject
    ∧ check_writev_row (writev_in 4 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) read_model
      = CheckOk (with_fds (fd_insert (m_fds read_model) 4 (.FdFileW [103] 2))
          (with_fs (fs_set (m_fs read_model) [103] [97, 98]) read_model)) []
    ∧ check_writev_row (writev_in 3 8192 1 (iov_array [(4096, 1)]))
        (with_copyins [(8192, 16)] (mkEffect (errno_ret ENOMEM) [] [])) writev_model
      = CheckReject
    ∧ check_writev_row (writev_in 3 8192 1 (iov_array [(4096, 1)]))
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) writev_model
      = CheckOk writev_model []
    ∧ check_writev_row (writev_in 1 8192 1 (iov_array [(4096, 1)]))
        (with_copyins [(8192, 16)] (mkEffect (errno_ret ENOMEM) [] [])) read_model
      = CheckReject
    ∧ check_writev_row (writev_in 1 8192 1 (iov_array [(4096, 1)]))
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckOk read_model []
    ∧ check_writev_row (writev_in 4 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1)] (mkEffect 1 [] [])) read_model
      = CheckReject
    ∧ check_writev_row (writev_in 3 8192 1 (iov_array [(4096, 1)]))
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) writev_model
      = CheckReject
    ∧ check_writev_row (writev_in 3 8192 1 (iov_array [(4096, 1)]))
        (mkEffect (errno_ret EFAULT) [] []) writev_model
      = CheckReject
    ∧ check_writev_row (writev_in 1 8192 1 (iov_array [(4096, 1)]))
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) read_model
      = CheckReject
    ∧ check_writev_row (writev_in 1 8192 1 (iov_array [(4096, 1)]))
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckReject
    ∧ check_writev_row (writev_in 3 8192 1 (iov_array [(4096, 1)]))
        (with_copyins [(8192, 16), (4096, 1)] (mkEffect 1 [] [])) writev_model
      = CheckReject
    ∧ check_writev_row (writev_in 1 8192 1 (iov_array [(4096, 1)]))
        (with_copyins [(8192, 16), (4096, 1)] (mkEffect 1 [] [])) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-- THE SCALAR CALLS REFUSE THE TRANSFER'S -ENOMEM TOO, the refusal the
section header's third class says the vectored ones inherit.
`check_write` refuses -ENOMEM on standard output (the first conjunct),
on `writev_model`'s empty write-only file (the third) and on
`read_model`'s write-only file (the fifth), which holds the page the
write lands in, so its -ENOMEM is not the allocation of a page the
file does not hold but, for example, the swapped-out or evicted page's,
beside the delivery of both bytes on each (the
second, fourth and sixth), and `check_read` refuses
it on the read-only file holding "hi" (the seventh), beside the
delivery of both bytes (the eighth).  Each is Linux's own answer at
v6.18.46: a pipe's `anon_pipe_write` when `anon_pipe_get_page` cannot
get a page (fs/pipe.c:515-519) on the path an empty pipe or a last
buffer that cannot take the bytes sends it down, a terminal's `iterate_tty_write` when
it cannot allocate its bounce buffer (drivers/tty/tty_io.c:988-991), a
file's `generic_perform_write` returning the error of `write_begin` when
nothing was written (mm/filemap.c:4272-4275, :4331-4332), and a file
read through `filemap_read` returning the -ENOMEM of
`filemap_create_folio` (mm/filemap.c:2567-2568, Linux v6.18.46), reached
through `filemap_get_pages` (:2656, :2760), when nothing was read
(:2834).  The
file write's refusal is `bugs/write-file-never-falls-short.md`'s, which
names `write_begin`'s -ENOMEM; the others have no entry to cite.  On
standard input and its alias fd 26 the -ENOMEM is refused (the ninth
and eleventh) beside the zero at end of input (the tenth and twelfth).
Those rest on standard input being a pipe, as it is under
`testing/syscall-check` (`bugs/channel-fds-assume-unidirectional-stdio.md`):
`anon_pipe_read` has no -ENOMEM of its own (fs/pipe.c:268-404).  The
thirteenth through sixteenth offer a source nothing maps on standard
output and on `writev_model`'s file, the scalar twins of the vectored
pin's twenty-seventh through thirtieth: the -ENOMEM refused (the
thirteenth and fifteenth) and the -EFAULT accepted (the fourteenth and
sixteenth), with the same bounds, the file's -ENOMEM there being a real
answer from v6.14 and the pipe's on the path above, as the section
header says.  The seventeenth refuses the delivery of the one byte on
the file, and the eighteenth on standard output, a pipe by the
piped-stdio assumption (bugs/channel-fds-assume-unidirectional-stdio.md),
which no implementation gives over a source it cannot read: Linux's
copy from it fails, the file's write answering -EFAULT
(mm/filemap.c:4321-4323, Linux v6.18.46), the copy that fails being
v6.14's, since v4.17 through v6.13 fail the fault-in before it (line
4036 of v6.13's mm/filemap.c), and the pipe's answering -EFAULT onto the
last buffer's tail (fs/pipe.c:488-491, Linux v6.18.46) or onto a fresh
page (:522-527),
and qemu-user answers -EFAULT before the host call when it cannot lock
the source for reading (QEMU 11.1.1, linux-user/syscall.c:9848-9849),
as the spec-level `file_write_unreadable_source_is_efault` states on
`write_model`'s file.  On Linux a /dev/null standard output answers 1
without reading (`write_null`, drivers/char/mem.c:418-422, Linux
v6.18.46), so the eighteenth rests on that assumption.
kernel: fs/pipe.c:anon_pipe_write,anon_pipe_get_page,anon_pipe_read; drivers/tty/tty_io.c:iterate_tty_write; mm/filemap.c:generic_perform_write,filemap_read,filemap_create_folio,filemap_get_pages@v6.18.46 -/
theorem check_write_read_transfer_enomem_is_refused :
    check_write_row (write_in 1 4096 2 mem_ab) (mkEffect (errno_ret ENOMEM) [] []) read_model
      = CheckReject
    ∧ check_write_row (write_in 1 4096 2 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        read_model
      = CheckOk read_model [WriteEv 1 97, WriteEv 1 98]
    ∧ check_write_row (write_in 3 4096 2 mem_ab) (mkEffect (errno_ret ENOMEM) [] []) writev_model
      = CheckReject
    ∧ check_write_row (write_in 3 4096 2 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        writev_model
      = CheckOk (with_fds [(3, .FdFileW [102] 2)] (with_fs [([102], [97, 98])] writev_model)) []
    ∧ check_write_row (write_in 4 4096 2 mem_ab) (mkEffect (errno_ret ENOMEM) [] []) read_model
      = CheckReject
    ∧ check_write_row (write_in 4 4096 2 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
        read_model
      = CheckOk (with_fds (fd_insert (m_fds read_model) 4 (.FdFileW [103] 2))
          (with_fs (fs_set (m_fs read_model) [103] [97, 98]) read_model)) []
    ∧ check_read_row (read_in 3 4096 2 (wmem_first 2)) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckReject
    ∧ check_read_row (read_in 3 4096 2 (wmem_first 2)) (mkEffect 2 [(4096, [104, 105])] [])
        read_model
      = CheckOk (with_fds (fd_insert (m_fds read_model) 3 (.FdFile [102] 2)) read_model) []
    ∧ check_read_row (read_in 0 4096 2 (wmem_first 2)) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckReject
    ∧ check_read_row (read_in 0 4096 2 (wmem_first 2)) (mkEffect 0 [] []) read_model
      = CheckOk read_model []
    ∧ check_read_row (read_in 26 4096 2 (wmem_first 2)) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckReject
    ∧ check_read_row (read_in 26 4096 2 (wmem_first 2)) (mkEffect 0 [] []) read_model
      = CheckOk read_model []
    ∧ check_write_row (write_in 1 4096 1 (iov_array [(4096, 1)]))
        (mkEffect (errno_ret ENOMEM) [] []) read_model
      = CheckReject
    ∧ check_write_row (write_in 1 4096 1 (iov_array [(4096, 1)]))
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckOk read_model []
    ∧ check_write_row (write_in 3 4096 1 (iov_array [(4096, 1)]))
        (mkEffect (errno_ret ENOMEM) [] []) writev_model
      = CheckReject
    ∧ check_write_row (write_in 3 4096 1 (iov_array [(4096, 1)]))
        (mkEffect (errno_ret EFAULT) [] []) writev_model
      = CheckOk writev_model []
    ∧ check_write_row (write_in 3 4096 1 (iov_array [(4096, 1)]))
        (with_copyins [(4096, 1)] (mkEffect 1 [] [])) writev_model
      = CheckReject
    ∧ check_write_row (write_in 1 4096 1 (iov_array [(4096, 1)]))
        (with_copyins [(4096, 1)] (mkEffect 1 [] [])) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩ <;> first | rfl | check_norm

/-- THE WRITE-ONLY FILE ANSWERS THE IMPORT AND THE ZERO AGGREGATE ITSELF,
as the channel does: on fd 3 of `writev_model` a second entry whose range
leaves the user address space — `at_top`, 2^47, bytes at 1, one past Sv48's
`TASK_SIZE` (`task_size_is_the_sv48_top`), the ceiling `__access_ok`
reads as `TASK_SIZE_MAX` (include/asm-generic/access_ok.h:15-16, :33,
Linux v6.18.46) — is -EFAULT with both descriptors read (`__import_iovec`'s loop,
lib/iov_iter.c:1377-1385), a narrowed count of 1025 is -EINVAL with
nothing read (`iovec_from_user`, :1306), and an all-empty vector is 0 with
the file and the offset untouched: `vfs_writev` returns the import's error
(fs/read_write.c:1042-1045) and a zero aggregate ahead of `rw_verify_area`
and the write operation (:1047-1049).
kernel: fs/read_write.c:vfs_writev; lib/iov_iter.c:__import_iovec,iovec_from_user; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem check_writev_file_import_and_zero :
    check_writev_row (writev_in 3 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) writev_model
      = CheckOk writev_model []
    ∧ check_writev_row (writev_in 3 8192 1025 mem_writev_ab) (mkEffect (errno_ret EINVAL) [] [])
        writev_model
      = CheckOk writev_model []
    ∧ check_writev_row (writev_in 3 8192 2 (mem_iov_pair 4096 0 4096 0))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) writev_model
      = CheckOk writev_model [] := by
  refine ⟨?_, ?_, ?_⟩ <;> rwv_norm

/-- THE WRITE-ONLY FILE'S TWO MODEL DECLINES: a gather landing
`rw_bytes_max + 1` past the end of an empty file declines — the hole
Linux leaves sparse (`generic_perform_write`, mm/filemap.c:4244-4335,
Linux v6.18.46) is bytes the flat file would have to build, and
`modeled_zero_fill` bounds them — and so does a descriptor onto a path the
file system does not hold, a state no run builds since `openat` never
mints one.  The source is readable throughout in both, so neither reaches
a source decline first.
model: `modeled_zero_fill`'s representation bound and `writev_file_arm`'s absent-path gap, both the model's own; not claims about Linux, which extends the file in the first and never sees the second -/
theorem check_writev_file_model_declines :
    check_writev_row (writev_in 3 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] []))
        writev_far_offset_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 3 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] []))
        (with_fs [] writev_model)
      = CheckUnmodeled := by
  refine ⟨?_, ?_⟩ <;> rwv_norm

/-- A FILE READV IS EXACT: from offset 0 the five bytes split two and three
across the entries, the offset at 5; a short count, a split that ignores
the entry boundary, a missing descriptor ledger and a ledger naming the
destination are refused; from offset 3 the two remaining bytes land in
the first entry; at the end it is 0 with the offset unmoved.  The
eighth refuses the first delivery with the descriptors read in one
32-byte range, the ledger v4.17 through v6.3 record (line 787 of
v4.17's fs/read_write.c, line 1738 of v6.3's lib/iov_iter.c), the fifth
of the section header's refusals with no entry to cite.
`shmem_file_read_iter` copies until the iterator is drained or `i_size`
is reached (mm/shmem.c:3388-3389, :3477-3478, Linux v6.18.46), and the
destination is written, never read.
kernel: mm/shmem.c:shmem_file_read_iter@v6.18.46 -/
theorem check_readv_file_delivery :
    check_readv_row (readv_in 3 8192 2 iov_2_3 (wmem_first 5))
        (with_copyins [(8192, 16), (8208, 16)]
          (mkEffect 5 [(4096, [97, 98]), (4098, [99, 100, 101])] [])) (readv_abcde_model 0)
      = CheckOk (readv_abcde_model 5) []
    ∧ check_readv_row (readv_in 3 8192 2 iov_2_3 (wmem_first 5))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 2 [(4096, [97, 98])] []))
        (readv_abcde_model 0)
      = CheckReject
    ∧ check_readv_row (readv_in 3 8192 2 iov_2_3 (wmem_first 5))
        (with_copyins [(8192, 16), (8208, 16)]
          (mkEffect 5 [(4096, [97, 98, 99]), (4099, [100, 101])] [])) (readv_abcde_model 0)
      = CheckReject
    ∧ check_readv_row (readv_in 3 8192 2 iov_2_3 (wmem_first 5))
        (mkEffect 5 [(4096, [97, 98]), (4098, [99, 100, 101])] []) (readv_abcde_model 0)
      = CheckReject
    ∧ check_readv_row (readv_in 3 8192 2 iov_2_3 (wmem_first 5))
        (with_copyins [(8192, 16), (8208, 16), (4096, 5)]
          (mkEffect 5 [(4096, [97, 98]), (4098, [99, 100, 101])] [])) (readv_abcde_model 0)
      = CheckReject
    ∧ check_readv_row (readv_in 3 8192 2 iov_2_3 (wmem_first 5))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 2 [(4096, [100, 101])] []))
        (readv_abcde_model 3)
      = CheckOk (readv_abcde_model 5) []
    ∧ check_readv_row (readv_in 3 8192 2 iov_2_3 (wmem_first 5))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) (readv_abcde_model 5)
      = CheckOk (readv_abcde_model 5) []
    ∧ check_readv_row (readv_in 3 8192 2 iov_2_3 (wmem_first 5))
        (with_copyins [(8192, 32)]
          (mkEffect 5 [(4096, [97, 98]), (4098, [99, 100, 101])] [])) (readv_abcde_model 0)
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-- A STANDARD-INPUT READV DELIVERS A NONEMPTY PREFIX OF THE STREAM: three
bytes and two are each accepted, the stream advanced by as many and one
event per byte; a 0 while bytes are queued, a split that ignores the
entry boundary and bytes the stream does not hold are refused.  With no
destination byte writable it is -EFAULT with the stream untouched, and
at end of input it is 0.  `anon_pipe_read` (fs/pipe.c:269, Linux
v6.18.46) answers -EFAULT when its first copy stores nothing and leaves
the buffer queued (:343-347).
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem check_readv_stdin_verdicts :
    check_readv_row (readv_in 0 8192 2 iov_2_3 (wmem_first 5))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 3 [(4096, [104, 101]), (4098, [108])] []))
        (with_stdin hello_stdin demo_model)
      = CheckOk (with_stdin (ICons 108 (ICons 111 IEof)) demo_model)
          [ReadEv 0 104, ReadEv 0 101, ReadEv 0 108]
    ∧ check_readv_row (readv_in 0 8192 2 iov_2_3 (wmem_first 5))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) (with_stdin hello_stdin demo_model)
      = CheckReject
    ∧ check_readv_row (readv_in 0 8192 2 iov_2_3 (wmem_first 5))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 3 [(4096, [104, 101, 108])] []))
        (with_stdin hello_stdin demo_model)
      = CheckReject
    ∧ check_readv_row (readv_in 0 8192 2 iov_2_3 (wmem_first 5))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 2 [(4096, [120, 121])] []))
        (with_stdin hello_stdin demo_model)
      = CheckReject
    ∧ check_readv_row (readv_in 0 8192 2 iov_2_3 (wmem_first 5))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 2 [(4096, [104, 101])] []))
        (with_stdin hello_stdin demo_model)
      = CheckOk (with_stdin (ICons 108 (ICons 108 (ICons 111 IEof))) demo_model)
          [ReadEv 0 104, ReadEv 0 101]
    ∧ check_readv_row (readv_in 0 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] []))
        (with_stdin hello_stdin demo_model)
      = CheckOk (with_stdin hello_stdin demo_model) []
    ∧ check_readv_row (readv_in 0 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) demo_model
      = CheckOk demo_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-- THE COUNT IS WHAT WAS COPIED, judged apart from the bytes: with the
five file bytes and the three standard-input bytes written exactly as
delivered, a count one short is refused on each.  `shmem_file_read_iter`
answers the `retval` it accumulates copy by copy (mm/shmem.c:3474, :3487,
Linux v6.18.46), and `anon_pipe_read` adds each buffer's `chars` as it
copies them (fs/pipe.c:349).
kernel: mm/shmem.c:shmem_file_read_iter; fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem check_readv_count_is_what_was_copied :
    check_readv_row (readv_in 3 8192 2 iov_2_3 (wmem_first 5))
        (with_copyins [(8192, 16), (8208, 16)]
          (mkEffect 4 [(4096, [97, 98]), (4098, [99, 100, 101])] [])) (readv_abcde_model 0)
      = CheckReject
    ∧ check_readv_row (readv_in 0 8192 2 iov_2_3 (wmem_first 5))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 2 [(4096, [104, 101]), (4098, [108])] []))
        (with_stdin hello_stdin demo_model)
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwv_norm

/-- AN ALL-EMPTY VECTOR IS 0 BEFORE THE KIND IS CONSULTED: on the directory
it is 0 and not `generic_read_dir`'s -EISDIR (fs/libfs.c:224-227, Linux
v6.18.46), and on standard input holding bytes it is 0 with the stream
untouched — `vfs_readv` returns on a zero aggregate ahead of
`rw_verify_area` and the read operation (fs/read_write.c:1009-1011).  The
ledger is the two descriptors read.
kernel: fs/read_write.c:vfs_readv; fs/libfs.c:generic_read_dir@v6.18.46 -/
theorem check_readv_zero_aggregate_answers_zero :
    check_readv_row (readv_in 5 8192 2 (mem_iov_pair 4096 0 4096 0) (wmem_first 5))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) read_model
      = CheckOk read_model []
    ∧ check_readv_row (readv_in 5 8192 2 (mem_iov_pair 4096 0 4096 0) (wmem_first 5))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EISDIR) [] [])) read_model
      = CheckReject
    ∧ check_readv_row (readv_in 0 8192 2 (mem_iov_pair 4096 0 4096 0) (wmem_first 5))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) (with_stdin hello_stdin demo_model)
      = CheckOk (with_stdin hello_stdin demo_model) [] := by
  refine ⟨?_, ?_, ?_⟩ <;> rwv_norm

/-- For count 2 with {4096,2},{4098,3} and no writable destinations, the checker declines readv
on closed fd 30 and write-only file, pipe and null fds 4, 15 and 9, including their alternate
ledgers; fd 4 also declines count 1025, a first length of 2^63, and a second range
{1,TASK_SIZE}. The readable null and socket controls accept their stated EOF, -ENOTCONN and
-ECONNRESET effects and refuse the offered -EFAULT effects or fresh-socket zero.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_readv_kind_verdicts :
    (check_readv_row (readv_in 30 8192 2 iov_2_3 wmem_none) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
      ∧ check_readv_row (readv_in 30 8192 2 iov_2_3 wmem_none) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk read_model [])
    ∧ check_readv_row (readv_in 4 8192 2 iov_2_3 wmem_none) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 15 8192 2 iov_2_3 wmem_none) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 9 8192 2 iov_2_3 wmem_none) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 8 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) read_model
      = CheckOk read_model []
    ∧ check_readv_row (readv_in 10 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ENOTCONN) [] [])) read_model
      = CheckOk read_model []
    ∧ check_readv_row (readv_in 10 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) read_model
      = CheckReject
    ∧ check_readv_row (readv_in 20 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) read_model
      = CheckOk read_model []
    ∧ check_readv_row (readv_in 21 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ECONNRESET) [] [])) read_model
      = CheckOk (with_fds (fd_insert read_fds 21 (.FdSocket (.SkReset peer_a 7))) read_model) []
    ∧ check_readv_row (readv_in 13 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) read_model
      = CheckOk read_model []
    ∧ check_readv_row (readv_in 4 8192 1025 iov_2_3 wmem_none) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 4 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1) wmem_none)
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 4 8192 2 (mem_iov_pair 4096 1 1 at_top) wmem_none)
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 4 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EBADF) [] [])) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 4 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EBADF) [] [])) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 15 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EBADF) [] [])) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 9 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EBADF) [] [])) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 4 8192 1025 iov_2_3 wmem_none) (mkEffect (errno_ret EINVAL) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 4 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1) wmem_none)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 15 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EBADF) [] [])) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 9 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EBADF) [] [])) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 4 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1) wmem_none)
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EINVAL) [] [])) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 4 8192 2 (mem_iov_pair 4096 1 1 at_top) wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 4 8192 2 (mem_iov_pair 4096 1 1 at_top) wmem_none)
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 30 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 30 8192 2 iov_2_3 wmem_none) (mkEffect (errno_ret EFAULT) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 4 8192 2 iov_2_3 wmem_none) (mkEffect (errno_ret EFAULT) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 15 8192 2 iov_2_3 wmem_none) (mkEffect (errno_ret EFAULT) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 9 8192 2 iov_2_3 wmem_none) (mkEffect (errno_ret EFAULT) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 8 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckReject
    ∧ check_readv_row (readv_in 10 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckReject
    ∧ check_readv_row (readv_in 20 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckReject
    ∧ check_readv_row (readv_in 21 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckReject
    ∧ check_readv_row (readv_in 13 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckReject
    ∧ check_readv_row (readv_in 4 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1) wmem_none)
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 4 8192 2 (mem_iov_pair 4096 1 1 at_top) wmem_none)
        (mkEffect (errno_ret EFAULT) [] []) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 30 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EBADF) [] [])) read_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    <;> rwv_norm

/-- At readv count 2 with {4096,2},{4098,3} and no writable destinations, -ENOMEM is declined on
pipe read end 14, urandom 24, missing-file 7, wrong-end 15 and closed fd 30, but rejected on
regular file 3, readable null 8, fresh socket 10 and EOF stdin 0. The range-fault, negative-
length, unreadable-array and two-empty-entry variants on fds 14, 24 and 7 reject -ENOMEM and
accept their stated -EFAULT, -EINVAL or zero controls; the regular-file fault and stdin EOF
controls are accepted too.
kernel: fs/read_write.c:vfs_readv; lib/iov_iter.c:iovec_from_user,copy_iovec_from_user@v6.18.46 -/
theorem check_readv_enomem_below_the_band :
    (check_readv_row (readv_in 14 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ENOMEM) [] [])) read_model
      = CheckUnmodeled
      ∧ check_readv_row (readv_in 15 8192 2 iov_2_3 wmem_none) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk read_model [])
    ∧ check_readv_row (readv_in 24 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ENOMEM) [] [])) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 7 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ENOMEM) [] [])) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 3 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ENOMEM) [] [])) read_model
      = CheckReject
    ∧ check_readv_row (readv_in 8 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ENOMEM) [] [])) read_model
      = CheckReject
    ∧ check_readv_row (readv_in 10 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ENOMEM) [] [])) read_model
      = CheckReject
    ∧ check_readv_row (readv_in 0 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ENOMEM) [] [])) read_model
      = CheckReject
    ∧ check_readv_row (readv_in 15 8192 2 iov_2_3 wmem_none) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 30 8192 2 iov_2_3 wmem_none) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 14 8192 2 (mem_iov_pair 4096 1 1 at_top) wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ENOMEM) [] [])) read_model
      = CheckReject
    ∧ check_readv_row
        (readv_in 24 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1) wmem_none)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret ENOMEM) [] [])) read_model
      = CheckReject
    ∧ check_readv_row (readv_in 7 8192 2 wmem_none wmem_none)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret ENOMEM) [] [])) read_model
      = CheckReject
    ∧ check_readv_row (readv_in 14 8192 2 (mem_iov_pair 4096 0 4096 0) wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ENOMEM) [] [])) read_model
      = CheckReject
    ∧ check_readv_row (readv_in 24 8192 2 (mem_iov_pair 4096 0 4096 0) wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ENOMEM) [] [])) read_model
      = CheckReject
    ∧ check_readv_row (readv_in 7 8192 2 (mem_iov_pair 4096 0 4096 0) wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ENOMEM) [] [])) read_model
      = CheckReject
    ∧ check_readv_row (readv_in 14 8192 2 (mem_iov_pair 4096 1 1 at_top) wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckOk read_model []
    ∧ check_readv_row (readv_in 14 8192 2 (mem_iov_pair 4096 0 4096 0) wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) read_model
      = CheckOk read_model []
    ∧ check_readv_row (readv_in 3 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckOk read_model []
    ∧ check_readv_row
        (readv_in 24 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1) wmem_none)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) read_model
      = CheckOk read_model []
    ∧ check_readv_row (readv_in 7 8192 2 wmem_none wmem_none)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckOk read_model []
    ∧ check_readv_row (readv_in 24 8192 2 (mem_iov_pair 4096 0 4096 0) wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) read_model
      = CheckOk read_model []
    ∧ check_readv_row (readv_in 7 8192 2 (mem_iov_pair 4096 0 4096 0) wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) read_model
      = CheckOk read_model []
    ∧ check_readv_row (readv_in 0 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) read_model
      = CheckOk read_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩ <;> rwv_norm

/-- Readv with count 0 on readable file fd 3 leaves {4096,2},{4098,3} unused and returns 0 in
both implementations; count 1025 on stdin fd 0 rejects the count with -EINVAL before reading its
eight {0,0} entries. The checker accepts those results and rejects -ENOMEM, but declines count
1025 on write-only file fd 4, where Linux v6.8+'s -EBADF differs from qemu-user's -EINVAL.
kernel: fs/read_write.c:vfs_readv; lib/iov_iter.c:iovec_from_user@v6.18.46 -/
theorem check_readv_enomem_at_counts_that_allocate_nothing :
    check_readv_row (readv_in 3 8192 0 iov_2_3 wmem_none) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckReject
    ∧ check_readv_row (readv_in 0 8192 1025 mem_readv_eight_zero wmem_none)
        (mkEffect (errno_ret ENOMEM) [] []) read_model
      = CheckReject
    ∧ (check_readv_row (readv_in 4 8192 1025 iov_2_3 wmem_none) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckUnmodeled
      ∧ check_readv_row (readv_in 4 8192 1025 iov_2_3 wmem_none) (mkEffect (errno_ret EBADF) [] [])
        read_model ≠ CheckOk read_model [])
    ∧ check_readv_row (readv_in 3 8192 0 iov_2_3 wmem_none) (mkEffect 0 [] []) read_model
      = CheckOk read_model []
    ∧ check_readv_row (readv_in 0 8192 1025 mem_readv_eight_zero wmem_none)
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckOk read_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-- Writev on read-only file fd 3 with counts 1 and 3 through 8 over eight readable {0,0}
entries accepts the shared -EBADF and rejects -ENOMEM. The pin instead declines the offered
-ENOMEM for count 2 over readable "ab" in {4096,1},{4097,1} on read-only file, directory,
urandom, null, pipe and stdin fds 3, 5, 24, 8, 14 and 0, and for readv count 1 with {4096,2} on
write-only file fd 4; its former -EBADF effects are refused too.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- badfdnonempty -/
theorem check_vectored_lock_iovec_enomem_refused_below_the_band :
    check_writev_row (writev_in 3 8192 1 mem_readv_eight_zero) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckReject
    ∧ check_writev_row (writev_in 3 8192 1 mem_readv_eight_zero) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckOk read_model []
    ∧ check_writev_row (writev_in 3 8192 3 mem_readv_eight_zero) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckReject
    ∧ check_writev_row (writev_in 3 8192 3 mem_readv_eight_zero) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckOk read_model []
    ∧ check_writev_row (writev_in 3 8192 4 mem_readv_eight_zero) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckReject
    ∧ check_writev_row (writev_in 3 8192 4 mem_readv_eight_zero) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckOk read_model []
    ∧ check_writev_row (writev_in 3 8192 5 mem_readv_eight_zero) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckReject
    ∧ check_writev_row (writev_in 3 8192 5 mem_readv_eight_zero) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckOk read_model []
    ∧ check_writev_row (writev_in 3 8192 6 mem_readv_eight_zero) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckReject
    ∧ check_writev_row (writev_in 3 8192 6 mem_readv_eight_zero) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckOk read_model []
    ∧ check_writev_row (writev_in 3 8192 7 mem_readv_eight_zero) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckReject
    ∧ check_writev_row (writev_in 3 8192 7 mem_readv_eight_zero) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckOk read_model []
    ∧ check_writev_row (writev_in 3 8192 8 mem_readv_eight_zero) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckReject
    ∧ check_writev_row (writev_in 3 8192 8 mem_readv_eight_zero) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckOk read_model []
    ∧ (check_writev_row (writev_in 3 8192 2 mem_writev_ab) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckUnmodeled
      ∧ check_writev_row (writev_in 3 8192 2 mem_writev_ab) (mkEffect (errno_ret EBADF) [] [])
        read_model ≠ CheckOk read_model [])
    ∧ check_writev_row (writev_in 5 8192 2 mem_writev_ab) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 24 8192 2 mem_writev_ab) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 8 8192 2 mem_writev_ab) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 14 8192 2 mem_writev_ab) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 0 8192 2 mem_writev_ab) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 4 8192 1 iov_2_3 wmem_none) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 4 8192 1 iov_2_3 wmem_none) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩ <;> rwv_norm

/-- On closed fd 30, readv and writev return -EBADF in Linux, but qemu-user returns -EFAULT for
count 9 with only eight {0,0} entries or count 2 with an unreadable array, -EINVAL for count
1025 or a first length of 2^63, and 0 for count 0. The pin declines the listed effects for these
shapes and for writev count 2 with {4096,2},{4098,3} and no source bytes, including the offered
-ENOMEM and zero results.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- badfdnonempty -/
theorem check_vectored_closed_slot_order_declines :
    (check_readv_row (readv_in 30 8192 9 mem_readv_eight_zero wmem_none)
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
      ∧ check_readv_row (readv_in 30 8192 9 mem_readv_eight_zero wmem_none)
        (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk read_model [])
    ∧ check_readv_row
        (readv_in 30 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1) wmem_none)
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 30 8192 9 mem_readv_eight_zero)
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 30 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 30 8192 0 iov_2_3 wmem_none) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 30 8192 0 mem_writev_ab) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 30 8192 9 mem_readv_eight_zero wmem_none)
        (mkEffect (errno_ret ENOMEM) [] []) read_model
      = CheckUnmodeled
    ∧ check_readv_row
        (readv_in 30 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1) wmem_none)
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 30 8192 0 iov_2_3 wmem_none) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 30 8192 9 mem_readv_eight_zero)
        (mkEffect (errno_ret ENOMEM) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 30 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 30 8192 0 iov_2_3 wmem_none) (mkEffect 0 [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 30 8192 0 mem_writev_ab) (mkEffect 0 [] []) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 30 8192 1025 iov_2_3 wmem_none) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 30 8192 1025 mem_writev_ab) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 30 8192 2 wmem_none wmem_none) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 30 8192 2 mem_none) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 30 8192 2 iov_2_3) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 30 8192 1025 iov_2_3 wmem_none)
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 30 8192 1025 mem_writev_ab) (mkEffect (errno_ret EINVAL) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 30 8192 2 wmem_none wmem_none) (mkEffect (errno_ret EFAULT) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 30 8192 2 mem_none) (mkEffect (errno_ret EFAULT) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 30 8192 2 iov_2_3) (mkEffect (errno_ret EFAULT) [] [])
        read_model
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩ <;> rwv_norm

/-- Fd 26 aliases read-only stdin at EOF: the pin declines writev count 2 over readable "ab" in
{4096,1},{4097,1} and the {4096,2^63},{4096,1} variant, including their delivery, -EBADF,
-EINVAL and -ENOMEM effects. Its readv count-2 controls accept 0 for {4096,2},{4098,3} and
-EINVAL for the negative first length, while rejecting -EBADF, -ENOMEM and the bulk-copy ledger
on the negative-length result.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- badfdnonempty -/
theorem check_vectored_stdin_alias_answers_as_stdin :
    (check_writev_row (writev_in 26 8192 2 mem_writev_ab) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckUnmodeled
      ∧ check_writev_row (writev_in 26 8192 2 mem_writev_ab) (mkEffect (errno_ret EBADF) [] [])
        read_model ≠ CheckOk read_model [])
    ∧ check_writev_row (writev_in 26 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EBADF) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 26 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 26 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) read_model
      = CheckOk read_model []
    ∧ check_readv_row (readv_in 26 8192 2 iov_2_3 wmem_none) (mkEffect (errno_ret EBADF) [] [])
        read_model
      = CheckReject
    ∧ check_writev_row (writev_in 26 8192 2 mem_writev_ab)
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EBADF) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 26 8192 2 mem_writev_ab) (mkEffect (errno_ret ENOMEM) [] [])
        read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 26 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ENOMEM) [] [])) read_model
      = CheckReject
    ∧ check_writev_row (writev_in 26 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 26 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 26 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (mkEffect (errno_ret EINVAL) [] []) read_model
      = CheckUnmodeled
    ∧ check_writev_row (writev_in 26 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1))
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EINVAL) [] [])) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 26 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1) wmem_none)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) read_model
      = CheckOk read_model []
    ∧ check_readv_row (readv_in 26 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1) wmem_none)
        (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckReject
    ∧ check_readv_row (readv_in 26 8192 2 (mem_iov_pair 4096 (Z_to_bv 64 (2 ^ 63)) 4096 1) wmem_none)
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EINVAL) [] [])) read_model
      = CheckReject := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-- THE TIMED-OUT CONNECTION (fd 22, `NTimedOut`) on readv as on read:
-ETIMEDOUT once, with the descriptor rewritten to `SkReset`, and
-ECONNRESET refused — the pending error is the one the retransmit timer
stored, `tcp_write_err`'s `sk_err_soft ?: ETIMEDOUT` with no soft error
pending (net/ipv4/tcp_timer.c:76-80, Linux v6.18.46), not the ECONNRESET
`tcp_reset` stores on an RST (net/ipv4/tcp_input.c:4700-4703); `sock_error`'s
`xchg` reads it once (include/net/sock.h:2486-2498).
kernel: net/ipv4/tcp_timer.c:tcp_write_err; net/ipv4/tcp_input.c:tcp_reset; include/net/sock.h:sock_error@v6.18.46 -/
theorem check_readv_timeout_is_etimedout_once :
    check_readv_row (readv_in 22 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ETIMEDOUT) [] [])) read_model
      = CheckOk (with_fds (fd_insert read_fds 22 (.FdSocket (.SkReset peer_a 7))) read_model) []
    ∧ check_readv_row (readv_in 22 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret ECONNRESET) [] [])) read_model
      = CheckReject := by
  refine ⟨?_, ?_⟩ <;> rwv_norm

/-- A CONNECTED SOCKET'S READV IS THE SCALAR READ'S DELIVERY: of the two
queued bytes, both land in the first entry, one event each on channel 7,
with the script advanced past them; a byte the script does not hold is
refused; with no destination byte writable it is -EFAULT with the script
untouched; and with one destination byte of five writable it declines.
`tcp_recvmsg_locked` sees only the iterator and its total, copies
`used = min(skb->len - offset, len)` (net/ipv4/tcp.c:2794-2796, Linux
v6.18.46), answers a first failed copy with -EFAULT before `*seq` moves
(:2822-2828), and advances `*seq` by what it copied (:2855-2856).  A copy
that faults after some bytes answers what whole copies moved, state the
model does not carry — `readv_imported`'s partial-destination paragraph —
hence the decline.
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem check_readv_socket_delivery :
    check_readv_row (readv_in 25 8192 2 iov_2_3 (wmem_first 5))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 2 [(4096, [1, 2])] []))
        (socket_model (NCons 1 (NCons 2 NFin)))
      = CheckOk (with_fds (fd_insert (socket_fds (NCons 1 (NCons 2 NFin))) 25
                  (.FdSocket (.SkConnected peer_a 7 NFin)))
                (socket_model (NCons 1 (NCons 2 NFin))))
          [ReadEv 7 1, ReadEv 7 2]
    ∧ check_readv_row (readv_in 25 8192 2 iov_2_3 (wmem_first 5))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 2 [(4096, [1, 9])] []))
        (socket_model (NCons 1 (NCons 2 NFin)))
      = CheckReject
    ∧ check_readv_row (readv_in 25 8192 2 iov_2_3 wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] []))
        (socket_model (NCons 1 (NCons 2 NFin)))
      = CheckOk (socket_model (NCons 1 (NCons 2 NFin))) []
    ∧ check_readv_row (readv_in 25 8192 2 iov_2_3 (wmem_first 1))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 1 [(4096, [1])] []))
        (socket_model (NCons 1 (NCons 2 NFin)))
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-- THE READV DECLINES, each a delivery the checker would otherwise have to
guess: a pipe read end with its destination writable throughout
(`readv_imported`'s PIPE paragraph: the atomicity argument that makes the
scalar pipe arm deterministic is stated per transfer, not per vector;
`anon_pipe_read`, fs/pipe.c:269, Linux v6.18.46), `/dev/urandom` (fail-closed,
though `urandom_read_iter` at drivers/char/random.c:1453 is derivable), a
file the file system does not hold, and a file whose destination is
writable for one byte of five — `shmem_file_read_iter` answers the bytes
it copied before the short page copy (mm/shmem.c:3474-3487), a count the
model does not carry.
kernel: fs/pipe.c:anon_pipe_read; drivers/char/random.c:urandom_read_iter; mm/shmem.c:shmem_file_read_iter@v6.18.46 -/
theorem check_readv_declines :
    check_readv_row (readv_in 14 8192 2 iov_2_3 (wmem_first 5))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 2 [(4096, [97, 98])] [])) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 24 8192 2 iov_2_3 (wmem_first 5))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 7 8192 2 iov_2_3 (wmem_first 5))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) read_model
      = CheckUnmodeled
    ∧ check_readv_row (readv_in 3 8192 2 iov_2_3 (wmem_first 1))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 1 [(4096, [97])] [])) (readv_abcde_model 0)
      = CheckUnmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rwv_norm

/-! ### The witnesses -/

/-- The writev witness for count 2 over readable "ab" in {4096,1},{4097,1} declines closed fd
30, writes two bytes to writable file fd 3, returns 2 on writable /dev/null fd 9, and returns
-EINVAL at file offset LLONG_MAX. Its count-1 control on writable file fd 3 at EOF returns
-EFAULT for {4096,1} with no readable source, with the stated descriptor ledger and file
updates.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- badfdnonempty -/
theorem writev_witness_names_the_answer :
    writev_witness_row (writev_in 3 8192 2 mem_writev_ab) writev_model
      = Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] []))
          (with_fds [(3, .FdFileW [102] 2)] (with_fs [([102], [97, 98])] writev_model)) []
    ∧ writev_witness_row (writev_in 30 8192 2 mem_writev_ab) read_model
      = Unmodeled
    ∧ writev_witness_row (writev_in 9 8192 2 mem_writev_ab) read_model
      = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 2 [] [])) read_model []
    ∧ writev_witness_row (writev_in 3 8192 2 mem_writev_ab) writev_llong_max_model
      = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EINVAL) [] []))
          writev_llong_max_model []
    ∧ writev_witness_row (writev_in 3 8192 1 (iov_array [(4096, 1)])) wend_model
      = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) wend_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rwv_witness_norm

/-- ON A CHANNEL THE WITNESS NAMES THE ONE-BYTE DELIVERY, the shortest
nonempty prefix of the gathered "ab".  That answer is the channel's
prefix rule, not a pipe's: a blocking pipe write of two readable bytes
copies both (fs/pipe.c:522-547, Linux v6.18.46), so the named answer is
a real one only of the other kinds a channel may be — the recorded
divergence `check_writev_ab_short_delivery` pins on the checker.
model: the witness's choice under the channel's prefix rule, whose one-byte answer is the recorded divergence bugs/write-channel-pipebuf-short-write.md -/
theorem writev_witness_names_the_short_channel_answer :
    writev_witness_row (writev_in 1 8192 2 mem_writev_ab) demo_model
      = Ok (with_copyins [(8192, 16), (8208, 16), (4096, 1)] (mkEffect 1 [] [])) demo_model
          [WriteEv 1 97] := by
  rwv_witness_norm

/-- …AND IS `Unmodeled` WHERE THE CHECKER DECLINES: the unreadable
source past a file's end, the partly readable source on a file, the pipe
write end and the socket — four of the declines
`check_writev_past_eof_unreadable_source_declines`,
`check_writev_partial_source_declines` and `check_writev_declines` pin on
the checker.  The first two rest on `generic_perform_write`'s fault-in
(mm/filemap.c:4321-4324, Linux v6.18.46), whose answer the supported
kernels do not share.
kernel: mm/filemap.c:generic_perform_write@v6.18.46 -/
theorem writev_witness_is_unmodeled_where_the_spec_declines :
    writev_witness_row (writev_in 4 8192 1 (iov_array [(4096, 1)])) wend_model = Unmodeled
    ∧ writev_witness_row (writev_in 3 8192 2 (mem_iov_pair 4096 1 4097 1)) writev_model = Unmodeled
    ∧ writev_witness_row (writev_in 15 8192 2 mem_writev_ab) read_model = Unmodeled
    ∧ writev_witness_row (writev_in 10 8192 2 mem_writev_ab) read_model = Unmodeled := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rwv_witness_norm

/-- For readv count 2 with {4096,2},{4098,3}, the witness delivers one byte from stdin "hello"
or five from file "abcde" when five destinations are writable, and returns -EFAULT for stdin
when none are writable. It declines write-only stdout fd 1 with an unreadable array, returns
-EISDIR on directory fd 5 with {0,0},{0,1}, and returns -EFAULT on stdin when the first
descriptor lacks its base bytes despite its readable length 2^63.
kernel: fs/read_write.c:vfs_readv; fs/libfs.c:generic_read_dir; fs/pipe.c:anon_pipe_read; lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem readv_witness_names_the_answer :
    readv_witness_row (readv_in 0 8192 2 iov_2_3 (wmem_first 5)) (with_stdin hello_stdin demo_model)
      = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 1 [(4096, [104])] []))
          (with_stdin (ICons 101 (ICons 108 (ICons 108 (ICons 111 IEof)))) demo_model)
          [ReadEv 0 104]
    ∧ readv_witness_row (readv_in 3 8192 2 iov_2_3 (wmem_first 5)) (readv_abcde_model 0)
      = Ok (with_copyins [(8192, 16), (8208, 16)]
            (mkEffect 5 [(4096, [97, 98]), (4098, [99, 100, 101])] [])) (readv_abcde_model 5) []
    ∧ readv_witness_row (readv_in 1 8192 2 mem_none wmem_none) demo_model
      = Unmodeled
    ∧ readv_witness_row (readv_in 5 8192 2 (mem_iov_pair 0 0 0 1) wmem_none) read_model
      = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EISDIR) [] [])) read_model []
    ∧ readv_witness_row (readv_in 0 8192 2 iov_2_3 wmem_none) (with_stdin hello_stdin demo_model)
      = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] []))
          (with_stdin hello_stdin demo_model) []
    ∧ readv_witness_row (readv_in 0 8192 2 mem_readv_len_only wmem_none) demo_model
      = Ok (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) demo_model [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rwv_witness_norm

/-- …and on a connected socket it names the one-byte delivery, the
script advanced past that byte alone: a nonempty prefix of what is
queued, the rule `check_readv_socket_delivery` pins on the checker
(`tcp_recvmsg_locked`, net/ipv4/tcp.c:2855-2856, Linux v6.18.46).
kernel: net/ipv4/tcp.c:tcp_recvmsg_locked@v6.18.46 -/
theorem readv_witness_names_the_socket_answer :
    readv_witness_row (readv_in 25 8192 2 iov_2_3 (wmem_first 5)) (socket_model (NCons 1 (NCons 2 NFin)))
      = Ok (with_copyins [(8192, 16), (8208, 16)] (mkEffect 1 [(4096, [1])] []))
          (with_fds (fd_insert (socket_fds (NCons 1 (NCons 2 NFin))) 25
             (.FdSocket (.SkConnected peer_a 7 (NCons 2 NFin))))
           (socket_model (NCons 1 (NCons 2 NFin))))
          [ReadEv 7 1] := by
  rwv_witness_norm

/-- …AND IS `Unmodeled` WHERE THE CHECKER DECLINES: the heap band of
counts, the partly writable destination on standard input, the pipe
read end, `/dev/urandom` and the partly writable destination on a file —
declines `check_readv_heap_iovec_boundary_fails_closed`,
`check_readv_stdin_partial_destination_declines` and
`check_readv_declines` pin on the checker.  The band is
`iovec_from_user`'s `kmalloc_array`, which may answer -ENOMEM
(lib/iov_iter.c:1308-1311, Linux v6.18.46).
kernel: lib/iov_iter.c:iovec_from_user@v6.18.46 -/
theorem readv_witness_is_unmodeled_where_the_spec_declines :
    readv_witness_row (readv_in 0 8192 9 mem_readv_eight_zero wmem_none) demo_model = Unmodeled
    ∧ readv_witness_row (readv_in 0 8192 2 (mem_iov_pair 4096 2 4098 3) (wmem_first 4))
        (with_stdin hello_stdin demo_model) = Unmodeled
    ∧ readv_witness_row (readv_in 14 8192 2 iov_2_3 (wmem_first 5)) read_model = Unmodeled
    ∧ readv_witness_row (readv_in 24 8192 2 iov_2_3 (wmem_first 5)) read_model = Unmodeled
    ∧ readv_witness_row (readv_in 3 8192 2 iov_2_3 (wmem_first 1)) (readv_abcde_model 0)
      = Unmodeled := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rwv_witness_norm

/-- The checker accepts whatever `readv_witness` names and declines where it
declines: `readv_witness_ok` puts the witness's outcome in the spec, and
`check_readv_complete_ok` and `check_readv_complete_unmodeled` carry the
spec back to the checker.  The concrete pins above are this, instance by
instance, with the answer written out.
model: composition of `readv_witness_ok` with the two completeness lemmas, no kernel claim of its own -/
theorem check_readv_accepts_the_witness (fd iov iovcnt : word) (i : SyscallInput) (m : Model) :
    (∀ (eff : SyscallEffect) (m' : Model) (evs : List event),
        readv_witness fd iov iovcnt i m = Ok eff m' evs →
        check_readv i fd iov iovcnt eff m = CheckOk m' evs)
    ∧ (∀ eff : SyscallEffect,
        readv_witness fd iov iovcnt i m = Unmodeled →
        check_readv i fd iov iovcnt eff m = CheckUnmodeled) := by
  refine ⟨?_, ?_⟩
  · intro eff m' evs h
    have hw := readv_witness_ok fd iov iovcnt i m
    rw [h] at hw
    exact check_readv_complete_ok i fd iov iovcnt eff m m' evs hw
  · intro eff h
    have hw := readv_witness_ok fd iov iovcnt i m
    rw [h] at hw
    exact check_readv_complete_unmodeled i fd iov iovcnt eff m hw

/-- The same for `writev_witness` and `check_writev`.
model: composition of `writev_witness_ok` with the two completeness lemmas, no kernel claim of its own -/
theorem check_writev_accepts_the_witness (fd iov iovcnt : word) (i : SyscallInput) (m : Model) :
    (∀ (eff : SyscallEffect) (m' : Model) (evs : List event),
        writev_witness fd iov iovcnt i m = Ok eff m' evs →
        check_writev i fd iov iovcnt eff m = CheckOk m' evs)
    ∧ (∀ eff : SyscallEffect,
        writev_witness fd iov iovcnt i m = Unmodeled →
        check_writev i fd iov iovcnt eff m = CheckUnmodeled) := by
  refine ⟨?_, ?_⟩
  · intro eff m' evs h
    have hw := writev_witness_ok fd iov iovcnt i m
    rw [h] at hw
    exact check_writev_complete_ok i fd iov iovcnt eff m m' evs hw
  · intro eff h
    have hw := writev_witness_ok fd iov iovcnt i m
    rw [h] at hw
    exact check_writev_complete_unmodeled i fd iov iovcnt eff m hw

/-! ### Rocq's closed copy-in accounting examples

Rocq states two of these in `Checks/Sys/Fs/ReadWrite.v` over fixtures
built with `RiscvSemantics.write_to_mem`; the checker module leaves the
fixtures `unported:` (its header says why), and the facts are restated
here under the examples' own names.  The third,
`readv_copyin_reports_the_iovec_table`, reads no fixture and is proved
beside `check_readv`.  The two memories below hold the
same sixteen bytes at 0x2000 and read zero everywhere else, as
`write_to_mem (fun _ => Some 0)` does — the zero background is what
makes the second descriptor readable, so that the stop after an invalid
first one is the walk's and not the memory's. -/

/-- One descriptor at 0x2000, `{ base = 0x3000, len = 2 }`, over zeros:
Rocq's `one_iovec_mem`.  0x2000 is 8192, where `iov_array` lays its
table. -/
def one_iovec_zero_mem : word → Option byte :=
  fun a => match iov_array [(0x3000, 2)] a with
           | some b => some b
           | none => some 0

/-- The same descriptor with the length 2^63, negative as an `ssize_t`:
Rocq's `invalid_first_iovec_mem`. -/
def invalid_first_iovec_zero_mem : word → Option byte :=
  fun a => match iov_array [(0x3000, Z_to_bv 64 (2 ^ 63))] a with
           | some b => some b
           | none => some 0

/-- A writev ledger is the descriptor read and then the delivered source
bytes: 16 at the table and 2 at the base.  The descriptor is read at
import (lib/iov_iter.c:1272-1273, Linux v6.18.46), the source bytes by
the write that consumes them.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem writev_copyin_reports_table_and_delivered_data :
    (copy_iovecs_accesses one_iovec_zero_mem 0x2000 1 ++ iov_prefix_accesses [(0x3000, 2)] 2).map
        (fun p => (bv_unsigned p.1, p.2))
      = [(0x2000, 16), (0x3000, 2)] := by
  rfl

/-- A negative first length stops the walk at the descriptor it was read
from: `copy_iovec_from_user` leaves the loop on `len < 0`
(lib/iov_iter.c:1276-1278, Linux v6.18.46), so the readable second
descriptor is never charged — where the same table with a valid first
length charges both.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem invalid_iovec_charges_only_the_attempted_descriptor :
    copy_iovecs_accesses invalid_first_iovec_zero_mem 0x2000 2 = [(0x2000, 16)]
    ∧ copy_iovecs_accesses one_iovec_zero_mem 0x2000 2 = [(0x2000, 16), (0x2010, 16)] := by
  refine ⟨rfl, rfl⟩


/-- The readable single empty entry has an in-range base and needs no allocation.
Linux v6.8+ tests the mode before importing (fs/read_write.c, vfs_readv /
vfs_writev; b8e1425bae85 and 1c8aa833034a). Linux v4.17 through v6.7
imports first (fs/read_write.c, vfs_readv / vfs_writev, read at v6.6),
then reaches the same mode error in do_iter_read / do_iter_write.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_writev_stdin_channel_is_ebadf :
    check_writev_row (writev_in 0 8192 1 (mem_iov_pair 4096 0 4096 0))
      (mkEffect (errno_ret EBADF) [] []) read_model = CheckOk read_model [] := by
  rwv_norm

/-- The readable single empty entry has an in-range base and needs no allocation.
Linux v6.8+ tests the mode before importing (fs/read_write.c, vfs_readv /
vfs_writev; b8e1425bae85 and 1c8aa833034a). Linux v4.17 through v6.7
imports first (fs/read_write.c, vfs_readv / vfs_writev, read at v6.6),
then reaches the same mode error in do_iter_read / do_iter_write.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_writev_stdin_alias_is_ebadf :
    check_writev_row (writev_in 26 8192 1 (mem_iov_pair 4096 0 4096 0))
      (mkEffect (errno_ret EBADF) [] []) read_model = CheckOk read_model [] := by
  rwv_norm

/-- The readable single empty entry has an in-range base and needs no allocation.
Linux v6.8+ tests the mode before importing (fs/read_write.c, vfs_readv /
vfs_writev; b8e1425bae85 and 1c8aa833034a). Linux v4.17 through v6.7
imports first (fs/read_write.c, vfs_readv / vfs_writev, read at v6.6),
then reaches the same mode error in do_iter_read / do_iter_write.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_writev_urandom_is_ebadf :
    check_writev_row (writev_in 24 8192 1 (mem_iov_pair 4096 0 4096 0))
      (mkEffect (errno_ret EBADF) [] []) read_model = CheckOk read_model [] := by
  rwv_norm

/-- The readable single empty entry has an in-range base and needs no allocation.
Linux v6.8+ tests the mode before importing (fs/read_write.c, vfs_readv /
vfs_writev; b8e1425bae85 and 1c8aa833034a). Linux v4.17 through v6.7
imports first (fs/read_write.c, vfs_readv / vfs_writev, read at v6.6),
then reaches the same mode error in do_iter_read / do_iter_write.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_writev_devnull_read_only_is_ebadf :
    check_writev_row (writev_in 8 8192 1 (mem_iov_pair 4096 0 4096 0))
      (mkEffect (errno_ret EBADF) [] []) read_model = CheckOk read_model [] := by
  rwv_norm

/-- The readable single empty entry has an in-range base and needs no allocation.
Linux v6.8+ tests the mode before importing (fs/read_write.c, vfs_readv /
vfs_writev; b8e1425bae85 and 1c8aa833034a). Linux v4.17 through v6.7
imports first (fs/read_write.c, vfs_readv / vfs_writev, read at v6.6),
then reaches the same mode error in do_iter_read / do_iter_write.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_writev_read_only_file_is_ebadf :
    check_writev_row (writev_in 3 8192 1 (mem_iov_pair 4096 0 4096 0))
      (mkEffect (errno_ret EBADF) [] []) read_model = CheckOk read_model [] := by
  rwv_norm

/-- The readable single empty entry has an in-range base and needs no allocation.
Linux v6.8+ tests the mode before importing (fs/read_write.c, vfs_readv /
vfs_writev; b8e1425bae85 and 1c8aa833034a). Linux v4.17 through v6.7
imports first (fs/read_write.c, vfs_readv / vfs_writev, read at v6.6),
then reaches the same mode error in do_iter_read / do_iter_write.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_writev_directory_is_ebadf :
    check_writev_row (writev_in 5 8192 1 (mem_iov_pair 4096 0 4096 0))
      (mkEffect (errno_ret EBADF) [] []) read_model = CheckOk read_model [] := by
  rwv_norm

/-- The readable single empty entry has an in-range base and needs no allocation.
Linux v6.8+ tests the mode before importing (fs/read_write.c, vfs_readv /
vfs_writev; b8e1425bae85 and 1c8aa833034a). Linux v4.17 through v6.7
imports first (fs/read_write.c, vfs_readv / vfs_writev, read at v6.6),
then reaches the same mode error in do_iter_read / do_iter_write.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_writev_pipe_read_end_is_ebadf :
    check_writev_row (writev_in 14 8192 1 (mem_iov_pair 4096 0 4096 0))
      (mkEffect (errno_ret EBADF) [] []) read_model = CheckOk read_model [] := by
  rwv_norm

/-- The readable single empty entry has an in-range base and needs no allocation.
Linux v6.8+ tests the mode before importing (fs/read_write.c, vfs_readv /
vfs_writev; b8e1425bae85 and 1c8aa833034a). Linux v4.17 through v6.7
imports first (fs/read_write.c, vfs_readv / vfs_writev, read at v6.6),
then reaches the same mode error in do_iter_read / do_iter_write.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_readv_stdout_is_ebadf_before_import :
    check_readv_row (readv_in 1 8192 1 (mem_iov_pair 4096 0 4096 0) wmem_none)
      (mkEffect (errno_ret EBADF) [] []) read_model = CheckOk read_model [] := by
  rwv_norm

/-- The readable single empty entry has an in-range base and needs no allocation.
Linux v6.8+ tests the mode before importing (fs/read_write.c, vfs_readv /
vfs_writev; b8e1425bae85 and 1c8aa833034a). Linux v4.17 through v6.7
imports first (fs/read_write.c, vfs_readv / vfs_writev, read at v6.6),
then reaches the same mode error in do_iter_read / do_iter_write.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_readv_stderr_is_ebadf :
    check_readv_row (readv_in 2 8192 1 (mem_iov_pair 4096 0 4096 0) wmem_none)
      (mkEffect (errno_ret EBADF) [] []) read_model = CheckOk read_model [] := by
  rwv_norm

/-- The readable single empty entry has an in-range base and needs no allocation.
Linux v6.8+ tests the mode before importing (fs/read_write.c, vfs_readv /
vfs_writev; b8e1425bae85 and 1c8aa833034a). Linux v4.17 through v6.7
imports first (fs/read_write.c, vfs_readv / vfs_writev, read at v6.6),
then reaches the same mode error in do_iter_read / do_iter_write.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_readv_devnull_write_only_is_ebadf :
    check_readv_row (readv_in 9 8192 1 (mem_iov_pair 4096 0 4096 0) wmem_none)
      (mkEffect (errno_ret EBADF) [] []) read_model = CheckOk read_model [] := by
  rwv_norm

/-- The readable single empty entry has an in-range base and needs no allocation.
Linux v6.8+ tests the mode before importing (fs/read_write.c, vfs_readv /
vfs_writev; b8e1425bae85 and 1c8aa833034a). Linux v4.17 through v6.7
imports first (fs/read_write.c, vfs_readv / vfs_writev, read at v6.6),
then reaches the same mode error in do_iter_read / do_iter_write.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_readv_pipe_write_end_is_ebadf :
    check_readv_row (readv_in 15 8192 1 (mem_iov_pair 4096 0 4096 0) wmem_none)
      (mkEffect (errno_ret EBADF) [] []) read_model = CheckOk read_model [] := by
  rwv_norm

/-- Eight complete empty descriptors stay on the fast path: UIO_FASTIOV is 8, so v4.17 through v6.7 import them without kmalloc_array (lib/iov_iter.c, iovec_from_user, v6.6) and then reach the mode error; v6.8+ tests the mode first (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46). This is the band's upper edge; nine entries are declined.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_eight_empty_is_ebadf :
    check_writev_row (writev_in 0 8192 8 t139_eight_empty_iovecs)
      (mkEffect (errno_ret EBADF) [] []) read_model = CheckOk read_model [] := by
  rwv_norm

/-- Eight complete empty descriptors stay on the fast path: UIO_FASTIOV is 8, so v4.17 through v6.7 import them without kmalloc_array (lib/iov_iter.c, iovec_from_user, v6.6) and then reach the mode error; v6.8+ tests the mode first (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46). This is the band's upper edge; nine entries are declined.
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_readv_open_eight_empty_is_ebadf :
    check_readv_row (readv_in 1 8192 8 t139_eight_empty_iovecs wmem_none)
      (mkEffect (errno_ret EBADF) [] []) read_model = CheckOk read_model [] := by
  rwv_norm

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_high_empty_is_unmodeled (eff : SyscallEffect) :
    check_writev_row (writev_in 0 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) eff read_model = CheckUnmodeled := by
  rwv_norm

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- wrongmode-highbase -/
theorem check_t139_writev_open_high_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    check_writev_row (writev_in 0 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk m' evs := by
  rw [check_t139_writev_open_high_empty_is_unmodeled]
  intro h
  cases h

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_readv_open_high_empty_is_unmodeled (eff : SyscallEffect) :
    check_readv_row (readv_in 1 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0) wmem_none) eff read_model = CheckUnmodeled := by
  rwv_norm

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv -- wrongmode-highbase -/
theorem check_t139_readv_open_high_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    check_readv_row (readv_in 1 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0) wmem_none) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk m' evs := by
  rw [check_t139_readv_open_high_empty_is_unmodeled]
  intro h
  cases h

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_nine_empty_is_unmodeled (eff : SyscallEffect) :
    check_writev_row (writev_in 0 8192 9 t139_nine_empty_iovecs) eff read_model = CheckUnmodeled := by
  rwv_norm

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_nine_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    check_writev_row (writev_in 0 8192 9 t139_nine_empty_iovecs) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk m' evs := by
  rw [check_t139_writev_open_nine_empty_is_unmodeled]
  intro h
  cases h

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_uncapped_later_is_unmodeled (eff : SyscallEffect) :
    check_writev_row (writev_in 0 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62)))) eff read_model = CheckUnmodeled := by
  rwv_norm

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_uncapped_later_ebadf_is_not_ok (m' : Model) (evs : List event) :
    check_writev_row (writev_in 0 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62)))) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk m' evs := by
  rw [check_t139_writev_open_uncapped_later_is_unmodeled]
  intro h
  cases h

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_file_high_empty_is_unmodeled (eff : SyscallEffect) :
    check_writev_row (writev_in 3 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) eff read_model = CheckUnmodeled := by
  rwv_norm

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_file_high_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    check_writev_row (writev_in 3 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk m' evs := by
  rw [check_t139_writev_open_file_high_empty_is_unmodeled]
  intro h
  cases h

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_file_nine_empty_is_unmodeled (eff : SyscallEffect) :
    check_writev_row (writev_in 3 8192 9 t139_nine_empty_iovecs) eff read_model = CheckUnmodeled := by
  rwv_norm

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_file_nine_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    check_writev_row (writev_in 3 8192 9 t139_nine_empty_iovecs) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk m' evs := by
  rw [check_t139_writev_open_file_nine_empty_is_unmodeled]
  intro h
  cases h

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_file_uncapped_later_is_unmodeled (eff : SyscallEffect) :
    check_writev_row (writev_in 3 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62)))) eff read_model = CheckUnmodeled := by
  rwv_norm

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_file_uncapped_later_ebadf_is_not_ok (m' : Model) (evs : List event) :
    check_writev_row (writev_in 3 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62)))) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk m' evs := by
  rw [check_t139_writev_open_file_uncapped_later_is_unmodeled]
  intro h
  cases h

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_dir_high_empty_is_unmodeled (eff : SyscallEffect) :
    check_writev_row (writev_in 5 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) eff read_model = CheckUnmodeled := by
  rwv_norm

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_dir_high_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    check_writev_row (writev_in 5 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk m' evs := by
  rw [check_t139_writev_open_dir_high_empty_is_unmodeled]
  intro h
  cases h

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_dir_nine_empty_is_unmodeled (eff : SyscallEffect) :
    check_writev_row (writev_in 5 8192 9 t139_nine_empty_iovecs) eff read_model = CheckUnmodeled := by
  rwv_norm

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_dir_nine_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    check_writev_row (writev_in 5 8192 9 t139_nine_empty_iovecs) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk m' evs := by
  rw [check_t139_writev_open_dir_nine_empty_is_unmodeled]
  intro h
  cases h

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_dir_uncapped_later_is_unmodeled (eff : SyscallEffect) :
    check_writev_row (writev_in 5 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62)))) eff read_model = CheckUnmodeled := by
  rwv_norm

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_dir_uncapped_later_ebadf_is_not_ok (m' : Model) (evs : List event) :
    check_writev_row (writev_in 5 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62)))) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk m' evs := by
  rw [check_t139_writev_open_dir_uncapped_later_is_unmodeled]
  intro h
  cases h

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_urandom_high_empty_is_unmodeled (eff : SyscallEffect) :
    check_writev_row (writev_in 24 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) eff read_model = CheckUnmodeled := by
  rwv_norm

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_urandom_high_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    check_writev_row (writev_in 24 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk m' evs := by
  rw [check_t139_writev_open_urandom_high_empty_is_unmodeled]
  intro h
  cases h

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_urandom_nine_empty_is_unmodeled (eff : SyscallEffect) :
    check_writev_row (writev_in 24 8192 9 t139_nine_empty_iovecs) eff read_model = CheckUnmodeled := by
  rwv_norm

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_urandom_nine_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    check_writev_row (writev_in 24 8192 9 t139_nine_empty_iovecs) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk m' evs := by
  rw [check_t139_writev_open_urandom_nine_empty_is_unmodeled]
  intro h
  cases h

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_urandom_uncapped_later_is_unmodeled (eff : SyscallEffect) :
    check_writev_row (writev_in 24 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62)))) eff read_model = CheckUnmodeled := by
  rwv_norm

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_urandom_uncapped_later_ebadf_is_not_ok (m' : Model) (evs : List event) :
    check_writev_row (writev_in 24 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62)))) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk m' evs := by
  rw [check_t139_writev_open_urandom_uncapped_later_is_unmodeled]
  intro h
  cases h

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_devnull_ro_high_empty_is_unmodeled (eff : SyscallEffect) :
    check_writev_row (writev_in 8 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) eff read_model = CheckUnmodeled := by
  rwv_norm

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_devnull_ro_high_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    check_writev_row (writev_in 8 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk m' evs := by
  rw [check_t139_writev_open_devnull_ro_high_empty_is_unmodeled]
  intro h
  cases h

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_devnull_ro_nine_empty_is_unmodeled (eff : SyscallEffect) :
    check_writev_row (writev_in 8 8192 9 t139_nine_empty_iovecs) eff read_model = CheckUnmodeled := by
  rwv_norm

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_devnull_ro_nine_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    check_writev_row (writev_in 8 8192 9 t139_nine_empty_iovecs) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk m' evs := by
  rw [check_t139_writev_open_devnull_ro_nine_empty_is_unmodeled]
  intro h
  cases h

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_devnull_ro_uncapped_later_is_unmodeled (eff : SyscallEffect) :
    check_writev_row (writev_in 8 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62)))) eff read_model = CheckUnmodeled := by
  rwv_norm

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_devnull_ro_uncapped_later_ebadf_is_not_ok (m' : Model) (evs : List event) :
    check_writev_row (writev_in 8 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62)))) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk m' evs := by
  rw [check_t139_writev_open_devnull_ro_uncapped_later_is_unmodeled]
  intro h
  cases h

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_pipe_read_high_empty_is_unmodeled (eff : SyscallEffect) :
    check_writev_row (writev_in 14 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) eff read_model = CheckUnmodeled := by
  rwv_norm

/-- The empty range above TASK_SIZE fails access_ok even at length zero.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_pipe_read_high_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    check_writev_row (writev_in 14 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk m' evs := by
  rw [check_t139_writev_open_pipe_read_high_empty_is_unmodeled]
  intro h
  cases h

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_pipe_read_nine_empty_is_unmodeled (eff : SyscallEffect) :
    check_writev_row (writev_in 14 8192 9 t139_nine_empty_iovecs) eff read_model = CheckUnmodeled := by
  rwv_norm

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_pipe_read_nine_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    check_writev_row (writev_in 14 8192 9 t139_nine_empty_iovecs) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk m' evs := by
  rw [check_t139_writev_open_pipe_read_nine_empty_is_unmodeled]
  intro h
  cases h

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_pipe_read_uncapped_later_is_unmodeled (eff : SyscallEffect) :
    check_writev_row (writev_in 14 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62)))) eff read_model = CheckUnmodeled := by
  rwv_norm

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_writev_open_pipe_read_uncapped_later_ebadf_is_not_ok (m' : Model) (evs : List event) :
    check_writev_row (writev_in 14 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62)))) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk m' evs := by
  rw [check_t139_writev_open_pipe_read_uncapped_later_is_unmodeled]
  intro h
  cases h

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_readv_open_nine_empty_is_unmodeled (eff : SyscallEffect) :
    check_readv_row (readv_in 1 8192 9 t139_nine_empty_iovecs wmem_none) eff read_model = CheckUnmodeled := by
  rwv_norm

/-- Nine entries may fail kmalloc_array with -ENOMEM before the mode test (lib/iov_iter.c, iovec_from_user, v6.6).
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_readv_open_nine_empty_ebadf_is_not_ok (m' : Model) (evs : List event) :
    check_readv_row (readv_in 1 8192 9 t139_nine_empty_iovecs wmem_none) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk m' evs := by
  rw [check_t139_readv_open_nine_empty_is_unmodeled]
  intro h
  cases h

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_readv_open_uncapped_later_is_unmodeled (eff : SyscallEffect) :
    check_readv_row (readv_in 1 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62))) wmem_none) eff read_model = CheckUnmodeled := by
  rwv_norm

/-- The later uncapped range fails access_ok despite its nonnegative length; an empty first entry cannot hide that failure.
Linux v4.17 through v6.7 imports before checking the mode (fs/read_write.c, vfs_writev / vfs_readv, v6.6). In v4.17, fs/read_write.c, rw_copy_check_uvector checks every uncapped range; v6.8+ mode-first gives -EBADF instead (fs/read_write.c, vfs_readv / vfs_writev, v6.18.46).
kernel: fs/read_write.c:vfs_readv,vfs_writev@v6.18.46 -/
theorem check_t139_readv_open_uncapped_later_ebadf_is_not_ok (m' : Model) (evs : List event) :
    check_readv_row (readv_in 1 8192 2 (mem_iov_pair 4096 0 4096 (Z_to_bv 64 (2 ^ 62))) wmem_none) (mkEffect (errno_ret EBADF) [] []) read_model ≠ CheckOk m' evs := by
  rw [check_t139_readv_open_uncapped_later_is_unmodeled]
  intro h
  cases h

/-- A closed fd is rejected by fdget_pos in do_readv / do_writev before import on every supported Linux (fs/read_write.c, v4.17 and v6.18.46). QEMU skips locking a zero-length first buffer (linux-user/syscall.c, lock_iovec, QEMU 11.1.1), so the high empty base does not change -EBADF.
kernel: fs/read_write.c:do_readv,do_writev@v6.18.46 -/
theorem check_t139_readv_closed_high_empty_is_ebadf :
    check_readv_row (readv_in 30 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0) wmem_none) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model [] := by
  rwv_norm

/-- A closed fd is rejected by fdget_pos in do_readv / do_writev before import on every supported Linux (fs/read_write.c, v4.17 and v6.18.46). QEMU skips locking a zero-length first buffer (linux-user/syscall.c, lock_iovec, QEMU 11.1.1), so the high empty base does not change -EBADF.
kernel: fs/read_write.c:do_readv,do_writev@v6.18.46 -/
theorem check_t139_writev_closed_high_empty_is_ebadf :
    check_writev_row (writev_in 30 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 4096 0)) (mkEffect (errno_ret EBADF) [] []) read_model
      = CheckOk read_model [] := by
  rwv_norm

/-- A writable destination lets QEMU reach the EOF answer that Linux may give
without copying a byte: linux-user/syscall.c, lock_iovec, QEMU 11.1.1;
fs/read_write.c, vfs_readv, Linux v6.18.46. Both one-byte destinations
are writable even though the EOF result contains no writes.
kernel: fs/read_write.c:vfs_readv@v6.18.46 -/
theorem t139_readv_open_normal_count_is_ok :
    check_readv_row (readv_in 0 8192 2 (mem_iov_pair 4096 1 4097 1) (wmem_first 2))
      (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) demo_model
      = CheckOk demo_model [] := by
  rwv_norm

end Vectored

-- lean-port sentinel: ticket V-Fs-ReadWrite-readv-writev appends below this line

section VectoredThroughTheTable

/-! ## Vectored examples through the real table

The dispatch lemmas identify the rows at 65 and 66; the pins below reuse
`Vectored`'s checker statements, fixtures and explicit copy-in ledgers.
They keep that section's conjuncts, including its extra rejection pins,
and its documented limitations across implementations. The single-iovec
cap pin keeps the checker conjuncts rather than Rocq's import equalities;
the unreadable-base pin retains its copy-in equality. The two-iovec write
also goes through the registered scalar write row. The LLONG_MAX readv
and partial-destination pins omit Rocq's scalar read conjuncts because
63 has no checked row at this base. The descriptor pins pair the narrowed
success with a bare -EBADF refusal, which distinguishes a whole-word lookup. -/

open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
  (arm_readv ca_check_arm_readv arm_writev ca_check_arm_writev
    lookup_ca_checked_table_readv lookup_ca_checked_table_writev)
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
  (check_syscall check_syscall_of_found)

/-- Dispatch at 65 applies the readv row. Linux v6.18.46,
fs/read_write.c, `SYSCALL_DEFINE3(readv, …)`, reaches `do_readv`;
include/linux/file.h's `DEFINE_CLASS(fd_pos, …)` takes `int fd`, then
fs/file.c's `fdget_pos` takes `unsigned int fd`, represented by `fd32`.
kernel: fs/read_write.c:readv@v6.18.46 -/
theorem check_syscall_readv_in (fd iov iovcnt : word) (mem wmem : word → Option byte)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (readv_in fd iov iovcnt mem wmem) eff m
      = check_readv_row (readv_in fd iov iovcnt mem wmem) eff m := by
  rw [check_syscall_of_found (readv_in fd iov iovcnt mem wmem) eff m arm_readv
        lookup_ca_checked_table_readv, ca_check_arm_readv]
  rfl

/-- Dispatch at 66 applies the writev row. Linux v6.18.46,
fs/read_write.c, `SYSCALL_DEFINE3(writev, …)`, reaches `do_writev`;
include/linux/file.h's `DEFINE_CLASS(fd_pos, …)` takes `int fd`, then
fs/file.c's `fdget_pos` takes `unsigned int fd`, represented by `fd32`.
kernel: fs/read_write.c:writev@v6.18.46 -/
theorem check_syscall_writev_in (fd iov iovcnt : word) (mem : word → Option byte)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (writev_in fd iov iovcnt mem) eff m
      = check_writev_row (writev_in fd iov iovcnt mem) eff m := by
  rw [check_syscall_of_found (writev_in fd iov iovcnt mem) eff m arm_writev
        lookup_ca_checked_table_writev, ca_check_arm_writev]
  rfl

/-- `check_writev_two_iovecs_equals_one_write` through dispatch, with its checker conjuncts.
Linux v6.18.46, fs/read_write.c:1028-1060, `vfs_writev`, hands the imported iterator to the write operation.
The checker-level twin gives the outcome argument and its limits.
kernel: fs/read_write.c:do_writev,vfs_writev,new_sync_write; lib/iov_iter.c:__import_iovec,iov_iter_init@v6.18.46 -/
theorem writev_two_iovecs_equals_one_write_over_the_real_table :
    check_syscall (writev_in 1 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) demo_model
      = check_syscall (write_in 1 4096 2 mem_ab) (with_copyins [(4096, 2)] (mkEffect 2 [] []))
          demo_model
    ∧ check_syscall (writev_in 1 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) demo_model
      = CheckOk demo_model [WriteEv 1 97, WriteEv 1 98] := by
  simp only [check_syscall_writev_in, check_syscall_write_in]
  exact check_writev_two_iovecs_equals_one_write

/-- Through the registered writev table entry, on stdout fd 1 with {4096,1},{4097,1} over
readable "ab", Linux narrows counts 2^32+2 and 2^32 to two and zero, whereas qemu-user returns
-EINVAL; the checker declines the offered two-byte and zero results. Counts 1025 and 2^64-1
exceed IOV_MAX in both readings, so their shared -EINVAL controls are accepted.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- raw2 -/
theorem writev_wide_iovcnt_is_unmodeled_over_the_real_table :
    (check_syscall (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 2)) mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) demo_model
      = CheckUnmodeled
      ∧ check_syscall (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 2)) mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) demo_model ≠ CheckOk demo_model [WriteEv 1 97, WriteEv 1 98])
    ∧ check_syscall (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32)) mem_writev_ab) (mkEffect 0 [] [])
        demo_model
      = CheckUnmodeled
    ∧ check_syscall (writev_in 1 8192 1025 mem_writev_ab) (mkEffect (errno_ret EINVAL) [] [])
        demo_model
      = CheckOk demo_model []
    ∧ check_syscall (writev_in 1 8192 (Z_to_bv 64 (two_pow_64 - 1)) mem_writev_ab)
        (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckOk demo_model [] := by
  simp only [check_syscall_writev_in]
  exact check_writev_wide_iovcnt_is_unmodeled

/-- Through the registered syscall table, writev on stdout fd 1 with count 2^32+2 and
{4096,1},{4097,1} over readable "ab" can deliver two bytes in Linux, while qemu-user returns
-EINVAL. The checker declines both offered answers and rejects -EINVAL at the ordinary count-2
control.
probe: testing/syscall-check/tests/writev_adversarial.c#fail-closed --expect-unmodeled writev -- raw2 -/
theorem writev_over_max_with_small_low32_is_unmodeled_over_the_real_table :
    (check_syscall (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 2)) mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) demo_model
      = CheckUnmodeled
      ∧ check_syscall (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 2)) mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) demo_model ≠ CheckOk demo_model [WriteEv 1 97, WriteEv 1 98])
    ∧ check_syscall (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 2)) mem_writev_ab)
        (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckUnmodeled
    ∧ check_syscall (writev_in 1 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EINVAL) [] [])) demo_model
      = CheckReject := by
  simp only [check_syscall_writev_in]
  exact check_writev_over_max_with_small_low32_is_unmodeled

/-- `check_writev_import_range_fault_beats_the_gather` through dispatch, with its checker conjuncts.
Linux v6.18.46, lib/iov_iter.c:1380-1385, `__import_iovec`, faults at import before gathering; `import_ubuf` at :1437 tests the single range.
The checker-level twin gives the outcome argument and its limits.
kernel: lib/iov_iter.c:__import_iovec,import_ubuf; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem writev_import_range_fault_beats_the_gather_over_the_real_table :
    check_syscall (writev_in 1 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) demo_model
      = CheckOk demo_model []
    ∧ check_syscall (writev_in 1 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (with_copyins [(8192, 16), (8208, 16), (4096, 1)] (mkEffect 1 [] [])) demo_model
      = CheckReject
    ∧ check_syscall (writev_in 1 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 0 0))
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) demo_model
      = CheckOk demo_model []
    ∧ check_syscall (writev_in 1 8192 1 (mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 0 0))
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) demo_model
      = CheckReject
    ∧ check_syscall (writev_in 1 8192 2 (mem_iov_pair 4096 1 1 at_top))
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EFAULT) [] [])) demo_model
      = CheckReject := by
  simp only [check_syscall_writev_in]
  exact check_writev_import_range_fault_beats_the_gather

/-- `check_writev_at_llong_max_is_einval` through dispatch, with its checker conjuncts.
Linux v6.18.46, fs/read_write.c:467-469, `rw_verify_area`, rejects the signed position overflow before the transfer.
The checker-level twin gives the outcome argument and its limits.
kernel: fs/read_write.c:vfs_writev,rw_verify_area@v6.18.46 -/
theorem writev_at_llong_max_is_einval_over_the_real_table :
    check_syscall (writev_in 3 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EINVAL) [] []))
        writev_llong_max_model
      = CheckOk writev_llong_max_model []
    ∧ check_syscall (writev_in 3 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] []))
        writev_llong_max_model
      = CheckReject := by
  simp only [check_syscall_writev_in]
  exact check_writev_at_llong_max_is_einval

/-- A normal count keeps the aggregate-bound control on the answered surface.
kernel: lib/iov_iter.c:__import_iovec,__import_iovec_ubuf,import_ubuf@v6.18.46 -/
theorem writev_over_rw_bytes_max_total_is_judged_over_the_real_table :
    check_syscall (writev_in 1 8192 1
          (mem_iov_pair 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 0))
        (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckReject
    ∧ check_syscall (writev_in 1 8192 1
          (mem_iov_pair 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 0))
        (with_copyins [(8192, 16), (4096, 1)] (mkEffect 1 [] [])) demo_model
      = CheckOk demo_model [WriteEv 1 97]
    ∧ check_syscall (writev_in 1 8192 1 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) demo_model
      = CheckReject
    ∧ check_syscall (writev_in 1 8192 1
          (mem_iov_pair 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 0))
        (with_copyins [(8192, 16), (4096, 2)] (mkEffect 2 [] [])) demo_model
      = CheckReject := by
  simp only [check_syscall_writev_in]
  exact check_writev_over_rw_bytes_max_total_is_judged

/-- Through the registered writev arm, writev on stdout fd 1 uses count 2^32+1 with
{4096,rw_bytes_max+1},{0,0}, only byte 97 readable, or with {4096,1},{4097,1} over "ab". The
checker declines the offered -EINVAL, one-byte and two-byte results, including the mismatched
source ledgers, and refuses acceptance of the former one-byte result.
probe: testing/syscall-check/tests/rw_bytes_bound.c#fail-closed --expect-unmodeled writev -- wv-over-max -/
theorem writev_wide_count_over_rw_bytes_max_is_unmodeled_over_the_real_table :
    (check_syscall (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 1))
          (mem_iov_pair 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 0))
        (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckUnmodeled
      ∧ check_syscall (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 1)) (mem_iov_pair 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 0)) (with_copyins [(8192, 16), (4096, 1)] (mkEffect 1 [] [])) demo_model ≠ CheckOk demo_model [WriteEv 1 97])
    ∧ check_syscall (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 1))
          (mem_iov_pair 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 0))
        (with_copyins [(8192, 16), (4096, 1)] (mkEffect 1 [] [])) demo_model
      = CheckUnmodeled
    ∧ check_syscall (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 1)) mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) demo_model
      = CheckUnmodeled
    ∧ check_syscall (writev_in 1 8192 (Z_to_bv 64 (2 ^ 32 + 1))
          (mem_iov_pair 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 0))
        (with_copyins [(8192, 16), (4096, 2)] (mkEffect 2 [] [])) demo_model
      = CheckUnmodeled := by
  simp only [check_syscall_writev_in]
  exact check_writev_wide_count_over_rw_bytes_max_is_unmodeled

/-- `check_readv_single_iovec_caps_before_access_ok` through dispatch, with its checker conjuncts. Rocq's import equalities are omitted, matching the checker twin.
Linux v6.18.46, lib/iov_iter.c:1435-1438, `import_ubuf`, caps before checking the range; `__import_iovec` at :1380-1388 reverses that order for an array.
The checker-level twin gives the outcome argument and its limits.
kernel: lib/iov_iter.c:import_ubuf,__import_iovec@v6.18.46 -/
theorem readv_single_iovec_caps_before_access_ok_over_the_real_table :
    check_syscall (readv_in 0 8192 1 mem_readv_cap_order wmem_none)
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) demo_model
      = CheckOk demo_model []
    ∧ check_syscall (readv_in 0 8192 2 mem_readv_cap_order wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) demo_model
      = CheckOk demo_model []
    ∧ check_syscall (readv_in 0 8192 2 mem_readv_cap_order wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) demo_model
      = CheckReject
    ∧ check_syscall (readv_in 0 8192 1 mem_readv_cap_order wmem_none)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) demo_model
      = CheckReject := by
  simp only [check_syscall_readv_in]
  exact check_readv_single_iovec_caps_before_access_ok

/-- `check_readv_huge_len_delivers_one_byte_without_unary_expansion` through dispatch, with its checker conjuncts.
Linux v6.18.46, lib/iov_iter.c:1435-1438, `import_ubuf`, caps the single range before its address check.
The checker-level twin gives the outcome argument and its limits.
kernel: lib/iov_iter.c:import_ubuf@v6.18.46 -/
theorem readv_huge_len_delivers_one_byte_without_unary_expansion_over_the_real_table :
    check_syscall (readv_in 0 8192 1 mem_readv_huge wmem_readv_one)
        (with_copyins [(8192, 16)] (mkEffect 1 [(4096, [120])] []))
        (with_stdin (ICons 120 IEof) demo_model)
      = CheckOk (with_stdin IEof demo_model) [ReadEv 0 120]
    ∧ check_syscall (readv_in 3 8192 1 mem_readv_huge wmem_readv_one)
        (with_copyins [(8192, 16)] (mkEffect 1 [(4096, [120])] [])) (readv_x_model 0)
      = CheckOk (readv_x_model 1) []
    ∧ check_syscall (readv_in 0 8192 1 mem_readv_huge wmem_readv_one)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] []))
        (with_stdin (ICons 120 IEof) demo_model)
      = CheckReject
    ∧ check_syscall (readv_in 3 8192 1 mem_readv_huge wmem_readv_one)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) (readv_x_model 0)
      = CheckReject := by
  simp only [check_syscall_readv_in]
  exact check_readv_huge_len_delivers_one_byte_without_unary_expansion

/-- `check_readv_huge_file_offset_is_bounded_by_file_length` through dispatch, with its checker conjuncts.
Linux v6.18.46, mm/shmem.c:3388-3389, `shmem_file_read_iter`, stops at EOF; the single range is capped by lib/iov_iter.c:1435-1438, `import_ubuf`.
The checker-level twin gives the outcome argument and its limits.
kernel: fs/read_write.c:rw_verify_area; mm/shmem.c:shmem_file_read_iter@v6.18.46 -/
theorem readv_huge_file_offset_is_bounded_by_file_length_over_the_real_table :
    check_syscall (readv_in 3 8192 1 mem_readv_huge wmem_readv_one)
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (readv_x_model (Z_to_bv 64 (2 ^ 62)))
      = CheckOk (readv_x_model (Z_to_bv 64 (2 ^ 62))) []
    ∧ check_syscall (readv_in 3 8192 1 mem_readv_huge wmem_readv_one)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] []))
        (readv_x_model (Z_to_bv 64 (2 ^ 62)))
      = CheckReject := by
  simp only [check_syscall_readv_in]
  exact check_readv_huge_file_offset_is_bounded_by_file_length

/-- Through the registered readv table entry, readv uses eight readable {0,0} entries at 8192:
on stdin fd 0 both implementations return 0 at count 8 and -EINVAL at 1025, which the checker
accepts while rejecting -ENOMEM at 8. The pin declines counts 9, 1024 and 2^32+9 on stdin, count
9 on closed fd 5, and counts 9 and 1025 on write-only file fd 3; the absent ninth entry and
oversized count prevent the latter -EBADF cases from being shared answers.
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv -- badfdiov -/
theorem readv_heap_iovec_boundary_fails_closed_over_the_real_table :
    check_syscall (readv_in 0 8192 8 mem_readv_eight_zero wmem_none)
        (with_copyins [(8192, 16), (8208, 16), (8224, 16), (8240, 16), (8256, 16), (8272, 16),
            (8288, 16), (8304, 16)] (mkEffect 0 [] [])) demo_model
      = CheckOk demo_model []
    ∧ check_syscall (readv_in 0 8192 8 mem_readv_eight_zero wmem_none)
        (with_copyins [(8192, 16), (8208, 16), (8224, 16), (8240, 16), (8256, 16), (8272, 16),
            (8288, 16), (8304, 16)] (mkEffect (errno_ret ENOMEM) [] [])) demo_model
      = CheckReject
    ∧ (check_syscall (readv_in 0 8192 9 mem_readv_eight_zero wmem_none) (mkEffect 0 [] [])
        demo_model
      = CheckUnmodeled
      ∧ check_syscall (readv_in 5 8192 9 mem_readv_eight_zero wmem_none) (mkEffect (errno_ret EBADF) [] []) demo_model ≠ CheckOk demo_model [])
    ∧ check_syscall (readv_in 0 8192 9 mem_readv_eight_zero wmem_none)
        (mkEffect (errno_ret ENOMEM) [] []) demo_model
      = CheckUnmodeled
    ∧ check_syscall (readv_in 0 8192 1024 mem_readv_eight_zero wmem_none) (mkEffect 0 [] [])
        demo_model
      = CheckUnmodeled
    ∧ check_syscall (readv_in 5 8192 9 mem_readv_eight_zero wmem_none)
        (mkEffect (errno_ret EBADF) [] []) demo_model
      = CheckUnmodeled
    ∧ check_syscall (readv_in 3 8192 9 mem_readv_eight_zero wmem_none)
        (mkEffect (errno_ret EBADF) [] []) readv_write_only_model
      = CheckUnmodeled
    ∧ check_syscall (readv_in 0 8192 (Z_to_bv 64 (2 ^ 32 + 9)) mem_readv_eight_zero wmem_none)
        (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckUnmodeled
    ∧ check_syscall (readv_in 0 8192 (Z_to_bv 64 (2 ^ 32 + 9)) mem_readv_eight_zero wmem_none)
        (mkEffect (errno_ret ENOMEM) [] []) demo_model
      = CheckUnmodeled
    ∧ check_syscall (readv_in 0 8192 1025 mem_readv_eight_zero wmem_none)
        (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckOk demo_model []
    ∧ check_syscall (readv_in 3 8192 9 mem_readv_eight_zero wmem_none)
        (mkEffect (errno_ret ENOMEM) [] []) readv_write_only_model
      = CheckUnmodeled
    ∧ check_syscall (readv_in 3 8192 9 mem_readv_eight_zero wmem_none)
        (with_copyins [(8192, 16), (8208, 16), (8224, 16), (8240, 16), (8256, 16), (8272, 16),
            (8288, 16), (8304, 16), (8320, 16)] (mkEffect (errno_ret EFAULT) [] []))
        readv_write_only_model
      = CheckUnmodeled
    ∧ check_syscall (readv_in 3 8192 9 mem_readv_eight_zero wmem_none)
        (with_copyins [(8192, 144)] (mkEffect (errno_ret EFAULT) [] [])) readv_write_only_model
      = CheckUnmodeled
    ∧ check_syscall (readv_in 3 8192 1025 mem_readv_eight_zero wmem_none)
        (mkEffect (errno_ret EINVAL) [] []) readv_write_only_model
      = CheckUnmodeled := by
  simp only [check_syscall_readv_in]
  exact check_readv_heap_iovec_boundary_fails_closed

/-- Through the registered readv arm, readv on stdin fd 0 at EOF with count 2^32+1 and one
{4096,1} entry at 8192 returns 0 after Linux narrows the count, but -EINVAL in qemu-user. The
checker declines that zero effect, accepts the count-1 EOF result despite the unwritable
destination, and rejects a count-2 zero result because the second descriptor is absent.
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv --stdin hello -- rawhigh -/
theorem readv_wide_iovcnt_is_unmodeled_over_the_real_table :
    (check_syscall (readv_in 0 8192 (Z_to_bv 64 (2 ^ 32 + 1)) mem_readv_iov wmem_none)
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) demo_model
      = CheckUnmodeled
      ∧ check_syscall (readv_in 0 8192 (Z_to_bv 64 (2 ^ 32 + 1)) mem_readv_iov wmem_none)
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) demo_model ≠ CheckOk demo_model [])
    ∧ check_syscall (readv_in 0 8192 1 mem_readv_iov wmem_none)
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) demo_model
      = CheckOk demo_model []
    ∧ check_syscall (readv_in 0 8192 2 mem_readv_iov wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) demo_model
      = CheckReject := by
  simp only [check_syscall_readv_in]
  exact check_readv_wide_iovcnt_is_unmodeled

/-- Through the registered syscall table, readv on stdin fd 0 at EOF with count 2^32+1 and one
{4096,1} entry at 8192 gives Linux's 0 and qemu-user's -EINVAL. The checker declines both
offered answers and rejects an import-count -EINVAL at the ordinary count-1 control.
probe: testing/syscall-check/tests/readv_spec.c#fail-closed --expect-unmodeled readv --stdin hello -- rawhigh -/
theorem readv_over_max_with_small_low32_is_unmodeled_over_the_real_table :
    (check_syscall (readv_in 0 8192 (Z_to_bv 64 (2 ^ 32 + 1)) mem_readv_iov wmem_none)
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) demo_model
      = CheckUnmodeled
      ∧ check_syscall (readv_in 0 8192 (Z_to_bv 64 (2 ^ 32 + 1)) mem_readv_iov wmem_none)
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) demo_model ≠ CheckOk demo_model [])
    ∧ check_syscall (readv_in 0 8192 (Z_to_bv 64 (2 ^ 32 + 1)) mem_readv_iov wmem_none)
        (mkEffect (errno_ret EINVAL) [] []) demo_model
      = CheckUnmodeled
    ∧ check_syscall (readv_in 0 8192 1 mem_readv_iov wmem_none)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) demo_model
      = CheckReject := by
  simp only [check_syscall_readv_in]
  exact check_readv_over_max_with_small_low32_is_unmodeled

/-- Through the registered readv table entry, readv on write-only stdout fd 1 with count 2 and
an unreadable array at 8192 gives Linux's -EBADF and qemu-user's -EFAULT. The checker declines
the offered -EBADF and the -EFAULT effects with empty, one-descriptor or whole-array copy-in
ledgers.
kernel: fs/read_write.c:vfs_readv; lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem readv_write_only_fd_unreadable_array_is_unmodeled_over_the_real_table :
    (check_syscall (readv_in 1 8192 2 mem_none wmem_none) (mkEffect (errno_ret EBADF) [] [])
        demo_model
      = CheckUnmodeled
      ∧ check_syscall (readv_in 1 8192 2 mem_none wmem_none) (mkEffect (errno_ret EBADF) [] [])
        demo_model ≠ CheckOk demo_model [])
    ∧ check_syscall (readv_in 1 8192 2 mem_none wmem_none)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) demo_model
      = CheckUnmodeled
    ∧ check_syscall (readv_in 1 8192 2 mem_none wmem_none)
        (with_copyins [(8192, 32)] (mkEffect (errno_ret EFAULT) [] [])) demo_model
      = CheckUnmodeled
    ∧ check_syscall (readv_in 1 8192 2 mem_none wmem_none) (mkEffect (errno_ret EFAULT) [] [])
        demo_model
      = CheckUnmodeled := by
  simp only [check_syscall_readv_in]
  exact check_readv_write_only_fd_unreadable_array_is_unmodeled

/-- `check_readv_zero_prefix_then_bad_base_is_efault_on_a_file` through dispatch, with its checker conjuncts.
Linux v6.18.46, mm/shmem.c:3479-3487, `shmem_file_read_iter`, returns -EFAULT when the first copy transfers no bytes.
The checker-level twin gives the outcome argument and its limits.
kernel: mm/shmem.c:shmem_file_read_iter; fs/libfs.c:generic_read_dir@v6.18.46 -/
theorem readv_zero_prefix_then_bad_base_is_efault_on_a_file_over_the_real_table :
    check_syscall (readv_in 3 8192 2 (mem_iov_pair 0 0 0 1) wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] []))
        (readv_abcde_model 0)
      = CheckOk (readv_abcde_model 0) []
    ∧ check_syscall (readv_in 3 8192 2 (mem_iov_pair 0 0 0 1) wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) (readv_abcde_model 0)
      = CheckReject
    ∧ check_syscall (readv_in 3 8192 2 (mem_iov_pair 0 0 0 1) wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EISDIR) [] []))
        (readv_abcde_model 0)
      = CheckReject := by
  simp only [check_syscall_readv_in]
  exact check_readv_zero_prefix_then_bad_base_is_efault_on_a_file

/-- `check_readv_directory_never_consults_the_destination` through dispatch, with its checker conjuncts.
Linux v6.18.46, fs/libfs.c:224-227, `generic_read_dir`, returns -EISDIR without a destination copy.
The checker-level twin gives the outcome argument and its limits.
kernel: fs/libfs.c:generic_read_dir; lib/iov_iter.c:__import_iovec@v6.18.46 -/
theorem readv_directory_never_consults_the_destination_over_the_real_table :
    check_syscall (readv_in 5 8192 2 (mem_iov_pair 0 0 0 1) wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EISDIR) [] [])) read_model
      = CheckOk read_model []
    ∧ check_syscall (readv_in 5 8192 2 (mem_iov_pair 0 0 0 1) wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect 0 [] [])) read_model
      = CheckReject
    ∧ check_syscall (readv_in 5 8192 2 (mem_iov_pair 0 0 0 1) wmem_none)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckReject
    ∧ check_syscall (readv_in 5 8192 2 (mem_iov_pair 4096 1 0 1) wmem_readv_one)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EISDIR) [] [])) read_model
      = CheckOk read_model []
    ∧ check_syscall (readv_in 5 8192 2 (mem_iov_pair 4096 1 0 1) wmem_readv_one)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckReject := by
  simp only [check_syscall_readv_in]
  exact check_readv_directory_never_consults_the_destination

/-- `check_readv_directory_import_range_fault_beats_eisdir` through dispatch, with its checker conjuncts.
Linux v6.18.46, lib/iov_iter.c:1380-1385, `__import_iovec`, returns the range fault before fs/libfs.c:224-227, `generic_read_dir`, is reached.
The checker-level twin gives the outcome argument and its limits.
kernel: lib/iov_iter.c:__import_iovec; include/asm-generic/access_ok.h:__access_ok; fs/libfs.c:generic_read_dir@v6.18.46 -/
theorem readv_directory_import_range_fault_beats_eisdir_over_the_real_table :
    check_syscall (readv_in 5 8192 2 (mem_iov_pair 1 at_top 4096 3) wmem_readv_one)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] [])) read_model
      = CheckOk read_model []
    ∧ check_syscall (readv_in 5 8192 2 (mem_iov_pair 1 at_top 4096 3) wmem_readv_one)
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EISDIR) [] [])) read_model
      = CheckReject := by
  simp only [check_syscall_readv_in]
  exact check_readv_directory_import_range_fault_beats_eisdir

/-- `check_readv_unreadable_base_faults_before_the_sign_test` through dispatch, with its checker conjuncts.
Linux v6.18.46, lib/iov_iter.c:1272-1276, `copy_iovec_from_user`, loads the base before testing the length sign.
The checker-level twin gives the outcome argument and its limits.
kernel: lib/iov_iter.c:copy_iovec_from_user@v6.18.46 -/
theorem readv_unreadable_base_faults_before_the_sign_test_over_the_real_table :
    import_iovecs_accesses mem_readv_len_only 8192 2 = [(8192, 16)]
    ∧ check_syscall (readv_in 0 8192 2 mem_readv_len_only wmem_none)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EFAULT) [] [])) demo_model
      = CheckOk demo_model []
    ∧ check_syscall (readv_in 0 8192 2 mem_readv_len_only wmem_none)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] [])) demo_model
      = CheckReject := by
  simp only [check_syscall_readv_in]
  exact check_readv_unreadable_base_faults_before_the_sign_test

/-- `check_readv_at_llong_max_is_einval` through dispatch, with its checker conjuncts. The scalar read conjuncts are omitted because 63 has no checked row at this base.
Linux v6.18.46, fs/read_write.c:467-469, `rw_verify_area`, rejects signed position overflow before reading.
The checker-level twin gives the outcome argument and its limits.
kernel: fs/read_write.c:vfs_readv,rw_verify_area@v6.18.46 -/
theorem readv_at_llong_max_is_einval_not_eof_over_the_real_table :
    check_syscall (readv_in 3 8192 1 mem_readv_iov wmem_readv_one)
        (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] []))
        (readv_abcde_model (Z_to_bv 64 (2 ^ 63 - 1)))
      = CheckOk (readv_abcde_model (Z_to_bv 64 (2 ^ 63 - 1))) []
    ∧ check_syscall (readv_in 3 8192 1 mem_readv_iov wmem_readv_one)
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) (readv_abcde_model (Z_to_bv 64 (2 ^ 63 - 1)))
      = CheckReject := by
  simp only [check_syscall_readv_in]
  exact check_readv_at_llong_max_is_einval

/-- `check_readv_stdin_partial_destination_declines` through dispatch, with its checker conjuncts.
Linux v6.18.46, fs/pipe.c:343-350, `anon_pipe_read`, handles a short destination copy before consuming the buffer; the twin pins the model decline.
The checker-level twin gives the outcome argument and its limits.
kernel: fs/pipe.c:anon_pipe_read@v6.18.46 -/
theorem partial_destination_on_a_pipe_declines_over_the_real_table :
    check_syscall (readv_in 0 8192 2 (mem_iov_pair 4096 2 4098 3) (wmem_first 4))
        (with_copyins [(8192, 16), (8208, 16)]
          (mkEffect 5 [(4096, [104, 101]), (4098, [108, 108, 111])] []))
        (with_stdin hello_stdin demo_model)
      = CheckUnmodeled
    ∧ check_syscall (readv_in 0 8192 2 (mem_iov_pair 4096 2 4098 3) (wmem_first 4))
        (with_copyins [(8192, 16), (8208, 16)] (mkEffect (errno_ret EFAULT) [] []))
        (with_stdin hello_stdin demo_model)
      = CheckUnmodeled
    ∧ check_syscall (readv_in 0 8192 2 (mem_iov_pair 4096 2 4098 3) (wmem_first 4))
        (with_copyins [(8192, 16), (8208, 16)]
          (mkEffect 4 [(4096, [104, 101]), (4098, [108, 108])] []))
        (with_stdin hello_stdin demo_model)
      = CheckUnmodeled
    ∧ check_syscall (readv_in 0 8192 2 (mem_iov_pair 4096 2 4098 3) (wmem_first 5))
        (with_copyins [(8192, 16), (8208, 16)]
          (mkEffect 5 [(4096, [104, 101]), (4098, [108, 108, 111])] []))
        (with_stdin hello_stdin demo_model)
      = CheckOk (with_stdin IEof demo_model)
          [ReadEv 0 104, ReadEv 0 101, ReadEv 0 108, ReadEv 0 108, ReadEv 0 111] := by
  simp only [check_syscall_readv_in]
  exact check_readv_stdin_partial_destination_declines

/-- The high descriptor bits are discarded: Linux v6.18.46,
fs/read_write.c, `do_writev`, uses include/linux/file.h's
`DEFINE_CLASS(fd_pos, …)` with `int fd`, then fs/file.c's `fdget_pos`
with `unsigned int fd`. This is the positive half of
`check_vectored_fd_truncates_to_32_bits` through dispatch.
kernel: fs/read_write.c:do_writev@v6.18.46 -/
theorem writev_fd_truncates_to_32_bits_over_the_real_table :
    check_syscall (writev_in (Z_to_bv 64 (2 ^ 32 + 1)) 8192 2 mem_writev_ab)
        (with_copyins [(8192, 16), (8208, 16), (4096, 1), (4097, 1)] (mkEffect 2 [] [])) demo_model
      = CheckOk demo_model [WriteEv 1 97, WriteEv 1 98] := by
  simp only [check_syscall_writev_in]
  exact check_vectored_fd_truncates_to_32_bits.1

/-- A bare -EBADF for the whole register is refused. Linux v6.18.46,
fs/read_write.c, `do_writev`, reaches the open low-word descriptor through
include/linux/file.h's `DEFINE_CLASS(fd_pos, …)` and fs/file.c's `fdget_pos`;
fs/read_write.c's `vfs_writev` passes its mode check in this fixture.
`check_vectored_fd_truncates_to_32_bits` gives the checker-level argument.
kernel: fs/read_write.c:do_writev,vfs_writev@v6.18.46 -/
theorem writev_whole_word_ebadf_rejected_over_the_real_table :
    check_syscall (writev_in (Z_to_bv 64 (2 ^ 32 + 1)) 8192 2 mem_writev_ab)
        (mkEffect (errno_ret EBADF) [] []) demo_model
      = CheckReject := by
  simp only [check_syscall_writev_in]
  exact check_vectored_fd_truncates_to_32_bits.2.1

/-- The high descriptor bits are discarded: Linux v6.18.46,
fs/read_write.c, `do_readv`, uses include/linux/file.h's
`DEFINE_CLASS(fd_pos, …)` with `int fd`, then fs/file.c's `fdget_pos`
with `unsigned int fd`. This is the positive half of
`check_vectored_fd_truncates_to_32_bits` through dispatch.
kernel: fs/read_write.c:do_readv@v6.18.46 -/
theorem readv_fd_truncates_to_32_bits_over_the_real_table :
    check_syscall (readv_in (Z_to_bv 64 (2 ^ 32)) 8192 1 mem_readv_iov wmem_none)
        (with_copyins [(8192, 16)] (mkEffect 0 [] [])) demo_model
      = CheckOk demo_model [] := by
  simp only [check_syscall_readv_in]
  exact check_vectored_fd_truncates_to_32_bits.2.2.1

/-- A bare -EBADF for the whole register is refused. Linux v6.18.46,
fs/read_write.c, `do_readv`, reaches the open low-word descriptor through
include/linux/file.h's `DEFINE_CLASS(fd_pos, …)` and fs/file.c's `fdget_pos`;
fs/read_write.c's `vfs_readv` passes its mode check in this fixture.
`check_vectored_fd_truncates_to_32_bits` gives the checker-level argument.
kernel: fs/read_write.c:do_readv,vfs_readv@v6.18.46 -/
theorem readv_whole_word_ebadf_rejected_over_the_real_table :
    check_syscall (readv_in (Z_to_bv 64 (2 ^ 32)) 8192 1 mem_readv_iov wmem_none)
        (mkEffect (errno_ret EBADF) [] []) demo_model
      = CheckReject := by
  simp only [check_syscall_readv_in]
  exact check_vectored_fd_truncates_to_32_bits.2.2.2.1

end VectoredThroughTheTable

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Fs.ReadWrite
