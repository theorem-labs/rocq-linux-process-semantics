-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Sys/Net/Socket.v theories/LinuxProcessSem/Checks/Witness/Net/Socket.v
import LinuxProcessSemantics.LinuxProcessSem.Sys.Net.Socket
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Uaccess
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Uaccess

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058 -/

/-! # LinuxProcessSem.Checks.Sys.Net.Socket — the checkers of `Sys/Net/Socket.lean`, their witnesses, and their proofs

Mirrors two Rocq files: `theories/LinuxProcessSem/Checks/Sys/Net/Socket.v`,
the checkers for the syscalls `Sys/Net/Socket.v` defines and the lemmas
relating each to its spec, and
`theories/LinuxProcessSem/Checks/Witness/Net/Socket.v`, the witnesses with
their `_ok` lemmas.  Both answer to `Sys/Net/Socket.lean`, the twin of the
spec they are judged against, and through it to Linux `net/socket.c` and
`net/ipv4/af_inet.c`.  Not part of the trusted specification: a checker is
executable and a witness is a value, and the lemmas are what tie either to
its spec.  The pins are `Checks/Cases/Checks/Sys/Net/Socket.lean`, the
checkers' verdicts on the fixtures of `Checks/Cases/Net/Socket.lean`.

This file carries all three groups of the two Rocq files: the LIFECYCLE
group, the OPTIONS group and the I/O group — `sendto`, `sendmsg`,
`recvfrom` and `recvmsg`, with the socket half the two sends share and the
descriptor answer the two receives share — the last in a section of its
own after `accept4`, its witnesses closing the witness section.  `socket`
and `accept4` hand back a new descriptor, and their checkers accept it
through `Checks/Sys/Fs/Open.lean`'s `check_new_fd_result`, as Rocq's do
through the same acceptor — which is the one reason this file imports the
`openat` checker; `sendto` and `recvfrom` test their buffer's range
through `Checks/Sys/Uaccess.lean`'s `check_access_ok_zero`, and
`sendto_witness` through `Checks/Witness/Uaccess.lean`'s
`access_ok_zero_witness`, as Rocq's do — `recvfrom_witness` spells
`access_okb` inline, as Rocq's does — which is the one reason for those
two imports.

ONE FILE FOR TWO, and why.  Rocq keeps the checkers under `Checks/Sys/` and
the witnesses under `Checks/Witness/` so that `ExecutableSpecs.v` and
`Progress.v` each import only the half it dispatches.  The Lean tree's
dispatcher takes a record instead — `CheckedArm`, in
`Checks/Sys/Dispatch.lean` — carrying the checker and the witness in one
value with the five proofs between them, so the two halves are written
where that arm will read them.  Every definition keeps its Rocq name.

WHAT IS NOT HERE.  No `CheckedArm` value, no `checked_table` row, no
`arm_unfold` lemma and no frame lemma: registration and the frame lemma
the registered arm owes `Checks/VmMapsDisjoint.lean` are the V ticket's
(linux-process-semantics@ff0313ba4f:docs/lean-port/BRIEF.md, section 5).  What the arm
will build from is the five theorems each syscall carries below —
`check_<name>_sound_ok`, `check_<name>_sound_unmodeled`,
`check_<name>_complete_ok`, `check_<name>_complete_unmodeled` and
`<name>_witness_ok` — stated against the two preludes and the spec twin
and, for `socket` and `accept4`, against `Checks/Sys/Fs/Open.lean` too:
their checkers accept through its `check_new_fd_result`, and their proofs
apply its `check_new_fd_result_ok_inv`, `check_new_fd_result_no_unmodeled`
and `errno_ret_in_alloc_fd`.  How Rocq's arms in `Checks/Sys/Dispatch.v`
apply each checker is restated as the `check_*_row` definitions of
`Checks/Cases/Checks/Sys/Net/Socket.lean`, each held to its registry arm by
a `_row_is_the_arm` theorem there.  `recvmsg`'s `msg`, a1, is not passed at all, the spec never reading
it.  The low-32 narrowing of the fd, of `how`, of the two `level`s and of
setsockopt's `optlen` is the arm's, not the checker's, and the checkers
below see the narrowed words; `socket`'s three words, `accept4`'s flags
and the `flags` of the two sends and of `recvmsg` are narrowed inside the
spec, by `sint32` and `abi_low32`, and the checkers narrow them the same
way.

THE BIND AND I/O DEPARTURES FROM ROCQ follow the spec twin rather than
the Rocq checker, since a checker is judged against its spec.
Rocq's `check_bind` answers -EINVAL on a connected socket whose stream
head is a byte or a FIN (`SkConnected _ _ (NCons _ _)` and `SkConnected _
_ NFin`) and declines only a pending reset or timeout;
`Sys/Net/Socket.lean`'s `bind_spec` declines EVERY connected head, its
docstring saying why the head cell cannot be read as the kernel's state.
So `check_bind` and `bind_witness` below answer `CheckUnmodeled` and
`Unmodeled` on `SkConnected _ _ _` as the twin does, and the two -EINVAL
arms Rocq admits there are outside what this file proves.

In the I/O group, Rocq's `check_send_on_socket` delivers on a connected
socket whose stream head is a byte or a FIN — answering 0 to a
zero-length request and -EFAULT when no byte is readable — and answers
the pending error, consuming it, on one whose head is a reset or a
timeout; `Sys/Net/Socket.lean`'s `send_on_socket` declines both connected
states (its section header says why), so `check_send_on_socket` and
`send_on_socket_witness` answer `SendDead`'s -EPIPE and decline the rest.
That makes two Rocq lemmas false, `check_send_on_socket_no_unmodeled`
and `send_on_socket_no_unmodeled`, which say the socket half never
declines: neither is ported, and `check_send_on_socket_sound_unmodeled`
and `check_send_on_socket_complete_unmodeled` state the directions that
hold instead.  That one is fail-closed, at the cost of every send on a
connected socket.  Rocq's `check_sendmsg` reads the header with
`read_bytes_map` and its six fields with `read_u64`, matching the six
reads together with a second, catch-all arm that is unreachable;
`sendmsg_spec` reads the header with the same `State.read_bytes_map`,
decodes the four fields it reads from the 56 bytes, and imports through
`State.copy_iovecs_aux` with `State.copy_iovecs_accesses` as the ledger,
and `check_sendmsg` and `sendmsg_witness` follow it arm for arm.  And Rocq's `recvfrom_spec`
binds the input it never reads, where the twin's does not, so the
recvfrom proofs peel one reader where Rocq's peel two; no answer changes.

A LEAN-ONLY DECLINE, a decline this file makes where Rocq's checker
answers, the spec twin's and inherited arm for arm: every send on a
connected socket (`check_send_on_socket`'s `SendGoes` and `SendErr`
arms).

SPELLINGS, said once.  Rocq tests `orb (Z.ltb al 0) (Z.ltb
SOCKADDR_STORAGE_SIZE al)`; here it is the `Prop` disjunction `al < 0 ∨
SOCKADDR_STORAGE_SIZE < al` under a decidable `if`, which is how
`Sys/Net/Socket.lean` spells its own gate.  `Z.eqb` is `=` on `Int` under
`if`, `negb` is `¬`, `Z.to_nat al` is `al.toNat`, `length bs` is
`bs.length`, `in_mem i` is `i.in_mem`, `inl`/`inr` are `.inl`/`.inr`, and
`Some`/`None` are `some`/`none`.  The flag tests of `check_socket`,
`check_accept4` and `check_recvmsg`, and of `socket_witness`,
`accept4_witness` and `recvmsg_witness`, are on the `word` (`bv_and`,
`bv_not`, `bv_or`) where Rocq's are on `bv_unsigned` in `Z` (`Z.land`,
`Z.ldiff`), as `Sys/Net/Socket.lean` spells them and for the reason its
header gives.
Each test below is spelled exactly as the
spec spells it, so that one `generalize` or `by_cases` on the shared term
drives both sides of every proof.

Two proof-shape facts, observed while the bind theorems were written and
stated here as observations rather than as a mechanism.  First, `sint32
addrlen` is generalised to `al` immediately after the `unfold`s, before any
`bind_ok0`, `generalize fd_lookup …` or `cases`: with the `sint32`
application still in the goal, the elaborator hit `maxRecDepth` on the
`FdSocket` case at the first `dsimp` (and even with the proof body left
as a bare hole), and moving the `generalize` first removed it.
`Checks/Sys/Kernel/Groups.lean` generalises its gates for the same
reason.  Second, once `cases e` has exposed a constructor under the
spec's `match`, the matcher is reduced with `simp only [] at h ⊢`, never
with `dsimp only`: the `dsimp` form elaborated but failed the kernel with
"deep recursion detected" on every theorem whose reduced hypothesis was
then used (it looked fine when the hypothesis was dropped, and passed
with the kernel's own type check switched off), and the `simp only []`
form is accepted.  A one-match, one-`ite` standalone example did not
reproduce the failure, so what makes this file's terms different is not
pinned; what is recorded is the shape that compiles. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Net.Socket

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.LinuxProcessSem.Sys.Net.Socket
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.File
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Uaccess
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Uaccess

/-! ## The errno-or-success acceptor

The other socket shape: an injected errno, or a fixed return with a new fd
table.  `bind` and `listen` both use it, and both return 0, so the success
return can never be mistaken for an errno; the completeness lemma below
takes that as a hypothesis and each call site discharges it by
evaluation.  Rocq: `check_errno_or_success` at the head of
`Checks/Sys/Net/Socket.v` and its five lemmas after `check_connect`
there. -/

/-- Accept an errno drawn from `es`, leaving the model as it was, or the
return `r` with the table replaced by `fds`.  The shape of the `alt` both
`bind_spec` and `listen_spec` build on a fresh socket: the errno is
`inet_csk_get_port`'s single failure code — the function initialises
`ret = -EADDRINUSE` (net/ipv4/inet_connection_sock.c:500, at :506, Linux
v6.18.46, commit 1f99e9ab748f), every failing path returns it unchanged,
and the one assignment after it is the success `ret = 0` (:581) — reached
from `__inet_bind` (net/ipv4/af_inet.c:473, at :538, Linux v6.18.46) and
from `inet_csk_listen_start` (net/ipv4/inet_connection_sock.c:1345, at
:1366, Linux v6.18.46);
the success side is the state change the call makes.  Rocq:
`Checks.Sys.Net.Socket.check_errno_or_success`. -/
def check_errno_or_success (es : List Int) (fds : List (word × FdEntry)) (r : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | SyscallEffect.mkEffectU ret [] [] [] [] [] =>
      if errno_ret_in es ret then CheckOk m []
      else if bv_eqb ret r then CheckOk (with_fds fds m) [] else CheckReject
  | _ => CheckReject

/-- Rocq: `Checks.Sys.Net.Socket.check_errno_or_success_sound_ok`.  A
`CheckOk` is an outcome of the `alt`: the errno side when the return is in
`es`, the success side when it is `r`. -/
theorem check_errno_or_success_sound_ok (es : List Int) (fds : List (word × FdEntry)) (r : word)
    (i : SyscallInput) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_errno_or_success es fds r eff m = CheckOk m' evs) :
    alt (e <- errno_from es ;; err_ret e) (set_fds fds ;; ret_only r) i m (Ok eff m' evs) := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws with
  | cons w ws => simp only [check_errno_or_success, reduceCtorEq] at h
  | nil =>
  cases zs with
  | cons z zs => simp only [check_errno_or_success, reduceCtorEq] at h
  | nil =>
  cases us with
  | cons u us => simp only [check_errno_or_success, reduceCtorEq] at h
  | nil =>
  cases cs with
  | cons c cs => simp only [check_errno_or_success, reduceCtorEq] at h
  | nil =>
  cases copyins with
  | cons ci copyins => simp only [check_errno_or_success, reduceCtorEq] at h
  | nil =>
  simp only [check_errno_or_success] at h
  cases hin : errno_ret_in es ret with
  | true =>
    simp only [hin, ↓reduceIte, check_result.CheckOk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨e, he, rfl⟩ := (errno_ret_in_true es ret).mp hin
    apply alt_l
    exact bind_ok0 _ _ i m e m _ _ _ (errno_from_witness es e i m he) (pure_ok _ i _)
  | false =>
    simp only [hin, Bool.false_eq_true, ↓reduceIte] at h
    cases heq : bv_eqb ret r with
    | true =>
      simp only [heq, ↓reduceIte, check_result.CheckOk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain rfl := (bv_eqb_eq _ _).mp heq
      apply alt_r
      exact bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m) (pure_ok _ i _)
    | false => simp only [heq, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-- Rocq: `Checks.Sys.Net.Socket.check_errno_or_success_no_unmodeled`.
Neither arm of the acceptor declines. -/
theorem check_errno_or_success_no_unmodeled (es : List Int) (fds : List (word × FdEntry))
    (r : word) (eff : SyscallEffect) (m : Model) :
    check_errno_or_success es fds r eff m ≠ CheckUnmodeled := by
  unfold check_errno_or_success
  split <;> (try split) <;> (try split) <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]

/-- Rocq: `Checks.Sys.Net.Socket.check_errno_or_success_complete_ok`.  The
success return must not read as one of the injectable errnos, or the errno
arm would swallow it and report the wrong model.  Both call sites return 0
and discharge `hne` by evaluation. -/
theorem check_errno_or_success_complete_ok (es : List Int) (fds : List (word × FdEntry))
    (r : word) (i : SyscallInput) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (hne : errno_ret_in es r = false)
    (h : alt (e <- errno_from es ;; err_ret e) (set_fds fds ;; ret_only r) i m (Ok eff m' evs)) :
    check_errno_or_success es fds r eff m = CheckOk m' evs := by
  simp only [Monad.alt, Monad.bind, errno_from, Monad.choose, err_ret, ret_only, Monad.pure,
    set_fds, Monad.modify, outcome.Ok.injEq] at h
  rcases h with ⟨e, m1, evs1, evs2, ⟨x, hx, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl⟩
    | ⟨u, m1, evs1, evs2, ⟨_, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl⟩
  · simp only [check_errno_or_success, errno_ret_in_intro _ _ hx, ↓reduceIte, List.append_nil]
  · simp only [check_errno_or_success, hne, Bool.false_eq_true, ↓reduceIte, bv_eqb_refl,
      List.append_nil]

/-- Rocq: `Checks.Sys.Net.Socket.errno_or_success_no_unmodeled`.  The
`alt` has no `unmodeled` in it: a `choose` and two `pure`s. -/
theorem errno_or_success_no_unmodeled (es : List Int) (fds : List (word × FdEntry)) (r : word)
    (i : SyscallInput) (m : Model) :
    ¬ alt (e <- errno_from es ;; err_ret e) (set_fds fds ;; ret_only r) i m Unmodeled := by
  intro h
  simp only [Monad.alt, Monad.bind, errno_from, Monad.choose, err_ret, ret_only, Monad.pure,
    set_fds, Monad.modify, reduceCtorEq, and_false, exists_false, or_self] at h

/-- Rocq: `Checks.Sys.Net.Socket.check_errno_or_success_complete_unmodeled`.
The premise is unsatisfiable, so the conclusion is free. -/
theorem check_errno_or_success_complete_unmodeled (es : List Int) (fds : List (word × FdEntry))
    (r : word) (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (h : alt (e <- errno_from es ;; err_ret e) (set_fds fds ;; ret_only r) i m Unmodeled) :
    check_errno_or_success es fds r eff m = CheckUnmodeled :=
  absurd h (errno_or_success_no_unmodeled es fds r i m)

/-! ## The ledger bridge for `bind`'s fresh-socket arm

`check_errno_or_success` has no copy-in variant of its own, and giving it
one would duplicate `check_copyins` for a single call site.  So `check_bind`
tests the ledger with `check_copyins` and hands the acceptor the effect
with the ledger stripped, which is what `check_ret_only_copyins` does
internally.  Rocq closes the three directions in place with two `Local
Lemma`s, `record_copyins_of_cleared` and `check_copyins_same`; the Lean
prelude carries the first as `record_copyins_clear_ok`, and the three
lemmas below are the composition each direction needs, stated once so the
`bind` proofs read as the others do. -/

/-- The sound direction: a ledger that matches and an acceptor that accepts
is a `record_copyins` of the `alt`. -/
theorem check_copyins_errno_or_success_sound_ok (es : List Int) (fds : List (word × FdEntry))
    (r : word) (reads : List (word × Nat)) (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_copyins reads eff (check_errno_or_success es fds r (clear_copyins eff) m)
      = CheckOk m' evs) :
    record_copyins reads (alt (e <- errno_from es ;; err_ret e) (set_fds fds ;; ret_only r)) i m
      (Ok eff m' evs) := by
  unfold check_copyins at h
  cases hc : access_ranges_eqb eff.eff_copyins reads
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  · simp only [hc, ↓reduceIte] at h
    exact record_copyins_clear_ok _ _ i m eff m' evs ((access_ranges_eqb_eq _ _).mp hc)
      (check_errno_or_success_sound_ok _ _ _ i _ _ _ _ h)

/-- Neither the ledger test nor the acceptor declines. -/
theorem check_copyins_errno_or_success_no_unmodeled (es : List Int) (fds : List (word × FdEntry))
    (r : word) (reads : List (word × Nat)) (eff : SyscallEffect) (m : Model) :
    check_copyins reads eff (check_errno_or_success es fds r (clear_copyins eff) m)
      ≠ CheckUnmodeled := by
  unfold check_copyins
  cases access_ranges_eqb eff.eff_copyins reads
  · simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true]
  · simp only [↓reduceIte]
    exact check_errno_or_success_no_unmodeled _ _ _ _ _

/-- The complete direction: every `Ok` of the recorded `alt` carries
exactly the recorded ledger over an effect the acceptor accepts. -/
theorem check_copyins_errno_or_success_complete_ok (es : List Int) (fds : List (word × FdEntry))
    (r : word) (reads : List (word × Nat)) (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (hne : errno_ret_in es r = false)
    (h : record_copyins reads (alt (e <- errno_from es ;; err_ret e) (set_fds fds ;; ret_only r))
      i m (Ok eff m' evs)) :
    check_copyins reads eff (check_errno_or_success es fds r (clear_copyins eff) m)
      = CheckOk m' evs := by
  obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
  simp only [Monad.alt, Monad.bind, errno_from, Monad.choose, err_ret, ret_only, Monad.pure,
    set_fds, Monad.modify, outcome.Ok.injEq] at hcore
  rcases hcore with ⟨e, m1, evs1, evs2, ⟨x, hx, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl⟩
    | ⟨u, m1, evs1, evs2, ⟨_, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl⟩
  · simp only [check_copyins, with_copyins, clear_copyins, List.append_nil,
      access_ranges_eqb_refl, ↓reduceIte, check_errno_or_success, errno_ret_in_intro _ _ hx]
  · simp only [check_copyins, with_copyins, clear_copyins, List.append_nil,
      access_ranges_eqb_refl, ↓reduceIte, check_errno_or_success, hne, Bool.false_eq_true,
      bv_eqb_refl]

/-! ## bind (200) -/

/-- The checker for `bind_spec`, arm for arm.  `__sys_bind` (net/socket.c:1889,
Linux v6.18.46, commit 1f99e9ab748f) answers -EBADF on an empty fd (:1896-1897)
and -ENOTSOCK when `sock_from_file` (:530-536) finds another file's ops
(:1898-1900) before `move_addr_to_kernel` (:248) runs at :1902; that copy
answers -EINVAL on a length below 0 or above `sizeof(struct
sockaddr_storage)` (:250-251), returns 0 having moved nothing on a length
of 0 (:252-253) — which `__inet_bind`'s 16-byte minimum
(net/ipv4/af_inet.c:444, Linux v6.18.46, `inet_bind_sk`, at :453-454) then
turns into -EINVAL — and -EFAULT when `copy_from_user` fails (:254-255).  Only
then does `__sys_bind_socket` (:1867) reach `->bind` (:1875), `inet_bind`
(net/ipv4/af_inet.c:467, Linux v6.18.46), whose `__inet_bind` (:473) refuses a
family other than AF_INET with -EAFNOSUPPORT unless it is AF_UNSPEC on
INADDR_ANY (:484-491), answers -EINVAL on a socket that is not TCP_CLOSE or
already has a port (:527-528), and calls `get_port` (:538).

PAST THE COPY, and that is where the ledger starts.  `move_addr_to_kernel`
has really moved `al` bytes out of user memory by the time any of the arms
below the read runs, so each of them expects `eff_copyins` to be exactly
`[(addrp, al)]`, while every arm ABOVE expects it empty: the two
`addrlen`-range -EINVALs return before the copy is attempted and the -EFAULT
arm is the copy FAILING, which transfers nothing.  This mirrors `bind_spec`'s
`record_copyins`, and it is what makes the ledger discriminate rather than
decorate — the two -EINVALs differ in nothing else.  A specific address or
port needs tables a one-process model does not have, so the checker
declines there rather than guesses, and with no ledger test: an `Unmodeled`
carries no effect at all, so there is nothing for a ledger to be right or
wrong about.  On a fresh socket the acceptor is `check_errno_or_success`
behind `check_copyins`, as the header of that section says.  A connected or
reset socket is declined, as the spec twin declines it (the header's
departure from Rocq).  Rocq: `Checks.Sys.Net.Socket.check_bind`. -/
def check_bind (i : SyscallInput) (fd addrp addrlen : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdSocket sk) =>
      (let al := sint32 addrlen
       if al < 0 ∨ SOCKADDR_STORAGE_SIZE < al then check_ret_only eff (errno_ret EINVAL) m []
       else if al = 0 then check_ret_only eff (errno_ret EINVAL) m []
       else
       match read_bytes_map i.in_mem addrp (Z_to_bv 64 al) with
       | none => check_ret_only eff (errno_ret EFAULT) m []
       | some bs =>
           if al < SOCKADDR_IN_SIZE then
             check_ret_only_copyins [(addrp, al.toNat)] eff (errno_ret EINVAL) m []
           else
             let fam := sa_family_of bs
             let port := sin_port_of bs
             let a := sin_addr_of bs
             if ¬ (fam = AF_INET ∨ (fam = AF_UNSPEC ∧ a = INADDR_ANY)) then
               check_ret_only_copyins [(addrp, al.toNat)] eff (errno_ret EAFNOSUPPORT) m []
             else if ¬ (a = INADDR_ANY) then CheckUnmodeled
             else if ¬ (port = 0) then CheckUnmodeled
             else
               match sk with
               | .SkFresh =>
                   check_copyins [(addrp, al.toNat)] eff
                     (check_errno_or_success bind_errnos
                        (fd_insert (m_fds m) fd (.FdSocket .SkBound)) (Z_to_bv 64 0)
                        (clear_copyins eff) m)
               | .SkBound | .SkListening =>
                   check_ret_only_copyins [(addrp, al.toNat)] eff (errno_ret EINVAL) m []
               | .SkReset _ _ => CheckUnmodeled
               | .SkConnected _ _ _ => CheckUnmodeled)
  | some _ => check_ret_only eff (errno_ret ENOTSOCK) m []

/-- Rocq: `Checks.Sys.Net.Socket.check_bind_sound_ok`.  A `CheckOk` is an
outcome of the spec: the same descriptor, length, read and address tests
are taken in the same order, and each accepting leaf is the spec's `pure`
— under `record_copyins` once the address has been read. -/
theorem check_bind_sound_ok (i : SyscallInput) (fd addrp addrlen : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_bind i fd addrp addrlen eff m = CheckOk m' evs) :
    bind_spec fd addrp addrlen i m (Ok eff m' evs) := by
  unfold check_bind at h
  unfold bind_spec
  generalize sint32 addrlen = al at h ⊢
  apply bind_ok0 _ _ i m i m _ _ _ (input_ok i m)
  apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none =>
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | some e =>
    cases e
    case FdSocket sk =>
      simp only [] at h ⊢
      by_cases h1 : al < 0 ∨ SOCKADDR_STORAGE_SIZE < al
      · simp only [h1, ↓reduceIte] at h ⊢
        obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
        exact pure_ok _ i _
      · simp only [h1, ↓reduceIte] at h ⊢
        by_cases h2 : al = 0
        · simp only [h2, ↓reduceIte] at h ⊢
          obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
          exact pure_ok _ i _
        · simp only [h2, ↓reduceIte] at h ⊢
          rcases hr : read_bytes_map i.in_mem addrp (Z_to_bv 64 al) with _ | bs
          · simp only [hr] at h ⊢
            obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
            exact pure_ok _ i _
          · simp only [hr] at h ⊢
            by_cases h3 : al < SOCKADDR_IN_SIZE
            · simp only [h3, ↓reduceIte] at h ⊢
              obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
              exact record_copyins_ok_empty _ _ i _ _ _ _ rfl (pure_ok _ i _)
            · simp only [h3, ↓reduceIte] at h ⊢
              by_cases h4 : sa_family_of bs = AF_INET
                  ∨ (sa_family_of bs = AF_UNSPEC ∧ sin_addr_of bs = INADDR_ANY)
              · simp only [h4, not_true_eq_false, ↓reduceIte] at h ⊢
                by_cases h5 : sin_addr_of bs = INADDR_ANY
                · simp only [h5, not_true_eq_false, ↓reduceIte] at h ⊢
                  by_cases h6 : sin_port_of bs = 0
                  · simp only [h6, not_true_eq_false, ↓reduceIte] at h ⊢
                    cases sk
                    case SkFresh =>
                      exact check_copyins_errno_or_success_sound_ok _ _ _ _ i _ _ _ _ h
                    case SkConnected peer ch rx => simp only [reduceCtorEq] at h
                    case SkReset peer ch => simp only [reduceCtorEq] at h
                    all_goals
                      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
                      exact record_copyins_ok_empty _ _ i _ _ _ _ rfl (pure_ok _ i _)
                  · simp only [h6, not_false_eq_true, ↓reduceIte, reduceCtorEq] at h
                · simp only [h5, not_false_eq_true, ↓reduceIte, reduceCtorEq] at h
              · simp only [h4, not_false_eq_true, ↓reduceIte] at h ⊢
                obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
                exact record_copyins_ok_empty _ _ i _ _ _ _ rfl (pure_ok _ i _)
    all_goals
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _

/-- Rocq: `Checks.Sys.Net.Socket.check_bind_sound_unmodeled`.  The checker
declines exactly where the spec does — a specific address, a nonzero port, a
connected or a reset socket — and every other arm is an acceptor that never
answers `CheckUnmodeled`. -/
theorem check_bind_sound_unmodeled (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_bind i fd addrp addrlen eff m = CheckUnmodeled) :
    bind_spec fd addrp addrlen i m Unmodeled := by
  unfold check_bind at h
  unfold bind_spec
  generalize sint32 addrlen = al at h ⊢
  apply bind_unmodeled2 _ _ i m i m [] (input_ok i m)
  apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | some e =>
    cases e
    case FdSocket sk =>
      simp only [] at h ⊢
      by_cases h1 : al < 0 ∨ SOCKADDR_STORAGE_SIZE < al
      · simp only [h1, ↓reduceIte] at h
        exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
      · simp only [h1, ↓reduceIte] at h ⊢
        by_cases h2 : al = 0
        · simp only [h2, ↓reduceIte] at h
          exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
        · simp only [h2, ↓reduceIte] at h ⊢
          rcases hr : read_bytes_map i.in_mem addrp (Z_to_bv 64 al) with _ | bs
          · simp only [hr] at h
            exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
          · simp only [hr] at h ⊢
            by_cases h3 : al < SOCKADDR_IN_SIZE
            · simp only [h3, ↓reduceIte] at h
              exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)
            · simp only [h3, ↓reduceIte] at h ⊢
              by_cases h4 : sa_family_of bs = AF_INET
                  ∨ (sa_family_of bs = AF_UNSPEC ∧ sin_addr_of bs = INADDR_ANY)
              · simp only [h4, not_true_eq_false, ↓reduceIte] at h ⊢
                by_cases h5 : sin_addr_of bs = INADDR_ANY
                · simp only [h5, not_true_eq_false, ↓reduceIte] at h ⊢
                  by_cases h6 : sin_port_of bs = 0
                  · simp only [h6, not_true_eq_false, ↓reduceIte] at h ⊢
                    cases sk
                    case SkFresh =>
                      exact absurd h (check_copyins_errno_or_success_no_unmodeled _ _ _ _ _ _)
                    case SkConnected peer ch rx =>
                      exact record_copyins_unmodeled _ _ i m (unmodeled_intro i m)
                    case SkReset peer ch =>
                      exact record_copyins_unmodeled _ _ i m (unmodeled_intro i m)
                    all_goals exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)
                  · simp only [h6, not_false_eq_true, ↓reduceIte]
                    exact record_copyins_unmodeled _ _ i m (unmodeled_intro i m)
                · simp only [h5, not_false_eq_true, ↓reduceIte]
                  exact record_copyins_unmodeled _ _ i m (unmodeled_intro i m)
              · simp only [h4, not_false_eq_true, ↓reduceIte] at h
                exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)
    all_goals exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

set_option linter.constructorNameAsVariable false in
/-- Rocq: `Checks.Sys.Net.Socket.check_bind_complete_ok`.  Every outcome the
spec admits is one the checker accepts, with the model and events the spec
produced; the fresh-socket arm discharges `check_errno_or_success`'s side
condition — 0 is not in `bind_errnos` — by evaluation. -/
theorem check_bind_complete_ok (i : SyscallInput) (fd addrp addrlen : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : bind_spec fd addrp addrlen i m (Ok eff m' evs)) :
    check_bind i fd addrp addrlen eff m = CheckOk m' evs := by
  have hne : errno_ret_in bind_errnos (Z_to_bv 64 0) = false := by decide
  unfold bind_spec at h
  unfold check_bind
  generalize sint32 addrlen = al at h ⊢
  have h := bind_input_model_inv _ i m _ h
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none =>
    simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | some e =>
    cases e
    case FdSocket sk =>
      simp only [] at h ⊢
      by_cases h1 : al < 0 ∨ SOCKADDR_STORAGE_SIZE < al
      · simp only [h1, ↓reduceIte] at h ⊢
        simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
      · simp only [h1, ↓reduceIte] at h ⊢
        by_cases h2 : al = 0
        · simp only [h2, ↓reduceIte] at h ⊢
          simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
        · simp only [h2, ↓reduceIte] at h ⊢
          rcases hr : read_bytes_map i.in_mem addrp (Z_to_bv 64 al) with _ | bs
          · simp only [hr] at h ⊢
            simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
          · simp only [hr] at h ⊢
            by_cases h3 : al < SOCKADDR_IN_SIZE
            · simp only [h3, ↓reduceIte] at h ⊢
              obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
              simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at hcore
              obtain ⟨rfl, rfl, rfl⟩ := hcore
              simp only [mkEffect, List.append_nil]
              exact check_ret_only_copyins_refl _ _ _ _
            · simp only [h3, ↓reduceIte] at h ⊢
              by_cases h4 : sa_family_of bs = AF_INET
                  ∨ (sa_family_of bs = AF_UNSPEC ∧ sin_addr_of bs = INADDR_ANY)
              · simp only [h4, not_true_eq_false, ↓reduceIte] at h ⊢
                by_cases h5 : sin_addr_of bs = INADDR_ANY
                · simp only [h5, not_true_eq_false, ↓reduceIte] at h ⊢
                  by_cases h6 : sin_port_of bs = 0
                  · simp only [h6, not_true_eq_false, ↓reduceIte] at h ⊢
                    cases sk
                    case SkFresh =>
                      exact check_copyins_errno_or_success_complete_ok _ _ _ _ i _ _ _ _ hne h
                    case SkConnected peer ch rx =>
                      obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
                      simp only [unmodeled_iff, reduceCtorEq] at hcore
                    case SkReset peer ch =>
                      obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
                      simp only [unmodeled_iff, reduceCtorEq] at hcore
                    all_goals
                      obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
                      simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at hcore
                      obtain ⟨rfl, rfl, rfl⟩ := hcore
                      simp only [mkEffect, List.append_nil]
                      exact check_ret_only_copyins_refl _ _ _ _
                  · simp only [h6, not_false_eq_true, ↓reduceIte] at h
                    obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
                    simp only [unmodeled_iff, reduceCtorEq] at hcore
                · simp only [h5, not_false_eq_true, ↓reduceIte] at h
                  obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
                  simp only [unmodeled_iff, reduceCtorEq] at hcore
              · simp only [h4, not_false_eq_true, ↓reduceIte] at h ⊢
                obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
                simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at hcore
                obtain ⟨rfl, rfl, rfl⟩ := hcore
                simp only [mkEffect, List.append_nil]
                exact check_ret_only_copyins_refl _ _ _ _
    all_goals
      simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

set_option linter.constructorNameAsVariable false in
/-- Rocq: `Checks.Sys.Net.Socket.check_bind_complete_unmodeled`.  Every
decline of the spec is a `CheckUnmodeled` of the checker, whatever effect
the checker is shown: the spec's `unmodeled` sites are exactly the
checker's, and none of them looks at `eff`. -/
theorem check_bind_complete_unmodeled (i : SyscallInput) (fd addrp addrlen : word) (m : Model)
    (eff : SyscallEffect) (h : bind_spec fd addrp addrlen i m Unmodeled) :
    check_bind i fd addrp addrlen eff m = CheckUnmodeled := by
  unfold bind_spec at h
  unfold check_bind
  generalize sint32 addrlen = al at h ⊢
  have h := bind_input_model_inv _ i m _ h
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
  | some e =>
    cases e
    case FdSocket sk =>
      simp only [] at h ⊢
      by_cases h1 : al < 0 ∨ SOCKADDR_STORAGE_SIZE < al
      · simp only [h1, ↓reduceIte, err_ret, ret_only, pure_iff, reduceCtorEq] at h
      · simp only [h1, ↓reduceIte] at h ⊢
        by_cases h2 : al = 0
        · simp only [h2, ↓reduceIte, err_ret, ret_only, pure_iff, reduceCtorEq] at h
        · simp only [h2, ↓reduceIte] at h ⊢
          rcases hr : read_bytes_map i.in_mem addrp (Z_to_bv 64 al) with _ | bs
          · simp only [hr, err_ret, ret_only, pure_iff, reduceCtorEq] at h
          · simp only [hr] at h ⊢
            have h := record_copyins_unmodeled_inv _ _ i m h
            by_cases h3 : al < SOCKADDR_IN_SIZE
            · simp only [h3, ↓reduceIte, err_ret, ret_only, pure_iff, reduceCtorEq] at h
            · simp only [h3, ↓reduceIte] at h ⊢
              by_cases h4 : sa_family_of bs = AF_INET
                  ∨ (sa_family_of bs = AF_UNSPEC ∧ sin_addr_of bs = INADDR_ANY)
              · simp only [h4, not_true_eq_false, ↓reduceIte] at h ⊢
                by_cases h5 : sin_addr_of bs = INADDR_ANY
                · simp only [h5, not_true_eq_false, ↓reduceIte] at h ⊢
                  by_cases h6 : sin_port_of bs = 0
                  · simp only [h6, not_true_eq_false, ↓reduceIte] at h ⊢
                    cases sk
                    case SkFresh => exact absurd h (errno_or_success_no_unmodeled _ _ _ i m)
                    case SkConnected peer ch rx => rfl
                    case SkReset peer ch => rfl
                    all_goals simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
                  · simp only [h6, not_false_eq_true, ↓reduceIte]
                · simp only [h5, not_false_eq_true, ↓reduceIte]
              · simp only [h4, not_false_eq_true, ↓reduceIte, err_ret, ret_only, pure_iff,
                  reduceCtorEq] at h
    all_goals simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h

/-! ## connect (203) -/

/-- The checker for `connect_spec`, arm for arm.  `__sys_connect`
(net/socket.c:2109, Linux v6.18.46, commit 1f99e9ab748f) answers -EBADF on an
empty fd (:2115-2116), then runs `move_addr_to_kernel` (:2118; the -EINVAL
length band and the -EFAULT are `move_addr_to_kernel`'s own at :248, as
`check_bind`'s docstring reads them), and only then does `__sys_connect_file`
(:2086) answer -ENOTSOCK from `sock_from_file` (:2092-2094) or reach
`->connect` (:2103).  So the address is copied — and the ledger charged —
before the descriptor's kind is examined, which is why the `-ENOTSOCK`
arm here sits under the read and carries the copy.  `__inet_stream_connect`
(net/ipv4/af_inet.c:626, Linux v6.18.46) answers -EINVAL on a length below
`sizeof(sa_family)` (:643-644), and on AF_UNSPEC disconnects (:646-648): a
fresh socket has nothing to disconnect and returns 0, while any other state
is a `tcp_disconnect` whose effect the model does not carry, so those
decline.  Otherwise SS_CONNECTED is -EISCONN (:658-659), SS_UNCONNECTED
proceeds only from TCP_CLOSE (:668-670) — a listening socket is not, so it
too is -EISCONN — and `tcp_v4_connect` (net/ipv4/tcp_ipv4.c:222, Linux
v6.18.46) refuses a length below `sizeof(struct sockaddr_in)` with -EINVAL
(:236-237) and a family other than AF_INET with -EAFNOSUPPORT (:239-240).  A
reset socket is still SS_CONNECTED at :658, as the spec's `SkReset` arm
records. The attempt itself is the environment's, so it declines.

ONE SPELLING DIFFERENCE from Rocq, which binds the ledger entry once as
`let copied := …` and uses it in eight leaves: here the `if al = 0 then []
else [(addrp, bs.length)]` is written out at each leaf.  With the `let` in
place, every theorem below failed the kernel with "deep recursion
detected" at the first `simp only []` that reduced the checker's outer
match — a scratch variant with the same `let` over a single leaf failed the
same way, and the inlined body passed with nothing else changed.  The
mechanism is not pinned; the shape that compiles is.  Rocq:
`Checks.Sys.Net.Socket.check_connect`. -/
def check_connect (i : SyscallInput) (fd addrp addrlen : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some e =>
      let al := sint32 addrlen
      if al < 0 ∨ SOCKADDR_STORAGE_SIZE < al then check_ret_only eff (errno_ret EINVAL) m []
      else
      match read_bytes_map i.in_mem addrp (Z_to_bv 64 al) with
      | none => check_ret_only eff (errno_ret EFAULT) m []
      | some bs =>
          match e with
          | .FdSocket sk =>
              (if al < SA_FAMILY_SIZE then
                 check_ret_only_copyins (if al = 0 then [] else [(addrp, bs.length)]) eff
                   (errno_ret EINVAL) m []
               else if sa_family_of bs = AF_UNSPEC then
                 (match sk with
                  | .SkFresh =>
                      check_ret_only_copyins (if al = 0 then [] else [(addrp, bs.length)]) eff
                        (Z_to_bv 64 0) m []
                  | .SkBound | .SkListening | .SkConnected _ _ _ | .SkReset _ _ => CheckUnmodeled)
               else
                 (match sk with
                  | .SkListening | .SkConnected _ _ _ | .SkReset _ _ =>
                      check_ret_only_copyins (if al = 0 then [] else [(addrp, bs.length)]) eff
                        (errno_ret EISCONN) m []
                  | .SkFresh | .SkBound =>
                      if al < SOCKADDR_IN_SIZE then
                        check_ret_only_copyins (if al = 0 then [] else [(addrp, bs.length)]) eff
                          (errno_ret EINVAL) m []
                      else if ¬ (sa_family_of bs = AF_INET) then
                        check_ret_only_copyins (if al = 0 then [] else [(addrp, bs.length)]) eff
                          (errno_ret EAFNOSUPPORT) m []
                      else CheckUnmodeled))
          | _ =>
              check_ret_only_copyins (if al = 0 then [] else [(addrp, bs.length)]) eff
                (errno_ret ENOTSOCK) m []

/-- Rocq: `Checks.Sys.Net.Socket.check_connect_sound_ok`.  A `CheckOk` is an
outcome of the spec, under `record_copyins` from the read down — including
the `-ENOTSOCK` arm, which Linux reaches only after the copy. -/
theorem check_connect_sound_ok (i : SyscallInput) (fd addrp addrlen : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_connect i fd addrp addrlen eff m = CheckOk m' evs) :
    connect_spec fd addrp addrlen i m (Ok eff m' evs) := by
  unfold check_connect at h
  unfold connect_spec
  generalize sint32 addrlen = al at h ⊢
  apply bind_ok0 _ _ i m i m _ _ _ (input_ok i m)
  apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none =>
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | some e =>
    simp only [] at h ⊢
    by_cases h1 : al < 0 ∨ SOCKADDR_STORAGE_SIZE < al
    · simp only [h1, ↓reduceIte] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _
    · simp only [h1, ↓reduceIte] at h ⊢
      rcases hr : read_bytes_map i.in_mem addrp (Z_to_bv 64 al) with _ | bs
      · simp only [hr] at h ⊢
        obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
        exact pure_ok _ i _
      · simp only [hr] at h ⊢
        cases e
        case FdSocket sk =>
          simp only [] at h ⊢
          by_cases h2 : al < SA_FAMILY_SIZE
          · simp only [h2, ↓reduceIte] at h ⊢
            obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
            exact record_copyins_ok_empty _ _ i _ _ _ _ rfl (pure_ok _ i _)
          · simp only [h2, ↓reduceIte] at h ⊢
            by_cases h3 : sa_family_of bs = AF_UNSPEC
            · simp only [h3, ↓reduceIte] at h ⊢
              cases sk
              case SkFresh =>
                obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
                exact record_copyins_ok_empty _ _ i _ _ _ _ rfl (pure_ok _ i _)
              all_goals simp only [reduceCtorEq] at h
            · simp only [h3, ↓reduceIte] at h ⊢
              cases sk
              case SkListening =>
                obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
                exact record_copyins_ok_empty _ _ i _ _ _ _ rfl (pure_ok _ i _)
              case SkConnected peer ch rx =>
                obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
                exact record_copyins_ok_empty _ _ i _ _ _ _ rfl (pure_ok _ i _)
              case SkReset peer ch =>
                obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
                exact record_copyins_ok_empty _ _ i _ _ _ _ rfl (pure_ok _ i _)
              all_goals
                simp only [] at h ⊢
                by_cases h4 : al < SOCKADDR_IN_SIZE
                · simp only [h4, ↓reduceIte] at h ⊢
                  obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
                  exact record_copyins_ok_empty _ _ i _ _ _ _ rfl (pure_ok _ i _)
                · simp only [h4, ↓reduceIte] at h ⊢
                  by_cases h5 : sa_family_of bs = AF_INET
                  · simp only [h5, not_true_eq_false, ↓reduceIte, reduceCtorEq] at h
                  · simp only [h5, not_false_eq_true, ↓reduceIte] at h ⊢
                    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
                    exact record_copyins_ok_empty _ _ i _ _ _ _ rfl (pure_ok _ i _)
        all_goals
          obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
          exact record_copyins_ok_empty _ _ i _ _ _ _ rfl (pure_ok _ i _)

/-- Rocq: `Checks.Sys.Net.Socket.check_connect_sound_unmodeled`.  The
checker declines exactly where the spec does — an AF_UNSPEC disconnect of
anything but a fresh socket, and the attempt itself — and every other arm
is an acceptor that never answers `CheckUnmodeled`. -/
theorem check_connect_sound_unmodeled (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_connect i fd addrp addrlen eff m = CheckUnmodeled) :
    connect_spec fd addrp addrlen i m Unmodeled := by
  unfold check_connect at h
  unfold connect_spec
  generalize sint32 addrlen = al at h ⊢
  apply bind_unmodeled2 _ _ i m i m [] (input_ok i m)
  apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | some e =>
    simp only [] at h ⊢
    by_cases h1 : al < 0 ∨ SOCKADDR_STORAGE_SIZE < al
    · simp only [h1, ↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    · simp only [h1, ↓reduceIte] at h ⊢
      rcases hr : read_bytes_map i.in_mem addrp (Z_to_bv 64 al) with _ | bs
      · simp only [hr] at h
        exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
      · simp only [hr] at h ⊢
        cases e
        case FdSocket sk =>
          simp only [] at h ⊢
          by_cases h2 : al < SA_FAMILY_SIZE
          · simp only [h2, ↓reduceIte] at h
            exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)
          · simp only [h2, ↓reduceIte] at h ⊢
            by_cases h3 : sa_family_of bs = AF_UNSPEC
            · simp only [h3, ↓reduceIte] at h ⊢
              cases sk
              case SkFresh => exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)
              all_goals exact record_copyins_unmodeled _ _ i m (unmodeled_intro i m)
            · simp only [h3, ↓reduceIte] at h ⊢
              cases sk
              case SkListening => exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)
              case SkConnected peer ch rx =>
                exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)
              case SkReset peer ch =>
                exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)
              all_goals
                simp only [] at h ⊢
                by_cases h4 : al < SOCKADDR_IN_SIZE
                · simp only [h4, ↓reduceIte] at h
                  exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)
                · simp only [h4, ↓reduceIte] at h ⊢
                  by_cases h5 : sa_family_of bs = AF_INET
                  · simp only [h5, not_true_eq_false, ↓reduceIte]
                    exact record_copyins_unmodeled _ _ i m (unmodeled_intro i m)
                  · simp only [h5, not_false_eq_true, ↓reduceIte] at h
                    exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)
        all_goals exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)

set_option linter.constructorNameAsVariable false in
/-- Rocq: `Checks.Sys.Net.Socket.check_connect_complete_ok`.  Every outcome
the spec admits is one the checker accepts, with the spec's model and
events: below the read the spec's `record_copyins` is inverted once, before
the descriptor's kind is split, and each leaf's ledger is then
`check_ret_only_copyins_refl`. -/
theorem check_connect_complete_ok (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : connect_spec fd addrp addrlen i m (Ok eff m' evs)) :
    check_connect i fd addrp addrlen eff m = CheckOk m' evs := by
  unfold connect_spec at h
  unfold check_connect
  generalize sint32 addrlen = al at h ⊢
  have h := bind_input_model_inv _ i m _ h
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none =>
    simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | some e =>
    simp only [] at h ⊢
    by_cases h1 : al < 0 ∨ SOCKADDR_STORAGE_SIZE < al
    · simp only [h1, ↓reduceIte] at h ⊢
      simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    · simp only [h1, ↓reduceIte] at h ⊢
      rcases hr : read_bytes_map i.in_mem addrp (Z_to_bv 64 al) with _ | bs
      · simp only [hr] at h ⊢
        simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
      · simp only [hr] at h ⊢
        cases e
        case FdSocket sk =>
          obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
          simp only [] at hcore ⊢
          by_cases h2 : al < SA_FAMILY_SIZE
          · simp only [h2, ↓reduceIte] at hcore ⊢
            simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at hcore
            obtain ⟨rfl, rfl, rfl⟩ := hcore
            simp only [mkEffect, List.append_nil]
            exact check_ret_only_copyins_refl _ _ _ _
          · simp only [h2, ↓reduceIte] at hcore ⊢
            by_cases h3 : sa_family_of bs = AF_UNSPEC
            · simp only [h3, ↓reduceIte] at hcore ⊢
              cases sk
              case SkFresh =>
                simp only [ret_only, pure_iff, outcome.Ok.injEq] at hcore
                obtain ⟨rfl, rfl, rfl⟩ := hcore
                simp only [mkEffect, List.append_nil]
                exact check_ret_only_copyins_refl _ _ _ _
              all_goals simp only [unmodeled_iff, reduceCtorEq] at hcore
            · simp only [h3, ↓reduceIte] at hcore ⊢
              cases sk
              case SkListening =>
                simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at hcore
                obtain ⟨rfl, rfl, rfl⟩ := hcore
                simp only [mkEffect, List.append_nil]
                exact check_ret_only_copyins_refl _ _ _ _
              case SkConnected peer ch rx =>
                simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at hcore
                obtain ⟨rfl, rfl, rfl⟩ := hcore
                simp only [mkEffect, List.append_nil]
                exact check_ret_only_copyins_refl _ _ _ _
              case SkReset peer ch =>
                simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at hcore
                obtain ⟨rfl, rfl, rfl⟩ := hcore
                simp only [mkEffect, List.append_nil]
                exact check_ret_only_copyins_refl _ _ _ _
              all_goals
                simp only [] at hcore ⊢
                by_cases h4 : al < SOCKADDR_IN_SIZE
                · simp only [h4, ↓reduceIte] at hcore ⊢
                  simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at hcore
                  obtain ⟨rfl, rfl, rfl⟩ := hcore
                  simp only [mkEffect, List.append_nil]
                  exact check_ret_only_copyins_refl _ _ _ _
                · simp only [h4, ↓reduceIte] at hcore ⊢
                  by_cases h5 : sa_family_of bs = AF_INET
                  · simp only [h5, not_true_eq_false, ↓reduceIte, unmodeled_iff, reduceCtorEq]
                      at hcore
                  · simp only [h5, not_false_eq_true, ↓reduceIte] at hcore ⊢
                    simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at hcore
                    obtain ⟨rfl, rfl, rfl⟩ := hcore
                    simp only [mkEffect, List.append_nil]
                    exact check_ret_only_copyins_refl _ _ _ _
        all_goals
          obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
          simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at hcore
          obtain ⟨rfl, rfl, rfl⟩ := hcore
          simp only [mkEffect, List.append_nil]
          exact check_ret_only_copyins_refl _ _ _ _

set_option linter.constructorNameAsVariable false in
/-- Rocq: `Checks.Sys.Net.Socket.check_connect_complete_unmodeled`.  Every
decline of the spec is a `CheckUnmodeled` of the checker, whatever effect
the checker is shown. -/
theorem check_connect_complete_unmodeled (i : SyscallInput) (fd addrp addrlen : word)
    (m : Model) (eff : SyscallEffect) (h : connect_spec fd addrp addrlen i m Unmodeled) :
    check_connect i fd addrp addrlen eff m = CheckUnmodeled := by
  unfold connect_spec at h
  unfold check_connect
  generalize sint32 addrlen = al at h ⊢
  have h := bind_input_model_inv _ i m _ h
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
  | some e =>
    simp only [] at h ⊢
    by_cases h1 : al < 0 ∨ SOCKADDR_STORAGE_SIZE < al
    · simp only [h1, ↓reduceIte, err_ret, ret_only, pure_iff, reduceCtorEq] at h
    · simp only [h1, ↓reduceIte] at h ⊢
      rcases hr : read_bytes_map i.in_mem addrp (Z_to_bv 64 al) with _ | bs
      · simp only [hr, err_ret, ret_only, pure_iff, reduceCtorEq] at h
      · simp only [hr] at h ⊢
        cases e
        case FdSocket sk =>
          have h := record_copyins_unmodeled_inv _ _ i m h
          simp only [] at h ⊢
          by_cases h2 : al < SA_FAMILY_SIZE
          · simp only [h2, ↓reduceIte, err_ret, ret_only, pure_iff, reduceCtorEq] at h
          · simp only [h2, ↓reduceIte] at h ⊢
            by_cases h3 : sa_family_of bs = AF_UNSPEC
            · simp only [h3, ↓reduceIte] at h ⊢
              cases sk
              case SkFresh => simp only [ret_only, pure_iff, reduceCtorEq] at h
              all_goals rfl
            · simp only [h3, ↓reduceIte] at h ⊢
              cases sk
              case SkListening => simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
              case SkConnected peer ch rx =>
                simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
              case SkReset peer ch => simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
              all_goals
                simp only [] at h ⊢
                by_cases h4 : al < SOCKADDR_IN_SIZE
                · simp only [h4, ↓reduceIte, err_ret, ret_only, pure_iff, reduceCtorEq] at h
                · simp only [h4, ↓reduceIte] at h ⊢
                  by_cases h5 : sa_family_of bs = AF_INET
                  · simp only [h5, not_true_eq_false, ↓reduceIte]
                  · simp only [h5, not_false_eq_true, ↓reduceIte, err_ret, ret_only, pure_iff,
                      reduceCtorEq] at h
        all_goals
          have h := record_copyins_unmodeled_inv _ _ i m h
          simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h

/-! ## listen (201) -/

set_option linter.unusedVariables false in
/-- The checker for `listen_spec`, arm for arm.  `__sys_listen`
(net/socket.c:1933, Linux v6.18.46, commit 1f99e9ab748f) answers -EBADF on an
empty fd and -ENOTSOCK on another file's ops (:1938-1942) before
`__sys_listen_socket` (:1919) clamps the backlog to `somaxconn` (:1924-1925)
and calls `->listen` (:1929).  `inet_listen` (net/ipv4/af_inet.c:232, Linux
v6.18.46) answers -EINVAL unless the socket is SS_UNCONNECTED and a stream
(:239-240), does nothing but store the backlog if it already listens
(`__inet_listen_sk`, :201 and :205), and otherwise calls
`inet_csk_listen_start` (net/ipv4/inet_connection_sock.c:1345, Linux
v6.18.46), whose `get_port` (:1366) is the one call that can fail —
`inet_csk_get_port` (:500, at :506) picks a port for an unbound socket and may
find none free, which is the -EADDRINUSE of the fresh arm; a bound socket
already holds its port, so its arm cannot fail.  A connected or a reset socket
is still SS_CONNECTED at :239.  The backlog is bound and unused, as
`listen_spec`'s own is: the clamp is behaviour the model has no queue to show.
Rocq: `Checks.Sys.Net.Socket.check_listen`. -/
def check_listen (fd backlog : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdSocket sk) =>
      (match sk with
       | .SkConnected _ _ _ => check_ret_only eff (errno_ret EINVAL) m []
       | .SkReset _ _ => check_ret_only eff (errno_ret EINVAL) m []
       | .SkListening => check_ret_only eff (Z_to_bv 64 0) m []
       | .SkBound =>
           check_ret_only eff (Z_to_bv 64 0)
             (with_fds (fd_insert (m_fds m) fd (.FdSocket .SkListening)) m) []
       | .SkFresh =>
           check_errno_or_success listen_errnos
             (fd_insert (m_fds m) fd (.FdSocket .SkListening)) (Z_to_bv 64 0) eff m)
  | some _ => check_ret_only eff (errno_ret ENOTSOCK) m []

/-- Rocq: `Checks.Sys.Net.Socket.check_listen_sound_ok`.  A `CheckOk` is an
outcome of the spec: the same descriptor and state tests, and each
accepting leaf is the spec's `pure`, with the bound arm's `set_fds` as the
model `check_ret_only` was handed. -/
theorem check_listen_sound_ok (fd backlog : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_listen fd backlog eff m = CheckOk m' evs) :
    listen_spec fd backlog i m (Ok eff m' evs) := by
  unfold check_listen at h
  unfold listen_spec
  apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none =>
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | some e =>
    cases e
    case FdSocket sk =>
      simp only [] at h ⊢
      cases sk
      case SkFresh => exact check_errno_or_success_sound_ok _ _ _ i _ _ _ _ h
      case SkBound =>
        obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
        exact bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m) (pure_ok _ i _)
      all_goals
        obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
        exact pure_ok _ i _
    all_goals
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _

/-- Rocq: `Checks.Sys.Net.Socket.check_listen_sound_unmodeled`.  The
checker never declines — every arm is an acceptor — so the hypothesis is
absurd and the spec's `Unmodeled`, which it never produces either, follows. -/
theorem check_listen_sound_unmodeled (fd backlog : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_listen fd backlog eff m = CheckUnmodeled) :
    listen_spec fd backlog i m Unmodeled := by
  exfalso
  unfold check_listen at h
  generalize fd_lookup (m_fds m) fd = r at h
  cases r with
  | none => exact check_ret_only_no_unmodeled _ _ _ _ h
  | some e =>
    cases e
    case FdSocket sk =>
      simp only [] at h
      cases sk
      case SkFresh => exact check_errno_or_success_no_unmodeled _ _ _ _ _ h
      all_goals exact check_ret_only_no_unmodeled _ _ _ _ h
    all_goals exact check_ret_only_no_unmodeled _ _ _ _ h

/-- Rocq: `Checks.Sys.Net.Socket.check_listen_complete_ok`.  Every outcome
the spec admits is one the checker accepts, with the spec's model and
events; the fresh arm discharges `check_errno_or_success`'s side condition —
0 is not in `listen_errnos` — by evaluation. -/
theorem check_listen_complete_ok (fd backlog : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : listen_spec fd backlog i m (Ok eff m' evs)) :
    check_listen fd backlog eff m = CheckOk m' evs := by
  have hne : errno_ret_in listen_errnos (Z_to_bv 64 0) = false := by decide
  unfold listen_spec at h
  unfold check_listen
  have h := bind_model_inv _ i m _ h
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none =>
    simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | some e =>
    cases e
    case FdSocket sk =>
      simp only [] at h ⊢
      cases sk
      case SkFresh => exact check_errno_or_success_complete_ok _ _ _ i _ _ _ _ hne h
      case SkBound =>
        simp only [bind_set_fds_iff, ret_only, pure_iff, outcome.Ok.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
      all_goals
        simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    all_goals
      simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- Rocq: `Checks.Sys.Net.Socket.check_listen_complete_unmodeled`.  The spec
has no `unmodeled` arm, so the hypothesis is absurd whatever `eff` is. -/
theorem check_listen_complete_unmodeled (fd backlog : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (h : listen_spec fd backlog i m Unmodeled) :
    check_listen fd backlog eff m = CheckUnmodeled := by
  exfalso
  unfold listen_spec at h
  have h := bind_model_inv _ i m _ h
  generalize fd_lookup (m_fds m) fd = r at h
  cases r with
  | none => simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
  | some e =>
    cases e
    case FdSocket sk =>
      simp only [] at h
      cases sk
      case SkFresh => exact errno_or_success_no_unmodeled _ _ _ i m h
      case SkBound => simp only [bind_set_fds_iff, ret_only, pure_iff, reduceCtorEq] at h
      all_goals simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
    all_goals simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h

/-! ## getsockname (204), getpeername (205), shutdown (210)

Three arms over `sock_fd`, the spec's own descriptor test, which folds the
-EBADF and the seven -ENOTSOCK kinds into one `Sum`.  The checkers match on
it too, so one `generalize sock_fd m fd = r` and a `cases r` drive each
proof; the kinds are never enumerated here. -/

/-- The checker for `getsockname_spec`.  `__sys_getsockname`
(net/socket.c:2136, Linux v6.18.46, commit 1f99e9ab748f) answers -EBADF on an
empty fd and -ENOTSOCK on another file's ops (:2144-2148) and otherwise
calls `->getname` (:2154) and writes the address back (:2159).
`inet_getname` (net/ipv4/af_inet.c:797) answers the bound port and address
(:819-823) and returns the length (:829): a real address write, of a port
the model does not choose, so every socket declines.  Rocq:
`Checks.Sys.Net.Socket.check_getsockname`. -/
def check_getsockname (fd : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match sock_fd m fd with
  | .inr e => check_ret_only eff (errno_ret e) m []
  | .inl _ => CheckUnmodeled

/-- Rocq: `Checks.Sys.Net.Socket.check_getsockname_sound_ok`. -/
theorem check_getsockname_sound_ok (fd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_getsockname fd eff m = CheckOk m' evs) :
    getsockname_spec fd i m (Ok eff m' evs) := by
  unfold check_getsockname at h
  unfold getsockname_spec
  apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
  generalize sock_fd m fd = r at h ⊢
  cases r with
  | inl sk => simp only [reduceCtorEq] at h
  | inr e =>
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _

/-- Rocq: `Checks.Sys.Net.Socket.check_getsockname_sound_unmodeled`. -/
theorem check_getsockname_sound_unmodeled (fd : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_getsockname fd eff m = CheckUnmodeled) :
    getsockname_spec fd i m Unmodeled := by
  unfold check_getsockname at h
  unfold getsockname_spec
  apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
  generalize sock_fd m fd = r at h ⊢
  cases r with
  | inl sk => exact unmodeled_intro i m
  | inr e => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

/-- Rocq: `Checks.Sys.Net.Socket.check_getsockname_complete_ok`. -/
theorem check_getsockname_complete_ok (fd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : getsockname_spec fd i m (Ok eff m' evs)) :
    check_getsockname fd eff m = CheckOk m' evs := by
  unfold getsockname_spec at h
  unfold check_getsockname
  have h := bind_model_inv _ i m _ h
  generalize sock_fd m fd = r at h ⊢
  cases r with
  | inl sk => simp only [unmodeled_iff, reduceCtorEq] at h
  | inr e =>
    simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- Rocq: `Checks.Sys.Net.Socket.check_getsockname_complete_unmodeled`. -/
theorem check_getsockname_complete_unmodeled (fd : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (h : getsockname_spec fd i m Unmodeled) :
    check_getsockname fd eff m = CheckUnmodeled := by
  unfold getsockname_spec at h
  unfold check_getsockname
  have h := bind_model_inv _ i m _ h
  generalize sock_fd m fd = r at h ⊢
  cases r with
  | inl sk => rfl
  | inr e => simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h

/-- The checker for `getpeername_spec`.  `__sys_getpeername`
(net/socket.c:2173, Linux v6.18.46, commit 1f99e9ab748f) takes the same
-EBADF / -ENOTSOCK path (:2181-2185) and calls `->getname` with `peer` set
(:2191), writing back on success (:2196).  `inet_getname`
(net/ipv4/af_inet.c:797) answers -ENOTCONN when the peer is asked for and
`inet_dport` is zero or the socket is TCP_CLOSE or SYN_SENT (the test at
:808-810, returning at :812): a fresh,
bound or listening socket has no port, and a reset one keeps its `dport`
but is TCP_CLOSE, which the spec's `SkReset` arm records as -ENOTCONN on
the strength of the same lines.  A connected socket answers the peer, an
address write the model does not export, so it declines.  Rocq:
`Checks.Sys.Net.Socket.check_getpeername`. -/
def check_getpeername (fd : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match sock_fd m fd with
  | .inr e => check_ret_only eff (errno_ret e) m []
  | .inl sk =>
      (match sk with
       | .SkFresh => check_ret_only eff (errno_ret ENOTCONN) m []
       | .SkBound => check_ret_only eff (errno_ret ENOTCONN) m []
       | .SkListening => check_ret_only eff (errno_ret ENOTCONN) m []
       | .SkReset _ _ => check_ret_only eff (errno_ret ENOTCONN) m []
       | .SkConnected _ _ _ => CheckUnmodeled)

/-- Rocq: `Checks.Sys.Net.Socket.check_getpeername_sound_ok`. -/
theorem check_getpeername_sound_ok (fd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_getpeername fd eff m = CheckOk m' evs) :
    getpeername_spec fd i m (Ok eff m' evs) := by
  unfold check_getpeername at h
  unfold getpeername_spec
  apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
  generalize sock_fd m fd = r at h ⊢
  cases r with
  | inl sk =>
    cases sk
    case SkConnected peer ch rx => simp only [reduceCtorEq] at h
    all_goals
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _
  | inr e =>
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _

/-- Rocq: `Checks.Sys.Net.Socket.check_getpeername_sound_unmodeled`. -/
theorem check_getpeername_sound_unmodeled (fd : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_getpeername fd eff m = CheckUnmodeled) :
    getpeername_spec fd i m Unmodeled := by
  unfold check_getpeername at h
  unfold getpeername_spec
  apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
  generalize sock_fd m fd = r at h ⊢
  cases r with
  | inl sk =>
    cases sk
    case SkConnected peer ch rx => exact unmodeled_intro i m
    all_goals exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | inr e => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

/-- Rocq: `Checks.Sys.Net.Socket.check_getpeername_complete_ok`. -/
theorem check_getpeername_complete_ok (fd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : getpeername_spec fd i m (Ok eff m' evs)) :
    check_getpeername fd eff m = CheckOk m' evs := by
  unfold getpeername_spec at h
  unfold check_getpeername
  have h := bind_model_inv _ i m _ h
  generalize sock_fd m fd = r at h ⊢
  cases r with
  | inl sk =>
    cases sk
    case SkConnected peer ch rx => simp only [unmodeled_iff, reduceCtorEq] at h
    all_goals
      simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | inr e =>
    simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- Rocq: `Checks.Sys.Net.Socket.check_getpeername_complete_unmodeled`. -/
theorem check_getpeername_complete_unmodeled (fd : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (h : getpeername_spec fd i m Unmodeled) :
    check_getpeername fd eff m = CheckUnmodeled := by
  unfold getpeername_spec at h
  unfold check_getpeername
  have h := bind_model_inv _ i m _ h
  generalize sock_fd m fd = r at h ⊢
  cases r with
  | inl sk =>
    cases sk
    case SkConnected peer ch rx => rfl
    all_goals simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
  | inr e => simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h

/-! ## setsockopt (208), getsockopt (209)

The two option calls, the OPTIONS group of the two Rocq files.  Both walk
the same first two gates as the lifecycle calls above — `__sys_setsockopt`
(net/socket.c:2372-2387, Linux v6.18.46, commit 1f99e9ab748f) and
`__sys_getsockopt` (:2439-2453) open with `CLASS(fd, f)(fd)`, answer -EBADF
on `fd_empty` (:2380-2381, :2445-2446) and -ENOTSOCK when `sock_from_file`
finds no socket (:2382-2384, :2447-2449) — and then part: the set side
tests `optlen < 0` as the first statement of `do_sock_setsockopt`
(:2335-2336), the get side copies four bytes from `optlen` in
`do_sock_getsockopt` (:2409-2410) and tests nothing.  Past that, both reach
the level.  `inet_stream_ops` (net/ipv4/af_inet.c:1063-1064, v6.18.46)
sends a level other than SOL_SOCKET through `sock_common_setsockopt`
(net/core/sock.c:3910, v6.18.46) to `tcp_setsockopt` (net/ipv4/tcp.c:4157,
v6.18.46), and through `sock_common_getsockopt` (net/core/sock.c:3888,
v6.18.46) to `tcp_getsockopt` (net/ipv4/tcp.c:4836, v6.18.46), and each
hands a level other than SOL_TCP to `ipv4_specific`
(net/ipv4/tcp_ipv4.c:2501-2502, v6.18.46): `ip_setsockopt` answers
-ENOPROTOOPT on a level other than SOL_IP (net/ipv4/ip_sockglue.c:1414-1415,
v6.18.46), `do_ip_getsockopt` answers -EOPNOTSUPP (:1515-1516, v6.18.46).
So an unknown level — one that is none of SOL_SOCKET, SOL_IP
and SOL_TCP, `sock_level_known` — has an errno on each side and no option
table behind it, and a known level is the option table, which the spec
declines; the spec twin's docstrings say why the declined intersection is
empty.  The errno pair is `inet_stream_ops`'s, and stops being true the
day an `FdSocket` can be anything but the AF_INET/SOCK_STREAM socket
`socket_spec` mints (Rocq's, and since #1201 this tree's): on an AF_UNIX
stream the set side's unknown level is -EOPNOTSUPP from `unix_setsockopt`
(net/unix/af_unix.c:943-951, v6.18.46), and the get side's -EOPNOTSUPP is
`do_sock_getsockopt`'s own for an ops table with no `getsockopt`
(net/socket.c:2415-2416), which `unix_stream_ops` lacks.  Rocq's checkers
and witnesses are ported here name for name; the Cases pins are
`Checks/Cases/Checks/Sys/Net/Socket.lean`'s options section. -/

/-- The checker for `setsockopt_spec`: -EBADF or -ENOTSOCK from
`__sys_setsockopt` (net/socket.c:2380-2384, Linux v6.18.46, commit
1f99e9ab748f), then -EINVAL on a negative `optlen` as the first statement
of `do_sock_setsockopt` (:2335-2336) — the `int` sign, which is why the
arm narrows a4 through `int32` — then -ENOPROTOOPT from `ip_setsockopt`
(net/ipv4/ip_sockglue.c:1414-1415, v6.18.46) on a level none of the three
tables claim, and `CheckUnmodeled` on one they do.  No arm reads user
memory: `optval` is copied only inside the option tables (`sk_setsockopt`,
net/core/sock.c:1186, v6.18.46, behind `sock_setsockopt`'s wrapper, and
its peers), all of which the spec declines, so
`check_ret_only` with an empty ledger is the acceptor on every answer.
Rocq: `Checks.Sys.Net.Socket.check_setsockopt`. -/
def check_setsockopt (fd level optlen : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match sock_fd m fd with
  | .inr e => check_ret_only eff (errno_ret e) m []
  | .inl _ =>
      if int32_neg optlen then check_ret_only eff (errno_ret EINVAL) m []
      else if ¬ (sock_level_known level) then check_ret_only eff (errno_ret ENOPROTOOPT) m []
      else CheckUnmodeled

/-- Rocq: `Checks.Sys.Net.Socket.check_setsockopt_sound_ok`. -/
theorem check_setsockopt_sound_ok (fd level optlen : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_setsockopt fd level optlen eff m = CheckOk m' evs) :
    setsockopt_spec fd level optlen i m (Ok eff m' evs) := by
  unfold check_setsockopt at h
  unfold setsockopt_spec
  apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
  generalize sock_fd m fd = r at h ⊢
  cases r with
  | inr e =>
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | inl _ =>
    simp only [] at h ⊢
    cases hn : int32_neg optlen
    · simp only [hn, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hl : sock_level_known level
      · simp only [hl, Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at h ⊢
        obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
        exact pure_ok _ i _
      · simp only [hl, not_true_eq_false, ↓reduceIte, reduceCtorEq] at h
    · simp only [hn, ↓reduceIte] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _

/-- Rocq: `Checks.Sys.Net.Socket.check_setsockopt_sound_unmodeled`.  The one
`CheckUnmodeled` is the known level on a socket, and the spec declines
exactly there. -/
theorem check_setsockopt_sound_unmodeled (fd level optlen : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput) (h : check_setsockopt fd level optlen eff m = CheckUnmodeled) :
    setsockopt_spec fd level optlen i m Unmodeled := by
  unfold check_setsockopt at h
  unfold setsockopt_spec
  apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
  generalize sock_fd m fd = r at h ⊢
  cases r with
  | inr e => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | inl _ =>
    simp only [] at h ⊢
    cases hn : int32_neg optlen
    · simp only [hn, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hl : sock_level_known level
      · simp only [hl, Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at h
        exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
      · simp only [not_true_eq_false, ↓reduceIte]
        exact unmodeled_intro i m
    · simp only [hn, ↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

/-- Rocq: `Checks.Sys.Net.Socket.check_setsockopt_complete_ok`. -/
theorem check_setsockopt_complete_ok (fd level optlen : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : setsockopt_spec fd level optlen i m (Ok eff m' evs)) :
    check_setsockopt fd level optlen eff m = CheckOk m' evs := by
  unfold setsockopt_spec at h
  unfold check_setsockopt
  have h := bind_model_inv _ i m _ h
  generalize sock_fd m fd = r at h ⊢
  cases r with
  | inr e =>
    simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | inl _ =>
    simp only [] at h ⊢
    cases hn : int32_neg optlen
    · simp only [hn, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hl : sock_level_known level
      · simp only [hl, Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at h ⊢
        simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
      · simp only [hl, not_true_eq_false, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h
    · simp only [hn, ↓reduceIte] at h ⊢
      simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- Rocq: `Checks.Sys.Net.Socket.check_setsockopt_complete_unmodeled`.  The
checker's one decline is the spec's, and it does not look at `eff`. -/
theorem check_setsockopt_complete_unmodeled (fd level optlen : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect) (h : setsockopt_spec fd level optlen i m Unmodeled) :
    check_setsockopt fd level optlen eff m = CheckUnmodeled := by
  unfold setsockopt_spec at h
  unfold check_setsockopt
  have h := bind_model_inv _ i m _ h
  generalize sock_fd m fd = r at h ⊢
  cases r with
  | inr e => simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
  | inl _ =>
    simp only [] at h ⊢
    cases hn : int32_neg optlen
    · simp only [hn, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hl : sock_level_known level
      · simp only [hl, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, err_ret, ret_only,
          pure_iff, reduceCtorEq] at h
      · simp only [not_true_eq_false, ↓reduceIte]
    · simp only [hn, ↓reduceIte, err_ret, ret_only, pure_iff, reduceCtorEq] at h

/-- The checker for `getsockopt_spec`: -EBADF or -ENOTSOCK from
`__sys_getsockopt` (net/socket.c:2445-2449, Linux v6.18.46, commit
1f99e9ab748f) with nothing read, then, on a socket, the four bytes
`do_sock_getsockopt` copies from `optlen` (:2409-2410) — recorded when the
range is wholly readable and not otherwise, which is
`getsockopt_optlen_read` — around the level: -EOPNOTSUPP from
`do_ip_getsockopt` (net/ipv4/ip_sockglue.c:1515-1516, v6.18.46) on a level
none of the three tables claim, and `CheckUnmodeled` on one they do.  The
acceptor on the errno is `check_ret_only_copyins`, which demands exactly
that ledger and no other copy-in, because the copy's result is discarded
(net/socket.c:2410, v6.18.46, tests nothing; `max_optlen` feeds only the
cgroup getsockopt hook, to which the modeled environment attaches no
program) and the errno is the same whatever `optlen` holds: the ledger is
the whole content of the read.  The checker takes the input, as Rocq's
does, because the read is of `i.in_mem`; the spec's `if` sits INSIDE its
`record_copyins` and the checker's sits outside, which the completeness
proofs bridge with `record_copyins_ok_inv`.  Rocq:
`Checks.Sys.Net.Socket.check_getsockopt`. -/
def check_getsockopt (i : SyscallInput) (fd level optlenp : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match sock_fd m fd with
  | .inr e => check_ret_only eff (errno_ret e) m []
  | .inl _ =>
      if ¬ (sock_level_known level)
      then check_ret_only_copyins (getsockopt_optlen_read i optlenp) eff (errno_ret EOPNOTSUPP) m []
      else CheckUnmodeled

/-- Rocq: `Checks.Sys.Net.Socket.check_getsockopt_sound_ok`. -/
theorem check_getsockopt_sound_ok (i : SyscallInput) (fd level optlenp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_getsockopt i fd level optlenp eff m = CheckOk m' evs) :
    getsockopt_spec fd level optlenp i m (Ok eff m' evs) := by
  unfold check_getsockopt at h
  unfold getsockopt_spec
  apply bind_ok0 _ _ i m i m _ _ _ (input_ok i m)
  apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
  generalize sock_fd m fd = r at h ⊢
  cases r with
  | inr e =>
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | inl _ =>
    simp only [] at h ⊢
    cases hl : sock_level_known level
    · simp only [hl, Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
      exact record_copyins_ok_empty _ _ i _ _ _ _ rfl (pure_ok _ i _)
    · simp only [hl, not_true_eq_false, ↓reduceIte, reduceCtorEq] at h

/-- Rocq: `Checks.Sys.Net.Socket.check_getsockopt_sound_unmodeled`.  The one
`CheckUnmodeled` is the known level on a socket, where the spec's
`record_copyins` wraps an `unmodeled`. -/
theorem check_getsockopt_sound_unmodeled (i : SyscallInput) (fd level optlenp : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_getsockopt i fd level optlenp eff m = CheckUnmodeled) :
    getsockopt_spec fd level optlenp i m Unmodeled := by
  unfold check_getsockopt at h
  unfold getsockopt_spec
  apply bind_unmodeled2 _ _ i m i m [] (input_ok i m)
  apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
  generalize sock_fd m fd = r at h ⊢
  cases r with
  | inr e => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | inl _ =>
    simp only [] at h ⊢
    cases hl : sock_level_known level
    · simp only [hl, Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at h
      exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)
    · simp only [not_true_eq_false, ↓reduceIte]
      exact record_copyins_unmodeled _ _ i m (unmodeled_intro i m)

/-- Rocq: `Checks.Sys.Net.Socket.check_getsockopt_complete_ok`.  The spec's
`record_copyins` around `err_ret` yields exactly `with_copyins reads
(mkEffect r [] [])`, which is what `check_ret_only_copyins_refl` accepts
once the empty tail of the ledger is dropped. -/
theorem check_getsockopt_complete_ok (i : SyscallInput) (fd level optlenp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : getsockopt_spec fd level optlenp i m (Ok eff m' evs)) :
    check_getsockopt i fd level optlenp eff m = CheckOk m' evs := by
  unfold getsockopt_spec at h
  unfold check_getsockopt
  have h := bind_input_model_inv _ i m _ h
  generalize sock_fd m fd = r at h ⊢
  cases r with
  | inr e =>
    simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | inl _ =>
    simp only [] at h ⊢
    cases hl : sock_level_known level
    · simp only [hl, Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
      simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at hcore
      obtain ⟨rfl, rfl, rfl⟩ := hcore
      simp only [mkEffect, List.append_nil]
      exact check_ret_only_copyins_refl _ _ _ _
    · simp only [hl, not_true_eq_false, ↓reduceIte] at h
      obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
      simp only [unmodeled_iff, reduceCtorEq] at hcore

/-- Rocq: `Checks.Sys.Net.Socket.check_getsockopt_complete_unmodeled`. -/
theorem check_getsockopt_complete_unmodeled (i : SyscallInput) (fd level optlenp : word)
    (m : Model) (eff : SyscallEffect) (h : getsockopt_spec fd level optlenp i m Unmodeled) :
    check_getsockopt i fd level optlenp eff m = CheckUnmodeled := by
  unfold getsockopt_spec at h
  unfold check_getsockopt
  have h := bind_input_model_inv _ i m _ h
  generalize sock_fd m fd = r at h ⊢
  cases r with
  | inr e => simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
  | inl _ =>
    simp only [] at h ⊢
    have h := record_copyins_unmodeled_inv _ _ i m h
    cases hl : sock_level_known level
    · simp only [hl, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, err_ret, ret_only,
        pure_iff, reduceCtorEq] at h
    · simp only [not_true_eq_false, ↓reduceIte]

/-- The checker for `shutdown_spec`.  `__sys_shutdown` (net/socket.c:2476,
Linux v6.18.46, commit 1f99e9ab748f) takes the -EBADF / -ENOTSOCK path
(:2481-2485) and `__sys_shutdown_sock` (:2465) calls `->shutdown` (:2471).
`inet_shutdown` (net/ipv4/af_inet.c:888) answers -EINVAL on a `how`
outside `SHUT_RD..SHUT_RDWR` before `lock_sock` (:896, :899-900); a
listening socket on SHUT_WR hits `case TCP_LISTEN` and breaks having
written nothing (:927-929), which is the one success this file
models, while SHUT_RD or SHUT_RDWR on it falls into `tcp_disconnect`
(:930-933), a TCP_CLOSE socket answers -ENOTCONN having set the shutdown
bits (:912-913, :916-918), and a connected socket sets its bits and may
send a FIN — state the model does not carry, so those arms decline, in the
order the
spec declines them.  Rocq: `Checks.Sys.Net.Socket.check_shutdown`. -/
def check_shutdown (fd how : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match sock_fd m fd with
  | .inr e => check_ret_only eff (errno_ret e) m []
  | .inl sk =>
      if ¬ (shut_how_ok how) then check_ret_only eff (errno_ret EINVAL) m []
      else
        (match sk with
         | .SkFresh => CheckUnmodeled
         | .SkBound => CheckUnmodeled
         | .SkListening =>
             if bv_unsigned how = SHUT_WR then check_ret_only eff (Z_to_bv 64 0) m []
             else CheckUnmodeled
         | .SkConnected _ _ _ => CheckUnmodeled
         | .SkReset _ _ => CheckUnmodeled)

/-- Rocq: `Checks.Sys.Net.Socket.check_shutdown_sound_ok`. -/
theorem check_shutdown_sound_ok (fd how : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_shutdown fd how eff m = CheckOk m' evs) :
    shutdown_spec fd how i m (Ok eff m' evs) := by
  unfold check_shutdown at h
  unfold shutdown_spec
  apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
  generalize sock_fd m fd = r at h ⊢
  cases r with
  | inr e =>
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | inl sk =>
    simp only [] at h ⊢
    cases hh : shut_how_ok how
    · simp only [hh, Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _
    · simp only [hh, not_true_eq_false, ↓reduceIte] at h ⊢
      cases sk
      case SkListening =>
        by_cases hw : bv_unsigned how = SHUT_WR
        · simp only [hw, ↓reduceIte] at h ⊢
          obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
          exact pure_ok _ i _
        · simp only [hw, ↓reduceIte, reduceCtorEq] at h
      all_goals simp only [reduceCtorEq] at h

/-- Rocq: `Checks.Sys.Net.Socket.check_shutdown_sound_unmodeled`. -/
theorem check_shutdown_sound_unmodeled (fd how : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_shutdown fd how eff m = CheckUnmodeled) :
    shutdown_spec fd how i m Unmodeled := by
  unfold check_shutdown at h
  unfold shutdown_spec
  apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
  generalize sock_fd m fd = r at h ⊢
  cases r with
  | inr e => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | inl sk =>
    simp only [] at h ⊢
    cases hh : shut_how_ok how
    · simp only [hh, Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    · simp only [hh, not_true_eq_false, ↓reduceIte] at h ⊢
      cases sk
      case SkListening =>
        by_cases hw : bv_unsigned how = SHUT_WR
        · simp only [hw, ↓reduceIte] at h
          exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
        · simp only [hw, ↓reduceIte]
          exact unmodeled_intro i m
      all_goals exact unmodeled_intro i m

/-- Rocq: `Checks.Sys.Net.Socket.check_shutdown_complete_ok`. -/
theorem check_shutdown_complete_ok (fd how : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : shutdown_spec fd how i m (Ok eff m' evs)) :
    check_shutdown fd how eff m = CheckOk m' evs := by
  unfold shutdown_spec at h
  unfold check_shutdown
  have h := bind_model_inv _ i m _ h
  generalize sock_fd m fd = r at h ⊢
  cases r with
  | inr e =>
    simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | inl sk =>
    simp only [] at h ⊢
    cases hh : shut_how_ok how
    · simp only [hh, Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at h ⊢
      simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    · simp only [hh, not_true_eq_false, ↓reduceIte] at h ⊢
      cases sk
      case SkListening =>
        by_cases hw : bv_unsigned how = SHUT_WR
        · simp only [hw, ↓reduceIte] at h ⊢
          simp only [ret_only, pure_iff, outcome.Ok.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
        · simp only [hw, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h
      all_goals simp only [unmodeled_iff, reduceCtorEq] at h

/-- Rocq: `Checks.Sys.Net.Socket.check_shutdown_complete_unmodeled`. -/
theorem check_shutdown_complete_unmodeled (fd how : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (h : shutdown_spec fd how i m Unmodeled) :
    check_shutdown fd how eff m = CheckUnmodeled := by
  unfold shutdown_spec at h
  unfold check_shutdown
  have h := bind_model_inv _ i m _ h
  generalize sock_fd m fd = r at h ⊢
  cases r with
  | inr e => simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
  | inl sk =>
    simp only [] at h ⊢
    cases hh : shut_how_ok how
    · simp only [hh, Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at h
      simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
    · simp only [hh, not_true_eq_false, ↓reduceIte] at h ⊢
      cases sk
      case SkListening =>
        by_cases hw : bv_unsigned how = SHUT_WR
        · simp only [hw, ↓reduceIte, ret_only, pure_iff, reduceCtorEq] at h
        · simp only [hw, ↓reduceIte]
      all_goals rfl

/-! ## socketpair (199)

`__sys_socketpair` (net/socket.c:1769, Linux v6.18.46, commit 1f99e9ab748f)
refuses a flag outside `SOCK_CLOEXEC | SOCK_NONBLOCK` with -EINVAL
(:1776-1778), reserves two descriptors with `get_unused_fd_flags` (:1788,
:1792; fs/file.c:620, whose `alloc_fd` at :570 answers -EMFILE past the
rlimit at :591-592 and grows the table through `expand_files` at :596,
which is where -ENOMEM comes from), WRITES both to `usockvec` (:1798,
:1802) and only then creates the sockets (:1811, :1815; `__sock_create`
at :1535 answers -ENFILE when `sock_alloc` fails, :1573) and calls
`->socketpair` (:1828), which for both `inet_stream_ops`
(net/ipv4/af_inet.c:1049, :1055, Linux v6.18.46) and `inet_dgram_ops` (:1084,
:1090) is `sock_no_socketpair` (net/core/sock.c:3444-3447, Linux v6.18.46):
-EOPNOTSUPP.  The `out:` path (:1855-1857) returns the error with both
descriptors released — and the two writes already done.  So on a writable
destination the effect is either a reserve-time errno with nothing written or
a create-time errno, or -EOPNOTSUPP, WITH the two descriptors written; on a
destination `access_ok` refuses it is a reserve-time errno or -EFAULT.  The
two acceptors below are those two shapes, and `check_socketpair` chooses
between them as `socketpair_spec` does. -/

/-- `writes_eqb` is reflexive, as `writes_eqb_eq` says; stated once for the
two completeness proofs that need it. -/
theorem writes_eqb_refl (l : List (word × List byte)) : writes_eqb l l = true :=
  (writes_eqb_eq l l).mpr rfl

/-- The acceptor for `socketpair_written`: a reserve-time errno carrying no
write, or the descriptor pair written at `sv` beside -EOPNOTSUPP or a
create-time errno.  Any other write list, any zero, unmap or copy, is a
lie.  Rocq: `Checks.Sys.Net.Socket.check_socketpair_written`. -/
def check_socketpair_written (sv fd1 fd2 : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match eff with
  | SyscallEffect.mkEffectU r [] [] [] [] [] =>
      if errno_ret_in socketpair_reserve_errnos r then CheckOk m [] else CheckReject
  | SyscallEffect.mkEffectU r ws [] [] [] [] =>
      if writes_eqb ws (socketpair_writes sv fd1 fd2)
         && (bv_eqb r (errno_ret EOPNOTSUPP) || errno_ret_in socketpair_create_errnos r)
      then CheckOk m [] else CheckReject
  | _ => CheckReject

/-- Rocq: `Checks.Sys.Net.Socket.socketpair_written_no_unmodeled`.  Three
`pure`s under two `choose`s: nothing declines. -/
theorem socketpair_written_no_unmodeled (sv fd1 fd2 : word) (i : SyscallInput) (m : Model) :
    ¬ socketpair_written sv fd1 fd2 i m Unmodeled := by
  intro h
  simp only [socketpair_written, Monad.alt, Monad.bind, errno_from, Monad.choose, err_ret,
    ret_only, Monad.pure, reduceCtorEq, and_false, exists_false, or_self] at h

/-- Rocq: `Checks.Sys.Net.Socket.check_socketpair_written_sound_ok`. -/
theorem check_socketpair_written_sound_ok (sv fd1 fd2 : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (h : check_socketpair_written sv fd1 fd2 eff m = CheckOk m' evs) :
    socketpair_written sv fd1 fd2 i m (Ok eff m' evs) := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases zs with
  | cons z zs => cases ws <;> simp only [check_socketpair_written, reduceCtorEq] at h
  | nil =>
  cases us with
  | cons u us => cases ws <;> simp only [check_socketpair_written, reduceCtorEq] at h
  | nil =>
  cases cs with
  | cons c cs => cases ws <;> simp only [check_socketpair_written, reduceCtorEq] at h
  | nil =>
  cases copyins with
  | cons ci copyins => cases ws <;> simp only [check_socketpair_written, reduceCtorEq] at h
  | nil =>
  cases ws with
  | nil =>
    simp only [check_socketpair_written] at h
    cases hin : errno_ret_in socketpair_reserve_errnos ret with
    | false => simp only [hin, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
    | true =>
      simp only [hin, ↓reduceIte, check_result.CheckOk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨e, he, rfl⟩ := (errno_ret_in_true _ ret).mp hin
      exact alt_l _ _ i m _
        (bind_ok0 _ _ i m e m _ _ _ (errno_from_witness _ e i m he) (pure_ok _ i _))
  | cons w ws =>
    simp only [check_socketpair_written] at h
    split at h
    · rename_i hc
      simp only [check_result.CheckOk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hc
      obtain ⟨hws, hr⟩ := hc
      rw [(writes_eqb_eq _ _).mp hws]
      rcases hr with hr | hr
      · obtain rfl := (bv_eqb_eq _ _).mp hr
        exact alt_r _ _ i m _ (alt_r _ _ i m _ (pure_ok _ i _))
      · obtain ⟨e, he, rfl⟩ := (errno_ret_in_true _ ret).mp hr
        exact alt_r _ _ i m _ (alt_l _ _ i m _
          (bind_ok0 _ _ i m e m _ _ _ (errno_from_witness _ e i m he) (pure_ok _ i _)))
    · simp only [reduceCtorEq] at h

/-- Rocq: `Checks.Sys.Net.Socket.check_socketpair_written_complete_ok`. -/
theorem check_socketpair_written_complete_ok (sv fd1 fd2 : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (h : socketpair_written sv fd1 fd2 i m (Ok eff m' evs)) :
    check_socketpair_written sv fd1 fd2 eff m = CheckOk m' evs := by
  simp only [socketpair_written, Monad.alt, Monad.bind, errno_from, Monad.choose, err_ret,
    ret_only, Monad.pure, outcome.Ok.injEq] at h
  rcases h with ⟨e, m1, evs1, evs2, ⟨x, hx, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl⟩
    | ⟨e, m1, evs1, evs2, ⟨x, hx, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl⟩
    | ⟨rfl, rfl, rfl⟩
  · simp only [check_socketpair_written, errno_ret_in_intro _ _ hx, ↓reduceIte, List.append_nil]
  · simp only [check_socketpair_written, socketpair_writes, writes_eqb_refl,
      errno_ret_in_intro _ _ hx, Bool.or_true, Bool.and_self, ↓reduceIte, List.append_nil]
  · simp only [check_socketpair_written, socketpair_writes, writes_eqb_refl, bv_eqb_refl,
      Bool.true_or, Bool.and_self, ↓reduceIte]

/-- Rocq: `Checks.Sys.Net.Socket.check_socketpair_written_no_unmodeled`. -/
theorem check_socketpair_written_no_unmodeled (sv fd1 fd2 : word) (eff : SyscallEffect)
    (m : Model) : check_socketpair_written sv fd1 fd2 eff m ≠ CheckUnmodeled := by
  unfold check_socketpair_written
  split <;> (try split) <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]

/-- The acceptor for `socketpair_faulted`: a reserve-time errno or -EFAULT,
with nothing written — the first `put_user` failed, so neither descriptor
reached user memory.  Rocq: `Checks.Sys.Net.Socket.check_socketpair_faulted`. -/
def check_socketpair_faulted (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | SyscallEffect.mkEffectU r [] [] [] [] [] =>
      if errno_ret_in socketpair_reserve_errnos r || bv_eqb r (errno_ret EFAULT)
      then CheckOk m [] else CheckReject
  | _ => CheckReject

/-- Rocq: `Checks.Sys.Net.Socket.socketpair_faulted_no_unmodeled`. -/
theorem socketpair_faulted_no_unmodeled (i : SyscallInput) (m : Model) :
    ¬ socketpair_faulted i m Unmodeled := by
  intro h
  simp only [socketpair_faulted, Monad.alt, Monad.bind, errno_from, Monad.choose, err_ret,
    ret_only, Monad.pure, reduceCtorEq, and_false, exists_false, or_self] at h

/-- Rocq: `Checks.Sys.Net.Socket.check_socketpair_faulted_sound_ok`. -/
theorem check_socketpair_faulted_sound_ok (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (h : check_socketpair_faulted eff m = CheckOk m' evs) :
    socketpair_faulted i m (Ok eff m' evs) := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws with
  | cons w ws => simp only [check_socketpair_faulted, reduceCtorEq] at h
  | nil =>
  cases zs with
  | cons z zs => simp only [check_socketpair_faulted, reduceCtorEq] at h
  | nil =>
  cases us with
  | cons u us => simp only [check_socketpair_faulted, reduceCtorEq] at h
  | nil =>
  cases cs with
  | cons c cs => simp only [check_socketpair_faulted, reduceCtorEq] at h
  | nil =>
  cases copyins with
  | cons ci copyins => simp only [check_socketpair_faulted, reduceCtorEq] at h
  | nil =>
  simp only [check_socketpair_faulted] at h
  split at h
  · rename_i hc
    simp only [check_result.CheckOk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.or_eq_true] at hc
    rcases hc with hc | hc
    · obtain ⟨e, he, rfl⟩ := (errno_ret_in_true _ ret).mp hc
      exact alt_l _ _ i m _
        (bind_ok0 _ _ i m e m _ _ _ (errno_from_witness _ e i m he) (pure_ok _ i _))
    · obtain rfl := (bv_eqb_eq _ _).mp hc
      exact alt_r _ _ i m _ (pure_ok _ i _)
  · simp only [reduceCtorEq] at h

/-- Rocq: `Checks.Sys.Net.Socket.check_socketpair_faulted_complete_ok`. -/
theorem check_socketpair_faulted_complete_ok (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput) (h : socketpair_faulted i m (Ok eff m' evs)) :
    check_socketpair_faulted eff m = CheckOk m' evs := by
  simp only [socketpair_faulted, Monad.alt, Monad.bind, errno_from, Monad.choose, err_ret,
    ret_only, Monad.pure, outcome.Ok.injEq] at h
  rcases h with ⟨e, m1, evs1, evs2, ⟨x, hx, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl⟩
    | ⟨rfl, rfl, rfl⟩
  · simp only [check_socketpair_faulted, errno_ret_in_intro _ _ hx, Bool.true_or, ↓reduceIte,
      List.append_nil]
  · simp only [check_socketpair_faulted, bv_eqb_refl, Bool.or_true, ↓reduceIte]

/-- Rocq: `Checks.Sys.Net.Socket.check_socketpair_faulted_no_unmodeled`. -/
theorem check_socketpair_faulted_no_unmodeled (eff : SyscallEffect) (m : Model) :
    check_socketpair_faulted eff m ≠ CheckUnmodeled := by
  unfold check_socketpair_faulted
  split <;> (try split) <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]

/-- The checker for `socketpair_spec`, arm for arm: the flag test, the
modeled-family test, the two-descriptor reservation, and the destination
test that picks the acceptor.  The section header reads the kernel.  Rocq:
`Checks.Sys.Net.Socket.check_socketpair`. -/
def check_socketpair (i : SyscallInput) (family type protocol sv : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if ¬ (socketpair_flags_ok type) then check_ret_only eff (errno_ret EINVAL) m []
  else if ¬ (socketpair_modeled_b family type protocol) then CheckUnmodeled
  else
  match socketpair_fds (m_fds m) with
  | none => CheckUnmodeled
  | some (fd1, fd2) =>
      if socketpair_dest_writable i.in_wmem sv then check_socketpair_written sv fd1 fd2 eff m
      else if ¬ (access_okb sv 4) then check_socketpair_faulted eff m
      else CheckUnmodeled

/-- Rocq: `Checks.Sys.Net.Socket.check_socketpair_sound_ok`. -/
theorem check_socketpair_sound_ok (i : SyscallInput) (family type protocol sv : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_socketpair i family type protocol sv eff m = CheckOk m' evs) :
    socketpair_spec family type protocol sv i m (Ok eff m' evs) := by
  unfold check_socketpair at h
  unfold socketpair_spec
  cases hfl : socketpair_flags_ok type with
  | false =>
    simp only [hfl, Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | true =>
    simp only [hfl, not_true_eq_false, ↓reduceIte] at h ⊢
    cases hmo : socketpair_modeled_b family type protocol with
    | false => simp only [hmo, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, reduceCtorEq] at h
    | true =>
      simp only [hmo, not_true_eq_false, ↓reduceIte] at h ⊢
      apply bind_ok0 _ _ i m i m _ _ _ (input_ok i m)
      apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
      generalize socketpair_fds (m_fds m) = r at h ⊢
      cases r with
      | none => simp only [reduceCtorEq] at h
      | some p =>
        obtain ⟨fd1, fd2⟩ := p
        simp only [] at h ⊢
        cases hw : socketpair_dest_writable i.in_wmem sv with
        | true =>
          simp only [hw, ↓reduceIte] at h ⊢
          exact check_socketpair_written_sound_ok _ _ _ _ _ _ _ i h
        | false =>
          simp only [hw, Bool.false_eq_true, ↓reduceIte] at h ⊢
          cases ha : access_okb sv 4 with
          | false =>
            simp only [ha, Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at h ⊢
            exact check_socketpair_faulted_sound_ok _ _ _ _ i h
          | true => simp only [ha, not_true_eq_false, ↓reduceIte, reduceCtorEq] at h

/-- Rocq: `Checks.Sys.Net.Socket.check_socketpair_sound_unmodeled`. -/
theorem check_socketpair_sound_unmodeled (i : SyscallInput) (family type protocol sv : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_socketpair i family type protocol sv eff m = CheckUnmodeled) :
    socketpair_spec family type protocol sv i m Unmodeled := by
  unfold check_socketpair at h
  unfold socketpair_spec
  cases hfl : socketpair_flags_ok type with
  | false =>
    simp only [hfl, Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | true =>
    simp only [hfl, not_true_eq_false, ↓reduceIte] at h ⊢
    cases hmo : socketpair_modeled_b family type protocol with
    | false =>
      simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
      exact unmodeled_intro i m
    | true =>
      simp only [hmo, not_true_eq_false, ↓reduceIte] at h ⊢
      apply bind_unmodeled2 _ _ i m i m [] (input_ok i m)
      apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
      generalize socketpair_fds (m_fds m) = r at h ⊢
      cases r with
      | none => exact unmodeled_intro i m
      | some p =>
        obtain ⟨fd1, fd2⟩ := p
        simp only [] at h ⊢
        cases hw : socketpair_dest_writable i.in_wmem sv with
        | true =>
          simp only [hw, ↓reduceIte] at h
          exact absurd h (check_socketpair_written_no_unmodeled _ _ _ _ _)
        | false =>
          simp only [hw, Bool.false_eq_true, ↓reduceIte] at h ⊢
          cases ha : access_okb sv 4 with
          | false =>
            simp only [ha, Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at h
            exact absurd h (check_socketpair_faulted_no_unmodeled _ _)
          | true =>
            simp only [not_true_eq_false, ↓reduceIte]
            exact unmodeled_intro i m

/-- Rocq: `Checks.Sys.Net.Socket.check_socketpair_complete_ok`. -/
theorem check_socketpair_complete_ok (i : SyscallInput) (family type protocol sv : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : socketpair_spec family type protocol sv i m (Ok eff m' evs)) :
    check_socketpair i family type protocol sv eff m = CheckOk m' evs := by
  unfold socketpair_spec at h
  unfold check_socketpair
  cases hfl : socketpair_flags_ok type with
  | false =>
    simp only [hfl, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, err_ret, ret_only,
      pure_iff] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | true =>
    simp only [hfl, not_true_eq_false, ↓reduceIte] at h ⊢
    cases hmo : socketpair_modeled_b family type protocol with
    | false =>
      simp only [hmo, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, unmodeled_iff,
        reduceCtorEq] at h
    | true =>
      simp only [hmo, not_true_eq_false, ↓reduceIte] at h ⊢
      have h := bind_input_model_inv _ i m _ h
      generalize socketpair_fds (m_fds m) = r at h ⊢
      cases r with
      | none => simp only [unmodeled_iff, reduceCtorEq] at h
      | some p =>
        obtain ⟨fd1, fd2⟩ := p
        simp only [] at h ⊢
        cases hw : socketpair_dest_writable i.in_wmem sv with
        | true =>
          simp only [hw, ↓reduceIte] at h ⊢
          exact check_socketpair_written_complete_ok _ _ _ _ _ _ _ i h
        | false =>
          simp only [hw, Bool.false_eq_true, ↓reduceIte] at h ⊢
          cases ha : access_okb sv 4 with
          | false =>
            simp only [ha, Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at h ⊢
            exact check_socketpair_faulted_complete_ok _ _ _ _ i h
          | true =>
            simp only [ha, not_true_eq_false, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h

/-- Rocq: `Checks.Sys.Net.Socket.check_socketpair_complete_unmodeled`. -/
theorem check_socketpair_complete_unmodeled (i : SyscallInput) (family type protocol sv : word)
    (m : Model) (eff : SyscallEffect)
    (h : socketpair_spec family type protocol sv i m Unmodeled) :
    check_socketpair i family type protocol sv eff m = CheckUnmodeled := by
  unfold socketpair_spec at h
  unfold check_socketpair
  cases hfl : socketpair_flags_ok type with
  | false =>
    simp only [hfl, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, err_ret, ret_only,
      pure_iff, reduceCtorEq] at h
  | true =>
    simp only [hfl, not_true_eq_false, ↓reduceIte] at h ⊢
    cases hmo : socketpair_modeled_b family type protocol with
    | false => simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
    | true =>
      simp only [hmo, not_true_eq_false, ↓reduceIte] at h ⊢
      have h := bind_input_model_inv _ i m _ h
      generalize socketpair_fds (m_fds m) = r at h ⊢
      cases r with
      | none => rfl
      | some p =>
        obtain ⟨fd1, fd2⟩ := p
        simp only [] at h ⊢
        cases hw : socketpair_dest_writable i.in_wmem sv with
        | true =>
          simp only [hw, ↓reduceIte] at h
          exact absurd h (socketpair_written_no_unmodeled _ _ _ i m)
        | false =>
          simp only [hw, Bool.false_eq_true, ↓reduceIte] at h ⊢
          cases ha : access_okb sv 4 with
          | false =>
            simp only [ha, Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at h
            exact absurd h (socketpair_faulted_no_unmodeled i m)
          | true => simp only [not_true_eq_false, ↓reduceIte]

/-! ## socket (198)

The checker takes `socket_spec`'s gates in the spec's order: the flag
word in `__sys_socket_create` (net/socket.c:1686, at :1697-1699, Linux
v6.18.46), the family and type ranges in `__sock_create` (:1535, at
:1545-1548), the protocol range and the protocol lookup in `inet_create`
(net/ipv4/af_inet.c:254, at :265-266 and :271-291, v6.18.46), and the
descriptor last, in `sock_map_fd` (net/socket.c:504, at :507, v6.18.46).
So a call two gates would refuse is answered by the earlier one, and only
a call past the protocol lookup reaches the descriptor-minting acceptor.
The LSM run configuration is tracked by linux-process-semantics@ff0313ba4f
issue #1472 (T152), which rocq-linux-process-semantics f1006fe8 does not
name.  Each
gate is spelled exactly as `socket_spec` spells it — on the low 32 bits of
`type` as a `word`, `sint32` of the family and the protocol — so one
`by_cases` on the shared proposition decides the checker and the spec
together; the proofs are that split, gate by gate. -/

/-- The errnos of `socket_errnos` are in `[1, 4095]`, which is what
`Open.errno_ret_in_alloc_fd` asks of the set before it can say that no
descriptor `alloc_fd` hands out reads as one of them. -/
theorem socket_errnos_ok : errnos_ok socket_errnos = true := by decide

/-- The acceptor for an `alt` whose success side admits NOTHING, leaving
the injected errno as the only outcome: `accept4_spec` on a listening
socket once `conn_ix_exhausted` holds, where the success branch is
`choose (fun _ => False)`.  A returned descriptor is therefore not
admissible however it was allocated, which is why this is not
`Open.check_new_fd_result` with an empty `mk` — that would still accept
`alloc_fd`'s value.  Rocq: `Checks.Sys.Net.Socket.check_errno_only`. -/
def check_errno_only (es : List Int) (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | SyscallEffect.mkEffectU ret [] [] [] [] [] =>
      if errno_ret_in es ret then CheckOk m [] else CheckReject
  | _ => CheckReject

/-- What `check_errno_only` accepts: a bare return that is one of `es`'s
errnos, at the model it was handed and with no event.  Lean-only, the
shape of `Open.check_new_fd_result_ok_inv`; `check_errno_only_sound_ok`
reads the errno side off it. -/
theorem check_errno_only_ok_inv (es : List Int) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_errno_only es eff m = CheckOk m' evs) :
    m' = m ∧ evs = [] ∧ ∃ ret, eff = mkEffect ret [] [] ∧ errno_ret_in es ret = true := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws with
  | cons w ws => simp only [check_errno_only, reduceCtorEq] at h
  | nil =>
  cases zs with
  | cons z zs => simp only [check_errno_only, reduceCtorEq] at h
  | nil =>
  cases us with
  | cons u us => simp only [check_errno_only, reduceCtorEq] at h
  | nil =>
  cases cs with
  | cons c cs => simp only [check_errno_only, reduceCtorEq] at h
  | nil =>
  cases copyins with
  | cons ci copyins => simp only [check_errno_only, reduceCtorEq] at h
  | nil =>
  simp only [check_errno_only] at h
  cases hin : errno_ret_in es ret with
  | true =>
    simp only [hin, ↓reduceIte, check_result.CheckOk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, ret, rfl, hin⟩
  | false => simp only [hin, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-- Rocq: `Checks.Sys.Net.Socket.check_errno_only_no_unmodeled`.  Neither
arm of the acceptor declines: the `choose (fun _ => False)` contributes no
`Ok`, and being a `choose` rather than `unmodeled`, no `Unmodeled` either. -/
theorem check_errno_only_no_unmodeled (es : List Int) (eff : SyscallEffect) (m : Model) :
    check_errno_only es eff m ≠ CheckUnmodeled := by
  unfold check_errno_only
  split <;> (try split) <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]

/-- Rocq: `Checks.Sys.Net.Socket.check_errno_only_sound_ok`.  A `CheckOk` is
the errno side of the `alt`, the return being `-e` for an `e` of `es`. -/
theorem check_errno_only_sound_ok (es : List Int) (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_errno_only es eff m = CheckOk m' evs) :
    alt (e <- errno_from es ;; err_ret e) (choose (fun (_ : SyscallEffect) => False))
      i m (Ok eff m' evs) := by
  obtain ⟨hm, rfl, ret, rfl, hin⟩ := check_errno_only_ok_inv es eff m m' evs h
  rw [hm]
  obtain ⟨e, he, rfl⟩ := (errno_ret_in_true es ret).mp hin
  apply alt_l
  exact bind_ok0 _ _ i m e m _ _ _ (errno_from_witness es e i m he) (pure_ok _ i _)

/-- Rocq: `Checks.Sys.Net.Socket.check_errno_only_complete_ok`.  An
outcome of the `alt` is its errno side, the `choose` side having none,
and the acceptor takes it. -/
theorem check_errno_only_complete_ok (es : List Int) (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : alt (e <- errno_from es ;; err_ret e) (choose (fun (_ : SyscallEffect) => False))
      i m (Ok eff m' evs)) :
    check_errno_only es eff m = CheckOk m' evs := by
  rw [alt_iff] at h
  rcases h with h | h
  · unfold errno_from at h
    rw [bind_choose_iff] at h
    obtain ⟨er, hmem, h⟩ := h
    simp only [err_ret, ret_only, pure_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    simp only [check_errno_only, errno_ret_in_intro es er hmem, ↓reduceIte]
  · obtain ⟨_, hF, _⟩ := h
    exact hF.elim

/-- The `alt` has no `Unmodeled`: a `choose` and a `pure` on the left, an
empty `choose` on the right.  Lean-only; the premise
`check_accept4_complete_unmodeled` refutes on the exhausted arm. -/
theorem errno_only_no_unmodeled (es : List Int) (i : SyscallInput) (m : Model) :
    ¬ alt (e <- errno_from es ;; err_ret e) (choose (fun (_ : SyscallEffect) => False))
      i m Unmodeled := by
  intro h
  unfold errno_from at h
  simp only [alt_iff, bind_choose_iff, err_ret, ret_only, pure_iff, Monad.choose, reduceCtorEq,
    and_false, exists_false, or_self] at h

/-- Rocq: `Checks.Sys.Net.Socket.check_socket`.  The SCTP and MPTCP
declines follow this tree's spec twin. -/
def check_socket (domain type protocol : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  let tu := abi_low32 type
  let flagbits := bv_and tu (bv_not (Z_to_bv 64 SOCK_TYPE_MASK))
  if ¬ (bv_unsigned (bv_and flagbits
          (bv_not (bv_or (Z_to_bv 64 SOCK_CLOEXEC) (Z_to_bv 64 SOCK_NONBLOCK)))) = 0)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if ¬ (bv_unsigned (bv_and flagbits (Z_to_bv 64 SOCK_NONBLOCK)) = 0) then CheckUnmodeled
  else
    let ty : Int := bv_unsigned (bv_and tu (Z_to_bv 64 SOCK_TYPE_MASK))
    let fam : Int := sint32 domain
    let pro : Int := sint32 protocol
    if fam < 0 ∨ NPROTO ≤ fam then check_ret_only eff (errno_ret EAFNOSUPPORT) m []
    else if SOCK_MAX ≤ ty then check_ret_only eff (errno_ret EINVAL) m []
    else if ¬ (fam = AF_INET) then CheckUnmodeled
    else if ty = SOCK_PACKET then CheckUnmodeled
    else if pro < 0 ∨ IPPROTO_MAX ≤ pro then check_ret_only eff (errno_ret EINVAL) m []
    else if ty = SOCK_STREAM then
      if pro = IPPROTO_SCTP ∨ pro = IPPROTO_MPTCP then CheckUnmodeled
      else if ¬ (pro = IPPROTO_IP ∨ pro = IPPROTO_TCP)
      then check_ret_only eff (errno_ret EPROTONOSUPPORT) m []
      else check_new_fd_result socket_errnos eff m
             (fun fd => with_fds (fd_insert (m_fds m) fd (.FdSocket .SkFresh)) m)
    else if ty = SOCK_DGRAM ∨ ty = SOCK_RAW then CheckUnmodeled
    else if ty = SOCK_SEQPACKET ∨ ty = SOCK_DCCP then CheckUnmodeled
    else check_ret_only eff (errno_ret ESOCKTNOSUPPORT) m []

/-- Rocq: `Checks.Sys.Net.Socket.check_socket_sound_ok`.  Every accepting
leaf is the spec's: a `check_ret_only` verdict is the spec's `err_ret`,
and `check_new_fd_result`'s two cases are the two sides of the spec's
`alt` — the errno drawn from `socket_errnos`, or the lowest free
descriptor `lowest_fd` chooses with the fresh socket installed there. -/
theorem check_socket_sound_ok (domain type protocol : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (h : check_socket domain type protocol eff m = CheckOk m' evs) :
    socket_spec domain type protocol i m (Ok eff m' evs) := by
  unfold check_socket at h
  unfold socket_spec
  generalize sint32 domain = fam at h ⊢
  generalize sint32 protocol = pro at h ⊢
  generalize abi_low32 type = tu at h ⊢
  refine bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m) ?_
  simp only [] at h ⊢
  by_cases h1 : bv_unsigned (bv_and (bv_and tu (bv_not (Z_to_bv 64 SOCK_TYPE_MASK)))
      (bv_not (bv_or (Z_to_bv 64 SOCK_CLOEXEC) (Z_to_bv 64 SOCK_NONBLOCK)))) = 0
  case neg =>
    simp only [h1, not_false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  simp only [h1, not_true_eq_false, ↓reduceIte] at h ⊢
  by_cases h2 : bv_unsigned (bv_and (bv_and tu (bv_not (Z_to_bv 64 SOCK_TYPE_MASK)))
      (Z_to_bv 64 SOCK_NONBLOCK)) = 0
  case neg =>
    simp only [h2, not_false_eq_true, ↓reduceIte, reduceCtorEq] at h
  simp only [h2, not_true_eq_false, ↓reduceIte] at h ⊢
  generalize bv_unsigned (bv_and tu (Z_to_bv 64 SOCK_TYPE_MASK)) = ty at h ⊢
  by_cases h3 : fam < 0 ∨ NPROTO ≤ fam
  · simp only [h3, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  simp only [h3, ↓reduceIte] at h ⊢
  by_cases h4 : SOCK_MAX ≤ ty
  · simp only [h4, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  simp only [h4, ↓reduceIte] at h ⊢
  by_cases h5 : fam = AF_INET
  case neg =>
    simp only [h5, not_false_eq_true, ↓reduceIte, reduceCtorEq] at h
  simp only [h5, not_true_eq_false, ↓reduceIte] at h ⊢
  by_cases h6 : ty = SOCK_PACKET
  · simp only [h6, ↓reduceIte, reduceCtorEq] at h
  simp only [h6, ↓reduceIte] at h ⊢
  by_cases h7 : pro < 0 ∨ IPPROTO_MAX ≤ pro
  · simp only [h7, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  simp only [h7, ↓reduceIte] at h ⊢
  by_cases h8 : ty = SOCK_STREAM
  · simp only [h8, ↓reduceIte] at h ⊢
    by_cases h9 : pro = IPPROTO_SCTP ∨ pro = IPPROTO_MPTCP
    · simp only [h9, ↓reduceIte, reduceCtorEq] at h
    simp only [h9, ↓reduceIte] at h ⊢
    by_cases h10 : pro = IPPROTO_IP ∨ pro = IPPROTO_TCP
    case neg =>
      simp only [h10, not_false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _
    simp only [h10, not_true_eq_false, ↓reduceIte] at h ⊢
    obtain ⟨rfl, ret, rfl, hcase⟩ := check_new_fd_result_ok_inv socket_errnos eff m _ m' evs h
    unfold errno_from lowest_fd set_fds
    rcases hcase with ⟨he, hm⟩ | ⟨hnone, hfd', hm⟩ <;> subst m'
    · obtain ⟨er, hmem, rfl⟩ := (errno_ret_in_true socket_errnos ret).mp he
      apply alt_l
      refine bind_ok0 _ _ i m er m _ _ _ (choose_ok _ er i m hmem) ?_
      exact pure_ok _ i m
    · apply alt_r
      refine bind_ok0 _ _ i m ret m _ _ _ (choose_ok _ ret i m (And.intro hnone hfd')) ?_
      refine bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m) ?_
      exact pure_ok _ i _
  simp only [h8, ↓reduceIte] at h ⊢
  by_cases h11 : ty = SOCK_DGRAM ∨ ty = SOCK_RAW
  · simp only [h11, ↓reduceIte, reduceCtorEq] at h
  simp only [h11, ↓reduceIte] at h ⊢
  by_cases h12 : ty = SOCK_SEQPACKET ∨ ty = SOCK_DCCP
  · simp only [h12, ↓reduceIte, reduceCtorEq] at h
  simp only [h12, ↓reduceIte] at h ⊢
  obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
  exact pure_ok _ i _

/-- Rocq: `Checks.Sys.Net.Socket.check_socket_sound_unmodeled`.  The
acceptors the checker reaches do not decline (`check_ret_only_no_unmodeled`,
`Open.check_new_fd_result_no_unmodeled`), so a `CheckUnmodeled` can only
have come from a gate the spec declines at. -/
theorem check_socket_sound_unmodeled (domain type protocol : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (h : check_socket domain type protocol eff m = CheckUnmodeled) :
    socket_spec domain type protocol i m Unmodeled := by
  unfold check_socket at h
  unfold socket_spec
  generalize sint32 domain = fam at h ⊢
  generalize sint32 protocol = pro at h ⊢
  generalize abi_low32 type = tu at h ⊢
  refine bind_unmodeled2 _ _ i m m m [] (get_model_ok i m) ?_
  simp only [] at h ⊢
  by_cases h1 : bv_unsigned (bv_and (bv_and tu (bv_not (Z_to_bv 64 SOCK_TYPE_MASK)))
      (bv_not (bv_or (Z_to_bv 64 SOCK_CLOEXEC) (Z_to_bv 64 SOCK_NONBLOCK)))) = 0
  case neg =>
    simp only [h1, not_false_eq_true, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  simp only [h1, not_true_eq_false, ↓reduceIte] at h ⊢
  by_cases h2 : bv_unsigned (bv_and (bv_and tu (bv_not (Z_to_bv 64 SOCK_TYPE_MASK)))
      (Z_to_bv 64 SOCK_NONBLOCK)) = 0
  case neg =>
    simp only [h2, not_false_eq_true, ↓reduceIte]
    exact unmodeled_intro i m
  simp only [h2, not_true_eq_false, ↓reduceIte] at h ⊢
  generalize bv_unsigned (bv_and tu (Z_to_bv 64 SOCK_TYPE_MASK)) = ty at h ⊢
  by_cases h3 : fam < 0 ∨ NPROTO ≤ fam
  · simp only [h3, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  simp only [h3, ↓reduceIte] at h ⊢
  by_cases h4 : SOCK_MAX ≤ ty
  · simp only [h4, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  simp only [h4, ↓reduceIte] at h ⊢
  by_cases h5 : fam = AF_INET
  case neg =>
    simp only [h5, not_false_eq_true, ↓reduceIte]
    exact unmodeled_intro i m
  simp only [h5, not_true_eq_false, ↓reduceIte] at h ⊢
  by_cases h6 : ty = SOCK_PACKET
  · simp only [h6, ↓reduceIte]
    exact unmodeled_intro i m
  simp only [h6, ↓reduceIte] at h ⊢
  by_cases h7 : pro < 0 ∨ IPPROTO_MAX ≤ pro
  · simp only [h7, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  simp only [h7, ↓reduceIte] at h ⊢
  by_cases h8 : ty = SOCK_STREAM
  · simp only [h8, ↓reduceIte] at h ⊢
    by_cases h9 : pro = IPPROTO_SCTP ∨ pro = IPPROTO_MPTCP
    · simp only [h9, ↓reduceIte]
      exact unmodeled_intro i m
    simp only [h9, ↓reduceIte] at h ⊢
    by_cases h10 : pro = IPPROTO_IP ∨ pro = IPPROTO_TCP
    case neg =>
      simp only [h10, not_false_eq_true, ↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    simp only [h10, not_true_eq_false, ↓reduceIte] at h
    exact absurd h (check_new_fd_result_no_unmodeled _ _ _ _)
  simp only [h8, ↓reduceIte] at h ⊢
  by_cases h11 : ty = SOCK_DGRAM ∨ ty = SOCK_RAW
  · simp only [h11, ↓reduceIte]
    exact unmodeled_intro i m
  simp only [h11, ↓reduceIte] at h ⊢
  by_cases h12 : ty = SOCK_SEQPACKET ∨ ty = SOCK_DCCP
  · simp only [h12, ↓reduceIte]
    exact unmodeled_intro i m
  simp only [h12, ↓reduceIte] at h
  exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

/-- Rocq: `Checks.Sys.Net.Socket.check_socket_complete_ok`. -/
theorem check_socket_complete_ok (domain type protocol : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (h : socket_spec domain type protocol i m (Ok eff m' evs)) :
    check_socket domain type protocol eff m = CheckOk m' evs := by
  unfold socket_spec at h
  unfold check_socket
  generalize sint32 domain = fam at h ⊢
  generalize sint32 protocol = pro at h ⊢
  generalize abi_low32 type = tu at h ⊢
  have h := bind_model_inv _ i m _ h
  simp only [] at h ⊢
  by_cases h1 : bv_unsigned (bv_and (bv_and tu (bv_not (Z_to_bv 64 SOCK_TYPE_MASK)))
      (bv_not (bv_or (Z_to_bv 64 SOCK_CLOEXEC) (Z_to_bv 64 SOCK_NONBLOCK)))) = 0
  case neg =>
    simp only [h1, not_false_eq_true, ↓reduceIte, err_ret, ret_only, pure_iff] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  simp only [h1, not_true_eq_false, ↓reduceIte] at h ⊢
  by_cases h2 : bv_unsigned (bv_and (bv_and tu (bv_not (Z_to_bv 64 SOCK_TYPE_MASK)))
      (Z_to_bv 64 SOCK_NONBLOCK)) = 0
  case neg =>
    simp only [h2, not_false_eq_true, ↓reduceIte] at h
    exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])
  simp only [h2, not_true_eq_false, ↓reduceIte] at h ⊢
  generalize bv_unsigned (bv_and tu (Z_to_bv 64 SOCK_TYPE_MASK)) = ty at h ⊢
  by_cases h3 : fam < 0 ∨ NPROTO ≤ fam
  · simp only [h3, ↓reduceIte, err_ret, ret_only, pure_iff] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  simp only [h3, ↓reduceIte] at h ⊢
  by_cases h4 : SOCK_MAX ≤ ty
  · simp only [h4, ↓reduceIte, err_ret, ret_only, pure_iff] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  simp only [h4, ↓reduceIte] at h ⊢
  by_cases h5 : fam = AF_INET
  case neg =>
    simp only [h5, not_false_eq_true, ↓reduceIte] at h
    exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])
  simp only [h5, not_true_eq_false, ↓reduceIte] at h ⊢
  by_cases h6 : ty = SOCK_PACKET
  · simp only [h6, ↓reduceIte] at h
    exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])
  simp only [h6, ↓reduceIte] at h ⊢
  by_cases h7 : pro < 0 ∨ IPPROTO_MAX ≤ pro
  · simp only [h7, ↓reduceIte, err_ret, ret_only, pure_iff] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  simp only [h7, ↓reduceIte] at h ⊢
  by_cases h8 : ty = SOCK_STREAM
  · simp only [h8, ↓reduceIte] at h ⊢
    by_cases h9 : pro = IPPROTO_SCTP ∨ pro = IPPROTO_MPTCP
    · simp only [h9, ↓reduceIte] at h
      exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])
    simp only [h9, ↓reduceIte] at h ⊢
    by_cases h10 : pro = IPPROTO_IP ∨ pro = IPPROTO_TCP
    case neg =>
      simp only [h10, not_false_eq_true, ↓reduceIte, err_ret, ret_only, pure_iff] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    simp only [h10, not_true_eq_false, ↓reduceIte] at h ⊢
    unfold errno_from lowest_fd set_fds at h
    rw [alt_iff] at h
    rcases h with h | h
    · rw [bind_choose_iff] at h
      obtain ⟨er, hmem, h⟩ := h
      simp only [err_ret, ret_only, pure_iff] at h
      obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
      simp only [check_new_fd_result, errno_ret_in_intro socket_errnos er hmem, ↓reduceIte]
    · rw [bind_choose_iff] at h
      obtain ⟨fd, ⟨hnone, hfd'⟩, h⟩ := h
      simp only [bind_modify_iff, ret_only, pure_iff] at h
      obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
      subst hfd'
      simp only [check_new_fd_result, errno_ret_in_alloc_fd _ _ socket_errnos_ok,
        Bool.false_eq_true, ↓reduceIte, hnone, bv_eqb_refl]
  simp only [h8, ↓reduceIte] at h ⊢
  by_cases h11 : ty = SOCK_DGRAM ∨ ty = SOCK_RAW
  · simp only [h11, ↓reduceIte] at h
    exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])
  simp only [h11, ↓reduceIte] at h ⊢
  by_cases h12 : ty = SOCK_SEQPACKET ∨ ty = SOCK_DCCP
  · simp only [h12, ↓reduceIte] at h
    exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])
  simp only [h12, ↓reduceIte] at h ⊢
  simp only [err_ret, ret_only, pure_iff] at h
  obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
  exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- Rocq: `Checks.Sys.Net.Socket.check_socket_complete_unmodeled`.  Where the
spec declines, the checker declines whatever effect it is offered; on the
other arms the spec's `Unmodeled` is impossible — an `err_ret`, or on the
passing call an `alt` of a `choose` and a `pure` on each side. -/
theorem check_socket_complete_unmodeled (domain type protocol : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (h : socket_spec domain type protocol i m Unmodeled) :
    check_socket domain type protocol eff m = CheckUnmodeled := by
  unfold socket_spec at h
  unfold check_socket
  generalize sint32 domain = fam at h ⊢
  generalize sint32 protocol = pro at h ⊢
  generalize abi_low32 type = tu at h ⊢
  have h := bind_model_inv _ i m _ h
  simp only [] at h ⊢
  by_cases h1 : bv_unsigned (bv_and (bv_and tu (bv_not (Z_to_bv 64 SOCK_TYPE_MASK)))
      (bv_not (bv_or (Z_to_bv 64 SOCK_CLOEXEC) (Z_to_bv 64 SOCK_NONBLOCK)))) = 0
  case neg =>
    simp only [h1, not_false_eq_true, ↓reduceIte, err_ret, ret_only, pure_iff,
      reduceCtorEq] at h
  simp only [h1, not_true_eq_false, ↓reduceIte] at h ⊢
  by_cases h2 : bv_unsigned (bv_and (bv_and tu (bv_not (Z_to_bv 64 SOCK_TYPE_MASK)))
      (Z_to_bv 64 SOCK_NONBLOCK)) = 0
  case neg =>
    simp only [h2, not_false_eq_true, ↓reduceIte]
  simp only [h2, not_true_eq_false, ↓reduceIte] at h ⊢
  generalize bv_unsigned (bv_and tu (Z_to_bv 64 SOCK_TYPE_MASK)) = ty at h ⊢
  by_cases h3 : fam < 0 ∨ NPROTO ≤ fam
  · simp only [h3, ↓reduceIte, err_ret, ret_only, pure_iff, reduceCtorEq] at h
  simp only [h3, ↓reduceIte] at h ⊢
  by_cases h4 : SOCK_MAX ≤ ty
  · simp only [h4, ↓reduceIte, err_ret, ret_only, pure_iff, reduceCtorEq] at h
  simp only [h4, ↓reduceIte] at h ⊢
  by_cases h5 : fam = AF_INET
  case neg =>
    simp only [h5, not_false_eq_true, ↓reduceIte]
  simp only [h5, not_true_eq_false, ↓reduceIte] at h ⊢
  by_cases h6 : ty = SOCK_PACKET
  · simp only [h6, ↓reduceIte]
  simp only [h6, ↓reduceIte] at h ⊢
  by_cases h7 : pro < 0 ∨ IPPROTO_MAX ≤ pro
  · simp only [h7, ↓reduceIte, err_ret, ret_only, pure_iff, reduceCtorEq] at h
  simp only [h7, ↓reduceIte] at h ⊢
  by_cases h8 : ty = SOCK_STREAM
  · simp only [h8, ↓reduceIte] at h ⊢
    by_cases h9 : pro = IPPROTO_SCTP ∨ pro = IPPROTO_MPTCP
    · simp only [h9, ↓reduceIte]
    simp only [h9, ↓reduceIte] at h ⊢
    by_cases h10 : pro = IPPROTO_IP ∨ pro = IPPROTO_TCP
    case neg =>
      simp only [h10, not_false_eq_true, ↓reduceIte, err_ret, ret_only, pure_iff,
        reduceCtorEq] at h
    simp only [h10, not_true_eq_false, ↓reduceIte] at h
    unfold errno_from lowest_fd set_fds at h
    simp only [alt_iff, bind_choose_iff, err_ret, ret_only, pure_iff, bind_modify_iff,
      reduceCtorEq, and_false, exists_false, or_self] at h
  simp only [h8, ↓reduceIte] at h ⊢
  by_cases h11 : ty = SOCK_DGRAM ∨ ty = SOCK_RAW
  · simp only [h11, ↓reduceIte]
  simp only [h11, ↓reduceIte] at h ⊢
  by_cases h12 : ty = SOCK_SEQPACKET ∨ ty = SOCK_DCCP
  · simp only [h12, ↓reduceIte]
  simp only [h12, ↓reduceIte, err_ret, ret_only, pure_iff, reduceCtorEq] at h

/-! ## accept (202) and accept4 (242)

`accept` reaches this checker with zero flags.  -EBADF comes before the
flags are even looked at, and the descriptor and address ordering below
it follows `accept4_spec`. -/

/-- The errnos of `accept_errnos` are in `[1, 4095]`, which is what
`Open.errno_ret_in_alloc_fd` asks of the set. -/
theorem accept_errnos_ok : errnos_ok accept_errnos = true := by decide

set_option linter.unusedVariables false in
/-- Rocq: `Checks.Sys.Net.Socket.check_accept4`. -/
def check_accept4 (fd addrp addrlenp flags : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some e =>
      let fl := abi_low32 flags
      if ¬ (bv_unsigned (bv_and fl
              (bv_not (bv_or (Z_to_bv 64 SOCK_CLOEXEC) (Z_to_bv 64 SOCK_NONBLOCK)))) = 0)
      then check_ret_only eff (errno_ret EINVAL) m []
      else if ¬ (bv_unsigned (bv_and fl (Z_to_bv 64 SOCK_NONBLOCK)) = 0) then CheckUnmodeled
      else
      (match e with
       | .FdSocket sk =>
           if ¬ (w_is0 addrp) then CheckUnmodeled
           else
           (match sk with
            | .SkListening =>
                if conn_ix_exhausted (m_conn_ix m) then check_errno_only accept_errnos eff m
                else
                  check_new_fd_result accept_errnos eff m
                    (fun nfd =>
                       with_accepted
                         (fd_insert (m_fds m) nfd
                           (.FdSocket (.SkConnected (nq_peer (m_net m))
                                                    (conn_channel (m_conn_ix m))
                                                    (nq_script (m_net m))))) m)
            | _ => check_ret_only eff (errno_ret EINVAL) m [])
       | _ => check_ret_only eff (errno_ret ENOTSOCK) m [])

/-- Rocq: `Checks.Sys.Net.Socket.check_accept4_sound_ok`.  The same
descriptor, flag, kind, address and state tests as the spec; the listening
arm's two acceptors are the spec's `alt` read from either side —
`check_errno_only_sound_ok` on an exhausted counter, and
`check_new_fd_result_ok_inv`'s two cases otherwise. -/
theorem check_accept4_sound_ok (fd addrp addrlenp flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (h : check_accept4 fd addrp addrlenp flags eff m = CheckOk m' evs) :
    accept4_spec fd addrp addrlenp flags i m (Ok eff m' evs) := by
  unfold check_accept4 at h
  unfold accept4_spec
  generalize abi_low32 flags = fl at h ⊢
  refine bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m) ?_
  simp only [] at h ⊢
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none =>
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | some e =>
    simp only [] at h ⊢
    by_cases h1 : bv_unsigned (bv_and fl
        (bv_not (bv_or (Z_to_bv 64 SOCK_CLOEXEC) (Z_to_bv 64 SOCK_NONBLOCK)))) = 0
    case neg =>
      simp only [h1, not_false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _
    simp only [h1, not_true_eq_false, ↓reduceIte] at h ⊢
    by_cases h2 : bv_unsigned (bv_and fl (Z_to_bv 64 SOCK_NONBLOCK)) = 0
    case neg => simp only [h2, not_false_eq_true, ↓reduceIte, reduceCtorEq] at h
    simp only [h2, not_true_eq_false, ↓reduceIte] at h ⊢
    cases e
    case FdSocket sk =>
      simp only [] at h ⊢
      cases ha : w_is0 addrp with
      | false =>
        simp only [ha, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, reduceCtorEq] at h
      | true =>
        simp only [ha, not_true_eq_false, ↓reduceIte] at h ⊢
        cases sk
        case SkListening =>
          simp only [] at h ⊢
          cases hx : conn_ix_exhausted (m_conn_ix m) with
          | true =>
            simp only [hx, ↓reduceIte] at h ⊢
            exact check_errno_only_sound_ok _ i _ _ _ _ h
          | false =>
            simp only [hx, Bool.false_eq_true, ↓reduceIte] at h ⊢
            obtain ⟨rfl, ret, rfl, hcase⟩ :=
              check_new_fd_result_ok_inv accept_errnos eff m _ m' evs h
            unfold errno_from lowest_fd
            rcases hcase with ⟨he, hm⟩ | ⟨hnone, hfd', hm⟩ <;> subst m'
            · obtain ⟨er, hmem, rfl⟩ := (errno_ret_in_true accept_errnos ret).mp he
              apply alt_l
              refine bind_ok0 _ _ i m er m _ _ _ (choose_ok _ er i m hmem) ?_
              exact pure_ok _ i m
            · apply alt_r
              refine bind_ok0 _ _ i m ret m _ _ _ (choose_ok _ ret i m (And.intro hnone hfd')) ?_
              refine bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m) ?_
              exact pure_ok _ i _
        all_goals
          obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
          exact pure_ok _ i _
    all_goals
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _

/-- Rocq: `Checks.Sys.Net.Socket.check_accept4_sound_unmodeled`.  As for
`check_socket`: the acceptors do not decline (`check_ret_only_no_unmodeled`,
`check_errno_only_no_unmodeled`, `Open.check_new_fd_result_no_unmodeled`),
so a `CheckUnmodeled` is a gate's,
and each such gate is one the spec declines at. -/
theorem check_accept4_sound_unmodeled (fd addrp addrlenp flags : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (h : check_accept4 fd addrp addrlenp flags eff m = CheckUnmodeled) :
    accept4_spec fd addrp addrlenp flags i m Unmodeled := by
  unfold check_accept4 at h
  unfold accept4_spec
  generalize abi_low32 flags = fl at h ⊢
  refine bind_unmodeled2 _ _ i m m m [] (get_model_ok i m) ?_
  simp only [] at h ⊢
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | some e =>
    simp only [] at h ⊢
    by_cases h1 : bv_unsigned (bv_and fl
        (bv_not (bv_or (Z_to_bv 64 SOCK_CLOEXEC) (Z_to_bv 64 SOCK_NONBLOCK)))) = 0
    case neg =>
      simp only [h1, not_false_eq_true, ↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    simp only [h1, not_true_eq_false, ↓reduceIte] at h ⊢
    by_cases h2 : bv_unsigned (bv_and fl (Z_to_bv 64 SOCK_NONBLOCK)) = 0
    case neg =>
      simp only [h2, not_false_eq_true, ↓reduceIte]
      exact unmodeled_intro i m
    simp only [h2, not_true_eq_false, ↓reduceIte] at h ⊢
    cases e
    case FdSocket sk =>
      simp only [] at h ⊢
      cases ha : w_is0 addrp with
      | false =>
        simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
        exact unmodeled_intro i m
      | true =>
        simp only [ha, not_true_eq_false, ↓reduceIte] at h ⊢
        cases sk
        case SkListening =>
          simp only [] at h
          cases hx : conn_ix_exhausted (m_conn_ix m) with
          | true =>
            simp only [hx, ↓reduceIte] at h
            exact absurd h (check_errno_only_no_unmodeled _ _ _)
          | false =>
            simp only [hx, Bool.false_eq_true, ↓reduceIte] at h
            exact absurd h (check_new_fd_result_no_unmodeled _ _ _ _)
        all_goals exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    all_goals exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

/-- Rocq: `Checks.Sys.Net.Socket.check_accept4_complete_ok`.  Every outcome
the spec admits is accepted with the spec's model and events; on the
listening arm the lowest free descriptor is kept out of `accept_errnos` by
`Open.errno_ret_in_alloc_fd`, so the errno side of `check_new_fd_result`
does not swallow it. -/
theorem check_accept4_complete_ok (fd addrp addrlenp flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (h : accept4_spec fd addrp addrlenp flags i m (Ok eff m' evs)) :
    check_accept4 fd addrp addrlenp flags eff m = CheckOk m' evs := by
  unfold accept4_spec at h
  unfold check_accept4
  generalize abi_low32 flags = fl at h ⊢
  have h := bind_model_inv _ i m _ h
  simp only [] at h ⊢
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none =>
    simp only [err_ret, ret_only, pure_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | some e =>
    simp only [] at h ⊢
    by_cases h1 : bv_unsigned (bv_and fl
        (bv_not (bv_or (Z_to_bv 64 SOCK_CLOEXEC) (Z_to_bv 64 SOCK_NONBLOCK)))) = 0
    case neg =>
      simp only [h1, not_false_eq_true, ↓reduceIte, err_ret, ret_only, pure_iff] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    simp only [h1, not_true_eq_false, ↓reduceIte] at h ⊢
    by_cases h2 : bv_unsigned (bv_and fl (Z_to_bv 64 SOCK_NONBLOCK)) = 0
    case neg =>
      simp only [h2, not_false_eq_true, ↓reduceIte] at h
      exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])
    simp only [h2, not_true_eq_false, ↓reduceIte] at h ⊢
    cases e
    case FdSocket sk =>
      simp only [] at h ⊢
      cases ha : w_is0 addrp with
      | false =>
        simp only [ha, Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at h
        exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])
      | true =>
        simp only [ha, not_true_eq_false, ↓reduceIte] at h ⊢
        cases sk
        case SkListening =>
          simp only [] at h ⊢
          cases hx : conn_ix_exhausted (m_conn_ix m) with
          | true =>
            simp only [hx, ↓reduceIte] at h ⊢
            exact check_errno_only_complete_ok _ i _ _ _ _ h
          | false =>
            simp only [hx, Bool.false_eq_true, ↓reduceIte] at h ⊢
            unfold errno_from lowest_fd at h
            rw [alt_iff] at h
            rcases h with h | h
            · rw [bind_choose_iff] at h
              obtain ⟨er, hmem, h⟩ := h
              simp only [err_ret, ret_only, pure_iff] at h
              obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
              simp only [check_new_fd_result, errno_ret_in_intro accept_errnos er hmem, ↓reduceIte]
            · rw [bind_choose_iff] at h
              obtain ⟨nfd, ⟨hnone, hfd'⟩, h⟩ := h
              simp only [bind_modify_iff, ret_only, pure_iff] at h
              obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
              subst hfd'
              simp only [check_new_fd_result, errno_ret_in_alloc_fd _ _ accept_errnos_ok,
                Bool.false_eq_true, ↓reduceIte, hnone, bv_eqb_refl]
        all_goals
          simp only [err_ret, ret_only, pure_iff] at h
          obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
          exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    all_goals
      simp only [err_ret, ret_only, pure_iff] at h
      obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- Rocq: `Checks.Sys.Net.Socket.check_accept4_complete_unmodeled`.  Where
the spec declines, the checker declines whatever effect it is offered; the
listening arm's `alt` has no `Unmodeled` on either counter. -/
theorem check_accept4_complete_unmodeled (fd addrp addrlenp flags : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (h : accept4_spec fd addrp addrlenp flags i m Unmodeled) :
    check_accept4 fd addrp addrlenp flags eff m = CheckUnmodeled := by
  unfold accept4_spec at h
  unfold check_accept4
  generalize abi_low32 flags = fl at h ⊢
  have h := bind_model_inv _ i m _ h
  simp only [] at h ⊢
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
  | some e =>
    simp only [] at h ⊢
    by_cases h1 : bv_unsigned (bv_and fl
        (bv_not (bv_or (Z_to_bv 64 SOCK_CLOEXEC) (Z_to_bv 64 SOCK_NONBLOCK)))) = 0
    case neg =>
      simp only [h1, not_false_eq_true, ↓reduceIte, err_ret, ret_only, pure_iff,
        reduceCtorEq] at h
    simp only [h1, not_true_eq_false, ↓reduceIte] at h ⊢
    by_cases h2 : bv_unsigned (bv_and fl (Z_to_bv 64 SOCK_NONBLOCK)) = 0
    case neg => simp only [h2, not_false_eq_true, ↓reduceIte]
    simp only [h2, not_true_eq_false, ↓reduceIte] at h ⊢
    cases e
    case FdSocket sk =>
      simp only [] at h ⊢
      cases ha : w_is0 addrp with
      | false => simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
      | true =>
        simp only [ha, not_true_eq_false, ↓reduceIte] at h ⊢
        cases sk
        case SkListening =>
          simp only [] at h
          exfalso
          cases hx : conn_ix_exhausted (m_conn_ix m) with
          | true =>
            simp only [hx, ↓reduceIte] at h
            exact errno_only_no_unmodeled _ i m h
          | false =>
            simp only [hx, Bool.false_eq_true, ↓reduceIte] at h
            unfold errno_from lowest_fd at h
            simp only [alt_iff, bind_choose_iff, err_ret, ret_only, pure_iff, bind_modify_iff,
              reduceCtorEq, and_false, exists_false, or_self] at h
        all_goals simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
    all_goals simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h

/-! ## sendto (206), sendmsg (211), recvfrom (207), recvmsg (212)

The I/O group.  The two sends share `check_send_on_socket`, the socket
half, and the two receives share `check_recv_fd_answer`, the descriptor
answer; each shared half carries its own lemmas, so the four callers
apply them rather than reopen them.  The pairs nest their checks in
opposite orders, as the kernel does: `__sys_sendto`
(net/socket.c:2210-2246, Linux v6.18.46) and `__sys_recvfrom`
(net/socket.c:2270-2304, Linux v6.18.46) import the buffer through
`import_ubuf` (lib/iov_iter.c:1433-1442, Linux v6.18.46) before they
resolve the fd, so their fd tests sit inside the range verdict, while
`__sys_sendmsg` (net/socket.c:2700-2718, Linux v6.18.46) and
`__sys_recvmsg` (net/socket.c:2909-2927, Linux v6.18.46) test
`MSG_CMSG_COMPAT` and then resolve the fd before any user memory is read,
so `sendmsg`'s header copy sits inside its fd match.  `sendmsg`'s four
header fields are generalised in the proofs as
the spec's `let`s name them, so one `cases` or `by_cases` on each gate
drives both sides. -/

set_option linter.unusedVariables false in
/-- The socket half both sends share, as an acceptor of `send_on_socket`:
`SendDead`'s -EPIPE with `pre` as the whole ledger, and a decline on the
two connected states, where Rocq's checker delivers a prefix (0 on a
zero-length request, -EFAULT when nothing is readable) or answers and
consumes the pending error (this file's header gives the departure, the
spec's section header the reason).  The -EPIPE is
`sk_stream_wait_connect`'s (net/core/stream.c:60-87, Linux v6.18.46),
which `tcp_sendmsg_locked` calls (net/ipv4/tcp.c:1159-1164, Linux
v6.18.46) for a socket neither established nor in CLOSE_WAIT (nor a
passive Fast Open one) before its copy loop begins (:1197), so no payload
range joins `pre`: every `SendDead` state is such a socket.  `acc`,
`fd`, `total` and `bs` are kept, unread, so the signature stays Rocq's.
Rocq: `Checks.Sys.Net.Socket.check_send_on_socket`. -/
def check_send_on_socket (pre : List (word × Nat)) (acc : Nat → List (word × Nat))
    (fd : word) (sk : SockState) (total : word) (bs : List byte) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match send_state sk with
  | .SendDead => check_ret_only_copyins pre eff (errno_ret EPIPE) m []
  | .SendErr _ _ _ => CheckUnmodeled
  | .SendGoes _ => CheckUnmodeled

/-- `sendto`: the three gates, then `import_ubuf`'s range verdict, then
the fd — and the fd match stays INSIDE `check_access_ok_zero`, because
that nesting is what makes `sendto(-1, unmapped, n, ...)` -EFAULT rather
than -EBADF.  `addrlen` is not a parameter here: the spec never reads it.
Rocq: `Checks.Sys.Net.Socket.check_sendto`. -/
def check_sendto (i : SyscallInput) (fd buf count flags addrp : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if ¬ (send_flags_modeled flags) then CheckUnmodeled
  else if ¬ (w_is0 addrp) then CheckUnmodeled
  else if ¬ (Sys.Uaccess.modeled_rw_count count) then CheckUnmodeled
  else
    check_access_ok_zero buf count eff m
      (match fd_lookup (m_fds m) fd with
       | none => check_ret_only eff (errno_ret EBADF) m []
       | some (.FdSocket sk) =>
           check_send_on_socket [] (fun n => [(buf, n)]) fd sk count
             (readable_bytes i.in_mem buf count) eff m
       | some _ => check_ret_only eff (errno_ret ENOTSOCK) m [])

/-- The checker for `sendmsg_spec`, arm for arm: the fd before the
header, the opposite nesting to `check_sendto` and deliberately not
shared with it.  Each arm spells out the ledger it expects where it
answers — the header alone at -EMSGSIZE, the header and
`copy_iovecs_accesses` at the import's -EFAULT and -EINVAL and as the
socket half's `pre` — so a reader sees at each answer which user bytes
had been read by then.  The four header fields are the spec's, decoded
from the 56 bytes `read_bytes_map` returned, where Rocq's checker reads
six with `read_u64` (this file's header).
Rocq: `Checks.Sys.Net.Socket.check_sendmsg`. -/
def check_sendmsg (i : SyscallInput) (fd msgp flags : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if ¬ (send_flags_modeled flags) then CheckUnmodeled
  else
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdChannel _) | some (.FdFile _ _)
  | some (.FdFileW _ _) | some (.FdFileA _ _) | some (.FdFileRW _ _)
  | some .FdDir
  | some (.FdPipe _ _)
  | some (.FdDevNull _ _)
  | some .FdUrandom => check_ret_only eff (errno_ret ENOTSOCK) m []
  | some (.FdSocket sk) =>
      match read_bytes_map i.in_mem msgp (Z_to_bv 64 MSGHDR_SIZE) with
      | none => check_ret_only eff (errno_ret EFAULT) m []
      | some hdr =>
          let name := le_bytes_to_word (hdr.take 8)
          let iov := le_bytes_to_word ((hdr.drop 16).take 8)
          let iovlen := le_bytes_to_word ((hdr.drop 24).take 8)
          let ctllen := le_bytes_to_word ((hdr.drop 40).take 8)
          if ¬ (w_is0 name) then CheckUnmodeled
          else if IOV_MAX < bv_unsigned iovlen
          then check_ret_only_copyins [(msgp, MSGHDR_SIZE.toNat)] eff (errno_ret EMSGSIZE) m []
          else if Sys.Fs.ReadWrite.UIO_FASTIOV < bv_unsigned iovlen then CheckUnmodeled
          else
            match copy_iovecs_aux i.in_mem iov (word_to_nat iovlen) with
            | .ImpFault =>
                check_ret_only_copyins ([(msgp, MSGHDR_SIZE.toNat)]
                                        ++ copy_iovecs_accesses i.in_mem iov (word_to_nat iovlen))
                  eff (errno_ret EFAULT) m []
            | .ImpInval =>
                check_ret_only_copyins ([(msgp, MSGHDR_SIZE.toNat)]
                                        ++ copy_iovecs_accesses i.in_mem iov (word_to_nat iovlen))
                  eff (errno_ret EINVAL) m []
            | .ImpOk iovs0 =>
                if ¬ (w_is0 ctllen) then CheckUnmodeled
                else if ¬ (iovs_total (cap_iovecs iovs0) ≤ Sys.Uaccess.rw_bytes_max)
                then CheckUnmodeled
                else
                  check_send_on_socket
                    ([(msgp, MSGHDR_SIZE.toNat)]
                     ++ copy_iovecs_accesses i.in_mem iov (word_to_nat iovlen))
                    (fun n => iov_prefix_accesses (cap_iovecs iovs0) n) fd sk
                    (Z_to_bv 64 (iovs_total (cap_iovecs iovs0)))
                    (writev_gathered i.in_mem iovs0) eff m

/-- Rocq: `Checks.Sys.Net.Socket.check_send_on_socket_sound_ok`.  Only
`SendDead` accepts, and its acceptor is the spec's `record_copyins pre`
over `err_ret EPIPE`. -/
theorem check_send_on_socket_sound_ok (pre : List (word × Nat))
    (acc : Nat → List (word × Nat)) (fd : word) (sk : SockState) (total : word)
    (bs : List byte) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput)
    (h : check_send_on_socket pre acc fd sk total bs eff m = CheckOk m' evs) :
    send_on_socket pre acc fd sk total bs m i m (Ok eff m' evs) := by
  unfold check_send_on_socket at h
  unfold send_on_socket
  generalize send_state sk = s at h ⊢
  cases s with
  | SendDead =>
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
    exact record_copyins_ok_empty _ _ i _ _ _ _ rfl (pure_ok _ i _)
  | SendErr _ _ _ => simp only [reduceCtorEq] at h
  | SendGoes _ => simp only [reduceCtorEq] at h

/-- Where Rocq has `check_send_on_socket_no_unmodeled`, false here (this
file's header): the checker declines on the two connected states, and so
does the spec.  Lean-only. -/
theorem check_send_on_socket_sound_unmodeled (pre : List (word × Nat))
    (acc : Nat → List (word × Nat)) (fd : word) (sk : SockState) (total : word)
    (bs : List byte) (eff : SyscallEffect) (m : Model) (i : SyscallInput)
    (h : check_send_on_socket pre acc fd sk total bs eff m = CheckUnmodeled) :
    send_on_socket pre acc fd sk total bs m i m Unmodeled := by
  unfold check_send_on_socket at h
  unfold send_on_socket
  generalize send_state sk = s at h ⊢
  cases s with
  | SendDead => exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)
  | SendErr _ _ _ => exact unmodeled_intro i m
  | SendGoes _ => exact unmodeled_intro i m

/-- Rocq: `Checks.Sys.Net.Socket.check_send_on_socket_complete_ok`.  The
spec's one `Ok` is `SendDead`'s, whose ledger is `pre` followed by
`err_ret`'s empty one. -/
theorem check_send_on_socket_complete_ok (pre : List (word × Nat))
    (acc : Nat → List (word × Nat)) (fd : word) (sk : SockState) (total : word)
    (bs : List byte) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput)
    (h : send_on_socket pre acc fd sk total bs m i m (Ok eff m' evs)) :
    check_send_on_socket pre acc fd sk total bs eff m = CheckOk m' evs := by
  unfold send_on_socket at h
  unfold check_send_on_socket
  generalize send_state sk = s at h ⊢
  cases s with
  | SendDead =>
    simp only [] at h ⊢
    obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
    simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at hcore
    obtain ⟨rfl, rfl, rfl⟩ := hcore
    simp only [mkEffect, List.append_nil]
    exact check_ret_only_copyins_refl _ _ _ _
  | SendErr _ _ _ => simp only [unmodeled_iff, reduceCtorEq] at h
  | SendGoes _ => simp only [unmodeled_iff, reduceCtorEq] at h

/-- The converse of `check_send_on_socket_sound_unmodeled`: a spec
decline is a checker decline, `SendDead`'s `record_copyins` over a
`pure` never declining.  Lean-only, for the reason that lemma gives. -/
theorem check_send_on_socket_complete_unmodeled (pre : List (word × Nat))
    (acc : Nat → List (word × Nat)) (fd : word) (sk : SockState) (total : word)
    (bs : List byte) (m : Model) (i : SyscallInput) (eff : SyscallEffect)
    (h : send_on_socket pre acc fd sk total bs m i m Unmodeled) :
    check_send_on_socket pre acc fd sk total bs eff m = CheckUnmodeled := by
  unfold send_on_socket at h
  unfold check_send_on_socket
  generalize send_state sk = s at h ⊢
  cases s with
  | SendDead =>
    simp only [] at h
    have h := record_copyins_unmodeled_inv _ _ i m h
    simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
  | SendErr _ _ _ => rfl
  | SendGoes _ => rfl

/-- Rocq: `Checks.Sys.Net.Socket.check_sendto_sound_ok`.  The gates
split on the same `Bool`s on both sides, `ok_zero_cases` opens the range
verdict, and the socket arm is `check_send_on_socket_sound_ok`. -/
theorem check_sendto_sound_ok (i : SyscallInput) (fd buf count flags addrp addrlen : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_sendto i fd buf count flags addrp eff m = CheckOk m' evs) :
    sendto_spec fd buf count flags addrp addrlen i m (Ok eff m' evs) := by
  unfold check_sendto at h
  unfold sendto_spec
  cases hf : send_flags_modeled flags with
  | false => simp only [hf, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, reduceCtorEq] at h
  | true =>
    simp only [hf, not_true_eq_false, ↓reduceIte] at h ⊢
    cases ha : w_is0 addrp with
    | false => simp only [ha, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, reduceCtorEq] at h
    | true =>
      simp only [ha, not_true_eq_false, ↓reduceIte] at h ⊢
      cases hc : Sys.Uaccess.modeled_rw_count count with
      | false =>
        simp only [hc, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, reduceCtorEq] at h
      | true =>
        simp only [hc, not_true_eq_false, ↓reduceIte] at h ⊢
        apply bind_ok0 _ _ i m i m _ _ _ (input_ok i m)
        apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
        ok_zero_cases h buf count
        · obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
          exact pure_ok _ i _
        · generalize fd_lookup (m_fds m) fd = r at h ⊢
          cases r with
          | none =>
            obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
            exact pure_ok _ i _
          | some e =>
            cases e
            case FdSocket sk => exact check_send_on_socket_sound_ok _ _ _ _ _ _ _ _ _ _ i h
            all_goals
              obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
              exact pure_ok _ i _

/-- Rocq: `Checks.Sys.Net.Socket.check_sendto_sound_unmodeled`.  A
decline is a gate's or the socket half's; every other leaf is an
acceptor, which never declines. -/
theorem check_sendto_sound_unmodeled (i : SyscallInput) (fd buf count flags addrp addrlen : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_sendto i fd buf count flags addrp eff m = CheckUnmodeled) :
    sendto_spec fd buf count flags addrp addrlen i m Unmodeled := by
  unfold check_sendto at h
  unfold sendto_spec
  cases hf : send_flags_modeled flags with
  | false =>
    simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
    simp only [hf, not_true_eq_false, ↓reduceIte] at h ⊢
    cases ha : w_is0 addrp with
    | false =>
      simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
      exact unmodeled_intro i m
    | true =>
      simp only [ha, not_true_eq_false, ↓reduceIte] at h ⊢
      cases hc : Sys.Uaccess.modeled_rw_count count with
      | false =>
        simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
        exact unmodeled_intro i m
      | true =>
        simp only [hc, not_true_eq_false, ↓reduceIte] at h ⊢
        apply bind_unmodeled2 _ _ i m i m [] (input_ok i m)
        apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
        ok_zero_cases h buf count
        · exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
        · generalize fd_lookup (m_fds m) fd = r at h ⊢
          cases r with
          | none => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
          | some e =>
            cases e
            case FdSocket sk => exact check_send_on_socket_sound_unmodeled _ _ _ _ _ _ _ _ i h
            all_goals exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

/-- Rocq: `Checks.Sys.Net.Socket.check_sendto_complete_ok`.  Rocq's proof
splits the range verdict with `ok_zero_split`; this one writes the split
out, one `generalize` of `access_okb` across the spec hypothesis and the
checker goal. -/
theorem check_sendto_complete_ok (i : SyscallInput) (fd buf count flags addrp addrlen : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : sendto_spec fd buf count flags addrp addrlen i m (Ok eff m' evs)) :
    check_sendto i fd buf count flags addrp eff m = CheckOk m' evs := by
  unfold sendto_spec at h
  unfold check_sendto
  cases hf : send_flags_modeled flags with
  | false =>
    simp only [hf, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, unmodeled_iff,
      reduceCtorEq] at h
  | true =>
    simp only [hf, not_true_eq_false, ↓reduceIte] at h ⊢
    cases ha : w_is0 addrp with
    | false =>
      simp only [ha, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, unmodeled_iff,
        reduceCtorEq] at h
    | true =>
      simp only [ha, not_true_eq_false, ↓reduceIte] at h ⊢
      cases hc : Sys.Uaccess.modeled_rw_count count with
      | false =>
        simp only [hc, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, unmodeled_iff,
          reduceCtorEq] at h
      | true =>
        simp only [hc, not_true_eq_false, ↓reduceIte] at h ⊢
        have h := bind_input_model_inv _ i m _ h
        unfold access_ok_zero at h
        unfold check_access_ok_zero
        generalize access_okb buf (bv_unsigned count) = ok at h ⊢
        cases ok with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
        | true =>
          simp only [↓reduceIte] at h ⊢
          generalize fd_lookup (m_fds m) fd = r at h ⊢
          cases r with
          | none =>
            simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
          | some e =>
            cases e
            case FdSocket sk => exact check_send_on_socket_complete_ok _ _ _ _ _ _ _ _ _ _ i h
            all_goals
              simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- Rocq: `Checks.Sys.Net.Socket.check_sendto_complete_unmodeled`. -/
theorem check_sendto_complete_unmodeled (i : SyscallInput)
    (fd buf count flags addrp addrlen : word) (m : Model) (eff : SyscallEffect)
    (h : sendto_spec fd buf count flags addrp addrlen i m Unmodeled) :
    check_sendto i fd buf count flags addrp eff m = CheckUnmodeled := by
  unfold sendto_spec at h
  unfold check_sendto
  cases hf : send_flags_modeled flags with
  | false => simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
  | true =>
    simp only [hf, not_true_eq_false, ↓reduceIte] at h ⊢
    cases ha : w_is0 addrp with
    | false => simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
    | true =>
      simp only [ha, not_true_eq_false, ↓reduceIte] at h ⊢
      cases hc : Sys.Uaccess.modeled_rw_count count with
      | false => simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
      | true =>
        simp only [hc, not_true_eq_false, ↓reduceIte] at h ⊢
        have h := bind_input_model_inv _ i m _ h
        unfold access_ok_zero at h
        unfold check_access_ok_zero
        generalize access_okb buf (bv_unsigned count) = ok at h ⊢
        cases ok with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, err_ret, ret_only, pure_iff,
            reduceCtorEq] at h
        | true =>
          simp only [↓reduceIte] at h ⊢
          generalize fd_lookup (m_fds m) fd = r at h ⊢
          cases r with
          | none => simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
          | some e =>
            cases e
            case FdSocket sk =>
              exact check_send_on_socket_complete_unmodeled _ _ _ _ _ _ _ i _ h
            all_goals simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h

/-- Rocq: `Checks.Sys.Net.Socket.check_sendmsg_sound_ok`.  Every gate is
split once, on the term both sides spell, and each ledger leaf is the
spec's `record_copyins` over a `pure`. -/
theorem check_sendmsg_sound_ok (i : SyscallInput) (fd msgp flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_sendmsg i fd msgp flags eff m = CheckOk m' evs) :
    sendmsg_spec fd msgp flags i m (Ok eff m' evs) := by
  unfold check_sendmsg at h
  unfold sendmsg_spec
  cases hf : send_flags_modeled flags with
  | false => simp only [hf, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, reduceCtorEq] at h
  | true =>
    simp only [hf, not_true_eq_false, ↓reduceIte] at h ⊢
    apply bind_ok0 _ _ i m i m _ _ _ (input_ok i m)
    apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
    generalize fd_lookup (m_fds m) fd = r at h ⊢
    cases r with
    | none =>
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _
    | some e =>
      cases e
      case FdSocket sk =>
        simp only [] at h ⊢
        generalize read_bytes_map i.in_mem msgp (Z_to_bv 64 MSGHDR_SIZE) = rh at h ⊢
        cases rh with
        | none =>
          obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
          exact pure_ok _ i _
        | some hdr =>
          simp only [] at h ⊢
          generalize le_bytes_to_word (List.take 8 hdr) = name at h ⊢
          generalize le_bytes_to_word (List.take 8 (List.drop 16 hdr)) = iov at h ⊢
          generalize le_bytes_to_word (List.take 8 (List.drop 24 hdr)) = iovlen at h ⊢
          generalize le_bytes_to_word (List.take 8 (List.drop 40 hdr)) = ctllen at h ⊢
          cases hn : w_is0 name with
          | false =>
            simp only [hn, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, reduceCtorEq] at h
          | true =>
            simp only [hn, not_true_eq_false, ↓reduceIte] at h ⊢
            by_cases hiv : IOV_MAX < bv_unsigned iovlen
            · simp only [hiv, ↓reduceIte] at h ⊢
              obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
              exact record_copyins_ok_empty _ _ i _ _ _ _ rfl (pure_ok _ i _)
            · simp only [hiv, ↓reduceIte] at h ⊢
              by_cases hfa : Sys.Fs.ReadWrite.UIO_FASTIOV < bv_unsigned iovlen
              · simp only [hfa, ↓reduceIte, reduceCtorEq] at h
              · simp only [hfa, ↓reduceIte] at h ⊢
                generalize copy_iovecs_aux i.in_mem iov (word_to_nat iovlen) = ri at h ⊢
                cases ri with
                | ImpFault =>
                  simp only [] at h ⊢
                  obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
                  exact record_copyins_ok_empty _ _ i _ _ _ _ rfl (pure_ok _ i _)
                | ImpInval =>
                  simp only [] at h ⊢
                  obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
                  exact record_copyins_ok_empty _ _ i _ _ _ _ rfl (pure_ok _ i _)
                | ImpOk iovs0 =>
                  simp only [] at h ⊢
                  cases hc : w_is0 ctllen with
                  | false =>
                    simp only [hc, Bool.false_eq_true, not_false_eq_true, ↓reduceIte,
                      reduceCtorEq] at h
                  | true =>
                    simp only [hc, not_true_eq_false, ↓reduceIte] at h ⊢
                    by_cases ht : iovs_total (cap_iovecs iovs0) ≤ Sys.Uaccess.rw_bytes_max
                    · simp only [ht, not_true_eq_false, ↓reduceIte] at h ⊢
                      exact check_send_on_socket_sound_ok _ _ _ _ _ _ _ _ _ _ i h
                    · simp only [ht, not_false_eq_true, ↓reduceIte, reduceCtorEq] at h
      all_goals
        obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
        exact pure_ok _ i _

/-- Rocq: `Checks.Sys.Net.Socket.check_sendmsg_sound_unmodeled`. -/
theorem check_sendmsg_sound_unmodeled (i : SyscallInput) (fd msgp flags : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_sendmsg i fd msgp flags eff m = CheckUnmodeled) :
    sendmsg_spec fd msgp flags i m Unmodeled := by
  unfold check_sendmsg at h
  unfold sendmsg_spec
  cases hf : send_flags_modeled flags with
  | false =>
    simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
    simp only [hf, not_true_eq_false, ↓reduceIte] at h ⊢
    apply bind_unmodeled2 _ _ i m i m [] (input_ok i m)
    apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
    generalize fd_lookup (m_fds m) fd = r at h ⊢
    cases r with
    | none => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | some e =>
      cases e
      case FdSocket sk =>
        simp only [] at h ⊢
        generalize read_bytes_map i.in_mem msgp (Z_to_bv 64 MSGHDR_SIZE) = rh at h ⊢
        cases rh with
        | none => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
        | some hdr =>
          simp only [] at h ⊢
          generalize le_bytes_to_word (List.take 8 hdr) = name at h ⊢
          generalize le_bytes_to_word (List.take 8 (List.drop 16 hdr)) = iov at h ⊢
          generalize le_bytes_to_word (List.take 8 (List.drop 24 hdr)) = iovlen at h ⊢
          generalize le_bytes_to_word (List.take 8 (List.drop 40 hdr)) = ctllen at h ⊢
          cases hn : w_is0 name with
          | false =>
            simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
            exact unmodeled_intro i m
          | true =>
            simp only [hn, not_true_eq_false, ↓reduceIte] at h ⊢
            by_cases hiv : IOV_MAX < bv_unsigned iovlen
            · simp only [hiv, ↓reduceIte] at h
              exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)
            · simp only [hiv, ↓reduceIte] at h ⊢
              by_cases hfa : Sys.Fs.ReadWrite.UIO_FASTIOV < bv_unsigned iovlen
              · simp only [hfa, ↓reduceIte]
                exact unmodeled_intro i m
              · simp only [hfa, ↓reduceIte] at h ⊢
                generalize copy_iovecs_aux i.in_mem iov (word_to_nat iovlen) = ri at h ⊢
                cases ri with
                | ImpFault =>
                  simp only [] at h
                  exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)
                | ImpInval =>
                  simp only [] at h
                  exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)
                | ImpOk iovs0 =>
                  simp only [] at h ⊢
                  cases hc : w_is0 ctllen with
                  | false =>
                    simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
                    exact unmodeled_intro i m
                  | true =>
                    simp only [hc, not_true_eq_false, ↓reduceIte] at h ⊢
                    by_cases ht : iovs_total (cap_iovecs iovs0) ≤ Sys.Uaccess.rw_bytes_max
                    · simp only [ht, not_true_eq_false, ↓reduceIte] at h ⊢
                      exact check_send_on_socket_sound_unmodeled _ _ _ _ _ _ _ _ i h
                    · simp only [ht, not_false_eq_true, ↓reduceIte]
                      exact unmodeled_intro i m
      all_goals exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

/-- Rocq: `Checks.Sys.Net.Socket.check_sendmsg_complete_ok`.  Each
ledger leaf inverts `record_copyins` and hands the checker the ledger
the spec built — the header alone at -EMSGSIZE, the header and
`copy_iovecs_accesses` after the import — in front of `err_ret`'s
empty one. -/
theorem check_sendmsg_complete_ok (i : SyscallInput) (fd msgp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : sendmsg_spec fd msgp flags i m (Ok eff m' evs)) :
    check_sendmsg i fd msgp flags eff m = CheckOk m' evs := by
  unfold sendmsg_spec at h
  unfold check_sendmsg
  cases hf : send_flags_modeled flags with
  | false =>
    simp only [hf, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, unmodeled_iff,
      reduceCtorEq] at h
  | true =>
    simp only [hf, not_true_eq_false, ↓reduceIte] at h ⊢
    have h := bind_input_model_inv _ i m _ h
    generalize fd_lookup (m_fds m) fd = r at h ⊢
    cases r with
    | none =>
      simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    | some e =>
      cases e
      case FdSocket sk =>
        simp only [] at h ⊢
        generalize read_bytes_map i.in_mem msgp (Z_to_bv 64 MSGHDR_SIZE) = rh at h ⊢
        cases rh with
        | none =>
          simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
        | some hdr =>
          simp only [] at h ⊢
          generalize le_bytes_to_word (List.take 8 hdr) = name at h ⊢
          generalize le_bytes_to_word (List.take 8 (List.drop 16 hdr)) = iov at h ⊢
          generalize le_bytes_to_word (List.take 8 (List.drop 24 hdr)) = iovlen at h ⊢
          generalize le_bytes_to_word (List.take 8 (List.drop 40 hdr)) = ctllen at h ⊢
          cases hn : w_is0 name with
          | false =>
            simp only [hn, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, unmodeled_iff,
              reduceCtorEq] at h
          | true =>
            simp only [hn, not_true_eq_false, ↓reduceIte] at h ⊢
            by_cases hiv : IOV_MAX < bv_unsigned iovlen
            · simp only [hiv, ↓reduceIte] at h ⊢
              obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
              simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at hcore
              obtain ⟨rfl, rfl, rfl⟩ := hcore
              simp only [mkEffect, List.append_nil]
              exact check_ret_only_copyins_refl _ _ _ _
            · simp only [hiv, ↓reduceIte] at h ⊢
              by_cases hfa : Sys.Fs.ReadWrite.UIO_FASTIOV < bv_unsigned iovlen
              · simp only [hfa, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h
              · simp only [hfa, ↓reduceIte] at h ⊢
                generalize copy_iovecs_aux i.in_mem iov (word_to_nat iovlen) = ri at h ⊢
                cases ri with
                | ImpFault =>
                  simp only [] at h ⊢
                  obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
                  simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at hcore
                  obtain ⟨rfl, rfl, rfl⟩ := hcore
                  simp only [mkEffect, List.append_nil]
                  exact check_ret_only_copyins_refl _ _ _ _
                | ImpInval =>
                  simp only [] at h ⊢
                  obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
                  simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at hcore
                  obtain ⟨rfl, rfl, rfl⟩ := hcore
                  simp only [mkEffect, List.append_nil]
                  exact check_ret_only_copyins_refl _ _ _ _
                | ImpOk iovs0 =>
                  simp only [] at h ⊢
                  cases hc : w_is0 ctllen with
                  | false =>
                    simp only [hc, Bool.false_eq_true, not_false_eq_true, ↓reduceIte,
                      unmodeled_iff, reduceCtorEq] at h
                  | true =>
                    simp only [hc, not_true_eq_false, ↓reduceIte] at h ⊢
                    by_cases ht : iovs_total (cap_iovecs iovs0) ≤ Sys.Uaccess.rw_bytes_max
                    · simp only [ht, not_true_eq_false, ↓reduceIte] at h ⊢
                      exact check_send_on_socket_complete_ok _ _ _ _ _ _ _ _ _ _ i h
                    · simp only [ht, not_false_eq_true, ↓reduceIte, unmodeled_iff,
                        reduceCtorEq] at h
      all_goals
        simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- Rocq: `Checks.Sys.Net.Socket.check_sendmsg_complete_unmodeled`. -/
theorem check_sendmsg_complete_unmodeled (i : SyscallInput) (fd msgp flags : word)
    (m : Model) (eff : SyscallEffect) (h : sendmsg_spec fd msgp flags i m Unmodeled) :
    check_sendmsg i fd msgp flags eff m = CheckUnmodeled := by
  unfold sendmsg_spec at h
  unfold check_sendmsg
  cases hf : send_flags_modeled flags with
  | false => simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
  | true =>
    simp only [hf, not_true_eq_false, ↓reduceIte] at h ⊢
    have h := bind_input_model_inv _ i m _ h
    generalize fd_lookup (m_fds m) fd = r at h ⊢
    cases r with
    | none => simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
    | some e =>
      cases e
      case FdSocket sk =>
        simp only [] at h ⊢
        generalize read_bytes_map i.in_mem msgp (Z_to_bv 64 MSGHDR_SIZE) = rh at h ⊢
        cases rh with
        | none => simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
        | some hdr =>
          simp only [] at h ⊢
          generalize le_bytes_to_word (List.take 8 hdr) = name at h ⊢
          generalize le_bytes_to_word (List.take 8 (List.drop 16 hdr)) = iov at h ⊢
          generalize le_bytes_to_word (List.take 8 (List.drop 24 hdr)) = iovlen at h ⊢
          generalize le_bytes_to_word (List.take 8 (List.drop 40 hdr)) = ctllen at h ⊢
          cases hn : w_is0 name with
          | false => simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
          | true =>
            simp only [hn, not_true_eq_false, ↓reduceIte] at h ⊢
            by_cases hiv : IOV_MAX < bv_unsigned iovlen
            · simp only [hiv, ↓reduceIte] at h
              have h := record_copyins_unmodeled_inv _ _ i m h
              simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
            · simp only [hiv, ↓reduceIte] at h ⊢
              by_cases hfa : Sys.Fs.ReadWrite.UIO_FASTIOV < bv_unsigned iovlen
              · simp only [hfa, ↓reduceIte]
              · simp only [hfa, ↓reduceIte] at h ⊢
                generalize copy_iovecs_aux i.in_mem iov (word_to_nat iovlen) = ri at h ⊢
                cases ri with
                | ImpFault =>
                  simp only [] at h
                  have h := record_copyins_unmodeled_inv _ _ i m h
                  simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
                | ImpInval =>
                  simp only [] at h
                  have h := record_copyins_unmodeled_inv _ _ i m h
                  simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
                | ImpOk iovs0 =>
                  simp only [] at h ⊢
                  cases hc : w_is0 ctllen with
                  | false => simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
                  | true =>
                    simp only [hc, not_true_eq_false, ↓reduceIte] at h ⊢
                    by_cases ht : iovs_total (cap_iovecs iovs0) ≤ Sys.Uaccess.rw_bytes_max
                    · simp only [ht, not_true_eq_false, ↓reduceIte] at h ⊢
                      exact check_send_on_socket_complete_unmodeled _ _ _ _ _ _ _ i _ h
                    · simp only [ht, not_false_eq_true, ↓reduceIte]
      all_goals simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h

/-- `recv_fd_answer` as an acceptor: the errno `sockfd_lookup_errno`
gives, or the decline a socket takes at these two entry points, as a
whole branch on both sides — which is what keeps the four directions
below exact.  Rocq: `Checks.Sys.Net.Socket.check_recv_fd_answer`. -/
def check_recv_fd_answer (fds : List (word × FdEntry)) (fd : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match sockfd_lookup_errno fds fd with
  | some e => check_ret_only eff (errno_ret e) m []
  | none => CheckUnmodeled

/-- Rocq: `Checks.Sys.Net.Socket.check_recv_fd_answer_sound_ok`. -/
theorem check_recv_fd_answer_sound_ok (fds : List (word × FdEntry)) (fd : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event) (i : SyscallInput)
    (h : check_recv_fd_answer fds fd eff m = CheckOk m' evs) :
    recv_fd_answer fds fd i m (Ok eff m' evs) := by
  unfold check_recv_fd_answer at h
  unfold recv_fd_answer
  generalize sockfd_lookup_errno fds fd = r at h ⊢
  cases r with
  | some e =>
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | none => simp only [reduceCtorEq] at h

/-- Rocq: `Checks.Sys.Net.Socket.check_recv_fd_answer_complete_ok`. -/
theorem check_recv_fd_answer_complete_ok (fds : List (word × FdEntry)) (fd : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event) (i : SyscallInput)
    (h : recv_fd_answer fds fd i m (Ok eff m' evs)) :
    check_recv_fd_answer fds fd eff m = CheckOk m' evs := by
  unfold recv_fd_answer at h
  unfold check_recv_fd_answer
  generalize sockfd_lookup_errno fds fd = r at h ⊢
  cases r with
  | some e =>
    simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | none => simp only [unmodeled_iff, reduceCtorEq] at h

/-- Rocq: `Checks.Sys.Net.Socket.check_recv_fd_answer_complete_unmodeled`. -/
theorem check_recv_fd_answer_complete_unmodeled (fds : List (word × FdEntry)) (fd : word)
    (eff : SyscallEffect) (m : Model) (i : SyscallInput)
    (h : recv_fd_answer fds fd i m Unmodeled) :
    check_recv_fd_answer fds fd eff m = CheckUnmodeled := by
  unfold recv_fd_answer at h
  unfold check_recv_fd_answer
  generalize sockfd_lookup_errno fds fd = r at h ⊢
  cases r with
  | some _ => simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
  | none => rfl

/-- Rocq: `Checks.Sys.Net.Socket.check_recv_fd_answer_no_ok_unmodeled`: a
checker decline is the spec's, the socket arm on both sides. -/
theorem check_recv_fd_answer_no_ok_unmodeled (fds : List (word × FdEntry)) (fd : word)
    (eff : SyscallEffect) (m : Model) (i : SyscallInput)
    (h : check_recv_fd_answer fds fd eff m = CheckUnmodeled) :
    recv_fd_answer fds fd i m Unmodeled := by
  unfold check_recv_fd_answer at h
  unfold recv_fd_answer
  generalize sockfd_lookup_errno fds fd = r at h ⊢
  cases r with
  | some _ => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | none => exact unmodeled_intro i m

set_option linter.unusedVariables false in
/-- The checker for `recvfrom_spec`: the count's bound, then the range
verdict, then the descriptor answer — the buffer before the fd, as
`import_ubuf` runs first.  No byte moves on any arm, so
`check_access_ok_zero` is the whole of the buffer's test.  `i` is kept,
unread, so the signature stays Rocq's; the twin does not bind the input.
Rocq: `Checks.Sys.Net.Socket.check_recvfrom`. -/
def check_recvfrom (i : SyscallInput) (fd buf size : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if ¬ (Sys.Uaccess.modeled_rw_count size) then CheckUnmodeled
  else check_access_ok_zero buf size eff m (check_recv_fd_answer (m_fds m) fd eff m)

/-- Rocq: `Checks.Sys.Net.Socket.check_recvfrom_sound_ok`.  One reader is
peeled where Rocq peels two (this file's header). -/
theorem check_recvfrom_sound_ok (i : SyscallInput) (fd buf size : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_recvfrom i fd buf size eff m = CheckOk m' evs) :
    recvfrom_spec fd buf size i m (Ok eff m' evs) := by
  unfold check_recvfrom at h
  unfold recvfrom_spec
  cases hc : Sys.Uaccess.modeled_rw_count size with
  | false => simp only [hc, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, reduceCtorEq] at h
  | true =>
    simp only [hc, not_true_eq_false, ↓reduceIte] at h ⊢
    apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
    ok_zero_cases h buf size
    · obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _
    · exact check_recv_fd_answer_sound_ok _ _ _ _ _ _ i h

/-- Rocq: `Checks.Sys.Net.Socket.check_recvfrom_sound_unmodeled`. -/
theorem check_recvfrom_sound_unmodeled (i : SyscallInput) (fd buf size : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_recvfrom i fd buf size eff m = CheckUnmodeled) :
    recvfrom_spec fd buf size i m Unmodeled := by
  unfold check_recvfrom at h
  unfold recvfrom_spec
  cases hc : Sys.Uaccess.modeled_rw_count size with
  | false =>
    simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
    simp only [hc, not_true_eq_false, ↓reduceIte] at h ⊢
    apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
    ok_zero_cases h buf size
    · exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    · exact check_recv_fd_answer_no_ok_unmodeled _ _ _ _ i h

/-- Rocq: `Checks.Sys.Net.Socket.check_recvfrom_complete_ok`. -/
theorem check_recvfrom_complete_ok (i : SyscallInput) (fd buf size : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : recvfrom_spec fd buf size i m (Ok eff m' evs)) :
    check_recvfrom i fd buf size eff m = CheckOk m' evs := by
  unfold recvfrom_spec at h
  unfold check_recvfrom
  cases hc : Sys.Uaccess.modeled_rw_count size with
  | false =>
    simp only [hc, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, unmodeled_iff,
      reduceCtorEq] at h
  | true =>
    simp only [hc, not_true_eq_false, ↓reduceIte] at h ⊢
    have h := bind_model_inv _ i m _ h
    unfold access_ok_zero at h
    unfold check_access_ok_zero
    generalize access_okb buf (bv_unsigned size) = ok at h ⊢
    cases ok with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact check_recv_fd_answer_complete_ok _ _ _ _ _ _ i h

/-- Rocq: `Checks.Sys.Net.Socket.check_recvfrom_complete_unmodeled`. -/
theorem check_recvfrom_complete_unmodeled (i : SyscallInput) (fd buf size : word) (m : Model)
    (eff : SyscallEffect) (h : recvfrom_spec fd buf size i m Unmodeled) :
    check_recvfrom i fd buf size eff m = CheckUnmodeled := by
  unfold recvfrom_spec at h
  unfold check_recvfrom
  cases hc : Sys.Uaccess.modeled_rw_count size with
  | false => simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
  | true =>
    simp only [hc, not_true_eq_false, ↓reduceIte] at h ⊢
    have h := bind_model_inv _ i m _ h
    unfold access_ok_zero at h
    unfold check_access_ok_zero
    generalize access_okb buf (bv_unsigned size) = ok at h ⊢
    cases ok with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, err_ret, ret_only, pure_iff,
        reduceCtorEq] at h
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact check_recv_fd_answer_complete_unmodeled _ _ _ _ i h

/-- The checker for `recvmsg_spec`: MSG_CMSG_COMPAT declines, its value
being a kernel configuration fact, and otherwise the descriptor alone
decides, because `__sys_recvmsg` resolves the fd before
`___sys_recvmsg` copies the header — so the header is never read and
`msg` is not a parameter.  The flag test is on the word, as the spec
spells it (this file's SPELLINGS).
Rocq: `Checks.Sys.Net.Socket.check_recvmsg`. -/
def check_recvmsg (fd flags : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if ¬ (bv_unsigned (bv_and (abi_low32 flags) (Z_to_bv 64 MSG_CMSG_COMPAT)) = 0)
  then CheckUnmodeled
  else check_recv_fd_answer (m_fds m) fd eff m

/-- Rocq: `Checks.Sys.Net.Socket.check_recvmsg_sound_ok`.  The flag test
is generalised whole, as the file header's bind note records for
`sint32`, so no `Z_to_bv` of the compat bit is ever reduced. -/
theorem check_recvmsg_sound_ok (fd flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput) (h : check_recvmsg fd flags eff m = CheckOk m' evs) :
    recvmsg_spec fd flags i m (Ok eff m' evs) := by
  unfold check_recvmsg at h
  unfold recvmsg_spec
  generalize bv_unsigned (bv_and (abi_low32 flags) (Z_to_bv 64 MSG_CMSG_COMPAT)) = c at h ⊢
  by_cases hc : c = 0
  · simp only [hc, not_true_eq_false, ↓reduceIte] at h ⊢
    apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
    exact check_recv_fd_answer_sound_ok _ _ _ _ _ _ i h
  · simp only [hc, not_false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-- Rocq: `Checks.Sys.Net.Socket.check_recvmsg_sound_unmodeled`. -/
theorem check_recvmsg_sound_unmodeled (fd flags : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_recvmsg fd flags eff m = CheckUnmodeled) :
    recvmsg_spec fd flags i m Unmodeled := by
  unfold check_recvmsg at h
  unfold recvmsg_spec
  generalize bv_unsigned (bv_and (abi_low32 flags) (Z_to_bv 64 MSG_CMSG_COMPAT)) = c at h ⊢
  by_cases hc : c = 0
  · simp only [hc, not_true_eq_false, ↓reduceIte] at h ⊢
    apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
    exact check_recv_fd_answer_no_ok_unmodeled _ _ _ _ i h
  · simp only [hc, not_false_eq_true, ↓reduceIte]
    exact unmodeled_intro i m

/-- Rocq: `Checks.Sys.Net.Socket.check_recvmsg_complete_ok`. -/
theorem check_recvmsg_complete_ok (fd flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput) (h : recvmsg_spec fd flags i m (Ok eff m' evs)) :
    check_recvmsg fd flags eff m = CheckOk m' evs := by
  unfold recvmsg_spec at h
  unfold check_recvmsg
  generalize bv_unsigned (bv_and (abi_low32 flags) (Z_to_bv 64 MSG_CMSG_COMPAT)) = c at h ⊢
  by_cases hc : c = 0
  · simp only [hc, not_true_eq_false, ↓reduceIte] at h ⊢
    have h := bind_model_inv _ i m _ h
    exact check_recv_fd_answer_complete_ok _ _ _ _ _ _ i h
  · simp only [hc, not_false_eq_true, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h

/-- Rocq: `Checks.Sys.Net.Socket.check_recvmsg_complete_unmodeled`. -/
theorem check_recvmsg_complete_unmodeled (fd flags : word) (m : Model) (eff : SyscallEffect)
    (i : SyscallInput) (h : recvmsg_spec fd flags i m Unmodeled) :
    check_recvmsg fd flags eff m = CheckUnmodeled := by
  unfold recvmsg_spec at h
  unfold check_recvmsg
  generalize bv_unsigned (bv_and (abi_low32 flags) (Z_to_bv 64 MSG_CMSG_COMPAT)) = c at h ⊢
  by_cases hc : c = 0
  · simp only [hc, not_true_eq_false, ↓reduceIte] at h ⊢
    have h := bind_model_inv _ i m _ h
    exact check_recv_fd_answer_complete_unmodeled _ _ _ _ i h
  · simp only [hc, not_false_eq_true, ↓reduceIte]

/-! ## Witnesses

One admitted outcome per arm, each proved to be an outcome of its spec.
Where the spec draws an errno the witness takes the head of the set, as
`errno_head_witness` supplies it: -EADDRINUSE for `bind` and `listen`,
-EMFILE for `socketpair` on either destination shape.  Where the spec
declines, the witness is `Unmodeled`.  Rocq: `Checks.Witness.Net.Socket`. -/

/-- Rocq: `Checks.Witness.Net.Socket.bind_witness`.  The checker's shape
with one outcome per leaf; the fresh-socket arm fails with the head of
`bind_errnos`. -/
def bind_witness (fd addrp addrlen : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some (.FdSocket sk) =>
      (let al := sint32 addrlen
       if al < 0 ∨ SOCKADDR_STORAGE_SIZE < al then ret_outcome (errno_ret EINVAL) m
       else if al = 0 then ret_outcome (errno_ret EINVAL) m
       else
       match read_bytes_map i.in_mem addrp (Z_to_bv 64 al) with
       | none => ret_outcome (errno_ret EFAULT) m
       | some bs =>
           outcome_copyins [(addrp, al.toNat)]
             (if al < SOCKADDR_IN_SIZE then ret_outcome (errno_ret EINVAL) m
              else
                let fam := sa_family_of bs
                let port := sin_port_of bs
                let a := sin_addr_of bs
                if ¬ (fam = AF_INET ∨ (fam = AF_UNSPEC ∧ a = INADDR_ANY)) then
                  ret_outcome (errno_ret EAFNOSUPPORT) m
                else if ¬ (a = INADDR_ANY) then Unmodeled
                else if ¬ (port = 0) then Unmodeled
                else
                  match sk with
                  | .SkFresh => ret_outcome (errno_ret EADDRINUSE) m
                  | .SkBound | .SkListening => ret_outcome (errno_ret EINVAL) m
                  | .SkReset _ _ => Unmodeled
                  | .SkConnected _ _ _ => Unmodeled))
  | some _ => ret_outcome (errno_ret ENOTSOCK) m

/-- Rocq: `Checks.Witness.Net.Socket.bind_witness_ok`. -/
theorem bind_witness_ok (fd addrp addrlen : word) (i : SyscallInput) (m : Model) :
    bind_spec fd addrp addrlen i m (bind_witness fd addrp addrlen i m) := by
  unfold bind_spec bind_witness
  generalize sint32 addrlen = al
  apply bind_step _ _ i m i m _ (input_ok i m)
  apply bind_step _ _ i m m m _ (get_model_ok i m)
  generalize fd_lookup (m_fds m) fd = r
  cases r with
  | none => exact pure_ok _ i _
  | some e =>
    cases e
    case FdSocket sk =>
      simp only []
      by_cases h1 : al < 0 ∨ SOCKADDR_STORAGE_SIZE < al
      · simp only [h1, ↓reduceIte]
        exact pure_ok _ i _
      · simp only [h1, ↓reduceIte]
        by_cases h2 : al = 0
        · simp only [h2, ↓reduceIte]
          exact pure_ok _ i _
        · simp only [h2, ↓reduceIte]
          generalize read_bytes_map i.in_mem addrp (Z_to_bv 64 al) = rb
          cases rb with
          | none => exact pure_ok _ i _
          | some bs =>
            simp only []
            by_cases h3 : al < SOCKADDR_IN_SIZE
            · simp only [h3, ↓reduceIte]
              exact record_copyins_outcome _ _ i m _ (pure_ok _ i _)
            · simp only [h3, ↓reduceIte]
              by_cases h4 : sa_family_of bs = AF_INET
                  ∨ (sa_family_of bs = AF_UNSPEC ∧ sin_addr_of bs = INADDR_ANY)
              · simp only [h4, not_true_eq_false, ↓reduceIte]
                by_cases h5 : sin_addr_of bs = INADDR_ANY
                · simp only [h5, not_true_eq_false, ↓reduceIte]
                  by_cases h6 : sin_port_of bs = 0
                  · simp only [h6, not_true_eq_false, ↓reduceIte]
                    cases sk
                    case SkFresh =>
                      exact record_copyins_outcome _ _ i m _ (alt_l _ _ i m _
                        (bind_step _ _ i m _ m _ (errno_head_witness _ _ i m) (pure_ok _ i _)))
                    case SkConnected peer ch rx =>
                      exact record_copyins_outcome _ _ i m _ (unmodeled_intro i m)
                    case SkReset peer ch =>
                      exact record_copyins_outcome _ _ i m _ (unmodeled_intro i m)
                    all_goals exact record_copyins_outcome _ _ i m _ (pure_ok _ i _)
                  · simp only [h6, not_false_eq_true, ↓reduceIte]
                    exact record_copyins_outcome _ _ i m _ (unmodeled_intro i m)
                · simp only [h5, not_false_eq_true, ↓reduceIte]
                  exact record_copyins_outcome _ _ i m _ (unmodeled_intro i m)
              · simp only [h4, not_false_eq_true, ↓reduceIte]
                exact record_copyins_outcome _ _ i m _ (pure_ok _ i _)
    all_goals exact pure_ok _ i _

/-- Rocq: `Checks.Witness.Net.Socket.listen_witness`.  The fresh-socket arm
fails with the head of `listen_errnos`; the backlog plays no part. -/
def listen_witness (fd : word) (m : Model) : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some (.FdSocket sk) =>
      (match sk with
       | .SkConnected _ _ _ => ret_outcome (errno_ret EINVAL) m
       | .SkReset _ _ => ret_outcome (errno_ret EINVAL) m
       | .SkListening => ret_outcome (Z_to_bv 64 0) m
       | .SkBound =>
           ret_outcome (Z_to_bv 64 0)
             (with_fds (fd_insert (m_fds m) fd (.FdSocket .SkListening)) m)
       | .SkFresh => ret_outcome (errno_ret EADDRINUSE) m)
  | some _ => ret_outcome (errno_ret ENOTSOCK) m

/-- Rocq: `Checks.Witness.Net.Socket.listen_witness_ok`. -/
theorem listen_witness_ok (fd backlog : word) (i : SyscallInput) (m : Model) :
    listen_spec fd backlog i m (listen_witness fd m) := by
  unfold listen_spec listen_witness
  apply bind_step _ _ i m m m _ (get_model_ok i m)
  generalize fd_lookup (m_fds m) fd = r
  cases r with
  | none => exact pure_ok _ i _
  | some e =>
    cases e
    case FdSocket sk =>
      simp only []
      cases sk
      case SkFresh =>
        exact alt_l _ _ i m _
          (bind_step _ _ i m _ m _ (errno_head_witness _ _ i m) (pure_ok _ i _))
      case SkBound => exact bind_step _ _ i m () _ _ (modify_ok _ i m) (pure_ok _ i _)
      all_goals exact pure_ok _ i _
    all_goals exact pure_ok _ i _

/-- Rocq: `Checks.Witness.Net.Socket.connect_witness`.  The checker's shape
with one outcome per leaf, under `outcome_copyins` from the read down. -/
def connect_witness (fd addrp addrlen : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some e =>
      let al := sint32 addrlen
      if al < 0 ∨ SOCKADDR_STORAGE_SIZE < al then ret_outcome (errno_ret EINVAL) m
      else
      match read_bytes_map i.in_mem addrp (Z_to_bv 64 al) with
      | none => ret_outcome (errno_ret EFAULT) m
      | some bs =>
          outcome_copyins (if al = 0 then [] else [(addrp, bs.length)])
            (match e with
             | .FdSocket sk =>
                 (if al < SA_FAMILY_SIZE then ret_outcome (errno_ret EINVAL) m
                  else if sa_family_of bs = AF_UNSPEC then
                    (match sk with
                     | .SkFresh => ret_outcome (Z_to_bv 64 0) m
                     | .SkBound | .SkListening | .SkConnected _ _ _ | .SkReset _ _ => Unmodeled)
                  else
                    (match sk with
                     | .SkListening | .SkConnected _ _ _ | .SkReset _ _ =>
                         ret_outcome (errno_ret EISCONN) m
                     | .SkFresh | .SkBound =>
                         if al < SOCKADDR_IN_SIZE then ret_outcome (errno_ret EINVAL) m
                         else if ¬ (sa_family_of bs = AF_INET) then
                           ret_outcome (errno_ret EAFNOSUPPORT) m
                         else Unmodeled))
             | _ => ret_outcome (errno_ret ENOTSOCK) m)

/-- Rocq: `Checks.Witness.Net.Socket.connect_witness_ok`. -/
theorem connect_witness_ok (fd addrp addrlen : word) (i : SyscallInput) (m : Model) :
    connect_spec fd addrp addrlen i m (connect_witness fd addrp addrlen i m) := by
  unfold connect_spec connect_witness
  generalize sint32 addrlen = al
  apply bind_step _ _ i m i m _ (input_ok i m)
  apply bind_step _ _ i m m m _ (get_model_ok i m)
  generalize fd_lookup (m_fds m) fd = r
  cases r with
  | none => exact pure_ok _ i _
  | some e =>
    simp only []
    by_cases h1 : al < 0 ∨ SOCKADDR_STORAGE_SIZE < al
    · simp only [h1, ↓reduceIte]
      exact pure_ok _ i _
    · simp only [h1, ↓reduceIte]
      generalize read_bytes_map i.in_mem addrp (Z_to_bv 64 al) = rb
      cases rb with
      | none => exact pure_ok _ i _
      | some bs =>
        simp only []
        cases e
        case FdSocket sk =>
          simp only []
          by_cases h2 : al < SA_FAMILY_SIZE
          · simp only [h2, ↓reduceIte]
            exact record_copyins_outcome _ _ i m _ (pure_ok _ i _)
          · simp only [h2, ↓reduceIte]
            by_cases h3 : sa_family_of bs = AF_UNSPEC
            · simp only [h3, ↓reduceIte]
              cases sk
              case SkFresh => exact record_copyins_outcome _ _ i m _ (pure_ok _ i _)
              all_goals exact record_copyins_outcome _ _ i m _ (unmodeled_intro i m)
            · simp only [h3, ↓reduceIte]
              cases sk
              case SkListening => exact record_copyins_outcome _ _ i m _ (pure_ok _ i _)
              case SkConnected peer ch rx =>
                exact record_copyins_outcome _ _ i m _ (pure_ok _ i _)
              case SkReset peer ch => exact record_copyins_outcome _ _ i m _ (pure_ok _ i _)
              all_goals
                simp only []
                by_cases h4 : al < SOCKADDR_IN_SIZE
                · simp only [h4, ↓reduceIte]
                  exact record_copyins_outcome _ _ i m _ (pure_ok _ i _)
                · simp only [h4, ↓reduceIte]
                  by_cases h5 : sa_family_of bs = AF_INET
                  · simp only [h5, not_true_eq_false, ↓reduceIte]
                    exact record_copyins_outcome _ _ i m _ (unmodeled_intro i m)
                  · simp only [h5, not_false_eq_true, ↓reduceIte]
                    exact record_copyins_outcome _ _ i m _ (pure_ok _ i _)
        all_goals exact record_copyins_outcome _ _ i m _ (pure_ok _ i _)

/-- Rocq: `Checks.Witness.Net.Socket.getsockname_witness`. -/
def getsockname_witness (fd : word) (m : Model) : outcome SyscallEffect :=
  match sock_fd m fd with
  | .inr e => ret_outcome (errno_ret e) m
  | .inl _ => Unmodeled

/-- Rocq: `Checks.Witness.Net.Socket.getsockname_witness_ok`. -/
theorem getsockname_witness_ok (fd : word) (i : SyscallInput) (m : Model) :
    getsockname_spec fd i m (getsockname_witness fd m) := by
  unfold getsockname_spec getsockname_witness
  apply bind_step _ _ i m m m _ (get_model_ok i m)
  generalize sock_fd m fd = r
  cases r with
  | inl sk => exact unmodeled_intro i m
  | inr e => exact pure_ok _ i _

/-- Rocq: `Checks.Witness.Net.Socket.getpeername_witness`. -/
def getpeername_witness (fd : word) (m : Model) : outcome SyscallEffect :=
  match sock_fd m fd with
  | .inr e => ret_outcome (errno_ret e) m
  | .inl sk =>
      (match sk with
       | .SkConnected _ _ _ => Unmodeled
       | _ => ret_outcome (errno_ret ENOTCONN) m)

/-- Rocq: `Checks.Witness.Net.Socket.getpeername_witness_ok`. -/
theorem getpeername_witness_ok (fd : word) (i : SyscallInput) (m : Model) :
    getpeername_spec fd i m (getpeername_witness fd m) := by
  unfold getpeername_spec getpeername_witness
  apply bind_step _ _ i m m m _ (get_model_ok i m)
  generalize sock_fd m fd = r
  cases r with
  | inl sk =>
    cases sk
    case SkConnected peer ch rx => exact unmodeled_intro i m
    all_goals exact pure_ok _ i _
  | inr e => exact pure_ok _ i _

/-- Rocq: `Checks.Witness.Net.Socket.setsockopt_witness`.  The descriptor
errno, then -EINVAL on a negative length, then -ENOPROTOOPT on an unknown
level; `Unmodeled` on a known one. -/
def setsockopt_witness (fd level optlen : word) (m : Model) : outcome SyscallEffect :=
  match sock_fd m fd with
  | .inr e => ret_outcome (errno_ret e) m
  | .inl _ =>
      if int32_neg optlen then ret_outcome (errno_ret EINVAL) m
      else if ¬ (sock_level_known level) then ret_outcome (errno_ret ENOPROTOOPT) m
      else Unmodeled

/-- Rocq: `Checks.Witness.Net.Socket.setsockopt_witness_ok`. -/
theorem setsockopt_witness_ok (fd level optlen : word) (i : SyscallInput) (m : Model) :
    setsockopt_spec fd level optlen i m (setsockopt_witness fd level optlen m) := by
  unfold setsockopt_spec setsockopt_witness
  apply bind_step _ _ i m m m _ (get_model_ok i m)
  generalize sock_fd m fd = r
  cases r with
  | inr e => exact pure_ok _ i _
  | inl _ =>
    simp only []
    cases int32_neg optlen
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases sock_level_known level
      · simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
        exact pure_ok _ i _
      · simp only [not_true_eq_false, ↓reduceIte]
        exact unmodeled_intro i m
    · simp only [↓reduceIte]
      exact pure_ok _ i _

/-- Rocq: `Checks.Witness.Net.Socket.getsockopt_witness`.  The descriptor
errno with nothing read; on a socket, the `optlen` read
`getsockopt_optlen_read` names — carried by `outcome_copyins` onto the
errno and dropped by it on the decline — around -EOPNOTSUPP on an unknown
level and `Unmodeled` on a known one.  It takes the input, as Rocq's does,
because the read is of `i.in_mem`. -/
def getsockopt_witness (fd level optlenp : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  match sock_fd m fd with
  | .inr e => ret_outcome (errno_ret e) m
  | .inl _ =>
      outcome_copyins (getsockopt_optlen_read i optlenp)
        (if ¬ (sock_level_known level) then ret_outcome (errno_ret EOPNOTSUPP) m else Unmodeled)

/-- Rocq: `Checks.Witness.Net.Socket.getsockopt_witness_ok`. -/
theorem getsockopt_witness_ok (fd level optlenp : word) (i : SyscallInput) (m : Model) :
    getsockopt_spec fd level optlenp i m (getsockopt_witness fd level optlenp i m) := by
  unfold getsockopt_spec getsockopt_witness
  apply bind_step _ _ i m i m _ (input_ok i m)
  apply bind_step _ _ i m m m _ (get_model_ok i m)
  generalize sock_fd m fd = r
  cases r with
  | inr e => exact pure_ok _ i _
  | inl _ =>
    simp only []
    cases sock_level_known level
    · simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
      exact record_copyins_outcome _ _ i m _ (pure_ok _ i _)
    · simp only [not_true_eq_false, ↓reduceIte]
      exact record_copyins_outcome _ _ i m _ (unmodeled_intro i m)

/-- Rocq: `Checks.Witness.Net.Socket.shutdown_witness`. -/
def shutdown_witness (fd how : word) (m : Model) : outcome SyscallEffect :=
  match sock_fd m fd with
  | .inr e => ret_outcome (errno_ret e) m
  | .inl sk =>
      if ¬ (shut_how_ok how) then ret_outcome (errno_ret EINVAL) m
      else
        (match sk with
         | .SkListening =>
             if bv_unsigned how = SHUT_WR then ret_outcome (Z_to_bv 64 0) m else Unmodeled
         | _ => Unmodeled)

/-- Rocq: `Checks.Witness.Net.Socket.shutdown_witness_ok`. -/
theorem shutdown_witness_ok (fd how : word) (i : SyscallInput) (m : Model) :
    shutdown_spec fd how i m (shutdown_witness fd how m) := by
  unfold shutdown_spec shutdown_witness
  apply bind_step _ _ i m m m _ (get_model_ok i m)
  generalize sock_fd m fd = r
  cases r with
  | inr e => exact pure_ok _ i _
  | inl sk =>
    simp only []
    cases shut_how_ok how
    · simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
      exact pure_ok _ i _
    · simp only [not_true_eq_false, ↓reduceIte]
      cases sk
      case SkListening =>
        by_cases hw : bv_unsigned how = SHUT_WR
        · simp only [hw, ↓reduceIte]
          exact pure_ok _ i _
        · simp only [hw, ↓reduceIte]
          exact unmodeled_intro i m
      all_goals exact unmodeled_intro i m

/-- Rocq: `Checks.Witness.Net.Socket.socketpair_witness`.  Both destination
shapes fail with -EMFILE, the head of `socketpair_reserve_errnos`, which
is admitted by `socketpair_written` and `socketpair_faulted` alike. -/
def socketpair_witness (family type protocol sv : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  if ¬ (socketpair_flags_ok type) then ret_outcome (errno_ret EINVAL) m
  else if ¬ (socketpair_modeled_b family type protocol) then Unmodeled
  else
  match socketpair_fds (m_fds m) with
  | none => Unmodeled
  | some _ =>
      if socketpair_dest_writable i.in_wmem sv then ret_outcome (errno_ret EMFILE) m
      else if ¬ (access_okb sv 4) then ret_outcome (errno_ret EMFILE) m
      else Unmodeled

/-- Rocq: `Checks.Witness.Net.Socket.socketpair_witness_ok`. -/
theorem socketpair_witness_ok (family type protocol sv : word) (i : SyscallInput) (m : Model) :
    socketpair_spec family type protocol sv i m (socketpair_witness family type protocol sv i m)
    := by
  unfold socketpair_spec socketpair_witness
  cases socketpair_flags_ok type with
  | false =>
    simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
    exact pure_ok _ i _
  | true =>
    simp only [not_true_eq_false, ↓reduceIte]
    cases socketpair_modeled_b family type protocol with
    | false =>
      simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
      exact unmodeled_intro i m
    | true =>
      simp only [not_true_eq_false, ↓reduceIte]
      apply bind_step _ _ i m i m _ (input_ok i m)
      apply bind_step _ _ i m m m _ (get_model_ok i m)
      generalize socketpair_fds (m_fds m) = r
      cases r with
      | none => exact unmodeled_intro i m
      | some p =>
        obtain ⟨fd1, fd2⟩ := p
        simp only []
        cases socketpair_dest_writable i.in_wmem sv with
        | true =>
          simp only [↓reduceIte]
          exact alt_l _ _ i m _
            (bind_step _ _ i m _ m _ (errno_head_witness _ _ i m) (pure_ok _ i _))
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases access_okb sv 4 with
          | false =>
            simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
            exact alt_l _ _ i m _
              (bind_step _ _ i m _ m _ (errno_head_witness _ _ i m) (pure_ok _ i _))
          | true =>
            simp only [not_true_eq_false, ↓reduceIte]
            exact unmodeled_intro i m

/-- Rocq: `Checks.Witness.Net.Socket.socket_witness`.  The checker's shape
with one outcome per leaf.  As `Fs.Open.openat_witness` does, the passing
call takes the ERRNO side of the `alt`: `socket_errnos` is headed by
`witness_errno`, so `errno_head_witness` supplies the outcome and
`lowest_fd` does not have to be shown inhabited. -/
def socket_witness (domain type protocol : word) (m : Model) : outcome SyscallEffect :=
  let tu := abi_low32 type
  let flagbits := bv_and tu (bv_not (Z_to_bv 64 SOCK_TYPE_MASK))
  if ¬ (bv_unsigned (bv_and flagbits
          (bv_not (bv_or (Z_to_bv 64 SOCK_CLOEXEC) (Z_to_bv 64 SOCK_NONBLOCK)))) = 0)
  then ret_outcome (errno_ret EINVAL) m
  else if ¬ (bv_unsigned (bv_and flagbits (Z_to_bv 64 SOCK_NONBLOCK)) = 0) then Unmodeled
  else
    let ty : Int := bv_unsigned (bv_and tu (Z_to_bv 64 SOCK_TYPE_MASK))
    let fam : Int := sint32 domain
    let pro : Int := sint32 protocol
    if fam < 0 ∨ NPROTO ≤ fam then ret_outcome (errno_ret EAFNOSUPPORT) m
    else if SOCK_MAX ≤ ty then ret_outcome (errno_ret EINVAL) m
    else if ¬ (fam = AF_INET) then Unmodeled
    else if ty = SOCK_PACKET then Unmodeled
    else if pro < 0 ∨ IPPROTO_MAX ≤ pro then ret_outcome (errno_ret EINVAL) m
    else if ty = SOCK_STREAM then
      if pro = IPPROTO_SCTP ∨ pro = IPPROTO_MPTCP then Unmodeled
      else if ¬ (pro = IPPROTO_IP ∨ pro = IPPROTO_TCP)
      then ret_outcome (errno_ret EPROTONOSUPPORT) m
      else ret_outcome (errno_ret witness_errno) m
    else if ty = SOCK_DGRAM ∨ ty = SOCK_RAW then Unmodeled
    else if ty = SOCK_SEQPACKET ∨ ty = SOCK_DCCP then Unmodeled
    else ret_outcome (errno_ret ESOCKTNOSUPPORT) m

/-- Rocq: `Checks.Witness.Net.Socket.socket_witness_ok`. -/
theorem socket_witness_ok (domain type protocol : word) (i : SyscallInput) (m : Model) :
    socket_spec domain type protocol i m (socket_witness domain type protocol m) := by
  unfold socket_spec socket_witness
  generalize sint32 domain = fam
  generalize sint32 protocol = pro
  generalize abi_low32 type = tu
  refine bind_step _ _ i m m m _ (get_model_ok i m) ?_
  simp only []
  by_cases h1 : bv_unsigned (bv_and (bv_and tu (bv_not (Z_to_bv 64 SOCK_TYPE_MASK)))
      (bv_not (bv_or (Z_to_bv 64 SOCK_CLOEXEC) (Z_to_bv 64 SOCK_NONBLOCK)))) = 0
  case neg =>
    simp only [h1, not_false_eq_true, ↓reduceIte]
    exact pure_ok _ i _
  simp only [h1, not_true_eq_false, ↓reduceIte]
  by_cases h2 : bv_unsigned (bv_and (bv_and tu (bv_not (Z_to_bv 64 SOCK_TYPE_MASK)))
      (Z_to_bv 64 SOCK_NONBLOCK)) = 0
  case neg =>
    simp only [h2, not_false_eq_true, ↓reduceIte]
    exact unmodeled_intro i m
  simp only [h2, not_true_eq_false, ↓reduceIte]
  generalize bv_unsigned (bv_and tu (Z_to_bv 64 SOCK_TYPE_MASK)) = ty
  by_cases h3 : fam < 0 ∨ NPROTO ≤ fam
  case pos =>
    simp only [h3, ↓reduceIte]
    exact pure_ok _ i _
  simp only [h3, ↓reduceIte]
  by_cases h4 : SOCK_MAX ≤ ty
  case pos =>
    simp only [h4, ↓reduceIte]
    exact pure_ok _ i _
  simp only [h4, ↓reduceIte]
  by_cases h5 : fam = AF_INET
  case neg =>
    simp only [h5, not_false_eq_true, ↓reduceIte]
    exact unmodeled_intro i m
  simp only [h5, not_true_eq_false, ↓reduceIte]
  by_cases h6 : ty = SOCK_PACKET
  case pos =>
    simp only [h6, ↓reduceIte]
    exact unmodeled_intro i m
  simp only [h6, ↓reduceIte]
  by_cases h7 : pro < 0 ∨ IPPROTO_MAX ≤ pro
  case pos =>
    simp only [h7, ↓reduceIte]
    exact pure_ok _ i _
  simp only [h7, ↓reduceIte]
  by_cases h8 : ty = SOCK_STREAM
  case pos =>
    simp only [h8, ↓reduceIte]
    by_cases h9 : pro = IPPROTO_SCTP ∨ pro = IPPROTO_MPTCP
    case pos =>
      simp only [h9, ↓reduceIte]
      exact unmodeled_intro i m
    simp only [h9, ↓reduceIte]
    by_cases h10 : pro = IPPROTO_IP ∨ pro = IPPROTO_TCP
    case neg =>
      simp only [h10, not_false_eq_true, ↓reduceIte]
      exact pure_ok _ i _
    simp only [h10, not_true_eq_false, ↓reduceIte]
    apply alt_l
    refine bind_step _ _ i m witness_errno m _ (errno_head_witness _ _ i m) ?_
    exact pure_ok _ i m
  simp only [h8, ↓reduceIte]
  by_cases h11 : ty = SOCK_DGRAM ∨ ty = SOCK_RAW
  case pos =>
    simp only [h11, ↓reduceIte]
    exact unmodeled_intro i m
  simp only [h11, ↓reduceIte]
  by_cases h12 : ty = SOCK_SEQPACKET ∨ ty = SOCK_DCCP
  case pos =>
    simp only [h12, ↓reduceIte]
    exact unmodeled_intro i m
  simp only [h12, ↓reduceIte]
  exact pure_ok _ i _

/-- Rocq: `Checks.Witness.Net.Socket.accept4_witness`.  The checker's shape
with one outcome per leaf; the listening arm takes the ERRNO side of the
`alt` with `witness_errno`, the head of `accept_errnos`, on either
counter — which is why it needs neither a free descriptor nor the
accepted socket's state, and why the exhausted counter's empty success
branch does not have to be looked at. -/
def accept4_witness (fd addrp flags : word) (m : Model) : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some e =>
      let fl := abi_low32 flags
      if ¬ (bv_unsigned (bv_and fl
              (bv_not (bv_or (Z_to_bv 64 SOCK_CLOEXEC) (Z_to_bv 64 SOCK_NONBLOCK)))) = 0)
      then ret_outcome (errno_ret EINVAL) m
      else if ¬ (bv_unsigned (bv_and fl (Z_to_bv 64 SOCK_NONBLOCK)) = 0) then Unmodeled
      else
      (match e with
       | .FdSocket sk =>
           if ¬ (w_is0 addrp) then Unmodeled
           else
           (match sk with
            | .SkListening => ret_outcome (errno_ret witness_errno) m
            | _ => ret_outcome (errno_ret EINVAL) m)
       | _ => ret_outcome (errno_ret ENOTSOCK) m)

/-- Rocq: `Checks.Witness.Net.Socket.accept4_witness_ok`.
The non-socket witness is -ENOTSOCK, the verdict the spec reaches
whatever the address argument is. -/
theorem accept4_witness_ok (fd addrp addrlenp flags : word) (i : SyscallInput) (m : Model) :
    accept4_spec fd addrp addrlenp flags i m (accept4_witness fd addrp flags m) := by
  unfold accept4_spec accept4_witness
  generalize abi_low32 flags = fl
  refine bind_step _ _ i m m m _ (get_model_ok i m) ?_
  simp only []
  generalize fd_lookup (m_fds m) fd = r
  cases r with
  | none => exact pure_ok _ i _
  | some e =>
    simp only []
    by_cases h1 : bv_unsigned (bv_and fl
        (bv_not (bv_or (Z_to_bv 64 SOCK_CLOEXEC) (Z_to_bv 64 SOCK_NONBLOCK)))) = 0
    case neg =>
      simp only [h1, not_false_eq_true, ↓reduceIte]
      exact pure_ok _ i _
    simp only [h1, not_true_eq_false, ↓reduceIte]
    by_cases h2 : bv_unsigned (bv_and fl (Z_to_bv 64 SOCK_NONBLOCK)) = 0
    case neg =>
      simp only [h2, not_false_eq_true, ↓reduceIte]
      exact unmodeled_intro i m
    simp only [h2, not_true_eq_false, ↓reduceIte]
    cases e
    case FdSocket sk =>
      simp only []
      cases ha : w_is0 addrp with
      | false =>
        simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
        exact unmodeled_intro i m
      | true =>
        simp only [not_true_eq_false, ↓reduceIte]
        cases sk
        case SkListening =>
          simp only []
          apply alt_l
          refine bind_step _ _ i m witness_errno m _ (errno_head_witness _ _ i m) ?_
          exact pure_ok _ i m
        all_goals exact pure_ok _ i m
    all_goals exact pure_ok _ i m

set_option linter.unusedVariables false in
/-- Rocq: `Checks.Witness.Net.Socket.send_on_socket_witness`.  `SendDead`'s
-EPIPE with `pre` as its ledger, and `Unmodeled` on the two connected
states the twin declines, where Rocq's witness sends one byte (0 on a
zero-length request, -EFAULT when nothing is readable) or answers the
pending error — so Rocq's `choose` discharge has no counterpart here
(this file's header). -/
def send_on_socket_witness (pre : List (word × Nat)) (acc : Nat → List (word × Nat))
    (fd : word) (sk : SockState) (total : word) (bs : List byte) (m : Model)
    : outcome SyscallEffect :=
  match send_state sk with
  | .SendDead => outcome_copyins pre (ret_outcome (errno_ret EPIPE) m)
  | .SendErr _ _ _ => Unmodeled
  | .SendGoes _ => Unmodeled

/-- Rocq: `Checks.Witness.Net.Socket.send_on_socket_witness_ok`. -/
theorem send_on_socket_witness_ok (pre : List (word × Nat)) (acc : Nat → List (word × Nat))
    (fd : word) (sk : SockState) (total : word) (bs : List byte) (i : SyscallInput)
    (m : Model) :
    send_on_socket pre acc fd sk total bs m i m
      (send_on_socket_witness pre acc fd sk total bs m) := by
  unfold send_on_socket send_on_socket_witness
  generalize send_state sk = s
  cases s with
  | SendDead => exact record_copyins_outcome _ _ i m _ (pure_ok _ i _)
  | SendErr _ _ _ => exact unmodeled_intro i m
  | SendGoes _ => exact unmodeled_intro i m

/-- Rocq: `Checks.Witness.Net.Socket.sendto_witness`.  The checker's
nesting with one outcome per leaf, the fd inside the range verdict. -/
def sendto_witness (fd buf count flags addrp : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  if ¬ (send_flags_modeled flags) then Unmodeled
  else if ¬ (w_is0 addrp) then Unmodeled
  else if ¬ (Sys.Uaccess.modeled_rw_count count) then Unmodeled
  else
    access_ok_zero_witness buf count m
      (match fd_lookup (m_fds m) fd with
       | none => ret_outcome (errno_ret EBADF) m
       | some (.FdSocket sk) =>
           send_on_socket_witness [] (fun n => [(buf, n)]) fd sk count
             (readable_bytes i.in_mem buf count) m
       | some _ => ret_outcome (errno_ret ENOTSOCK) m)

/-- Rocq: `Checks.Witness.Net.Socket.sendto_witness_ok`. -/
theorem sendto_witness_ok (fd buf count flags addrp addrlen : word) (i : SyscallInput)
    (m : Model) :
    sendto_spec fd buf count flags addrp addrlen i m
      (sendto_witness fd buf count flags addrp i m) := by
  unfold sendto_spec sendto_witness
  cases send_flags_modeled flags with
  | false =>
    simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
    simp only [not_true_eq_false, ↓reduceIte]
    cases w_is0 addrp with
    | false =>
      simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
      exact unmodeled_intro i m
    | true =>
      simp only [not_true_eq_false, ↓reduceIte]
      cases Sys.Uaccess.modeled_rw_count count with
      | false =>
        simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
        exact unmodeled_intro i m
      | true =>
        simp only [not_true_eq_false, ↓reduceIte]
        apply bind_step _ _ i m i m _ (input_ok i m)
        apply bind_step _ _ i m m m _ (get_model_ok i m)
        unfold access_ok_zero access_ok_zero_witness
        cases access_okb buf (bv_unsigned count) with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact pure_ok _ i _
        | true =>
          simp only [↓reduceIte]
          generalize fd_lookup (m_fds m) fd = r
          cases r with
          | none => exact pure_ok _ i _
          | some e =>
            cases e
            case FdSocket sk => exact send_on_socket_witness_ok _ _ _ _ _ _ i m
            all_goals exact pure_ok _ i _

/-- Rocq: `Checks.Witness.Net.Socket.sendmsg_witness`.  The checker's
nesting with one outcome per leaf, the fd before the header. -/
def sendmsg_witness (fd msgp flags : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  if ¬ (send_flags_modeled flags) then Unmodeled
  else
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some (.FdChannel _) | some (.FdFile _ _)
  | some (.FdFileW _ _) | some (.FdFileA _ _) | some (.FdFileRW _ _)
  | some .FdDir
  | some (.FdPipe _ _)
  | some (.FdDevNull _ _)
  | some .FdUrandom => ret_outcome (errno_ret ENOTSOCK) m
  | some (.FdSocket sk) =>
      match read_bytes_map i.in_mem msgp (Z_to_bv 64 MSGHDR_SIZE) with
      | none => ret_outcome (errno_ret EFAULT) m
      | some hdr =>
          let name := le_bytes_to_word (hdr.take 8)
          let iov := le_bytes_to_word ((hdr.drop 16).take 8)
          let iovlen := le_bytes_to_word ((hdr.drop 24).take 8)
          let ctllen := le_bytes_to_word ((hdr.drop 40).take 8)
          if ¬ (w_is0 name) then Unmodeled
          else if IOV_MAX < bv_unsigned iovlen
          then outcome_copyins [(msgp, MSGHDR_SIZE.toNat)] (ret_outcome (errno_ret EMSGSIZE) m)
          else if Sys.Fs.ReadWrite.UIO_FASTIOV < bv_unsigned iovlen then Unmodeled
          else
            match copy_iovecs_aux i.in_mem iov (word_to_nat iovlen) with
            | .ImpFault =>
                outcome_copyins ([(msgp, MSGHDR_SIZE.toNat)]
                                 ++ copy_iovecs_accesses i.in_mem iov (word_to_nat iovlen))
                  (ret_outcome (errno_ret EFAULT) m)
            | .ImpInval =>
                outcome_copyins ([(msgp, MSGHDR_SIZE.toNat)]
                                 ++ copy_iovecs_accesses i.in_mem iov (word_to_nat iovlen))
                  (ret_outcome (errno_ret EINVAL) m)
            | .ImpOk iovs0 =>
                if ¬ (w_is0 ctllen) then Unmodeled
                else if ¬ (iovs_total (cap_iovecs iovs0) ≤ Sys.Uaccess.rw_bytes_max)
                then Unmodeled
                else
                  send_on_socket_witness
                    ([(msgp, MSGHDR_SIZE.toNat)]
                     ++ copy_iovecs_accesses i.in_mem iov (word_to_nat iovlen))
                    (fun n => iov_prefix_accesses (cap_iovecs iovs0) n) fd sk
                    (Z_to_bv 64 (iovs_total (cap_iovecs iovs0)))
                    (writev_gathered i.in_mem iovs0) m

/-- Rocq: `Checks.Witness.Net.Socket.sendmsg_witness_ok`. -/
theorem sendmsg_witness_ok (fd msgp flags : word) (i : SyscallInput) (m : Model) :
    sendmsg_spec fd msgp flags i m (sendmsg_witness fd msgp flags i m) := by
  unfold sendmsg_spec sendmsg_witness
  cases send_flags_modeled flags with
  | false =>
    simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
    simp only [not_true_eq_false, ↓reduceIte]
    apply bind_step _ _ i m i m _ (input_ok i m)
    apply bind_step _ _ i m m m _ (get_model_ok i m)
    generalize fd_lookup (m_fds m) fd = r
    cases r with
    | none => exact pure_ok _ i _
    | some e =>
      cases e
      case FdSocket sk =>
        simp only []
        generalize read_bytes_map i.in_mem msgp (Z_to_bv 64 MSGHDR_SIZE) = rh
        cases rh with
        | none => exact pure_ok _ i _
        | some hdr =>
          simp only []
          generalize le_bytes_to_word (List.take 8 hdr) = name
          generalize le_bytes_to_word (List.take 8 (List.drop 16 hdr)) = iov
          generalize le_bytes_to_word (List.take 8 (List.drop 24 hdr)) = iovlen
          generalize le_bytes_to_word (List.take 8 (List.drop 40 hdr)) = ctllen
          cases w_is0 name with
          | false =>
            simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
            exact unmodeled_intro i m
          | true =>
            simp only [not_true_eq_false, ↓reduceIte]
            by_cases hiv : IOV_MAX < bv_unsigned iovlen
            · simp only [hiv, ↓reduceIte]
              exact record_copyins_outcome _ _ i m _ (pure_ok _ i _)
            · simp only [hiv, ↓reduceIte]
              by_cases hfa : Sys.Fs.ReadWrite.UIO_FASTIOV < bv_unsigned iovlen
              · simp only [hfa, ↓reduceIte]
                exact unmodeled_intro i m
              · simp only [hfa, ↓reduceIte]
                generalize copy_iovecs_aux i.in_mem iov (word_to_nat iovlen) = ri
                cases ri with
                | ImpFault =>
                  simp only []
                  exact record_copyins_outcome _ _ i m _ (pure_ok _ i _)
                | ImpInval =>
                  simp only []
                  exact record_copyins_outcome _ _ i m _ (pure_ok _ i _)
                | ImpOk iovs0 =>
                  simp only []
                  cases w_is0 ctllen with
                  | false =>
                    simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
                    exact unmodeled_intro i m
                  | true =>
                    simp only [not_true_eq_false, ↓reduceIte]
                    by_cases ht : iovs_total (cap_iovecs iovs0) ≤ Sys.Uaccess.rw_bytes_max
                    · simp only [ht, not_true_eq_false, ↓reduceIte]
                      exact send_on_socket_witness_ok _ _ _ _ _ _ i m
                    · simp only [ht, not_false_eq_true, ↓reduceIte]
                      exact unmodeled_intro i m
      all_goals exact pure_ok _ i _

set_option linter.unusedVariables false in

/-- Rocq: `Checks.Witness.Net.Socket.recvfrom_witness`.  The range verdict
spelled out as Rocq's witness spells it, then the descriptor answer; `i`
is kept, unread, for Rocq's signature. -/
def recvfrom_witness (fd buf size : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  if ¬ (Sys.Uaccess.modeled_rw_count size) then Unmodeled
  else if access_okb buf (bv_unsigned size)
  then (match sockfd_lookup_errno (m_fds m) fd with
        | some e => ret_outcome (errno_ret e) m
        | none => Unmodeled)
  else ret_outcome (errno_ret EFAULT) m

/-- Rocq: `Checks.Witness.Net.Socket.recvfrom_witness_ok`. -/
theorem recvfrom_witness_ok (fd buf size : word) (i : SyscallInput) (m : Model) :
    recvfrom_spec fd buf size i m (recvfrom_witness fd buf size i m) := by
  unfold recvfrom_spec recvfrom_witness
  cases Sys.Uaccess.modeled_rw_count size with
  | false =>
    simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
    simp only [not_true_eq_false, ↓reduceIte]
    apply bind_step _ _ i m m m _ (get_model_ok i m)
    unfold access_ok_zero recv_fd_answer
    cases access_okb buf (bv_unsigned size) with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact pure_ok _ i _
    | true =>
      simp only [↓reduceIte]
      generalize sockfd_lookup_errno (m_fds m) fd = r
      cases r with
      | some _ => exact pure_ok _ i _
      | none => exact unmodeled_intro i m

/-- Rocq: `Checks.Witness.Net.Socket.recvmsg_witness`. -/
def recvmsg_witness (fd flags : word) (m : Model) : outcome SyscallEffect :=
  if ¬ (bv_unsigned (bv_and (abi_low32 flags) (Z_to_bv 64 MSG_CMSG_COMPAT)) = 0) then Unmodeled
  else
    match sockfd_lookup_errno (m_fds m) fd with
    | some e => ret_outcome (errno_ret e) m
    | none => Unmodeled

/-- Rocq: `Checks.Witness.Net.Socket.recvmsg_witness_ok`. -/
theorem recvmsg_witness_ok (fd flags : word) (i : SyscallInput) (m : Model) :
    recvmsg_spec fd flags i m (recvmsg_witness fd flags m) := by
  unfold recvmsg_spec recvmsg_witness
  generalize bv_unsigned (bv_and (abi_low32 flags) (Z_to_bv 64 MSG_CMSG_COMPAT)) = c
  by_cases hc : c = 0
  · simp only [hc, not_true_eq_false, ↓reduceIte]
    apply bind_step _ _ i m m m _ (get_model_ok i m)
    unfold recv_fd_answer
    generalize sockfd_lookup_errno (m_fds m) fd = r
    cases r with
    | some _ => exact pure_ok _ i _
    | none => exact unmodeled_intro i m
  · simp only [hc, not_false_eq_true, ↓reduceIte]
    exact unmodeled_intro i m

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Net.Socket
