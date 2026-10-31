-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Sys/Fs/ReadWrite.v
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Uaccess
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Uaccess
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.ReadWrite

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058
unported: one_iovec_mem -- a memory fixture of Rocq's closed copy-in accounting example `writev_copyin_reports_table_and_delivered_data`, read by nothing but that example and built with `RiscvSemantics.write_to_mem`, whose module imports the RISC-V decoders and instruction semantics (`Riscv.Decode`, `Riscv.DecodeC`, `Riscv.Sem`): porting it would make this checker module import all three for a fixture no proof reads.  The example's fact is twinned instead in `Checks/Cases/Checks/Sys/Fs/ReadWrite.lean`, under the example's name, over `one_iovec_zero_mem`, a memory holding the same descriptor and reading zero at every other address as `write_to_mem (fun _ => Some 0)` does; the name belongs here the day this module imports `RiscvSemantics`, directly or transitively, for another reason
unported: invalid_first_iovec_mem -- the fixture of Rocq's closed example `invalid_iovec_charges_only_the_attempted_descriptor`, unported for `one_iovec_mem`'s reason and twinned the same way, under the example's name, over `invalid_first_iovec_zero_mem` -/

/-! # LinuxProcessSem.Checks.Sys.Fs.ReadWrite — the checkers of `Sys/Fs/ReadWrite.lean`, their proofs, and their witnesses

Mirrors `theories/LinuxProcessSem/Checks/Sys/Fs/ReadWrite.v` (the executable
checkers and the lemmas relating each to its spec) and
`theories/LinuxProcessSem/Checks/Witness/Fs/ReadWrite.v` (the receptiveness
witnesses and their `_ok` lemmas).  Both Rocq files hold the checkers and
witnesses for every syscall `Sys/Fs/ReadWrite.v` defines; this module holds
them in four sections, one per porting ticket, each carrying both halves
for its syscalls, and each after the first opened by a `lean-port
sentinel` comment so that the tickets' PRs could merge by keeping every
section: `read` (63), ticket C-Fs-ReadWrite-read's, first, with the
shared steps before it; `write` (64), ticket C-Fs-ReadWrite-write's;
`pread64` (67), `pwrite64` (68) and `lseek` (62), ticket
C-Fs-ReadWrite-pread-pwrite-lseek's; and `readv` (65) and `writev` (66),
ticket C-Fs-ReadWrite-readv-writev's, last.

THE BASELINE.  The header pins f1006fe8178338a499b5e5c41be83006c4edd058,
the Rocq commit this file and its spec twin, `Sys/Fs/ReadWrite.lean`,
are both ported to.  At that commit every arm of every checker here has
a Rocq twin, and no arm of this file narrows its spec.

WHAT IS MIRRORED, AND WHAT THE LEAN SHAPES CHANGE.  `check_read` is Rocq's
arm for arm against the Lean `read_spec`, which is itself Rocq's
`read_spec` arm for arm; every departure is one the spec twin already made
and is spelled the same way here, so the proofs below step through the two
in lockstep:

- The `FdFileRW` and `FdFileA` arms answer, each as the spec twin's arm
  of that kind answers: on `read` an `FdFileRW` is the `FdFile` arm on
  the O_RDWR constructor, which writes the entry back under that kind,
  and an `FdFileA` is -EBADF, since an append fd is O_WRONLY.
- Rocq matches an `InputStream` against `IEof | ICons b s'` and a
  `NetStream` against `NFin | NRst | NTimedOut | NCons b rest`.  Both are
  structures here, so the channel arm looks at `(m_stdin m).uncons` and
  the connected-socket arm at `rx.cell_at 0`, as the spec twin does; the
  witness's one-byte deliveries take the byte and the remainder from
  `uncons` and from `net_take rx 1`.
- Rocq's `if negb b` is `if !b`, its `(1 <=? n)%Z` is `decide (1 ≤ n)`, its
  `match bs, eff with` in the file arm is a `match bs with` whose cons arm
  matches `eff` — the same three alternatives, nested — and the
  `/dev/null` arm's two `if`s of the spec twin meet Rocq's
  `check_access_ok_zero` acceptor unchanged, since both decide the same
  range verdict.

THE KERNEL ORDER `check_read` follows is `read_spec`'s, and the argument for
each decision is on that definition's docstring in `Sys/Fs/ReadWrite.lean`
and on Rocq's; this file adds nothing to it and repeats only what a reader
of a proof needs.  `SYSCALL_DEFINE3(read, …)` (fs/read_write.c:722-725,
Linux v6.18.46, commit 1f99e9ab748f) is `ksys_read` (fs/read_write.c:704-720,
Linux v6.18.46), which answers -EBADF on an empty descriptor before
anything else, then `vfs_read` (fs/read_write.c:552-581, Linux v6.18.46):
`FMODE_READ` clear → -EBADF (:556-557), `FMODE_CAN_READ` clear → -EINVAL
(:558-559; every modeled kind's `file_operations` has a reader, so no
modeled call reaches it), `access_ok` on the count the call NAMED →
-EFAULT (:560-561), `rw_verify_area` (:563; defined at :451, and its
-EINVAL where `pos + count` overflows `loff_t`, :467-469, is the divergence
the spec twin records), the
`MAX_RW_COUNT` clamp (:566-567; include/linux/fs.h:2838, Linux v6.18.46),
and only then the file's own reader — `anon_pipe_read`
(fs/pipe.c:269, Linux v6.18.46) for a pipe, `urandom_read_iter`
(drivers/char/random.c:1453, Linux v6.18.46) through `get_random_bytes_user`
(drivers/char/random.c:434, Linux v6.18.46) for /dev/urandom, `read_null`
(drivers/char/mem.c:412, Linux v6.18.46) for /dev/null, `generic_read_dir`
(fs/libfs.c:224, Linux v6.18.46) for a directory, and `tcp_recvmsg_locked`
(net/ipv4/tcp.c:2634, Linux v6.18.46) for a connected socket.  Which errno wins
when two conditions hold is the earlier test's, and the checker's arms are
ordered so.

WHAT THIS FILE HOLDS, AND WHAT WAITS.  For `read`, the checker, the
witness and the five theorems a `CheckedArm` is built from, proved against
the K1 and K5 preludes and the spec twin alone; the three sections after it
hold the same for each of `write`, `pread64`, `pwrite64`, `lseek`, `readv`
and `writev`, on the same terms.  No
`CheckedArm` value, no `checked_table` row, no `arm_unfold` lemma and no
`*_frame` lemma: the registration and the arm-level vm-maps fact are the V
ticket's, as they were for `Checks/Sys/Fs/Open.lean` — for readv, that
includes Rocq's `check_readv_gap_frame` and its `vm_done` registration,
V-Fs-ReadWrite-readv-writev's.  The two Rocq lemmas about the urandom
acceptor are also here: `check_read_urandom_delivery_clamped`, which
`Checks/Cases/Checks/Sys/Fs/ReadWrite.lean`'s clamp twin walks, and
`check_read_urandom_same_stream`, whose one consumer is a Rocq `Open`
example outside this ticket's files — stated here so that example can be
restated without reopening the acceptor.

Spellings that differ from Rocq without changing a value, said once: the
`ret_only` arms are closed by the three lemmas stated in the "Shared
steps" section (`ret_only_sound`, `ret_only_complete`,
`ret_only_not_unmodeled`) rather than by the inline `apply
check_ret_only_ok_iff in H; destruct H as (-> & -> & ->); apply pure_ok`
Rocq repeats at each of them;
`srw` is defined by both preludes with one expansion, as
`Checks/Witness/Prelude.lean`'s header explains, and this file uses
neither.  Not part of the trusted specification: the checkers are
executable and their proofs relate them to the relational specs in
`Sys/Fs/ReadWrite.lean`; a witness exhibits one outcome the spec admits. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite

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
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Uaccess

/-! ## Shared steps

Not Rocq lemmas.  Every non-delivering arm of `read_spec` is a `ret_only`
(an `err_ret` is one by definition), and its acceptor is `check_ret_only`
over the same return, model and empty event list.  Rocq closes each such
arm inline; `read_spec` has enough of them that the two directions and
the refusal to decline are stated once here and applied by name.  Each is the
K1 lemma it names, specialised to the empty event list the arms carry.
`Checks/Sys/Kernel/Futex/Syscalls.lean` states the same three facts under
its own names (`ret_only_of_check_ret_only`, `check_ret_only_of_ret_only`,
`ret_only_not_unmodeled`); both copies leave the day the frozen K1 prelude
states them once. -/

/-- A `CheckOk` of a `check_ret_only` arm is the `ret_only` outcome. -/
theorem ret_only_sound (eff : SyscallEffect) (r : word) (m m' : Model) (evs : List event)
    (i : SyscallInput) (h : check_ret_only eff r m [] = CheckOk m' evs) :
    ret_only r i m (Ok eff m' evs) := by
  obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
  exact pure_ok _ i _

/-- The `ret_only` outcome is what `check_ret_only` accepts. -/
theorem ret_only_complete (eff : SyscallEffect) (r : word) (m m' : Model) (evs : List event)
    (i : SyscallInput) (h : ret_only r i m (Ok eff m' evs)) :
    check_ret_only eff r m [] = CheckOk m' evs := by
  simp only [ret_only, pure_iff, outcome.Ok.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- `ret_only` never runs `Unmodeled`. -/
theorem ret_only_not_unmodeled (r : word) (i : SyscallInput) (m : Model)
    (h : ret_only r i m Unmodeled) : False := by
  simp only [ret_only, pure_iff, reduceCtorEq] at h

/-- `access_ok_zero` over a `ret_only` never runs `Unmodeled` either: both
range verdicts are `ret_only`s. -/
theorem access_ok_zero_ret_only_not_unmodeled (buf count r : word) (i : SyscallInput)
    (m : Model) (h : access_ok_zero buf count (ret_only r) i m Unmodeled) : False := by
  unfold access_ok_zero at h
  generalize access_okb buf (bv_unsigned count) = ok at h
  cases ok with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact ret_only_not_unmodeled _ i m h
  | true =>
    simp only [↓reduceIte] at h
    exact ret_only_not_unmodeled _ i m h

/-- Nor does its acceptor decline: both range verdicts are `check_ret_only`s. -/
theorem check_access_ok_zero_ret_only_no_unmodeled (buf count : word) (eff : SyscallEffect)
    (m m2 : Model) (r : word) (evs2 : List event) :
    check_access_ok_zero buf count eff m (check_ret_only eff r m2 evs2) ≠ CheckUnmodeled := by
  unfold check_access_ok_zero
  generalize access_okb buf (bv_unsigned count) = ok
  cases ok with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact check_ret_only_no_unmodeled _ _ _ _
  | true =>
    simp only [↓reduceIte]
    exact check_ret_only_no_unmodeled _ _ _ _

/-- Soundness of the acceptor over a `check_ret_only`: whichever side of
the range verdict, a `CheckOk` is the corresponding `ret_only` outcome. -/
theorem check_access_ok_zero_ret_only_sound (buf count r : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (h : check_access_ok_zero buf count eff m (check_ret_only eff r m []) = CheckOk m' evs) :
    access_ok_zero buf count (ret_only r) i m (Ok eff m' evs) := by
  ok_zero_cases h buf count <;> exact ret_only_sound _ _ _ _ _ i h

/-- Completeness of the same: the `ret_only` outcome on either side of the
range verdict is what the acceptor accepts. -/
theorem access_ok_zero_ret_only_complete (buf count r : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (h : access_ok_zero buf count (ret_only r) i m (Ok eff m' evs)) :
    check_access_ok_zero buf count eff m (check_ret_only eff r m []) = CheckOk m' evs := by
  unfold access_ok_zero at h
  unfold check_access_ok_zero
  generalize access_okb buf (bv_unsigned count) = ok at h ⊢
  cases ok with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact ret_only_complete _ _ _ _ _ i h
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact ret_only_complete _ _ _ _ _ i h

/-- `Prelude.listN_eqb` is reflexive, by `listN_eqb_eq`.  A private copy:
`Checks/Sys/Fs/Pipe.lean` holds the other (`Checks/Sys/Net/Socket.lean`
has none), and the frozen K1 prelude holds the same fact for `bv_eqb` and
`access_ranges_eqb` only.  The day the prelude gains this name both
copies leave together, since a file opening two of the namespaces would
find the name ambiguous. -/
theorem listN_eqb_refl (l : List byte) : listN_eqb l l = true := (listN_eqb_eq l l).mpr rfl

/-- `Prelude.writes_eqb` is reflexive, by `writes_eqb_eq`; the second copy,
`Checks/Sys/Net/Socket.lean` holding the other, and it leaves under the
same condition as `listN_eqb_refl`. -/
theorem writes_eqb_refl (l : List (word × List byte)) : writes_eqb l l = true :=
  (writes_eqb_eq l l).mpr rfl

/-- A nonzero count clamps to at least one byte: `w_is0` is `bv_eqb` against
the zero word, so a `false` there is a positive `bv_unsigned`, and
`State.MAX_RW_COUNT` is positive.  What the witnesses' one-byte deliveries
owe the `choose` of the channel and socket arms. -/
theorem one_le_rw_count_clamp (count : word) (h : w_is0 count = false) :
    1 ≤ rw_count_clamp count := by
  have hpos : 0 < bv_unsigned count := by
    unfold w_is0 bv_eqb at h
    simp only [beq_eq_false_iff_ne, ne_eq] at h
    have hr := word_unsigned_range count
    rcases Int.lt_or_eq_of_le hr.1 with hlt | heq
    · exact hlt
    · exfalso
      apply h
      unfold bv_unsigned at heq
      apply BitVec.eq_of_toNat_eq
      have h0 : count.toNat = 0 := by omega
      rw [h0]
      rfl
  unfold rw_count_clamp MAX_RW_COUNT
  omega

/-- The one byte at the head of an input stream, as `stream_take` delivers
it: the bytes are `[b]` and the remainder is the tail `uncons` exposed. -/
theorem stream_take_one_of_uncons (s : InputStream) (b : byte) (s' : InputStream)
    (hu : s.uncons = some (b, s')) : stream_take s 1 = ([b], s') := by
  simp only [stream_take, hu]

/-- The one byte at the head of a connection's script, as `net_take`
delivers it: the bytes are `[b]`; the remainder is whatever `net_take`
leaves, which the witness names by that same term. -/
theorem net_take_one_bytes_of_head (rx : NetStream) (b : byte) (hc : rx.cell_at 0 = .NByte b) :
    (net_take rx 1).1 = [b] := by
  simp only [net_take, NetStream.uncons, hc]

/-! ## read (63) — the checker

Mirrors the `read` half of `theories/LinuxProcessSem/Checks/Sys/Fs/ReadWrite.v`
at the header's baseline. -/

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_socket_pending_error`.
`ReadWrite.socket_pending_error` as an acceptor: the read that reports the
peer's RST or timeout also consumes it, so the accepted model is the one
whose connection has moved to `SkReset`.  No byte moves, so the range
verdict is all that is left in front of it. -/
def check_socket_pending_error (e : Int) (fd : word) (peer : PeerAddr) (ch : word)
    (buf count : word) (_i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  check_access_ok_zero buf count eff m
    (check_ret_only eff (errno_ret e)
       (with_fds (fd_insert (m_fds m) fd (.FdSocket (.SkReset peer ch))) m) [])

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_read_urandom`.  `ReadWrite.read_urandom`
as an acceptor, branch for branch: the zero count, the first-byte verdict,
the stream's length test, the whole-delivery verdict, and then ONE delivery
— exactly the clamped count off the front of `m_urandom` at `buf`, the
stream advanced past them, no event.  Nothing is chosen, so the accepted
effect is computed rather than matched against a predicate. -/
def check_read_urandom (i : SyscallInput) (buf count : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if w_is0 count then check_ret_only eff (Z_to_bv 64 0) m []
  else
    match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
    | none => check_ret_only eff (errno_ret EFAULT) m []
    | some _ =>
        let r := stream_take_z (m_urandom m) (rw_count_clamp count)
        if !((r.1.length : Int) = rw_count_clamp count) then CheckUnmodeled
        else
          match read_bytes_map i.in_wmem buf (len_word r.1) with
          | none => CheckUnmodeled
          | some _ =>
              match eff with
              | .mkEffectU ret [(a, bs)] [] [] [] [] =>
                  if bv_eqb a buf && bv_eqb ret (len_word r.1) && listN_eqb bs r.1
                  then CheckOk (with_urandom r.2 m) [] else CheckReject
              | _ => CheckReject

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_read`.  `read_spec` as an acceptor,
arm for arm, in the kernel's order; the argument for each decision is on
the spec's docstring.  The delivering arms differ in what is checked:

- a channel or a connected socket delivers a nonempty prefix of what the
  environment has left to say, so the accepted effect is judged against a
  PREDICATE — a length in `1 ..= rw_count_clamp count`, the bytes equal to
  that prefix of the stream, the delivered prefix writable — and the
  accepted model advances the stream past exactly those bytes;
- a file, a pipe or /dev/urandom delivers what the model computes, so the
  accepted effect is compared to it byte for byte, an empty file read
  taking the canonical empty-writes shape `check_ret_only` accepts.

A file opened O_RDWR (`FdFileRW`) is the read-only file arm (`FdFile`)
word for word, and the accepted model writes the advanced entry back
under `FdFileRW`.  A file opened O_WRONLY|O_APPEND (`FdFileA`) is -EBADF,
as `FdFileW` is: the append word rides on O_WRONLY, so FMODE_READ is
clear.

A destination none of whose bytes can land is -EFAULT; one that is
writable in part is `CheckUnmodeled`, since the copy routine's rounded
progress is not described (the spec's docstring gives the kernel reading). -/
def check_read (i : SyscallInput) (fd buf count : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdFileW _ _) => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdFileA _ _) => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdChannel ch) =>
      if !w_is0 ch then check_ret_only eff (errno_ret EBADF) m []
      else if !access_okb buf (bv_unsigned count) then check_ret_only eff (errno_ret EFAULT) m []
      else if w_is0 count then check_ret_only eff (Z_to_bv 64 0) m []
      else
        match (m_stdin m).uncons with
        | none => check_ret_only eff (Z_to_bv 64 0) m []
        | some _ =>
          match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
          | none => check_ret_only eff (errno_ret EFAULT) m []
          | some _ =>
            match read_bytes_map i.in_wmem buf
                    (len_word (stream_take_z (m_stdin m) (rw_count_clamp count)).1) with
            | none => CheckUnmodeled
            | some _ =>
              match eff with
              | .mkEffectU ret [(a, bs)] [] [] [] [] =>
                  if bv_eqb a buf
                     && bv_eqb ret (len_word bs)
                     && decide (1 ≤ (bs.length : Int))
                     && decide ((bs.length : Int) ≤ rw_count_clamp count)
                     && listN_eqb (stream_take (m_stdin m) bs.length).1 bs
                     && wmem_ok i buf (len_word bs)
                  then CheckOk (with_stdin (stream_take (m_stdin m) bs.length).2 m)
                         (List.map (ReadEv ch) bs)
                  else CheckReject
              | _ => CheckReject
  | some (.FdDevNull rd _) =>
      if !rd then check_ret_only eff (errno_ret EBADF) m []
      else check_access_ok_zero buf count eff m (check_ret_only eff (Z_to_bv 64 0) m [])
  | some .FdUrandom =>
      if !access_okb buf (bv_unsigned count) then check_ret_only eff (errno_ret EFAULT) m []
      else check_read_urandom i buf count eff m
  | some .FdDir =>
      if !access_okb buf (bv_unsigned count) then check_ret_only eff (errno_ret EFAULT) m []
      else check_ret_only eff (errno_ret EISDIR) m []
  | some (.FdSocket sk) =>
      if !modeled_rw_range buf count then CheckUnmodeled
      else if w_is0 count then
        check_access_ok_zero buf count eff m (check_ret_only eff (Z_to_bv 64 0) m [])
      else
        match sk with
        | .SkConnected peer ch rx =>
            match rx.cell_at 0 with
            | .NFin => check_access_ok_zero buf count eff m (check_ret_only eff (Z_to_bv 64 0) m [])
            | .NRst => check_socket_pending_error ECONNRESET fd peer ch buf count i eff m
            | .NTimedOut => check_socket_pending_error ETIMEDOUT fd peer ch buf count i eff m
            | .NByte _ =>
                match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
                | none => check_ret_only eff (errno_ret EFAULT) m []
                | some _ =>
                  match read_bytes_map i.in_wmem buf
                          (len_word (net_take_z rx (rw_count_clamp count)).1) with
                  | none => CheckUnmodeled
                  | some _ =>
                    match eff with
                    | .mkEffectU ret [(a, bs)] [] [] [] [] =>
                        if bv_eqb a buf
                           && bv_eqb ret (len_word bs)
                           && decide (1 ≤ (bs.length : Int))
                           && decide ((bs.length : Int) ≤ rw_count_clamp count)
                           && listN_eqb (net_take rx bs.length).1 bs
                           && wmem_ok i buf (len_word bs)
                        then CheckOk
                               (with_fds (fd_insert (m_fds m) fd
                                  (.FdSocket (.SkConnected peer ch (net_take rx bs.length).2))) m)
                               (List.map (ReadEv ch) bs)
                        else CheckReject
                    | _ => CheckReject
        | .SkReset _ _ =>
            check_access_ok_zero buf count eff m (check_ret_only eff (Z_to_bv 64 0) m [])
        | .SkFresh | .SkBound | .SkListening =>
            check_access_ok_zero buf count eff m (check_ret_only eff (errno_ret ENOTCONN) m [])
  | some (.FdFile p off) =>
      if !access_okb buf (bv_unsigned count) then check_ret_only eff (errno_ret EFAULT) m []
      else
        match fs_lookup (m_fs m) p with
        | none => CheckUnmodeled
        | some data =>
          let bs := file_read data off (Z_to_bv 64 (rw_count_clamp count))
          match read_bytes_map i.in_wmem buf (len_word bs) with
          | none =>
              match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
              | none => check_ret_only eff (errno_ret EFAULT) m []
              | some _ => CheckUnmodeled
          | some _ =>
              let m' := with_fds (fd_insert (m_fds m) fd (.FdFile p (off + len_word bs))) m
              match bs with
              | [] => check_ret_only eff (Z_to_bv 64 0) m' []
              | _ :: _ =>
                match eff with
                | .mkEffectU ret [(a, bs')] [] [] [] [] =>
                    if bv_eqb a buf && listN_eqb bs' bs && bv_eqb ret (len_word bs)
                    then CheckOk m' [] else CheckReject
                | _ => CheckReject
  | some (.FdFileRW p off) =>
      if !access_okb buf (bv_unsigned count) then check_ret_only eff (errno_ret EFAULT) m []
      else
        match fs_lookup (m_fs m) p with
        | none => CheckUnmodeled
        | some data =>
          let bs := file_read data off (Z_to_bv 64 (rw_count_clamp count))
          match read_bytes_map i.in_wmem buf (len_word bs) with
          | none =>
              match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
              | none => check_ret_only eff (errno_ret EFAULT) m []
              | some _ => CheckUnmodeled
          | some _ =>
              let m' := with_fds (fd_insert (m_fds m) fd (.FdFileRW p (off + len_word bs))) m
              match bs with
              | [] => check_ret_only eff (Z_to_bv 64 0) m' []
              | _ :: _ =>
                match eff with
                | .mkEffectU ret [(a, bs')] [] [] [] [] =>
                    if bv_eqb a buf && listN_eqb bs' bs && bv_eqb ret (len_word bs)
                    then CheckOk m' [] else CheckReject
                | _ => CheckReject
  | some (.FdPipe id w) =>
      if w then check_ret_only eff (errno_ret EBADF) m []
      else if !modeled_rw_range buf count then CheckUnmodeled
      else if w_is0 count then
        check_access_ok_zero buf count eff m (check_ret_only eff (Z_to_bv 64 0) m [])
      else
        match pipe_lookup (m_pipes m) id with
        | none => CheckUnmodeled
        | some ([], _) =>
            if pipe_end_live (m_fds m) id true then CheckUnmodeled
            else check_access_ok_zero buf count eff m (check_ret_only eff (Z_to_bv 64 0) m [])
        | some (q@(_ :: _), used) =>
            let del := pipe_take q (rw_count_clamp count)
            match read_bytes_map i.in_wmem buf (len_word del) with
            | none =>
                match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
                | none => check_ret_only eff (errno_ret EFAULT) m []
                | some _ => CheckUnmodeled
            | some _ =>
                let m' := with_pipes (pipe_insert (m_pipes m) id
                            (pipe_consume (q, used) del.length)) m
                match eff with
                | .mkEffectU ret ws [] [] [] [] =>
                    if writes_eqb ws (delivered_writes buf del) && bv_eqb ret (len_word del)
                    then CheckOk m' [] else CheckReject
                | _ => CheckReject

/-! ### The pending-error acceptor against `socket_pending_error`

Not Rocq lemmas: Rocq's `check_read_*` proofs open `check_socket_pending_error`
inline at the two arms that reach it.  The three facts are stated once here
so those proofs apply them by name at `NRst` and `NTimedOut`. -/

theorem check_socket_pending_error_sound_ok (e : Int) (fd : word) (peer : PeerAddr)
    (ch buf count : word) (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : check_socket_pending_error e fd peer ch buf count i eff m = CheckOk m' evs) :
    socket_pending_error e fd peer ch buf count i m i m (Ok eff m' evs) := by
  unfold check_socket_pending_error at h
  unfold socket_pending_error
  ok_zero_cases h buf count
  · exact ret_only_sound _ _ _ _ _ i h
  · exact (bind_set_fds_iff _ _ i m _).mpr (ret_only_sound _ _ _ _ _ i h)

theorem check_socket_pending_error_no_unmodeled (e : Int) (fd : word) (peer : PeerAddr)
    (ch buf count : word) (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_socket_pending_error e fd peer ch buf count i eff m ≠ CheckUnmodeled := by
  unfold check_socket_pending_error
  exact check_access_ok_zero_ret_only_no_unmodeled _ _ _ _ _ _ _

theorem check_socket_pending_error_complete_ok (e : Int) (fd : word) (peer : PeerAddr)
    (ch buf count : word) (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : socket_pending_error e fd peer ch buf count i m i m (Ok eff m' evs)) :
    check_socket_pending_error e fd peer ch buf count i eff m = CheckOk m' evs := by
  unfold socket_pending_error access_ok_zero at h
  unfold check_socket_pending_error check_access_ok_zero
  generalize access_okb buf (bv_unsigned count) = ok at h ⊢
  cases ok with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact ret_only_complete _ _ _ _ _ i h
  | true =>
    simp only [↓reduceIte, bind_set_fds_iff] at h ⊢
    exact ret_only_complete _ _ _ _ _ i h

theorem socket_pending_error_not_unmodeled (e : Int) (fd : word) (peer : PeerAddr)
    (ch buf count : word) (i : SyscallInput) (m : Model)
    (h : socket_pending_error e fd peer ch buf count i m i m Unmodeled) : False := by
  unfold socket_pending_error access_ok_zero at h
  generalize access_okb buf (bv_unsigned count) = ok at h
  cases ok with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact ret_only_not_unmodeled _ i m h
  | true =>
    simp only [↓reduceIte, bind_set_fds_iff] at h
    exact ret_only_not_unmodeled _ i _ h

/-! ### The urandom acceptor against `read_urandom` -/

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_read_urandom_sound_ok`. -/
theorem check_read_urandom_sound_ok (i : SyscallInput) (buf count : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_read_urandom i buf count eff m = CheckOk m' evs) :
    read_urandom buf count i m i m (Ok eff m' evs) := by
  unfold check_read_urandom at h
  unfold read_urandom
  generalize w_is0 count = b0 at h ⊢
  cases b0 with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact ret_only_sound _ _ _ _ _ i h
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
  cases w1 with
  | none => exact ret_only_sound _ _ _ _ _ i h
  | some _ =>
  dsimp only at h ⊢
  generalize stream_take_z (m_urandom m) (rw_count_clamp count) = r at h ⊢
  generalize decide ((r.1.length : Int) = rw_count_clamp count) = d at h ⊢
  cases d with
  | false =>
    simp only [Bool.not_false, ↓reduceIte] at h
    cases h
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  generalize read_bytes_map i.in_wmem buf (len_word r.1) = w2 at h ⊢
  cases w2 with
  | none => cases h
  | some _ =>
  dsimp only at h ⊢
  split at h
  · rename_i ret a bs
    split at h
    · rename_i hg
      obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj h
      simp only [Bool.and_eq_true, bv_eqb_eq, listN_eqb_eq] at hg
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hg
      exact (bind_set_urandom_iff _ _ i m _).mpr (pure_ok _ i _)
    · cases h
  · cases h

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_read_urandom_sound_unmodeled`. -/
theorem check_read_urandom_sound_unmodeled (i : SyscallInput) (buf count : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_read_urandom i buf count eff m = CheckUnmodeled) :
    read_urandom buf count i m i m Unmodeled := by
  unfold check_read_urandom at h
  unfold read_urandom
  generalize w_is0 count = b0 at h ⊢
  cases b0 with
  | true =>
    simp only [↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
  cases w1 with
  | none => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | some _ =>
  dsimp only at h ⊢
  generalize stream_take_z (m_urandom m) (rw_count_clamp count) = r at h ⊢
  generalize decide ((r.1.length : Int) = rw_count_clamp count) = d at h ⊢
  cases d with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  generalize read_bytes_map i.in_wmem buf (len_word r.1) = w2 at h ⊢
  cases w2 with
  | none => exact unmodeled_intro i m
  | some _ =>
  exfalso
  dsimp only at h
  split at h
  · split at h <;> cases h
  · cases h

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_read_urandom_complete_ok`. -/
theorem check_read_urandom_complete_ok (i : SyscallInput) (buf count : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : read_urandom buf count i m i m (Ok eff m' evs)) :
    check_read_urandom i buf count eff m = CheckOk m' evs := by
  unfold read_urandom at h
  unfold check_read_urandom
  generalize w_is0 count = b0 at h ⊢
  cases b0 with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact ret_only_complete _ _ _ _ _ i h
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
  cases w1 with
  | none => exact ret_only_complete _ _ _ _ _ i h
  | some _ =>
  dsimp only at h ⊢
  generalize stream_take_z (m_urandom m) (rw_count_clamp count) = r at h ⊢
  generalize decide ((r.1.length : Int) = rw_count_clamp count) = d at h ⊢
  cases d with
  | false =>
    simp only [Bool.not_false, ↓reduceIte] at h
    cases h
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  generalize read_bytes_map i.in_wmem buf (len_word r.1) = w2 at h ⊢
  cases w2 with
  | none => cases h
  | some _ =>
  dsimp only at h ⊢
  simp only [bind_set_urandom_iff, pure_iff, outcome.Ok.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  simp only [bv_eqb_refl, listN_eqb_refl, Bool.and_self, ↓reduceIte]

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_read_urandom_complete_unmodeled`. -/
theorem check_read_urandom_complete_unmodeled (i : SyscallInput) (buf count : word)
    (eff : SyscallEffect) (m : Model)
    (h : read_urandom buf count i m i m Unmodeled) :
    check_read_urandom i buf count eff m = CheckUnmodeled := by
  unfold read_urandom at h
  unfold check_read_urandom
  generalize w_is0 count = b0 at h ⊢
  cases b0 with
  | true =>
    simp only [↓reduceIte] at h
    exact (ret_only_not_unmodeled _ i m h).elim
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
  cases w1 with
  | none => exact (ret_only_not_unmodeled _ i m h).elim
  | some _ =>
  dsimp only at h ⊢
  generalize stream_take_z (m_urandom m) (rw_count_clamp count) = r at h ⊢
  generalize decide ((r.1.length : Int) = rw_count_clamp count) = d at h ⊢
  cases d with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  generalize read_bytes_map i.in_wmem buf (len_word r.1) = w2 at h ⊢
  cases w2 with
  | none => rfl
  | some _ =>
  dsimp only at h
  simp only [bind_set_urandom_iff, pure_iff, reduceCtorEq] at h

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_read_urandom_delivery_clamped`.  An
accepted delivery is at most `MAX_RW_COUNT` bytes long: the length test
equates it to the clamped count, which `rw_count_clamp_range` bounds. -/
theorem check_read_urandom_delivery_clamped (i : SyscallInput) (buf count : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event) (a : word) (bs : List byte)
    (h : check_read_urandom i buf count eff m = CheckOk m' evs)
    (hws : eff.eff_writes = [(a, bs)]) :
    (bs.length : Int) ≤ MAX_RW_COUNT := by
  unfold check_read_urandom at h
  generalize w_is0 count = b0 at h
  cases b0 with
  | true =>
    simp only [↓reduceIte] at h
    obtain ⟨rfl, -, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    cases hws
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h
  cases w1 with
  | none =>
    obtain ⟨rfl, -, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    cases hws
  | some _ =>
  dsimp only at h
  generalize stream_take_z (m_urandom m) (rw_count_clamp count) = r at h
  generalize hlen : decide ((r.1.length : Int) = rw_count_clamp count) = d at h
  cases d with
  | false =>
    simp only [Bool.not_false, ↓reduceIte] at h
    cases h
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  generalize read_bytes_map i.in_wmem buf (len_word r.1) = w2 at h
  cases w2 with
  | none => cases h
  | some _ =>
  dsimp only at h
  split at h
  · rename_i ret a' bs'
    split at h
    · rename_i hg
      simp only [Bool.and_eq_true, bv_eqb_eq, listN_eqb_eq] at hg
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hg
      simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hws
      obtain ⟨rfl, rfl⟩ := hws
      have hl := of_decide_eq_true hlen
      have hr := rw_count_clamp_range count
      omega
    · cases h
  · cases h

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_read_urandom_same_stream`.  THE SAME
STREAM READS THE SAME BYTES: two models that agree on `m_urandom` — the
source and the target of an equivalence pair, seeded from one
`in_urandom` — hand the same bytes to the same request and leave the same
remainder, whatever else they differ in.  Nothing is chosen on the way, so
this is by computation rather than by a relation between choices; the
proof walks the acceptor once with both hypotheses in step. -/
theorem check_read_urandom_same_stream (i : SyscallInput) (buf count : word)
    (eff1 eff2 : SyscallEffect) (m1 m2 m1' m2' : Model) (evs1 evs2 : List event)
    (hu : m_urandom m1 = m_urandom m2)
    (h1 : check_read_urandom i buf count eff1 m1 = CheckOk m1' evs1)
    (h2 : check_read_urandom i buf count eff2 m2 = CheckOk m2' evs2) :
    eff1.eff_writes = eff2.eff_writes ∧ eff1.eff_ret = eff2.eff_ret
      ∧ m_urandom m1' = m_urandom m2' := by
  unfold check_read_urandom at h1 h2
  generalize w_is0 count = b0 at h1 h2
  cases b0 with
  | true =>
    simp only [↓reduceIte] at h1 h2
    obtain ⟨rfl, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h1
    obtain ⟨rfl, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h2
    exact ⟨rfl, rfl, hu⟩
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2
  generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h1 h2
  cases w1 with
  | none =>
    obtain ⟨rfl, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h1
    obtain ⟨rfl, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h2
    exact ⟨rfl, rfl, hu⟩
  | some _ =>
  dsimp only at h1 h2
  rw [hu] at h1
  generalize stream_take_z (m_urandom m2) (rw_count_clamp count) = r at h1 h2
  generalize decide ((r.1.length : Int) = rw_count_clamp count) = d at h1 h2
  cases d with
  | false => simp only [Bool.not_false, ↓reduceIte] at h1; cases h1
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h1 h2
  generalize read_bytes_map i.in_wmem buf (len_word r.1) = w2 at h1 h2
  cases w2 with
  | none => cases h1
  | some _ =>
  dsimp only at h1 h2
  split at h1
  · split at h1
    · rename_i hg1
      simp only [Bool.and_eq_true, bv_eqb_eq, listN_eqb_eq] at hg1
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hg1
      obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj h1
      split at h2
      · split at h2
        · rename_i hg2
          simp only [Bool.and_eq_true, bv_eqb_eq, listN_eqb_eq] at hg2
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hg2
          obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj h2
          exact ⟨rfl, rfl, rfl⟩
        · cases h2
      · cases h2
    · cases h1
  · cases h1

/-! ### The read acceptor against `read_spec`

Each proof walks the two definitions in lockstep: the descriptor lookup,
then the arm's gates in the kernel's order, `generalize`d so that both
sides step together, and at the leaf either the `ret_only` lemmas above,
the delivery's own predicate, or a constructor clash.  The `_unmodeled`
directions have real arms to reach — the partially writable destination,
the missing file, the pipe that would block and the pipe id the table does
not hold — and refute every other leaf. -/

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_read_sound_ok`. -/
theorem check_read_sound_ok (i : SyscallInput) (fd buf count : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_read i fd buf count eff m = CheckOk m' evs) :
    read_spec fd buf count i m (Ok eff m' evs) := by
  unfold check_read at h
  unfold read_spec
  rw [bind_input_iff, bind_get_model_iff]
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact ret_only_sound _ _ _ _ _ i h
  | some e =>
  cases e with
  | FdFileW _ _ => exact ret_only_sound _ _ _ _ _ i h
  | FdFileA _ _ => exact ret_only_sound _ _ _ _ _ i h
  | FdChannel ch =>
    dsimp only at h ⊢
    generalize (!w_is0 ch) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize w_is0 count = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (m_stdin m).uncons = u at h ⊢
    cases u with
    | none => exact ret_only_sound _ _ _ _ _ i h
    | some _ =>
    dsimp only at h ⊢
    generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
    cases w1 with
    | none => exact ret_only_sound _ _ _ _ _ i h
    | some _ =>
    dsimp only at h ⊢
    generalize read_bytes_map i.in_wmem buf
      (len_word (stream_take_z (m_stdin m) (rw_count_clamp count)).1) = w2 at h ⊢
    cases w2 with
    | none => cases h
    | some _ =>
    dsimp only at h ⊢
    split at h
    · rename_i ret a bs
      split at h
      · rename_i hg
        obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj h
        simp only [Bool.and_eq_true, bv_eqb_eq, listN_eqb_eq, decide_eq_true_eq,
          wmem_ok_true] at hg
        obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, h1⟩, h2⟩, h3⟩, h4⟩ := hg
        rw [bind_choose_iff]
        refine ⟨bs, ⟨h1, h2, h3, h4⟩, ?_⟩
        exact (bind_set_stdin_iff _ _ i m _).mpr (emit_pure_ok _ _ i _)
      · cases h
    · cases h
  | FdDevNull rd wr =>
    dsimp only at h ⊢
    cases rd with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    unfold check_access_ok_zero at h
    generalize access_okb buf (bv_unsigned count) = ok at h ⊢
    cases ok with
    | false =>
      simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
  | FdUrandom =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact check_read_urandom_sound_ok _ _ _ _ _ _ _ h
  | FdDir =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
  | FdSocket sk =>
    dsimp only at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize w_is0 count = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact check_access_ok_zero_ret_only_sound _ _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases sk with
    | SkFresh =>
      dsimp only at h ⊢
      exact check_access_ok_zero_ret_only_sound _ _ _ _ _ _ _ i h
    | SkBound =>
      dsimp only at h ⊢
      exact check_access_ok_zero_ret_only_sound _ _ _ _ _ _ _ i h
    | SkListening =>
      dsimp only at h ⊢
      exact check_access_ok_zero_ret_only_sound _ _ _ _ _ _ _ i h
    | SkReset _ _ =>
      dsimp only at h ⊢
      exact check_access_ok_zero_ret_only_sound _ _ _ _ _ _ _ i h
    | SkConnected peer ch rx =>
    dsimp only at h ⊢
    generalize rx.cell_at 0 = c at h ⊢
    cases c with
    | NFin =>
      dsimp only at h ⊢
      exact check_access_ok_zero_ret_only_sound _ _ _ _ _ _ _ i h
    | NRst => exact check_socket_pending_error_sound_ok _ _ _ _ _ _ _ _ _ _ _ h
    | NTimedOut => exact check_socket_pending_error_sound_ok _ _ _ _ _ _ _ _ _ _ _ h
    | NByte _ =>
    dsimp only at h ⊢
    generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
    cases w1 with
    | none => exact ret_only_sound _ _ _ _ _ i h
    | some _ =>
    dsimp only at h ⊢
    generalize read_bytes_map i.in_wmem buf
      (len_word (net_take_z rx (rw_count_clamp count)).1) = w2 at h ⊢
    cases w2 with
    | none => cases h
    | some _ =>
    dsimp only at h ⊢
    split at h
    · rename_i ret a bs
      split at h
      · rename_i hg
        obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj h
        simp only [Bool.and_eq_true, bv_eqb_eq, listN_eqb_eq, decide_eq_true_eq,
          wmem_ok_true] at hg
        obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, h1⟩, h2⟩, h3⟩, h4⟩ := hg
        rw [bind_choose_iff]
        refine ⟨bs, ⟨h1, h2, h3, h4⟩, ?_⟩
        exact (bind_set_fds_iff _ _ i m _).mpr (emit_pure_ok _ _ i _)
      · cases h
    · cases h
  | FdFile p off =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize file_read data off (Z_to_bv 64 (rw_count_clamp count)) = bs at h ⊢
    generalize read_bytes_map i.in_wmem buf (len_word bs) = w at h ⊢
    cases w with
    | none =>
      dsimp only at h ⊢
      generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
      cases w1 with
      | none => exact ret_only_sound _ _ _ _ _ i h
      | some _ => cases h
    | some _ =>
    dsimp only at h ⊢
    rw [bind_set_fds_iff]
    cases bs with
    | nil =>
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _
    | cons b bs0 =>
    dsimp only at h
    split at h
    · rename_i ret a bs'
      split at h
      · rename_i hg
        obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj h
        simp only [Bool.and_eq_true, bv_eqb_eq, listN_eqb_eq] at hg
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hg
        exact pure_ok _ i _
      · cases h
    · cases h
  | FdFileRW p off =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize file_read data off (Z_to_bv 64 (rw_count_clamp count)) = bs at h ⊢
    generalize read_bytes_map i.in_wmem buf (len_word bs) = w at h ⊢
    cases w with
    | none =>
      dsimp only at h ⊢
      generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
      cases w1 with
      | none => exact ret_only_sound _ _ _ _ _ i h
      | some _ => cases h
    | some _ =>
    dsimp only at h ⊢
    rw [bind_set_fds_iff]
    cases bs with
    | nil =>
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _
    | cons b bs0 =>
    dsimp only at h
    split at h
    · rename_i ret a bs'
      split at h
      · rename_i hg
        obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj h
        simp only [Bool.and_eq_true, bv_eqb_eq, listN_eqb_eq] at hg
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hg
        exact pure_ok _ i _
      · cases h
    · cases h
  | FdPipe id w =>
    dsimp only at h ⊢
    cases w with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize w_is0 count = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact check_access_ok_zero_ret_only_sound _ _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize pipe_lookup (m_pipes m) id = pl at h ⊢
    rcases pl with _ | ⟨_ | ⟨b, q0⟩, used⟩
    · cases h
    · dsimp only at h ⊢
      generalize pipe_end_live (m_fds m) id true = live at h ⊢
      cases live with
      | true =>
        simp only [↓reduceIte] at h
        cases h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact check_access_ok_zero_ret_only_sound _ _ _ _ _ _ _ i h
    · dsimp only at h ⊢
      generalize pipe_take (b :: q0) (rw_count_clamp count) = del at h ⊢
      generalize read_bytes_map i.in_wmem buf (len_word del) = w at h ⊢
      cases w with
      | none =>
        dsimp only at h ⊢
        generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
        cases w1 with
        | none => exact ret_only_sound _ _ _ _ _ i h
        | some _ => cases h
      | some _ =>
      dsimp only at h ⊢
      split at h
      · rename_i ret ws
        split at h
        · rename_i hg
          obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj h
          simp only [Bool.and_eq_true, writes_eqb_eq, bv_eqb_eq] at hg
          obtain ⟨rfl, rfl⟩ := hg
          exact (bind_set_pipes_iff _ _ i m _).mpr (pure_ok _ i _)
        · cases h
      · cases h

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_read_sound_unmodeled`. -/
theorem check_read_sound_unmodeled (i : SyscallInput) (fd buf count : word) (eff : SyscallEffect)
    (m : Model) (h : check_read i fd buf count eff m = CheckUnmodeled) :
    read_spec fd buf count i m Unmodeled := by
  unfold check_read at h
  unfold read_spec
  rw [bind_input_iff, bind_get_model_iff]
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | some e =>
  cases e with
  | FdFileW _ _ => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | FdFileA _ _ => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | FdChannel ch =>
    dsimp only at h ⊢
    generalize (!w_is0 ch) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize w_is0 count = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (m_stdin m).uncons = u at h ⊢
    cases u with
    | none => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | some _ =>
    dsimp only at h ⊢
    generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
    cases w1 with
    | none => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | some _ =>
    dsimp only at h ⊢
    generalize read_bytes_map i.in_wmem buf
      (len_word (stream_take_z (m_stdin m) (rw_count_clamp count)).1) = w2 at h ⊢
    cases w2 with
    | none => exact unmodeled_intro i m
    | some _ =>
    exfalso
    dsimp only at h
    split at h
    · split at h <;> cases h
    · cases h
  | FdDevNull rd wr =>
    exfalso
    dsimp only at h
    cases rd with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h
      exact check_ret_only_no_unmodeled _ _ _ _ h
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      exact check_access_ok_zero_ret_only_no_unmodeled _ _ _ _ _ _ _ h
  | FdUrandom =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact check_read_urandom_sound_unmodeled _ _ _ _ _ h
  | FdDir =>
    exfalso
    dsimp only at h
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact check_ret_only_no_unmodeled _ _ _ _ h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact check_ret_only_no_unmodeled _ _ _ _ h
  | FdSocket sk =>
    dsimp only at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize w_is0 count = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_access_ok_zero_ret_only_no_unmodeled _ _ _ _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases sk with
    | SkFresh =>
      dsimp only at h
      exact absurd h (check_access_ok_zero_ret_only_no_unmodeled _ _ _ _ _ _ _)
    | SkBound =>
      dsimp only at h
      exact absurd h (check_access_ok_zero_ret_only_no_unmodeled _ _ _ _ _ _ _)
    | SkListening =>
      dsimp only at h
      exact absurd h (check_access_ok_zero_ret_only_no_unmodeled _ _ _ _ _ _ _)
    | SkReset _ _ =>
      dsimp only at h
      exact absurd h (check_access_ok_zero_ret_only_no_unmodeled _ _ _ _ _ _ _)
    | SkConnected peer ch rx =>
    dsimp only at h ⊢
    generalize rx.cell_at 0 = c at h ⊢
    cases c with
    | NFin =>
      dsimp only at h
      exact absurd h (check_access_ok_zero_ret_only_no_unmodeled _ _ _ _ _ _ _)
    | NRst => exact absurd h (check_socket_pending_error_no_unmodeled _ _ _ _ _ _ _ _ _)
    | NTimedOut => exact absurd h (check_socket_pending_error_no_unmodeled _ _ _ _ _ _ _ _ _)
    | NByte _ =>
    dsimp only at h ⊢
    generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
    cases w1 with
    | none => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | some _ =>
    dsimp only at h ⊢
    generalize read_bytes_map i.in_wmem buf
      (len_word (net_take_z rx (rw_count_clamp count)).1) = w2 at h ⊢
    cases w2 with
    | none => exact unmodeled_intro i m
    | some _ =>
    exfalso
    dsimp only at h
    split at h
    · split at h <;> cases h
    · cases h
  | FdFile p off =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only at h ⊢
    generalize file_read data off (Z_to_bv 64 (rw_count_clamp count)) = bs at h ⊢
    generalize read_bytes_map i.in_wmem buf (len_word bs) = w at h ⊢
    cases w with
    | none =>
      dsimp only at h ⊢
      generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
      cases w1 with
      | none => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
      | some _ => exact unmodeled_intro i m
    | some _ =>
    exfalso
    dsimp only at h
    cases bs with
    | nil => exact check_ret_only_no_unmodeled _ _ _ _ h
    | cons b bs0 =>
      dsimp only at h
      split at h
      · split at h <;> cases h
      · cases h
  | FdFileRW p off =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only at h ⊢
    generalize file_read data off (Z_to_bv 64 (rw_count_clamp count)) = bs at h ⊢
    generalize read_bytes_map i.in_wmem buf (len_word bs) = w at h ⊢
    cases w with
    | none =>
      dsimp only at h ⊢
      generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
      cases w1 with
      | none => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
      | some _ => exact unmodeled_intro i m
    | some _ =>
    exfalso
    dsimp only at h
    cases bs with
    | nil => exact check_ret_only_no_unmodeled _ _ _ _ h
    | cons b bs0 =>
      dsimp only at h
      split at h
      · split at h <;> cases h
      · cases h
  | FdPipe id w =>
    dsimp only at h ⊢
    cases w with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize w_is0 count = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_access_ok_zero_ret_only_no_unmodeled _ _ _ _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize pipe_lookup (m_pipes m) id = pl at h ⊢
    rcases pl with _ | ⟨_ | ⟨b, q0⟩, used⟩
    · exact unmodeled_intro i m
    · dsimp only at h ⊢
      generalize pipe_end_live (m_fds m) id true = live at h ⊢
      cases live with
      | true =>
        simp only [↓reduceIte]
        exact unmodeled_intro i m
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        exact absurd h (check_access_ok_zero_ret_only_no_unmodeled _ _ _ _ _ _ _)
    · dsimp only at h ⊢
      generalize pipe_take (b :: q0) (rw_count_clamp count) = del at h ⊢
      generalize read_bytes_map i.in_wmem buf (len_word del) = w at h ⊢
      cases w with
      | none =>
        dsimp only at h ⊢
        generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
        cases w1 with
        | none => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
        | some _ => exact unmodeled_intro i m
      | some _ =>
      exfalso
      dsimp only at h
      split at h
      · split at h <;> cases h
      · cases h

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_read_complete_ok`. -/
theorem check_read_complete_ok (i : SyscallInput) (fd buf count : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : read_spec fd buf count i m (Ok eff m' evs)) :
    check_read i fd buf count eff m = CheckOk m' evs := by
  unfold read_spec at h
  unfold check_read
  rw [bind_input_iff, bind_get_model_iff] at h
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact ret_only_complete _ _ _ _ _ i h
  | some e =>
  cases e with
  | FdFileW _ _ => exact ret_only_complete _ _ _ _ _ i h
  | FdFileA _ _ => exact ret_only_complete _ _ _ _ _ i h
  | FdChannel ch =>
    dsimp only at h ⊢
    generalize (!w_is0 ch) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize w_is0 count = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (m_stdin m).uncons = u at h ⊢
    cases u with
    | none => exact ret_only_complete _ _ _ _ _ i h
    | some _ =>
    dsimp only at h ⊢
    generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
    cases w1 with
    | none => exact ret_only_complete _ _ _ _ _ i h
    | some _ =>
    dsimp only at h ⊢
    generalize read_bytes_map i.in_wmem buf
      (len_word (stream_take_z (m_stdin m) (rw_count_clamp count)).1) = w2 at h ⊢
    cases w2 with
    | none => cases h
    | some _ =>
    dsimp only at h ⊢
    rw [bind_choose_iff] at h
    obtain ⟨bs, ⟨h1, h2, h3, h4⟩, hk⟩ := h
    simp only [bind_set_stdin_iff, bind_emit_cases_iff] at hk
    rcases hk with ⟨y, m2, evs2, hp, heq⟩ | ⟨-, heq⟩
    · simp only [pure_iff, outcome.Ok.injEq] at hp
      obtain ⟨rfl, rfl, rfl⟩ := hp
      obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj heq
      simp only [bv_eqb_refl, decide_eq_true h1, decide_eq_true h2, h3, listN_eqb_refl,
        (wmem_ok_true _ _ _).mpr h4, Bool.and_self, ↓reduceIte, List.append_nil]
    · cases heq
  | FdDevNull rd wr =>
    dsimp only at h ⊢
    cases rd with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    unfold check_access_ok_zero
    generalize access_okb buf (bv_unsigned count) = ok at h ⊢
    cases ok with
    | false =>
      simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
  | FdUrandom =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact check_read_urandom_complete_ok _ _ _ _ _ _ _ h
  | FdDir =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
  | FdSocket sk =>
    dsimp only at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize w_is0 count = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact access_ok_zero_ret_only_complete _ _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases sk with
    | SkFresh =>
      dsimp only at h ⊢
      exact access_ok_zero_ret_only_complete _ _ _ _ _ _ _ i h
    | SkBound =>
      dsimp only at h ⊢
      exact access_ok_zero_ret_only_complete _ _ _ _ _ _ _ i h
    | SkListening =>
      dsimp only at h ⊢
      exact access_ok_zero_ret_only_complete _ _ _ _ _ _ _ i h
    | SkReset _ _ =>
      dsimp only at h ⊢
      exact access_ok_zero_ret_only_complete _ _ _ _ _ _ _ i h
    | SkConnected peer ch rx =>
    dsimp only at h ⊢
    generalize rx.cell_at 0 = c at h ⊢
    cases c with
    | NFin =>
      dsimp only at h ⊢
      exact access_ok_zero_ret_only_complete _ _ _ _ _ _ _ i h
    | NRst => exact check_socket_pending_error_complete_ok _ _ _ _ _ _ _ _ _ _ _ h
    | NTimedOut => exact check_socket_pending_error_complete_ok _ _ _ _ _ _ _ _ _ _ _ h
    | NByte _ =>
    dsimp only at h ⊢
    generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
    cases w1 with
    | none => exact ret_only_complete _ _ _ _ _ i h
    | some _ =>
    dsimp only at h ⊢
    generalize read_bytes_map i.in_wmem buf
      (len_word (net_take_z rx (rw_count_clamp count)).1) = w2 at h ⊢
    cases w2 with
    | none => cases h
    | some _ =>
    dsimp only at h ⊢
    rw [bind_choose_iff] at h
    obtain ⟨bs, ⟨h1, h2, h3, h4⟩, hk⟩ := h
    simp only [bind_set_fds_iff, bind_emit_cases_iff] at hk
    rcases hk with ⟨y, m2, evs2, hp, heq⟩ | ⟨-, heq⟩
    · simp only [pure_iff, outcome.Ok.injEq] at hp
      obtain ⟨rfl, rfl, rfl⟩ := hp
      obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj heq
      simp only [bv_eqb_refl, decide_eq_true h1, decide_eq_true h2, h3, listN_eqb_refl,
        (wmem_ok_true _ _ _).mpr h4, Bool.and_self, ↓reduceIte, List.append_nil]
    · cases heq
  | FdFile p off =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize file_read data off (Z_to_bv 64 (rw_count_clamp count)) = bs at h ⊢
    generalize read_bytes_map i.in_wmem buf (len_word bs) = w at h ⊢
    cases w with
    | none =>
      dsimp only at h ⊢
      generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
      cases w1 with
      | none => exact ret_only_complete _ _ _ _ _ i h
      | some _ => cases h
    | some _ =>
    dsimp only at h ⊢
    simp only [bind_set_fds_iff, pure_iff, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    cases bs with
    | nil => exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    | cons b bs0 =>
      simp only [delivered_writes, bv_eqb_refl, listN_eqb_refl, Bool.and_self, ↓reduceIte]
  | FdFileRW p off =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize file_read data off (Z_to_bv 64 (rw_count_clamp count)) = bs at h ⊢
    generalize read_bytes_map i.in_wmem buf (len_word bs) = w at h ⊢
    cases w with
    | none =>
      dsimp only at h ⊢
      generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
      cases w1 with
      | none => exact ret_only_complete _ _ _ _ _ i h
      | some _ => cases h
    | some _ =>
    dsimp only at h ⊢
    simp only [bind_set_fds_iff, pure_iff, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    cases bs with
    | nil => exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    | cons b bs0 =>
      simp only [delivered_writes, bv_eqb_refl, listN_eqb_refl, Bool.and_self, ↓reduceIte]
  | FdPipe id w =>
    dsimp only at h ⊢
    cases w with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize w_is0 count = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact access_ok_zero_ret_only_complete _ _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize pipe_lookup (m_pipes m) id = pl at h ⊢
    rcases pl with _ | ⟨_ | ⟨b, q0⟩, used⟩
    · cases h
    · dsimp only at h ⊢
      generalize pipe_end_live (m_fds m) id true = live at h ⊢
      cases live with
      | true =>
        simp only [↓reduceIte] at h
        cases h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact access_ok_zero_ret_only_complete _ _ _ _ _ _ _ i h
    · dsimp only at h ⊢
      generalize pipe_take (b :: q0) (rw_count_clamp count) = del at h ⊢
      generalize read_bytes_map i.in_wmem buf (len_word del) = w at h ⊢
      cases w with
      | none =>
        dsimp only at h ⊢
        generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
        cases w1 with
        | none => exact ret_only_complete _ _ _ _ _ i h
        | some _ => cases h
      | some _ =>
      dsimp only at h ⊢
      simp only [bind_set_pipes_iff, pure_iff, outcome.Ok.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [writes_eqb_refl, bv_eqb_refl, Bool.and_self, ↓reduceIte]

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_read_complete_unmodeled`. -/
theorem check_read_complete_unmodeled (i : SyscallInput) (fd buf count : word)
    (eff : SyscallEffect) (m : Model) (h : read_spec fd buf count i m Unmodeled) :
    check_read i fd buf count eff m = CheckUnmodeled := by
  unfold read_spec at h
  unfold check_read
  rw [bind_input_iff, bind_get_model_iff] at h
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact (ret_only_not_unmodeled _ i m h).elim
  | some e =>
  cases e with
  | FdFileW _ _ => exact (ret_only_not_unmodeled _ i m h).elim
  | FdFileA _ _ => exact (ret_only_not_unmodeled _ i m h).elim
  | FdChannel ch =>
    dsimp only at h ⊢
    generalize (!w_is0 ch) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize w_is0 count = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (m_stdin m).uncons = u at h ⊢
    cases u with
    | none => exact (ret_only_not_unmodeled _ i m h).elim
    | some _ =>
    dsimp only at h ⊢
    generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
    cases w1 with
    | none => exact (ret_only_not_unmodeled _ i m h).elim
    | some _ =>
    dsimp only at h ⊢
    generalize read_bytes_map i.in_wmem buf
      (len_word (stream_take_z (m_stdin m) (rw_count_clamp count)).1) = w2 at h ⊢
    cases w2 with
    | none => rfl
    | some _ =>
    exfalso
    dsimp only at h
    rw [bind_choose_iff] at h
    obtain ⟨bs, -, hk⟩ := h
    simp only [bind_set_stdin_iff, bind_emit_cases_iff] at hk
    rcases hk with ⟨y, m2, evs2, -, heq⟩ | ⟨hp, -⟩
    · cases heq
    · simp only [pure_iff, reduceCtorEq] at hp
  | FdDevNull rd wr =>
    exfalso
    dsimp only at h
    cases rd with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h
      exact ret_only_not_unmodeled _ i m h
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      generalize access_okb buf (bv_unsigned count) = ok at h
      cases ok with
      | false =>
        simp only [Bool.not_false, ↓reduceIte] at h
        exact ret_only_not_unmodeled _ i m h
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        exact ret_only_not_unmodeled _ i m h
  | FdUrandom =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact check_read_urandom_complete_unmodeled _ _ _ _ _ h
  | FdDir =>
    exfalso
    dsimp only at h
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact ret_only_not_unmodeled _ i m h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact ret_only_not_unmodeled _ i m h
  | FdSocket sk =>
    dsimp only at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true => simp only [↓reduceIte]
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize w_is0 count = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (access_ok_zero_ret_only_not_unmodeled _ _ _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases sk with
    | SkFresh =>
      dsimp only at h
      exact (access_ok_zero_ret_only_not_unmodeled _ _ _ i m h).elim
    | SkBound =>
      dsimp only at h
      exact (access_ok_zero_ret_only_not_unmodeled _ _ _ i m h).elim
    | SkListening =>
      dsimp only at h
      exact (access_ok_zero_ret_only_not_unmodeled _ _ _ i m h).elim
    | SkReset _ _ =>
      dsimp only at h
      exact (access_ok_zero_ret_only_not_unmodeled _ _ _ i m h).elim
    | SkConnected peer ch rx =>
    dsimp only at h ⊢
    generalize rx.cell_at 0 = c at h ⊢
    cases c with
    | NFin =>
      dsimp only at h
      exact (access_ok_zero_ret_only_not_unmodeled _ _ _ i m h).elim
    | NRst => exact (socket_pending_error_not_unmodeled _ _ _ _ _ _ i m h).elim
    | NTimedOut => exact (socket_pending_error_not_unmodeled _ _ _ _ _ _ i m h).elim
    | NByte _ =>
    dsimp only at h ⊢
    generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
    cases w1 with
    | none => exact (ret_only_not_unmodeled _ i m h).elim
    | some _ =>
    dsimp only at h ⊢
    generalize read_bytes_map i.in_wmem buf
      (len_word (net_take_z rx (rw_count_clamp count)).1) = w2 at h ⊢
    cases w2 with
    | none => rfl
    | some _ =>
    exfalso
    dsimp only at h
    rw [bind_choose_iff] at h
    obtain ⟨bs, -, hk⟩ := h
    simp only [bind_set_fds_iff, bind_emit_cases_iff] at hk
    rcases hk with ⟨y, m2, evs2, -, heq⟩ | ⟨hp, -⟩
    · cases heq
    · simp only [pure_iff, reduceCtorEq] at hp
  | FdFile p off =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => rfl
    | some data =>
    dsimp only at h ⊢
    generalize file_read data off (Z_to_bv 64 (rw_count_clamp count)) = bs at h ⊢
    generalize read_bytes_map i.in_wmem buf (len_word bs) = w at h ⊢
    cases w with
    | none =>
      dsimp only at h ⊢
      generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
      cases w1 with
      | none => exact (ret_only_not_unmodeled _ i m h).elim
      | some _ => rfl
    | some _ =>
    exfalso
    dsimp only at h
    simp only [bind_set_fds_iff, pure_iff, reduceCtorEq] at h
  | FdFileRW p off =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => rfl
    | some data =>
    dsimp only at h ⊢
    generalize file_read data off (Z_to_bv 64 (rw_count_clamp count)) = bs at h ⊢
    generalize read_bytes_map i.in_wmem buf (len_word bs) = w at h ⊢
    cases w with
    | none =>
      dsimp only at h ⊢
      generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
      cases w1 with
      | none => exact (ret_only_not_unmodeled _ i m h).elim
      | some _ => rfl
    | some _ =>
    exfalso
    dsimp only at h
    simp only [bind_set_fds_iff, pure_iff, reduceCtorEq] at h
  | FdPipe id w =>
    dsimp only at h ⊢
    cases w with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true => simp only [↓reduceIte]
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize w_is0 count = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (access_ok_zero_ret_only_not_unmodeled _ _ _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize pipe_lookup (m_pipes m) id = pl at h ⊢
    rcases pl with _ | ⟨_ | ⟨b, q0⟩, used⟩
    · rfl
    · dsimp only at h ⊢
      generalize pipe_end_live (m_fds m) id true = live at h ⊢
      cases live with
      | true => simp only [↓reduceIte]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        exact (access_ok_zero_ret_only_not_unmodeled _ _ _ i m h).elim
    · dsimp only at h ⊢
      generalize pipe_take (b :: q0) (rw_count_clamp count) = del at h ⊢
      generalize read_bytes_map i.in_wmem buf (len_word del) = w at h ⊢
      cases w with
      | none =>
        dsimp only at h ⊢
        generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
        cases w1 with
        | none => exact (ret_only_not_unmodeled _ i m h).elim
        | some _ => rfl
      | some _ =>
      exfalso
      dsimp only at h
      simp only [bind_set_pipes_iff, pure_iff, reduceCtorEq] at h

/-! ## The witness — `Checks/Witness/Fs/ReadWrite.v`

Mirrors the `read` half of `theories/LinuxProcessSem/Checks/Witness/Fs/ReadWrite.v`
at the header's baseline.  A witness is one outcome the spec admits, on
every input and model, so that `read_spec` is receptive; where the spec
chooses — the channel and the connected socket deliver any nonempty
prefix of what is left to say — the witness takes the shortest, one byte,
which needs only that the count is nonzero and the first byte can land,
both already decided by the gates in front of it.  Where the spec
computes, the witness is the spec's own answer. -/

/-- Rocq: `Checks.Witness.Fs.ReadWrite.read_urandom_witness`. -/
def read_urandom_witness (buf count : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  if w_is0 count then ret_outcome (Z_to_bv 64 0) m
  else
    match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
    | none => ret_outcome (errno_ret EFAULT) m
    | some _ =>
        let r := stream_take_z (m_urandom m) (rw_count_clamp count)
        if !((r.1.length : Int) = rw_count_clamp count) then Unmodeled
        else
          match read_bytes_map i.in_wmem buf (len_word r.1) with
          | none => Unmodeled
          | some _ => Ok (mkEffect (len_word r.1) [(buf, r.1)] []) (with_urandom r.2 m) []

/-- Rocq: `Checks.Witness.Fs.ReadWrite.read_urandom_witness_ok`. -/
theorem read_urandom_witness_ok (buf count : word) (i : SyscallInput) (m : Model) :
    read_urandom buf count i m i m (read_urandom_witness buf count i m) := by
  unfold read_urandom read_urandom_witness
  generalize w_is0 count = b0
  cases b0 with
  | true =>
    simp only [↓reduceIte]
    exact pure_ok _ i _
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1
  cases w1 with
  | none => exact pure_ok _ i _
  | some _ =>
  dsimp only
  generalize stream_take_z (m_urandom m) (rw_count_clamp count) = r
  generalize decide ((r.1.length : Int) = rw_count_clamp count) = d
  cases d with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  generalize read_bytes_map i.in_wmem buf (len_word r.1) = w2
  cases w2 with
  | none => exact unmodeled_intro i m
  | some _ => exact (bind_set_urandom_iff _ _ i m _).mpr (pure_ok _ i _)

/-- Rocq: `Checks.Witness.Fs.ReadWrite.read_witness`.  The Rocq `ICons b s'`
and `NCons b rest` arms are the `some (b, s')` of `uncons` and the
`.NByte b` head of the script, the remainder of the latter being what
`net_take rx 1` leaves — the term the spec's `set_fds` names for a
one-byte delivery.  The `FdFileA` arm is -EBADF, as for `FdFileW`; the
`FdFileRW` arm is the `FdFile` arm word for word, with the entry written
back under `FdFileRW`. -/
def read_witness (fd buf count : word) (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some (.FdFileW _ _) => ret_outcome (errno_ret EBADF) m
  | some (.FdFileA _ _) => ret_outcome (errno_ret EBADF) m
  | some (.FdChannel ch) =>
      if !w_is0 ch then ret_outcome (errno_ret EBADF) m
      else if !access_okb buf (bv_unsigned count) then ret_outcome (errno_ret EFAULT) m
      else if w_is0 count then ret_outcome (Z_to_bv 64 0) m
      else
        match (m_stdin m).uncons with
        | none => ret_outcome (Z_to_bv 64 0) m
        | some (b, s') =>
          match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
          | none => ret_outcome (errno_ret EFAULT) m
          | some _ =>
            match read_bytes_map i.in_wmem buf
                    (len_word (stream_take_z (m_stdin m) (rw_count_clamp count)).1) with
            | none => Unmodeled
            | some _ =>
                Ok (mkEffect (Z_to_bv 64 1) [(buf, [b])] []) (with_stdin s' m) [ReadEv ch b]
  | some (.FdDevNull rd _) =>
      if !rd then ret_outcome (errno_ret EBADF) m
      else access_ok_zero_witness buf count m (ret_outcome (Z_to_bv 64 0) m)
  | some .FdUrandom =>
      if !access_okb buf (bv_unsigned count) then ret_outcome (errno_ret EFAULT) m
      else read_urandom_witness buf count i m
  | some .FdDir =>
      if !access_okb buf (bv_unsigned count) then ret_outcome (errno_ret EFAULT) m
      else ret_outcome (errno_ret EISDIR) m
  | some (.FdSocket sk) =>
      if !modeled_rw_range buf count then Unmodeled
      else if w_is0 count then access_ok_zero_witness buf count m (ret_outcome (Z_to_bv 64 0) m)
      else
        match sk with
        | .SkConnected peer ch rx =>
            match rx.cell_at 0 with
            | .NFin => access_ok_zero_witness buf count m (ret_outcome (Z_to_bv 64 0) m)
            | .NRst =>
                access_ok_zero_witness buf count m
                  (ret_outcome (errno_ret ECONNRESET)
                     (with_fds (fd_insert (m_fds m) fd (.FdSocket (.SkReset peer ch))) m))
            | .NTimedOut =>
                access_ok_zero_witness buf count m
                  (ret_outcome (errno_ret ETIMEDOUT)
                     (with_fds (fd_insert (m_fds m) fd (.FdSocket (.SkReset peer ch))) m))
            | .NByte b =>
                match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
                | none => ret_outcome (errno_ret EFAULT) m
                | some _ =>
                  match read_bytes_map i.in_wmem buf
                          (len_word (net_take_z rx (rw_count_clamp count)).1) with
                  | none => Unmodeled
                  | some _ =>
                      Ok (mkEffect (Z_to_bv 64 1) [(buf, [b])] [])
                         (with_fds (fd_insert (m_fds m) fd
                            (.FdSocket (.SkConnected peer ch (net_take rx 1).2))) m)
                         [ReadEv ch b]
        | .SkReset _ _ => access_ok_zero_witness buf count m (ret_outcome (Z_to_bv 64 0) m)
        | .SkFresh | .SkBound | .SkListening =>
            access_ok_zero_witness buf count m (ret_outcome (errno_ret ENOTCONN) m)
  | some (.FdFile p off) =>
      if !access_okb buf (bv_unsigned count) then ret_outcome (errno_ret EFAULT) m
      else
        match fs_lookup (m_fs m) p with
        | none => Unmodeled
        | some data =>
          let bs := file_read data off (Z_to_bv 64 (rw_count_clamp count))
          match read_bytes_map i.in_wmem buf (len_word bs) with
          | none =>
              match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
              | none => ret_outcome (errno_ret EFAULT) m
              | some _ => Unmodeled
          | some _ =>
              Ok (mkEffect (len_word bs) (delivered_writes buf bs) [])
                 (with_fds (fd_insert (m_fds m) fd (.FdFile p (off + len_word bs))) m) []
  | some (.FdFileRW p off) =>
      if !access_okb buf (bv_unsigned count) then ret_outcome (errno_ret EFAULT) m
      else
        match fs_lookup (m_fs m) p with
        | none => Unmodeled
        | some data =>
          let bs := file_read data off (Z_to_bv 64 (rw_count_clamp count))
          match read_bytes_map i.in_wmem buf (len_word bs) with
          | none =>
              match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
              | none => ret_outcome (errno_ret EFAULT) m
              | some _ => Unmodeled
          | some _ =>
              Ok (mkEffect (len_word bs) (delivered_writes buf bs) [])
                 (with_fds (fd_insert (m_fds m) fd (.FdFileRW p (off + len_word bs))) m) []
  | some (.FdPipe id w) =>
      if w then ret_outcome (errno_ret EBADF) m
      else if !modeled_rw_range buf count then Unmodeled
      else if w_is0 count then access_ok_zero_witness buf count m (ret_outcome (Z_to_bv 64 0) m)
      else
        match pipe_lookup (m_pipes m) id with
        | none => Unmodeled
        | some ([], _) =>
            if pipe_end_live (m_fds m) id true then Unmodeled
            else access_ok_zero_witness buf count m (ret_outcome (Z_to_bv 64 0) m)
        | some (q@(_ :: _), used) =>
            let del := pipe_take q (rw_count_clamp count)
            match read_bytes_map i.in_wmem buf (len_word del) with
            | none =>
                match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
                | none => ret_outcome (errno_ret EFAULT) m
                | some _ => Unmodeled
            | some _ =>
                Ok (mkEffect (len_word del) (delivered_writes buf del) [])
                   (with_pipes (pipe_insert (m_pipes m) id (pipe_consume (q, used) del.length)) m)
                   []

/-! The two range-verdict shapes the witness meets, once each. -/

/-- `access_ok_zero_witness` over a `ret_outcome` is a run of `access_ok_zero`
over the matching `ret_only`. -/
theorem access_ok_zero_witness_ret (buf count r : word) (i : SyscallInput) (m : Model) :
    access_ok_zero buf count (ret_only r) i m
      (access_ok_zero_witness buf count m (ret_outcome r m)) := by
  unfold access_ok_zero access_ok_zero_witness
  generalize access_okb buf (bv_unsigned count) = ok
  cases ok with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact pure_ok _ i _
  | true =>
    simp only [↓reduceIte]
    exact pure_ok _ i _

/-- …and over the pending-error outcome, a run of `socket_pending_error`. -/
theorem access_ok_zero_witness_pending (e : Int) (fd : word) (peer : PeerAddr)
    (ch buf count : word) (i : SyscallInput) (m : Model) :
    socket_pending_error e fd peer ch buf count i m i m
      (access_ok_zero_witness buf count m
        (ret_outcome (errno_ret e)
           (with_fds (fd_insert (m_fds m) fd (.FdSocket (.SkReset peer ch))) m))) := by
  unfold socket_pending_error access_ok_zero access_ok_zero_witness
  generalize access_okb buf (bv_unsigned count) = ok
  cases ok with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact pure_ok _ i _
  | true =>
    simp only [↓reduceIte]
    exact (bind_set_fds_iff _ _ i m _).mpr (pure_ok _ i _)

/-- Rocq: `Checks.Witness.Fs.ReadWrite.read_witness_ok`. -/
theorem read_witness_ok (fd buf count : word) (i : SyscallInput) (m : Model) :
    read_spec fd buf count i m (read_witness fd buf count i m) := by
  unfold read_spec read_witness
  rw [bind_input_iff, bind_get_model_iff]
  generalize fd_lookup (m_fds m) fd = r
  cases r with
  | none => exact pure_ok _ i _
  | some e =>
  cases e with
  | FdFileW _ _ => exact pure_ok _ i _
  | FdFileA _ _ => exact pure_ok _ i _
  | FdChannel ch =>
    dsimp only
    generalize (!w_is0 ch) = b0
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize (!access_okb buf (bv_unsigned count)) = b1
    cases b1 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize hc : w_is0 count = b2
    cases b2 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases hu : (m_stdin m).uncons with
    | none => exact pure_ok _ i _
    | some u =>
    obtain ⟨b, s'⟩ := u
    dsimp only
    cases hw1 : read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
    | none => exact pure_ok _ i _
    | some _ =>
    dsimp only
    generalize read_bytes_map i.in_wmem buf
      (len_word (stream_take_z (m_stdin m) (rw_count_clamp count)).1) = w2
    cases w2 with
    | none => exact unmodeled_intro i m
    | some _ =>
    dsimp only
    have hst := stream_take_one_of_uncons _ _ _ hu
    rw [bind_choose_iff]
    refine ⟨[b], ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · exact Int.le_refl _
    · exact one_le_rw_count_clamp count hc
    · show (stream_take (m_stdin m) 1).1 = [b]
      rw [hst]
    · show read_bytes_map i.in_wmem buf (Z_to_bv 64 1) ≠ none
      rw [hw1]
      exact Option.some_ne_none _
    · show (set_stdin (stream_take (m_stdin m) 1).2 ;;
            emit (List.map (ReadEv ch) [b]) ;;
            Monad.pure (mkEffect (len_word [b]) [(buf, [b])] [])) i m
             (Ok (mkEffect (Z_to_bv 64 1) [(buf, [b])] []) (with_stdin s' m) [ReadEv ch b])
      rw [hst]
      exact (bind_set_stdin_iff _ _ i m _).mpr (emit_pure_ok _ _ i _)
  | FdDevNull rd wr =>
    dsimp only
    cases rd with
    | false =>
      simp only [Bool.not_false, ↓reduceIte]
      exact pure_ok _ i _
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      unfold access_ok_zero_witness
      generalize access_okb buf (bv_unsigned count) = ok
      cases ok with
      | false =>
        simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
        exact pure_ok _ i _
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact pure_ok _ i _
  | FdUrandom =>
    dsimp only
    generalize (!access_okb buf (bv_unsigned count)) = b0
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact read_urandom_witness_ok buf count i m
  | FdDir =>
    dsimp only
    generalize (!access_okb buf (bv_unsigned count)) = b0
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact pure_ok _ i _
  | FdSocket sk =>
    dsimp only
    generalize (!modeled_rw_range buf count) = b0
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize hc : w_is0 count = b1
    cases b1 with
    | true =>
      simp only [↓reduceIte]
      exact access_ok_zero_witness_ret _ _ _ i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases sk with
    | SkFresh => exact access_ok_zero_witness_ret _ _ _ i m
    | SkBound => exact access_ok_zero_witness_ret _ _ _ i m
    | SkListening => exact access_ok_zero_witness_ret _ _ _ i m
    | SkReset _ _ => exact access_ok_zero_witness_ret _ _ _ i m
    | SkConnected peer ch rx =>
    dsimp only
    cases hcell : rx.cell_at 0 with
    | NFin => exact access_ok_zero_witness_ret _ _ _ i m
    | NRst => exact access_ok_zero_witness_pending _ _ _ _ _ _ i m
    | NTimedOut => exact access_ok_zero_witness_pending _ _ _ _ _ _ i m
    | NByte b =>
    dsimp only
    cases hw1 : read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
    | none => exact pure_ok _ i _
    | some _ =>
    dsimp only
    generalize read_bytes_map i.in_wmem buf
      (len_word (net_take_z rx (rw_count_clamp count)).1) = w2
    cases w2 with
    | none => exact unmodeled_intro i m
    | some _ =>
    dsimp only
    have hnt := net_take_one_bytes_of_head _ _ hcell
    rw [bind_choose_iff]
    refine ⟨[b], ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · exact Int.le_refl _
    · exact one_le_rw_count_clamp count hc
    · show (net_take rx 1).1 = [b]
      exact hnt
    · show read_bytes_map i.in_wmem buf (Z_to_bv 64 1) ≠ none
      rw [hw1]
      exact Option.some_ne_none _
    · show (set_fds (fd_insert (m_fds m) fd
              (.FdSocket (.SkConnected peer ch (net_take rx 1).2))) ;;
            emit (List.map (ReadEv ch) [b]) ;;
            Monad.pure (mkEffect (len_word [b]) [(buf, [b])] [])) i m
             (Ok (mkEffect (Z_to_bv 64 1) [(buf, [b])] [])
               (with_fds (fd_insert (m_fds m) fd
                  (.FdSocket (.SkConnected peer ch (net_take rx 1).2))) m)
               [ReadEv ch b])
      exact (bind_set_fds_iff _ _ i m _).mpr (emit_pure_ok _ _ i _)
  | FdFile p off =>
    dsimp only
    generalize (!access_okb buf (bv_unsigned count)) = b0
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize fs_lookup (m_fs m) p = fl
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only
    generalize file_read data off (Z_to_bv 64 (rw_count_clamp count)) = bs
    generalize read_bytes_map i.in_wmem buf (len_word bs) = w
    cases w with
    | none =>
      dsimp only
      generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1
      cases w1 with
      | none => exact pure_ok _ i _
      | some _ => exact unmodeled_intro i m
    | some _ =>
      dsimp only
      exact (bind_set_fds_iff _ _ i m _).mpr (pure_ok _ i _)
  | FdFileRW p off =>
    dsimp only
    generalize (!access_okb buf (bv_unsigned count)) = b0
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize fs_lookup (m_fs m) p = fl
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only
    generalize file_read data off (Z_to_bv 64 (rw_count_clamp count)) = bs
    generalize read_bytes_map i.in_wmem buf (len_word bs) = w
    cases w with
    | none =>
      dsimp only
      generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1
      cases w1 with
      | none => exact pure_ok _ i _
      | some _ => exact unmodeled_intro i m
    | some _ =>
      dsimp only
      exact (bind_set_fds_iff _ _ i m _).mpr (pure_ok _ i _)
  | FdPipe id w =>
    dsimp only
    cases w with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize (!modeled_rw_range buf count) = b0
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize w_is0 count = b1
    cases b1 with
    | true =>
      simp only [↓reduceIte]
      exact access_ok_zero_witness_ret _ _ _ i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize pipe_lookup (m_pipes m) id = pl
    rcases pl with _ | ⟨_ | ⟨b, q0⟩, used⟩
    · exact unmodeled_intro i m
    · dsimp only
      generalize pipe_end_live (m_fds m) id true = live
      cases live with
      | true =>
        simp only [↓reduceIte]
        exact unmodeled_intro i m
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact access_ok_zero_witness_ret _ _ _ i m
    · dsimp only
      generalize pipe_take (b :: q0) (rw_count_clamp count) = del
      generalize read_bytes_map i.in_wmem buf (len_word del) = w
      cases w with
      | none =>
        dsimp only
        generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1
        cases w1 with
        | none => exact pure_ok _ i _
        | some _ => exact unmodeled_intro i m
      | some _ =>
        dsimp only
        exact (bind_set_pipes_iff _ _ i m _).mpr (pure_ok _ i _)

-- lean-port sentinel: ticket C-Fs-ReadWrite-write appends below this line

/-! ## write (64) — the checker

Mirrors the `write` half of `theories/LinuxProcessSem/Checks/Sys/Fs/ReadWrite.v`
at the header's baseline, ported by ticket C-Fs-ReadWrite-write.  The arms
are Rocq's, in Rocq's order.

The channel arm judges the claimed return where `write_spec` chooses the
delivered prefix: the return names the prefix, so `1 ≤ ret ≤ length bs`
and a ledger of exactly `(buf, ret)` accept precisely the `choose` the
spec makes.  The spec's bound is `rw_count_clamp count` rather than
`length bs`; the two agree because `write_source` reads at most the
clamped count (`Uaccess.write_source_length_le`) and the prefix must be
one of `bs`.  Rocq nests the ledger test under the range test so that
`vm_compute`, being call by value, never converts an errno-sized `ret` to
a unary `nat`; Lean's `Nat` is not unary and `&&` does not evaluate its
right operand first, so nothing here depends on the nesting, which is
kept only so the two checkers read alike. -/

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_write`.  `write_spec` as an
acceptor, arm for arm, in the kernel's order; the argument for each
decision is on the spec's docstring.  The channel's delivery is judged
against the claimed return (section header); a file or a pipe delivers
what the model computes, so its accepted effect is the one
`check_ret_only_copyins` rebuilds from the readable prefix. -/
def check_write (i : SyscallInput) (fd buf count : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdFile _ _) => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdChannel ch) =>
      if w_is0 ch then check_ret_only eff (errno_ret EBADF) m []
      else if !modeled_rw_range buf count then CheckUnmodeled
      else if w_is0 count then
        check_access_ok_zero buf count eff m (check_ret_only eff (Z_to_bv 64 0) m [])
      else
        let bs := write_source i.in_mem buf count
        if bs.length == 0 then check_ret_only eff (errno_ret EFAULT) m []
        else
          match eff with
          | .mkEffectU ret [] [] [] [] copyins =>
              if decide (1 ≤ bv_unsigned ret) && decide (bv_unsigned ret ≤ (bs.length : Int)) then
                if access_ranges_eqb copyins [(buf, (bv_unsigned ret).toNat)]
                then CheckOk m (List.map (WriteEv ch) (bs.take (bv_unsigned ret).toNat))
                else CheckReject
              else CheckReject
          | _ => CheckReject
  | some .FdDir => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdSocket _) => CheckUnmodeled
  | some (.FdFileW p off) =>
      if !modeled_rw_range buf count then CheckUnmodeled
      else
        let bs := write_source i.in_mem buf count
        if !w_is0 count && bs.length == 0 then check_ret_only eff (errno_ret EFAULT) m []
        else
          let k :=
            match fs_lookup (m_fs m) p with
            | none => CheckUnmodeled
            | some data =>
                if !modeled_file_gap data off bs then CheckUnmodeled
                else
                  let m' := with_fds (fd_insert (m_fds m) fd (.FdFileW p (off + len_word bs)))
                              (with_fs (fs_set (m_fs m) p (file_write data off bs)) m)
                  if w_is0 count then check_ret_only eff (len_word bs) m' []
                  else check_ret_only_copyins [(buf, bs.length)] eff (len_word bs) m' []
          if w_is0 count then check_access_ok_zero buf count eff m k else k
  | some (.FdFileRW p off) => -- the `FdFileW` arm above, on the O_RDWR kind
      if !modeled_rw_range buf count then CheckUnmodeled
      else
        let bs := write_source i.in_mem buf count
        if !w_is0 count && bs.length == 0 then check_ret_only eff (errno_ret EFAULT) m []
        else
          let k :=
            match fs_lookup (m_fs m) p with
            | none => CheckUnmodeled
            | some data =>
                if !modeled_file_gap data off bs then CheckUnmodeled
                else
                  let m' := with_fds (fd_insert (m_fds m) fd (.FdFileRW p (off + len_word bs)))
                              (with_fs (fs_set (m_fs m) p (file_write data off bs)) m)
                  if w_is0 count then check_ret_only eff (len_word bs) m' []
                  else check_ret_only_copyins [(buf, bs.length)] eff (len_word bs) m' []
          if w_is0 count then check_access_ok_zero buf count eff m k else k
  | some (.FdFileA p off) =>
      -- the arm above with the bytes placed at end-of-file, no `modeled_file_gap`
      -- guard, and `rw_verify_area`'s test on the fd's real position (`write_spec`)
      if !modeled_rw_range buf count then CheckUnmodeled
      else if !access_okb buf (bv_unsigned count) then check_ret_only eff (errno_ret EFAULT) m []
      else if rw_pos_einvalb off (bv_unsigned count) then
        check_ret_only eff (errno_ret EINVAL) m []
      else
        let bs := write_source i.in_mem buf count
        if !w_is0 count && bs.length == 0 then check_ret_only eff (errno_ret EFAULT) m []
        else
          let k :=
            match fs_lookup (m_fs m) p with
            | none => CheckUnmodeled
            | some data =>
                let m' :=
                  with_fds (fd_insert (m_fds m) fd (.FdFileA p (append_new_pos data bs off)))
                    (with_fs (fs_set (m_fs m) p (file_write data (len_word data) bs)) m)
                if w_is0 count then check_ret_only eff (len_word bs) m' []
                else check_ret_only_copyins [(buf, bs.length)] eff (len_word bs) m' []
          if w_is0 count then check_access_ok_zero buf count eff m k else k
  | some .FdUrandom => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdDevNull _ wr) =>
      if !wr then check_ret_only eff (errno_ret EBADF) m []
      else if !modeled_rw_range buf count then CheckUnmodeled
      else
        check_access_ok_zero buf count eff m
          (check_ret_only eff (Z_to_bv 64 (rw_count_clamp count)) m [])
  | some (.FdPipe id w) =>
      if !w then check_ret_only eff (errno_ret EBADF) m []
      else if !modeled_rw_range buf count then CheckUnmodeled
      else if w_is0 count then
        check_access_ok_zero buf count eff m (check_ret_only eff (Z_to_bv 64 0) m [])
      else if !pipe_end_live (m_fds m) id false then CheckUnmodeled
      else
        match pipe_lookup (m_pipes m) id with
        | none => CheckUnmodeled
        | some st =>
            if !pipe_write_room st (bv_unsigned count) then CheckUnmodeled
            else
              let bs := write_source i.in_mem buf count
              if !(bs.length == word_to_nat count) then CheckUnmodeled
              else
                check_ret_only_copyins [(buf, bs.length)] eff count
                  (with_pipes (pipe_insert (m_pipes m) id (pipe_append st bs)) m) []

/-! ### The write acceptor against `write_spec`

The same lockstep as `read`'s.  The channel delivery is the one leaf
that is not a constructor clash or a shared lemma: soundness picks the
prefix the claimed return names and shows it satisfies the spec's
`choose`, completeness replays the prefix the spec chose through the
checker's range and ledger tests. -/

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_write_sound_ok`. -/
theorem check_write_sound_ok (i : SyscallInput) (fd buf count : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_write i fd buf count eff m = CheckOk m' evs) :
    write_spec fd buf count i m (Ok eff m' evs) := by
  unfold check_write at h
  unfold write_spec write_range_gate write_file_tail write_ledger
  rw [bind_input_iff, bind_get_model_iff]
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact ret_only_sound _ _ _ _ _ i h
  | some e =>
  cases e with
  | FdFile _ _ => exact ret_only_sound _ _ _ _ _ i h
  | FdChannel ch =>
    dsimp only at h ⊢
    generalize w_is0 ch = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!modeled_rw_range buf count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize w_is0 count = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact check_access_ok_zero_ret_only_sound _ _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    have hbs := write_source_length_le i.in_mem buf count
    generalize write_source i.in_mem buf count = bs at h hbs ⊢
    generalize (bs.length == 0) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    split at h
    · rename_i ret copyins
      split at h
      · rename_i hg
        split at h
        · rename_i hreads
          obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
          obtain ⟨h1, h2⟩ := hg
          obtain rfl := (access_ranges_eqb_eq _ _).mp hreads
          have hr := word_unsigned_range ret
          have hlen := firstn_length_le_Z bs (bv_unsigned ret) hr.1 h2
          have hn : (bs.take (bv_unsigned ret).toNat).length = (bv_unsigned ret).toNat := by omega
          have hlw := len_word_firstn_ret ret bs ⟨hr.1, h2⟩
          rw [bind_choose_iff]
          refine ⟨bs.take (bv_unsigned ret).toNat, ⟨by omega, by omega, by rw [hn]⟩, ?_⟩
          rw [hn, hlw]
          exact witness_bind_ok_eq _ _ i m () m _ _ m [] _ (emit_ok _ i m)
            (record_copyins_ok_empty _ _ i m _ m [] rfl (pure_ok _ i m)) (List.append_nil _).symm
        · cases h
      · cases h
    · cases h
  | FdDir => exact ret_only_sound _ _ _ _ _ i h
  | FdSocket _ => cases h
  | FdFileW p off =>
    dsimp only at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (!w_is0 count && bs.length == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none =>
      dsimp only at h ⊢
      generalize w_is0 count = c at h ⊢
      cases c with
      | true =>
        simp only [↓reduceIte] at h ⊢
        ok_zero_cases h buf count
        · exact ret_only_sound _ _ _ _ _ i h
        · cases h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        cases h
    | some data =>
    dsimp only at h ⊢
    generalize (!modeled_file_gap data off bs) = g at h ⊢
    cases g with
    | true =>
      simp only [↓reduceIte] at h ⊢
      generalize w_is0 count = c at h ⊢
      cases c with
      | true =>
        simp only [↓reduceIte] at h ⊢
        ok_zero_cases h buf count
        · exact ret_only_sound _ _ _ _ _ i h
        · cases h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize w_is0 count = c at h ⊢
    cases c with
    | true =>
      simp only [↓reduceIte] at h ⊢
      ok_zero_cases h buf count
      · exact ret_only_sound _ _ _ _ _ i h
      · rw [bind_set_fs_iff, bind_set_fds_iff]
        exact ret_only_sound _ _ _ _ _ i h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      rw [bind_set_fs_iff, bind_set_fds_iff]
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
      exact record_copyins_ok_empty _ _ i _ _ _ _ rfl (pure_ok _ i _)
  | FdFileRW p off =>
    dsimp only at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (!w_is0 count && bs.length == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none =>
      dsimp only at h ⊢
      generalize w_is0 count = c at h ⊢
      cases c with
      | true =>
        simp only [↓reduceIte] at h ⊢
        ok_zero_cases h buf count
        · exact ret_only_sound _ _ _ _ _ i h
        · cases h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        cases h
    | some data =>
    dsimp only at h ⊢
    generalize (!modeled_file_gap data off bs) = g at h ⊢
    cases g with
    | true =>
      simp only [↓reduceIte] at h ⊢
      generalize w_is0 count = c at h ⊢
      cases c with
      | true =>
        simp only [↓reduceIte] at h ⊢
        ok_zero_cases h buf count
        · exact ret_only_sound _ _ _ _ _ i h
        · cases h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize w_is0 count = c at h ⊢
    cases c with
    | true =>
      simp only [↓reduceIte] at h ⊢
      ok_zero_cases h buf count
      · exact ret_only_sound _ _ _ _ _ i h
      · rw [bind_set_fs_iff, bind_set_fds_iff]
        exact ret_only_sound _ _ _ _ _ i h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      rw [bind_set_fs_iff, bind_set_fds_iff]
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
      exact record_copyins_ok_empty _ _ i _ _ _ _ rfl (pure_ok _ i _)
  | FdFileA p off =>
    dsimp only at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb off (bv_unsigned count) = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (!w_is0 count && bs.length == 0) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none =>
      dsimp only at h ⊢
      generalize w_is0 count = c at h ⊢
      cases c with
      | true =>
        simp only [↓reduceIte] at h ⊢
        ok_zero_cases h buf count
        · exact ret_only_sound _ _ _ _ _ i h
        · cases h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        cases h
    | some data =>
    dsimp only at h ⊢
    generalize w_is0 count = c at h ⊢
    cases c with
    | true =>
      simp only [↓reduceIte] at h ⊢
      ok_zero_cases h buf count
      · exact ret_only_sound _ _ _ _ _ i h
      · rw [bind_set_fs_iff, bind_set_fds_iff]
        exact ret_only_sound _ _ _ _ _ i h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      rw [bind_set_fs_iff, bind_set_fds_iff]
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
      exact record_copyins_ok_empty _ _ i _ _ _ _ rfl (pure_ok _ i _)
  | FdUrandom => exact ret_only_sound _ _ _ _ _ i h
  | FdDevNull rd wr =>
    dsimp only at h ⊢
    cases wr with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact check_access_ok_zero_ret_only_sound _ _ _ _ _ _ _ i h
  | FdPipe id w =>
    dsimp only at h ⊢
    cases w with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize w_is0 count = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact check_access_ok_zero_ret_only_sound _ _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!pipe_end_live (m_fds m) id false) = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize pipe_lookup (m_pipes m) id = pl at h ⊢
    cases pl with
    | none => cases h
    | some st =>
    dsimp only at h ⊢
    generalize (!pipe_write_room st (bv_unsigned count)) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (!(bs.length == word_to_nat count)) = b4 at h ⊢
    cases b4 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    rw [bind_set_pipes_iff]
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
    exact record_copyins_ok_empty _ _ i _ _ _ _ rfl (pure_ok _ i _)

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_write_sound_unmodeled`. -/
theorem check_write_sound_unmodeled (i : SyscallInput) (fd buf count : word)
    (eff : SyscallEffect) (m : Model) (h : check_write i fd buf count eff m = CheckUnmodeled) :
    write_spec fd buf count i m Unmodeled := by
  unfold check_write at h
  unfold write_spec write_range_gate write_file_tail write_ledger
  rw [bind_input_iff, bind_get_model_iff]
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | some e =>
  cases e with
  | FdFile _ _ => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | FdChannel ch =>
    dsimp only at h ⊢
    generalize w_is0 ch = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!modeled_rw_range buf count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize w_is0 count = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_access_ok_zero_ret_only_no_unmodeled _ _ _ _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (bs.length == 0) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
    exfalso
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · split at h
      · split at h <;> cases h
      · cases h
    · cases h
  | FdDir => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | FdSocket _ => exact unmodeled_intro i m
  | FdFileW p off =>
    dsimp only at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (!w_is0 count && bs.length == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none =>
      dsimp only at h ⊢
      generalize w_is0 count = c at h ⊢
      cases c with
      | true =>
        simp only [↓reduceIte] at h ⊢
        ok_zero_cases h buf count
        · exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
        · exact unmodeled_intro i m
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact unmodeled_intro i m
    | some data =>
    dsimp only at h ⊢
    generalize (!modeled_file_gap data off bs) = g at h ⊢
    cases g with
    | true =>
      simp only [↓reduceIte] at h ⊢
      generalize w_is0 count = c at h ⊢
      cases c with
      | true =>
        simp only [↓reduceIte] at h ⊢
        ok_zero_cases h buf count
        · exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
        · exact unmodeled_intro i m
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    generalize w_is0 count = c at h ⊢
    cases c with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_access_ok_zero_ret_only_no_unmodeled _ _ _ _ _ _ _)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)
  | FdFileRW p off =>
    dsimp only at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (!w_is0 count && bs.length == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none =>
      dsimp only at h ⊢
      generalize w_is0 count = c at h ⊢
      cases c with
      | true =>
        simp only [↓reduceIte] at h ⊢
        ok_zero_cases h buf count
        · exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
        · exact unmodeled_intro i m
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact unmodeled_intro i m
    | some data =>
    dsimp only at h ⊢
    generalize (!modeled_file_gap data off bs) = g at h ⊢
    cases g with
    | true =>
      simp only [↓reduceIte] at h ⊢
      generalize w_is0 count = c at h ⊢
      cases c with
      | true =>
        simp only [↓reduceIte] at h ⊢
        ok_zero_cases h buf count
        · exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
        · exact unmodeled_intro i m
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    generalize w_is0 count = c at h ⊢
    cases c with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_access_ok_zero_ret_only_no_unmodeled _ _ _ _ _ _ _)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)
  | FdFileA p off =>
    dsimp only at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb off (bv_unsigned count) = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (!w_is0 count && bs.length == 0) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none =>
      dsimp only at h ⊢
      generalize w_is0 count = c at h ⊢
      cases c with
      | true =>
        simp only [↓reduceIte] at h ⊢
        ok_zero_cases h buf count
        · exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
        · exact unmodeled_intro i m
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact unmodeled_intro i m
    | some data =>
    dsimp only at h ⊢
    generalize w_is0 count = c at h ⊢
    cases c with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_access_ok_zero_ret_only_no_unmodeled _ _ _ _ _ _ _)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)
  | FdUrandom => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | FdDevNull rd wr =>
    dsimp only at h ⊢
    cases wr with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact absurd h (check_access_ok_zero_ret_only_no_unmodeled _ _ _ _ _ _ _)
  | FdPipe id w =>
    dsimp only at h ⊢
    cases w with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize w_is0 count = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_access_ok_zero_ret_only_no_unmodeled _ _ _ _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!pipe_end_live (m_fds m) id false) = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize pipe_lookup (m_pipes m) id = pl at h ⊢
    cases pl with
    | none => exact unmodeled_intro i m
    | some st =>
    dsimp only at h ⊢
    generalize (!pipe_write_room st (bv_unsigned count)) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (!(bs.length == word_to_nat count)) = b4 at h ⊢
    cases b4 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_write_complete_ok`. -/
theorem check_write_complete_ok (i : SyscallInput) (fd buf count : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : write_spec fd buf count i m (Ok eff m' evs)) :
    check_write i fd buf count eff m = CheckOk m' evs := by
  unfold write_spec write_range_gate write_file_tail write_ledger at h
  unfold check_write
  rw [bind_input_iff, bind_get_model_iff] at h
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact ret_only_complete _ _ _ _ _ i h
  | some e =>
  cases e with
  | FdFile _ _ => exact ret_only_complete _ _ _ _ _ i h
  | FdChannel ch =>
    dsimp only at h ⊢
    generalize w_is0 ch = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!modeled_rw_range buf count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize w_is0 count = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact access_ok_zero_ret_only_complete _ _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    have hcl := rw_count_clamp_range count
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (bs.length == 0) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    rw [bind_choose_iff] at h
    obtain ⟨ds, ⟨h1, h2, h3⟩, hk⟩ := h
    rw [bind_emit_cases_iff] at hk
    rcases hk with ⟨y, m2, evs2, hr, heq⟩ | ⟨-, heq⟩
    · obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m2 evs2 hr
      simp only [ret_only, pure_iff, outcome.Ok.injEq] at hcore
      obtain ⟨rfl, rfl, rfl⟩ := hcore
      obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj heq
      have hsm : (ds.length : Int) < two_pow_64 := by
        unfold MAX_RW_COUNT at hcl
        unfold two_pow_64
        omega
      have hle : ds.length ≤ bs.length := by
        have hl := congrArg List.length h3
        rw [List.length_take] at hl
        omega
      have hle' : (ds.length : Int) ≤ (bs.length : Int) := by omega
      simp only [with_copyins, List.append_nil, len_word_unsigned ds hsm, decide_eq_true h1,
        decide_eq_true hle', Bool.and_self, ↓reduceIte, Int.toNat_natCast, ← h3,
        access_ranges_eqb_refl]
    · cases heq
  | FdDir => exact ret_only_complete _ _ _ _ _ i h
  | FdSocket _ => cases h
  | FdFileW p off =>
    dsimp only at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (!w_is0 count && bs.length == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none =>
      dsimp only at h ⊢
      generalize w_is0 count = c at h ⊢
      cases c with
      | true =>
        simp only [↓reduceIte] at h ⊢
        unfold access_ok_zero at h
        unfold check_access_ok_zero
        generalize access_okb buf (bv_unsigned count) = ok at h ⊢
        cases ok with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          exact ret_only_complete _ _ _ _ _ i h
        | true =>
          simp only [↓reduceIte] at h
          cases h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        cases h
    | some data =>
    dsimp only at h ⊢
    generalize (!modeled_file_gap data off bs) = g at h ⊢
    cases g with
    | true =>
      simp only [↓reduceIte] at h ⊢
      generalize w_is0 count = c at h ⊢
      cases c with
      | true =>
        simp only [↓reduceIte] at h ⊢
        unfold access_ok_zero at h
        unfold check_access_ok_zero
        generalize access_okb buf (bv_unsigned count) = ok at h ⊢
        cases ok with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          exact ret_only_complete _ _ _ _ _ i h
        | true =>
          simp only [↓reduceIte] at h
          cases h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize w_is0 count = c at h ⊢
    cases c with
    | true =>
      simp only [↓reduceIte] at h ⊢
      unfold access_ok_zero at h
      unfold check_access_ok_zero
      generalize access_okb buf (bv_unsigned count) = ok at h ⊢
      cases ok with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact ret_only_complete _ _ _ _ _ i h
      | true =>
        simp only [↓reduceIte] at h ⊢
        rw [bind_set_fs_iff, bind_set_fds_iff] at h
        exact ret_only_complete _ _ _ _ _ i h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      rw [bind_set_fs_iff, bind_set_fds_iff] at h
      obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i _ _ _ _ h
      simp only [ret_only, pure_iff, outcome.Ok.injEq] at hcore
      obtain ⟨rfl, rfl, rfl⟩ := hcore
      exact check_ret_only_copyins_refl _ _ _ _
  | FdFileRW p off =>
    dsimp only at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (!w_is0 count && bs.length == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none =>
      dsimp only at h ⊢
      generalize w_is0 count = c at h ⊢
      cases c with
      | true =>
        simp only [↓reduceIte] at h ⊢
        unfold access_ok_zero at h
        unfold check_access_ok_zero
        generalize access_okb buf (bv_unsigned count) = ok at h ⊢
        cases ok with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          exact ret_only_complete _ _ _ _ _ i h
        | true =>
          simp only [↓reduceIte] at h
          cases h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        cases h
    | some data =>
    dsimp only at h ⊢
    generalize (!modeled_file_gap data off bs) = g at h ⊢
    cases g with
    | true =>
      simp only [↓reduceIte] at h ⊢
      generalize w_is0 count = c at h ⊢
      cases c with
      | true =>
        simp only [↓reduceIte] at h ⊢
        unfold access_ok_zero at h
        unfold check_access_ok_zero
        generalize access_okb buf (bv_unsigned count) = ok at h ⊢
        cases ok with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          exact ret_only_complete _ _ _ _ _ i h
        | true =>
          simp only [↓reduceIte] at h
          cases h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize w_is0 count = c at h ⊢
    cases c with
    | true =>
      simp only [↓reduceIte] at h ⊢
      unfold access_ok_zero at h
      unfold check_access_ok_zero
      generalize access_okb buf (bv_unsigned count) = ok at h ⊢
      cases ok with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact ret_only_complete _ _ _ _ _ i h
      | true =>
        simp only [↓reduceIte] at h ⊢
        rw [bind_set_fs_iff, bind_set_fds_iff] at h
        exact ret_only_complete _ _ _ _ _ i h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      rw [bind_set_fs_iff, bind_set_fds_iff] at h
      obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i _ _ _ _ h
      simp only [ret_only, pure_iff, outcome.Ok.injEq] at hcore
      obtain ⟨rfl, rfl, rfl⟩ := hcore
      exact check_ret_only_copyins_refl _ _ _ _
  | FdFileA p off =>
    dsimp only at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb off (bv_unsigned count) = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (!w_is0 count && bs.length == 0) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none =>
      dsimp only at h ⊢
      generalize w_is0 count = c at h ⊢
      cases c with
      | true =>
        simp only [↓reduceIte] at h ⊢
        unfold access_ok_zero at h
        unfold check_access_ok_zero
        generalize access_okb buf (bv_unsigned count) = ok at h ⊢
        cases ok with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          exact ret_only_complete _ _ _ _ _ i h
        | true =>
          simp only [↓reduceIte] at h
          cases h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        cases h
    | some data =>
    dsimp only at h ⊢
    generalize w_is0 count = c at h ⊢
    cases c with
    | true =>
      simp only [↓reduceIte] at h ⊢
      unfold access_ok_zero at h
      unfold check_access_ok_zero
      generalize access_okb buf (bv_unsigned count) = ok at h ⊢
      cases ok with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact ret_only_complete _ _ _ _ _ i h
      | true =>
        simp only [↓reduceIte] at h ⊢
        rw [bind_set_fs_iff, bind_set_fds_iff] at h
        exact ret_only_complete _ _ _ _ _ i h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      rw [bind_set_fs_iff, bind_set_fds_iff] at h
      obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i _ _ _ _ h
      simp only [ret_only, pure_iff, outcome.Ok.injEq] at hcore
      obtain ⟨rfl, rfl, rfl⟩ := hcore
      exact check_ret_only_copyins_refl _ _ _ _
  | FdUrandom => exact ret_only_complete _ _ _ _ _ i h
  | FdDevNull rd wr =>
    dsimp only at h ⊢
    cases wr with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact access_ok_zero_ret_only_complete _ _ _ _ _ _ _ i h
  | FdPipe id w =>
    dsimp only at h ⊢
    cases w with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize w_is0 count = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact access_ok_zero_ret_only_complete _ _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!pipe_end_live (m_fds m) id false) = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize pipe_lookup (m_pipes m) id = pl at h ⊢
    cases pl with
    | none => cases h
    | some st =>
    dsimp only at h ⊢
    generalize (!pipe_write_room st (bv_unsigned count)) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (!(bs.length == word_to_nat count)) = b4 at h ⊢
    cases b4 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    rw [bind_set_pipes_iff] at h
    obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i _ _ _ _ h
    simp only [ret_only, pure_iff, outcome.Ok.injEq] at hcore
    obtain ⟨rfl, rfl, rfl⟩ := hcore
    exact check_ret_only_copyins_refl _ _ _ _

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_write_complete_unmodeled`. -/
theorem check_write_complete_unmodeled (i : SyscallInput) (fd buf count : word)
    (eff : SyscallEffect) (m : Model) (h : write_spec fd buf count i m Unmodeled) :
    check_write i fd buf count eff m = CheckUnmodeled := by
  unfold write_spec write_range_gate write_file_tail write_ledger at h
  unfold check_write
  rw [bind_input_iff, bind_get_model_iff] at h
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact (ret_only_not_unmodeled _ i m h).elim
  | some e =>
  cases e with
  | FdFile _ _ => exact (ret_only_not_unmodeled _ i m h).elim
  | FdChannel ch =>
    dsimp only at h ⊢
    generalize w_is0 ch = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!modeled_rw_range buf count) = b1 at h ⊢
    cases b1 with
    | true => simp only [↓reduceIte]
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize w_is0 count = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h
      exact (access_ok_zero_ret_only_not_unmodeled _ _ _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (bs.length == 0) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    exfalso
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    rw [bind_choose_iff] at h
    obtain ⟨ds, -, hk⟩ := h
    rw [bind_emit_cases_iff] at hk
    rcases hk with ⟨_, _, _, _, heq⟩ | ⟨hr, -⟩
    · cases heq
    · exact ret_only_not_unmodeled _ i m (record_copyins_unmodeled_inv _ _ i m hr)
  | FdDir => exact (ret_only_not_unmodeled _ i m h).elim
  | FdSocket _ => rfl
  | FdFileW p off =>
    dsimp only at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true => simp only [↓reduceIte]
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (!w_is0 count && bs.length == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none =>
      dsimp only at h ⊢
      generalize w_is0 count = c at h ⊢
      cases c with
      | true =>
        simp only [↓reduceIte] at h ⊢
        unfold access_ok_zero at h
        unfold check_access_ok_zero
        generalize access_okb buf (bv_unsigned count) = ok at h ⊢
        cases ok with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          exact (ret_only_not_unmodeled _ i m h).elim
        | true => simp only [↓reduceIte]
      | false => simp only [Bool.false_eq_true, ↓reduceIte]
    | some data =>
    dsimp only at h ⊢
    generalize (!modeled_file_gap data off bs) = g at h ⊢
    cases g with
    | true =>
      simp only [↓reduceIte] at h ⊢
      generalize w_is0 count = c at h ⊢
      cases c with
      | true =>
        simp only [↓reduceIte] at h ⊢
        unfold access_ok_zero at h
        unfold check_access_ok_zero
        generalize access_okb buf (bv_unsigned count) = ok at h ⊢
        cases ok with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          exact (ret_only_not_unmodeled _ i m h).elim
        | true => simp only [↓reduceIte]
      | false => simp only [Bool.false_eq_true, ↓reduceIte]
    | false =>
    exfalso
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    generalize w_is0 count = c at h
    cases c with
    | true =>
      simp only [↓reduceIte] at h
      unfold access_ok_zero at h
      generalize access_okb buf (bv_unsigned count) = ok at h
      cases ok with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        exact ret_only_not_unmodeled _ i m h
      | true =>
        simp only [↓reduceIte] at h
        rw [bind_set_fs_iff, bind_set_fds_iff] at h
        exact ret_only_not_unmodeled _ i _ h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      rw [bind_set_fs_iff, bind_set_fds_iff] at h
      exact ret_only_not_unmodeled _ i _ (record_copyins_unmodeled_inv _ _ i _ h)
  | FdFileRW p off =>
    dsimp only at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true => simp only [↓reduceIte]
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (!w_is0 count && bs.length == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none =>
      dsimp only at h ⊢
      generalize w_is0 count = c at h ⊢
      cases c with
      | true =>
        simp only [↓reduceIte] at h ⊢
        unfold access_ok_zero at h
        unfold check_access_ok_zero
        generalize access_okb buf (bv_unsigned count) = ok at h ⊢
        cases ok with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          exact (ret_only_not_unmodeled _ i m h).elim
        | true => simp only [↓reduceIte]
      | false => simp only [Bool.false_eq_true, ↓reduceIte]
    | some data =>
    dsimp only at h ⊢
    generalize (!modeled_file_gap data off bs) = g at h ⊢
    cases g with
    | true =>
      simp only [↓reduceIte] at h ⊢
      generalize w_is0 count = c at h ⊢
      cases c with
      | true =>
        simp only [↓reduceIte] at h ⊢
        unfold access_ok_zero at h
        unfold check_access_ok_zero
        generalize access_okb buf (bv_unsigned count) = ok at h ⊢
        cases ok with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          exact (ret_only_not_unmodeled _ i m h).elim
        | true => simp only [↓reduceIte]
      | false => simp only [Bool.false_eq_true, ↓reduceIte]
    | false =>
    exfalso
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    generalize w_is0 count = c at h
    cases c with
    | true =>
      simp only [↓reduceIte] at h
      unfold access_ok_zero at h
      generalize access_okb buf (bv_unsigned count) = ok at h
      cases ok with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        exact ret_only_not_unmodeled _ i m h
      | true =>
        simp only [↓reduceIte] at h
        rw [bind_set_fs_iff, bind_set_fds_iff] at h
        exact ret_only_not_unmodeled _ i _ h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      rw [bind_set_fs_iff, bind_set_fds_iff] at h
      exact ret_only_not_unmodeled _ i _ (record_copyins_unmodeled_inv _ _ i _ h)
  | FdFileA p off =>
    dsimp only at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true => simp only [↓reduceIte]
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb off (bv_unsigned count) = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (!w_is0 count && bs.length == 0) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none =>
      dsimp only at h ⊢
      generalize w_is0 count = c at h ⊢
      cases c with
      | true =>
        simp only [↓reduceIte] at h ⊢
        unfold access_ok_zero at h
        unfold check_access_ok_zero
        generalize access_okb buf (bv_unsigned count) = ok at h ⊢
        cases ok with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          exact (ret_only_not_unmodeled _ i m h).elim
        | true => simp only [↓reduceIte]
      | false => simp only [Bool.false_eq_true, ↓reduceIte]
    | some data =>
    exfalso
    dsimp only at h
    generalize w_is0 count = c at h
    cases c with
    | true =>
      simp only [↓reduceIte] at h
      unfold access_ok_zero at h
      generalize access_okb buf (bv_unsigned count) = ok at h
      cases ok with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        exact ret_only_not_unmodeled _ i m h
      | true =>
        simp only [↓reduceIte] at h
        rw [bind_set_fs_iff, bind_set_fds_iff] at h
        exact ret_only_not_unmodeled _ i _ h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      rw [bind_set_fs_iff, bind_set_fds_iff] at h
      exact ret_only_not_unmodeled _ i _ (record_copyins_unmodeled_inv _ _ i _ h)
  | FdUrandom => exact (ret_only_not_unmodeled _ i m h).elim
  | FdDevNull rd wr =>
    dsimp only at h ⊢
    cases wr with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true => simp only [↓reduceIte]
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact (access_ok_zero_ret_only_not_unmodeled _ _ _ i m h).elim
  | FdPipe id w =>
    dsimp only at h ⊢
    cases w with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!modeled_rw_range buf count) = b0 at h ⊢
    cases b0 with
    | true => simp only [↓reduceIte]
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize w_is0 count = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (access_ok_zero_ret_only_not_unmodeled _ _ _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!pipe_end_live (m_fds m) id false) = b2 at h ⊢
    cases b2 with
    | true => simp only [↓reduceIte]
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize pipe_lookup (m_pipes m) id = pl at h ⊢
    cases pl with
    | none => rfl
    | some st =>
    dsimp only at h ⊢
    generalize (!pipe_write_room st (bv_unsigned count)) = b3 at h ⊢
    cases b3 with
    | true => simp only [↓reduceIte]
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (!(bs.length == word_to_nat count)) = b4 at h ⊢
    cases b4 with
    | true => simp only [↓reduceIte]
    | false =>
    exfalso
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    rw [bind_set_pipes_iff] at h
    exact ret_only_not_unmodeled _ i _ (record_copyins_unmodeled_inv _ _ i _ h)

/-! ## write (64) — the witness

Mirrors the `write` half of `theories/LinuxProcessSem/Checks/Witness/Fs/ReadWrite.v`
at the header's baseline.  Where `write_spec` chooses — the channel's
delivered prefix — the witness takes the whole readable prefix, as Rocq's
does: it is nonempty behind the -EFAULT test and within the clamp by
`write_source_length_le`, so it satisfies the `choose` with nothing more
to decide.  A pipe's delivery is deterministic, so the witness is the one
outcome `write_spec` admits there. -/

/-- Rocq: `Checks.Witness.Fs.ReadWrite.write_witness`.  The arms are in
Rocq's order. -/
def write_witness (fd buf count : word) (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some (.FdChannel ch) =>
      if w_is0 ch then ret_outcome (errno_ret EBADF) m
      else if !modeled_rw_range buf count then Unmodeled
      else if w_is0 count then access_ok_zero_witness buf count m (ret_outcome (Z_to_bv 64 0) m)
      else
        let bs := write_source i.in_mem buf count
        if bs.length == 0 then ret_outcome (errno_ret EFAULT) m
        else
          outcome_copyins [(buf, bs.length)]
            (Ok (mkEffect (len_word bs) [] []) m (List.map (WriteEv ch) bs))
  | some .FdDir => ret_outcome (errno_ret EBADF) m
  | some (.FdFile _ _) => ret_outcome (errno_ret EBADF) m
  | some (.FdFileW p off) =>
      if !modeled_rw_range buf count then Unmodeled
      else
        let bs := write_source i.in_mem buf count
        if !w_is0 count && bs.length == 0 then ret_outcome (errno_ret EFAULT) m
        else
          let k :=
            match fs_lookup (m_fs m) p with
            | none => Unmodeled
            | some data =>
                if !modeled_file_gap data off bs then Unmodeled
                else
                  let out :=
                    Ok (mkEffect (len_word bs) [] [])
                      (with_fds (fd_insert (m_fds m) fd (.FdFileW p (off + len_word bs)))
                        (with_fs (fs_set (m_fs m) p (file_write data off bs)) m))
                      []
                  if w_is0 count then out else outcome_copyins [(buf, bs.length)] out
          if w_is0 count then access_ok_zero_witness buf count m k else k
  | some (.FdFileRW p off) => -- the `FdFileW` arm above, on the O_RDWR kind
      if !modeled_rw_range buf count then Unmodeled
      else
        let bs := write_source i.in_mem buf count
        if !w_is0 count && bs.length == 0 then ret_outcome (errno_ret EFAULT) m
        else
          let k :=
            match fs_lookup (m_fs m) p with
            | none => Unmodeled
            | some data =>
                if !modeled_file_gap data off bs then Unmodeled
                else
                  let out :=
                    Ok (mkEffect (len_word bs) [] [])
                      (with_fds (fd_insert (m_fds m) fd (.FdFileRW p (off + len_word bs)))
                        (with_fs (fs_set (m_fs m) p (file_write data off bs)) m))
                      []
                  if w_is0 count then out else outcome_copyins [(buf, bs.length)] out
          if w_is0 count then access_ok_zero_witness buf count m k else k
  | some (.FdFileA p off) =>
      -- the arm above with the bytes placed at end-of-file, no `modeled_file_gap`
      -- guard, and `rw_verify_area`'s test on the fd's real position (`write_spec`)
      if !modeled_rw_range buf count then Unmodeled
      else if !access_okb buf (bv_unsigned count) then ret_outcome (errno_ret EFAULT) m
      else if rw_pos_einvalb off (bv_unsigned count) then ret_outcome (errno_ret EINVAL) m
      else
        let bs := write_source i.in_mem buf count
        if !w_is0 count && bs.length == 0 then ret_outcome (errno_ret EFAULT) m
        else
          let k :=
            match fs_lookup (m_fs m) p with
            | none => Unmodeled
            | some data =>
                let out :=
                  Ok (mkEffect (len_word bs) [] [])
                    (with_fds (fd_insert (m_fds m) fd (.FdFileA p (append_new_pos data bs off)))
                      (with_fs (fs_set (m_fs m) p (file_write data (len_word data) bs)) m))
                    []
                if w_is0 count then out else outcome_copyins [(buf, bs.length)] out
          if w_is0 count then access_ok_zero_witness buf count m k else k
  | some (.FdSocket _) => Unmodeled
  | some .FdUrandom => ret_outcome (errno_ret EBADF) m
  | some (.FdDevNull _ wr) =>
      if !wr then ret_outcome (errno_ret EBADF) m
      else if !modeled_rw_range buf count then Unmodeled
      else access_ok_zero_witness buf count m (ret_outcome (Z_to_bv 64 (rw_count_clamp count)) m)
  | some (.FdPipe id w) =>
      if !w then ret_outcome (errno_ret EBADF) m
      else if !modeled_rw_range buf count then Unmodeled
      else if w_is0 count then access_ok_zero_witness buf count m (ret_outcome (Z_to_bv 64 0) m)
      else if !pipe_end_live (m_fds m) id false then Unmodeled
      else
        match pipe_lookup (m_pipes m) id with
        | none => Unmodeled
        | some st =>
            if !pipe_write_room st (bv_unsigned count) then Unmodeled
            else
              let bs := write_source i.in_mem buf count
              if !(bs.length == word_to_nat count) then Unmodeled
              else
                outcome_copyins [(buf, bs.length)]
                  (Ok (mkEffect count [] [])
                    (with_pipes (pipe_insert (m_pipes m) id (pipe_append st bs)) m) [])

/-- `access_ok_zero_witness` over a declined continuation is a run of
`access_ok_zero` over `unmodeled`: out of range both are the -EFAULT, in
range both decline.  The file arms' shape where the path or the gap
declines behind a zero count. -/
theorem access_ok_zero_witness_unmodeled (buf count : word) (i : SyscallInput) (m : Model) :
    access_ok_zero buf count unmodeled i m (access_ok_zero_witness buf count m Unmodeled) := by
  unfold access_ok_zero access_ok_zero_witness
  generalize access_okb buf (bv_unsigned count) = ok
  cases ok with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact pure_ok _ i _
  | true =>
    simp only [↓reduceIte]
    exact unmodeled_intro i m

/-- Rocq: `Checks.Witness.Fs.ReadWrite.write_witness_ok`. -/
theorem write_witness_ok (fd buf count : word) (i : SyscallInput) (m : Model) :
    write_spec fd buf count i m (write_witness fd buf count i m) := by
  unfold write_spec write_range_gate write_file_tail write_ledger write_witness
  rw [bind_input_iff, bind_get_model_iff]
  generalize fd_lookup (m_fds m) fd = r
  cases r with
  | none => exact pure_ok _ i _
  | some e =>
  cases e with
  | FdFile _ _ => exact pure_ok _ i _
  | FdChannel ch =>
    dsimp only
    generalize w_is0 ch = b0
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize (!modeled_rw_range buf count) = b1
    cases b1 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize w_is0 count = b2
    cases b2 with
    | true =>
      simp only [↓reduceIte]
      exact access_ok_zero_witness_ret _ _ _ i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hbs := write_source_length_le i.in_mem buf count
    generalize write_source i.in_mem buf count = bs at hbs ⊢
    generalize hb : (bs.length == 0) = b3
    cases b3 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    simp only [beq_eq_false_iff_ne, ne_eq] at hb
    rw [bind_choose_iff]
    refine ⟨bs, ⟨by omega, hbs, List.take_length.symm⟩, ?_⟩
    exact witness_bind_ok_eq _ _ i m () m _ _ m [] _ (emit_ok _ i m)
      (record_copyins_ok _ _ i m _ m [] (pure_ok _ i m)) (List.append_nil _).symm
  | FdDir => exact pure_ok _ i _
  | FdSocket _ => exact unmodeled_intro i m
  | FdFileW p off =>
    dsimp only
    generalize (!modeled_rw_range buf count) = b0
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize write_source i.in_mem buf count = bs
    generalize (!w_is0 count && bs.length == 0) = b1
    cases b1 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize fs_lookup (m_fs m) p = fl
    cases fl with
    | none =>
      dsimp only
      generalize w_is0 count = c
      cases c with
      | true =>
        simp only [↓reduceIte]
        exact access_ok_zero_witness_unmodeled _ _ i m
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact unmodeled_intro i m
    | some data =>
    dsimp only
    generalize (!modeled_file_gap data off bs) = g
    cases g with
    | true =>
      simp only [↓reduceIte]
      generalize w_is0 count = c
      cases c with
      | true =>
        simp only [↓reduceIte]
        exact access_ok_zero_witness_unmodeled _ _ i m
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize w_is0 count = c
    cases c with
    | true =>
      simp only [↓reduceIte]
      unfold access_ok_zero access_ok_zero_witness
      generalize access_okb buf (bv_unsigned count) = ok
      cases ok with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact pure_ok _ i _
      | true =>
        simp only [↓reduceIte]
        exact (bind_set_fs_iff _ _ i m _).mpr ((bind_set_fds_iff _ _ i _ _).mpr (pure_ok _ i _))
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact (bind_set_fs_iff _ _ i m _).mpr ((bind_set_fds_iff _ _ i _ _).mpr
        (record_copyins_ok _ _ i _ _ _ _ (pure_ok _ i _)))
  | FdFileRW p off =>
    dsimp only
    generalize (!modeled_rw_range buf count) = b0
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize write_source i.in_mem buf count = bs
    generalize (!w_is0 count && bs.length == 0) = b1
    cases b1 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize fs_lookup (m_fs m) p = fl
    cases fl with
    | none =>
      dsimp only
      generalize w_is0 count = c
      cases c with
      | true =>
        simp only [↓reduceIte]
        exact access_ok_zero_witness_unmodeled _ _ i m
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact unmodeled_intro i m
    | some data =>
    dsimp only
    generalize (!modeled_file_gap data off bs) = g
    cases g with
    | true =>
      simp only [↓reduceIte]
      generalize w_is0 count = c
      cases c with
      | true =>
        simp only [↓reduceIte]
        exact access_ok_zero_witness_unmodeled _ _ i m
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize w_is0 count = c
    cases c with
    | true =>
      simp only [↓reduceIte]
      unfold access_ok_zero access_ok_zero_witness
      generalize access_okb buf (bv_unsigned count) = ok
      cases ok with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact pure_ok _ i _
      | true =>
        simp only [↓reduceIte]
        exact (bind_set_fs_iff _ _ i m _).mpr ((bind_set_fds_iff _ _ i _ _).mpr (pure_ok _ i _))
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact (bind_set_fs_iff _ _ i m _).mpr ((bind_set_fds_iff _ _ i _ _).mpr
        (record_copyins_ok _ _ i _ _ _ _ (pure_ok _ i _)))
  | FdFileA p off =>
    dsimp only
    generalize (!modeled_rw_range buf count) = b0
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize (!access_okb buf (bv_unsigned count)) = b1
    cases b1 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize rw_pos_einvalb off (bv_unsigned count) = b2
    cases b2 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize write_source i.in_mem buf count = bs
    generalize (!w_is0 count && bs.length == 0) = b3
    cases b3 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize fs_lookup (m_fs m) p = fl
    cases fl with
    | none =>
      dsimp only
      generalize w_is0 count = c
      cases c with
      | true =>
        simp only [↓reduceIte]
        exact access_ok_zero_witness_unmodeled _ _ i m
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact unmodeled_intro i m
    | some data =>
    dsimp only
    generalize w_is0 count = c
    cases c with
    | true =>
      simp only [↓reduceIte]
      unfold access_ok_zero access_ok_zero_witness
      generalize access_okb buf (bv_unsigned count) = ok
      cases ok with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact pure_ok _ i _
      | true =>
        simp only [↓reduceIte]
        exact (bind_set_fs_iff _ _ i m _).mpr ((bind_set_fds_iff _ _ i _ _).mpr (pure_ok _ i _))
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact (bind_set_fs_iff _ _ i m _).mpr ((bind_set_fds_iff _ _ i _ _).mpr
        (record_copyins_ok _ _ i _ _ _ _ (pure_ok _ i _)))
  | FdUrandom => exact pure_ok _ i _
  | FdDevNull rd wr =>
    dsimp only
    cases wr with
    | false =>
      simp only [Bool.not_false, ↓reduceIte]
      exact pure_ok _ i _
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    generalize (!modeled_rw_range buf count) = b0
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact access_ok_zero_witness_ret _ _ _ i m
  | FdPipe id w =>
    dsimp only
    cases w with
    | false =>
      simp only [Bool.not_false, ↓reduceIte]
      exact pure_ok _ i _
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    generalize (!modeled_rw_range buf count) = b0
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize w_is0 count = b1
    cases b1 with
    | true =>
      simp only [↓reduceIte]
      exact access_ok_zero_witness_ret _ _ _ i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize (!pipe_end_live (m_fds m) id false) = b2
    cases b2 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize pipe_lookup (m_pipes m) id = pl
    cases pl with
    | none => exact unmodeled_intro i m
    | some st =>
    dsimp only
    generalize (!pipe_write_room st (bv_unsigned count)) = b3
    cases b3 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize write_source i.in_mem buf count = bs
    generalize (!(bs.length == word_to_nat count)) = b4
    cases b4 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact (bind_set_pipes_iff _ _ i m _).mpr (record_copyins_ok _ _ i _ _ _ _ (pure_ok _ i _))

-- lean-port sentinel: ticket C-Fs-ReadWrite-pread-pwrite-lseek appends below this line

/-! ## pread64 (67), pwrite64 (68) and lseek (62) — the checkers

Mirrors the `pread64`, `pwrite64` and `lseek` parts of
`theories/LinuxProcessSem/Checks/Sys/Fs/ReadWrite.v` at the header's
baseline, ported by ticket C-Fs-ReadWrite-pread-pwrite-lseek.  Each checker
is its spec twin's definition arm for arm — `pread64_spec`, `pwrite64_spec`
and `lseek_spec` in `Sys/Fs/ReadWrite.lean` — so the proofs below step
through the two in lockstep, and the argument for every decision is on the
spec's docstring, not repeated here.  The arms come in the spec's order,
except that `check_lseek` keeps Rocq's checker order for its file arms
(`FdFile`, `FdFileW`, `FdFileRW`, `FdFileA`) where `lseek_spec` keeps
Rocq's spec order (`FdFile`, `FdFileRW`, `FdFileW`, `FdFileA`); the
patterns do not overlap, so that order changes no answer.  What a reader
of the proofs needs is the order of the tests, which is the kernel's.
`ksys_pread64` (fs/read_write.c:752-766, Linux v6.18.46, commit
1f99e9ab748f) and `ksys_pwrite64` (fs/read_write.c:782-796) test `pos < 0`
before they fetch the descriptor (:755-756, :785-786), answer -EBADF on an
empty slot (:759-760, :789-790), and pass to `vfs_read` / `vfs_write` only
a file carrying `FMODE_PREAD` / `FMODE_PWRITE` (:762-763, :792-793),
-ESPIPE otherwise (:765, :795). `vfs_read` (fs/read_write.c:552-581, Linux
v6.18.46) and `vfs_write` (fs/read_write.c:666-696, Linux v6.18.46) then
make the mode test, `access_ok` on the count the call named and
`rw_verify_area`, in that order, ahead of the file's own transfer.
`ksys_lseek` (fs/read_write.c:393-408, Linux v6.18.46) fetches the
descriptor (:396-398), tests `whence <= SEEK_MAX` (:400-401), and only
then calls `vfs_llseek` (:402), whose -ESPIPE for a file without
`FMODE_LSEEK` (fs/read_write.c:385-390, Linux v6.18.46) is the kind's
first answer. Which errno wins when two conditions hold is the earlier
test's, and each checker's arms are ordered so.

WHAT THE LEAN SHAPES CHANGE.  Every departure is one the spec twin made
first, spelled the same way here:

- Rocq's `FdFile p _ | FdFileRW p _` arm of `check_pread64`, and its
  `FdFileW p _ | FdFileRW p _` arm of `check_pwrite64`, are each written
  here as two arms with one body repeated, one arm per constructor, as
  the spec twin writes them.  Each match enumerates the constructors
  without a wildcard, as the spec's does, so the day a constructor lands
  it is a decision here too.
- Rocq's `Nat.eqb (length bs) 0` is `bs.length == 0`, and its
  `(SEEK_MAX <? bv_unsigned whence)%Z` the decidable `SEEK_MAX <
  bv_unsigned whence`, each as the spec twin writes it.

Like `check_read`, none of the three reads the effect before the arm is
known: every errno is a `check_ret_only` over the kernel's return, every
decline is `CheckUnmodeled` whatever the effect, and the three delivering
arms compare the effect with the computed delivery byte for byte —
`check_pread64`'s two file arms here, and its random-device arm through
`check_read_urandom`. -/

open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi (SEEK_MAX)

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_pread64`.  `pread64_spec` as an
acceptor: the position test, then the descriptor, then the kind's gates in
`vfs_read`'s order, then the transfer.  Off the random device a pread
moves nothing, so the accepted model is `m` itself; on /dev/urandom the
delivery is
`check_read_urandom`'s, which advances the declared stream as a `read`
would, since `urandom_read_iter` reads no position. -/
def check_pread64 (i : SyscallInput) (fd buf count pos : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if ppos_einvalb pos then check_ret_only eff (errno_ret EINVAL) m []
  else
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdChannel _) => check_ret_only eff (errno_ret ESPIPE) m []
  | some (.FdPipe _ _) => check_ret_only eff (errno_ret ESPIPE) m []
  | some (.FdSocket _) => check_ret_only eff (errno_ret ESPIPE) m []
  | some (.FdFileW _ _) => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdFileA _ _) => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdDevNull rd _) =>
      if !rd then check_ret_only eff (errno_ret EBADF) m []
      else if !access_okb buf (bv_unsigned count) then check_ret_only eff (errno_ret EFAULT) m []
      else if rw_pos_einvalb pos (bv_unsigned count) then
        check_ret_only eff (errno_ret EINVAL) m []
      else check_ret_only eff (Z_to_bv 64 0) m []
  | some .FdUrandom =>
      if !access_okb buf (bv_unsigned count) then check_ret_only eff (errno_ret EFAULT) m []
      else if rw_pos_einvalb pos (bv_unsigned count) then
        check_ret_only eff (errno_ret EINVAL) m []
      else check_read_urandom i buf count eff m
  | some .FdDir =>
      if !access_okb buf (bv_unsigned count) then check_ret_only eff (errno_ret EFAULT) m []
      else if rw_pos_einvalb pos (bv_unsigned count) then
        check_ret_only eff (errno_ret EINVAL) m []
      else check_ret_only eff (errno_ret EISDIR) m []
  | some (.FdFile p _) =>
      if !access_okb buf (bv_unsigned count) then check_ret_only eff (errno_ret EFAULT) m []
      else if rw_pos_einvalb pos (bv_unsigned count) then
        check_ret_only eff (errno_ret EINVAL) m []
      else
        match fs_lookup (m_fs m) p with
        | none => CheckUnmodeled
        | some data =>
          let bs := file_read data pos (Z_to_bv 64 (rw_count_clamp count))
          match read_bytes_map i.in_wmem buf (len_word bs) with
          | none =>
              match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
              | none => check_ret_only eff (errno_ret EFAULT) m []
              | some _ => CheckUnmodeled
          | some _ =>
              match bs with
              | [] => check_ret_only eff (Z_to_bv 64 0) m []
              | _ :: _ =>
                match eff with
                | .mkEffectU ret [(a, bs')] [] [] [] [] =>
                    if bv_eqb a buf && listN_eqb bs' bs && bv_eqb ret (len_word bs)
                    then CheckOk m [] else CheckReject
                | _ => CheckReject
  | some (.FdFileRW p _) =>
      if !access_okb buf (bv_unsigned count) then check_ret_only eff (errno_ret EFAULT) m []
      else if rw_pos_einvalb pos (bv_unsigned count) then
        check_ret_only eff (errno_ret EINVAL) m []
      else
        match fs_lookup (m_fs m) p with
        | none => CheckUnmodeled
        | some data =>
          let bs := file_read data pos (Z_to_bv 64 (rw_count_clamp count))
          match read_bytes_map i.in_wmem buf (len_word bs) with
          | none =>
              match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
              | none => check_ret_only eff (errno_ret EFAULT) m []
              | some _ => CheckUnmodeled
          | some _ =>
              match bs with
              | [] => check_ret_only eff (Z_to_bv 64 0) m []
              | _ :: _ =>
                match eff with
                | .mkEffectU ret [(a, bs')] [] [] [] [] =>
                    if bv_eqb a buf && listN_eqb bs' bs && bv_eqb ret (len_word bs)
                    then CheckOk m [] else CheckReject
                | _ => CheckReject

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_pwrite64`.  `pwrite64_spec` as an
acceptor, in the same order.  The two transferring arms, the write-only and
the read-write file, accept exactly the readable prefix of the clamped
source landed at `pos`, its length returned and, for a nonzero count, its
copy-in recorded; the descriptor's offset is not read and not moved, so
the accepted model differs from `m` in the file system alone.  An append
descriptor declines, as the spec's arm does. -/
def check_pwrite64 (i : SyscallInput) (fd buf count pos : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if ppos_einvalb pos then check_ret_only eff (errno_ret EINVAL) m []
  else
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdChannel _) => check_ret_only eff (errno_ret ESPIPE) m []
  | some (.FdPipe _ _) => check_ret_only eff (errno_ret ESPIPE) m []
  | some (.FdSocket _) => check_ret_only eff (errno_ret ESPIPE) m []
  | some (.FdFile _ _) => check_ret_only eff (errno_ret EBADF) m []
  | some .FdUrandom => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdDevNull _ wr) =>
      if !wr then check_ret_only eff (errno_ret EBADF) m []
      else if !access_okb buf (bv_unsigned count) then check_ret_only eff (errno_ret EFAULT) m []
      else if rw_pos_einvalb pos (bv_unsigned count) then
        check_ret_only eff (errno_ret EINVAL) m []
      else check_ret_only eff (Z_to_bv 64 (rw_count_clamp count)) m []
  | some .FdDir => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdFileA _ _) => CheckUnmodeled
  | some (.FdFileW p _) =>
      if !access_okb buf (bv_unsigned count) then check_ret_only eff (errno_ret EFAULT) m []
      else if rw_pos_einvalb pos (bv_unsigned count) then
        check_ret_only eff (errno_ret EINVAL) m []
      else
        let bs := write_source i.in_mem buf count
        if !w_is0 count && bs.length == 0 then check_ret_only eff (errno_ret EFAULT) m []
        else
          match fs_lookup (m_fs m) p with
          | none => CheckUnmodeled
          | some data =>
              if !modeled_file_gap data pos bs then CheckUnmodeled
              else
                let m' := with_fs (fs_set (m_fs m) p (file_write data pos bs)) m
                if w_is0 count then check_ret_only eff (len_word bs) m' []
                else check_ret_only_copyins [(buf, bs.length)] eff (len_word bs) m' []
  | some (.FdFileRW p _) =>
      if !access_okb buf (bv_unsigned count) then check_ret_only eff (errno_ret EFAULT) m []
      else if rw_pos_einvalb pos (bv_unsigned count) then
        check_ret_only eff (errno_ret EINVAL) m []
      else
        let bs := write_source i.in_mem buf count
        if !w_is0 count && bs.length == 0 then check_ret_only eff (errno_ret EFAULT) m []
        else
          match fs_lookup (m_fs m) p with
          | none => CheckUnmodeled
          | some data =>
              if !modeled_file_gap data pos bs then CheckUnmodeled
              else
                let m' := with_fs (fs_set (m_fs m) p (file_write data pos bs)) m
                if w_is0 count then check_ret_only eff (len_word bs) m' []
                else check_ret_only_copyins [(buf, bs.length)] eff (len_word bs) m' []

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_lseek`.  `lseek_spec` as an
acceptor: the descriptor, then the whence, then the kind.  Nothing is
chosen, so each accepted effect is a bare return and the accepted model is
`m`, or, on a file, `m` with the descriptor moved to the destination it
returns.  Like Rocq's, it takes no input: the call reads no user memory. -/
def check_lseek (fd off whence : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some e =>
      if SEEK_MAX < bv_unsigned whence then check_ret_only eff (errno_ret EINVAL) m []
      else
        match e with
        | .FdChannel _ => check_ret_only eff (errno_ret ESPIPE) m []
        | .FdSocket _ => check_ret_only eff (errno_ret ESPIPE) m []
        | .FdPipe _ _ => check_ret_only eff (errno_ret ESPIPE) m []
        | .FdDevNull _ _ => check_ret_only eff (Z_to_bv 64 0) m []
        | .FdUrandom => check_ret_only eff (Z_to_bv 64 0) m []
        | .FdDir => CheckUnmodeled
        | .FdFile p cur =>
            match fs_lookup (m_fs m) p with
            | none => CheckUnmodeled
            | some data =>
                match lseek_base whence cur (len_word data) with
                | none => CheckUnmodeled
                | some base =>
                    match lseek_dest base off with
                    | none => check_ret_only eff (errno_ret EINVAL) m []
                    | some r =>
                        check_ret_only eff r (with_fds (fd_insert (m_fds m) fd (.FdFile p r)) m) []
        | .FdFileW p cur =>
            match fs_lookup (m_fs m) p with
            | none => CheckUnmodeled
            | some data =>
                match lseek_base whence cur (len_word data) with
                | none => CheckUnmodeled
                | some base =>
                    match lseek_dest base off with
                    | none => check_ret_only eff (errno_ret EINVAL) m []
                    | some r =>
                        check_ret_only eff r (with_fds (fd_insert (m_fds m) fd (.FdFileW p r)) m) []
        | .FdFileRW p cur =>
            match fs_lookup (m_fs m) p with
            | none => CheckUnmodeled
            | some data =>
                match lseek_base whence cur (len_word data) with
                | none => CheckUnmodeled
                | some base =>
                    match lseek_dest base off with
                    | none => check_ret_only eff (errno_ret EINVAL) m []
                    | some r =>
                        check_ret_only eff r
                          (with_fds (fd_insert (m_fds m) fd (.FdFileRW p r)) m) []
        | .FdFileA p cur =>
            match fs_lookup (m_fs m) p with
            | none => CheckUnmodeled
            | some data =>
                match lseek_base whence cur (len_word data) with
                | none => CheckUnmodeled
                | some base =>
                    match lseek_dest base off with
                    | none => check_ret_only eff (errno_ret EINVAL) m []
                    | some r =>
                        check_ret_only eff r (with_fds (fd_insert (m_fds m) fd (.FdFileA p r)) m) []

/-! ### The pread64 acceptor against `pread64_spec`

The shape of the `read` proofs above: the position test, then the lookup,
then each arm's gates `generalize`d so that both sides step together, and
at the leaf a `ret_only` lemma, `check_read_urandom`'s quartet, the
delivery's comparison, or a constructor clash.  The `_unmodeled`
directions reach each file arm's two declines — the partially writable
destination and the missing file — and, through `check_read_urandom`'s
`_unmodeled` lemmas, the random device's two, a declared stream shorter
than the count and a partially writable destination; they refute every
other leaf. -/

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_pread64_sound_ok`. -/
theorem check_pread64_sound_ok (i : SyscallInput) (fd buf count pos : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_pread64 i fd buf count pos eff m = CheckOk m' evs) :
    pread64_spec fd buf count pos i m (Ok eff m' evs) := by
  unfold check_pread64 at h
  unfold pread64_spec
  generalize ppos_einvalb pos = bp at h ⊢
  cases bp with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact ret_only_sound _ _ _ _ _ i h
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  rw [bind_input_iff, bind_get_model_iff]
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact ret_only_sound _ _ _ _ _ i h
  | some e =>
  cases e with
  | FdChannel _ => exact ret_only_sound _ _ _ _ _ i h
  | FdPipe _ _ => exact ret_only_sound _ _ _ _ _ i h
  | FdSocket _ => exact ret_only_sound _ _ _ _ _ i h
  | FdFileW _ _ => exact ret_only_sound _ _ _ _ _ i h
  | FdFileA _ _ => exact ret_only_sound _ _ _ _ _ i h
  | FdDevNull rd wr =>
    dsimp only at h ⊢
    cases rd with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
  | FdUrandom =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact check_read_urandom_sound_ok _ _ _ _ _ _ _ h
  | FdDir =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
  | FdFile p _ =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize file_read data pos (Z_to_bv 64 (rw_count_clamp count)) = bs at h ⊢
    generalize read_bytes_map i.in_wmem buf (len_word bs) = w at h ⊢
    cases w with
    | none =>
      dsimp only at h ⊢
      generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
      cases w1 with
      | none => exact ret_only_sound _ _ _ _ _ i h
      | some _ => cases h
    | some _ =>
    dsimp only at h ⊢
    cases bs with
    | nil =>
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _
    | cons b bs0 =>
    dsimp only at h
    split at h
    · rename_i ret a bs'
      split at h
      · rename_i hg
        obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj h
        simp only [Bool.and_eq_true, bv_eqb_eq, listN_eqb_eq] at hg
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hg
        exact pure_ok _ i _
      · cases h
    · cases h
  | FdFileRW p _ =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize file_read data pos (Z_to_bv 64 (rw_count_clamp count)) = bs at h ⊢
    generalize read_bytes_map i.in_wmem buf (len_word bs) = w at h ⊢
    cases w with
    | none =>
      dsimp only at h ⊢
      generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
      cases w1 with
      | none => exact ret_only_sound _ _ _ _ _ i h
      | some _ => cases h
    | some _ =>
    dsimp only at h ⊢
    cases bs with
    | nil =>
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _
    | cons b bs0 =>
    dsimp only at h
    split at h
    · rename_i ret a bs'
      split at h
      · rename_i hg
        obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj h
        simp only [Bool.and_eq_true, bv_eqb_eq, listN_eqb_eq] at hg
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hg
        exact pure_ok _ i _
      · cases h
    · cases h

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_pread64_sound_unmodeled`. -/
theorem check_pread64_sound_unmodeled (i : SyscallInput) (fd buf count pos : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_pread64 i fd buf count pos eff m = CheckUnmodeled) :
    pread64_spec fd buf count pos i m Unmodeled := by
  unfold check_pread64 at h
  unfold pread64_spec
  generalize ppos_einvalb pos = bp at h ⊢
  cases bp with
  | true =>
    simp only [↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  rw [bind_input_iff, bind_get_model_iff]
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | some e =>
  cases e with
  | FdChannel _ => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | FdPipe _ _ => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | FdSocket _ => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | FdFileW _ _ => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | FdFileA _ _ => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | FdDevNull rd wr =>
    exfalso
    dsimp only at h
    cases rd with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h
      exact check_ret_only_no_unmodeled _ _ _ _ h
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact check_ret_only_no_unmodeled _ _ _ _ h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact check_ret_only_no_unmodeled _ _ _ _ h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact check_ret_only_no_unmodeled _ _ _ _ h
  | FdUrandom =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact check_read_urandom_sound_unmodeled _ _ _ _ _ h
  | FdDir =>
    exfalso
    dsimp only at h
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact check_ret_only_no_unmodeled _ _ _ _ h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact check_ret_only_no_unmodeled _ _ _ _ h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact check_ret_only_no_unmodeled _ _ _ _ h
  | FdFile p _ =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only at h ⊢
    generalize file_read data pos (Z_to_bv 64 (rw_count_clamp count)) = bs at h ⊢
    generalize read_bytes_map i.in_wmem buf (len_word bs) = w at h ⊢
    cases w with
    | none =>
      dsimp only at h ⊢
      generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
      cases w1 with
      | none => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
      | some _ => exact unmodeled_intro i m
    | some _ =>
    exfalso
    dsimp only at h
    cases bs with
    | nil => exact check_ret_only_no_unmodeled _ _ _ _ h
    | cons b bs0 =>
      dsimp only at h
      split at h
      · split at h <;> cases h
      · cases h
  | FdFileRW p _ =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only at h ⊢
    generalize file_read data pos (Z_to_bv 64 (rw_count_clamp count)) = bs at h ⊢
    generalize read_bytes_map i.in_wmem buf (len_word bs) = w at h ⊢
    cases w with
    | none =>
      dsimp only at h ⊢
      generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
      cases w1 with
      | none => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
      | some _ => exact unmodeled_intro i m
    | some _ =>
    exfalso
    dsimp only at h
    cases bs with
    | nil => exact check_ret_only_no_unmodeled _ _ _ _ h
    | cons b bs0 =>
      dsimp only at h
      split at h
      · split at h <;> cases h
      · cases h

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_pread64_complete_ok`. -/
theorem check_pread64_complete_ok (i : SyscallInput) (fd buf count pos : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : pread64_spec fd buf count pos i m (Ok eff m' evs)) :
    check_pread64 i fd buf count pos eff m = CheckOk m' evs := by
  unfold pread64_spec at h
  unfold check_pread64
  generalize ppos_einvalb pos = bp at h ⊢
  cases bp with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact ret_only_complete _ _ _ _ _ i h
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  rw [bind_input_iff, bind_get_model_iff] at h
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact ret_only_complete _ _ _ _ _ i h
  | some e =>
  cases e with
  | FdChannel _ => exact ret_only_complete _ _ _ _ _ i h
  | FdPipe _ _ => exact ret_only_complete _ _ _ _ _ i h
  | FdSocket _ => exact ret_only_complete _ _ _ _ _ i h
  | FdFileW _ _ => exact ret_only_complete _ _ _ _ _ i h
  | FdFileA _ _ => exact ret_only_complete _ _ _ _ _ i h
  | FdDevNull rd wr =>
    dsimp only at h ⊢
    cases rd with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
  | FdUrandom =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact check_read_urandom_complete_ok _ _ _ _ _ _ _ h
  | FdDir =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
  | FdFile p _ =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize file_read data pos (Z_to_bv 64 (rw_count_clamp count)) = bs at h ⊢
    generalize read_bytes_map i.in_wmem buf (len_word bs) = w at h ⊢
    cases w with
    | none =>
      dsimp only at h ⊢
      generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
      cases w1 with
      | none => exact ret_only_complete _ _ _ _ _ i h
      | some _ => cases h
    | some _ =>
    dsimp only at h ⊢
    simp only [pure_iff, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    cases bs with
    | nil => exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    | cons b bs0 =>
      simp only [delivered_writes, bv_eqb_refl, listN_eqb_refl, Bool.and_self, ↓reduceIte]
  | FdFileRW p _ =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize file_read data pos (Z_to_bv 64 (rw_count_clamp count)) = bs at h ⊢
    generalize read_bytes_map i.in_wmem buf (len_word bs) = w at h ⊢
    cases w with
    | none =>
      dsimp only at h ⊢
      generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
      cases w1 with
      | none => exact ret_only_complete _ _ _ _ _ i h
      | some _ => cases h
    | some _ =>
    dsimp only at h ⊢
    simp only [pure_iff, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    cases bs with
    | nil => exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    | cons b bs0 =>
      simp only [delivered_writes, bv_eqb_refl, listN_eqb_refl, Bool.and_self, ↓reduceIte]

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_pread64_complete_unmodeled`. -/
theorem check_pread64_complete_unmodeled (i : SyscallInput) (fd buf count pos : word)
    (eff : SyscallEffect) (m : Model) (h : pread64_spec fd buf count pos i m Unmodeled) :
    check_pread64 i fd buf count pos eff m = CheckUnmodeled := by
  unfold pread64_spec at h
  unfold check_pread64
  generalize ppos_einvalb pos = bp at h ⊢
  cases bp with
  | true =>
    simp only [↓reduceIte] at h
    exact (ret_only_not_unmodeled _ i m h).elim
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  rw [bind_input_iff, bind_get_model_iff] at h
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact (ret_only_not_unmodeled _ i m h).elim
  | some e =>
  cases e with
  | FdChannel _ => exact (ret_only_not_unmodeled _ i m h).elim
  | FdPipe _ _ => exact (ret_only_not_unmodeled _ i m h).elim
  | FdSocket _ => exact (ret_only_not_unmodeled _ i m h).elim
  | FdFileW _ _ => exact (ret_only_not_unmodeled _ i m h).elim
  | FdFileA _ _ => exact (ret_only_not_unmodeled _ i m h).elim
  | FdDevNull rd wr =>
    exfalso
    dsimp only at h
    cases rd with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h
      exact ret_only_not_unmodeled _ i m h
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact ret_only_not_unmodeled _ i m h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact ret_only_not_unmodeled _ i m h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact ret_only_not_unmodeled _ i m h
  | FdUrandom =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact check_read_urandom_complete_unmodeled _ _ _ _ _ h
  | FdDir =>
    exfalso
    dsimp only at h
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact ret_only_not_unmodeled _ i m h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact ret_only_not_unmodeled _ i m h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact ret_only_not_unmodeled _ i m h
  | FdFile p _ =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => rfl
    | some data =>
    dsimp only at h ⊢
    generalize file_read data pos (Z_to_bv 64 (rw_count_clamp count)) = bs at h ⊢
    generalize read_bytes_map i.in_wmem buf (len_word bs) = w at h ⊢
    cases w with
    | none =>
      dsimp only at h ⊢
      generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
      cases w1 with
      | none => exact (ret_only_not_unmodeled _ i m h).elim
      | some _ => rfl
    | some _ =>
    exfalso
    dsimp only at h
    simp only [pure_iff, reduceCtorEq] at h
  | FdFileRW p _ =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => rfl
    | some data =>
    dsimp only at h ⊢
    generalize file_read data pos (Z_to_bv 64 (rw_count_clamp count)) = bs at h ⊢
    generalize read_bytes_map i.in_wmem buf (len_word bs) = w at h ⊢
    cases w with
    | none =>
      dsimp only at h ⊢
      generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1 at h ⊢
      cases w1 with
      | none => exact (ret_only_not_unmodeled _ i m h).elim
      | some _ => rfl
    | some _ =>
    exfalso
    dsimp only at h
    simp only [pure_iff, reduceCtorEq] at h

/-! ### The pwrite64 acceptor against `pwrite64_spec`

The same walk.  Each of the two transferring arms has the same leaves:
the zero count's bare return and the nonzero count's return with its
copy-in, which `check_ret_only_copyins` and `record_copyins` state in
step.  Its declines are the missing file and the hole `modeled_file_gap`
refuses, each generalized as both sides test it.  The append descriptor
declines outright. -/

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_pwrite64_sound_ok`. -/
theorem check_pwrite64_sound_ok (i : SyscallInput) (fd buf count pos : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_pwrite64 i fd buf count pos eff m = CheckOk m' evs) :
    pwrite64_spec fd buf count pos i m (Ok eff m' evs) := by
  unfold check_pwrite64 at h
  unfold pwrite64_spec
  generalize ppos_einvalb pos = bp at h ⊢
  cases bp with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact ret_only_sound _ _ _ _ _ i h
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  rw [bind_input_iff, bind_get_model_iff]
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact ret_only_sound _ _ _ _ _ i h
  | some e =>
  cases e with
  | FdChannel _ => exact ret_only_sound _ _ _ _ _ i h
  | FdPipe _ _ => exact ret_only_sound _ _ _ _ _ i h
  | FdSocket _ => exact ret_only_sound _ _ _ _ _ i h
  | FdFile _ _ => exact ret_only_sound _ _ _ _ _ i h
  | FdUrandom => exact ret_only_sound _ _ _ _ _ i h
  | FdDir => exact ret_only_sound _ _ _ _ _ i h
  | FdDevNull rd wr =>
    dsimp only at h ⊢
    cases wr with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
  | FdFileA _ _ => cases h
  | FdFileW p _ =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (!w_is0 count && bs.length == 0) = g at h ⊢
    cases g with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize (!modeled_file_gap data pos bs) = k at h ⊢
    cases k with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    rw [bind_set_fs_iff]
    generalize w_is0 count = z at h ⊢
    cases z with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
      exact record_copyins_ok_empty _ _ i _ _ _ [] rfl (pure_ok _ i _)
  | FdFileRW p _ =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (!w_is0 count && bs.length == 0) = g at h ⊢
    cases g with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize (!modeled_file_gap data pos bs) = k at h ⊢
    cases k with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    rw [bind_set_fs_iff]
    generalize w_is0 count = z at h ⊢
    cases z with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
      exact record_copyins_ok_empty _ _ i _ _ _ [] rfl (pure_ok _ i _)

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_pwrite64_sound_unmodeled`. -/
theorem check_pwrite64_sound_unmodeled (i : SyscallInput) (fd buf count pos : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_pwrite64 i fd buf count pos eff m = CheckUnmodeled) :
    pwrite64_spec fd buf count pos i m Unmodeled := by
  unfold check_pwrite64 at h
  unfold pwrite64_spec
  generalize ppos_einvalb pos = bp at h ⊢
  cases bp with
  | true =>
    simp only [↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  rw [bind_input_iff, bind_get_model_iff]
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | some e =>
  cases e with
  | FdChannel _ => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | FdPipe _ _ => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | FdSocket _ => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | FdFile _ _ => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | FdUrandom => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | FdDir => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | FdDevNull rd wr =>
    exfalso
    dsimp only at h
    cases wr with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h
      exact check_ret_only_no_unmodeled _ _ _ _ h
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact check_ret_only_no_unmodeled _ _ _ _ h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact check_ret_only_no_unmodeled _ _ _ _ h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact check_ret_only_no_unmodeled _ _ _ _ h
  | FdFileA _ _ => exact unmodeled_intro i m
  | FdFileW p _ =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (!w_is0 count && bs.length == 0) = g at h ⊢
    cases g with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only at h ⊢
    generalize (!modeled_file_gap data pos bs) = k at h ⊢
    cases k with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    exfalso
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    generalize w_is0 count = z at h
    cases z with
    | true =>
      simp only [↓reduceIte] at h
      exact check_ret_only_no_unmodeled _ _ _ _ h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact check_ret_only_copyins_no_unmodeled _ _ _ _ _ h
  | FdFileRW p _ =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (!w_is0 count && bs.length == 0) = g at h ⊢
    cases g with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only at h ⊢
    generalize (!modeled_file_gap data pos bs) = k at h ⊢
    cases k with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    exfalso
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    generalize w_is0 count = z at h
    cases z with
    | true =>
      simp only [↓reduceIte] at h
      exact check_ret_only_no_unmodeled _ _ _ _ h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact check_ret_only_copyins_no_unmodeled _ _ _ _ _ h

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_pwrite64_complete_ok`. -/
theorem check_pwrite64_complete_ok (i : SyscallInput) (fd buf count pos : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : pwrite64_spec fd buf count pos i m (Ok eff m' evs)) :
    check_pwrite64 i fd buf count pos eff m = CheckOk m' evs := by
  unfold pwrite64_spec at h
  unfold check_pwrite64
  generalize ppos_einvalb pos = bp at h ⊢
  cases bp with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact ret_only_complete _ _ _ _ _ i h
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  rw [bind_input_iff, bind_get_model_iff] at h
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact ret_only_complete _ _ _ _ _ i h
  | some e =>
  cases e with
  | FdChannel _ => exact ret_only_complete _ _ _ _ _ i h
  | FdPipe _ _ => exact ret_only_complete _ _ _ _ _ i h
  | FdSocket _ => exact ret_only_complete _ _ _ _ _ i h
  | FdFile _ _ => exact ret_only_complete _ _ _ _ _ i h
  | FdUrandom => exact ret_only_complete _ _ _ _ _ i h
  | FdDir => exact ret_only_complete _ _ _ _ _ i h
  | FdDevNull rd wr =>
    dsimp only at h ⊢
    cases wr with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
  | FdFileA _ _ => cases h
  | FdFileW p _ =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (!w_is0 count && bs.length == 0) = g at h ⊢
    cases g with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize (!modeled_file_gap data pos bs) = k at h ⊢
    cases k with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    rw [bind_set_fs_iff] at h
    generalize w_is0 count = z at h ⊢
    cases z with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨core, hcore, rfl⟩ := (record_copyins_ok_iff _ _ _ _ _ _ _).mp h
      simp only [ret_only, pure_iff, outcome.Ok.injEq] at hcore
      obtain ⟨rfl, rfl, rfl⟩ := hcore
      exact check_ret_only_copyins_refl _ _ _ _
  | FdFileRW p _ =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (!w_is0 count && bs.length == 0) = g at h ⊢
    cases g with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize (!modeled_file_gap data pos bs) = k at h ⊢
    cases k with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    rw [bind_set_fs_iff] at h
    generalize w_is0 count = z at h ⊢
    cases z with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨core, hcore, rfl⟩ := (record_copyins_ok_iff _ _ _ _ _ _ _).mp h
      simp only [ret_only, pure_iff, outcome.Ok.injEq] at hcore
      obtain ⟨rfl, rfl, rfl⟩ := hcore
      exact check_ret_only_copyins_refl _ _ _ _

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_pwrite64_complete_unmodeled`. -/
theorem check_pwrite64_complete_unmodeled (i : SyscallInput) (fd buf count pos : word)
    (eff : SyscallEffect) (m : Model) (h : pwrite64_spec fd buf count pos i m Unmodeled) :
    check_pwrite64 i fd buf count pos eff m = CheckUnmodeled := by
  unfold pwrite64_spec at h
  unfold check_pwrite64
  generalize ppos_einvalb pos = bp at h ⊢
  cases bp with
  | true =>
    simp only [↓reduceIte] at h
    exact (ret_only_not_unmodeled _ i m h).elim
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  rw [bind_input_iff, bind_get_model_iff] at h
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact (ret_only_not_unmodeled _ i m h).elim
  | some e =>
  cases e with
  | FdChannel _ => exact (ret_only_not_unmodeled _ i m h).elim
  | FdPipe _ _ => exact (ret_only_not_unmodeled _ i m h).elim
  | FdSocket _ => exact (ret_only_not_unmodeled _ i m h).elim
  | FdFile _ _ => exact (ret_only_not_unmodeled _ i m h).elim
  | FdUrandom => exact (ret_only_not_unmodeled _ i m h).elim
  | FdDir => exact (ret_only_not_unmodeled _ i m h).elim
  | FdDevNull rd wr =>
    exfalso
    dsimp only at h
    cases wr with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h
      exact ret_only_not_unmodeled _ i m h
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact ret_only_not_unmodeled _ i m h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact ret_only_not_unmodeled _ i m h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact ret_only_not_unmodeled _ i m h
  | FdFileA _ _ => rfl
  | FdFileW p _ =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (!w_is0 count && bs.length == 0) = g at h ⊢
    cases g with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => rfl
    | some data =>
    dsimp only at h ⊢
    generalize (!modeled_file_gap data pos bs) = k at h ⊢
    cases k with
    | true =>
      simp only [↓reduceIte]
    | false =>
    exfalso
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    rw [bind_set_fs_iff] at h
    generalize w_is0 count = z at h
    cases z with
    | true =>
      simp only [↓reduceIte] at h
      exact ret_only_not_unmodeled _ i _ h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact ret_only_not_unmodeled _ i _ ((record_copyins_unmodeled_iff _ _ _ _).mp h)
  | FdFileRW p _ =>
    dsimp only at h ⊢
    generalize (!access_okb buf (bv_unsigned count)) = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize write_source i.in_mem buf count = bs at h ⊢
    generalize (!w_is0 count && bs.length == 0) = g at h ⊢
    cases g with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => rfl
    | some data =>
    dsimp only at h ⊢
    generalize (!modeled_file_gap data pos bs) = k at h ⊢
    cases k with
    | true =>
      simp only [↓reduceIte]
    | false =>
    exfalso
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    rw [bind_set_fs_iff] at h
    generalize w_is0 count = z at h
    cases z with
    | true =>
      simp only [↓reduceIte] at h
      exact ret_only_not_unmodeled _ i _ h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact ret_only_not_unmodeled _ i _ ((record_copyins_unmodeled_iff _ _ _ _).mp h)

/-! ### The lseek acceptor against `lseek_spec`

The lookup, then the whence test — a `Prop`-valued `if` on both sides,
split by `by_cases` — then the kind; on a file, the path, the whence's
origin and the destination, each `generalize`d as both sides compute it.
Three declines reach `Unmodeled`: a directory, a missing path, and
SEEK_DATA or SEEK_HOLE on a file. -/

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_lseek_sound_ok`. -/
theorem check_lseek_sound_ok (fd off whence : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_lseek fd off whence eff m = CheckOk m' evs) :
    lseek_spec fd off whence i m (Ok eff m' evs) := by
  unfold check_lseek at h
  unfold lseek_spec
  rw [bind_get_model_iff]
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact ret_only_sound _ _ _ _ _ i h
  | some e =>
  dsimp only at h ⊢
  by_cases hw : SEEK_MAX < bv_unsigned whence
  · simp only [hw, ↓reduceIte] at h ⊢
    exact ret_only_sound _ _ _ _ _ i h
  simp only [hw, ↓reduceIte] at h ⊢
  cases e with
  | FdChannel _ => exact ret_only_sound _ _ _ _ _ i h
  | FdSocket _ => exact ret_only_sound _ _ _ _ _ i h
  | FdPipe _ _ => exact ret_only_sound _ _ _ _ _ i h
  | FdDevNull _ _ => exact ret_only_sound _ _ _ _ _ i h
  | FdUrandom => exact ret_only_sound _ _ _ _ _ i h
  | FdDir => cases h
  | FdFile p cur =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize lseek_base whence cur (len_word data) = lb at h ⊢
    cases lb with
    | none => cases h
    | some base =>
    dsimp only at h ⊢
    generalize lseek_dest base off = ld at h ⊢
    cases ld with
    | none => exact ret_only_sound _ _ _ _ _ i h
    | some r =>
      dsimp only at h ⊢
      rw [bind_set_fds_iff]
      exact ret_only_sound _ _ _ _ _ i h
  | FdFileW p cur =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize lseek_base whence cur (len_word data) = lb at h ⊢
    cases lb with
    | none => cases h
    | some base =>
    dsimp only at h ⊢
    generalize lseek_dest base off = ld at h ⊢
    cases ld with
    | none => exact ret_only_sound _ _ _ _ _ i h
    | some r =>
      dsimp only at h ⊢
      rw [bind_set_fds_iff]
      exact ret_only_sound _ _ _ _ _ i h
  | FdFileRW p cur =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize lseek_base whence cur (len_word data) = lb at h ⊢
    cases lb with
    | none => cases h
    | some base =>
    dsimp only at h ⊢
    generalize lseek_dest base off = ld at h ⊢
    cases ld with
    | none => exact ret_only_sound _ _ _ _ _ i h
    | some r =>
      dsimp only at h ⊢
      rw [bind_set_fds_iff]
      exact ret_only_sound _ _ _ _ _ i h
  | FdFileA p cur =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize lseek_base whence cur (len_word data) = lb at h ⊢
    cases lb with
    | none => cases h
    | some base =>
    dsimp only at h ⊢
    generalize lseek_dest base off = ld at h ⊢
    cases ld with
    | none => exact ret_only_sound _ _ _ _ _ i h
    | some r =>
      dsimp only at h ⊢
      rw [bind_set_fds_iff]
      exact ret_only_sound _ _ _ _ _ i h

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_lseek_sound_unmodeled`. -/
theorem check_lseek_sound_unmodeled (fd off whence : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_lseek fd off whence eff m = CheckUnmodeled) :
    lseek_spec fd off whence i m Unmodeled := by
  unfold check_lseek at h
  unfold lseek_spec
  rw [bind_get_model_iff]
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | some e =>
  dsimp only at h ⊢
  by_cases hw : SEEK_MAX < bv_unsigned whence
  · simp only [hw, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  simp only [hw, ↓reduceIte] at h ⊢
  cases e with
  | FdChannel _ => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | FdSocket _ => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | FdPipe _ _ => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | FdDevNull _ _ => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | FdUrandom => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | FdDir => exact unmodeled_intro i m
  | FdFile p cur =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only at h ⊢
    generalize lseek_base whence cur (len_word data) = lb at h ⊢
    cases lb with
    | none => exact unmodeled_intro i m
    | some base =>
    exfalso
    dsimp only at h
    generalize lseek_dest base off = ld at h
    cases ld with
    | none => exact check_ret_only_no_unmodeled _ _ _ _ h
    | some r => exact check_ret_only_no_unmodeled _ _ _ _ h
  | FdFileW p cur =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only at h ⊢
    generalize lseek_base whence cur (len_word data) = lb at h ⊢
    cases lb with
    | none => exact unmodeled_intro i m
    | some base =>
    exfalso
    dsimp only at h
    generalize lseek_dest base off = ld at h
    cases ld with
    | none => exact check_ret_only_no_unmodeled _ _ _ _ h
    | some r => exact check_ret_only_no_unmodeled _ _ _ _ h
  | FdFileRW p cur =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only at h ⊢
    generalize lseek_base whence cur (len_word data) = lb at h ⊢
    cases lb with
    | none => exact unmodeled_intro i m
    | some base =>
    exfalso
    dsimp only at h
    generalize lseek_dest base off = ld at h
    cases ld with
    | none => exact check_ret_only_no_unmodeled _ _ _ _ h
    | some r => exact check_ret_only_no_unmodeled _ _ _ _ h
  | FdFileA p cur =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only at h ⊢
    generalize lseek_base whence cur (len_word data) = lb at h ⊢
    cases lb with
    | none => exact unmodeled_intro i m
    | some base =>
    exfalso
    dsimp only at h
    generalize lseek_dest base off = ld at h
    cases ld with
    | none => exact check_ret_only_no_unmodeled _ _ _ _ h
    | some r => exact check_ret_only_no_unmodeled _ _ _ _ h

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_lseek_complete_ok`. -/
theorem check_lseek_complete_ok (fd off whence : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput) (h : lseek_spec fd off whence i m (Ok eff m' evs)) :
    check_lseek fd off whence eff m = CheckOk m' evs := by
  unfold lseek_spec at h
  unfold check_lseek
  rw [bind_get_model_iff] at h
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact ret_only_complete _ _ _ _ _ i h
  | some e =>
  dsimp only at h ⊢
  by_cases hw : SEEK_MAX < bv_unsigned whence
  · simp only [hw, ↓reduceIte] at h ⊢
    exact ret_only_complete _ _ _ _ _ i h
  simp only [hw, ↓reduceIte] at h ⊢
  cases e with
  | FdChannel _ => exact ret_only_complete _ _ _ _ _ i h
  | FdSocket _ => exact ret_only_complete _ _ _ _ _ i h
  | FdPipe _ _ => exact ret_only_complete _ _ _ _ _ i h
  | FdDevNull _ _ => exact ret_only_complete _ _ _ _ _ i h
  | FdUrandom => exact ret_only_complete _ _ _ _ _ i h
  | FdDir => cases h
  | FdFile p cur =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize lseek_base whence cur (len_word data) = lb at h ⊢
    cases lb with
    | none => cases h
    | some base =>
    dsimp only at h ⊢
    generalize lseek_dest base off = ld at h ⊢
    cases ld with
    | none => exact ret_only_complete _ _ _ _ _ i h
    | some r =>
      dsimp only at h ⊢
      rw [bind_set_fds_iff] at h
      exact ret_only_complete _ _ _ _ _ i h
  | FdFileW p cur =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize lseek_base whence cur (len_word data) = lb at h ⊢
    cases lb with
    | none => cases h
    | some base =>
    dsimp only at h ⊢
    generalize lseek_dest base off = ld at h ⊢
    cases ld with
    | none => exact ret_only_complete _ _ _ _ _ i h
    | some r =>
      dsimp only at h ⊢
      rw [bind_set_fds_iff] at h
      exact ret_only_complete _ _ _ _ _ i h
  | FdFileRW p cur =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize lseek_base whence cur (len_word data) = lb at h ⊢
    cases lb with
    | none => cases h
    | some base =>
    dsimp only at h ⊢
    generalize lseek_dest base off = ld at h ⊢
    cases ld with
    | none => exact ret_only_complete _ _ _ _ _ i h
    | some r =>
      dsimp only at h ⊢
      rw [bind_set_fds_iff] at h
      exact ret_only_complete _ _ _ _ _ i h
  | FdFileA p cur =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize lseek_base whence cur (len_word data) = lb at h ⊢
    cases lb with
    | none => cases h
    | some base =>
    dsimp only at h ⊢
    generalize lseek_dest base off = ld at h ⊢
    cases ld with
    | none => exact ret_only_complete _ _ _ _ _ i h
    | some r =>
      dsimp only at h ⊢
      rw [bind_set_fds_iff] at h
      exact ret_only_complete _ _ _ _ _ i h

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_lseek_complete_unmodeled`. -/
theorem check_lseek_complete_unmodeled (fd off whence : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (h : lseek_spec fd off whence i m Unmodeled) :
    check_lseek fd off whence eff m = CheckUnmodeled := by
  unfold lseek_spec at h
  unfold check_lseek
  rw [bind_get_model_iff] at h
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact (ret_only_not_unmodeled _ i m h).elim
  | some e =>
  dsimp only at h ⊢
  by_cases hw : SEEK_MAX < bv_unsigned whence
  · simp only [hw, ↓reduceIte] at h
    exact (ret_only_not_unmodeled _ i m h).elim
  simp only [hw, ↓reduceIte] at h ⊢
  cases e with
  | FdChannel _ => exact (ret_only_not_unmodeled _ i m h).elim
  | FdSocket _ => exact (ret_only_not_unmodeled _ i m h).elim
  | FdPipe _ _ => exact (ret_only_not_unmodeled _ i m h).elim
  | FdDevNull _ _ => exact (ret_only_not_unmodeled _ i m h).elim
  | FdUrandom => exact (ret_only_not_unmodeled _ i m h).elim
  | FdDir => rfl
  | FdFile p cur =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => rfl
    | some data =>
    dsimp only at h ⊢
    generalize lseek_base whence cur (len_word data) = lb at h ⊢
    cases lb with
    | none => rfl
    | some base =>
    exfalso
    dsimp only at h
    generalize lseek_dest base off = ld at h
    cases ld with
    | none => exact ret_only_not_unmodeled _ i m h
    | some r =>
      dsimp only at h
      rw [bind_set_fds_iff] at h
      exact ret_only_not_unmodeled _ i _ h
  | FdFileW p cur =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => rfl
    | some data =>
    dsimp only at h ⊢
    generalize lseek_base whence cur (len_word data) = lb at h ⊢
    cases lb with
    | none => rfl
    | some base =>
    exfalso
    dsimp only at h
    generalize lseek_dest base off = ld at h
    cases ld with
    | none => exact ret_only_not_unmodeled _ i m h
    | some r =>
      dsimp only at h
      rw [bind_set_fds_iff] at h
      exact ret_only_not_unmodeled _ i _ h
  | FdFileRW p cur =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => rfl
    | some data =>
    dsimp only at h ⊢
    generalize lseek_base whence cur (len_word data) = lb at h ⊢
    cases lb with
    | none => rfl
    | some base =>
    exfalso
    dsimp only at h
    generalize lseek_dest base off = ld at h
    cases ld with
    | none => exact ret_only_not_unmodeled _ i m h
    | some r =>
      dsimp only at h
      rw [bind_set_fds_iff] at h
      exact ret_only_not_unmodeled _ i _ h
  | FdFileA p cur =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => rfl
    | some data =>
    dsimp only at h ⊢
    generalize lseek_base whence cur (len_word data) = lb at h ⊢
    cases lb with
    | none => rfl
    | some base =>
    exfalso
    dsimp only at h
    generalize lseek_dest base off = ld at h
    cases ld with
    | none => exact ret_only_not_unmodeled _ i m h
    | some r =>
      dsimp only at h
      rw [bind_set_fds_iff] at h
      exact ret_only_not_unmodeled _ i _ h

/-! ## The pread64, pwrite64 and lseek witnesses — `Checks/Witness/Fs/ReadWrite.v`

Mirrors the three witnesses of that file at the header's baseline.  None
of the three specs chooses on an arm it answers — a positional transfer
never reaches the channel, pipe or socket arms whose short deliveries are
where `read_spec` and `write_spec` choose, and `lseek` computes every
answer — so each witness is its spec's one outcome, arm for arm, with
`Unmodeled` exactly where the spec declines. -/

/-- Rocq: `Checks.Witness.Fs.ReadWrite.pread64_witness`. -/
def pread64_witness (fd buf count pos : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  if ppos_einvalb pos then ret_outcome (errno_ret EINVAL) m
  else
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some (.FdChannel _) => ret_outcome (errno_ret ESPIPE) m
  | some (.FdPipe _ _) => ret_outcome (errno_ret ESPIPE) m
  | some (.FdSocket _) => ret_outcome (errno_ret ESPIPE) m
  | some (.FdFileW _ _) => ret_outcome (errno_ret EBADF) m
  | some (.FdFileA _ _) => ret_outcome (errno_ret EBADF) m
  | some (.FdDevNull rd _) =>
      if !rd then ret_outcome (errno_ret EBADF) m
      else if !access_okb buf (bv_unsigned count) then ret_outcome (errno_ret EFAULT) m
      else if rw_pos_einvalb pos (bv_unsigned count) then ret_outcome (errno_ret EINVAL) m
      else ret_outcome (Z_to_bv 64 0) m
  | some .FdUrandom =>
      if !access_okb buf (bv_unsigned count) then ret_outcome (errno_ret EFAULT) m
      else if rw_pos_einvalb pos (bv_unsigned count) then ret_outcome (errno_ret EINVAL) m
      else read_urandom_witness buf count i m
  | some .FdDir =>
      if !access_okb buf (bv_unsigned count) then ret_outcome (errno_ret EFAULT) m
      else if rw_pos_einvalb pos (bv_unsigned count) then ret_outcome (errno_ret EINVAL) m
      else ret_outcome (errno_ret EISDIR) m
  | some (.FdFile p _) =>
      if !access_okb buf (bv_unsigned count) then ret_outcome (errno_ret EFAULT) m
      else if rw_pos_einvalb pos (bv_unsigned count) then ret_outcome (errno_ret EINVAL) m
      else
        match fs_lookup (m_fs m) p with
        | none => Unmodeled
        | some data =>
          let bs := file_read data pos (Z_to_bv 64 (rw_count_clamp count))
          match read_bytes_map i.in_wmem buf (len_word bs) with
          | none =>
              match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
              | none => ret_outcome (errno_ret EFAULT) m
              | some _ => Unmodeled
          | some _ => Ok (mkEffect (len_word bs) (delivered_writes buf bs) []) m []
  | some (.FdFileRW p _) =>
      if !access_okb buf (bv_unsigned count) then ret_outcome (errno_ret EFAULT) m
      else if rw_pos_einvalb pos (bv_unsigned count) then ret_outcome (errno_ret EINVAL) m
      else
        match fs_lookup (m_fs m) p with
        | none => Unmodeled
        | some data =>
          let bs := file_read data pos (Z_to_bv 64 (rw_count_clamp count))
          match read_bytes_map i.in_wmem buf (len_word bs) with
          | none =>
              match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
              | none => ret_outcome (errno_ret EFAULT) m
              | some _ => Unmodeled
          | some _ => Ok (mkEffect (len_word bs) (delivered_writes buf bs) []) m []

/-- Rocq: `Checks.Witness.Fs.ReadWrite.pread64_witness_ok`. -/
theorem pread64_witness_ok (fd buf count pos : word) (i : SyscallInput) (m : Model) :
    pread64_spec fd buf count pos i m (pread64_witness fd buf count pos i m) := by
  unfold pread64_spec pread64_witness
  generalize ppos_einvalb pos = bp
  cases bp with
  | true =>
    simp only [↓reduceIte]
    exact pure_ok _ i _
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [bind_input_iff, bind_get_model_iff]
  generalize fd_lookup (m_fds m) fd = r
  cases r with
  | none => exact pure_ok _ i _
  | some e =>
  cases e with
  | FdChannel _ => exact pure_ok _ i _
  | FdPipe _ _ => exact pure_ok _ i _
  | FdSocket _ => exact pure_ok _ i _
  | FdFileW _ _ => exact pure_ok _ i _
  | FdFileA _ _ => exact pure_ok _ i _
  | FdDevNull rd wr =>
    dsimp only
    cases rd with
    | false =>
      simp only [Bool.not_false, ↓reduceIte]
      exact pure_ok _ i _
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    generalize (!access_okb buf (bv_unsigned count)) = b0
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1
    cases b1 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact pure_ok _ i _
  | FdUrandom =>
    dsimp only
    generalize (!access_okb buf (bv_unsigned count)) = b0
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1
    cases b1 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact read_urandom_witness_ok _ _ i m
  | FdDir =>
    dsimp only
    generalize (!access_okb buf (bv_unsigned count)) = b0
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1
    cases b1 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact pure_ok _ i _
  | FdFile p _ =>
    dsimp only
    generalize (!access_okb buf (bv_unsigned count)) = b0
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1
    cases b1 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize fs_lookup (m_fs m) p = fl
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only
    generalize file_read data pos (Z_to_bv 64 (rw_count_clamp count)) = bs
    generalize read_bytes_map i.in_wmem buf (len_word bs) = w
    cases w with
    | none =>
      dsimp only
      generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1
      cases w1 with
      | none => exact pure_ok _ i _
      | some _ => exact unmodeled_intro i m
    | some _ => exact pure_ok _ i _
  | FdFileRW p _ =>
    dsimp only
    generalize (!access_okb buf (bv_unsigned count)) = b0
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1
    cases b1 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize fs_lookup (m_fs m) p = fl
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only
    generalize file_read data pos (Z_to_bv 64 (rw_count_clamp count)) = bs
    generalize read_bytes_map i.in_wmem buf (len_word bs) = w
    cases w with
    | none =>
      dsimp only
      generalize read_bytes_map i.in_wmem buf (Z_to_bv 64 1) = w1
      cases w1 with
      | none => exact pure_ok _ i _
      | some _ => exact unmodeled_intro i m
    | some _ => exact pure_ok _ i _

/-- Rocq: `Checks.Witness.Fs.ReadWrite.pwrite64_witness`. -/
def pwrite64_witness (fd buf count pos : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  if ppos_einvalb pos then ret_outcome (errno_ret EINVAL) m
  else
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some (.FdChannel _) => ret_outcome (errno_ret ESPIPE) m
  | some (.FdPipe _ _) => ret_outcome (errno_ret ESPIPE) m
  | some (.FdSocket _) => ret_outcome (errno_ret ESPIPE) m
  | some (.FdFile _ _) => ret_outcome (errno_ret EBADF) m
  | some .FdUrandom => ret_outcome (errno_ret EBADF) m
  | some (.FdDevNull _ wr) =>
      if !wr then ret_outcome (errno_ret EBADF) m
      else if !access_okb buf (bv_unsigned count) then ret_outcome (errno_ret EFAULT) m
      else if rw_pos_einvalb pos (bv_unsigned count) then ret_outcome (errno_ret EINVAL) m
      else ret_outcome (Z_to_bv 64 (rw_count_clamp count)) m
  | some .FdDir => ret_outcome (errno_ret EBADF) m
  | some (.FdFileA _ _) => Unmodeled
  | some (.FdFileW p _) =>
      if !access_okb buf (bv_unsigned count) then ret_outcome (errno_ret EFAULT) m
      else if rw_pos_einvalb pos (bv_unsigned count) then ret_outcome (errno_ret EINVAL) m
      else
        let bs := write_source i.in_mem buf count
        if !w_is0 count && bs.length == 0 then ret_outcome (errno_ret EFAULT) m
        else
          match fs_lookup (m_fs m) p with
          | none => Unmodeled
          | some data =>
              if !modeled_file_gap data pos bs then Unmodeled
              else
                let out := Ok (mkEffect (len_word bs) [] [])
                  (with_fs (fs_set (m_fs m) p (file_write data pos bs)) m) []
                if w_is0 count then out else outcome_copyins [(buf, bs.length)] out
  | some (.FdFileRW p _) =>
      if !access_okb buf (bv_unsigned count) then ret_outcome (errno_ret EFAULT) m
      else if rw_pos_einvalb pos (bv_unsigned count) then ret_outcome (errno_ret EINVAL) m
      else
        let bs := write_source i.in_mem buf count
        if !w_is0 count && bs.length == 0 then ret_outcome (errno_ret EFAULT) m
        else
          match fs_lookup (m_fs m) p with
          | none => Unmodeled
          | some data =>
              if !modeled_file_gap data pos bs then Unmodeled
              else
                let out := Ok (mkEffect (len_word bs) [] [])
                  (with_fs (fs_set (m_fs m) p (file_write data pos bs)) m) []
                if w_is0 count then out else outcome_copyins [(buf, bs.length)] out

/-- Rocq: `Checks.Witness.Fs.ReadWrite.pwrite64_witness_ok`. -/
theorem pwrite64_witness_ok (fd buf count pos : word) (i : SyscallInput) (m : Model) :
    pwrite64_spec fd buf count pos i m (pwrite64_witness fd buf count pos i m) := by
  unfold pwrite64_spec pwrite64_witness
  generalize ppos_einvalb pos = bp
  cases bp with
  | true =>
    simp only [↓reduceIte]
    exact pure_ok _ i _
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [bind_input_iff, bind_get_model_iff]
  generalize fd_lookup (m_fds m) fd = r
  cases r with
  | none => exact pure_ok _ i _
  | some e =>
  cases e with
  | FdChannel _ => exact pure_ok _ i _
  | FdPipe _ _ => exact pure_ok _ i _
  | FdSocket _ => exact pure_ok _ i _
  | FdFile _ _ => exact pure_ok _ i _
  | FdUrandom => exact pure_ok _ i _
  | FdDir => exact pure_ok _ i _
  | FdDevNull rd wr =>
    dsimp only
    cases wr with
    | false =>
      simp only [Bool.not_false, ↓reduceIte]
      exact pure_ok _ i _
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    generalize (!access_okb buf (bv_unsigned count)) = b0
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1
    cases b1 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact pure_ok _ i _
  | FdFileA _ _ => exact unmodeled_intro i m
  | FdFileW p _ =>
    dsimp only
    generalize (!access_okb buf (bv_unsigned count)) = b0
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1
    cases b1 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize write_source i.in_mem buf count = bs
    generalize (!w_is0 count && bs.length == 0) = g
    cases g with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize fs_lookup (m_fs m) p = fl
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only
    generalize (!modeled_file_gap data pos bs) = k
    cases k with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [bind_set_fs_iff]
    generalize w_is0 count = z
    cases z with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact record_copyins_outcome _ _ i _ _ (pure_ok _ i _)
  | FdFileRW p _ =>
    dsimp only
    generalize (!access_okb buf (bv_unsigned count)) = b0
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize rw_pos_einvalb pos (bv_unsigned count) = b1
    cases b1 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize write_source i.in_mem buf count = bs
    generalize (!w_is0 count && bs.length == 0) = g
    cases g with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize fs_lookup (m_fs m) p = fl
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only
    generalize (!modeled_file_gap data pos bs) = k
    cases k with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [bind_set_fs_iff]
    generalize w_is0 count = z
    cases z with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact record_copyins_outcome _ _ i _ _ (pure_ok _ i _)

/-- Rocq: `Checks.Witness.Fs.ReadWrite.lseek_witness`.  Like `check_lseek`,
it takes no input. -/
def lseek_witness (fd off whence : word) (m : Model) : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some e =>
      if SEEK_MAX < bv_unsigned whence then ret_outcome (errno_ret EINVAL) m
      else
        match e with
        | .FdChannel _ => ret_outcome (errno_ret ESPIPE) m
        | .FdSocket _ => ret_outcome (errno_ret ESPIPE) m
        | .FdPipe _ _ => ret_outcome (errno_ret ESPIPE) m
        | .FdDevNull _ _ => ret_outcome (Z_to_bv 64 0) m
        | .FdUrandom => ret_outcome (Z_to_bv 64 0) m
        | .FdDir => Unmodeled
        | .FdFile p cur =>
            match fs_lookup (m_fs m) p with
            | none => Unmodeled
            | some data =>
                match lseek_base whence cur (len_word data) with
                | none => Unmodeled
                | some base =>
                    match lseek_dest base off with
                    | none => ret_outcome (errno_ret EINVAL) m
                    | some r => ret_outcome r (with_fds (fd_insert (m_fds m) fd (.FdFile p r)) m)
        | .FdFileW p cur =>
            match fs_lookup (m_fs m) p with
            | none => Unmodeled
            | some data =>
                match lseek_base whence cur (len_word data) with
                | none => Unmodeled
                | some base =>
                    match lseek_dest base off with
                    | none => ret_outcome (errno_ret EINVAL) m
                    | some r => ret_outcome r (with_fds (fd_insert (m_fds m) fd (.FdFileW p r)) m)
        | .FdFileRW p cur =>
            match fs_lookup (m_fs m) p with
            | none => Unmodeled
            | some data =>
                match lseek_base whence cur (len_word data) with
                | none => Unmodeled
                | some base =>
                    match lseek_dest base off with
                    | none => ret_outcome (errno_ret EINVAL) m
                    | some r => ret_outcome r (with_fds (fd_insert (m_fds m) fd (.FdFileRW p r)) m)
        | .FdFileA p cur =>
            match fs_lookup (m_fs m) p with
            | none => Unmodeled
            | some data =>
                match lseek_base whence cur (len_word data) with
                | none => Unmodeled
                | some base =>
                    match lseek_dest base off with
                    | none => ret_outcome (errno_ret EINVAL) m
                    | some r => ret_outcome r (with_fds (fd_insert (m_fds m) fd (.FdFileA p r)) m)

/-- Rocq: `Checks.Witness.Fs.ReadWrite.lseek_witness_ok`. -/
theorem lseek_witness_ok (fd off whence : word) (i : SyscallInput) (m : Model) :
    lseek_spec fd off whence i m (lseek_witness fd off whence m) := by
  unfold lseek_spec lseek_witness
  rw [bind_get_model_iff]
  generalize fd_lookup (m_fds m) fd = r
  cases r with
  | none => exact pure_ok _ i _
  | some e =>
  dsimp only
  by_cases hw : SEEK_MAX < bv_unsigned whence
  · simp only [hw, ↓reduceIte]
    exact pure_ok _ i _
  simp only [hw, ↓reduceIte]
  cases e with
  | FdChannel _ => exact pure_ok _ i _
  | FdSocket _ => exact pure_ok _ i _
  | FdPipe _ _ => exact pure_ok _ i _
  | FdDevNull _ _ => exact pure_ok _ i _
  | FdUrandom => exact pure_ok _ i _
  | FdDir => exact unmodeled_intro i m
  | FdFile p cur =>
    dsimp only
    generalize fs_lookup (m_fs m) p = fl
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only
    generalize lseek_base whence cur (len_word data) = lb
    cases lb with
    | none => exact unmodeled_intro i m
    | some base =>
    dsimp only
    generalize lseek_dest base off = ld
    cases ld with
    | none => exact pure_ok _ i _
    | some r => exact (bind_set_fds_iff _ _ i m _).mpr (pure_ok _ i _)
  | FdFileW p cur =>
    dsimp only
    generalize fs_lookup (m_fs m) p = fl
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only
    generalize lseek_base whence cur (len_word data) = lb
    cases lb with
    | none => exact unmodeled_intro i m
    | some base =>
    dsimp only
    generalize lseek_dest base off = ld
    cases ld with
    | none => exact pure_ok _ i _
    | some r => exact (bind_set_fds_iff _ _ i m _).mpr (pure_ok _ i _)
  | FdFileRW p cur =>
    dsimp only
    generalize fs_lookup (m_fs m) p = fl
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only
    generalize lseek_base whence cur (len_word data) = lb
    cases lb with
    | none => exact unmodeled_intro i m
    | some base =>
    dsimp only
    generalize lseek_dest base off = ld
    cases ld with
    | none => exact pure_ok _ i _
    | some r => exact (bind_set_fds_iff _ _ i m _).mpr (pure_ok _ i _)
  | FdFileA p cur =>
    dsimp only
    generalize fs_lookup (m_fs m) p = fl
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only
    generalize lseek_base whence cur (len_word data) = lb
    cases lb with
    | none => exact unmodeled_intro i m
    | some base =>
    dsimp only
    generalize lseek_dest base off = ld
    cases ld with
    | none => exact pure_ok _ i _
    | some r => exact (bind_set_fds_iff _ _ i m _).mpr (pure_ok _ i _)

-- lean-port sentinel: ticket C-Fs-ReadWrite-readv-writev appends below this line

/-! ## readv (65) and writev (66) — the checkers and witnesses

Twins of Rocq's `check_writev`, `check_readv_gap`, `check_readv_imported` and
`check_readv` (`Checks/Sys/Fs/ReadWrite.v`) and of `writev_witness` and
`readv_witness` (`Checks/Witness/Fs/ReadWrite.v`), with the lemmas relating
each to its spec, in Rocq's order: writev first, then readv, then the two
witnesses.  They are proved against `writev_spec`, `readv_spec` and
`readv_imported` in `Sys/Fs/ReadWrite.lean`, whose docstrings carry the
kernel argument; the order a reader of a proof needs is `do_writev`
(fs/read_write.c:1091-1112, Linux v6.18.46, commit 1f99e9ab748f) into
`vfs_writev` (fs/read_write.c:1028-1066, Linux v6.18.46) from
`SYSCALL_DEFINE3(writev, …)` (fs/read_write.c:1168-1172, Linux v6.18.46),
and `do_readv` (fs/read_write.c:1068-1089, Linux v6.18.46) into `vfs_readv`
(fs/read_write.c:990-1026, Linux v6.18.46) from `SYSCALL_DEFINE3(readv, …)`
(fs/read_write.c:1162-1166, Linux v6.18.46), both importing through
`__import_iovec` (lib/iov_iter.c:1352-1400, Linux v6.18.46).

WHAT IS MIRRORED, AND WHAT THE LEAN SHAPES CHANGE, beyond the module
header's list:

- The `FdFileRW` and `FdFileA` arms answer, each as the spec twin's arm
  of that kind answers.  On `writev` an `FdFileRW` is the `FdFileW` arm on
  the O_RDWR constructor, and an `FdFileA` writes the gathered bytes at
  the end of the file, with no `modeled_file_gap` guard, and moves the
  offset to `append_new_pos`; its position test still reads the fd's real
  offset.  On `readv` an `RdFileRW` is the `RdFile` arm on the O_RDWR
  constructor, and `readable_fd` turns an `FdFileA` away, so the `readv`
  checker answers it as a write-only file, through the wrong-mode gate.
- THE THREE FILE ARMS OF `check_writev` AND OF `writev_witness` write a
  gathered prefix of any nonzero length, as `writev_file_arm` does: a
  source that is readable at its first byte but not to its end gives a
  short write, and an empty gather is -EFAULT at every offset.  The
  declines that stay on these arms are the spec twin's: a path that the
  file system does not hold and an error-encoded length, on all three
  arms, and the `modeled_file_gap` hole test on `FdFileW` and `FdFileRW`.
  The `FdFileA` arm does not make the hole test (`append_opens_no_gap`).
- Rocq's `concat (map snd writes)` is `(writes.map Prod.snd).flatten`,
  the shape `State.scatter_iovecs_concat` states; the socket arm's
  catch-all `_` is the three unconnected constructors, as in `check_read`.
- Rocq's channel acceptor keeps `!addr_is_error_b ret` and its readv
  acceptors keep `bs.length ≤ total`.  Both follow from the spec's own
  constraints — the completeness proofs derive the first from
  `writev_gathered_length_le` and the second from
  `scatter_iovecs_length_le` — so they refuse nothing the spec admits;
  they are kept so that the acceptors stay Rocq's word for word.

The steps below are stated in this module because the files that would
own them — `State/` and the K1 prelude — are frozen for a checker ticket;
they leave the day a `lean: base:` PR states them there, as the module's
first shared steps do. -/

/-! ### Shared steps of the vectored arms

Not Rocq lemmas.  Every errno and fixed-return arm of `writev_spec`
behind the import, and `readv_spec`'s two import answers, are each a
`ret_only` under the import's `record_copyins`, accepted by
`check_ret_only_copyins` over the same ledger and closed with
`ret_only_copyins_sound` and `ret_only_copyins_complete`; the
post-import arms of `check_readv_imported` instead judge, with
`check_ret_only`, the effect `Prelude.strip_copyin_prefix` has
stripped of that ledger — `Prelude.check_copyin_prefix` then requires
the effect's own ledger to begin with it — and close with
`ret_only_sound` and `ret_only_complete` — the socket-reset arms, which
rewrite the descriptor first, under `bind_set_fds_iff`; Rocq closes each
inline.
Two bounds follow.
`scatter_iovecs_length_le` is a capacity bound: a scatter that succeeds
delivers no more than the vector holds, which discharges readv's
`bs.length ≤ total`.  `writev_gathered_length_le` is what the writev
channel arm owes its completeness: the claimed return of a delivered
prefix decodes to that prefix's length only while the length is below
`2^64` (`len_word_unsigned`), and the import's aggregate clamp is what
keeps it there — `__import_iovec` (lib/iov_iter.c:1387-1390, Linux
v6.18.46) and, for a count of one, `import_ubuf` (:1435-1436), which
`State.cap_iovecs` twins. -/

/-- A `CheckOk` of `check_ret_only_copyins` is the `ret_only` outcome under
the same ledger. -/
theorem ret_only_copyins_sound (reads : List (word × Nat)) (eff : SyscallEffect) (r : word)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (h : check_ret_only_copyins reads eff r m [] = CheckOk m' evs) :
    record_copyins reads (ret_only r) i m (Ok eff m' evs) := by
  obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
  exact record_copyins_ok_empty _ _ i _ _ _ _ rfl (pure_ok _ i _)

/-- The `ret_only` outcome under a ledger is what `check_ret_only_copyins`
accepts. -/
theorem ret_only_copyins_complete (reads : List (word × Nat)) (eff : SyscallEffect) (r : word)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (h : record_copyins reads (ret_only r) i m (Ok eff m' evs)) :
    check_ret_only_copyins reads eff r m [] = CheckOk m' evs := by
  obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
  simp only [ret_only, pure_iff, outcome.Ok.injEq] at hcore
  obtain ⟨rfl, rfl, rfl⟩ := hcore
  refine (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mpr ⟨?_, rfl, rfl⟩
  simp only [with_copyins, List.append_nil]

/-- A `ret_only` under a ledger never runs `Unmodeled`. -/
theorem record_ret_only_not_unmodeled (reads : List (word × Nat)) (r : word) (i : SyscallInput)
    (m : Model) (h : record_copyins reads (ret_only r) i m Unmodeled) : False :=
  ret_only_not_unmodeled r i m (record_copyins_unmodeled_inv _ _ i m h)

/-- The gatherable prefix is no longer than the vector asks for: each
segment contributes at most its `iov_len` (`State.readable_bytes_length_le`). -/
theorem gather_prefix_length_le (mp : word → Option byte) (iovs : List (word × word)) :
    ((gather_prefix mp iovs).length : Int) ≤ iovs_total iovs := by
  induction iovs with
  | nil => simp only [gather_prefix, iovs_total, List.length_nil, Int.natCast_zero, Int.le_refl]
  | cons p rest ih =>
    obtain ⟨base, len⟩ := p
    have hr := readable_bytes_length_le mp base len
    have hn := iovs_total_nonneg rest
    simp only [gather_prefix, iovs_total]
    split
    · rw [List.length_append, Int.natCast_add]
      omega
    · omega

/-- What a writev gathers is at most `MAX_RW_COUNT` bytes: the gather is
over the CAPPED vector (`State.writev_gathered`), whose aggregate is
clamped there (`State.iovs_total_cap`). -/
theorem writev_gathered_length_le (mp : word → Option byte) (iovs0 : List (word × word)) :
    ((writev_gathered mp iovs0).length : Int) ≤ MAX_RW_COUNT := by
  have h1 := gather_prefix_length_le mp (cap_iovecs iovs0)
  have h2 := iovs_total_cap iovs0
  unfold writev_gathered
  omega

/-- A scatter that succeeds delivers no more bytes than the vector holds:
`State.scatter_iovecs` answers `none` for a delivery past the aggregate
capacity. -/
theorem scatter_iovecs_length_le (mp : word → Option byte) (iovs : List (word × word)) :
    ∀ (bs : List byte) (writes : List (word × List byte)),
      scatter_iovecs mp iovs bs = some writes → (bs.length : Int) ≤ iovs_total iovs := by
  induction iovs with
  | nil =>
    intro bs writes h
    cases bs with
    | nil => simp only [List.length_nil, iovs_total, Int.natCast_zero, Int.le_refl]
    | cons b bs' =>
      simp only [scatter_iovecs] at h
      cases h
  | cons p rest ih =>
    obtain ⟨base, len⟩ := p
    intro bs writes h
    have hrest := iovs_total_nonneg rest
    have hl := (word_unsigned_range len).1
    cases bs with
    | nil =>
      simp only [List.length_nil, iovs_total, Int.natCast_zero]
      omega
    | cons b bs' =>
      have hwb : ((word_to_nat_bounded len (b :: bs').length : Nat) : Int) ≤ bv_unsigned len := by
        unfold word_to_nat_bounded
        split
        · unfold word_to_nat bv_unsigned
          omega
        · omega
      have hlen : (((b :: bs').length : Nat) : Int)
          = (((b :: bs').take (word_to_nat_bounded len (b :: bs').length)).length : Nat)
            + (((b :: bs').drop (word_to_nat_bounded len (b :: bs').length)).length : Nat) := by
        rw [List.length_take, List.length_drop]
        omega
      have htk := List.length_take_le (word_to_nat_bounded len (b :: bs').length) (b :: bs')
      have hlater : ∃ w, scatter_iovecs mp rest
          ((b :: bs').drop (word_to_nat_bounded len (b :: bs').length)) = some w := by
        cases hhere : (b :: bs').take (word_to_nat_bounded len (b :: bs').length) with
        | nil =>
          simp only [scatter_iovecs, hhere] at h
          exact ⟨writes, h⟩
        | cons x xs =>
          cases hr : read_bytes_map mp base (len_word (x :: xs)) with
          | none =>
            simp only [scatter_iovecs, hhere, hr] at h
            cases h
          | some ok =>
            cases ht : scatter_iovecs mp rest
                ((b :: bs').drop (word_to_nat_bounded len (b :: bs').length)) with
            | none =>
              simp only [scatter_iovecs, hhere, hr, ht] at h
              cases h
            | some tail => exact ⟨tail, rfl⟩
      obtain ⟨w, hw⟩ := hlater
      have hih := ih _ w hw
      simp only [iovs_total]
      omega

/-- A `CheckOk` through `Prelude.check_copyin_prefix` is the inner verdict's,
and the effect is the stripped one with the prefix put back — the shape
`record_copyins_ok` builds. -/
theorem check_copyin_prefix_ok_inv (reads : List (word × Nat)) (eff : SyscallEffect)
    (res : check_result) (m' : Model) (evs : List event)
    (h : check_copyin_prefix reads eff res = CheckOk m' evs) :
    res = CheckOk m' evs ∧
      eff = with_copyins (reads ++ (strip_copyin_prefix reads eff).eff_copyins)
              (strip_copyin_prefix reads eff) := by
  unfold check_copyin_prefix at h
  cases res with
  | CheckUnmodeled => cases h
  | CheckReject =>
    dsimp only at h
    split at h <;> cases h
  | CheckOk m1 evs1 =>
    dsimp only at h
    split at h
    · rename_i hr
      refine ⟨h, ?_⟩
      rw [access_ranges_eqb_eq] at hr
      obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
      simp only [strip_copyin_prefix, with_copyins] at hr ⊢
      have hsplit := List.take_append_drop reads.length copyins
      rw [hr] at hsplit
      rw [hsplit]
    · cases h

/-- A decline through `Prelude.check_copyin_prefix` is the inner verdict's. -/
theorem check_copyin_prefix_unmodeled_inv (reads : List (word × Nat)) (eff : SyscallEffect)
    (res : check_result) (h : check_copyin_prefix reads eff res = CheckUnmodeled) :
    res = CheckUnmodeled := by
  unfold check_copyin_prefix at h
  cases res with
  | CheckUnmodeled => rfl
  | CheckReject =>
    dsimp only at h
    split at h <;> cases h
  | CheckOk m1 evs1 =>
    dsimp only at h
    split at h <;> cases h

/-- Stripping the prefix `record_copyins` prepended gives the inner effect back. -/
theorem strip_copyin_prefix_record (reads : List (word × Nat)) (core : SyscallEffect) :
    strip_copyin_prefix reads (with_copyins (reads ++ core.eff_copyins) core) = core := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := core
  simp only [strip_copyin_prefix, with_copyins, List.drop_left]

/-- …and `check_copyin_prefix` passes the inner `CheckOk` of such an effect
through. -/
theorem check_copyin_prefix_record_ok (reads : List (word × Nat)) (core : SyscallEffect)
    (m' : Model) (evs : List event) :
    check_copyin_prefix reads (with_copyins (reads ++ core.eff_copyins) core) (CheckOk m' evs)
      = CheckOk m' evs := by
  simp only [check_copyin_prefix, with_copyins, List.take_left, access_ranges_eqb_refl,
    ↓reduceIte]

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_writev`. -/
def check_writev (i : SyscallInput) (fd iov iovcnt : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdFile _ _) => check_ret_only eff (errno_ret EBADF) m []
  | some .FdDir => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdSocket _) => CheckUnmodeled
  | some (.FdChannel ch) =>
      if w_is0 ch then check_ret_only eff (errno_ret EBADF) m []
      else
        match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
        | .ImpFault => check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (errno_ret EFAULT) m []
        | .ImpInval => check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (errno_ret EINVAL) m []
        | .ImpOk iovs0 =>
            let total := iovs_total (cap_iovecs iovs0)
            let bs := writev_gathered i.in_mem iovs0
            if total == 0 then check_ret_only_copyins
              (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (Z_to_bv 64 0) m []
            else if bs.length == 0 then check_ret_only_copyins
              (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (errno_ret EFAULT) m []
            else if addr_is_error_b (len_word bs) then CheckUnmodeled
            else
              match eff with
              | .mkEffectU ret [] [] [] [] copyins =>
                  if decide (1 ≤ bv_unsigned ret) && decide (bv_unsigned ret ≤ (bs.length : Int))
                     && !addr_is_error_b ret then
                    if access_ranges_eqb copyins
                         (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) ++
                          iov_prefix_accesses (cap_iovecs iovs0) (bv_unsigned ret).toNat)
                    then CheckOk m (List.map (WriteEv ch) (bs.take (bv_unsigned ret).toNat))
                    else CheckReject
                  else CheckReject
              | _ => CheckReject
  | some (.FdFileW p off) =>
      match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
      | .ImpFault => check_ret_only_copyins
          (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (errno_ret EFAULT) m []
      | .ImpInval => check_ret_only_copyins
          (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (errno_ret EINVAL) m []
      | .ImpOk iovs0 =>
          let total := iovs_total (cap_iovecs iovs0)
          let bs := writev_gathered i.in_mem iovs0
          if total == 0 then check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (Z_to_bv 64 0) m []
          else if rw_pos_einvalb off total then check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (errno_ret EINVAL) m []
          else if bs.length == 0 then check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (errno_ret EFAULT) m []
          else
            match fs_lookup (m_fs m) p with
            | none => CheckUnmodeled
            | some data =>
                if !modeled_file_gap data off bs then CheckUnmodeled
                else if addr_is_error_b (len_word bs) then CheckUnmodeled
                else check_ret_only_copyins
                  (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) ++
                   iov_prefix_accesses (cap_iovecs iovs0) bs.length)
                  eff (len_word bs)
                  (with_fds (fd_insert (m_fds m) fd (.FdFileW p (off + len_word bs)))
                    (with_fs (fs_set (m_fs m) p (file_write data off bs)) m))
                  []
  | some (.FdFileRW p off) =>   -- the `FdFileW` arm above, on the O_RDWR kind
      match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
      | .ImpFault => check_ret_only_copyins
          (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (errno_ret EFAULT) m []
      | .ImpInval => check_ret_only_copyins
          (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (errno_ret EINVAL) m []
      | .ImpOk iovs0 =>
          let total := iovs_total (cap_iovecs iovs0)
          let bs := writev_gathered i.in_mem iovs0
          if total == 0 then check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (Z_to_bv 64 0) m []
          else if rw_pos_einvalb off total then check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (errno_ret EINVAL) m []
          else if bs.length == 0 then check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (errno_ret EFAULT) m []
          else
            match fs_lookup (m_fs m) p with
            | none => CheckUnmodeled
            | some data =>
                if !modeled_file_gap data off bs then CheckUnmodeled
                else if addr_is_error_b (len_word bs) then CheckUnmodeled
                else check_ret_only_copyins
                  (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) ++
                   iov_prefix_accesses (cap_iovecs iovs0) bs.length)
                  eff (len_word bs)
                  (with_fds (fd_insert (m_fds m) fd (.FdFileRW p (off + len_word bs)))
                    (with_fs (fs_set (m_fs m) p (file_write data off bs)) m))
                  []
  | some (.FdFileA p off) =>
      -- `rw_pos_einvalb` still reads `off`, the fd's real position; only the
      -- destination moves.  See `Sys.Fs.ReadWrite.writev_spec`'s `FdFileA` arm
      match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
      | .ImpFault => check_ret_only_copyins
          (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (errno_ret EFAULT) m []
      | .ImpInval => check_ret_only_copyins
          (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (errno_ret EINVAL) m []
      | .ImpOk iovs0 =>
          let total := iovs_total (cap_iovecs iovs0)
          let bs := writev_gathered i.in_mem iovs0
          if total == 0 then check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (Z_to_bv 64 0) m []
          else if rw_pos_einvalb off total then check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (errno_ret EINVAL) m []
          else if bs.length == 0 then check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (errno_ret EFAULT) m []
          else
            match fs_lookup (m_fs m) p with
            | none => CheckUnmodeled
            | some data =>
                if addr_is_error_b (len_word bs) then CheckUnmodeled
                else check_ret_only_copyins
                  (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) ++
                   iov_prefix_accesses (cap_iovecs iovs0) bs.length)
                  eff (len_word bs)
                  (with_fds (fd_insert (m_fds m) fd (.FdFileA p (append_new_pos data bs off)))
                    (with_fs (fs_set (m_fs m) p (file_write data (len_word data) bs)) m))
                  []
  | some (.FdPipe _ w) =>
      if !w then check_ret_only eff (errno_ret EBADF) m []
      else
        match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
        | .ImpFault => check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (errno_ret EFAULT) m []
        | .ImpInval => check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (errno_ret EINVAL) m []
        | .ImpOk iovs0 =>
            if iovs_total (cap_iovecs iovs0) == 0 then check_ret_only_copyins
              (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (Z_to_bv 64 0) m []
            else CheckUnmodeled
  | some .FdUrandom => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdDevNull _ wr) =>
      if !wr then check_ret_only eff (errno_ret EBADF) m []
      else
        match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
        | .ImpFault => check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (errno_ret EFAULT) m []
        | .ImpInval => check_ret_only_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (errno_ret EINVAL) m []
        | .ImpOk iovs0 =>
            check_ret_only_copyins
              (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
              eff (Z_to_bv 64 (iovs_total (cap_iovecs iovs0))) m []

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_writev_sound_ok`. -/
theorem check_writev_sound_ok (i : SyscallInput) (fd iov iovcnt : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_writev i fd iov iovcnt eff m = CheckOk m' evs) :
    writev_spec fd iov iovcnt i m (Ok eff m' evs) := by
  unfold check_writev at h
  unfold writev_spec writev_file_arm writev_ledger writev_buf_gap
  rw [bind_input_iff, bind_get_model_iff]
  dsimp only at h ⊢
  generalize import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) = A at h ⊢
  generalize import_iovecs i.in_mem iov (iovcnt32 iovcnt) = imp at h ⊢
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact ret_only_sound _ _ _ _ _ i h
  | some e =>
  cases e with
  | FdFile _ _ => exact ret_only_sound _ _ _ _ _ i h
  | FdDir => exact ret_only_sound _ _ _ _ _ i h
  | FdSocket _ => cases h
  | FdUrandom => exact ret_only_sound _ _ _ _ _ i h
  | FdChannel ch =>
    dsimp only at h ⊢
    generalize w_is0 ch = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases imp with
    | ImpFault => exact ret_only_copyins_sound _ _ _ _ _ _ i h
    | ImpInval => exact ret_only_copyins_sound _ _ _ _ _ _ i h
    | ImpOk iovs0 =>
    dsimp only at h ⊢
    generalize (iovs_total (cap_iovecs iovs0) == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_copyins_sound _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize writev_gathered i.in_mem iovs0 = bs at h ⊢
    generalize (bs.length == 0) = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_copyins_sound _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize addr_is_error_b (len_word bs) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    split at h
    · rename_i ret copyins
      split at h
      · rename_i hg
        split at h
        · rename_i hreads
          obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
          obtain ⟨⟨h1, h2⟩, -⟩ := hg
          obtain rfl := (access_ranges_eqb_eq _ _).mp hreads
          have hr := word_unsigned_range ret
          have hlen := firstn_length_le_Z bs (bv_unsigned ret) hr.1 h2
          have hn : (bs.take (bv_unsigned ret).toNat).length = (bv_unsigned ret).toNat := by omega
          have hlw := len_word_firstn_ret ret bs ⟨hr.1, h2⟩
          rw [record_copyins_ok_iff]
          refine ⟨.mkEffectU ret [] [] [] []
            (iov_prefix_accesses (cap_iovecs iovs0) (bv_unsigned ret).toNat), ?_, rfl⟩
          rw [bind_choose_iff]
          refine ⟨bs.take (bv_unsigned ret).toNat, ⟨by omega, by rw [hn]⟩, ?_⟩
          rw [hn, hlw]
          exact witness_bind_ok_eq _ _ i m () m _ _ m [] _ (emit_ok _ i m)
            (record_copyins_ok_empty _ _ i m _ m [] rfl (pure_ok _ i m)) (List.append_nil _).symm
        · cases h
      · cases h
    · cases h
  | FdFileW p off =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases imp with
    | ImpFault => exact ret_only_copyins_sound _ _ _ _ _ _ i h
    | ImpInval => exact ret_only_copyins_sound _ _ _ _ _ _ i h
    | ImpOk iovs0 =>
    dsimp only at h ⊢
    generalize (iovs_total (cap_iovecs iovs0) == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_copyins_sound _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_copyins_sound _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize writev_gathered i.in_mem iovs0 = bs at h ⊢
    generalize (bs.length == 0) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_copyins_sound _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize (!modeled_file_gap data off bs) = b4 at h ⊢
    cases b4 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize addr_is_error_b (len_word bs) = b5 at h ⊢
    cases b5 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
    rw [record_copyins_ok_iff]
    refine ⟨with_copyins (iov_prefix_accesses (cap_iovecs iovs0) bs.length)
      (mkEffect (len_word bs) [] []), ?_, rfl⟩
    rw [bind_set_fs_iff, bind_set_fds_iff]
    exact record_copyins_ok_empty _ _ i _ _ _ _ rfl (pure_ok _ i _)
  | FdFileRW p off =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases imp with
    | ImpFault => exact ret_only_copyins_sound _ _ _ _ _ _ i h
    | ImpInval => exact ret_only_copyins_sound _ _ _ _ _ _ i h
    | ImpOk iovs0 =>
    dsimp only at h ⊢
    generalize (iovs_total (cap_iovecs iovs0) == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_copyins_sound _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_copyins_sound _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize writev_gathered i.in_mem iovs0 = bs at h ⊢
    generalize (bs.length == 0) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_copyins_sound _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize (!modeled_file_gap data off bs) = b4 at h ⊢
    cases b4 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize addr_is_error_b (len_word bs) = b5 at h ⊢
    cases b5 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
    rw [record_copyins_ok_iff]
    refine ⟨with_copyins (iov_prefix_accesses (cap_iovecs iovs0) bs.length)
      (mkEffect (len_word bs) [] []), ?_, rfl⟩
    rw [bind_set_fs_iff, bind_set_fds_iff]
    exact record_copyins_ok_empty _ _ i _ _ _ _ rfl (pure_ok _ i _)
  | FdFileA p off =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases imp with
    | ImpFault => exact ret_only_copyins_sound _ _ _ _ _ _ i h
    | ImpInval => exact ret_only_copyins_sound _ _ _ _ _ _ i h
    | ImpOk iovs0 =>
    dsimp only at h ⊢
    generalize (iovs_total (cap_iovecs iovs0) == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_copyins_sound _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_copyins_sound _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize writev_gathered i.in_mem iovs0 = bs at h ⊢
    generalize (bs.length == 0) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_copyins_sound _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize addr_is_error_b (len_word bs) = b5 at h ⊢
    cases b5 with
    | true =>
      simp only [↓reduceIte] at h
      cases h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
    rw [record_copyins_ok_iff]
    refine ⟨with_copyins (iov_prefix_accesses (cap_iovecs iovs0) bs.length)
      (mkEffect (len_word bs) [] []), ?_, rfl⟩
    rw [bind_set_fs_iff, bind_set_fds_iff]
    exact record_copyins_ok_empty _ _ i _ _ _ _ rfl (pure_ok _ i _)
  | FdPipe _ w =>
    dsimp only at h ⊢
    cases w with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases imp with
    | ImpFault => exact ret_only_copyins_sound _ _ _ _ _ _ i h
    | ImpInval => exact ret_only_copyins_sound _ _ _ _ _ _ i h
    | ImpOk iovs0 =>
    dsimp only at h ⊢
    generalize (iovs_total (cap_iovecs iovs0) == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_copyins_sound _ _ _ _ _ _ i h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      cases h
  | FdDevNull _ wr =>
    dsimp only at h ⊢
    cases wr with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases imp with
    | ImpFault => exact ret_only_copyins_sound _ _ _ _ _ _ i h
    | ImpInval => exact ret_only_copyins_sound _ _ _ _ _ _ i h
    | ImpOk iovs0 => exact ret_only_copyins_sound _ _ _ _ _ _ i h

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_writev_sound_unmodeled`. -/
theorem check_writev_sound_unmodeled (i : SyscallInput) (fd iov iovcnt : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_writev i fd iov iovcnt eff m = CheckUnmodeled) :
    writev_spec fd iov iovcnt i m Unmodeled := by
  unfold check_writev at h
  unfold writev_spec writev_file_arm writev_ledger writev_buf_gap
  rw [bind_input_iff, bind_get_model_iff]
  dsimp only at h ⊢
  generalize import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) = A at h ⊢
  generalize import_iovecs i.in_mem iov (iovcnt32 iovcnt) = imp at h ⊢
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
  | some e =>
  cases e with
  | FdFile _ _ => exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
  | FdDir => exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
  | FdSocket _ => exact unmodeled_intro i m
  | FdUrandom => exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
  | FdChannel ch =>
    dsimp only at h ⊢
    generalize w_is0 ch = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases imp with
    | ImpFault => exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
    | ImpInval => exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
    | ImpOk iovs0 =>
    dsimp only at h ⊢
    generalize (iovs_total (cap_iovecs iovs0) == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize writev_gathered i.in_mem iovs0 = bs at h ⊢
    generalize (bs.length == 0) = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h
      exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize addr_is_error_b (len_word bs) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte]
      exact record_copyins_unmodeled _ _ i m (unmodeled_intro i m)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · split at h
      · split at h <;> cases h
      · cases h
    · cases h
  | FdFileW p off =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases imp with
    | ImpFault => exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
    | ImpInval => exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
    | ImpOk iovs0 =>
    dsimp only at h ⊢
    generalize (iovs_total (cap_iovecs iovs0) == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h
      exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize writev_gathered i.in_mem iovs0 = bs at h ⊢
    generalize (bs.length == 0) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte] at h
      exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases fl with
    | none => exact record_copyins_unmodeled _ _ i m (unmodeled_intro i m)
    | some data =>
    dsimp only at h ⊢
    generalize (!modeled_file_gap data off bs) = b4 at h ⊢
    cases b4 with
    | true =>
      simp only [↓reduceIte]
      exact record_copyins_unmodeled _ _ i m (unmodeled_intro i m)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize addr_is_error_b (len_word bs) = b5 at h ⊢
    cases b5 with
    | true =>
      simp only [↓reduceIte]
      exact record_copyins_unmodeled _ _ i m (unmodeled_intro i m)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
  | FdFileRW p off =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases imp with
    | ImpFault => exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
    | ImpInval => exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
    | ImpOk iovs0 =>
    dsimp only at h ⊢
    generalize (iovs_total (cap_iovecs iovs0) == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h
      exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize writev_gathered i.in_mem iovs0 = bs at h ⊢
    generalize (bs.length == 0) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte] at h
      exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases fl with
    | none => exact record_copyins_unmodeled _ _ i m (unmodeled_intro i m)
    | some data =>
    dsimp only at h ⊢
    generalize (!modeled_file_gap data off bs) = b4 at h ⊢
    cases b4 with
    | true =>
      simp only [↓reduceIte]
      exact record_copyins_unmodeled _ _ i m (unmodeled_intro i m)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize addr_is_error_b (len_word bs) = b5 at h ⊢
    cases b5 with
    | true =>
      simp only [↓reduceIte]
      exact record_copyins_unmodeled _ _ i m (unmodeled_intro i m)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
  | FdFileA p off =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases imp with
    | ImpFault => exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
    | ImpInval => exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
    | ImpOk iovs0 =>
    dsimp only at h ⊢
    generalize (iovs_total (cap_iovecs iovs0) == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h
      exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize writev_gathered i.in_mem iovs0 = bs at h ⊢
    generalize (bs.length == 0) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte] at h
      exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases fl with
    | none => exact record_copyins_unmodeled _ _ i m (unmodeled_intro i m)
    | some data =>
    dsimp only at h ⊢
    generalize addr_is_error_b (len_word bs) = b5 at h ⊢
    cases b5 with
    | true =>
      simp only [↓reduceIte]
      exact record_copyins_unmodeled _ _ i m (unmodeled_intro i m)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
  | FdPipe _ w =>
    dsimp only at h ⊢
    cases w with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h
      exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases imp with
    | ImpFault => exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
    | ImpInval => exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
    | ImpOk iovs0 =>
    dsimp only at h ⊢
    generalize (iovs_total (cap_iovecs iovs0) == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact record_copyins_unmodeled _ _ i m (unmodeled_intro i m)
  | FdDevNull _ wr =>
    dsimp only at h ⊢
    cases wr with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h
      exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases imp with
    | ImpFault => exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
    | ImpInval => exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
    | ImpOk iovs0 => exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_writev_complete_ok`. -/
theorem check_writev_complete_ok (i : SyscallInput) (fd iov iovcnt : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : writev_spec fd iov iovcnt i m (Ok eff m' evs)) :
    check_writev i fd iov iovcnt eff m = CheckOk m' evs := by
  unfold writev_spec writev_file_arm writev_ledger writev_buf_gap at h
  unfold check_writev
  rw [bind_input_iff, bind_get_model_iff] at h
  dsimp only at h ⊢
  generalize import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) = A at h ⊢
  generalize import_iovecs i.in_mem iov (iovcnt32 iovcnt) = imp at h ⊢
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact ret_only_complete _ _ _ _ _ i h
  | some e =>
  cases e with
  | FdFile _ _ => exact ret_only_complete _ _ _ _ _ i h
  | FdDir => exact ret_only_complete _ _ _ _ _ i h
  | FdSocket _ => cases h
  | FdUrandom => exact ret_only_complete _ _ _ _ _ i h
  | FdChannel ch =>
    dsimp only at h ⊢
    generalize w_is0 ch = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases imp with
    | ImpFault => exact ret_only_copyins_complete _ _ _ _ _ _ i h
    | ImpInval => exact ret_only_copyins_complete _ _ _ _ _ _ i h
    | ImpOk iovs0 =>
    dsimp only at h ⊢
    generalize (iovs_total (cap_iovecs iovs0) == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_copyins_complete _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    have hbs := writev_gathered_length_le i.in_mem iovs0
    generalize writev_gathered i.in_mem iovs0 = bs at h hbs ⊢
    generalize (bs.length == 0) = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_copyins_complete _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize addr_is_error_b (len_word bs) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte] at h
      obtain ⟨_, hcore, -⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
      cases hcore
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
    rw [bind_choose_iff] at hcore
    obtain ⟨ds, ⟨h1, h3⟩, hk⟩ := hcore
    rw [bind_emit_cases_iff] at hk
    rcases hk with ⟨y, m2, evs2, hr, heq⟩ | ⟨-, heq⟩
    · obtain ⟨core2, hcore2, rfl⟩ := record_copyins_ok_inv _ _ i m _ m2 evs2 hr
      simp only [ret_only, pure_iff, outcome.Ok.injEq] at hcore2
      obtain ⟨rfl, rfl, rfl⟩ := hcore2
      obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj heq
      have hle : ds.length ≤ bs.length := by
        have hl := congrArg List.length h3
        rw [List.length_take] at hl
        omega
      have hle' : (ds.length : Int) ≤ (bs.length : Int) := by omega
      have hsm : (ds.length : Int) < two_pow_64 := by
        unfold MAX_RW_COUNT at hbs
        unfold two_pow_64
        omega
      have hae : addr_is_error_b (len_word ds) = false := by
        unfold addr_is_error_b
        rw [len_word_unsigned ds hsm]
        simp only [decide_eq_false_iff_not]
        unfold MAX_RW_COUNT at hbs
        unfold two_pow_64
        omega
      simp only [with_copyins, List.append_nil, len_word_unsigned ds hsm,
        decide_eq_true h1, decide_eq_true hle', hae, Bool.not_false, Bool.and_self, ↓reduceIte,
        Int.toNat_natCast, ← h3, access_ranges_eqb_refl]
    · cases heq
  | FdFileW p off =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases imp with
    | ImpFault => exact ret_only_copyins_complete _ _ _ _ _ _ i h
    | ImpInval => exact ret_only_copyins_complete _ _ _ _ _ _ i h
    | ImpOk iovs0 =>
    dsimp only at h ⊢
    generalize (iovs_total (cap_iovecs iovs0) == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_copyins_complete _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_copyins_complete _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize writev_gathered i.in_mem iovs0 = bs at h ⊢
    generalize (bs.length == 0) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_copyins_complete _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases fl with
    | none =>
      obtain ⟨_, hcore, -⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
      cases hcore
    | some data =>
    dsimp only at h ⊢
    generalize (!modeled_file_gap data off bs) = b4 at h ⊢
    cases b4 with
    | true =>
      simp only [↓reduceIte] at h
      obtain ⟨_, hcore, -⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
      cases hcore
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize addr_is_error_b (len_word bs) = b5 at h ⊢
    cases b5 with
    | true =>
      simp only [↓reduceIte] at h
      obtain ⟨_, hcore, -⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
      cases hcore
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
    rw [bind_set_fs_iff, bind_set_fds_iff] at hcore
    obtain ⟨core2, hcore2, rfl⟩ := record_copyins_ok_inv _ _ i _ _ m' evs hcore
    simp only [ret_only, pure_iff, outcome.Ok.injEq] at hcore2
    obtain ⟨rfl, rfl, rfl⟩ := hcore2
    refine (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mpr ⟨?_, rfl, rfl⟩
    simp only [with_copyins, List.append_nil]
  | FdFileRW p off =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases imp with
    | ImpFault => exact ret_only_copyins_complete _ _ _ _ _ _ i h
    | ImpInval => exact ret_only_copyins_complete _ _ _ _ _ _ i h
    | ImpOk iovs0 =>
    dsimp only at h ⊢
    generalize (iovs_total (cap_iovecs iovs0) == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_copyins_complete _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_copyins_complete _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize writev_gathered i.in_mem iovs0 = bs at h ⊢
    generalize (bs.length == 0) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_copyins_complete _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases fl with
    | none =>
      obtain ⟨_, hcore, -⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
      cases hcore
    | some data =>
    dsimp only at h ⊢
    generalize (!modeled_file_gap data off bs) = b4 at h ⊢
    cases b4 with
    | true =>
      simp only [↓reduceIte] at h
      obtain ⟨_, hcore, -⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
      cases hcore
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize addr_is_error_b (len_word bs) = b5 at h ⊢
    cases b5 with
    | true =>
      simp only [↓reduceIte] at h
      obtain ⟨_, hcore, -⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
      cases hcore
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
    rw [bind_set_fs_iff, bind_set_fds_iff] at hcore
    obtain ⟨core2, hcore2, rfl⟩ := record_copyins_ok_inv _ _ i _ _ m' evs hcore
    simp only [ret_only, pure_iff, outcome.Ok.injEq] at hcore2
    obtain ⟨rfl, rfl, rfl⟩ := hcore2
    refine (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mpr ⟨?_, rfl, rfl⟩
    simp only [with_copyins, List.append_nil]
  | FdFileA p off =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases imp with
    | ImpFault => exact ret_only_copyins_complete _ _ _ _ _ _ i h
    | ImpInval => exact ret_only_copyins_complete _ _ _ _ _ _ i h
    | ImpOk iovs0 =>
    dsimp only at h ⊢
    generalize (iovs_total (cap_iovecs iovs0) == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_copyins_complete _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_copyins_complete _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize writev_gathered i.in_mem iovs0 = bs at h ⊢
    generalize (bs.length == 0) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_copyins_complete _ _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases fl with
    | none =>
      obtain ⟨_, hcore, -⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
      cases hcore
    | some data =>
    dsimp only at h ⊢
    generalize addr_is_error_b (len_word bs) = b5 at h ⊢
    cases b5 with
    | true =>
      simp only [↓reduceIte] at h
      obtain ⟨_, hcore, -⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
      cases hcore
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
    rw [bind_set_fs_iff, bind_set_fds_iff] at hcore
    obtain ⟨core2, hcore2, rfl⟩ := record_copyins_ok_inv _ _ i _ _ m' evs hcore
    simp only [ret_only, pure_iff, outcome.Ok.injEq] at hcore2
    obtain ⟨rfl, rfl, rfl⟩ := hcore2
    refine (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mpr ⟨?_, rfl, rfl⟩
    simp only [with_copyins, List.append_nil]
  | FdPipe _ w =>
    dsimp only at h ⊢
    cases w with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases imp with
    | ImpFault => exact ret_only_copyins_complete _ _ _ _ _ _ i h
    | ImpInval => exact ret_only_copyins_complete _ _ _ _ _ _ i h
    | ImpOk iovs0 =>
    dsimp only at h ⊢
    generalize (iovs_total (cap_iovecs iovs0) == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_copyins_complete _ _ _ _ _ _ i h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨_, hcore, -⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
      cases hcore
  | FdDevNull _ wr =>
    dsimp only at h ⊢
    cases wr with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases imp with
    | ImpFault => exact ret_only_copyins_complete _ _ _ _ _ _ i h
    | ImpInval => exact ret_only_copyins_complete _ _ _ _ _ _ i h
    | ImpOk iovs0 => exact ret_only_copyins_complete _ _ _ _ _ _ i h

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_writev_complete_unmodeled`. -/
theorem check_writev_complete_unmodeled (i : SyscallInput) (fd iov iovcnt : word)
    (eff : SyscallEffect) (m : Model) (h : writev_spec fd iov iovcnt i m Unmodeled) :
    check_writev i fd iov iovcnt eff m = CheckUnmodeled := by
  unfold writev_spec writev_file_arm writev_ledger writev_buf_gap at h
  unfold check_writev
  rw [bind_input_iff, bind_get_model_iff] at h
  dsimp only at h ⊢
  generalize import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) = A at h ⊢
  generalize import_iovecs i.in_mem iov (iovcnt32 iovcnt) = imp at h ⊢
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact (ret_only_not_unmodeled _ i m h).elim
  | some e =>
  cases e with
  | FdFile _ _ => exact (ret_only_not_unmodeled _ i m h).elim
  | FdDir => exact (ret_only_not_unmodeled _ i m h).elim
  | FdSocket _ => rfl
  | FdUrandom => exact (ret_only_not_unmodeled _ i m h).elim
  | FdChannel ch =>
    dsimp only at h ⊢
    generalize w_is0 ch = b0 at h ⊢
    cases b0 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases imp with
    | ImpFault => exact (record_ret_only_not_unmodeled _ _ i m h).elim
    | ImpInval => exact (record_ret_only_not_unmodeled _ _ i m h).elim
    | ImpOk iovs0 =>
    dsimp only at h ⊢
    generalize (iovs_total (cap_iovecs iovs0) == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (record_ret_only_not_unmodeled _ _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize writev_gathered i.in_mem iovs0 = bs at h ⊢
    generalize (bs.length == 0) = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h
      exact (record_ret_only_not_unmodeled _ _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize addr_is_error_b (len_word bs) = b3 at h ⊢
    cases b3 with
    | true => simp only [↓reduceIte]
    | false =>
    exfalso
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    have hin := record_copyins_unmodeled_inv _ _ i m h
    rw [bind_choose_iff] at hin
    obtain ⟨ds, -, hk⟩ := hin
    rw [bind_emit_cases_iff] at hk
    rcases hk with ⟨_, _, _, _, heq⟩ | ⟨hr, -⟩
    · cases heq
    · exact record_ret_only_not_unmodeled _ _ i m hr
  | FdFileW p off =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases imp with
    | ImpFault => exact (record_ret_only_not_unmodeled _ _ i m h).elim
    | ImpInval => exact (record_ret_only_not_unmodeled _ _ i m h).elim
    | ImpOk iovs0 =>
    dsimp only at h ⊢
    generalize (iovs_total (cap_iovecs iovs0) == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (record_ret_only_not_unmodeled _ _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h
      exact (record_ret_only_not_unmodeled _ _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize writev_gathered i.in_mem iovs0 = bs at h ⊢
    generalize (bs.length == 0) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte] at h
      exact (record_ret_only_not_unmodeled _ _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases fl with
    | none => rfl
    | some data =>
    dsimp only at h ⊢
    generalize (!modeled_file_gap data off bs) = b4 at h ⊢
    cases b4 with
    | true => simp only [↓reduceIte]
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize addr_is_error_b (len_word bs) = b5 at h ⊢
    cases b5 with
    | true => simp only [↓reduceIte]
    | false =>
    exfalso
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    have hin := record_copyins_unmodeled_inv _ _ i m h
    rw [bind_set_fs_iff, bind_set_fds_iff] at hin
    exact record_ret_only_not_unmodeled _ _ i _ hin
  | FdFileRW p off =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases imp with
    | ImpFault => exact (record_ret_only_not_unmodeled _ _ i m h).elim
    | ImpInval => exact (record_ret_only_not_unmodeled _ _ i m h).elim
    | ImpOk iovs0 =>
    dsimp only at h ⊢
    generalize (iovs_total (cap_iovecs iovs0) == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (record_ret_only_not_unmodeled _ _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h
      exact (record_ret_only_not_unmodeled _ _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize writev_gathered i.in_mem iovs0 = bs at h ⊢
    generalize (bs.length == 0) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte] at h
      exact (record_ret_only_not_unmodeled _ _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases fl with
    | none => rfl
    | some data =>
    dsimp only at h ⊢
    generalize (!modeled_file_gap data off bs) = b4 at h ⊢
    cases b4 with
    | true => simp only [↓reduceIte]
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize addr_is_error_b (len_word bs) = b5 at h ⊢
    cases b5 with
    | true => simp only [↓reduceIte]
    | false =>
    exfalso
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    have hin := record_copyins_unmodeled_inv _ _ i m h
    rw [bind_set_fs_iff, bind_set_fds_iff] at hin
    exact record_ret_only_not_unmodeled _ _ i _ hin
  | FdFileA p off =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases imp with
    | ImpFault => exact (record_ret_only_not_unmodeled _ _ i m h).elim
    | ImpInval => exact (record_ret_only_not_unmodeled _ _ i m h).elim
    | ImpOk iovs0 =>
    dsimp only at h ⊢
    generalize (iovs_total (cap_iovecs iovs0) == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (record_ret_only_not_unmodeled _ _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = b2 at h ⊢
    cases b2 with
    | true =>
      simp only [↓reduceIte] at h
      exact (record_ret_only_not_unmodeled _ _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize writev_gathered i.in_mem iovs0 = bs at h ⊢
    generalize (bs.length == 0) = b3 at h ⊢
    cases b3 with
    | true =>
      simp only [↓reduceIte] at h
      exact (record_ret_only_not_unmodeled _ _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases fl with
    | none => rfl
    | some data =>
    dsimp only at h ⊢
    generalize addr_is_error_b (len_word bs) = b5 at h ⊢
    cases b5 with
    | true => simp only [↓reduceIte]
    | false =>
    exfalso
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    have hin := record_copyins_unmodeled_inv _ _ i m h
    rw [bind_set_fs_iff, bind_set_fds_iff] at hin
    exact record_ret_only_not_unmodeled _ _ i _ hin
  | FdPipe _ w =>
    dsimp only at h ⊢
    cases w with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases imp with
    | ImpFault => exact (record_ret_only_not_unmodeled _ _ i m h).elim
    | ImpInval => exact (record_ret_only_not_unmodeled _ _ i m h).elim
    | ImpOk iovs0 =>
    dsimp only at h ⊢
    generalize (iovs_total (cap_iovecs iovs0) == 0) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (record_ret_only_not_unmodeled _ _ i m h).elim
    | false => simp only [Bool.false_eq_true, ↓reduceIte]
  | FdDevNull _ wr =>
    dsimp only at h ⊢
    cases wr with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases imp with
    | ImpFault => exact (record_ret_only_not_unmodeled _ _ i m h).elim
    | ImpInval => exact (record_ret_only_not_unmodeled _ _ i m h).elim
    | ImpOk iovs0 => exact (record_ret_only_not_unmodeled _ _ i m h).elim

/-- The checker-side spelling of a readv fail-closed gap: a plain decline
(`Sys.Fs.ReadWrite.readv_buf_gap`).  Rocq:
`Checks.Sys.Fs.ReadWrite.check_readv_gap`. -/
def check_readv_gap : check_result := CheckUnmodeled

/-- Rocq: `Checks.Sys.Fs.ReadWrite.readv_heap_gap_no_ok`. -/
theorem readv_heap_gap_no_ok (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model)
    (evs : List event) (h : readv_heap_gap i m (Ok eff m' evs)) : False := by
  simp only [readv_heap_gap, readv_buf_gap, unmodeled_iff, reduceCtorEq] at h

/-- The read operation behind a successful import, on the stripped effect
(Rocq: `Checks.Sys.Fs.ReadWrite.check_readv_imported`).  A channel or a
connected socket with a byte ready accepts the canonical scatter of the
bytes its ledger delivers: `bs` is read back off the writes, so an effect
whose writes are not `scatter_iovecs` of their own concatenation is
rejected by the `writes_eqb` against that scatter. -/
def check_readv_imported (i : SyscallInput) (fd : word) (r : ReadableFd)
    (iovs0 : List (word × word)) (eff : SyscallEffect) (m : Model) : check_result :=
  let iovs := cap_iovecs iovs0
  let total := iovs_total iovs
  if total == 0 then check_ret_only eff (Z_to_bv 64 0) m []
  else
  match r with
  | .RdChannel ch =>
      match (m_stdin m).uncons with
      | none => check_ret_only eff (Z_to_bv 64 0) m []
      | some _ =>
          match scatter_iovecs i.in_wmem iovs [Z_to_bv 8 0] with
          | none => check_ret_only eff (errno_ret EFAULT) m []
          | some _ =>
              match scatter_iovecs i.in_wmem iovs (stream_take_z (m_stdin m) total).1 with
              | none => check_readv_gap   -- partially writable destination
              | some _ =>
                  match eff with
                  | .mkEffectU ret writes [] [] [] [] =>
                      let bs := (writes.map Prod.snd).flatten
                      match scatter_iovecs i.in_wmem iovs bs with
                      | none => CheckReject
                      | some expected =>
                          if bv_eqb ret (len_word bs)
                             && writes_eqb writes expected
                             && decide (1 ≤ (bs.length : Int))
                             && decide ((bs.length : Int) ≤ total)
                             && listN_eqb (stream_take (m_stdin m) bs.length).1 bs
                          then CheckOk (with_stdin (stream_take (m_stdin m) bs.length).2 m)
                                 (List.map (ReadEv ch) bs)
                          else CheckReject
                  | _ => CheckReject
  | .RdSocket sk =>
      match sk with
      | .SkConnected peer ch rx =>
          match rx.cell_at 0 with
          | .NFin => check_ret_only eff (Z_to_bv 64 0) m []
          | .NRst =>
              check_ret_only eff (errno_ret ECONNRESET)
                (with_fds (fd_insert (m_fds m) fd (.FdSocket (.SkReset peer ch))) m) []
          | .NTimedOut =>
              check_ret_only eff (errno_ret ETIMEDOUT)
                (with_fds (fd_insert (m_fds m) fd (.FdSocket (.SkReset peer ch))) m) []
          | .NByte _ =>
              match scatter_iovecs i.in_wmem iovs [Z_to_bv 8 0] with
              | none => check_ret_only eff (errno_ret EFAULT) m []
              | some _ =>
                  match scatter_iovecs i.in_wmem iovs (net_take_z rx total).1 with
                  | none => check_readv_gap   -- partially writable destination
                  | some _ =>
                      match eff with
                      | .mkEffectU ret writes [] [] [] [] =>
                          let bs := (writes.map Prod.snd).flatten
                          match scatter_iovecs i.in_wmem iovs bs with
                          | none => CheckReject
                          | some expected =>
                              if bv_eqb ret (len_word bs)
                                 && writes_eqb writes expected
                                 && decide (1 ≤ (bs.length : Int))
                                 && decide ((bs.length : Int) ≤ total)
                                 && listN_eqb (net_take rx bs.length).1 bs
                              then CheckOk
                                     (with_fds (fd_insert (m_fds m) fd
                                        (.FdSocket (.SkConnected peer ch
                                          (net_take rx bs.length).2))) m)
                                     (List.map (ReadEv ch) bs)
                              else CheckReject
                      | _ => CheckReject
      | .SkReset _ _ => check_ret_only eff (Z_to_bv 64 0) m []
      | .SkFresh | .SkBound | .SkListening => check_ret_only eff (errno_ret ENOTCONN) m []
  | .RdPipe _ => check_readv_gap   -- vectored pipe reads are unmodeled
  | .RdDevNull => check_ret_only eff (Z_to_bv 64 0) m []
  | .RdUrandom => check_readv_gap   -- vectored device reads decline
  | .RdDir => check_ret_only eff (errno_ret EISDIR) m []
  | .RdFile p off =>
      match fs_lookup (m_fs m) p with
      | none => check_readv_gap
      | some data =>
          if rw_pos_einvalb off total then check_ret_only eff (errno_ret EINVAL) m []
          else
          let bs := file_read data off (Z_to_bv 64 total)
          match scatter_iovecs i.in_wmem iovs bs with
          | some writes =>
              if addr_is_error_b (len_word bs) then check_readv_gap
              else
              match eff with
              | .mkEffectU ret writes' [] [] [] [] =>
                  if bv_eqb ret (len_word bs) && writes_eqb writes' writes
                  then CheckOk
                         (with_fds (fd_insert (m_fds m) fd (.FdFile p (off + len_word bs))) m) []
                  else CheckReject
              | _ => CheckReject
          | none =>
              match scatter_iovecs i.in_wmem iovs [Z_to_bv 8 0] with
              | none => check_ret_only eff (errno_ret EFAULT) m []
              | some _ => check_readv_gap
  | .RdFileRW p off =>   -- the `RdFile` arm above, on the O_RDWR kind
      match fs_lookup (m_fs m) p with
      | none => check_readv_gap
      | some data =>
          if rw_pos_einvalb off total then check_ret_only eff (errno_ret EINVAL) m []
          else
          let bs := file_read data off (Z_to_bv 64 total)
          match scatter_iovecs i.in_wmem iovs bs with
          | some writes =>
              if addr_is_error_b (len_word bs) then check_readv_gap
              else
              match eff with
              | .mkEffectU ret writes' [] [] [] [] =>
                  if bv_eqb ret (len_word bs) && writes_eqb writes' writes
                  then CheckOk
                         (with_fds (fd_insert (m_fds m) fd (.FdFileRW p (off + len_word bs))) m) []
                  else CheckReject
              | _ => CheckReject
          | none =>
              match scatter_iovecs i.in_wmem iovs [Z_to_bv 8 0] with
              | none => check_ret_only eff (errno_ret EFAULT) m []
              | some _ => check_readv_gap

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_readv`. -/
def check_readv (i : SyscallInput) (fd iov iovcnt : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some e =>
      match readable_fd e with
      | none => check_ret_only eff (errno_ret EBADF) m []
          -- the read end of a pipe has a `RdPipe`; only the O_WRONLY write
          -- end reaches this arm, where -EBADF is the kernel's own answer
      | some r =>
          if readv_heap_iovecb iovcnt then check_readv_gap
          else
            match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
            | .ImpFault => check_ret_only_copyins
                (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (errno_ret EFAULT) m []
            | .ImpInval => check_ret_only_copyins
                (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff (errno_ret EINVAL) m []
            | .ImpOk iovs0 =>
                check_copyin_prefix (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff
                  (check_readv_imported i fd r iovs0
                    (strip_copyin_prefix (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
                      eff) m)

/-- Rocq: `Checks.Sys.Fs.ReadWrite.readv_copyin_reports_the_iovec_table`: two
readable descriptors are charged as two 16-byte ranges, one per descriptor
`copy_iovec_from_user` reads (lib/iov_iter.c:1260-1290, Linux v6.18.46) — the
ledger `check_readv` strips off the front of an imported effect.  Rocq closes
it by `vm_compute`; `rfl` evaluates the same walk.  Its two siblings need
fixtures this module does not port (header). -/
theorem readv_copyin_reports_the_iovec_table :
    (import_iovecs_accesses (fun _ => some 0) 0x2000 2).map (fun p => (bv_unsigned p.1, p.2))
      = [(0x2000, 16), (0x2010, 16)] := by
  rfl

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_readv_imported_sound_ok`. -/
theorem check_readv_imported_sound_ok (i : SyscallInput) (fd : word) (r : ReadableFd)
    (iovs0 : List (word × word)) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_readv_imported i fd r iovs0 eff m = CheckOk m' evs) :
    readv_imported fd r iovs0 i m i m (Ok eff m' evs) := by
  unfold check_readv_imported check_readv_gap at h
  unfold readv_imported readv_buf_gap
  dsimp only at h ⊢
  generalize (iovs_total (cap_iovecs iovs0) == 0) = b0 at h ⊢
  cases b0 with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact ret_only_sound _ _ _ _ _ i h
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases r with
  | RdChannel ch =>
    dsimp only at h ⊢
    generalize (m_stdin m).uncons = u at h ⊢
    cases u with
    | none => exact ret_only_sound _ _ _ _ _ i h
    | some _ =>
    dsimp only at h ⊢
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) [Z_to_bv 8 0] = w1 at h ⊢
    cases w1 with
    | none => exact ret_only_sound _ _ _ _ _ i h
    | some _ =>
    dsimp only at h ⊢
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0)
      (stream_take_z (m_stdin m) (iovs_total (cap_iovecs iovs0))).1 = w2 at h ⊢
    cases w2 with
    | none => cases h
    | some _ =>
    dsimp only at h ⊢
    split at h
    · rename_i ret writes
      split at h
      · cases h
      · rename_i expected hexp
        split at h
        · rename_i hg
          obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj h
          simp only [Bool.and_eq_true, bv_eqb_eq, writes_eqb_eq, listN_eqb_eq,
            decide_eq_true_eq] at hg
          obtain ⟨⟨⟨⟨rfl, rfl⟩, h1⟩, -⟩, h3⟩ := hg
          rw [bind_choose_iff]
          refine ⟨(writes.map Prod.snd).flatten, ⟨h1, h3⟩, ?_⟩
          rw [bind_choose_iff]
          refine ⟨writes, hexp, ?_⟩
          exact (bind_set_stdin_iff _ _ i m _).mpr (emit_pure_ok _ _ i _)
        · cases h
    · cases h
  | RdSocket sk =>
    cases sk with
    | SkFresh => exact ret_only_sound _ _ _ _ _ i h
    | SkBound => exact ret_only_sound _ _ _ _ _ i h
    | SkListening => exact ret_only_sound _ _ _ _ _ i h
    | SkReset _ _ => exact ret_only_sound _ _ _ _ _ i h
    | SkConnected peer ch rx =>
    dsimp only at h ⊢
    generalize rx.cell_at 0 = c at h ⊢
    cases c with
    | NFin => exact ret_only_sound _ _ _ _ _ i h
    | NRst => exact (bind_set_fds_iff _ _ i m _).mpr (ret_only_sound _ _ _ _ _ i h)
    | NTimedOut => exact (bind_set_fds_iff _ _ i m _).mpr (ret_only_sound _ _ _ _ _ i h)
    | NByte _ =>
    dsimp only at h ⊢
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) [Z_to_bv 8 0] = w1 at h ⊢
    cases w1 with
    | none => exact ret_only_sound _ _ _ _ _ i h
    | some _ =>
    dsimp only at h ⊢
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0)
      (net_take_z rx (iovs_total (cap_iovecs iovs0))).1 = w2 at h ⊢
    cases w2 with
    | none => cases h
    | some _ =>
    dsimp only at h ⊢
    split at h
    · rename_i ret writes
      split at h
      · cases h
      · rename_i expected hexp
        split at h
        · rename_i hg
          obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj h
          simp only [Bool.and_eq_true, bv_eqb_eq, writes_eqb_eq, listN_eqb_eq,
            decide_eq_true_eq] at hg
          obtain ⟨⟨⟨⟨rfl, rfl⟩, h1⟩, -⟩, h3⟩ := hg
          rw [bind_choose_iff]
          refine ⟨(writes.map Prod.snd).flatten, ⟨h1, h3⟩, ?_⟩
          rw [bind_choose_iff]
          refine ⟨writes, hexp, ?_⟩
          exact (bind_set_fds_iff _ _ i m _).mpr (emit_pure_ok _ _ i _)
        · cases h
    · cases h
  | RdPipe _ => cases h
  | RdDevNull => exact ret_only_sound _ _ _ _ _ i h
  | RdUrandom => cases h
  | RdDir => exact ret_only_sound _ _ _ _ _ i h
  | RdFile p off =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize file_read data off (Z_to_bv 64 (iovs_total (cap_iovecs iovs0))) = bs at h ⊢
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc at h ⊢
    cases sc with
    | some writes =>
      dsimp only at h ⊢
      generalize addr_is_error_b (len_word bs) = b2 at h ⊢
      cases b2 with
      | true =>
        simp only [↓reduceIte] at h
        cases h
      | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      split at h
      · rename_i ret writes'
        split at h
        · rename_i hg
          obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj h
          simp only [Bool.and_eq_true, bv_eqb_eq, writes_eqb_eq] at hg
          obtain ⟨rfl, rfl⟩ := hg
          exact (bind_set_fds_iff _ _ i m _).mpr (pure_ok _ i _)
        · cases h
      · cases h
    | none =>
      dsimp only at h ⊢
      generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) [Z_to_bv 8 0] = w1 at h ⊢
      cases w1 with
      | none => exact ret_only_sound _ _ _ _ _ i h
      | some _ => cases h
  | RdFileRW p off =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_sound _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize file_read data off (Z_to_bv 64 (iovs_total (cap_iovecs iovs0))) = bs at h ⊢
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc at h ⊢
    cases sc with
    | some writes =>
      dsimp only at h ⊢
      generalize addr_is_error_b (len_word bs) = b2 at h ⊢
      cases b2 with
      | true =>
        simp only [↓reduceIte] at h
        cases h
      | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      split at h
      · rename_i ret writes'
        split at h
        · rename_i hg
          obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj h
          simp only [Bool.and_eq_true, bv_eqb_eq, writes_eqb_eq] at hg
          obtain ⟨rfl, rfl⟩ := hg
          exact (bind_set_fds_iff _ _ i m _).mpr (pure_ok _ i _)
        · cases h
      · cases h
    | none =>
      dsimp only at h ⊢
      generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) [Z_to_bv 8 0] = w1 at h ⊢
      cases w1 with
      | none => exact ret_only_sound _ _ _ _ _ i h
      | some _ => cases h

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_readv_imported_sound_unmodeled`. -/
theorem check_readv_imported_sound_unmodeled (i : SyscallInput) (fd : word) (r : ReadableFd)
    (iovs0 : List (word × word)) (eff : SyscallEffect) (m : Model)
    (h : check_readv_imported i fd r iovs0 eff m = CheckUnmodeled) :
    readv_imported fd r iovs0 i m i m Unmodeled := by
  unfold check_readv_imported check_readv_gap at h
  unfold readv_imported readv_buf_gap
  dsimp only at h ⊢
  generalize (iovs_total (cap_iovecs iovs0) == 0) = b0 at h ⊢
  cases b0 with
  | true =>
    simp only [↓reduceIte] at h
    exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases r with
  | RdChannel ch =>
    dsimp only at h ⊢
    generalize (m_stdin m).uncons = u at h ⊢
    cases u with
    | none => exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
    | some _ =>
    dsimp only at h ⊢
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) [Z_to_bv 8 0] = w1 at h ⊢
    cases w1 with
    | none => exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
    | some _ =>
    dsimp only at h ⊢
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0)
      (stream_take_z (m_stdin m) (iovs_total (cap_iovecs iovs0))).1 = w2 at h ⊢
    cases w2 with
    | none => exact unmodeled_intro i m
    | some _ =>
    exfalso
    dsimp only at h
    split at h
    · split at h
      · cases h
      · split at h <;> cases h
    · cases h
  | RdSocket sk =>
    cases sk with
    | SkFresh => exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
    | SkBound => exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
    | SkListening => exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
    | SkReset _ _ => exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
    | SkConnected peer ch rx =>
    dsimp only at h ⊢
    generalize rx.cell_at 0 = c at h ⊢
    cases c with
    | NFin => exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
    | NRst => exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
    | NTimedOut => exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
    | NByte _ =>
    dsimp only at h ⊢
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) [Z_to_bv 8 0] = w1 at h ⊢
    cases w1 with
    | none => exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
    | some _ =>
    dsimp only at h ⊢
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0)
      (net_take_z rx (iovs_total (cap_iovecs iovs0))).1 = w2 at h ⊢
    cases w2 with
    | none => exact unmodeled_intro i m
    | some _ =>
    exfalso
    dsimp only at h
    split at h
    · split at h
      · cases h
      · split at h <;> cases h
    · cases h
  | RdPipe _ => exact unmodeled_intro i m
  | RdDevNull => exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
  | RdUrandom => exact unmodeled_intro i m
  | RdDir => exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
  | RdFile p off =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only at h ⊢
    generalize rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize file_read data off (Z_to_bv 64 (iovs_total (cap_iovecs iovs0))) = bs at h ⊢
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc at h ⊢
    cases sc with
    | some writes =>
      dsimp only at h ⊢
      generalize addr_is_error_b (len_word bs) = b2 at h ⊢
      cases b2 with
      | true =>
        simp only [↓reduceIte]
        exact unmodeled_intro i m
      | false =>
      exfalso
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · split at h <;> cases h
      · cases h
    | none =>
      dsimp only at h ⊢
      generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) [Z_to_bv 8 0] = w1 at h ⊢
      cases w1 with
      | none => exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
      | some _ => exact unmodeled_intro i m
  | RdFileRW p off =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only at h ⊢
    generalize rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize file_read data off (Z_to_bv 64 (iovs_total (cap_iovecs iovs0))) = bs at h ⊢
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc at h ⊢
    cases sc with
    | some writes =>
      dsimp only at h ⊢
      generalize addr_is_error_b (len_word bs) = b2 at h ⊢
      cases b2 with
      | true =>
        simp only [↓reduceIte]
        exact unmodeled_intro i m
      | false =>
      exfalso
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · split at h <;> cases h
      · cases h
    | none =>
      dsimp only at h ⊢
      generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) [Z_to_bv 8 0] = w1 at h ⊢
      cases w1 with
      | none => exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
      | some _ => exact unmodeled_intro i m

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_readv_imported_complete_ok`. -/
theorem check_readv_imported_complete_ok (i : SyscallInput) (fd : word) (r : ReadableFd)
    (iovs0 : List (word × word)) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : readv_imported fd r iovs0 i m i m (Ok eff m' evs)) :
    check_readv_imported i fd r iovs0 eff m = CheckOk m' evs := by
  unfold readv_imported readv_buf_gap at h
  unfold check_readv_imported check_readv_gap
  dsimp only at h ⊢
  generalize (iovs_total (cap_iovecs iovs0) == 0) = b0 at h ⊢
  cases b0 with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact ret_only_complete _ _ _ _ _ i h
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases r with
  | RdChannel ch =>
    dsimp only at h ⊢
    generalize (m_stdin m).uncons = u at h ⊢
    cases u with
    | none => exact ret_only_complete _ _ _ _ _ i h
    | some _ =>
    dsimp only at h ⊢
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) [Z_to_bv 8 0] = w1 at h ⊢
    cases w1 with
    | none => exact ret_only_complete _ _ _ _ _ i h
    | some _ =>
    dsimp only at h ⊢
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0)
      (stream_take_z (m_stdin m) (iovs_total (cap_iovecs iovs0))).1 = w2 at h ⊢
    cases w2 with
    | none => cases h
    | some _ =>
    dsimp only at h ⊢
    rw [bind_choose_iff] at h
    obtain ⟨bs, ⟨h1, h3⟩, hk⟩ := h
    rw [bind_choose_iff] at hk
    obtain ⟨writes, hsc, hk⟩ := hk
    simp only [bind_set_stdin_iff, bind_emit_cases_iff] at hk
    rcases hk with ⟨y, m2, evs2, hp, heq⟩ | ⟨-, heq⟩
    · simp only [pure_iff, outcome.Ok.injEq] at hp
      obtain ⟨rfl, rfl, rfl⟩ := hp
      obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj heq
      have hcat := scatter_iovecs_concat _ _ _ _ hsc
      have hle := scatter_iovecs_length_le _ _ _ _ hsc
      simp only [hcat, hsc, bv_eqb_refl, writes_eqb_refl, decide_eq_true h1,
        decide_eq_true hle, h3, listN_eqb_refl, Bool.and_self, ↓reduceIte, List.append_nil]
    · cases heq
  | RdSocket sk =>
    cases sk with
    | SkFresh => exact ret_only_complete _ _ _ _ _ i h
    | SkBound => exact ret_only_complete _ _ _ _ _ i h
    | SkListening => exact ret_only_complete _ _ _ _ _ i h
    | SkReset _ _ => exact ret_only_complete _ _ _ _ _ i h
    | SkConnected peer ch rx =>
    dsimp only at h ⊢
    generalize rx.cell_at 0 = c at h ⊢
    cases c with
    | NFin => exact ret_only_complete _ _ _ _ _ i h
    | NRst =>
      dsimp only at h ⊢
      rw [bind_set_fds_iff] at h
      exact ret_only_complete _ _ _ _ _ i h
    | NTimedOut =>
      dsimp only at h ⊢
      rw [bind_set_fds_iff] at h
      exact ret_only_complete _ _ _ _ _ i h
    | NByte _ =>
    dsimp only at h ⊢
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) [Z_to_bv 8 0] = w1 at h ⊢
    cases w1 with
    | none => exact ret_only_complete _ _ _ _ _ i h
    | some _ =>
    dsimp only at h ⊢
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0)
      (net_take_z rx (iovs_total (cap_iovecs iovs0))).1 = w2 at h ⊢
    cases w2 with
    | none => cases h
    | some _ =>
    dsimp only at h ⊢
    rw [bind_choose_iff] at h
    obtain ⟨bs, ⟨h1, h3⟩, hk⟩ := h
    rw [bind_choose_iff] at hk
    obtain ⟨writes, hsc, hk⟩ := hk
    simp only [bind_set_fds_iff, bind_emit_cases_iff] at hk
    rcases hk with ⟨y, m2, evs2, hp, heq⟩ | ⟨-, heq⟩
    · simp only [pure_iff, outcome.Ok.injEq] at hp
      obtain ⟨rfl, rfl, rfl⟩ := hp
      obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj heq
      have hcat := scatter_iovecs_concat _ _ _ _ hsc
      have hle := scatter_iovecs_length_le _ _ _ _ hsc
      simp only [hcat, hsc, bv_eqb_refl, writes_eqb_refl, decide_eq_true h1,
        decide_eq_true hle, h3, listN_eqb_refl, Bool.and_self, ↓reduceIte, List.append_nil]
    · cases heq
  | RdPipe _ => cases h
  | RdDevNull => exact ret_only_complete _ _ _ _ _ i h
  | RdUrandom => cases h
  | RdDir => exact ret_only_complete _ _ _ _ _ i h
  | RdFile p off =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize file_read data off (Z_to_bv 64 (iovs_total (cap_iovecs iovs0))) = bs at h ⊢
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc at h ⊢
    cases sc with
    | some writes =>
      dsimp only at h ⊢
      generalize addr_is_error_b (len_word bs) = b2 at h ⊢
      cases b2 with
      | true =>
        simp only [↓reduceIte] at h
        cases h
      | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      rw [bind_set_fds_iff] at h
      simp only [pure_iff, outcome.Ok.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [bv_eqb_refl, writes_eqb_refl, Bool.and_self, ↓reduceIte]
    | none =>
      dsimp only at h ⊢
      generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) [Z_to_bv 8 0] = w1 at h ⊢
      cases w1 with
      | none => exact ret_only_complete _ _ _ _ _ i h
      | some _ => cases h
  | RdFileRW p off =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => cases h
    | some data =>
    dsimp only at h ⊢
    generalize rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact ret_only_complete _ _ _ _ _ i h
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize file_read data off (Z_to_bv 64 (iovs_total (cap_iovecs iovs0))) = bs at h ⊢
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc at h ⊢
    cases sc with
    | some writes =>
      dsimp only at h ⊢
      generalize addr_is_error_b (len_word bs) = b2 at h ⊢
      cases b2 with
      | true =>
        simp only [↓reduceIte] at h
        cases h
      | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      rw [bind_set_fds_iff] at h
      simp only [pure_iff, outcome.Ok.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [bv_eqb_refl, writes_eqb_refl, Bool.and_self, ↓reduceIte]
    | none =>
      dsimp only at h ⊢
      generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) [Z_to_bv 8 0] = w1 at h ⊢
      cases w1 with
      | none => exact ret_only_complete _ _ _ _ _ i h
      | some _ => cases h

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_readv_imported_complete_unmodeled`. -/
theorem check_readv_imported_complete_unmodeled (i : SyscallInput) (fd : word) (r : ReadableFd)
    (iovs0 : List (word × word)) (eff : SyscallEffect) (m : Model)
    (h : readv_imported fd r iovs0 i m i m Unmodeled) :
    check_readv_imported i fd r iovs0 eff m = CheckUnmodeled := by
  unfold readv_imported readv_buf_gap at h
  unfold check_readv_imported check_readv_gap
  dsimp only at h ⊢
  generalize (iovs_total (cap_iovecs iovs0) == 0) = b0 at h ⊢
  cases b0 with
  | true =>
    simp only [↓reduceIte] at h
    exact (ret_only_not_unmodeled _ i m h).elim
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases r with
  | RdChannel ch =>
    dsimp only at h ⊢
    generalize (m_stdin m).uncons = u at h ⊢
    cases u with
    | none => exact (ret_only_not_unmodeled _ i m h).elim
    | some _ =>
    dsimp only at h ⊢
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) [Z_to_bv 8 0] = w1 at h ⊢
    cases w1 with
    | none => exact (ret_only_not_unmodeled _ i m h).elim
    | some _ =>
    dsimp only at h ⊢
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0)
      (stream_take_z (m_stdin m) (iovs_total (cap_iovecs iovs0))).1 = w2 at h ⊢
    cases w2 with
    | none => rfl
    | some _ =>
    exfalso
    dsimp only at h
    rw [bind_choose_iff] at h
    obtain ⟨bs, -, hk⟩ := h
    rw [bind_choose_iff] at hk
    obtain ⟨writes, -, hk⟩ := hk
    simp only [bind_set_stdin_iff, bind_emit_cases_iff] at hk
    rcases hk with ⟨_, _, _, _, heq⟩ | ⟨hp, -⟩
    · cases heq
    · cases hp
  | RdSocket sk =>
    cases sk with
    | SkFresh => exact (ret_only_not_unmodeled _ i m h).elim
    | SkBound => exact (ret_only_not_unmodeled _ i m h).elim
    | SkListening => exact (ret_only_not_unmodeled _ i m h).elim
    | SkReset _ _ => exact (ret_only_not_unmodeled _ i m h).elim
    | SkConnected peer ch rx =>
    dsimp only at h ⊢
    generalize rx.cell_at 0 = c at h ⊢
    cases c with
    | NFin => exact (ret_only_not_unmodeled _ i m h).elim
    | NRst =>
      dsimp only at h ⊢
      rw [bind_set_fds_iff] at h
      exact (ret_only_not_unmodeled _ i _ h).elim
    | NTimedOut =>
      dsimp only at h ⊢
      rw [bind_set_fds_iff] at h
      exact (ret_only_not_unmodeled _ i _ h).elim
    | NByte _ =>
    dsimp only at h ⊢
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) [Z_to_bv 8 0] = w1 at h ⊢
    cases w1 with
    | none => exact (ret_only_not_unmodeled _ i m h).elim
    | some _ =>
    dsimp only at h ⊢
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0)
      (net_take_z rx (iovs_total (cap_iovecs iovs0))).1 = w2 at h ⊢
    cases w2 with
    | none => rfl
    | some _ =>
    exfalso
    dsimp only at h
    rw [bind_choose_iff] at h
    obtain ⟨bs, -, hk⟩ := h
    rw [bind_choose_iff] at hk
    obtain ⟨writes, -, hk⟩ := hk
    simp only [bind_set_fds_iff, bind_emit_cases_iff] at hk
    rcases hk with ⟨_, _, _, _, heq⟩ | ⟨hp, -⟩
    · cases heq
    · cases hp
  | RdPipe _ => rfl
  | RdDevNull => exact (ret_only_not_unmodeled _ i m h).elim
  | RdUrandom => rfl
  | RdDir => exact (ret_only_not_unmodeled _ i m h).elim
  | RdFile p off =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => rfl
    | some data =>
    dsimp only at h ⊢
    generalize rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize file_read data off (Z_to_bv 64 (iovs_total (cap_iovecs iovs0))) = bs at h ⊢
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc at h ⊢
    cases sc with
    | some writes =>
      dsimp only at h ⊢
      generalize addr_is_error_b (len_word bs) = b2 at h ⊢
      cases b2 with
      | true => simp only [↓reduceIte]
      | false =>
      exfalso
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      rw [bind_set_fds_iff] at h
      cases h
    | none =>
      dsimp only at h ⊢
      generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) [Z_to_bv 8 0] = w1 at h ⊢
      cases w1 with
      | none => exact (ret_only_not_unmodeled _ i m h).elim
      | some _ => rfl
  | RdFileRW p off =>
    dsimp only at h ⊢
    generalize fs_lookup (m_fs m) p = fl at h ⊢
    cases fl with
    | none => rfl
    | some data =>
    dsimp only at h ⊢
    generalize rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = b1 at h ⊢
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h
      exact (ret_only_not_unmodeled _ i m h).elim
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize file_read data off (Z_to_bv 64 (iovs_total (cap_iovecs iovs0))) = bs at h ⊢
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc at h ⊢
    cases sc with
    | some writes =>
      dsimp only at h ⊢
      generalize addr_is_error_b (len_word bs) = b2 at h ⊢
      cases b2 with
      | true => simp only [↓reduceIte]
      | false =>
      exfalso
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      rw [bind_set_fds_iff] at h
      cases h
    | none =>
      dsimp only at h ⊢
      generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) [Z_to_bv 8 0] = w1 at h ⊢
      cases w1 with
      | none => exact (ret_only_not_unmodeled _ i m h).elim
      | some _ => rfl

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_readv_sound_ok`. -/
theorem check_readv_sound_ok (i : SyscallInput) (fd iov iovcnt : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_readv i fd iov iovcnt eff m = CheckOk m' evs) :
    readv_spec fd iov iovcnt i m (Ok eff m' evs) := by
  unfold check_readv check_readv_gap at h
  unfold readv_spec
  rw [bind_input_iff, bind_get_model_iff]
  generalize import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) = A at h ⊢
  generalize import_iovecs i.in_mem iov (iovcnt32 iovcnt) = imp at h ⊢
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact ret_only_sound _ _ _ _ _ i h
  | some e =>
  dsimp only at h ⊢
  generalize readable_fd e = rd at h ⊢
  cases rd with
  | none => exact ret_only_sound _ _ _ _ _ i h
  | some r =>
  dsimp only at h ⊢
  generalize readv_heap_iovecb iovcnt = hb at h ⊢
  cases hb with
  | true =>
    simp only [↓reduceIte] at h
    cases h
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases imp with
  | ImpFault => exact ret_only_copyins_sound _ _ _ _ _ _ i h
  | ImpInval => exact ret_only_copyins_sound _ _ _ _ _ _ i h
  | ImpOk iovs0 =>
  dsimp only at h ⊢
  obtain ⟨hres, heff⟩ := check_copyin_prefix_ok_inv _ _ _ _ _ h
  rw [heff]
  exact record_copyins_ok _ _ i m _ m' evs (check_readv_imported_sound_ok _ _ _ _ _ _ _ _ hres)

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_readv_sound_unmodeled`. -/
theorem check_readv_sound_unmodeled (i : SyscallInput) (fd iov iovcnt : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_readv i fd iov iovcnt eff m = CheckUnmodeled) :
    readv_spec fd iov iovcnt i m Unmodeled := by
  unfold check_readv check_readv_gap at h
  unfold readv_spec
  rw [bind_input_iff, bind_get_model_iff]
  generalize import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) = A at h ⊢
  generalize import_iovecs i.in_mem iov (iovcnt32 iovcnt) = imp at h ⊢
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
  | some e =>
  dsimp only at h ⊢
  generalize readable_fd e = rd at h ⊢
  cases rd with
  | none => exact (check_ret_only_no_unmodeled _ _ _ _ h).elim
  | some r =>
  dsimp only at h ⊢
  generalize readv_heap_iovecb iovcnt = hb at h ⊢
  cases hb with
  | true =>
    simp only [↓reduceIte]
    exact unmodeled_intro i m
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases imp with
  | ImpFault => exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
  | ImpInval => exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ h).elim
  | ImpOk iovs0 =>
  dsimp only at h ⊢
  exact record_copyins_unmodeled _ _ i m
    (check_readv_imported_sound_unmodeled _ _ _ _ _ _
      (check_copyin_prefix_unmodeled_inv _ _ _ h))

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_readv_complete_ok`. -/
theorem check_readv_complete_ok (i : SyscallInput) (fd iov iovcnt : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : readv_spec fd iov iovcnt i m (Ok eff m' evs)) :
    check_readv i fd iov iovcnt eff m = CheckOk m' evs := by
  unfold readv_spec at h
  unfold check_readv check_readv_gap
  rw [bind_input_iff, bind_get_model_iff] at h
  generalize import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) = A at h ⊢
  generalize import_iovecs i.in_mem iov (iovcnt32 iovcnt) = imp at h ⊢
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact ret_only_complete _ _ _ _ _ i h
  | some e =>
  dsimp only at h ⊢
  generalize readable_fd e = rd at h ⊢
  cases rd with
  | none => exact ret_only_complete _ _ _ _ _ i h
  | some r =>
  dsimp only at h ⊢
  generalize readv_heap_iovecb iovcnt = hb at h ⊢
  cases hb with
  | true =>
    simp only [↓reduceIte] at h
    exact (readv_heap_gap_no_ok _ _ _ _ _ h).elim
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases imp with
  | ImpFault => exact ret_only_copyins_complete _ _ _ _ _ _ i h
  | ImpInval => exact ret_only_copyins_complete _ _ _ _ _ _ i h
  | ImpOk iovs0 =>
  dsimp only at h ⊢
  obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
  rw [strip_copyin_prefix_record, check_readv_imported_complete_ok _ _ _ _ _ _ _ _ hcore]
  exact check_copyin_prefix_record_ok _ _ _ _

/-- Rocq: `Checks.Sys.Fs.ReadWrite.check_readv_complete_unmodeled`. -/
theorem check_readv_complete_unmodeled (i : SyscallInput) (fd iov iovcnt : word)
    (eff : SyscallEffect) (m : Model) (h : readv_spec fd iov iovcnt i m Unmodeled) :
    check_readv i fd iov iovcnt eff m = CheckUnmodeled := by
  unfold readv_spec at h
  unfold check_readv check_readv_gap
  rw [bind_input_iff, bind_get_model_iff] at h
  generalize import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) = A at h ⊢
  generalize import_iovecs i.in_mem iov (iovcnt32 iovcnt) = imp at h ⊢
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact (ret_only_not_unmodeled _ i m h).elim
  | some e =>
  dsimp only at h ⊢
  generalize readable_fd e = rd at h ⊢
  cases rd with
  | none => exact (ret_only_not_unmodeled _ i m h).elim
  | some r =>
  dsimp only at h ⊢
  generalize readv_heap_iovecb iovcnt = hb at h ⊢
  cases hb with
  | true => simp only [↓reduceIte]
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases imp with
  | ImpFault => exact (record_ret_only_not_unmodeled _ _ i m h).elim
  | ImpInval => exact (record_ret_only_not_unmodeled _ _ i m h).elim
  | ImpOk iovs0 =>
  dsimp only at h ⊢
  rw [check_readv_imported_complete_unmodeled _ _ _ _ _ _ (record_copyins_unmodeled_inv _ _ i m h)]
  rfl

/-- A witness for `writev_spec` (Rocq: `Checks.Witness.Fs.ReadWrite.writev_witness`):
wherever the spec admits an outcome, one of them, chosen arm for arm as
Rocq's witness chooses, and `Unmodeled` wherever the spec declines;
`writev_witness_ok` is the statement that every answer is admitted.  The
three file arms decline where the spec twin's do: a path the file system
does not hold, and an error-encoded length; the `FdFileW` and `FdFileRW`
arms also decline the hole `modeled_file_gap` refuses.  A gathered prefix
shorter than the capped aggregate is written, as the spec twin writes it. -/
def writev_witness (fd iov iovcnt : word) (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some (.FdChannel ch) =>
      if w_is0 ch then ret_outcome (errno_ret EBADF) m   -- stdin is read-only
      else outcome_copyins (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
        (match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
         | .ImpFault => ret_outcome (errno_ret EFAULT) m
         | .ImpInval => ret_outcome (errno_ret EINVAL) m
         | .ImpOk iovs0 =>
             let total := iovs_total (cap_iovecs iovs0)
             let bs := writev_gathered i.in_mem iovs0
             if total == 0 then ret_outcome (Z_to_bv 64 0) m   -- zero aggregate
             else if bs.length == 0 then ret_outcome (errno_ret EFAULT) m   -- nothing gatherable
             else if addr_is_error_b (len_word bs) then Unmodeled
             else outcome_copyins (iov_prefix_accesses (cap_iovecs iovs0) (bs.take 1).length)
                    (Ok (mkEffect (len_word (bs.take 1)) [] []) m
                      (List.map (WriteEv ch) (bs.take 1))))   -- the one-byte delivery
  | some .FdDir => ret_outcome (errno_ret EBADF) m   -- directory fd is O_RDONLY
  | some (.FdFile _ _) => ret_outcome (errno_ret EBADF) m   -- read-only file
  | some (.FdPipe _ w) =>
      if !w then ret_outcome (errno_ret EBADF) m   -- read end
      else outcome_copyins (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
        (match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
         | .ImpFault => ret_outcome (errno_ret EFAULT) m
         | .ImpInval => ret_outcome (errno_ret EINVAL) m
         | .ImpOk iovs0 =>
             if iovs_total (cap_iovecs iovs0) == 0 then ret_outcome (Z_to_bv 64 0) m
             else Unmodeled)   -- vectored pipe writes
  | some .FdUrandom => ret_outcome (errno_ret EBADF) m   -- read-only
  | some (.FdDevNull _ wr) =>
      if !wr then ret_outcome (errno_ret EBADF) m
      else outcome_copyins (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
        (match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
         | .ImpFault => ret_outcome (errno_ret EFAULT) m
         | .ImpInval => ret_outcome (errno_ret EINVAL) m
         | .ImpOk iovs0 => ret_outcome (Z_to_bv 64 (iovs_total (cap_iovecs iovs0))) m)
  | some (.FdFileW p off) =>
      outcome_copyins (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
        (match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
         | .ImpFault => ret_outcome (errno_ret EFAULT) m
         | .ImpInval => ret_outcome (errno_ret EINVAL) m
         | .ImpOk iovs0 =>
             let total := iovs_total (cap_iovecs iovs0)
             let bs := writev_gathered i.in_mem iovs0
             if total == 0 then ret_outcome (Z_to_bv 64 0) m
             else if rw_pos_einvalb off total then ret_outcome (errno_ret EINVAL) m
             else if bs.length == 0 then ret_outcome (errno_ret EFAULT) m
             else
               match fs_lookup (m_fs m) p with
               | none => Unmodeled
               | some data =>
                   if !modeled_file_gap data off bs then Unmodeled   -- hole too large
                   else if addr_is_error_b (len_word bs) then Unmodeled
                   else outcome_copyins (iov_prefix_accesses (cap_iovecs iovs0) bs.length)
                     (Ok (mkEffect (len_word bs) [] [])
                        (with_fds (fd_insert (m_fds m) fd (.FdFileW p (off + len_word bs)))
                          (with_fs (fs_set (m_fs m) p (file_write data off bs)) m))
                        []))
  | some (.FdFileRW p off) =>   -- the `FdFileW` arm above, on the O_RDWR kind
      outcome_copyins (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
        (match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
         | .ImpFault => ret_outcome (errno_ret EFAULT) m
         | .ImpInval => ret_outcome (errno_ret EINVAL) m
         | .ImpOk iovs0 =>
             let total := iovs_total (cap_iovecs iovs0)
             let bs := writev_gathered i.in_mem iovs0
             if total == 0 then ret_outcome (Z_to_bv 64 0) m
             else if rw_pos_einvalb off total then ret_outcome (errno_ret EINVAL) m
             else if bs.length == 0 then ret_outcome (errno_ret EFAULT) m
             else
               match fs_lookup (m_fs m) p with
               | none => Unmodeled
               | some data =>
                   if !modeled_file_gap data off bs then Unmodeled   -- hole too large
                   else if addr_is_error_b (len_word bs) then Unmodeled
                   else outcome_copyins (iov_prefix_accesses (cap_iovecs iovs0) bs.length)
                     (Ok (mkEffect (len_word bs) [] [])
                        (with_fds (fd_insert (m_fds m) fd (.FdFileRW p (off + len_word bs)))
                          (with_fs (fs_set (m_fs m) p (file_write data off bs)) m))
                        []))
  | some (.FdFileA p off) =>
      outcome_copyins (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
        (match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
         | .ImpFault => ret_outcome (errno_ret EFAULT) m
         | .ImpInval => ret_outcome (errno_ret EINVAL) m
         | .ImpOk iovs0 =>
             let total := iovs_total (cap_iovecs iovs0)
             let bs := writev_gathered i.in_mem iovs0
             if total == 0 then ret_outcome (Z_to_bv 64 0) m
             else if rw_pos_einvalb off total then ret_outcome (errno_ret EINVAL) m
             else if bs.length == 0 then ret_outcome (errno_ret EFAULT) m
             else
               match fs_lookup (m_fs m) p with
               | none => Unmodeled
               | some data =>
                   if addr_is_error_b (len_word bs) then Unmodeled
                   else outcome_copyins (iov_prefix_accesses (cap_iovecs iovs0) bs.length)
                     (Ok (mkEffect (len_word bs) [] [])
                        (with_fds (fd_insert (m_fds m) fd (.FdFileA p (append_new_pos data bs off)))
                          (with_fs (fs_set (m_fs m) p (file_write data (len_word data) bs)) m))
                        []))
  | some (.FdSocket _) => Unmodeled   -- `Sys.Fs.ReadWrite.writev_buf_gap`

/-- Rocq: `Checks.Witness.Fs.ReadWrite.writev_witness_ok`. -/
theorem writev_witness_ok (fd iov iovcnt : word) (i : SyscallInput) (m : Model) :
    writev_spec fd iov iovcnt i m (writev_witness fd iov iovcnt i m) := by
  unfold writev_spec writev_witness writev_file_arm writev_ledger writev_buf_gap
  rw [bind_input_iff, bind_get_model_iff]
  generalize import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) = A
  generalize import_iovecs i.in_mem iov (iovcnt32 iovcnt) = imp
  generalize fd_lookup (m_fds m) fd = r
  cases r with
  | none => exact pure_ok _ i _
  | some e =>
  cases e with
  | FdFile _ _ => exact pure_ok _ i _
  | FdDir => exact pure_ok _ i _
  | FdSocket _ => exact unmodeled_intro i m
  | FdUrandom => exact pure_ok _ i _
  | FdChannel ch =>
    dsimp only
    generalize w_is0 ch = b0
    cases b0 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply record_copyins_outcome
    cases imp with
    | ImpFault => exact pure_ok _ i _
    | ImpInval => exact pure_ok _ i _
    | ImpOk iovs0 =>
    dsimp only
    generalize (iovs_total (cap_iovecs iovs0) == 0) = b1
    cases b1 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize writev_gathered i.in_mem iovs0 = bs
    generalize hb2 : (bs.length == 0) = b2
    cases b2 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize addr_is_error_b (len_word bs) = b3
    cases b3 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hne := beq_eq_false_iff_ne.mp hb2
    have hlen1 : (bs.take 1).length = 1 := by
      rw [List.length_take]
      omega
    rw [bind_choose_iff]
    refine ⟨bs.take 1, ⟨by omega, by rw [hlen1]⟩, ?_⟩
    exact witness_bind_ok_eq _ _ i m () m _ _ m [] _ (emit_ok _ i m)
      (record_copyins_outcome _ _ i m _ (pure_ok _ i m)) (List.append_nil _).symm
  | FdFileW p off =>
    dsimp only
    generalize fs_lookup (m_fs m) p = fl
    apply record_copyins_outcome
    cases imp with
    | ImpFault => exact pure_ok _ i _
    | ImpInval => exact pure_ok _ i _
    | ImpOk iovs0 =>
    dsimp only
    generalize (iovs_total (cap_iovecs iovs0) == 0) = b1
    cases b1 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = b2
    cases b2 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize writev_gathered i.in_mem iovs0 = bs
    generalize (bs.length == 0) = b3
    cases b3 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only
    generalize (!modeled_file_gap data off bs) = b4
    cases b4 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize addr_is_error_b (len_word bs) = b5
    cases b5 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [bind_set_fs_iff, bind_set_fds_iff]
    exact record_copyins_outcome _ _ i _ _ (pure_ok _ i _)
  | FdFileRW p off =>
    dsimp only
    generalize fs_lookup (m_fs m) p = fl
    apply record_copyins_outcome
    cases imp with
    | ImpFault => exact pure_ok _ i _
    | ImpInval => exact pure_ok _ i _
    | ImpOk iovs0 =>
    dsimp only
    generalize (iovs_total (cap_iovecs iovs0) == 0) = b1
    cases b1 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = b2
    cases b2 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize writev_gathered i.in_mem iovs0 = bs
    generalize (bs.length == 0) = b3
    cases b3 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only
    generalize (!modeled_file_gap data off bs) = b4
    cases b4 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize addr_is_error_b (len_word bs) = b5
    cases b5 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [bind_set_fs_iff, bind_set_fds_iff]
    exact record_copyins_outcome _ _ i _ _ (pure_ok _ i _)
  | FdFileA p off =>
    dsimp only
    generalize fs_lookup (m_fs m) p = fl
    apply record_copyins_outcome
    cases imp with
    | ImpFault => exact pure_ok _ i _
    | ImpInval => exact pure_ok _ i _
    | ImpOk iovs0 =>
    dsimp only
    generalize (iovs_total (cap_iovecs iovs0) == 0) = b1
    cases b1 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = b2
    cases b2 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize writev_gathered i.in_mem iovs0 = bs
    generalize (bs.length == 0) = b3
    cases b3 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only
    generalize addr_is_error_b (len_word bs) = b5
    cases b5 with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [bind_set_fs_iff, bind_set_fds_iff]
    exact record_copyins_outcome _ _ i _ _ (pure_ok _ i _)
  | FdPipe _ w =>
    dsimp only
    cases w with
    | false =>
      simp only [Bool.not_false, ↓reduceIte]
      exact pure_ok _ i _
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    apply record_copyins_outcome
    cases imp with
    | ImpFault => exact pure_ok _ i _
    | ImpInval => exact pure_ok _ i _
    | ImpOk iovs0 =>
    dsimp only
    generalize (iovs_total (cap_iovecs iovs0) == 0) = b1
    cases b1 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact unmodeled_intro i m
  | FdDevNull _ wr =>
    dsimp only
    cases wr with
    | false =>
      simp only [Bool.not_false, ↓reduceIte]
      exact pure_ok _ i _
    | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    apply record_copyins_outcome
    cases imp with
    | ImpFault => exact pure_ok _ i _
    | ImpInval => exact pure_ok _ i _
    | ImpOk iovs0 => exact pure_ok _ i _

/-- A witness for `readv_spec` (Rocq: `Checks.Witness.Fs.ReadWrite.readv_witness`):
wherever the spec admits an outcome, one of them, chosen arm for arm as
Rocq's witness chooses, and `Unmodeled` wherever the spec declines;
`readv_witness_ok` is the statement that every answer is admitted.  The
one-byte scatter's `none` arm is unreachable once a
zero byte scatters — byte values do not affect writability
(`State.scatter_iovecs_singleton_some`) — and answers `Unmodeled` only to
keep the match total. -/
def readv_witness (fd iov iovcnt : word) (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some e =>
      match readable_fd e with
      | none => ret_outcome (errno_ret EBADF) m
      | some r =>
          if readv_heap_iovecb iovcnt then Unmodeled
          else
          outcome_copyins (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
          (match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
          | .ImpFault => ret_outcome (errno_ret EFAULT) m
          | .ImpInval => ret_outcome (errno_ret EINVAL) m
          | .ImpOk iovs0 =>
              let iovs := cap_iovecs iovs0
              let total := iovs_total iovs
              if total == 0 then ret_outcome (Z_to_bv 64 0) m
              else
              match r with
              | .RdChannel ch =>
                  match (m_stdin m).uncons with
                  | none => ret_outcome (Z_to_bv 64 0) m
                  | some (b, s') =>
                      match scatter_iovecs i.in_wmem iovs [Z_to_bv 8 0] with
                      | none => ret_outcome (errno_ret EFAULT) m
                      | some _ =>
                          match scatter_iovecs i.in_wmem iovs
                                  (stream_take_z (m_stdin m) total).1 with
                          | none => Unmodeled   -- partially writable destination
                          | some _ =>
                              match scatter_iovecs i.in_wmem iovs [b] with
                              | none => Unmodeled   -- unreachable: see the docstring
                              | some writes =>
                                  Ok (mkEffect (Z_to_bv 64 1) writes []) (with_stdin s' m)
                                    [ReadEv ch b]
              | .RdPipe _ => Unmodeled   -- vectored pipe reads
              | .RdDevNull => ret_outcome (Z_to_bv 64 0) m
              | .RdUrandom => Unmodeled   -- vectored device reads decline
              | .RdDir => ret_outcome (errno_ret EISDIR) m
              | .RdSocket sk =>
                  match sk with
                  | .SkConnected peer ch rx =>
                      match rx.cell_at 0 with
                      | .NFin => ret_outcome (Z_to_bv 64 0) m
                      | .NRst =>
                          ret_outcome (errno_ret ECONNRESET)
                            (with_fds (fd_insert (m_fds m) fd (.FdSocket (.SkReset peer ch))) m)
                      | .NTimedOut =>
                          ret_outcome (errno_ret ETIMEDOUT)
                            (with_fds (fd_insert (m_fds m) fd (.FdSocket (.SkReset peer ch))) m)
                      | .NByte b =>
                          match scatter_iovecs i.in_wmem iovs [Z_to_bv 8 0] with
                          | none => ret_outcome (errno_ret EFAULT) m
                          | some _ =>
                              match scatter_iovecs i.in_wmem iovs (net_take_z rx total).1 with
                              | none => Unmodeled   -- partially writable destination
                              | some _ =>
                                  match scatter_iovecs i.in_wmem iovs [b] with
                                  | none => Unmodeled   -- unreachable: see the docstring
                                  | some writes =>
                                      Ok (mkEffect (Z_to_bv 64 1) writes [])
                                        (with_fds (fd_insert (m_fds m) fd
                                          (.FdSocket (.SkConnected peer ch (net_take rx 1).2))) m)
                                        [ReadEv ch b]
                  | .SkReset _ _ => ret_outcome (Z_to_bv 64 0) m
                  | .SkFresh | .SkBound | .SkListening => ret_outcome (errno_ret ENOTCONN) m
              | .RdFile p off =>
                  match fs_lookup (m_fs m) p with
                  | none => Unmodeled
                  | some data =>
                      if rw_pos_einvalb off total then ret_outcome (errno_ret EINVAL) m
                      else
                      let bs := file_read data off (Z_to_bv 64 total)
                      match scatter_iovecs i.in_wmem iovs bs with
                      | some writes =>
                          if addr_is_error_b (len_word bs) then Unmodeled
                          else Ok (mkEffect (len_word bs) writes [])
                                 (with_fds (fd_insert (m_fds m) fd
                                   (.FdFile p (off + len_word bs))) m) []
                      | none =>
                          match scatter_iovecs i.in_wmem iovs [Z_to_bv 8 0] with
                          | none => ret_outcome (errno_ret EFAULT) m
                          | some _ => Unmodeled
              | .RdFileRW p off =>   -- the `RdFile` arm above, on the O_RDWR kind
                  match fs_lookup (m_fs m) p with
                  | none => Unmodeled
                  | some data =>
                      if rw_pos_einvalb off total then ret_outcome (errno_ret EINVAL) m
                      else
                      let bs := file_read data off (Z_to_bv 64 total)
                      match scatter_iovecs i.in_wmem iovs bs with
                      | some writes =>
                          if addr_is_error_b (len_word bs) then Unmodeled
                          else Ok (mkEffect (len_word bs) writes [])
                                 (with_fds (fd_insert (m_fds m) fd
                                   (.FdFileRW p (off + len_word bs))) m) []
                      | none =>
                          match scatter_iovecs i.in_wmem iovs [Z_to_bv 8 0] with
                          | none => ret_outcome (errno_ret EFAULT) m
                          | some _ => Unmodeled)

/-- Rocq: `Checks.Witness.Fs.ReadWrite.readv_witness_ok`. -/
theorem readv_witness_ok (fd iov iovcnt : word) (i : SyscallInput) (m : Model) :
    readv_spec fd iov iovcnt i m (readv_witness fd iov iovcnt i m) := by
  unfold readv_spec readv_witness readv_imported readv_heap_gap readv_buf_gap
  rw [bind_input_iff, bind_get_model_iff]
  generalize import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) = A
  generalize import_iovecs i.in_mem iov (iovcnt32 iovcnt) = imp
  generalize fd_lookup (m_fds m) fd = r
  cases r with
  | none => exact pure_ok _ i _
  | some e =>
  dsimp only
  generalize readable_fd e = rd
  cases rd with
  | none => exact pure_ok _ i _
  | some r =>
  dsimp only
  generalize readv_heap_iovecb iovcnt = hb
  cases hb with
  | true =>
    simp only [↓reduceIte]
    exact unmodeled_intro i m
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply record_copyins_outcome
  cases imp with
  | ImpFault => exact pure_ok _ i _
  | ImpInval => exact pure_ok _ i _
  | ImpOk iovs0 =>
  dsimp only
  generalize (iovs_total (cap_iovecs iovs0) == 0) = b0
  cases b0 with
  | true =>
    simp only [↓reduceIte]
    exact pure_ok _ i _
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases r with
  | RdChannel ch =>
    dsimp only
    cases hu : (m_stdin m).uncons with
    | none => exact pure_ok _ i _
    | some u =>
    obtain ⟨b, s'⟩ := u
    dsimp only
    cases hw1 : scatter_iovecs i.in_wmem (cap_iovecs iovs0) [Z_to_bv 8 0] with
    | none => exact pure_ok _ i _
    | some one =>
    dsimp only
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0)
      (stream_take_z (m_stdin m) (iovs_total (cap_iovecs iovs0))).1 = w2
    cases w2 with
    | none => exact unmodeled_intro i m
    | some _ =>
    dsimp only
    obtain ⟨writes, hsc⟩ := scatter_iovecs_singleton_some _ _ _ _ b hw1
    rw [hsc]
    dsimp only
    have hst := stream_take_one_of_uncons _ _ _ hu
    rw [bind_choose_iff]
    refine ⟨[b], ⟨Int.le_refl _, ?_⟩, ?_⟩
    · show (stream_take (m_stdin m) 1).1 = [b]
      rw [hst]
    rw [bind_choose_iff]
    refine ⟨writes, hsc, ?_⟩
    show (set_stdin (stream_take (m_stdin m) 1).2 ;;
          emit (List.map (ReadEv ch) [b]) ;;
          Monad.pure (mkEffect (len_word [b]) writes [])) i m
           (Ok (mkEffect (Z_to_bv 64 1) writes []) (with_stdin s' m) [ReadEv ch b])
    rw [hst]
    exact (bind_set_stdin_iff _ _ i m _).mpr (emit_pure_ok _ _ i _)
  | RdPipe _ => exact unmodeled_intro i m
  | RdDevNull => exact pure_ok _ i _
  | RdUrandom => exact unmodeled_intro i m
  | RdDir => exact pure_ok _ i _
  | RdSocket sk =>
    cases sk with
    | SkFresh => exact pure_ok _ i _
    | SkBound => exact pure_ok _ i _
    | SkListening => exact pure_ok _ i _
    | SkReset _ _ => exact pure_ok _ i _
    | SkConnected peer ch rx =>
    dsimp only
    cases hcell : rx.cell_at 0 with
    | NFin => exact pure_ok _ i _
    | NRst => exact (bind_set_fds_iff _ _ i m _).mpr (pure_ok _ i _)
    | NTimedOut => exact (bind_set_fds_iff _ _ i m _).mpr (pure_ok _ i _)
    | NByte b =>
    dsimp only
    cases hw1 : scatter_iovecs i.in_wmem (cap_iovecs iovs0) [Z_to_bv 8 0] with
    | none => exact pure_ok _ i _
    | some one =>
    dsimp only
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0)
      (net_take_z rx (iovs_total (cap_iovecs iovs0))).1 = w2
    cases w2 with
    | none => exact unmodeled_intro i m
    | some _ =>
    dsimp only
    obtain ⟨writes, hsc⟩ := scatter_iovecs_singleton_some _ _ _ _ b hw1
    rw [hsc]
    dsimp only
    have hnt := net_take_one_bytes_of_head _ _ hcell
    rw [bind_choose_iff]
    refine ⟨[b], ⟨Int.le_refl _, hnt⟩, ?_⟩
    rw [bind_choose_iff]
    refine ⟨writes, hsc, ?_⟩
    exact (bind_set_fds_iff _ _ i m _).mpr (emit_pure_ok _ _ i _)
  | RdFile p off =>
    dsimp only
    generalize fs_lookup (m_fs m) p = fl
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only
    generalize rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = b1
    cases b1 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize file_read data off (Z_to_bv 64 (iovs_total (cap_iovecs iovs0))) = bs
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc
    cases sc with
    | some writes =>
      dsimp only
      generalize addr_is_error_b (len_word bs) = b2
      cases b2 with
      | true =>
        simp only [↓reduceIte]
        exact unmodeled_intro i m
      | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact (bind_set_fds_iff _ _ i m _).mpr (pure_ok _ i _)
    | none =>
      dsimp only
      generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) [Z_to_bv 8 0] = w1
      cases w1 with
      | none => exact pure_ok _ i _
      | some _ => exact unmodeled_intro i m
  | RdFileRW p off =>
    dsimp only
    generalize fs_lookup (m_fs m) p = fl
    cases fl with
    | none => exact unmodeled_intro i m
    | some data =>
    dsimp only
    generalize rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = b1
    cases b1 with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i _
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize file_read data off (Z_to_bv 64 (iovs_total (cap_iovecs iovs0))) = bs
    generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc
    cases sc with
    | some writes =>
      dsimp only
      generalize addr_is_error_b (len_word bs) = b2
      cases b2 with
      | true =>
        simp only [↓reduceIte]
        exact unmodeled_intro i m
      | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact (bind_set_fds_iff _ _ i m _).mpr (pure_ok _ i _)
    | none =>
      dsimp only
      generalize scatter_iovecs i.in_wmem (cap_iovecs iovs0) [Z_to_bv 8 0] = w1
      cases w1 with
      | none => exact pure_ok _ i _
      | some _ => exact unmodeled_intro i m

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite
