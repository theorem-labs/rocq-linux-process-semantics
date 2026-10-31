-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/State.v
import LinuxProcessSemantics.LinuxProcessSem.Fs
import LinuxProcessSemantics.LinuxProcessSem.State.Streams

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058 -/

/-! # LinuxProcessSem.State.Fd — descriptors and their table

One part of `State.v`'s twin, re-exported by `State.lean`, whose header
says how the ten parts divide the Rocq file, what a part may hold and
where the pins live.

WHAT GOES HERE: what a descriptor can be (`FdEntry`, `SockState`,
the pipe buffer type and `PIPE_BUF`), the fd table helpers, and the
descriptor allocator ticket A7 ported.  The pipe helpers over
`PipeBuf` are `State/Pipes.lean`.

TRUST BOUNDARY: this file is part of the trusted specification. -/

namespace LinuxProcessSemantics.LinuxProcessSem.State

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Fs

/-! ## Descriptors -/

inductive SockState : Type
  | SkFresh
  | SkBound
  | SkListening
  | SkConnected (peer : PeerAddr) (chan : word) (rx : NetStream)
  | SkReset (peer : PeerAddr) (chan : word)

/-- `PIPE_BUF` (include/uapi/linux/limits.h). -/
def PIPE_BUF : Int := 4096

/-- One pipe: the bytes it holds and the merge high-water mark.  An
`abbrev`, as Rocq's `Definition PipeBuf : Type := list byte * Z.` is
transparent: a `def` here is opaque to `simp`'s unifier, which rewrites
under `withReducible` and checks a metavariable's type at `implicit`
transparency — reducible, instance-reducible and implicit-reducible
constants, never a plain `def` (Lean 4.34, `withSimpContext` in
`Lean.Meta.Tactic.Simp.Types` and `checkTypesAndAssign` in
`Lean.Meta.ExprDefEq`).  So no equation lemma with a `PipeBuf`-typed
pattern variable applied as a REWRITE RULE — `pipe_lookup`'s own
`pipe_lookup ((k, st) :: r) id = …` on a literal pipe table, the route
`sys_norm` takes — could fire: the metavariable `st : PipeBuf` is
assigned a pair whose inferred type is `List byte × Int`, and that type
check fails.  Unfolding `pipe_lookup` by name always worked; the pins do
not go that way.  A pin over a pipe read therefore stayed stuck on its
`match` until this word changed, and `Checks/Cases/State.lean`'s
`pipe_lookup_literal_by_equation_lemma` is the pin that stops closing if
it changes back. -/
abbrev PipeBuf : Type := List byte × Int

inductive FdEntry : Type
  | FdChannel (chan : word)
  | FdFile (p : path) (offset : word)
  | FdFileW (p : path) (offset : word)
  /-- A file opened O_WRONLY|O_CREAT|O_APPEND, Rocq's `FdFileA`
  (State.v:2578-2596 at 96c2debdb): write-only, and a write lands at the
  CURRENT end of the file.  `iocb_flags` (include/linux/fs.h,
  Linux v6.18.46) turns O_APPEND into IOCB_APPEND, and
  `generic_write_checks_count` (fs/read_write.c, same version, reached
  through `generic_write_checks`) then sets the iocb's position to
  `i_size_read(inode)` for any write of nonzero length, whatever `offset`
  says and wherever an `lseek` left it.
  A separate constructor rather than a flag on `FdFileW`, because a flag
  would let every `FdFileW` arm absorb an append fd —
  `Sys.Fs.Fcntl.setfl_noop_on`'s `true` among them, which would let
  F_SETFL clear O_APPEND unseen (that definition says why).

  `offset` is still the file's `f_pos`, which `lseek` repositions and a
  write leaves at the new end of file; no write position is derived from
  it.

  NO RUN CAN HOLD ONE YET, for the reason the `FdFileRW` note below gives,
  with the append word in place of the read-write ones: the arm that mints
  the kind, Rocq's `Open.open_append`, is `unported:` in
  `Sys/Fs/Open.lean`, whose `openat_resolved_spec` declines the append
  word on a plain name, and `File.dup_modeled_entry` and
  `Kernel.Fork.clone_no_shared_file_b` refuse this kind as they refuse
  that one.  This stops being true when `Sys/Fs/Open.lean` ports
  `open_append`. -/
  | FdFileA (p : path) (offset : word)
  /-- A file opened O_RDWR, Rocq's `FdFileRW` (State.v:2597-2619 at
  96c2debdb): the one file kind on which both directions answer, at the
  one `f_pos` both advance.  A separate constructor rather than a flag on
  `FdFile` or `FdFileW`, because every `FdFile` arm answers -EBADF to a
  write and every `FdFileW` arm -EBADF to a read, and a flag would let
  each absorb this kind with a -EBADF Linux never returns.

  NO RUN CAN HOLD ONE YET, which is what lets the spec arms that decline
  it (each file's header declares its own) narrow nothing an example
  reaches.  `State.init_model` starts the table with three channels; the
  arm that mints the kind, Rocq's `Open.open_rdwr`, is `unported:` in
  `Sys/Fs/Open.lean`, whose `openat_resolved_spec` declines every
  read-write word on a plain name; `File.dup_modeled_entry` declines to
  copy an entry of this kind and `Kernel.Fork.clone_no_shared_file_b` to
  share a table holding one.  This stops being true when
  `Sys/Fs/Open.lean` ports `open_rdwr`. -/
  | FdFileRW (p : path) (offset : word)
  | FdDir
  | FdSocket (sk : SockState)
  | FdPipe (id : word) (writer : Bool)
  /-- The character device /dev/null, with the access mode the open
  granted (see the Rocq constructor's note). -/
  | FdDevNull (rd wr : Bool)
  /-- The character device /dev/urandom, open read-only; its reads
  consume the run's declared stream (see the Rocq constructor's note). -/
  | FdUrandom

/-! ## fd table helpers -/

def fd_lookup (fds : List (word × FdEntry)) (fd : word) : Option FdEntry :=
  match fds with
  | [] => none
  | (k, e) :: r => if bv_eqb k fd then some e else fd_lookup r fd

def fd_insert (fds : List (word × FdEntry)) (fd : word) (e : FdEntry)
    : List (word × FdEntry) :=
  (fd, e) :: fds.filter (fun p => !(bv_eqb p.1 fd))

def fd_remove (fds : List (word × FdEntry)) (fd : word) : List (word × FdEntry) :=
  fds.filter (fun p => !(bv_eqb p.1 fd))

/-! ## Descriptor allocation — ticket A7 (`alloc_fd_aux`, `alloc_fd`, `alloc_fd2`)

Mirrors the descriptor-allocation block of `theories/LinuxProcessSem/State.v`
(the three definitions after `fd_remove`).  The fuel argument and the
4096 bound are argued on the Rocq definitions, with one condition worth
stating here: the answer is the kernel's only while some descriptor in
0..4096 is free — the scan tests 0..4095 and answers 4096 unconditionally
when all of them are held, so with descriptors 0..4096 all live it
answers 4096, a HELD descriptor, where Linux answers 4097 when
`RLIMIT_NOFILE` is above 4097 and -EMFILE when it is 4097 (the
`fd >= end` test of `alloc_fd`, fs/file.c:591-593, Linux v6.18.46, commit
1f99e9ab748f).  Every caller tests the answer's freeness, and Rocq fixes
the SHAPE of that test: `Fs.File.lowest_fd` (Sys/Fs/File.v) conjoins
freeness onto a `choose`, so a held answer EMPTIES its success set and
the caller's `alt (errno_from …) (… lowest_fd …)` — openat, dup, pipe2,
socket, accept4 — is left with the injected errno as its only outcome,
so Linux's success at 4097 is neither admitted nor declared unmodeled;
`Net.Socket.socketpair_fds` alone declines.  A twin keeps that shape:
`linux-process-semantics@ff0313ba4f:bugs/fd-allocation-ignores-rlimit-nofile.md` records what it
costs and names the decline as a fix not taken, not as the rule.  This header
carries the kernel reading behind the LOWEST-free answer, which the Rocq
prose leaves to `Fs.File.lowest_fd`.

Kernel (fs/file.c, Linux v6.18.46, commit 1f99e9ab748f): every allocation
the model sees goes through `get_unused_fd_flags`, which is
`__get_unused_fd_flags(flags, rlimit(RLIMIT_NOFILE))`, which is
`alloc_fd(0, nofile, flags)`.  That stops being true when `fcntl`'s
`F_DUPFD` or `F_DUPFD_CLOEXEC` lands: both reach `f_dupfd`, which calls
`alloc_fd` with the caller's `arg` as `start`, a parameter neither Rocq's
`alloc_fd` nor this one takes.  `alloc_fd` starts its scan
at `start`, or at `files->next_fd` if that is higher, and takes the first
clear bit `find_next_fd` reports at or above that point.  The hint can
never sit above the lowest free descriptor: `alloc_fd` raises it only just
past a descriptor it has taken (and only when `start <= next_fd`, always
so from 0), `__put_unused_fd` lowers it to any descriptor released below
it, `do_dup2` sets a bit without touching it, and `dup_fd` resets it to 0
for a new table.  So with `start = 0` the answer is the lowest descriptor
the table does not hold, whatever order the table was built in.

What `alloc_fd` does NOT model is any errno exit of the kernel's
`alloc_fd`: the `-EMFILE` when the descriptor reaches
`end = rlimit(RLIMIT_NOFILE)`, and the `-EMFILE` at `sysctl_nr_open` or
`-ENOMEM` from `alloc_fdtable` that `expand_files` hands back when the
table must grow.  It does not read `m_nofile`; every one of those gates
stays with the calling spec, as in Rocq. -/

/-- The lowest candidate at or above `cand` that `fds` does not hold, looking
at no more than `fuel` candidates; with the fuel exhausted the current
candidate is answered even when held, and callers test the answer for
freeness (`Fs.File.lowest_fd` in Rocq).  `alloc_fd` in fs/file.c (Linux
v6.18.46, commit 1f99e9ab748f) is the same scan over the `open_fds`
bitmap: it starts at the larger of `start` and `files->next_fd` and
takes the first clear bit `find_next_fd` reports, answering -EMFILE when
that bit is at or past `end` (:591-593) and otherwise expanding the table
and scanning again when it is at or past `max_fds` (:595-600); with
`start = 0`
and the hint never above the lowest free descriptor (the header's
argument), that is the scan from 0 to the first clear bit. -/
def alloc_fd_aux (fds : List (word × FdEntry)) (cand : word) (fuel : Nat) : word :=
  match fuel with
  | 0 => cand
  | f + 1 =>
    match fd_lookup fds cand with
    | none => cand
    | some _ => alloc_fd_aux fds (cand + 1) f

/-- The descriptor the kernel hands out: the lowest one `fds` does not hold
(`alloc_fd(0, nofile, flags)` via `__get_unused_fd_flags`, fs/file.c, Linux
v6.18.46, commit 1f99e9ab748f).  The scan is fuel-bounded at 4096
candidates, so the answer is at most 4096 (`alloc_fd_le`) and never reads
as an error-encoded return. -/
def alloc_fd (fds : List (word × FdEntry)) : word :=
  alloc_fd_aux fds (Z_to_bv 64 0) 4096

/-- The SECOND descriptor of a call that reserves two: the lowest free one
strictly above `alloc_fd fds`.  `__do_pipe_flags` (fs/pipe.c) and
`__sys_socketpair` (net/socket.c), both Linux v6.18.46, commit
1f99e9ab748f, call `get_unused_fd_flags` twice, and `alloc_fd`'s
`__set_open_fd` has marked the first answer in `open_fds` before the second
scan runs, so the second scan skips it.  In Rocq only
`Net.Socket.socketpair_fds` reads this, and Lean has no reader yet;
Rocq's `pipe2_spec` takes its two ends by calling `lowest_fd` twice, the
second over the table with the read end inserted, a shape its twin keeps
because the two agree only until the fuel boundary.
Same fuel as `alloc_fd` over a range starting one higher; the freeness
test is the caller's, as for `alloc_fd`. -/
def alloc_fd2 (fds : List (word × FdEntry)) : word :=
  alloc_fd_aux fds (alloc_fd fds + 1) 4096

/-! ### Bounds — `Checks/Sys/Fs/Open.v`'s `alloc_fd_aux_le` and `alloc_fd_le` -/

/-- A scan of `fuel` candidates from `cand` answers at most `cand + fuel`,
provided that sum does not wrap the 64-bit candidate. -/
theorem alloc_fd_aux_le (fuel : Nat) (fds : List (word × FdEntry)) (cand : word) :
    bv_unsigned cand + (fuel : Int) < 18446744073709551616 →
    bv_unsigned (alloc_fd_aux fds cand fuel) ≤ bv_unsigned cand + (fuel : Int) := by
  induction fuel generalizing cand with
  | zero =>
    intro _
    simp only [alloc_fd_aux]
    omega
  | succ f ih =>
    intro hb
    simp only [alloc_fd_aux]
    cases fd_lookup fds cand with
    | none =>
      simp only
      omega
    | some _ =>
      simp only
      have hlt : cand.toNat + 1 < 2 ^ 64 := by
        simp only [bv_unsigned] at hb
        omega
      have h1 : (1 : word).toNat = 1 := by decide
      have hu : bv_unsigned (cand + 1) = bv_unsigned cand + 1 := by
        simp only [bv_unsigned]
        rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt hlt]
        omega
      have ih' := ih (cand + 1) (by rw [hu]; omega)
      rw [hu] at ih'
      omega

/-- `alloc_fd` answers at most 4096: far below the errno window
`[2^64 - 4095, 2^64)`, so a successful open's return is never confused with
an errno. -/
theorem alloc_fd_le (fds : List (word × FdEntry)) : bv_unsigned (alloc_fd fds) ≤ 4096 := by
  have h := alloc_fd_aux_le 4096 fds (Z_to_bv 64 0) (by decide)
  have h0 : bv_unsigned (Z_to_bv 64 0) = 0 := by decide
  rw [h0] at h
  unfold alloc_fd
  omega

end LinuxProcessSemantics.LinuxProcessSem.State
