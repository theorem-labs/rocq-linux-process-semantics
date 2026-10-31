import LinuxProcessSemantics.LinuxProcessSem.State.Fd

/-! rocq-baseline: 7b4cf49586658ecbffbab14145ab0969272a0b23 -/

/-! # LinuxProcessSem.State.Pipes — the pipe helpers

One part of `State.v`'s twin, re-exported by `State.lean`, whose header
says how the ten parts divide the Rocq file, what a part may hold and
where the pins live.

WHAT GOES HERE: the "Pipe helpers" block of `State.v`, ticket A8's,
`pipe_lookup` through `pipe_fd_bytes`, with the twins of its Rocq
lemmas.

TRUST BOUNDARY: this file is part of the trusted specification. -/

namespace LinuxProcessSemantics.LinuxProcessSem.State

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase

/-! ## Pipe helpers — the `fdst_pipes` side table and the fd ends that name it

Ticket A8.  Mirrors the "Pipe helpers" block of
`theories/LinuxProcessSem/State.v` (`pipe_lookup` through
`pipe_fd_bytes`), at the `rocq-baseline` this file's header carries (the
block was first read at f44244ad; `pipe_end_live`'s `FdUrandom` arm is
the one definitional difference since).
Every definition keeps the Rocq name and shape; each docstring names the
kernel file, function and version the decision rests on, with the line
numbers re-read in that tree when this block was ported, and points at
the Rocq definition for the argument in full, so there is one place to
correct it.

Four spellings differ from Rocq without changing a value: the `Z.leb`
tests are `decide` on the `Int` order, `Bool.eqb` is `==`, `Z.shiftr` on
a non-negative `Z` is `Int`'s arithmetic `>>>`, and Rocq's
`Z.to_nat (Z.min n (Z.of_nat (length q)))` is `Int.toNat (min n
q.length)`, the same function on every input.

Which arms read this block is the two tables' answer, `spec_table`
(`Sys/SyscallTable.lean`) and `checked_table` (`Checks/Sys/Table.lean`),
not this comment's.  What the helpers promise
those arms about Linux is pinned in `Checks/Cases/State.lean`; only the
twins of the Rocq lemmas stay here. -/

/-- The state of pipe `id`, or `none` for an id no `pipe2` handed out.
Same shape as `fd_lookup`: first match wins, and `pipe_insert` keeps at
most one entry per id. -/
def pipe_lookup (ps : List (word × PipeBuf)) (id : word) : Option PipeBuf :=
  match ps with
  | [] => none
  | (k, st) :: r => if bv_eqb k id then some st else pipe_lookup r id

/-- Bind `id` to `st`, replacing any existing binding. -/
def pipe_insert (ps : List (word × PipeBuf)) (id : word) (st : PipeBuf)
    : List (word × PipeBuf) :=
  (id, st) :: ps.filter (fun p => !(bv_eqb p.1 id))

/-- MAY A WRITE OF `n` BYTES LAND IN THE SLOT THE PIPE ALREADY USES?
Every claim is fs/pipe.c `anon_pipe_read` (:269) and `anon_pipe_write`
(:431) at Linux v6.18.46 (commit 1f99e9ab748f), the pair `pipeanon_fops`
(:1257-1266) installs on an anonymous pipe.  An EMPTY queue means the
ring is empty too — `anon_pipe_read` releases a buffer as soon as its
last byte is taken (:359-362) — so the write starts a fresh page and any
`n` up to `PIPE_BUF` fits, `PIPE_BUF` exactly included (`chars =
total_len & (PAGE_SIZE-1)` at :477 is 0, and :478 tests `chars`).  A
NONEMPTY queue is one slot with `used` bytes of its page spoken for, and
the top-up succeeds exactly when `used + n` still fits (:480-483); the
other two merge conditions hold by construction, argued on the Rocq
definition (`PIPE_BUF_FLAG_CAN_MERGE` set at :536-539, no `.confirm` in
`anon_pipe_buf_ops` at :223-227).  Anything else Linux writes onto a
SECOND page (the loop at :500, `anon_pipe_get_page` at :515), where slot
accounting and blocking start to matter: the arm declines rather than
guesses. -/
def pipe_write_room (st : PipeBuf) (n : Int) : Bool :=
  match st with
  | ([], _) => decide (n ≤ PIPE_BUF)
  | (_ :: _, used) => decide (used + n ≤ PIPE_BUF)

/-- The queue after appending `bs`.  An empty queue restarts the mark at
the new page's fill; a nonempty one carries it up. -/
def pipe_append (st : PipeBuf) (bs : List byte) : PipeBuf :=
  match st with
  | ([], _) => (bs, (bs.length : Int))
  | (q, used) => (q ++ bs, used + (bs.length : Int))

/-- The bytes a read of `n` takes off the front of a pipe's queue.  The
minimum against the queue's own length is taken in `Int` FIRST so that
the natural-number index is bounded by the queue, not by the count; the
cost that ordering removes is the Rocq definition's subject (issue
#666).  `pipe_take_firstn` is the equation proofs go through. -/
def pipe_take (q : List byte) (n : Int) : List byte :=
  q.take (Int.toNat (min n (q.length : Int)))

/-- The queue after a read of `k` bytes.  THE MARK DOES NOT MOVE: the
bytes a reader consumed are at the FRONT of the page and stay unavailable
to writers — fs/pipe.c `anon_pipe_read` at Linux v6.18.46 advances
`buf->offset` by what it consumed and shortens `buf->len` (:350-351),
leaving their sum unchanged.  `k` is a `Nat` and stays one: every caller
passes the LENGTH OF THE DELIVERED PREFIX, which `pipe_take` has already
bounded by the queue (`pipe_consume_of_take`). -/
def pipe_consume (st : PipeBuf) (k : Nat) : PipeBuf :=
  (st.1.drop k, st.2)

/-- The id a new pipe gets: the number of pipes created so far.  Entries
are NEVER REMOVED from `fdst_pipes` — closing both ends drops the two fds
and leaves the table entry behind — so this counts creations and an id is
never reused; a fresh pipe therefore cannot inherit a dead one's bytes.
Linux frees the pipe inode, and nothing a program can do observes the
difference; the argument is on the Rocq definition. -/
def pipe_new_id (ps : List (word × PipeBuf)) : word :=
  Z_to_bv 64 (ps.length : Int)

/-- Is some fd in the table an end of pipe `id` of the given direction?
`writer = true` asks whether the pipe still has a WRITER (end-of-file
versus blocking on a read at end-of-data); `writer = false` asks whether
it still has a READER (a write versus SIGPIPE).

DERIVED, not counted.  Linux keeps `pipe->readers` / `pipe->writers`:
for a `pipe2` pipe fs/pipe.c `get_pipe_inode` sets both to 1 (:902) and
`pipe_release` lowers each by the file's `f_mode` (:730-733), both at
Linux v6.18.46 (commit 1f99e9ab748f) — `fifo_open` (:1121), which raises
them by `f_mode` for a FIFO or a by-path re-open, is never on this path,
since the pipe's files come from `alloc_file_pseudo` / `alloc_file_clone`
(:944, :956) and no `->open` runs; the model reads the same fact off the
fd table.  The two agree only while NO REFERENCE TO A PIPE EXISTS
OUTSIDE THIS TABLE — Linux counts `struct file`s, and fs/file.c's
`f_dupfd` (:1472, v6.18.46) and `do_dup2` (:1265) each just `get_file` the existing
one (:1480, :1303) — and the Rocq definition carries the argument for
that claim route by route: `dup`/`dup3` decline a pipe end, `clone`
refuses to share a table holding one, `F_DUPFD` and fd-passing over
AF_UNIX are declined.  FALSIFIED BY a Lean arm that admits AF_UNIX,
models `F_DUPFD`, or lifts `dup`'s `FdPipe` decline: such an arm must
decline pipe ends or give this model a reference held by no fd.  No arm
of either table copies a pipe end, which closes the routes the
FALSIFIED BY list names, and the obligation transfers arm by arm.  It
does not close a reference no arm makes: another process can re-open
the pipe through `/proc/<pid>/fd/<n>`, which reaches `fifo_open`
(fs/pipe.c:1121, Linux v6.18.46) through the inode's `pipeanon_fops`
(:903, :1258).  A re-open for writing raises `pipe->writers` there
(:1193, and :1211 for O_RDWR), a writer this table does not hold, and
neither this argument nor the Rocq one excludes it.

Of the two directions this function answers, ONLY THE WRITER DIRECTION
IS A SOUNDNESS EXPOSURE: a missed writer answers a modeled 0 where Linux
blocks; a missed reader only makes the write arm's guard fire, which is
`unmodeled`.  That ranking is about the count alone.  A reference held
outside the model that reads or writes the buffer changes the queue
this model holds: a read then answers bytes another process already
took, and `pipe_write_room` counts room another process already filled.
That exposure, too, is outside both arguments.

The non-pipe kinds are named rather than wildcarded, as in Rocq, so that
a later `FdEntry` constructor able to name a pipe end stops the build
here instead of being skipped silently. -/
def pipe_end_live (fds : List (word × FdEntry)) (id : word) (writer : Bool) : Bool :=
  match fds with
  | [] => false
  | (_, .FdPipe id' w) :: r =>
      (bv_eqb id' id && (w == writer)) || pipe_end_live r id writer
  | (_, .FdChannel _) :: r => pipe_end_live r id writer
  | (_, .FdFile _ _) :: r => pipe_end_live r id writer
  | (_, .FdFileW _ _) :: r => pipe_end_live r id writer
  | (_, .FdFileA _ _) :: r => pipe_end_live r id writer
  | (_, .FdFileRW _ _) :: r => pipe_end_live r id writer
  | (_, .FdDir) :: r => pipe_end_live r id writer
  | (_, .FdSocket _) :: r => pipe_end_live r id writer
  | (_, .FdDevNull _ _) :: r => pipe_end_live r id writer
  | (_, .FdUrandom) :: r => pipe_end_live r id writer

/-- A 32-bit value as the four little-endian bytes the kernel's
`copy_to_user` of an `int` lays down. -/
def le32_bytes (v : word) : List byte :=
  let z := bv_unsigned v
  [ Z_to_bv 8 z, Z_to_bv 8 (z >>> 8), Z_to_bv 8 (z >>> 16), Z_to_bv 8 (z >>> 24) ]

/-- The eight bytes `pipe2` copies out: the read end then the write end,
as one `int fildes[2]` — a SINGLE contiguous range, which is how
fs/pipe.c `do_pipe2`'s one `copy_to_user` writes it (:1040, with
`fd[0] = fdr` and `fd[1] = fdw` set by `__do_pipe_flags` at :1005-1006,
Linux v6.18.46, commit 1f99e9ab748f). -/
def pipe_fd_bytes (fdr fdw : word) : List byte :=
  le32_bytes fdr ++ le32_bytes fdw

/-! ### The `pipe_take` / `pipe_consume` equations — twins of the Rocq lemmas -/

theorem pipe_take_firstn (q : List byte) (n : Int) (hn : 0 ≤ n) :
    pipe_take q n = q.take n.toNat := by
  unfold pipe_take
  rcases Int.le_total n (q.length : Int) with h | h
  · have e : Int.toNat (min n (q.length : Int)) = n.toNat := by omega
    rw [e]
  · have e : Int.toNat (min n (q.length : Int)) = q.length := by omega
    rw [e, List.take_length, List.take_of_length_le (by omega)]

theorem pipe_take_length (q : List byte) (n : Int) :
    ((pipe_take q n).length : Int) ≤ max 0 n := by
  unfold pipe_take
  rw [List.length_take]
  omega

theorem pipe_consume_of_take (q : List byte) (used n : Int) (hn : 0 ≤ n) :
    pipe_consume (q, used) (pipe_take q n).length
      = pipe_consume (q, used) n.toNat := by
  rw [pipe_take_firstn q n hn]
  unfold pipe_consume
  dsimp only
  rcases Nat.le_total n.toNat q.length with h | h
  · rw [List.length_take, Nat.min_eq_left h]
  · rw [List.take_of_length_le h, List.drop_length, List.drop_of_length_le h]

end LinuxProcessSemantics.LinuxProcessSem.State
