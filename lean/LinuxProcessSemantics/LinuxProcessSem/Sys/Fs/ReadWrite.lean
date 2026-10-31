-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Sys/Fs/ReadWrite.v
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi.Fs

/-! # LinuxProcessSem.Sys.Fs.ReadWrite — read (63), write (64), pread64 (67), pwrite64 (68), readv (65), writev (66) and lseek (62)

Mirrors `theories/LinuxProcessSem/Sys/Fs/ReadWrite.v`, which answers to
Linux `fs/read_write.c`: it holds what the kernel defines there, and
nothing else.  This file carries every syscall arm of that twin, in
Rocq's order and each in a delimited section headed by its syscalls:
`read` (63) and `write` (64) one apiece, `pread64` (67) and `pwrite64`
(68) together, `readv` (65) and `writev` (66) together (Rocq's order
within it but for `writev_spec`, which closes the section here, after
the readv definitions it shares nothing with), and `lseek` (62) last, so
that two PRs adding to this file merge by keeping both sections.

TRUST BOUNDARY: this file is part of the trusted specification.  Its
pins are `Checks/Cases/Fs/ReadWrite.lean`.

Every definition keeps the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function and line numbers
at Linux v6.18.46 (commit 1f99e9ab748f), every one opened there — and
point at the Rocq definition for the argument in full, so there is one
place to correct it.  Where Rocq's comment cites a line number without a
version, the number is v6.12's and is relabelled here at v6.18.46 after
reading it there.

SPELLINGS THAT DIFFER FROM ROCQ WITHOUT CHANGING A VALUE:

- The input stream and the peer's script are STRUCTURES here where Rocq
  has coinductives, so the two-way `match m_stdin m with IEof | ICons`
  is `match (m_stdin m).uncons with none | some _` — `State.uncons_cons`
  and `State.uncons_eof` are the equations — and the four-way match on a
  script is on its head cell, `rx.cell_at 0`, whose four constructors
  (`NFin`, `NRst`, `NTimedOut`, `NByte`) stand for Rocq's four stream
  shapes (`NFin | NRst | NTimedOut | NCons _ _`).  Neither arm
  binds the tail: as in Rocq, the body reads the whole stream again
  through `stream_take` / `net_take`.
- Rocq's `Z.of_nat (length bs)` is `(bs.length : Int)`; `<> None` is
  `≠ none`; `negb` is `!`; the Rocq `let deliver := … in deliver` of the
  file arm is written inline.
- The socket wildcard `| _ =>` that Rocq gives the fresh, bound and
  listening states is enumerated (`.SkFresh | .SkBound | .SkListening`),
  so that a `SockState` constructor added later is a decision here and
  not an inherited -ENOTCONN.
- `readv_imported`'s channel and connected-socket deliveries choose the
  ledger as a second `choose`, `scatter_iovecs i.in_wmem iovs bs = some
  writes`.  Rocq instead demands `scatter_iovecs … bs <> None` of the
  chosen `bs` and then matches the scatter, and that match's `None` arm,
  `choose (fun _ => False)`, is one no chosen `bs` reaches.  A `bs`
  Rocq refuses has no `writes` here, so both allow the same outcomes.
  The same two choices of `bs` drop Rocq's `(bs.length : Int) <= total`:
  `scatter_iovecs` answers `none` once the segments run out with bytes
  left, `total` is what the capped vector holds, and so a longer `bs`
  has no `writes` either.
- `writev_spec`'s channel delivery drops two of Rocq's four conjuncts on
  the chosen `ds`, `(ds.length : Int) < two_pow_64` and
  `addr_is_error_b (len_word ds) = false`.  `ds = bs.take ds.length`
  bounds `ds` by the gather, which `writev_gathered` takes over the
  capped vector, so no `ds` is longer than `MAX_RW_COUNT` and both hold
  of every `ds` the other two allow.
- What the two items above drop is not kept for the twin's shape: a
  mutant of a conjunct or an arm no outcome depends on changes no
  answer, so no pin can tell it from the original, and
  `linux-process-semantics@ff0313ba4f:docs/lean-port/TESTING.md`'s OBL-2
  reads each such guard as one nothing tests.
- The three `if addr_is_error_b (len_word bs)` gates of `writev_spec`,
  `writev_file_arm` and `readv_imported` are as dead, and are kept.  An
  `if` is two outcomes: its negate and branch-then mutants make every
  call the decline and are killed, which is the pin OBL-2 asks of an
  `if`, and only its branch-else is the equivalent one, allowlisted.  A
  dropped conjunct's one mutant is its guard-drop, which nothing kills.
- The `write` section's own header lists the spellings of that half.

Rocq's `read_spec` reaches `State.rw_count_clamp` and `State.MAX_RW_COUNT`
(fs/read_write.c `vfs_read`'s clamp at v6.18.46, below); both live in
`State.lean`, and this file reads them from there.

Rocq's `write_spec` reaches `State.rw_count_clamp` and `State.MAX_RW_COUNT`
(`vfs_write`'s clamp, fs/read_write.c:680-681, v6.18.46); both live in
`State.lean`, and this file reads them from there.
-/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.ReadWrite

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! ## read (63) -/

/-- A READ THAT REPORTS THE PEER'S ERROR, and consumes it.

`sock_error` (include/net/sock.h:2486-2498, Linux v6.18.46, commit
1f99e9ab748f) reads the pending error with an `xchg(&sk->sk_err, 0)`
(:2496), so the read that reports it is the only one that sees it: the
socket moves to `SkReset`, which the next read answers 0 on.  Why 0 and
not -ENOTCONN is `tcp_done` (net/ipv4/tcp.c:5020-5044, v6.18.46), which sets
`sk_shutdown = SHUTDOWN_MASK` (:5038) on the RST path, while
`tcp_recvmsg_locked` (net/ipv4/tcp.c:2634, v6.18.46) tests
`sk_shutdown & RCV_SHUTDOWN` (:2749-2750) IMMEDIATELY ABOVE the
`sk_state == TCP_CLOSE` arm that answers -ENOTCONN (:2752-2757).  Get
that order wrong and the model says -ENOTCONN where Linux says 0.
(SOCK_DONE plays no part: the RST path never sets it.)  `SkReset` reads
exactly as a consumed `NFin` does and is a separate constructor only
because the two are different TCP states for a sender; see
`State.SockState`.

No byte moves, so the destination is never touched and the only thing
left to decide about it is the range verdict `vfs_read` made before
dispatching (fs/read_write.c:560-561, v6.18.46) — hence `access_ok_zero`.  On the
-EFAULT branch of that verdict the state is NOT advanced: the protocol
is never reached, so the error stays pending, exactly as on Linux.  The
argument in full is on Rocq's `ReadWrite.socket_pending_error`. -/
def socket_pending_error (e : Int) (fd : word) (peer : PeerAddr) (ch : word)
    (buf count : word) (_i : SyscallInput) (m : Model) : Sys SyscallEffect :=
  access_ok_zero buf count
    (set_fds (fd_insert (m_fds m) fd (.FdSocket (.SkReset peer ch))) ;;
     err_ret e)

/-- A READ OF /dev/urandom, shared by the `read` and `pread64` arms on
`State.FdUrandom` once each has made the test Linux makes ahead of the
device (`vfs_read`'s `access_ok`; for pread64 also `rw_verify_area`'s
position test).  It answers exactly the clamped `count` bytes taken from
the front of the run's DECLARED stream (`State.m_urandom`) and advances
the stream past them; nothing is chosen and nothing reaches the trace,
because the bytes are an input of the run, the same on both sides of an
equivalence.  The argument in full is on Rocq's
`ReadWrite.read_urandom`; the kernel facts, all drivers/char/random.c at
Linux v6.18.46 (commit 1f99e9ab748f):

- `urandom_fops` (:1572-1581) installs `urandom_read_iter` (:1453-1475)
  as `.read_iter` and `noop_llseek` as `.llseek`, so `vfs_read`'s dispatch
  (fs/read_write.c:571-572, v6.18.46) reaches it through `new_sync_read`
  (fs/read_write.c:481-496, v6.18.46) with the clamped count;
  `memory_open` (drivers/char/mem.c:720-721, v6.18.46) is what puts that
  table on the file, for minor 9 (`devlist`, :701).
- `urandom_read_iter` never waits: it calls `try_to_generate_entropy`
  and warns about an unseeded pool (:1461-1472) and then reads anyway
  (:1474), so this device has no -EINTR and no -EAGAIN — unlike
  `random_read_iter`'s `wait_for_random_bytes` (:1477-1490).
- `get_random_bytes_user` (:434-482) returns 0 on an empty request
  (:440-441) and otherwise fills it: a request of at most 32 bytes straight
  from the key (:455-458, `goto out_zero_chacha`), a longer one entirely in
  64-byte ChaCha blocks (:460-478), stopping
  early only where `copy_to_iter` copies short (:465-468) or, at a page
  boundary (`ret % PAGE_SIZE == 0`, :471), when a signal is pending
  (:472-473).  The signal stop is a signal-interrupted transfer and is
  REJECTED rather than declined, for the reason
  `linux-process-semantics@ff0313ba4f:bugs/read-write-reject-an-interrupted-transfer.md`
  gives every read arm.
  `return ret ? ret : -EFAULT` (:481) is the -EFAULT of a destination
  none of whose bytes can land.

THE DESTINATION, in the order `get_random_bytes_user` decides it: not one
byte can land → -EFAULT; a range admitted but not wholly writable copies
a prefix whose length is the copy routine's rounded progress, which this
model does not describe → `unmodeled`, as every read arm declines it.

THE COUNT is judged through `State.rw_count_clamp`, the `MAX_RW_COUNT`
clamp `vfs_read` applies before the read (fs/read_write.c:566-567, v6.18.46), and
carries no ceiling of its own.  THE STREAM RUNNING OUT is a DECLINE, not
a short read: Linux v5.18 and later never fall short of the request
(`get_random_bytes_user` loops until the iterator is empty; the
per-call cap older kernels apply is
`linux-process-semantics@ff0313ba4f:bugs/urandom-read-proves-the-full-count-pre-v5-18-kernels-cap.md`),
so a
declared stream that ends first is an environment that stopped answering
and the arm answers only when the stream holds the whole clamped count.
That test comes ahead of the whole-range writability, so the numeral the
range test builds is the delivery's. -/
def read_urandom (buf count : word) (i : SyscallInput) (m : Model) : Sys SyscallEffect :=
  if w_is0 count then ret_only (Z_to_bv 64 0)
  else
    match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
    | none => err_ret EFAULT
    | some _ =>
        let r := stream_take_z (m_urandom m) (rw_count_clamp count)
        if !((r.1.length : Int) = rw_count_clamp count) then unmodeled
        else
          match read_bytes_map i.in_wmem buf (len_word r.1) with
          | none => unmodeled
          | some _ =>
              set_urandom r.2 ;;
              Monad.pure (mkEffect (len_word r.1) [(buf, r.1)] [])

/-- `read fd buf count`.

THE ORDER IS THE KERNEL'S, walked from `SYSCALL_DEFINE3(read, …)`
(fs/read_write.c:722-725, Linux v6.18.46, commit 1f99e9ab748f) into
`ksys_read` (:704-720), which resolves the descriptor with
`CLASS(fd_pos, f)(fd)` (:706) and answers -EBADF on an empty one (:707,
:709) before anything else, then into `vfs_read` (:552-581), whose tests
fire in this order: `FMODE_READ` clear → -EBADF (:556-557);
`FMODE_CAN_READ` clear → -EINVAL (:558-559), which no modeled kind can
reach, since the bit is set whenever the file has a `.read` or a
`.read_iter` — by `do_dentry_open` (fs/open.c:970-972, v6.18.46) on a
path-opened file, by `file_init_path` (fs/file_table.c:366-368, v6.18.46)
on a socket's or a pipe's — and every kind below has one; `access_ok(buf, count)` on the count the call NAMED → -EFAULT
(:560-561; `__access_ok`, include/asm-generic/access_ok.h:31-40 at v6.18.46, is
`State.access_okb`); `rw_verify_area` (:563-565; :451-478); the clamp
`if (count > MAX_RW_COUNT) count = MAX_RW_COUNT` (:566-567;
`MAX_RW_COUNT`, include/linux/fs.h:2838 at v6.18.46, is `State.MAX_RW_COUNT` and the
clamp is `State.rw_count_clamp`); and only then the file's own `.read` or
`.read_iter` (:569-574).  `fd` arrives already truncated to 32 bits
(`Syscall.fd32`).  Every arm below is that order restricted to what the
kind can reach, and the argument for each line is on Rocq's
`ReadWrite.read_spec`; what follows is the citation each decision rests
on.

WHAT IS DECIDED BEFORE THE DESTINATION.  -EBADF and -EISDIR never touch
`buf`: a closed fd, the write-only kinds (`FdFileW`; channels 1 and 2 BY
ASSUMPTION about the stdio the process was handed, not by the fd number,
`linux-process-semantics@ff0313ba4f:bugs/channel-fds-assume-unidirectional-stdio.md`;
a write-only /dev/null;
a pipe's write end, opened O_WRONLY by `create_pipe_files`,
fs/pipe.c:944-946, v6.18.46) fail `FMODE_READ`, derived from the open's
access mode by `init_file` (fs/file_table.c:199, v6.18.46:
`f->f_mode = OPEN_FMODE(flags)`).  A directory fd passes it and reaches
`generic_read_dir` (fs/libfs.c:224-227, v6.18.46), which is `return -EISDIR` — but
only after `vfs_read`'s `access_ok`, so a range past `State.TASK_SIZE` is
-EFAULT ahead of -EISDIR.

THE RANGE VERDICT, then the count.  The channel, file, /dev/null and
directory arms ask `access_ok` themselves and answer -EFAULT for any
range whose exact end passes `State.TASK_SIZE`, which includes every
`count` negative as `ssize_t` (never -EINVAL: `rw_verify_area`'s
`(ssize_t) count < 0` test at :456-457 sits BEHIND `access_ok`).  The
SOCKET and PIPE arms do not: they carry `Uaccess.modeled_rw_range`
instead — unchanged at or below `Uaccess.rw_bytes_max`, judged above it
when the range is inside the address space, and DECLINED above it when
it is not, where Linux answers -EFAULT
(`linux-process-semantics@ff0313ba4f:bugs/write-out-of-range-short-write.md`).
`count = 0` returns 0 without
implying end of file, after the range verdict alone.  What a delivering
arm then moves is bounded by the CLAMPED count, `State.rw_count_clamp`,
never the raw one.

THE DESTINATION, for a delivering arm.  `copy_to_user` touches only the
bytes it copies (`_inline_copy_to_user`, include/linux/uaccess.h:189-199 at v6.18.46,
runs `access_ok` and then the raw copy over exactly `n`), so the prefix
`[buf, buf + n)` must be writable for the `n` bytes DELIVERED and nothing
beyond.  Not even the first byte writable → -EFAULT, a real kernel
return with nothing delivered and nothing consumed.  A strict nonempty
writable prefix → `unmodeled`, fail closed: the count Linux answers there
is the copy routine's rounded progress on a file, and on stdin, a socket
or a pipe it turns on how the queued bytes are split into pipe buffers
or skbs (`anon_pipe_read`'s page copy at fs/pipe.c:343, v6.18.46, fails
the whole buffer at :344-348) — the argument is Rocq's note above
`readv_imported`, which applies here verbatim.

THE KINDS:

- CHANNEL 0, the input stream.  End of input (`IEof`) returns 0 and
  consumes nothing, STICKY by construction since `IEof` has no successor.
  Otherwise the read delivers a NONEMPTY prefix of the remaining stream
  of at most the clamped count: WHICH bytes is the input's, only HOW MANY
  is the environment's (a terminal or a pipe can deliver fewer bytes than
  asked), each delivered byte is one `ReadEv` on channel 0, and the
  stream advances past exactly them.  The destination gate asks for the
  `min` of the clamped count and the remaining stream
  (`stream_take_z`), the pipe rule above.
- /dev/null opened for reading: `read_null` (drivers/char/mem.c:412-416, v6.18.46)
  is `return 0`; `null_fops` installs it as `.read` (:644-652, :646), so
  `vfs_read` takes its `.read` branch (:569-570).  No byte lands, `f_pos`
  does not move, and the destination is never inspected — 0 into an
  unmapped buffer.  `rw_verify_area` between the range test and the read
  cannot fire: `f_pos` is 0 on this kind and a count of 2^63 or more
  already failed `access_ok`.
- /dev/urandom: every descriptor of this kind is O_RDONLY (the open
  admits no other word), so FMODE_READ holds and there is no -EBADF to
  decide; `vfs_read`'s `access_ok` on the NAMED count, then
  `read_urandom` above.  `rw_verify_area`'s position test cannot fire:
  `f_pos` is 0 on this kind (`noop_llseek`, and `urandom_read_iter` never
  moves it) and a count of 2^63 or more already failed `access_ok`.
- DIRECTORY: -EFAULT for a refused range, else -EISDIR (above).
- SOCKET.  `sock_read_iter` (net/socket.c:1154-1174, v6.18.46) opens with
  `if (!iov_iter_count(to)) return 0;` (:1168-1169), so a ZERO count is 0
  on ANY socket — fresh, listening, or reset — before the protocol is
  reached (recv(2) has no such short-circuit; the model has no recv); its
  `ki_pos != 0 → -ESPIPE` (:1165-1166) is unreachable, a socket's position
  being 0.  Then `tcp_recvmsg_locked` (net/ipv4/tcp.c:2634, v6.18.46): a listening
  socket is -ENOTCONN at :2651-2653; a fresh or bound one never left
  TCP_CLOSE and is -ENOTCONN at :2752-2757; both decided without
  touching the destination, so the range verdict is all that is left
  (`access_ok_zero`).  A connected socket whose script is at `NFin` is 0
  and STICKY: `tcp_fin` (net/ipv4/tcp_input.c:4720, v6.18.46) sets
  `RCV_SHUTDOWN` (:4726) and `SOCK_DONE` (:4727), and
  `tcp_recvmsg_locked` tests `SOCK_DONE` (:2741-2742) BEFORE `sk_err`
  (:2744-2747), so END OF STREAM DOMINATES A LATER ERROR.  `NRst` and
  `NTimedOut` are `socket_pending_error` with -ECONNRESET and -ETIMEDOUT;
  `SkReset` is the 0 that follows.  Queued bytes are delivered as the
  channel's are, on the CONNECTION's channel, ONE CALL DRAINING WHATEVER
  IS QUEUED IN SEQUENCE up to the clamped count: the loop walks
  `sk_receive_queue` (:2703) copying `used = skb->len - offset` (:2794)
  capped at `len`, and `target` (:2685, 1 by default) governs only
  whether to BLOCK for more, never when to stop copying, so any length in
  `[1, count]` is possible.  Queued bytes preempt a pending error by
  representation: the error is only ever the head of the script.
- FILE, opened read-only: deterministic.  The bytes are the interpreted
  file's at the fd's offset, truncated at end of file
  (`shmem_file_read_iter`, mm/shmem.c:3370 at v6.18.46, copies nothing at or past
  `i_size`, :3388-3389) and at the clamp (`Fs.file_read`); the offset
  advances by the delivered length (`ksys_read` writes `f_pos` back,
  fs/read_write.c:716-717, v6.18.46); no trace events, file contents are observed
  at exit.  A zero-byte read (at end of file, or `count = 0`) has the
  canonical zero-byte shape (`Uaccess.delivered_writes`) and never
  inspects the destination.  DETERMINISTIC ON THE PREMISE THAT THE PATH
  NAMES A REGULAR FILE,
  `linux-process-semantics@ff0313ba4f:bugs/fs-paths-assumed-regular-files.md`; a path
  the file system does not hold is `unmodeled`, since `openat` never
  mints one.  The offset carries no guard: `rw_verify_area`'s
  `(loff_t)(pos + count) < 0 → -EINVAL` (:467-469), reachable through an
  `lseek` to just under 2^63, is the divergence
  `linux-process-semantics@ff0313ba4f:bugs/read-write-position-past-llong-max-answers-zero.md`
  records; of the
  Rocq file's arms, `readv`, `writev`'s file arm, `pread64`, `pwrite64`
  and `write`'s append arm carry the test through `rw_pos_einvalb`
  (the `write` section's, below), and `read` does not.
- FILE, opened O_RDWR: the arm above WORD FOR WORD, with the entry
  written back under `FdFileRW`.  An O_RDWR description reads exactly as
  a read-only one does: `vfs_read` tests FMODE_READ, which
  `ACC_MODE(O_RDWR)` supplies, and nothing below that test looks at the
  access mode again (fs/read_write.c, v6.18.46).  What the shared `f_pos`
  then means for the next write is `write_spec`'s `FdFileRW` arm; here it
  is only advanced.
- FILE, opened O_WRONLY or O_WRONLY|O_APPEND: -EBADF.  The append word
  rides on O_WRONLY here, so FMODE_READ is clear and the same test
  answers; where an append write lands never comes up, because nothing
  reads.
- PIPE, read end.  Everything is `anon_pipe_read` (fs/pipe.c:269, v6.18.46),
  the `.read_iter` `pipeanon_fops` installs on both ends (:1257-1266,
  :1259).  "Null read succeeds": a zero count is 0 at :277-279, BEFORE
  the `mutex_lock` at :282, so it never consults the queue or the
  writers.  An EMPTY queue with a LIVE WRITER has no answer here: the
  loop falls past `if (!pipe->writers) break;` (:370-371) to the
  `wait_event_interruptible_exclusive` at :388 and sleeps; the model has
  no blocking and no O_NONBLOCK (-EAGAIN at :374-378), so it declines.
  With no writer left it is END OF FILE, 0, from the break at :370-371
  with `ret` still 0 — what makes `close` of the write end observable.
  A NONEMPTY queue delivers EXACTLY `min count (length q)`, never short:
  the loop takes `chars = buf->len` (:323) capped at `total_len`
  (:327-334), advances the buffer (:349-351), and continues while bytes
  remain and the ring is not empty (:363-367); once a byte has moved the
  `if (ret) break;` at :372-373 precedes the only wait.  `State.pipe_take`
  is that `min`, in `Int`, and `State.pipe_consume` keeps what the
  delivery did not take.  A pipe id the table does not hold is
  `unmodeled`: `pipe2` never mints one.

Neither this spec nor `write_spec` has an -EINTR outcome, so an
interrupted transfer is REJECTED rather than declined:
`linux-process-semantics@ff0313ba4f:bugs/read-write-reject-an-interrupted-transfer.md`. -/
def read_spec (fd buf count : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some (.FdFileW _ _) => err_ret EBADF
  | some (.FdFileA _ _) => err_ret EBADF
  | some (.FdChannel ch) =>
      if !w_is0 ch then err_ret EBADF
      else if !access_okb buf (bv_unsigned count) then err_ret EFAULT
      else if w_is0 count then ret_only (Z_to_bv 64 0)
      else
        match (m_stdin m).uncons with
        | none => ret_only (Z_to_bv 64 0)
        | some _ =>
          match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
          | none => err_ret EFAULT
          | some _ =>
            match read_bytes_map i.in_wmem buf
                    (len_word (stream_take_z (m_stdin m) (rw_count_clamp count)).1) with
            | none => unmodeled
            | some _ =>
              bs <- choose (fun bs : List byte =>
                      1 ≤ (bs.length : Int)
                      ∧ (bs.length : Int) ≤ rw_count_clamp count
                      ∧ (stream_take (m_stdin m) bs.length).1 = bs
                      ∧ read_bytes_map i.in_wmem buf (len_word bs) ≠ none) ;;
              set_stdin (stream_take (m_stdin m) bs.length).2 ;;
              emit (List.map (ReadEv ch) bs) ;;
              Monad.pure (mkEffect (len_word bs) [(buf, bs)] [])
  | some (.FdDevNull rd _) =>
      if !rd then err_ret EBADF
      else if !access_okb buf (bv_unsigned count) then err_ret EFAULT
      else ret_only (Z_to_bv 64 0)
  | some .FdUrandom =>
      if !access_okb buf (bv_unsigned count) then err_ret EFAULT
      else read_urandom buf count i m
  | some .FdDir =>
      if !access_okb buf (bv_unsigned count) then err_ret EFAULT
      else err_ret EISDIR
  | some (.FdSocket sk) =>
      if !modeled_rw_range buf count then unmodeled
      else if w_is0 count then access_ok_zero buf count (ret_only (Z_to_bv 64 0))
      else
        match sk with
        | .SkConnected peer ch rx =>
            match rx.cell_at 0 with
            | .NFin => access_ok_zero buf count (ret_only (Z_to_bv 64 0))
            | .NRst => socket_pending_error ECONNRESET fd peer ch buf count i m
            | .NTimedOut => socket_pending_error ETIMEDOUT fd peer ch buf count i m
            | .NByte _ =>
                match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
                | none => err_ret EFAULT
                | some _ =>
                  match read_bytes_map i.in_wmem buf
                          (len_word (net_take_z rx (rw_count_clamp count)).1) with
                  | none => unmodeled
                  | some _ =>
                    bs <- choose (fun bs : List byte =>
                            1 ≤ (bs.length : Int)
                            ∧ (bs.length : Int) ≤ rw_count_clamp count
                            ∧ (net_take rx bs.length).1 = bs
                            ∧ read_bytes_map i.in_wmem buf (len_word bs) ≠ none) ;;
                    set_fds (fd_insert (m_fds m) fd
                               (.FdSocket (.SkConnected peer ch (net_take rx bs.length).2))) ;;
                    emit (List.map (ReadEv ch) bs) ;;
                    Monad.pure (mkEffect (len_word bs) [(buf, bs)] [])
        | .SkReset _ _ => access_ok_zero buf count (ret_only (Z_to_bv 64 0))
        | .SkFresh | .SkBound | .SkListening => access_ok_zero buf count (err_ret ENOTCONN)
  | some (.FdFile p off) =>
      if !access_okb buf (bv_unsigned count) then err_ret EFAULT
      else
        match fs_lookup (m_fs m) p with
        | none => unmodeled
        | some data =>
          let bs := file_read data off (Z_to_bv 64 (rw_count_clamp count))
          match read_bytes_map i.in_wmem buf (len_word bs) with
          | none =>
              match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
              | none => err_ret EFAULT
              | some _ => unmodeled
          | some _ =>
              set_fds (fd_insert (m_fds m) fd (.FdFile p (off + len_word bs))) ;;
              Monad.pure (mkEffect (len_word bs) (delivered_writes buf bs) [])
  | some (.FdFileRW p off) =>
      if !access_okb buf (bv_unsigned count) then err_ret EFAULT
      else
        match fs_lookup (m_fs m) p with
        | none => unmodeled
        | some data =>
          let bs := file_read data off (Z_to_bv 64 (rw_count_clamp count))
          match read_bytes_map i.in_wmem buf (len_word bs) with
          | none =>
              match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
              | none => err_ret EFAULT
              | some _ => unmodeled
          | some _ =>
              set_fds (fd_insert (m_fds m) fd (.FdFileRW p (off + len_word bs))) ;;
              Monad.pure (mkEffect (len_word bs) (delivered_writes buf bs) [])
  | some (.FdPipe id w) =>
      if w then err_ret EBADF
      else if !modeled_rw_range buf count then unmodeled
      else if w_is0 count then access_ok_zero buf count (ret_only (Z_to_bv 64 0))
      else
        match pipe_lookup (m_pipes m) id with
        | none => unmodeled
        | some ([], _) =>
            if pipe_end_live (m_fds m) id true then unmodeled
            else access_ok_zero buf count (ret_only (Z_to_bv 64 0))
        | some (q@(_ :: _), used) =>
            let del := pipe_take q (rw_count_clamp count)
            match read_bytes_map i.in_wmem buf (len_word del) with
            | none =>
                match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
                | none => err_ret EFAULT
                | some _ => unmodeled
            | some _ =>
                set_pipes (pipe_insert (m_pipes m) id (pipe_consume (q, used) del.length)) ;;
                Monad.pure (mkEffect (len_word del) (delivered_writes buf del) [])

/-! ## write (64)

`write_spec` and the helpers before it are the write half of the Rocq
file.  The kernel path they mirror, all
fs/read_write.c at Linux v6.18.46 (commit 1f99e9ab748f) unless said
otherwise: `SYSCALL_DEFINE3(write)` (:746-750) is `ksys_write` (:727-744),
which fetches the descriptor with `fdget_pos` (:729) and answers -EBADF
on an empty one (:730, the `fd_empty` test at :732), loads `f_pos`
through `file_ppos` (:733, :699-702), calls `vfs_write` (:738) and writes
the position back under `if (ret >= 0 && ppos)` (:739-740).  `vfs_write` (:666-696) tests
FMODE_WRITE (-EBADF, :670-671), FMODE_CAN_WRITE (-EINVAL, :672-673),
`access_ok` over the named range (-EFAULT, :674-675), `rw_verify_area`
(:677-679), clamps the count at `MAX_RW_COUNT` (:680-681) and dispatches
to `->write` or `new_sync_write` (:683-686).  Which of those tests each
fd kind reaches, and in what order, is the arm's; the errno that wins
when two hold is the earlier test's.

SPELLINGS THAT DIFFER FROM ROCQ WITHOUT CHANGING A VALUE, beyond the
module header's list: Rocq's `Z.leb`/`Z.ltb` Bool tests are Lean's
decidable `≤`/`<` on `Int`; `Nat.eqb` is `==`; `firstn (length ds) bs`
is `bs.take ds.length`; `(in_mem i)` is `i.in_mem`; Rocq's `Lemma` and
`Remark` beside the guards are `theorem`s of the same names.

`write_spec`'s `FdFileA` arm calls `append_new_pos`, as `writev_spec`'s
`FdFileA` arm does, and `append_opens_no_gap` proves the hole guard
those two arms omit would have been `true` at every call. -/

/-- The zero-fill a call forces on the model is one the model can
represent: `endpoint`, the byte position the call opens the file out to,
lies at most `Uaccess.rw_bytes_max` past the current end.  Linux leaves
the region between as a sparse hole for free (a write past end-of-file
lands at `ki_pos` through `generic_perform_write`, mm/filemap.c,
v6.18.46, and the pages between are never allocated); the model holds
the file as a flat byte list and has to BUILD those bytes, so the
distance — not the file — is what is bounded.

Two calls extend a file that way, a write past end-of-file and a GROWING
`ftruncate`, and they are bounded by one comparison here rather than by
two copies of it.  Their guards differ only in which position each
measures and in the carve-out each makes, and each keeps its own name so
a caller's error message still says which syscall was declined.  This is
the model's own bound, not a kernel test: where it is off the arm says
`unmodeled`, never an errno. -/
def modeled_zero_fill (endpoint : Int) (data : List byte) : Bool :=
  endpoint - (data.length : Int) ≤ rw_bytes_max

/-- The hole this write opens past end-of-file is one the model can
represent.  A write past the end zero-fills the gap (`Fs.file_write`),
and the model holds a file as a flat byte list, so the hole is bytes it
has to BUILD — where on Linux a hole in a sparse file costs nothing.  A
zero-length write opens no hole at all (`Fs.file_write`'s `[]` arm
leaves the file alone, as Linux does: `generic_write_checks_count`
returns 0 on an empty iterator before anything is positioned,
fs/read_write.c:1744-1745, v6.18.46), so it is judged at any offset. -/
def modeled_file_gap (data : List byte) (off : word) (bs : List byte) : Bool :=
  match bs with
  | [] => true
  | _ :: _ => modeled_zero_fill (bv_unsigned off) data

/-- Discharge the hole guard, in the `!… = false` form the arm tests it. -/
theorem file_gap_in_range (data : List byte) (off : word) (bs : List byte)
    (h : bv_unsigned off ≤ (data.length : Int) + rw_bytes_max) :
    (!modeled_file_gap data off bs) = false := by
  cases bs with
  | nil => rfl
  | cons b bs =>
    show (!modeled_zero_fill (bv_unsigned off) data) = false
    unfold modeled_zero_fill
    have h' : bv_unsigned off - (data.length : Int) ≤ rw_bytes_max := by omega
    simp only [h', decide_true, Bool.not_true]

/-- Where an append write leaves `f_pos`, and the zero-length case is the
whole reason this is a definition rather than an expression.

A DELIVERING append write ends at the new end of file, `ki_pos + n` with
`ki_pos` the old size.  A ZERO-LENGTH one leaves `f_pos` EXACTLY WHERE IT
WAS, and not because the arithmetic happens to agree — it does not,
since the offset can sit anywhere an `lseek` put it.  Two things in
Linux say so, and the first is enough: `generic_write_checks_count`
(fs/read_write.c:1736-1756, v6.18.46; Rocq cites it under its caller
`generic_write_checks`'s name and mm/filemap.c, where it lived before it
moved) opens with `if (!*count) return 0;` (:1744-1745; the caller
`generic_write_checks` derives that count from `iov_iter_count(from)`)
BEFORE its `if (iocb->ki_flags & IOCB_APPEND) iocb->ki_pos =
i_size_read(inode);` (:1747-1748), so a zero-count write never even
computes the append position; and `new_sync_write`
(fs/read_write.c:583-598, v6.18.46) writes the position back only under `if (ret > 0 && ppos)`
(:595-596), so a 0 return copies nothing back.

The `FdFileW` arm needs no such definition because `off + len_word bs`
is already `off` when `bs` is empty.  Here the two are different words,
which is what makes an unconditional end-of-file assignment a
confidently wrong answer at `count = 0` rather than a harmless
restatement: `lseek(fd, 0, SEEK_CUR)` afterwards would report the file's
size where Linux reports the untouched offset.  Its callers are
`write_spec`'s and `writev_spec`'s `FdFileA` arms. -/
def append_new_pos (data bs : List byte) (off : word) : word :=
  match bs with
  | [] => off
  | _ :: _ => len_word data + len_word bs

/-- An APPEND write opens no hole, which is why Rocq's `FdFileA` arm
carries no `modeled_file_gap` guard where the `FdFileW` arm needs one.
The position such a write uses is the file's own length, so the distance
the model would have to zero-fill is at most zero: `bv_unsigned (len_word
data)` is `data.length` reduced mod 2^64, which never exceeds
`data.length` itself.  Stated as a theorem rather than left to a reader
comparing two arms. -/
theorem append_opens_no_gap (data bs : List byte) :
    modeled_file_gap data (len_word data) bs = true := by
  cases bs with
  | nil => rfl
  | cons b bs =>
    show modeled_zero_fill (bv_unsigned (len_word data)) data = true
    unfold modeled_zero_fill
    have hle : bv_unsigned (len_word data) ≤ (data.length : Int) := by
      unfold len_word bv_unsigned Z_to_bv
      rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat]
      exact Int.ofNat_le.mpr (Nat.mod_le _ _)
    have h' : bv_unsigned (len_word data) - (data.length : Int) ≤ rw_bytes_max := by
      unfold rw_bytes_max
      omega
    simp only [h', decide_true]

/-- `rw_verify_area`'s position test (fs/read_write.c:451-478, v6.18.46):
with `f_pos` non-negative, `(loff_t)(pos + count) < 0` (:467-469) is
exactly `LLONG_MAX < pos + count` in `Int`, and answers -EINVAL on a
regular file.  That reading rests on the sum not wrapping 64 bits, and
it cannot: every modeled offset is under 2^63 (Rocq's `lseek_dest`), and
`count` is at most `MAX_RW_COUNT` on the vectored path and at most
`State.TASK_SIZE` on the scalar one — a larger count fails `access_ok`
first (`vfs_read`'s :560-561, `vfs_write`'s :674-675) — so `pos + count`
is below 2^64 and is negative as a
`loff_t` exactly when it reaches 2^63.  `vfs_write` hands it the `pos` that `ksys_write` copied
out of `f_pos` (:733-736; `rw_verify_area` at :677-679) BEFORE the
iterator is built, so on an O_APPEND descriptor it reads the fd's REAL
position, which `generic_write_checks_count` overrides only once the
write is under way.  `write_spec`'s `FdFileA` arm applies it after
`vfs_write`'s `access_ok` and before the tail, and that spec's `FdFileW`
and `FdFileRW` arms do not model the test at all — the omission is priced
in
`linux-process-semantics@ff0313ba4f:bugs/read-write-position-past-llong-max-answers-zero.md`.
`pread64_spec` and `pwrite64_spec` apply it to the position the call
names, which `ppos_einvalb` has already held under 2^63; the vectored
section's file arms apply it to `f_pos` and the capped aggregate. -/
def rw_pos_einvalb (off : word) (count : Int) : Bool :=
  2 ^ 63 - 1 < bv_unsigned off + count

/-- THE COUNT GATE, and it is the FIRST thing every file write arm does.

`Uaccess.modeled_rw_range` is the disjunction `modeled_rw_count count ||
access_okb buf count`, so it is a gate on whether the MODEL will judge
this call at all, not a kernel test.  It has to stay AHEAD of the arm's
own kernel tests: its left disjunct is what admits a small count at an
unaddressable buffer, and that is the call on which the append arm's
`access_ok` then produces the real -EFAULT.  An arm that ran a kernel
test first would be answering for a call the model had not yet agreed to
judge.  Where the gate is off the answer is `unmodeled`: Linux would say
-EFAULT (`access_ok`, include/asm-generic/access_ok.h, in `vfs_write`,
fs/read_write.c:674-675, v6.18.46),
and the decline costs priority 3 only. -/
def write_range_gate (buf count : word) (k : Sys SyscallEffect) : Sys SyscallEffect :=
  if !modeled_rw_range buf count then unmodeled else k

/-- The ledger and the return, shared by the file arms.

A zero-length write reads no user byte, so its ledger is EMPTY rather
than a singleton zero-length range; a delivering one records the prefix
it actually read.  The return is the delivered length in both cases
(`new_sync_write`'s `ret`, the bytes `generic_perform_write` landed,
fs/read_write.c:593, mm/filemap.c, v6.18.46). -/
def write_ledger (buf count : word) (bs : List byte) : Sys SyscallEffect :=
  if w_is0 count then ret_only (len_word bs)
  else record_copyins [(buf, bs.length)] (ret_only (len_word bs))

/-- The tail every file write arm shares: the source bytes, the -EFAULT
on an unreadable buffer, the zero-count range verdict, and the ledger.

`place bs` is the KIND's own middle and the only thing that varies: it
answers `none` where that kind declines — an fd whose path is not in the
file system, or a hole the model would have to build — and otherwise the
state update, which is where the destination and the written-back entry
live.  The update is handed the ledger as its CONTINUATION rather than
building one: it cannot vary the ledger, the -EFAULT or the zero-count
wrapper, because it is given the first already built and never sees the
other two.

`Uaccess.write_source` is the readable prefix of the CLAMPED range: Linux
clamps at `MAX_RW_COUNT` before the write (`vfs_write`,
fs/read_write.c:680-681, v6.18.46), so a delivering write moves at most
that much and the model's answer is exact below it.  The -EFAULT is
guarded by `!w_is0 count` because a zero-length write touches no byte
and so cannot fault on the buffer (`generic_write_checks_count` returns
0 before any copy, fs/read_write.c:1744-1745, v6.18.46); what remains for it is the
RANGE verdict, which is `Uaccess.access_ok_zero` (`vfs_write`'s
`access_ok`, :674-675, runs on a zero count too).  A nonempty prefix
shorter than the count is a SHORT write, delivered: `generic_perform_write`
(mm/filemap.c, v6.18.46) returns the bytes written before the byte that
would not fault in and -EFAULT only when that is none.  That is Linux
v5.18 on.  Linux v4.17 through v5.17 fault each chunk in ahead of
`write_begin` and answer the prefix cut back to a page boundary of the
file position, -EFAULT with the file untouched when that leaves nothing
(`linux-process-semantics@ff0313ba4f:bugs/write-file-prefault-before-v5-18-answers-a-chunk.md`),
and qemu-user answers -EFAULT for any unreadable byte (`lock_user`,
linux-user/syscall.c:9848-9849, QEMU 11.1.1), so this certain short
write is a known divergence from those implementations, recorded in
`linux-process-semantics@ff0313ba4f:bugs/write-file-partial-source-short-write-is-certain.md`.
`writev_file_arm` answers the same shape the same way. -/
def write_file_tail (mp : word → Option byte) (buf count : word)
    (place : List byte → Option (Sys SyscallEffect → Sys SyscallEffect)) : Sys SyscallEffect :=
  let bs := write_source mp buf count
  if !w_is0 count && bs.length == 0 then err_ret EFAULT
  else
    let deliver :=
      match place bs with
      | none => unmodeled
      | some upd => upd (write_ledger buf count bs)
    if w_is0 count then access_ok_zero buf count deliver else deliver

/-- `write fd buf count`.

THE FMODE_WRITE ARMS.  `none` is `ksys_write`'s -EBADF on an empty
descriptor (fs/read_write.c:730, v6.18.46; the empty-descriptor test is :732).  `FdFile` (O_RDONLY),
`FdDir` (a directory opens O_RDONLY only: `may_open` answers -EISDIR to
MAY_WRITE on S_IFDIR, fs/namei.c:3540-3542), `FdUrandom` (every
descriptor of this kind is O_RDONLY — the open declines the write words —
so Linux's own `random_write_iter`, drivers/char/random.c:1448 (v6.18.46) through
`urandom_fops`' `.write_iter` at :1574, is reachable only through a
descriptor this model never mints), a read-only `FdDevNull`, channel 0
and a pipe's READ end are `vfs_write`'s FMODE_WRITE test (:670-671),
which runs before the buffer is looked at, so -EBADF beats -EFAULT on
every one of them.  Channel 0 is read-only BY ASSUMPTION (piped stdio),
not by the fd number:
`linux-process-semantics@ff0313ba4f:bugs/channel-fds-assume-unidirectional-stdio.md`.

`FdDevNull` open for writing: `write_range_gate` — the count rule every
judging write arm applies; it decides nothing here that the range test
does not, and is kept so the arms agree on one rule — then
`vfs_write`'s `access_ok` over the WHOLE named range (:674-675), the one
test Linux makes on the buffer, then `write_null` (drivers/char/mem.c:418-422, v6.18.46,
`null_fops`' `.write` at :647, reached through `memory_open`'s
`devlist[3]` at :694 and :720-721) returns the count `vfs_write` clamped
at `MAX_RW_COUNT` (:680-681) without reading a byte.  NOT the file arms'
shape: no readable prefix is taken, so an unmapped in-range buffer is a
full count here where a file would be -EFAULT, and NO copy-in is
recorded, because none happens.  `access_ok_zero` is that range test by
another name; it is not only for a zero count.

`FdChannel ch`, `ch ≠ 0`: after the fd test, a write above
`Uaccess.rw_bytes_max` whose range leaves the user address space fails
closed (`Uaccess.modeled_rw_range`); `count = 0` moves no byte and so
never touches `buf`, leaving only the range verdict
(`Uaccess.access_ok_zero`); nothing readable at `buf` is the real
-EFAULT; otherwise a NONEMPTY prefix of the readable prefix is delivered
— a short write is real: `anon_pipe_write` copies into the ring what
the ring takes before its only `signal_pending` test (fs/pipe.c:
557-559, v6.18.46) — which bytes is fixed by the buffer, only how many
is the environment's choice, one `WriteEv` per byte, the ledger the
prefix read and the return its length.  The channel is assumed to have a
reader
(`linux-process-semantics@ff0313ba4f:bugs/write-channel-assumes-its-reader-is-alive.md`);
a source readable in its first byte but not throughout is answered as a
short write where a pipe answers -EFAULT
(`linux-process-semantics@ff0313ba4f:bugs/write-channel-partial-source-efault-refused.md`);
and no -EINTR outcome exists
(`linux-process-semantics@ff0313ba4f:bugs/read-write-reject-an-interrupted-transfer.md`).

`FdSocket`: WRITING A SOCKET IS UNMODELED, PERMANENTLY — not deferred.
On a connection the peer has reset, write(2) returns -EPIPE *and raises
SIGPIPE*: `sk_stream_error` (net/core/stream.c:190-197, v6.18.46) sends
the signal at :195 whenever the final errno is exactly -EPIPE and
MSG_NOSIGNAL is clear, and write(2) cannot set that flag.  The reason is
NOT that `sock_write_iter` (net/socket.c:1176-1199) passes only
MSG_DONTWAIT: it also raises MSG_NOSIGNAL from `IOCB_NOSIGNAL`
(:1193-1194) and MSG_EOR for SOCK_SEQPACKET (:1190-1191).  What write(2)
cannot do is set `IOCB_NOSIGNAL` (include/linux/fs.h:359, v6.18.46):
`iocb_flags` (include/linux/fs.h:3839-3851, v6.18.46) ORs only
IOCB_APPEND, IOCB_DIRECT,
IOCB_DSYNC and IOCB_SYNC, and RWF_NOSIGNAL (include/uapi/linux/fs.h:434,
v6.18.46) reaches a kiocb through `kiocb_set_rw_flags`
(include/linux/fs.h:3853, v6.18.46),
which write(2) never calls and writev(2) calls with `flags = 0`
(writev's entry, fs/read_write.c:1168-1172, into `do_writev`,
fs/read_write.c:1091-1112, and `do_iter_readv_writev`, fs/read_write.c:819,
v6.18.46), so IOCB_NOSIGNAL is set on neither path.  SIGPIPE is in none of
SIG_KERNEL_IGNORE_MASK, SIG_KERNEL_STOP_MASK or SIG_KERNEL_COREDUMP_MASK
(include/linux/signal.h:422-436, v6.18.46), so under SIG_DFL `get_signal`
(kernel/signal.c:2808, v6.18.46) reaches `do_group_exit` (:3043) and the whole
thread group dies.  A spec's outcomes are `Ok` and `Unmodeled` and
nothing else (`Monad.Sys`), so "the process died" cannot be stated:
returning -EPIPE and continuing asserts the process SURVIVED, and
halting with 141 is indistinguishable from a voluntary exit(141).  Nor is
a never-connected socket an escape: `sk_stream_wait_connect`
(net/core/stream.c:60, v6.18.46) returns -EPIPE at :71 for every state outside
SYN_SENT/SYN_RECV, so that raises SIGPIPE too.  Nor is zero length:
`sock_write_iter` has no zero-count short-circuit of the kind
`sock_read_iter` has (:1168), so `write(sockfd, buf, 0)` on a reset
connection is not a no-op.  The socket write path this model can grow is
sendto/sendmsg with MSG_NOSIGNAL REQUIRED and checked first, which works
only because the flag is a syscall argument a spec can read.

`FdFileW p off`: NO LEADING KERNEL TEST, a deliberate omission and not
the helper's doing: this arm models neither `vfs_write`'s `access_ok`
nor `rw_verify_area`, and rests on `modeled_file_gap` declining first.
The cost is priced in
`linux-process-semantics@ff0313ba4f:bugs/read-write-position-past-llong-max-answers-zero.md`
and
`linux-process-semantics@ff0313ba4f:bugs/wrapping-walks-unbounded-segments.md`.
An `FdFileW` always points into the fs (`openat` minted it), so
an absent path is `unmodeled`; a hole past end-of-file too large to
zero-fill as a byte list is `unmodeled` too, behind the tail's -EFAULT.
Otherwise the prefix lands AT `off` (`Fs.file_write`; nothing sets
IOCB_APPEND, so `generic_write_checks_count` leaves `ki_pos` alone) and
the entry advances by the delivered length (`ksys_write`'s `f_pos`
write-back, :739-740).

`FdFileRW p off`: the `FdFileW` arm with the entry written back under
this kind, through the SAME two helpers rather than a copy of that arm's
body — an O_RDWR description writes exactly as an O_WRONLY one does, the
bytes landing AT `f_pos` because nothing sets IOCB_APPEND, and the offset
it advances is the one `read_spec`'s `FdFileRW` arm advances.  It
inherits the two missing kernel tests with the rest of the arm.

`FdFileA p off`: THE OFFSET IS NOT READ.  `iocb_flags`
(include/linux/fs.h, v6.18.46) turns the fd's O_APPEND into IOCB_APPEND,
and `generic_write_checks` (mm/filemap.c) then assigns
`iocb->ki_pos = i_size_read(inode)`, so the bytes land at the CURRENT end
of the file however far an `lseek` moved `f_pos`, and `f_pos` follows a
delivering write to that new end (`append_new_pos`).  There is NO
`modeled_file_gap` guard — the position IS the current length, so the
hole this write opens is empty (`append_opens_no_gap`) — and dropping it
is why this arm KEEPS `rw_pos_einvalb`, which reads the fd's REAL
position because `rw_verify_area` runs before the iterator, and
`vfs_write`'s `access_ok` ahead of it.  Both sit INSIDE
`write_range_gate` and not before it: the gate decides whether the model
judges the call at all, the two tests are `vfs_write`'s own.

`FdPipe id w`: the READ end is -EBADF before the source buffer, as
FMODE_WRITE is tested first; the range gate as on the channel arm;
"Null write succeeds": `anon_pipe_write` returns 0 for a zero-length
request at fs/pipe.c:454-456 (v6.18.46), BEFORE the `mutex_lock` at :458 and so
before the `if (!pipe->readers)` test at :460, so a zero-length write to
a pipe whose reader is gone is 0 — NOT -EPIPE, and no SIGPIPE.  NO READER
LEFT: Linux raises SIGPIPE and answers -EPIPE (:460-465), and SIGPIPE's
default disposition TERMINATES the process — an outcome this model
cannot express — so it fails closed.  A pipe id the table does not hold
is `unmodeled` (`pipe2` never mints one).  A WRITE THAT NEEDS A SECOND
RING SLOT HAS NO ANSWER HERE: past one slot the pipe's fullness — and so
whether `anon_pipe_write` sleeps at :573 — depends on the ring accounting
the model does not carry (`State.pipe_write_room`, which also explains
why a byte-counted capacity would be wrong); decided before the source
buffer only in the model, since a declining call is one the model refuses
to judge at all.  THE SOURCE MUST BE WHOLLY READABLE: a short
`copy_page_from_iter` does not simply shorten the transfer the way it
does on a file.  Both copy sites fault BEFORE they publish — the merge
site copies at :488 and on a short copy takes `ret = -EFAULT; goto out`
(:489-492) without reaching `buf->len += ret` (:494); the fresh-page site
copies at :522, hands the page back and breaks (:523-528) without
reaching `pipe->head = head + 1` (:530), with `if (!ret) ret = -EFAULT`
(:525-526) — and under `pipe_write_room` the transfer reaches exactly ONE
site (an empty queue skips the merge guard `chars && !was_empty` at :478;
a nonempty one has `used ≥ 1`, so the room test `used + count ≤ PIPE_BUF`
IS the kernel's `offset + chars <= PAGE_SIZE` at :480-483), so Linux's
answer across the whole admitted band is a plain -EFAULT with the pipe
unchanged.  Declining is CONSERVATIVE, costing priority 3 only; it is
kept because that -EFAULT holds only while the capacity guard confines
the write to one site, and answering it would be a second rule silently
depending on a bound the model means to relax.  The delivery has NO
SHORT POSITIVE RETURN, deliberately not the channel arm's short write:
with room in the ring and the whole source readable, `anon_pipe_write`
copies everything before it reaches its only `signal_pending` test
(:557-559, reached only once `pipe_full` at :510 holds); the whole source
IS read, so the range goes in the copy-in ledger exactly as the channel
and file arms record theirs, and there are no trace events.  The
delivery is therefore DETERMINISTIC and admits no second answer. -/
def write_spec (fd buf count : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some (.FdFile _ _) => err_ret EBADF
  | some .FdUrandom => err_ret EBADF
  | some (.FdDevNull _ wr) =>
      if !wr then err_ret EBADF
      else
        write_range_gate buf count
          (access_ok_zero buf count (ret_only (Z_to_bv 64 (rw_count_clamp count))))
  | some (.FdChannel ch) =>
      if w_is0 ch then err_ret EBADF
      else if !modeled_rw_range buf count then unmodeled
      else if w_is0 count then access_ok_zero buf count (ret_only (Z_to_bv 64 0))
      else
        let bs := write_source i.in_mem buf count
        if bs.length == 0 then err_ret EFAULT
        else
          ds <- choose (fun ds : List byte =>
                  1 ≤ (ds.length : Int)
                  ∧ (ds.length : Int) ≤ rw_count_clamp count
                  ∧ ds = bs.take ds.length) ;;
          emit (List.map (WriteEv ch) ds) ;;
          record_copyins [(buf, ds.length)] (ret_only (len_word ds))
  | some .FdDir => err_ret EBADF
  | some (.FdSocket _) => unmodeled
  | some (.FdFileW p off) =>
      write_range_gate buf count
        (write_file_tail i.in_mem buf count (fun bs =>
          match fs_lookup (m_fs m) p with
          | none => none
          | some data =>
              if !modeled_file_gap data off bs then none
              else
                some (fun k =>
                  set_fs (fs_set (m_fs m) p (file_write data off bs)) ;;
                  set_fds (fd_insert (m_fds m) fd (.FdFileW p (off + len_word bs))) ;;
                  k)))
  | some (.FdFileRW p off) =>
      write_range_gate buf count
        (write_file_tail i.in_mem buf count (fun bs =>
          match fs_lookup (m_fs m) p with
          | none => none
          | some data =>
              if !modeled_file_gap data off bs then none
              else
                some (fun k =>
                  set_fs (fs_set (m_fs m) p (file_write data off bs)) ;;
                  set_fds (fd_insert (m_fds m) fd (.FdFileRW p (off + len_word bs))) ;;
                  k)))
  | some (.FdFileA p off) =>
      write_range_gate buf count
        (if !access_okb buf (bv_unsigned count) then err_ret EFAULT
         else if rw_pos_einvalb off (bv_unsigned count) then err_ret EINVAL
         else
         write_file_tail i.in_mem buf count (fun bs =>
          match fs_lookup (m_fs m) p with
          | none => none
          | some data =>
              some (fun k =>
                set_fs (fs_set (m_fs m) p (file_write data (len_word data) bs)) ;;
                set_fds (fd_insert (m_fds m) fd (.FdFileA p (append_new_pos data bs off))) ;;
                k)))
  | some (.FdPipe id w) =>
      if !w then err_ret EBADF
      else if !modeled_rw_range buf count then unmodeled
      else if w_is0 count then access_ok_zero buf count (ret_only (Z_to_bv 64 0))
      else if !pipe_end_live (m_fds m) id false then unmodeled
      else
        match pipe_lookup (m_pipes m) id with
        | none => unmodeled
        | some st =>
            if !pipe_write_room st (bv_unsigned count) then unmodeled
            else
              let bs := write_source i.in_mem buf count
              if !(bs.length == word_to_nat count) then unmodeled
              else
                set_pipes (pipe_insert (m_pipes m) id (pipe_append st bs)) ;;
                record_copyins [(buf, bs.length)] (ret_only count)

/-! ## pread64 (67) and pwrite64 (68): `read` and `write` at a position the call names

Twins of Rocq's `ppos_einvalb`, `pread64_spec` and `pwrite64_spec`.  The
argument for two separate specs rather than `read_spec`/`write_spec` at
a substituted offset is Rocq's (the header above `ppos_einvalb` in
`theories/LinuxProcessSem/Sys/Fs/ReadWrite.v`), and what it rests on at
Linux v6.18.46 (commit 1f99e9ab748f) is where the two syscalls diverge
from the plain ones BEFORE `vfs_read`/`vfs_write` is entered:
`ksys_pread64` (fs/read_write.c:752-766) tests `pos < 0` (:755-756)
above the `CLASS(fd, f)(fd)` that fetches the descriptor (:758), answers
-EBADF on an empty slot (:759-760), and calls `vfs_read` with the
address of its own `pos` parameter only when the descriptor carries
`FMODE_PREAD` (:762-763), answering -ESPIPE otherwise (:765);
`ksys_pwrite64` (fs/read_write.c:782-796, v6.18.46) is the same shape over
`FMODE_PWRITE` (:785-786, :788, :789-790, :792-793, :795).
`do_dentry_open` sets both bits on every path open (fs/open.c:961, v6.18.46,
together with `FMODE_LSEEK`); a pipe end and a socket never pass there —
`create_pipe_files` (fs/pipe.c:944, v6.18.46) and `sock_alloc_file`
(net/socket.c:483, v6.18.46) build their files with `alloc_file_pseudo`,
and the pipe's read end with `alloc_file_clone` from it (fs/pipe.c:956;
fs/file_table.c:464-475, v6.18.46), both through `file_init_path`
(fs/file_table.c:356-377, v6.18.46), which sets neither
bit — and `stream_open`, which both run (fs/pipe.c:966-967; net/socket.c:494),
clears all three besides (fs/open.c:1658, v6.18.46, in :1656-1661), which is
why a pipe end and a socket are -ESPIPE
here where `read`/`write` on the wrong end are -EBADF.  A CHANNEL is
-ESPIPE by the piped-stdio assumption the header names
(`linux-process-semantics@ff0313ba4f:bugs/channel-fds-assume-unidirectional-stdio.md`):
the harness's stdio descriptors are pipes.

SPELLINGS, beyond the module header's: Rocq's `FdFile p _ | FdFileRW p _`
arm of `pread64_spec`, and its `FdFileW p _ | FdFileRW p _` arm of
`pwrite64_spec`, are each written here as two arms with one body
repeated, one arm per constructor, which is what Lean's `match` takes.
Each match enumerates the constructors without a wildcard, so the day a
constructor lands it is a decision here and not an inherited arm. -/

/-- `pos < 0`, the first test in both `ksys_pread64` (fs/read_write.c:755-756,
v6.18.46) and `ksys_pwrite64` (fs/read_write.c:785-786): `pos` arrives as an
`loff_t`, signed 64-bit, so the test is on `bv_signed` and not on the
unsigned word, and both specs make it before the descriptor is looked up
(the `CLASS(fd, f)(fd)` declarations are :758 and :788). -/
def ppos_einvalb (pos : word) : Bool := bv_signed pos < 0

/-- `pread64 fd buf count pos`: `read_spec`'s answer at `pos` rather than at
the descriptor's own offset, and without moving that offset — the advance
`vfs_read` makes lands in `ksys_pread64`'s own `pos` parameter
(fs/read_write.c:763, v6.18.46) and is discarded, so a conforming pread
leaves the fd table exactly as it found it.

In the kernel's order: `ppos_einvalb` before the descriptor; -EBADF on an
empty slot; -ESPIPE on the three kinds without `FMODE_PREAD` (section
header); -EBADF on a write-only file, `vfs_read`'s `FMODE_READ` test
(fs/read_write.c:556-557, v6.18.46), reached because a regular file keeps
`FMODE_PREAD` whatever its access mode; then, on every kind that reaches
the transfer, `vfs_read`'s `access_ok` on the count the call NAMED
(:560-561) ahead of `rw_verify_area` (:563-565), whose
`(loff_t)(pos + count) < 0` test (:467-469, through `rw_pos_einvalb`) is
applied to the UNCLAMPED count as `vfs_read` applies it — the
`MAX_RW_COUNT` clamp is two statements later (:566-567).  `read_spec`
does not carry the position test
(`linux-process-semantics@ff0313ba4f:bugs/read-write-position-past-llong-max-answers-zero.md`);
here `pos`
is an argument and the test is unavoidable.  A directory then answers
`generic_read_dir`'s -EISDIR (fs/libfs.c:224-227, v6.18.46); /dev/null
`read_null`'s 0 (drivers/char/mem.c:412-416, v6.18.46), its `FMODE_READ`
test failing on a write-only description as for a file; /dev/urandom
`urandom_read_iter` (drivers/char/random.c:1453, v6.18.46; the `.read_iter`
of `urandom_fops`, :1573), which reads no position,
so the same bytes come off the same declared stream a plain `read` would
take (`read_urandom`); and a regular file delivers the bytes at `pos`
truncated at end-of-file and at `rw_count_clamp`.  Both character
devices carry `FMODE_PREAD`: `do_dentry_open` sets it (fs/open.c:961,
v6.18.46) and `memory_open` (drivers/char/mem.c:707-727, v6.18.46) clears
nothing, and neither `null_fops` (drivers/char/mem.c:644-652, v6.18.46) nor
`urandom_fops` (drivers/char/random.c:1572-1581, v6.18.46) is a stream, so `rw_verify_area`'s
position test applies to them as to a file.

UNMODELED (fail closed), both Rocq's: `read_spec`'s destination-shape
gap — a delivered prefix that is nonempty, writable at its first byte
and not writable throughout, where Linux's count is the copy routine's
rounded progress — and a file fd whose path the file system does not
hold, which `openat` makes unreachable. -/
def pread64_spec (fd buf count pos : word) : Sys SyscallEffect :=
  if ppos_einvalb pos then err_ret EINVAL
  else
  i <- input ;;
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some (.FdChannel _) => err_ret ESPIPE
  | some (.FdPipe _ _) => err_ret ESPIPE
  | some (.FdSocket _) => err_ret ESPIPE
  | some (.FdFileW _ _) => err_ret EBADF
  | some (.FdFileA _ _) => err_ret EBADF
  | some (.FdDevNull rd _) =>
      if !rd then err_ret EBADF
      else if !access_okb buf (bv_unsigned count) then err_ret EFAULT
      else if rw_pos_einvalb pos (bv_unsigned count) then err_ret EINVAL
      else ret_only (Z_to_bv 64 0)
  | some .FdUrandom =>
      if !access_okb buf (bv_unsigned count) then err_ret EFAULT
      else if rw_pos_einvalb pos (bv_unsigned count) then err_ret EINVAL
      else read_urandom buf count i m
  | some .FdDir =>
      if !access_okb buf (bv_unsigned count) then err_ret EFAULT
      else if rw_pos_einvalb pos (bv_unsigned count) then err_ret EINVAL
      else err_ret EISDIR
  | some (.FdFile p _) =>
      if !access_okb buf (bv_unsigned count) then err_ret EFAULT
      else if rw_pos_einvalb pos (bv_unsigned count) then err_ret EINVAL
      else
        match fs_lookup (m_fs m) p with
        | none => unmodeled
        | some data =>
          let bs := file_read data pos (Z_to_bv 64 (rw_count_clamp count))
          match read_bytes_map i.in_wmem buf (len_word bs) with
          | none =>
              match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
              | none => err_ret EFAULT
              | some _ => unmodeled
          | some _ =>
              Monad.pure (mkEffect (len_word bs) (delivered_writes buf bs) [])
  | some (.FdFileRW p _) =>
      if !access_okb buf (bv_unsigned count) then err_ret EFAULT
      else if rw_pos_einvalb pos (bv_unsigned count) then err_ret EINVAL
      else
        match fs_lookup (m_fs m) p with
        | none => unmodeled
        | some data =>
          let bs := file_read data pos (Z_to_bv 64 (rw_count_clamp count))
          match read_bytes_map i.in_wmem buf (len_word bs) with
          | none =>
              match read_bytes_map i.in_wmem buf (Z_to_bv 64 1) with
              | none => err_ret EFAULT
              | some _ => unmodeled
          | some _ =>
              Monad.pure (mkEffect (len_word bs) (delivered_writes buf bs) [])

/-- `pwrite64 fd buf count pos`: `write_spec`'s file arm at `pos`, without
moving the descriptor's offset (`ksys_pwrite64` hands `vfs_write` its own
`pos`, fs/read_write.c:793, v6.18.46, and discards the advance).

In the kernel's order: `ppos_einvalb` before the descriptor; -EBADF on an
empty slot; -ESPIPE on the three kinds without `FMODE_PWRITE` (section
header) — which is where `write_spec`'s channel over-approximation, pipe
capacity and socket -EPIPE stop being reachable at all; -EBADF from
`vfs_write`'s `FMODE_WRITE` test (fs/read_write.c:670-671, v6.18.46) on a
read-only
file, on /dev/urandom (every descriptor of that kind this model mints is
read-only, `write_spec`'s docstring), on a read-only /dev/null and on a
directory — a directory reaches that test holding `FMODE_PWRITE`, since
`do_dentry_open` set the bit for it too, and so answers -EBADF and NOT
-EISDIR; then `vfs_write`'s `access_ok` on the count the call named
(:674-675), which `write_spec` does not make and this arm does (Rocq's
docstring says why: a count whose range merely ENDS past `TASK_SIZE`);
then `rw_verify_area`'s position test (:677-679, :467-469) on the
unclamped count; then the transfer.  /dev/null returns the count clamped
at `MAX_RW_COUNT` (`write_null`, drivers/char/mem.c:418-422, v6.18.46, after
`vfs_write`'s clamp at fs/read_write.c:680-681, v6.18.46), no byte read and
no
ledger.  A write-only file lands the readable prefix of the CLAMPED range
(`write_source`) at `pos`, zero-filling a hole past end-of-file
(`file_write`), returns that prefix's length and records it; the count
carries NO bound beyond the clamp (argued in Rocq).

UNMODELED (fail closed): a hole past end-of-file wider than
`modeled_zero_fill` admits — `write_spec`'s decline, tested on `pos`
exactly as it is tested on the fd's offset there, so pwrite reaches no
offset a chain of writes could not; a file fd whose path the file system
does not hold; and an APPEND fd, the one kind this syscall cannot answer
with the file arm below.  `iocb_flags` (include/linux/fs.h, v6.18.46)
turns O_APPEND into IOCB_APPEND and `generic_write_checks`
(mm/filemap.c) then assigns `ki_pos = i_size_read(inode)`, so the `pos`
the call named is DISCARDED and the bytes land at end-of-file.  Putting
them at `pos` would be a wrong modeled behaviour rather than a missing
one, so that arm fails closed. -/
def pwrite64_spec (fd buf count pos : word) : Sys SyscallEffect :=
  if ppos_einvalb pos then err_ret EINVAL
  else
  i <- input ;;
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some (.FdChannel _) => err_ret ESPIPE
  | some (.FdPipe _ _) => err_ret ESPIPE
  | some (.FdSocket _) => err_ret ESPIPE
  | some (.FdFile _ _) => err_ret EBADF
  | some .FdUrandom => err_ret EBADF
  | some (.FdDevNull _ wr) =>
      if !wr then err_ret EBADF
      else if !access_okb buf (bv_unsigned count) then err_ret EFAULT
      else if rw_pos_einvalb pos (bv_unsigned count) then err_ret EINVAL
      else ret_only (Z_to_bv 64 (rw_count_clamp count))
  | some .FdDir => err_ret EBADF
  | some (.FdFileA _ _) => unmodeled
      -- the named `pos` is discarded on an append fd, so the arm below
      -- would put the bytes in the wrong place: fail closed
  | some (.FdFileW p _) =>
      if !access_okb buf (bv_unsigned count) then err_ret EFAULT
      else if rw_pos_einvalb pos (bv_unsigned count) then err_ret EINVAL
      else
        let bs := write_source i.in_mem buf count
        if !w_is0 count && bs.length == 0 then err_ret EFAULT
        else
          match fs_lookup (m_fs m) p with
          | none => unmodeled
          | some data =>
              if !modeled_file_gap data pos bs then unmodeled
              else
                set_fs (fs_set (m_fs m) p (file_write data pos bs)) ;;
                (if w_is0 count then ret_only (len_word bs)
                 else record_copyins [(buf, bs.length)] (ret_only (len_word bs)))
  | some (.FdFileRW p _) =>
      if !access_okb buf (bv_unsigned count) then err_ret EFAULT
      else if rw_pos_einvalb pos (bv_unsigned count) then err_ret EINVAL
      else
        let bs := write_source i.in_mem buf count
        if !w_is0 count && bs.length == 0 then err_ret EFAULT
        else
          match fs_lookup (m_fs m) p with
          | none => unmodeled
          | some data =>
              if !modeled_file_gap data pos bs then unmodeled
              else
                set_fs (fs_set (m_fs m) p (file_write data pos bs)) ;;
                (if w_is0 count then ret_only (len_word bs)
                 else record_copyins [(buf, bs.length)] (ret_only (len_word bs)))

/-! ## The vectored calls: `readv` (65) and `writev` (66)

Everything below is read at Linux v6.18.46 (commit 1f99e9ab748f), in the
order the kernel decides it: fs/read_write.c `do_readv` (:1068-1089) →
`vfs_readv` (:990-1026) → lib/iov_iter.c `import_iovec` (:1424-1430) →
`__import_iovec` (:1352-1400), then `rw_verify_area` (fs/read_write.c:451-478,
Linux v6.18.46) and the read operation; and, for the write side, `do_writev`
(:1091-1112) → `vfs_writev` (:1028-1066) through the same import.  The
import itself is `State.import_iovecs`, and the per-function
argument is on it; this file adds the gates in front of it and the arms
behind it. -/

/-- writev's and readv's `iovcnt` reach the kernel as a full 64-bit
register, declared `unsigned long` at the syscall boundary
(`SYSCALL_DEFINE3(readv)`, fs/read_write.c:1162-1166, and
`SYSCALL_DEFINE3(writev)`, fs/read_write.c:1168-1172, v6.18.46) and reach `__import_iovec` through
`import_iovec`'s `unsigned nr_segs` (lib/iov_iter.c:1424-1425,
v6.18.46): only the low 32 bits are validated and used.  writev(fd, iov,
2^32 + 2) really writes 2 iovecs, writev(fd, iov, 2^32) transfers nothing
and returns 0, and a count whose low 32 bits exceed `IOV_MAX` — every
negative `int` count included — is -EINVAL.  Commits bc917be8 and 0504c074
(Al Viro, first released in v4.1) put the `unsigned` boundary there;
qemu-user's `lock_iovec` validates the raw 64-bit count instead, and the
model rejects its -EINVAL for a count over `IOV_MAX` whose low 32 bits
are in range.
Rocq: `ReadWrite.iovcnt32`. -/
def iovcnt32 (iovcnt : word) : word := abi_low32 iovcnt

/-- A writev buffer-shape gap: the model cannot describe this transfer, so
it DECLINES.  One name for every writev decline, as `readv_buf_gap` is
for readv.  (An unreadable iovec array or source buffer is NOT routed
here: those are a genuine -EFAULT or short write through the gather.)
Rocq: `ReadWrite.writev_buf_gap`. -/
def writev_buf_gap : Sys SyscallEffect := unmodeled

/-- The ledger and the return, shared by the file writev arms: the prefix
of the CAPPED vector the write actually read, and its length.  A zero
aggregate never reaches here — `writev_file_arm` (below) returns 0 before it,
without inspecting a source byte, as `vfs_writev` does at `if (!tot_len)
goto out` (fs/read_write.c:1047-1049, v6.18.46).  Rocq:
`ReadWrite.writev_ledger`. -/
def writev_ledger (iovs : List (word × word)) (bs : List byte) : Sys SyscallEffect :=
  record_copyins (iov_prefix_accesses (cap_iovecs iovs) bs.length) (ret_only (len_word bs))

/-- The shape every file writev arm shares (Rocq: `ReadWrite.writev_file_arm`,
whose header carries the three-arm argument): the import and its access
ledger (`vfs_writev`, fs/read_write.c:1042-1043, v6.18.46), the import's two
errnos (lib/iov_iter.c, v6.18.46: -EFAULT from `copy_iovec_from_user`
:1263-1266 on a descriptor it cannot read and from `__import_iovec` :1384
on a range that leaves the address space; -EINVAL from `iovec_from_user`
:1306-1307 and `copy_iovec_from_user` :1276-1279), the
zero-aggregate 0 (`vfs_writev` :1047-1049), `rw_verify_area`'s position
test on `off` (:1051, then fs/read_write.c:467-469, v6.18.46), the -EFAULT when
nothing is gatherable, the error-encoded-length decline, and the ledger.

`place bs` is the KIND's own middle: `none` where that kind declines,
otherwise the state update carrying the destination and the written-back
entry, handed the shared ledger as its continuation.  It is not passed
the imported vector: the ledger is the only thing that reads it, and the
ledger is built here.

A GATHERED PREFIX SHORTER THAN THE CAPPED AGGREGATE IS PLACED, whatever
its length: this helper tests only whether the gather is EMPTY.  A source
readable at its first byte but not throughout therefore delivers that
prefix, as Linux from v5.18 does — `generic_perform_write`
(mm/filemap.c:4244-4335, v6.18.46) bails with -EFAULT only when
`fault_in_iov_iter_readable` faults in none of the chunk (:4321-4324, the
`== bytes` test commit 631f871f0717 introduced for v5.18) and otherwise
copies as far as the fault and returns `written` (:4331-4334) — and as
the scalar `write_file_tail` does.  Linux v4.17 through v5.17 fault each
chunk in BEFORE `write_begin` and answer the prefix cut back to a page
boundary of the file position, and qemu-user's `lock_iovec` zeroes the
length of a later descriptor it cannot lock whole
(linux-user/syscall.c:3120-3134, QEMU 11.1.1), so this delivery is a
known divergence from both.

THE POSITION TEST READS THE FD'S REAL `f_pos` ON EVERY KIND — `do_writev`
(fs/read_write.c:1098-1102, v6.18.46) hands `vfs_writev`
(fs/read_write.c:1028-1066) the value `file_ppos` (fs/read_write.c:699-702)
reads — `f_pos` for every kind that is not `FMODE_STREAM` — copied into a
local it passes by address and writes back on success (:1098-1105) — which
is why it is stated on `off` here and not on the destination; the append
arm is the one it matters for, and `writev_spec`'s `FdFileA` arm says so.

THE `addr_is_error_b` DECLINE SITS BEHIND `place` and not in front of it:
after the kind's own guards and before its update.  It is unreachable
under the aggregate cap — `bs` is a prefix of the CAPPED vector, so its
length is at most `MAX_RW_COUNT` — and every decline around it is the same
`writev_buf_gap`, so the position is not observable.

COUNTS 9 TO `IOV_MAX` ARE JUDGED HERE, where `readv_spec` declines them
(`readv_heap_iovecb`): `iovec_from_user` allocates the array with
`kmalloc_array` and may answer -ENOMEM (lib/iov_iter.c:1308-1312,
v6.18.46), an answer this helper never gives.  That is Rocq's shape and
Rocq's recorded divergence,
`linux-process-semantics@ff0313ba4f:bugs/writev-heap-iovec-enomem-not-admitted.md`,
which this helper inherits with `writev_spec`. -/
def writev_file_arm (mp : word → Option byte) (iov iovcnt off : word)
    (place : List byte → Option (Sys SyscallEffect → Sys SyscallEffect)) : Sys SyscallEffect :=
  record_copyins (import_iovecs_accesses mp iov (iovcnt32 iovcnt))
    (match import_iovecs mp iov (iovcnt32 iovcnt) with
     | .ImpFault => err_ret EFAULT
     | .ImpInval => err_ret EINVAL
     | .ImpOk iovs0 =>
         let total := iovs_total (cap_iovecs iovs0)
         let bs := writev_gathered mp iovs0
         if total == 0 then ret_only (Z_to_bv 64 0)
         else if rw_pos_einvalb off total then err_ret EINVAL
         else if bs.length == 0 then err_ret EFAULT
         else
           match place bs with
           | none => writev_buf_gap
           | some upd =>
               if addr_is_error_b (len_word bs) then writev_buf_gap
               else upd (writev_ledger iovs0 bs))

/-- The fd kinds a readv reaches once the `FMODE_READ` gate has passed.
Naming them keeps `readv_imported` total without carrying an arm for a
case the gate has already excluded.  Rocq: `ReadWrite.ReadableFd`. -/
inductive ReadableFd : Type
  | RdChannel (chan : word)
  | RdFile (p : path) (offset : word)
  /-- The same file at the same offset, through an O_RDWR description.
  A separate constructor rather than `RdFile`, because `readv_imported`
  writes the entry back: folding an O_RDWR fd into `RdFile` would store
  it under the read-only kind, and a later write would answer a -EBADF
  Linux never returns. -/
  | RdFileRW (p : path) (offset : word)
  | RdDir
  | RdSocket (sk : SockState)
  | RdPipe (id : word)
  /-- /dev/null opened for reading.  It carries nothing because the read
  arm consults nothing: `read_iter_null` returns 0 (drivers/char/mem.c
  :424-427, v6.18.46). -/
  | RdDevNull
  /-- /dev/urandom, which is only ever open for reading.  It carries
  nothing because the stream it would read is the model's
  (`State.m_urandom`), not the descriptor's. -/
  | RdUrandom

/-- `FMODE_READ` (`vfs_readv`'s first test, fs/read_write.c:999-1000,
v6.18.46): an fd not open for reading is -EBADF, decided BEFORE the iovec
array is imported (:1004-1005).  Of the channels only stdin is readable —
an ASSUMPTION about the stdio the process was handed rather than a fact
about the fd number; see
`linux-process-semantics@ff0313ba4f:bugs/channel-fds-assume-unidirectional-stdio.md`.
`FdFileW` and
`FdFileA` are the model's O_WRONLY files — the append word carries
O_WRONLY — and a pipe's WRITE end is the third thing this gate turns
away.

A SOCKET PASSES THIS GATE, and answering `none` for it would be a FALSE
-EBADF — a confidently wrong modeled answer, not a gap: net/socket.c
`sock_alloc_file` (:476-484, v6.18.46) creates every socket file with
`O_RDWR | (flags & O_NONBLOCK)` (:483-484), so `FMODE_READ` is always
set; `RdSocket` carries the socket's state so the read arm can answer for
it.  A PIPE'S READ END PASSES IT FOR THE SAME REASON, and the write end is
the one case here where `none` is the kernel's own answer rather than a
shortage of state: fs/pipe.c `create_pipe_files` (:926, v6.18.46) opens
`res[1]` O_WRONLY (:944-945) and `res[0]` O_RDONLY (:956), so -EBADF on
the write end is exact.  A write-only /dev/null gets the same -EBADF: the
access mode the open granted IS `FMODE_READ`, so the gate is exact in
both directions.  Rocq: `ReadWrite.readable_fd`.

The match is enumerated without a wildcard on purpose: an `FdEntry`
constructor added later is a decision here, not an inherited -EBADF. -/
def readable_fd (e : FdEntry) : Option ReadableFd :=
  match e with
  | .FdChannel ch => if w_is0 ch then some (.RdChannel ch) else none
  | .FdFile p off => some (.RdFile p off)
  | .FdFileRW p off => some (.RdFileRW p off)
    -- O_RDWR carries FMODE_READ, so the gate must let it through, and
    -- `RdFileRW` is what keeps the write-back on the right kind
  | .FdDir => some .RdDir
  | .FdSocket sk => some (.RdSocket sk)
  | .FdFileW _ _ => none
  | .FdFileA _ _ => none
    -- an append fd is O_WRONLY too, so this is the kernel's own -EBADF
    -- and not a shortage of state
  | .FdPipe id w => if w then none else some (.RdPipe id)
  | .FdDevNull rd _ => if rd then some .RdDevNull else none
  | .FdUrandom => some .RdUrandom

/-- Linux keeps eight iovecs on the syscall stack (`UIO_FASTIOV`,
include/uapi/linux/uio.h:45, v6.18.46) sizing `vfs_readv`'s `iovstack`
(fs/read_write.c:993, v6.18.46).  For counts 9 through `IOV_MAX`, lib/iov_iter.c
`iovec_from_user` (:1308-1312, v6.18.46) allocates a temporary array with
`kmalloc_array` and may fail with -ENOMEM (:1311) before it reads a
descriptor or applies `access_ok`.  The model does not represent this
allocation choice, so it fails closed on the whole heap-backed range
(`readv_heap_iovecb`).  The fd and FMODE_READ gates in `readv_spec` run
first; counts above `IOV_MAX` are -EINVAL without allocating (:1306-1307),
and a count of one never allocates at all (`__import_iovec` :1360-1361).
Rocq: `ReadWrite.UIO_FASTIOV`. -/
def UIO_FASTIOV : Int := 8

/-- The heap-backed count band.  The outer parentheses change no value.
Without them `lean_mutate`'s guard-drop reads the first conjunct as
starting on the `let` line, and its mutant does not parse, so the
`UIO_FASTIOV` bound had no mutant a pin could kill.
Rocq: `ReadWrite.readv_heap_iovecb`. -/
def readv_heap_iovecb (iovcnt : word) : Bool :=
  let n := bv_unsigned (iovcnt32 iovcnt)
  ((UIO_FASTIOV < n) && (n ≤ IOV_MAX))

/-- A readv destination-shape gap: the model cannot describe this
delivery, so it DECLINES.  The input-side analogue of `writev_buf_gap`.
Rocq: `ReadWrite.readv_buf_gap`. -/
def readv_buf_gap : Sys SyscallEffect := unmodeled

/-- Fail closed on the heap-backed count band (`readv_heap_iovecb`).  A
DISTINCT NAME for a distinct reason to decline — the optional -ENOMEM of
the temporary iovec allocation, not an unrepresentable buffer shape — but
deliberately not a second copy of the policy: one body, so the two cannot
drift apart.  Rocq: `ReadWrite.readv_heap_gap`. -/
def readv_heap_gap : Sys SyscallEffect := readv_buf_gap

/-- Execute readv once `State.import_iovecs` has accepted the descriptor
array.  `iovs0` is the array as imported; the aggregate cap is applied
here (`State.cap_iovecs`), and everything below reads the CAPPED vector —
entries past `MAX_RW_COUNT` survive at length zero, so they still occupy
an index but can carry no bytes.

A zero aggregate returns 0 before anything else (`vfs_readv`: `tot_len =
iov_iter_count(&iter)`, then `if (!tot_len) goto out`, fs/read_write.c
:1009-1011, v6.18.46 — ahead of `rw_verify_area` at :1013 and of the
operation at :1017-1020), which is why an all-zero vector on a directory
is 0 and not -EISDIR.

A PARTIALLY WRITABLE DESTINATION IS UNDESCRIBED for every kind that
copies, and Rocq's note above `readv_imported` carries the argument in
full: the copy is one primitive everywhere (lib/iov_iter.c `_copy_to_iter`,
v6.18.46, stepping `copy_to_user_iter` over each segment), a fault inside it is
reported by arch/riscv/lib/uaccess.S's fixup as the copy routine's ROUNDED
progress, and what each kind then returns — a file (mm/shmem.c
`shmem_file_read_iter`, :3370, v6.18.46) the bytes already read or -EFAULT, a pipe
(fs/pipe.c `anon_pipe_read`, v6.18.46) whole buffers, a TCP socket (net/ipv4/tcp.c
`tcp_recvmsg_locked`, :2634, v6.18.46) whole skbs — depends on state the model does
not carry.  So, with `w` the writable prefix of the capped scatter and
`need` the bytes the source can supply now: `w = 0` is -EFAULT with nothing
stored and nothing consumed, exact for every kind; `w ≥ need` is the
delivery — exactly `need` for a file, any nonempty prefix for a pipe or
socket; `0 < w < need` is `readv_buf_gap`.  Zero-length entries take no
part in `w`: `iterate_iovec` skips a segment with no bytes left
(include/linux/iov_iter.h:51, `if (likely(part))`, v6.18.46) and never
touches its base, which `State.scatter_iovecs` mirrors.

Per kind, all v6.18.46:

- CHANNEL: a nonempty prefix of the stream of the environment's
  choosing, as `read_spec`'s channel arm; sticky EOF is 0.
- SOCKET: exactly the channel rule on the connection's script — nothing
  about the vector reaches the protocol, `tcp_recvmsg_locked` sees only an
  `iov_iter` and its total, so a socket readv and a socket read of the
  same total allow the same lengths; the script's terminals answer as
  `read_spec`'s socket arm answers them, whose docstring has the lines.
- PIPE: VECTORED PIPE READS ARE UNMODELED, the mirror of `writev`'s pipe
  arm and for the same reason — the atomicity argument that makes the
  scalar arm deterministic is stated per transfer, not per vector.  The
  -EBADF ordering is still exact: `readable_fd` answers the write end
  before this point.
- /dev/null: `read_iter_null` (drivers/char/mem.c:424-427, v6.18.46) is `return 0`,
  reached through `do_iter_readv_writev` because `null_fops` carries
  `.read_iter` (:648); no destination byte is touched and `f_pos`, pinned
  at 0, cannot make `rw_verify_area` fire.
- /dev/urandom: FAIL-CLOSED, though derivable.  A real answer is
  `urandom_read_iter` (drivers/char/random.c:1453, v6.18.46) over the imported
  iterator — the capped aggregate's worth of bytes off the front of
  `State.m_urandom`, scattered as the channel arm scatters stdin's, with
  the same partial-destination decline.  Not written, so the vectored
  read declines rather than guess at a scatter; `read_urandom` is the
  scalar answer.
- DIRECTORY: fs/libfs.c `generic_read_dir` (:224-227, v6.18.46) is `return -EISDIR`,
  reached through fs/read_write.c `do_loop_readv_writev` (:835, v6.18.46) because a
  directory's operations carry `.read` and no `.read_iter`: -EISDIR on the
  first entry, the destination never consulted.  Everything the
  destination could have said was said at import: an entry outside the
  address space is -EFAULT there, an entry inside it imports whether or
  not it is mapped.  PREMISE: the directory's position is 0, so
  `rw_verify_area`'s position test cannot fire — `FdDir` tracks no
  position because nothing modeled moves it: `getdents64_spec` declines
  the listing that would (`Sys/Fs/Readdir.lean`; `iterate_dir` writes
  `ctx->pos` back to `f_pos`, fs/readdir.c:107-109, v6.18.46).  Rocq puts
  the position test in front of -EISDIR for the position a kernel can
  park a directory at: an exhausted ext4 listing sits at
  `EXT4_HTREE_EOF_64BIT` (fs/ext4/ext4.h:2589, v6.18.46), the `LLONG_MAX`
  the test refuses, where tmpfs parks at `DIR_OFFSET_EOD` (fs/libfs.c:248,
  v6.18.46), inside it.  The premise stops holding when a listing is
  modeled: `FdDir` then carries a position and the test is read on it.
- FILE: deterministic — exactly the bytes at the offset (`Fs.file_read`),
  after `rw_verify_area`'s position test (`rw_pos_einvalb`), the offset
  advanced by the delivery; a path the file system does not hold is a
  gap, since `openat` never mints one.  The `addr_is_error_b` decline
  cannot fire under the aggregate cap; it is what lets a checker conclude
  the return is not an errno without a separate bound lemma.  An O_RDWR
  file (`RdFileRW`) is that arm word for word, with the entry written
  back under its own kind.

Rocq: `ReadWrite.readv_imported`. -/
def readv_imported (fd : word) (r : ReadableFd) (iovs0 : List (word × word))
    (i : SyscallInput) (m : Model) : Sys SyscallEffect :=
  let iovs := cap_iovecs iovs0
  let total := iovs_total iovs
  if total == 0 then ret_only (Z_to_bv 64 0)
  else
  match r with
  | .RdChannel ch =>
      match (m_stdin m).uncons with
      | none => ret_only (Z_to_bv 64 0)
      | some _ =>
          match scatter_iovecs i.in_wmem iovs [Z_to_bv 8 0] with
          | none => err_ret EFAULT
          | some _ =>
              match scatter_iovecs i.in_wmem iovs (stream_take_z (m_stdin m) total).1 with
              | none => readv_buf_gap
              | some _ =>
                  bs <- choose (fun bs : List byte =>
                          1 ≤ (bs.length : Int)
                          ∧ (stream_take (m_stdin m) bs.length).1 = bs) ;;
                  writes <- choose (fun writes : List (word × List byte) =>
                              scatter_iovecs i.in_wmem iovs bs = some writes) ;;
                  set_stdin (stream_take (m_stdin m) bs.length).2 ;;
                  emit (List.map (ReadEv ch) bs) ;;
                  Monad.pure (mkEffect (len_word bs) writes [])
  | .RdSocket sk =>
      match sk with
      | .SkConnected peer ch rx =>
          match rx.cell_at 0 with
          | .NFin => ret_only (Z_to_bv 64 0)
          | .NRst =>
              set_fds (fd_insert (m_fds m) fd (.FdSocket (.SkReset peer ch))) ;;
              err_ret ECONNRESET
          | .NTimedOut =>
              set_fds (fd_insert (m_fds m) fd (.FdSocket (.SkReset peer ch))) ;;
              err_ret ETIMEDOUT
          | .NByte _ =>
              match scatter_iovecs i.in_wmem iovs [Z_to_bv 8 0] with
              | none => err_ret EFAULT
              | some _ =>
                  match scatter_iovecs i.in_wmem iovs (net_take_z rx total).1 with
                  | none => readv_buf_gap
                  | some _ =>
                      bs <- choose (fun bs : List byte =>
                              1 ≤ (bs.length : Int)
                              ∧ (net_take rx bs.length).1 = bs) ;;
                      writes <- choose (fun writes : List (word × List byte) =>
                                  scatter_iovecs i.in_wmem iovs bs = some writes) ;;
                      set_fds (fd_insert (m_fds m) fd
                                 (.FdSocket (.SkConnected peer ch (net_take rx bs.length).2))) ;;
                      emit (List.map (ReadEv ch) bs) ;;
                      Monad.pure (mkEffect (len_word bs) writes [])
      | .SkReset _ _ => ret_only (Z_to_bv 64 0)
      | .SkFresh | .SkBound | .SkListening => err_ret ENOTCONN
  | .RdPipe _ => readv_buf_gap
  | .RdDevNull => ret_only (Z_to_bv 64 0)
  | .RdUrandom => readv_buf_gap
  | .RdDir => err_ret EISDIR
  | .RdFile p off =>
      match fs_lookup (m_fs m) p with
      | none => readv_buf_gap
      | some data =>
          if rw_pos_einvalb off total then err_ret EINVAL
          else
          let bs := file_read data off (Z_to_bv 64 total)
          match scatter_iovecs i.in_wmem iovs bs with
          | some writes =>
              if addr_is_error_b (len_word bs) then readv_buf_gap
              else
              set_fds (fd_insert (m_fds m) fd (.FdFile p (off + len_word bs))) ;;
              Monad.pure (mkEffect (len_word bs) writes [])
          | none =>
              match scatter_iovecs i.in_wmem iovs [Z_to_bv 8 0] with
              | none => err_ret EFAULT
              | some _ => readv_buf_gap
  | .RdFileRW p off =>
      -- the `RdFile` arm above WORD FOR WORD, with the entry written back
      -- under the O_RDWR kind
      match fs_lookup (m_fs m) p with
      | none => readv_buf_gap
      | some data =>
          if rw_pos_einvalb off total then err_ret EINVAL
          else
          let bs := file_read data off (Z_to_bv 64 total)
          match scatter_iovecs i.in_wmem iovs bs with
          | some writes =>
              if addr_is_error_b (len_word bs) then readv_buf_gap
              else
              set_fds (fd_insert (m_fds m) fd (.FdFileRW p (off + len_word bs))) ;;
              Monad.pure (mkEffect (len_word bs) writes [])
          | none =>
              match scatter_iovecs i.in_wmem iovs [Z_to_bv 8 0] with
              | none => err_ret EFAULT
              | some _ => readv_buf_gap

/-- `readv fd iov iovcnt`: scatter the bytes a `read` of the same total
would deliver across the imported destination vectors, in order (Rocq:
`ReadWrite.readv_spec`, whose docstring carries DELIVERY, NONDETERMINISM
and STICKY EOF in full).  The ORDER, all Linux v6.18.46, from `do_readv`
(fs/read_write.c:1068-1089), `vfs_readv` (:990-1026) and `__import_iovec`
(lib/iov_iter.c:1352-1400): fd existence — `CLASS(fd_pos, f)(fd)` on the
fd truncated to 32 bits (`Syscall.fd32`, the table's), -EBADF on an empty
slot (:1071-1074); then read mode (`readable_fd`, :999-1000); then the
count band (`readv_heap_iovecb`, the -ENOMEM the model declines); then
the import — descriptor readability, negative lengths and `access_ok`
(`State.import_iovecs`, in the kernel's two passes: `copy_iovec_from_user`
(lib/iov_iter.c:1260-1290, v6.18.46) copies the descriptors in index order and stops
at the first field it cannot read, -EFAULT, or negative length, -EINVAL,
so either beats a range fault at any index; `__import_iovec` (:1377-1385)
then range-checks every copied entry on its uncapped length, except that
a count of one goes through `import_ubuf` (:1433-1438), which caps to
`MAX_RW_COUNT` before its range test) — then the aggregate cap,
a zero aggregate, the position test, and finally the read operation
(`readv_imported`).  The count is judged on its low 32 bits (`iovcnt32`).

Three -EFAULTs, in the kernel's order: an unreadable descriptor array or
descriptor, then an entry whose range leaves the user address space
(`State.access_okb`, zero-length entries included), both from the import
and before any byte moves; then, on the kinds that copy, a first
DELIVERED byte that cannot be written.  A zero-length entry with an
unmapped but in-range base is simply skipped.

Two things are NOT admitted, because both are qemu-user's behaviour
rather than any Linux's: a -EINVAL for a raw count over `IOV_MAX` decided
before the fd (Linux truncates the count and resolves the fd first), and
a 0 or -EFAULT decided by locking the destination vector before the read
(Linux touches the destination only as far as the copy goes). -/
def readv_spec (fd iov iovcnt : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF                -- fd not open: real -EBADF, not a modeling gap
  | some e =>
      match readable_fd e with
      | none => err_ret EBADF            -- FMODE_READ, ahead of the import
          -- EVERY `none` HERE IS A REAL -EBADF, including the pipe end that
          -- reaches it: `readable_fd` hands the read end a `RdPipe`
          -- (`create_pipe_files` opens it O_RDONLY), so the only pipe end
          -- left in this arm is the WRITE end, which is O_WRONLY and whose
          -- -EBADF is the kernel's own answer rather than a modeling gap
      | some r =>
          if readv_heap_iovecb iovcnt then readv_heap_gap
          else
            record_copyins (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
              (match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
               | .ImpFault => err_ret EFAULT
               | .ImpInval => err_ret EINVAL
               | .ImpOk iovs0 => readv_imported fd r iovs0 i m)

/-- `writev fd iov iovcnt`: the write of the GATHERED source, in the order
stable Linux v6.18.46 decides it (Rocq: `ReadWrite.writev_spec`, whose
docstring carries the six-step argument and the file arms' division of
labour in full).  From `do_writev` (fs/read_write.c:1091-1112), `vfs_writev`
(:1028-1066) and `__import_iovec` (lib/iov_iter.c:1352-1400, v6.18.46): the fd
low 32 bits (`Syscall.fd32`, the table's) — `CLASS(fd_pos, f)(fd)`, -EBADF
on an empty slot (:1094-1097); `FMODE_WRITE` clear is -EBADF (:1037-1038):
stdin BY ASSUMPTION
(`linux-process-semantics@ff0313ba4f:bugs/channel-fds-assume-unidirectional-stdio.md`), a
read-only file, a directory, a pipe's read end, `/dev/urandom`, a read-only
`/dev/null`; then the import (:1042-1043), the same `State.import_iovecs`
readv imports through, the count on its low 32 bits (`iovcnt32`); a zero
aggregate returns 0 before `rw_verify_area` and before the write operation
on EVERY kind (:1047-1049), so a pipe write end answers it ahead of the
vectored-pipe decline; then `rw_verify_area`'s position test on a file
with a position (:1051, `rw_pos_einvalb` inside `writev_file_arm`); then
the write.  The bytes available to it are the GATHERABLE PREFIX over the
CAPPED vector (`State.writev_gathered`); nothing gatherable while
something was requested is -EFAULT.  A channel delivers a NONEMPTY prefix
of the environment's choosing, as `write_spec` does; a file exactly the
gatherable prefix, advancing its offset; `/dev/null` answers the capped
aggregate without reading a buffer (`write_iter_null`,
drivers/char/mem.c:429-434, v6.18.46, advances by `iov_iter_count` and
returns it);
a vectored write to a pipe or a socket declines (`writev_buf_gap`: the
scalar pipe arm's atomicity argument is per transfer, not per vector, and
the socket argument is `write_spec`'s).

The three file arms share `writev_file_arm`: `FdFileW` and `FdFileRW`
place the gathered bytes at `f_pos` under `modeled_file_gap` and advance
the entry, and `FdFileA` places them at end-of-file with no gap guard,
moving `f_pos` to the new end (`append_new_pos`) while keeping the
position test on the fd's REAL `f_pos`. -/
def writev_spec (fd iov iovcnt : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF                        -- fd not open: real -EBADF
  | some (.FdFile _ _) => err_ret EBADF          -- fd open read-only: real -EBADF
  | some .FdDir => err_ret EBADF                 -- directory fds are O_RDONLY
  | some (.FdSocket _) => writev_buf_gap
  | some (.FdChannel ch) =>
      if w_is0 ch then err_ret EBADF       -- channel 0 is read-only BY ASSUMPTION
      else
        record_copyins (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
          (match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
           | .ImpFault => err_ret EFAULT
           | .ImpInval => err_ret EINVAL
           | .ImpOk iovs0 =>
               let total := iovs_total (cap_iovecs iovs0)
               let bs := writev_gathered i.in_mem iovs0
               if total == 0 then ret_only (Z_to_bv 64 0)   -- no buffer inspected
               else if bs.length == 0 then err_ret EFAULT   -- not even the first byte readable
               else if addr_is_error_b (len_word bs) then writev_buf_gap
               else
                 ds <- choose (fun ds : List byte =>
                         1 ≤ (ds.length : Int)
                         ∧ ds = bs.take ds.length) ;;
                 emit (List.map (WriteEv ch) ds) ;;
                 record_copyins (iov_prefix_accesses (cap_iovecs iovs0) ds.length)
                   (ret_only (len_word ds)))
  | some (.FdFileW p off) =>
      writev_file_arm i.in_mem iov iovcnt off (fun bs =>
        match fs_lookup (m_fs m) p with
        | none => none                          -- an FdFileW always points into the fs
        | some data =>
            if !modeled_file_gap data off bs then none
            else
              some (fun k =>
                set_fs (fs_set (m_fs m) p (file_write data off bs)) ;;
                set_fds (fd_insert (m_fds m) fd (.FdFileW p (off + len_word bs))) ;;
                k))
  | some (.FdFileRW p off) =>
      writev_file_arm i.in_mem iov iovcnt off (fun bs =>
        match fs_lookup (m_fs m) p with
        | none => none                          -- an FdFileRW always points into the fs
        | some data =>
            if !modeled_file_gap data off bs then none
            else
              some (fun k =>
                set_fs (fs_set (m_fs m) p (file_write data off bs)) ;;
                set_fds (fd_insert (m_fds m) fd (.FdFileRW p (off + len_word bs))) ;;
                k))
  | some (.FdFileA p off) =>
      -- the destination MOVES to end-of-file and the `modeled_file_gap`
      -- guard goes with it; the position test inside `writev_file_arm`
      -- still reads the fd's REAL `off`
      writev_file_arm i.in_mem iov iovcnt off (fun bs =>
        match fs_lookup (m_fs m) p with
        | none => none                          -- an FdFileA always points into the fs
        | some data =>
            some (fun k =>
              set_fs (fs_set (m_fs m) p (file_write data (len_word data) bs)) ;;
              set_fds (fd_insert (m_fds m) fd (.FdFileA p (append_new_pos data bs off))) ;;
              k))
  | some .FdUrandom => err_ret EBADF         -- O_RDONLY, always, before the import
  | some (.FdDevNull _ wr) =>
      if !wr then err_ret EBADF              -- O_RDONLY: FMODE_WRITE, before the import
      else
        record_copyins (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
          (match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
           | .ImpFault => err_ret EFAULT
           | .ImpInval => err_ret EINVAL
           | .ImpOk iovs0 => ret_only (Z_to_bv 64 (iovs_total (cap_iovecs iovs0))))
  | some (.FdPipe _ w) =>
      if !w then err_ret EBADF               -- the READ end is O_RDONLY: real -EBADF
      else
        record_copyins (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
          (match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
           | .ImpFault => err_ret EFAULT
           | .ImpInval => err_ret EINVAL
           | .ImpOk iovs0 =>
               if iovs_total (cap_iovecs iovs0) == 0 then ret_only (Z_to_bv 64 0)
               else writev_buf_gap)             -- VECTORED PIPE WRITES ARE UNMODELED

/-! ## lseek (62)

Twins of Rocq's `lseek_base`, `lseek_dest` and `lseek_spec`.  `ksys_lseek`
(fs/read_write.c:393-408, Linux v6.18.46, commit 1f99e9ab748f) fetches the
descriptor first (`CLASS(fd_pos, f)(fd)`, :396; -EBADF on `fd_empty`,
:397-398), then tests `whence <= SEEK_MAX` (:400-401) and only then calls
`vfs_llseek` (:402), which answers -ESPIPE for a file without
`FMODE_LSEEK` (fs/read_write.c:385-390, v6.18.46, the test at :387-388)
before any
`f_op` is consulted — so the spec resolves the fd, then the whence, then
the kind, and `lseek(pipe, 0, 42)` is -EINVAL where `lseek(pipe, 0,
SEEK_HOLE)` is -ESPIPE.  Both `fd` and `whence` are `unsigned int` in
`SYSCALL_DEFINE3(lseek, …)` (fs/read_write.c:410-413, v6.18.46) and arrive
here
through `fd32` and `whence32`; `offset` is `off_t`, the full register.

Which kinds lack `FMODE_LSEEK`: a path open sets it in `do_dentry_open`
(fs/open.c:961, v6.18.46) and clears it again for a table with no
`.llseek` (:976-977); a pipe end or a socket never passes there — its file
is `alloc_file_pseudo`'s (`create_pipe_files`, fs/pipe.c:944;
`sock_alloc_file`, net/socket.c:483, v6.18.46) or, for the pipe's read
end, `alloc_file_clone`'s (fs/pipe.c:956; fs/file_table.c:464-475,
v6.18.46), and both reach `file_init_path`, which sets
the bit only for a table with an `.llseek` (fs/file_table.c:364-365,
v6.18.46, in :356-377), and `pipeanon_fops` (fs/pipe.c:1257-1266) and
`socket_file_ops` (net/socket.c:156-173) have none — and `stream_open`
(fs/open.c:1658), which both run (fs/pipe.c:966-967; net/socket.c:494),
clears a bit that was never set; a channel is a pipe by the piped-stdio
assumption.

SPELLINGS: Rocq's four file arms of `lseek_spec` are four here, in Rocq's
order — `FdFile`, `FdFileRW`, `FdFileW`, `FdFileA` — each written out
with the same body under its own kind.  The match enumerates the
constructors with no wildcard. -/

/-- The whence-selected origin — 0, the fd's current offset, or the file's
length — `must_set_pos`'s three answering cases (fs/read_write.c:102-140,
v6.18.46: SEEK_END adds `eof` at :106-107, SEEK_CUR is folded into
`generic_file_llseek_size`'s `file->f_pos + offset` at :170-183 — or, for
a zero displacement, answered as `f_pos` outright at :115-118 and
:167-168, the same value — SEEK_SET falls through to
`vfs_setpos(file, offset, …)` at :185).  `none` for the
two whences past those that `lseek_spec` lets through, SEEK_DATA (3) and
SEEK_HOLE (4): real filesystems answer them with a filesystem-dependent
notion of a hole (`shmem_file_llseek`, mm/shmem.c:3669-3687, v6.18.46,
through `mapping_seek_hole_data`, mm/filemap.c:3159, v6.18.46), so they are
unmodeled rather than -EINVAL.
`len` presumes the path names a regular file
(`linux-process-semantics@ff0313ba4f:bugs/fs-paths-assumed-regular-files.md`);
the character devices never
reach this. -/
def lseek_base (whence : word) (cur len : word) : Option word :=
  if bv_unsigned whence == SEEK_SET then some (Z_to_bv 64 0)
  else if bv_unsigned whence == SEEK_CUR then some cur
  else if bv_unsigned whence == SEEK_END then some len
  else none

/-- The destination: `base` plus the SIGNED displacement (`off` is `off_t`,
read through `bv_signed`), exact in `Int` so nothing wraps.  `none` where
`vfs_setpos_cookie` (fs/read_write.c:55-69, v6.18.46) refuses: a negative
result (:58-59, -EINVAL; no filesystem here sets `FOP_UNSIGNED_OFFSET`),
or one past `LLONG_MAX` — on tmpfs the `maxsize` of the `offset > maxsize`
test (:60-61) is `MAX_LFS_FILESIZE`, `(loff_t)LLONG_MAX` on 64-bit
(include/linux/fs.h:1279, v6.18.46).  `shmem_file_llseek` (mm/shmem.c:3675-3676,
v6.18.46) passes that literal as the ceiling — not the superblock's
`s_maxbytes`, which `shmem_fill_super` (mm/shmem.c:5118, v6.18.46) also
sets to it and which tmpfs reads elsewhere (the write limit,
`generic_write_check_limits`, fs/read_write.c:1712, and the truncate
limit, `inode_newsize_ok`, fs/attr.c:254, v6.18.46) but not here — so
2^63 - 1 is the last offset it stores; a filesystem with a smaller
ceiling refuses sooner, and the model holds tmpfs's
(`linux-process-semantics@ff0313ba4f:bugs/lseek-destination-ceiling-is-tmpfs.md`).
Rocq folds
the -EOVERFLOW `ksys_lseek` would give a result above `off_t`'s range
(:404-405) into this -EINVAL; a 64-bit `off_t` never reaches it. -/
def lseek_dest (base off : word) : Option word :=
  let d := bv_unsigned base + bv_signed off
  if 0 ≤ d && d < 2 ^ 63 then some (Z_to_bv 64 d) else none

/-- `lseek fd off whence`: the fd first (-EBADF), then `whence <= SEEK_MAX`
(-EINVAL, ahead of the kind), then the kind.  -ESPIPE on a channel, a
socket and either pipe end (section header).  /dev/null is `null_lseek`'s
`return file->f_pos = 0` for every whence and offset (drivers/char/mem.c:561-564,
v6.18.46, the `.llseek` of `null_fops` at :645), SEEK_DATA and SEEK_HOLE
included, since `vfs_llseek` dispatches to it once `FMODE_LSEEK` is set;
/dev/urandom is `noop_llseek`'s `return file->f_pos` (fs/read_write.c:324-327,
v6.18.46, the `.llseek` of `urandom_fops` at drivers/char/random.c:1578), and
`f_pos` is 0 on that kind: `urandom_read_iter` never touches `ki_pos`, so
`new_sync_read` writes back the 0 it started from (fs/read_write.c:493-494,
v6.18.46)
and `pread64_spec` reads through its own position.  A tmpfs directory
seeks through `offset_dir_llseek` (fs/libfs.c:433-448, v6.18.46: SEEK_SET
and SEEK_CUR reposition its cursor, every other whence is -EINVAL) but
`FdDir` tracks no offset: unmodeled, fail closed, after the whence test.
A regular file of ANY kind — read-only, write-only, read-write or
append-mode (`shmem_file_llseek`, mm/shmem.c:3669-3687, v6.18.46, hands
SEEK_SET, SEEK_CUR and SEEK_END to `generic_file_llseek_size`,
fs/read_write.c:158-186, which reads the position and the size and
nothing about the access mode, and nothing on that path reads O_APPEND
either) moves to `lseek_dest` of
`lseek_base`, records the new offset and returns it; a negative or
unrepresentable destination is `vfs_setpos_cookie`'s -EINVAL.  Offsets
past end-of-file are legal and recorded: a later `read` there is 0 and
a later nonempty `write` zero-fills (`file_write`).

Two declines on a file, both Rocq's: SEEK_DATA/SEEK_HOLE (`lseek_base`),
and a path the file system does not hold, which `openat` makes
unreachable. -/
def lseek_spec (fd off whence : word) : Sys SyscallEffect :=
  m <- get_model ;;
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some e =>
      if SEEK_MAX < bv_unsigned whence then err_ret EINVAL
      else
        match e with
        | .FdChannel _ => err_ret ESPIPE
        | .FdSocket _ => err_ret ESPIPE
        | .FdPipe _ _ => err_ret ESPIPE
        | .FdDevNull _ _ => ret_only (Z_to_bv 64 0)
        | .FdUrandom => ret_only (Z_to_bv 64 0)
        | .FdDir => unmodeled
        | .FdFile p cur =>
            match fs_lookup (m_fs m) p with
            | none => unmodeled
            | some data =>
                match lseek_base whence cur (len_word data) with
                | none => unmodeled
                | some base =>
                    match lseek_dest base off with
                    | none => err_ret EINVAL
                    | some r =>
                        set_fds (fd_insert (m_fds m) fd (.FdFile p r)) ;;
                        ret_only r
        | .FdFileRW p cur =>
            -- the position an `lseek` sets here is the one the next read AND
            -- the next write both start from
            match fs_lookup (m_fs m) p with
            | none => unmodeled
            | some data =>
                match lseek_base whence cur (len_word data) with
                | none => unmodeled
                | some base =>
                    match lseek_dest base off with
                    | none => err_ret EINVAL
                    | some r =>
                        set_fds (fd_insert (m_fds m) fd (.FdFileRW p r)) ;;
                        ret_only r
        | .FdFileW p cur =>
            match fs_lookup (m_fs m) p with
            | none => unmodeled
            | some data =>
                match lseek_base whence cur (len_word data) with
                | none => unmodeled
                | some base =>
                    match lseek_dest base off with
                    | none => err_ret EINVAL
                    | some r =>
                        set_fds (fd_insert (m_fds m) fd (.FdFileW p r)) ;;
                        ret_only r
        | .FdFileA p cur =>
            -- NOR ON THE APPEND FLAG: nothing on the llseek path reads
            -- O_APPEND, so an append fd repositions and REPORTS exactly as
            -- the write-only fd above
            match fs_lookup (m_fs m) p with
            | none => unmodeled
            | some data =>
                match lseek_base whence cur (len_word data) with
                | none => unmodeled
                | some base =>
                    match lseek_dest base off with
                    | none => err_ret EINVAL
                    | some r =>
                        set_fds (fd_insert (m_fds m) fd (.FdFileA p r)) ;;
                        ret_only r

end LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.ReadWrite
