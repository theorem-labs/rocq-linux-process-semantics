import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.File

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Fs.Pipe — pipe2 (59)

Mirrors `theories/LinuxProcessSem/Sys/Fs/Pipe.v`, which answers to Linux
`fs/pipe.c`: it holds the spec for the one syscall defined there that
CREATES a pipe, and no other.  The pipe STATE — `State.pipe_write_room`,
`State.pipe_append`, `State.pipe_consume` and `State.pipe_end_live` in
`State/Pipes.lean`, `State.PipeBuf` itself in `State/Fd.lean`, both
re-exported by `State.lean` — lives beside the rest of the
model, because the fd-kind arms that read it are spread over the
`read`/`write`/`close`/`fsync`/`ioctl` twins, and the descriptor
allocator it borrows (`lowest_fd`) is `Sys/Fs/File.lean`'s, as in Rocq.

TRUST BOUNDARY: this file is part of the trusted specification.  Its pins
are `Checks/Cases/Fs/Pipe.lean`.

Every definition keeps the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function, and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f), every one re-read in that
tree when this file was written — and point at the Rocq definition for
the argument in full, so there is one place to correct it.  Rocq's own
line numbers for this file were already v6.18.46 and were found to agree.

THE BASELINE.  The ticket's Rocq baseline is
f44244ad6b8041aa83053d9ca91e090037ed743b.  The spec was read at
2b5fb8277f069ff156c4939cefcd9f183432abd3, where two definitions in this
spec's closure had moved since the ticket's commit — `State.FdEntry` gained
an `FdUrandom` constructor and `State.IoState` an `iost_urandom` stream (the
/dev/urandom mirror, PR #712) — and both were re-read there.  Neither is read
by anything in this file: `pipe2_spec` matches no `FdEntry` and touches no
stream, and the `State/` parts already carry both.  The header names
a71fd38a08571d519b9cfc5f66308db5c26da570 instead: PR #794 squashed the
2026-09-11 history into main as that commit, so neither f44244ad nor 2b5fb827
is an ancestor of a tree descending from main, which the parity checker
requires of a baseline.  Its tree is byte-identical to fc3d97ec, the 09-11
head; `Sys/Fs/Pipe.v` is byte-identical at all three commits; and between
2b5fb827 and a71fd38a none of the 69 Rocq definitions in this spec's closure
changes in text — the files that carry them differ only in comments
(`Sys/Fs/File.v`, `Sys/Uapi.v`) and in definitions this spec never reaches
(`State.v`'s /tmp seed and `ProcInput` constructor, `Fs.v`) — so what was
read at 2b5fb827 is what a71fd38a holds.

Two spellings differ from Rocq without changing a value: the mask test is
done on the `word` (`bv_and` with the complemented constant) where Rocq
does it on `bv_unsigned` in `Z` (`Z.ldiff`) — `pipe2_flags_mask` is below
`2^64`, so the two agree on every word — and Rocq's `Z.eqb` Bool test is
Lean's `==` on `Int`.  Rocq's `in_wmem i` is the field access `i.in_wmem`.
The `let`-bound `injected` alternative is a `let` here too. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Pipe

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.File

/-- The flag bits `__do_pipe_flags` accepts: its opening
`if (flags & ~(O_CLOEXEC | O_NONBLOCK | O_DIRECT | O_NOTIFICATION_PIPE))`
(fs/pipe.c:987-988, Linux v6.18.46, commit 1f99e9ab748f).  Everything
else is a deterministic -EINVAL, raised BEFORE the pipe is made and before
the user pointer is touched.  `O_NOTIFICATION_PIPE` is spelled `O_EXCL`
(include/uapi/linux/watch_queue.h:9, v6.18.46), which is why the fourth
summand is `O_EXCL`.  Rocq: `Pipe.pipe2_flags_mask`. -/
def pipe2_flags_mask : Int := O_CLOEXEC + O_NONBLOCK + O_DIRECT + O_EXCL

/-- pipe2's injectable failures: environment conditions the model does not
track.  -EMFILE at RLIMIT_NOFILE — `alloc_fd`'s `fd >= end` test
(fs/file.c:591-593, Linux v6.18.46, commit 1f99e9ab748f), reached through
`get_unused_fd_flags` (fs/file.c:620-623, v6.18.46) twice, so pipe2 needs TWO free
descriptors and can hit it where an `openat` would not; -ENFILE at the
system file limit — `alloc_empty_file`'s `files_stat.max_files` test
(fs/file_table.c:239-278, v6.18.46), reached from `create_pipe_files` through
`alloc_file_pseudo` (fs/file_table.c:408, v6.18.46) and `alloc_file_clone`
(fs/file_table.c:464, v6.18.46), which it calls at :944 and :956 and whose
errors it hands back at :950 and :961 — and also the errno a
failed `alloc_pipe_info` surfaces as, since `get_pipe_inode`
(fs/pipe.c:886-924, v6.18.46) returns NULL for it (:896-898, :923) and
`create_pipe_files` turns that NULL into -ENFILE (fs/pipe.c:932-933,
v6.18.46); and -ENOMEM out of growing the fd table,
`alloc_fdtable`'s `ERR_PTR(-ENOMEM)` (fs/file.c:242, v6.18.46) handed back through
`expand_files` (fs/file.c:288-320, v6.18.46) from `alloc_fd` (:595-598).  Like the
`openat` errno list, this alternative also keeps the spec receptive when
no free fd exists.  Rocq: `Pipe.pipe2_errnos`. -/
def pipe2_errnos : List Int := [EMFILE, ENFILE, ENOMEM]

/-- `pipe2 fildes flags`: make a pipe and write its two descriptors — read
end first — through `fildes`.  THE MODEL'S FIRST FD WHOSE CONTENTS COME
FROM THE PROGRAM: everything else an fd names is supplied by the
environment (a channel) or by the file system.

Kernel source for everything below is fs/pipe.c at Linux v6.18.46 (commit
1f99e9ab748f): `SYSCALL_DEFINE2(pipe2, int __user *, fildes, int, flags)`
(fs/pipe.c:1054, v6.18.46), `do_pipe2` (fs/pipe.c:1032, v6.18.46), `__do_pipe_flags`
(fs/pipe.c:982, v6.18.46), `create_pipe_files` (fs/pipe.c:926, v6.18.46), `pipe_release`
(fs/pipe.c:725, v6.18.46), and the transfer pair `anon_pipe_read` (fs/pipe.c:269, v6.18.46) and
`anon_pipe_write` (fs/pipe.c:431, v6.18.46).

THE PAIR IS NAMED `anon_pipe_*` BECAUSE THAT IS WHAT EXISTS HERE, and the
older names are a trap rather than a synonym: at v6.18.46 `pipe_read` and
`pipe_write` survive only inside three comments of fs/pipe.c (:76, :1068,
:1071), and the functions were split in two — an anonymous pair and a
FIFO pair, `fifo_pipe_read` at fs/pipe.c:407 and `fifo_pipe_write` at
:604, that wraps them with a timestamp update.  Which pair a descriptor
gets is decided by its file-operations table: `pipefifo_fops`
(fs/pipe.c:1246-1255, v6.18.46) takes the FIFO pair, `pipeanon_fops` (:1257-1266)
the anonymous one.  `create_pipe_files` installs `pipeanon_fops` on both
ends (fs/pipe.c:946, v6.18.46, :957), so every claim here and in the pipe arms it
points at is about `anon_pipe_read`/`anon_pipe_write`, never the FIFO
wrappers.

ORDER, as `do_pipe2` has it (fs/pipe.c:1032-1052, v6.18.46), walked from the
`SYSCALL_DEFINE2` down:

- FLAGS FIRST: `__do_pipe_flags` tests the mask (fs/pipe.c:987-988, v6.18.46) before
  anything else and before the user pointer is read: a bit outside
  `pipe2_flags_mask` is -EINVAL, so `pipe2(unmapped, 1)` is -EINVAL and
  never -EFAULT.  Of the four accepted bits the model interprets only
  their ABSENCE: `flags = 0` is the whole modeled surface (it is what a
  `pipe(2)` call becomes on riscv64, which has no `pipe` syscall — musl's
  src/unistd/pipe.c issues `pipe2(fd, 0)`), and any nonzero accepted
  combination is `unmodeled`.  Each of the four would need something the
  model does not have: O_CLOEXEC an execve, O_NONBLOCK the -EAGAIN
  answers this spec's whole design declines, O_DIRECT packet mode (where
  a read DISCARDS the tail of a packet it did not take), and
  O_NOTIFICATION_PIPE a kernel built with CONFIG_WATCH_QUEUE —
  `create_pipe_files` calls `watch_queue_init` for that bit
  (fs/pipe.c:935-942, v6.18.46) and the stub the option compiles out to returns
  -ENOPKG (`watch_queue_init`, include/linux/watch_queue.h:126-129,
  v6.18.46), so even the failure is configuration-dependent.
- THEN THE DESCRIPTORS: `__do_pipe_flags` takes the read end first and the
  write end second (fs/pipe.c:994-1006, v6.18.46), each the lowest free number —
  `get_unused_fd_flags` (fs/file.c:620-623, v6.18.46) is `alloc_fd` (fs/file.c:570-613, v6.18.46),
  which starts its scan of `open_fds` at the larger of `start` (0 here) and
  the table's `next_fd` hint (fs/file.c:580-582) and takes the first clear bit
  from there through `find_next_fd` (fs/file.c:544-565, v6.18.46).  The hint
  never hides a free descriptor: `__put_unused_fd` (fs/file.c:626-632,
  v6.18.46) lowers it to every descriptor that is freed, so the answer is the
  lowest free number — and `fd[0] < fd[1]`, since the write end is allocated
  with the read end already reserved: `__set_open_fd` (fs/file.c:333-340,
  v6.18.46) marks it, and `alloc_fd` calls it at fs/file.c:606 before
  returning.
- THEN THE COPY-OUT, and only then `fd_install`: `do_pipe2`'s
  `copy_to_user(fildes, fd, sizeof(fd))` (fs/pipe.c:1040, v6.18.46) precedes the two
  `fd_install`s (:1047-1048).  The eight bytes go out as ONE
  `copy_to_user` of `int fildes[2]`, so the effect is one contiguous
  range, not two.  A failed copy is -EFAULT with NOTHING installed:
  `do_pipe2` `fput`s both files and `put_unused_fd`s both reservations
  (fs/pipe.c:1041-1045, v6.18.46), so the call is atomic — the fd table is exactly as
  it was.  The model therefore answers -EFAULT and changes nothing.
  A PARTIALLY writable destination is `unmodeled` instead: the kernel
  copies a prefix before it faults, and how much depends on the
  architecture's uaccess loop, so the model will not say what is in those
  bytes.
- ONE INVERSION OF THAT ORDER, named rather than assumed away.  The term
  tests the destination's writability BEFORE it allocates, so on the
  wholly-unwritable branch it offers -EFAULT beside the injected
  `pipe2_errnos`.  Linux runs `__do_pipe_flags` first, so a task with
  fewer than two free descriptors answers -EMFILE and never attempts the
  copy — the model allows an answer that kernel would not give in that one
  state.  It is over-permissive, not unsound: -EMFILE is allowed there
  too, so no real trace is refused.  The Rocq definition says why it is
  recorded rather than restructured around.  Two more admissions of the
  same kind come with `pipe2_errnos` being an unordered alternative: the
  spec allows -EMFILE where a task at both the system file limit and
  RLIMIT_NOFILE gets -ENFILE, because `__do_pipe_flags` (fs/pipe.c:982,
  v6.18.46) calls `create_pipe_files` (fs/pipe.c:926-980, v6.18.46) at
  :990, before its first call of `get_unused_fd_flags` (fs/file.c:620-623,
  v6.18.46) at :994;
  and it allows -EMFILE on a process whose table is far below its limit,
  because the environment's failures are injectable in every state.  Both
  are over-permissive in the same way, and neither refuses a real trace.

THE `access_ok` GUARD.  `copy_to_user` IS `access_ok` AND THEN THE COPY
(`_inline_copy_to_user`, include/linux/uaccess.h:190, v6.18.46), and
`access_okb fildes 8` is the `access_ok` half.  Without it nothing bounds
`fildes` before the walk below: `State.read_bytes_map` advances with
WRAPPING `bv` addition, so a `fildes` near `2^64` walks off the top and
back in at 0, and if a memory backs both halves the walk answers `some`
and this spec would return SUCCESS on a range Linux's `access_ok`
refuses outright (`__access_ok`, include/asm-generic/access_ok.h:31-41,
v6.18.46).  `State.access_okb` compares `bv_unsigned fildes ≤ TASK_SIZE - 8`
in `Int`, where nothing wraps, and so refuses it.  Because
`do_pipe2` copies both descriptors with a single call (fs/pipe.c:1040,
v6.18.46) of `copy_to_user` (include/linux/uaccess.h:216-226, v6.18.46),
there is one `access_ok` over the whole 8 bytes rather than two `put_user`s
over 4 each; a refused range therefore copies
NOTHING, and -EFAULT with the model unchanged is Linux's answer rather
than a fail-closed stand-in.  The Rocq definition carries the shape and
the repair it shares with `socketpair`.

What a pipe costs the theorem, why a pipe is the first fd kind to cost
anything, what would close the gap, and the dropbear measurement that
makes the gap concrete are on the Rocq definition `Pipe.pipe2_spec` and
are not restated here.

`flags` arrives already truncated to 32 bits (see `Syscall.pipe_flags32`),
because pipe2's flag word is an `int`.  Rocq: `Pipe.pipe2_spec`. -/
def pipe2_spec (fildes flags : word) : Sys SyscallEffect :=
  i <- input ;;
  m <- get_model ;;
  if !(bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 pipe2_flags_mask))) == 0)
  then err_ret EINVAL          -- a bit outside the accepted mask: real -EINVAL, before
                               -- the pipe is made and before `fildes` is touched
  else if !(w_is0 flags) then unmodeled
                               -- an accepted but uninterpreted flag: fail closed
  else
    let id := pipe_new_id (m_pipes m)
    match pipe_lookup (m_pipes m) id with
    | some _ => unmodeled      -- the id-space wrapped: see `State.pipe_new_id`.
                               -- Unreachable, and fail closed rather than alias
    | none =>
        let injected : Sys SyscallEffect := (e <- errno_from pipe2_errnos ;; err_ret e)
        if !(access_okb fildes 8) then alt injected (err_ret EFAULT)
          -- `access_ok` refuses the range: -EFAULT with nothing copied and
          -- nothing installed (the guard paragraph above)
        else
          match read_bytes_map i.in_wmem fildes (Z_to_bv 64 8) with
          | some _ =>
              alt injected
                  (fdr <- lowest_fd (m_fds m) ;;          -- read end: the lowest free fd
                   let fds1 := fd_insert (m_fds m) fdr (.FdPipe id false)
                   fdw <- lowest_fd fds1 ;;               -- write end: the next lowest
                   -- THE SCAN WALL, met one descriptor early: `lowest_fd` is
                   -- empty once `State.alloc_fd`'s 4096-candidate scan finds
                   -- nothing (bugs/fd-allocation-ignores-rlimit-nofile.md), so
                   -- a table holding 0..4095 already empties THIS choice and
                   -- only the injected errnos remain, where Linux under an
                   -- RLIMIT_NOFILE of 4098 or more answers (4096, 4097).
                   set_fds (fd_insert fds1 fdw (.FdPipe id true)) ;;
                   set_pipes (pipe_insert (m_pipes m) id ([], 0)) ;;  -- an empty queue
                   Monad.pure (mkEffect (Z_to_bv 64 0) [(fildes, pipe_fd_bytes fdr fdw)] []))
          | none =>
              match read_bytes_map i.in_wmem fildes (Z_to_bv 64 1) with
              | none => alt injected (err_ret EFAULT)
                  -- the FIRST byte of the destination is unwritable, so the
                  -- kernel's first store faults and nothing lands: real
                  -- -EFAULT, with no pipe made and no descriptor installed
              | some _ => unmodeled
                  -- a writable prefix and an unwritable tail: `copy_to_user`
                  -- leaves an architecture-dependent number of bytes behind.
                  -- Fail closed

end LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Pipe
