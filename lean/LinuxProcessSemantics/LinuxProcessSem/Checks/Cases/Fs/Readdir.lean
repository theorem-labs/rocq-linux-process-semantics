-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Cases/Fs/Readdir.v
import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! # Checks.Cases.Fs.Readdir — what `getdents64` admits, read off against Linux

Worked examples over `Sys.Fs.Readdir.getdents64_spec`, the twin of
`theories/LinuxProcessSem/Checks/Cases/Fs/Readdir.v`.  Not part of the
trusted specification: this file is QA on the definitions, written to be
READ, and every claim in it is a claim about what the kernel does, with the
citation beside it — fs/readdir.c at Linux v6.18.46 (commit 1f99e9ab748f)
unless another file is named.

HOW THESE ARE STATED.  The Lean tree has no executable checker, so a check
is stated on the relation itself: an `iff` over EVERY outcome `o` pins the
positive half (what is admitted) and the negative half (nothing else is —
not another errno, not a written byte, not `Unmodeled`) in one statement,
and a refutation beside it names the concrete lie a kernel could tell.
Every proof is `sys_norm` or `sys_refute` (`Checks/Cases/Tactic.lean`).

THE ROCQ FILE SAYS ALMOST NOTHING ABOUT THIS SYSCALL, and says why: every
arm is reachable from a probe, and
`linux-process-semantics@ff0313ba4f:testing/syscall-check/tests/getdents64_spec.c` pins the arms against a
real kernel (every kind but `FdDevNull` and `FdUrandom`, which no mode of
that probe opens).  What it keeps is what a probe reads nothing about —
where the model puts the buffer-size edge, on both sides of the sign, and
that every answer leaves the model alone — and those three are here, each
pin carrying a `rocq-twin:` line naming the Rocq example it restates.  The
checker proofs of `theories/LinuxProcessSem/Checks/Sys/Fs/Readdir.v` and
the progress witness of `theories/LinuxProcessSem/Checks/Witness/Fs/Readdir.v`
belong to the `C-` and `V-` tickets, not to this file.  The rest of this
file is what the Lean tree has no probe replay for yet: one `iff` per
decision of the spec, in the order the kernel takes them, and a refutation
of each errno the arm must refuse.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Readdir

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Readdir
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude

/-! ## What `sys_norm` reads the spec with

The spec and its errno list enter the `sys_simp` set here, at the low
priority `Checks/Cases/Tactic.lean` gives every unfolding; the gates
(`getdents64_no_room`) are decided, never unfolded, so they are not
registered.  Every ported spec registers itself from its Cases file this
way; this port does not edit `Tactic.lean`. -/

attribute [sys_simp low] getdents64_spec.eq_1 getdents64_errnos.eq_1

/-! ## The fixture

fd 3 is an O_RDONLY file parked at offset 7, fd 4 an O_WRONLY one at offset
9, fd 5 the directory — the Rocq `getdents64_model` — and then fds 6 to 9,
one per further constructor the spec's `match` has an arm for: a pipe read
end, a fresh socket, /dev/null opened for reading, and /dev/urandom.  The
`iff`s below return this model itself; the inertness refutations forge a
model whose fd table was emptied and require the spec to refuse it. -/

def readdir_fds : List (word × FdEntry) :=
  [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
    (3, .FdFile [Z_to_bv 8 102] 7), (4, .FdFileW [Z_to_bv 8 103] 9), (5, .FdDir),
    (6, .FdPipe 0 false), (7, .FdSocket .SkFresh), (8, .FdDevNull true false),
    (9, .FdUrandom) ]

def readdir_fs : Fs.Fs :=
  [ ([Z_to_bv 8 102], [Z_to_bv 8 120]), ([Z_to_bv 8 103], [Z_to_bv 8 121]) ]

/-- The process the checks run on.  Kept opaque to the normal form: no arm
of the spec reads anything of it but the fd table, and the table is read
through the lookups below. -/
def readdir_model : Model := fixture_of (fds := readdir_fds) (fs := readdir_fs)

/-! ### The fd table read at each fd a check names

So that the spec's `match` is decided in the FIRST pass of `sys_norm`: left
to the second, `+ground` pass, the closed `errno_from` under the directory
arm is evaluated to its `choose` before `bind_errno_from_iff` sees it, and
a refutation of a return outside the errno list is left open (the two-pass
note in `Checks/Cases/Tactic.lean`; `dir_fd_no_room_success_rejected` below
is the pin that measured it here).

They are stated on `readdir_model.m_fd.fdst_table`, the projection chain,
and not on `m_fds readdir_model`.  In a match discriminant the first pass
rewrites `m_fds readdir_model` to that chain — `m_fds.eq_1` is a `rfl`
lemma and applies there before any lemma on the parent is tried (Lean
v4.34.0) — so a lookup stated on `m_fds readdir_model` never sees its
redex, while at an ordinary node a projection lemma on `m_fds readdir_model`
wins as `Tactic.lean`'s priority contract says.  The shape a pass produces
is what a rewrite has to match. -/

/-- fd 0, a channel.
model: the fixture's fd table read at one fd, a rewrite for the normal form. -/
@[sys_simp] theorem fd_lookup_readdir_0 :
    fd_lookup readdir_model.m_fd.fdst_table 0 = some (.FdChannel 0) := rfl
/-- fd 3, the O_RDONLY file.
model: the fixture's fd table read at one fd, a rewrite for the normal form. -/
@[sys_simp] theorem fd_lookup_readdir_3 :
    fd_lookup readdir_model.m_fd.fdst_table 3 = some (.FdFile [Z_to_bv 8 102] 7) := rfl
/-- fd 4, the O_WRONLY file.
model: the fixture's fd table read at one fd, a rewrite for the normal form. -/
@[sys_simp] theorem fd_lookup_readdir_4 :
    fd_lookup readdir_model.m_fd.fdst_table 4 = some (.FdFileW [Z_to_bv 8 103] 9) := rfl
/-- fd 5, the directory.
model: the fixture's fd table read at one fd, a rewrite for the normal form. -/
@[sys_simp] theorem fd_lookup_readdir_5 :
    fd_lookup readdir_model.m_fd.fdst_table 5 = some .FdDir := rfl
/-- fd 6, the pipe read end.
model: the fixture's fd table read at one fd, a rewrite for the normal form. -/
@[sys_simp] theorem fd_lookup_readdir_6 :
    fd_lookup readdir_model.m_fd.fdst_table 6 = some (.FdPipe 0 false) := rfl
/-- fd 7, the fresh socket.
model: the fixture's fd table read at one fd, a rewrite for the normal form. -/
@[sys_simp] theorem fd_lookup_readdir_7 :
    fd_lookup readdir_model.m_fd.fdst_table 7 = some (.FdSocket .SkFresh) := rfl
/-- fd 8, /dev/null.
model: the fixture's fd table read at one fd, a rewrite for the normal form. -/
@[sys_simp] theorem fd_lookup_readdir_8 :
    fd_lookup readdir_model.m_fd.fdst_table 8 = some (.FdDevNull true false) := rfl
/-- fd 9, /dev/urandom.
model: the fixture's fd table read at one fd, a rewrite for the normal form. -/
@[sys_simp] theorem fd_lookup_readdir_9 :
    fd_lookup readdir_model.m_fd.fdst_table 9 = some .FdUrandom := rfl
/-- fd 99, not open.
model: the fixture's fd table read at one fd, a rewrite for the normal form. -/
@[sys_simp] theorem fd_lookup_readdir_99 :
    fd_lookup readdir_model.m_fd.fdst_table 99 = none := rfl

/-! ## The constants, pinned to the headers

`dirent64_min_reclen` is 24 because `offsetof(struct linux_dirent64, d_name)`
is 19 — `u64`, `s64`, `unsigned short`, `unsigned char`
(include/linux/dirent.h:5-11, Linux v6.18.46) — plus the one-byte name "."
and its NUL, aligned to `sizeof(u64)` by `filldir64` (fs/readdir.c:355-356). -/

/-- 24 is the aligned record of "." (`filldir64`'s `reclen`), and equally the
floor `ALIGN(20 + namlen, 8)` takes over every `namlen` in 0..4; what
`verify_dirent_name` refusing `len <= 0` rules out is a negative `namlen`,
whose `size_t` arithmetic would wrap `reclen` below 24, and whose `-EIO`
(fs/readdir.c:363-365) no admitted arm can reach because the first name
emitted is ".".
kernel: fs/readdir.c:filldir64,verify_dirent_name@v6.18.46 -/
example : dirent64_min_reclen = 24 := by decide
/-- …and it is `ALIGN(19 + 1 + 1, 8)`: the `d_name` offset — `u64`, `s64`,
`unsigned short`, `unsigned char`, include/linux/dirent.h:5-11 — the byte, its NUL.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
example : (19 + 1 + 1 + 7) / 8 * 8 = dirent64_min_reclen := by decide
/-- The one injected failure is `iterate_dir`'s `-ENOENT` for a removed directory.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
example : getdents64_errnos = [ENOENT] := by decide

/-! ## `fd_empty` first: `-EBADF` on a closed fd

`SYSCALL_DEFINE3(getdents64)` (fs/readdir.c:409-410, Linux v6.18.46) returns
`-EBADF` when `fd_empty(f)`, before `iterate_dir` is entered, so neither the kind test
nor the buffer-size test is reached. -/

/-- A closed fd is `-EBADF` whatever the count: here count 0, which the
directory arm would answer `-EINVAL` one step later.  The `iff` refuses
that `-EINVAL` and every other answer.
kernel: fs/readdir.c:getdents64@v6.18.46 -/
theorem closed_fd_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    getdents64_spec 99 0 i readdir_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) readdir_model [] := by
  sys_norm

/-- …so a kernel answering `-EINVAL` on a closed fd — as one that tested
the count before the fd would — is lying.
kernel: fs/readdir.c:getdents64@v6.18.46 -/
theorem closed_fd_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ getdents64_spec 99 0 i readdir_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and the count is not a gate in front of the fd either: at 4096, where
the DIRECTORY arm has room and declines, a closed fd is still `-EBADF`.
`fd_empty` (include/linux/file.h:45, Linux v6.18.46), which fs/readdir.c:409-410
tests, returns before `iterate_dir` is entered, and every look at the buffer
size lives inside it, so the fd decides the
answer whether or not the buffer has room.  Without this pin every `-EBADF`
statement in the file stands at a count with NO room, and a spec that
tested the count FIRST and declined every call with room would satisfy all
of them.
kernel: fs/readdir.c:getdents64@v6.18.46 -/
theorem closed_fd_with_room_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    getdents64_spec 99 4096 i readdir_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) readdir_model [] := by
  sys_norm

/-! ## `iterate_dir`'s first statement: `-ENOTDIR` on every non-directory

`iterate_dir` (fs/readdir.c:88-91, Linux v6.18.46) opens with `int res =
-ENOTDIR; if (!file->f_op->iterate_shared) goto out;`.  No `file_operations`
table of a non-directory object defines `.iterate_shared` — `pipefifo_fops` and
`pipeanon_fops` (fs/pipe.c, Linux v6.18.46), `socket_file_ops` (net/socket.c),
`ext4_file_operations` (fs/ext4/file.c), `shmem_file_operations`
(mm/shmem.c), `null_fops` (drivers/char/mem.c), `urandom_fops`
(drivers/char/random.c), `tty_fops` (drivers/tty/tty_io.c), all at Linux
v6.18.46 — so each kind below is
`-ENOTDIR`, and with count 0 in every case, so that the `-EINVAL` a
directory would answer is what the `iff` refuses. -/

/-- fd 0, a channel: whatever object the launch put there, `iterate_dir`
tests for `.iterate_shared` and nothing else, so a pipe, a tty, a socket,
/dev/null and a regular file behind a redirection are `-ENOTDIR` alike.
THE ONE OBJECT THAT IS NOT is a directory, which `prog < /some/dir` puts on
fd 0 — `may_open` refuses a directory only for MAY_WRITE and MAY_EXEC —
and there this arm answers `-ENOTDIR` where Linux lists.  So the `iff` pins
the model's premise, not a theorem about Linux: `State.ProcInput` carries
no fd table, so nothing the model holds says what a channel names, and
linux-process-semantics@ff0313ba4f:bugs/getdents64-channel-fd-assumed-not-a-directory.md records the premise.
kernel: fs/readdir.c:iterate_dir; fs/namei.c:may_open@v6.18.46 -/
theorem channel_fd_is_enotdir (i : SyscallInput) (o : outcome SyscallEffect) :
    getdents64_spec 0 0 i readdir_model o ↔
      o = Ok (mkEffect (errno_ret ENOTDIR) [] []) readdir_model [] := by
  sys_norm

/-- fd 3, a regular file opened O_RDONLY (`ext4_file_operations`,
`shmem_file_operations`).
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem file_fd_is_enotdir (i : SyscallInput) (o : outcome SyscallEffect) :
    getdents64_spec 3 0 i readdir_model o ↔
      o = Ok (mkEffect (errno_ret ENOTDIR) [] []) readdir_model [] := by
  sys_norm

/-- fd 4, the same kind of file opened O_WRONLY: the access mode changes
what `read` and `write` answer, not which `file_operations` the inode has.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem wronly_file_fd_is_enotdir (i : SyscallInput) (o : outcome SyscallEffect) :
    getdents64_spec 4 0 i readdir_model o ↔
      o = Ok (mkEffect (errno_ret ENOTDIR) [] []) readdir_model [] := by
  sys_norm

/-- fd 6, a pipe read end (`pipefifo_fops`, `pipeanon_fops`).
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem pipe_fd_is_enotdir (i : SyscallInput) (o : outcome SyscallEffect) :
    getdents64_spec 6 0 i readdir_model o ↔
      o = Ok (mkEffect (errno_ret ENOTDIR) [] []) readdir_model [] := by
  sys_norm

/-- fd 7, a socket (`socket_file_ops`).
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem socket_fd_is_enotdir (i : SyscallInput) (o : outcome SyscallEffect) :
    getdents64_spec 7 0 i readdir_model o ↔
      o = Ok (mkEffect (errno_ret ENOTDIR) [] []) readdir_model [] := by
  sys_norm

/-- fd 8, /dev/null (`null_fops`).
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem devnull_fd_is_enotdir (i : SyscallInput) (o : outcome SyscallEffect) :
    getdents64_spec 8 0 i readdir_model o ↔
      o = Ok (mkEffect (errno_ret ENOTDIR) [] []) readdir_model [] := by
  sys_norm

/-- fd 9, /dev/urandom (`urandom_fops`, drivers/char/random.c: no `.iterate_shared`
either, so the same first statement of `iterate_dir` answers).
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem urandom_fd_is_enotdir (i : SyscallInput) (o : outcome SyscallEffect) :
    getdents64_spec 9 0 i readdir_model o ↔
      o = Ok (mkEffect (errno_ret ENOTDIR) [] []) readdir_model [] := by
  sys_norm

/-- The count is not consulted on a non-directory: a kernel answering
`-EINVAL` to `getdents64(3, buf, 0)` would have reached `filldir64`
(fs/readdir.c:366-368) on an fd whose `f_op` has no iterator to call it.
kernel: fs/readdir.c:iterate_dir,filldir64@v6.18.46 -/
theorem file_fd_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ getdents64_spec 3 0 i readdir_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and the count is not a gate in front of the KIND test: at 4096 a
regular file fd is `-ENOTDIR`, not a decline.  `iterate_dir`'s
`.iterate_shared` test (fs/readdir.c:88-91) precedes `filldir64` entirely,
so a buffer with room changes nothing on a non-directory — the pair to
`file_fd_einval_rejected`, which pins the same order from the other side.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem file_fd_with_room_is_enotdir (i : SyscallInput) (o : outcome SyscallEffect) :
    getdents64_spec 3 4096 i readdir_model o ↔
      o = Ok (mkEffect (errno_ret ENOTDIR) [] []) readdir_model [] := by
  sys_norm

/-- …and the same for every other non-directory kind, so the count gates
none of them: `iterate_dir`'s `.iterate_shared` test (fs/readdir.c:88-91)
is the whole of the answer on each, and a buffer with room does not reach
`filldir64`.  One `iff` per kind, at 4096, is what stops a port that gated
a single arm on the size — a mutation the operator set cannot express,
since the arms carry no comparison to perturb.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem channel_fd_with_room_is_enotdir (i : SyscallInput) (o : outcome SyscallEffect) :
    getdents64_spec 0 4096 i readdir_model o ↔
      o = Ok (mkEffect (errno_ret ENOTDIR) [] []) readdir_model [] := by
  sys_norm

/-- fd 4, the O_WRONLY file, with room.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem wronly_file_fd_with_room_is_enotdir (i : SyscallInput) (o : outcome SyscallEffect) :
    getdents64_spec 4 4096 i readdir_model o ↔
      o = Ok (mkEffect (errno_ret ENOTDIR) [] []) readdir_model [] := by
  sys_norm

/-- fd 6, the pipe read end, with room.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem pipe_fd_with_room_is_enotdir (i : SyscallInput) (o : outcome SyscallEffect) :
    getdents64_spec 6 4096 i readdir_model o ↔
      o = Ok (mkEffect (errno_ret ENOTDIR) [] []) readdir_model [] := by
  sys_norm

/-- fd 7, the socket, with room.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem socket_fd_with_room_is_enotdir (i : SyscallInput) (o : outcome SyscallEffect) :
    getdents64_spec 7 4096 i readdir_model o ↔
      o = Ok (mkEffect (errno_ret ENOTDIR) [] []) readdir_model [] := by
  sys_norm

/-- fd 8, /dev/null, with room.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem devnull_fd_with_room_is_enotdir (i : SyscallInput) (o : outcome SyscallEffect) :
    getdents64_spec 8 4096 i readdir_model o ↔
      o = Ok (mkEffect (errno_ret ENOTDIR) [] []) readdir_model [] := by
  sys_norm

/-- fd 9, /dev/urandom, with room.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem urandom_fd_with_room_is_enotdir (i : SyscallInput) (o : outcome SyscallEffect) :
    getdents64_spec 9 4096 i readdir_model o ↔
      o = Ok (mkEffect (errno_ret ENOTDIR) [] []) readdir_model [] := by
  sys_norm

/-- fd 4: `-EBADF` is what an O_WRONLY fd gets from `read` — `vfs_read`'s
`!(file->f_mode & FMODE_READ)` (fs/read_write.c:556-557) — and it is not
what refuses this call: `fdget_pos` tests no access mode, and `iterate_dir`
(fs/readdir.c:88-91) refuses on the `f_op` alone.
kernel: fs/readdir.c:iterate_dir; fs/read_write.c:vfs_read@v6.18.46 -/
theorem wronly_file_fd_ebadf_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ getdents64_spec 4 0 i readdir_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- fd 6: a pipe end that "listed".  `pipefifo_fops` has no `.iterate_shared`,
so `iterate_dir` (fs/readdir.c:88-91) never reaches an iterator that could
have returned 0 — the probe's `ret=0 -- pipe` mutation, stated here.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem pipe_fd_listing_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ getdents64_spec 6 0 i readdir_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- fd 7: `-ENOTSOCK` is what the SOCKET calls answer on an fd that is not a
socket (`sockfd_lookup`, net/socket.c:565); nothing on `getdents64`'s path
calls it, and a socket fd here is `-ENOTDIR` like every other non-directory.
kernel: fs/readdir.c:iterate_dir; net/socket.c:sockfd_lookup@v6.18.46 -/
theorem socket_fd_enotsock_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ getdents64_spec 7 0 i readdir_model (Ok (mkEffect (errno_ret ENOTSOCK) [] []) m' evs) := by
  sys_refute

/-- fd 8: /dev/null reads as end-of-file — `read_null` returns 0
(drivers/char/mem.c:412-416) — so a 0 "empty listing" is the lie this kind
invites; `null_fops` defines no `.iterate_shared`, so `iterate_dir` never
reaches an iterator that could have returned it.
kernel: fs/readdir.c:iterate_dir; drivers/char/mem.c:read_null@v6.18.46 -/
theorem devnull_fd_listing_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ getdents64_spec 8 0 i readdir_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- fd 9: /dev/urandom is the kind whose read never comes back short —
`urandom_read_iter` (drivers/char/random.c:1453) fills the whole request —
so the lie this kind invites is a FILLED record rather than an empty
listing: a 24-byte return, the size of the one entry a minimal buffer
holds.  `iterate_dir` has no iterator to have written it.
kernel: fs/readdir.c:iterate_dir; drivers/char/random.c:urandom_read_iter@v6.18.46 -/
theorem urandom_fd_listing_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ getdents64_spec 9 0 i readdir_model (Ok (mkEffect 24 [] []) m' evs) := by
  sys_refute

/-- The injectable `-ENOENT` belongs to the directory arm alone: it is
`iterate_dir`'s `IS_DEADDIR` answer (fs/readdir.c:105-106), which sits
BEHIND the `.iterate_shared` test, so no non-directory reaches it.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem file_fd_enoent_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ getdents64_spec 3 0 i readdir_model (Ok (mkEffect (errno_ret ENOENT) [] []) m' evs) := by
  sys_refute

/-- …and a listing of a channel, even an empty one, is a lie: `iterate_dir`
(fs/readdir.c:88-91) never returns 0 without an iterator to have run.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem channel_fd_listing_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ getdents64_spec 0 0 i readdir_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-! ## `filldir64`'s `-EINVAL`, and the removed directory's `-ENOENT`

On a directory fd with a buffer too small for any entry, two answers and
only two: `-ENOENT` from `iterate_dir` (fs/readdir.c:105-106, Linux v6.18.46)
when the directory was removed after the open, else `-EINVAL` from `filldir64`
(fs/readdir.c:366-368, Linux v6.18.46) on `reclen > ctx->count`.  Which one
reaches userspace is decided by `if (error >= 0) error = buf.error;`
(fs/readdir.c:413-414, Linux v6.18.46): `iterate_dir` returns 0 on the live
directory so `buf.error` wins, and `-ENOENT` on the removed one so it does not
— `buf` is designated-initialized (fs/readdir.c:401-406, Linux v6.18.46),
leaving `buf.error` 0
there.  `buf.prev_reclen` is still 0 either way, so the
`count - buf.ctx.count` rewrite is skipped.  Two more answers Linux can
give here are refused on purpose, and pinned as refusals below: the
`-EACCES` of an enforcing LSM and the `-EPERM` of a `FAN_DENY` listener
(linux-process-semantics@ff0313ba4f:bugs/getdents64-lsm-and-fanotify-denials-not-admitted.md). -/

/-- `getdents64(dirfd, buf, 0)`: the two admitted answers, in the order
the kernel would reach them, and nothing else — no success, no write, no
event, no `Unmodeled`.
kernel: fs/readdir.c:iterate_dir,filldir64@v6.18.46 -/
theorem dir_fd_no_room_is_enoent_or_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    getdents64_spec 5 0 i readdir_model o ↔
      (o = Ok (mkEffect (errno_ret ENOENT) [] []) readdir_model []
       ∨ o = Ok (mkEffect (errno_ret EINVAL) [] []) readdir_model []) := by
  sys_norm

/-- A directory read to nothing is not what count 0 means: the iteration
at position 0 emits "." first (`dir_emit_dots`, include/linux/fs.h:4028-4031,
Linux v6.18.46), so a 0 return would need a filesystem whose readdir emits
nothing at position 0 — which neither tmpfs nor sysfs is, and a `subset=pid`
procfs is (`proc_readdir`, fs/proc/generic.c:335-336; the spec header names
that bound and linux-process-semantics@ff0313ba4f:bugs/getdents64-position-zero-premise-excludes-pidonly-procfs.md
records it) — or an `FdDir` past position 0, which the spec header argues
no modeled run holds.  Both halves of that premise are the spec's, not this
pin's: give `FdDir` a position and this refutation has to be re-read.
kernel: fs/readdir.c:filldir64; include/linux/fs.h:dir_emit_dots@v6.18.46 -/
theorem dir_fd_no_room_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ getdents64_spec 5 0 i readdir_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- No `-EFAULT` on the size refusal: `filldir64` reaches
`user_write_access_begin` (include/linux/uaccess.h:569, Linux v6.18.46) — the
call is fs/readdir.c:374 — only after the `reclen > ctx->count` test
(fs/readdir.c:367, Linux v6.18.46) has passed, so the buffer pointer is never
dereferenced on this arm.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
theorem dir_fd_no_room_efault_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ getdents64_spec 5 0 i readdir_model (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- Nothing is written: `filldir64` returns false on the size test before
its first `unsafe_put_user` (fs/readdir.c:367-368 against :378-382), so a
record smuggled into the effect beside the errno is refused.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
theorem dir_fd_no_room_write_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ getdents64_spec 5 0 i readdir_model
        (Ok (mkEffect (errno_ret EINVAL) [(4096, [Z_to_bv 8 0])] []) m' evs) := by
  sys_refute

/-- …and no event: no channel is read or written on any arm.
kernel: fs/readdir.c:getdents64,filldir64@v6.18.46 -/
theorem dir_fd_no_room_event_rejected (i : SyscallInput) (m' : Model) :
    ¬ getdents64_spec 5 0 i readdir_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' [WriteEv 1 (Z_to_bv 8 65)]) := by
  sys_refute

/-- `-EACCES` is a REAL answer this arm refuses: an enforcing LSM gives it
through `security_file_permission` (security/security.c:2944, Linux v6.18.46),
which fs/readdir.c:93 calls, between the `-ENOTDIR` and the `-EINVAL`.  linux-process-semantics@ff0313ba4f:bugs/getdents64-lsm-and-fanotify-denials-not-admitted.md
records the refusal as a narrowing kept on purpose, and this statement is
its Lean falsifier: the day `getdents64_errnos` gains the errno, it stops
closing and that entry is out of date.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem dir_fd_no_room_eacces_refused (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ getdents64_spec 5 0 i readdir_model (Ok (mkEffect (errno_ret EACCES) [] []) m' evs) := by
  sys_refute

/-- …and `-EPERM`, the `FAN_DENY` answer of `fsnotify_file_perm`
(include/linux/fsnotify.h:204, Linux v6.18.46), which fs/readdir.c:97 calls, is
refused the same way and for the same reason.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem dir_fd_no_room_eperm_refused (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ getdents64_spec 5 0 i readdir_model (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  sys_refute

/-! ## Every answer is inert

The Rocq `getdents64_answers_are_inert`.  A probe sees only the errno; that
the fd table came back UNCHANGED — the two offsets, the directory, the
channels — is a statement about the model's own state.  The `iff`s above
already say the returned model is `readdir_model` itself; what is added
here is the refutation of the one alternative a wrong port could produce,
a model with the table rewritten, on each of the three arms. -/

/-- `-EBADF` from `fd_empty` runs no code that reaches the table: a rewritten table is refused.
kernel: fs/readdir.c:getdents64@v6.18.46
rocq-twin: getdents64_answers_are_inert -/
theorem closed_fd_answer_is_inert (i : SyscallInput) :
    ¬ getdents64_spec 99 0 i readdir_model
        (Ok (mkEffect (errno_ret EBADF) [] []) (with_fds [] readdir_model) []) := by
  sys_refute

/-- `-ENOTDIR` from `iterate_dir`'s first statement touches no state: a rewritten table is refused.
kernel: fs/readdir.c:getdents64,iterate_dir@v6.18.46
rocq-twin: getdents64_answers_are_inert -/
theorem file_fd_answer_is_inert (i : SyscallInput) :
    ¬ getdents64_spec 3 0 i readdir_model
        (Ok (mkEffect (errno_ret ENOTDIR) [] []) (with_fds [] readdir_model) []) := by
  sys_refute

/-- `filldir64`'s size refusal writes nothing, `dir_emit_dots` leaves `ctx->pos` at 0 when the
first emit fails, and `iterate_dir` writes that 0 back to `f_pos`: a rewritten table is refused.
kernel: fs/readdir.c:getdents64,iterate_dir,filldir64; include/linux/fs.h:dir_emit_dots@v6.18.46
rocq-twin: getdents64_answers_are_inert -/
theorem dir_fd_answer_is_inert (i : SyscallInput) :
    ¬ getdents64_spec 5 0 i readdir_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) (with_fds [] readdir_model) []) := by
  sys_refute

/-! ## Where the buffer-size edge is

The Rocq `getdents64_edge_is_the_minimum_reclen`.  A probe learns that the
kernel said `-EINVAL` at some count and listed the directory at some larger
one; it never learns where the MODEL puts the boundary, and a spec whose
edge sat one byte either side would pass every probe case that lands clear
of it.  `reclen` for "." is `ALIGN(19 + 1 + 1, 8) = 24` (`filldir64`,
fs/readdir.c:355-356, Linux v6.18.46), so `reclen > ctx->count`
(fs/readdir.c:367, Linux v6.18.46) holds at 23 and fails at 24. -/

/-- 23 is answered: `-EINVAL`, or the removed directory's `-ENOENT`.
kernel: fs/readdir.c:iterate_dir,filldir64@v6.18.46
rocq-twin: getdents64_edge_is_the_minimum_reclen -/
theorem count_23_is_enoent_or_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    getdents64_spec 5 23 i readdir_model o ↔
      (o = Ok (mkEffect (errno_ret ENOENT) [] []) readdir_model []
       ∨ o = Ok (mkEffect (errno_ret EINVAL) [] []) readdir_model []) := by
  sys_norm

/-- 24 has room for ".", so Linux lists the directory — and the model
declines, because the listing is not derivable from what it carries: a
nullary `FdDir`, a file system with no `d_ino`, `d_off` or `d_type`, and a
key set that is not the directory (the Rocq `getdents64_spec` header).
Both supported implementations answer here; the model says `Unmodeled`
rather than invent what they answer.
kernel: fs/readdir.c:filldir64@v6.18.46
rocq-twin: getdents64_edge_is_the_minimum_reclen -/
theorem count_24_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    getdents64_spec 5 24 i readdir_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and 23 admits the errno rather than any return.
kernel: fs/readdir.c:filldir64; include/linux/fs.h:dir_emit_dots@v6.18.46
rocq-twin: getdents64_edge_is_the_minimum_reclen -/
theorem count_23_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ getdents64_spec 5 23 i readdir_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- …while 24 declines the very errno 23 admits, so the decline is the
COUNT's doing and not the effect's.
kernel: fs/readdir.c:filldir64@v6.18.46
rocq-twin: getdents64_edge_is_the_minimum_reclen -/
theorem count_24_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ getdents64_spec 5 24 i readdir_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and declines the 24-byte return the kernel really gives for ".",
because declining is not admitting.
kernel: fs/readdir.c:getdents64,filldir64@v6.18.46
rocq-twin: getdents64_edge_is_the_minimum_reclen -/
theorem count_24_listing_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ getdents64_spec 5 24 i readdir_model (Ok (mkEffect 24 [] []) m' evs) := by
  sys_refute

/-! ## The same edge, on the other side of the sign

The Rocq `getdents64_count_is_a_signed_int`.  `count` is `unsigned int` at
the prototype (`SYSCALL_DEFINE3(getdents64)`, fs/readdir.c:397-398) and
`int` in `dir_context` (include/linux/fs.h:2210, Linux v6.18.46), where
`filldir64` compares it (fs/readdir.c:367).  2^31 - 1 is the largest
positive `ctx->count`, and has room; 2^31 is the smallest negative one,
and has none.  A model comparing the unsigned low half would have declined
BOTH. -/

/-- INT_MAX has room: the listing, declined for the reasons
`count_24_is_unmodeled` gives.
kernel: fs/readdir.c:getdents64,filldir64@v6.18.46
rocq-twin: getdents64_count_is_a_signed_int -/
theorem count_int_max_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    getdents64_spec 5 (Z_to_bv 64 (2 ^ 31 - 1)) i readdir_model o ↔ o = Unmodeled := by
  sys_norm

/-- 0x80000000 is INT_MIN as `ctx->count`: `reclen > ctx->count` holds for
every `reclen`, so `-EINVAL` — the answer that carries the signed reading.
kernel: fs/readdir.c:getdents64,iterate_dir,filldir64@v6.18.46
rocq-twin: getdents64_count_is_a_signed_int -/
theorem count_2_pow_31_is_enoent_or_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    getdents64_spec 5 (Z_to_bv 64 (2 ^ 31)) i readdir_model o ↔
      (o = Ok (mkEffect (errno_ret ENOENT) [] []) readdir_model []
       ∨ o = Ok (mkEffect (errno_ret EINVAL) [] []) readdir_model []) := by
  sys_norm

/-- UINT_MAX is -1 as `ctx->count`: no room either.
kernel: fs/readdir.c:getdents64,iterate_dir,filldir64@v6.18.46
rocq-twin: getdents64_count_is_a_signed_int -/
theorem count_uint_max_is_enoent_or_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    getdents64_spec 5 (Z_to_bv 64 (2 ^ 32 - 1)) i readdir_model o ↔
      (o = Ok (mkEffect (errno_ret ENOENT) [] []) readdir_model []
       ∨ o = Ok (mkEffect (errno_ret EINVAL) [] []) readdir_model []) := by
  sys_norm

/-- The high half of the register is discarded first (`unsigned int
count` at the prototype), so 2^32 + 24 is 24 again and has room.
kernel: fs/readdir.c:getdents64,filldir64@v6.18.46
rocq-twin: getdents64_count_is_a_signed_int -/
theorem count_2_pow_32_plus_24_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    getdents64_spec 5 (Z_to_bv 64 (2 ^ 32 + 24)) i readdir_model o ↔ o = Unmodeled := by
  sys_norm

/-- 0 is "the directory is exhausted", which a buffer the kernel refused to
write into never establishes: `filldir64` returns false on
`reclen > ctx->count` (fs/readdir.c:367-368) before it emits anything, and
`SYSCALL_DEFINE3(getdents64)` then reports `buf.error` rather than a byte
count (fs/readdir.c:413-415).  This is the kernel lie the probe's
`ret=0 -- neg` mutation forces; it is NOT what separates the readings of
`count`, since this spec has no success arm at any count and refuses a 0
return under an unsigned reading too.  `count_2_pow_31_is_enoent_or_einval`
is the statement that carries that.
kernel: fs/readdir.c:getdents64,filldir64@v6.18.46 -/
theorem count_2_pow_31_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ getdents64_spec 5 (Z_to_bv 64 (2 ^ 31)) i readdir_model (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- The two pins above answer `-EINVAL` at 2^31 and at 2^32 - 1; this one
says the model is not simply answering `-EINVAL` to every large count.
2^32 + 24 is a LARGER register value than 2^32 - 1 and yet has room, which
no monotone reading of the whole register can produce, so the pair is where
the truncation to `unsigned int` (fs/readdir.c:397-398) becomes observable.
What this does NOT refuse is a whole-register SIGNED reading: 2^32 + 24 is
4294967320, positive and above 24 as an `sint64` too, so such a model
declines here exactly as this spec does.  The pins that catch that one are
`count_2_pow_31_is_enoent_or_einval` and `count_uint_max_is_enoent_or_einval`,
where every reading of the whole register finds room and the kernel answers
the errno.
kernel: fs/readdir.c:getdents64,filldir64@v6.18.46
rocq-twin: getdents64_count_is_a_signed_int -/
theorem count_2_pow_32_plus_24_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ getdents64_spec 5 (Z_to_bv 64 (2 ^ 32 + 24)) i readdir_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-! ## Through the table: syscall 61, the fd's truncation, and which register is the count

The table line is `getdents64_spec (fd32 a0) a2`: `fd` is `unsigned int`
at the prototype (fs/readdir.c:397, Linux v6.18.46), so `fd32` drops its high
half, and
`count` is the THIRD argument, `dirent` the second.  The pointer is not an
argument of the spec, so no pin here can constrain what the model does with
it; a1 is 0 — a NULL buffer — so that a table line reading `a1` as the
count would answer `-EINVAL` where these say `Unmodeled`, which is the one
thing the choice of a1 CAN pin.  That `getdents64(dirfd, NULL, 0)` is
`-EINVAL` and never `-EFAULT` is the spec's claim about the kernel
(`filldir64` tests the size before `user_write_access_begin`), stated on
the `-EFAULT` refutation below; the a1 these inputs carry does not test it,
because the spec never reads a1. -/

/-- One `getdents64` call: fd in a0, a NULL buffer in a1, the count in a2.
The Rocq `getdents64_in` parks the buffer at 4096 instead; nothing reads it
either way, and 0 is the value that tells a1 from a2 above. -/
def getdents64_in (fd count : word) : SyscallInput :=
  SyscallInput.mkInput 61 [fd, 0, count, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- The input read back: the number.
model: a projection of the closed input `getdents64_in`, a rewrite for the normal form. -/
@[sys_simp] theorem in_sysno_getdents64_in (fd count : word) :
    (getdents64_in fd count).in_sysno = 61 := rfl
/-- The input read back: a0, the fd.
model: a projection of the closed input `getdents64_in`, a rewrite for the normal form. -/
@[sys_simp] theorem in_arg_getdents64_in_0 (fd count : word) :
    in_arg (getdents64_in fd count) 0 = fd := rfl
/-- The input read back: a2, the count.
model: a projection of the closed input `getdents64_in`, a rewrite for the normal form. -/
@[sys_simp] theorem in_arg_getdents64_in_2 (fd count : word) :
    in_arg (getdents64_in fd count) 2 = count := rfl

/-- `fd32` at the fds the table pins name: the identity below 2^32, and 0
at 2^32 (`Syscall.fd32`'s note: the `unsigned int` of the prototype).
model: `Syscall.fd32` at a numeral, a rewrite for the normal form. -/
@[sys_simp] theorem fd32_5 : fd32 5 = 5 := by decide
/-- `fd32` at 99: the identity below 2^32.
model: `Syscall.fd32` at a numeral, a rewrite for the normal form. -/
@[sys_simp] theorem fd32_99 : fd32 99 = 99 := by decide
/-- `fd32` at 2^32: the high word gone, 0.
model: `Syscall.fd32` at a numeral, a rewrite for the normal form. -/
@[sys_simp] theorem fd32_2_pow_32 : fd32 (Z_to_bv 64 (2 ^ 32)) = 0 := by decide

/-- Syscall 61 reaches the arm: `getdents64(99, NULL, 0)` is `-EBADF`
(fs/readdir.c:409-410).
kernel: fs/readdir.c:getdents64@v6.18.46 -/
theorem sysno_61_closed_fd_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (getdents64_in 99 0) readdir_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) readdir_model [] := by
  sys_norm

/-- `getdents64(2^32, NULL, 0)` names fd 0: `fd` is `unsigned int`
(fs/readdir.c:397), so the register's high word is gone before `fdget_pos`
reads it, and fd 0 is a channel — `-ENOTDIR`, not the `-EBADF` a 64-bit
reading of the register would give.
kernel: fs/readdir.c:getdents64,iterate_dir@v6.18.46 -/
theorem sysno_61_fd_2_pow_32_names_fd_0 (o : outcome SyscallEffect) :
    syscall_spec (getdents64_in (Z_to_bv 64 (2 ^ 32)) 0) readdir_model o ↔
      o = Ok (mkEffect (errno_ret ENOTDIR) [] []) readdir_model [] := by
  sys_norm

/-- …so `-EBADF` for a0 = 2^32 — the answer to a 64-bit reading of the register — is refused.
kernel: fs/readdir.c:getdents64,iterate_dir@v6.18.46 -/
theorem sysno_61_fd_2_pow_32_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getdents64_in (Z_to_bv 64 (2 ^ 32)) 0) readdir_model
        (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- `getdents64(dirfd, NULL, 0)` is `-EINVAL` (or the removed directory's
`-ENOENT`), never `-EFAULT`: `filldir64` refuses on the size
(fs/readdir.c:367, Linux v6.18.46) before `user_write_access_begin`
(include/linux/uaccess.h:569, Linux v6.18.46), which fs/readdir.c:374 calls.
kernel: fs/readdir.c:iterate_dir,filldir64@v6.18.46 -/
theorem sysno_61_null_buffer_no_room_is_enoent_or_einval (o : outcome SyscallEffect) :
    syscall_spec (getdents64_in 5 0) readdir_model o ↔
      (o = Ok (mkEffect (errno_ret ENOENT) [] []) readdir_model []
       ∨ o = Ok (mkEffect (errno_ret EINVAL) [] []) readdir_model []) := by
  sys_norm

/-- …and `-EFAULT` for the NULL buffer is refused: the size test comes first.
kernel: fs/readdir.c:filldir64@v6.18.46 -/
theorem sysno_61_null_buffer_efault_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getdents64_in 5 0) readdir_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- The count is a2: with a NULL a1 and 24 in a2, the directory arm has
room and declines, for the reasons `count_24_is_unmodeled` gives.  A table
line reading a1 would answer `-EINVAL` here.
kernel: fs/readdir.c:getdents64,filldir64@v6.18.46 -/
theorem sysno_61_count_is_a2 (o : outcome SyscallEffect) :
    syscall_spec (getdents64_in 5 24) readdir_model o ↔ o = Unmodeled := by
  sys_norm

/-- …so the `-EINVAL` a table line reading a1 as the count would answer is refused.
kernel: fs/readdir.c:getdents64,filldir64@v6.18.46 -/
theorem sysno_61_count_is_a2_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (getdents64_in 5 24) readdir_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-! ## A17: FdFileRW and FdFileA -/

def a17_readdir_model : Model :=
  fixture_of (fds := [(3, .FdFileRW [102] 0)]) (fs := [([102], [120])])

attribute [sys_simp low] a17_readdir_model.eq_1

/-- `getdents64` through a read-write file is -ENOTDIR, as it is through
an `FdFile`: `iterate_dir` (fs/readdir.c:88-91, Linux v6.18.46) answers
-ENOTDIR when the file has no `.iterate_shared`, and the access mode
decides nothing about the inode's operation table.  The count 256 has
room, so a mutant that declined this kind the way the DIRECTORY arm
declines a roomy buffer fails here.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem a17_rdwr_getdents64_is_enotdir (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 61 [3, 4096, 256, 0, 0, 0]
        (fun _ => none) (fun _ => none)) a17_readdir_model o
      ↔ o = Ok (mkEffect (errno_ret ENOTDIR) [] []) a17_readdir_model [] := by
  sys_norm

def a17_readdir_append_model : Model :=
  fixture_of (fds := [(3, .FdFileA [102] 0)]) (fs := [([102], [120])])

attribute [sys_simp low] a17_readdir_append_model.eq_1

/-- `getdents64` through an append-mode file is -ENOTDIR, as it is
through an `FdFileW`: append mode changes where a write lands, not
whether the inode has an `.iterate_shared`, which is what `iterate_dir`
(fs/readdir.c:88-91, Linux v6.18.46) tests.
kernel: fs/readdir.c:iterate_dir@v6.18.46 -/
theorem a17_append_getdents64_is_enotdir (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 61 [3, 4096, 256, 0, 0, 0]
        (fun _ => none) (fun _ => none)) a17_readdir_append_model o
      ↔ o = Ok (mkEffect (errno_ret ENOTDIR) [] []) a17_readdir_append_model [] := by
  sys_norm

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Readdir
