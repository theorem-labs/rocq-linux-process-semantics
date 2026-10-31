import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! # Checks.Cases.Fs.File — what `dup` and `dup3` allow, read off against Linux

Worked examples over `Sys.Fs.File.dup_spec` and `Sys.Fs.File.dup3_spec`,
the twin of `theories/LinuxProcessSem/Checks/Cases/Fs/File.v`.  Not part
of the trusted specification: this file is QA on the definitions, written
to be READ, and every claim in it is a claim about what the kernel does,
with the citation beside it.

HOW THESE ARE STATED.  Each decision is pinned on the spec itself —
`dup_spec 0 i dup_model o` over a symbolic input `i`, since neither arm
reads memory — as an `iff` over EVERY outcome `o`, which fixes the admitted
answer and refuses every other one, `Unmodeled` included, beside a
refutation of the concrete answer a wrong model or a lying kernel would
give: the fd `dup` would have chosen, the errno of the neighbouring gate,
the success a kind-first model would answer.  The table's `fd32` narrowing
is pinned separately through the dispatcher, on a `SyscallInput` numbered
23 or 24, as Rocq's `check_syscall (mkInput 23 …)` cases have it.  Nearly
all close by `sys_norm` / `sys_refute`; the ones that do not say so where
they stand.

`dup`'s admitted set is a DISJUNCTION, and every positive `dup` pin
spells it out: -ENOMEM or -EMFILE (the two failures `get_unused_fd_flags`
can raise), or the copy installed at the lowest free fd.  The two errnos
are admitted at EVERY state, and that is permissiveness, not a claim
about the state at hand: on `dup_model` the lowest free fd is 5, below
the embedded table and below the limit, so `alloc_fd` (fs/file.c:570-613,
Linux v6.18.46) reaches neither its -EMFILE (:591-593) nor `expand_files`
(:595-598), and Linux answers 5 and nothing else.  The model admits the errnos anyway
because it carries neither the table's `max_fds` nor, at allocation, the
limit (`Sys.Fs.File.lowest_fd` names the bug entry), so the `iff`s below
state what the spec admits, the probe's `dup-inject` cases hold the
harness to it, and a pin that named the success alone would be false of
the spec.  `dup3` has no such alternative: everything it answers is
decided from state, which the five-errno refutations under `do_dup2` pin.

A DECLINE HERE IS A COVERAGE GAP, NOT AN EMPTY INTERSECTION.  Every
`Unmodeled` below is one Linux answers with a definite value that the
model has no state to derive — a second fd on one file offset, a second
reference on a pipe's writer count, a free `newfd` whose answer turns on
the table's `max_fds` — and the pins that offer the kernel's own value
and still require `Unmodeled` are what keep a later arm from turning a
gap into a guess: the open file description layer has to land first.

What a probe cannot reach, and these therefore carry (Rocq's header): the
fd TABLE the model is left with, the DECLINES, which hold for every
claimed return rather than the one a run produced, and the two facts
about dup3's RLIMIT_NOFILE gate that need a SECOND model to state — that
it is read from the run rather than written into the spec, and that it
beats a descriptor the process already holds.

Rocq's worked cases are carried conjunct by conjunct, each on a theorem
marked `rocq-twin:` (the check that none is missing is ticket T9; until it
lands, `check_lean_pin_evidence.py` verifies only that each name cited
exists).  Beyond them: the closed-fd and truncation pins Rocq leaves to the
probe; the probe's recorded calls, restated at the registers it passed — a
`probe:` line below names a case whose call the theorem states, and a pin
at other registers cites the kernel instead; the injectable-errno set from
both sides; `ksys_dup3`'s order pinned pair by pair; and the fd kinds
Rocq's fixture does not hold — a write-only file, a socket, both pipe
ends, /dev/null and /dev/urandom — each put through both arms.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.File

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.File
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! ## The register lines the specs owe `sys_simp`

`Checks/Cases/Tactic.lean`'s header asks each spec for its unfolding
equation in the set, and for each helper its post-states are spelled
with; they are registered here, beside the pins that read them, because
this port edits only its own two files.  `dup_errnos` enters as `mmap_errnos`
does, so `bind_errno_from_iff` reads its members; `lowest_fd` enters so
its `choose` is read continuation-first. -/

attribute [sys_simp low] dup_spec.eq_1 dup3_spec.eq_1 lowest_fd.eq_1 dup_errnos.eq_1

/-! ## The constants these checks spell out -/

/-- The one flag `ksys_dup3` admits (fs/file.c:1405, Linux v6.18.46,
commit 1f99e9ab748f), as the numeral the pins pass.
kernel: include/uapi/asm-generic/fcntl.h:O_CLOEXEC@v6.18.46 -/
example : O_CLOEXEC = 524288 := by decide

/-- The two errnos `dup` may be handed from below `get_unused_fd_flags`:
-EMFILE from `alloc_fd`'s `fd >= end` test (fs/file.c:591-593, Linux
v6.18.46, commit 1f99e9ab748f), -ENOMEM (and -EMFILE again) from
`alloc_fdtable` (:197, :213, :242) when the table must grow.
kernel: fs/file.c:alloc_fd,alloc_fdtable@v6.18.46 -/
example : dup_errnos = [ENOMEM, EMFILE] := by decide

/-! ## The fixtures

`dup_model` is Rocq's: the three channels, a read-only file "f" = "hi" at
fd 3 positioned one byte in, and the directory fd at 4 — one fd of every
kind Rocq's fixture holds, so both sides of `dup_modeled_entry` are in
reach.  The lowest free fd is 5; fd 9 is the closed fd the -EBADF pins
name.  Rocq spells it through `mkModel`, whose overflow credentials
`fixture_of` replaces with the demo user's; neither arm reads
credentials, so no pin here can see the difference.

`dup_model_nofile4` is the same table under a soft RLIMIT_NOFILE of 4,
which a parent that lowered the limit really can hand a process: `execve`
closes only the close-on-exec descriptors (`do_close_on_exec`,
fs/file.c:862, from `begin_new_exec`, fs/exec.c:1194, Linux v6.18.46) and
the rest stay open however low the limit is.

`dup_kinds_model` adds the kinds Rocq's file does not pin: a fresh socket
(fd 5), both ends of one pipe (fd 6 reads, fd 7 writes, over an empty
pipe buffer 0), /dev/null opened read-write (fd 8) and /dev/urandom
(fd 9).  Its lowest free fd is 10. -/

/-- The fd table of `dup_model`, named so the post-states below can be
spelled as one entry consed onto it. -/
def dup_fds : List (word × FdEntry) :=
  [ (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
    (3, .FdFile [102] 1), (4, .FdDir) ]

def dup_fs : Fs.Fs := [([102], [104, 105])]

def dup_model : Model := fixture_of (fds := dup_fds) (fs := dup_fs)

/-- Rocq's `dup_model_nofile4`: the same descriptors under a soft limit
of 4. -/
def dup_model_nofile4 : Model := with_nofile (Z_to_bv 64 4) dup_model

/-- `dup_fds` with a WRITE-ONLY file fd at 5, "f" opened for writing at
offset 0: the one kind of `dup_modeled_entry`'s `false` row that no other
fixture holds.  Its lowest free fd is 6. -/
def dup_filew_fds : List (word × FdEntry) := dup_fds ++ [(5, .FdFileW [102] 0)]

def dup_filew_model : Model := fixture_of (fds := dup_filew_fds) (fs := dup_fs)

/-- `dup_fds` with fd 0 CLOSED: the table `close(0)` leaves, the probe's
`dup-lowest` state.  The lowest free fd is 0, below every open one. -/
def dup_fds_closed0 : List (word × FdEntry) :=
  [ (1, .FdChannel 1), (2, .FdChannel 2), (3, .FdFile [102] 1), (4, .FdDir) ]

def dup_model_closed0 : Model := fixture_of (fds := dup_fds_closed0) (fs := dup_fs)

/-- `dup_fds` with fd 1 CLOSED: the table the probe's `d3-newfree` mode
builds with `close(1)` before `dup3(2, 1, 0)`, so its free `newfd` is a
standard descriptor below `NR_OPEN_DEFAULT`. -/
def dup_fds_closed1 : List (word × FdEntry) :=
  [ (0, .FdChannel 0), (2, .FdChannel 2), (3, .FdFile [102] 1), (4, .FdDir) ]

def dup_model_closed1 : Model := fixture_of (fds := dup_fds_closed1) (fs := dup_fs)


/-- `dup_fds` with one descriptor OPEN at 100: above `NR_OPEN_DEFAULT` and
under `State.default_nofile`, the band where the FREE-`newfd` arm declines.
A process reaches it by opening enough descriptors, or by a `dup3` the
model declines; that it is reachable at all is what makes the pair of arms
a distinction rather than a dead branch. -/
def dup_high_fds : List (word × FdEntry) := dup_fds ++ [(100, .FdChannel 2)]

def dup_high_model : Model := fixture_of (fds := dup_high_fds) (fs := dup_fs)

/-- `dup_fds` with four of the five kinds Rocq's file does not pin; the
write-only file has `dup_filew_model`. -/
def dup_kinds_fds : List (word × FdEntry) :=
  dup_fds ++
  [ (5, .FdSocket .SkFresh), (6, .FdPipe 0 false), (7, .FdPipe 0 true),
    (8, .FdDevNull true true), (9, .FdUrandom) ]

def dup_kinds_model : Model :=
  fixture_of (fds := dup_kinds_fds) (pipes := [(0, ([], 0))]) (fs := dup_fs)

/-! ### The fixtures' readings

Each lookup the pins need is one closed fact, registered in `sys_simp` at
the default priority.  They are stated on `dup_model.m_fd.fdst_table`, the
spelling the first pass leaves a match discriminant in — `m_fds.eq_1`
opens the getter there before a projection lemma on `m_fds dup_model` is
tried — so the match reduces in the FIRST pass and `bind_errno_from_iff`
reads `dup`'s errno alternative enumeration-first.  Stated on `m_fds
dup_model` instead, the match waits for the second pass, which evaluates
`errno_from` to its `choose` before the reading sees it, and every
refutation whose only contradiction is the injected errno's value is left
open with that equation last (the file header of `Checks/Cases/Tactic.lean`
predicts this; `Checks/Cases/Fs/Fcntl.lean` never meets it because
`fcntl_spec` injects nothing).  The fixtures stay names in the normal form,
and a post-state an `iff` names is spelled as `fixture_of` of the literal
table the arm leaves, which the second pass evaluates to the same
constructor tree as the arm's `with_fds`. -/

/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_dup_0 : fd_lookup dup_model.m_fd.fdst_table 0 = some (.FdChannel 0) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_dup_1 : fd_lookup dup_model.m_fd.fdst_table 1 = some (.FdChannel 1) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_dup_2 : fd_lookup dup_model.m_fd.fdst_table 2 = some (.FdChannel 2) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_dup_3 : fd_lookup dup_model.m_fd.fdst_table 3 = some (.FdFile [102] 1) := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_dup_4 : fd_lookup dup_model.m_fd.fdst_table 4 = some .FdDir := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_dup_5 : fd_lookup dup_model.m_fd.fdst_table 5 = none := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_dup_7 : fd_lookup dup_model.m_fd.fdst_table 7 = none := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_dup_9 : fd_lookup dup_model.m_fd.fdst_table 9 = none := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_dup_63 : fd_lookup dup_model.m_fd.fdst_table 63 = none := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_dup_64 : fd_lookup dup_model.m_fd.fdst_table 64 = none := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_dup_100 : fd_lookup dup_model.m_fd.fdst_table 100 = none := rfl
/-- One closed lookup in the fixture table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_dup_999 : fd_lookup dup_model.m_fd.fdst_table 999 = none := rfl

/-- One closed lookup in the write-only-file fixture's table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_filew_1 : fd_lookup dup_filew_model.m_fd.fdst_table 1 = some (.FdChannel 1) := rfl
/-- One closed lookup in the write-only-file fixture's table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_filew_5 : fd_lookup dup_filew_model.m_fd.fdst_table 5 = some (.FdFileW [102] 0) := rfl
/-- One closed lookup in the closed-0 fixture's table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_closed0_0 : fd_lookup dup_model_closed0.m_fd.fdst_table 0 = none := rfl
/-- One closed lookup in the closed-0 fixture's table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_closed0_2 : fd_lookup dup_model_closed0.m_fd.fdst_table 2 = some (.FdChannel 2) := rfl
/-- One closed lookup in the closed-1 fixture's table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_closed1_1 : fd_lookup dup_model_closed1.m_fd.fdst_table 1 = none := rfl
/-- One closed lookup in the closed-1 fixture's table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_closed1_2 : fd_lookup dup_model_closed1.m_fd.fdst_table 2 = some (.FdChannel 2) := rfl

/-- One closed lookup in the high-descriptor fixture's table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_high_0 : fd_lookup dup_high_model.m_fd.fdst_table 0 = some (.FdChannel 0) := rfl
/-- One closed lookup in the high-descriptor fixture's table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_high_100 : fd_lookup dup_high_model.m_fd.fdst_table 100 = some (.FdChannel 2) := rfl
/-- One closed lookup in the lowered-limit fixture's table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_nofile4_0 : fd_lookup dup_model_nofile4.m_fd.fdst_table 0 = some (.FdChannel 0) := rfl
/-- One closed lookup in the lowered-limit fixture's table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_nofile4_3 : fd_lookup dup_model_nofile4.m_fd.fdst_table 3 = some (.FdFile [102] 1) := rfl
/-- One closed lookup in the lowered-limit fixture's table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_nofile4_2 : fd_lookup dup_model_nofile4.m_fd.fdst_table 2 = some (.FdChannel 2) := rfl

/-- One closed lookup in the wider table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_dup_kinds_0 : fd_lookup dup_kinds_model.m_fd.fdst_table 0 = some (.FdChannel 0) := rfl
/-- One closed lookup in the wider table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_dup_kinds_1 : fd_lookup dup_kinds_model.m_fd.fdst_table 1 = some (.FdChannel 1) := rfl
/-- One closed lookup in the wider table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_dup_kinds_5 : fd_lookup dup_kinds_model.m_fd.fdst_table 5 = some (.FdSocket .SkFresh) := rfl
/-- One closed lookup in the wider table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_dup_kinds_6 : fd_lookup dup_kinds_model.m_fd.fdst_table 6 = some (.FdPipe 0 false) := rfl
/-- One closed lookup in the wider table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_dup_kinds_7 : fd_lookup dup_kinds_model.m_fd.fdst_table 7 = some (.FdPipe 0 true) := rfl
/-- One closed lookup in the wider table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_dup_kinds_8 : fd_lookup dup_kinds_model.m_fd.fdst_table 8 = some (.FdDevNull true true) := rfl
/-- One closed lookup in the wider table.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
theorem lookup_dup_kinds_9 : fd_lookup dup_kinds_model.m_fd.fdst_table 9 = some .FdUrandom := rfl

attribute [sys_simp]
  lookup_dup_0 lookup_dup_1 lookup_dup_2 lookup_dup_3 lookup_dup_4 lookup_dup_5 lookup_dup_7
    lookup_dup_9 lookup_dup_63 lookup_dup_64 lookup_dup_100 lookup_dup_999
  lookup_high_0 lookup_high_100
  lookup_closed0_0 lookup_closed0_2 lookup_closed1_1 lookup_closed1_2
  lookup_filew_1 lookup_filew_5
  lookup_nofile4_0 lookup_nofile4_2 lookup_nofile4_3
  lookup_dup_kinds_0 lookup_dup_kinds_1 lookup_dup_kinds_5 lookup_dup_kinds_6 lookup_dup_kinds_7 lookup_dup_kinds_8
  lookup_dup_kinds_9

/-! ## `SYSCALL_DEFINE1(dup)`: the fd is resolved first, then a slot is taken

`SYSCALL_DEFINE1(dup, unsigned int, fildes)` (fs/file.c:1457-1470, Linux
v6.18.46, commit 1f99e9ab748f) starts from `ret = -EBADF` (:1459),
resolves the descriptor with `fget_raw` (:1460) and only inside
`if (file)` (:1462) asks `get_unused_fd_flags(0)` (:1463) for a slot.  So a
closed fd is -EBADF before any allocation, and the allocator's two
failures — -EMFILE at `alloc_fd`'s `fd >= end` (:591-593) and -ENOMEM from
`alloc_fdtable` (:242) — can only be answered on an OPEN fd. -/

/-- A closed fd is -EBADF, and nothing else: not a decline, and not either
allocator errno, since `fget_raw` (fs/file.c:1088-1091, Linux v6.18.46)
fails at :1460 before `get_unused_fd_flags` (fs/file.c:620-623) is reached
at :1463.  The probe's own `dup(999)`, on a table where 999 is open in no
fixture.
probe: testing/syscall-check/tests/dup_spec.c#conform -- dup-trunc -/
theorem dup_closed_fd_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    dup_spec 999 i dup_model o ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) dup_model [] := by
  sys_norm

/-- …and a kernel answering -EMFILE for a closed fd has allocated before
it looked the fd up, which fs/file.c:1460-1463 (Linux v6.18.46) does not
allow.  The probe's second `dup` is `dup(-1)` — `2^32 - 1` after the
table's `fd32` — so this is stated through the table, as the probe reaches
it.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup#2:ret=-EMFILE -- dup-trunc -/
theorem dup_closed_fd_emfile_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 23 [Z_to_bv 64 (-1), 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        dup_model (Ok (mkEffect (errno_ret EMFILE) [] []) m' evs) := by
  sys_refute

/-- …nor can a table that failed to grow be blamed for a bad fd.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup#2:ret=-ENOMEM -- dup-trunc -/
theorem dup_closed_fd_enomem_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 23 [Z_to_bv 64 (-1), 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        dup_model (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-! ## `get_unused_fd_flags`: the lowest free fd, bound to a copy

`get_unused_fd_flags` (fs/file.c:620-623, Linux v6.18.46) is
`alloc_fd(0, nofile, 0)` (:615-618), which takes the first clear bit from 0 (:580-585) or fails
with -EMFILE at the limit (:591-593) or with `expand_files`' error when
the table must grow (:595-598).  `fd_install` (:1465, defined :652) then
binds the very `struct file` the old fd holds. -/

/-- dup hands out the lowest free fd and binds it to a COPY of the entry,
which is the whole of what "share the description" means for a channel:
the read position is `m_stdin` and the writes are trace events, so both
fds already name the same thing.  The admitted set is exactly the two
injectable errnos, with nothing changed, or fd 5 with the copy installed —
no other fd, no other errno, no decline.  The probe's `dup-stdin` mode is
this call, `dup(0)`.
rocq-twin: dup_installs_a_copy_at_the_lowest_free_fd
probe: testing/syscall-check/tests/dup_spec.c#conform --stdin aacdef -- dup-stdin -/
theorem dup_installs_a_copy_at_the_lowest_free_fd (i : SyscallInput) (o : outcome SyscallEffect) :
    dup_spec 0 i dup_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) dup_model []
        ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) dup_model [])
       ∨ o = Ok (mkEffect 5 [] []) (fixture_of (fds := (5, .FdChannel 0) :: dup_fds) (fs := dup_fs)) []) := by
  sys_norm

/-- The probe's `dup-chan` call is `dup(2)`: the copy of channel 2 lands at
the lowest free fd — 5 here, 3 on the probe's own three-channel table —
with the two errnos admitted as everywhere.
probe: testing/syscall-check/tests/dup_spec.c#conform -- dup-chan -/
theorem dup_of_channel_2_installs_at_5 (i : SyscallInput) (o : outcome SyscallEffect) :
    dup_spec 2 i dup_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) dup_model []
        ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) dup_model [])
       ∨ o = Ok (mkEffect 5 [] []) (fixture_of (fds := (5, .FdChannel 2) :: dup_fds) (fs := dup_fs)) []) := by
  sys_norm

/-- No kernel can be made to hand out a non-lowest fd, so the model
REJECTS fd 6: `alloc_fd` returns `find_next_fd`'s first clear bit
(fs/file.c:585, Linux v6.18.46), which is 5 here.  Only `--mutate
dup:ret+1` reaches this: the probe's `dup(2)` handed 4 where 3 was free.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup:ret+1 -- dup-chan -/
theorem dup_non_lowest_fd_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup_spec 2 i dup_model (Ok (mkEffect 6 [] []) m' evs) := by
  sys_refute

/-- …nor an fd that is already open: `__set_open_fd` (fs/file.c:333-340,
Linux v6.18.46) marks the slot at :606, and `find_next_fd`
(fs/file.c:544-565) never returns a set bit.  The probe's `dup(2)`
claiming 2 itself.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup:ret=2 -- dup-chan -/
theorem dup_open_fd_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup_spec 2 i dup_model (Ok (mkEffect 2 [] []) m' evs) := by
  sys_refute

/-- The success is admitted with the copy installed at 5: the fd TABLE the
model is left with, which no return value reveals.  `dup(0)`, the probe's
`dup-stdin` call.
probe: testing/syscall-check/tests/dup_spec.c#conform --stdin aacdef -- dup-stdin -/
theorem dup_copy_at_5_admitted (i : SyscallInput) :
    dup_spec 0 i dup_model
      (Ok (mkEffect 5 [] []) (fixture_of (fds := (5, .FdChannel 0) :: dup_fds) (fs := dup_fs)) []) := by
  sys_norm

/-- …and a success that installed the copy anywhere else, or nothing at
all, is refused: here the return is right and the table is the old one.
Refuted in hypothesis form: with `evs` symbolic the goal form leaves a
residue the pass list does not fold, while `sys_refute at h` folds the
hypothesis to `False` (`Checks/Cases/Mm/Mprotect.lean`'s
`middle_page_unsplit_ledger_rejected` is the pattern).
kernel: fs/file.c:dup,fd_install@v6.18.46 -/
theorem dup_success_without_the_copy_rejected (i : SyscallInput) (evs : List event) :
    ¬ dup_spec 0 i dup_model (Ok (mkEffect 5 [] []) dup_model evs) := by
  intro h; sys_refute at h

/-- A directory fd duplicates too: `FdDir` is nullary, so a copy carries no
position that could drift, and `fget_raw` (fs/file.c:1088-1091, Linux
v6.18.46) does not care what the file is.  The probe's `dup-dir` opens its
directory at 3, where this fixture holds Rocq's file, so its `dup(3)` is
not restated here.
rocq-twin: dup_of_a_directory_fd_duplicates
kernel: fs/file.c:dup,fget_raw,alloc_fd,alloc_fdtable@v6.18.46 -/
theorem dup_of_a_directory_fd_duplicates (i : SyscallInput) (o : outcome SyscallEffect) :
    dup_spec 4 i dup_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) dup_model []
        ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) dup_model [])
       ∨ o = Ok (mkEffect 5 [] []) (fixture_of (fds := (5, .FdDir) :: dup_fds) (fs := dup_fs)) []) := by
  sys_norm

/-- Lowest-free holds for a directory fd too: `find_next_fd`
(fs/file.c:544-565, Linux v6.18.46), called at :585, does not read the
file's kind.
kernel: fs/file.c:dup,alloc_fd,find_next_fd@v6.18.46 -/
theorem dup_dir_non_lowest_fd_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup_spec 4 i dup_model (Ok (mkEffect 6 [] []) m' evs) := by
  sys_refute

/-! ### The freed slot is retaken: `next_fd` is lowered by a close

`alloc_fd(0, …)` (fs/file.c:570-613, Linux v6.18.46) starts its scan at
`start = 0` and moves to `files->next_fd` only when that is higher
(:580-582), and a close LOWERS `next_fd`: `file_close_fd_locked`
(:692-709) hands the slot to
`__put_unused_fd` (:626-632), whose `if (fd < files->next_fd)
files->next_fd = fd` (:630-631) is what makes the freed slot the next
answer.  So after `close(0)`, `dup(2)` returns 0 — not the slot after the
highest open one, which is what a hint that only ever rose would give. -/

/-- After `close(0)`, `dup(2)` takes the freed slot 0: the copy of channel 2
lands at 0, and the two errnos stay admitted as everywhere.
probe: testing/syscall-check/tests/dup_spec.c#conform -- dup-lowest -/
theorem dup_retakes_the_freed_slot (i : SyscallInput) (o : outcome SyscallEffect) :
    dup_spec 2 i dup_model_closed0 o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) dup_model_closed0 []
        ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) dup_model_closed0 [])
       ∨ o = Ok (mkEffect 0 [] [])
            (fixture_of (fds := (0, .FdChannel 2) :: dup_fds_closed0) (fs := dup_fs)) []) := by
  sys_norm

/-- …and the probe's lie, `ret+1`: fd 1 is open, so a kernel handing it out
has broken `__set_open_fd`'s invariant (fs/file.c:333-340, Linux v6.18.46).
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup:ret+1 -- dup-lowest -/
theorem dup_freed_slot_plus_one_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup_spec 2 i dup_model_closed0 (Ok (mkEffect 1 [] []) m' evs) := by
  sys_refute

/-- …and the slot after the highest open descriptor, 5, which a hint that a
close never lowered would answer, is refused: `__put_unused_fd` lowered
`next_fd` to 0 (fs/file.c:630-631) and `find_next_fd` (:544-565) finds the
clear bit there.
kernel: fs/file.c:alloc_fd,find_next_fd,__put_unused_fd,file_close_fd_locked@v6.18.46 -/
theorem dup_slot_after_the_highest_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup_spec 2 i dup_model_closed0 (Ok (mkEffect 5 [] []) m' evs) := by
  sys_refute

/-! ## The injectable errnos, from both sides

`alloc_fd` (fs/file.c:570-613, Linux v6.18.46) has two exits below the
success: -EMFILE when the first free slot is at or past
`rlimit(RLIMIT_NOFILE)`
(:591-593), and `expand_files`' error (:595-598), which is -EMFILE at
`sysctl_nr_open` (:310-311) or what `alloc_fdtable` returns: -EMFILE
(:197, :213) or -ENOMEM (:242).  Nothing else on `dup`'s path can fail:
`fget_raw` only says whether the fd is open, and `fd_install` (:652) has
no error return. -/

/-- -ENOMEM is admitted on an open fd, with nothing changed.  NOT because
Linux can answer it here — the lowest free fd is 5, `expand_files` is
never reached (:595), and the kernel's only answer is 5 — but because the
model carries no `max_fds` to say so (the file header); where the table
does grow, `alloc_fdtable` (:242) fails this way and `dup` drops its
reference at :1467 with nothing installed, which is the shape admitted.
probe: testing/syscall-check/tests/dup_spec.c#conform --mutate dup:ret=-ENOMEM -- dup-inject -/
theorem dup_enomem_admitted (i : SyscallInput) :
    dup_spec 2 i dup_model (Ok (mkEffect (errno_ret ENOMEM) [] []) dup_model []) := by
  sys_norm

/-- -EMFILE likewise: `alloc_fd`'s `fd >= end` (:591-593) needs the lowest
free fd at or past the soft limit, which 5 under 1024 is not; admitted
because `lowest_fd` consults no limit (its docstring, and the bug entry
it names).
probe: testing/syscall-check/tests/dup_spec.c#conform --mutate dup:ret=-EMFILE -- dup-inject -/
theorem dup_emfile_admitted (i : SyscallInput) :
    dup_spec 2 i dup_model (Ok (mkEffect (errno_ret EMFILE) [] []) dup_model []) := by
  sys_norm

/-- -ENFILE is refused: dup allocates no `struct file` — `fd_install`
(fs/file.c:644-677, Linux v6.18.46) stores, at :1465, the pointer
`fget_raw` returned — so the system-wide open-file limit, which
`alloc_empty_file` (fs/file_table.c:239-279, v6.18.46) enforces, is never
consulted.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup:ret=-ENFILE -- dup-inject -/
theorem dup_enfile_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup_spec 2 i dup_model (Ok (mkEffect (errno_ret ENFILE) [] []) m' evs) := by
  sys_refute

/-- -EBUSY is `do_dup2`'s errno (fs/file.c:1313-1315, Linux v6.18.46), on
`dup3`'s path and not on `dup`'s.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup:ret=-EBUSY -- dup-inject -/
theorem dup_ebusy_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup_spec 2 i dup_model (Ok (mkEffect (errno_ret EBUSY) [] []) m' evs) := by
  sys_refute

/-- -EINTR is refused: nothing between `fget_raw` and `fd_install` sleeps
interruptibly.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup:ret=-EINTR -- dup-inject -/
theorem dup_eintr_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup_spec 2 i dup_model (Ok (mkEffect (errno_ret EINTR) [] []) m' evs) := by
  sys_refute

/-- -EBADF on an OPEN fd is refused: fd validity is tracked, never
injected, and `fget_raw` on an open descriptor does not fail.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup:ret=-EBADF -- dup-inject -/
theorem dup_ebadf_on_open_fd_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
        ¬ dup_spec 2 i dup_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- WHERE THE ALLOCATOR'S DIVERGENCE BITES, stated so it is visible: under a
soft limit of 4 with fds 0-4 held, Linux answers -EMFILE and nothing else —
`alloc_fd`'s `fd >= end` (fs/file.c:591-593, Linux v6.18.46), with `end =
rlimit(RLIMIT_NOFILE)` from `__get_unused_fd_flags` (:615-618) — while
`lowest_fd` reads no limit, so the model admits the copy at 5 as well.
That is the priority-2 divergence bugs/fd-allocation-ignores-rlimit-nofile.md
records: the kernel's own answer stays admitted, beside one it never gives.
kernel: fs/file.c:alloc_fd,alloc_fdtable,__get_unused_fd_flags,get_unused_fd_flags@v6.18.46 -/
theorem dup_above_the_soft_limit_still_admits_the_slot (i : SyscallInput)
    (o : outcome SyscallEffect) :
    dup_spec 2 i dup_model_nofile4 o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) dup_model_nofile4 []
        ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) dup_model_nofile4 [])
       ∨ o = Ok (mkEffect 5 [] [])
            (with_nofile (Z_to_bv 64 4)
              (fixture_of (fds := (5, .FdChannel 2) :: dup_fds) (fs := dup_fs))) []) := by
  sys_norm

/-- …and it is a divergence, not a decline: `Unmodeled` is refused there, so
a later reader cannot mistake the gap for a fail-closed one.
kernel: fs/file.c:alloc_fd@v6.18.46 -/
theorem dup_above_the_soft_limit_not_declined (i : SyscallInput) :
    ¬ dup_spec 2 i dup_model_nofile4 Unmodeled := by
  sys_refute

/-! ### Never a held descriptor: the freeness conjunct

`find_next_fd` (fs/file.c:544-565, Linux v6.18.46) returns a clear bit of
`open_fds`, `alloc_fd` marks the slot before returning (`__set_open_fd`,
:606) and asserts it empty (:608), and `fd_install` (:652) fills a NULL
slot; so
`dup` never hands out a descriptor the process holds.  In the model that
is `lowest_fd`'s freeness conjunct, and no fixture can exercise it: the
conjunct bites only where `State.alloc_fd`'s 4096-candidate scan ends on a
held slot, a table dense up to 4096 (`State.alloc_fd_le` is the bound, and
`Sys.Fs.File.lowest_fd`'s docstring carries what the wall costs against
Linux).  So the conjunct is pinned for EVERY table instead, by hand. -/

/-- `dup` never answers a descriptor the table already holds, whatever the
model and whichever fd: `find_next_fd` (fs/file.c:544-565) returns a clear
bit of `open_fds`, `alloc_fd` marks it before returning (`__set_open_fd`,
:606) and asserts the slot empty (:608), and `fd_install` (:652) fills a
NULL slot.  Bounded to descriptors below the scan wall so the two errnos,
which sit at the top of the word, are out of reach.  This is the one pin
that reads `lowest_fd`'s FREENESS conjunct: drop it and the install arm
would answer `State.alloc_fd`'s number even where the table holds it.
kernel: fs/file.c:dup,alloc_fd,find_next_fd,__set_open_fd,fd_install@v6.18.46 -/
theorem dup_never_answers_a_held_fd (fd r : word) (i : SyscallInput) (m m' : Model)
    (evs : List event) (hr : bv_unsigned r ≤ 4096) (hheld : fd_lookup (m_fds m) r ≠ none) :
    ¬ dup_spec fd i m (Ok (mkEffect r [] []) m' evs) := by
  intro h
  simp only [dup_spec, bind_get_model_iff] at h
  cases hl : fd_lookup (m_fds m) fd with
  | none =>
    simp only [hl, err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
    have hr' : r = errno_ret EBADF := congrArg SyscallEffect.eff_ret h.1
    have hv : bv_unsigned (errno_ret EBADF) = 18446744073709551607 := by decide
    rw [hr', hv] at hr
    omega
  | some e =>
    simp only [hl] at h
    cases hk : dup_modeled_entry e with
    | false =>
      simp only [hk, Bool.not_false, ↓reduceIte, unmodeled_iff] at h
      cases h
    | true =>
      simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, alt_iff, errno_from, lowest_fd,
        bind_choose_iff, err_ret, ret_only, set_fds, bind_modify_iff, pure_iff,
        outcome.Ok.injEq] at h
      rcases h with ⟨er, hin, heq, -, -⟩ | ⟨fd', ⟨hfree, -⟩, heq, -, -⟩
      · have hr' : r = errno_ret er := congrArg SyscallEffect.eff_ret heq
        simp only [dup_errnos, List.mem_cons, List.not_mem_nil, or_false] at hin
        have h1 : bv_unsigned (errno_ret ENOMEM) = 18446744073709551604 := by decide
        have h2 : bv_unsigned (errno_ret EMFILE) = 18446744073709551592 := by decide
        rcases hin with rfl | rfl
        · rw [hr', h1] at hr
          omega
        · rw [hr', h2] at hr
          omega
      · have hr' : r = fd' := congrArg SyscallEffect.eff_ret heq
        rw [hr'] at hheld
        exact hheld hfree

/-! ## The offset-sharing gap: a FILE fd declines

`fd_install` (fs/file.c:644-677, Linux v6.18.46), called at :1465, hands
the new slot the very `struct file` the old fd holds, so on Linux the two
fds share one `f_pos` (include/linux/fs.h:1233, v6.18.46).  `State.FdEntry` keeps the offset in the
entry, so the model cannot say that, and says nothing. -/

/-- Duplicating a FILE fd declines WHATEVER the kernel claims.  A probe
pins one claimed return; this pins all of them, which is what makes it a
fail-closed gap rather than a wrong answer.
rocq-twin: dup_of_a_file_fd_declines_whatever_the_kernel_claims
probe: testing/syscall-check/tests/dup_spec.c#fail-closed -- dup-file -/
theorem dup_of_a_file_fd_declines_whatever_the_kernel_claims (i : SyscallInput)
    (o : outcome SyscallEffect) :
    dup_spec 3 i dup_model o ↔ o = Unmodeled := by
  sys_norm

/-- On Linux the call succeeds with 5; the model refuses that 5, because a
copy of the entry would read bytes 0..3 twice where Linux reads 0..3 and
then 4..7.
probe: testing/syscall-check/tests/dup_spec.c#fail-closed -- dup-file -/
theorem dup_of_a_file_fd_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup_spec 3 i dup_model (Ok (mkEffect 5 [] []) m' evs) := by
  sys_refute

/-- …and the decline precedes the return: -EBADF is refused too, for an
fd that is open.
probe: testing/syscall-check/tests/dup_spec.c#fail-closed --mutate dup:ret=-EBADF -- dup-file -/
theorem dup_of_a_file_fd_ebadf_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup_spec 3 i dup_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- A WRITE-ONLY file fd declines for the same reason: `write` and `lseek`
rewrite the entry's offset in place, and `fd_install` (fs/file.c:652, at
:1465) would make the new fd a second reference to the one `f_pos`
(include/linux/fs.h:1233).  Linux answers 6 here.
kernel: fs/file.c:dup,fd_install@v6.18.46 -/
theorem dup_of_a_write_only_file_fd_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    dup_spec 5 i dup_filew_model o ↔ o = Unmodeled := by
  sys_norm

/-- The 6 Linux returns for the write-only file is refused.
kernel: fs/file.c:dup,fd_install@v6.18.46 -/
theorem dup_of_a_write_only_file_fd_success_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ dup_spec 5 i dup_filew_model (Ok (mkEffect 6 [] []) m' evs) := by
  sys_refute

/-- …and through `dup3`, as the SOURCE: declined; the 1 Linux returns is
refused next.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_from_a_write_only_file_fd_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 5 1 0 i dup_filew_model o ↔ o = Unmodeled := by
  sys_norm

/-- The 1 Linux returns there is refused.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_from_a_write_only_file_fd_success_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ dup3_spec 5 1 0 i dup_filew_model (Ok (mkEffect 1 [] []) m' evs) := by
  sys_refute


/-! ## The kinds Rocq's fixture does not hold

`dup_modeled_entry` answers each `FdEntry` kind; Rocq's fixture reaches
three, and the write-only file is pinned above on `dup_filew_model`.  The
other four, each offered the answer Linux gives — fd 10, the lowest free
slot of `dup_kinds_model` — and either admitted or refused for the reason
on `Sys.Fs.File.dup_modeled_entry`.  Each kind is exercised at ONE
payload: the arms are payload-blind by construction (`| .FdDevNull _ _`),
and a refinement answering another payload differently would fail closed
on a kind no Lean arm can mint until `openat` is ported — the condition
under which this section is re-read. -/

/-- /dev/null duplicates: `null_lseek` pins `f_pos` at 0 and `read_null` /
`write_null` never advance it (drivers/char/mem.c:561, :412, :418), so
copying the entry IS the sharing, as for a channel.
kernel: fs/file.c:dup,alloc_fd,alloc_fdtable; drivers/char/mem.c:null_lseek,read_null,write_null@v6.18.46 -/
theorem dup_of_devnull_duplicates (i : SyscallInput) (o : outcome SyscallEffect) :
    dup_spec 8 i dup_kinds_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) dup_kinds_model []
        ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) dup_kinds_model [])
       ∨ o = Ok (mkEffect 10 [] [])
                        (fixture_of (fds := (10, .FdDevNull true true) :: dup_kinds_fds)
                        (pipes := [(0, ([], 0))]) (fs := dup_fs)) []) := by
  sys_norm

/-- …and a model grouping /dev/null with the declining kinds is refuted:
the decline is refused where Linux copies.
kernel: fs/file.c:dup,fd_install; drivers/char/mem.c:null_lseek@v6.18.46 -/
theorem dup_of_devnull_decline_rejected (i : SyscallInput) :
    ¬ dup_spec 8 i dup_kinds_model Unmodeled := by
  sys_refute


/-- /dev/urandom duplicates: `urandom_fops` (drivers/char/random.c:1572-1581)
seeks through `noop_llseek` (fs/read_write.c:324-327) and reads through
`urandom_read_iter` (drivers/char/random.c:1453-1475), neither of which
moves `f_pos`, and the bytes a read delivers come from the run's declared
stream, which is the model's and not the entry's — so two fds on one
description and two opens of the device read alike, and copying the
entry IS the sharing.
kernel: fs/file.c:dup,alloc_fd,alloc_fdtable; drivers/char/random.c:urandom_read_iter; fs/read_write.c:noop_llseek@v6.18.46 -/
theorem dup_of_urandom_duplicates (i : SyscallInput) (o : outcome SyscallEffect) :
    dup_spec 9 i dup_kinds_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) dup_kinds_model []
        ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) dup_kinds_model [])
       ∨ o = Ok (mkEffect 10 [] [])
            (fixture_of (fds := (10, .FdUrandom) :: dup_kinds_fds)
                        (pipes := [(0, ([], 0))]) (fs := dup_fs)) []) := by
  sys_norm

/-- …and a model that grouped the random device with the declining
kinds is refuted: the decline is refused where Linux copies.
kernel: fs/file.c:dup,fd_install; drivers/char/random.c:urandom_read_iter@v6.18.46 -/
theorem dup_of_urandom_decline_rejected (i : SyscallInput) :
    ¬ dup_spec 9 i dup_kinds_model Unmodeled := by
  sys_refute

/-- A socket declines: the entry carries the connection's remaining
receive script, rewritten in place by a read, and a copy would report the
peer's reset once per fd.  Linux answers 10; refused.
kernel: fs/file.c:dup,fd_install@v6.18.46 -/
theorem dup_of_a_socket_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    dup_spec 5 i dup_kinds_model o ↔ o = Unmodeled := by
  sys_norm

/-- The 10 Linux returns for the socket is refused.
kernel: fs/file.c:dup,fd_install@v6.18.46 -/
theorem dup_of_a_socket_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup_spec 5 i dup_kinds_model (Ok (mkEffect 10 [] []) m' evs) := by
  sys_refute

/-- A pipe end declines, and NOT because of an offset: `do_dup2`'s
`get_file` and `dup`'s `fd_install` add a reference to the one `struct
file` without touching `pipe->readers` / `pipe->writers`, which
`pipe_release` (fs/pipe.c:724-746, Linux v6.18.46) decrements (:731, :733)
once per `struct file` release — so
after `dup` the pipe still has one writer, and closing ONE of the two
write-end fds must not deliver EOF.  The model counts ends off the fd
table, which `dup` is exactly the operation that makes wrong.  Both ends,
each refused the 10 Linux returns.
kernel: fs/file.c:dup,fd_install,do_dup2@v6.18.46 -/
theorem dup_of_a_pipe_reader_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    dup_spec 6 i dup_kinds_model o ↔ o = Unmodeled := by
  sys_norm

/-- The write end declines for the same reason.
kernel: fs/file.c:dup,fd_install,do_dup2@v6.18.46 -/
theorem dup_of_a_pipe_writer_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    dup_spec 7 i dup_kinds_model o ↔ o = Unmodeled := by
  sys_norm

/-- The 10 Linux returns for the write end is refused: with it admitted, a
later `close` of either fd would read EOF off the table where the pipe
still has a writer.
kernel: fs/file.c:dup,fd_install,do_dup2@v6.18.46 -/
theorem dup_of_a_pipe_writer_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup_spec 7 i dup_kinds_model (Ok (mkEffect 10 [] []) m' evs) := by
  sys_refute

/-! ## The dispatcher: syscall 23, and the fd's 32 bits

`SYSCALL_DEFINE1(dup, unsigned int, fildes)` (fs/file.c:1457, Linux
v6.18.46) reads the register's low half, so `dup(2^32 | 2)` is `dup(2)` and `dup(-1)` is
`dup(2^32 - 1)`, a number no table holds.  The table applies `fd32`; these
pins run through it. -/

/-- Syscall 23 on fd 4 reaches the directory arm: the copy lands at 5.
kernel: include/uapi/asm-generic/unistd.h:__NR_dup; fs/file.c:dup,alloc_fd,alloc_fdtable@v6.18.46 -/
theorem sysno_23_is_dup (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 23 [4, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        dup_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) dup_model []
        ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) dup_model [])
       ∨ o = Ok (mkEffect 5 [] []) (fixture_of (fds := (5, .FdDir) :: dup_fds) (fs := dup_fs)) []) := by
  sys_norm

/-- `dup(2^32 | 2)` IS `dup(2)`: the copy of channel 2 lands at 5.
probe: testing/syscall-check/tests/dup_spec.c#conform -- dup-trunc -/
theorem dup_fd_truncates_to_32_bits (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 23 [4294967298, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        dup_model o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) dup_model []
        ∨ o = Ok (mkEffect (errno_ret EMFILE) [] []) dup_model [])
       ∨ o = Ok (mkEffect 5 [] []) (fixture_of (fds := (5, .FdChannel 2) :: dup_fds) (fs := dup_fs)) []) := by
  sys_norm

/-- Truncation ALIASES rather than REJECTS: a model comparing the full
64-bit register would find no such fd and answer -EBADF, which
`SYSCALL_DEFINE1(dup, unsigned int, fildes)` never does — the wrapper's
cast (`__SYSCALL_DEFINEx`, arch/riscv/include/asm/syscall_wrapper.h:82-88,
through `__SC_CAST`, include/linux/syscalls.h:132) drops the high half
before `fget_raw` sees the number.  Read off the `iff` above: through the
table the fd is `fd32` of a register, not a numeral the lookup facts can
match in the first pass, so the admitted set is taken from the positive
pin and the forged answer compared against each member.
kernel: fs/file.c:dup,fget_raw; arch/riscv/include/asm/syscall_wrapper.h:__SYSCALL_DEFINEx; include/linux/syscalls.h:__SC_CAST@v6.18.46 -/
theorem dup_fd_2_pow_32_is_not_ebadf (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 23 [4294967298, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        dup_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  rw [dup_fd_truncates_to_32_bits]; sys_refute

/-- `dup(-1)` is -EBADF: `2^32 - 1` is open in no table.
probe: testing/syscall-check/tests/dup_spec.c#conform -- dup-trunc -/
theorem dup_minus_one_is_ebadf (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 23 [Z_to_bv 64 (-1), 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        dup_model o ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) dup_model [] := by
  sys_norm

/-- …and truncation invents no fd: a kernel claiming it duplicated fd -1
onto 3 is lying.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup#2:ret=3 -- dup-trunc -/
theorem dup_minus_one_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 23 [Z_to_bv 64 (-1), 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
                dup_model (Ok (mkEffect 3 [] []) m' evs) := by
  sys_refute

/-- The decline holds through the table too: `dup(2^32 | 3)` is `dup(3)`, the
file fd, and the 5 Linux returns for it is refused through `spec_table` as
it is on the spec — the one pin that puts a declining arm through the
table.  (Stated as a refutation: an `iff` with `Unmodeled` on a numbered
`mkInput` is a shape tools/check_decline_registers.py would read as a
number decline.)
kernel: fs/file.c:dup,fd_install@v6.18.46 -/
theorem dup_of_an_aliased_file_fd_success_rejected_through_the_table (m' : Model)
    (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 23 [4294967299, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        dup_model (Ok (mkEffect 5 [] []) m' evs) := by
  sys_refute

/-- …and so is -EBADF for it: the aliased fd is open.
kernel: fs/file.c:dup,fget_raw@v6.18.46 -/
theorem dup_of_an_aliased_file_fd_ebadf_rejected_through_the_table (m' : Model)
    (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 23 [4294967299, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        dup_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-! ## `ksys_dup3`, step 1: the flag word

`ksys_dup3` (fs/file.c:1399-1431, Linux v6.18.46, commit 1f99e9ab748f)
opens with `if ((flags & ~O_CLOEXEC) != 0) return -EINVAL;` (:1405-1406),
before the fds are compared (:1408), before the limit (:1411) and before
`oldfd` is looked up (:1416).  The pins take the neighbouring gates in
turn: each pair holds the earlier answer where the later condition also
holds. -/

/-- A bit outside O_CLOEXEC is -EINVAL on two open fds that would otherwise
succeed.
probe: testing/syscall-check/tests/dup_spec.c#conform -- d3-flags -/
theorem dup3_bad_flag_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 2 1 1 i dup_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) dup_model [] := by
  sys_norm

/-- …and a kernel ignoring the bad bit and returning `newfd` is refuted.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3:ret=1 -- d3-flags -/
theorem dup3_bad_flag_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 2 1 1 i dup_model (Ok (mkEffect 1 [] []) m' evs) := by
  sys_refute

/-- Rocq's other bit, 4 — `0o4`, outside `O_ACCMODE`'s two bits
(include/uapi/asm-generic/fcntl.h:18-21, Linux v6.18.46) and no open flag
on asm-generic — is -EINVAL all the same: `(flags & ~O_CLOEXEC) != 0`
(fs/file.c:1405) is a mask, not a list.
rocq-twin: dup3_ignores_o_cloexec_but_not_another_bit
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_bit_4_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 0 1 4 i dup_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) dup_model [] := by
  sys_norm

/-- The probe's second flag word, 2 — `O_RDWR`'s bit, no flag of `dup3`'s —
is -EINVAL as well, on the probe's pair.
probe: testing/syscall-check/tests/dup_spec.c#conform -- d3-flags -/
theorem dup3_bit_2_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 2 1 2 i dup_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) dup_model [] := by
  sys_norm


/-- O_CLOEXEC together with a bad bit is still -EINVAL: the accepted bit
does not excuse its neighbour.
probe: testing/syscall-check/tests/dup_spec.c#conform -- d3-flags -/
theorem dup3_o_cloexec_with_a_bad_bit_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 2 1 524289 i dup_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) dup_model [] := by
  sys_norm

/-- THE FLAG GATE BEATS THE FREE-NEWFD DECLINE: `dup3(2, 999, 1)`.  999 is
free, above `NR_OPEN_DEFAULT` and under `dup_model`'s limit of 1024, so
with a clean flag word the call would be declined; with the bad bit it is
-EINVAL, decided at :1405 before anything about 999 is read.
probe: testing/syscall-check/tests/dup_spec.c#conform -- d3-flags -/
theorem dup3_bad_flag_beats_the_free_newfd (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 2 999 1 i dup_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) dup_model [] := by
  sys_norm

/-- …so neither -EBADF nor a decline is the answer there.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3#4:ret=-EBADF -- d3-flags -/
theorem dup3_bad_flag_over_free_newfd_ebadf_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ dup3_spec 2 999 1 i dup_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- THE FLAG GATE BEATS A BAD OLDFD: `dup3(999, 1, 1)` is -EINVAL, not the
-EBADF the lookup at :1416-1418 would give.
probe: testing/syscall-check/tests/dup_spec.c#conform -- d3-flags -/
theorem dup3_bad_flag_beats_a_bad_oldfd (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 999 1 1 i dup_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) dup_model [] := by
  sys_norm

/-- …so the lookup's -EBADF is refused there.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3#5:ret=-EBADF -- d3-flags -/
theorem dup3_bad_flag_over_bad_oldfd_ebadf_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ dup3_spec 999 1 1 i dup_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- THE FLAG GATE BEATS THE KIND DECLINE: `dup3(3, 1, 1)` is -EINVAL,
decided at :1405 before `oldfd` is looked up at :1416, so the file fd the
model refuses to duplicate is never reached.  Declining here would be
fail-closed but wrong-shaped, as the equality pin below says of step 2.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_bad_flag_beats_the_kind_decline (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 3 1 1 i dup_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) dup_model [] := by
  sys_norm

/-- …so a kind-first model's decline is refused there.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_bad_flag_over_kind_decline_unmodeled_rejected (i : SyscallInput) :
    ¬ dup3_spec 3 1 1 i dup_model Unmodeled := by
  sys_refute

/-- THE FLAG GATE BEATS THE LIMIT: `dup3(0, 2000, 4)` is -EINVAL, where
2000 alone would be -EBADF at :1411-1412.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_bad_flag_beats_the_limit (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 0 2000 4 i dup_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) dup_model [] := by
  sys_norm

/-- …so the limit's -EBADF is refused there.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_bad_flag_over_limit_ebadf_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 0 2000 4 i dup_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- O_CLOEXEC is accepted and leaves the same state as flags 0: fd 1 stops
naming channel 1 and names channel 0.  `do_dup2` records the bit in the
table's `close_on_exec` bitmap alone (`__set_open_fd(fd, fdt, flags &
O_CLOEXEC)`, fs/file.c:1305, Linux v6.18.46), and nothing in the modeled
surface reads it back.  Rocq's pair; the probe's, `(2, 1)`, is pinned next.
rocq-twin: dup3_ignores_o_cloexec_but_not_another_bit
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_ignores_o_cloexec (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 0 1 524288 i dup_model o ↔
      o = Ok (mkEffect 1 [] [])
            (fixture_of (fds := [(1, .FdChannel 0), (0, .FdChannel 0), (2, .FdChannel 2),
                                 (3, .FdFile [102] 1), (4, .FdDir)]) (fs := dup_fs)) [] := by
  sys_norm

/-- …and not rejected: the -EINVAL of the bad-bit pins is refused here.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_o_cloexec_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 0 1 524288 i dup_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- The probe's `d3-cloexec` call, `dup3(2, 1, O_CLOEXEC)`: fd 1 becomes
channel 2, as with flags 0.
probe: testing/syscall-check/tests/dup_spec.c#conform -- d3-cloexec -/
theorem dup3_o_cloexec_on_the_probe_s_pair_installs (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 2 1 524288 i dup_model o ↔
      o = Ok (mkEffect 1 [] [])
            (fixture_of (fds := [(1, .FdChannel 2), (0, .FdChannel 0), (2, .FdChannel 2),
                                 (3, .FdFile [102] 1), (4, .FdDir)]) (fs := dup_fs)) [] := by
  sys_norm

/-- …and the probe's lie there, -EINVAL, is refused.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3:ret=-EINVAL -- d3-cloexec -/
theorem dup3_o_cloexec_on_the_probe_s_pair_einval_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ dup3_spec 2 1 524288 i dup_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- O_CLOEXEC onto a FREE `newfd` below the embedded table installs as flags
0 would: the branch where `__set_open_fd(fd, fdt, flags & O_CLOEXEC)`
(fs/file.c:1305, Linux v6.18.46) runs with nothing displaced.
kernel: fs/file.c:ksys_dup3,do_dup2,expand_files@v6.18.46 -/
theorem dup3_o_cloexec_onto_a_free_newfd_installs (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 0 7 524288 i dup_model o ↔
      o = Ok (mkEffect 7 [] []) (fixture_of (fds := (7, .FdChannel 0) :: dup_fds) (fs := dup_fs)) [] := by
  sys_norm


/-- THE FLAG WORD IS AN `int`: `SYSCALL_DEFINE3(dup3, unsigned int, oldfd,
unsigned int, newfd, int, flags)` (fs/file.c:1433, Linux v6.18.46) discards
the high half, so `dup3(2, 1, 2^32)` is `dup3(2, 1, 0)` and returns 1.  The truncation is
`dup3_flags_ok`'s own `flag32`, not the table's, so it shows on the spec.
probe: testing/syscall-check/tests/dup_spec.c#conform -- d3-flags-hi -/
theorem dup3_flags_high_half_is_discarded (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 2 1 4294967296 i dup_model o ↔
      o = Ok (mkEffect 1 [] [])
            (fixture_of (fds := [(1, .FdChannel 2), (0, .FdChannel 0), (2, .FdChannel 2),
                                 (3, .FdFile [102] 1), (4, .FdDir)]) (fs := dup_fs)) [] := by
  sys_norm

/-- A kernel that tested the flags on all 64 bits would answer -EINVAL;
refused.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3:ret=-EINVAL -- d3-flags-hi -/
theorem dup3_flags_high_half_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 2 1 4294967296 i dup_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- The high half is discarded and O_CLOEXEC is kept: `2^32 + O_CLOEXEC`
truncates to O_CLOEXEC alone and the call succeeds, the two facts
composed on one word.
kernel: fs/file.c:dup3,ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_flags_high_half_with_o_cloexec_installs (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 2 1 4295491584 i dup_model o ↔
      o = Ok (mkEffect 1 [] [])
            (fixture_of (fds := [(1, .FdChannel 2), (0, .FdChannel 0), (2, .FdChannel 2),
                                 (3, .FdFile [102] 1), (4, .FdDir)]) (fs := dup_fs)) [] := by
  sys_norm

/-- THE `int`'S SIGN BIT: `2^31` survives the truncation, is outside
O_CLOEXEC, and is -EINVAL — `(flags & ~O_CLOEXEC) != 0` (:1405) is a
truthiness test on the `int`, so a negative word is refused exactly as a
small one.  The one flag shape neither the probe nor the pins above reach.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_flags_sign_bit_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 2 1 2147483648 i dup_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) dup_model [] := by
  sys_norm

/-- …and the success a model reading the word as a signed `int` and
testing `flags > O_CLOEXEC` would give is refused.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_flags_sign_bit_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 2 1 2147483648 i dup_model (Ok (mkEffect 1 [] []) m' evs) := by
  sys_refute

/-! ## `ksys_dup3`, step 2: `oldfd == newfd`

`if (unlikely(oldfd == newfd)) return -EINVAL;` (fs/file.c:1408-1409, Linux
v6.18.46): unconditionally, and before any validity test.  This is where dup3 differs
from dup2, whose `SYSCALL_DEFINE2` (:1438-1455) answers the corner case
itself with `newfd` for an open fd and -EBADF for a closed one. -/

/-- `oldfd == newfd` is -EINVAL even for a FILE fd, which is a place the
model is deliberately MORE precise than its own decline: the equality test
precedes every kind test, as `ksys_dup3` orders them, so the entry that
carries an offset is never reached.  Declining here instead would be
fail-closed but wrong-shaped — Linux answers -EINVAL whatever the fd is.
rocq-twin: dup3_eq_beats_the_file_fd_decline
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_eq_beats_the_file_fd_decline (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 3 3 0 i dup_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) dup_model [] := by
  sys_norm

/-- …and dup2's answer, `newfd` back, is refused: dup3 is not dup2.  Rocq's
conjunct, carried here, is the file fd's pair and its 3; the probe's pair
is `(2, 2, 0)` and its lie a 2, pinned next.
rocq-twin: dup3_eq_beats_the_file_fd_decline
kernel: fs/file.c:ksys_dup3,dup2@v6.18.46 -/
theorem dup3_eq_newfd_back_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 3 3 0 i dup_model (Ok (mkEffect 3 [] []) m' evs) := by
  sys_refute

/-- The probe's pair, `dup3(2, 2, 0)`: -EINVAL at :1408 for an open channel
onto itself.
probe: testing/syscall-check/tests/dup_spec.c#conform -- d3-eq -/
theorem dup3_eq_on_the_probe_s_pair_is_einval (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 2 2 0 i dup_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) dup_model [] := by
  sys_norm

/-- …and dup2's `newfd` back, the probe's lie, is refused there.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3#1:ret=2 -- d3-eq -/
theorem dup3_eq_on_the_probe_s_pair_newfd_back_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ dup3_spec 2 2 0 i dup_model (Ok (mkEffect 2 [] []) m' evs) := by
  sys_refute

/-- …as is the 1 the probe's `arg1=2` mutation claims for it: `d3-basic`'s
`dup3(2, 1, 0)` rewritten to `dup3(2, 2, 0)` while still answering 1.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3:arg1=2 -- d3-basic -/
theorem dup3_eq_on_the_probe_s_pair_one_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 2 2 0 i dup_model (Ok (mkEffect 1 [] []) m' evs) := by
  sys_refute


/-- The equality is tested BEFORE `oldfd`'s validity: a closed fd onto
itself — the probe's `dup3(999, 999, 0)` — is -EINVAL, not the lookup's
-EBADF.
probe: testing/syscall-check/tests/dup_spec.c#conform -- d3-eq -/
theorem dup3_eq_beats_a_bad_oldfd (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 999 999 0 i dup_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) dup_model [] := by
  sys_norm

/-- …so the lookup's -EBADF is refused for the closed pair.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3#2:ret=-EBADF -- d3-eq -/
theorem dup3_eq_on_closed_fd_ebadf_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
        ¬ dup3_spec 999 999 0 i dup_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- …and BEFORE the free-`newfd` decline: 100 onto itself is -EINVAL at
:1408, where a model that looked `newfd` up first would decline the free
slot above the embedded table — fail-closed but wrong-shaped.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_eq_beats_the_free_newfd_decline (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 100 100 0 i dup_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) dup_model [] := by
  sys_norm

/-- …so that decline is refused there.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_eq_over_free_newfd_unmodeled_rejected (i : SyscallInput) :
    ¬ dup3_spec 100 100 0 i dup_model Unmodeled := by
  sys_refute

/-- …and BEFORE the RLIMIT_NOFILE gate: a huge fd onto itself is -EINVAL,
not the -EBADF of :1411-1412.
probe: testing/syscall-check/tests/dup_spec.c#conform -- d3-eq -/
theorem dup3_eq_beats_the_limit (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 2147483648 2147483648 0 i dup_model o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) dup_model [] := by
  sys_norm

/-- …so the limit's -EBADF is refused for the huge pair.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3#4:ret=-EBADF -- d3-eq -/
theorem dup3_eq_over_limit_ebadf_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 2147483648 2147483648 0 i dup_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-! ## `ksys_dup3`, step 3: `newfd >= rlimit(RLIMIT_NOFILE)`

`if (newfd >= rlimit(RLIMIT_NOFILE)) return -EBADF;` (fs/file.c:1411-1412,
Linux v6.18.46), before `expand_files` (:1415) and before `oldfd` is looked
up (:1416).
The model answers it from `State.m_nofile`, the soft limit the run was
launched with; `dup_model` carries `State.default_nofile`, 1024, so 2000
is over it and 999 under. -/

/-- The gate: 2000, Rocq's value, is over `dup_model`'s limit, so -EBADF
with nothing changed, from an open channel oldfd.  The probe's value is
2^31, pinned below.
rocq-twin: dup3_over_the_limit_is_ebadf_before_the_oldfd_lookup
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_over_the_limit_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 0 2000 0 i dup_model o ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) dup_model [] := by
  sys_norm

/-- …and its PLACEMENT: -EBADF even for an `oldfd` whose kind the model
refuses to duplicate — 3 is a file — because `ksys_dup3` tests the limit
before it looks `oldfd` up.  Reorder the spec to test the kind first and
this `iff` turns into `Unmodeled`.
rocq-twin: dup3_over_the_limit_is_ebadf_before_the_oldfd_lookup
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_over_the_limit_is_ebadf_before_the_oldfd_lookup (i : SyscallInput)
    (o : outcome SyscallEffect) :
    dup3_spec 3 2000 0 i dup_model o ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) dup_model [] := by
  sys_norm

/-- THE PROBE'S VALUE: `HUGE_FD` is 2^31, above `sysctl_nr_open_max`
(2^31 - 64, fs/file.c:100-101, Linux v6.18.46) and so above every soft
limit `do_prlimit` (kernel/sys.c:1513-1515) can install, not only
`dup_model`'s 1024.  `dup3(2, 2^31, 0)` is -EBADF at :1411-1412; a gate
reading the narrowed fd as a signed `int` would let it through to the
free-`newfd` decline instead.
probe: testing/syscall-check/tests/dup_spec.c#conform -- d3-huge -/
theorem dup3_at_two_pow_31_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 2 2147483648 0 i dup_model o ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) dup_model [] := by
  sys_norm

/-- …so the decline a signed reading would give there is refused.
kernel: fs/file.c:ksys_dup3,dup3@v6.18.46 -/
theorem dup3_at_two_pow_31_decline_rejected (i : SyscallInput) :
    ¬ dup3_spec 2 2147483648 0 i dup_model Unmodeled := by
  sys_refute

/-- …and from the file fd at the probe's value, `dup3(3, 2^31, 0)`: -EBADF
before the kind is read.
probe: testing/syscall-check/tests/dup_spec.c#conform -- d3-huge-file -/
theorem dup3_at_two_pow_31_from_a_file_fd_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 3 2147483648 0 i dup_model o ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) dup_model [] := by
  sys_norm


/-- Nothing succeeds past the limit: `newfd` back, Rocq's conjunct…
rocq-twin: dup3_over_the_limit_is_ebadf_before_the_oldfd_lookup
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_over_the_limit_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 0 2000 0 i dup_model (Ok (mkEffect 2000 [] []) m' evs) := by
  sys_refute

/-- …and the probe's own lie, a 1 handed back past the limit, at the probe's
own value.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3:ret=1 -- d3-huge -/
theorem dup3_over_the_limit_one_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 2 2147483648 0 i dup_model (Ok (mkEffect 1 [] []) m' evs) := by
  sys_refute

/-- Step 3 is -EBADF outright: `expand_files`' -EMFILE (:310-311) never
surfaces, since :1411 returns before :1415 is reached.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3:ret=-EMFILE -- d3-huge -/
theorem dup3_over_the_limit_emfile_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 2 2147483648 0 i dup_model (Ok (mkEffect (errno_ret EMFILE) [] []) m' evs) := by
  sys_refute

/-- The limit answer is -EBADF, not -EINVAL.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3:ret=-EINVAL -- d3-huge -/
theorem dup3_over_the_limit_einval_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 2 2147483648 0 i dup_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …still -EBADF from the file oldfd, and not the -EINVAL a model that
reached the kind test and misfiled its answer might give.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3:ret=-EINVAL -- d3-huge-file -/
theorem dup3_over_the_limit_from_file_einval_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
        ¬ dup3_spec 3 2147483648 0 i dup_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and not the kind-first model's decline: the limit is read at :1411
before `oldfd` is looked up at :1416, so the file fd is never reached.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_over_the_limit_from_file_unmodeled_rejected (i : SyscallInput) :
    ¬ dup3_spec 3 2000 0 i dup_model Unmodeled := by
  sys_refute

/-! ### The limit is READ FROM THE RUN, not written into the spec

The pair that says so: the same input against `dup_model` and against
`dup_model_nofile4`, so only the limit can separate the answers.  Replace
`dup3_newfd_under_limit`'s `m_nofile m` with any constant and one of the
two sides breaks. -/

/-- fd 5 is free and below `NR_OPEN_DEFAULT`, so nothing but the limit can
separate the two answers: under `State.default_nofile` the free-`newfd`
arm installs it, and under 4 the gate answers first.
rocq-twin: dup3_free_newfd_is_decided_by_the_run_s_limit
kernel: fs/file.c:ksys_dup3,expand_files@v6.18.46 -/
theorem dup3_free_newfd_under_default_limit_installs (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 0 5 0 i dup_model o ↔
      o = Ok (mkEffect 5 [] []) (fixture_of (fds := (5, .FdChannel 0) :: dup_fds) (fs := dup_fs)) [] := by
  sys_norm

/-- …and under a soft limit of 4 the same call is -EBADF: 5 is at or above
`rlimit(RLIMIT_NOFILE)` (fs/file.c:1411-1412).
rocq-twin: dup3_free_newfd_is_decided_by_the_run_s_limit
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_free_newfd_under_limit_4_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 0 5 0 i dup_model_nofile4 o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) dup_model_nofile4 [] := by
  sys_norm

/-- …with the installation the default-limit model admits refused there.
rocq-twin: dup3_free_newfd_is_decided_by_the_run_s_limit
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_free_newfd_under_limit_4_success_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ dup3_spec 0 5 0 i dup_model_nofile4 (Ok (mkEffect 5 [] []) m' evs) := by
  sys_refute

/-- THE GATE BEATS THE DESCRIPTOR THE PROCESS ALREADY HOLDS, which is the
case a spec that only looked the fd up would answer wrongly: fd 4 is open
(the directory fd) and sits AT the limit, so dup3 onto it is -EBADF where
such a spec would have returned 4.  fd 3 beside it, open and under the
limit, is the ordinary replacement — so the pair also pins the comparison
as STRICT, since `newfd <= limit` would make 4 succeed.
rocq-twin: dup3_limit_beats_an_fd_the_process_holds
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_under_limit_4_replaces_fd_3 (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 0 3 0 i dup_model_nofile4 o ↔
      o = Ok (mkEffect 3 [] [])
            (with_nofile (Z_to_bv 64 4)
              (fixture_of (fds := [(3, .FdChannel 0), (0, .FdChannel 0), (1, .FdChannel 1),
                                   (2, .FdChannel 2), (4, .FdDir)]) (fs := dup_fs))) [] := by
  sys_norm

/-- fd 4, open and AT the limit: -EBADF.
rocq-twin: dup3_limit_beats_an_fd_the_process_holds
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_limit_beats_an_fd_the_process_holds (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 0 4 0 i dup_model_nofile4 o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) dup_model_nofile4 [] := by
  sys_norm

/-- …and the 4 a lookup-only spec would return is refused.
rocq-twin: dup3_limit_beats_an_fd_the_process_holds
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_at_limit_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
        ¬ dup3_spec 0 4 0 i dup_model_nofile4 (Ok (mkEffect 4 [] []) m' evs) := by
  sys_refute

/-- A closed `oldfd` onto the open fd AT the limit: -EBADF from the gate
(:1411-1412) before the lookup (:1416-1418) could answer the same errno,
with the table unchanged — the two gates agree on the errno, and the
post-state is what the pin fixes.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_closed_oldfd_onto_an_open_fd_at_the_limit_is_ebadf (i : SyscallInput)
    (o : outcome SyscallEffect) :
    dup3_spec 9 4 0 i dup_model_nofile4 o
      ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) dup_model_nofile4 [] := by
  sys_norm

/-! ### The registers the gate rests on

`dup3_newfd_under_limit` reads a value that stays put only while nothing
modeled writes it.  The syscalls that can — `setrlimit` (164, whose compat
twin shares the number: `__SC_COMP`, include/uapi/asm-generic/unistd.h:440)
and `prlimit64` (261), all through `do_prlimit` (kernel/sys.c:1500, Linux
v6.18.46, the store at :1536) — are held off it two ways.  `setrlimit`
has no arm in the Lean table, and the first theorem holds that absence in
the number-decline shape tools/check_decline_registers.py reads, so
porting it collides there instead of silently invalidating the gate.
`prlimit64` HAS an arm since the Kernel/Sys port, and it declines every
resource but RLIMIT_CORE — `Kernel.Sys.prlimit64_spec`'s second gate,
pinned as `Checks.Cases.Kernel.Sys.prlimit64_other_resources_are_unmodeled`
— so the second theorem is a SHAPE decline of a modeled number: named so
the register reader does not take it for a claim that 261 has no arm,
and still what keeps `m_nofile` unwritten.  Rocq registers its
`setrlimit` decline the same way (`Checks.ProcessCreation`), with
`getrlimit` (163) beside it for the harness's sake and not this gate's —
it writes nothing (kernel/sys.c:1563, v6.18.46). -/

/-- `setrlimit` (164) declines: no arm writes `m_nofile`.
kernel: include/uapi/asm-generic/unistd.h:__NR_setrlimit; kernel/sys.c:setrlimit,do_prlimit@v6.18.46 -/
theorem sysno_164_is_unmodeled (m : Model) :
    syscall_spec (SyscallInput.mkInput 164 [7, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m
      Unmodeled := rfl

/-- `prlimit64(0, RLIMIT_NOFILE, NULL, NULL)` (261) declines: the other
writer of the soft limit answers no resource but RLIMIT_CORE.
kernel: include/uapi/asm-generic/unistd.h:__NR_prlimit64; kernel/sys.c:prlimit64,do_prlimit@v6.18.46 -/
theorem sysno_261_nofile_declines (m : Model) :
    syscall_spec (SyscallInput.mkInput 261 [0, 7, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m
      Unmodeled := rfl

/-! ## `ksys_dup3`, steps 4 and 5: `expand_files`, then the `oldfd` lookup

`expand_files(files, newfd)` is called (fs/file.c:1415, Linux v6.18.46) but
its result
is not read until after `files_lookup_fd_locked(files, oldfd)` (:1416)
has been tested (:1417-1418, `goto Ebadf`).  So a missing `oldfd` is
-EBADF whatever `newfd` is, and beats the allocator's -ENOMEM (:1422) and
the -EMFILE `ksys_dup3` rewrites to -EBADF (:1420-1421). -/

/-- A closed `oldfd` onto an open `newfd` is -EBADF: the probe's
`dup3(999, 1, 0)`.
probe: testing/syscall-check/tests/dup_spec.c#conform -- d3-badold -/
theorem dup3_bad_oldfd_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 999 1 0 i dup_model o ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) dup_model [] := by
  sys_norm

/-- A bad oldfd cannot succeed.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3:ret=1 -- d3-badold -/
theorem dup3_bad_oldfd_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
        ¬ dup3_spec 999 1 0 i dup_model (Ok (mkEffect 1 [] []) m' evs) := by
  sys_refute

/-- `expand_files` runs first but its error is read AFTER the lookup: a
kernel answering -ENOMEM for a bad oldfd has read :1419 before :1417.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3:ret=-ENOMEM -- d3-badold -/
theorem dup3_bad_oldfd_enomem_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
        ¬ dup3_spec 999 1 0 i dup_model (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-- A closed `oldfd` onto a huge `newfd` is -EBADF from the limit gate,
which fires first; the probe's pair `(999, 2^31)` is -EBADF from both steps
and -EINVAL from neither.
probe: testing/syscall-check/tests/dup_spec.c#conform -- d3-badold -/
theorem dup3_bad_oldfd_over_the_limit_is_ebadf (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 999 2147483648 0 i dup_model o ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) dup_model [] := by
  sys_norm

/-- That pair is -EBADF, not -EINVAL.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3#2:ret=-EINVAL -- d3-badold -/
theorem dup3_bad_oldfd_over_the_limit_einval_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
        ¬ dup3_spec 999 2147483648 0 i dup_model (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- THE OLDFD LOOKUP BEATS THE FREE-NEWFD DECLINE: `dup3(9, 100, 0)`.  100
is free and above `NR_OPEN_DEFAULT`, the shape the model declines for an
open oldfd; with a closed oldfd it is a determined -EBADF, because :1417
is tested before :1419 reads what `expand_files(files, 100)` did.  A model
that looked `newfd` up first would decline here.
kernel: fs/file.c:ksys_dup3,expand_files@v6.18.46 -/
theorem dup3_bad_oldfd_beats_the_free_newfd_decline (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 9 100 0 i dup_model o ↔ o = Ok (mkEffect (errno_ret EBADF) [] []) dup_model [] := by
  sys_norm

/-- …so the decline a newfd-first model would give is refused there.
kernel: fs/file.c:ksys_dup3,expand_files@v6.18.46 -/
theorem dup3_bad_oldfd_over_free_newfd_unmodeled_rejected (i : SyscallInput) :
    ¬ dup3_spec 9 100 0 i dup_model Unmodeled := by
  sys_refute

/-! ## `do_dup2`: the target is replaced, and the return is `newfd`

`do_dup2` (fs/file.c:1265-1316, Linux v6.18.46) takes the file at `newfd`
(:1300), stores
the new one with a reference of its own (:1303-1304), records the
close-on-exec bit (:1305), closes what was there with the return value of
`filp_close` discarded (:1308-1309; fs/open.c:1558-1566, v6.18.46) and
returns `fd`
(:1311).  Its one errno, -EBUSY (:1301-1302, :1313-1315), needs a slot
reserved but not yet installed by another thread of a shared table, which
no modeled run has. -/

/-- dup3 returns the fd it was GIVEN, silently closing what was there: fd 1
stops naming channel 1 and names channel 0, so it stops being WRITABLE —
which is what the probe's `d3-direction` mode asserts against a real
kernel.  That the entry moved is model-internal state no return value
reveals.
rocq-twin: dup3_replaces_the_target_and_returns_it
probe: testing/syscall-check/tests/dup_spec.c#conform --stdin abcdef -- d3-direction -/
theorem dup3_replaces_the_target_and_returns_it (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 0 1 0 i dup_model o ↔
      o = Ok (mkEffect 1 [] [])
            (fixture_of (fds := [(1, .FdChannel 0), (0, .FdChannel 0), (2, .FdChannel 2),
                                 (3, .FdFile [102] 1), (4, .FdDir)]) (fs := dup_fs)) [] := by
  sys_norm

/-- The fd `dup` would have chosen, 5, is refused: dup3 does not allocate.
rocq-twin: dup3_replaces_the_target_and_returns_it
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_lowest_free_fd_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 0 1 0 i dup_model (Ok (mkEffect 5 [] []) m' evs) := by
  sys_refute

/-- The probe's `d3-basic`, `dup3(2, 1, 0)`: fd 1 becomes channel 2.
probe: testing/syscall-check/tests/dup_spec.c#conform -- d3-basic -/
theorem dup3_2_onto_1_replaces (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 2 1 0 i dup_model o ↔
      o = Ok (mkEffect 1 [] [])
            (fixture_of (fds := [(1, .FdChannel 2), (0, .FdChannel 0), (2, .FdChannel 2),
                                 (3, .FdFile [102] 1), (4, .FdDir)]) (fs := dup_fs)) [] := by
  sys_norm

/-- The fd it was given is the only admissible return.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3:ret+1 -- d3-basic -/
theorem dup3_newfd_plus_one_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 2 1 0 i dup_model (Ok (mkEffect 2 [] []) m' evs) := by
  sys_refute

/-- Both fds are open: -EBADF is refused.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3:ret=-EBADF -- d3-basic -/
theorem dup3_open_pair_ebadf_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 2 1 0 i dup_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- dup3 IS DETERMINISTIC on an open `newfd`: no table growth is needed
(`expand_files` returns at :299-300 for a slot the table covers), so
-ENOMEM is refused…
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3:ret=-ENOMEM -- d3-basic -/
theorem dup3_open_pair_enomem_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 2 1 0 i dup_model (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-- …and -EMFILE, which `ksys_dup3` would have rewritten to -EBADF anyway
(:1420-1421)…
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3:ret=-EMFILE -- d3-basic -/
theorem dup3_open_pair_emfile_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 2 1 0 i dup_model (Ok (mkEffect (errno_ret EMFILE) [] []) m' evs) := by
  sys_refute

/-- …and -EBUSY, which needs a second thread in a shared table…
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3:ret=-EBUSY -- d3-basic -/
theorem dup3_open_pair_ebusy_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 2 1 0 i dup_model (Ok (mkEffect (errno_ret EBUSY) [] []) m' evs) := by
  sys_refute

/-- …and -EINTR: nothing here is interruptible.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3:ret=-EINTR -- d3-basic -/
theorem dup3_open_pair_eintr_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 2 1 0 i dup_model (Ok (mkEffect (errno_ret EINTR) [] []) m' evs) := by
  sys_refute

/-- A directory fd installed at fd 1: the entry is copied, as `dup` copies
it.  The probe's `d3-dir` holds its directory at 3 and this fixture at 4,
so the probe's `dup3(3, 1, 0)` is not restated.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_directory_onto_1_replaces (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 4 1 0 i dup_model o ↔
      o = Ok (mkEffect 1 [] [])
            (fixture_of (fds := [(1, .FdDir), (0, .FdChannel 0), (2, .FdChannel 2),
                                 (3, .FdFile [102] 1), (4, .FdDir)]) (fs := dup_fs)) [] := by
  sys_norm

/-- A FILE fd may be the TARGET: it is simply closed, as `filp_close`
(:1308-1309) closes it with the result discarded, and the channel takes
its number.  The offset it carried is gone with it, so nothing is shared.
probe: testing/syscall-check/tests/dup_spec.c#conform -- d3-file-new -/
theorem dup3_onto_a_file_fd_replaces (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 2 3 0 i dup_model o ↔
      o = Ok (mkEffect 3 [] [])
            (fixture_of (fds := [(3, .FdChannel 2), (0, .FdChannel 0), (1, .FdChannel 1),
                                 (2, .FdChannel 2), (4, .FdDir)]) (fs := dup_fs)) [] := by
  sys_norm

/-- Displacing it cannot fail.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3:ret=-EBADF -- d3-file-new -/
theorem dup3_onto_a_file_fd_ebadf_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 2 3 0 i dup_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- A FILE fd as the SOURCE declines, for `dup`'s reason: `get_file`
(:1303) makes fd 1 a second reference to the file's one `f_pos`.  Linux
answers 1; refused.
probe: testing/syscall-check/tests/dup_spec.c#fail-closed -- d3-file-old -/
theorem dup3_from_a_file_fd_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 3 1 0 i dup_model o ↔ o = Unmodeled := by
  sys_norm

/-- The 1 Linux returns from a file source is refused.
probe: testing/syscall-check/tests/dup_spec.c#fail-closed -- d3-file-old -/
theorem dup3_from_a_file_fd_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 3 1 0 i dup_model (Ok (mkEffect 1 [] []) m' evs) := by
  sys_refute

/-- The kinds Rocq's fixture lacks, through `dup3`.  /dev/null as the
SOURCE is copied onto fd 1: `do_dup2`'s `get_file` (:1303) shares a
`struct file` no modeled arm can tell apart from a copy, `null_lseek`
(drivers/char/mem.c:561) holding `f_pos` at 0.
kernel: fs/file.c:ksys_dup3,do_dup2; drivers/char/mem.c:null_lseek@v6.18.46 -/
theorem dup3_from_devnull_replaces (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 8 1 0 i dup_kinds_model o ↔
      o = Ok (mkEffect 1 [] [])
            (fixture_of (fds := [(1, .FdDevNull true true), (0, .FdChannel 0), (2, .FdChannel 2),
                                 (3, .FdFile [102] 1), (4, .FdDir), (5, .FdSocket .SkFresh),
                                 (6, .FdPipe 0 false), (7, .FdPipe 0 true), (8, .FdDevNull true true),
                                 (9, .FdUrandom)])
                        (pipes := [(0, ([], 0))]) (fs := dup_fs)) [] := by
  sys_norm

/-- /dev/urandom as the SOURCE is copied onto fd 1 for `dup`'s reason.
kernel: fs/file.c:ksys_dup3,do_dup2; drivers/char/random.c:urandom_read_iter; fs/read_write.c:noop_llseek@v6.18.46 -/
theorem dup3_from_urandom_replaces (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 9 1 0 i dup_kinds_model o ↔
      o = Ok (mkEffect 1 [] [])
            (fixture_of (fds := [(1, .FdUrandom), (0, .FdChannel 0), (2, .FdChannel 2),
                                 (3, .FdFile [102] 1), (4, .FdDir), (5, .FdSocket .SkFresh),
                                 (6, .FdPipe 0 false), (7, .FdPipe 0 true), (8, .FdDevNull true true),
                                 (9, .FdUrandom)])
                        (pipes := [(0, ([], 0))]) (fs := dup_fs)) [] := by
  sys_norm

/-- …and a model grouping the random device with the declining kinds is
refuted here as on `dup`'s path: the decline is refused where Linux copies.
kernel: fs/file.c:ksys_dup3,do_dup2; drivers/char/random.c:urandom_read_iter@v6.18.46 -/
theorem dup3_from_urandom_decline_rejected (i : SyscallInput) :
    ¬ dup3_spec 9 1 0 i dup_kinds_model Unmodeled := by
  sys_refute

/-- A socket as the SOURCE declines, for `dup`'s reason.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_from_a_socket_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 5 1 0 i dup_kinds_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the 1 Linux returns there is refused.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_from_a_socket_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 5 1 0 i dup_kinds_model (Ok (mkEffect 1 [] []) m' evs) := by
  sys_refute

/-- A pipe end as the SOURCE declines through `dup3` too: `do_dup2`'s
`get_file` (:1303) would make fd 1 a second reference to the write end
without moving `pipe->writers`, which the model cannot count off the
table.  Linux answers 1.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_from_a_pipe_writer_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 7 1 0 i dup_kinds_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the 1 Linux returns there is refused.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_from_a_pipe_writer_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
        ¬ dup3_spec 7 1 0 i dup_kinds_model (Ok (mkEffect 1 [] []) m' evs) := by
  sys_refute

/-- The read end as the SOURCE declines through `dup3` for the same reason,
`pipe->readers` (fs/pipe.c:731, Linux v6.18.46) being the count a second
reference would leave unmoved.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_from_a_pipe_reader_is_unmodeled (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 6 1 0 i dup_kinds_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the 1 Linux returns there is refused.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_from_a_pipe_reader_success_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 6 1 0 i dup_kinds_model (Ok (mkEffect 1 [] []) m' evs) := by
  sys_refute


/-- A pipe end as the TARGET is displaced: the model drops the entry as
`close` would.  That is right because `filp_close` (:1308-1309;
fs/open.c:1558-1566, Linux v6.18.46) drops a reference through
`fput_close` (:1563), and `pipe_release` (fs/pipe.c:724-746) runs when the
LAST reference goes (`__fput_deferred`, fs/file_table.c:555-577, reached
from :621-622) — at once here, and only because `dup_modeled_entry` never lets a pipe end hold two
references.  So the writer count moves as the table's scan says it does,
and relaxing the `FdPipe` arm re-opens this pin.
kernel: fs/file.c:ksys_dup3,do_dup2; fs/open.c:filp_close; fs/pipe.c:pipe_release@v6.18.46 -/
theorem dup3_onto_a_pipe_end_replaces (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 0 7 0 i dup_kinds_model o ↔
      o = Ok (mkEffect 7 [] [])
            (fixture_of (fds := [(7, .FdChannel 0), (0, .FdChannel 0), (1, .FdChannel 1),
                                 (2, .FdChannel 2), (3, .FdFile [102] 1), (4, .FdDir),
                                 (5, .FdSocket .SkFresh), (6, .FdPipe 0 false),
                                 (8, .FdDevNull true true), (9, .FdUrandom)])
                        (pipes := [(0, ([], 0))]) (fs := dup_fs)) [] := by
  sys_norm

/-! ## The free `newfd`: below the embedded table it is installed, at or
above it the call declines

`expand_files(files, nr)` (fs/file.c:288-320, Linux v6.18.46) returns 0 at
once when `nr < fdt->max_fds` (:299-300), and the embedded table has
`NR_OPEN_DEFAULT` = `BITS_PER_LONG` = 64 slots (include/linux/fdtable.h:24,
:56, v6.18.46), a floor on
`max_fds`.  So a free `newfd` below 64 is installed with nothing
allocated; at or above 64 the answer turns on the live `max_fds` and on
`sysctl_nr_open` (:310-311), neither of which the model carries. -/

/-- A FREE `newfd` below `NR_OPEN_DEFAULT` is installed at the number
given, not at the lowest free one — which is the difference between dup3
and dup, and is why the refutation beside it claims fd 5, the number `dup`
would have answered.  `dup_model`'s limit is `State.default_nofile`, so 7
is under it.  The probe's `d3-newfree` closes fd 1 and dup3s onto it; that
table is `dup_model_closed1`, pinned after the 7 and 63 boundaries.
rocq-twin: dup3_takes_a_free_newfd_below_the_embedded_table
kernel: fs/file.c:ksys_dup3,expand_files,do_dup2@v6.18.46 -/
theorem dup3_takes_a_free_newfd_below_the_embedded_table (i : SyscallInput)
    (o : outcome SyscallEffect) :
    dup3_spec 0 7 0 i dup_model o ↔
      o = Ok (mkEffect 7 [] []) (fixture_of (fds := (7, .FdChannel 0) :: dup_fds) (fs := dup_fs)) [] := by
  sys_norm

/-- …and 5 is refused.
rocq-twin: dup3_takes_a_free_newfd_below_the_embedded_table
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_free_newfd_lowest_free_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 0 7 0 i dup_model (Ok (mkEffect 5 [] []) m' evs) := by
  sys_refute

/-- Nothing on that path allocates: -ENOMEM is unreachable, not merely
unobserved, and refused.
kernel: fs/file.c:ksys_dup3,expand_files@v6.18.46 -/
theorem dup3_free_newfd_enomem_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 0 7 0 i dup_model (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-- …as is -EMFILE, which `ksys_dup3` would have rewritten to -EBADF anyway.
kernel: fs/file.c:ksys_dup3,expand_files@v6.18.46 -/
theorem dup3_free_newfd_emfile_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 0 7 0 i dup_model (Ok (mkEffect (errno_ret EMFILE) [] []) m' evs) := by
  sys_refute

/-- …and -EBUSY, the one errno of this path that is not structurally
impossible in the kernel: `do_dup2`'s `!tofree && fd_is_open(fd, fdt)`
(:1301-1302) needs a slot reserved by ANOTHER task of a shared table
between `__set_open_fd` (:606) and `fd_install` (:652) — a race no
sequential model runs whatever arms its table gains: `clone` is modeled
parent-side only and no `Run.config` holds a second machine
(bugs/clone-child-not-in-the-model.md).  Refused.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_free_newfd_ebusy_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 0 7 0 i dup_model (Ok (mkEffect (errno_ret EBUSY) [] []) m' evs) := by
  sys_refute

/-- …and -EBADF: 7 is under the limit and oldfd is open.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem dup3_free_newfd_ebadf_rejected (i : SyscallInput) (m' : Model) (evs : List event) :
    ¬ dup3_spec 0 7 0 i dup_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- THE PROBE'S `d3-newfree`: after `close(1)`, `dup3(2, 1, 0)` installs
channel 2 at the freed standard descriptor — the same triple as `d3-basic`,
differing only in whether `newfd` is open, which is what makes it the free
arm's case rather than the replacement's.
probe: testing/syscall-check/tests/dup_spec.c#conform -- d3-newfree -/
theorem dup3_onto_the_closed_fd_1_installs (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 2 1 0 i dup_model_closed1 o ↔
      o = Ok (mkEffect 1 [] [])
            (fixture_of (fds := (1, .FdChannel 2) :: dup_fds_closed1) (fs := dup_fs)) [] := by
  sys_norm

/-- `oldfd` back, the probe's lie: the fd it was given is the only return.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3:ret=0 -- d3-newfree -/
theorem dup3_onto_the_closed_fd_1_oldfd_back_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ dup3_spec 2 1 0 i dup_model_closed1 (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- Nothing on that path allocates: -ENOMEM is refused…
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3:ret=-ENOMEM -- d3-newfree -/
theorem dup3_onto_the_closed_fd_1_enomem_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ dup3_spec 2 1 0 i dup_model_closed1 (Ok (mkEffect (errno_ret ENOMEM) [] []) m' evs) := by
  sys_refute

/-- …as is -EMFILE, which `ksys_dup3` would have rewritten to -EBADF anyway…
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3:ret=-EMFILE -- d3-newfree -/
theorem dup3_onto_the_closed_fd_1_emfile_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ dup3_spec 2 1 0 i dup_model_closed1 (Ok (mkEffect (errno_ret EMFILE) [] []) m' evs) := by
  sys_refute

/-- …and -EBUSY, another task's reserved slot…
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3:ret=-EBUSY -- d3-newfree -/
theorem dup3_onto_the_closed_fd_1_ebusy_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ dup3_spec 2 1 0 i dup_model_closed1 (Ok (mkEffect (errno_ret EBUSY) [] []) m' evs) := by
  sys_refute

/-- …and -EBADF: 1 is under the limit and `oldfd` is open.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3:ret=-EBADF -- d3-newfree -/
theorem dup3_onto_the_closed_fd_1_ebadf_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ dup3_spec 2 1 0 i dup_model_closed1 (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute


/-- A FREE `newfd` at or above the embedded table is declined for every
claimed return.  Linux decides 100 here out of the descriptor table's
current `max_fds` and the `sysctl_nr_open` ceiling, neither of which the
model carries: it may return 100, or -EBADF (from the -EMFILE `ksys_dup3`
rewrites), or -ENOMEM.  Three answers, no way to choose.  Rocq's oldfd is
0; the probe's `dup3(2, 100, 0)` follows.
rocq-twin: dup3_declines_a_free_newfd_above_the_embedded_table
kernel: fs/file.c:ksys_dup3,expand_files,alloc_fdtable@v6.18.46 -/
theorem dup3_declines_a_free_newfd_above_the_embedded_table (i : SyscallInput)
    (o : outcome SyscallEffect) :
    dup3_spec 0 100 0 i dup_model o ↔ o = Unmodeled := by
  sys_norm

/-- The 100 a default kernel returns is refused…
kernel: fs/file.c:ksys_dup3,expand_files@v6.18.46 -/
theorem dup3_free_newfd_above_the_table_success_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ dup3_spec 0 100 0 i dup_model (Ok (mkEffect 100 [] []) m' evs) := by
  sys_refute

/-- …and so is the -EBADF a lowered `sysctl_nr_open` produces: the decline
precedes the return.
kernel: fs/file.c:ksys_dup3,expand_files@v6.18.46 -/
theorem dup3_free_newfd_above_the_table_ebadf_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ dup3_spec 0 100 0 i dup_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- The probe's `d3-newmid`, `dup3(2, 100, 0)`: declined for every claimed
return.
probe: testing/syscall-check/tests/dup_spec.c#fail-closed -- d3-newmid -/
theorem dup3_declines_the_probe_s_free_newfd_100 (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 2 100 0 i dup_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the 100 a default kernel returns is refused…
probe: testing/syscall-check/tests/dup_spec.c#fail-closed -- d3-newmid -/
theorem dup3_probe_s_free_newfd_100_success_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ dup3_spec 2 100 0 i dup_model (Ok (mkEffect 100 [] []) m' evs) := by
  sys_refute

/-- …so is the -EBADF a lowered `sysctl_nr_open` produces…
probe: testing/syscall-check/tests/dup_spec.c#fail-closed --mutate dup3:ret=-EBADF -- d3-newmid -/
theorem dup3_probe_s_free_newfd_100_ebadf_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ dup3_spec 2 100 0 i dup_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- …and so is the 1 of the probe's `arg1=100` mutation, `d3-basic`'s
`dup3(2, 1, 0)` rewritten to `dup3(2, 100, 0)` while still answering 1.
probe: testing/syscall-check/tests/dup_spec.c#fail-closed --mutate dup3:arg1=100 -- d3-basic -/
theorem dup3_probe_s_free_newfd_100_one_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ dup3_spec 2 100 0 i dup_model (Ok (mkEffect 1 [] []) m' evs) := by
  sys_refute


/-- AN ALREADY-OPEN `newfd` NEEDS NO SUCH BOUND, and this is the pin for
the spec's second branch: 100 is the same number the pair above declines,
and with a descriptor open there the call succeeds.  An open fd is by
construction below the table's `max_fds`, so `expand_files` takes its
`nr < fdt->max_fds` early return (fs/file.c:299-300) and neither errno of
the declining case exists.  Without this pin a spec that tested
`NR_OPEN_DEFAULT` on BOTH branches would pass everything else in this file.
kernel: fs/file.c:ksys_dup3,expand_files,do_dup2@v6.18.46 -/
theorem dup3_onto_an_open_high_newfd_installs (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 0 100 0 i dup_high_model o ↔
      o = Ok (mkEffect 100 [] [])
            (fixture_of (fds := (100, .FdChannel 0) :: dup_fds) (fs := dup_fs)) [] := by
  sys_norm

/-- …so the decline the FREE 100 gets is refused here: the two branches
differ, and the difference is whether the descriptor is open.
kernel: fs/file.c:ksys_dup3,expand_files@v6.18.46 -/
theorem dup3_open_high_newfd_decline_rejected (i : SyscallInput) :
    ¬ dup3_spec 0 100 0 i dup_high_model Unmodeled := by
  sys_refute

/-- …and the displaced channel really is gone: fd 100 named channel 2 and
now names channel 0, which is the `filp_close` of the old description
(fs/file.c:1308-1309) read off the model's table.  Hypothesis form, as
`dup_success_without_the_copy_rejected`.
kernel: fs/file.c:do_dup2; fs/open.c:filp_close@v6.18.46 -/
theorem dup3_open_high_newfd_keeps_the_old_entry_rejected (i : SyscallInput)
    (evs : List event) :
    ¬ dup3_spec 0 100 0 i dup_high_model (Ok (mkEffect 100 [] []) dup_high_model evs) := by
  intro h; sys_refute at h

/-- `NR_OPEN_DEFAULT`'s own boundary, adjacent values either side: 63 is
answered and 64 is declined.  Neither the probe suite nor the cases above
reach it — they sit at 5, 7 and 100 — so an off-by-one in that one
comparison would otherwise pass everything.
rocq-twin: dup3_free_newfd_just_below_the_embedded_table
kernel: fs/file.c:ksys_dup3,expand_files@v6.18.46 -/
theorem dup3_free_newfd_just_below_the_embedded_table (i : SyscallInput) (o : outcome SyscallEffect) :
    dup3_spec 0 63 0 i dup_model o ↔
      o = Ok (mkEffect 63 [] []) (fixture_of (fds := (63, .FdChannel 0) :: dup_fds) (fs := dup_fs)) [] := by
  sys_norm

/-- 64 is the first slot the embedded table does not have.
rocq-twin: dup3_declines_a_free_newfd_at_the_embedded_table
kernel: fs/file.c:ksys_dup3,expand_files@v6.18.46 -/
theorem dup3_declines_a_free_newfd_at_the_embedded_table (i : SyscallInput)
    (o : outcome SyscallEffect) :
    dup3_spec 0 64 0 i dup_model o ↔ o = Unmodeled := by
  sys_norm

/-- …and the 64 a default kernel returns there is refused, which is what
makes 63 a boundary rather than a sample.
kernel: fs/file.c:ksys_dup3,expand_files@v6.18.46 -/
theorem dup3_free_newfd_at_the_table_success_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ dup3_spec 0 64 0 i dup_model (Ok (mkEffect 64 [] []) m' evs) := by
  sys_refute

/-! ## The dispatcher: syscall 24, and the fds' 32 bits

`SYSCALL_DEFINE3(dup3, unsigned int, oldfd, unsigned int, newfd, int,
flags)` (fs/file.c:1433-1436, Linux v6.18.46) narrows both fds before
`ksys_dup3` compares them, so `dup3(2^32, 0, 0)` is `dup3(0, 0, 0)`: -EINVAL, not the -EBADF a
model comparing the whole register would give for an fd it cannot find. -/

/-- Syscall 24 on `(0, 1, 0)` reaches the replacement arm.
kernel: include/uapi/asm-generic/unistd.h:__NR_dup3; fs/file.c:dup3,ksys_dup3,do_dup2@v6.18.46 -/
theorem sysno_24_is_dup3 (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 24 [0, 1, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        dup_model o ↔
      o = Ok (mkEffect 1 [] [])
            (fixture_of (fds := [(1, .FdChannel 0), (0, .FdChannel 0), (2, .FdChannel 2),
                                 (3, .FdFile [102] 1), (4, .FdDir)]) (fs := dup_fs)) [] := by
  sys_norm

/-- The fds are compared after truncation: `dup3(2^32, 0, 0)` is -EINVAL.
probe: testing/syscall-check/tests/dup_spec.c#conform -- d3-eq -/
theorem dup3_fds_are_compared_after_truncation (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 24 [4294967296, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        dup_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) dup_model [] := by
  sys_norm

/-- …and not -EBADF for an fd `2^32` the table does not hold.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3#3:ret=-EBADF -- d3-eq -/
theorem dup3_truncated_pair_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 24 [4294967296, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        dup_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- The SECOND fd is narrowed too: `dup3(0, 2^32, 0)` is `dup3(0, 0, 0)`,
-EINVAL at :1408.  `newfd` is the `unsigned int` of `SYSCALL_DEFINE3(dup3,
…)` (fs/file.c:1433) exactly as `oldfd` is, and this is the one input that
tells a table narrowing both fds from one narrowing `oldfd` alone: left
wide, `2^32` is at or above the limit and the answer would be -EBADF at
:1411.  No probe case reaches this shape; the reading is the evidence.
kernel: fs/file.c:dup3,ksys_dup3@v6.18.46 -/
theorem dup3_newfd_is_narrowed_before_the_comparison (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 24 [0, 4294967296, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        dup_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) dup_model [] := by
  sys_norm

/-- …so the -EBADF a table that left `newfd` wide would answer is refused.
kernel: fs/file.c:dup3,ksys_dup3@v6.18.46 -/
theorem dup3_wide_newfd_ebadf_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 24 [0, 4294967296, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
                dup_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-- The narrowing ALIASES rather than zeroes or rejects: `dup3(2^32 | 2, 1, 0)`
is `dup3(2, 1, 0)` and installs CHANNEL 2 at fd 1 — a table comparing the
wide register would answer -EBADF for an fd it cannot find, and one zeroing
the high half would install channel 0.
kernel: fs/file.c:dup3,ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_aliased_oldfd_installs_through_the_table (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 24 [4294967298, 1, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        dup_model o ↔
      o = Ok (mkEffect 1 [] [])
            (fixture_of (fds := [(1, .FdChannel 2), (0, .FdChannel 0), (2, .FdChannel 2),
                                 (3, .FdFile [102] 1), (4, .FdDir)]) (fs := dup_fs)) [] := by
  sys_norm

/-- THE FLAG WORD IS THE THIRD REGISTER, `flags` in `SYSCALL_DEFINE3(dup3,
unsigned int, oldfd, unsigned int, newfd, int, flags)` (fs/file.c:1433-1436,
Linux v6.18.46): syscall 24 with O_CLOEXEC in a2 and a bad bit in a3
installs, because `ksys_dup3` (:1405) tests only what a2 carried.  No
direct-spec pin can see which register the table hands `dup3_spec`; this
one and the next are what separate `in_arg i 2` from a table reading a3,
or a zero.
kernel: fs/file.c:dup3,ksys_dup3,do_dup2@v6.18.46 -/
theorem dup3_flags_are_the_third_register (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 24 [2, 1, 524288, 1, 0, 0] (fun _ => none) (fun _ => none))
        dup_model o ↔
      o = Ok (mkEffect 1 [] [])
            (fixture_of (fds := [(1, .FdChannel 2), (0, .FdChannel 0), (2, .FdChannel 2),
                                 (3, .FdFile [102] 1), (4, .FdDir)]) (fs := dup_fs)) [] := by
  sys_norm

/-- …and a bad bit IN a2 is -EINVAL through the table (fs/file.c:1405-1406,
Linux v6.18.46): the probe's `dup3(2, 1, 1)` as the table receives it.
probe: testing/syscall-check/tests/dup_spec.c#conform -- d3-flags -/
theorem dup3_bad_flag_through_the_table_is_einval (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 24 [2, 1, 1, 0, 0, 0] (fun _ => none) (fun _ => none))
        dup_model o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) dup_model [] := by
  sys_norm

/-- …so the 1 a table that read its flags from a zero register would answer
is refused.
probe: testing/syscall-check/tests/dup_spec.c#reject --mutate dup3:ret=1 -- d3-flags -/
theorem dup3_bad_flag_through_the_table_success_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 24 [2, 1, 1, 0, 0, 0] (fun _ => none) (fun _ => none))
        dup_model (Ok (mkEffect 1 [] []) m' evs) := by
  sys_refute

/-! ## A17: FdFileRW and FdFileA -/

/-- Rocq: `File.dup_modeled_entry`, File.v:100 at 96c2debdb.
Duplication shares the struct file via get_file in fs/file.c, do_dup2,
Linux v6.18.46; copying an entry would split its shared read/write position.
kernel: fs/file.c:do_dup2@v6.18.46 -/
theorem a17_rdwr_dup_declines :
    dup_modeled_entry (.FdFileRW [102] 0) = false := by
  rfl

/-- Rocq: `File.dup_modeled_entry`, File.v:99 at 96c2debdb.
Duplication shares the struct file via get_file in fs/file.c, do_dup2,
Linux v6.18.46.  A write through either fd lands at end of file, but an
lseek on one moves the f_pos the other reports, which copied entries split.
kernel: fs/file.c:do_dup2@v6.18.46 -/
theorem a17_append_dup_declines :
    dup_modeled_entry (.FdFileA [102] 0) = false := by
  rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.File
