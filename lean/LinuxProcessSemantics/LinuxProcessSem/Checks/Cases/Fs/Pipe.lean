import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! # Checks.Cases.Fs.Pipe — what `pipe2` admits, read off against Linux

Worked examples over `Sys.Fs.Pipe.pipe2_spec`, the twin of
`theories/LinuxProcessSem/Checks/Cases/Fs/Pipe.v`, read at
f44244ad6b8041aa83053d9ca91e090037ed743b and byte-identical at
2b5fb8277f069ff156c4939cefcd9f183432abd3 and at
a71fd38a08571d519b9cfc5f66308db5c26da570, the spec twin's baseline (the
squash of the 2026-09-11 work onto main; see THE BASELINE there).  Not part of the
trusted specification: this file is QA on the definitions, written to be
READ, and every claim in it is a claim about what the kernel does, with the
citation beside it — Linux v6.18.46 (commit 1f99e9ab748f) throughout, mostly
fs/pipe.c and fs/file.c, with fs/fcntl.c, fs/stat.c, fs/select.c and the
riscv uaccess sources where an arm outside fs/pipe.c is read; the function
and line are named on each pin.

HOW THESE ARE STATED.  A check is stated on the relation itself
(`Checks/Cases/Mm/Mmap.lean`'s header says why): an `iff` over EVERY
outcome `o`,

    pipe2_spec fildes flags i m o ↔ o = Ok … m' …

pins the positive half (what is allowed, and the model and event list it
leaves) and the negative half (nothing else is — not another errno, not a
second write range, not `Unmodeled`) in one statement.  Where an arm
answers with the environment's choice the right-hand side is the
DISJUNCTION `pipe2_errnos` and the kernel's own answer make, spelled out
in the order the normal form produces it: the three injectable errnos
first, then the copy-out or the -EFAULT.  Each `iff` is followed by
refutations of the concrete lies a kernel could tell there.  The sections
follow the kernel's order — `do_pipe2` (fs/pipe.c:1032-1052, v6.18.46) runs
`__do_pipe_flags`, which tests the mask (:987-988) and then reserves the
two descriptors (:994-1006), and only then the one `copy_to_user` (:1040)
and the two `fd_install`s (:1047-1048) — and each section pins the answer
against the one the NEXT check would have given, which is what makes the
order a claim and not a convention.

THE INPUTS.  `pipe2_in fildes flags wmem` is the call as the dispatcher
sees it: syscall 59, the two arguments in a0 and a1, nothing readable and
`wmem` writable.  A pin that reads no memory quantifies over the input
instead, which is the statement that the pointer is never consulted there.
The destinations are literal byte maps — the eight bytes at 4096
(`pipe2_flat_mem`), the same eight across a page boundary, four of them,
seven of them, none of them, and the two ends of the address space that
the wrapping walk joins (`pipe2_wrap_mem`).  The models are `demo_model`
(three channels, no pipe), the model `pipe2` leaves behind
(`one_pipe_model`, then `two_pipe_model`), a table with a hole below a
live descriptor (`holes_model`), and one hand-built table whose pipe ids
have wrapped (`aliased_id_model`), which no run can reach.

THE REGISTER.  The spec's unfolding, its errno list and `lowest_fd`'s
unfolding enter `sys_simp` here, at low priority like every other
(`Checks/Cases/Tactic.lean`'s header says why).  The fixtures stay OPAQUE
and enter by projection facts stated on the chain the first pass produces
(`demo_model.m_fd.fdst_pipes`), because two of the spec's decisions are
`match`es whose discriminants — `pipe_lookup` of the next id and
`read_bytes_map` over the destination — must reduce in the FIRST pass: an
`errno_from` left under a stuck match is evaluated to its `choose` by the
second pass before the enumeration-first reading can see it, and every
refutation of a wrong errno then stays open.  The same file header
explains the two passes; the getdents64 port (PR #760) found the shape
first.  Two more readings are registered here and explained where they
stand: the `pipe_insert` the spec builds on each pre-state, which the
second pass cannot evaluate (the models section says why), and an
existential lemma for the equation the outer `lowest_fd` choice leaves in
the fourth position, one past what core substitutes.

THREE PROOF SHAPES BEYOND `sys_norm`/`sys_refute`, each explained where
used.  A refutation whose lie is in the PAIR OF BYTES (a truncated pair,
poisoned bytes, the ends swapped, a descriptor taken twice, the wrong pipe
id) cannot be closed by `sys_refute` alone: the bytes are
`pipe_fd_bytes fdr fdw` with both descriptors still bound by the two
`lowest_fd` choices, and the forged outcome's injectivity puts the choice
equations behind more conjuncts than any existential lemma substitutes.
Those refutations go through the `iff` proved beside them: the forged
outcome is one of four `Ok`s, and each is refuted on a literal.  The
positive pins that name a concrete outcome are the `iff`'s right-hand side
by `Or.inr rfl`, for the same reason.  A refutation whose lie is in the
MODEL alone (a table left unchanged, a pipe id reused) goes through the
`iff` too and is decided on a projection — the return against the errno
cases, the number of pipe entries against the success — because the
model's pipe list is of the `PipeBuf` alias type and the injectivity
lemmas do not reach into it (the models section says why).  The rest close by
`sys_refute`, since their lie is decided on the return or on a second
write range, neither of which depends on the chosen descriptors.

THE ROCQ WORKED CASES, one by one.  `theories/LinuxProcessSem/Checks/Cases/Fs/Pipe.v`
also carries the arms `State.FdPipe` forces at fd-kind dispatch sites
OUTSIDE fs/pipe.c, because a constructor is answered wherever the tree
dispatches on fd kind.  Each is either pinned here, carried by the Cases
file of the arm it reads, or owed to the ticket that ports that arm:

- `init_model_holds_no_pipe_end`, `pipe2_wrap_would_pass_the_bare_walk`,
  `pipe2_wrap_fildes_is_not_access_ok`,
  `pipe2_wrapping_fildes_rejects_the_pair`,
  `pipe2_wrapping_fildes_is_efault`, `pipe2_flat_fildes_is_access_ok`,
  `pipe2_unwrapped_fildes_still_installs_the_pair`,
  `pipe2_unwrapped_fildes_rejects_efault`: pinned here under the same
  names, marked `rocq-twin`.  Rocq's `one_pipe_model`, `pipe2_wrap_fildes`,
  `pipe2_wrap_mem`, `pipe2_flat_fildes` and `pipe2_flat_mem` are defined
  here under their names.
- `fcntl_setfd_on_a_pipe_end_is_zero`: pinned here, on `pipe_model`,
  because `Checks/Cases/Fs/Fcntl.lean` pins F_SETFD on every kind but a
  pipe end.
- `fsync_on_a_pipe_end_is_einval`: carried by `Checks/Cases/Fs/Sync.lean`
  (`pipe_read_end_is_einval`, `pipe_write_end_is_einval`,
  `pipe_write_end_success_rejected`, with `channel_is_einval` and
  `write_file_is_zero` as the contrasts).
- `fcntl_setfl_on_a_pipe_end_declines`: carried by
  `Checks/Cases/Fs/Fcntl.lean` (`setfl_empty_on_pipe_reader_is_unmodeled`,
  `setfl_empty_on_pipe_writer_is_unmodeled`,
  `setfl_empty_on_pipe_zero_rejected`).
- `dup_of_a_pipe_end_declines`: carried by `Checks/Cases/Fs/File.lean`
  (`dup_of_a_pipe_reader_is_unmodeled`, `dup_of_a_pipe_writer_is_unmodeled`,
  `dup_of_a_pipe_writer_success_rejected`), the twin ticket S-Fs-File
  lands with.
- `fstat_on_a_pipe_end_declines`: pinned here under the Rocq name, on
  `pipe_model`, both ends and the closed fd 9 that keeps it from being
  vacuous; `Checks/Cases/Fs/Stat.lean`'s `pipe_is_unmodeled` holds the read
  end on that file's own fixture.
- `pselect6_over_a_pipe_end_declines`: carried at the syscall by
  `Checks/Cases/Fs/Select.lean` (`a_pipe_end_is_declined`, and
  `ppoll_a_pipe_end_is_declined` for ppoll), on a read end.
  `pselect_core_gaps_on_a_pipe_end_only` and
  `pselect6_pollability_is_per_kind`: pinned here under the Rocq names, at
  `Select.pselect_core` and `Select.bits_all_pollable` over `pipe_model`,
  because no pin of `Select.lean` reaches either function on a write end.
- `fd_names_path_ignores_a_pipe_end`: carried by
  `Checks/Cases/Fs/Namei.lean` under the same name, all four conjuncts.
- `ftruncate_on_a_pipe_end_is_einval`,
  `ftruncate_on_a_pipe_write_end_rejects_success`: carried through
  `check_syscall` by `Checks/Cases/Checks/Sys/Fs/Open.lean` under the same
  names, over this file's `pipe_model`.
- Not pinned, because the arm each reads has no Lean twin yet; each lands
  with the ticket named: `ioctl_on_a_pipe_end_is_enotty`,
  `ioctl_on_a_pipe_end_rejects_success`,
  `ioctl_other_request_on_a_pipe_end_declines` (ioctl, S-Fs-Ioctl);
  `socket_calls_on_a_pipe_end_are_enotsock`,
  `socket_calls_on_a_pipe_end_reject_ebadf` (bind and recvfrom,
  S-Net-Socket-lifecycle and S-Net-Socket-io);
  `readv_pipe_gate_splits_the_two_ends` and
  `pipe_writev_zero_count_truncates` (readv and writev,
  S-Fs-ReadWrite-readv-writev);
  `lseek_on_a_pipe_end_is_espipe_but_whence_wins` (lseek,
  S-Fs-ReadWrite-pread-pwrite-lseek); `clone_with_a_pipe_end_open_declines`,
  `clone_without_a_pipe_end_is_admitted` (clone, S-Kernel-Fork-clone).
  Rocq's `pipe_model` is defined here for the F_SETFD, fstat and pselect
  pins, and `Checks/Cases/Checks/Sys/Fs/Open.lean`'s two ftruncate pins
  read it too; its `clone_model` is not, since nothing here reads it.

NOTHING HERE COMPARES THE LEAN SPEC TO THE ROCQ ONE.  What these pins prove
is that this spec and a named line of Linux agree. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Pipe

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.File
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Fcntl
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Pipe
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! ## The register lines the specs owe `sys_simp`

`pipe2_spec.eq_1` and `pipe2_errnos.eq_1` are this file's to register.
`lowest_fd.eq_1`, `fcntl_spec.eq_1` and `fstat_spec.eq_1` belong to
`Checks/Cases/Fs/File.lean`, `Checks/Cases/Fs/Fcntl.lean` and
`Checks/Cases/Fs/Stat.lean`, none of which this file imports; they are
registered LOCALLY here, as `Stat.lean` registers `record_copyins.eq_1` for
itself, so that a module importing this file and the owner does not hold
the rewrite twice. -/

attribute [sys_simp low] pipe2_spec.eq_1 pipe2_errnos.eq_1
attribute [local sys_simp low] lowest_fd.eq_1 fcntl_spec.eq_1 Sys.Fs.Stat.fstat_spec.eq_1

/-- An equation on the bound variable in the FOURTH position, with nothing
after it: the shape the outer `lowest_fd` choice leaves once the inner one
has been eliminated — the outcome equation, the inner guard's freeness
(now on the outer variable), the outer guard's freeness, and the outer
guard's equation `fd = alloc_fd fds`.  Core's `exists_eq_right_right`
covers the third position; `Checks/Cases/Tactic.lean`'s `exists_eq_mid`
the second with any tail.  Registered at the default priority like them.
model: a propositional reading for `sys_norm`; no kernel claim. -/
@[sys_simp] theorem exists_eq_right_right_right {α : Sort _} {p q r : α → Prop} {v : α} :
    (∃ a, p a ∧ q a ∧ r a ∧ a = v) ↔ p v ∧ q v ∧ r v := by
  constructor
  · rintro ⟨a, hp, hq, hr, rfl⟩
    exact ⟨hp, hq, hr⟩
  · rintro ⟨hp, hq, hr⟩
    exact ⟨v, hp, hq, hr, rfl⟩

/-! ## The constants these checks spell out

Kept as numerals in the statements so a reader sees the register value the
program passes (include/uapi/asm-generic/fcntl.h, Linux v6.18.46); these
pins say what each one is.  The mask's fourth bit is spelled `O_EXCL`
because `O_NOTIFICATION_PIPE` is `#define O_NOTIFICATION_PIPE O_EXCL`
(include/uapi/linux/watch_queue.h:9, v6.18.46): a macro whose value is another macro,
so the pin names the one with a number. -/

/-- kernel: include/uapi/asm-generic/fcntl.h:O_CLOEXEC@v6.18.46 -/
example : O_CLOEXEC = 524288 := by decide
/-- kernel: include/uapi/asm-generic/fcntl.h:O_NONBLOCK@v6.18.46 -/
example : O_NONBLOCK = 2048 := by decide
/-- kernel: include/uapi/asm-generic/fcntl.h:O_DIRECT@v6.18.46 -/
example : O_DIRECT = 16384 := by decide
/-- kernel: include/uapi/asm-generic/fcntl.h:O_EXCL@v6.18.46 -/
example : O_EXCL = 128 := by decide

/-- The four bits `__do_pipe_flags` lets through (fs/pipe.c:987-988,
Linux v6.18.46), as one number: 524288 + 2048 + 16384 + 128.
kernel: include/uapi/asm-generic/fcntl.h:O_CLOEXEC,O_NONBLOCK,O_DIRECT,O_EXCL@v6.18.46 -/
theorem pipe2_flags_mask_is_542848 : pipe2_flags_mask = 542848 := by decide

/-- The three errnos the environment may hand `pipe2`: -EMFILE from
`alloc_fd`'s `fd >= end` test (fs/file.c:591-593, Linux v6.18.46);
-ENFILE from the system file limit, `alloc_empty_file`'s
`files_stat.max_files` test (fs/file_table.c:239-278, v6.18.46) on the way
from `create_pipe_files` through `alloc_file_pseudo` (fs/file_table.c:408,
v6.18.46) and `alloc_file_clone` (fs/file_table.c:464, v6.18.46), called at
:944 and :956 and handed back at :950 and :961 — the -ENFILE
`create_pipe_files` returns for itself (fs/pipe.c:932-933) stands for a
NULL from `get_pipe_inode`, an allocation that failed; -ENOMEM from
`alloc_fdtable` (fs/file.c:242, v6.18.46) when the table must grow, and
from those same file allocations.
kernel: fs/file.c:alloc_fd,alloc_fdtable; fs/file_table.c:alloc_empty_file; fs/pipe.c:create_pipe_files@v6.18.46 -/
theorem pipe2_errnos_is_emfile_enfile_enomem : pipe2_errnos = [EMFILE, ENFILE, ENOMEM] := by
  decide

/-! ## The inputs -/

/-- `pipe2(fildes, flags)` as the dispatcher sees it: syscall 59, the two
arguments in a0 and a1, nothing readable, `wmem` writable. -/
def pipe2_in (fildes flags : word) (wmem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 59 [fildes, flags, 0, 0, 0, 0] (fun _ => none) wmem

/-- The input's syscall number, read off by projection.
model: a fixture projection, a rewrite for `sys_norm`. -/
@[sys_simp] theorem in_sysno_pipe2_in (f fl : word) (w : word → Option byte) :
    (pipe2_in f fl w).in_sysno = 59 := rfl
/-- a0 is `fildes`.
model: a fixture projection, a rewrite for `sys_norm`. -/
@[sys_simp] theorem in_arg_pipe2_in_0 (f fl : word) (w : word → Option byte) :
    in_arg (pipe2_in f fl w) 0 = f := rfl
/-- a1 is `flags`.
model: a fixture projection, a rewrite for `sys_norm`. -/
@[sys_simp] theorem in_arg_pipe2_in_1 (f fl : word) (w : word → Option byte) :
    in_arg (pipe2_in f fl w) 1 = fl := rfl
/-- The writable view is the map the call names.
model: a fixture projection, a rewrite for `sys_norm`. -/
@[sys_simp] theorem in_wmem_pipe2_in (f fl : word) (w : word → Option byte) :
    (pipe2_in f fl w).in_wmem = w := rfl

/-! ## The destinations -/

/-- The last four bytes of the address space, so the 8-byte copy-out
covers them and then the four at 0.  Rocq's `pipe2_wrap_fildes`. -/
def pipe2_wrap_fildes : word := Z_to_bv 64 (2 ^ 64 - 4)

/-- A writable view backing exactly those two ends and nothing between.
Rocq's `pipe2_wrap_mem`. -/
def pipe2_wrap_mem : word → Option byte :=
  fun a => if bv_unsigned a < 4 ∨ 2 ^ 64 - 4 ≤ bv_unsigned a then some (Z_to_bv 8 0) else none

/-- An ordinary destination: 4096 is not load-bearing, any address
`access_okb` accepts would do.  Rocq's `pipe2_flat_fildes`. -/
def pipe2_flat_fildes : word := Z_to_bv 64 4096

/-- Exactly the eight bytes at 4096, so the mapped range and the copy-out
are the same range.  Rocq's `pipe2_flat_mem`. -/
def pipe2_flat_mem : word → Option byte :=
  fun a => if 4096 ≤ bv_unsigned a ∧ bv_unsigned a < 4096 + 8 then some (Z_to_bv 8 0) else none

/-- Four writable bytes at 4096 and a fault behind them: the read end's
`int` lands and the write end's faults — the probe's `partial`. -/
def pipe2_half_mem : word → Option byte :=
  fun a => if 4096 ≤ bv_unsigned a ∧ bv_unsigned a < 4096 + 4 then some (Z_to_bv 8 0) else none

/-- Seven writable bytes at 4096: one short of `sizeof(int[2])`. -/
def pipe2_seven_mem : word → Option byte :=
  fun a => if 4096 ≤ bv_unsigned a ∧ bv_unsigned a < 4096 + 7 then some (Z_to_bv 8 0) else none

/-- Nothing writable anywhere. -/
def pipe2_dead_mem : word → Option byte := fun _ => none

/-- A destination above 2^32 — `2^32 + 4096` — and the eight bytes there:
the table hands a0 to the spec WHOLE, where it narrows a1. -/
def pipe2_high_fildes : word := Z_to_bv 64 (2 ^ 32 + 4096)
def pipe2_high_mem : word → Option byte :=
  fun a => if 2 ^ 32 + 4096 ≤ bv_unsigned a ∧ bv_unsigned a < 2 ^ 32 + 4096 + 8
           then some (Z_to_bv 8 0) else none

/-- A destination four bytes short of a page boundary, and the eight bytes
across it: the probe's `straddle`. -/
def pipe2_straddle_fildes : word := Z_to_bv 64 8188
def pipe2_straddle_mem : word → Option byte :=
  fun a => if 8188 ≤ bv_unsigned a ∧ bv_unsigned a < 8188 + 8 then some (Z_to_bv 8 0) else none

/-! ### The destinations, pinned

Each is a claim the docstring above it makes about a byte map; a map that
lost the property would silently weaken every check that relies on it. -/

/-- The flat map answers its eight bytes and nothing on either side.
model: a closed fact about a fixture byte map. -/
theorem pipe2_flat_mem_is_eight_bytes :
    pipe2_flat_mem 4095 = none ∧ pipe2_flat_mem 4096 = some (Z_to_bv 8 0)
      ∧ pipe2_flat_mem 4103 = some (Z_to_bv 8 0) ∧ pipe2_flat_mem 4104 = none := by decide

/-- The half map stops after four; the seven map after seven.
model: a closed fact about two fixture byte maps. -/
theorem pipe2_half_and_seven_stop_short :
    pipe2_half_mem 4099 = some (Z_to_bv 8 0) ∧ pipe2_half_mem 4100 = none
      ∧ pipe2_seven_mem 4102 = some (Z_to_bv 8 0) ∧ pipe2_seven_mem 4103 = none := by decide

/-- The wrapped map is the last four bytes and the first four, and nothing
between.
model: a closed fact about a fixture byte map. -/
theorem pipe2_wrap_mem_is_the_two_ends :
    pipe2_wrap_mem pipe2_wrap_fildes = some (Z_to_bv 8 0) ∧ pipe2_wrap_mem 3 = some (Z_to_bv 8 0)
      ∧ pipe2_wrap_mem 4 = none ∧ pipe2_wrap_mem (Z_to_bv 64 (2 ^ 64 - 5)) = none := by decide

/-! ## The models

The post-states are LITERAL fixtures: the table and the pipe list a pin
names are written out, and `pipe2_model m id` — the model `pipe2` leaves,
the twin of the Rocq checker's builder of the same name
(`theories/LinuxProcessSem/Checks/Sys/Fs/Pipe.v`) — is pinned equal to
each of them by `rfl`, so a reader sees the descriptor numbers and the
builder is held to them.

WHY LITERALS AND NOT THE BUILDER.  `State.PipeBuf` is a `def` alias of
`List byte × Int`, and the second pass of `sys_norm` unfolds a closed
definition only through its equation theorem, whose `PipeBuf`-typed binder
does not unify with a `List byte × Int`-typed argument at the reducible
transparency simp matches under (measured: `simp +ground only []` leaves
`pipe_insert [] 0 ([], 0)` as it is while it evaluates `fd_insert`).  So a
`pipe_insert` on closed arguments is never evaluated by `sys_norm`, on
either side of an `iff`.  A literal needs no evaluation, and the three
`pipe_insert` terms the spec itself produces on these pre-states are
rewritten by the projection facts below.  THIS STOPS BEING TRUE when PR
#830 (`lean: base: make PipeBuf an abbrev`) lands: an `abbrev` unfolds at
reducible transparency, the equation theorems match again, and the second
pass will evaluate `pipe_insert` on its own — the literals and the facts
below stay correct then, and become removable. -/

/-- The read end's descriptor: the lowest free one. -/
def pipe2_fdr (m : Model) : word := alloc_fd (m_fds m)
/-- The table with the read end installed. -/
def pipe2_fds1 (m : Model) (id : word) : List (word × FdEntry) :=
  fd_insert (m_fds m) (pipe2_fdr m) (.FdPipe id false)
/-- The write end's descriptor: the lowest free one once the read end is in. -/
def pipe2_fdw (m : Model) (id : word) : word := alloc_fd (pipe2_fds1 m id)
/-- The model `pipe2` leaves behind. -/
def pipe2_model (m : Model) (id : word) : Model :=
  with_pipes (pipe_insert (m_pipes m) id ([], 0))
    (with_fds (fd_insert (pipe2_fds1 m id) (pipe2_fdw m id) (.FdPipe id true)) m)

/-- The pipe lists the fixtures carry, as NAMED constants of the alias type
`List (word × PipeBuf)`.  A literal list written in place elaborates with
the alias unfolded, and then `with_pipes`' and `fixture_of`'s equation
theorems — whose binders carry the alias — no longer unify with it at the
transparency simp matches under (the section header says why); a constant
declared at the alias type unifies, and the second pass unfolds it to the
same literal on both sides of an `iff`.  Owed to PR #830 (`PipeBuf` as an
`abbrev`) in the same way as the section header.  One pipe, id 0, empty. -/
def one_pipe_pipes : List (word × PipeBuf) := [(0, ([], 0))]

/-- Two pipes, ids 1 and 0, both empty, the newer first as `pipe_insert`
conses it. -/
def two_pipe_pipes : List (word × PipeBuf) := [(1, ([], 0)), (0, ([], 0))]

/-- A model holding one pipe, as `pipe2_spec` makes one from the demo
process: the read end took fd 3 and the write end fd 4, over the three
channels, and the queue of pipe 0 is empty.  Rocq's `one_pipe_model`,
written out (`one_pipe_model_is_built` says it is the builder's value). -/
def one_pipe_model : Model :=
  fixture_of
    (fds := [(4, .FdPipe 0 true), (3, .FdPipe 0 false),
             (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2)])
    (pipes := one_pipe_pipes)

/-- The second pipe of the same process: fds 5 and 6, pipe id 1, the first
pipe's entry kept. -/
def two_pipe_model : Model :=
  fixture_of
    (fds := [(6, .FdPipe 1 true), (5, .FdPipe 1 false), (4, .FdPipe 0 true), (3, .FdPipe 0 false),
             (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2)])
    (pipes := two_pipe_pipes)

/-- The lie a model reusing pipe 0's id would tell for the second pipe: the
new ends bound to the OLD queue, and one pipe entry where the kernel has
two `pipe_inode_info`s.  `reused_id_model_is_the_old_id` says it is what
the builder computes at id 0. -/
def reused_id_model : Model :=
  fixture_of
    (fds := [(6, .FdPipe 0 true), (5, .FdPipe 0 false), (4, .FdPipe 0 true), (3, .FdPipe 0 false),
             (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2)])
    (pipes := one_pipe_pipes)

/-- The three channels and a directory reference at fd 4, so fd 3 is free
below a live descriptor: the smallest table with a hole under a live
number, where the read end fills the hole and the write end skips the live
number.  The probe's `holes` has that shape on a bigger table —
`holes_probe_model` below is that table — so the pins over this one carry
kernel evidence and the probe's evidence sits on the pins over its own. -/
def holes_model : Model :=
  fixture_of (fds := [(0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2), (4, .FdDir)])

/-- `holes_model` after one `pipe2`: fds 3 and 5, pipe 0. -/
def holes_after_model : Model :=
  fixture_of
    (fds := [(5, .FdPipe 0 true), (3, .FdPipe 0 false),
             (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2), (4, .FdDir)])
    (pipes := one_pipe_pipes)

/-- The table the probe's `holes` really runs its third `pipe2` on: two
pipes took (3, 4) and (5, 6) and `close(3)` freed the lowest, so fd 3 is
the hole under three live pipe ends — `two_pipe_model` less fd 3.  The
probe expects `(fda[0], fdb[1] + 1)`, which is (3, 7). -/
def holes_probe_model : Model :=
  fixture_of
    (fds := [(6, .FdPipe 1 true), (5, .FdPipe 1 false), (4, .FdPipe 0 true),
             (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2)])
    (pipes := two_pipe_pipes)

/-- Three pipes, ids 2, 1 and 0, the newest first. -/
def three_pipe_pipes : List (word × PipeBuf) := [(2, ([], 0)), (1, ([], 0)), (0, ([], 0))]

/-- `holes_probe_model` after the third `pipe2`: fds 3 and 7, pipe 2, the
two earlier pipes kept. -/
def holes_probe_after_model : Model :=
  fixture_of
    (fds := [(7, .FdPipe 2 true), (3, .FdPipe 2 false),
             (6, .FdPipe 1 true), (5, .FdPipe 1 false), (4, .FdPipe 0 true),
             (0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2)])
    (pipes := three_pipe_pipes)

/-- A pipe table already binding the id the NEXT pipe would get.  No run
builds this: ids count creations (`State.pipe_new_id`) and entries are
never removed, so the next id is always one past every key.  It is the
one way to reach the spec's aliasing arm. -/
def aliased_id_model : Model := fixture_of (pipes := [(1, ([], 0))])

/-- Rocq's `pipe_model`: both ends of pipe 0 at fds 3 and 4 and a
write-only file at fd 5, for the one fcntl pin this file carries. -/
def pipe_model : Model :=
  fixture_of
    (fds := [(0, .FdChannel 0), (1, .FdChannel 1), (2, .FdChannel 2),
             (3, .FdPipe 0 false), (4, .FdPipe 0 true), (5, .FdFileW [102] 0)])
    (fs := [([102], [120])])

/-! ### The builder agrees with the literals

Each literal above is what `pipe2_model` computes on its pre-state, by
`rfl`: the kernel claim about the numbers is on the pin, the literal is
what the pins read. -/

/-- One pipe from the demo process: fd 3 reads, fd 4 writes, pipe 0 is
empty and the channels are untouched — `fd[0] = fdr`, `fd[1] = fdw`
(fs/pipe.c:1005-1006, v6.18.46), each from `get_unused_fd_flags` (:994, :999) over a
table holding 0, 1 and 2.
kernel: fs/pipe.c:__do_pipe_flags; fs/file.c:alloc_fd@v6.18.46 -/
theorem one_pipe_model_is_built :
    one_pipe_model = pipe2_model demo_model (pipe_new_id (m_pipes demo_model)) := rfl

/-- The second pipe takes 5 and 6 and the next id, 1; the first pipe's
entry stays.
kernel: fs/pipe.c:__do_pipe_flags; fs/file.c:alloc_fd@v6.18.46 -/
theorem two_pipe_model_is_built :
    two_pipe_model = pipe2_model one_pipe_model (pipe_new_id (m_pipes one_pipe_model)) := rfl

/-- Over the hole: the read end takes 3 and the write end 5.  `alloc_fd`
starts at the larger of 0 and the `next_fd` hint (fs/file.c:580-582,
v6.18.46), which `__put_unused_fd` (fs/file.c:626-632, v6.18.46) lowered to 3
when 3 was freed, and `find_next_fd` (fs/file.c:544-565, v6.18.46) skips the
live 4 on the second scan.
kernel: fs/pipe.c:__do_pipe_flags; fs/file.c:alloc_fd,find_next_fd,__put_unused_fd@v6.18.46 -/
theorem holes_after_model_is_built :
    holes_after_model = pipe2_model holes_model (pipe_new_id (m_pipes holes_model)) := rfl

/-- Over the probe's hole: the read end takes the freed 3, the write end 7,
the first number above the live 4, 5 and 6; the third pipe is id 2.
kernel: fs/pipe.c:__do_pipe_flags; fs/file.c:alloc_fd,find_next_fd,__put_unused_fd@v6.18.46 -/
theorem holes_probe_after_model_is_built :
    holes_probe_after_model
      = pipe2_model holes_probe_model (pipe_new_id (m_pipes holes_probe_model)) := rfl

/-- The forged second pipe is the builder at id 0: `pipe_insert` replaces
the entry it finds, so one pipe remains.
model: the forged fixture is a closed value of the builder, a fact about the model. -/
theorem reused_id_model_is_the_old_id : reused_id_model = pipe2_model one_pipe_model 0 := rfl

/-- PIPE2 IS THE ONLY THING THAT MAKES A PIPE END, and `State.pipe_end_live`
rests on it.  The half a proof can state is the STARTING table:
`State.init_model` seeds three channels and nothing else, so a pipe end is
absent before the first instruction.
rocq-twin: init_model_holds_no_pipe_end -/
theorem init_model_holds_no_pipe_end :
    (m_fds demo_model).all (fun e => match e.2 with | .FdPipe _ _ => false | _ => true) = true := by
  decide

/-- The next pipe id of each pre-state is unbound: the discriminant of the
spec's first `match`, on the chain the first pass produces.
model: a closed `pipe_lookup` at the next id, a rewrite for `sys_norm`. -/
@[sys_simp] theorem pipe_lookup_demo_next :
    pipe_lookup demo_model.m_fd.fdst_pipes (pipe_new_id demo_model.m_fd.fdst_pipes) = none := rfl
/-- model: a closed `pipe_lookup` at the next id, a rewrite for `sys_norm`. -/
@[sys_simp] theorem pipe_lookup_one_pipe_next :
    pipe_lookup one_pipe_model.m_fd.fdst_pipes (pipe_new_id one_pipe_model.m_fd.fdst_pipes)
      = none := rfl
/-- model: a closed `pipe_lookup` at the next id, a rewrite for `sys_norm`. -/
@[sys_simp] theorem pipe_lookup_holes_next :
    pipe_lookup holes_model.m_fd.fdst_pipes (pipe_new_id holes_model.m_fd.fdst_pipes) = none := rfl
/-- model: a closed `pipe_lookup` at the next id, a rewrite for `sys_norm`. -/
@[sys_simp] theorem pipe_lookup_holes_probe_next :
    pipe_lookup holes_probe_model.m_fd.fdst_pipes (pipe_new_id holes_probe_model.m_fd.fdst_pipes)
      = none := rfl
/-- …and the aliased table binds it.
model: a closed `pipe_lookup` at the next id, a rewrite for `sys_norm`. -/
@[sys_simp] theorem pipe_lookup_aliased_next :
    pipe_lookup aliased_id_model.m_fd.fdst_pipes (pipe_new_id aliased_id_model.m_fd.fdst_pipes)
      = some ([], 0) := rfl
/-- The pipe list the spec builds on the demo process, on the chain the
first pass produces: read here because the second pass cannot evaluate
`pipe_insert` (the section header above says why).
model: a closed `pipe_insert` at the next id, a rewrite for `sys_norm`. -/
@[sys_simp] theorem pipe_insert_demo_next :
    pipe_insert demo_model.m_fd.fdst_pipes (pipe_new_id demo_model.m_fd.fdst_pipes) ([], 0)
      = one_pipe_pipes := rfl
/-- model: a closed `pipe_insert` at the next id, a rewrite for `sys_norm`. -/
@[sys_simp] theorem pipe_insert_one_pipe_next :
    pipe_insert one_pipe_model.m_fd.fdst_pipes (pipe_new_id one_pipe_model.m_fd.fdst_pipes) ([], 0)
      = two_pipe_pipes := rfl
/-- model: a closed `pipe_insert` at the next id, a rewrite for `sys_norm`. -/
@[sys_simp] theorem pipe_insert_holes_next :
    pipe_insert holes_model.m_fd.fdst_pipes (pipe_new_id holes_model.m_fd.fdst_pipes) ([], 0)
      = one_pipe_pipes := rfl
/-- model: a closed `pipe_insert` at the next id, a rewrite for `sys_norm`. -/
@[sys_simp] theorem pipe_insert_holes_probe_next :
    pipe_insert holes_probe_model.m_fd.fdst_pipes (pipe_new_id holes_probe_model.m_fd.fdst_pipes)
        ([], 0)
      = three_pipe_pipes := rfl

/-! ### The pair's bytes, read off

`pipe_fd_bytes` is `le32_bytes` twice, and `le32_bytes` shifts an `Int`;
the second pass evaluates `alloc_fd` to the descriptor but leaves
`Int.shiftRight` standing, so the bytes are read here in the first pass,
on the exact term the spec builds once the two `lowest_fd` choices are
substituted: the read end is `alloc_fd` of the table, the write end
`alloc_fd` of the table with the read end installed.  Each is a closed
computation over the model and is what `copy_to_user(fildes, fd,
sizeof(fd))` lays down for that pair (fs/pipe.c:1040, v6.18.46): two
little-endian `int`s, read end first. -/

/-- model: the pair's bytes on the demo process, a rewrite for `sys_norm`. -/
@[sys_simp] theorem pair_bytes_demo :
    pipe_fd_bytes (alloc_fd demo_model.m_fd.fdst_table)
        (alloc_fd (fd_insert demo_model.m_fd.fdst_table (alloc_fd demo_model.m_fd.fdst_table)
          (.FdPipe (pipe_new_id demo_model.m_fd.fdst_pipes) false)))
      = [3, 0, 0, 0, 4, 0, 0, 0] := rfl
/-- model: the pair's bytes on `one_pipe_model`, a rewrite for `sys_norm`. -/
@[sys_simp] theorem pair_bytes_one_pipe :
    pipe_fd_bytes (alloc_fd one_pipe_model.m_fd.fdst_table)
        (alloc_fd (fd_insert one_pipe_model.m_fd.fdst_table (alloc_fd one_pipe_model.m_fd.fdst_table)
          (.FdPipe (pipe_new_id one_pipe_model.m_fd.fdst_pipes) false)))
      = [5, 0, 0, 0, 6, 0, 0, 0] := rfl
/-- model: the pair's bytes on `holes_model`, a rewrite for `sys_norm`. -/
@[sys_simp] theorem pair_bytes_holes :
    pipe_fd_bytes (alloc_fd holes_model.m_fd.fdst_table)
        (alloc_fd (fd_insert holes_model.m_fd.fdst_table (alloc_fd holes_model.m_fd.fdst_table)
          (.FdPipe (pipe_new_id holes_model.m_fd.fdst_pipes) false)))
      = [3, 0, 0, 0, 5, 0, 0, 0] := rfl
/-- model: the pair's bytes on `holes_probe_model`, a rewrite for `sys_norm`. -/
@[sys_simp] theorem pair_bytes_holes_probe :
    pipe_fd_bytes (alloc_fd holes_probe_model.m_fd.fdst_table)
        (alloc_fd (fd_insert holes_probe_model.m_fd.fdst_table
          (alloc_fd holes_probe_model.m_fd.fdst_table)
          (.FdPipe (pipe_new_id holes_probe_model.m_fd.fdst_pipes) false)))
      = [3, 0, 0, 0, 7, 0, 0, 0] := rfl

/-- The two projections a forged post-state is told apart by when its lie
is in the MODEL rather than in the effect: the return, and how many pipes
the model carries (0 for a decline).  A refutation applies `congrArg` with
one of them to the `iff`'s equation and decides the numbers.
model: projections of an outcome, no kernel claim. -/
def outcome_ret : outcome SyscallEffect → word
  | Ok e _ _ => e.eff_ret
  | Unmodeled => 0
/-- model: projections of an outcome, no kernel claim. -/
def outcome_pipe_count : outcome SyscallEffect → Nat
  | Ok _ m _ => (m_pipes m).length
  | Unmodeled => 0
/-- The read end of `pipe_model`, for the fcntl pin.
model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
@[sys_simp] theorem fd_lookup_pipe_model_3 :
    fd_lookup pipe_model.m_fd.fdst_table 3 = some (.FdPipe 0 false) := rfl
/-- model: a closed `fd_lookup` at a numeral, a rewrite for `sys_norm`. -/
@[sys_simp] theorem fd_lookup_pipe_model_4 :
    fd_lookup pipe_model.m_fd.fdst_table 4 = some (.FdPipe 0 true) := rfl
/-- model: a closed `fd_lookup` at a numeral no entry holds, a rewrite for `sys_norm`. -/
@[sys_simp] theorem fd_lookup_pipe_model_9 :
    fd_lookup pipe_model.m_fd.fdst_table 9 = none := rfl

/-! ### The walks, read off

`read_bytes_map` over each destination, for the spec's two other
`match`es.  Evaluated closed, so each is a fact about the fixture map. -/

/-- model: a closed walk over a fixture map, a rewrite for `sys_norm`. -/
@[sys_simp] theorem walk_flat_8 :
    read_bytes_map pipe2_flat_mem pipe2_flat_fildes (Z_to_bv 64 8)
      = some (List.replicate 8 (Z_to_bv 8 0)) := by decide
/-- model: a closed walk over a fixture map, a rewrite for `sys_norm`. -/
@[sys_simp] theorem walk_high_8 :
    read_bytes_map pipe2_high_mem pipe2_high_fildes (Z_to_bv 64 8)
      = some (List.replicate 8 (Z_to_bv 8 0)) := by decide
/-- model: a closed walk over a fixture map, a rewrite for `sys_norm`. -/
@[sys_simp] theorem walk_straddle_8 :
    read_bytes_map pipe2_straddle_mem pipe2_straddle_fildes (Z_to_bv 64 8)
      = some (List.replicate 8 (Z_to_bv 8 0)) := by decide
/-- model: a closed walk over a fixture map, a rewrite for `sys_norm`. -/
@[sys_simp] theorem walk_half_8 :
    read_bytes_map pipe2_half_mem pipe2_flat_fildes (Z_to_bv 64 8) = none := by decide
/-- model: a closed walk over a fixture map, a rewrite for `sys_norm`. -/
@[sys_simp] theorem walk_half_1 :
    read_bytes_map pipe2_half_mem pipe2_flat_fildes (Z_to_bv 64 1) = some [Z_to_bv 8 0] := by
  decide
/-- model: a closed walk over a fixture map, a rewrite for `sys_norm`. -/
@[sys_simp] theorem walk_seven_8 :
    read_bytes_map pipe2_seven_mem pipe2_flat_fildes (Z_to_bv 64 8) = none := by decide
/-- model: a closed walk over a fixture map, a rewrite for `sys_norm`. -/
@[sys_simp] theorem walk_seven_1 :
    read_bytes_map pipe2_seven_mem pipe2_flat_fildes (Z_to_bv 64 1) = some [Z_to_bv 8 0] := by
  decide
/-- model: a closed walk over a fixture map, a rewrite for `sys_norm`. -/
@[sys_simp] theorem walk_dead_8 :
    read_bytes_map pipe2_dead_mem pipe2_flat_fildes (Z_to_bv 64 8) = none := by decide
/-- model: a closed walk over a fixture map, a rewrite for `sys_norm`. -/
@[sys_simp] theorem walk_dead_1 :
    read_bytes_map pipe2_dead_mem pipe2_flat_fildes (Z_to_bv 64 1) = none := by decide

/-! ## The spec, dispatched: `pipe_flags32` truncates the flag word

`pipe_flags32` narrows a1 to its low 32 bits, as
`SYSCALL_DEFINE2(pipe2, int __user *, fildes, int, flags)` (fs/pipe.c:1054, v6.18.46)
does by declaring `flags` an `int`; these facts let the first pass read
the table's arm on the literals the dispatcher pins pass. -/

/-- model: the calling-convention wrapper at a numeral, a rewrite for `sys_norm`. -/
@[sys_simp] theorem pipe_flags32_two_pow_32 : pipe_flags32 4294967296 = 0 := by decide
/-- model: the calling-convention wrapper at a numeral, a rewrite for `sys_norm`. -/
@[sys_simp] theorem pipe_flags32_two_pow_32_plus_bit_30 :
    pipe_flags32 5368709120 = 1073741824 := by decide
/-- model: the calling-convention wrapper at a numeral, a rewrite for `sys_norm`. -/
@[sys_simp] theorem pipe_flags32_two_pow_32_plus_nonblock : pipe_flags32 4294969344 = 2048 := by
  decide

/-! ## `__do_pipe_flags`, first test: the mask

fs/pipe.c:987-988 at Linux v6.18.46:
`if (flags & ~(O_CLOEXEC | O_NONBLOCK | O_DIRECT | O_NOTIFICATION_PIPE))
return -EINVAL;` — the first statement of `__do_pipe_flags`, ahead of
`create_pipe_files` (:990), ahead of both `get_unused_fd_flags` (:994,
:999), and ahead of the only read of `fildes`, `do_pipe2`'s `copy_to_user`
(:1040).  Every pin here holds for a SYMBOLIC input and model: the
statement that neither the pointer nor the fd table is consulted. -/

/-- Bit 30 is outside the mask: -EINVAL, on any model, whatever memory the
input carries — the probe's `flagdrop`.  The `iff` refuses every other
answer, a pair among them.
probe: testing/syscall-check/tests/pipe2_spec.c#conform -- flagdrop -/
theorem unaccepted_bit_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    pipe2_spec 4096 1073741824 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- A kernel that dropped the bit and handed out a pair is refused.  That is
qemu-user's trace: QEMU v11.1.1's `do_pipe` (linux-user/syscall.c) runs
`flags` through `target_to_host_bitmask(arg2, fcntl_flags_tbl)`, which keeps
the bits the table names and drops every other, so the host `pipe2` sees 0
and succeeds.  The tree reads that as the emulator's translation defect — a
deviation from the kernel it emulates — and not as a behavior of a supported
implementation, which is what makes the probe's case a `reject`.
probe: testing/syscall-check/tests/pipe2_spec.c#reject --mutate pipe2:ret=0,smuggle-write-bytes:a0:0300000004000000 -- flagdrop -/
theorem unaccepted_bit_pair_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ pipe2_spec 4096 1073741824 i m
        (Ok (mkEffect 0 [(4096, [3, 0, 0, 0, 4, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-- Bit 0 (`O_WRONLY`) is outside the mask too: the residue is tested as a
whole, not bit 31 alone.
kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem bit_zero_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    pipe2_spec 4096 1 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- Bit 31 alone, the `int`'s sign bit: `flags & ~mask` is nonzero and the
`if` tests truthiness, not sign, so it is -EINVAL like any other bit.
kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem sign_bit_is_einval (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    pipe2_spec 4096 2147483648 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- PRECEDENCE, -EINVAL over -EFAULT: an unaccepted bit beside a destination
not one byte of which is writable is -EINVAL, because :987 fires before
:1040 and nothing between them touches the pointer — the probe's
`flagorder`.
probe: testing/syscall-check/tests/pipe2_spec.c#conform -- flagorder -/
theorem unaccepted_bit_beats_unwritable_fildes (m : Model) (o : outcome SyscallEffect) :
    pipe2_spec pipe2_flat_fildes 1073741824 (pipe2_in pipe2_flat_fildes 1073741824 pipe2_dead_mem)
        m o
      ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- A kernel that tested the pointer first would fault in `copy_to_user`
and answer -EFAULT: refused.
probe: testing/syscall-check/tests/pipe2_spec.c#reject --mutate pipe2:ret=-EFAULT -- flagorder -/
theorem unaccepted_bit_efault_rejected (m m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 1073741824 (pipe2_in pipe2_flat_fildes 1073741824 pipe2_dead_mem)
        m (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- PRECEDENCE, -EINVAL over the decline: `O_NONBLOCK` beside bit 30 is
-EINVAL, because the mask test (:987) precedes everything the model
declines to interpret.
kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem unaccepted_bit_beside_accepted_is_einval (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    pipe2_spec 4096 1073743872 i m o ↔ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- …so the decline is refused there: a model that declined every nonzero
word would have declined this one.
kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem unaccepted_bit_beside_accepted_unmodeled_rejected (i : SyscallInput) (m : Model) :
    ¬ pipe2_spec 4096 1073743872 i m Unmodeled := by
  sys_refute

/-! ## The four accepted bits: declined, each for a stated reason

`__do_pipe_flags` lets `O_CLOEXEC`, `O_NONBLOCK`, `O_DIRECT` and
`O_NOTIFICATION_PIPE` through (fs/pipe.c:987-988, v6.18.46), and the model
interprets none of them: `flags = 0` is the whole modeled surface.  Three
of the four are COVERAGE GAPS — Linux answers with a definite pair, and
the model lacks the state to carry what the bit would later mean — and
the fourth is an EMPTY INTERSECTION.  Each `iff` says which, and is paired
with the refusal of the -EINVAL a model with a narrower mask would give
and of the pair a model that ignored the bit would give. -/

/-- `O_NONBLOCK`: accepted (:987), then carried into both files' `f_flags`
by `create_pipe_files` (fs/pipe.c:945, v6.18.46, :956).  Linux hands out a pair; the
model declines, because the bit turns every blocking read and write on the
pipe into -EAGAIN and the model has no blocking to speak of — a gap, not
an empty intersection.  The probe's `nonblock`.
probe: testing/syscall-check/tests/pipe2_spec.c#fail-closed -- nonblock -/
theorem nonblock_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    pipe2_spec 4096 2048 i m o ↔ o = Unmodeled := by
  sys_norm

/-- The bit is inside the mask, so -EINVAL is a lie: a model whose mask
lacked `O_NONBLOCK` would tell it.
kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem nonblock_einval_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ pipe2_spec 4096 2048 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- …and the pair Linux really hands out is refused too: a decline is not a
guess at the kernel's answer.
probe: testing/syscall-check/tests/pipe2_spec.c#fail-closed -- nonblock -/
theorem nonblock_pair_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ pipe2_spec 4096 2048 i m (Ok (mkEffect 0 [(4096, [3, 0, 0, 0, 4, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-- `O_CLOEXEC`: accepted (:987) and recorded only in the descriptor
table's close-on-exec bitmap — `__set_open_fd` (fs/file.c:333-340, v6.18.46), which
`alloc_fd` calls with `flags & O_CLOEXEC` at fs/file.c:606, reached from
`__do_pipe_flags` (fs/pipe.c:994 and :999, v6.18.46), which calls
`get_unused_fd_flags` (fs/file.c:620-623, v6.18.46) twice.  Its readers are
`get_close_on_exec` (fs/file.c:1256, v6.18.46) behind `do_fcntl`'s `F_GETFD`
(fs/fcntl.c:465-467, v6.18.46), which `Sys.Fs.Fcntl.fcntl_spec` declines;
`do_close_on_exec` (fs/file.c:862, v6.18.46) on the `execve` path, which the
model has no arm for; and /proc's fdinfo, which no modeled call reads.  A
gap, not an empty intersection, and one the `F_GETFD` decline is
load-bearing for.
kernel: fs/pipe.c:__do_pipe_flags; fs/file.c:alloc_fd@v6.18.46 -/
theorem cloexec_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    pipe2_spec 4096 524288 i m o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem cloexec_einval_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ pipe2_spec 4096 524288 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- `O_DIRECT`: accepted (:987) and set on the write end's `f_flags`
(fs/pipe.c:945, v6.18.46), selecting packet mode, where a read DISCARDS the tail of
a packet it did not take — a queue discipline `State.PipeBuf` does not
have.  A gap.
kernel: fs/pipe.c:__do_pipe_flags,create_pipe_files@v6.18.46 -/
theorem direct_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    pipe2_spec 4096 16384 i m o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem direct_einval_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ pipe2_spec 4096 16384 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- `O_NOTIFICATION_PIPE` (spelled `O_EXCL`, 128): accepted (:987), and
then `create_pipe_files` calls `watch_queue_init` for it (fs/pipe.c:935-942, v6.18.46).
THE INTERSECTION IS EMPTY: under CONFIG_WATCH_QUEUE the call returns a
notification pipe, and without it the stub returns -ENOPKG
(include/linux/watch_queue.h:126-129, v6.18.46) and the call fails, both of them
real Linux configurations.  No single answer is in every supported
implementation's set, so none may be proved certain; the model holds no
notification-pipe state to answer both with, so it declines.  That is a
sound answer, not the only one: `alt` over the stub's -ENOPKG and the
configured kernel's answers — the pair, or the -ENOMEM of `watch_queue_init`
(kernel/watch_queue.c:691-706, v6.18.46) — would be sound too once the state
exists.
kernel: fs/pipe.c:__do_pipe_flags,create_pipe_files; include/linux/watch_queue.h:watch_queue_init@v6.18.46 -/
theorem notification_pipe_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    pipe2_spec 4096 128 i m o ↔ o = Unmodeled := by
  sys_norm

/-- Neither configuration's answer is committed to: not the stub's -ENOPKG
(65)…
kernel: include/linux/watch_queue.h:watch_queue_init@v6.18.46 -/
theorem notification_pipe_enopkg_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ pipe2_spec 4096 128 i m (Ok (mkEffect (errno_ret 65) [] []) m' evs) := by
  sys_refute

/-- …nor the pair a CONFIG_WATCH_QUEUE kernel returns, nor -EINVAL, since
the bit is inside the mask.
kernel: fs/pipe.c:__do_pipe_flags,create_pipe_files@v6.18.46 -/
theorem notification_pipe_pair_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ pipe2_spec 4096 128 i m (Ok (mkEffect 0 [(4096, [3, 0, 0, 0, 4, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-- kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem notification_pipe_einval_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ pipe2_spec 4096 128 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- All four accepted bits at once (542848) pass the mask and decline: the
mask is exactly these four, so this is the largest word that is not
-EINVAL.
kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem all_accepted_bits_is_unmodeled (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    pipe2_spec 4096 542848 i m o ↔ o = Unmodeled := by
  sys_norm

/-- kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem all_accepted_bits_einval_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ pipe2_spec 4096 542848 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-! ## The id-space wrap: fail closed where no run can go

`State.pipe_new_id` counts creations and entries are never removed, so
the id a new pipe gets is never already bound; `aliased_id_model` is the
hand-built table where it is.  Linux has no such state to be in — every
call gets a fresh `pipe_inode_info` from `alloc_pipe_info` (fs/pipe.c:792, v6.18.46)
through `get_pipe_inode` (:886-924) — so the arm exists only so that the
model never aliases two pipes' queues, and it declines rather than
guesses. -/

/-- On the aliased table the call declines, whatever the destination.
kernel: fs/pipe.c:get_pipe_inode,alloc_pipe_info@v6.18.46 -/
theorem aliased_id_is_unmodeled (o : outcome SyscallEffect) :
    pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) aliased_id_model o
      ↔ o = Unmodeled := by
  sys_norm

/-- …and the pair a kernel really returns — 3 and 4 over three channels —
is refused there, because saying so would bind pipe 1's queue twice.
kernel: fs/pipe.c:get_pipe_inode,alloc_pipe_info@v6.18.46 -/
theorem aliased_id_pair_rejected (m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) aliased_id_model
        (Ok (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-! ## `access_ok`: a destination that wraps the address space

`do_pipe2`'s single `copy_to_user(fildes, fd, sizeof(fd))` (fs/pipe.c:1040, v6.18.46)
is `access_ok` and then the copy (`_inline_copy_to_user`,
include/linux/uaccess.h:190), and `__access_ok` compares
`addr <= TASK_SIZE_MAX - size` (include/asm-generic/access_ok.h:31-41, v6.18.46), so a
range whose eight bytes run off the top of the address space is refused
before a byte moves; `do_pipe2` then `fput`s both files and `put_unused_fd`s
both reservations (:1041-1045) and the call is -EFAULT with nothing
installed.  Why the group is here and not in a probe, and why the guard
cannot be reached from a run, is on Rocq's `Checks/Cases/Fs/Pipe.v`; the
argument for the guard is on `Sys/Fs/Pipe.lean`'s `pipe2_spec`. -/

/-- THE MUTATION TEST, MADE PERMANENT: the walk beneath the guard WRAPS
(`State.read_bytes_map` advances in word arithmetic) and reads all eight
bytes off a memory mapping only those eight, so it would call the
destination writable.  Pinned beside the guard so the three checks below
cannot go vacuous: they would also pass if the map stopped backing the
range.
rocq-twin: pipe2_wrap_would_pass_the_bare_walk -/
theorem pipe2_wrap_would_pass_the_bare_walk :
    read_bytes_map pipe2_wrap_mem pipe2_wrap_fildes (Z_to_bv 64 8) ≠ none := by decide

/-- The guard declines it: `State.access_okb`, the model's transcription
of `__access_ok`, written as a subtraction so the wrapping sum is never
formed, refuses the range on its `addr <= TASK_SIZE - size` half.
rocq-twin: pipe2_wrap_fildes_is_not_access_ok
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pipe2_wrap_fildes_is_not_access_ok : access_okb pipe2_wrap_fildes 8 = false := by decide

/-- The whole answer on the wrapping destination: -EFAULT with nothing
changed, or one of the three injectable errnos.  The errnos are the
inversion `Sys/Fs/Pipe.lean` names: `__do_pipe_flags` allocates before the
copy is attempted, so a task short of two descriptors answers -EMFILE and
never reaches `access_ok`; the model allows both.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags,create_pipe_files; fs/file.c:alloc_fd,alloc_fdtable; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem wrapping_fildes_is_efault_or_injected (o : outcome SyscallEffect) :
    pipe2_spec pipe2_wrap_fildes 0 (pipe2_in pipe2_wrap_fildes 0 pipe2_wrap_mem) demo_model o ↔
      ((o = Ok (mkEffect (errno_ret EMFILE) [] []) demo_model []
        ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) demo_model []
        ∨ o = Ok (mkEffect (errno_ret ENOMEM) [] []) demo_model [])
       ∨ o = Ok (mkEffect (errno_ret EFAULT) [] []) demo_model []) := by
  sys_norm

/-- THE NEGATIVE HALF, AND THE ONE THAT MATTERS: the effect offered here is
EXACTLY the answer the model used to give — return 0 with the two
descriptor numbers stored as one 8-byte range at `2^64 - 4` and, once the
word wrapped, at 0.  Linux cannot produce it: the copy is refused by
`access_ok` before a byte moves and the `fput`/`put_unused_fd` pair at
:1041-1045 undoes both reservations.  The pair is spelled as bytes so the
rejection is of a concrete stored value.
rocq-twin: pipe2_wrapping_fildes_rejects_the_pair
kernel: fs/pipe.c:do_pipe2; include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pipe2_wrapping_fildes_rejects_the_pair (m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_wrap_fildes 0 (pipe2_in pipe2_wrap_fildes 0 pipe2_wrap_mem) demo_model
        (Ok (mkEffect (Z_to_bv 64 0) [(pipe2_wrap_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-- …and the positive half, which is Linux's own answer: -EFAULT, no write,
and the model unchanged — no pipe in `m_pipes` and no descriptor in
`m_fds`.  The probe's `wrapfildes`.
rocq-twin: pipe2_wrapping_fildes_is_efault
probe: testing/syscall-check/tests/pipe2_spec.c#conform -- wrapfildes -/
theorem pipe2_wrapping_fildes_is_efault :
    pipe2_spec pipe2_wrap_fildes 0 (pipe2_in pipe2_wrap_fildes 0 pipe2_wrap_mem) demo_model
      (Ok (mkEffect (errno_ret EFAULT) [] []) demo_model []) := by
  sys_norm

/-- The refused range is Linux's exact -EFAULT and not a fail-closed
stand-in: one `access_ok` covers all eight bytes (:1040), so a refused
range moves no byte and there is no partial write to decline over.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem wrapping_fildes_unmodeled_rejected :
    ¬ pipe2_spec pipe2_wrap_fildes 0 (pipe2_in pipe2_wrap_fildes 0 pipe2_wrap_mem) demo_model
        Unmodeled := by
  sys_refute

/-! ## The pair, on a destination the copy accepts

`__do_pipe_flags` reserves the read end first and the write end second
(fs/pipe.c:994-1006, v6.18.46), each through `get_unused_fd_flags` (fs/file.c:620-623, v6.18.46)
— `alloc_fd(0, nofile, flags)` (:615-618), the first clear bit of
`open_fds` at or above the `next_fd` hint (:580-585, `find_next_fd`), a
hint `__put_unused_fd` (:626-632) lowers to every freed descriptor, so the
answer is the lowest free number — and the bit `alloc_fd` sets at :606
marks the first before the second scan runs, so `fd[0] < fd[1]`.  `do_pipe2`
then copies both as ONE `int fildes[2]` (:1040) and installs both
(:1047-1048).  On the demo process the pair is (3, 4). -/

/-- The flat destination passes the guard.
rocq-twin: pipe2_flat_fildes_is_access_ok
kernel: include/asm-generic/access_ok.h:__access_ok@v6.18.46 -/
theorem pipe2_flat_fildes_is_access_ok : access_okb pipe2_flat_fildes 8 = true := by decide

/-- THE WHOLE ANSWER on a fresh process: one of the three injectable errnos
with nothing changed, or return 0, the pair (3, 4) stored as one 8-byte
little-endian range at `fildes`, both ends installed and an empty pipe
bound — `one_pipe_model`.  No other fd, no other errno, no decline, no
second range.  The probe's `fresh`.
probe: testing/syscall-check/tests/pipe2_spec.c#conform -- fresh -/
theorem fresh_pair_iff (o : outcome SyscallEffect) :
    pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) demo_model o ↔
      ((o = Ok (mkEffect (errno_ret EMFILE) [] []) demo_model []
        ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) demo_model []
        ∨ o = Ok (mkEffect (errno_ret ENOMEM) [] []) demo_model [])
       ∨ o = Ok (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) one_pipe_model []) := by
  sys_norm

/-- WHERE THE NARROWING LANDS: the same call on an UNWRAPPED destination
with the same eight bytes backed still succeeds and still installs the
pair, so the guard above refuses the wrapping range and not every range.
The pair is spelled as bytes: 3 then 4, each a little-endian `int`.
rocq-twin: pipe2_unwrapped_fildes_still_installs_the_pair
probe: testing/syscall-check/tests/pipe2_spec.c#conform -- fresh -/
theorem pipe2_unwrapped_fildes_still_installs_the_pair :
    pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) demo_model
      (Ok (mkEffect (Z_to_bv 64 0) [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] [])
          one_pipe_model []) :=
  (fresh_pair_iff _).mpr (Or.inr rfl)

/-- …and -EFAULT is refused THERE: the errno the wrapping destination earns
is a lie on the destination the guard accepts and the copy completes.
rocq-twin: pipe2_unwrapped_fildes_rejects_efault
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem pipe2_unwrapped_fildes_rejects_efault (m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) demo_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- A modeled call declines nothing: `Unmodeled` is refused on the fresh
process.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem fresh_pair_unmodeled_rejected :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) demo_model
        Unmodeled := by
  sys_refute

/-- The only success return is 0 (`do_pipe2` returns `error`, left 0 by
`__do_pipe_flags` at :1007): a 1 is a lie.
probe: testing/syscall-check/tests/pipe2_spec.c#reject --mutate pipe2:ret=1 -- fresh -/
theorem fresh_pair_ret_one_rejected (m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) demo_model
        (Ok (mkEffect 1 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-- The descriptors must be reported: a success that wrote nothing is
refused, whatever table it claims to leave.
probe: testing/syscall-check/tests/pipe2_spec.c#reject --mutate pipe2:drop-writes -- fresh -/
theorem fresh_pair_drop_writes_rejected (m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) demo_model
        (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- ONE contiguous 8-byte `copy_to_user`, not two 4-byte ones: a kernel
reporting the pair as two ranges is refused.
probe: testing/syscall-check/tests/pipe2_spec.c#reject --mutate pipe2:split-writes -- fresh -/
theorem fresh_pair_split_writes_rejected (m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) demo_model
        (Ok (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0]), (4100, [4, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-- The pair lands at `fildes` exactly.
probe: testing/syscall-check/tests/pipe2_spec.c#reject --mutate pipe2:shift-writes:1 -- fresh -/
theorem fresh_pair_shift_writes_rejected (m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) demo_model
        (Ok (mkEffect 0 [(4097, [3, 0, 0, 0, 4, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-- pipe2 touches no byte outside the pair.
probe: testing/syscall-check/tests/pipe2_spec.c#reject --mutate pipe2:smuggle-write:a0:1 -- fresh -/
theorem fresh_pair_smuggled_write_rejected (m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) demo_model
        (Ok (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0]), (pipe2_flat_fildes, [0])] [])
            m' evs) := by
  sys_refute

/-- pipe2 grants no memory.
probe: testing/syscall-check/tests/pipe2_spec.c#reject --mutate pipe2:smuggle-zeros:a0:1 -- fresh -/
theorem fresh_pair_smuggled_zeros_rejected (m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) demo_model
        (Ok (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] [(pipe2_flat_fildes, 1)])
            m' evs) := by
  sys_refute

/-- pipe2 unmaps no memory.
probe: testing/syscall-check/tests/pipe2_spec.c#reject --mutate pipe2:smuggle-unmap:a0:1 -- fresh -/
theorem fresh_pair_smuggled_unmap_rejected (m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) demo_model
        (Ok (SyscallEffect.mkEffectU 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []
              [(pipe2_flat_fildes, 1)] [] [])
            m' evs) := by
  sys_refute

/-- The fd table must gain both ends: a success that leaves the demo
process as it was is refused on the pipe table, which `fd_install` and the
new `pipe_inode_info` both change.
kernel: fs/pipe.c:do_pipe2,get_pipe_inode@v6.18.46 -/
theorem fresh_pair_unchanged_model_rejected (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) demo_model
        (Ok (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) demo_model evs) := by
  intro h
  rcases (fresh_pair_iff _).mp h with (h' | h' | h') | h'
  · have hr := congrArg outcome_ret h'
    simp only [outcome_ret] at hr
    exact absurd hr (by decide)
  · have hr := congrArg outcome_ret h'
    simp only [outcome_ret] at hr
    exact absurd hr (by decide)
  · have hr := congrArg outcome_ret h'
    simp only [outcome_ret] at hr
    exact absurd hr (by decide)
  · have hp := congrArg outcome_pipe_count h'
    simp only [outcome_pipe_count] at hp
    exact absurd hp (by decide)

/-! ### Lies in the bytes themselves

Each of these goes through `fresh_pair_iff` (the file header says why):
the forged outcome is one of its four `Ok`s or none, and each is refuted on
a literal — an errno against the return 0, or the pair's bytes against the
forged ones. -/

/-- Both descriptors, not just the read end: a truncated pair is refused.
probe: testing/syscall-check/tests/pipe2_spec.c#reject --mutate pipe2:trunc-writes:4 -- fresh -/
theorem fresh_pair_trunc_writes_rejected (m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) demo_model
        (Ok (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0])] []) m' evs) := by
  intro h
  have h' := (fresh_pair_iff _).mp h
  sys_refute at h'

/-- The fd numbers must be the ones the model computed: poisoned bytes are
refused.
probe: testing/syscall-check/tests/pipe2_spec.c#reject --mutate pipe2:poison-writes:255 -- fresh -/
theorem fresh_pair_poisoned_rejected (m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) demo_model
        (Ok (mkEffect 0 [(pipe2_flat_fildes, [255, 255, 255, 255, 255, 255, 255, 255])] [])
            m' evs) := by
  intro h
  have h' := (fresh_pair_iff _).mp h
  sys_refute at h'

/-- Read end first: `fd[0] = fdr` (fs/pipe.c:1005, v6.18.46) is the FIRST
`get_unused_fd_flags` (:994), so the pair (4, 3) is a lie.
kernel: fs/pipe.c:__do_pipe_flags@v6.18.46 -/
theorem fresh_pair_swapped_ends_rejected (m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) demo_model
        (Ok (mkEffect 0 [(pipe2_flat_fildes, [4, 0, 0, 0, 3, 0, 0, 0])] []) m' evs) := by
  intro h
  have h' := (fresh_pair_iff _).mp h
  sys_refute at h'

/-- Never the same descriptor twice: `__set_open_fd` (fs/file.c:333-340, v6.18.46),
called by `alloc_fd` at fs/file.c:606, marks the read end before the second
scan, so (3, 3) is a lie.
kernel: fs/file.c:alloc_fd@v6.18.46 -/
theorem fresh_pair_same_end_twice_rejected (m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) demo_model
        (Ok (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 3, 0, 0, 0])] []) m' evs) := by
  intro h
  have h' := (fresh_pair_iff _).mp h
  sys_refute at h'

/-- Lowest free, both times: `alloc_fd` scans from the larger of `start` and
the `next_fd` hint (fs/file.c:580-582, v6.18.46) — 0 in a table `dup_fd`
built (fs/file.c:399), which is what a fresh process holds, and never above
the lowest free number under any of the hint's three writers (:399,
:603-604, :630-631) — and `find_next_fd` (fs/file.c:544-565, v6.18.46)
returns the first clear bit from there — 3, then 4 — never (4, 5).
kernel: fs/file.c:alloc_fd,find_next_fd@v6.18.46 -/
theorem fresh_pair_non_lowest_rejected (m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) demo_model
        (Ok (mkEffect 0 [(pipe2_flat_fildes, [4, 0, 0, 0, 5, 0, 0, 0])] []) m' evs) := by
  intro h
  have h' := (fresh_pair_iff _).mp h
  sys_refute at h'

/-! ### Across a page boundary: still one range -/

/-- A `fildes` four bytes below a page boundary is one 8-byte effect range,
because there is one `copy_to_user` (:1040) whatever pages it crosses.
The probe's `straddle`.
probe: testing/syscall-check/tests/pipe2_spec.c#conform -- straddle -/
theorem straddle_pair_iff (o : outcome SyscallEffect) :
    pipe2_spec pipe2_straddle_fildes 0 (pipe2_in pipe2_straddle_fildes 0 pipe2_straddle_mem)
        demo_model o ↔
      ((o = Ok (mkEffect (errno_ret EMFILE) [] []) demo_model []
        ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) demo_model []
        ∨ o = Ok (mkEffect (errno_ret ENOMEM) [] []) demo_model [])
       ∨ o = Ok (mkEffect 0 [(pipe2_straddle_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] [])
             one_pipe_model []) := by
  sys_norm

/-- …still ONE range, even split across two pages.
probe: testing/syscall-check/tests/pipe2_spec.c#reject --mutate pipe2:split-writes -- straddle -/
theorem straddle_pair_split_writes_rejected (m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_straddle_fildes 0 (pipe2_in pipe2_straddle_fildes 0 pipe2_straddle_mem)
        demo_model
        (Ok (mkEffect 0 [(pipe2_straddle_fildes, [3, 0, 0, 0]), (8192, [4, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-! ## The second pipe, and the hole

The pair is RELATIONAL: each end is the lowest free number at the moment
it is taken (`alloc_fd`, fs/file.c:570-613, v6.18.46), so a second pipe of the same
process takes (5, 6), and a process with fd 3 free below a live fd 4 gets
(3, 5).  The pipe id counts creations (`State.pipe_new_id`), so the second
pipe is bound at 1 with the first pipe's entry kept — as Linux allocates a
fresh `pipe_inode_info` per call (`get_pipe_inode`, fs/pipe.c:886-924,
v6.18.46)
and never hands one pipe's buffer to another.  The probe's `holes`. -/

/-- The second pipe of the demo process: (5, 6), pipe 1, over
`one_pipe_model`.
probe: testing/syscall-check/tests/pipe2_spec.c#conform -- holes -/
theorem second_pair_iff (o : outcome SyscallEffect) :
    pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) one_pipe_model o ↔
      ((o = Ok (mkEffect (errno_ret EMFILE) [] []) one_pipe_model []
        ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) one_pipe_model []
        ∨ o = Ok (mkEffect (errno_ret ENOMEM) [] []) one_pipe_model [])
       ∨ o = Ok (mkEffect 0 [(pipe2_flat_fildes, [5, 0, 0, 0, 6, 0, 0, 0])] []) two_pipe_model []) := by
  sys_norm

/-- The first pipe's descriptors are taken: (3, 4) again is a lie.
kernel: fs/file.c:alloc_fd,find_next_fd@v6.18.46 -/
theorem second_pair_first_numbers_rejected (m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) one_pipe_model
        (Ok (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) m' evs) := by
  intro h
  have h' := (second_pair_iff _).mp h
  sys_refute at h'

/-- A second pipe REUSING the first pipe's id — binding the new ends to the
old queue — is refused: `reused_id_model` has one pipe entry where the
kernel has two `pipe_inode_info`s.  Through the `iff`, on the pipe list.
kernel: fs/pipe.c:get_pipe_inode,alloc_pipe_info@v6.18.46 -/
theorem second_pair_reused_id_rejected (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) one_pipe_model
        (Ok (mkEffect 0 [(pipe2_flat_fildes, [5, 0, 0, 0, 6, 0, 0, 0])] []) reused_id_model evs) := by
  intro h
  rcases (second_pair_iff _).mp h with (h' | h' | h') | h'
  · have hr := congrArg outcome_ret h'
    simp only [outcome_ret] at hr
    exact absurd hr (by decide)
  · have hr := congrArg outcome_ret h'
    simp only [outcome_ret] at hr
    exact absurd hr (by decide)
  · have hr := congrArg outcome_ret h'
    simp only [outcome_ret] at hr
    exact absurd hr (by decide)
  · have hp := congrArg outcome_pipe_count h'
    simp only [outcome_pipe_count] at hp
    exact absurd hp (by decide)

/-- Over the hole: the read end fills 3 and the write end skips the live 4
for 5.  Closing 3 lowered the table's `next_fd` hint to 3 (`__put_unused_fd`,
fs/file.c:626-632, v6.18.46), `alloc_fd` starts there (fs/file.c:580-582), and
`find_next_fd` (fs/file.c:544-565, v6.18.46) scans the bitmap past the live
4 — the hint is a floor on the scan, never the answer.  The probe's `holes`
runs on a bigger table and is pinned on it below (`holes_probe_pair_iff`).
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags,create_pipe_files; fs/file.c:alloc_fd,alloc_fdtable,find_next_fd,__put_unused_fd@v6.18.46 -/
theorem holes_pair_iff (o : outcome SyscallEffect) :
    pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) holes_model o ↔
      ((o = Ok (mkEffect (errno_ret EMFILE) [] []) holes_model []
        ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) holes_model []
        ∨ o = Ok (mkEffect (errno_ret ENOMEM) [] []) holes_model [])
       ∨ o = Ok (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 5, 0, 0, 0])] []) holes_after_model []) := by
  sys_norm

/-- Poisoned bytes are refused over the hole too.
kernel: fs/file.c:alloc_fd,find_next_fd@v6.18.46 -/
theorem holes_pair_poisoned_rejected (m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) holes_model
        (Ok (mkEffect 0 [(pipe2_flat_fildes, [5, 5, 5, 5, 5, 5, 5, 5])] []) m' evs) := by
  intro h
  have h' := (holes_pair_iff _).mp h
  sys_refute at h'

/-- …and (3, 4), the answer of a model that took "the next number up"
rather than the next FREE one, is refused: 4 is live.
kernel: fs/file.c:alloc_fd,find_next_fd@v6.18.46 -/
theorem holes_pair_consecutive_rejected (m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) holes_model
        (Ok (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) m' evs) := by
  intro h
  have h' := (holes_pair_iff _).mp h
  sys_refute at h'

/-- THE PROBE'S OWN TABLE: over `holes_probe_model` the read end fills the
freed 3 and the write end takes 7, the first number above the three live
pipe ends — the probe's third pipe, `(fda[0], fdb[1] + 1)`.
probe: testing/syscall-check/tests/pipe2_spec.c#conform -- holes -/
theorem holes_probe_pair_iff (o : outcome SyscallEffect) :
    pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) holes_probe_model o ↔
      ((o = Ok (mkEffect (errno_ret EMFILE) [] []) holes_probe_model []
        ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) holes_probe_model []
        ∨ o = Ok (mkEffect (errno_ret ENOMEM) [] []) holes_probe_model [])
       ∨ o = Ok (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 7, 0, 0, 0])] [])
             holes_probe_after_model []) := by
  sys_norm

/-- The third pipe's fds are computed, not chosen: poisoned bytes are
refused on the probe's table.
probe: testing/syscall-check/tests/pipe2_spec.c#reject --mutate pipe2#3:poison-writes:5 -- holes -/
theorem holes_probe_pair_poisoned_rejected (m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) holes_probe_model
        (Ok (mkEffect 0 [(pipe2_flat_fildes, [5, 5, 5, 5, 5, 5, 5, 5])] []) m' evs) := by
  intro h
  have h' := (holes_probe_pair_iff _).mp h
  sys_refute at h'

/-- …and (3, 4) — the freed 3 with "the next number up" — is refused there
too: 4 is the first pipe's live write end.
kernel: fs/file.c:alloc_fd,find_next_fd@v6.18.46 -/
theorem holes_probe_pair_consecutive_rejected (m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_flat_mem) holes_probe_model
        (Ok (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) m' evs) := by
  intro h
  have h' := (holes_probe_pair_iff _).mp h
  sys_refute at h'

/-! ## The destination the copy cannot use

`copy_to_user` returns the count of bytes NOT copied and `do_pipe2` turns
any nonzero count into -EFAULT with both files released and both
reservations returned (fs/pipe.c:1040-1045, v6.18.46).  Two shapes: not one byte
writable, where the copy moves nothing and the answer is Linux's own
-EFAULT; and a writable PREFIX, where the copy moves some bytes first and
how many is the copier's business. -/

/-- Not one byte of `fildes` writable — and the arm's gate is the FIRST
byte alone, `read_bytes_map … 1 = none`, because a copy whose first store
faults (`sb`, arch/riscv/lib/uaccess.S:205, v6.18.46) has moved nothing
whatever the bytes behind it: -EFAULT with nothing installed, or an
injectable errno; the model is unchanged.  qemu-user's `do_pipe` (QEMU
v11.1.1, linux-user/syscall.c) has already made the host pair when its
`put_user_s32` faults, and does not close it; as with its dropped flag bit
(`unaccepted_bit_pair_rejected`) the tree reads that as the emulator's
defect, not a behavior, so the table pinned is the one Linux leaves.
kernel: fs/pipe.c:do_pipe2,__do_pipe_flags,create_pipe_files; fs/file.c:alloc_fd,alloc_fdtable; include/linux/uaccess.h:_inline_copy_to_user@v6.18.46 -/
theorem dead_fildes_is_efault_or_injected (o : outcome SyscallEffect) :
    pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_dead_mem) demo_model o ↔
      ((o = Ok (mkEffect (errno_ret EMFILE) [] []) demo_model []
        ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) demo_model []
        ∨ o = Ok (mkEffect (errno_ret ENOMEM) [] []) demo_model [])
       ∨ o = Ok (mkEffect (errno_ret EFAULT) [] []) demo_model []) := by
  sys_norm

/-- A pair claimed on an unwritable destination is refused: the `fput` /
`put_unused_fd` pair at :1041-1044 undoes both reservations.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem dead_fildes_pair_rejected (m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_dead_mem) demo_model
        (Ok (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-- …and the -EFAULT is Linux's exact answer, not a decline: nothing was
copied, so nothing is left to be uncertain about.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem dead_fildes_unmodeled_rejected :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_dead_mem) demo_model
        Unmodeled := by
  sys_refute

/-- A WRITABLE PREFIX declines — the probe's `partial`.  What Linux does on
riscv64 is definite, on both of its copy paths.  `__asm_copy_to_user`
(arch/riscv/lib/uaccess.S:15-23, v6.18.46) takes the scalar copier for a
count under `riscv_v_usercopy_threshold` (arch/riscv/lib/riscv_v_helpers.c:17,
v6.18.46), a Kconfig int, RISCV_ISA_V_UCOPY_THRESHOLD, defaulting to 768 and
unbounded (arch/riscv/Kconfig:645-651, v6.18.46), so 8 bytes take it on a
default kernel — and that copier's byte tail
(`fallback_scalar_usercopy_sum_enabled`, arch/riscv/lib/uaccess.S:56-77 for
the dispatch to `.Lbyte_copy_tail`, :193-207 for the tail, v6.18.46) stores a
byte at a time until the fault; a kernel configured to take the vector
copier at 8 bytes stores the same prefix, because a faulting vector store is
fixed up from the vstart CSR (arch/riscv/lib/uaccess_vector.S:44-60, v6.18.46) and
`enter_vector_usercopy` (arch/riscv/lib/riscv_v_helpers.c:22-45, v6.18.46)
resumes the scalar copy at the copied offset.  So the read end's four bytes
land and the write end's first byte faults; `do_pipe2` then releases both
files and both reservations and returns -EFAULT (fs/pipe.c:1040-1045,
v6.18.46).  WHY THE MODEL STILL DECLINES: the stored prefix is the copier's,
not the syscall's, and Rocq's arm does not state it; qemu-user's own copier
(`do_pipe`, QEMU v11.1.1, linux-user/syscall.c: the host `pipe2`, then two
`put_user_s32`) leaves the same four bytes and, unlike Linux, the host pair
open — the leak `dead_fildes_is_efault_or_injected` reads as the emulator's
defect.  So an answer exists, the four bytes and -EFAULT with nothing
installed, and this decline is a COVERAGE GAP of the Rocq arm, mirrored:
`Unmodeled` is a sound answer that costs priority 3 only, and stating the
prefix on the Rocq side is what would close it.
probe: testing/syscall-check/tests/pipe2_spec.c#fail-closed -- partial -/
theorem half_fildes_is_unmodeled (o : outcome SyscallEffect) :
    pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_half_mem) demo_model o ↔
      o = Unmodeled := by
  sys_norm

/-- The kernel's own -EFAULT is refused there: a decline is not the errno
with the prefix left unstated.
probe: testing/syscall-check/tests/pipe2_spec.c#fail-closed -- partial -/
theorem half_fildes_efault_rejected (m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_half_mem) demo_model
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- …and so is the pair, which four writable bytes cannot hold.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem half_fildes_pair_rejected (m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_half_mem) demo_model
        (Ok (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-- Seven writable bytes are a prefix too: `sizeof(fd)` is 8 (:1040), and
the eighth byte's fault is the same decline.
kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem seven_bytes_is_unmodeled (o : outcome SyscallEffect) :
    pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_seven_mem) demo_model o ↔
      o = Unmodeled := by
  sys_norm

/-- kernel: fs/pipe.c:do_pipe2@v6.18.46 -/
theorem seven_bytes_pair_rejected (m' : Model) (evs : List event) :
    ¬ pipe2_spec pipe2_flat_fildes 0 (pipe2_in pipe2_flat_fildes 0 pipe2_seven_mem) demo_model
        (Ok (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-! ## The dispatcher: `pipe2` is number 59, and `flags` is an `int`

`SYSCALL_DEFINE2(pipe2, int __user *, fildes, int, flags)` (fs/pipe.c:1054, v6.18.46):
a1 is narrowed to its low 32 bits (`Syscall.pipe_flags32`) before
`__do_pipe_flags` sees it, so `2^32` is 0 and `2^32 + 2^30` is `2^30`.
riscv64 generates its table from scripts/syscall.tbl (`59 common pipe2`,
:77, v6.18.46), the number asm-generic's `__NR_pipe2` also carries; the pin
below cites the header because that is where the value is a definition. -/

/-- kernel: include/uapi/asm-generic/unistd.h:__NR_pipe2@v6.18.46 -/
theorem pipe2_is_dispatched : (59 : Int) ∈ modeled_sysnos := by decide

/-- `flags = 2^32 + 2^30`: the high word is gone and bit 30 stays, so the
call is -EINVAL through the table.
kernel: fs/pipe.c:pipe2,__do_pipe_flags@v6.18.46 -/
theorem dispatched_flags_truncate_to_einval (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (pipe2_in pipe2_flat_fildes 5368709120 pipe2_flat_mem) m o ↔
      o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_norm

/-- `flags = 2^32` is `flags = 0`: through the table, the whole answer is
the fresh process's.
kernel: fs/pipe.c:pipe2,do_pipe2,__do_pipe_flags,create_pipe_files; fs/file.c:alloc_fd,alloc_fdtable@v6.18.46 -/
theorem dispatched_flags_two_pow_32_iff (o : outcome SyscallEffect) :
    syscall_spec (pipe2_in pipe2_flat_fildes 4294967296 pipe2_flat_mem) demo_model o ↔
      ((o = Ok (mkEffect (errno_ret EMFILE) [] []) demo_model []
        ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) demo_model []
        ∨ o = Ok (mkEffect (errno_ret ENOMEM) [] []) demo_model [])
       ∨ o = Ok (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) one_pipe_model []) := by
  sys_norm

/-- …so the pair is allowed through the table.
kernel: fs/pipe.c:pipe2,do_pipe2@v6.18.46 -/
theorem dispatched_flags_truncate_to_zero_installs_the_pair :
    syscall_spec (pipe2_in pipe2_flat_fildes 4294967296 pipe2_flat_mem) demo_model
      (Ok (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) one_pipe_model []) :=
  (dispatched_flags_two_pow_32_iff _).mpr (Or.inr rfl)

/-- …and a model reading all 64 bits would answer -EINVAL to it: refused.
kernel: fs/pipe.c:pipe2,__do_pipe_flags@v6.18.46 -/
theorem dispatched_flags_two_pow_32_einval_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pipe2_in pipe2_flat_fildes 4294967296 pipe2_flat_mem) demo_model
        (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- `fildes` is a POINTER and reaches the spec whole: `SYSCALL_DEFINE2(pipe2,
int __user *, fildes, int, flags)` (fs/pipe.c:1054, v6.18.46) narrows `flags`
to an `int` and `fildes` not at all, so a destination above 2^32 is written
where it is, and the pair lands at `2^32 + 4096`.
kernel: fs/pipe.c:pipe2,do_pipe2,__do_pipe_flags,create_pipe_files; fs/file.c:alloc_fd,alloc_fdtable@v6.18.46 -/
theorem dispatched_fildes_passes_whole (o : outcome SyscallEffect) :
    syscall_spec (pipe2_in pipe2_high_fildes 0 pipe2_high_mem) demo_model o ↔
      ((o = Ok (mkEffect (errno_ret EMFILE) [] []) demo_model []
        ∨ o = Ok (mkEffect (errno_ret ENFILE) [] []) demo_model []
        ∨ o = Ok (mkEffect (errno_ret ENOMEM) [] []) demo_model [])
       ∨ o = Ok (mkEffect 0 [(pipe2_high_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) one_pipe_model []) := by
  sys_norm

/-- A model that narrowed a0 to 32 bits would store the pair at 4096: refused.
kernel: fs/pipe.c:pipe2@v6.18.46 -/
theorem dispatched_fildes_truncated_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pipe2_in pipe2_high_fildes 0 pipe2_high_mem) demo_model
        (Ok (mkEffect 0 [(4096, [3, 0, 0, 0, 4, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-- `flags = 2^32 + O_NONBLOCK` is `O_NONBLOCK`: the pair is refused through
the table, as the spec-level decline says.
kernel: fs/pipe.c:pipe2,__do_pipe_flags@v6.18.46 -/
theorem dispatched_flags_nonblock_pair_rejected (m' : Model) (evs : List event) :
    ¬ syscall_spec (pipe2_in pipe2_flat_fildes 4294969344 pipe2_flat_mem) demo_model
        (Ok (mkEffect 0 [(pipe2_flat_fildes, [3, 0, 0, 0, 4, 0, 0, 0])] []) m' evs) := by
  sys_refute

/-! ## A pipe end at `fcntl`'s F_SETFD

The one arm outside fs/pipe.c whose pipe case has no other Lean home.
`do_fcntl` answers `F_SETFD` with `err = 0; set_close_on_exec(fd, argi &
FD_CLOEXEC);` (fs/fcntl.c:468-471, v6.18.46) reading nothing of the file —
what runs before it in `SYSCALL_DEFINE3(fcntl)` (fs/fcntl.c:574-592), the
FMODE_PATH test (:582-585) and `security_file_fcntl` (:587), is the same
for every fd kind and is the LSM commitment `Sys/Fs/Fcntl.lean` declares —
so a pipe end gets the same 0 every other fd does; pinned because
"the pipe end declines at fcntl" (F_SETFL, F_GETFL) would otherwise read as
covering this too. -/

/-- F_SETFD (2) with FD_CLOEXEC (1) on the read end of a pipe is 0, and the
model is untouched.
rocq-twin: fcntl_setfd_on_a_pipe_end_is_zero
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem fcntl_setfd_on_a_pipe_end_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    fcntl_spec 3 2 1 i pipe_model o ↔ o = Ok (mkEffect 0 [] []) pipe_model [] := by
  sys_norm

/-- The write end too.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem fcntl_setfd_on_a_pipe_writer_is_zero (i : SyscallInput) (o : outcome SyscallEffect) :
    fcntl_spec 4 2 1 i pipe_model o ↔ o = Ok (mkEffect 0 [] []) pipe_model [] := by
  sys_norm

/-- A pipe end is an OPEN descriptor: -EBADF is a lie here.
kernel: fs/fcntl.c:do_fcntl@v6.18.46 -/
theorem fcntl_setfd_on_a_pipe_end_ebadf_rejected (i : SyscallInput) (m' : Model)
    (evs : List event) :
    ¬ fcntl_spec 3 2 1 i pipe_model (Ok (mkEffect (errno_ret EBADF) [] []) m' evs) := by
  sys_refute

/-! ## fstat and pselect6 over a pipe end: Rocq's other worked cases

Rocq's `Checks/Cases/Fs/Pipe.v` pins the arms `State.FdPipe` forces at
`fstat` and `pselect6` on ITS `pipe_model`; the Lean Cases files of those
arms hold a read end only (`Checks/Cases/Fs/Stat.lean`'s `fstat_kinds_fds`,
`Checks/Cases/Fs/Select.lean`'s `pselect_kinds_fds`), so the write end and
the two `Select` predicates are pinned here, on the same `pipe_model`. -/

/-- fstat (80) on the read end declines: S_IFIFO is known and a pipe's
`st_size` and `st_blocks` are not the queue's length.  Same fixture and
answer for the write end below; the closed fd 9 keeps the pair from being
vacuous.
rocq-twin: fstat_on_a_pipe_end_declines
kernel: fs/stat.c:vfs_fstat,cp_new_stat@v6.18.46 -/
theorem fstat_on_a_pipe_end_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    Sys.Fs.Stat.fstat_spec 3 4096 i pipe_model o ↔ o = Unmodeled := by
  sys_norm

/-- …the write end too.
kernel: fs/stat.c:vfs_fstat,cp_new_stat@v6.18.46 -/
theorem fstat_on_a_pipe_write_end_declines (i : SyscallInput) (o : outcome SyscallEffect) :
    Sys.Fs.Stat.fstat_spec 4 4096 i pipe_model o ↔ o = Unmodeled := by
  sys_norm

/-- …while a CLOSED fd is a real -EBADF from `vfs_fstat` before `statbuf` is
touched, so the two declines above are the arm's answer and not the
dispatcher's fallback.
kernel: fs/stat.c:vfs_fstat@v6.18.46 -/
theorem fstat_on_a_closed_fd_beside_a_pipe_is_ebadf (i : SyscallInput)
    (o : outcome SyscallEffect) :
    Sys.Fs.Stat.fstat_spec 9 4096 i pipe_model o ↔
      o = Ok (mkEffect (errno_ret EBADF) [] []) pipe_model [] := by
  sys_norm

/-- pselect6's read set naming the pipe's read end, as `core_sys_select`
sees it: `n` 4, `readfds` at 4096 holding bit 3, the other two sets NULL. -/
def pselect_pipe_in : SyscallInput :=
  SyscallInput.mkInput 72 [4, 4096, 0, 0, 0, 0]
    (fun a => if bv_eqb a 4096 then some 8 else some 0) (fun _ => some 0)

/-- The same call naming the `FdFileW` at fd 5: `n` 6, bit 5. -/
def pselect_file_in : SyscallInput :=
  SyscallInput.mkInput 72 [6, 4096, 0, 0, 0, 0]
    (fun a => if bv_eqb a 4096 then some 32 else some 0) (fun _ => some 0)

-- `Select.PselectCore` carries no `DecidableEq` of its own (no pin of
-- `Select.lean` compares two of its values), so the two computations below
-- are decided through this derived instance; a `deriving` on the type itself
-- would make this line redundant, not wrong.
deriving instance DecidableEq for Sys.Fs.Select.PselectCore

/-- `Select.pselect_core` gaps on the pipe end and answers on the file —
same model, same sets, only the polled fd changed — so the gap comes from
the fd's KIND through `bits_all_pollable` and from nothing else in the
call: `pipe_poll` (fs/pipe.c:660-706, v6.18.46) reports EPOLLIN only on a
non-empty ring (:690), which the model does not track, while a regular
file has no `->poll` and takes `DEFAULT_POLLMASK` from `vfs_poll`
(include/linux/poll.h, v6.18.46).
rocq-twin: pselect_core_gaps_on_a_pipe_end_only
kernel: fs/pipe.c:pipe_poll; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem pselect_core_gaps_on_a_pipe_end_only :
    Sys.Fs.Select.pselect_core pselect_pipe_in pipe_model 4 4096 0 0 = .PsCoreGap
    ∧ Sys.Fs.Select.pselect_core pselect_file_in pipe_model 6 4096 0 0 ≠ .PsCoreGap := by
  decide

/-- `Select.bits_all_pollable` is per kind: false on the pipe's read end
(bit 3), on its write end (bit 4) and on the channel at fd 0, true on the
`FdFileW` at fd 5 — the pipe end joined an existing decline rather than
creating one, and the predicate is not refusing everything.  `pipe_poll`
(fs/pipe.c:660-706, v6.18.46) reports EPOLLOUT only on a ring that is not
full (:697), so the write end is no more unconditional than the read end.
rocq-twin: pselect6_pollability_is_per_kind
kernel: fs/pipe.c:pipe_poll; include/linux/poll.h:vfs_poll@v6.18.46 -/
theorem pselect6_pollability_is_per_kind :
    Sys.Fs.Select.bits_all_pollable (m_fds pipe_model) 8 6 = false
    ∧ Sys.Fs.Select.bits_all_pollable (m_fds pipe_model) 16 6 = false
    ∧ Sys.Fs.Select.bits_all_pollable (m_fds pipe_model) 1 6 = false
    ∧ Sys.Fs.Select.bits_all_pollable (m_fds pipe_model) 32 6 = true := by
  decide

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.Pipe
