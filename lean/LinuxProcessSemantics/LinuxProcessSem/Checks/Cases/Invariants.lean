import LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.VmMapsDisjoint
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Mm.Mmap

/-! # Checks.Cases.Invariants — the cross-arm invariant registry, exercised

Pins over `Checks.Invariants`, the cross-arm invariant registry (ticket
I3).  That file mirrors no Rocq file, so neither does this one: these are
the Lean tree's tests for what the registry claims, in the place every pin
in this tree lives so that `tools/check_lean_pins.py` and
`tools/check_lean_pin_evidence.py` read them.  Not part of the trusted
specification.

WHAT IS UNDER TEST is three claims about Linux and one about a tactic.
The three are the registered invariants: no page-aligned byte of the
memory ledger has two owners, no descriptor is bound twice, and no pipe's
queue or merge mark leaves the page the pipe's one slot lives in.  Each
gets a positive pin and a refutation of the state Linux cannot be in, and
each names the kernel lines that make it Linux's rather than the model's.
The fourth is the alternation: run over a fixture registry and the
two-arm fixture table of `Checks/Cases/Checks/Sys/Dispatch.lean`, once
with every pair covered, once with one pair's fact dropped and once with
its alternative written behind the closing `| skip`, so the message the
build prints for an uncovered pair is pinned rather than described.
A last section, `DispatcherCorollaries`, is about the two theorems
`Checks/Invariants.lean` states over the dispatcher on top of the
registry: each applied at a step the tree's real table accepts, and each
premise the port added or the twin carries shown load-bearing.

THE REGISTER `tools/check_lean_invariant_pins.py` reads, one line per
registered invariant, naming the theorem that pins it positively, the one
that refutes it, the one that carries the kernel citation, and the one
that reads the entry's `holds` back to the predicate over the entry's own
view:

pins: vm_wf -- positive disjoint_grants_are_vm_wf, negative overlapping_grants_are_not_vm_wf, kernel disjoint_grants_are_vm_wf, view inv_vm_wf_holds_is_vm_wf
pins: fd_table_unique -- positive the_start_table_binds_each_descriptor_once, negative a_doubled_descriptor_is_not_unique, kernel the_start_table_binds_each_descriptor_once, view inv_fd_table_unique_reads_the_table
pins: pipes_within_capacity -- positive a_full_page_is_within_capacity, negative a_mark_past_the_page_is_not_within_capacity, kernel a_full_page_is_within_capacity, view inv_pipes_within_capacity_reads_the_pipes

That register is WRITTEN and read back rather than derived, for
`tools/check_lean_cases_parity.py`'s reason about worked cases: a
name-matching rule between an entry and the theorems that pin it cannot
survive the shapes a pin takes, and a rule that guesses reports its
guess. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint
open LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Dispatch

section VmWf

/-! ## `vm_wf`: one owner per page

The invariant itself, its lemmas and its refutations over hand-built
ledgers are `Checks/Cases/Checks/VmMapsDisjoint.lean`'s, and are not
repeated.  What the registry adds, and what is pinned here, is the KERNEL
reading: that the model's page-level uniqueness is a property Linux has
and not a property the model happens to have. -/

/-- TWO GRANTS THAT DO NOT OVERLAP ARE WELL FORMED, which is the state
Linux leaves behind.  A new mapping does not join an old one over the
same pages, and the step that makes that true is the DETACH, not the
completion.  `__mmap_prepare` (mm/vma.c:2386, Linux v6.18.46) gathers
every VMA overlapping `[addr, end)` — its call of
`vms_gather_munmap_vmas` (mm/vma.c:1372) is at mm/vma.c:2404 — and that
walk writes each one into the detach tree (`mas_store_gfp`,
lib/maple_tree.c:5118, called at mm/vma.c:1428) and marks it detached
(`vma_mark_detached`, mm/mmap_lock.c:106, called at mm/vma.c:1432), and — still inside `__mmap_prepare` — clears their PTEs
while they are in the tree (`vms_clean_up_area`, mm/vma.c:1281, called
at mm/vma.c:2441, running `vms_clear_ptes` (mm/vma.c:1255) at
mm/vma.c:1289).  Only then
does `__mmap_region` (mm/vma.c:2682) store the new VMA over the range,
by `vma_merge_new_range` (mm/vma.c:1043), called at mm/vma.c:2708, or
`__mmap_new_vma` (mm/vma.c:2495), called at mm/vma.c:2713, which stores
through `vma_iter_store_new` (mm/vma.h:553) at mm/vma.c:2542.
GET THE ORDER RIGHT, because the obvious reading is wrong:
`__mmap_complete` (mm/vma.c:2569) runs LAST, at mm/vma.c:2721, after the
new VMA is already in the tree, and its `vms_complete_munmap_vmas`
(mm/vma.c:1304, called at mm/vma.c:2577) finds the PTEs already cleared
(`vms->clear_ptes` was dropped at mm/vma.c:1278, so its own call of
`vms_clear_ptes` (mm/vma.c:1255), at mm/vma.c:1319, returns at once),
fixes the accounting
and `remove_vma`s the detached VMAs — it frees them, it does not unmap
them out from under the new one.  So no page is ever reachable through
two attached VMAs, which is `page_owner_unique` read at page
granularity.
kernel: mm/vma.c:__mmap_prepare,__mmap_region,vms_gather_munmap_vmas,vms_complete_munmap_vmas@v6.18.46 -/
theorem disjoint_grants_are_vm_wf :
    vm_wf (VmMaps.mkVmMapsFull [] [(65536, 4096), (69632, 4096)] [] 65536 69632 0 0 0) := by
  refine ⟨?_, ?_⟩
  · intro e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl <;> decide
  · intro p hp
    have e1 : bv_unsigned (65536 : word) = 65536 := by decide
    have e2 : bv_unsigned (69632 : word) = 69632 := by decide
    have e3 : bv_unsigned (4096 : word) = 4096 := by decide
    simp only [page_size] at hp
    show owners [((65536 : word), (4096 : word)), (69632, 4096)] p ≤ 1
    simp only [owners, owns_b, e1, e2, e3, Bool.and_eq_true, decide_eq_true_eq, Nat.add_zero]
    split <;> split <;> omega

/-- …AND THE OVERLAP IS REFUSED.  The same two kernel steps are why no
run reaches a ledger with one page-aligned base twice, and WHICH PATH a
second mmap over 65536 takes is the flags' to choose, not one path for
all: with `MAP_FIXED`, `generic_get_unmapped_area` hands the address
back as asked (mm/mmap.c:700-701) and `__mmap_prepare` detaches what was
there, so the new grant REPLACES the old rather than adding to it; with
no flag, an occupied hint is dropped and a free range found instead
(mm/mmap.c:703-709, the `if (addr)` test whose failure falls through to
`vm_unmapped_area`); with `MAP_FIXED_NOREPLACE`, `do_mmap` answers
`-EEXIST` on the intersection (mm/mmap.c:410-412).  None of the three
leaves two attached VMAs over one page.  A model state holding both is a
state Linux is never in, so the invariant must refuse it, and this is
the refutation the registry's `inv_refused` field carries.
kernel: mm/vma.c:__mmap_prepare,__mmap_complete; mm/mmap.c:do_mmap,generic_get_unmapped_area@v6.18.46 -/
theorem overlapping_grants_are_not_vm_wf :
    ¬ vm_wf (VmMaps.mkVmMapsFull [] [(65536, 4096), (65536, 100)] [] 65536 69632 0 0 0) := by
  intro h
  -- `vm_wf` is a `def`, so `h.2`'s subject is the record's `vm_maps`
  -- projection while `h2`'s is the literal list.  The ascription is what
  -- makes `omega` see one term rather than two atoms.
  have h' : sizes_nonzero [((65536 : word), (4096 : word)), (65536, 100)] ∧
      page_owner_unique [((65536 : word), (4096 : word)), (65536, 100)] := h
  have h1 := h'.2 65536 (by decide)
  have h2 : owners [((65536 : word), (4096 : word)), (65536, 100)] 65536 = 2 := by decide
  omega

/-- …AND SO IS AN OVERLAP OF ONE BYTE, at the other boundary of the
positive pin: the grants that pin accepts meet exactly at 69632, and a
first grant one byte longer reaches into the second's page.  In Linux
there is no one-byte overlap to begin with: `do_mmap` rounds the length
up (`PAGE_ALIGN(len)`, mm/mmap.c:368), so the 4097-byte grant IS a
two-page grant whose second page is the page the second grant asks for.
`vms_gather_munmap_vmas` then detaches exactly the overlapped pages and
not the whole VMA -- it splits the first VMA at the range's start and
at its end (`__split_vma`, mm/vma.c:488, called at mm/vma.c:1401 and
:1422) and detaches what lies between -- so the byte-granular ledger the model
keeps is refuted at the page Linux would have taken away.  Either way
the state with both attached is as unreachable as the shared-base one.
kernel: mm/vma.c:__mmap_prepare,vms_gather_munmap_vmas,__split_vma; mm/mmap.c:do_mmap@v6.18.46 -/
theorem a_one_byte_overlap_is_not_vm_wf :
    ¬ vm_wf (VmMaps.mkVmMapsFull [] [(65536, 4097), (69632, 4096)] [] 65536 69632 0 0 0) := by
  intro h
  have h' : sizes_nonzero [((65536 : word), (4097 : word)), (69632, 4096)] ∧
      page_owner_unique [((65536 : word), (4097 : word)), (69632, 4096)] := h
  have h1 := h'.2 69632 (by decide)
  have h2 : owners [((65536 : word), (4097 : word)), (69632, 4096)] 69632 = 2 := by decide
  omega

/-- The registry's entry is that invariant and not a near miss: its
`holds` at a model is `vm_wf` of that model's ledger, by definition.
model: `Invariant.holds` at `inv_vm_wf`, unfolded -/
theorem inv_vm_wf_holds_is_vm_wf (m : Model) : inv_vm_wf.holds m = vm_wf (m_vmmaps m) := rfl

end VmWf

section FdTableUnique

/-! ## `fd_table_unique`: one file per descriptor

The invariant Rocq does not state, pinned here before any arm is asked to
preserve it.  Its kernel reading is the strongest of the three, because
the kernel asserts it of itself. -/

/-- THE DESCRIPTOR TABLE BINDS EACH DESCRIPTOR ONCE, and the process
starts that way.  Linux's table is an array indexed by the descriptor:
`fd_install` (fs/file.c:652) writes `fdt->fd[fd]` and asserts the slot
was empty first — `VFS_BUG_ON(rcu_access_pointer(fdt->fd[fd]) != NULL)`
at fs/file.c:666 and :674, on each of the two paths it takes — and
`alloc_fd` (fs/file.c:570) asserts the same of the descriptor it has just
reserved (fs/file.c:608).
THE ASSERTION IS CONFIG-GATED AND THE ARGUMENT IS NOT.  `VFS_BUG_ON` is
`BUG_ON` only under `CONFIG_DEBUG_VFS`, and `BUILD_BUG_ON_INVALID`
otherwise (include/linux/vfsdebug.h:12 and :35), so on a build without
it a doubled install would trip nothing — and CLAUDE.md's scope section
makes a configuration choice a variant the model must accept, not one
it may assume away.  What holds on EVERY configuration is the data
structure: `fdt->fd` is an array indexed by the descriptor, so one
descriptor has one slot whether or not the assertion is compiled in.
The two `VFS_BUG_ON`s are evidence that Linux means it, not the reason
it is true.  The three descriptors `init_model` starts with are 0, 1
and 2.
kernel: fs/file.c:fd_install,alloc_fd@v6.18.46 -/
theorem the_start_table_binds_each_descriptor_once :
    fd_table_unique [(Z_to_bv 64 0, FdEntry.FdChannel (Z_to_bv 64 0)),
                     (Z_to_bv 64 1, FdEntry.FdChannel (Z_to_bv 64 1)),
                     (Z_to_bv 64 2, FdEntry.FdChannel (Z_to_bv 64 2))] := by
  -- `fd_table_unique` is a `def`, so instance search does not reach the
  -- `Nodup` behind it and `decide` has nothing to run until the `show`
  -- names it.
  show (([(Z_to_bv 64 0, FdEntry.FdChannel (Z_to_bv 64 0)),
          (Z_to_bv 64 1, FdEntry.FdChannel (Z_to_bv 64 1)),
          (Z_to_bv 64 2, FdEntry.FdChannel (Z_to_bv 64 2))] :
           List (word × FdEntry)).map Prod.fst).Nodup
  decide

/-- …AND A DOUBLED DESCRIPTOR IS REFUSED.  This is the state the two
`VFS_BUG_ON`s above exist to make unreachable, so a model that could
build it would be modelling a kernel that cannot be.
kernel: fs/file.c:fd_install@v6.18.46 -/
theorem a_doubled_descriptor_is_not_unique :
    ¬ fd_table_unique [(Z_to_bv 64 0, FdEntry.FdChannel (Z_to_bv 64 0)),
                       (Z_to_bv 64 0, FdEntry.FdChannel (Z_to_bv 64 1))] := by
  show ¬ (([(Z_to_bv 64 0, FdEntry.FdChannel (Z_to_bv 64 0)),
            (Z_to_bv 64 0, FdEntry.FdChannel (Z_to_bv 64 1))] :
             List (word × FdEntry)).map Prod.fst).Nodup
  decide

/-- WHY THE KEY AND NOT THE PAIR: two descriptors may name one file, and
Linux hands that out on request.  `ksys_dup3` (fs/file.c:1399) installs
the OLD descriptor's file at the caller's `newfd` through `do_dup2`
(fs/file.c:1265), so a table binding 0 and 3 to the same channel is a
state a program can ask for, and the invariant accepts it.
kernel: fs/file.c:ksys_dup3,do_dup2@v6.18.46 -/
theorem two_descriptors_may_name_one_file :
    fd_table_unique [(Z_to_bv 64 0, FdEntry.FdChannel (Z_to_bv 64 0)),
                     (Z_to_bv 64 3, FdEntry.FdChannel (Z_to_bv 64 0))] := by
  show (([(Z_to_bv 64 0, FdEntry.FdChannel (Z_to_bv 64 0)),
          (Z_to_bv 64 3, FdEntry.FdChannel (Z_to_bv 64 0))] :
           List (word × FdEntry)).map Prod.fst).Nodup
  decide

/-- …AND THE SAME CALL IS WHY "LOWEST FREE" IS NOT IN THIS REGISTRY.
`ksys_dup3` installs at the descriptor the CALLER named, with no test
that it is the lowest free one.  The bounds it puts on WHERE the
descriptor lands are both refusals, never relocations: `newfd >=
rlimit(RLIMIT_NOFILE)` (fs/file.c:1411) and, through `expand_files`
(fs/file.c:288, called at fs/file.c:1415), `newfd >= sysctl_nr_open`
(fs/file.c:310-311, whose
`-EMFILE` `ksys_dup3` turns into `-EBADF` at fs/file.c:1419-1421).  It
does refuse `oldfd == newfd` (fs/file.c:1408-1409), but that refuses the
CALL, not a placement.  So a cross-arm claim that every descriptor an arm
creates is `alloc_fd`'s answer would be false of Linux the day `dup3`'s
arm enters `checked_table` (`dup3_spec` itself is ported,
`Sys/Fs/File.lean`).  THE PIN IS ON THE STATE BEFORE THE CALL, which is
where the allocator's answer lives: on a table binding 0 alone, the
model's `alloc_fd` answers 1 — 0 is taken, so `alloc_fd_aux` steps past
it (`State/Fd.lean`) — while `dup3(0, 3)` binds 3, the table
`two_descriptors_may_name_one_file` accepts above.  Stated as `= 1` and
not `≠ 3`: an `alloc_fd` never answers a bound descriptor, so `≠ 3` on
the post-state would hold of any table binding 3 and pin nothing about
this argument.  Registered as `unported:` in no header, because it is not
a definition left out: it is a claim the registry must not make.
kernel: fs/file.c:ksys_dup3@v6.18.46 -/
theorem a_duplicate_need_not_be_the_lowest_free_descriptor :
    alloc_fd [(Z_to_bv 64 0, FdEntry.FdChannel (Z_to_bv 64 0))] = Z_to_bv 64 1 := by
  decide

/-- WHAT A DOUBLED DESCRIPTOR WOULD COST, stated over the model's own
reader so the invariant is not merely tidy: `fd_lookup` takes the first
match, so the second binding is a file no call can reach.
model: `fd_lookup` on a hand-built table with one descriptor twice -/
theorem fd_lookup_hides_the_second_binding :
    fd_lookup [(Z_to_bv 64 0, FdEntry.FdChannel (Z_to_bv 64 0)),
               (Z_to_bv 64 0, FdEntry.FdChannel (Z_to_bv 64 1))] (Z_to_bv 64 0)
      = some (FdEntry.FdChannel (Z_to_bv 64 0)) := by
  -- `FdEntry` derives no `DecidableEq`, so a closed `fd_lookup` is pinned
  -- by `rfl` here as it is everywhere else in `Checks/Cases`.
  rfl

end FdTableUnique

section PipeCapacity

/-! ## `pipes_within_capacity`: one pipe, one page

The second invariant Rocq does not state.  `pipe2`'s arm binds a fresh
pipe inside its page (`pipes_within_capacity_arm_pipe2`,
`Checks/Arms/Fs/Pipe.lean`), `write`'s pipe arm fills one only behind
the room test (`pipes_within_capacity_arm_write`,
`Checks/Arms/Fs/ReadWrite.lean`), and an arm that touches no pipe
preserves it by framing.  The pins below are what makes it a claim
rather than a placeholder.
`pipe_append_under_the_gate_stays_within_capacity` is the fact `write`'s
arm meets, restated there as `pipe_append_within_capacity` because that
file cannot import this one; `pipe_consume_stays_within_capacity` is the
one `read`'s pipe arm meets. -/

/-- A PIPE FILLED TO THE PAGE IS STILL WITHIN CAPACITY, and a pipe filled
past it is not a pipe Linux can produce.  The mark the model carries is
Linux's `buf->offset + buf->len` for the slot written last,
`pipe_buf(pipe, head - 1)` (fs/pipe.c:479): `anon_pipe_write`
reads exactly that sum into `offset` (fs/pipe.c:480) and merges a top-up
into the slot only while `offset + chars <= PAGE_SIZE` (fs/pipe.c:482-483),
and `anon_pipe_read` moves bytes from `len` into `offset`
(fs/pipe.c:350-351), which leaves the sum where it was.  So the sum rises
only to the page's end and never falls below what the queue still holds.
THE FIXTURE IS THE STATE LINUX REACHES: a `PIPE_BUF`-byte write onto an
empty pipe has `chars = total_len & (PAGE_SIZE-1) = 0` (fs/pipe.c:477),
skips the merge, and the loop at fs/pipe.c:500 copies one whole page into
one fresh slot (`copy_page_from_iter(page, 0, PAGE_SIZE, from)`) — 4096
bytes queued under a mark of 4096, both conjuncts at their bound at once.
An EMPTY queue under that mark, the other fixture one might write, is
one Linux does not have (the drained slot is released, fs/pipe.c:359-362)
and only the model's `pipe_consume` produces; it would exercise the first
conjunct as `0 ≤ 4096` and say nothing at the boundary.
WHAT THE CITED LINES DO NOT SAY: that the mark never falls at all.  A
`PIPE_BUF_FLAG_PACKET` buffer has `buf->len` zeroed at fs/pipe.c:356 and
a drained buffer is released at fs/pipe.c:359-362, and the model's own
`pipe_append` restarts the mark on an empty queue (`State/Pipes.lean`).
A falling mark threatens only the first conjunct, and the reader lemma
below is what bounds it: `pipe_consume` holds the mark fixed while the
queue shrinks.
WHICH CONSTANT IS THE BOUND, since the two are not the same idea: Linux's
merge gate is `PAGE_SIZE`, and `PIPE_BUF` (include/uapi/linux/limits.h:14)
is the atomic-write guarantee, which the model writes for the bound
instead (`State/Fd.lean`).  They coincide here, both being 4096 on
riscv64's base page (arch/riscv/Kconfig selects `HAVE_PAGE_SIZE_4KB` and
no other), and the pin is stated at the model's spelling because that is
what its writer's gate `pipe_write_room` reads.  What is Linux's and what
is the model's single-slot representation is drawn on the predicate's
own docstring in `Checks/Invariants.lean`.
kernel: fs/pipe.c:anon_pipe_write,anon_pipe_read; include/uapi/linux/limits.h:PIPE_BUF@v6.18.46 -/
theorem a_full_page_is_within_capacity :
    pipes_within_capacity
      [(Z_to_bv 64 0, ((List.replicate 4096 (Z_to_bv 8 0), PIPE_BUF) : PipeBuf))] := by
  intro p hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  subst hp
  refine ⟨?_, by decide⟩
  show (((List.replicate 4096 (Z_to_bv 8 0)).length : Nat) : Int) ≤ PIPE_BUF
  simp only [List.length_replicate]
  decide

/-- …AND A MARK PAST THE PAGE IS REFUSED.  `anon_pipe_write`'s merge test
at fs/pipe.c:482-483 is the reason no run reaches it: a top-up that would
carry `buf->offset + buf->len` past `PAGE_SIZE` is not merged at all, it
starts a fresh slot, and the model declines the two-slot case rather than
guessing (`pipe_write_room`, `State/Pipes.lean`).
kernel: fs/pipe.c:anon_pipe_write@v6.18.46 -/
theorem a_mark_past_the_page_is_not_within_capacity :
    ¬ pipes_within_capacity [(Z_to_bv 64 0, (([], PIPE_BUF + 1) : PipeBuf))] := by
  intro h
  exact absurd (h _ List.mem_cons_self).2 (by decide)

/-- …AND SO IS A QUEUE LONGER THAN ITS MARK, the FIRST conjunct's
refutation, without which the predicate could lose that conjunct with
every other pin here still closing.  In Linux the mark is
`buf->offset + buf->len` (fs/pipe.c:480) and the queue is the `buf->len`
bytes behind it: `anon_pipe_read` takes `chars = buf->len` from a slot
(fs/pipe.c:323), clamped DOWN to what the reader asked for
(fs/pipe.c:327-334) and never up, so the bytes a reader can be handed
and the summand are one field and a queue longer than the mark is a
state the kernel's bookkeeping does not have.  Not because two unsigned
summands cannot be exceeded -- a `len` past the page is exactly what the
merge gate at fs/pipe.c:482-483 exists to refuse creating -- but because
there is no second count for the bytes to outrun.  A one-byte queue
under a mark of 0 is the smallest such state.
kernel: fs/pipe.c:anon_pipe_write,anon_pipe_read@v6.18.46 -/
theorem a_queue_past_its_mark_is_not_within_capacity :
    ¬ pipes_within_capacity [(Z_to_bv 64 0, (([Z_to_bv 8 0], 0) : PipeBuf))] := by
  intro h
  exact absurd (h _ List.mem_cons_self).1 (by decide)

/-- THE MODEL'S ONLY WRITER KEEPS IT.  `pipe_append` behind the gate
`pipe_write_room` cannot leave the page: on an empty queue the gate is
the whole bound, and on a nonempty one the new mark is the old one plus
what was written, which the gate has already bounded.  This is the
obligation `write`'s `FdPipe` branch owes, and its arm file proves a copy
of it (`pipe_append_within_capacity`).
model: `pipe_append` under `pipe_write_room`, over the model's own
definitions -/
theorem pipe_append_under_the_gate_stays_within_capacity (st : PipeBuf) (bs : List byte)
    (hcap : pipe_within_capacity st) (hroom : pipe_write_room st (bs.length : Int) = true) :
    pipe_within_capacity (pipe_append st bs) := by
  obtain ⟨q, used⟩ := st
  cases q with
  | nil =>
    simp only [pipe_write_room, decide_eq_true_eq] at hroom
    exact ⟨Int.le_refl _, hroom⟩
  | cons a r =>
    simp only [pipe_write_room, decide_eq_true_eq] at hroom
    -- `pipe_within_capacity` is a `def`, so `omega` reads `hcap.1`'s
    -- subject as an atom of its own unless the ascription names the same
    -- length it will meet in the goal.
    have h1 : ((a :: r).length : Int) ≤ used := hcap.1
    refine ⟨?_, hroom⟩
    simp only [pipe_append, List.length_append]
    omega

/-- …AND THE READER KEEPS IT TOO: `pipe_consume` drops bytes off the
front and leaves the mark alone, which is what Linux does at
fs/pipe.c:350-351 (Linux v6.18.46), so both conjuncts survive.
model: `pipe_consume` over the model's own definitions -/
theorem pipe_consume_stays_within_capacity (st : PipeBuf) (k : Nat)
    (hcap : pipe_within_capacity st) : pipe_within_capacity (pipe_consume st k) := by
  obtain ⟨q, used⟩ := st
  have h1 : (q.length : Int) ≤ used := hcap.1
  refine ⟨?_, hcap.2⟩
  show ((q.drop k).length : Int) ≤ used
  have hle : (q.drop k).length ≤ q.length := by
    simp only [List.length_drop]
    omega
  omega

end PipeCapacity

section Registration

/-! ## The registry itself

Three pins on the register as data: that it holds the three entries, in
order, and that each entry reads the subsystem its name says. -/

/-- The registry holds three entries and no more.  A fourth added
without its arm facts fails the build; a fourth added WITH them is a
change this pin makes visible.
model: `invariant_registry` as data -/
theorem the_registry_has_three_entries : invariant_registry.length = 3 := rfl

/-- The entries are the three the file documents, in order.
model: `invariant_registry`'s `inv_name` fields -/
theorem the_registry_names :
    invariant_registry.map Invariant.inv_name
      = ["vm_wf", "fd_table_unique", "pipes_within_capacity"] := rfl

/-- The descriptor entry reads the descriptor table and not the pipes: a
`inv_view` copied from the wrong neighbour would still build, since both
carriers are lists of pairs over `word`.
model: `inv_fd_table_unique`'s view at an arbitrary model -/
theorem inv_fd_table_unique_reads_the_table (m : Model) :
    inv_fd_table_unique.holds m = fd_table_unique (m_fds m) := rfl

/-- …and the pipe entry reads the pipes.
model: `inv_pipes_within_capacity`'s view at an arbitrary model -/
theorem inv_pipes_within_capacity_reads_the_pipes (m : Model) :
    inv_pipes_within_capacity.holds m = pipes_within_capacity (m_pipes m) := rfl

end Registration

section ArmFacts

/-! ## The arm facts, by type

Every fact's elaborated type is pinned in the generated
`Checks.Cases.CheckedTable`, one `#guard_msgs` per (invariant, arm) pair
that `tools/gen_lean_checked.py` renders from the arm files beside the
alternation it names them in, so a registration adds no pin here.  What
stays is the pair the generator's header rule exists for, shown closing
the wrong way, so that the blind spot is a fact in the tree and not a
story about one. -/

/-- THE BLIND SPOT IS REAL, AND THIS IS ITS SHAPE: the `arm_exit` fact
closes the `arm_exit_group` goal, because `arm_exit_group.ca_check` is
`arm_exit.ca_check` by definition (`Checks/Arms/Kernel/Exit.lean`) and
`arm_preserves` reads nothing else of the arm.  So every
`<invariant>_arm_exit_group` line of `registry_preserves` could be
deleted and the BUILD would close by the line above it; that is why
`tools/gen_lean_checked.py` renders every line from the arm files and
refuses, by ARM-4, an arm file missing a fact.  The day one of
these three stops elaborating, the two checkers have parted and the
text rule has become the build's own.
model: `arm_preserves inv_vm_wf arm_exit_group` closed by `vm_wf_arm_exit` -/
example : arm_preserves inv_vm_wf arm_exit_group := vm_wf_arm_exit

/-- …the same at the descriptor table.
model: `arm_preserves inv_fd_table_unique arm_exit_group` closed by `fd_table_unique_arm_exit` -/
example : arm_preserves inv_fd_table_unique arm_exit_group := fd_table_unique_arm_exit

/-- …and at the pipes.
model: `arm_preserves inv_pipes_within_capacity arm_exit_group` closed by `pipes_within_capacity_arm_exit` -/
example : arm_preserves inv_pipes_within_capacity arm_exit_group :=
  pipes_within_capacity_arm_exit

end ArmFacts

section Alternation

/-! ## The alternation, the fallback, and the pair it names

The guard is not exercised by the real registry and the real table, both
of which are covered: what a covered product shows is that the
alternation closes, not that an uncovered pair is caught.  So the shape
is run again over a FIXTURE registry of two entries and the two-arm
`fixture_table` of `Checks/Cases/Checks/Sys/Dispatch.lean` — four pairs —
once whole, once with one pair's alternative dropped and once with it
written behind the closing `| skip`.  The last two are `example`s under
`#guard_msgs`, which is the T20-shape drop the ticket asks for done at
elaboration time rather than by a harness rebuilding the tree: the
example fails, `#guard_msgs` captures the message exactly, and the pin
stops closing if the wording drifts or if an uncovered pair stops
failing. -/

/-- Two entries, so that a dropped alternative for one is not closed by
the other's: `arm_preserves` is applied to the entry, so the two pairs
over one arm have different types.
AND TWO ARMS THAT ARE NOT EACH OTHER, which is the axis that actually
bites: an alternative can only be stolen by a pair whose GOAL is
definitionally the same, and `fixture_arm_unmodeled`'s checker is
constantly `CheckUnmodeled` (`Checks/Cases/Checks/Sys/Dispatch.lean`)
where `fixture_check_exit` accepts, so no fact about one arm has the
other's type.  `checked_table` is not safe this way and the file header
of `Checks/Invariants.lean` says where it is not. -/
def fixture_registry : List Invariant :=
  inv_fd_table_unique ::
  inv_pipes_within_capacity ::
  []

/-- The fixture exit arm hands the descriptor subsystem back untouched;
`vm_frame` reads the hypothesis down to the accepted model and closes the
goal, exactly as it does for `fixture_check_exit_frame` over the ledger.
model: `vm_frame` on the fixture exit arm's checker -/
theorem fixture_check_exit_fd_state_frame (code : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : fixture_check_exit code eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  unfold fixture_check_exit at h
  vm_frame h

/-- `fd_table_unique` × the fixture exit arm.
model: `arm_preserves_of_view_frame` over `fixture_check_exit_fd_state_frame` -/
theorem fixture_fd_table_unique_arm_exit : arm_preserves inv_fd_table_unique fixture_arm_exit :=
  arm_preserves_of_view_frame inv_fd_table_unique fixture_arm_exit (fun _i eff m m' evs h =>
    congrArg FdState.fdst_table (fixture_check_exit_fd_state_frame _ eff m m' evs h))

/-- `pipes_within_capacity` × the fixture exit arm.
model: `arm_preserves_of_view_frame` over `fixture_check_exit_fd_state_frame` -/
theorem fixture_pipes_within_capacity_arm_exit :
    arm_preserves inv_pipes_within_capacity fixture_arm_exit :=
  arm_preserves_of_view_frame inv_pipes_within_capacity fixture_arm_exit (fun _i eff m m' evs h =>
    congrArg FdState.fdst_pipes (fixture_check_exit_fd_state_frame _ eff m m' evs h))

/-- `fd_table_unique` × the fail-closed arm: vacuously, its checker never
accepts.
model: `fixture_arm_unmodeled_declines` at `inv_fd_table_unique` -/
theorem fixture_fd_table_unique_arm_unmodeled :
    arm_preserves inv_fd_table_unique fixture_arm_unmodeled := by
  intro i eff m m' evs h _
  rw [fixture_arm_unmodeled_declines] at h
  exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

/-- `pipes_within_capacity` × the fail-closed arm: likewise.
model: `fixture_arm_unmodeled_declines` at `inv_pipes_within_capacity` -/
theorem fixture_pipes_within_capacity_arm_unmodeled :
    arm_preserves inv_pipes_within_capacity fixture_arm_unmodeled := by
  intro i eff m m' evs h _
  rw [fixture_arm_unmodeled_declines] at h
  exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

/-- EVERY PAIR COVERED: the split, the alternation and the fallback step
over the fixture product, closing.
model: `inv_arms_split` and the `first` alternation over the fixtures -/
theorem fixture_registry_preserves :
    ∀ inv ∈ fixture_registry, ∀ c ∈ fixture_table, arm_preserves inv c := by
  inv_arms_split fixture_registry, fixture_table
  all_goals first
    | exact fixture_fd_table_unique_arm_exit
    | exact fixture_fd_table_unique_arm_unmodeled
    | exact fixture_pipes_within_capacity_arm_exit
    | exact fixture_pipes_within_capacity_arm_unmodeled
    | skip
  all_goals inv_arm_uncovered

/-- The dispatcher-level reading over the fixtures, composed the way
`Checks/Invariants.lean` composes it.
model: `lookup_ca_In` and `fixture_registry_preserves` composed -/
theorem fixture_lookup_preserves (inv : Invariant) (hinv : inv ∈ fixture_registry)
    (i : SyscallInput) (eff : SyscallEffect) (m m' : Model) (evs : List event) (c : CheckedArm)
    (hlk : lookup_ca fixture_table (bv_unsigned i.in_sysno) = some c)
    (h : c.ca_check i eff m = CheckOk m' evs) (hold : inv.holds m) : inv.holds m' :=
  fixture_registry_preserves inv hinv c (lookup_ca_In fixture_table _ c hlk) i eff m m' evs h hold

/--
error: registry_preserves has no case for this (invariant, arm) pair.
State `<invariant>_<arm> : arm_preserves <invariant> <arm>` in the arm's file under
Checks/Arms/ -- from the checker's frame lemma through
arm_preserves_of_view_frame, or from a preserves lemma directly, with
`simp only [arm_unfold] at h` recovering the plain checker -- and let
tools/gen_lean_checked.py render its `| exact <invariant>_<arm>` ABOVE the closing `| skip`;
an alternative listed behind that line never runs.  The uncovered goal, which names
the invariant and the arm:
⊢ arm_preserves inv_pipes_within_capacity fixture_arm_unmodeled
-/
#guard_msgs in
/-- THE FALLBACK FIRES, AND NAMES BOTH.  One pair's alternative is
dropped and the message names the invariant and the arm, not the position
in the product.  This is the ticket's acceptance line — dropping one
arm's lemma for any registered invariant fails the build naming both —
pinned on the fixture product, since dropping one in the real
`registry_preserves` would fail this file's own build and could not be
pinned at all.
model: `inv_arm_uncovered` over the fixtures with one alternative dropped -/
example : ∀ inv ∈ fixture_registry, ∀ c ∈ fixture_table, arm_preserves inv c := by
  inv_arms_split fixture_registry, fixture_table
  all_goals first
    | exact fixture_fd_table_unique_arm_exit
    | exact fixture_fd_table_unique_arm_unmodeled
    | exact fixture_pipes_within_capacity_arm_exit
    | skip
  all_goals inv_arm_uncovered

/--
error: registry_preserves has no case for this (invariant, arm) pair.
State `<invariant>_<arm> : arm_preserves <invariant> <arm>` in the arm's file under
Checks/Arms/ -- from the checker's frame lemma through
arm_preserves_of_view_frame, or from a preserves lemma directly, with
`simp only [arm_unfold] at h` recovering the plain checker -- and let
tools/gen_lean_checked.py render its `| exact <invariant>_<arm>` ABOVE the closing `| skip`;
an alternative listed behind that line never runs.  The uncovered goal, which names
the invariant and the arm:
⊢ arm_preserves inv_fd_table_unique fixture_arm_exit
-/
#guard_msgs in
/-- AN ALTERNATIVE BEHIND THE `| skip` NEVER RUNS.  A DIFFERENT pair's
alternative from the one the example above dropped -- the first pair of
the product, not the last -- is present here, written one line too late,
and the build fails exactly as if it were absent, naming THIS pair: so
the message tracks the pair that is open and is not a constant the two
examples happen to share.  This is why the alternation's last
alternative is `skip` and the fallback is the step after it.
model: `inv_arm_uncovered` over the fixtures with one alternative
misordered -/
example : ∀ inv ∈ fixture_registry, ∀ c ∈ fixture_table, arm_preserves inv c := by
  inv_arms_split fixture_registry, fixture_table
  all_goals first
    | exact fixture_fd_table_unique_arm_unmodeled
    | exact fixture_pipes_within_capacity_arm_exit
    | exact fixture_pipes_within_capacity_arm_unmodeled
    | skip
    | exact fixture_fd_table_unique_arm_exit
  all_goals inv_arm_uncovered

/-- A SPEC THAT BREAKS BOTH DESCRIPTOR-SIDE INVARIANTS ON EVERY CALL,
with the bare return 0: it installs a table binding descriptor 0 twice
and a pipe whose mark is past the page.  Internally consistent -- its
checker and witness meet all five `CheckedArm` obligations, the way
`fixture_arm_breaks_ledger` does while doubling the memory ledger
(`Checks/Cases/Checks/VmMapsDisjoint.lean`) -- and wrong about Linux
twice over.  The record cannot tell it from a good arm; the registry
can, and the two refutations below are where. -/
def breaks_fd_state (m : Model) : Model :=
  with_pipes [(Z_to_bv 64 0, (([], PIPE_BUF + 1) : PipeBuf))]
    (with_fds [(Z_to_bv 64 0, FdEntry.FdChannel (Z_to_bv 64 0)),
               (Z_to_bv 64 0, FdEntry.FdChannel (Z_to_bv 64 1))] m)

/-- The spec behind the arm below. -/
def breaks_fd_state_spec : Sys SyscallEffect :=
  fun _ m o => o = Ok (mkEffect 0 [] []) (breaks_fd_state m) []

/-- The arm over it, every field discharged as `fixture_arm_breaks_ledger`'s
are. -/
def fixture_arm_breaks_fd_state : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 0 breaks_fd_state_spec
  ca_check := fun _ eff m => check_ret_only eff 0 (breaks_fd_state m) []
  ca_witness := fun _ m => Ok (mkEffect 0 [] []) (breaks_fd_state m) []
  ca_sound_ok := by
    intro i eff m m' evs h
    obtain ⟨heff, hm', hevs⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    subst heff
    subst hm'
    subst hevs
    exact rfl
  ca_sound_unmodeled := by
    intro i eff m h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  ca_complete_ok := by
    intro i eff m m' evs h
    have h' : (Ok eff m' evs : outcome SyscallEffect)
        = Ok (mkEffect 0 [] []) (breaks_fd_state m) [] := h
    injection h' with heff hm' hevs
    subst heff
    subst hm'
    subst hevs
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  ca_complete_unmodeled := by
    intro i m eff h
    have h' : (Unmodeled : outcome SyscallEffect)
        = Ok (mkEffect 0 [] []) (breaks_fd_state m) [] := h
    cases h'
  ca_receptive := by
    intro i m
    exact rfl

/-- The one accepted step the two refutations read: from the start state
the arm accepts a bare return 0 into `breaks_fd_state wit_s0`.
model: `check_ret_only_ok_iff` at the breaking arm's checker -/
theorem fixture_arm_breaks_fd_state_accepts :
    fixture_arm_breaks_fd_state.ca_check (brk_in 0) (mkEffect 0 [] []) wit_s0
      = CheckOk (breaks_fd_state wit_s0) [] :=
  (check_ret_only_ok_iff (mkEffect 0 [] []) 0 (breaks_fd_state wit_s0) []
    (breaks_fd_state wit_s0) []).mpr ⟨rfl, rfl, rfl⟩

/-- …AND `fd_table_unique` REFUSES THE ARM: `arm_preserves` demands the
post-state keep the invariant the start state has (`inv_at_init`), and
the post-state is the doubled table `a_doubled_descriptor_is_not_unique`
refutes.  This is the negative the registration exists for -- an arm the
five fields accept and the registry does not -- stated at the checker
level, where an arm that WROTE `m_fd` wrongly would be caught; the real
arms today only carry `m_fd` across, so their facts are frame lemmas and
this is the pin that shows the obligation has teeth.
model: `arm_preserves inv_fd_table_unique` on `fixture_arm_breaks_fd_state` at `wit_s0` -/
theorem fixture_arm_breaks_fd_state_breaks_fd_table_unique :
    ¬ arm_preserves inv_fd_table_unique fixture_arm_breaks_fd_state := by
  intro h
  have hend : inv_fd_table_unique.holds (breaks_fd_state wit_s0) :=
    h _ _ _ _ _ fixture_arm_breaks_fd_state_accepts
      (inv_fd_table_unique.inv_at_init _ _ _ _ _ _)
  exact a_doubled_descriptor_is_not_unique hend

/-- …AND SO DOES `pipes_within_capacity`, from the same accepted step: the
post-state's one pipe has the mark `a_mark_past_the_page_is_not_within_capacity`
refutes.
model: `arm_preserves inv_pipes_within_capacity` on `fixture_arm_breaks_fd_state` at `wit_s0` -/
theorem fixture_arm_breaks_fd_state_breaks_pipes_within_capacity :
    ¬ arm_preserves inv_pipes_within_capacity fixture_arm_breaks_fd_state := by
  intro h
  have hend : inv_pipes_within_capacity.holds (breaks_fd_state wit_s0) :=
    h _ _ _ _ _ fixture_arm_breaks_fd_state_accepts
      (inv_pipes_within_capacity.inv_at_init _ _ _ _ _ _)
  exact a_mark_past_the_page_is_not_within_capacity hend

end Alternation

section NonVacuity

/-! ## The two proof fields, and what each refuses

`Invariant` cannot be built without `inv_at_init` and `inv_refused`.  The
pins below are the reason each is there: the predicate a registration
would most like to get away with, and the field that stops it. -/

/-- The predicate a registration would most like to get away with, under
a name: `tools/check_lean_pins.py` PIN-4 refuses the constant spelled out
in any statement, since a conjoined or disjoined one is closed by
`trivial` and pins nothing, and here the constant is the SUBJECT of the
pin rather than a clause of it.  The name keeps that distinction where
the lint can see it. -/
def always_true (_ : Model) : Prop := True

/-- `always_true` CANNOT BE REGISTERED: with a model in hand, no value of
the carrier is refused, so `inv_refused` has no proof.  Every arm
preserves that predicate and it says nothing about Linux; this is the
vacuous guard the registry's structure refuses by construction rather
than by review.
model: the `inv_refused` obligation at the always-true predicate -/
theorem the_always_true_predicate_has_no_refusal :
    ¬ ∃ x : Model, ¬ always_true x :=
  fun ⟨_, hne⟩ => hne True.intro

/-- `fun _ => False` CANNOT BE REGISTERED EITHER: it is preserved by every
arm, vacuously, since no accepted step starts from a model satisfying it
— and `inv_at_init` has no proof, because `execve` does build a model.
Stated at the registry's own start state so the refutation is about a
model that exists.
model: the `inv_at_init` obligation at the always-false predicate -/
theorem the_always_false_predicate_fails_at_init (reserved : List (word × word))
    (brk0 mbase sp : word) (lim : Int) (inp : ProcInput) :
    ¬ (fun _ : Model => False) (init_model reserved brk0 mbase sp lim inp) :=
  fun h => h

/-- The refusal each registered entry carries is a real one, read back
off the register: `inv_refused` is inhabited for every entry, so no
entry is the always-true predicate.
model: the `inv_refused` fields of `invariant_registry` -/
theorem every_registered_invariant_refuses_something :
    ∀ inv ∈ invariant_registry, ∃ x : inv.inv_carrier, ¬ inv.inv_pred x :=
  fun inv _ => inv.inv_refused

/-- …and `inv_at_init` likewise, so no entry is the always-false one.
model: the `inv_at_init` fields of `invariant_registry` -/
theorem every_registered_invariant_holds_at_init :
    ∀ inv ∈ invariant_registry, ∀ (reserved : List (word × word)) (brk0 mbase sp : word)
      (lim : Int) (inp : ProcInput), inv.holds (init_model reserved brk0 mbase sp lim inp) :=
  fun inv _ reserved brk0 mbase sp lim inp => inv.inv_at_init reserved brk0 mbase sp lim inp

end NonVacuity

section DispatcherCorollaries

/-! ## The two corollaries over the dispatcher, applied and refuted

`Checks/Invariants.lean`'s `syscall_spec_preserves` and
`base_unique_after_syscall` are twins of Rocq corollaries and stand
beside the definitions for that reason.  Pinned here is what their
statements do NOT say.  Each is APPLIED once, at a step the tree's real
`checked_table` accepts, so that every premise is seen discharged at a
real syscall and not left to a caller: the spec-level one at the plain
rw grant, whose post-model differs from its pre-model, and the
base-uniqueness one at the contained `MAP_FIXED` commit.  The
spec-level one is generic over the registry, so it is applied at every
entry the registry holds today, not at `vm_wf` alone; an entry added
later owes its own application here.  And each has the premises the
port added or the twin already carried shown load-bearing, in the
different senses the premises allow: `lookups_agree_at` is FALSE at a
number only `spec_table` carries, so the proof cannot proceed there
(the premise-free statement is not refuted -- `fsync` touches no ledger
-- it is not proved in this tree, and would need every `spec_table` arm
to preserve every registered invariant, which nothing states); dropping
the alignment premise from `base_unique_after_syscall`, or its
well-formedness premise, leaves a statement a ledger of the tree's own
REFUTES.

The models are `Checks/Cases/Prelude.lean`'s `fixture` over a one-page
ledger -- `one_map_model` is that file's, `one_page_left_model` is
`Checks/Cases/Mm/Mmap.lean`'s; `mmap_in`, the `dispatch_norm` reader and
the accepted steps over the real table are
`Checks/Cases/Checks/Sys/Mm/Mmap.lean`'s, opened for this section alone:
its macros are `scoped`, for the reason its header gives.  The non-wf
ledger the last refutation uses is
`Checks/Cases/Checks/VmMapsDisjoint.lean`'s `doubled_vm`. -/

open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Mm.Mmap
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Mm.Mmap

/-- THE SPEC-LEVEL COROLLARY REACHES A REAL SYSCALL, and this is the
step that carries it there.  `syscall_spec_preserves` takes a premise
Rocq's corollary does not -- `lookups_agree_at` at the call's number --
and at 222 (`mmap`), a number `checked_table` carries, that premise
comes off the table itself: `lookup_ca checked_table 222` finds
`arm_mmap`, and `lookups_agree_at_of_found` turns that into the premise.
model: `lookups_agree_at_of_found` at `arm_mmap` over `checked_table` -/
theorem the_premise_holds_at_the_mmap_number :
    Checks.ExecutableSpecs.lookups_agree_at 222 :=
  Checks.ExecutableSpecs.lookups_agree_at_of_found 222 arm_mmap lookup_ca_checked_table_mmap

/-- …and at 214 and 215, the two numbers V-pilot-Mm-Mmap registered: the
same step off the same table, so the corollary reaches `brk` and `munmap`
the day they are registered and not by any edit to it.
model: `lookups_agree_at_of_found` at `arm_brk` and `arm_munmap` over `checked_table` -/
theorem the_premise_holds_at_the_brk_and_munmap_numbers :
    Checks.ExecutableSpecs.lookups_agree_at 214 ∧ Checks.ExecutableSpecs.lookups_agree_at 215 :=
  ⟨Checks.ExecutableSpecs.lookups_agree_at_of_found 214 arm_brk lookup_ca_checked_table_brk,
   Checks.ExecutableSpecs.lookups_agree_at_of_found 215 arm_munmap lookup_ca_checked_table_munmap⟩

/-- …and at 19, the number V-pilot-Fs-EventFd registered: the same step
off the same table, so the corollary reaches `eventfd2` the day it is
registered and not by any edit to it.
model: `lookups_agree_at_of_found` at `arm_eventfd2` over `checked_table` -/
theorem the_premise_holds_at_the_eventfd2_number :
    Checks.ExecutableSpecs.lookups_agree_at 19 :=
  Checks.ExecutableSpecs.lookups_agree_at_of_found 19 arm_eventfd2 lookup_ca_checked_table_eventfd2

/-- The one-page ledger the two mmap fixtures share is well formed: one
page granted over the empty ledger, which `maps_wf_cons_free` covers
exactly as it covers `wit_s5`'s identical ledger in
`Checks/Cases/Checks/VmMapsDisjoint.lean`'s `step5_grant_is_wf`.
`one_map_model` and `one_page_left_model` differ only in the budget,
which `vm_wf` does not read, so this is stated over the ledger and
instantiated twice below.
model: `maps_wf_cons_free` on the one-entry ledger -/
theorem the_one_page_ledger_is_vm_wf (lim : Int) (sp : word) :
    vm_wf (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 lim 0 sp) :=
  maps_wf_cons_free [] 65536 4096
    ⟨fun _ h => (List.not_mem_nil h).elim, fun _ _ => Nat.zero_le 1⟩ (by decide) (by decide)

/-- The fixture's descriptor table is the three standard channels, and
the invariant reads their keys: `fixture` leaves `fixture_of`'s `fds`
slot at `init_fds`, so this is `init_fds`'s uniqueness at every ledger.
model: `fd_table_unique` at `init_fds`, the fixture's table -/
theorem the_fixture_fd_table_is_unique (h : VmMaps) :
    inv_fd_table_unique.holds (fixture h) := by
  show ((init_fds : List (word × FdEntry)).map Prod.fst).Nodup
  decide

/-- …and the fixture holds no pipe, so the pipe invariant holds of it
vacuously: `fixture_of`'s `pipes` slot is `[]`.
model: `pipes_within_capacity` at the empty pipe table -/
theorem the_fixture_pipes_are_within_capacity (h : VmMaps) :
    inv_pipes_within_capacity.holds (fixture h) :=
  fun _ hp => (List.not_mem_nil hp).elim

/-- THE PLAIN RW GRANT IS A RELATIONAL STEP OF THE SPEC: the checker
accepts it over the real table (`dispatch_norm` reads the dispatcher
down to the `check_mmap` step `rw_grant_is_accepted` pins), and soundness
carries the accepted step to `Specs.syscall_spec`.  Stated because the corollary below consumes a
relational step, not a checked one, and because this is the one step in
this file whose post-model is not its pre-model: the page is granted.
probe: testing/syscall-check/tests/mmap_shapes.c#conform -- ok -/
theorem the_rw_grant_is_a_relational_step :
    Specs.syscall_spec (mmap_in 0 4096 3 34 Sys.Mm.Mmap.mmap_fd_none 0) one_page_left_model
      (Ok (mkEffect 0x40000000 [] [(0x40000000, 4096)])
        (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)] [] 0 0 8192 0
          demo_sp)) []) :=
  Checks.ExecutableSpecs.check_syscall_sound_ok _ _ _ _ _ (by dispatch_norm)

/-- …AND THE SPEC-LEVEL COROLLARY CARRIES THE LEDGER INVARIANT ACROSS
IT with nothing left for the caller: the agreement premise is
`the_premise_holds_at_the_mmap_number`, the step is
`the_rw_grant_is_a_relational_step`, and the invariant at the pre-model
is the one-page ledger's.  The conclusion is a closed fact `decide`
could settle; the pin is the PROOF TERM, which is the application of
`syscall_spec_preserves` at `inv_vm_wf`, and it is what shows the
corollary usable at a real, ledger-changing step rather than only
stated.
model: `syscall_spec_preserves` at `inv_vm_wf` over the rw grant -/
theorem the_spec_level_corollary_applies_at_the_rw_grant :
    vm_wf (m_vmmaps (fixture (VmMaps.mkVmMapsFull [] [(0x40000000, 4096), (65536, 4096)] []
      0 0 8192 0 demo_sp))) :=
  syscall_spec_preserves inv_vm_wf inv_vm_wf_registered
    (mmap_in 0 4096 3 34 Sys.Mm.Mmap.mmap_fd_none 0) one_page_left_model _ _ _
    the_premise_holds_at_the_mmap_number the_rw_grant_is_a_relational_step
    (the_one_page_ledger_is_vm_wf 8192 demo_sp)

/-- …AND IT IS GENERIC IN FACT, NOT ONLY IN ITS BINDER: the same step
carries the other two registered invariants, with membership proved
inline: a `_registered` helper belongs beside the definitions only when
a lemma there consumes it, as `base_unique_after_syscall` consumes
`inv_vm_wf_registered`.  The grant touches no descriptor, so the
post-model's table is still `init_fds`; the conclusion is decidable, the
pin is the application.
model: `syscall_spec_preserves` at `inv_fd_table_unique` over the rw grant -/
theorem the_spec_level_corollary_applies_at_the_rw_grant_for_fd_table_unique :
    inv_fd_table_unique.holds (fixture (VmMaps.mkVmMapsFull []
      [(0x40000000, 4096), (65536, 4096)] [] 0 0 8192 0 demo_sp)) :=
  syscall_spec_preserves inv_fd_table_unique
    (by unfold invariant_registry; exact List.mem_cons_of_mem _ List.mem_cons_self)
    (mmap_in 0 4096 3 34 Sys.Mm.Mmap.mmap_fd_none 0) one_page_left_model _ _ _
    the_premise_holds_at_the_mmap_number the_rw_grant_is_a_relational_step
    (the_fixture_fd_table_is_unique _)

/-- …and the pipe invariant, the registry's third entry.
model: `syscall_spec_preserves` at `inv_pipes_within_capacity` over the rw grant -/
theorem the_spec_level_corollary_applies_at_the_rw_grant_for_pipes :
    inv_pipes_within_capacity.holds (fixture (VmMaps.mkVmMapsFull []
      [(0x40000000, 4096), (65536, 4096)] [] 0 0 8192 0 demo_sp)) :=
  syscall_spec_preserves inv_pipes_within_capacity
    (by unfold invariant_registry
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    (mmap_in 0 4096 3 34 Sys.Mm.Mmap.mmap_fd_none 0) one_page_left_model _ _ _
    the_premise_holds_at_the_mmap_number the_rw_grant_is_a_relational_step
    (the_fixture_pipes_are_within_capacity _)

/-- BASE UNIQUENESS APPLIES AT THE CONTAINED COMMIT: the `MAP_FIXED` rw
commit over `one_map_model`
(`check_syscall_accepts_fixed_rw_contained_over_the_real_table`) hands
back the same one-page ledger, and `base_unique_after_syscall` names its
one entry at the page-aligned base 65536 from the accepted step, the
pre-model's `vm_wf`, the alignment and `map_has` alone.  As above, the
conclusion is decidable and the pin is the application: every premise of
the twin is seen discharged at a step the real table accepts.
model: `base_unique_after_syscall` over the contained `MAP_FIXED` commit -/
theorem base_uniqueness_applies_at_the_contained_commit :
    ((m_vmmaps one_map_model).vm_maps).filter (fun q => bv_eqb q.1 65536) = [(65536, 4096)] :=
  base_unique_after_syscall _ _ _ _ _ 65536 4096
    check_syscall_accepts_fixed_rw_contained_over_the_real_table
    (the_one_page_ledger_is_vm_wf demo_limit demo_sp) (by decide) (by decide)

/-- …AND ITS ALIGNMENT PREMISE IS LOAD-BEARING: the theorem with that
one premise dropped is FALSE, and the tree's own witness refutes it.
`wit_s8` is the last state of Rocq's PART 1 chain -- eight modeled steps
of `brk`, `munmap` and `mmap`, whose step examples are ticket K9's and
not pinned here; the refutation does not rest on that history, only on
the ledger: it is well formed (`duplicate_base_ledger_is_vm_wf`), and
`-ENOMEM` at the plain rw grant is a step the real table accepts at
every model with the model unchanged
(`check_syscall_accepts_mmap_enomem_over_the_real_table`), so `wit_s8`
is a post-model of an accepted step.  `map_has` answers true there at
`(67536, 100)` (`wit_duplicate_base`), and the filter at 67536 keeps two
entries (`unaligned_base_names_two_entries`), not one.  67536 is not
page aligned (`wit_duplicate_base_is_unaligned`): the alignment premise
is exactly what keeps this state out of the twin's reach.  This is the
dispatcher-level lift of `base_entry_unique_needs_alignment`, the same
refutation stated over the bare ledger lemma.
model: `base_unique_after_syscall` minus alignment, refuted on `wit_s8` -/
theorem dropping_the_alignment_premise_refutes_base_uniqueness :
    ¬ ∀ (i : SyscallInput) (eff : SyscallEffect) (m m' : Model) (evs : List event) (a n : word),
        Checks.ExecutableSpecs.check_syscall i eff m = CheckOk m' evs →
        vm_wf (m_vmmaps m) →
        map_has (m_vmmaps m').vm_maps a n = true →
        ((m_vmmaps m').vm_maps).filter (fun q => bv_eqb q.1 a) = [(a, n)] := by
  intro hall
  have h := hall _ _ wit_s8 wit_s8 [] 67536 100
    (check_syscall_accepts_mmap_enomem_over_the_real_table wit_s8)
    Checks.Cases.Checks.VmMapsDisjoint.duplicate_base_ledger_is_vm_wf
    wit_duplicate_base.1
  rw [Checks.Cases.Checks.VmMapsDisjoint.unaligned_base_names_two_entries] at h
  exact absurd h (by decide)

/-- …AND SO IS ITS WELL-FORMEDNESS PREMISE: with `vm_wf (m_vmmaps m)`
dropped and alignment kept, the statement is FALSE, and the ledger
`Checks/Cases/Checks/VmMapsDisjoint.lean` builds to refute `vm_wf` itself
refutes it.  `doubled_vm` records the page-aligned base 65536 twice, so
`with_vmmaps doubled_vm wit_s0` is not `vm_wf` (`doubled_start_is_not_vm_wf`);
`-ENOMEM` at the plain rw grant is accepted there with the model
unchanged, so it is a post-model of an accepted step; `map_has` answers
true at `(65536, 4096)` and the filter at 65536 keeps both entries.  The
twin's docstring says `vm_wf` is a HYPOTHESIS there, not a fact about
reachable states; this is the pin that the hypothesis is doing work.
model: `base_unique_after_syscall` minus well-formedness, refuted on `doubled_vm` -/
theorem dropping_the_wellformedness_premise_refutes_base_uniqueness :
    ¬ ∀ (i : SyscallInput) (eff : SyscallEffect) (m m' : Model) (evs : List event) (a n : word),
        Checks.ExecutableSpecs.check_syscall i eff m = CheckOk m' evs →
        bv_unsigned a % page_size = 0 →
        map_has (m_vmmaps m').vm_maps a n = true →
        ((m_vmmaps m').vm_maps).filter (fun q => bv_eqb q.1 a) = [(a, n)] := by
  intro hall
  have h := hall _ _ (with_vmmaps Checks.Cases.Checks.VmMapsDisjoint.doubled_vm wit_s0)
    (with_vmmaps Checks.Cases.Checks.VmMapsDisjoint.doubled_vm wit_s0) [] 65536 4096
    (check_syscall_accepts_mmap_enomem_over_the_real_table _) (by decide) (by decide)
  exact absurd h (by decide)

end DispatcherCorollaries

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Invariants
