import LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/-! # LinuxProcessSem.Checks.InvariantRegistry — the cross-arm invariant registry

THIS FILE MIRRORS NOTHING.  `theories/LinuxProcessSem/` has no
`Checks/Invariants` module -- written without its extension because a
`.v` token is a citation to `tools/check_citations.py`, and this path is
one this tree means never to resolve.  The Rocq tree states one
cross-arm invariant, the memory ledger's, and states it in
`Checks/VmMapsDisjoint.v` beside the interval lemmas that prove it.
There is therefore no `rocq-baseline` header here — a baseline names
the commit a twin was READ at, and this file twins no Rocq file.  What
it generalises is `VmMapsDisjoint.v`'s shape, and the Rocq reading
behind that shape is `Checks/VmMapsDisjoint.lean`'s, at the baseline its
own header carries.
Not part of the trusted specification.

WHAT A CROSS-ARM INVARIANT IS.  A property of the MODEL that every
registered dispatcher arm carries from the model it was handed to the
model it answers with.  `vm_wf` is the one the tree already had: no
page-aligned byte has two owners.  The point of a registry is that the
coverage obligation is a PRODUCT — one goal per (invariant, arm) pair —
so registering an arm owes a fact per invariant and registering an
invariant owes a fact per arm, and neither can be added silently.

WHAT AN `Invariant` CANNOT BE, and this is the ticket's own constraint
read honestly.  The registry's entries are predicates on ONE model, so a
property of a STEP is not one of them.  "A descriptor this call created
is the lowest free one" is the standing example, and it is the reason
`State.lean` keeps the lowest-free reading per arm in `alloc_fd`'s own
lemmas rather than here: it is not a predicate on a state, and it is not
even true of every arm.  `ksys_dup3` (fs/file.c:1399-1431, Linux
v6.18.46, commit 1f99e9ab748f) installs the duplicate at the CALLER'S
`newfd` through `do_dup2` (fs/file.c:1265), not at the lowest free
descriptor, so a cross-arm claim that every new descriptor is
`alloc_fd`'s answer would be false the day `dup3`'s arm enters
`checked_table` — the SPEC is ported already (`dup3_spec`,
`Sys/Fs/File.lean`, installing at `newfd` through `fd_insert`); it is
the checker arm that is not.  What the registry carries in its place is
the state invariant the allocator's answer is only meaningful against —
that a descriptor is bound at most once — which Linux holds by
construction and, under `CONFIG_DEBUG_VFS`, asserts of itself
(`fd_install`, fs/file.c:652-677, Linux v6.18.46: one array slot per
descriptor, with `VFS_BUG_ON` on a second install).  A step-shaped registry is a
different object with a different alternation; this one does not pretend
to hold it.

WHAT ELSE THE TICKET NAMED AND THIS REGISTRY CANNOT HOLD, for the same
reason: the second half of "pipe capacity conservation" as
docs/lean-port/TESTING.md tier 3 words it — "a read never returns bytes
a write did not put there".  That relates a read's answer to the WRITE
HISTORY before it, a property of a trace and not of one model, so no
`inv_pred` can state it; what a state can carry is the first half, the
bound `pipes_within_capacity` below, and the trace half stays with the
pipe arms' own pins (`pipe_take` and `pipe_consume` over `State/Pipes.lean`).

WHY THE STRUCTURE CARRIES PROOF FIELDS AT ALL.  `inv_at_init` and
`inv_refused` are what a registered invariant cannot be without.  They
are the two halves of "the PREDICATE is not constant", which is LESS
than "the entry reads something", and the gap is what the `view` role of
the pins register exists to cover: a registration whose `inv_view`
ignores the model and hands back a fixed carrier value satisfies both
proof fields, is preserved by every arm for free, and is caught only by
the `_reads_the_` theorem `tools/check_lean_invariant_pins.py` demands
of each entry.  Without `inv_refused` the
registry accepts `fun _ => True`, which every arm preserves and which
says nothing — the vacuous guard.  Without `inv_at_init` it accepts
`fun _ => False`, which every arm also preserves, vacuously, because no
accepted step ever starts from a model satisfying it.  Each field
refuses exactly one of those, neither is derivable from the other, and
both are discharged at the registration site, so no tool has to ask
whether they were: this is guard G5's shape — a `CheckedArm` cannot be
built without its five proofs — one level up.  What they do NOT force is
that the invariant is Linux's rather than the model's; that is a
citation, which no type can hold, and
`tools/check_lean_invariant_pins.py` is what requires each registered
invariant to carry one in `Checks/Cases/Invariants.lean`.

WHERE THE `vm_wf` ENTRY'S PROOFS COME FROM.  Not from a second PROOF:
each arm's file under `Checks/Arms/` states its ledger fact once, as
`arm_<name>_preserves_vm` for `checked_table_preserves_vm`, and its
`vm_wf_arm_<name>` is that fact re-wrapped, accepted by definitional
unfolding (`arm_preserves inv_vm_wf c` and `arm_preserves_vm c` are the
same statement once the structure literal's projections reduce).  Both
alternations that name them are rendered by `tools/gen_lean_checked.py`
from those files, so an arm's registration owes the two facts in its own
file and writes neither alternative.  The same holds one level up:
registering an invariant here owes one fact in every arm's file, and the
generator refuses each file that lacks it by name.

THE BLIND SPOT THE ALTERNATION INHERITS is a property of `first` and not
of any file: `first` closes a goal with the earliest alternative whose
TYPE fits, and `arm_preserves inv c` unfolds to a statement about
`c.ca_check` alone, so an arm whose `ca_check` is definitionally another
arm's — `arm_exit_group` and `arm_exit` share `check_exit` — is closed by
the other arm's alternative when its own is missing.  The alternation is
then complete in fact and short one line in text.  The fact is owed all
the same, and the generator's refusal of an arm file without it is what
holds that by text: the day the two checkers diverge the shared closure
stops and the fallback names the pair. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-! ## What a registered invariant is -/

/-- One cross-arm invariant.  `inv_view` names the part of the model the
invariant reads and `inv_pred` is the property of that part, split so
that a checker which leaves the part alone discharges the invariant in
one step (`arm_preserves_of_view_frame`) whatever the property says.
The two proof fields are the non-vacuity obligations the file header
argues for. -/
structure Invariant where
  /-- The name a reader sees; the uncovered-pair message prints the
  registry entry itself, so this is for the pin register and the PR, not
  for the tactic. -/
  inv_name : String
  /-- The part of the model the invariant reads. -/
  inv_carrier : Type
  /-- How that part is read off a model. -/
  inv_view : Model → inv_carrier
  /-- The property of that part. -/
  inv_pred : inv_carrier → Prop
  /-- NOT VACUOUSLY FALSE: the invariant holds of the state `execve`
  builds, whatever image, break, mmap base, stack pointer, limit and
  process input the run declares.  Without this field `fun _ => False`
  registers and is preserved by every arm, since no accepted step starts
  from a model satisfying it. -/
  inv_at_init : ∀ (reserved : List (word × word)) (brk0 mbase sp : word) (lim : Int)
      (inp : ProcInput), inv_pred (inv_view (init_model reserved brk0 mbase sp lim inp))
  /-- NOT VACUOUSLY TRUE: some value of the carrier is refused.  Stated
  over the CARRIER and not over `Model`, because this tree has no
  `Model` constant outside its fixtures and a registration must not have
  to import one.  Without this field `fun _ => True` registers and every
  arm preserves it. -/
  inv_refused : ∃ x : inv_carrier, ¬ inv_pred x

/-- The invariant as a predicate on the model. -/
def Invariant.holds (inv : Invariant) (m : Model) : Prop := inv.inv_pred (inv.inv_view m)

/-- What one dispatcher arm owes one invariant.  The `VmMapsDisjoint`
twin's `arm_preserves_vm` is this at `inv_vm_wf`, and is accepted for it
below without a conversion step. -/
def arm_preserves (inv : Invariant) (c : CheckedArm) : Prop :=
  ∀ i eff m m' evs, c.ca_check i eff m = CheckOk m' evs → inv.holds m → inv.holds m'

/-- The frame reading: a checker that hands back the part an invariant
reads, unchanged, preserves it whatever it says.  This is
`VmMapsDisjoint.arm_preserves_of_frame` with the read part a parameter
rather than `m_vmmaps`. -/
theorem arm_preserves_of_view_frame (inv : Invariant) (c : CheckedArm)
    (hf : ∀ i eff m m' evs, c.ca_check i eff m = CheckOk m' evs →
      inv.inv_view m' = inv.inv_view m) :
    arm_preserves inv c := by
  intro i eff m m' evs h hold
  show inv.inv_pred (inv.inv_view m')
  rw [hf i eff m m' evs h]
  exact hold

/-! ## The invariants

Each is a `def` of the property over its carrier, so that a pin can name
the property without naming the registry entry, and then the entry. -/

/-- NO DESCRIPTOR IS BOUND TWICE.  Linux's descriptor table is an array
indexed by the descriptor — `fd_install` (fs/file.c:652-677, Linux
v6.18.46, commit 1f99e9ab748f) writes `fdt->fd[fd]` and asserts the slot
was empty (`VFS_BUG_ON(rcu_access_pointer(fdt->fd[fd]) != NULL)`, :666
and :674), and `alloc_fd` (fs/file.c:570-613) asserts the same of the
descriptor it just reserved (:608) — so no state Linux can be in binds
one descriptor to two files.  The model's table is an association list,
which can spell that state, and `fd_lookup` (`State/Fd.lean`) takes the
FIRST match, so a second binding would be a file no call could ever
reach, and one `fd_remove` — which filters every binding of the key —
would drop unreported along with the first.  Nothing in the model stops
the spelling; this invariant is what stops the state.

`Prod.fst` and not the pairs: two entries may bind different descriptors
to the same file (`dup`), which Linux does all day. -/
def fd_table_unique (fds : List (word × FdEntry)) : Prop := (fds.map Prod.fst).Nodup

/-- ONE PIPE STAYS INSIDE ITS PAGE.  `PipeBuf` is the queue a reader will
be handed and the high-water mark a writer merges against
(`State/Pipes.lean`).  In Linux the mark is `buf->offset + buf->len` of
the slot written last, `pipe_buf(pipe, head - 1)` (fs/pipe.c:479):
`anon_pipe_write` merges a top-up into that slot
only while `offset + chars <= PAGE_SIZE` (fs/pipe.c:480-483, Linux
v6.18.46, commit 1f99e9ab748f, where `offset` is that very sum), and
`anon_pipe_read` moves bytes from `len` into `offset` (fs/pipe.c:350-351)
so the sum does not fall when a reader takes bytes from a mergeable
slot — a `PIPE_BUF_FLAG_PACKET` slot has `len` zeroed (:356) and a
drained slot is released (:359-362), but a slot is packet OR mergeable
(:536-539), never both, so the sum the merge gate reads never falls.
Two claims follow, and this predicate is both: the queue never holds
more than the mark (in Linux the queue IS `buf->len`, the count the
reader takes its bytes from at fs/pipe.c:323, Linux v6.18.46, so the
bytes and the summand are one field), and the mark never exceeds the
page the slot lives in.  The model spells that page `PIPE_BUF` because
`pipe_write_room`, its only writer's gate, is written against `PIPE_BUF`
(`State/Pipes.lean`; the constant is `State/Fd.lean`'s, from
include/uapi/linux/limits.h:14 at Linux v6.18.46); the kernel line
bounds the same quantity by `PAGE_SIZE`.

WHAT IS LINUX'S HERE AND WHAT IS THE MODEL'S, said plainly so the entry
is not quoted for more than it holds.  Linux's is the bound on ONE slot:
the last-written `pipe_buffer`'s bytes sit inside its page.  A Linux pipe holds
up to `pipe->max_usage` such slots (sixteen pages by default, more by
`F_SETPIPE_SZ`), and a write that would need a second slot is exactly
what `pipe_write_room` DECLINES — the model's `PipeBuf` is a single-slot
representation, and the decline is its fail-closed edge, argued on that
definition.  So this invariant is a Linux property of the one slot the
model represents, and a bound the representation could not violate; it
is not a claim that a Linux pipe's capacity is a page.  The day a pipe
arm lifts the second-slot decline (a real Linux behaviour, priority 3),
`PipeBuf` changes shape and this entry is re-stated over the new one,
with the per-slot bound as its conjunct — the registration is what makes
that change visible instead of silent.

`0 ≤ st.2` is not a third conjunct: a list's length is not negative, so
the first conjunct gives it. -/
def pipe_within_capacity (st : PipeBuf) : Prop :=
  (st.1.length : Int) ≤ st.2 ∧ st.2 ≤ PIPE_BUF

/-- …of every pipe the model has handed out. -/
def pipes_within_capacity (ps : List (word × PipeBuf)) : Prop :=
  ∀ p ∈ ps, pipe_within_capacity p.2

/-! ### The registry entries -/

/-- The memory ledger's invariant, `Checks/VmMapsDisjoint.lean`'s. -/
def inv_vm_wf : Invariant where
  inv_name := "vm_wf"
  inv_carrier := VmMaps
  inv_view := m_vmmaps
  inv_pred := vm_wf
  inv_at_init := init_model_vm_wf
  inv_refused :=
    ⟨VmMaps.mkVmMapsFull [] [(65536, 4096), (65536, 100)] [] 65536 69632 0 0 0, by
      intro h
      -- `vm_wf` is a `def`, and `h`'s components mention the record's
      -- projection rather than the literal list; the ascription is what
      -- makes `omega` see the same term twice.
      have h' : sizes_nonzero [((65536 : word), (4096 : word)), (65536, 100)] ∧
          page_owner_unique [((65536 : word), (4096 : word)), (65536, 100)] := h
      have h1 := h'.2 65536 (by decide)
      have h2 : owners [((65536 : word), (4096 : word)), (65536, 100)] 65536 = 2 := by decide
      omega⟩

/-- The descriptor table's. -/
def inv_fd_table_unique : Invariant where
  inv_name := "fd_table_unique"
  inv_carrier := List (word × FdEntry)
  inv_view := m_fds
  inv_pred := fd_table_unique
  inv_at_init := by
    intro reserved brk0 mbase sp lim inp
    show ((([(Z_to_bv 64 0, FdEntry.FdChannel (Z_to_bv 64 0)),
             (Z_to_bv 64 1, FdEntry.FdChannel (Z_to_bv 64 1)),
             (Z_to_bv 64 2, FdEntry.FdChannel (Z_to_bv 64 2))] : List (word × FdEntry))).map
             Prod.fst).Nodup
    decide
  inv_refused :=
    ⟨[(Z_to_bv 64 0, FdEntry.FdChannel (Z_to_bv 64 0)),
      (Z_to_bv 64 0, FdEntry.FdChannel (Z_to_bv 64 1))], by
      -- As above: `fd_table_unique` is a `def`, so instance search does
      -- not see the `Nodup` behind it and `decide` has nothing to run.
      show ¬ ((([(Z_to_bv 64 0, FdEntry.FdChannel (Z_to_bv 64 0)),
                 (Z_to_bv 64 0, FdEntry.FdChannel (Z_to_bv 64 1))] :
                  List (word × FdEntry))).map Prod.fst).Nodup
      decide⟩

/-- The pipes'. -/
def inv_pipes_within_capacity : Invariant where
  inv_name := "pipes_within_capacity"
  inv_carrier := List (word × PipeBuf)
  inv_view := m_pipes
  inv_pred := pipes_within_capacity
  inv_at_init := by
    intro reserved brk0 mbase sp lim inp
    show ∀ p ∈ ([] : List (word × PipeBuf)), pipe_within_capacity p.2
    exact fun _ he => (List.not_mem_nil he).elim
  inv_refused :=
    ⟨[(Z_to_bv 64 0, (([], PIPE_BUF + 1) : PipeBuf))], by
      intro h
      exact absurd (h _ List.mem_cons_self).2 (by decide)⟩

/-- THE REGISTRY.  Append an entry and one goal per arm of
`checked_table` appears in `registry_preserves`, which
`tools/gen_lean_checked.py` renders into the generated module
`Checks.InvariantCoverage`, with no edit to its statement; the generator
refuses every arm file that does not state the entry's fact. -/
def invariant_registry : List Invariant :=
  inv_vm_wf ::
  inv_fd_table_unique ::
  inv_pipes_within_capacity ::
  []

/-! ## The split and the fallback

`inv_arms_split r t` turns `∀ inv ∈ r, ∀ c ∈ t, arm_preserves inv c` into
one goal per pair, in registry order and then table order, and closes it
outright when either list is empty.  `inv_arm_uncovered` is the fallback,
a step of its own AFTER the alternation and not its last alternative:
Lean's `first` is a `try … catch` and would swallow a failing
alternative, so the alternation closes with `| skip`, which always
succeeds, and an alternative written behind that line never runs — the
pair it names stays open and the step below fails naming it.  That is
`checked_table_preserves_vm`'s construction, and the argument for it in
full is on `vm_arm_uncovered`.  Both are here rather than beside the
generated `registry_preserves` that runs them because
`Checks/Cases/Invariants.lean` runs them over fixture registries and
tables too. -/

/-- One goal per (invariant, arm) pair. -/
macro "inv_arms_split " r:ident ", " t:ident : tactic =>
  `(tactic| (simp only [$r:ident, $t:ident, List.forall_mem_cons, List.mem_nil_iff,
      false_implies, implies_true, and_true]
             repeat' constructor))

open Lean Elab Tactic in
/-- The fallback that names the invariant AND the arm.  It prints the
goal's TYPE rather than the goal, for `vm_arm_uncovered`'s reason: the
case tag `constructor` attaches varies with the pair's position in the
product, and a pinned message must not. -/
elab "inv_arm_uncovered" : tactic => do
  let g ← getMainGoal
  let ty ← g.withContext do instantiateMVars (← g.getType)
  let msg : String :=
    "registry_preserves has no case for this (invariant, arm) pair.\n" ++
    "State `<invariant>_<arm> : arm_preserves <invariant> <arm>` in the arm's file under\n" ++
    "Checks/Arms/ -- from the checker's frame lemma through\n" ++
    "arm_preserves_of_view_frame, or from a preserves lemma directly, with\n" ++
    "`simp only [arm_unfold] at h` recovering the plain checker -- and let\n" ++
    "tools/gen_lean_checked.py render its `| exact <invariant>_<arm>` ABOVE the closing `| skip`;\n" ++
    "an alternative listed behind that line never runs.  The uncovered goal, which names\n" ++
    "the invariant and the arm:"
  throwError m!"{msg}\n⊢ {ty}"

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
