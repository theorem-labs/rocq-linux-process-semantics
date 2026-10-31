import Lean
import LinuxProcessSemantics.LinuxProcessSem.SysSimp
import LinuxProcessSemantics.LinuxProcessSem.BvBase
import LinuxProcessSemantics.LinuxProcessSem.State
import LinuxProcessSemantics.LinuxProcessSem.Monad
import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

/-! # Checks.Cases.TacticCore — reading a spec off its primitives, by one simp set

Not part of the trusted specification.  Lean-only: no Rocq file mirrors
this one.  What it stands in for is spread over the Rocq tree: the `model`
rewrite database `State.v` registers each setter/getter equation in
(`autorewrite with model`), `Checks/Cases/Prelude.v`'s `check_eq`
(`vm_compute` then `reflexivity`), and the executable checker's
soundness/completeness pair (`Checks/ExecutableSpecs.v`), through which a
Rocq check reads what a spec admits.  The Lean tree has no executable
checker, so a check is stated on the relation itself
(`Checks/Cases/Mm/Mmap.lean`'s header), and this file is what turns one
concrete call of a spec into a plain statement about its outcome.

## What `sys_norm` produces

On a goal, or with `at h` on a hypothesis, of the shape `<spec> args… i m o`
it rewrites until the statement is first-order in `o`:

    o = Ok eff m' evs
      ∨ ∃ a, o = Ok (eff a) (m' a) [] ∧ guard a
      ∨ o = Unmodeled

with every closed gate decided, every monad primitive replaced by its
reading, every setter and getter replaced by what it does to the model's
fields, and every closed subterm — a page rounding, a `maps_subtract` over
literal lists, a fixture — evaluated to its value.  The normal form of a
MODEL is its constructor tree: `Model.mkModelOf` of the seven subsystem
records, a symbolic base model `m` contributing `m.m_fd`, `m.m_vm`, … for
the fields nothing wrote.  Two models written differently therefore meet
in one term, and two models that differ are told apart field by field,
which is what a refutation needs and what the Rocq tree gets from
`vm_compute`.

## Two passes, and why

The first pass is `simp +decide only [sys_simp, …]`: it unfolds the spec,
decides the closed gates and reads each primitive.  The second is the
same call with `+ground`, which evaluates every closed subterm by
unfolding it (`Simp.Config.ground`; the rewrites it emits are proof terms
Lean's kernel checks by its own reduction, as it checks a `decide`).
One pass with `+ground` would do almost everything, and the measurement of
what it does not is `errno_demo_eperm_needs_two_passes` below: the
children of an application are simplified before its post-lemmas are
tried, and both the readings and ground evaluation are post-steps
(`postDefault` in the toolchain's `Lean.Meta.Tactic.Simp.Rewrite`, Lean
v4.34.0), so the closed `errno_from es` under a `bind` is evaluated to its
`choose` before `bind_errno_from_iff` sees the parent.  What reads it then
is `bind_choose_outcome_iff`, continuation first, and the errno's equation
lands behind everything a forged outcome's injectivity produces, where
nothing substitutes it: a refutation of an errno outside the list is left
open, while every positive check and every other refutation closes.  Two
passes keep the enumeration-first reading in force, and after the first
pass nothing of `Sys` type is left PROVIDED every gate was decided; a gate
over a symbolic model leaves `(if g then c1 else c2) i m o`, which
neither pass reads, and a check on such a call states the gate as the
spec has it.

## What is registered, at which priority

- The READINGS of the monad primitives, at the default priority: the
  `_iff` lemmas of `Monad.lean` and the ones below that it does not state.
- The UNFOLDING equation (`f.eq_1`, generated from the definition, so it
  cannot drift) of every `State` setter and getter, of every `Monad`
  setter, of every spec and of its post-state builders, at LOW priority.
  Gate predicates (`mmap_modeled_b`, …) are left out on purpose: a gate
  is decided, never unfolded, so a symbolic gate stays a readable Bool.
- A FIXTURE (`Checks/Cases/Prelude.lean`'s `fixture`, and any model a
  check names) enters the set in ONE of two ways, never both.  Either
  kept opaque, with its projection lemmas (`m_vmmaps (fixture h) = h`, …)
  at the default priority; or by its own unfolding equation, at low
  priority like every other, so that it is then a constructor tree like
  everything else.  Low priority on the getter unfoldings is what lets
  the first way fire at a node where the fixture is in view: `simp`
  tries the candidates at one node in priority order, so
  `m_vmmaps_symbolic_fixture` (below) is tried before `m_vmmaps.eq_1`
  opens the getter on a `symbolic_fixture h m0` it cannot see into.  Under `get_model` no such node
  exists: `sys_norm` normalises the continuation before the model is
  substituted, so the fixture lands in a raw projection no lemma matches
  and the first way is dead there (`Prelude.lean`'s
  `projection_registration_dies_under_get_model`), which is why a
  fixture with a SYMBOLIC argument that a check runs on takes the second.
  Where a spec reads its ledger through `get_vmmaps` directly instead of
  `get_model` -- `munmap_spec` does, alone under `Sys/` today -- such a
  node does exist: the fixture reaches the continuation whole, so both
  its projection lemma and its fold DO match
  (`projection_registration_reads_under_get_vmmaps` in
  `Checks/Cases/Prelude.lean`, against the same statement on a fixture
  registered neither way); a second spec reading `get_vmmaps` or
  `get_fds` directly is covered by the same pair, and no check runs a
  symbolic fixture on `munmap_spec`, so the rule stands.  `Prelude.lean`'s
  header argues that and pins both readings.
  A CLOSED model is a different case: `sys_norm`'s second pass evaluates
  it whether or not it is registered, so a closed model may stay a name
  behind projection lemmas at the default priority (`Fs/Stat.lean`'s
  `statat_absent_model`, `Fs/Sync.lean`'s models) with nothing owed to the
  register.  Neither way survives a mix:
  children are simplified before their parent, so with `fixture.eq_1` in
  the set the `fixture h` under `m_vmmaps` is opened first and a
  projection lemma on `m_vmmaps (fixture h)` never matches — the check
  `symbolic_fixture_unfolding_kills_projection` below pins that.  The
  unfoldings are `f.eq_1` and not `f` itself for the same reason:
  `attribute [sys_simp] f` on a non-recursive definition also puts `f` in
  the set's `toUnfold`, which `simp` applies before the children and
  before any post-lemma, whatever priority is named (`Simp.unfoldEvenWithEqns` in the toolchain's
  `Lean.Meta.Tactic.Simp.SimpTheorems`, v4.34.0; its own remark says this
  may change).  A closed fixture is evaluated by the second pass
  either way; which way a fixture chose matters where its argument is
  symbolic.

## Two conventions the readings assume

- The reading of `choose` puts the CONTINUATION first: `∃ x, k x i m o ∧
  P x`, not `Monad.bind_choose_iff`'s `P x ∧ k x i m o`.  When `o` is a
  forged outcome, `k x i m o` becomes `Ok forged = Ok (eff x) …` and its
  injectivity yields `v = x` as the FIRST conjunct, which `exists_eq_left'`
  substitutes whatever follows it; behind the guard it would sit at a
  depth no core lemma reaches, and `simp` cannot reorder conjuncts.
- `errno_from` is the exception, read ENUMERATION first: its guard is
  the membership that becomes the equation (`bind_errno_from_iff`).
- A guard that determines the choice states the equation FIRST
  (`choose (fun a => a = addr ∧ …)`), where `exists_eq_mid` substitutes it
  when `o` is symbolic.  The core lemmas cover an equation in the first,
  third-of-three and last positions; `exists_eq_mid` adds the second
  position with any tail.  A guard spelled otherwise still normalizes — the
  existential just stays, and the check states it as the spec has it.

## What a new definition owes

A `State` setter or getter, or a `Monad` setter: one
`attribute [sys_simp low] f.eq_1` line in the register below — and
`#check_sys_simp_register` at the end of the register fails the build
when one is missing, when the unfolding is registered at the default
priority or as a pre-lemma (`↓`), or when `f` itself was tagged (which
puts it in `toUnfold`, the FIXTURE bullet above), so the line is owed in
that shape, not remembered.  The probe at the end of this file is the
check's own negative: each wrong shape, refused by name.  A `Monad`
setter owes a second thing, in `Monad.lean`'s ticket D4 section: its
reading `bind_<name>_iff`, the instance of `bind_det_iff` at that setter,
which `#check_bind_readings` beside the register check demands the same
way.  The line moves
to the definition site once `State.lean` imports `SysSimp`, at the price
of the trusted spec importing `Lean.Meta.Tactic.Simp.RegisterCommand`.  A spec: the same line for the
spec and for each builder its post-states are spelled with; nothing for
its gates.  A fixture: its unfolding, or else its projection lemmas, in
the file that defines it — `Checks/Cases/Prelude.lean` imports `SysSimp`
for exactly that, and its header says which way each of its fixtures
chose.  A monad primitive: a reading below, stated with the continuation
first. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch

/-! ## The readings `Monad.lean` does not state

Each is stated over EVERY outcome, `Unmodeled` included, as the ones in
`Monad.lean` are, so an `Unmodeled` past the primitive is read exactly as
`bind` defines it. -/

/-- `choose`, continuation first (the file header says why this order and
not `Monad.bind_choose_iff`'s). -/
theorem bind_choose_outcome_iff {A B : Type} (P : A → Prop) (k : A → Sys B) (i : SyscallInput)
    (m : Model) (o : outcome B) : bind (choose P) k i m o ↔ ∃ x, k x i m o ∧ P x := by
  rw [bind_choose_iff]
  exact exists_congr (fun _ => and_comm)

/-- `errno_from`, ENUMERATION first.  It is a `choose` whose guard is a
list membership, and the membership is what becomes the equation
(`e ∈ [ENOMEM]` is `e = ENOMEM`), so here the guard leads and
`exists_eq_left` substitutes it whatever the continuation adds; read
continuation-first, the equation would sit behind every conjunct the
forged outcome's injectivity produces.  `errno_from` is therefore read
here and never unfolded to its `choose`. -/
theorem bind_errno_from_iff {B : Type} (es : List Int) (k : Int → Sys B) (i : SyscallInput)
    (m : Model) (o : outcome B) : bind (errno_from es) k i m o ↔ ∃ e, e ∈ es ∧ k e i m o :=
  bind_choose_iff (fun e => e ∈ es) k i m o

/-- `bind` distributes over `alt` on the left. -/
theorem bind_alt_iff {A B : Type} (c1 c2 : Sys A) (k : A → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind (alt c1 c2) k i m o ↔ bind c1 k i m o ∨ bind c2 k i m o := by
  cases o with
  | Ok y m2 evs =>
    constructor
    · rintro ⟨x, m1, e1, e2, (h | h), hk, he⟩
      · exact Or.inl ⟨x, m1, e1, e2, h, hk, he⟩
      · exact Or.inr ⟨x, m1, e1, e2, h, hk, he⟩
    · rintro (⟨x, m1, e1, e2, h, hk, he⟩ | ⟨x, m1, e1, e2, h, hk, he⟩)
      · exact ⟨x, m1, e1, e2, Or.inl h, hk, he⟩
      · exact ⟨x, m1, e1, e2, Or.inr h, hk, he⟩
  | Unmodeled =>
    constructor
    · rintro ((h | h) | ⟨x, m1, e1, (h | h), hk⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr ⟨x, m1, e1, h, hk⟩)
      · exact Or.inr (Or.inr ⟨x, m1, e1, h, hk⟩)
    · rintro ((h | ⟨x, m1, e1, h, hk⟩) | (h | ⟨x, m1, e1, h, hk⟩))
      · exact Or.inl (Or.inl h)
      · exact Or.inr ⟨x, m1, e1, Or.inl h, hk⟩
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨x, m1, e1, Or.inr h, hk⟩

/-- A bound helper is read by re-associating: `Monad.bind_assoc`, pointwise. -/
theorem bind_bind_iff {A B C : Type} (c : Sys A) (k : A → Sys B) (h : B → Sys C) (i : SyscallInput)
    (m : Model) (o : outcome C) :
    bind (bind c k) h i m o ↔ bind c (fun x => bind (k x) h) i m o :=
  bind_assoc c k h i m o

theorem bind_unmodeled_iff {A B : Type} (k : A → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind (unmodeled : Sys A) k i m o ↔ o = Unmodeled := by
  cases o with
  | Ok y m2 evs =>
    constructor
    · rintro ⟨x, m1, e1, e2, h, -, -⟩
      cases h
    · intro h
      cases h
  | Unmodeled =>
    exact ⟨fun _ => rfl, fun _ => Or.inl rfl⟩

/-- What `emit evs ;; k` makes of an outcome `k` admits: the events are
prepended, an `Unmodeled` stays one. -/
def prefix_events {A : Type} (evs : List event) : outcome A → outcome A
  | Ok y m2 evs2 => Ok y m2 (evs ++ evs2)
  | Unmodeled => Unmodeled

/-- `emit`, continuation first: one existential over the outcome `k`
admits, so that reading `k` yields a single leading equation for
`exists_eq_left`, however many events a chain of `emit`s adds. -/
theorem bind_emit_iff {B : Type} (evs : List event) (k : Unit → Sys B) (i : SyscallInput)
    (m : Model) (o : outcome B) :
    bind (emit evs) k i m o ↔ ∃ o', k () i m o' ∧ o = prefix_events evs o' := by
  cases o with
  | Ok y m2 evs' =>
    constructor
    · rintro ⟨x, m1, e1, e2, h, hk, he⟩
      simp only [emit, outcome.Ok.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      subst he
      exact ⟨Ok y m2 e2, hk, rfl⟩
    · rintro ⟨o', hk, ho⟩
      cases o' with
      | Ok y' m' e' =>
        simp only [prefix_events, outcome.Ok.injEq] at ho
        obtain ⟨rfl, rfl, rfl⟩ := ho
        exact ⟨(), m, evs, e', rfl, hk, rfl⟩
      | Unmodeled =>
        simp only [prefix_events] at ho
        cases ho
  | Unmodeled =>
    constructor
    · rintro (h | ⟨x, m1, e1, h, hk⟩)
      · cases h
      · simp only [emit, outcome.Ok.injEq] at h
        obtain ⟨-, rfl, rfl⟩ := h
        exact ⟨Unmodeled, hk, rfl⟩
    · rintro ⟨o', hk, ho⟩
      cases o' with
      | Ok y' m' e' =>
        simp only [prefix_events] at ho
        cases ho
      | Unmodeled =>
        exact Or.inr ⟨(), m, evs, rfl, hk⟩

/-- The primitives not under a `bind`, read as the statements they are. -/
theorem get_model_iff (i : SyscallInput) (m : Model) (o : outcome Model) :
    get_model i m o ↔ o = Ok m m [] := Iff.rfl
theorem get_fds_iff (i : SyscallInput) (m : Model) (o : outcome (List (word × FdEntry))) :
    get_fds i m o ↔ o = Ok (m_fds m) m [] := Iff.rfl
theorem get_vmmaps_iff (i : SyscallInput) (m : Model) (o : outcome VmMaps) :
    get_vmmaps i m o ↔ o = Ok (m_vmmaps m) m [] := Iff.rfl
theorem input_iff (i : SyscallInput) (m : Model) (o : outcome SyscallInput) :
    input i m o ↔ o = Ok i m [] := Iff.rfl
theorem sysno_iff (i : SyscallInput) (m : Model) (o : outcome word) :
    sysno i m o ↔ o = Ok i.in_sysno m [] := Iff.rfl
theorem arg_iff (n : Nat) (i : SyscallInput) (m : Model) (o : outcome word) :
    arg n i m o ↔ o = Ok (in_arg i n) m [] := Iff.rfl
theorem choose_iff {A : Type} (P : A → Prop) (i : SyscallInput) (m : Model) (o : outcome A) :
    choose P i m o ↔ ∃ x, o = Ok x m [] ∧ P x :=
  exists_congr (fun _ => and_comm)
theorem errno_from_iff (es : List Int) (i : SyscallInput) (m : Model) (o : outcome Int) :
    errno_from es i m o ↔ ∃ e, e ∈ es ∧ o = Ok e m [] := Iff.rfl
theorem modify_iff (f : Model → Model) (i : SyscallInput) (m : Model) (o : outcome Unit) :
    modify f i m o ↔ o = Ok () (f m) [] := Iff.rfl
theorem emit_iff (evs : List event) (i : SyscallInput) (m : Model) (o : outcome Unit) :
    emit evs i m o ↔ o = Ok () m evs := Iff.rfl

/-! ## The existential shapes the core lemmas leave -/

/-- An equation on the bound variable in the SECOND position, with any
tail: what a `choose` guard that leads with its equation produces once the
outcome equation precedes it.  Core's `exists_eq_right_right` covers the
third-of-three position and `exists_eq_left`/`exists_eq_right` the ends. -/
theorem exists_eq_mid {α : Sort _} {p q : α → Prop} {v : α} :
    (∃ a, p a ∧ a = v ∧ q a) ↔ p v ∧ q v := by
  constructor
  · rintro ⟨a, hp, rfl, hq⟩
    exact ⟨hp, hq⟩
  · rintro ⟨hp, hq⟩
    exact ⟨v, hp, rfl, hq⟩

theorem exists_eq_mid' {α : Sort _} {p q : α → Prop} {v : α} :
    (∃ a, p a ∧ v = a ∧ q a) ↔ p v ∧ q v := by
  constructor
  · rintro ⟨a, hp, rfl, hq⟩
    exact ⟨hp, hq⟩
  · rintro ⟨hp, hq⟩
    exact ⟨v, hp, rfl, hq⟩

/-- An `emit` past a `choose`: the outcome `k` admits is itself an
existential, and the two collapse into one.  Stated in the orientation the
readings above produce — the bound outcome on the left of its equation,
the continuation before the guard — which no core lemma covers. -/
theorem exists_exists_eq_and_and {α β : Sort _} {f : α → β} {p : α → Prop} {q : β → Prop} :
    (∃ b, (∃ a, b = f a ∧ p a) ∧ q b) ↔ ∃ a, q (f a) ∧ p a := by
  constructor
  · rintro ⟨b, ⟨a, rfl, hp⟩, hq⟩
    exact ⟨a, hq, hp⟩
  · rintro ⟨a, hq, hp⟩
    exact ⟨f a, ⟨a, rfl, hp⟩, hq⟩

/-! ## The register

Grouped by the file each member comes from.  Readings and fixture lemmas at
the default priority, unfoldings at `low`; the file header says why. -/

attribute [sys_simp]
  bind_get_model_iff bind_modify_iff bind_pure_iff pure_iff unmodeled_iff alt_iff
  bind_get_fds_iff bind_get_vmmaps_iff bind_input_iff bind_sysno_iff bind_arg_iff  -- Monad.lean's, since D4
  bind_choose_outcome_iff bind_errno_from_iff bind_alt_iff bind_bind_iff bind_unmodeled_iff
  bind_emit_iff
  get_model_iff get_fds_iff get_vmmaps_iff input_iff sysno_iff arg_iff choose_iff errno_from_iff
  modify_iff
  emit_iff prefix_events.eq_1 prefix_events.eq_2  -- the helper's reading; nothing competes
  exists_eq_mid exists_eq_mid' exists_exists_eq_and_and

-- Monad.lean: the setters, each a `modify` of a `State` setter.
attribute [sys_simp low]
  set_fds.eq_1 set_pipes.eq_1 set_vmmaps.eq_1 forget_vm_range.eq_1 set_stdin.eq_1 set_urandom.eq_1 set_fs.eq_1
  set_halted.eq_1 set_tid.eq_1 set_creds.eq_1 set_rlimit_core.eq_1 set_setsid_succeeded.eq_1
  set_sigmask.eq_1 set_clock.eq_1 add_vm_lazy.eq_1 set_utsname.eq_1
  set_statpin.eq_1 set_sigaltstack_installed.eq_1 set_sigabrt_pending.eq_1 set_killed.eq_1

-- State.lean: the getters, the setters, the model builders, the effect builder.
attribute [sys_simp low]
  m_fds.eq_1 m_pipes.eq_1 m_vmmaps.eq_1 m_vm_lazy.eq_1 m_vm_materialized.eq_1 m_stdin.eq_1
  m_net.eq_1 m_conn_ix.eq_1 m_fs.eq_1 m_halted.eq_1 m_tid.eq_1 m_setsid_succeeded.eq_1
  m_has_children.eq_1 m_sigmask.eq_1 m_rlimit_core.eq_1 m_nofile.eq_1 m_clock.eq_1 m_creds.eq_1
  m_utsname.eq_1 m_sigaltstack_installed.eq_1 m_killed.eq_1 m_sigabrt_pending.eq_1
  m_urandom.eq_1
  m_abort_terminal.eq_1 m_statpins.eq_1
  with_fds.eq_1 with_pipes.eq_1 with_vmmaps.eq_1 with_vm_backing.eq_1 with_stdin.eq_1
  with_net.eq_1 with_fs.eq_1 with_halted.eq_1 with_tid.eq_1 with_rlimit_core.eq_1
  with_nofile.eq_1 with_creds.eq_1 with_setsid_succeeded.eq_1 with_children.eq_1
  with_sigmask.eq_1 with_clock.eq_1 with_accepted.eq_1 with_utsname.eq_1
  with_urandom.eq_1
  with_statpin.eq_1 with_abort_terminal.eq_1 with_sigaltstack_installed.eq_1
  with_sigabrt_pending.eq_1 with_killed.eq_1
  statpins_restrict.eq_1 statpin_lookup.eq_1 statpin_lookup.eq_2  -- what `with_fs` and the stat pin read
  mkModel.eq_1 init_model.eq_1 vm_forget_range.eq_1 vm_add_lazy.eq_1
  mkEffect.eq_1 with_copyins.eq_1  -- `mkEffect` is an abbrev; its equation is still what rewrites it

-- Sys/Syscall.lean: the calling-convention wrappers (`errno_from` is read above, not unfolded).
attribute [sys_simp low] ret_only.eq_1 err_ret.eq_1
-- Sys/Syscall.lean, ticket D4: `record_copyins` is read continuation first (`record_copyins_iff`, a
-- reading, so at the default priority), and `outcome_copyins`'s equations then attach the ledger to
-- each outcome the inner spec is read to.  The wrapper's own unfolding is registered too, at `low` like
-- every other: it is what reads the wrapper when its RESULT is bound under a further `bind`, where the
-- two-argument `record_copyins reads spec` is a child the five-argument reading cannot match and the
-- unfolding hands the parent to `bind_bind_iff`.  At a full application the reading is tried first, by
-- priority, so the unfolding never fires there (`Checks/Cases/Sys/Syscall.lean`'s `ledger_bound_demo_iff`
-- and `ledger_demo_iff` pin the two routes).
attribute [sys_simp] record_copyins_iff
attribute [sys_simp low] record_copyins.eq_1 outcome_copyins.eq_1 outcome_copyins.eq_2


open Lean Elab Command Meta in
/-- The register is complete for the model, IN THE SHAPE THE HEADER
PRESCRIBES: every definition of `State` named `with_*` or `m_*`, and
every definition of `Monad` named `set_*`, `add_*` or `forget_*`, has its
`eq_1` in `sys_simp` as a post-lemma below the default priority, and is
not itself in the set's `toUnfold`.  Read off the environment, so a
setter added to `State.lean` without its line here fails this file's
build rather than the next check that reads it — and so does a line in the wrong shape,
which the first version of this check let through: a bare
`attribute [sys_simp] f` (whose `toUnfold` entry `simp` applies before any
post-lemma, whatever priority is named) and an `f.eq_1` at the default
priority (which beats a fixture's projection lemma at the same node)
both passed as "registered", and the second version let a `↓`
pre-registration through, tried before any post-lemma at whatever
priority it names.  Nested namespaces (`State.Foo.with_x`) are
walked too; structure projections (`Model.m_fd`, the raw fields the
`m_*` getters read through) are skipped, and not because the shape is
unwritable — `Model.m_fd.eq_1 : m_fd self = self.1` elaborates like any
other — but because it must not be written: `m.m_fd` on a symbolic `m` is
the normal-form leaf the header names, `simp` reduces a projection of a
constructor by itself before any lemma is tried, and tagging the
projection registers no equation but sends the name to `toUnfold`
(`Simp.ignoreEquations` in the toolchain's
`Lean.Meta.Tactic.Simp.SimpTheorems`, v4.34.0).  The walk sees `def`s
only: a `private`, `partial` or `opaque` definition under the namespace
is outside it (none exists today), and `eq_1` is the whole unfolding
only for a body with no top-level `match` — a split body owes each of its
equations by hand, as `statpin_lookup.eq_1`/`.eq_2` are.  The bound of the
check is the environment at its call site: a registration in a file that
imports this one, or below the call in this file, is out of its sight, and
the guard is complete only while the register below is the one place a
`State` or `Monad` definition is tagged.  The names are reported sorted,
one per line, so the probe at the end of the file can pin the message. -/
def checkSysSimpRegister (wanted : List (Name × List String)) : CommandElabM Unit := do
  let some ext ← liftCoreM (getSimpExtension? `sys_simp)
    | throwError "sys_simp is not registered"
  let thms ← liftCoreM ext.getTheorems
  -- origin ↦ the highest priority a live tree entry gives it; `isLemma` alone
  -- cannot see the priority.  On this toolchain there is one entry per
  -- equation: `SimpTheorem`'s `BEq` compares the proof alone, and the tree
  -- keeps one value per equal key, so a second `attribute [sys_simp] f.eq_1`
  -- REPLACES the first and the last line wins, for `simp` and for this check
  -- alike (the probe's `with_dup`).  Two entries of one origin exist only
  -- across the two trees (`↓` at one priority and a post-lemma at another,
  -- the probe's `with_pre_dup`); the fold takes the highest so that the
  -- default-priority one is reported however the lines are ordered.
  -- An erased member (`attribute [-sys_simp] f.eq_1`) STAYS in the trees and
  -- joins `erased`, so a tree entry counts only while `erased` does not hold
  -- it -- and the attribute never clears `erased` (Lean 4 issue #5852, the
  -- note on `SimpTheorems.uneraseSimpEntry`), so a re-registration after an
  -- erasure is as dead for `simp`, whose `rewrite?` skips erased origins, as
  -- for this check (the probe's `with_readded`).
  let live (t : SimpTheorem) : Bool := !thms.erased.contains t.origin
  let prios : Std.HashMap Origin Nat :=
    (thms.pre.values ++ thms.post.values).foldl (init := {}) fun acc t =>
      if live t then acc.insert t.origin (max t.priority (acc.getD t.origin 0)) else acc
  -- origins with a live PRE entry (`attribute [sys_simp ↓] f.eq_1`): a pre-lemma
  -- is tried before the children and before every post-lemma, so it opens the
  -- getter before a fixture's projection lemma is reached, at any priority.
  let pres : Std.HashMap Origin Unit :=
    thms.pre.values.foldl (init := {}) fun acc t => if live t then acc.insert t.origin () else acc
  let env ← getEnv
  for (ns, prefixes) in wanted do
    let (found, missing, bare, dflt, pre) :=
      env.constants.fold
        (init := ((0 : Nat), (#[] : Array Name), (#[] : Array Name), (#[] : Array Name), (#[] : Array Name)))
        fun (found, missing, bare, dflt, pre) n ci =>
          match ci, n with
          | .defnInfo _, .str owner last =>
            if ns.isPrefixOf owner && prefixes.any (fun q => last.startsWith q)
                && !env.isProjectionFn n then
              let key := Origin.decl (n ++ `eq_1)
              let bare := if thms.toUnfold.contains n then bare.push n else bare
              let pre := if pres.contains key then pre.push n else pre
              match prios[key]? with
              | none => (found + 1, missing.push n, bare, dflt, pre)
              | some p =>
                if p < eval_prio default then (found + 1, missing, bare, dflt, pre)
                else (found + 1, missing, bare, dflt.push n, pre)
            else (found, missing, bare, dflt, pre)
          | _, _ => (found, missing, bare, dflt, pre)
    -- A namespace that matched nothing is a renamed namespace, not a complete
    -- register: the check would otherwise pass with nothing to say.
    if found == 0 then
      throwError "no definition of {ns} is named {prefixes}: the register check reads nothing"
    let list (a : Array Name) : String :=
      String.intercalate "\n" ((a.qsort (fun x y => x.toString < y.toString)).toList.map (fun n => "  " ++ n.toString))
    let mut problems : Array String := #[]
    unless missing.isEmpty do
      problems := problems.push s!"sys_simp register is missing the unfolding of:\n{list missing}"
    unless dflt.isEmpty do
      problems := problems.push
        s!"sys_simp register has the unfolding at or above the default priority (tag `f.eq_1` at `low`) of:\n{list dflt}"
    unless bare.isEmpty do
      problems := problems.push
        s!"sys_simp register has the definition itself tagged (in `toUnfold`; tag `f.eq_1` at `low`, not `f`) for:\n{list bare}"
    unless pre.isEmpty do
      problems := problems.push
        s!"sys_simp register has the unfolding as a pre-lemma (`↓`; tag `f.eq_1` at `low` as a post-lemma) for:\n{list pre}"
    unless problems.isEmpty do
      throwError "{String.intercalate "\n" problems.toList}"

open Lean Elab Command in
/-- The register check over the model's two namespaces (`checkSysSimpRegister`). -/
elab "#check_sys_simp_register" : command =>
  checkSysSimpRegister
    [(`LinuxProcessSemantics.LinuxProcessSem.State, ["with_", "m_"]),
     (`LinuxProcessSemantics.LinuxProcessSem.Monad, ["set_", "add_", "forget_"])]

open Lean Elab Command in
/-- The same check over a named namespace and prefixes, for the probe
below: `#check_sys_simp_register_over Ns "with_" "m_"`. -/
elab "#check_sys_simp_register_over" ns:ident ps:str* : command =>
  checkSysSimpRegister [(ns.getId, ps.toList.map (·.getString))]

#check_sys_simp_register

open Lean Elab Command in
/-- Ticket D4's obligation, read off the environment as the register's is:
every setter of `Monad` -- a definition named `set_*`, `add_*` or
`forget_*` -- has its reading `Monad.bind_<name>_iff`, the instance of
`Monad.bind_det_iff` at that setter, so a setter added after the D4
section of `Monad.lean` fails this file's build rather than leaving the
next proof to take `bind`'s existential apart by hand. -/
elab "#check_bind_readings" : command => do
  let ns := `LinuxProcessSemantics.LinuxProcessSem.Monad
  let env ← getEnv
  let (found, missing) := env.constants.fold (init := ((0 : Nat), (#[] : Array Name)))
    fun (found, missing) n ci =>
      match ci, n with
      | .defnInfo _, .str pre last =>
        if pre == ns && ["set_", "add_", "forget_"].any (fun q => last.startsWith q) then
          if env.contains (.str ns ("bind_" ++ last ++ "_iff")) then (found + 1, missing)
          else (found + 1, missing.push n)
        else (found, missing)
      | _, _ => (found, missing)
  if found == 0 then
    throwError "no definition of {ns} is named set_/add_/forget_: the readings check reads nothing"
  unless missing.isEmpty do
    throwError "Monad.lean's D4 section is missing the reading bind_<name>_iff of: {missing}"

#check_bind_readings

/-! ## The tactics -/

/-- One pass of the normalizer, under the given `simp` configuration: the
`sys_simp` set, the injectivity of every outcome, effect, model and event
constructor, and the propositional and existential lemmas that turn the
readings' result into a plain statement.  `sys_norm` runs it twice with
the configurations the file header explains. -/
syntax "sys_simp_pass" Lean.Parser.Tactic.optConfig (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| sys_simp_pass $cfg:optConfig $[$loc]?) =>
    `(tactic| simp $cfg:optConfig only [sys_simp, ↓reduceIte,
        outcome.Ok.injEq, SyscallEffect.mkEffectU.injEq, Model.mkModelOf.injEq,
        VmMaps.mkVmMapsFull.injEq, FdState.mkFdState.injEq, VmState.mkVmState.injEq,
        IoState.mkIoState.injEq, FsState.mkFsState.injEq, ProcState.mkProcState.injEq,
        LimState.mkLimState.injEq, TimeState.mkTimeState.injEq, Creds.mkCreds.injEq,
        event.ReadEv.injEq, event.WriteEv.injEq, event.ExitEv.injEq, event.KillEv.injEq,
        Option.some.injEq, List.cons.injEq, Prod.mk.injEq, reduceCtorEq,
        List.cons_ne_nil, List.nil_eq, List.mem_singleton, List.mem_cons, List.not_mem_nil,
        List.append_nil, List.nil_append, List.cons_append, List.append_assoc,
        and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or,
        and_self, or_self, and_assoc, and_or_left, or_and_right, iff_self, eq_self_iff_true,
        exists_or, exists_const, exists_false, exists_eq, exists_eq', exists_eq_left,
        exists_eq_left', exists_eq_right, exists_eq_right', exists_eq_right_right,
        exists_eq_right_right', exists_and_left, exists_and_right, exists_eq_or_imp, exists_eq_or_imp',
        exists_or_eq_imp, exists_or_eq_imp',
        not_or, not_exists, not_and, not_false_eq_true, not_true_eq_false, ne_eq,
        Bool.false_eq_true, Bool.true_eq_false] $[$loc]?)

/-- Read a concrete call of a spec off as a first-order statement about its
outcome: unfold the spec, decide every closed gate, replace each primitive
by its reading, then evaluate what is closed.  `sys_norm at h` does the
same to a hypothesis. -/
macro "sys_norm" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| (sys_simp_pass +decide $[$loc]?;
             first
               | done
               | sys_simp_pass +ground +decide -failIfUnchanged $[$loc]?))

/-- Refute: `sys_norm`, and the goal must be closed by it — an outcome
outside what the spec allows differs from every allowed one in some
component that the normal form decides, and a `¬` that survives is
reported as the unsolved residue rather than left for the next tactic to
misread.  `sys_refute at h` closes the goal by reducing `h` to `False`. -/
macro "sys_refute" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| (sys_norm $[$loc]?; done))

/-! ## Worked checks of the normal form

Every reading under a `bind` exercised positively and refuted, on programs
written for the purpose (registered `local`, so the set other files import
holds the model and the specs only); the bare readings on one primitive
outside any `bind`; then the one real spec whose post-state is fully
symbolic, `exit_spec`, and the dispatcher.  Nothing here is a claim about
`mmap`: those checks are `Checks/Cases/Mm/Mmap.lean`'s. -/

/-- A primitive outside any `bind` is read by its bare reading. -/
example (i : SyscallInput) (m : Model) (o : outcome Int) :
    errno_from [ENOMEM] i m o ↔ o = Ok ENOMEM m [] := by
  sys_norm
example (i : SyscallInput) (m : Model) (o : outcome Unit) :
    modify (with_clock 3) i m o ↔ o = Ok () (with_clock 3 m) [] := by
  sys_norm

/-- Every reader, and the model untouched. -/
def readers_demo : Sys SyscallEffect :=
  i <- input ;; n <- sysno ;; a <- arg 1 ;; m <- get_model ;; fds <- get_fds ;; vm <- get_vmmaps ;;
  Monad.pure (SyscallEffect.mkEffectU n [] [(a, len_word fds)] [(i.in_sysno, vm.vm_brk)] []
                [(len_word (m_fds m), 0)])

attribute [local sys_simp low] readers_demo.eq_1

theorem readers_demo_iff (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    readers_demo i m o ↔
      o = Ok (SyscallEffect.mkEffectU i.in_sysno [] [(in_arg i 1, len_word (m_fds m))]
                [(i.in_sysno, (m_vmmaps m).vm_brk)] [] [(len_word (m_fds m), 0)]) m [] := by
  sys_norm

theorem readers_demo_never_unmodeled (i : SyscallInput) (m : Model) :
    ¬ readers_demo i m Unmodeled := by
  sys_refute

/-- The zero-fill names the SECOND argument, not the first: a forgery that
swaps them is refuted on the effect, once the two arguments are known to
differ.  With `at h` the normal form of the forgery is the conjunction of
what would have to hold, and its first conjunct is the swapped pair. -/
theorem readers_demo_wrong_arg_rejected (i : SyscallInput) (m m' : Model) (evs : List event)
    (hne : in_arg i 0 ≠ in_arg i 1) :
    ¬ readers_demo i m
        (Ok (SyscallEffect.mkEffectU i.in_sysno [] [(in_arg i 0, len_word (m_fds m))]
              [(i.in_sysno, (m_vmmaps m).vm_brk)] [] [(len_word (m_fds m), 0)]) m' evs) := by
  intro h
  sys_norm at h
  exact hne h.1

/-- A helper spec bound in another: `choose` under `bind_bind_iff`, a
setter, and `alt` against an `unmodeled` arm. -/
def helper_demo (bound : word) : Sys word :=
  y <- choose (fun y => bv_unsigned y < bv_unsigned bound) ;; set_clock y ;; Monad.pure y

def chooser_demo : Sys SyscallEffect :=
  alt ((unmodeled : Sys Unit) ;; Monad.pure (mkEffect 0 [] []))
      (y <- helper_demo 4 ;; Monad.pure (mkEffect y [] []))

attribute [local sys_simp low] helper_demo.eq_1 chooser_demo.eq_1

theorem chooser_demo_iff (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    chooser_demo i m o ↔
      (o = Unmodeled ∨ ∃ y : word, o = Ok (mkEffect y [] []) (with_clock y m) [] ∧ bv_unsigned y < 4) := by
  sys_norm

/-- A concrete admitted outcome closes by `sys_norm` alone: the forged
value is substituted into the guard and the guard is evaluated. -/
theorem chooser_demo_three_admitted (i : SyscallInput) (m : Model) :
    chooser_demo i m (Ok (mkEffect 3 [] []) (with_clock 3 m) []) := by
  sys_norm

theorem chooser_demo_seven_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ chooser_demo i m (Ok (mkEffect 7 [] []) m' evs) := by
  sys_refute

/-- …and so does the same forgery arriving as a hypothesis. -/
theorem chooser_demo_seven_rejected_at (i : SyscallInput) (m m' : Model) (evs : List event)
    (h : chooser_demo i m (Ok (mkEffect 7 [] []) m' evs)) : False := by
  sys_refute at h

/-- The clock is WRITTEN: a success that leaves the model alone is refuted
on the time field, even though every other field agrees.  Nothing decides
this for the tactic: a model rebuilt from `m`'s fields with one of them
replaced is never syntactically `m` (structure eta is not a rewrite), so
the refutation reads the replaced field off the equation and the check
states what `m` holds there as a hypothesis. -/
theorem chooser_demo_unwritten_clock_rejected (i : SyscallInput) (m : Model)
    (hm : m_clock m ≠ 3) :
    ¬ chooser_demo i m (Ok (mkEffect 3 [] []) m []) := by
  sys_norm
  intro h
  exact hm (congrArg m_clock h)

/-- The environment's errno choice: one arm per errno of the list, and
an errno outside it is the lie no kernel tells. -/
def errno_demo : Sys SyscallEffect :=
  e <- errno_from [ENOMEM, EINVAL] ;; err_ret e

attribute [local sys_simp low] errno_demo.eq_1

theorem errno_demo_iff (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    errno_demo i m o ↔
      (o = Ok (mkEffect (errno_ret ENOMEM) [] []) m [] ∨ o = Ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  sys_norm


theorem errno_demo_enomem_admitted (i : SyscallInput) (m : Model) :
    errno_demo i m (Ok (mkEffect (errno_ret ENOMEM) [] []) m []) := by
  sys_norm

theorem errno_demo_eperm_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ errno_demo i m (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  sys_refute

/-- The measurement the two-pass design rests on (file header): ONE pass
with `+ground` leaves this refutation open, because the closed
`errno_from [ENOMEM, EINVAL]` is evaluated to its `choose` before the
enumeration-first reading sees it.  If a toolchain bump makes the single
pass close it, this check fails and the header's argument is up for
review. -/
theorem errno_demo_eperm_needs_two_passes (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ errno_demo i m (Ok (mkEffect (errno_ret EPERM) [] []) m' evs) := by
  fail_if_success (sys_simp_pass +ground +decide; done)
  sys_refute

theorem errno_demo_success_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ errno_demo i m (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- A guard that DETERMINES the choice, equation first: with `o` symbolic
`exists_eq_mid` substitutes it and the rest of the guard stays as stated. -/
def guarded_demo (addr : word) : Sys SyscallEffect :=
  a <- choose (fun a => a = addr ∧ bv_unsigned a % page_size = 0) ;; Monad.pure (mkEffect a [] [])

attribute [local sys_simp low] guarded_demo.eq_1

theorem guarded_demo_iff (addr : word) (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    guarded_demo addr i m o ↔ o = Ok (mkEffect addr [] []) m [] ∧ bv_unsigned addr % page_size = 0 := by
  sys_norm

theorem guarded_demo_aligned_admitted (i : SyscallInput) (m : Model) :
    guarded_demo 8192 i m (Ok (mkEffect 8192 [] []) m []) := by
  sys_norm

theorem guarded_demo_other_address_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ guarded_demo 8192 i m (Ok (mkEffect 4096 [] []) m' evs) := by
  sys_refute

theorem guarded_demo_unaligned_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ guarded_demo 1 i m (Ok (mkEffect 1 [] []) m' evs) := by
  sys_refute

/-- `alt` under a `bind`: the continuation is read against each arm. -/
def alt_demo : Sys SyscallEffect :=
  x <- alt (Monad.pure (1 : word)) (Monad.pure 2) ;; Monad.pure (mkEffect x [] [])

attribute [local sys_simp low] alt_demo.eq_1

theorem alt_demo_iff (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    alt_demo i m o ↔ (o = Ok (mkEffect 1 [] []) m [] ∨ o = Ok (mkEffect 2 [] []) m []) := by
  sys_norm

theorem alt_demo_three_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ alt_demo i m (Ok (mkEffect 3 [] []) m' evs) := by
  sys_refute

/-- `emit` before and after a `choose`: events concatenate in program order
around the chosen value, and one existential survives. -/
def emit_demo : Sys SyscallEffect :=
  emit [WriteEv 1 65] ;; b <- choose (fun b : byte => bv_unsigned b < 2) ;;
  emit [WriteEv 1 b] ;; Monad.pure (mkEffect 0 [] [])

attribute [local sys_simp low] emit_demo.eq_1

theorem emit_demo_iff (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    emit_demo i m o ↔
      ∃ b : byte, o = Ok (mkEffect 0 [] []) m [WriteEv 1 65, WriteEv 1 b] ∧ bv_unsigned b < 2 := by
  sys_norm

theorem emit_demo_admitted (i : SyscallInput) (m : Model) :
    emit_demo i m (Ok (mkEffect 0 [] []) m [WriteEv 1 65, WriteEv 1 1]) := by
  sys_norm

theorem emit_demo_reordered_rejected (i : SyscallInput) (m m' : Model) :
    ¬ emit_demo i m (Ok (mkEffect 0 [] []) m' [WriteEv 1 1, WriteEv 1 65]) := by
  sys_refute

theorem emit_demo_never_unmodeled (i : SyscallInput) (m : Model) :
    ¬ emit_demo i m Unmodeled := by
  sys_refute

/-- A getter over a setter, with everything symbolic: read to the fields. -/
example (m : Model) (h : VmMaps) : m_vm_lazy (with_vmmaps h m) = m_vm_lazy m := by sys_norm
example (m : Model) (h : VmMaps) : m_vmmaps (with_vmmaps h m) = h := by sys_norm
example (m : Model) (v : word) : m_fs (with_halted v m) = m_fs m := by sys_norm

/-- The priority contract: a fixture whose only registered fact is a
projection lemma keeps it.  `symbolic_fixture` is deliberately NOT
registered for unfolding, so the check below closes only if
`m_vmmaps_symbolic_fixture` is tried before `m_vmmaps.eq_1` opens the
getter on a term it cannot see into. -/
def symbolic_fixture (h : VmMaps) (m0 : Model) : Model := with_vmmaps h m0

@[local sys_simp] theorem m_vmmaps_symbolic_fixture (h : VmMaps) (m0 : Model) :
    m_vmmaps (symbolic_fixture h m0) = h := rfl

example (h : VmMaps) (m0 : Model) : m_vmmaps (symbolic_fixture h m0) = h := by sys_norm

set_option linter.unusedSimpArgs false in
/-- …and why a fixture cannot have both: with the unfolding in the same
list, the child `symbolic_fixture h m0` is opened before the projection
lemma is tried at the parent, the lemma never matches, and what is left is
the getter over the setter.  `guard_target` pins that the lemma was dead;
`sys_norm` then reads the residue the ordinary way.  The unused-argument
linter is silenced here because the unused argument is the claim. -/
theorem symbolic_fixture_unfolding_kills_projection (h : VmMaps) (m0 : Model) :
    m_vmmaps (symbolic_fixture h m0) = h := by
  simp only [symbolic_fixture.eq_1, m_vmmaps_symbolic_fixture]
  guard_target =ₛ m_vmmaps (with_vmmaps h m0) = h
  sys_norm


/-! ### The register check's own negative

Definitions tagged in the wrong shapes the header forbids — not at all,
at the default priority, the definition itself, tagged right and then
erased, tagged right after an erasure (which Lean never clears, issue
#5852), as a pre-lemma and in reverse — beside three tagged right: plainly, in a
nested namespace so that the prefix walk is exercised, and at the
default priority and then at `low`, which on this toolchain leaves the
`low` entry alone (a re-registration replaces the entry) and so is not
a wrong shape; under a namespace of their own so that the real register
is not touched, with the attributes `local` to the section, so nothing
of this probe reaches the set a check reads.  A structure field named
like a setter sits beside them: a projection, which the walk must skip.
`#guard_msgs` pins that the check names each wrong one under its own
heading and stays silent on the right ones and on the projection: a check that accepted a wrong one, or a toolchain
that kept both `with_dup` entries, would change this message and fail
the build here. -/

namespace RegisterProbe
def with_low (m : Model) : Model := m
def with_missing (m : Model) : Model := m
def with_default (m : Model) : Model := m
def with_bare (m : Model) : Model := m
def with_erased (m : Model) : Model := m
def with_readded (m : Model) : Model := m
def with_dup (m : Model) : Model := m
def with_pre (m : Model) : Model := m
def with_pre_dup (m : Model) : Model := m
def with_high (m : Model) : Model := m
def with_bare_low (m : Model) : Model := m
namespace Inner
def with_nested_low (m : Model) : Model := m
def with_nested_missing (m : Model) : Model := m
end Inner
/-- A structure whose field is named like a setter: its projection must be
skipped, not reported missing. -/
structure Rec where
  with_field : Nat
/-- Registered in reverse (`←`): the origin carries `inv := true`, which is
not the origin of the forward equation, so it reads as MISSING. -/
def with_reversed (m : Model) : Model := with_low m
end RegisterProbe

section
attribute [local sys_simp low] RegisterProbe.with_low.eq_1
attribute [local sys_simp] RegisterProbe.with_default.eq_1
attribute [local sys_simp] RegisterProbe.with_bare
-- Registered right, then erased: the trees keep the entry, `erased` names it,
-- and the check must report it MISSING like a name never tagged.
attribute [local sys_simp low] RegisterProbe.with_erased.eq_1
attribute [-sys_simp] RegisterProbe.with_erased.eq_1
-- Registered right, erased, registered right again: the attribute never clears
-- `erased`, so `simp` skips it and the check must still say MISSING.
attribute [local sys_simp low] RegisterProbe.with_readded.eq_1
attribute [-sys_simp] RegisterProbe.with_readded.eq_1
attribute [local sys_simp low] RegisterProbe.with_readded.eq_1
-- Registered at the default priority and then at `low`: the second line
-- replaces the entry, so `simp` and the check both see `low` and it is right.
attribute [local sys_simp] RegisterProbe.with_dup.eq_1
attribute [local sys_simp low] RegisterProbe.with_dup.eq_1
-- A pre-lemma at `low`: tried before every post-lemma, whatever the priority.
attribute [local sys_simp ↓ low] RegisterProbe.with_pre.eq_1
-- A pre-lemma at the default priority beside a post-lemma at `low`: two trees,
-- so both entries live; the check must report the default one, not only the
-- pre one, whichever line comes last.
attribute [local sys_simp ↓] RegisterProbe.with_pre_dup.eq_1
attribute [local sys_simp low] RegisterProbe.with_pre_dup.eq_1
-- Above the default priority: refused under the same heading as the default.
attribute [local sys_simp high] RegisterProbe.with_high.eq_1
-- The likelier slip: the definition tagged at `low` with `.eq_1` forgotten.
-- The priority is right, so only the `toUnfold` test can catch it.
attribute [local sys_simp low] RegisterProbe.with_bare_low
attribute [local sys_simp ← low] RegisterProbe.with_reversed.eq_1
attribute [local sys_simp low] RegisterProbe.Inner.with_nested_low.eq_1

/--
error: sys_simp register is missing the unfolding of:
  LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic.RegisterProbe.Inner.with_nested_missing
  LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic.RegisterProbe.with_erased
  LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic.RegisterProbe.with_missing
  LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic.RegisterProbe.with_readded
  LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic.RegisterProbe.with_reversed
sys_simp register has the unfolding at or above the default priority (tag `f.eq_1` at `low`) of:
  LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic.RegisterProbe.with_bare
  LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic.RegisterProbe.with_default
  LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic.RegisterProbe.with_high
  LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic.RegisterProbe.with_pre_dup
sys_simp register has the definition itself tagged (in `toUnfold`; tag `f.eq_1` at `low`, not `f`) for:
  LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic.RegisterProbe.with_bare
  LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic.RegisterProbe.with_bare_low
sys_simp register has the unfolding as a pre-lemma (`↓`; tag `f.eq_1` at `low` as a post-lemma) for:
  LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic.RegisterProbe.with_pre
  LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic.RegisterProbe.with_pre_dup
-/
#guard_msgs in
#check_sys_simp_register_over LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic.RegisterProbe "with_"

/-! …and a namespace with nothing under the prefixes is refused rather than
passed vacuously. -/
/--
error: no definition of LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic.RegisterProbe is named [m_]: the register check reads nothing
-/
#guard_msgs in
#check_sys_simp_register_over LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic.RegisterProbe "m_"
end

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic
