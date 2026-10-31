import LinuxProcessSemantics.LinuxProcessSem.State

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Monad — the non-determinism monad for syscall specs

Mirrors `theories/LinuxProcessSem/Monad.v`.

TRUST BOUNDARY: this file is part of the trusted specification.

A `Sys A` spec is a RELATION: given the syscall's `SyscallInput` and the
current `Model`, it relates them to the set of admissible `outcome`s —
`Ok x m' evs` (return `x`, new model, emitted events) or `Unmodeled` (the
model does not cover this; a POSITIVE outcome that drives the explicit
error transition, fail closed).  Reader over the input, state over the
model, writer over the events, exception with a unit payload, all on a
non-determinism base; the Rocq header spells the transformer stack out
and why the exception sits INSIDE the state (an `Unmodeled` discards the
model and the events). -/

namespace LinuxProcessSemantics.LinuxProcessSem.Monad

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State

inductive outcome (A : Type) : Type
  | Ok (x : A) (m : Model) (evs : List event)
  | Unmodeled

export outcome (Ok Unmodeled)

def Sys (A : Type) : Type := SyscallInput → Model → outcome A → Prop

def pure {A : Type} (x : A) : Sys A := fun _ m o => o = Ok x m []

/-- Sequencing: an `Unmodeled` anywhere in the chain is an `Unmodeled` of
the whole program; event lists concatenate in chronological order. -/
def bind {A B : Type} (c : Sys A) (k : A → Sys B) : Sys B :=
  fun i m o =>
    match o with
    | Unmodeled =>
        c i m Unmodeled ∨
        (∃ x m1 evs1, c i m (Ok x m1 evs1) ∧ k x i m1 Unmodeled)
    | Ok y m2 evs =>
        ∃ x m1 evs1 evs2,
          c i m (Ok x m1 evs1) ∧ k x i m1 (Ok y m2 evs2) ∧ evs = evs1 ++ evs2

/-! Rocq's `x <- c ;; k` and `c ;; k` notations.  The bound computation
`c` parses at 61 so that `x <- c1 ;; c2 ;; k` reads as `x <- c1 ;; (c2 ;; k)`
and not as `x <- (c1 ;; c2) ;; k`; the continuation `k` stays loose so a
chain nests to the right. -/
scoped notation:60 x " <- " c:61 " ;; " k => bind c (fun x => k)
scoped notation:60 c:61 " ;; " k => bind c (fun _ => k)

/-- Equality of specs is extensional. -/
def sys_equiv {A : Type} (c1 c2 : Sys A) : Prop :=
  ∀ i m o, c1 i m o ↔ c2 i m o

scoped infix:50 " ≡ " => sys_equiv

theorem sys_equiv_refl {A : Type} (c : Sys A) : c ≡ c := fun _ _ _ => Iff.rfl
theorem sys_equiv_sym {A : Type} (c1 c2 : Sys A) : c1 ≡ c2 → c2 ≡ c1 :=
  fun h i m o => (h i m o).symm
theorem sys_equiv_trans {A : Type} (c1 c2 c3 : Sys A) : c1 ≡ c2 → c2 ≡ c3 → c1 ≡ c3 :=
  fun h1 h2 i m o => (h1 i m o).trans (h2 i m o)

/-! ## Core effects -/

/-- THE MODEL DOES NOT COVER THIS CALL (fail closed).  Not a kernel
failure: those are ordinary `Ok`s carrying a negative errno. -/
def unmodeled {A : Type} : Sys A := fun _ _ o => o = Unmodeled

/-- Environment choice: any `x` satisfying `P` may be returned. -/
def choose {A : Type} (P : A → Prop) : Sys A :=
  fun _ m o => ∃ x, P x ∧ o = Ok x m []

/-- Union of two admissible-outcome sets. -/
def alt {A : Type} (c1 c2 : Sys A) : Sys A :=
  fun i m o => c1 i m o ∨ c2 i m o

/-- Emit observable events. -/
def emit (evs : List event) : Sys Unit := fun _ m o => o = Ok () m evs

/-! ## Readers (the syscall input) and state accessors (the model) -/

def input : Sys SyscallInput := fun i m o => o = Ok i m []
def sysno : Sys word := fun i m o => o = Ok i.in_sysno m []
def arg (k : Nat) : Sys word := fun i m o => o = Ok (in_arg i k) m []

def get_model : Sys Model := fun _ m o => o = Ok m m []
def modify (f : Model → Model) : Sys Unit := fun _ m o => o = Ok () (f m) []

def get_fds : Sys (List (word × FdEntry)) := fun _ m o => o = Ok (m_fds m) m []
def get_vmmaps : Sys VmMaps := fun _ m o => o = Ok (m_vmmaps m) m []

def set_fds (fds : List (word × FdEntry)) : Sys Unit := modify (with_fds fds)
def set_pipes (ps : List (word × PipeBuf)) : Sys Unit := modify (with_pipes ps)
def set_vmmaps (h : VmMaps) : Sys Unit := modify (with_vmmaps h)
def forget_vm_range (lo hi : Int) : Sys Unit := modify (vm_forget_range lo hi)
def set_stdin (s : InputStream) : Sys Unit := modify (with_stdin s)
/-- Advance the random device's declared stream, `State.m_urandom`.  Its one
caller once ported is the delivering branch of Rocq's
`Fs.ReadWrite.read_urandom` (Sys/Fs/ReadWrite.v at a71fd38a), shared by the
`read` and `pread64` arms on `State.FdUrandom`, which hands it the stream
past the bytes it has just delivered.  The stream is the model's and not the
descriptor's because the device keeps no position: `urandom_read_iter`
(drivers/char/random.c, Linux v6.18.46) reads nothing off its kiocb and
hands the iterator straight to the generator, so every open of the device
draws from the one sequence and a non-negative offset given to `pread64` is
ignored — a negative one is refused with -EINVAL by `ksys_pread64`
(fs/read_write.c, Linux v6.18.46) before the device is reached.
What a read consumes from the stream is pinned in `Checks/Cases/Monad.lean`,
ticket A16.  Rocq: `Monad.set_urandom`. -/
def set_urandom (s : InputStream) : Sys Unit := modify (with_urandom s)
def set_fs (fs : Fs.Fs) : Sys Unit := modify (with_fs fs)
def set_halted (code : word) : Sys Unit := modify (with_halted code)
def set_tid (tid : word) : Sys Unit := modify (with_tid tid)
def set_creds (c : Creds) : Sys Unit := modify (with_creds c)
def set_rlimit_core (bs : List byte) : Sys Unit := modify (with_rlimit_core bs)
def set_setsid_succeeded : Sys Unit := modify with_setsid_succeeded
def set_sigmask (sm : word) : Sys Unit := modify (with_sigmask sm)
def set_clock (t : word) : Sys Unit := modify (with_clock t)
def add_vm_lazy (a n : word) : Sys Unit := modify (vm_add_lazy a n)

/-! ## Introduction lemmas -/

theorem bind_ok {A B : Type} (c : Sys A) (k : A → Sys B) (i : SyscallInput) (m : Model)
    (x : A) (m1 : Model) (evs1 : List event) (y : B) (m2 : Model) (evs2 : List event) :
    c i m (Ok x m1 evs1) → k x i m1 (Ok y m2 evs2) → bind c k i m (Ok y m2 (evs1 ++ evs2)) :=
  fun h1 h2 => ⟨x, m1, evs1, evs2, h1, h2, rfl⟩

theorem bind_unmodeled1 {A B : Type} (c : Sys A) (k : A → Sys B) (i : SyscallInput) (m : Model) :
    c i m Unmodeled → bind c k i m Unmodeled := fun h => Or.inl h

theorem bind_unmodeled2 {A B : Type} (c : Sys A) (k : A → Sys B) (i : SyscallInput) (m : Model)
    (x : A) (m1 : Model) (evs1 : List event) :
    c i m (Ok x m1 evs1) → k x i m1 Unmodeled → bind c k i m Unmodeled :=
  fun h1 h2 => Or.inr ⟨x, m1, evs1, h1, h2⟩

theorem pure_ok {A : Type} (x : A) (i : SyscallInput) (m : Model) : pure x i m (Ok x m []) := rfl
theorem choose_ok {A : Type} (P : A → Prop) (x : A) (i : SyscallInput) (m : Model) :
    P x → choose P i m (Ok x m []) := fun h => ⟨x, h, rfl⟩
theorem unmodeled_intro {A : Type} (i : SyscallInput) (m : Model) : (unmodeled : Sys A) i m Unmodeled := rfl
theorem alt_l {A : Type} (c1 c2 : Sys A) (i : SyscallInput) (m : Model) (o : outcome A) :
    c1 i m o → alt c1 c2 i m o := Or.inl
theorem alt_r {A : Type} (c1 c2 : Sys A) (i : SyscallInput) (m : Model) (o : outcome A) :
    c2 i m o → alt c1 c2 i m o := Or.inr
theorem emit_ok (evs : List event) (i : SyscallInput) (m : Model) : emit evs i m (Ok () m evs) := rfl
theorem input_ok (i : SyscallInput) (m : Model) : input i m (Ok i m []) := rfl
theorem sysno_ok (i : SyscallInput) (m : Model) : sysno i m (Ok i.in_sysno m []) := rfl
theorem arg_ok (k : Nat) (i : SyscallInput) (m : Model) : arg k i m (Ok (in_arg i k) m []) := rfl
theorem get_model_ok (i : SyscallInput) (m : Model) : get_model i m (Ok m m []) := rfl
theorem get_fds_ok (i : SyscallInput) (m : Model) : get_fds i m (Ok (m_fds m) m []) := rfl
theorem get_vmmaps_ok (i : SyscallInput) (m : Model) : get_vmmaps i m (Ok (m_vmmaps m) m []) := rfl
theorem modify_ok (f : Model → Model) (i : SyscallInput) (m : Model) : modify f i m (Ok () (f m) []) := rfl

/-! ## Monad laws, up to `sys_equiv` -/

theorem bind_pure_l {A B : Type} (a : A) (k : A → Sys B) : bind (pure a) k ≡ k a := by
  intro i m o
  cases o with
  | Ok y m2 evs =>
    constructor
    · rintro ⟨x, m1, evs1, evs2, hp, hk, hevs⟩
      simp only [pure, outcome.Ok.injEq] at hp
      obtain ⟨rfl, rfl, rfl⟩ := hp
      subst hevs
      simpa using hk
    · intro h
      exact ⟨a, m, [], evs, rfl, h, by simp⟩
  | Unmodeled =>
    constructor
    · rintro (h | ⟨x, m1, evs1, hp, hk⟩)
      · exact absurd h (by simp [pure])
      · simp only [pure, outcome.Ok.injEq] at hp
        obtain ⟨rfl, rfl, rfl⟩ := hp
        exact hk
    · intro h
      exact Or.inr ⟨a, m, [], rfl, h⟩

theorem bind_pure_r {A : Type} (c : Sys A) : bind c pure ≡ c := by
  intro i m o
  cases o with
  | Ok y m2 evs =>
    constructor
    · rintro ⟨x, m1, evs1, evs2, hc, hk, hevs⟩
      simp only [pure, outcome.Ok.injEq] at hk
      obtain ⟨rfl, rfl, rfl⟩ := hk
      subst hevs
      simpa using hc
    · intro h
      exact ⟨y, m2, evs, [], h, rfl, by simp⟩
  | Unmodeled =>
    constructor
    · rintro (h | ⟨x, m1, evs1, _, hk⟩)
      · exact h
      · exact absurd hk (by simp [pure])
    · intro h
      exact Or.inl h

theorem bind_assoc {A B C : Type} (c : Sys A) (k : A → Sys B) (h : B → Sys C) :
    bind (bind c k) h ≡ bind c (fun x => bind (k x) h) := by
  intro i m o
  cases o with
  | Ok z m3 evs =>
    constructor
    · rintro ⟨y, m2, evsA, evsB, ⟨x, m1, evs1, evs2, hc, hk, rfl⟩, hh, rfl⟩
      exact ⟨x, m1, evs1, evs2 ++ evsB, hc, ⟨y, m2, evs2, evsB, hk, hh, rfl⟩,
        by simp [List.append_assoc]⟩
    · rintro ⟨x, m1, evs1, evsBC, hc, ⟨y, m2, evs2, evsB, hk, hh, rfl⟩, rfl⟩
      exact ⟨y, m2, evs1 ++ evs2, evsB, ⟨x, m1, evs1, evs2, hc, hk, rfl⟩, hh,
        by simp [List.append_assoc]⟩
  | Unmodeled =>
    constructor
    · rintro ((hc | ⟨x, m1, evs1, hc, hk⟩) | ⟨y, m2, evsA, ⟨x, m1, evs1, evs2, hc, hk, _⟩, hh⟩)
      · exact Or.inl hc
      · exact Or.inr ⟨x, m1, evs1, hc, Or.inl hk⟩
      · exact Or.inr ⟨x, m1, evs1, hc, Or.inr ⟨y, m2, evs2, hk, hh⟩⟩
    · rintro (hc | ⟨x, m1, evs1, hc, (hk | ⟨y, m2, evs2, hk, hh⟩)⟩)
      · exact Or.inl (Or.inl hc)
      · exact Or.inl (Or.inr ⟨x, m1, evs1, hc, hk⟩)
      · exact Or.inr ⟨y, m2, evs1 ++ evs2, ⟨x, m1, evs1, evs2, hc, hk, rfl⟩, hh⟩


/-! ## Reading a spec off its primitives

Each primitive's `bind` has a first-order reading: what `bind c k` admits at
`i m o` in terms of what `k` admits.  These are what let a concrete call of
a spec be turned into a plain statement about `o` — the form every check in
`Checks/Cases/` is written in — and they are stated over EVERY outcome,
`Unmodeled` included, so an `Unmodeled` produced past a `choose` is read
exactly as `bind` defines it.  Lean-only: the Rocq tree reaches the same
place through the executable checker's soundness/completeness pair, and
through the inversions of `Checks/Sys/Prelude.v` (`input_bind_ok_inv`,
`get_model_bind_ok_inv`, `bind_input_model_inv`, …), each of which takes
`bind`'s existential apart by hand for a fixed primitive — most at one
outcome, `bind_input_model_inv` for the two-reader prologue at every
outcome.  Here one lemma does that for every primitive that admits one
outcome, `bind_det_iff`; its instances are the ticket D4 section below,
after the last setter they read. -/

/-- A DETERMINISTIC first component — one admitting exactly one outcome at
every `i m`: the value `x i m`, the model `f i m`, no events — is read under
`bind` by handing that value and that model to the continuation.  Every
reader (`input`, `sysno`, `arg`, `get_model`, `get_fds`, `get_vmmaps`) and
every setter (`modify`, and each `set_*` over it) has this shape, so each
instance is this lemma at its `x` and `f` with `Iff.rfl` for `hc`.  What
is NOT of this shape is `emit`, whose events are not `[]`:
`bind_det_cases_iff` below is the same reading with events, and `emit` is
read through that one.  Rocq's `Checks/Sys/Prelude.v` states the two
halves of the `→` direction separately per primitive
(`input_bind_ok_inv` and `input_bind_unmodeled_inv`, `get_model_bind_ok_inv`
and `get_model_bind_unmodeled_inv`); each is an instance's `.1` at that
outcome, and `Checks/Cases/Monad.lean` pins them as such. -/
theorem bind_det_iff {A B : Type} (c : Sys A) (x : SyscallInput → Model → A)
    (f : SyscallInput → Model → Model)
    (hc : ∀ i m o, c i m o ↔ o = Ok (x i m) (f i m) []) (k : A → Sys B)
    (i : SyscallInput) (m : Model) (o : outcome B) :
    bind c k i m o ↔ k (x i m) i (f i m) o := by
  cases o with
  | Ok y m2 evs =>
    constructor
    · rintro ⟨v, m1, evs1, evs2, hv, hk, hevs⟩
      rw [hc] at hv
      simp only [outcome.Ok.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      subst hevs
      simpa only [List.nil_append] using hk
    · intro h
      exact ⟨x i m, f i m, [], evs, (hc i m _).2 rfl, h, (List.nil_append evs).symm⟩
  | Unmodeled =>
    constructor
    · rintro (h | ⟨v, m1, evs1, hv, hk⟩)
      · rw [hc] at h
        cases h
      · rw [hc] at hv
        simp only [outcome.Ok.injEq] at hv
        obtain ⟨rfl, rfl, rfl⟩ := hv
        exact hk
    · intro h
      exact Or.inr ⟨x i m, f i m, [], (hc i m _).2 rfl, h⟩

/-- The same reading for a first component that also emits `e i m`: an
`Ok` of the whole is an `Ok` of the continuation with those events
prepended, and an `Unmodeled` is the continuation's.  First-order in `o`
as a disjunction over its constructor, the shape a completeness proof
destructs; `bind_det_iff` is this lemma at `e = fun _ _ => []` with the
disjunction folded back into `o`. -/
theorem bind_det_cases_iff {A B : Type} (c : Sys A) (x : SyscallInput → Model → A)
    (f : SyscallInput → Model → Model) (e : SyscallInput → Model → List event)
    (hc : ∀ i m o, c i m o ↔ o = Ok (x i m) (f i m) (e i m)) (k : A → Sys B)
    (i : SyscallInput) (m : Model) (o : outcome B) :
    bind c k i m o ↔
      (∃ y m2 evs2, k (x i m) i (f i m) (Ok y m2 evs2) ∧ o = Ok y m2 (e i m ++ evs2)) ∨
      (k (x i m) i (f i m) Unmodeled ∧ o = Unmodeled) := by
  cases o with
  | Ok y m2 evs =>
    constructor
    · rintro ⟨v, m1, evs1, evs2, hv, hk, hevs⟩
      rw [hc] at hv
      simp only [outcome.Ok.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      exact Or.inl ⟨y, m2, evs2, hk, by rw [hevs]⟩
    · rintro (⟨y', m2', evs2, hk, ho⟩ | ⟨-, ho⟩)
      · simp only [outcome.Ok.injEq] at ho
        obtain ⟨rfl, rfl, rfl⟩ := ho
        exact ⟨x i m, f i m, e i m, evs2, (hc i m _).2 rfl, hk, rfl⟩
      · cases ho
  | Unmodeled =>
    constructor
    · rintro (h | ⟨v, m1, evs1, hv, hk⟩)
      · rw [hc] at h
        cases h
      · rw [hc] at hv
        simp only [outcome.Ok.injEq] at hv
        obtain ⟨rfl, rfl, rfl⟩ := hv
        exact Or.inr ⟨hk, rfl⟩
    · rintro (⟨y, m2, evs2, -, ho⟩ | ⟨hk, -⟩)
      · cases ho
      · exact Or.inr ⟨x i m, f i m, e i m, (hc i m _).2 rfl, hk⟩

theorem bind_get_model_iff {B : Type} (k : Model → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind get_model k i m o ↔ k m i m o :=
  bind_det_iff get_model (fun _ m => m) (fun _ m => m) (fun _ _ _ => Iff.rfl) k i m o

theorem bind_choose_iff {A B : Type} (P : A → Prop) (k : A → Sys B) (i : SyscallInput)
    (m : Model) (o : outcome B) : bind (choose P) k i m o ↔ ∃ x, P x ∧ k x i m o := by
  cases o with
  | Ok y m2 evs =>
    constructor
    · rintro ⟨x, m1, evs1, evs2, ⟨x', hP, hx⟩, hk, hevs⟩
      simp only [outcome.Ok.injEq] at hx
      obtain ⟨rfl, rfl, rfl⟩ := hx
      subst hevs
      exact ⟨_, hP, by simpa using hk⟩
    · rintro ⟨x, hP, hk⟩
      exact ⟨x, m, [], evs, ⟨x, hP, rfl⟩, hk, by simp⟩
  | Unmodeled =>
    constructor
    · rintro (⟨x, _, h⟩ | ⟨x, m1, evs1, ⟨x', hP, hx⟩, hk⟩)
      · exact absurd h (by simp)
      · simp only [outcome.Ok.injEq] at hx
        obtain ⟨rfl, rfl, rfl⟩ := hx
        exact ⟨_, hP, hk⟩
    · rintro ⟨x, hP, hk⟩
      exact Or.inr ⟨x, m, [], ⟨x, hP, rfl⟩, hk⟩

theorem bind_modify_iff {B : Type} (f : Model → Model) (k : Unit → Sys B) (i : SyscallInput)
    (m : Model) (o : outcome B) : bind (modify f) k i m o ↔ k () i (f m) o :=
  bind_det_iff (modify f) (fun _ _ => ()) (fun _ m => f m) (fun _ _ _ => Iff.rfl) k i m o

theorem bind_pure_iff {A B : Type} (x : A) (k : A → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind (pure x) k i m o ↔ k x i m o :=
  bind_pure_l x k i m o

theorem pure_iff {A : Type} (x : A) (i : SyscallInput) (m : Model) (o : outcome A) :
    pure x i m o ↔ o = Ok x m [] := Iff.rfl

theorem unmodeled_iff {A : Type} (i : SyscallInput) (m : Model) (o : outcome A) :
    (unmodeled : Sys A) i m o ↔ o = Unmodeled := Iff.rfl

theorem alt_iff {A : Type} (c1 c2 : Sys A) (i : SyscallInput) (m : Model) (o : outcome A) :
    alt c1 c2 i m o ↔ c1 i m o ∨ c2 i m o := Iff.rfl

/-! ## Ticket A11: the UTS pin's setter

Appended as one delimited section so concurrent additions to this file
meet only at its end; in Rocq `set_utsname` sits between
`set_rlimit_core` and `set_setsid_succeeded`. -/

/-- Record the UTS name the environment revealed.  Called on exactly one
branch of Rocq's `Kernel.Sys.uname_spec` (Sys/Kernel/Sys.v at f44244ad),
the only caller once ported — the branch where `State.m_utsname` was
`none` — so the pin is written once; see `State.with_utsname`.  Rocq:
`Monad.set_utsname`. -/
def set_utsname (bs : List byte) : Sys Unit := modify (with_utsname bs)

/-! ## Ticket A12: the setters of the signal and terminal state

Appended for the A11 section's reason; in Rocq `set_statpin` sits after
`set_setsid_succeeded` and the other three after `set_sigmask`. -/

/-- Record the `struct stat` a file was first seen with.  Every caller —
in Rocq the `fstat` arms of Sys/Fs/Stat.v, here the `fstat` arms of
`Sys/Fs/Stat.lean` — reaches it only on the branch where
`State.statpin_lookup` answered `none`, so a path's pin is written once
and every later `fstat` of the path is held to it; see
`State.procst_statpins`.  A caller pinning on another branch would
overwrite an existing pin, which `pinned_repeat_admitted` and
`pinned_inode_defector_rejected` in `Checks/Cases/Fs/Stat.lean` catch;
that the pin lands at all is `set_statpin_pins_the_path` in
`Checks/Cases/Monad.lean`.  Rocq: `Monad.set_statpin`. -/
def set_statpin (p : Fs.path) (bs : List byte) : Sys Unit := modify (with_statpin p bs)

/-- Rocq: `Monad.set_sigaltstack_installed`; see
`State.with_sigaltstack_installed` for the one branch that calls it. -/
def set_sigaltstack_installed : Sys Unit := modify with_sigaltstack_installed

/-- Record a BLOCKED SIGABRT as pending, and end the process by a fatal
signal.  Rocq's `Kernel.Signal` (Sys/Kernel/Signal.v at f44244ad) holds
the only callers of either, none ported yet; see
`State.with_sigabrt_pending` and `State.with_killed` for what each
writes and why.  Rocq: `Monad.set_sigabrt_pending`, `Monad.set_killed`. -/
def set_sigabrt_pending : Sys Unit := modify with_sigabrt_pending
def set_killed (sig : word) : Sys Unit := modify (with_killed sig)

/-! ## Ticket D4: the deterministic primitives, read under `bind`

`bind_det_iff` at each reader and each setter, `bind_det_cases_iff` at
`emit`.  Appended as one delimited section after every setter it reads, so
that concurrent additions to this file meet only at its end; a setter added
after this section owes its instance here, which
`Checks/Cases/Tactic.lean`'s `#check_bind_readings` enforces, and its
`eq_1` line in that file's register, which `#check_sys_simp_register`
enforces.  The readers' instances are stated here, and not in the tactic
file that registers them, so that a proof importing this file alone — a
checker's completeness proof, or `Checks/Sys/Prelude.lean`'s twins of the
Rocq inversions — reads a primitive without importing the tactic file and
every spec behind it.  `sys_norm` reads a setter through its `eq_1` and
`bind_modify_iff` (its children are simplified before the `bind`, so a
reading at the setter's own name would never be tried there); the setter
instances serve proofs written against a setter by name, as
`Checks/Cases/Monad.lean` reads `set_vmmaps`, not the register. -/

theorem bind_input_iff {B : Type} (k : SyscallInput → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind input k i m o ↔ k i i m o :=
  bind_det_iff input (fun i _ => i) (fun _ m => m) (fun _ _ _ => Iff.rfl) k i m o

theorem bind_sysno_iff {B : Type} (k : word → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind sysno k i m o ↔ k i.in_sysno i m o :=
  bind_det_iff sysno (fun i _ => i.in_sysno) (fun _ m => m) (fun _ _ _ => Iff.rfl) k i m o

theorem bind_arg_iff {B : Type} (n : Nat) (k : word → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind (arg n) k i m o ↔ k (in_arg i n) i m o :=
  bind_det_iff (arg n) (fun i _ => in_arg i n) (fun _ m => m) (fun _ _ _ => Iff.rfl) k i m o

theorem bind_get_fds_iff {B : Type} (k : List (word × FdEntry) → Sys B) (i : SyscallInput)
    (m : Model) (o : outcome B) : bind get_fds k i m o ↔ k (m_fds m) i m o :=
  bind_det_iff get_fds (fun _ m => m_fds m) (fun _ m => m) (fun _ _ _ => Iff.rfl) k i m o

theorem bind_get_vmmaps_iff {B : Type} (k : VmMaps → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind get_vmmaps k i m o ↔ k (m_vmmaps m) i m o :=
  bind_det_iff get_vmmaps (fun _ m => m_vmmaps m) (fun _ m => m) (fun _ _ _ => Iff.rfl) k i m o

/-- `emit` is the one primitive with events, so it is read by cases. -/
theorem bind_emit_cases_iff {B : Type} (evs : List event) (k : Unit → Sys B) (i : SyscallInput)
    (m : Model) (o : outcome B) :
    bind (emit evs) k i m o ↔
      (∃ y m2 evs2, k () i m (Ok y m2 evs2) ∧ o = Ok y m2 (evs ++ evs2)) ∨
      (k () i m Unmodeled ∧ o = Unmodeled) :=
  bind_det_cases_iff (emit evs) (fun _ _ => ()) (fun _ m => m) (fun _ _ => evs)
    (fun _ _ _ => Iff.rfl) k i m o

/-! The setters, in the order the definitions above give them; the A12 four
last, as their section sits last above. -/

theorem bind_set_fds_iff {B : Type} (fds : List (word × FdEntry)) (k : Unit → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind (set_fds fds) k i m o ↔ k () i (with_fds fds m) o :=
  bind_det_iff (set_fds fds) (fun _ _ => ()) (fun _ m => with_fds fds m) (fun _ _ _ => Iff.rfl) k i m o

theorem bind_set_pipes_iff {B : Type} (ps : List (word × PipeBuf)) (k : Unit → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind (set_pipes ps) k i m o ↔ k () i (with_pipes ps m) o :=
  bind_det_iff (set_pipes ps) (fun _ _ => ()) (fun _ m => with_pipes ps m) (fun _ _ _ => Iff.rfl) k i m o

theorem bind_set_vmmaps_iff {B : Type} (h : VmMaps) (k : Unit → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind (set_vmmaps h) k i m o ↔ k () i (with_vmmaps h m) o :=
  bind_det_iff (set_vmmaps h) (fun _ _ => ()) (fun _ m => with_vmmaps h m) (fun _ _ _ => Iff.rfl) k i m o

theorem bind_forget_vm_range_iff {B : Type} (lo hi : Int) (k : Unit → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind (forget_vm_range lo hi) k i m o ↔ k () i (vm_forget_range lo hi m) o :=
  bind_det_iff (forget_vm_range lo hi) (fun _ _ => ()) (fun _ m => vm_forget_range lo hi m) (fun _ _ _ => Iff.rfl) k i m o

theorem bind_set_stdin_iff {B : Type} (s : InputStream) (k : Unit → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind (set_stdin s) k i m o ↔ k () i (with_stdin s m) o :=
  bind_det_iff (set_stdin s) (fun _ _ => ()) (fun _ m => with_stdin s m) (fun _ _ _ => Iff.rfl) k i m o

theorem bind_set_urandom_iff {B : Type} (s : InputStream) (k : Unit → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind (set_urandom s) k i m o ↔ k () i (with_urandom s m) o :=
  bind_det_iff (set_urandom s) (fun _ _ => ()) (fun _ m => with_urandom s m) (fun _ _ _ => Iff.rfl) k i m o

theorem bind_set_fs_iff {B : Type} (fs : Fs.Fs) (k : Unit → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind (set_fs fs) k i m o ↔ k () i (with_fs fs m) o :=
  bind_det_iff (set_fs fs) (fun _ _ => ()) (fun _ m => with_fs fs m) (fun _ _ _ => Iff.rfl) k i m o

theorem bind_set_halted_iff {B : Type} (code : word) (k : Unit → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind (set_halted code) k i m o ↔ k () i (with_halted code m) o :=
  bind_det_iff (set_halted code) (fun _ _ => ()) (fun _ m => with_halted code m) (fun _ _ _ => Iff.rfl) k i m o

theorem bind_set_tid_iff {B : Type} (tid : word) (k : Unit → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind (set_tid tid) k i m o ↔ k () i (with_tid tid m) o :=
  bind_det_iff (set_tid tid) (fun _ _ => ()) (fun _ m => with_tid tid m) (fun _ _ _ => Iff.rfl) k i m o

theorem bind_set_creds_iff {B : Type} (c : Creds) (k : Unit → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind (set_creds c) k i m o ↔ k () i (with_creds c m) o :=
  bind_det_iff (set_creds c) (fun _ _ => ()) (fun _ m => with_creds c m) (fun _ _ _ => Iff.rfl) k i m o

theorem bind_set_rlimit_core_iff {B : Type} (bs : List byte) (k : Unit → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind (set_rlimit_core bs) k i m o ↔ k () i (with_rlimit_core bs m) o :=
  bind_det_iff (set_rlimit_core bs) (fun _ _ => ()) (fun _ m => with_rlimit_core bs m) (fun _ _ _ => Iff.rfl) k i m o

theorem bind_set_setsid_succeeded_iff {B : Type} (k : Unit → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind (set_setsid_succeeded) k i m o ↔ k () i (with_setsid_succeeded m) o :=
  bind_det_iff (set_setsid_succeeded) (fun _ _ => ()) (fun _ m => with_setsid_succeeded m) (fun _ _ _ => Iff.rfl) k i m o

theorem bind_set_sigmask_iff {B : Type} (sm : word) (k : Unit → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind (set_sigmask sm) k i m o ↔ k () i (with_sigmask sm m) o :=
  bind_det_iff (set_sigmask sm) (fun _ _ => ()) (fun _ m => with_sigmask sm m) (fun _ _ _ => Iff.rfl) k i m o

theorem bind_set_clock_iff {B : Type} (t : word) (k : Unit → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind (set_clock t) k i m o ↔ k () i (with_clock t m) o :=
  bind_det_iff (set_clock t) (fun _ _ => ()) (fun _ m => with_clock t m) (fun _ _ _ => Iff.rfl) k i m o

theorem bind_add_vm_lazy_iff {B : Type} (a n : word) (k : Unit → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind (add_vm_lazy a n) k i m o ↔ k () i (vm_add_lazy a n m) o :=
  bind_det_iff (add_vm_lazy a n) (fun _ _ => ()) (fun _ m => vm_add_lazy a n m) (fun _ _ _ => Iff.rfl) k i m o

theorem bind_set_utsname_iff {B : Type} (bs : List byte) (k : Unit → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind (set_utsname bs) k i m o ↔ k () i (with_utsname bs m) o :=
  bind_det_iff (set_utsname bs) (fun _ _ => ()) (fun _ m => with_utsname bs m) (fun _ _ _ => Iff.rfl) k i m o

theorem bind_set_statpin_iff {B : Type} (p : Fs.path) (bs : List byte) (k : Unit → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind (set_statpin p bs) k i m o ↔ k () i (with_statpin p bs m) o :=
  bind_det_iff (set_statpin p bs) (fun _ _ => ()) (fun _ m => with_statpin p bs m) (fun _ _ _ => Iff.rfl) k i m o

theorem bind_set_sigaltstack_installed_iff {B : Type} (k : Unit → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind (set_sigaltstack_installed) k i m o ↔ k () i (with_sigaltstack_installed m) o :=
  bind_det_iff (set_sigaltstack_installed) (fun _ _ => ()) (fun _ m => with_sigaltstack_installed m) (fun _ _ _ => Iff.rfl) k i m o

theorem bind_set_sigabrt_pending_iff {B : Type} (k : Unit → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind (set_sigabrt_pending) k i m o ↔ k () i (with_sigabrt_pending m) o :=
  bind_det_iff (set_sigabrt_pending) (fun _ _ => ()) (fun _ m => with_sigabrt_pending m) (fun _ _ _ => Iff.rfl) k i m o

theorem bind_set_killed_iff {B : Type} (sig : word) (k : Unit → Sys B) (i : SyscallInput) (m : Model)
    (o : outcome B) : bind (set_killed sig) k i m o ↔ k () i (with_killed sig m) o :=
  bind_det_iff (set_killed sig) (fun _ _ => ()) (fun _ m => with_killed sig m) (fun _ _ _ => Iff.rfl) k i m o

end LinuxProcessSemantics.LinuxProcessSem.Monad
