import LinuxProcessSemantics.Common.ExitSim
import LinuxProcessSemantics.Common.CatSim
import LinuxProcessSemantics.Common.CatExec

/-! # Common.WallSim — the "write-all" retry node over a channel

Ported from `theories/Common/WallSim.v` at
2cde689f94c086b868999970834b76a25616b94a: the part of it `cat1024_ns`'s
`Proof.v` reaches (`Print All Dependencies` of its
`strong_universal`, ticket E-proof-library), with the Rocq statements.
That is `fd32_1`, the put-loop arithmetic (`u_len_word`,
`u_len_word_firstn`, `v_add_len_firstn_Z`, `word_add_nat_Z`,
`v_sub_len_firstn`), the mutual write-all node `to_wall`/`to_wall_tail`
with its induction schemes (`to_wall_min`, `to_wall_tail_min`,
`to_wall_mutind`, `to_wall_tail_ind`), `to_wall_tail_nil_msteps`, the
write-pending one-step inversion (`sstep_to_wall_inv`,
`to_wall_no_error_sstep`), star admissibility
(`to_wall_star_admits_mut`, `to_wall_tail_star_admits`) and the raw-ecall
wrapper `twl_write_rec`.  Ticket E-proof-library-2c added
`msteps_to_wall_tail`, after the induction schemes, where Rocq states it.

A channel write delivers a nondeterministic NONEMPTY prefix of the offered
buffer (CatSim's delivered-length family), so real binaries wrap every
program-level write in a put-style retry loop; `to_wall ms rest k` is that
loop's shape, whose trace contribution is exactly `map (WriteEv ch) rest`
whatever the chunking, ending in a state satisfying the continuation
predicate `k`.

Left unported by ticket E-proof-library: `fd32_2`, `len_word_firstn_nat`,
`v_add_len_firstn`,
Rocq's generated non-mutual `to_wall_ind`, its generated SProp eliminators
`to_wall_sind` and `to_wall_tail_sind` (Lean has no SProp),
`msteps_to_wall_tail`, `to_wall_star_admits`, the star-exhaustiveness pair
`to_wall_star_only_mut`/`to_wall_star_only`, and everything after
`twl_write_rec`: `to_wallexit` and the 15 lemmas that follow it
(`to_wall_k_ex_mut`, `to_wall_tail_k_ex`, `to_wallexit_bufs_nonempty`,
`twe_step`, `msteps_to_wallexit`, `to_wall_exec_mut`,
`to_wexit_nil_exec_aux`, `to_wexit_nil_exec`, `to_wallexit_exec`,
`to_wallexit_star_admits`, `to_wallexit_no_other_exit`,
`to_wallexit_trace_unique`, `to_wallexit_not_silent`,
`to_wallexit_star_only`, `to_wallexit_no_error`), the abbreviation
`wexit1`, `wevents_ch_fd1`, and the run-level `wall_omni_run`,
`wall_obs_iff`, `wall_no_error_run`, `wall_omni_strong_equiv` and
`wall_strong_equiv`.  cat1024_ns reaches none of them.  Sections appended
at the end of this file since, each headed by the ticket that added it,
port some of them.

Representation divergences, spelled Lean's way:
- Rocq `firstn`/`skipn` are `List.take`/`List.drop`, and `(_ <= _)%nat` is
  `Nat`'s `≤`; Rocq's `bv_add p q` on words is `p + q`.
- Rocq Section variables become explicit leading arguments: the node takes
  `segs fd` as parameters, and the inversion and admissibility lemmas take
  `segs fd ch` and the hypothesis `Hfd32 : fd32 fd = fd` ahead of their own
  binders, the order Rocq's `Section WithSegsCh` closes them in.

Structural divergences:
- Rocq's `Scheme … Minimality` (`to_wall_min`, `to_wall_tail_min`) and
  `Combined Scheme` (`to_wall_mutind`) are Rocq commands generating
  induction principles; Lean has no such command, so the three are stated
  here as theorems with the generated statements and proved from Lean's
  mutual recursors `to_wall.rec`/`to_wall_tail.rec` at proof-irrelevant
  motives.
- Rocq auto-generates `to_wall_tail_ind`, the NON-mutual principle (no
  induction hypothesis through `twt_more`'s `to_wall` premise); Lean
  generates no such principle: `to_wall_tail.rec` is mutual with
  `to_wall.rec`, and every motive it takes ranges over the derivation.  So
  it too is stated as a theorem with the Rocq statement, from
  `to_wall_tail_min` at a trivial `to_wall` motive.

Universes.  Rocq's `u_len_word` is not universe polymorphic, and binds
`A : Type@{u_len_word.u0}`, a global universe.  Here it binds
`{A : Type}`, universe 0, because the `BvBase.len_word` its statement
applies binds `{A : Type}`, as does the `len_word_unsigned` its proof
applies, and a `Type _` binder is set to 0 by the statement with no error.
Rocq's `A` may also be a proposition, by cumulativity, or a type Lean places
above `Type`, such as `Type` itself, which a use admits by bounding the
lemma's global universe from below; Lean's may be neither.  `Prop`,
`Nat → Prop` and `List Prop` are not among these: Rocq places them above
`Set`, Lean places them in `Type`, and both take them.  Widening the
binder needs a `lean: base:` change that widens `BvBase.len_word` first,
and the proof as written needs `len_word_unsigned` widened too; the
instances where Rocq's `A` is a proposition have no Lean form either
way. -/

namespace LinuxProcessSemantics.Common.WallSim

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.CatSim

/-- The stdout fd literal is 32-bit-stable (the `fd32` truncation
`check_syscall` applies leaves it unchanged) — the `Hfd32` instantiation
every consumer needs. -/
theorem fd32_1 : fd32 (Z_to_bv 64 1) = Z_to_bv 64 1 :=
  fd32_id _ (by decide)

/-! ## Put-loop arithmetic

The delivered length as a word, the pointer bump, and the count decrement,
in the forms the per-binary retry-loop proofs meet (a0 =
`len_word (firstn n bs)` after the write). -/

/-- `bv_unsigned` of a modeled block length (all lengths here are far
below 2^64). -/
theorem u_len_word {A : Type} (l : List A) (H : (l.length : Int) < 2 ^ 64) :
    bv_unsigned (len_word l) = (l.length : Int) :=
  len_word_unsigned l (by unfold two_pow_64; exact H)

-- These instances pin the header's accepted universe-0 types.
example := @u_len_word Prop
example := @u_len_word (Nat → Prop)
example := @u_len_word (List Prop)

-- The `Type` refusal records the header's claim. Widening just this lemma's
-- binder to `Type _` elaborates at `Type` again: the statement's
-- `BvBase.len_word` is universe 0, so a real widening changes that constant too.
/-- error: Application type mismatch: The argument
  Type
has type
  Type 1
of sort `Type 2` but is expected to have type
  Type
of sort `Type 1` in the application
  @u_len_word Type -/
#guard_msgs in
set_option pp.mvars false in
example := @u_len_word Type

/-- error: Application type mismatch: The argument
  True
has type
  Prop
of sort `Type` but is expected to have type
  Type
of sort `Type 1` in the application
  @u_len_word True -/
#guard_msgs in
set_option pp.mvars false in
example := @u_len_word True

theorem u_len_word_firstn (n : Nat) (bs : List byte) (Hn : n ≤ bs.length)
    (Hlen : (bs.length : Int) < 2 ^ 64) :
    bv_unsigned (len_word (bs.take n)) = (n : Int) := by
  rw [len_word_unsigned (bs.take n) (by unfold two_pow_64; rw [List.length_take]; omega),
    List.length_take]
  omega

/-- `v_add` variant landing on the canonical `Z_to_bv 64 (...)` form. -/
theorem v_add_len_firstn_Z (p : word) (n : Nat) (bs : List byte) (Hn : n ≤ bs.length)
    (Hlen : (bs.length : Int) < 2 ^ 64) :
    v_add p (len_word (bs.take n)) = Z_to_bv 64 (bv_unsigned p + (n : Int)) := by
  unfold v_add
  rw [u_len_word_firstn n bs Hn Hlen]

/-- `SeqExec.rdn_skipn`'s address, in the canonical form. -/
theorem word_add_nat_Z (p : word) (k : Nat) (Hk : (k : Int) < 2 ^ 64) :
    p + nat_to_word k = Z_to_bv 64 (bv_unsigned p + (k : Int)) := by
  apply bv_eq_of_unsigned
  have hkw : bv_unsigned (nat_to_word k) = (k : Int) :=
    bv_unsigned_Z_to_bv_small (k : Int) (by omega) Hk
  rw [Z_to_bv_unsigned, bv_wrap64_mod, ← hkw]
  unfold bv_unsigned
  rw [BitVec.toNat_add]
  omega

/-- The count decrement `sub a2,a2,a0` is the remainder's length. -/
theorem v_sub_len_firstn (n : Nat) (bs : List byte) (Hn : n ≤ bs.length)
    (Hlen : (bs.length : Int) < 2 ^ 64) :
    v_sub (len_word bs) (len_word (bs.take n)) = len_word (bs.drop n) := by
  apply bv_eq_of_unsigned
  have h1 := u_len_word_firstn n bs Hn Hlen
  have h2 : bv_unsigned (len_word bs) = (bs.length : Int) :=
    len_word_unsigned bs (by unfold two_pow_64; omega)
  have h3 : bv_unsigned (len_word (bs.drop n)) = ((bs.drop n).length : Int) :=
    len_word_unsigned _ (by unfold two_pow_64; rw [List.length_drop]; omega)
  rw [v_sub_small _ _ (by omega), h1, h2, h3, List.length_drop]
  omega

/-! ## The write-all node -/

mutual
/-- `to_wall ms rest k`: `ms` is a write-pending ecall state offering `rest`
(nonempty) on `fd`; the machine delivers exactly `rest` across one or more
(possibly short) channel writes, then reaches a state satisfying `k`.  The
write node is RET-OBLIVIOUS: the continuation must handle every delivered
length `n`. -/
inductive to_wall (segs : List Segment) (fd : word) :
    machine_state → List byte → (machine_state → Prop) → Prop
  | twl_write : ∀ ms x8 rest k,
      ms.ms_svc_pending = some x8 →
      bv_unsigned x8 = 64 →
      ms_gpr ms 0 = fd →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some rest →
      1 ≤ rest.length →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        to_wall_tail segs fd (advance_past_svc (set_gpr0 ms (len_word (rest.take n))))
          (rest.drop n) k) →
      to_wall segs fd ms rest k

/-- `to_wall_tail ms rest k` is the between-syscalls form: the machine still
owes `rest` (instruction steps, then — if `rest` is nonempty — another
write-pending state; if `rest` is empty, a `k`-state). -/
inductive to_wall_tail (segs : List Segment) (fd : word) :
    machine_state → List byte → (machine_state → Prop) → Prop
  | twt_done : ∀ ms k, k ms → to_wall_tail segs fd ms [] k
  | twt_more : ∀ ms rest k,
      1 ≤ rest.length →
      to_wall segs fd ms rest k →
      to_wall_tail segs fd ms rest k
  | twt_step : ∀ ms ms' rest k,
      ms.ms_svc_pending = none →
      step segs ms = MachineOk ms' →
      to_wall_tail segs fd ms' rest k →
      to_wall_tail segs fd ms rest k
end

/-- Rocq `Scheme to_wall_min := Minimality for to_wall Sort Prop`. -/
theorem to_wall_min (segs : List Segment) (fd : word)
    (P P0 : machine_state → List byte → (machine_state → Prop) → Prop)
    (f : ∀ ms x8 rest k,
      ms.ms_svc_pending = some x8 →
      bv_unsigned x8 = 64 →
      ms_gpr ms 0 = fd →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some rest →
      1 ≤ rest.length →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        to_wall_tail segs fd (advance_past_svc (set_gpr0 ms (len_word (rest.take n))))
          (rest.drop n) k) →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        P0 (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) (rest.drop n) k) →
      P ms rest k)
    (f0 : ∀ ms k, k ms → P0 ms [] k)
    (f1 : ∀ ms rest k, 1 ≤ rest.length → to_wall segs fd ms rest k → P ms rest k →
      P0 ms rest k)
    (f2 : ∀ ms ms' rest k, ms.ms_svc_pending = none → step segs ms = MachineOk ms' →
      to_wall_tail segs fd ms' rest k → P0 ms' rest k → P0 ms rest k) :
    ∀ m l P1, to_wall segs fd m l P1 → P m l P1 := by
  intro m l P1 h
  exact to_wall.rec (motive_1 := fun ms rest k _ => P ms rest k)
    (motive_2 := fun ms rest k _ => P0 ms rest k)
    (fun ms x8 rest k h1 h2 h3 h4 h5 h6 ih => f ms x8 rest k h1 h2 h3 h4 h5 h6 ih)
    (fun ms k hk => f0 ms k hk)
    (fun ms rest k h1 h2 ih => f1 ms rest k h1 h2 ih)
    (fun ms ms' rest k h1 h2 h3 ih => f2 ms ms' rest k h1 h2 h3 ih)
    h

/-- Rocq `with to_wall_tail_min := Minimality for to_wall_tail Sort Prop`. -/
theorem to_wall_tail_min (segs : List Segment) (fd : word)
    (P P0 : machine_state → List byte → (machine_state → Prop) → Prop)
    (f : ∀ ms x8 rest k,
      ms.ms_svc_pending = some x8 →
      bv_unsigned x8 = 64 →
      ms_gpr ms 0 = fd →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some rest →
      1 ≤ rest.length →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        to_wall_tail segs fd (advance_past_svc (set_gpr0 ms (len_word (rest.take n))))
          (rest.drop n) k) →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        P0 (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) (rest.drop n) k) →
      P ms rest k)
    (f0 : ∀ ms k, k ms → P0 ms [] k)
    (f1 : ∀ ms rest k, 1 ≤ rest.length → to_wall segs fd ms rest k → P ms rest k →
      P0 ms rest k)
    (f2 : ∀ ms ms' rest k, ms.ms_svc_pending = none → step segs ms = MachineOk ms' →
      to_wall_tail segs fd ms' rest k → P0 ms' rest k → P0 ms rest k) :
    ∀ m l P1, to_wall_tail segs fd m l P1 → P0 m l P1 := by
  intro m l P1 h
  exact to_wall_tail.rec (motive_1 := fun ms rest k _ => P ms rest k)
    (motive_2 := fun ms rest k _ => P0 ms rest k)
    (fun ms x8 rest k h1 h2 h3 h4 h5 h6 ih => f ms x8 rest k h1 h2 h3 h4 h5 h6 ih)
    (fun ms k hk => f0 ms k hk)
    (fun ms rest k h1 h2 ih => f1 ms rest k h1 h2 ih)
    (fun ms ms' rest k h1 h2 h3 ih => f2 ms ms' rest k h1 h2 h3 ih)
    h

/-- Rocq `Combined Scheme to_wall_mutind from to_wall_min, to_wall_tail_min`. -/
theorem to_wall_mutind (segs : List Segment) (fd : word)
    (P P0 : machine_state → List byte → (machine_state → Prop) → Prop)
    (f : ∀ ms x8 rest k,
      ms.ms_svc_pending = some x8 →
      bv_unsigned x8 = 64 →
      ms_gpr ms 0 = fd →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some rest →
      1 ≤ rest.length →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        to_wall_tail segs fd (advance_past_svc (set_gpr0 ms (len_word (rest.take n))))
          (rest.drop n) k) →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        P0 (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) (rest.drop n) k) →
      P ms rest k)
    (f0 : ∀ ms k, k ms → P0 ms [] k)
    (f1 : ∀ ms rest k, 1 ≤ rest.length → to_wall segs fd ms rest k → P ms rest k →
      P0 ms rest k)
    (f2 : ∀ ms ms' rest k, ms.ms_svc_pending = none → step segs ms = MachineOk ms' →
      to_wall_tail segs fd ms' rest k → P0 ms' rest k → P0 ms rest k) :
    (∀ m l P1, to_wall segs fd m l P1 → P m l P1) ∧
      (∀ m l P1, to_wall_tail segs fd m l P1 → P0 m l P1) :=
  ⟨to_wall_min segs fd P P0 f f0 f1 f2, to_wall_tail_min segs fd P P0 f f0 f1 f2⟩

/-- Rocq's generated non-mutual induction principle for `to_wall_tail`. -/
theorem to_wall_tail_ind (segs : List Segment) (fd : word)
    (P : machine_state → List byte → (machine_state → Prop) → Prop)
    (f : ∀ ms k, k ms → P ms [] k)
    (f0 : ∀ ms rest k, 1 ≤ rest.length → to_wall segs fd ms rest k → P ms rest k)
    (f1 : ∀ ms ms' rest k, ms.ms_svc_pending = none → step segs ms = MachineOk ms' →
      to_wall_tail segs fd ms' rest k → P ms' rest k → P ms rest k) :
    ∀ m l P0, to_wall_tail segs fd m l P0 → P m l P0 :=
  to_wall_tail_min segs fd (fun _ _ _ => True) P
    (fun _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    f
    (fun ms rest k h1 h2 _ => f0 ms rest k h1 h2)
    f1

/-- A straight instruction line in front of a write-all tail is absorbed
into it.  Ported by ticket E-proof-library-2c for `Common/MuslCall.lean`'s
`musl_write_wall`, with the Rocq statement, where Rocq states it: after
the induction schemes, before `to_wall_tail_nil_msteps`.  It takes the
Section variables `segs fd` that Rocq's `Section WithSegsCh` closes it
over. -/
theorem msteps_to_wall_tail (segs : List Segment) (fd : word) (ms ms' : machine_state)
    (rest : List byte) (k : machine_state → Prop)
    (H : msteps segs ms ms') (Hw : to_wall_tail segs fd ms' rest k) :
    to_wall_tail segs fd ms rest k := by
  induction H with
  | mst_refl => exact Hw
  | mst_step _ _ _ hsvc hstep _ ih => exact to_wall_tail.twt_step _ _ _ _ hsvc hstep (ih Hw)

/-- An empty remainder is a straight instruction line to a `k`-state. -/
theorem to_wall_tail_nil_msteps (segs : List Segment) (fd : word) (ms : machine_state)
    (k : machine_state → Prop) (H : to_wall_tail segs fd ms [] k) :
    ∃ ms', msteps segs ms ms' ∧ k ms' :=
  to_wall_tail_ind segs fd
    (fun ms rest k => rest = [] → ∃ ms', msteps segs ms ms' ∧ k ms')
    (fun ms _ hk _ => ⟨ms, msteps.mst_refl ms, hk⟩)
    (fun _ rest _ hnb _ hr => by
      subst hr
      exact absurd hnb (Nat.not_succ_le_zero 0))
    (fun ms ms' _ _ hsvc hstep _ ih hr =>
      match ih hr with
      | ⟨ms'', hm, hk⟩ => ⟨ms'', msteps.mst_step ms ms' ms'' hsvc hstep hm, hk⟩)
    ms [] k H rfl

/-! ## One-step inversion at the write-pending head, with the continuation

The delivered chunk is a nonempty prefix, and the remainder derivation
continues at `skipn n rest` (Lean `List.drop n rest`).  This is the shape
the downstream loop invariants consume (an `SError` `st` is refuted by the
`SNext` equation). -/

theorem sstep_to_wall_inv (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd)
    (ms : machine_state) (rest : List byte) (k : machine_state → Prop) (model : Model)
    (evs : List event) (st : step_to)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfdc : fdchan fd ch model) (Hbm : buf_modeled rest)
    (Hw : to_wall segs fd ms rest k)
    (Hss : sstep segs (config.mkCfg ms model) evs st) :
    ∃ n, 1 ≤ n ∧ n ≤ rest.length ∧
      evs = List.map (WriteEv ch) (rest.take n) ∧
      st = SNext (config.mkCfg (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) model) ∧
      to_wall_tail segs fd (advance_past_svc (set_gpr0 ms (len_word (rest.take n))))
        (rest.drop n) k := by
  cases Hw with
  | twl_write _ x8 _ _ hsvc hno hg hr hnb hcont =>
    obtain ⟨n, hn1, hn2, hevs, hst⟩ :=
      sstep_write_ch_inv segs fd ch Hfd32 ms model x8 rest evs st
        Hh Hlazy Hfdc hsvc hno hg hr Hbm hnb Hss
    exact ⟨n, hn1, hn2, hevs, hst, hcont n hn1 hn2⟩

theorem to_wall_no_error_sstep (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd)
    (ms : machine_state) (rest : List byte) (k : machine_state → Prop) (model : Model)
    (evs : List event)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfdc : fdchan fd ch model) (Hbm : buf_modeled rest)
    (Hw : to_wall segs fd ms rest k) :
    ¬ sstep segs (config.mkCfg ms model) evs SError := by
  intro Hss
  obtain ⟨_, _, _, _, hst, _⟩ :=
    sstep_to_wall_inv segs fd ch Hfd32 ms rest k model evs SError Hh Hlazy Hfdc Hbm Hw Hss
  cases hst

/-! ## Star admissibility: the retry loop realizes the full-buffer trace

One syscall (full delivery) per node suffices as the witness. -/

theorem to_wall_star_admits_mut (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd)
    (model : Model) (tr_k : List event)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfdc : fdchan fd ch model) :
    (∀ ms rest k, to_wall segs fd ms rest k →
      buf_modeled rest →
      (∀ ms', k ms' → ∃ c, star segs (config.mkCfg ms' model) tr_k c) →
      ∃ c, star segs (config.mkCfg ms model) (List.map (WriteEv ch) rest ++ tr_k) c) ∧
    (∀ ms rest k, to_wall_tail segs fd ms rest k →
      buf_modeled rest →
      (∀ ms', k ms' → ∃ c, star segs (config.mkCfg ms' model) tr_k c) →
      ∃ c, star segs (config.mkCfg ms model) (List.map (WriteEv ch) rest ++ tr_k) c) := by
  refine to_wall_mutind segs fd
    (fun ms rest k =>
      buf_modeled rest →
      (∀ ms', k ms' → ∃ c, star segs (config.mkCfg ms' model) tr_k c) →
      ∃ c, star segs (config.mkCfg ms model) (List.map (WriteEv ch) rest ++ tr_k) c)
    (fun ms rest k =>
      buf_modeled rest →
      (∀ ms', k ms' → ∃ c, star segs (config.mkCfg ms' model) tr_k c) →
      ∃ c, star segs (config.mkCfg ms model) (List.map (WriteEv ch) rest ++ tr_k) c)
    ?_ ?_ ?_ ?_
  · -- twl_write: deliver everything in one syscall
    intro ms x8 rest k hsvc hno hg hr hnb _ ih hbm hk
    obtain ⟨c, hstar⟩ :=
      ih rest.length hnb (Nat.le_refl _) (buf_modeled_skipn rest.length rest hbm) hk
    have hsys := sstep.sstep_syscall ms model x8
      (with_copyins [(ms_gpr ms 1, rest.length)]
        (mkEffect (len_word (rest.take rest.length)) [] [])) model model
      (List.map (WriteEv ch) (rest.take rest.length)) Hh hsvc
      (write_ch_ok_n segs ms x8 model fd ch rest rest.length Hfdc Hfd32 hno hg hr hbm hnb
        (Nat.le_refl _))
      Hh (materialize_model_accesses_no_lazy model _ Hlazy)
    rw [apply_effect_copyins_no_write] at hsys
    have hall := star.star_step _ _ _ _ _ hsys hstar
    rw [List.take_length, List.drop_length, List.map_nil, List.nil_append] at hall
    exact ⟨c, hall⟩
  · -- twt_done: hand off to the continuation
    intro ms k hk _ hcont
    exact hcont ms hk
  · -- twt_more
    intro ms rest k _ _ ih hbm hk
    exact ih hbm hk
  · -- twt_step
    intro ms ms' rest k hsvc hstep _ ih hbm hk
    obtain ⟨c, hstar⟩ := ih hbm hk
    have hi : sstep segs (config.mkCfg ms model) [] (SNext (config.mkCfg ms' model)) :=
      sstep.sstep_instr ms model ms' model Hh hsvc
        (by rw [mi_account_step_no_lazy _ _ _ Hlazy, hstep])
    exact ⟨c, star.star_step _ [] _ _ _ hi hstar⟩

theorem to_wall_tail_star_admits (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd)
    (ms : machine_state) (rest : List byte) (k : machine_state → Prop)
    (Hw : to_wall_tail segs fd ms rest k) (Hbm : buf_modeled rest)
    (model : Model) (tr_k : List event)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfdc : fdchan fd ch model)
    (Hk : ∀ ms', k ms' → ∃ c, star segs (config.mkCfg ms' model) tr_k c) :
    ∃ c, star segs (config.mkCfg ms model) (List.map (WriteEv ch) rest ++ tr_k) c :=
  (to_wall_star_admits_mut segs fd ch Hfd32 model tr_k Hh Hlazy Hfdc).2 ms rest k Hw Hbm Hk

/-! ## Ergonomic raw-ecall-record wrapper

Mirrors CatExec/SeqExec's `_rec` entry points: the write node at the state
`step_ecall` leaves. -/

theorem twl_write_rec (segs : List Segment) (fd : word) (k : machine_state → Prop)
    (rest : List byte) (regs : bvmap 5 word) (pc : word) (mem rom : word → Option byte)
    (H17 : bv_unsigned (getr regs 17) = 64)
    (H10 : reg_get regs 10 = fd)
    (Hr : ms_read_bytes
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom }
      (reg_get regs 11) (reg_get regs 12) = some rest)
    (Hnb : 1 ≤ rest.length)
    (Hcont : ∀ n, 1 ≤ n → n ≤ rest.length →
      to_wall_tail segs fd (mkst (regupd regs 10 (len_word (rest.take n))) (v_addi pc 4) mem rom)
        (rest.drop n) k) :
    to_wall segs fd
      { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none,
        ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom }
      rest k := by
  have E10 : (Z_to_bv 5 (10 + ((0 : Nat) : Int)) : reg) = 10 := by decide
  have E11 : (Z_to_bv 5 (10 + ((1 : Nat) : Int)) : reg) = 11 := by decide
  have E12 : (Z_to_bv 5 (10 + ((2 : Nat) : Int)) : reg) = 12 := by decide
  refine to_wall.twl_write _ (getr regs 17) rest k rfl H17 ?_ ?_ Hnb ?_
  · unfold ms_gpr
    rw [E10]
    exact H10
  · unfold ms_gpr
    rw [E11, E12]
    exact Hr
  · intro n hn1 hn2
    rw [adv_set]
    exact Hcont n hn1 hn2

end LinuxProcessSemantics.Common.WallSim

/-! ## Additions for E-proof-library-2a

Ported from `theories/Common/WallSim.v` with the Rocq statements, for
ticket E-proof-library-2a, and appended under the lead's ruling of
2026-09-29 on #1298's files: the declarations above are unchanged.  The
Rocq file was read at 7ba58b45f (`nightly/09-28-2026`), where it matches
the commit the header names byte for byte; 62d810d34 was the last commit
to change it.

`Common/AllocSim.lean` reaches these: the exit-after-retry-loops relation
`to_wallexit`, its omni judgment `to_wallexit_exec` with the lemmas it is
built from (`to_wall_exec_mut`, and `to_wexit_nil_exec` through
`to_wexit_nil_exec_aux`), `to_wallexit_star_admits`, and
`wevents_ch_fd1`.  Why the trace set of a `to_wallexit` run is the
full-delivery one whatever the chunking is argued on the Rocq
`to_wallexit` and `to_wall_exec_mut`.

Spellings, beyond the header's: `to_wallexit` takes Rocq's Section
variables `segs fd` as leading parameters, as `to_wall` does.  Of the
Section variables, `to_wexit_nil_exec_aux` and `to_wexit_nil_exec` take
`segs`, and `to_wall_exec_mut`, `to_wallexit_exec` and
`to_wallexit_star_admits` take `segs fd ch Hfd32`, the variables Rocq's
`Section WithSegsCh` closes them over; `wevents_ch_fd1`, stated after that
section closes, takes no Section variable.  Rocq `Forall_cons_iff` on
`bufs_modeled` is `List.mem_cons_self` and `List.mem_cons_of_mem` here. -/

namespace LinuxProcessSemantics.Common.WallSim

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.OmniRun
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.ExitSim (exit_dispatch_ok sstep_exit_inv sstep_instr_inv)

/-- An exit-after-writes run whose writes go through put-style retry
loops (a `to_wall_tail` node per buffer), bottoming out in the exit
straight line `to_wexit segs ms [] code`. -/
def to_wallexit (segs : List Segment) (fd : word) (bufs : List (List byte)) (code : word)
    (ms : machine_state) : Prop :=
  match bufs with
  | [] => to_wexit segs ms [] code
  | buf :: rest => 1 ≤ buf.length ∧ to_wall_tail segs fd ms buf (to_wallexit segs fd rest code)

/-- The omni reading of a `to_wall` node: whatever the chunking, the node
emits its buffer and continues into a configuration satisfying the
continuation's judgment. -/
theorem to_wall_exec_mut (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd)
    (model : Model) (Q : post)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfdc : fdchan fd ch model) :
    (∀ ms rest k, to_wall segs fd ms rest k →
      buf_modeled rest →
      (∀ ms', k ms' → exec segs (config.mkCfg ms' model) Q) →
      exec segs (config.mkCfg ms model)
        (fun tr o => ∃ tr', tr = List.map (WriteEv ch) rest ++ tr' ∧ Q tr' o)) ∧
    (∀ ms rest k, to_wall_tail segs fd ms rest k →
      buf_modeled rest →
      (∀ ms', k ms' → exec segs (config.mkCfg ms' model) Q) →
      exec segs (config.mkCfg ms model)
        (fun tr o => ∃ tr', tr = List.map (WriteEv ch) rest ++ tr' ∧ Q tr' o)) := by
  refine to_wall_mutind segs fd
    (fun ms rest k =>
      buf_modeled rest →
      (∀ ms', k ms' → exec segs (config.mkCfg ms' model) Q) →
      exec segs (config.mkCfg ms model)
        (fun tr o => ∃ tr', tr = List.map (WriteEv ch) rest ++ tr' ∧ Q tr' o))
    (fun ms rest k =>
      buf_modeled rest →
      (∀ ms', k ms' → exec segs (config.mkCfg ms' model) Q) →
      exec segs (config.mkCfg ms model)
        (fun tr o => ∃ tr', tr = List.map (WriteEv ch) rest ++ tr' ∧ Q tr' o))
    ?_ ?_ ?_ ?_
  · -- twl_write: the delivered lengths are the successors, and the IH covers them
    intro ms x8 rest k hsvc hno hg hr hnb hcont ih hbm hK
    have hw : to_wall segs fd ms rest k := to_wall.twl_write ms x8 rest k hsvc hno hg hr hnb hcont
    refine exec.exec_step _ _ Hh ?_ ?_ ?_
    · -- progress: deliver the whole buffer in one syscall
      exact ⟨_, _, sstep.sstep_syscall ms model x8
        (with_copyins [(ms_gpr ms 1, rest.length)]
          (mkEffect (len_word (rest.take rest.length)) [] [])) model model
        (List.map (WriteEv ch) (rest.take rest.length)) Hh hsvc
        (write_ch_ok_n segs ms x8 model fd ch rest rest.length Hfdc Hfd32 hno hg hr hbm hnb
          (Nat.le_refl _))
        Hh (materialize_model_accesses_no_lazy model _ Hlazy)⟩
    · intro evs hss
      obtain ⟨_, _, _, _, habs, _⟩ :=
        sstep_to_wall_inv segs fd ch Hfd32 ms rest k model evs SError Hh Hlazy Hfdc hbm hw hss
      cases habs
    · intro evs c' hss
      obtain ⟨n, hn1, hn2, hevs, hc', _⟩ :=
        sstep_to_wall_inv segs fd ch Hfd32 ms rest k model evs (SNext c') Hh Hlazy Hfdc hbm hw hss
      subst hevs
      cases hc'
      refine exec_conseq _ _ _ _ (ih n hn1 hn2 (buf_modeled_skipn n rest hbm) hK) ?_
      intro tr o h
      obtain ⟨tr', htr, hq⟩ := h
      refine ⟨tr', ?_, hq⟩
      rw [htr, ← List.append_assoc, ← List.map_append, List.take_append_drop]
  · -- twt_done: the continuation's own judgment
    intro ms k hk _ hK
    exact exec_conseq _ _ _ _ (hK ms hk) (fun tr _ hq => ⟨tr, rfl, hq⟩)
  · -- twt_more
    intro ms rest k _ _ ih hbm hK
    exact ih hbm hK
  · -- twt_step: one silent instruction
    intro ms ms' rest k hsvc hstep _ ih hbm hK
    apply exec_step_only segs _ _ [] (config.mkCfg ms' model)
    · exact sstep.sstep_instr ms model ms' model Hh hsvc
        (by rw [mi_account_step_no_lazy _ _ _ Hlazy, hstep])
    · intro evs st hs
      exact sstep_instr_inv segs ms model ms' evs st Hlazy hsvc hstep hs
    · exact ih hbm hK

/-- The exit straight line at the bottom of a `to_wallexit`: the
`bufs = []` fragment of `to_wexit`, which needs no channel assumption. -/
theorem to_wexit_nil_exec_aux (segs : List Segment) (ms : machine_state)
    (bufs : List (List byte)) (code : word) (model : Model)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hte : to_wexit segs ms bufs code) (Hbufs : bufs = []) :
    exec segs (config.mkCfg ms model)
      (fun tr o => tr = [ExitEv code (m_fs model)] ∧ exits_with code tr o) := by
  induction Hte with
  | tw_exit ms x8 hsvc hx8 =>
    apply exec_step_only segs _ _
      [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
      (config.mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))
    · exact sstep.sstep_exit ms model x8 _ _ [] _ Hh hsvc
        (exit_dispatch_ok _ model hx8) rfl rfl
    · intro evs st hs
      exact sstep_exit_inv _ _ _ _ _ _ Hh hsvc hx8 hs
    · apply exec.exec_halt
      · simp only [m_halted_with_halted, ne_eq, reduceCtorEq, not_false_eq_true]
      · exact And.intro rfl (And.intro (m_halted_with_halted _ _) (m_killed_with_halted _ _))
  | tw_write _ _ _ _ _ _ _ _ _ _ _ _ => cases Hbufs
  | tw_step ms ms' _ _ hsvc hstep _ ih =>
    apply exec_step_only segs _ _ [] (config.mkCfg ms' model)
    · exact sstep.sstep_instr ms model ms' model Hh hsvc
        (by rw [mi_account_step_no_lazy _ _ _ Hlazy, hstep])
    · intro evs st hs
      exact sstep_instr_inv segs ms model ms' evs st Hlazy hsvc hstep hs
    · exact ih Hbufs

theorem to_wexit_nil_exec (segs : List Segment) (ms : machine_state) (code : word)
    (model : Model)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hte : to_wexit segs ms [] code) :
    exec segs (config.mkCfg ms model)
      (fun tr o => tr = [ExitEv code (m_fs model)] ∧ exits_with code tr o) :=
  to_wexit_nil_exec_aux segs ms [] code model Hh Hlazy Hte rfl

/-- The judgment for a retry-loop run: its executions emit the
full-delivery trace, then the exit. -/
theorem to_wallexit_exec (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd)
    (bufs : List (List byte)) (code : word) (ms : machine_state) (model : Model)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfdc : fdchan fd ch model) (Hbm : bufs_modeled bufs)
    (Hw : to_wallexit segs fd bufs code ms) :
    exec segs (config.mkCfg ms model)
      (fun tr o => tr = wevents_ch ch bufs ++ [ExitEv code (m_fs model)]
        ∧ exits_with code tr o) := by
  induction bufs generalizing ms with
  | nil => exact to_wexit_nil_exec segs ms code model Hh Hlazy Hw
  | cons buf rest ih =>
    obtain ⟨_, Hw⟩ := Hw
    have Hb : buf_modeled buf := Hbm buf List.mem_cons_self
    have Hbs : bufs_modeled rest := fun b hb => Hbm b (List.mem_cons_of_mem _ hb)
    refine exec_conseq _ _ _ _
      ((to_wall_exec_mut segs fd ch Hfd32 model _ Hh Hlazy Hfdc).2 ms buf
        (to_wallexit segs fd rest code) Hw Hb (fun ms' Hk => ih ms' Hbs Hk)) ?_
    intro tr o h
    obtain ⟨tr', htr, heq, hx⟩ := h
    refine ⟨?_, hx⟩
    rw [htr, heq]
    show _ = (List.map (WriteEv ch) buf ++ wevents_ch ch rest) ++ _
    rw [List.append_assoc]

theorem to_wallexit_star_admits (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd)
    (bufs : List (List byte)) (code : word) (ms : machine_state) (model : Model)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfdc : fdchan fd ch model) (Hbm : bufs_modeled bufs)
    (Hw : to_wallexit segs fd bufs code ms) :
    ∃ c, star segs (config.mkCfg ms model)
      (wevents_ch ch bufs ++ [ExitEv code (m_fs model)]) c := by
  obtain ⟨tr, o, hm, heq, hx⟩ :=
    exec_realizes _ _ _ (to_wallexit_exec segs fd ch Hfd32 bufs code ms model Hh Hlazy Hfdc Hbm Hw)
  cases o with
  | OError _ => exact False.elim hx
  | OHalt c' =>
    subst heq
    exact ⟨c', (mexec_halt_star _ _ _ _ hm c' rfl).1⟩

/-- The generic-channel event list at fd 1 is `wevents`. -/
theorem wevents_ch_fd1 : ∀ bufs, wevents_ch (Z_to_bv 64 1) bufs = wevents bufs := by
  intro bufs
  induction bufs with
  | nil => rfl
  | cons b bs ih =>
    show List.map _ b ++ wevents_ch _ bs = List.map _ b ++ wevents bs
    rw [ih]

end LinuxProcessSemantics.Common.WallSim

/-! ## Additions for E-proof-library-2b

Ported from `theories/Common/WallSim.v` with the Rocq statements, for
ticket E-proof-library-2b, and appended under the lead's ruling of
2026-09-29 on #1298's files: the declarations above are unchanged.  The
Rocq file is unchanged from the commit the header names to the day tip
f62e8cc14; 62d810d34 was the last commit to change it.

`Common/DrainSim.lean`'s finishing phase reaches these:
`to_wall_star_admits`, which is the write-node half of `to_wall_star_admits_mut`
(the tail half is `to_wall_tail_star_admits` above), and the
star-exhaustiveness pair `to_wall_star_only_mut`/`to_wall_star_only`.
They take `segs fd ch Hfd32` first, the Section variables Rocq's
`Section WithSegsCh` closes them over, as the lemmas above do.  The
mutual proof runs through `to_wall_mutind`, as Rocq's does. -/

namespace LinuxProcessSemantics.Common.WallSim

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.ExitSim (sstep_instr_inv)

theorem to_wall_star_admits (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd)
    (ms : machine_state) (rest : List byte) (k : machine_state → Prop)
    (Hw : to_wall segs fd ms rest k) (Hbm : buf_modeled rest)
    (model : Model) (tr_k : List event)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfdc : fdchan fd ch model)
    (Hk : ∀ ms', k ms' → ∃ c, star segs (config.mkCfg ms' model) tr_k c) :
    ∃ c, star segs (config.mkCfg ms model) (List.map (WriteEv ch) rest ++ tr_k) c :=
  (to_wall_star_admits_mut segs fd ch Hfd32 model tr_k Hh Hlazy Hfdc).1 ms rest k Hw Hbm Hk

/-- Every run from a write-all node is a prefix of the whole buffer's
writes followed by what the continuation allows, however the environment
chunks the writes. -/
theorem to_wall_star_only_mut (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd)
    (model : Model) (T : List event)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfdc : fdchan fd ch model) :
    (∀ ms rest k, to_wall segs fd ms rest k →
      buf_modeled rest →
      (∀ ms' tr c, k ms' → star segs (config.mkCfg ms' model) tr c → is_prefix tr T) →
      ∀ tr c, star segs (config.mkCfg ms model) tr c →
        is_prefix tr (List.map (WriteEv ch) rest ++ T)) ∧
    (∀ ms rest k, to_wall_tail segs fd ms rest k →
      buf_modeled rest →
      (∀ ms' tr c, k ms' → star segs (config.mkCfg ms' model) tr c → is_prefix tr T) →
      ∀ tr c, star segs (config.mkCfg ms model) tr c →
        is_prefix tr (List.map (WriteEv ch) rest ++ T)) := by
  refine to_wall_mutind segs fd
    (fun ms rest k =>
      buf_modeled rest →
      (∀ ms' tr c, k ms' → star segs (config.mkCfg ms' model) tr c → is_prefix tr T) →
      ∀ tr c, star segs (config.mkCfg ms model) tr c →
        is_prefix tr (List.map (WriteEv ch) rest ++ T))
    (fun ms rest k =>
      buf_modeled rest →
      (∀ ms' tr c, k ms' → star segs (config.mkCfg ms' model) tr c → is_prefix tr T) →
      ∀ tr c, star segs (config.mkCfg ms model) tr c →
        is_prefix tr (List.map (WriteEv ch) rest ++ T))
    ?_ ?_ ?_ ?_
  · -- twl_write
    intro ms x8 rest k Hsvc Hno Hg Hr Hnb _ IH Hbm HK tr c Hstar
    cases Hstar with
    | star_refl => exact is_prefix_nil _
    | star_step _ evs c2 tr2 _ Hss Hstar2 =>
      obtain ⟨n, Hn1, Hn2, Hevs, Hc2⟩ :=
        sstep_write_ch_inv segs fd ch Hfd32 ms model x8 rest evs (SNext c2)
          Hh Hlazy Hfdc Hsvc Hno Hg Hr Hbm Hnb Hss
      subst Hevs
      cases Hc2
      have Hp := IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) HK tr2 c Hstar2
      have heq : List.map (WriteEv ch) rest ++ T =
          List.map (WriteEv ch) (rest.take n) ++ (List.map (WriteEv ch) (rest.drop n) ++ T) := by
        rw [← List.append_assoc, ← List.map_append, List.take_append_drop]
      rw [heq]
      exact is_prefix_app_mono _ _ _ Hp
  · -- twt_done
    intro ms k Hk _ HK tr c Hstar
    rw [List.map_nil, List.nil_append]
    exact HK ms tr c Hk Hstar
  · -- twt_more
    intro ms rest k _ _ IH Hbm HK tr c Hstar
    exact IH Hbm HK tr c Hstar
  · -- twt_step
    intro ms ms' rest k Hsvc Hstep _ IH Hbm HK tr c Hstar
    cases Hstar with
    | star_refl => exact is_prefix_nil _
    | star_step _ evs c2 tr2 _ Hss Hstar2 =>
      obtain ⟨Hevs, Hc2⟩ :=
        sstep_instr_inv segs ms model ms' evs (SNext c2) Hlazy Hsvc Hstep Hss
      subst Hevs
      cases Hc2
      exact IH Hbm HK tr2 c Hstar2

theorem to_wall_star_only (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd)
    (ms : machine_state) (rest : List byte) (k : machine_state → Prop)
    (Hw : to_wall segs fd ms rest k) (Hbm : buf_modeled rest)
    (model : Model) (T : List event)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfdc : fdchan fd ch model)
    (HK : ∀ ms' tr c, k ms' → star segs (config.mkCfg ms' model) tr c → is_prefix tr T)
    (tr : List event) (c : config) (Hstar : star segs (config.mkCfg ms model) tr c) :
    is_prefix tr (List.map (WriteEv ch) rest ++ T) :=
  (to_wall_star_only_mut segs fd ch Hfd32 model T Hh Hlazy Hfdc).1 ms rest k Hw Hbm HK tr c Hstar

end LinuxProcessSemantics.Common.WallSim

/-! ## Additions for ticket E-conditional_bug_ns

Ported from `theories/Common/WallSim.v` with the Rocq statements. The
Rocq file was read at f44244ad6b8041aa83053d9ca91e090037ed743b, where it
matches the header's commit byte for byte.
`theories/Examples/conditional_bug_ns/Proof.v` glues its
no-output arms with `CatSim.cat_omni_strong_equiv_te` and its 'h' arm
with `wall_omni_strong_equiv`.

Section variables become explicit leading arguments: `twe_step` and
`msteps_to_wallexit` take `segs fd` (Rocq drops the unused `ch` and
`Hfd32`). Run-level lemmas retain Rocq's `fd ch Hfd32` argument order.
The existing retry-loop execution theorem and CatSim's `bufs_modeled`
are reused. No declaration above needs to move for Lean's declaration
order. -/

namespace LinuxProcessSemantics.Common.WallSim

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.OmniRun
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
open LinuxProcessSemantics.Common.CatSim

/-- Prepend one ordinary instruction to a retry-loop write-then-exit derivation. -/
theorem twe_step (segs : List Segment) (fd : word) (ms ms' : machine_state)
    (bufs : List (List byte)) (code : word)
    (Hsvc : ms.ms_svc_pending = none) (Hstep : step segs ms = MachineOk ms')
    (Hw : to_wallexit segs fd bufs code ms') : to_wallexit segs fd bufs code ms := by
  cases bufs with
  | nil => exact to_wexit.tw_step ms ms' [] code Hsvc Hstep Hw
  | cons buf rest =>
    exact ⟨Hw.1, to_wall_tail.twt_step ms ms' buf (to_wallexit segs fd rest code)
      Hsvc Hstep Hw.2⟩

/-- Prepend an ordinary instruction run to a retry-loop write-then-exit derivation. -/
theorem msteps_to_wallexit (segs : List Segment) (fd : word) (ms ms' : machine_state)
    (bufs : List (List byte)) (code : word) (Hms : msteps segs ms ms')
    (Hw : to_wallexit segs fd bufs code ms') : to_wallexit segs fd bufs code ms := by
  cases bufs with
  | nil => exact msteps_to_wexit segs ms ms' [] code Hms Hw
  | cons buf rest =>
    exact ⟨Hw.1, msteps_to_wall_tail segs fd ms ms' buf (to_wallexit segs fd rest code) Hms Hw.2⟩

/-- The run-level omni judgment of a retry-loop run. -/
theorem wall_omni_run (fd ch : word) (Hfd32 : fd32 fd = fd)
    (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (bufs : List (List byte)) (code : word)
    (Hfdc : fdchan fd ch (init_model (segments_reserved segs) brk0 mb sp lim inp))
    (Hbm : bufs_modeled bufs)
    (Hw : to_wallexit segs fd bufs code
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)) :
    omni_run (Image.mkImage segs pc ph) lim (ExecEntry.mkEntry sp brk0 mb rnd) inp
      (fun tr o => tr = wevents_ch ch bufs ++ [ExitEv code inp.in_fs] ∧ exits_with code tr o) :=
  to_wallexit_exec segs fd ch Hfd32 bufs code _
    (init_model (segments_reserved segs) brk0 mb sp lim inp) rfl rfl Hfdc Hbm Hw

/-- Observable traces are precisely prefixes of the full delivery followed by the exit. -/
theorem wall_obs_iff (fd ch : word) (Hfd32 : fd32 fd = fd)
    (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (bufs : List (List byte)) (code : word)
    (Hfdc : fdchan fd ch (init_model (segments_reserved segs) brk0 mb sp lim inp))
    (Hbm : bufs_modeled bufs)
    (Hw : to_wallexit segs fd bufs code
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap))
    (tr : List event) :
    obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr ↔
      is_prefix tr (wevents_ch ch bufs ++ [ExitEv code inp.in_fs]) := by
  apply exec_obs_iff
  refine exec_conseq _ _ _ _
    (wall_omni_run fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw) ?_
  intro tr' o h
  exact ⟨h.1, exits_with_never_errors _ tr' o h.2⟩

/-- The initialized retry-loop run does not reach an explicit error. -/
theorem wall_no_error_run (fd ch : word) (Hfd32 : fd32 fd = fd)
    (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (bufs : List (List byte)) (code : word)
    (Hfdc : fdchan fd ch (init_model (segments_reserved segs) brk0 mb sp lim inp))
    (Hbm : bufs_modeled bufs)
    (Hw : to_wallexit segs fd bufs code
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)) :
    ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) := by
  apply exec_no_error
  refine exec_conseq _ _ _ _
    (wall_omni_run fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw) ?_
  intro tr o h
  exact exits_with_never_errors _ tr o h.2

/-- Equal buffers and exit code give omni strong equivalence of retry-loop binaries. -/
theorem wall_omni_strong_equiv (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo) (asp abrk amb : word)
    (arnd : EntryDraw) (bufs : List (List byte)) (code : word) (inp : ProcInput)
    (Hsource : to_wallexit source_segs (Z_to_bv 64 1) bufs code
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap))
    (Htarget : to_wallexit target_segs (Z_to_bv 64 1) bufs code
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap))
    (Hbm : bufs_modeled bufs) :
    omni_strong_equiv (Image.mkImage source_segs rpc rph) (Image.mkImage target_segs apc aph)
      (ExecEntry.mkEntry rsp rbrk rmb rrnd) (ExecEntry.mkEntry asp abrk amb arnd) inp := by
  have HfdS : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp) := ⟨rfl, rfl⟩
  have HfdT : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp) := ⟨rfl, rfl⟩
  refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
  · refine coexec_conseq _ _ _ _
      (exec_coexec _ _ _ (wall_omni_run _ _ fd32_1 source_segs rpc rph rsp rbrk rmb rrnd
        source_alloc_limit inp bufs code HfdS Hbm Hsource)) ?_
    intro tr o h
    exact never_errors_covered _ _ _ (exits_with_never_errors _ tr o h.2)
  · refine (trace_equiv_iff_omni _ _ _ _ _ _ _).1 ?_
    intro tr
    exact (wall_obs_iff _ _ fd32_1 source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp
      bufs code HfdS Hbm Hsource tr).trans
      (wall_obs_iff _ _ fd32_1 target_segs apc aph asp abrk amb arnd target_alloc_limit inp
        bufs code HfdT Hbm Htarget tr).symm
  · exact (bh_errors_iff (Image.mkImage target_segs apc aph) target_alloc_limit
      (ExecEntry.mkEntry asp abrk amb arnd) inp).1
      (wall_no_error_run _ _ fd32_1 target_segs apc aph asp abrk amb arnd target_alloc_limit inp
        bufs code HfdT Hbm Htarget)

/-- Equal buffers and exit code give modeledness and equivalence at the supplied budgets. -/
theorem wall_strong_equiv (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo) (asp abrk amb : word)
    (arnd : EntryDraw) (alim : Int) (bufs : List (List byte)) (code : word) (inp : ProcInput)
    (Hsource : to_wallexit source_segs (Z_to_bv 64 1) bufs code
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap))
    (Htarget : to_wallexit target_segs (Z_to_bv 64 1) bufs code
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap))
    (Hbm : bufs_modeled bufs) :
    modeled (run (Image.mkImage source_segs rpc rph) rlim (ExecEntry.mkEntry rsp rbrk rmb rrnd) inp) ∧
    equiv (run (Image.mkImage source_segs rpc rph) rlim (ExecEntry.mkEntry rsp rbrk rmb rrnd) inp)
      (run (Image.mkImage target_segs apc aph) alim (ExecEntry.mkEntry asp abrk amb arnd) inp) := by
  have HfdS : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
      (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) := ⟨rfl, rfl⟩
  have HfdT : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
      (init_model (segments_reserved target_segs) abrk amb asp alim inp) := ⟨rfl, rfl⟩
  refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
  · exact no_error_no_unmodeled _ _
      (wall_no_error_run _ _ fd32_1 source_segs rpc rph rsp rbrk rmb rrnd rlim inp
        bufs code HfdS Hbm Hsource)
  · intro tr
    exact (wall_obs_iff _ _ fd32_1 source_segs rpc rph rsp rbrk rmb rrnd rlim inp
      bufs code HfdS Hbm Hsource tr).trans
      (wall_obs_iff _ _ fd32_1 target_segs apc aph asp abrk amb arnd alim inp
        bufs code HfdT Hbm Htarget tr).symm
  · exact wall_no_error_run _ _ fd32_1 target_segs apc aph asp abrk amb arnd alim inp
      bufs code HfdT Hbm Htarget

end LinuxProcessSemantics.Common.WallSim

/-! ## Additions for ticket E-conditional_bug_ns, second batch

Ported from `theories/Common/WallSim.v` with the Rocq statements; the Rocq
file was read at f44244ad6b8041aa83053d9ca91e090037ed743b. Other examples'
proofs reach `fd32_2`, `len_word_firstn_nat` and `v_add_len_firstn`:
`tail1_ns`, `arena_tee_ns` and `brk_rev_ns`. -/

namespace LinuxProcessSemantics.Common.WallSim

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.Common.PropExec

/-- The stderr fd literal is 32-bit-stable. -/
theorem fd32_2 : fd32 (Z_to_bv 64 2) = Z_to_bv 64 2 :=
  fd32_id _ (by decide)

/-- The length word of a prefix of length `n` is `nat_to_word n`. -/
theorem len_word_firstn_nat (n : Nat) (bs : List byte) (Hn : n ≤ bs.length) :
    len_word (bs.take n) = nat_to_word n := by
  unfold len_word nat_to_word
  rw [List.length_take, Nat.min_eq_left Hn]

/-- The pointer bump after a delivery of `n` bytes is `p + nat_to_word n`. -/
theorem v_add_len_firstn (p : word) (n : Nat) (bs : List byte) (Hn : n ≤ bs.length) :
    v_add p (len_word (bs.take n)) = p + nat_to_word n := by
  rw [len_word_firstn_nat n bs Hn]
  unfold v_add
  apply bv_eq_of_unsigned
  rw [Z_to_bv_unsigned, bv_unsigned_add]

end LinuxProcessSemantics.Common.WallSim
