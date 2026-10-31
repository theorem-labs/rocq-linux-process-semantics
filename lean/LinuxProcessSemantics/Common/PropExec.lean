import Lean
import LinuxProcessSemantics.LinuxProcessSem.Run

/-! # Common.PropExec — the proof-side machine interface and step library

Proof-side machine and memory interfaces, corresponding to
`theories/Common/PropExec.v`. These lemmas reason about the existing step
function; they do not introduce a second instruction semantics.

The part before "The shared core" predates ticket E-proof-library and
serves the `rwx_flag_ns` pilot: Rocq's `mkst`, `getr`, `regupd`,
`wrap_mem` and `u_add1` beside Lean-only helpers (`read_argc_ov`,
`build_stack_bytes_prefix`, `step_of_fetch`, `decode_exec_of_interp`,
`interp_*`, …).  From "The shared core" on, the file ports, at
2cde689f94c086b868999970834b76a25616b94a, the `PropExec.v` constants
`cat1024_ns`'s `strong_universal` reaches (`Print All Dependencies`), with
the Rocq statements; each section's docstring names the spellings it uses.
`bv_eqb_refl` is `protected`, which changes how it is named, in this
namespace as well as outside it, and not its statement (its docstring says
why).  Everything else in the Rocq file was left unported by that ticket;
cat1024_ns reaches none of it.  Sections appended at the end of this file
since, each headed by the ticket that added it, port some of it.

Lean-only fault helpers used by `ErrEscape` sit in the appended T175
section, each named for what a Rocq tactic did inline:
- `step_fault_of_interp` is the fault half of `step_exec`.  Rocq's
  two faulting loads run `step_pipeline`, whose Lean macro applies
  `step_exec`; that lemma fixes the decoded size at 4 and the answer at
  `MachineOk`, so the Lean proofs go through this helper instead, which
  keeps Rocq's quantified `isz`.
- `interp_load_none` is the `ELoad` arm of `interp_eff_accesses` when the
  `ov_read_bytes` read (the overlay, then the loaded segments) misses, the
  step Rocq closes by `rewrite ov_rdn, b_addsext, Hread` and `reflexivity`.

Universes.  Rocq's `nth_error_skipn_cons` and `len_word_nat` are not
universe polymorphic, and each binds `A : Type@{<lemma>.u0}`, a global
universe.  Here `nth_error_skipn_cons` binds `{A : Type _}`, whose
universe is a parameter of the theorem with no upper bound, where Rocq's
global universe bounds `A` from above; Rocq's `A` may also be a
proposition, by cumulativity, and a `Type _` binder may not.
`len_word_nat` binds `{A : Type}`, universe 0, because the
`BvBase.len_word` its statement applies binds `{A : Type}`, and a
`Type _` binder is set to 0 there with no error.  Rocq's `A` may also be
a proposition, by cumulativity, or a type Lean places above `Type`, such
as `Type` itself, which a use admits by bounding the lemma's global
universe from below; Lean's may be neither.  `Prop`, `Nat → Prop` and
`List Prop` are not among these: Rocq places them above `Set`, Lean places
them in `Type`, and both take them.  Widening `len_word_nat`'s binder
needs a `lean: base:` change that widens `BvBase.len_word` first, and the
instances where Rocq's `A` is a proposition have no Lean form either
way. -/

namespace LinuxProcessSemantics.Common.PropExec

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.DecodeC
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run

def mkst (regs : bvmap 5 word) (pc : word) (mem rom : word → Option byte) : machine_state :=
  { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
    ms_svc_pending := none, ms_resv := none, ms_fcsr := 0,
    ms_mem := mem, ms_rom := rom }

def getr (regs : bvmap 5 word) (r : reg) : word :=
  if bv_eqb r 0 then 0 else reg_get regs r

def regupd (regs : bvmap 5 word) (r : reg) (v : word) : bvmap 5 word :=
  bvmap_set r v regs

def wrap_mem (ph : PhdrInfo) (sp : word) (argv envp : List (List byte))
    (uid hwcap : word) (draw : EntryDraw) : word → Option byte :=
  fun addr =>
    match stack_to_mem sp (entry_stack_image ph sp argv envp uid hwcap draw) addr with
    | some b => some b
    | none =>
      if (bv_unsigned sp - stack_max_size ≤ bv_unsigned addr) &&
          (bv_unsigned addr < bv_unsigned sp)
      then some 0 else none

theorem u_add1 (a : word) (h : bv_unsigned a + 1 < 2 ^ 64) :
    bv_unsigned (a + 1) = bv_unsigned a + 1 := by
  have hn : a.toNat + 1 < 2 ^ 64 := by
    unfold bv_unsigned at h
    exact_mod_cast h
  simp [bv_unsigned, BitVec.toNat_add, Nat.mod_eq_of_lt hn]

theorem add_offset_succ (a : word) (i : Nat) :
    a + 1 + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (i + 1) := by
  rw [BitVec.ofNat_add]
  change a + 1 + BitVec.ofNat 64 i = a + (BitVec.ofNat 64 i + 1)
  simp only [BitVec.add_assoc, BitVec.add_comm 1]

theorem u_add_offset (a : word) (i : Nat) (h : a.toNat + i < 2 ^ 64) :
    bv_unsigned (a + BitVec.ofNat 64 i) = bv_unsigned a + (i : Int) := by
  have hi : i < 2 ^ 64 := by omega
  simp [bv_unsigned, BitVec.toNat_add, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt h]

theorem ov_read_bytes_of_prefix (segs : List Segment) (m : word → Option byte)
    (a : word) (bs : List byte)
    (h : ∀ i (hi : i < bs.length), m (a + BitVec.ofNat 64 i) = some bs[i]) :
    ov_read_bytes segs m a bs.length = some bs := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    have h0 : m a = some b := by
      have hh := h 0 (by simp)
      change m (a + 0#64) = some b at hh
      rw [BitVec.add_zero] at hh
      exact hh
    have ht := ih (a + 1) (by
      intro i hi
      rw [add_offset_succ]
      exact h (i + 1) (by simpa using Nat.succ_lt_succ hi))
    simp only [List.length_cons, ov_read_bytes, h0, ht]

theorem stack_to_mem_prefix (base : word) (headBytes tailBytes : List byte)
    (i : Nat) (hi : i < headBytes.length) (hnw : base.toNat + i < 2 ^ 64) :
    stack_to_mem base (headBytes ++ tailBytes) (base + BitVec.ofNat 64 i) = some headBytes[i] := by
  have hua := u_add_offset base i hnw
  have hlo : bv_unsigned base ≤ bv_unsigned base + (i : Int) := by omega
  have hlen : (i : Int) < ((headBytes ++ tailBytes).length : Int) := by
    simp only [List.length_append]
    exact_mod_cast (show i < headBytes.length + tailBytes.length by omega)
  have hoff : bv_unsigned base + (i : Int) - bv_unsigned base = (i : Int) := by omega
  simp only [stack_to_mem, hua, ite_eq_left hlo, hoff, ite_eq_left hlen, Int.toNat_natCast]
  rw [List.getElem?_append_left hi]
  exact List.getElem?_eq_getElem hi

theorem build_stack_bytes_prefix (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (uid hwcap : word) (draw : EntryDraw) :
    ∃ rest, build_stack_bytes ph sp argv envp uid hwcap draw =
      word_le8 (len_word argv) ++ rest := by
  unfold build_stack_bytes
  simp only [List.append_assoc]
  exact ⟨_, rfl⟩

/-- Startup entropy is inside the written block and page-tail bytes are
appended to it. Neither choice changes the initial argc word. -/
theorem entry_stack_image_argc_prefix (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (uid hwcap : word) (draw : EntryDraw) :
    ∃ rest, entry_stack_image ph sp argv envp uid hwcap draw =
      word_le8 (len_word argv) ++ rest := by
  obtain ⟨rest, hrest⟩ := build_stack_bytes_prefix ph sp argv envp uid hwcap draw
  unfold entry_stack_image
  rw [hrest, List.append_assoc]
  exact ⟨_, rfl⟩

/-- Lean-only: argc read back through the overlay reader `ov_read_bytes`,
the form the `rwx_flag_ns` pilot uses.  Rocq's `read_argc`, over `rdn` and
the raw `stack_to_mem`, is ported under its own name below. -/
theorem read_argc_ov (segs : List Segment) (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (uid hwcap : word) (draw : EntryDraw)
    (hnw : sp.toNat + 8 < 2 ^ 64) :
    ov_read_bytes segs (wrap_mem ph sp argv envp uid hwcap draw) sp 8 =
      some (word_le8 (len_word argv)) := by
  have hlen : (word_le8 (len_word argv)).length = 8 := rfl
  rw [← hlen]
  apply ov_read_bytes_of_prefix
  intro i hi
  obtain ⟨rest, hrest⟩ := entry_stack_image_argc_prefix ph sp argv envp uid hwcap draw
  have hread := stack_to_mem_prefix sp (word_le8 (len_word argv)) rest i hi
    (by rw [hlen] at hi; omega)
  simp only [wrap_mem, hrest, hread]

theorem write_to_mem_away (m : word → Option byte) (a : word) (bs : List byte)
    (p : word) (h : ∀ i, i < bs.length → p ≠ a + BitVec.ofNat 64 i) :
    write_to_mem m a bs p = m p := by
  induction bs generalizing m a with
  | nil => rfl
  | cons b bs ih =>
    have h0 : p ≠ a := by simpa using h 0 (by simp)
    simp only [write_to_mem]
    rw [ih]
    · simp [bv_eqb, h0]
    · intro i hi
      rw [add_offset_succ]
      exact h (i + 1) (by simpa using Nat.succ_lt_succ hi)

theorem read_written_byte (segs : List Segment) (m : word → Option byte)
    (a : word) (b : byte) :
    ov_read_bytes segs (write_to_mem m a [b]) a 1 = some [b] := by
  simp [ov_read_bytes, write_to_mem, bv_eqb]

theorem step_of_fetch (segs : List Segment) (ms : machine_state) (w : BitVec 32)
    (hf : fetch_word segs (ms_pc ms) = some w) :
    RiscvSemantics.step segs ms = decode_exec segs ms w := by
  simp [RiscvSemantics.step, step_accesses, hf, decode_exec]

theorem step_of_fetch_ov (segs : List Segment) (ms : machine_state) (w : BitVec 32)
    (hf : fetch_word segs (ms_pc ms) = none)
    (hov : fetch_word_ov segs ms.ms_mem (ms_pc ms) = some w) :
    RiscvSemantics.step segs ms = decode_exec segs ms w := by
  simp [RiscvSemantics.step, step_accesses, hf, hov, decode_exec]

/-- Projecting access reports does not change the machine result. This bridge
lets instruction proofs use the same interpreter as lazy-page accounting. -/
theorem decode_exec_of_interp (segs : List Segment) (regs regs' : bvmap 5 word)
    (pc pc' : word) (m m' rom : word → Option byte) (w : BitVec 32) (i : instr)
    (hne : is_ecall w = false) (hd : decode_any w = some (i, 4))
    (hi : interp_eff segs
      (exec 4 i (core.Core regs bvmap_empty pc 0 none)) m =
      MachineOk (core.Core regs' bvmap_empty pc' 0 none, m')) :
    decode_exec segs (mkst regs pc m rom) w = MachineOk (mkst regs' pc' m' rom) := by
  unfold interp_eff at hi
  cases he : interp_eff_accesses segs
      (exec 4 i (core.Core regs bvmap_empty pc 0 none)) m with
  | MachineFault => rw [he] at hi; cases hi
  | MachineUnmodeled => rw [he] at hi; cases hi
  | MachineOk report =>
    have hv : report.access_value = (core.Core regs' bvmap_empty pc' 0 none, m') := by
      rw [he] at hi
      exact machine_result.MachineOk.inj hi
    simp only [decode_exec, decode_exec_accesses, mkst, hne, Bool.false_eq_true,
      ↓reduceIte, hd]
    have hfour : Z_to_bv 64 (4 : Int) = (4 : word) := by decide
    rw [hfour, he]
    simp only [hv, drop_access_report]

theorem interp_done (segs : List Segment) (c : core) (m : word → Option byte) :
    interp_eff segs (.EDone c) m = MachineOk (c, m) := rfl

theorem interp_load (segs : List Segment) (n : Nat) (a : word) (bs : List byte)
    (k : BitVec n → eff) (c : core) (m : word → Option byte)
    (hr : ov_read_bytes segs m a (width_bytes n) = some bs)
    (hk : k (bv_extract 0 n (le_bytes_to_word bs)) = .EDone c) :
    interp_eff segs (.ELoad n a k) m = MachineOk (c, m) := by
  simp [interp_eff, interp_eff_accesses, hr, hk, drop_access_report]

theorem interp_store (segs : List Segment) (n : Nat) (a : word) (v : BitVec n)
    (c : core) (m : word → Option byte)
    (hw : store_ok segs m a (width_bytes n) = true) :
    interp_eff segs (.EStore n a v (.EDone c)) m =
      MachineOk (c, write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v))) := by
  simp [interp_eff, interp_eff_accesses, hw, drop_access_report]

theorem store_ok_of_empty (segs : List Segment) (m : word → Option byte)
    (a : word) (n : Nat) :
    store_ok segs (fun _ => none) a n = true → store_ok segs m a n = true := by
  induction n generalizing a with
  | zero => simp [store_ok]
  | succ n ih =>
    intro h
    simp only [store_ok, wview] at h ⊢
    cases hm : m a with
    | some b =>
      apply ih
      split at h <;> simp_all
    | none =>
      split at h <;> simp_all

/-! ## The shared core the example proofs stand on

Ported from `theories/Common/PropExec.v` at
2cde689f94c086b868999970834b76a25616b94a, the lemmas `cat1024_ns`'s
`Proof.v` reaches (`Print All Dependencies` of its `strong_universal`,
ticket E-proof-library), with the Rocq statements.

Lean's model has no stdpp `bv_wrap`/`bv_swrap`: its words are `BitVec`,
and `bv_unsigned`/`bv_signed` read `toNat`/`toInt`.  The library's
statements are phrased over them, so `bv_wrap` and `bv_swrap` are defined
below with stdpp's meaning (`Z.modulo` is `Int.emod`, which agrees with it
at a positive modulus); `bv_wrap` takes its width as a `Nat` where stdpp's
takes an `N`.  `Z_to_bv_unsigned` / `bv_signed_swrap` are the two stdpp
facts connecting them to the model's words.  Proofs differ from Rocq's
wherever stdpp's bitvector lemmas have no core-Lean counterpart; no
statement does. -/

/-- stdpp's `bv_wrap n z`: `z` reduced into `[0, 2^n)`. -/
def bv_wrap (n : Nat) (z : Int) : Int := z % 2 ^ n

theorem Z_to_bv_unsigned (n : Nat) (z : Int) : bv_unsigned (Z_to_bv n z) = bv_wrap n z := by
  unfold bv_unsigned Z_to_bv bv_wrap
  rw [BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by
    have : (0 : Int) < ((2 ^ n : Nat) : Int) := by exact_mod_cast Nat.two_pow_pos n
    omega))]
  simp only [Int.natCast_pow, Int.cast_ofNat_Int]

theorem bv_wrap64_mod (z : Int) : bv_wrap 64 z = z % 2 ^ 64 := rfl

/-- `protected`: `Checks.Sys.Prelude.bv_eqb_refl` has the same name and, in
Lean, the same statement, and a file opening both namespaces would
otherwise read the bare name as ambiguous (Rocq settles the clash silently
by import order).  Of the two Rocq originals, `Common/PropExec.v`'s takes
the width implicit, as both Lean copies do; `Checks/Sys/Prelude.v`'s takes
it explicit. -/
protected theorem bv_eqb_refl {n : Nat} (a : BitVec n) : bv_eqb a a = true :=
  (bv_eqb_eq a a).2 rfl

theorem bv_eqb_neq {n : Nat} (a b : BitVec n) (hne : a ≠ b) : bv_eqb a b = false := by
  cases h : bv_eqb a b with
  | false => rfl
  | true => exact absurd ((bv_eqb_eq a b).1 h) hne

theorem u64_range (x : word) : 0 ≤ bv_unsigned x ∧ bv_unsigned x < 2 ^ 64 := by
  unfold bv_unsigned
  have := x.isLt
  omega

def v_addi (x : word) (imm : Int) : word := Z_to_bv 64 (bv_unsigned x + imm)
def v_add (x y : word) : word := Z_to_bv 64 (bv_unsigned x + bv_unsigned y)
def v_sub (x y : word) : word := Z_to_bv 64 (bv_unsigned x - bv_unsigned y)

def c_eq (x y : word) : Bool := bv_eqb x y
def c_lts (x y : word) : Bool := bv_lts x y
def c_ltu (x y : word) : Bool := bv_ltu x y

def btgt (pc : word) (imm : Int) : word := v_addi pc imm

/-- Two words are equal when their unsigned views are: the Lean spelling
of stdpp's `bv_eq`, the step every value bridge below starts with. -/
theorem bv_eq_of_unsigned {n : Nat} (a b : BitVec n) (h : bv_unsigned a = bv_unsigned b) :
    a = b := by
  unfold bv_unsigned at h
  exact BitVec.eq_of_toNat_eq (by exact_mod_cast h)

theorem b_npc4 (p : word) : p + Z_to_bv 64 4 = v_addi p 4 := by
  apply bv_eq_of_unsigned
  rw [v_addi, Z_to_bv_unsigned, bv_wrap]
  unfold bv_unsigned
  rw [BitVec.toNat_add]
  have h4 : (Z_to_bv 64 4).toNat = 4 := by decide
  rw [h4]
  omega

theorem v_sub_small (x y : word) (h : bv_unsigned y ≤ bv_unsigned x) :
    bv_unsigned (v_sub x y) = bv_unsigned x - bv_unsigned y := by
  unfold v_sub
  rw [Z_to_bv_unsigned, bv_wrap64_mod]
  have hx := u64_range x
  have hy := u64_range y
  exact Int.emod_eq_of_lt (by omega) (by omega)

def seg_rom (segs : List Segment) : word → Option byte :=
  fun addr => match memory_read segs addr 1 with
    | some (b :: _) => some b
    | _ => none

def rdn (segs : List Segment) (mem : word → Option byte) (a : word) (n : Nat) :
    Option (List byte) :=
  match n with
  | 0 => some []
  | n' + 1 =>
    match (match mem a with | some b => some b | none => seg_rom segs a) with
    | some b =>
      match rdn segs mem (a + 1) n' with
      | some rest => some (b :: rest)
      | none => none
    | none => none

theorem rdn_ext (segs : List Segment) (k : Nat) (m1 m2 : word → Option byte) (a : word)
    (hnw : bv_unsigned a + (k : Int) ≤ 2 ^ 64)
    (hext : ∀ x : word, bv_unsigned a ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned a + (k : Int) →
      m1 x = m2 x) :
    rdn segs m1 a k = rdn segs m2 a k := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    have ha := u64_range a
    have h0 : m1 a = m2 a := hext a ⟨Int.le_refl _, by omega⟩
    cases k with
    | zero => simp only [rdn, h0]
    | succ k' =>
      have hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1 := u_add1 a (by omega)
      have hrest := ih (a + 1) (by omega) (by
        intro x hx
        apply hext
        omega)
      simp only [rdn, h0] at hrest ⊢
      rw [hrest]

/-! ## Value bridges and per-instruction step lemmas

The value shapes, the bridges from the bitvector expressions `Sem.exec`
produces to them, and the per-instruction `step_*` lemmas of
`theories/Common/PropExec.v`, with the Rocq statements.

Core Lean 4.34 has no `Z.land`, `Z.testbit`, `Z.shiftl` at an integer
amount, `Z.pow` at an integer exponent, nor stdpp's `bv_modulus`,
`bv_half_modulus`, `bv_swrap`.  They are defined first below as `Z_land`,
`Z_testbit`, `Z_shiftl`, `Z_pow`, `bv_modulus`, `bv_half_modulus` and
`bv_swrap`, each with the Rocq meaning on every argument, negative integer
operands included, and the ported statements use those spellings.  The
three stdpp functions take their width as a `Nat` where stdpp takes an `N`,
so only `bv_swrap`'s integer argument can be negative.  The `example`s
after the definitions check every arm of each definition, and each width
function at 0, against the values Rocq's stdlib and stdpp compute; a
second group adds, for each wrong reading of a twin that its comments
name, a point at which that reading gives another value.  They are tests,
not a proof: a wrong reading that agrees with Rocq at every one of these
points passes them all.  A LITERAL exponent (`2 ^ 64`) stays Lean's `^`,
which agrees with `Z.pow` there.  Rocq's
`bv_concat 32 imm (Z_to_bv 12 0)` is `bv_concat imm (Z_to_bv 12 0)`: the
Lean `bv_concat` computes its result width (`Riscv/Prelude.lean`).

Rocq's `step_pipeline` Ltac unfolds `step` by `cbv`; the Lean
`step_pipeline` macro instead applies the Lean-only `step_exec` (built on
`step_of_fetch` and `decode_exec_of_interp`), leaving the interpreter goal
for the decoded instruction, which each lemma closes by rewriting. -/

/-! ### Lean-core twins -/

/-- Rocq's `Z.pow` at an integer exponent: `x ^ k` for an exponent `k ≥ 0`
and `0` for a negative one, stdlib's `Zneg _ => 0` arm. -/
def Z_pow (x y : Int) : Int :=
  match y with
  | .ofNat k => x ^ k
  | .negSucc _ => 0

/-- Rocq's `Z.land`: bitwise and of the infinite two's-complement readings
of both operands.  Stdlib's definition has six arms: its two zero arms fall
into the arms here with an `.ofNat 0` operand, which answer 0 there too, and
each of its other four is one of these four.  `Int.negSucc n` is
`-(n+1)`, whose bits are the complement of `n`'s, so a non-negative `a`
against a negative `-(b+1)` is `N.ldiff a b`, written `a - (a &&& b)` (the
bits of `a &&& b` are a subset of `a`'s, so the subtraction borrows
nowhere), and two negatives give the complement of the `lor` of the
complements. -/
def Z_land (a b : Int) : Int :=
  match a, b with
  | .ofNat a, .ofNat b => .ofNat (a &&& b)
  | .ofNat a, .negSucc b => .ofNat (a - (a &&& b))
  | .negSucc a, .ofNat b => .ofNat (b - (b &&& a))
  | .negSucc a, .negSucc b => .negSucc (a ||| b)

/-- Rocq's `Z.testbit a k`: bit `k` of the two's-complement reading of `a`
(a negative `-(n+1)` reads as the complement of `n`); `false` at a negative
index, stdlib's `neg _ => false` arm. -/
def Z_testbit (a k : Int) : Bool :=
  match k with
  | .negSucc _ => false
  | .ofNat k =>
    match a with
    | .ofNat a => a.testBit k
    | .negSucc a => !(a.testBit k)

/-- Rocq's `Z.shiftl a n` at an integer amount: a non-negative `n` multiplies
by `2 ^ n`, a negative one is the floor shift right by `-n` (stdlib iterates
`Z.div2`, which rounds toward minus infinity, as `Int`'s `>>>` does). -/
def Z_shiftl (a n : Int) : Int :=
  match n with
  | .ofNat k => a <<< k
  | .negSucc k => a >>> (k + 1)

/-- stdpp's `bv_modulus n`: `2 ^ n`. -/
def bv_modulus (n : Nat) : Int := 2 ^ n

/-- stdpp's `bv_half_modulus n`: `bv_modulus n / 2` (both readings of `/`
agree on these non-negative operands). -/
def bv_half_modulus (n : Nat) : Int := bv_modulus n / 2

/-- stdpp's `bv_swrap n z`: `z` reduced into `[-2^(n-1), 2^(n-1))`. -/
def bv_swrap (n : Nat) (z : Int) : Int :=
  bv_wrap n (z + bv_half_modulus n) - bv_half_modulus n

-- The twins at every arm, against the values Rocq's stdlib (`Z.land`,
-- `Z.testbit`, `Z.shiftl`, `Z.pow`) and stdpp (`bv_modulus`,
-- `bv_half_modulus`, `bv_swrap`) compute.
example : Z_land 6 3 = 2 := by decide
example : Z_land (-6) 3 = 2 := by decide
example : Z_land 6 (-3) = 4 := by decide
example : Z_land (-6) (-3) = -8 := by decide
example : Z_testbit 5 2 = true := by decide
example : Z_testbit (-2) 0 = false := by decide
example : Z_testbit (-2) 100 = true := by decide
example : Z_testbit 5 (-1) = false := by decide
example : Z_shiftl (-5) (-1) = -3 := by decide
example : Z_shiftl 3 2 = 12 := by decide
example : Z_shiftl (-5) 2 = -20 := by decide
example : Z_pow 2 (-1) = 0 := by decide
example : Z_pow (-2) 3 = -8 := by decide
example : bv_modulus 0 = 1 := by decide
example : bv_half_modulus 0 = 0 := by decide
example : bv_half_modulus 8 = 128 := by decide
example : bv_swrap 0 5 = 0 := by decide
example : bv_swrap 8 (-400) = 112 := by decide
example : bv_swrap 8 200 = -56 := by decide
example : bv_swrap 8 100 = 100 := by decide
example : bv_swrap 8 (-129) = 127 := by decide
example : bv_swrap 8 (-128) = -128 := by decide
example : bv_swrap 8 (-1) = -1 := by decide
example : bv_swrap 8 128 = -128 := by decide
-- The second group.  Under each comment, for every wrong reading of a
-- twin the comment names, a point at which that reading gives another
-- value than Rocq's.  The values are again Rocq's.
-- `Z_pow` at a negative exponent: the reciprocal `1 / x ^ |y|`, in `Int`
-- or in `Nat` through `toNat`, or 1 wherever `x ^ |y|` is 1.
example : Z_pow (-1) (-1) = 0 := by decide
example : Z_pow 1 (-1) = 0 := by decide
-- `Z_pow` at a non-negative exponent: 0 at exponent 0, or at base 0
-- (`0 ^ 0` among them); and the base's sign kept, at exponent 0 or at a
-- positive even one.
example : Z_pow (-3) 0 = 1 := by decide
example : Z_pow 0 0 = 1 := by decide
example : Z_pow (-2) 2 = 4 := by decide
-- `Z_land`: `xor` or a `Nat` difference for the (+,-) arm's and-not; in
-- either mixed arm, the negative operand read as its magnitude, as the
-- complement of its magnitude, or as its two's complement within 64 or
-- 128 bits; `xor`, a sum or a forced low bit for the (-,-) arm's `or`;
-- and the (+,+) arm truncated to 64 bits.
example : Z_land (2 ^ 64 + 5) (-3) = 2 ^ 64 + 5 := by decide
example : Z_land (-1) (2 ^ 64 + 3) = 2 ^ 64 + 3 := by decide
example : Z_land (2 ^ 128) (-1) = 2 ^ 128 := by decide
example : Z_land (-1) (2 ^ 128) = 2 ^ 128 := by decide
example : Z_land (-4) (-6) = -8 := by decide
example : Z_land (-1) (-1) = -1 := by decide
example : Z_land (2 ^ 64) (2 ^ 64) = 2 ^ 64 := by decide
-- `Z_testbit` at a negative index: a bit of the operand for `false` --
-- the bit the index's `natAbs` names, or bit 0, on operands of either sign
-- or of both; the sign; and, for an operand `-(n+1)`, bit 0 of `n`.
example : Z_testbit (-1) (-1) = false := by decide
example : Z_testbit (-2) (-1) = false := by decide
example : Z_testbit 5 (-2) = false := by decide
-- `Z_shiftl`: a multiplier `k ^ 2` for `2 ^ k`, and either shift amount
-- taken mod 64.
example : Z_shiftl 5 3 = 40 := by decide
example : Z_shiftl 1 64 = 2 ^ 64 := by decide
example : Z_shiftl (-5) (-64) = -1 := by decide
-- The width functions: a width wrapped at 64 -- in `bv_swrap`, at any of
-- its three uses -- and `bv_modulus`'s wrapped at 128 too; and
-- `bv_half_modulus` 0 at width 1.
example : bv_modulus 64 = 2 ^ 64 := by decide
example : bv_modulus 128 = 2 ^ 128 := by decide
example : bv_half_modulus 1 = 1 := by decide
example : bv_half_modulus 64 = 2 ^ 63 := by decide
example : bv_swrap 64 (-1) = -1 := by decide

/-! ### Conversion and bitvector helpers -/

theorem bv_eqb0_is_x0 (r : reg) : bv_eqb r 0 = is_x0 r := by
  unfold bv_eqb is_x0
  by_cases h : r = 0
  · subst h; rfl
  · have h' : r.toNat ≠ 0 := fun hn => h (BitVec.eq_of_toNat_eq (by rw [hn]; rfl))
    rw [beq_eq_false_iff_ne.mpr h, decide_eq_false h']

theorem is_x0_0 : is_x0 0 = true := rfl

/-- Lean-only helper: stdpp's `bv_add_unsigned`, on `BitVec`. -/
theorem bv_unsigned_add {n : Nat} (a b : BitVec n) :
    bv_unsigned (a + b) = bv_wrap n (bv_unsigned a + bv_unsigned b) := by
  unfold bv_unsigned bv_wrap
  rw [BitVec.toNat_add]
  rfl

/-- Lean-only helper: stdpp's `bv_sub_unsigned`, on `BitVec`. -/
theorem bv_unsigned_sub {n : Nat} (a b : BitVec n) :
    bv_unsigned (a - b) = bv_wrap n (bv_unsigned a - bv_unsigned b) := by
  unfold bv_unsigned bv_wrap
  rw [BitVec.toNat_sub]
  have hb := b.isLt
  have hP : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by
    rw [Int.natCast_pow, Int.cast_ofNat_Int]
  rw [Int.natCast_emod, Int.natCast_add, Int.natCast_sub (Nat.le_of_lt hb), hP]
  have h : (2 : Int) ^ n - b.toNat + a.toNat = (a.toNat - b.toNat) + 2 ^ n := by omega
  rw [h, Int.add_emod_right]

/-- Lean-only helper: sign extension is the wrap of the signed reading
(stdpp's `bv_sign_extend_unsigned`; definitional here). -/
theorem sext_eq {n : Nat} (m : Nat) (b : BitVec n) : sext m b = Z_to_bv m (bv_signed b) := rfl

/-- Lean-only helper: stdpp's `bv_and_unsigned`, on `BitVec`. -/
theorem bv_unsigned_and {n : Nat} (a b : BitVec n) :
    bv_unsigned (bv_and a b) = Z_land (bv_unsigned a) (bv_unsigned b) := by
  unfold bv_unsigned bv_and
  rw [BitVec.toNat_and]
  rfl

/-! ### Value shapes and bridges -/

def v_slli (x : word) (sh : Int) : word := Z_to_bv 64 (Z_shiftl (bv_unsigned x) sh)

/-- Upper immediates: `imm` is the ALREADY-SHIFTED signed U-immediate. -/
def v_lui (imm : Int) : word := Z_to_bv 64 imm
def v_auipc (pc : word) (imm : Int) : word := Z_to_bv 64 (imm + bv_unsigned pc)

def v_lw (v : word) : word := Z_to_bv 64 (bv_swrap 32 (bv_unsigned v))

/-- jalr target: `(rs1 + imm)` with bit 0 cleared. -/
def jalr_tgtZ (x : word) (imm : Int) : Int := Z_land (bv_unsigned x + imm) (-2)
def jalr_tgt (x : word) (imm : Int) : word := Z_to_bv 64 (jalr_tgtZ x imm)

theorem b_addsext (a : word) {n : Nat} (imm : BitVec n) :
    a + sext 64 imm = v_addi a (bv_signed imm) := by
  apply bv_eq_of_unsigned
  rw [v_addi, Z_to_bv_unsigned, bv_unsigned_add, sext_eq, Z_to_bv_unsigned]
  unfold bv_wrap
  rw [Int.add_emod_emod]

theorem alu_addi (a : word) {n : Nat} (imm : BitVec n) :
    alu64 .ALU_ADD a (sext 64 imm) = v_addi a (bv_signed imm) :=
  b_addsext a imm

theorem alu_add (a b : word) : alu64 .ALU_ADD a b = v_add a b := by
  apply bv_eq_of_unsigned
  rw [v_add, Z_to_bv_unsigned]
  exact bv_unsigned_add a b

theorem alu_sub (a b : word) : alu64 .ALU_SUB a b = v_sub a b := by
  apply bv_eq_of_unsigned
  rw [v_sub, Z_to_bv_unsigned]
  exact bv_unsigned_sub a b

/-- Lean-only helper: setting bit 0 of a natural number. -/
theorem nat_or_one (m : Nat) : m ||| 1 = 2 * (m / 2) + 1 := by
  have hm : m = 2 ^ 1 * (m / 2) ||| m % 2 := by
    rw [← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (by decide))]
    omega
  have hr : m % 2 ||| 1 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one m with h | h <;> rw [h] <;> rfl
  have h1 := Nat.two_pow_add_eq_or_of_lt (i := 1) (b := 1) (by decide) (m / 2)
  calc m ||| 1 = (2 ^ 1 * (m / 2) ||| m % 2) ||| 1 := by rw [← hm]
    _ = 2 ^ 1 * (m / 2) ||| (m % 2 ||| 1) := Nat.or_assoc _ _ _
    _ = 2 * (m / 2) + 1 := by rw [hr, ← h1, Nat.pow_one]

/-- Lean-only helper: masking with `-2` clears bit 0, on every integer. -/
theorem Z_land_m2 (z : Int) : Z_land z (-2) = z - z % 2 := by
  cases z with
  | ofNat n =>
    show ((n - (n &&& 1) : Nat) : Int) = (n : Int) - (n : Int) % 2
    rw [Nat.and_one_is_mod]
    omega
  | negSucc m =>
    show Int.negSucc (m ||| 1) = Int.negSucc m - Int.negSucc m % 2
    rw [nat_or_one, Int.negSucc_eq, Int.negSucc_eq]
    omega

/-- Lean-only helper: the 64-bit mask `2^64 - 2` clears bit 0 of a value
below `2^64`. -/
theorem nat_land_m2_64 (p : Nat) (hp : p < 2 ^ 64) : p &&& (2 ^ 64 - 2) = p - p % 2 := by
  apply Nat.eq_of_testBit_eq
  intro j
  have h1 : 2 ^ 64 - 2 = 2 ^ 1 * (2 ^ 63 - 1) + 0 := by decide
  have h2 : p - p % 2 = 2 ^ 1 * (p / 2) + 0 := by omega
  have h4 : p.testBit j = (2 ^ 1 * (p / 2) + p % 2).testBit j := by
    rw [← (by omega : p = 2 ^ 1 * (p / 2) + p % 2)]
  rw [Nat.testBit_and, h1, h2, h4,
    Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (by decide)) j,
    Nat.testBit_two_pow_mul_add _ (by decide : 0 < 2 ^ 1) j,
    Nat.testBit_two_pow_mul_add _ (by decide : 0 < 2 ^ 1) j]
  by_cases hj : j < 1
  · simp only [hj, ↓reduceIte, Nat.zero_testBit, Bool.and_false]
  · simp only [hj, ↓reduceIte, Nat.testBit_two_pow_sub_one]
    by_cases hk : j - 1 < 63
    · simp only [hk, decide_true, Bool.and_true]
    · have h63 : p / 2 < 2 ^ 63 := by omega
      have hlt : p / 2 < 2 ^ (j - 1) :=
        Nat.lt_of_lt_of_le h63 (Nat.pow_le_pow_right (by decide) (by omega))
      rw [Nat.testBit_lt_two_pow hlt, Bool.false_and]

theorem Z_land_m2_wrap (z : Int) :
    Z_land (bv_wrap 64 z) (bv_wrap 64 (-2)) = bv_wrap 64 (Z_land z (-2)) := by
  have hm2 : bv_wrap 64 (-2) = ((2 ^ 64 - 2 : Nat) : Int) := by decide
  have hnn : 0 ≤ bv_wrap 64 z := Int.emod_nonneg _ (by decide)
  have hlt : bv_wrap 64 z < 2 ^ 64 := Int.emod_lt_of_pos _ (by decide)
  obtain ⟨p, hp⟩ : ∃ p : Nat, bv_wrap 64 z = (p : Int) :=
    ⟨_, (Int.toNat_of_nonneg hnn).symm⟩
  rw [hm2, hp, Z_land_m2 z]
  have hp64 : p < 2 ^ 64 := by omega
  show ((p &&& (2 ^ 64 - 2) : Nat) : Int) = _
  rw [nat_land_m2_64 p hp64]
  unfold bv_wrap at hp ⊢
  omega

theorem b_jalr (a : word) (imm : BitVec 12) :
    bv_and (a + sext 64 imm) (bv_not (Z_to_bv 64 1)) = jalr_tgt a (bv_signed imm) := by
  rw [b_addsext]
  apply bv_eq_of_unsigned
  rw [bv_unsigned_and, jalr_tgt, jalr_tgtZ, v_addi, Z_to_bv_unsigned, Z_to_bv_unsigned]
  have hm : bv_unsigned (bv_not (Z_to_bv 64 1)) = bv_wrap 64 (-2) := by decide
  rw [hm]
  exact Z_land_m2_wrap _

/-! ### Step pipeline -/

/-- Lean-only helper: `Sem.rget` on a core built from a register map is
`getr` on the map. -/
theorem rget_mk (regs fr : bvmap 5 word) (pc : word) (fc : BitVec 32) (rv : Option word)
    (r : reg) : rget (core.Core regs fr pc fc rv) r = getr regs r := by
  unfold rget getr
  rw [bv_eqb0_is_x0]
  rfl

/-- Lean-only helper: `Sem.rset` on a core built from a register map. -/
theorem rset_mk (rd : reg) (v : word) (regs fr : bvmap 5 word) (pc : word) (fc : BitVec 32)
    (rv : Option word) :
    rset rd v (core.Core regs fr pc fc rv) =
      core.Core (if bv_eqb rd 0 then regs else regupd regs rd v) fr pc fc rv := by
  unfold rset
  rw [bv_eqb0_is_x0]
  cases is_x0 rd <;> rfl

/-- Lean-only helper: `b_npc4` at the literal `decode_exec_of_interp` leaves. -/
theorem npc4 (pc : word) : pc + (4 : word) = v_addi pc 4 := b_npc4 pc

/-- Lean-only helper: a step of `mkst regs pc mem rom` whose word is fetched
from the static image, is no ecall and decodes at size 4 is the interpreter's
answer on that instruction's effect tree. -/
theorem step_exec (segs : List Segment) (regs regs' : bvmap 5 word) (pc pc' : word)
    (mem mem' rom : word → Option byte) (w : BitVec 32) (i : instr)
    (hf : fetch_word segs pc = some w) (hne : is_ecall w = false)
    (hd : decode_any w = some (i, 4))
    (hi : interp_eff segs (exec 4 i (core.Core regs bvmap_empty pc 0 none)) mem =
      MachineOk (core.Core regs' bvmap_empty pc' 0 none, mem')) :
    RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs' pc' mem' rom) :=
  (step_of_fetch segs (mkst regs pc mem rom) w hf).trans
    (decode_exec_of_interp segs regs regs' pc pc' mem mem' rom w i hne hd hi)

/-- The Lean counterpart of Rocq's `step_pipeline Hfetch Hecall Hdecode`:
reduces a `step` goal of the `step_*` shape to the interpreter goal on the
decoded instruction's effect tree. -/
macro "step_pipeline" hf:term:max he:term:max hd:term:max : tactic =>
  `(tactic| refine step_exec _ _ _ _ _ _ _ _ _ _ $hf $he $hd ?_)

/-! ### Per-instruction step lemmas -/

/-- A probe for the pipeline: OpImm, generic in the aluop. -/
theorem step_opimm_gen (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : aluop) (rd rs : reg)
    (imm : BitVec 12)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.OpImm op rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
                      (v_addi pc 4) mem rom) := by
  step_pipeline hf he hd
  show MachineOk (rset rd (alu64 op (rget (core.Core regs bvmap_empty pc 0 none) rs)
      (sext 64 imm)) (core.Core regs bvmap_empty (pc + 4) 0 none), mem) = _
  rw [rget_mk, npc4, rset_mk]

theorem step_op_gen (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : aluop) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Op op rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  step_pipeline hf he hd
  show MachineOk (rset rd (alu64 op (rget (core.Core regs bvmap_empty pc 0 none) rs1)
      (rget (core.Core regs bvmap_empty pc 0 none) rs2))
      (core.Core regs bvmap_empty (pc + 4) 0 none), mem) = _
  rw [rget_mk, rget_mk, npc4, rset_mk]

theorem step_addi (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.OpImm .ALU_ADD rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_addi (getr regs rs) (bv_signed imm)))
                      (v_addi pc 4) mem rom) := by
  rw [step_opimm_gen segs regs pc mem rom w .ALU_ADD rd rs imm hf he hd, alu_addi]

theorem step_add (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Op .ALU_ADD rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_add (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w .ALU_ADD rd rs1 rs2 hf he hd, alu_add]

theorem step_sub (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Op .ALU_SUB rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_sub (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w .ALU_SUB rd rs1 rs2 hf he hd, alu_sub]

/-- General Jalr: rd := pc + 4 (unless rd = x0), jump to the masked target.
No alignment side condition (the ISA model has no check). -/
theorem step_jalr_gen (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 : reg) (imm : BitVec 12)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Jalr rd rs1 imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
                      (jalr_tgt (getr regs rs1) (bv_signed imm)) mem rom) := by
  step_pipeline hf he hd
  show MachineOk (rset rd (pc + 4) (core.Core regs bvmap_empty
      (bv_and (rget (core.Core regs bvmap_empty pc 0 none) rs1 + sext 64 imm)
        (bv_not (Z_to_bv 64 1))) 0 none), mem) = _
  rw [rget_mk, npc4, b_jalr, rset_mk]

theorem bv_wrap32_mod (z : Int) : bv_wrap 32 z = z % 2 ^ 32 := rfl

theorem u6_range (s : BitVec 6) : 0 ≤ bv_unsigned s ∧ bv_unsigned s < 64 := by
  unfold bv_unsigned
  have := s.isLt
  omega

theorem u5_range (s : BitVec 5) : 0 ≤ bv_unsigned s ∧ bv_unsigned s < 32 := by
  unfold bv_unsigned
  have := s.isLt
  omega

/-- Lean-only helper: stdpp's `bv_signed` is `bv_swrap` of the unsigned
reading, by definition in stdpp; here `bv_signed` is `BitVec.toInt`. -/
theorem bv_signed_swrap {n : Nat} (b : BitVec n) : bv_signed b = bv_swrap n (bv_unsigned b) := by
  unfold bv_signed bv_swrap bv_half_modulus bv_modulus bv_wrap bv_unsigned
  rw [BitVec.toInt_eq_toNat_cond]
  have hb := b.isLt
  cases n with
  | zero =>
    have h0 : b.toNat = 0 := by omega
    rw [h0]
    decide
  | succ k =>
    obtain ⟨P, hPdef⟩ : ∃ P : Nat, P = 2 ^ k := ⟨_, rfl⟩
    have hPpos : 0 < P := hPdef ▸ Nat.two_pow_pos k
    have hN : 2 ^ (k + 1) = 2 * P := by rw [Nat.pow_succ, hPdef, Nat.mul_comm]
    have hI : (2 : Int) ^ (k + 1) = 2 * (P : Int) := by
      have hc : ((2 ^ (k + 1) : Nat) : Int) = (2 : Int) ^ (k + 1) := by
        rw [Int.natCast_pow, Int.cast_ofNat_Int]
      rw [← hc, hN, Int.natCast_mul, Int.cast_ofNat_Int]
    rw [hN] at hb ⊢
    rw [hI]
    have hh : (2 * (P : Int)) / 2 = P := by omega
    rw [hh, Int.natCast_mul, Int.cast_ofNat_Int]
    split
    · rename_i h
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
      omega
    · rename_i h
      rw [show (b.toNat : Int) + P = ((b.toNat : Int) + P - 2 * P) + 2 * P by omega,
        Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
      omega

theorem shamt6_mask (s : BitVec 6) :
    bv_unsigned (bv_and (zext 64 s) (Z_to_bv 64 63)) = bv_unsigned s := by
  unfold bv_unsigned bv_and
  have hz : (zext 64 s).toNat = s.toNat :=
    BitVec.toNat_setWidth_of_le (w' := 64) (b := s) (by decide)
  have h63 : (Z_to_bv 64 63).toNat = 2 ^ 6 - 1 := by decide
  rw [BitVec.toNat_and, hz, h63, Nat.and_two_pow_sub_one_eq_mod]
  have := s.isLt
  rw [Nat.mod_eq_of_lt this]

theorem alu_slli (a : word) (s : BitVec 6) :
    alu64 .ALU_SLL a (zext 64 s) = v_slli a (bv_unsigned s) := by
  apply bv_eq_of_unsigned
  have hm : (bv_and (zext 64 s) (Z_to_bv 64 63)).toNat = s.toNat := by
    have h := shamt6_mask s
    unfold bv_unsigned at h
    exact_mod_cast h
  show bv_unsigned (a <<< (bv_and (zext 64 s) (Z_to_bv 64 63)).toNat) = _
  rw [hm, v_slli, Z_to_bv_unsigned]
  unfold bv_unsigned bv_wrap
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  show _ = ((a.toNat : Int) <<< s.toNat) % 2 ^ 64
  rw [Int.shiftLeft_eq]
  norm_cast

theorem sext32_unsigned (v : BitVec 32) :
    bv_unsigned (sext 64 v) = bv_wrap 64 (bv_swrap 32 (bv_unsigned v)) := by
  rw [sext_eq, Z_to_bv_unsigned, bv_signed_swrap]

theorem bv_swrap_hi (n : Nat) (z : Int) (hn : n ≠ 0) (hlo : bv_half_modulus n ≤ z)
    (hhi : z < bv_modulus n) : bv_swrap n z = z - bv_modulus n := by
  unfold bv_swrap bv_wrap
  unfold bv_half_modulus at hlo ⊢
  unfold bv_modulus at hlo hhi ⊢
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hI : (2 : Int) ^ (k + 1) = 2 * 2 ^ k := by rw [Int.pow_succ, Int.mul_comm]
  have hpos : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
  rw [hI] at hlo hhi ⊢
  generalize (2 : Int) ^ k = P at hlo hhi hpos ⊢
  have hh : (2 * P) / 2 = P := by omega
  rw [hh] at hlo ⊢
  rw [show z + P = (z + P - 2 * P) + 2 * P by omega, Int.add_emod_right,
    Int.emod_eq_of_lt (by omega) (by omega)]
  omega

theorem b_lui (imm : BitVec 20) :
    sext 64 (bv_concat imm (Z_to_bv 12 0)) = v_lui (Z_shiftl (bv_signed imm) 12) := by
  have hz : Z_to_bv 12 0 = 0#12 := by decide
  unfold v_lui bv_concat
  rw [sext_eq, hz]
  congr 1
  unfold bv_signed
  rw [BitVec.toInt_append_zero]
  show 2 ^ 12 * imm.toInt = imm.toInt <<< 12
  rw [Int.shiftLeft_eq, Int.mul_comm]
  rfl

theorem b_auipc (p : word) (imm : BitVec 20) :
    p + sext 64 (bv_concat imm (Z_to_bv 12 0)) = v_auipc p (Z_shiftl (bv_signed imm) 12) := by
  rw [b_lui]
  apply bv_eq_of_unsigned
  rw [bv_unsigned_add, v_lui, v_auipc, Z_to_bv_unsigned, Z_to_bv_unsigned]
  unfold bv_wrap
  rw [Int.add_emod_emod, Int.add_comm]

theorem v_slli_3 (x : word) (h8 : 8 * bv_unsigned x < 2 ^ 64) :
    bv_unsigned (v_slli x 3) = 8 * bv_unsigned x := by
  unfold v_slli
  rw [Z_to_bv_unsigned, bv_wrap64_mod]
  rw [show Z_shiftl (bv_unsigned x) 3 = bv_unsigned x <<< 3 from rfl, Int.shiftLeft_eq]
  have hx := u64_range x
  have h : bv_unsigned x * 2 ^ 3 = 8 * bv_unsigned x := by omega
  rw [h]
  exact Int.emod_eq_of_lt (by omega) h8

theorem step_shiftimm_gen (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : aluop) (rd rs : reg)
    (sh : BitVec 6)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.ShiftImm op rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (alu64 op (getr regs rs) (zext 64 sh)))
                      (v_addi pc 4) mem rom) := by
  step_pipeline hf he hd
  show MachineOk (rset rd (alu64 op (rget (core.Core regs bvmap_empty pc 0 none) rs)
      (zext 64 sh)) (core.Core regs bvmap_empty (pc + 4) 0 none), mem) = _
  rw [rget_mk, npc4, rset_mk]

theorem step_opimm32_gen (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.OpImm32 rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd
                         (sext 64 (alu32 .ALU_ADD (low32 (getr regs rs)) (sext 32 imm))))
                      (v_addi pc 4) mem rom) := by
  step_pipeline hf he hd
  show MachineOk (rset rd (sext 64 (alu32 .ALU_ADD
      (low32 (rget (core.Core regs bvmap_empty pc 0 none) rs)) (sext 32 imm)))
      (core.Core regs bvmap_empty (pc + 4) 0 none), mem) = _
  rw [rget_mk, npc4, rset_mk]

theorem step_shiftimm32_gen (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : aluop) (rd rs : reg)
    (sh : BitVec 5)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.ShiftImm32 op rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd
                         (sext 64 (alu32 op (low32 (getr regs rs)) (zext 32 sh))))
                      (v_addi pc 4) mem rom) := by
  step_pipeline hf he hd
  show MachineOk (rset rd (sext 64 (alu32 op
      (low32 (rget (core.Core regs bvmap_empty pc 0 none) rs)) (zext 32 sh)))
      (core.Core regs bvmap_empty (pc + 4) 0 none), mem) = _
  rw [rget_mk, npc4, rset_mk]

theorem step_op32_gen (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : aluop) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Op32 op rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd
                         (sext 64 (alu32 op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
                      (v_addi pc 4) mem rom) := by
  step_pipeline hf he hd
  show MachineOk (rset rd (sext 64 (alu32 op
      (low32 (rget (core.Core regs bvmap_empty pc 0 none) rs1))
      (low32 (rget (core.Core regs bvmap_empty pc 0 none) rs2))))
      (core.Core regs bvmap_empty (pc + 4) 0 none), mem) = _
  rw [rget_mk, rget_mk, npc4, rset_mk]

theorem step_mul_gen (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : mulop) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Mul op rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (mul_div op (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  step_pipeline hf he hd
  show MachineOk (rset rd (mul_div op (rget (core.Core regs bvmap_empty pc 0 none) rs1)
      (rget (core.Core regs bvmap_empty pc 0 none) rs2))
      (core.Core regs bvmap_empty (pc + 4) 0 none), mem) = _
  rw [rget_mk, rget_mk, npc4, rset_mk]

theorem step_mul32_gen (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : mulop) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Mul32 op rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd
                         (sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
                      (v_addi pc 4) mem rom) := by
  step_pipeline hf he hd
  show MachineOk (rset rd (sext 64 (mul_div op
      (low32 (rget (core.Core regs bvmap_empty pc 0 none) rs1))
      (low32 (rget (core.Core regs bvmap_empty pc 0 none) rs2))))
      (core.Core regs bvmap_empty (pc + 4) 0 none), mem) = _
  rw [rget_mk, rget_mk, npc4, rset_mk]

/-- Generic branch step lemmas: taken and fall-through. -/
theorem step_branch_tk_gen (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (c : branch_cond) (rs1 rs2 : reg)
    (imm : BitVec 13)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Branch c rs1 rs2 imm, 4))
    (hc : branch_taken c (getr regs rs1) (getr regs rs2) = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom) := by
  step_pipeline hf he hd
  show MachineOk (core.Core regs bvmap_empty
      (if branch_taken c (rget (core.Core regs bvmap_empty pc 0 none) rs1)
          (rget (core.Core regs bvmap_empty pc 0 none) rs2)
       then pc + sext 64 imm else pc + 4) 0 none, mem) = _
  rw [rget_mk, rget_mk, hc, ite_eq_left rfl, b_addsext]
  rfl

theorem step_branch_ft_gen (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (c : branch_cond) (rs1 rs2 : reg)
    (imm : BitVec 13)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Branch c rs1 rs2 imm, 4))
    (hc : branch_taken c (getr regs rs1) (getr regs rs2) = false) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (v_addi pc 4) mem rom) := by
  step_pipeline hf he hd
  show MachineOk (core.Core regs bvmap_empty
      (if branch_taken c (rget (core.Core regs bvmap_empty pc 0 none) rs1)
          (rget (core.Core regs bvmap_empty pc 0 none) rs2)
       then pc + sext 64 imm else pc + 4) 0 none, mem) = _
  rw [rget_mk, rget_mk, hc, ite_eq_right Bool.false_ne_true, npc4]

theorem step_slli (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (sh : BitVec 6)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.ShiftImm .ALU_SLL rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_slli (getr regs rs) (bv_unsigned sh)))
                      (v_addi pc 4) mem rom) := by
  rw [step_shiftimm_gen segs regs pc mem rom w .ALU_SLL rd rs sh hf he hd, alu_slli]

theorem step_beq_tk (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 13)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Branch .BC_EQ rs1 rs2 imm, 4))
    (hc : c_eq (getr regs rs1) (getr regs rs2) = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom) :=
  step_branch_tk_gen segs regs pc mem rom w .BC_EQ rs1 rs2 imm hf he hd hc

theorem step_beq_ft (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 13)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Branch .BC_EQ rs1 rs2 imm, 4))
    (hc : c_eq (getr regs rs1) (getr regs rs2) = false) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (v_addi pc 4) mem rom) :=
  step_branch_ft_gen segs regs pc mem rom w .BC_EQ rs1 rs2 imm hf he hd hc

/-- Bne taken <=> `c_eq rs1 rs2 = false`; fall-through <=> `= true`. -/
theorem step_bne_tk (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 13)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Branch .BC_NE rs1 rs2 imm, 4))
    (hc : c_eq (getr regs rs1) (getr regs rs2) = false) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom) := by
  apply step_branch_tk_gen segs regs pc mem rom w .BC_NE rs1 rs2 imm hf he hd
  show (!(bv_eqb (getr regs rs1) (getr regs rs2))) = true
  rw [show bv_eqb (getr regs rs1) (getr regs rs2) = false from hc]
  rfl

theorem step_bne_ft (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 13)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Branch .BC_NE rs1 rs2 imm, 4))
    (hc : c_eq (getr regs rs1) (getr regs rs2) = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (v_addi pc 4) mem rom) := by
  apply step_branch_ft_gen segs regs pc mem rom w .BC_NE rs1 rs2 imm hf he hd
  show (!(bv_eqb (getr regs rs1) (getr regs rs2))) = false
  rw [show bv_eqb (getr regs rs1) (getr regs rs2) = true from hc]
  rfl

/-- Blt is the signed `<`; "false" = not-less = fall-through to pc+4. -/
theorem step_blt_ft (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 13)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Branch .BC_LT rs1 rs2 imm, 4))
    (hc : c_lts (getr regs rs1) (getr regs rs2) = false) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (v_addi pc 4) mem rom) :=
  step_branch_ft_gen segs regs pc mem rom w .BC_LT rs1 rs2 imm hf he hd hc

/-- Bge taken <=> `c_lts rs1 rs2 = false`; fall-through <=> `= true`. -/
theorem step_bge_ft (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 13)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Branch .BC_GE rs1 rs2 imm, 4))
    (hc : c_lts (getr regs rs1) (getr regs rs2) = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (v_addi pc 4) mem rom) := by
  apply step_branch_ft_gen segs regs pc mem rom w .BC_GE rs1 rs2 imm hf he hd
  show (!(bv_lts (getr regs rs1) (getr regs rs2))) = false
  rw [show bv_lts (getr regs rs1) (getr regs rs2) = true from hc]
  rfl

theorem step_bltu_ft (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 13)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Branch .BC_LTU rs1 rs2 imm, 4))
    (hc : c_ltu (getr regs rs1) (getr regs rs2) = false) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (v_addi pc 4) mem rom) :=
  step_branch_ft_gen segs regs pc mem rom w .BC_LTU rs1 rs2 imm hf he hd hc

/-- `imm` is the raw 20-bit U-immediate; the value shape takes the shifted
signed immediate (the "real" constant). -/
theorem step_lui (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd : reg) (imm : BitVec 20)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Lui rd imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_lui (Z_shiftl (bv_signed imm) 12)))
                      (v_addi pc 4) mem rom) := by
  step_pipeline hf he hd
  show MachineOk (rset rd (sext 64 (bv_concat imm (Z_to_bv 12 0)))
      (core.Core regs bvmap_empty (pc + 4) 0 none), mem) = _
  rw [b_lui, npc4, rset_mk]

theorem step_auipc (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd : reg) (imm : BitVec 20)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Auipc rd imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_auipc pc (Z_shiftl (bv_signed imm) 12)))
                      (v_addi pc 4) mem rom) := by
  step_pipeline hf he hd
  show MachineOk (rset rd (pc + sext 64 (bv_concat imm (Z_to_bv 12 0)))
      (core.Core regs bvmap_empty (pc + 4) 0 none), mem) = _
  rw [b_auipc, npc4, rset_mk]

theorem step_jal_x0 (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (imm : BitVec 21)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Jal 0 imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom) := by
  step_pipeline hf he hd
  show MachineOk (rset 0 (pc + 4) (core.Core regs bvmap_empty (pc + sext 64 imm) 0 none),
    mem) = _
  rw [rset_mk, PropExec.bv_eqb_refl, ite_eq_left rfl, b_addsext]
  rfl

theorem step_ecall (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc,
                  ms_svc_pending := some (getr regs 17), ms_resv := none,
                  ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom } := by
  rw [step_of_fetch segs (mkst regs pc mem rom) w hf]
  simp only [decode_exec, decode_exec_accesses, he, ↓reduceIte, drop_access_report]
  rfl

/-! ## Loads: overlay reads, loaded-value bridges and the load step lemmas

`ov_rdn` and `rdn_length`, the loaded-value bridges (`le_word_1`,
`le_word_v`, `b_extract8_id`), the little-endian range facts, the
`Z.testbit` range lemmas, and the `step_lbu`/`step_lhu`/`step_lwu`/`step_ld`
load steps, with the Rocq statements.

Spellings: a Rocq power whose exponent is a non-negative expression in a
length, `2 ^ (8 * Z.of_nat (length bs))`, is `2 ^ (8 * bs.length)` with a
`Nat` exponent, as in the stack-layout part; one at a free `Z` exponent is
`Z_pow 2 n`.  `Z.testbit` is `Z_testbit`.  The load steps go through
`step_pipeline`/`step_exec` and `interp_load`; the one Lean-only helper,
`zext_extract_small`, carries the zero-extension step Rocq's proofs take with
stdpp's `bv_zero_extend_unsigned`/`bv_wrap_small`. -/

/-! ### Z-level range/bit helpers -/

theorem Z_testbit_high (n a k : Int) (hn : 0 ≤ n) (ha : 0 ≤ a ∧ a < Z_pow 2 n) (hk : n ≤ k) :
    Z_testbit a k = false := by
  obtain ⟨n', rfl⟩ := Int.eq_ofNat_of_zero_le hn
  obtain ⟨a', rfl⟩ := Int.eq_ofNat_of_zero_le ha.1
  obtain ⟨k', rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_trans hn hk)
  have hp : Z_pow 2 (n' : Int) = ((2 ^ n' : Nat) : Int) := by
    show (2 : Int) ^ n' = _
    rw [Int.natCast_pow]
    rfl
  have ht : Z_testbit (a' : Int) (k' : Int) = a'.testBit k' := rfl
  have hlt : a' < 2 ^ n' := by
    have h2 := ha.2
    rw [hp] at h2
    exact_mod_cast h2
  have hnk : n' ≤ k' := by exact_mod_cast hk
  rw [ht]
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) hnk))

theorem Z_bounded_by_bits (n a : Int) (hn : 0 ≤ n) (ha : 0 ≤ a)
    (hb : ∀ k, n ≤ k → Z_testbit a k = false) : a < Z_pow 2 n := by
  obtain ⟨n', rfl⟩ := Int.eq_ofNat_of_zero_le hn
  obtain ⟨a', rfl⟩ := Int.eq_ofNat_of_zero_le ha
  have hp : Z_pow 2 (n' : Int) = ((2 ^ n' : Nat) : Int) := by
    show (2 : Int) ^ n' = _
    rw [Int.natCast_pow]
    rfl
  rw [hp]
  have hlt : a' < 2 ^ n' := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    exact hb (i : Int) (by exact_mod_cast hi)
  exact_mod_cast hlt

/-! ### Overlay reads and loaded-value bridges -/

/-- The tree interpreter's overlay read is `rdn`. -/
theorem ov_rdn (segs : List Segment) (mem : word → Option byte) (n : Nat) (a : word) :
    ov_read_bytes segs mem a n = rdn segs mem a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [ov_read_bytes, rdn, ih]
    rfl

/-- Loaded-value bridges: `interp_eff` hands
`bv_extract 0 n (le_bytes_to_word bs)` to the `ELoad` continuation, which
is why `b_extract8_id` follows. -/
theorem le_word_1 (b : byte) : le_bytes_to_word [b] = Z_to_bv 64 (bv_unsigned b) := by
  unfold le_bytes_to_word bytes_le_to_Z bv_unsigned
  simp only [bytes_le_to_nat, Nat.zero_shiftLeft, Nat.or_zero]

theorem le_word_v (bs : List byte) (v : word) (hv : bytes_le_to_Z bs = bv_unsigned v) :
    le_bytes_to_word bs = v := by
  unfold le_bytes_to_word
  rw [hv]
  unfold bv_unsigned Z_to_bv
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem b_extract8_id (b : byte) : bv_extract 0 8 (Z_to_bv 64 (bv_unsigned b)) = b := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt
  unfold bv_extract bv_unsigned Z_to_bv
  rw [BitVec.extractLsb'_toNat, BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.shiftRight_zero,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem rdn_length (segs : List Segment) (mem : word → Option byte) (n : Nat) (a : word)
    (bs : List byte) (h : rdn segs mem a n = some bs) : bs.length = n := by
  induction n generalizing a bs with
  | zero =>
    simp only [rdn, Option.some.injEq] at h
    rw [← h]
    rfl
  | succ n ih =>
    simp only [rdn] at h
    split at h
    · split at h
      · rename_i rest hrest
        simp only [Option.some.injEq] at h
        rw [← h, List.length_cons, ih (a + 1) rest hrest]
      · cases h
    · cases h

theorem bytes_le_to_Z_nonneg (bs : List byte) : 0 ≤ bytes_le_to_Z bs := by
  unfold bytes_le_to_Z
  omega

theorem bytes_le_to_Z_bound (bs : List byte) : bytes_le_to_Z bs < 2 ^ (8 * bs.length) := by
  have h : bytes_le_to_nat bs < 2 ^ (8 * bs.length) := by
    induction bs with
    | nil => decide
    | cons b bs ih =>
      simp only [bytes_le_to_nat, List.length_cons]
      rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq,
        show 8 * (bs.length + 1) = 8 * bs.length + 8 by omega, Nat.pow_add]
      have hb := b.isLt
      omega
  unfold bytes_le_to_Z
  exact_mod_cast h

theorem u8_range (b : byte) : 0 ≤ bv_unsigned b ∧ bv_unsigned b < 256 := by
  unfold bv_unsigned
  have := b.isLt
  omega

/-! ### Loads -/

/-- Lean-only helper: zero-extending the low `n` bits of a word that already
fits in `n` bits gives the word back. -/
theorem zext_extract_small (v : word) (n : Nat) (hn : n ≤ 64) (hv : bv_unsigned v < 2 ^ n) :
    zext 64 (bv_extract 0 n v) = v := by
  apply BitVec.eq_of_toNat_eq
  have hv' : v.toNat < 2 ^ n := by
    unfold bv_unsigned at hv
    exact_mod_cast hv
  unfold zext bv_zero_extend bv_extract
  rw [BitVec.zeroExtend, BitVec.toNat_setWidth_of_le hn, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, Nat.mod_eq_of_lt hv']

theorem step_lbu (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12) (b : byte)
    (hfetch : fetch_word segs pc = some w) (hecall : is_ecall w = false)
    (hdecode : decode_any w = some (.Load .SZ1 false rd rs imm, 4))
    (hread : rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1 = some [b]) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (Z_to_bv 64 (bv_unsigned b)))
                      (v_addi pc 4) mem rom) := by
  have hz : zext 64 (bv_extract 0 8 (le_bytes_to_word [b])) = Z_to_bv 64 (bv_unsigned b) := by
    rw [le_word_1]
    have hb := u8_range b
    apply zext_extract_small _ 8 (by decide)
    rw [Z_to_bv_unsigned, bv_wrap, Int.emod_eq_of_lt hb.1 (by omega)]
    omega
  step_pipeline hfetch hecall hdecode
  refine interp_load segs 8 _ [b] _ _ mem ?_ ?_
  · show ov_read_bytes segs mem (rget (core.Core regs bvmap_empty pc 0 none) rs + sext 64 imm) 1
      = some [b]
    rw [rget_mk, b_addsext, ov_rdn]
    exact hread
  · show eff.EDone (rset rd (zext 64 (bv_extract 0 8 (le_bytes_to_word [b])))
      (core.Core regs bvmap_empty (pc + 4) 0 none)) = _
    rw [hz, npc4, rset_mk]

theorem step_lhu (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (bs : List byte) (v : word)
    (hfetch : fetch_word segs pc = some w) (hecall : is_ecall w = false)
    (hdecode : decode_any w = some (.Load .SZ2 false rd rs imm, 4))
    (hread : rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 2 = some bs)
    (hv : bytes_le_to_Z bs = bv_unsigned v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) mem rom) := by
  have hz : zext 64 (bv_extract 0 16 v) = v := by
    have hb := bytes_le_to_Z_bound bs
    rw [rdn_length segs mem 2 _ bs hread, hv] at hb
    exact zext_extract_small v 16 (by decide) hb
  step_pipeline hfetch hecall hdecode
  refine interp_load segs 16 _ bs _ _ mem ?_ ?_
  · show ov_read_bytes segs mem (rget (core.Core regs bvmap_empty pc 0 none) rs + sext 64 imm) 2
      = some bs
    rw [rget_mk, b_addsext, ov_rdn]
    exact hread
  · show eff.EDone (rset rd (zext 64 (bv_extract 0 16 (le_bytes_to_word bs)))
      (core.Core regs bvmap_empty (pc + 4) 0 none)) = _
    rw [le_word_v bs v hv, hz, npc4, rset_mk]

theorem step_lwu (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (bs : List byte) (v : word)
    (hfetch : fetch_word segs pc = some w) (hecall : is_ecall w = false)
    (hdecode : decode_any w = some (.Load .SZ4 false rd rs imm, 4))
    (hread : rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4 = some bs)
    (hv : bytes_le_to_Z bs = bv_unsigned v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) mem rom) := by
  have hz : zext 64 (bv_extract 0 32 v) = v := by
    have hb := bytes_le_to_Z_bound bs
    rw [rdn_length segs mem 4 _ bs hread, hv] at hb
    exact zext_extract_small v 32 (by decide) hb
  step_pipeline hfetch hecall hdecode
  refine interp_load segs 32 _ bs _ _ mem ?_ ?_
  · show ov_read_bytes segs mem (rget (core.Core regs bvmap_empty pc 0 none) rs + sext 64 imm) 4
      = some bs
    rw [rget_mk, b_addsext, ov_rdn]
    exact hread
  · show eff.EDone (rset rd (zext 64 (bv_extract 0 32 (le_bytes_to_word bs)))
      (core.Core regs bvmap_empty (pc + 4) 0 none)) = _
    rw [le_word_v bs v hv, hz, npc4, rset_mk]

theorem step_ld (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (bs : List byte) (v : word)
    (hfetch : fetch_word segs pc = some w) (hecall : is_ecall w = false)
    (hdecode : decode_any w = some (.Load .SZ8 true rd rs imm, 4))
    (hread : rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 8 = some bs)
    (hv : bytes_le_to_Z bs = bv_unsigned v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) mem rom) := by
  have hz : bv_extract 0 64 v = v := by
    apply BitVec.eq_of_toNat_eq
    unfold bv_extract
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Nat.mod_eq_of_lt v.isLt]
  step_pipeline hfetch hecall hdecode
  refine interp_load segs 64 _ bs _ _ mem ?_ ?_
  · show ov_read_bytes segs mem (rget (core.Core regs bvmap_empty pc 0 none) rs + sext 64 imm) 8
      = some bs
    rw [rget_mk, b_addsext, ov_rdn]
    exact hread
  · show eff.EDone (rset rd (bv_extract 0 64 (le_bytes_to_word bs))
      (core.Core regs bvmap_empty (pc + 4) 0 none)) = _
    rw [le_word_v bs v hv, hz, npc4, rset_mk]

/-! ## Stack layout, byte decoding and value conditions

The comparison and value-condition lemmas, the register-file helpers,
little-endian byte decoding, and the entry-stack layout and read-back
lemmas, with the Rocq statements. See the header's Universes paragraph
for the universe differences.

Spellings: Rocq's `2^(8 * Z.of_nat k)` has a `Z` exponent and core Lean's
`Int` power a `Nat` one, so it is `2 ^ (8 * k)` here (the Rocq exponent is
non-negative, where the two agree).  `nth_error`, `skipn`, `firstn`,
`flat_map` and `Z.to_nat` are `l[d]?`, `List.drop`, `List.take`,
`List.flatMap` and `Int.toNat`.  Rocq's `++` associates to the right and
Lean's to the left, so a Rocq `pre ++ mid ++ post` is written
`pre ++ (mid ++ post)`.  `bsb_argc_prefix` states exactly the pilot's
Lean-only `build_stack_bytes_prefix` above and is proved by it.

Lean-only helpers: `bytes_le_nat_Z_to_le` (the same statement as
`Checks.Sys.Kernel.Time.PosixTimers.bytes_le_to_nat_of_le_bytes`, which
Common does not import) and `bv_extract8_shift`. -/

/-! ### Value and comparison simplification -/

theorem v_addi_0 (x : word) : v_addi x 0 = x := by
  apply bv_eq_of_unsigned
  rw [v_addi, Z_to_bv_unsigned, bv_wrap, Int.add_zero]
  have hx := u64_range x
  exact Int.emod_eq_of_lt hx.1 hx.2

theorem v_add_small (x y : word) (h : bv_unsigned x + bv_unsigned y < 2 ^ 64) :
    bv_unsigned (v_add x y) = bv_unsigned x + bv_unsigned y := by
  unfold v_add
  rw [Z_to_bv_unsigned, bv_wrap64_mod]
  have hx := u64_range x
  have hy := u64_range y
  exact Int.emod_eq_of_lt (by omega) h

theorem bv_signed_small (x : word) (hx : bv_unsigned x < 2 ^ 63) :
    bv_signed x = bv_unsigned x := by
  unfold bv_signed bv_unsigned at *
  have h : 2 * x.toNat < 2 ^ 64 := by omega
  exact BitVec.toInt_eq_toNat_of_lt h

theorem c_lts_small (x y : word) (hx : bv_unsigned x < 2 ^ 63) (hy : bv_unsigned y < 2 ^ 63) :
    c_lts x y = bv_ltu x y := by
  have hx' := bv_signed_small x hx
  have hy' := bv_signed_small y hy
  unfold c_lts bv_lts bv_ltu
  unfold bv_signed bv_unsigned at hx' hy'
  rw [Bool.eq_iff_iff, BitVec.slt_iff_toInt_lt, BitVec.ult_iff_lt, BitVec.lt_def, hx', hy']
  exact Int.ofNat_lt

theorem c_lts_pos_0 (x : word) (hx : bv_unsigned x < 2 ^ 63) :
    c_lts x (Z_to_bv 64 0) = false := by
  have h0 : bv_unsigned (Z_to_bv 64 0) = 0 := rfl
  rw [c_lts_small x _ hx (by rw [h0]; decide)]
  unfold bv_ltu
  rw [Bool.eq_false_iff]
  intro h
  rw [BitVec.ult_iff_lt, BitVec.lt_def] at h
  unfold bv_unsigned at h0
  omega

/-- `blez a0` falls through on a nonempty syscall return: the mirror of
`c_lts_pos_0` with the zero on the left.  This is the form every
retry loop meets after a short write, and the form the streamcat
read loops meet after a short read.  The bound is stated once, at
`2^63` — the signed boundary — rather than at any particular
buffer size, so a single lemma serves both; a caller holding a
tighter bound (a page, `rw_bytes_max`, ...) discharges it by `omega`.

Stated here, beside `c_lts_pos_0` and `c_lts_small`, and not in the
per-shape libraries, following Rocq, whose PropExec.v places it here
because two Rocq libraries once carried rival copies of it. -/
theorem c_lts_0_pos (n : word) (h1 : 1 ≤ bv_unsigned n) (h2 : bv_unsigned n < 2 ^ 63) :
    c_lts (Z_to_bv 64 0) n = true := by
  have h0 : bv_unsigned (Z_to_bv 64 0) = 0 := rfl
  rw [c_lts_small _ n (by rw [h0]; decide) h2]
  unfold bv_ltu
  rw [BitVec.ult_iff_lt, BitVec.lt_def]
  unfold bv_unsigned at h0 h1
  omega

theorem c_eq_0_false (x : word) (hnz : bv_unsigned x ≠ 0) :
    c_eq x (Z_to_bv 64 0) = false := by
  unfold c_eq
  apply bv_eqb_neq
  intro h
  apply hnz
  rw [h]
  rfl

/-- The positive counterpart of `c_eq_0_false`: the `beqz` a put loop
takes on full delivery, from an unsigned-level zero fact.

Stated here, beside `c_eq_0_false`, following Rocq, whose PropExec.v
places it here for the reason it places `c_lts_0_pos`. -/
theorem c_eq_0_of_u (x : word) (hx : bv_unsigned x = 0) :
    c_eq x (Z_to_bv 64 0) = true := by
  have hx0 : x = Z_to_bv 64 0 := bv_eq_of_unsigned _ _ (by rw [hx]; rfl)
  rw [hx0]
  exact PropExec.bv_eqb_refl _

theorem c_eq_0_true : c_eq (Z_to_bv 64 0) (Z_to_bv 64 0) = true := PropExec.bv_eqb_refl _

/-! ### Register-file helpers -/

theorem getr_same (regs : bvmap 5 word) (r : reg) (v : word) (h : r ≠ 0) :
    getr (regupd regs r v) r = v := by
  unfold getr regupd reg_get
  rw [bv_eqb_neq r 0 h, bvmap_get_set_same]
  rfl

theorem getr_other (regs : bvmap 5 word) (r : reg) (v : word) (r' : reg) (h : r' ≠ r) :
    getr (regupd regs r v) r' = getr regs r' := by
  unfold getr regupd reg_get
  cases bv_eqb r' 0 with
  | true => rfl
  | false =>
    rw [bvmap_get_set_other r r' v regs (Ne.symm h)]

theorem getr_nz (regs : bvmap 5 word) (r : reg) (h : r ≠ 0) : getr regs r = reg_get regs r := by
  unfold getr
  rw [bv_eqb_neq r 0 h]
  rfl

theorem regupd_other (regs : bvmap 5 word) (r : reg) (v : word) (r' : reg) (h : r' ≠ r) :
    reg_get (regupd regs r v) r' = reg_get regs r' := by
  unfold regupd reg_get
  rw [bvmap_get_set_other r r' v regs (Ne.symm h)]

theorem regupd_same (regs : bvmap 5 word) (r : reg) (v : word) :
    reg_get (regupd regs r v) r = v := by
  unfold regupd reg_get
  rw [bvmap_get_set_same]

/-! ### LE byte decoding -/

theorem bv_wrap8_mod (z : Int) : bv_wrap 8 z = z % 2 ^ 8 := rfl

/-- Lean-only helper: `bytes_le_Z_to_le` at a non-negative argument, in the
`Nat` arithmetic `bytes_le_to_nat` computes in.  The same statement is
`Checks.Sys.Kernel.Time.PosixTimers.bytes_le_to_nat_of_le_bytes`, in a
module Common does not import. -/
theorem bytes_le_nat_Z_to_le (k n : Nat) :
    bytes_le_to_nat (Z_to_le_bytes k (n : Int)) = n % 2 ^ (8 * k) := by
  induction k generalizing n with
  | zero => simp only [Z_to_le_bytes, bytes_le_to_nat, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
  | succ k ih =>
    simp only [Z_to_le_bytes, bytes_le_to_nat]
    rw [← Int.natCast_shiftRight, ih]
    have hb : (Z_to_bv 8 (n : Int)).toNat = n % 2 ^ 8 := by
      unfold Z_to_bv
      rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat]
    rw [hb, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide))]
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    rw [show 8 * (k + 1) = 8 + 8 * k by omega, Nat.pow_add, Nat.mod_mul]
    rw [Nat.mul_comm, Nat.add_comm]

theorem bytes_le_Z_to_le (k : Nat) (z : Int) (hz : 0 ≤ z) :
    bytes_le_to_Z (Z_to_le_bytes k z) = z % 2 ^ (8 * k) := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
  unfold bytes_le_to_Z
  rw [bytes_le_nat_Z_to_le, Int.natCast_emod, Int.natCast_pow]
  rfl

theorem bytes_le_N (k : Nat) (v : word) :
    bytes_le_to_Z (word_to_le_bytes k v) = bv_unsigned v % 2 ^ (8 * k) := by
  unfold word_to_le_bytes
  exact bytes_le_Z_to_le k (bv_unsigned v) (u64_range v).1

/-- Lean-only helper: one byte of `word_le8` is the low byte of the shifted
unsigned value, the form `Z_to_le_bytes` produces it in. -/
theorem bv_extract8_shift (v : word) (lo : Nat) :
    bv_extract lo 8 v = Z_to_bv 8 (bv_unsigned v >>> lo) := by
  apply BitVec.eq_of_toNat_eq
  unfold bv_extract bv_unsigned Z_to_bv
  rw [← Int.natCast_shiftRight, BitVec.ofInt_natCast, BitVec.toNat_ofNat, BitVec.extractLsb'_toNat]

theorem n_to_le_8_spec (v : word) : word_le8 v = word_to_le_bytes 8 v := by
  unfold word_le8 word_to_le_bytes
  simp only [Z_to_le_bytes, bv_extract8_shift, ← Int.shiftRight_add, Nat.reduceAdd,
    Int.shiftRight_zero]

theorem bytes_le_n_to_le_8 (v : word) : bytes_le_to_Z (word_le8 v) = bv_unsigned v := by
  rw [n_to_le_8_spec, bytes_le_N]
  have hv := u64_range v
  exact Int.emod_eq_of_lt hv.1 hv.2

/-! ### Stack memory reads -/

theorem nth_error_skipn_cons {A : Type _} (bs : List A) (d : Nat) (hd : d < bs.length) :
    ∃ b, bs[d]? = some b ∧ bs.drop d = b :: bs.drop (d + 1) := by
  induction bs generalizing d with
  | nil => exact absurd hd (Nat.not_lt_zero _)
  | cons x bs ih =>
    cases d with
    | zero => exact ⟨x, rfl, rfl⟩
    | succ d' =>
      rw [List.length_cons] at hd
      obtain ⟨b, h1, h2⟩ := ih d' (by omega)
      refine ⟨b, ?_, ?_⟩
      · rw [List.getElem?_cons_succ]
        exact h1
      · rw [List.drop_succ_cons, List.drop_succ_cons]
        exact h2

-- The fresh universe pins the header's polymorphism claim; the mutation
-- case `common-nth-error-skipn-cons-universe` checks this named theorem.
universe u in
theorem nth_error_skipn_cons_any_universe :
    ∀ {A : Type u} (bs : List A) (d : Nat), d < bs.length →
    ∃ b, bs[d]? = some b ∧ bs.drop d = b :: bs.drop (d + 1) :=
  nth_error_skipn_cons

/-- error: Application type mismatch: The argument
  True
has type
  Prop
of sort `Type` but is expected to have type
  Type _
of sort `Type (_ + 1)` in the application
  @nth_error_skipn_cons True -/
#guard_msgs in
set_option pp.mvars false in
example := @nth_error_skipn_cons True

/-- The address walk is a wrapping `bv` add, so the read lemmas need
the (always trivially satisfied in practice) no-overflow bound
`sp + length bytes < 2^64`. -/
theorem rdn_stack (segs : List Segment) (sp : word) (bytes : List byte) (k : Nat) (addr : word)
    (hsp : bv_unsigned sp ≤ bv_unsigned addr)
    (hlen : (bv_unsigned addr - bv_unsigned sp).toNat + k ≤ bytes.length)
    (hnw : bv_unsigned sp + (bytes.length : Int) < 2 ^ 64) :
    rdn segs (stack_to_mem sp bytes) addr k =
      some ((bytes.drop (bv_unsigned addr - bv_unsigned sp).toNat).take k) := by
  induction k generalizing addr with
  | zero => rfl
  | succ k ih =>
    have hr := u64_range addr
    have hs := u64_range sp
    obtain ⟨b, hnth, hskip⟩ :=
      nth_error_skipn_cons bytes (bv_unsigned addr - bv_unsigned sp).toNat (by omega)
    have hm : stack_to_mem sp bytes addr = some b := by
      have hlt : bv_unsigned addr - bv_unsigned sp < (bytes.length : Int) := by omega
      simp only [stack_to_mem, ite_eq_left hsp, ite_eq_left hlt]
      exact hnth
    have hu1 : bv_unsigned (addr + 1) = bv_unsigned addr + 1 := u_add1 addr (by omega)
    have hd : (bv_unsigned (addr + 1) - bv_unsigned sp).toNat =
        (bv_unsigned addr - bv_unsigned sp).toNat + 1 := by
      rw [hu1]
      omega
    have hrest := ih (addr + 1) (by omega) (by rw [hd]; omega)
    rw [hd] at hrest
    simp only [rdn, hm, hrest]
    rw [hskip]
    rfl

/-! ### Stack layout decomposition -/

theorem length_n_to_le_8 (v : word) : (word_le8 v).length = 8 := rfl

theorem length_flat_map_le8 (l : List word) : (l.flatMap word_le8).length = 8 * l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.flatMap_cons, List.length_append, ih, length_n_to_le_8, List.length_cons]
    omega

/-- The nat-valued companion of `Run.total_arg_bytes`: the spec states
its bound in `Z`, but the stack-image length arithmetic below lives
in `nat` with `length`, so the splitting lemmas use this form and
`total_arg_bytes_Z` bridges to the spec's bound. -/
def total_arg_bytes_nat (args : List (List byte)) : Nat :=
  args.foldr (fun a acc => a.length + 1 + acc) 0

theorem total_arg_bytes_Z (l : List (List byte)) :
    total_arg_bytes l = (total_arg_bytes_nat l : Int) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [total_arg_bytes, total_arg_bytes_nat, List.foldr_cons] at ih ⊢
    rw [ih]
    omega

theorem length_flatten_strings (l : List (List byte)) :
    (flatten_strings l).length = total_arg_bytes_nat l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [flatten_strings, total_arg_bytes_nat, List.flatMap_cons, List.length_append,
      List.length_singleton, List.foldr_cons] at ih ⊢
    rw [ih]

theorem len_word_nat {A : Type} (l : List A) : len_word l = nat_to_word l.length := rfl

-- These instances pin the header's accepted universe-0 types.
example := @len_word_nat Prop
example := @len_word_nat (Nat → Prop)
example := @len_word_nat (List Prop)

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
  @len_word_nat Type -/
#guard_msgs in
set_option pp.mvars false in
example := @len_word_nat Type

/-- error: Application type mismatch: The argument
  True
has type
  Prop
of sort `Type` but is expected to have type
  Type
of sort `Type 1` in the application
  @len_word_nat True -/
#guard_msgs in
set_option pp.mvars false in
example := @len_word_nat True

theorem word1_nat : (1 : word) = nat_to_word 1 := rfl

theorem word_add_0 (a : word) : a + nat_to_word 0 = a := by
  have h0 : nat_to_word 0 = 0#64 := rfl
  rw [h0, BitVec.add_zero]

theorem nat_to_word_merge (m k : Nat) :
    nat_to_word m + nat_to_word k = nat_to_word (m + k) := by
  unfold nat_to_word Z_to_bv
  rw [BitVec.ofInt_natCast, BitVec.ofInt_natCast, BitVec.ofInt_natCast, BitVec.ofNat_add]

theorem nat_to_word_add_merge (a : word) (m k : Nat) :
    a + nat_to_word m + nat_to_word k = a + nat_to_word (m + k) := by
  rw [BitVec.add_assoc, nat_to_word_merge]

theorem string_addrs_fst_structure (strs : List (List byte)) (base : word) :
    (string_addrs base strs).1 =
      match strs with
      | [] => []
      | s :: rest => base :: (string_addrs (base + len_word s + 1) rest).1 := by
  cases strs with
  | nil => rfl
  | cons s rest => rfl

theorem string_addrs_pair (strs : List (List byte)) (base : word) :
    string_addrs base strs =
      ((string_addrs base strs).1, base + nat_to_word (total_arg_bytes_nat strs)) := by
  induction strs generalizing base with
  | nil =>
    show (([] : List word), base) = ([], base + nat_to_word 0)
    rw [word_add_0]
  | cons s rest ih =>
    refine Prod.ext rfl ?_
    show (string_addrs (base + len_word s + 1) rest).2 = _
    rw [ih (base + len_word s + 1)]
    show base + len_word s + 1 + nat_to_word (total_arg_bytes_nat rest) =
      base + nat_to_word (s.length + 1 + total_arg_bytes_nat rest)
    rw [len_word_nat, word1_nat, nat_to_word_add_merge, nat_to_word_add_merge, Nat.add_assoc]

theorem length_string_addrs_fst (strs : List (List byte)) (base : word) :
    (string_addrs base strs).1.length = strs.length := by
  induction strs generalizing base with
  | nil => rfl
  | cons s rest ih =>
    rw [string_addrs_fst_structure]
    simp only [List.length_cons]
    rw [ih]

/-- The entry stack image never exceeds `Run.entry_stack_span`, the
closed-form upper bound `Run.entry_stack_fits` is stated against.
`Run` cannot prove this itself — the layout arithmetic lives here —
and without it `entry_stack_span` would be an over-approximation
nothing checks: add one more word to `build_stack_bytes` and this
lemma stops holding, which is the whole reason the span is a closed
form rather than a second copy of the layout.  Everything that needs
a size for the initial stack image goes through this lemma:
`StepTac.bsb_bound` is derived from it and
`Run.entry_stack_span_bound`, so there is one derivation. -/
theorem build_stack_bytes_within_span (ph : PhdrInfo) (sp : word) (a e : List (List byte))
    (uid hw : word) (rnd : EntryDraw) :
    ((build_stack_bytes ph sp a e uid hw rnd).length : Int) ≤ entry_stack_span a e := by
  unfold build_stack_bytes
  dsimp only
  rw [string_addrs_pair a]
  dsimp only
  rw [string_addrs_pair e]
  dsimp only
  simp only [List.length_append, List.length_replicate, length_flat_map_le8,
    length_string_addrs_fst, length_n_to_le_8, length_auxv_bytes, length_flatten_strings,
    length_at_random_bytes]
  unfold entry_stack_span auxv_size
  rw [total_arg_bytes_Z, total_arg_bytes_Z]
  omega

/-! ### Stack read corollaries -/

theorem bsb_argc_prefix (ph : PhdrInfo) (sp : word) (argv envp : List (List byte))
    (uid hw : word) (rnd : EntryDraw) :
    ∃ tl, build_stack_bytes ph sp argv envp uid hw rnd = word_le8 (len_word argv) ++ tl :=
  build_stack_bytes_prefix ph sp argv envp uid hw rnd

/-- The `k` bytes `mid` that sit after `pre` in a stack block are what
`rdn` reads back at `sp + length pre`, provided the block ends strictly
below 2^64 (`bv_unsigned sp + length bytes < 2^64`, Rocq's bound). -/
theorem read_at_offset (segs : List Segment) (sp : word) (bytes pre mid post : List byte)
    (k : Nat) (hb : bytes = pre ++ (mid ++ post)) (hk : mid.length = k)
    (hnw : bv_unsigned sp + (bytes.length : Int) < 2 ^ 64) :
    rdn segs (stack_to_mem sp bytes) (sp + nat_to_word pre.length) k = some mid := by
  have hs := u64_range sp
  have hlen : bytes.length = pre.length + (mid.length + post.length) := by
    rw [hb, List.length_append, List.length_append]
  have hu : bv_unsigned (sp + nat_to_word pre.length) = bv_unsigned sp + (pre.length : Int) := by
    rw [nat_to_word_eq_ofNat]
    apply u_add_offset
    unfold bv_unsigned at hnw
    omega
  have hsp : bv_unsigned sp ≤ bv_unsigned (sp + nat_to_word pre.length) := by omega
  have hoff : (bv_unsigned (sp + nat_to_word pre.length) - bv_unsigned sp).toNat = pre.length := by
    rw [hu]
    omega
  rw [rdn_stack segs sp bytes k _ hsp (by rw [hoff]; omega) hnw, hoff, hb, List.drop_left,
    ← hk, List.take_left]

/-- A read that stays inside the BLOCK sees the block: the page tail
`Run.entry_stack_image` adds sits above it
(`Run.stack_to_mem_image_in_block` byte by byte). -/
theorem rdn_image_in_block (segs : List Segment) (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (uid hwcap : word) (draw : EntryDraw) (a : word) (n : Nat)
    (hin : bv_unsigned a + (n : Int) ≤
      entry_block_top sp (build_stack_bytes ph sp argv envp uid hwcap draw))
    (hnw : bv_unsigned a + (n : Int) ≤ 2 ^ 64) :
    rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hwcap draw)) a n =
      rdn segs (stack_to_mem sp (build_stack_bytes ph sp argv envp uid hwcap draw)) a n := by
  apply rdn_ext segs n _ _ a hnw
  intro x hx
  exact stack_to_mem_image_in_block ph sp argv envp uid hwcap draw x (by omega)

/-- `read_at_offset` against the mapped image rather than the block.  A
read of a run that `build_stack_bytes` lays out is inside the block by
construction, so this needs no premise the block version does not: it
is the one step every read-back lemma takes, and the reason none
of their statements had to grow a bound when the model started mapping
the whole page. -/
theorem read_at_offset_image (segs : List Segment) (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (uid hwcap : word) (draw : EntryDraw)
    (pre mid post : List byte) (k : Nat)
    (hb : build_stack_bytes ph sp argv envp uid hwcap draw = pre ++ (mid ++ post))
    (hk : mid.length = k)
    (hnw : bv_unsigned sp
      + ((build_stack_bytes ph sp argv envp uid hwcap draw).length : Int) < 2 ^ 64) :
    rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hwcap draw))
        (sp + nat_to_word pre.length) k = some mid := by
  have hs := u64_range sp
  have hlen : (build_stack_bytes ph sp argv envp uid hwcap draw).length =
      pre.length + (mid.length + post.length) := by
    rw [hb, List.length_append, List.length_append]
  have hu : bv_unsigned (sp + nat_to_word pre.length) = bv_unsigned sp + (pre.length : Int) := by
    rw [nat_to_word_eq_ofNat]
    apply u_add_offset
    unfold bv_unsigned at hnw
    omega
  rw [rdn_image_in_block segs ph sp argv envp uid hwcap draw _ k
    (by unfold entry_block_top; rw [hu]; omega) (by rw [hu]; omega)]
  exact read_at_offset segs sp _ pre mid post k hb hk hnw

theorem read_argc (ph : PhdrInfo) (segs : List Segment) (sp : word)
    (argv envp : List (List byte)) (uid hw : word) (rnd : EntryDraw)
    (hnw : bv_unsigned sp
      + ((build_stack_bytes ph sp argv envp uid hw rnd).length : Int) < 2 ^ 64) :
    rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd)) sp 8 =
      some (word_le8 (len_word argv)) := by
  obtain ⟨tl, e⟩ := bsb_argc_prefix ph sp argv envp uid hw rnd
  have h := read_at_offset_image segs ph sp argv envp uid hw rnd [] (word_le8 (len_word argv))
    tl 8 (by rw [e]; rfl) rfl hnw
  rw [List.length_nil, word_add_0] at h
  exact h

/-! ### The wrapper bridge

`init_machine_state` sets `ms_mem` to a wrapper that, for stack addresses
below `sp` (and above `sp - stack_max_size`), returns `some 0`, else defers
to the raw `stack_to_mem`.  Every read the binaries perform is at
`addr >= sp`, where the zero-fill guard is false, so the wrapper agrees with
`stack_to_mem`. -/

theorem init_mkst (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp : word) (argv envp : List (List byte)) (uid hw : word) (rnd : EntryDraw) :
    init_machine_state segs pc ph sp rnd argv envp uid hw =
      mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp)
        (Z_to_bv 64 (pc : Int)) (wrap_mem ph sp argv envp uid hw rnd) (seg_rom segs) := rfl

/-- Above (or at) `sp`, the wrapper equals the raw `stack_to_mem`:
the zero-fill branch is gated by `addr < sp`, which is false. -/
theorem wrap_above_sp (ph : PhdrInfo) (sp : word) (argv envp : List (List byte)) (x : word)
    (uid hw : word) (rnd : EntryDraw) (hx : bv_unsigned sp ≤ bv_unsigned x) :
    wrap_mem ph sp argv envp uid hw rnd x =
      stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd) x := by
  unfold wrap_mem
  cases h : stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd) x with
  | some b => rfl
  | none =>
    have hlt : ¬ (bv_unsigned x < bv_unsigned sp) := by omega
    simp only [hlt, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

theorem rdn_wrap_stack_above (segs : List Segment) (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (a : word) (n : Nat) (uid hw : word) (rnd : EntryDraw)
    (hsp : bv_unsigned sp ≤ bv_unsigned a) (hnw : bv_unsigned a + (n : Int) ≤ 2 ^ 64) :
    rdn segs (wrap_mem ph sp argv envp uid hw rnd) a n =
      rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd)) a n := by
  apply rdn_ext segs n _ _ a hnw
  intro x hx
  exact wrap_above_sp ph sp argv envp x uid hw rnd (Int.le_trans hsp hx.1)

/-! ## Additions for ticket E-proof-library-2c: `Z_lor`, `Z_lxor`, `v_xori` and `v_and`

Ported from the same Rocq file at the baseline the header names, for
`Common/MuslStrlen.lean`, which states musl's has-zero test with them: the
value shapes `v_xori` and `v_and`, with the Rocq definitions.  Core Lean
4.34 has no `Z.lor` or `Z.lxor` either; they are defined first as `Z_lor`
and `Z_lxor` after stdlib's definitions, negative operands included, and
each docstring says how stdlib's six arms fold into its four.  The
`example`s after them follow the convention of the Lean-core twins above
(`Z_land` and the others), with stdlib's two zero arms added: every arm
of each definition and those two arms against the values Rocq's stdlib
computes, then a second group with, for each wrong reading its comments
name, a point at which that reading gives another value.  They are tests,
not a proof: a wrong reading that agrees with Rocq at every one of these
points passes them all.  The proofs are `Common/MuslStrlen.lean`'s
`Z_lor_unique` and `Z_lxor_unique`: they combine `Z_testbit_lor` and
`Z_testbit_lxor` with `Z_bits_inj` to fix both definitions at every input. -/

/-- Lean-only helper, standing for Rocq's stdlib `Z.lor`: bitwise or of the
infinite two's-complement readings of both operands.  Stdlib's definition
has six arms: its two zero arms fall into the arms here with an `.ofNat 0`
operand, which answer the other operand there too, and each of its other
four is one of these four.  As in `Z_land`, `Int.negSucc n` is `-(n+1)`,
whose bits are the complement of `n`'s: a non-negative `a` paired, in
either order, with a negative `-(n+1)` gives the complement of
`N.ldiff n a`, written `n - (n &&& a)`, and two negatives give the
complement of the `land` of the complements. -/
def Z_lor (a b : Int) : Int :=
  match a, b with
  | .ofNat a, .ofNat b => .ofNat (a ||| b)
  | .ofNat a, .negSucc b => .negSucc (b - (b &&& a))
  | .negSucc a, .ofNat b => .negSucc (a - (a &&& b))
  | .negSucc a, .negSucc b => .negSucc (a &&& b)

/-- Lean-only helper, standing for Rocq's stdlib `Z.lxor`: bitwise exclusive
or of the infinite two's-complement readings of both operands.  Stdlib's
six arms fold into these four as `Z_lor`'s do.  A non-negative `a`
paired, in either order, with a negative `-(n+1)` gives the complement of
`a ^^^ n`; two negative operands cancel. -/
def Z_lxor (a b : Int) : Int :=
  match a, b with
  | .ofNat a, .ofNat b => .ofNat (a ^^^ b)
  | .ofNat a, .negSucc b => .negSucc (a ^^^ b)
  | .negSucc a, .ofNat b => .negSucc (a ^^^ b)
  | .negSucc a, .negSucc b => .ofNat (a ^^^ b)

-- The two helpers at every arm, stdlib's two zero arms among them, against the
-- values Rocq's stdlib (`Z.lor`, `Z.lxor`) computes.
example : Z_lor 6 3 = 7 := by decide
example : Z_lor (-6) 3 = -5 := by decide
example : Z_lor 6 (-3) = -1 := by decide
example : Z_lor (-6) (-3) = -1 := by decide
example : Z_lor 0 (-7) = -7 := by decide
example : Z_lor (-7) 0 = -7 := by decide
example : Z_lxor 6 3 = 5 := by decide
example : Z_lxor (-6) 3 = -7 := by decide
example : Z_lxor 6 (-3) = -5 := by decide
example : Z_lxor (-6) (-3) = 7 := by decide
example : Z_lxor 0 (-7) = -7 := by decide
example : Z_lxor (-7) 0 = -7 := by decide
-- The second group.  Under each comment, for every wrong reading of a
-- helper the comment names, a point at which that reading gives another
-- value than Rocq's.  The values are again Rocq's.
-- `Z_lor`: in either mixed arm, the negative operand `-(n+1)` read as its
-- magnitude, as the complement of its magnitude (the bits of `n + 1`
-- complemented), or as its two's complement within 64 or 128 bits; `xor`
-- or a `Nat` difference for either mixed arm's and-not; `or` or `xor` for
-- the (-,-) arm's `and`, or the `or` of the magnitudes; and the (+,+) arm
-- truncated to 64 bits.
example : Z_lor (2 ^ 64 + 5) (-3) = -3 := by decide
example : Z_lor (-1) (2 ^ 64 + 3) = -1 := by decide
example : Z_lor (2 ^ 128) (-1) = -1 := by decide
example : Z_lor 3 (-8) = -5 := by decide
example : Z_lor (-8) 3 = -5 := by decide
example : Z_lor 3 (-6) = -5 := by decide
example : Z_lor (-12) 5 = -11 := by decide
example : Z_lor (-4) (-6) = -2 := by decide
example : Z_lor (2 ^ 64) 1 = 2 ^ 64 + 1 := by decide
example : Z_lor 1 (-(2 ^ 128 + 1)) = -(2 ^ 128 + 1) := by decide
example : Z_lor (-(2 ^ 128 + 1)) 1 = -(2 ^ 128 + 1) := by decide
example : Z_lor (-1) (2 ^ 128) = -1 := by decide
-- `Z_lxor`: in either mixed arm, the negative operand read in each of the
-- four ways `Z_lor`'s comment names; for the (-,-) arm, a negative result,
-- `or` or `and` for `xor`, or the `xor` of the magnitudes; and the (+,+)
-- arm truncated to 64 bits.
example : Z_lxor (2 ^ 64 + 5) (-3) = -(2 ^ 64 + 8) := by decide
example : Z_lxor (-1) (2 ^ 64 + 3) = -(2 ^ 64 + 4) := by decide
example : Z_lxor (2 ^ 128) (-1) = -(2 ^ 128 + 1) := by decide
example : Z_lxor (-4) (-6) = 6 := by decide
example : Z_lxor (2 ^ 64) 1 = 2 ^ 64 + 1 := by decide
example : Z_lxor (-1) (2 ^ 128) = -(2 ^ 128 + 1) := by decide

def v_xori (x : word) (imm : Int) : word := Z_to_bv 64 (Z_lxor (bv_unsigned x) (bv_wrap 64 imm))
def v_and (x y : word) : word := Z_to_bv 64 (Z_land (bv_unsigned x) (bv_unsigned y))

/-! ## Additions for ticket E-proof-library-2b: `v_addiw`

`v_addiw`, for `SymBranch.v_addiw_range`, ported from
`theories/Common/PropExec.v` at 2cde689f94c086b868999970834b76a25616b94a with
the Rocq definition.  Rocq defines it beside the other RV64 word operations;
it is appended here because the lead's ruling of 2026-09-29 has the
proof-library tickets append to this file without changing its existing
declarations. -/

/-- RV64 `addiw`: the 32-bit sum, sign-extended to 64 bits. -/
def v_addiw (x : word) (imm : Int) : word :=
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned x + imm))

-- The 32-bit wrap and the sign extension.
example : v_addiw (Z_to_bv 64 0x7fffffff) 1 = Z_to_bv 64 (-2 ^ 31) := by decide
example : v_addiw (Z_to_bv 64 0xffffffff) 1 = Z_to_bv 64 0 := by decide
example : v_addiw (Z_to_bv 64 0) (-1) = Z_to_bv 64 (-1) := by decide
example : v_addiw (Z_to_bv 64 (2 ^ 63 + 2 ^ 31)) 0 = Z_to_bv 64 (2 ^ 64 - 2 ^ 31) := by decide

/-! ## Additions for ticket E-proof-library-2c: `v_addi_0_64`

Ported from the same Rocq file at the baseline the header names, with the
Rocq statement: the `li a0,64` step of `Common/MuslCall.lean`'s
`musl_write_enter`. -/

theorem v_addi_0_64 : v_addi (Z_to_bv 64 0) 64 = Z_to_bv 64 64 := by decide

end LinuxProcessSemantics.Common.PropExec

/-! ## Additions for E-proof-library-2a (MmapSim)

Ported from `theories/Common/PropExec.v` with the Rocq statement, for
ticket E-proof-library-2a, and appended under the lead's ruling of
2026-09-29 on #1298's files: the declarations above are unchanged.  The
Rocq file was read at 7ba58b45f (`nightly/09-28-2026`).

`Common/MmapSim.lean`'s shift lemmas reach `v_srli`. -/

namespace LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase

/-- Logical right shift by the immediate `sh`.  Rocq's `Z.shiftr a n` is by
definition `Z.shiftl a (-n)`, which is how it is spelled here. -/
def v_srli (x : word) (sh : Int) : word := Z_to_bv 64 (Z_shiftl (bv_unsigned x) (-sh))

end LinuxProcessSemantics.Common.PropExec

/-! ## Additions for ticket E-grep_args_ns (SeqExec)

Ports exactly `v_mul`, `v_andi`, `v_ori`, `v_sltiu`, `v_srai`, and `v_subw`
from `theories/Common/PropExec.v` at
f44244ad6b8041aa83053d9ca91e090037ed743b, with the Rocq definitions and in
Rocq order. `Common/SeqExec.lean`'s `step_*_at` and value lemmas state their
results with these definitions. The declarations above are unchanged.
Rocq's `Z.land`/`Z.lor` are `Z_land`/`Z_lor`, `Z.shiftr a n` is
`Z_shiftl a (-n)`, and `Z.ltb a b` is `decide (a < b)`. -/

namespace LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase

def v_mul (x y : word) : word := Z_to_bv 64 (bv_unsigned x * bv_unsigned y)
def v_andi (x : word) (imm : Int) : word := Z_to_bv 64 (Z_land (bv_unsigned x) (bv_wrap 64 imm))
def v_ori (x : word) (imm : Int) : word := Z_to_bv 64 (Z_lor (bv_unsigned x) (bv_wrap 64 imm))
def v_sltiu (x : word) (imm : Int) : word :=
  if decide (bv_unsigned x < bv_wrap 64 imm) then Z_to_bv 64 1 else Z_to_bv 64 0
def v_srai (x : word) (sh : Int) : word := Z_to_bv 64 (Z_shiftl (bv_signed x) (-sh))
def v_subw (x y : word) : word :=
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned x - bv_unsigned y))

example : v_mul (Z_to_bv 64 3) (Z_to_bv 64 4) = Z_to_bv 64 12 := by decide
example : v_andi (Z_to_bv 64 6) 3 = Z_to_bv 64 2 := by decide
example : v_ori (Z_to_bv 64 6) 3 = Z_to_bv 64 7 := by decide
example : v_sltiu (Z_to_bv 64 2) 3 = Z_to_bv 64 1 := by decide
example : v_srai (Z_to_bv 64 (-8)) 2 = Z_to_bv 64 (-2) := by decide
example : v_subw (Z_to_bv 64 3) (Z_to_bv 64 5) = Z_to_bv 64 (-2) := by decide

end LinuxProcessSemantics.Common.PropExec

/-! ## Additions for ticket E-grep_args_ns (PropExec)

Ports the rest of `theories/Common/PropExec.v` at f44244ad6b80, with the
Rocq names and statements in Rocq order, save the Ltac `split_value_ifs`
(Rocq: between `c_eq_refl` and `bytes_le_single`), which is last here because
it needs a `section` opening Lean's metaprogramming namespaces. Rocq `Z` is
`Int`, `nat`/`N` are `Nat`, `Z.of_nat` is the `Nat` to `Int` cast, `S j` is
`j + 1`, `Z.land` is `Z_land`, `Z.lor` is `Z_lor`, `Z.lxor` is `Z_lxor`,
`Z.shiftr a n` is `Z_shiftl a (-n)`, `Z.ltb a b` is `decide (a < b)` and
`Z.eqb a b` is `decide (a = b)`. The declarations above are unchanged. Rocq
`Z.quot`/`Z.rem` are `Int.tdiv`/`Int.tmod`, and `nth j s d` is
`s[j]?.getD d`. -/

namespace LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.DecodeC
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run

theorem arg_reg_0 : Z_to_bv 5 (10 + (0 : Nat)) = (10 : reg) := by decide
theorem arg_reg_1 : Z_to_bv 5 (10 + (1 : Nat)) = (11 : reg) := by decide
theorem arg_reg_2 : Z_to_bv 5 (10 + (2 : Nat)) = (12 : reg) := by decide

theorem Z_land_range (a b : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64) (Hb : 0 ≤ b) :
    0 ≤ Z_land a b ∧ Z_land a b < 2 ^ 64 := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le Ha.1
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le Hb
  have := Nat.and_le_left (n := a) (m := b)
  change 0 ≤ ((a &&& b : Nat) : Int) ∧ ((a &&& b : Nat) : Int) < 2 ^ 64
  omega

theorem Z_lor_range (a b : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64)
    (Hb : 0 ≤ b ∧ b < 2 ^ 64) : 0 ≤ Z_lor a b ∧ Z_lor a b < 2 ^ 64 := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le Ha.1
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le Hb.1
  have := Nat.or_lt_two_pow (n := 64) (x := a) (y := b) (by omega) (by omega)
  change 0 ≤ ((a ||| b : Nat) : Int) ∧ ((a ||| b : Nat) : Int) < 2 ^ 64
  omega

theorem Z_lxor_range (a b : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64)
    (Hb : 0 ≤ b ∧ b < 2 ^ 64) : 0 ≤ Z_lxor a b ∧ Z_lxor a b < 2 ^ 64 := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le Ha.1
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le Hb.1
  have := Nat.xor_lt_two_pow (n := 64) (x := a) (y := b) (by omega) (by omega)
  change 0 ≤ ((a ^^^ b : Nat) : Int) ∧ ((a ^^^ b : Nat) : Int) < 2 ^ 64
  omega

theorem Z_shiftr_range (a k : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64) (Hk : 0 ≤ k) :
    0 ≤ Z_shiftl a (-k) ∧ Z_shiftl a (-k) < 2 ^ 64 := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le Ha.1
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le Hk
  cases k with
  | zero => exact Ha
  | succ k =>
    change 0 ≤ ((a >>> (k + 1) : Nat) : Int) ∧
      ((a >>> (k + 1) : Nat) : Int) < 2 ^ 64
    constructor
    · exact Int.natCast_nonneg _
    · exact_mod_cast Nat.lt_of_le_of_lt (Nat.shiftRight_le a (k + 1))
        (show a < 2 ^ 64 by omega)

theorem bv_swrap_add_idemp_l (n : Nat) (x y : Int) :
    bv_swrap n (bv_wrap n x + y) = bv_swrap n (x + y) := by
  unfold bv_swrap bv_wrap
  rw [Int.add_assoc, Int.emod_add_emod, ← Int.add_assoc]

theorem bv_swrap_add_idemp_r (n : Nat) (x y : Int) :
    bv_swrap n (x + bv_wrap n y) = bv_swrap n (x + y) := by
  rw [Int.add_comm x, bv_swrap_add_idemp_l, Int.add_comm y]

theorem bv_swrap_wrap' (n : Nat) (z : Int) : bv_swrap n (bv_wrap n z) = bv_swrap n z := by
  have := bv_swrap_add_idemp_l n z 0
  simpa only [Int.add_zero] using this

def zsig (x : word) : Int := bv_signed x
example : zsig (Z_to_bv 64 (-3)) = -3 := by decide

def v_or (x y : word) : word := Z_to_bv 64 (Z_lor (bv_unsigned x) (bv_unsigned y))
example : v_or (Z_to_bv 64 6) (Z_to_bv 64 3) = Z_to_bv 64 7 := by decide

def v_xor (x y : word) : word := Z_to_bv 64 (Z_lxor (bv_unsigned x) (bv_unsigned y))
example : v_xor (Z_to_bv 64 6) (Z_to_bv 64 3) = Z_to_bv 64 5 := by decide

def v_slti (x : word) (imm : Int) : word :=
  if decide (zsig x < imm) then Z_to_bv 64 1 else Z_to_bv 64 0
example : v_slti (Z_to_bv 64 (-1)) 0 = Z_to_bv 64 1 := by decide

def v_slt (x y : word) : word := if c_lts x y then Z_to_bv 64 1 else Z_to_bv 64 0
example : v_slt (Z_to_bv 64 (-1)) (Z_to_bv 64 0) = Z_to_bv 64 1 := by decide

def v_sltu (x y : word) : word := if c_ltu x y then Z_to_bv 64 1 else Z_to_bv 64 0
example : v_sltu (Z_to_bv 64 1) (Z_to_bv 64 2) = Z_to_bv 64 1 := by decide

def v_sll (x y : word) : word :=
  Z_to_bv 64 (Z_shiftl (bv_unsigned x) (bv_unsigned y % 64))
example : v_sll (Z_to_bv 64 3) (Z_to_bv 64 2) = Z_to_bv 64 12 := by decide

def v_srl (x y : word) : word :=
  Z_to_bv 64 (Z_shiftl (bv_unsigned x) (-(bv_unsigned y % 64)))
example : v_srl (Z_to_bv 64 12) (Z_to_bv 64 2) = Z_to_bv 64 3 := by decide

def v_sra (x y : word) : word :=
  Z_to_bv 64 (Z_shiftl (bv_signed x) (-(bv_unsigned y % 64)))
example : v_sra (Z_to_bv 64 (-12)) (Z_to_bv 64 2) = Z_to_bv 64 (-3) := by decide

def v_slliw (x : word) (sh : Int) : word :=
  Z_to_bv 64 (bv_swrap 32 (Z_shiftl (bv_unsigned x) sh))
example : v_slliw (Z_to_bv 64 3) 2 = Z_to_bv 64 12 := by decide

def v_srliw (x : word) (sh : Int) : word :=
  Z_to_bv 64 (bv_swrap 32 (Z_shiftl (bv_wrap 32 (bv_unsigned x)) (-sh)))
example : v_srliw (Z_to_bv 64 12) 2 = Z_to_bv 64 3 := by decide

def v_sraiw (x : word) (sh : Int) : word :=
  Z_to_bv 64 (bv_swrap 32 (Z_shiftl (bv_swrap 32 (bv_unsigned x)) (-sh)))
example : v_sraiw (Z_to_bv 64 (-12)) 2 = Z_to_bv 64 (-3) := by decide

def v_addw (x y : word) : word :=
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned x + bv_unsigned y))
example : v_addw (Z_to_bv 64 3) (Z_to_bv 64 4) = Z_to_bv 64 7 := by decide

def v_sllw (x y : word) : word :=
  Z_to_bv 64 (bv_swrap 32 (Z_shiftl (bv_unsigned x) (bv_unsigned y % 32)))
example : v_sllw (Z_to_bv 64 3) (Z_to_bv 64 2) = Z_to_bv 64 12 := by decide

def v_srlw (x y : word) : word :=
  Z_to_bv 64 (bv_swrap 32 (Z_shiftl (bv_wrap 32 (bv_unsigned x)) (-(bv_unsigned y % 32))))
example : v_srlw (Z_to_bv 64 12) (Z_to_bv 64 2) = Z_to_bv 64 3 := by decide

def v_sraw (x y : word) : word :=
  Z_to_bv 64 (bv_swrap 32 (Z_shiftl (bv_swrap 32 (bv_unsigned x)) (-(bv_unsigned y % 32))))
example : v_sraw (Z_to_bv 64 (-12)) (Z_to_bv 64 2) = Z_to_bv 64 (-3) := by decide

def v_mulh (x y : word) : word :=
  Z_to_bv 64 (Z_shiftl (bv_signed x * bv_signed y) (-64))
example : v_mulh (Z_to_bv 64 (-3)) (Z_to_bv 64 4) = Z_to_bv 64 (-1) := by decide

def v_mulhsu (x y : word) : word :=
  Z_to_bv 64 (Z_shiftl (bv_signed x * bv_unsigned y) (-64))
example : v_mulhsu (Z_to_bv 64 (-3)) (Z_to_bv 64 4) = Z_to_bv 64 (-1) := by decide

def v_mulhu (x y : word) : word :=
  Z_to_bv 64 (Z_shiftl (bv_unsigned x * bv_unsigned y) (-64))
example : v_mulhu (Z_to_bv 64 3) (Z_to_bv 64 4) = Z_to_bv 64 0 := by decide

def v_mulw (x y : word) : word := Z_to_bv 64 (bv_swrap 32 (bv_unsigned x * bv_unsigned y))
example : v_mulw (Z_to_bv 64 3) (Z_to_bv 64 4) = Z_to_bv 64 12 := by decide

/-- Rocq's truncating `Z.quot` is Lean's `Int.tdiv`. -/
def v_div (x y : word) : word :=
  if decide (bv_unsigned y = 0) then Z_to_bv 64 (-1)
  else Z_to_bv 64 (Int.tdiv (zsig x) (zsig y))
example : v_div (Z_to_bv 64 (-7)) (Z_to_bv 64 3) = Z_to_bv 64 (-2) := by decide

/-- Rocq's truncating `Z.rem` is Lean's `Int.tmod`. -/
def v_rem (x y : word) : word :=
  if decide (bv_unsigned y = 0) then x else Z_to_bv 64 (Int.tmod (zsig x) (zsig y))
example : v_rem (Z_to_bv 64 (-7)) (Z_to_bv 64 3) = Z_to_bv 64 (-1) := by decide

def v_divw (x y : word) : word :=
  if decide (bv_wrap 32 (bv_unsigned y) = 0) then Z_to_bv 64 (-1)
  else Z_to_bv 64 (bv_swrap 32 (Int.tdiv (bv_swrap 32 (bv_unsigned x)) (bv_swrap 32 (bv_unsigned y))))
example : v_divw (Z_to_bv 64 (-7)) (Z_to_bv 64 3) = Z_to_bv 64 (-2) := by decide

def v_remw (x y : word) : word :=
  if decide (bv_wrap 32 (bv_unsigned y) = 0) then Z_to_bv 64 (bv_swrap 32 (bv_unsigned x))
  else Z_to_bv 64 (bv_swrap 32 (Int.tmod (bv_swrap 32 (bv_unsigned x)) (bv_swrap 32 (bv_unsigned y))))
example : v_remw (Z_to_bv 64 (-7)) (Z_to_bv 64 3) = Z_to_bv 64 (-1) := by decide

def v_divuw (x y : word) : word :=
  if decide (bv_wrap 32 (bv_unsigned y) = 0) then Z_to_bv 64 (-1)
  else Z_to_bv 64 (bv_swrap 32 (bv_wrap 32 (bv_unsigned x) / bv_wrap 32 (bv_unsigned y)))
example : v_divuw (Z_to_bv 64 7) (Z_to_bv 64 3) = Z_to_bv 64 2 := by decide

def v_remuw (x y : word) : word :=
  if decide (bv_wrap 32 (bv_unsigned y) = 0) then Z_to_bv 64 (bv_swrap 32 (bv_unsigned x))
  else Z_to_bv 64 (bv_swrap 32 (bv_wrap 32 (bv_unsigned x) % bv_wrap 32 (bv_unsigned y)))
example : v_remuw (Z_to_bv 64 7) (Z_to_bv 64 3) = Z_to_bv 64 1 := by decide

def v_lb (b : byte) : word := Z_to_bv 64 (bv_signed b)
example : v_lb (Z_to_bv 8 255) = Z_to_bv 64 (-1) := by decide

def v_lh (v : word) : word := Z_to_bv 64 (bv_swrap 16 (bv_unsigned v))
example : v_lh (Z_to_bv 64 65535) = Z_to_bv 64 (-1) := by decide

theorem b_lb_val (b : byte) : sext 64 (bv_extract 0 8 (le_bytes_to_word [b])) = v_lb b := by
  rw [le_word_1, b_extract8_id]
  rfl

theorem b_lh_val (v : word) : sext 64 (bv_extract 0 16 v) = v_lh v := by
  have h : bv_signed (bv_extract 0 16 v) = bv_swrap 16 (bv_unsigned v) := by
    unfold bv_signed bv_extract bv_swrap bv_half_modulus bv_modulus bv_wrap bv_unsigned
    rw [BitVec.toInt_eq_toNat_cond, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    split <;> omega
  show Z_to_bv 64 (bv_signed (bv_extract 0 16 v)) = _
  rw [h]
  rfl

/-- Protected because `Common.SymExec.b_lw_val` already declares this name. -/
protected theorem b_lw_val (v : word) : sext 64 (bv_extract 0 32 v) = v_lw v := by
  have h : bv_signed (bv_extract 0 32 v) = bv_swrap 32 (bv_unsigned v) := by
    unfold bv_signed bv_extract bv_swrap bv_half_modulus bv_modulus bv_wrap bv_unsigned
    rw [BitVec.toInt_eq_toNat_cond, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    split <;> omega
  show Z_to_bv 64 (bv_signed (bv_extract 0 32 v)) = _
  rw [h]
  rfl

theorem bytes_le_app (xs ys : List byte) :
    bytes_le_to_Z (xs ++ ys) =
      Z_lor (bytes_le_to_Z xs) (Z_shiftl (bytes_le_to_Z ys) (8 * (xs.length : Int))) := by
  have h : bytes_le_to_nat (xs ++ ys) =
      bytes_le_to_nat xs ||| (bytes_le_to_nat ys <<< (8 * xs.length)) := by
    induction xs with
    | nil => simp only [List.nil_append, bytes_le_to_nat, List.length_nil, Nat.mul_zero,
        Nat.shiftLeft_zero, Nat.zero_or]
    | cons x xs ih =>
      simp only [List.cons_append, bytes_le_to_nat, List.length_cons, ih,
        Nat.shiftLeft_or_distrib, Nat.or_assoc, ← Nat.shiftLeft_add]
      congr 2
  have he : 8 * (xs.length : Int) = ((8 * xs.length : Nat) : Int) := by omega
  rw [he]
  change (bytes_le_to_nat (xs ++ ys) : Int) =
    ((bytes_le_to_nat xs ||| (bytes_le_to_nat ys <<< (8 * xs.length)) : Nat) : Int)
  rw [h]

theorem le2_spec (b1 b0 : byte) : bv_unsigned (le2 b1 b0) = bytes_le_to_Z [b0, b1] := by
  simp only [bv_unsigned, le2, BitVec.toNat_append, bytes_le_to_Z, bytes_le_to_nat,
    Nat.zero_shiftLeft, Nat.or_zero]
  rw [Nat.or_comm]

theorem le4_spec (b3 b2 b1 b0 : byte) :
    bv_unsigned (le4 b3 b2 b1 b0) = bytes_le_to_Z [b0, b1, b2, b3] := by
  have h : bv_unsigned (le4 b3 b2 b1 b0) =
      Z_lor (bv_unsigned (le2 b3 b2) <<< 16) (bv_unsigned (le2 b1 b0)) := by
    simp only [le4, bv_unsigned, BitVec.toNat_append]
    rfl
  rw [h, le2_spec, le2_spec]
  rw [show [b0, b1, b2, b3] = [b0, b1] ++ [b2, b3] from rfl, bytes_le_app]
  change ((_ ||| _ : Nat) : Int) = ((_ ||| _ : Nat) : Int)
  rw [Nat.or_comm]
  rfl

theorem le8_spec (b7 b6 b5 b4 b3 b2 b1 b0 : byte) :
    bv_unsigned (le8 b7 b6 b5 b4 b3 b2 b1 b0) =
      bytes_le_to_Z [b0, b1, b2, b3, b4, b5, b6, b7] := by
  have h : bv_unsigned (le8 b7 b6 b5 b4 b3 b2 b1 b0) =
      Z_lor (bv_unsigned (le4 b7 b6 b5 b4) <<< 32) (bv_unsigned (le4 b3 b2 b1 b0)) := by
    simp only [le8, bv_unsigned, BitVec.toNat_append]
    rfl
  rw [h, le4_spec, le4_spec]
  rw [show [b0, b1, b2, b3, b4, b5, b6, b7] = [b0, b1, b2, b3] ++ [b4, b5, b6, b7] from rfl,
    bytes_le_app]
  change ((_ ||| _ : Nat) : Int) = ((_ ||| _ : Nat) : Int)
  rw [Nat.or_comm]
  rfl

theorem ok_mkst_eq (r1 r2 : bvmap 5 word) (p1 p2 : word) (m1 m2 ro : word → Option byte)
    (Hr : r1 = r2) (Hp : p1 = p2) (Hm : ∀ a, m1 a = m2 a) :
    MachineOk (mkst r1 p1 m1 ro) = MachineOk (mkst r2 p2 m2 ro) := by
  rw [Hr, Hp, funext Hm]

theorem wrap64_range (z : Int) : 0 ≤ bv_wrap 64 z ∧ bv_wrap 64 z < 2 ^ 64 := by
  exact ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩

theorem bv_swrap_congr (n : Nat) (x y : Int) (H : bv_wrap n x = bv_wrap n y) :
    bv_swrap n x = bv_swrap n y := by
  rw [← bv_swrap_wrap' n x, H, bv_swrap_wrap']

theorem bv_swrap_add_swrap_l (n : Nat) (x y : Int) :
    bv_swrap n (bv_swrap n x + y) = bv_swrap n (x + y) := by
  unfold bv_swrap
  rw [show bv_wrap n (x + bv_half_modulus n) - bv_half_modulus n + y + bv_half_modulus n =
    bv_wrap n (x + bv_half_modulus n) + y by omega]
  unfold bv_wrap
  rw [Int.emod_add_emod]
  congr 1
  congr 1
  omega

theorem bv_swrap_add_swrap_r (n : Nat) (x y : Int) :
    bv_swrap n (x + bv_swrap n y) = bv_swrap n (x + y) := by
  rw [Int.add_comm x, bv_swrap_add_swrap_l, Int.add_comm y]

private theorem port_unsigned_or {n : Nat} (a b : BitVec n) :
    bv_unsigned (bv_or a b) = Z_lor (bv_unsigned a) (bv_unsigned b) := by
  unfold bv_unsigned bv_or
  rw [BitVec.toNat_or]
  rfl

private theorem port_unsigned_xor {n : Nat} (a b : BitVec n) :
    bv_unsigned (bv_xor a b) = Z_lxor (bv_unsigned a) (bv_unsigned b) := by
  unfold bv_unsigned bv_xor
  rw [BitVec.toNat_xor]
  rfl

theorem alu_andi (a : word) {n : Nat} (imm : BitVec n) :
    alu64 .ALU_AND a (sext 64 imm) = v_andi a (bv_signed imm) := by
  apply bv_eq_of_unsigned
  change bv_unsigned (bv_and a (sext 64 imm)) = _
  rw [bv_unsigned_and, sext_eq, Z_to_bv_unsigned, v_andi, Z_to_bv_unsigned]
  exact (Int.emod_eq_of_lt
    (Z_land_range _ _ (u64_range a) (wrap64_range _).1).1
    (Z_land_range _ _ (u64_range a) (wrap64_range _).1).2).symm

theorem alu_ori (a : word) {n : Nat} (imm : BitVec n) :
    alu64 .ALU_OR a (sext 64 imm) = v_ori a (bv_signed imm) := by
  apply bv_eq_of_unsigned
  change bv_unsigned (bv_or a (sext 64 imm)) = _
  rw [port_unsigned_or, sext_eq, Z_to_bv_unsigned, v_ori, Z_to_bv_unsigned]
  exact (Int.emod_eq_of_lt
    (Z_lor_range _ _ (u64_range a) (wrap64_range _)).1
    (Z_lor_range _ _ (u64_range a) (wrap64_range _)).2).symm

theorem alu_xori (a : word) {n : Nat} (imm : BitVec n) :
    alu64 .ALU_XOR a (sext 64 imm) = v_xori a (bv_signed imm) := by
  apply bv_eq_of_unsigned
  change bv_unsigned (bv_xor a (sext 64 imm)) = _
  rw [port_unsigned_xor, sext_eq, Z_to_bv_unsigned, v_xori, Z_to_bv_unsigned]
  exact (Int.emod_eq_of_lt
    (Z_lxor_range _ _ (u64_range a) (wrap64_range _)).1
    (Z_lxor_range _ _ (u64_range a) (wrap64_range _)).2).symm

theorem alu_slti (a : word) (imm : BitVec 12) :
    alu64 .ALU_SLT a (sext 64 imm) = v_slti a (bv_signed imm) := by
  change (if decide (a.toInt < (imm.signExtend 64).toInt) then _ else _) = _
  rw [BitVec.toInt_signExtend_of_le (by decide)]
  rfl

theorem alu_sltiu (a : word) {n : Nat} (imm : BitVec n) :
    alu64 .ALU_SLTU a (sext 64 imm) = v_sltiu a (bv_signed imm) := by
  have h : bv_ltu a (sext 64 imm) = decide (bv_unsigned a < bv_wrap 64 (bv_signed imm)) := by
    rw [← Z_to_bv_unsigned, ← sext_eq]
    change decide (a.toNat < (sext 64 imm).toNat) = decide ((a.toNat : Int) < ((sext 64 imm).toNat : Int))
    simp only [Int.ofNat_lt]
  change (if bv_ltu a (sext 64 imm) then _ else _) = _
  rw [h]
  rfl

theorem alu_slt (a b : word) : alu64 .ALU_SLT a b = v_slt a b := rfl
theorem alu_sltu (a b : word) : alu64 .ALU_SLTU a b = v_sltu a b := rfl

theorem alu_and (a b : word) : alu64 .ALU_AND a b = v_and a b := by
  apply bv_eq_of_unsigned
  change bv_unsigned (bv_and a b) = _
  rw [bv_unsigned_and, v_and, Z_to_bv_unsigned]
  exact (Int.emod_eq_of_lt (Z_land_range _ _ (u64_range a) (u64_range b).1).1
    (Z_land_range _ _ (u64_range a) (u64_range b).1).2).symm

theorem alu_or (a b : word) : alu64 .ALU_OR a b = v_or a b := by
  apply bv_eq_of_unsigned
  change bv_unsigned (bv_or a b) = _
  rw [port_unsigned_or, v_or, Z_to_bv_unsigned]
  exact (Int.emod_eq_of_lt (Z_lor_range _ _ (u64_range a) (u64_range b)).1
    (Z_lor_range _ _ (u64_range a) (u64_range b)).2).symm

theorem alu_xor (a b : word) : alu64 .ALU_XOR a b = v_xor a b := by
  apply bv_eq_of_unsigned
  change bv_unsigned (bv_xor a b) = _
  rw [port_unsigned_xor, v_xor, Z_to_bv_unsigned]
  exact (Int.emod_eq_of_lt (Z_lxor_range _ _ (u64_range a) (u64_range b)).1
    (Z_lxor_range _ _ (u64_range a) (u64_range b)).2).symm

theorem regamt64_mask (b : word) :
    bv_unsigned (bv_and b (Z_to_bv 64 63)) = bv_unsigned b % 64 := by
  unfold bv_unsigned bv_and
  rw [BitVec.toNat_and, show (Z_to_bv 64 63).toNat = 2 ^ 6 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

private theorem port_shiftr (a : Int) (k : Nat) : Z_shiftl a (-(k : Int)) = a >>> k := by
  cases k with
  | zero => simp only [Int.natCast_zero, Int.neg_zero, Z_shiftl, Int.shiftLeft_zero, Int.shiftRight_zero]
  | succ k => rfl

private theorem port_shift_left {n : Nat} (a : BitVec n) (k : Nat) :
    a <<< k = Z_to_bv n (Z_shiftl (bv_unsigned a) (k : Int)) := by
  apply bv_eq_of_unsigned
  rw [Z_to_bv_unsigned]
  unfold bv_unsigned bv_wrap
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  change _ = ((a.toNat : Int) <<< k) % 2 ^ n
  rw [Int.shiftLeft_eq]
  norm_cast

private theorem port_shift_right {n : Nat} (a : BitVec n) (k : Nat) :
    a >>> k = Z_to_bv n (Z_shiftl (bv_unsigned a) (-(k : Int))) := by
  rw [port_shiftr]
  apply BitVec.eq_of_toNat_eq
  simp only [Z_to_bv, bv_unsigned, BitVec.toNat_ushiftRight, BitVec.toNat_ofInt]
  change _ = (Int.ofNat (a.toNat >>> k) % (2 ^ n : Nat)).toNat
  have hr : (Int.ofNat (a.toNat >>> k)) % (Int.ofNat (2 ^ n)) = Int.ofNat (a.toNat >>> k) :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr
      (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) a.isLt))
  exact (congrArg Int.toNat hr).symm

private theorem port_shift_arith {n : Nat} (a : BitVec n) (k : Nat) :
    a.sshiftRight k = Z_to_bv n (Z_shiftl (bv_signed a) (-(k : Int))) := by
  rw [port_shiftr]
  change _ = BitVec.ofInt n (a.toInt >>> k)
  rw [← BitVec.toInt_sshiftRight, BitVec.ofInt_toInt]

theorem alu_srli (a : word) (s : BitVec 6) :
    alu64 .ALU_SRL a (zext 64 s) = v_srli a (bv_unsigned s) := by
  have hm := shamt6_mask s
  change (((bv_and (zext 64 s) (Z_to_bv 64 63)).toNat : Int)) = (s.toNat : Int) at hm
  have hn := Int.ofNat_inj.mp hm
  change a >>> _ = _
  rw [hn, port_shift_right]
  rfl

theorem alu_srai (a : word) (s : BitVec 6) :
    alu64 .ALU_SRA a (zext 64 s) = v_srai a (bv_unsigned s) := by
  have hm := shamt6_mask s
  change (((bv_and (zext 64 s) (Z_to_bv 64 63)).toNat : Int)) = (s.toNat : Int) at hm
  have hn := Int.ofNat_inj.mp hm
  change a.sshiftRight _ = _
  rw [hn, port_shift_arith]
  rfl

theorem alu_sll (a b : word) : alu64 .ALU_SLL a b = v_sll a b := by
  change a <<< (bv_and b (Z_to_bv 64 63)).toNat = _
  rw [port_shift_left]
  change Z_to_bv 64 (Z_shiftl (bv_unsigned a) (bv_unsigned (bv_and b (Z_to_bv 64 63)))) = _
  rw [regamt64_mask]
  rfl

theorem alu_srl (a b : word) : alu64 .ALU_SRL a b = v_srl a b := by
  change a >>> (bv_and b (Z_to_bv 64 63)).toNat = _
  rw [port_shift_right]
  change Z_to_bv 64 (Z_shiftl (bv_unsigned a) (-bv_unsigned (bv_and b (Z_to_bv 64 63)))) = _
  rw [regamt64_mask]
  rfl

theorem alu_sra (a b : word) : alu64 .ALU_SRA a b = v_sra a b := by
  change a.sshiftRight (bv_and b (Z_to_bv 64 63)).toNat = _
  rw [port_shift_arith]
  change Z_to_bv 64 (Z_shiftl (bv_signed a) (-bv_unsigned (bv_and b (Z_to_bv 64 63)))) = _
  rw [regamt64_mask]
  rfl

theorem low32_unsigned (a : word) : bv_unsigned (low32 a) = bv_wrap 32 (bv_unsigned a) := by
  unfold low32 bv_unsigned bv_extract bv_wrap
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  omega

theorem low32_signed (a : word) : bv_signed (low32 a) = bv_swrap 32 (bv_unsigned a) := by
  rw [bv_signed_swrap, low32_unsigned, bv_swrap_wrap']

theorem shamt5_mask (s : BitVec 5) :
    bv_unsigned (bv_and (zext 32 s) (Z_to_bv 32 31)) = bv_unsigned s := by
  unfold bv_unsigned bv_and
  rw [BitVec.toNat_and, show (zext 32 s).toNat = s.toNat from
    BitVec.toNat_setWidth_of_le (w' := 32) (b := s) (by decide),
    show (Z_to_bv 32 31).toNat = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt s.isLt]

theorem regamt32_mask (b : word) :
    bv_unsigned (bv_and (low32 b) (Z_to_bv 32 31)) = bv_unsigned b % 32 := by
  unfold bv_unsigned bv_and low32 bv_extract
  rw [BitVec.toNat_and, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    show (Z_to_bv 32 31).toNat = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

private theorem port_sext_swrap (v : BitVec 32) :
    sext 64 v = Z_to_bv 64 (bv_swrap 32 (bv_unsigned v)) := by
  rw [sext_eq, bv_signed_swrap]

private theorem port_sext_wrap (z : Int) :
    sext 64 (Z_to_bv 32 z) = Z_to_bv 64 (bv_swrap 32 z) := by
  rw [port_sext_swrap, Z_to_bv_unsigned, bv_swrap_wrap']

theorem w_addiw (a : word) (imm : BitVec 12) :
    sext 64 (alu32 .ALU_ADD (low32 a) (sext 32 imm)) = v_addiw a (bv_signed imm) := by
  change sext 64 (low32 a + sext 32 imm) = _
  rw [port_sext_swrap, bv_unsigned_add, low32_unsigned, sext_eq, Z_to_bv_unsigned,
    bv_swrap_wrap', bv_swrap_add_idemp_l, bv_swrap_add_idemp_r]
  rfl

private theorem port_swrap_shift (x : Int) (k : Nat) :
    bv_swrap 32 (Z_shiftl (bv_wrap 32 x) (k : Int)) =
      bv_swrap 32 (Z_shiftl x (k : Int)) := by
  apply bv_swrap_congr
  change ((x % 2 ^ 32) <<< k) % 2 ^ 32 = (x <<< k) % 2 ^ 32
  simp only [Int.shiftLeft_eq, Int.mul_emod, Int.emod_emod]

theorem w_slliw (a : word) (s : BitVec 5) :
    sext 64 (alu32 .ALU_SLL (low32 a) (zext 32 s)) = v_slliw a (bv_unsigned s) := by
  change sext 64 (low32 a <<< (bv_and (zext 32 s) (Z_to_bv 32 31)).toNat) = _
  rw [port_shift_left, port_sext_wrap]
  change Z_to_bv 64 (bv_swrap 32 (Z_shiftl (bv_unsigned (low32 a))
    (bv_unsigned (bv_and (zext 32 s) (Z_to_bv 32 31))))) = _
  rw [shamt5_mask, low32_unsigned]
  change Z_to_bv 64 (bv_swrap 32 (Z_shiftl (bv_wrap 32 (bv_unsigned a)) (s.toNat : Int))) = _
  rw [port_swrap_shift]
  rfl

theorem w_srliw (a : word) (s : BitVec 5) :
    sext 64 (alu32 .ALU_SRL (low32 a) (zext 32 s)) = v_srliw a (bv_unsigned s) := by
  change sext 64 (low32 a >>> (bv_and (zext 32 s) (Z_to_bv 32 31)).toNat) = _
  rw [port_shift_right, port_sext_wrap]
  change Z_to_bv 64 (bv_swrap 32 (Z_shiftl (bv_unsigned (low32 a))
    (-bv_unsigned (bv_and (zext 32 s) (Z_to_bv 32 31))))) = _
  rw [shamt5_mask, low32_unsigned]
  rfl

theorem w_sraiw (a : word) (s : BitVec 5) :
    sext 64 (alu32 .ALU_SRA (low32 a) (zext 32 s)) = v_sraiw a (bv_unsigned s) := by
  change sext 64 ((low32 a).sshiftRight (bv_and (zext 32 s) (Z_to_bv 32 31)).toNat) = _
  rw [port_shift_arith, port_sext_wrap]
  change Z_to_bv 64 (bv_swrap 32 (Z_shiftl (bv_signed (low32 a))
    (-bv_unsigned (bv_and (zext 32 s) (Z_to_bv 32 31))))) = _
  rw [shamt5_mask, low32_signed]
  rfl

theorem w_addw (a b : word) : sext 64 (alu32 .ALU_ADD (low32 a) (low32 b)) = v_addw a b := by
  change sext 64 (low32 a + low32 b) = _
  rw [port_sext_swrap, bv_unsigned_add, low32_unsigned, low32_unsigned,
    bv_swrap_wrap', bv_swrap_add_idemp_l, bv_swrap_add_idemp_r]
  rfl

theorem w_subw (a b : word) : sext 64 (alu32 .ALU_SUB (low32 a) (low32 b)) = v_subw a b := by
  change sext 64 (low32 a - low32 b) = _
  rw [port_sext_swrap, bv_unsigned_sub, low32_unsigned, low32_unsigned, bv_swrap_wrap']
  unfold v_subw
  congr 1
  apply bv_swrap_congr
  unfold bv_wrap
  simp only [Int.sub_emod, Int.emod_emod]

theorem w_sllw (a b : word) : sext 64 (alu32 .ALU_SLL (low32 a) (low32 b)) = v_sllw a b := by
  change sext 64 (low32 a <<< (bv_and (low32 b) (Z_to_bv 32 31)).toNat) = _
  rw [port_shift_left, port_sext_wrap, low32_unsigned, port_swrap_shift]
  change Z_to_bv 64 (bv_swrap 32 (Z_shiftl (bv_unsigned a)
    (bv_unsigned (bv_and (low32 b) (Z_to_bv 32 31))))) = _
  rw [regamt32_mask]
  rfl

theorem w_srlw (a b : word) : sext 64 (alu32 .ALU_SRL (low32 a) (low32 b)) = v_srlw a b := by
  change sext 64 (low32 a >>> (bv_and (low32 b) (Z_to_bv 32 31)).toNat) = _
  rw [port_shift_right, port_sext_wrap, low32_unsigned]
  change Z_to_bv 64 (bv_swrap 32 (Z_shiftl (bv_wrap 32 (bv_unsigned a))
    (-bv_unsigned (bv_and (low32 b) (Z_to_bv 32 31))))) = _
  rw [regamt32_mask]
  rfl

theorem w_sraw (a b : word) : sext 64 (alu32 .ALU_SRA (low32 a) (low32 b)) = v_sraw a b := by
  change sext 64 ((low32 a).sshiftRight (bv_and (low32 b) (Z_to_bv 32 31)).toNat) = _
  rw [port_shift_arith, port_sext_wrap, low32_signed]
  change Z_to_bv 64 (bv_swrap 32 (Z_shiftl (bv_swrap 32 (bv_unsigned a))
    (-bv_unsigned (bv_and (low32 b) (Z_to_bv 32 31))))) = _
  rw [regamt32_mask]
  rfl

private theorem port_unsigned_mul {n : Nat} (a b : BitVec n) :
    bv_unsigned (a * b) = bv_wrap n (bv_unsigned a * bv_unsigned b) := by
  unfold bv_unsigned bv_wrap
  rw [BitVec.toNat_mul]
  rfl

theorem m_mul (a b : word) : mul_div .M_MUL a b = v_mul a b := by
  apply bv_eq_of_unsigned
  change bv_unsigned (a * b) = _
  rw [port_unsigned_mul, v_mul, Z_to_bv_unsigned]

theorem m_mulh (a b : word) : mul_div .M_MULH a b = v_mulh a b := rfl
theorem m_mulhsu (a b : word) : mul_div .M_MULHSU a b = v_mulhsu a b := rfl
theorem m_mulhu (a b : word) : mul_div .M_MULHU a b = v_mulhu a b := rfl

private theorem port_quots {n : Nat} (a b : BitVec n) :
    bv_quots a b = Z_to_bv n (Int.tdiv (bv_signed a) (bv_signed b)) := by
  apply BitVec.eq_of_toInt_eq
  change (a.sdiv b).toInt = (BitVec.ofInt n (a.toInt.tdiv b.toInt)).toInt
  rw [BitVec.toInt_sdiv, BitVec.toInt_ofInt]

private theorem port_rems {n : Nat} (a b : BitVec n) :
    bv_rems a b = Z_to_bv n (Int.tmod (bv_signed a) (bv_signed b)) := by
  change a.srem b = BitVec.ofInt n (a.toInt.tmod b.toInt)
  rw [← BitVec.toInt_srem, BitVec.ofInt_toInt]

theorem m_div (a b : word) : mul_div .M_DIV a b = v_div a b := by
  unfold mul_div v_div
  simp only [bv_unsigned, Int.natCast_eq_zero, decide_eq_true_eq]
  split
  · rfl
  · exact port_quots a b

theorem m_rem (a b : word) : mul_div .M_REM a b = v_rem a b := by
  unfold mul_div v_rem
  simp only [bv_unsigned, Int.natCast_eq_zero, decide_eq_true_eq]
  split
  · rfl
  · exact port_rems a b

theorem w_mulw (a b : word) : sext 64 (mul_div .M_MUL (low32 a) (low32 b)) = v_mulw a b := by
  change sext 64 (low32 a * low32 b) = _
  rw [port_sext_swrap, port_unsigned_mul, low32_unsigned, low32_unsigned, bv_swrap_wrap']
  unfold v_mulw
  apply congrArg (Z_to_bv 64)
  apply bv_swrap_congr
  unfold bv_wrap
  simp only [Int.mul_emod, Int.emod_emod]

theorem div0_32 (b : word) :
    decide (bv_unsigned (low32 b) = 0) = decide (bv_wrap 32 (bv_unsigned b) = 0) := by
  rw [low32_unsigned]

private theorem port_div0 (b : word) :
    (low32 b).toNat = 0 ↔ bv_wrap 32 (bv_unsigned b) = 0 := by
  rw [← low32_unsigned]
  exact Int.natCast_eq_zero.symm

theorem w_divw (a b : word) : sext 64 (mul_div .M_DIV (low32 a) (low32 b)) = v_divw a b := by
  unfold mul_div v_divw
  simp only [port_div0, decide_eq_true_eq]
  split
  · rfl
  · rw [port_quots, port_sext_wrap, low32_signed, low32_signed]

theorem w_remw (a b : word) : sext 64 (mul_div .M_REM (low32 a) (low32 b)) = v_remw a b := by
  unfold mul_div v_remw
  simp only [port_div0, decide_eq_true_eq]
  split
  · rw [sext_eq, low32_signed]
  · rw [port_rems, port_sext_wrap, low32_signed, low32_signed]

private theorem port_unsigned_div {n : Nat} (a b : BitVec n) :
    bv_unsigned (bv_divu a b) = bv_unsigned a / bv_unsigned b := by
  unfold bv_unsigned bv_divu
  change (((a / b).toNat : Nat) : Int) = _
  rw [BitVec.toNat_udiv]
  rfl

private theorem port_unsigned_mod {n : Nat} (a b : BitVec n) :
    bv_unsigned (bv_modu a b) = bv_unsigned a % bv_unsigned b := by
  unfold bv_unsigned bv_modu
  change (((a % b).toNat : Nat) : Int) = _
  rw [BitVec.toNat_umod]
  rfl

theorem w_divuw (a b : word) : sext 64 (mul_div .M_DIVU (low32 a) (low32 b)) = v_divuw a b := by
  unfold mul_div v_divuw
  simp only [port_div0, decide_eq_true_eq]
  split
  · rfl
  · rw [port_sext_swrap, port_unsigned_div, low32_unsigned, low32_unsigned]

theorem w_remuw (a b : word) : sext 64 (mul_div .M_REMU (low32 a) (low32 b)) = v_remuw a b := by
  unfold mul_div v_remuw
  simp only [port_div0, decide_eq_true_eq]
  split
  · rw [sext_eq, low32_signed]
  · rw [port_sext_swrap, port_unsigned_mod, low32_unsigned, low32_unsigned]

theorem step_andi (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.OpImm .ALU_AND rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_andi (getr regs rs) (bv_signed imm)))
                      (v_addi pc 4) mem rom) := by
  rw [step_opimm_gen segs regs pc mem rom w .ALU_AND rd rs imm hf he hd, alu_andi]

theorem step_ori (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.OpImm .ALU_OR rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_ori (getr regs rs) (bv_signed imm)))
                      (v_addi pc 4) mem rom) := by
  rw [step_opimm_gen segs regs pc mem rom w .ALU_OR rd rs imm hf he hd, alu_ori]

theorem step_xori (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.OpImm .ALU_XOR rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_xori (getr regs rs) (bv_signed imm)))
                      (v_addi pc 4) mem rom) := by
  rw [step_opimm_gen segs regs pc mem rom w .ALU_XOR rd rs imm hf he hd, alu_xori]

theorem step_sltiu (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.OpImm .ALU_SLTU rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_sltiu (getr regs rs) (bv_signed imm)))
                      (v_addi pc 4) mem rom) := by
  rw [step_opimm_gen segs regs pc mem rom w .ALU_SLTU rd rs imm hf he hd, alu_sltiu]

theorem step_slti (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.OpImm .ALU_SLT rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_slti (getr regs rs) (bv_signed imm)))
                      (v_addi pc 4) mem rom) := by
  rw [step_opimm_gen segs regs pc mem rom w .ALU_SLT rd rs imm hf he hd, alu_slti]

theorem step_srli (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (sh : BitVec 6)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.ShiftImm .ALU_SRL rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_srli (getr regs rs) (bv_unsigned sh)))
                      (v_addi pc 4) mem rom) := by
  rw [step_shiftimm_gen segs regs pc mem rom w .ALU_SRL rd rs sh hf he hd, alu_srli]

theorem step_srai (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (sh : BitVec 6)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.ShiftImm .ALU_SRA rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_srai (getr regs rs) (bv_unsigned sh)))
                      (v_addi pc 4) mem rom) := by
  rw [step_shiftimm_gen segs regs pc mem rom w .ALU_SRA rd rs sh hf he hd, alu_srai]

theorem step_slt (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Op .ALU_SLT rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_slt (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w .ALU_SLT rd rs1 rs2 hf he hd, alu_slt]

theorem step_sltu (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Op .ALU_SLTU rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_sltu (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w .ALU_SLTU rd rs1 rs2 hf he hd, alu_sltu]

theorem step_and (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Op .ALU_AND rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_and (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w .ALU_AND rd rs1 rs2 hf he hd, alu_and]

theorem step_or (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Op .ALU_OR rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_or (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w .ALU_OR rd rs1 rs2 hf he hd, alu_or]

theorem step_xor (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Op .ALU_XOR rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_xor (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w .ALU_XOR rd rs1 rs2 hf he hd, alu_xor]

theorem step_sll (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Op .ALU_SLL rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_sll (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w .ALU_SLL rd rs1 rs2 hf he hd, alu_sll]

theorem step_srl (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Op .ALU_SRL rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_srl (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w .ALU_SRL rd rs1 rs2 hf he hd, alu_srl]

theorem step_sra (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Op .ALU_SRA rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_sra (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w .ALU_SRA rd rs1 rs2 hf he hd, alu_sra]

theorem step_addiw (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.OpImm32 rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_addiw (getr regs rs) (bv_signed imm)))
                      (v_addi pc 4) mem rom) := by
  rw [step_opimm32_gen segs regs pc mem rom w rd rs imm hf he hd, w_addiw]

theorem step_slliw (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (sh : BitVec 5)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.ShiftImm32 .ALU_SLL rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_slliw (getr regs rs) (bv_unsigned sh)))
                      (v_addi pc 4) mem rom) := by
  rw [step_shiftimm32_gen segs regs pc mem rom w .ALU_SLL rd rs sh hf he hd, w_slliw]

theorem step_srliw (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (sh : BitVec 5)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.ShiftImm32 .ALU_SRL rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_srliw (getr regs rs) (bv_unsigned sh)))
                      (v_addi pc 4) mem rom) := by
  rw [step_shiftimm32_gen segs regs pc mem rom w .ALU_SRL rd rs sh hf he hd, w_srliw]

theorem step_sraiw (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (sh : BitVec 5)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.ShiftImm32 .ALU_SRA rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_sraiw (getr regs rs) (bv_unsigned sh)))
                      (v_addi pc 4) mem rom) := by
  rw [step_shiftimm32_gen segs regs pc mem rom w .ALU_SRA rd rs sh hf he hd, w_sraiw]

theorem step_addw (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Op32 .ALU_ADD rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_addw (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_op32_gen segs regs pc mem rom w .ALU_ADD rd rs1 rs2 hf he hd, w_addw]

theorem step_subw (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Op32 .ALU_SUB rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_subw (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_op32_gen segs regs pc mem rom w .ALU_SUB rd rs1 rs2 hf he hd, w_subw]

theorem step_sllw (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Op32 .ALU_SLL rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_sllw (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_op32_gen segs regs pc mem rom w .ALU_SLL rd rs1 rs2 hf he hd, w_sllw]

theorem step_srlw (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Op32 .ALU_SRL rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_srlw (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_op32_gen segs regs pc mem rom w .ALU_SRL rd rs1 rs2 hf he hd, w_srlw]

theorem step_sraw (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Op32 .ALU_SRA rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_sraw (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_op32_gen segs regs pc mem rom w .ALU_SRA rd rs1 rs2 hf he hd, w_sraw]

theorem step_mul (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Mul .M_MUL rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_mul (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_mul_gen segs regs pc mem rom w .M_MUL rd rs1 rs2 hf he hd, m_mul]

theorem step_mulh (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Mul .M_MULH rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_mulh (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_mul_gen segs regs pc mem rom w .M_MULH rd rs1 rs2 hf he hd, m_mulh]

theorem step_mulhsu (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Mul .M_MULHSU rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_mulhsu (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_mul_gen segs regs pc mem rom w .M_MULHSU rd rs1 rs2 hf he hd, m_mulhsu]

theorem step_mulhu (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Mul .M_MULHU rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_mulhu (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_mul_gen segs regs pc mem rom w .M_MULHU rd rs1 rs2 hf he hd, m_mulhu]

theorem step_div (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Mul .M_DIV rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_div (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_mul_gen segs regs pc mem rom w .M_DIV rd rs1 rs2 hf he hd, m_div]

theorem step_rem (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Mul .M_REM rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_rem (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_mul_gen segs regs pc mem rom w .M_REM rd rs1 rs2 hf he hd, m_rem]

theorem step_mulw (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Mul32 .M_MUL rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_mulw (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_mul32_gen segs regs pc mem rom w .M_MUL rd rs1 rs2 hf he hd, w_mulw]

theorem step_divw (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Mul32 .M_DIV rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_divw (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_mul32_gen segs regs pc mem rom w .M_DIV rd rs1 rs2 hf he hd, w_divw]

theorem step_divuw (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Mul32 .M_DIVU rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_divuw (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_mul32_gen segs regs pc mem rom w .M_DIVU rd rs1 rs2 hf he hd, w_divuw]

theorem step_remw (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Mul32 .M_REM rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_remw (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_mul32_gen segs regs pc mem rom w .M_REM rd rs1 rs2 hf he hd, w_remw]

theorem step_remuw (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Mul32 .M_REMU rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs
                       else regupd regs rd (v_remuw (getr regs rs1) (getr regs rs2)))
                      (v_addi pc 4) mem rom) := by
  rw [step_mul32_gen segs regs pc mem rom w .M_REMU rd rs1 rs2 hf he hd, w_remuw]

theorem step_blt_tk (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 13)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decode_any w = some (.Branch .BC_LT rs1 rs2 imm, 4))
    (Hc : c_lts (getr regs rs1) (getr regs rs2) = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom) := by
  apply step_branch_tk_gen segs regs pc mem rom w .BC_LT rs1 rs2 imm Hf He Hd
  exact Hc

theorem step_bge_tk (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 13)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decode_any w = some (.Branch .BC_GE rs1 rs2 imm, 4))
    (Hc : c_lts (getr regs rs1) (getr regs rs2) = false) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom) := by
  apply step_branch_tk_gen segs regs pc mem rom w .BC_GE rs1 rs2 imm Hf He Hd
  change (!c_lts (getr regs rs1) (getr regs rs2)) = _
  rw [Hc]
  rfl

theorem step_bltu_tk (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 13)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decode_any w = some (.Branch .BC_LTU rs1 rs2 imm, 4))
    (Hc : c_ltu (getr regs rs1) (getr regs rs2) = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom) := by
  apply step_branch_tk_gen segs regs pc mem rom w .BC_LTU rs1 rs2 imm Hf He Hd
  exact Hc

theorem step_bgeu_tk (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 13)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decode_any w = some (.Branch .BC_GEU rs1 rs2 imm, 4))
    (Hc : c_ltu (getr regs rs1) (getr regs rs2) = false) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom) := by
  apply step_branch_tk_gen segs regs pc mem rom w .BC_GEU rs1 rs2 imm Hf He Hd
  change (!c_ltu (getr regs rs1) (getr regs rs2)) = _
  rw [Hc]
  rfl

theorem step_bgeu_ft (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 13)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decode_any w = some (.Branch .BC_GEU rs1 rs2 imm, 4))
    (Hc : c_ltu (getr regs rs1) (getr regs rs2) = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst regs (v_addi pc 4) mem rom) := by
  apply step_branch_ft_gen segs regs pc mem rom w .BC_GEU rs1 rs2 imm Hf He Hd
  change (!c_ltu (getr regs rs1) (getr regs rs2)) = _
  rw [Hc]
  rfl

theorem step_lb (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (b : byte)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (.Load .SZ1 true rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1 = some [b])
    : RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lb b))
        (v_addi pc 4) mem rom) := by
  step_pipeline Hfetch Hecall Hdecode
  refine interp_load segs 8 _ [b] _ _ mem ?_ ?_
  · show ov_read_bytes segs mem (rget (core.Core regs bvmap_empty pc 0 none) rs + sext 64 imm) 1
      = some [b]
    rw [rget_mk, b_addsext, ov_rdn]
    exact Hread
  · show eff.EDone (rset rd (sext 64 (bv_extract 0 8 (le_bytes_to_word [b])))
      (core.Core regs bvmap_empty (pc + 4) 0 none)) = _
    rw [b_lb_val, npc4, rset_mk]

theorem step_lh (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (bs : List byte) (v : word)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (.Load .SZ2 true rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 2 = some bs)
    (Hv : bytes_le_to_Z bs = bv_unsigned v)
    : RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lh v))
        (v_addi pc 4) mem rom) := by
  step_pipeline Hfetch Hecall Hdecode
  refine interp_load segs 16 _ bs _ _ mem ?_ ?_
  · show ov_read_bytes segs mem (rget (core.Core regs bvmap_empty pc 0 none) rs + sext 64 imm) 2
      = some bs
    rw [rget_mk, b_addsext, ov_rdn]
    exact Hread
  · show eff.EDone (rset rd (sext 64 (bv_extract 0 16 (le_bytes_to_word bs)))
      (core.Core regs bvmap_empty (pc + 4) 0 none)) = _
    rw [le_word_v bs v Hv, b_lh_val, npc4, rset_mk]

/-- Protected because `Common.SymExec.step_lw` already declares this name. -/
protected theorem step_lw (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (bs : List byte) (v : word)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (.Load .SZ4 true rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4 = some bs)
    (Hv : bytes_le_to_Z bs = bv_unsigned v)
    : RiscvSemantics.step segs (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lw v))
        (v_addi pc 4) mem rom) := by
  step_pipeline Hfetch Hecall Hdecode
  refine interp_load segs 32 _ bs _ _ mem ?_ ?_
  · show ov_read_bytes segs mem (rget (core.Core regs bvmap_empty pc 0 none) rs + sext 64 imm) 4
      = some bs
    rw [rget_mk, b_addsext, ov_rdn]
    exact Hread
  · show eff.EDone (rset rd (sext 64 (bv_extract 0 32 (le_bytes_to_word bs)))
      (core.Core regs bvmap_empty (pc + 4) 0 none)) = _
    rw [le_word_v bs v Hv, PropExec.b_lw_val, npc4, rset_mk]

theorem two64_pos : (0 : Int) < 2 ^ 64 := by decide

theorem v_addi_nneg (x : word) (imm : Int) (Hi : 0 ≤ imm)
    (Hs : bv_unsigned x + imm < 2 ^ 64) : bv_unsigned (v_addi x imm) = bv_unsigned x + imm := by
  rw [v_addi, Z_to_bv_unsigned, bv_wrap64_mod]
  have := u64_range x
  exact Int.emod_eq_of_lt (by omega) Hs

theorem v_addi_0_1 : v_addi (Z_to_bv 64 0) 1 = Z_to_bv 64 1 := by decide

theorem v_addi_Sj (j : Nat) (_ : (j : Int) + 1 < 2 ^ 64) :
    v_addi (nat_to_word j) 1 = nat_to_word (j + 1) := by
  unfold v_addi nat_to_word
  apply bv_eq_of_unsigned
  rw [Z_to_bv_unsigned, Z_to_bv_unsigned, Z_to_bv_unsigned]
  unfold bv_wrap
  rw [Int.emod_add_emod]
  congr 1

theorem bv_signed_hi (x : word) (Hx : 2 ^ 63 ≤ bv_unsigned x) :
    bv_signed x = bv_unsigned x - 2 ^ 64 := by
  unfold bv_signed bv_unsigned at *
  rw [BitVec.toInt_eq_toNat_cond]
  split <;> omega

theorem c_lts_neg_0 (x : word) (Hx : 2 ^ 63 ≤ bv_unsigned x) :
    c_lts x (Z_to_bv 64 0) = true := by
  change decide (bv_signed x < 0) = true
  rw [bv_signed_hi x Hx]
  have := u64_range x
  exact decide_eq_true (by omega)

theorem errno_ret_range (e : Int) (H1 : 1 ≤ e) (H2 : e ≤ 4095) :
    2 ^ 63 ≤ bv_unsigned (errno_ret e) ∧ bv_unsigned (errno_ret e) < 2 ^ 64 := by
  change 2 ^ 63 ≤ bv_unsigned (Z_to_bv 64 (-e)) ∧ bv_unsigned (Z_to_bv 64 (-e)) < 2 ^ 64
  rw [Z_to_bv_unsigned, bv_wrap64_mod]
  omega

theorem errno_ret_signed (e : Int) (H1 : 1 ≤ e) (H2 : e ≤ 4095) :
    bv_signed (errno_ret e) = -e := by
  rw [bv_signed_hi _ (errno_ret_range e H1 H2).1]
  change bv_unsigned (Z_to_bv 64 (-e)) - 2 ^ 64 = -e
  rw [Z_to_bv_unsigned, bv_wrap64_mod]
  omega

theorem c_lts_errno (e : Int) (H1 : 1 ≤ e) (H2 : e ≤ 4095) :
    c_lts (errno_ret e) (Z_to_bv 64 0) = true :=
  c_lts_neg_0 _ (errno_ret_range e H1 H2).1

theorem c_eq_small (x y : word) : c_eq x y = bv_eqb x y := rfl
theorem c_ltu_small (x y : word) : c_ltu x y = bv_ltu x y := rfl

theorem c_eq_neq (x y : word) (Hne : bv_unsigned x ≠ bv_unsigned y) : c_eq x y = false := by
  exact bv_eqb_neq x y (fun h => Hne (congrArg bv_unsigned h))

theorem c_eq_refl (x : word) : c_eq x x = true := PropExec.bv_eqb_refl x

theorem bytes_le_single (b : byte) : bytes_le_to_Z [b] = bv_unsigned b := by
  simp only [bytes_le_to_Z, bytes_le_to_nat, Nat.zero_shiftLeft, Nat.or_zero]
  rfl

theorem read_byte_at (segs : List Segment) (sp : word) (bytes pre s post : List byte) (j : Nat)
    (Hb : bytes = pre ++ s ++ post) (Hj : j < s.length)
    (Hnw : bv_unsigned sp + (bytes.length : Int) < 2 ^ 64) :
    rdn segs (stack_to_mem sp bytes) (sp + nat_to_word (pre.length + j)) 1 =
      some [s[j]?.getD (Z_to_bv 8 0)] := by
  obtain ⟨b, Hnth, Hskip⟩ := nth_error_skipn_cons s j Hj
  have Hsj : s = s.take j ++ b :: s.drop (j + 1) := by
    rw [← Hskip]
    exact (List.take_append_drop j s).symm
  have Hbytes : bytes = (pre ++ s.take j) ++ ([b] ++ (s.drop (j + 1) ++ post)) := by
    calc
      bytes = pre ++ s ++ post := Hb
      _ = pre ++ (s.take j ++ b :: s.drop (j + 1)) ++ post :=
        congrArg (fun t => pre ++ t ++ post) Hsj
      _ = _ := by simp only [List.append_assoc, List.cons_append, List.nil_append]
  have H := read_at_offset segs sp bytes (pre ++ s.take j) [b] (s.drop (j + 1) ++ post)
    1 Hbytes rfl Hnw
  rw [List.length_append, List.length_take, Nat.min_eq_left (Nat.le_of_lt Hj)] at H
  rw [Hnth]
  exact H

theorem read_byte_at_image (segs : List Segment) (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (uid hwcap : word) (draw : EntryDraw)
    (pre s post : List byte) (j : Nat)
    (Hb : build_stack_bytes ph sp argv envp uid hwcap draw = pre ++ s ++ post)
    (Hj : j < s.length)
    (Hnw : bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hwcap draw).length : Int) < 2 ^ 64) :
    rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hwcap draw))
      (sp + nat_to_word (pre.length + j)) 1 = some [s[j]?.getD (Z_to_bv 8 0)] := by
  obtain ⟨b, Hnth, Hskip⟩ := nth_error_skipn_cons s j Hj
  have Hsj : s = s.take j ++ b :: s.drop (j + 1) := by
    rw [← Hskip]
    exact (List.take_append_drop j s).symm
  have Hbytes : build_stack_bytes ph sp argv envp uid hwcap draw =
      (pre ++ s.take j) ++ ([b] ++ (s.drop (j + 1) ++ post)) := by
    calc
      build_stack_bytes ph sp argv envp uid hwcap draw = pre ++ s ++ post := Hb
      _ = pre ++ (s.take j ++ b :: s.drop (j + 1)) ++ post :=
        congrArg (fun t => pre ++ t ++ post) Hsj
      _ = _ := by simp only [List.append_assoc, List.cons_append, List.nil_append]
  have H := read_at_offset_image segs ph sp argv envp uid hwcap draw (pre ++ s.take j)
    [b] (s.drop (j + 1) ++ post) 1 Hbytes rfl Hnw
  rw [List.length_append, List.length_take, Nat.min_eq_left (Nat.le_of_lt Hj)] at H
  rw [Hnth]
  exact H

theorem nth_app0_bound (a1 : List byte) (j : Nat) :
    bv_unsigned ((a1 ++ [Z_to_bv 8 0])[j]?.getD (Z_to_bv 8 0)) < 256 :=
  (u8_range _).2

theorem entry_page_top_within_window (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (uid hwcap : word) (draw : EntryDraw)
    (Hfit : entry_stack_fits sp argv envp) :
    entry_page_top sp (build_stack_bytes ph sp argv envp uid hwcap draw) ≤ sp_window_hi := by
  have Hlen := build_stack_bytes_within_span ph sp argv envp uid hwcap draw
  unfold entry_stack_fits at Hfit
  unfold entry_page_top entry_block_top page_round_up_Z
  change ((bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hwcap draw).length : Int)
    + 4096 - 1) / 4096) * 4096 ≤ 140737488355328
  change bv_unsigned sp + entry_stack_span argv envp ≤ 140737488355328 at Hfit
  omega

section
open Lean Meta Elab Tactic

/-- Extract the Bool scrutinee of the two nondependent Boolean-if forms. -/
private def valueIfBool? (e : Expr) : Option Expr := do
  let b ← if e.isAppOfArity ``cond 4 then
      some (e.getArg! 1)
    else if e.isAppOfArity ``ite 5 then do
      let c := e.getArg! 1
      guard (c.isAppOfArity ``Eq 3 && (c.getArg! 0).isConstOf ``Bool &&
        (c.getArg! 2).isConstOf ``Bool.true)
      some (c.getArg! 1)
    else none
  guard (!b.isConstOf ``Bool.true && !b.isConstOf ``Bool.false && !b.hasLooseBVars)
  return b

private def splitValueIf : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let some e := target.find? (fun e => (valueIfBool? e).isSome)
    | throwError "no nonliteral Boolean if in the goal"
  let some b := valueIfBool? e | throwError "no Boolean scrutinee"
  let bs ← Term.exprToSyntax b
  if b.isFVar then
    evalTactic (← `(tactic| cases ($bs)))
  else
    evalTactic (← `(tactic| first
      | (generalize $bs:term = x at *; cases x)
      | cases ($bs)))

/-- Rocq's `split_value_ifs`: repeatedly destruct a nonliteral Bool scrutinee
of an if in the goal, on every resulting goal; the leaves are left for
conversion or another proof. With no eligible if, this succeeds unchanged.

As in Rocq, the scrutinee is found in the goal only (`|- context [...]`), the
search takes the outermost, leftmost if first, a scrutinee mentioning a
variable bound inside the goal is skipped, and literal `true`/`false`
scrutinees are skipped, as is an if on any condition that is not a Bool
(Lean: a Prop `if` such as `if b = false`, or a dependent `dite`; Rocq: a
`sumbool` one), the search going on to the next if. As Rocq's `destruct` does, the split replaces the
scrutinee in the hypotheses as well as the goal: `cases` does so for a local
variable; a compound scrutinee (such as the `bv_eqb rd 0` that
`step_pipeline` leaves) is first generalized in the goal and every hypothesis
(`generalize ... at *`), and only when that generalization fails is it split
in the goal alone.

Lean's ordinary `if b then ... else ...` for `b : Bool` elaborates to
`ite (b = true)` (the form in `getr`, `rset_mk` and the interpreter); `bif` is
`cond b`. Both are recognized without unfolding definitions; an explicit
`if b = true` is the same term and is split too. Differences from Rocq: Lean
orders the Bool cases false then true, opposite to Rocq, so bullets copied
after it swap; a Bool `match` is not split (Rocq's `if` is a `match`, so
Rocq's tactic splits one; Lean elaborates `match` to an auxiliary matcher,
which this does not recognize); and Lean's `repeat'` supplies Rocq's
repetition on all generated goals within its iteration bound, `focus`
confining it to the original main goal. No branch is simplified beyond the
reduction `cases` itself performs. The keyword is tactic-category syntax only
and remains usable as a term identifier. -/
elab "split_value_ifs" : tactic => focus do
  evalTactic (← `(tactic| repeat' (run_tac splitValueIf)))

-- Two different scrutinees: all four leaves must have been split.
example (b c : Bool) :
    (if b then 1 else 2) + (if c then 3 else 4) =
      (if c then 3 else 4) + (if b then 1 else 2) := by
  fail_if_success rfl
  split_value_ifs
  all_goals
    first
    | guard_target =~ (6 : Nat) = 6
    | guard_target =~ (5 : Nat) = 5
    | guard_target =~ (4 : Nat) = 4
  all_goals rfl

-- The same compound scrutinee on both sides, as after step_pipeline.
example (rd : reg) :
    (if bv_eqb rd 0 then 1 else 2) + 1 =
      (if bv_eqb rd 0 then 2 else 3) := by
  fail_if_success rfl
  split_value_ifs
  · guard_target =~ (3 : Nat) = 3
    rfl
  · guard_target =~ (2 : Nat) = 2
    rfl

-- cond/bif and ite share the same Bool; destruct replaces it everywhere.
example (b : Bool) : (bif b then 1 else 2) + 1 = (if b then 2 else 3) := by
  fail_if_success rfl
  split_value_ifs
  · guard_target =~ (3 : Nat) = 3
    rfl
  · guard_target =~ (2 : Nat) = 2
    rfl

-- A cond-only goal ensures bif support cannot pass via a neighboring ite.
example (b : Bool) : (bif b then 1 else 2) + 1 = (bif b then 2 else 3) := by
  fail_if_success rfl
  split_value_ifs
  · guard_target =ₛ (bif false then 1 else 2) + 1 = (bif false then 2 else 3)
    rfl
  · guard_target =ₛ (bif true then 1 else 2) + 1 = (bif true then 2 else 3)
    rfl

-- A successful repeat is not evidence of progress: pin the unchanged goal.
example (n : Nat) : n = n := by
  fail_if_success (split_value_ifs; guard_target =ₛ True)
  split_value_ifs
  guard_target =ₛ n = n
  rfl

example (p : Prop) [Decidable p] : (if p then 1 else 2) = (if p then 1 else 2) := by
  fail_if_success (split_value_ifs; guard_target =ₛ (1 : Nat) = 1)
  split_value_ifs
  guard_target =ₛ (if p then 1 else 2) = (if p then 1 else 2)
  rfl

example : (if true then 1 else 2) = (1 : Nat) := by
  fail_if_success (split_value_ifs; guard_target =ₛ (1 : Nat) = 1)
  split_value_ifs
  guard_target =ₛ (if true then 1 else 2) = (1 : Nat)
  rfl

example : (bif false then 1 else 2) = (2 : Nat) := by
  fail_if_success (split_value_ifs; guard_target =ₛ (2 : Nat) = 2)
  split_value_ifs
  guard_target =ₛ (bif false then 1 else 2) = (2 : Nat)
  rfl

-- A scrutinee bound inside the goal is skipped, and the search goes on to the
-- free one after it (Rocq does the same).
example (b : Bool) :
    (fun x : Bool => (if x then 1 else 2) + (if b then 1 else 2)) =
      (fun x : Bool => (if x then 1 else 2) + (if b then (1 : Nat) else 2)) := by
  split_value_ifs
  · guard_target =ₛ (fun x : Bool => (if x then 1 else 2) + (if false then 1 else 2)) =
      (fun x : Bool => (if x then 1 else 2) + (if false then (1 : Nat) else 2))
    rfl
  · guard_target =ₛ (fun x : Bool => (if x then 1 else 2) + (if true then 1 else 2)) =
      (fun x : Bool => (if x then 1 else 2) + (if true then (1 : Nat) else 2))
    rfl

-- Outermost first: the compound outer scrutinee is split whole, leaving two
-- goals, not the four an innermost-first search would.
example (b c : Bool) :
    (if (if c then b else false) then 1 else 2) =
      (if (if c then b else false) then 1 else (2 : Nat)) := by
  split_value_ifs
  · guard_target =ₛ (if false then 1 else 2) = (if false then 1 else (2 : Nat))
    rfl
  · guard_target =ₛ (if true then 1 else 2) = (if true then 1 else (2 : Nat))
    rfl

-- `if b = false` is a Prop condition, not a Bool if: left alone.
example (b : Bool) :
    (if b = false then 1 else 2) = (if b = false then 1 else (2 : Nat)) := by
  split_value_ifs
  guard_target =ₛ (if b = false then 1 else 2) = (if b = false then 1 else (2 : Nat))
  rfl

-- As Rocq's `destruct`, a compound scrutinee is replaced in hypotheses too.
example (f : Nat → Bool) (n : Nat) (H : (if f n then 1 else 2) = (0 : Nat)) :
    (if f n then 1 else 2) = (0 : Nat) := by
  split_value_ifs
  · guard_hyp H :ₛ (if false then 1 else 2) = (0 : Nat)
    guard_target =ₛ (if false then 1 else 2) = (0 : Nat)
    exact H
  · guard_hyp H :ₛ (if true then 1 else 2) = (0 : Nat)
    guard_target =ₛ (if true then 1 else 2) = (0 : Nat)
    exact H

-- And so is a local-variable scrutinee.
example (b : Bool) (H : (if b then 1 else 2) = (0 : Nat)) :
    (if b then 1 else 2) = (0 : Nat) := by
  split_value_ifs
  · guard_hyp H :ₛ (if false then 1 else 2) = (0 : Nat)
    exact H
  · guard_hyp H :ₛ (if true then 1 else 2) = (0 : Nat)
    exact H

-- A Bool `match` is not split (Rocq's tactic would split it): one goal stays.
example (b : Bool) : (match b with | true => 1 | false => (2 : Nat)) = 1 ∨ True := by
  split_value_ifs
  exact Or.inr trivial

example (split_value_ifs step_pipeline : Nat) :
    split_value_ifs + step_pipeline = step_pipeline + split_value_ifs := by
  exact Nat.add_comm _ _

end

/-! ## Additions for ticket T175 (#1384): shared word conversion helpers -/

/-- Shared Lean helper: stdpp's `Z_to_bv_bv_unsigned` at width 64. -/
theorem Z_to_bv_bv_unsigned64 (x : word) : Z_to_bv 64 (bv_unsigned x) = x := by
  unfold bv_unsigned Z_to_bv
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The unsigned value of the zero word, stated inline by `change` in
Rocq's AllocSim and named `u_Z_to_bv64_0` in SymExec. -/
theorem u_zero64 : bv_unsigned (Z_to_bv 64 0) = 0 := by decide

/-! ## Additions for ticket T175 (#1382): fault helpers for ErrEscape

These Lean-only helpers moved from `ErrEscape`, where ticket
E-proof-library-2c (#1333) added them. -/

/-- Lean-only helper: a step of `mkst regs pc mem rom` whose word is
fetched from the static image, is no ecall, and whose decoded instruction's
effect tree faults, at whatever size it decoded, is `MachineFault`. -/
theorem step_fault_of_interp (segs : List Segment) (regs : bvmap 5 word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (i : instr) (isz : Int)
    (hf : fetch_word segs pc = some w) (hne : is_ecall w = false)
    (hd : decode_any w = some (i, isz))
    (hi : interp_eff_accesses segs
      (exec (Z_to_bv 64 isz) i (core.Core regs bvmap_empty pc 0 none)) mem = MachineFault) :
    RiscvSemantics.step segs (mkst regs pc mem rom) = MachineFault := by
  rw [step_of_fetch segs (mkst regs pc mem rom) w hf]
  simp only [decode_exec, decode_exec_accesses, mkst, hne, Bool.false_eq_true,
    ↓reduceIte, hd]
  rw [hi]
  rfl

/-- Lean-only helper: a load whose `ov_read_bytes` read (the overlay, then
the loaded segments) misses faults. -/
theorem interp_load_none (segs : List Segment) (n : Nat) (a : word) (k : BitVec n → eff)
    (m : word → Option byte) (hr : ov_read_bytes segs m a (width_bytes n) = none) :
    interp_eff_accesses segs (.ELoad n a k) m = MachineFault := by
  simp only [interp_eff_accesses, hr]

end LinuxProcessSemantics.Common.PropExec
