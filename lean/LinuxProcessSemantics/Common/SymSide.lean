import Lean
import LinuxProcessSemantics.Common.StepTac
import LinuxProcessSemantics.Common.SymBranch
import LinuxProcessSemantics.Common.CatExec

/-! rocq-baseline: 2cde689f94c086b868999970834b76a25616b94a -/

/-! # Common.SymSide — nested-window normalization for `SymExec`'s address side conditions

Ported from `theories/Common/SymSide.v` at the baseline above.  The Rocq
file's Ltac definitions are Lean tactics here, under the Rocq names.  The
Rocq docstring says why innermost-first rewriting matters (a block that
crosses a call nests the `bv_unsigned (Z_to_bv 64 _)` projections); it is
not repeated here.

The Rocq tactics call `StepTac` Ltac definitions that `StepTac.lean` leaves
unported (its docstring): `u_norm` is SymBranch's `sym_u_norm`, and
`imm_norm` is `sym_imm_norm` below, under a name of its own for the same
reason; `check_closed_term` has no twin, and `decide` makes a closedness
check of its own.  `sym_close_open` calls stdpp's `f_equal`, which is
`sym_f_equal` below: Lean's `congr` does not stop where it stops.

These are not step-for-step twins: Lean's `rewrite`, `omega` and `decide`
are not Rocq's `rewrite`, `lia` and `vm_compute`, so some goals close on
one side and not the other.  The tactic names stay usable as identifiers
(the last example). -/

namespace LinuxProcessSemantics.Common.SymSide

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.Common.PropExec

section
open Lean Meta Elab Tactic

/-- `n` is the numeral `64`. -/
private def isN64 (e : Expr) : Bool := e.nat? == some 64 || e.rawNatLit? == some 64

/-- The `z` of `bv_unsigned (Z_to_bv 64 z)`. -/
private def uZ? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``bv_unsigned 2 then
    let w := e.appArg!
    if w.isAppOfArity ``Z_to_bv 2 && isN64 w.appFn!.appArg! then some w.appArg! else none
  else none

/-- `z` holds a `Z_to_bv 64 _` (Rocq's `context [Z_to_bv 64 _]`). -/
private def hasZ64 (z : Expr) : Bool :=
  (z.find? fun s => s.isAppOfArity ``Z_to_bv 2 && isN64 s.appFn!.appArg!).isSome

/-- The `z`s of the `bv_unsigned (Z_to_bv 64 z)` instances in `e`, each
once, outermost first and left to right. -/
private def uZs : Expr → Array Expr → Array Expr
  | .app f a, acc =>
    let acc := match uZ? (.app f a) with
      | some z => if acc.contains z then acc else acc.push z
      | none => acc
    uZs a (uZs f acc)
  | .lam _ t b _, acc => uZs b (uZs t acc)
  | .forallE _ t b _, acc => uZs b (uZs t acc)
  | .letE _ t v b _, acc => uZs b (uZs v (uZs t acc))
  | .mdata _ b, acc => uZs b acc
  | .proj _ _ b, acc => uZs b acc
  | _, acc => acc

/-- `u_norm_deep`, in the goal or in hypothesis `h?`.  A failing attempt
throws, and the state saved before it is restored.  `focus` keeps the
rewritten goal first, so the next pass reads it and not the goal after it. -/
private def uNormDeepAt (h? : Option Ident) : TacticM Unit := do
  repeat
    let progress ← withMainContext do
      let t ← match h? with
        | none => getMainTarget
        | some h => pure (← getLocalDeclFromUserName h.getId).type
      let mut progress := false
      for z in uZs (← instantiateMVars t) #[] do
        if z.hasLooseBVars || hasZ64 z then continue
        let s ← saveState
        try
          let zs ← Term.exprToSyntax z
          match h? with
          | none => evalTactic (← `(tactic|
              (focus (rewrite [StepTac.u_Z2bv $zs]; rotate_left; omega; omega))))
          | some h => evalTactic (← `(tactic|
              (focus (rewrite [StepTac.u_Z2bv $zs] at $h:ident; rotate_left; omega; omega))))
          progress := true
          break
        catch _ => s.restore
      pure progress
    if !progress then break

/-- Rocq's `u_norm_deep`: collapse `bv_unsigned (Z_to_bv 64 z)` to `z`,
innermost first, while `omega` closes `0 ≤ z` and `z < 2 ^ 64`, in the
first goal alone.  An instance whose `z` still holds a `Z_to_bv 64 _` is
passed over (Rocq's `lazymatch` guard, which makes the collapse innermost
first), and so is one whose side conditions fail or whose `z` mentions a
variable bound inside the goal; after each rewrite the search starts
again.  So a failing instance does not stop it, where it stops
`sym_u_norm`.  With the projection width written as `32 + 32` and the
inner conversion still `Z_to_bv 64 z`, Lean collapses the projection;
Rocq's `u_norm_deep` leaves that spelling unchanged (the width-expression
example below). -/
elab "u_norm_deep" : tactic => uNormDeepAt none

/-- Rocq's `u_norm_deep_in H`: `u_norm_deep` in hypothesis `h`, whose side
conditions `omega` proves from the whole context, as Rocq's `lia` does.
That context holds `h` as the earlier rewrites left it, so collapsing one
instance can take away the link a later one's bound needs. -/
elab "u_norm_deep_in " h:ident : tactic => uNormDeepAt (some h)

private def litWord? (b : Expr) : MetaM (Option (Nat × Nat)) := do
  let num? (e : Expr) : Option Nat := e.nat? <|> e.rawNatLit?
  if b.isAppOfArity ``OfNat.ofNat 3 && (b.getArg! 2).isAppOf ``BitVec.instOfNat then
    let ty ← whnfR (b.getArg! 0)
    if ty.isAppOfArity ``BitVec 1 then
      if let (some n, some k) := (num? (ty.getArg! 0), (b.getArg! 1).rawNatLit?) then
        return some (n, k)
  if b.isAppOfArity ``BitVec.ofNat 2 || b.isAppOfArity ``BitVec.ofNatLT 3 then
    if let (some n, some k) := (num? (b.getArg! 0), num? (b.getArg! 1)) then
      return some (n, k)
  if b.isAppOfArity ``BitVec.ofFin 2 then
    let f := b.getArg! 1
    if f.isAppOfArity ``Fin.mk 3 then
      if let (some n, some k) := (num? (b.getArg! 0), num? (f.getArg! 1)) then
        return some (n, k)
  return none

/-- The `Int` numeral `v`, negated for a negative `v`. -/
private def mkIntLit (v : Int) : MetaM Expr := do
  if 0 ≤ v then mkNumeral (mkConst ``Int) v.toNat
  else mkAppM ``Neg.neg #[← mkNumeral (mkConst ``Int) (-v).toNat]

/-- Rocq's `StepTac.imm_norm`: replace `bv_signed b` and `bv_unsigned b`
in the first goal alone, for a word `b` that `litWord?` reads as a literal,
by the `Int` numeral it reads as, by conversion (Rocq's `change`, of the
value `vm_compute` gives).  A word it does not read keeps its reading, which
`omega` then sees as an atom.  The value is computed here and checked
against the reading by `isDefEq`, which fails the tactic rather than
change the goal to a numeral the reading is not.  Rocq matches the
constructor `@BV n k H`, including a computed width or payload and a
variable payload; the computed- and variable-payload examples below show
where Lean leaves an atom that Rocq's `imm_norm` reduces.

The conversion check raises `exponentiation.threshold` to at least the
word's width, preserving a higher caller setting.  The width-65536
`#guard_msgs` examples below reject the tested fixed thresholds of 1000
and 65535.  A fixed threshold of 65536 or more survives those pins, as
does a sufficient fixed raise around the whole transform.  A finite-width
pin leaves larger fixed thresholds untested. -/
elab "sym_imm_norm" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let t' ← Meta.transform t (post := fun s => do
    let uns := s.isAppOfArity ``bv_unsigned 2
    if uns || s.isAppOfArity ``bv_signed 2 then
      if let some (n, k) ← litWord? s.appArg! then
        let u : Int := ((k % 2 ^ n : Nat) : Int)
        let v ← mkIntLit (if uns || 2 * u < 2 ^ n then u else u - 2 ^ n)
        let raise (o : Options) :=
          exponentiation.threshold.set o (max (exponentiation.threshold.get o) n)
        unless ← withOptions raise (withAtLeastTransparency .default (isDefEq s v)) do
          throwError "sym_imm_norm: {s} does not reduce to {v}"
        return .done v
    return .continue)
  if t' != t then replaceMainGoal [← g.replaceTargetDefEq t']

end

/-- Rocq's `vm_closed`, on the first goal alone.  `+kernel` evaluates in
the kernel, which gets through `reg_get` where `decide`'s own evaluation
does not (pinned). -/
macro "vm_closed" : tactic => `(tactic| decide +kernel)

/-- stdpp's `f_equal` (`stdpp.tactics.f_equal`, the one `SymSide.v` calls)
without its outer `try`.  It never splits an argument goal.

`rfl` and `apply` are reducible, where stdpp's `reflexivity` and `apply`
unfold definitions.  At default transparency `rfl` and
`apply congrFun` can run into `maxRecDepth` on an offset goal (pinned). -/
syntax "sym_f_equal" : tactic
macro_rules
  | `(tactic| sym_f_equal) => `(tactic| first
    | with_reducible rfl
    | (focus
        with_reducible apply congr
        focus sym_f_equal
        all_goals try with_reducible rfl)
    | (focus
        with_reducible apply congrFun
        sym_f_equal))

/-- Rocq's `sym_close_open`, on the first goal alone: `reflexivity`; or
`f_equal`, then `lia` on the goals it leaves; or `bv_eq_of_unsigned`
(Rocq's `bv_eq`), `u_norm` and `lia`.  The first alternative is a shortcut in both: `f_equal` starts
with the same `reflexivity`.  `rfl` is reducible for the reason
`sym_f_equal`'s docstring gives. -/
macro "sym_close_open" : tactic => `(tactic| first
  | with_reducible rfl
  | ((try sym_f_equal) <;> omega)
  | (apply PropExec.bv_eq_of_unsigned <;> sym_u_norm <;> omega))

/-- Rocq's `sym_sc`, on the first goal alone: `imm_norm`, `u_norm_deep`,
`u_norm`, `imm_norm`, `repeat split`, `lia`.

Rocq's `split` (Rocq 9.2, `tactics/tactics.ml`, `constructor_tac`)
introduces the goal's premises and applies its only constructor, or fails
as a whole.  Here it is `repeat intro`, then
`apply And.intro`, `exact True.intro`, `apply Iff.intro` or
`with_reducible rfl`, undone if none applies, repeated on every goal. -/
macro "sym_sc" : tactic => `(tactic|
  sym_imm_norm <;> u_norm_deep <;> sym_u_norm <;> sym_imm_norm <;>
  (repeat' ((repeat intro); first
    | apply And.intro | exact True.intro | apply Iff.intro | with_reducible rfl)) <;>
  omega)

/-- Rocq's `rdn_side`, on the first goal alone:
`rewrite ?length_N_to_le_bytes`, `cbn [length]`, then `sym_sc`'s steps
without its `repeat split`.  `cbn [length]` is
`dsimp only [List.length_cons, List.length_nil]`: both compute the length
of a literal list and β-reduce (pinned). -/
macro "rdn_side" : tactic => `(tactic|
  (repeat rewrite [CatExec.length_N_to_le_bytes]) <;>
  (try dsimp only [List.length_cons, List.length_nil]) <;>
  sym_imm_norm <;> u_norm_deep <;> sym_u_norm <;> sym_imm_norm <;> omega)

/-! ### `sym_sc` -/

-- A cross-call frame: the projection nests two deep.
example (rsp : word) (h1 : 4096 ≤ bv_unsigned rsp) (h2 : bv_unsigned rsp < 2 ^ 47) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 96)) - 160)) + 8
      ≤ bv_unsigned rsp := by
  sym_sc
-- A literal immediate (`-8` as a 12-bit word), under a conjunction.
example (rsp : word) (h1 : 4096 ≤ bv_unsigned rsp) (h2 : bv_unsigned rsp < 2 ^ 47) :
    0 ≤ bv_unsigned (Z_to_bv 64 (bv_unsigned rsp + bv_signed (0xff8#12))) ∧
    bv_unsigned (Z_to_bv 64 (bv_unsigned rsp + bv_signed (0xff8#12))) < bv_unsigned rsp := by
  sym_sc
-- Literal spellings `sym_imm_norm` reads.  A non-literal operand keeps
-- its `bv_unsigned` form, so `h` still applies.
example (x : word) (h : bv_unsigned x = 3) : bv_unsigned x + bv_unsigned (5 : word) = 8 := by
  sym_sc
example (x : word) (h : bv_unsigned x = 3) : bv_unsigned x + bv_signed (5 : word) = 8 := by
  sym_sc
example (rsp : word) : bv_unsigned rsp + bv_signed (4088 : BitVec 12) < bv_unsigned rsp := by
  sym_sc
example (x : word) (h : bv_unsigned x = 3) : bv_unsigned x + bv_unsigned (5#64) = 8 := by
  sym_sc
example (x : word) (h : bv_unsigned x = 3) :
    bv_unsigned x + bv_unsigned (BitVec.ofNatLT 5 (by decide) : word) = 8 := by
  sym_sc
example (x : word) (h : bv_unsigned x = 3) :
    bv_unsigned x + bv_unsigned (BitVec.ofFin ⟨5, by decide⟩ : word) = 8 := by
  sym_sc
example (rsp : word) :
    bv_unsigned rsp + bv_signed (BitVec.ofNatLT 4088 (by decide) : BitVec 12) < bv_unsigned rsp := by
  sym_sc
example (rsp : word) :
    bv_unsigned rsp + bv_signed (BitVec.ofFin ⟨4088, by decide⟩ : BitVec 12) < bv_unsigned rsp := by
  sym_sc
example (x : word) (h : bv_unsigned x = 3000) :
    bv_unsigned x + bv_signed (2048 : BitVec 12) = 952 := by sym_sc
example (rsp : word) : bv_unsigned rsp + bv_signed (2047#12) = bv_unsigned rsp + 2047 := by sym_sc
example (x : word) (h : bv_unsigned x = 3) : bv_unsigned x + bv_unsigned (300 : BitVec 8) = 47 := by
  sym_sc
example (x : word) (h : bv_unsigned x = 3) : bv_unsigned x + bv_unsigned (0xff8#12) = 4091 := by
  sym_sc
example (x : word) (h : bv_unsigned x = 3) :
    bv_unsigned x + bv_unsigned (5 : BitVec (nat_lit 64)) = 8 := by sym_sc
example (x : word) (h : bv_unsigned x = 3) :
    bv_unsigned x + bv_unsigned (BitVec.ofNat 64 (nat_lit 5)) = 8 := by sym_sc
example (F : Int → Int) : F (bv_signed (0#12)) = F 0 := by sym_sc
#guard_msgs in
example (x : word) (h : bv_unsigned x = 3) : bv_unsigned x + bv_unsigned (5 : BitVec 500) = 8 := by
  sym_sc
#guard_msgs in
example (x : word) (h : bv_unsigned x = 3) : bv_unsigned x + bv_signed (5 : BitVec 500) = 8 := by
  sym_sc
#guard_msgs in
example (x : word) (h : bv_unsigned x = 3) : bv_unsigned x + bv_unsigned (5 : BitVec 1000) = 8 := by
  sym_sc
#guard_msgs in
example (x : word) (h : bv_unsigned x = 3) : bv_unsigned x + bv_signed (5 : BitVec 1000) = 8 := by
  sym_sc
-- The width-derived threshold is needed by both readings; the guards also
-- reject the warning produced by a fixed threshold of 65535.
#guard_msgs in
example : bv_unsigned (5 : BitVec 65536) = 5 := by sym_imm_norm; rfl
#guard_msgs in
example : bv_signed (5 : BitVec 65536) = 5 := by sym_imm_norm; rfl
-- With `exponentiation.threshold` lowered below the width.
set_option exponentiation.threshold 32 in
#guard_msgs in
example (x : word) (h : bv_unsigned x = 3) : bv_unsigned x + bv_unsigned (5 : word) = 8 := by
  sym_sc
set_option exponentiation.threshold 32 in
#guard_msgs in
example (x : word) (h : bv_unsigned x = 3) : bv_unsigned x + bv_signed (5 : word) = 8 := by
  sym_sc
-- With `exponentiation.threshold` raised above an exponent in the width.
set_option exponentiation.threshold 400 in
#guard_msgs in
example (x : word) (h : bv_unsigned x = 3) :
    bv_unsigned x + @bv_signed (64 + 0 * 2 ^ 300) (5 : BitVec 64) = 8 := by
  sym_sc
-- Under `with_reducible`.
example (x : word) (h : bv_unsigned x = 3) : bv_unsigned x + bv_unsigned (5 : BitVec 64) = 8 := by
  with_reducible sym_imm_norm
  omega

-- Lean refuses to replace this reading by 7 modulo 4.  Rocq's `imm_norm`
-- reads the stored 7 in `@BV 2 7 H`, even under the contradictory bound.
example (h : 7 < 2 ^ 2) : bv_unsigned (BitVec.ofNatLT 7 h : BitVec 2) = 7 := by
  fail_if_success sym_imm_norm
  rfl
-- A payload of `2 ^ 300 + 5` at width 300, behind a false bound: refused.
example (h : 2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397381 < 2 ^ 300) :
    bv_unsigned (BitVec.ofNatLT 2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397381 h) =
      bv_unsigned (BitVec.ofNatLT 2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397381 h) := by
  fail_if_success sym_imm_norm
  rfl
-- Spellings Lean does not read: `omega` sees an atom and fails.
-- Rocq's `sym_sc` also refuses the `Z_to_bv 12 (-8)` twin below.
example (rsp : word) : bv_unsigned rsp + bv_signed (-8 : BitVec 12) < bv_unsigned rsp := by
  fail_if_success sym_sc
  have h : bv_signed (-8 : BitVec 12) = -8 := by decide
  omega
example (rsp : word) : bv_unsigned rsp + bv_signed (Z_to_bv 12 (-8)) < bv_unsigned rsp := by
  fail_if_success sym_sc
  have h : bv_signed (Z_to_bv 12 (-8)) = -8 := by decide
  omega
example (rsp : word) : bv_unsigned rsp + bv_signed (BitVec.ofInt 12 (-8)) < bv_unsigned rsp := by
  fail_if_success sym_sc
  have h : bv_signed (BitVec.ofInt 12 (-8)) = -8 := by decide
  omega
-- With payload `2 + 3` or width `32 + 32`, Rocq's `imm_norm` reduces
-- the `@BV` twins and `sym_sc` closes them; Lean refuses these spellings.
example (x : word) (h : bv_unsigned x = 3) :
    bv_unsigned x + bv_unsigned (BitVec.ofNat 64 (2 + 3)) = 8 := by
  fail_if_success sym_sc
  have e : bv_unsigned (BitVec.ofNat 64 (2 + 3)) = 5 := by decide
  omega
example (x : word) (h : bv_unsigned x = 3) :
    bv_unsigned x + bv_unsigned (5 : BitVec (32 + 32)) = 8 := by
  fail_if_success sym_sc
  have e : bv_unsigned (5 : BitVec (32 + 32)) = 5 := by decide
  omega
example (x : word) (h : bv_unsigned x = 3) :
    bv_unsigned x + bv_unsigned (BitVec.ofNat (32 + 32) 5) = 8 := by
  fail_if_success sym_sc
  have e : bv_unsigned (BitVec.ofNat (32 + 32) 5) = 5 := by decide
  omega
example (x : word) (h : bv_unsigned x = 3) :
    bv_unsigned x + bv_unsigned (BitVec.ofFin (w := 32 + 32) ⟨5, by decide⟩) = 8 := by
  fail_if_success sym_sc
  have e : bv_unsigned (BitVec.ofFin (w := 32 + 32) ⟨5, by decide⟩) = 5 := by decide
  omega
example (x : word) (h : bv_unsigned x = 3) :
    bv_unsigned x + bv_unsigned (BitVec.ofFin ⟨2 + 3, by decide⟩ : word) = 8 := by
  fail_if_success sym_sc
  have e : bv_unsigned (BitVec.ofFin ⟨2 + 3, by decide⟩ : word) = 5 := by decide
  omega
example (x : word) (h : bv_unsigned x = 3) :
    bv_unsigned x + bv_unsigned (@OfNat.ofNat (BitVec 64) (2 + 3) _) = 8 := by
  fail_if_success sym_sc
  have e : bv_unsigned (@OfNat.ofNat (BitVec 64) (2 + 3) _) = 5 := by decide
  omega
-- A word that is not a literal keeps its reading, under both readings.
example (n : Nat) (h : bv_unsigned (BitVec.ofNat 64 n) = 3) :
    bv_unsigned (BitVec.ofNat 64 n) + 5 = 8 := by
  sym_sc
example (n : Nat) (h : bv_signed (BitVec.ofNat 64 n) = 3) :
    bv_signed (BitVec.ofNat 64 n) + 5 = 8 := by
  sym_sc
-- A variable constructor payload: Lean's `sym_sc` refuses these two
-- goals, while Rocq's `imm_norm` exposes `m` in `@BV 64 m hm`, and its
-- `sym_sc` closes the twin from `m = 3`.
example (m : Nat) (hm : m < 2 ^ 64) (h : m = 3) :
    bv_unsigned (BitVec.ofFin ⟨m, hm⟩ : word) + 5 = 8 := by
  fail_if_success sym_sc
  show ((m : Int)) + 5 = 8
  omega
example (m : Nat) (hm : m < 2 ^ 64) (h : m = 3) :
    bv_unsigned (BitVec.ofNatLT m hm : word) + 5 = 8 := by
  fail_if_success sym_sc
  show ((m : Int)) + 5 = 8
  omega
example (m : Nat) (hm : m < 2 ^ 64) (h : bv_unsigned (BitVec.ofFin ⟨m, hm⟩ : word) < 5) :
    bv_unsigned (BitVec.ofFin ⟨m, hm⟩ : word) < 6 := by
  sym_sc
example (m : Nat) (hm : m < 2 ^ 64) (h : bv_unsigned (BitVec.ofNatLT m hm : word) < 5) :
    bv_unsigned (BitVec.ofNatLT m hm : word) < 6 := by
  sym_sc
-- A numeral through an instance other than `BitVec.instOfNat` keeps its reading.
example [OfNat (BitVec 64) 5] (x : word) (h : bv_unsigned x = bv_unsigned (5 : BitVec 64)) :
    bv_unsigned x = bv_unsigned (5 : BitVec 64) := by
  sym_imm_norm
  exact h
-- A local instance is a constant too: checking only for a free variable
-- would mistake this spelling of 5 for the standard instance.
section
local instance : OfNat (BitVec 64) 5 := ⟨7#64⟩
example : bv_unsigned (5 : BitVec 64) = 7 := by sym_imm_norm; decide
end
-- A projection whose side conditions `omega` cannot prove keeps its form,
-- so `h` still applies.
example (n : Int) (h : bv_unsigned (Z_to_bv 64 n) = 3) : bv_unsigned (Z_to_bv 64 n) + 5 = 8 := by
  sym_sc
-- Two instances `u_norm_deep` passes over, each argument holding a
-- `Z_to_bv 64` literal: `sym_u_norm` collapses both, as Rocq's `u_norm`
-- does.
example (x : word) (h1 : 0 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40)
    (h5 : bv_signed (Z_to_bv 64 5) = 5) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned x + bv_signed (Z_to_bv 64 5)))
      + bv_unsigned (Z_to_bv 64 (bv_unsigned x + 8 + bv_signed (Z_to_bv 64 5)))
      = 2 * bv_unsigned x + 18 := by
  sym_sc
-- The `repeat split` twin: a `True` conjunct, and conjuncts that hold
-- syntactically, close as in Rocq.
example (rsp : word) (h1 : 4096 ≤ bv_unsigned rsp) (h2 : bv_unsigned rsp < 2 ^ 47) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 8)) < bv_unsigned rsp ∧ True := by
  sym_sc
example (x : word) (h : bv_unsigned x < 5) : bv_unsigned x < 6 ∧ Z_to_bv 64 5 = Z_to_bv 64 5 := by
  sym_sc
example (x : word) (h : bv_unsigned x < 5) : bv_unsigned x < 6 ∧ x = x := by
  sym_sc

-- Lean's `sym_sc` refuses these four goals.  In Rocq, `split` closes
-- the definitional equations and the closed strict bound by conversion;
-- `sym_sc` closes the full twins, including their arithmetic conjuncts.
example (x : word) (h : bv_unsigned x < 5) :
    bv_unsigned x < 6 ∧ v_addi x 0 = Z_to_bv 64 (bv_unsigned x + 0) := by
  fail_if_success sym_sc
  exact ⟨by omega, rfl⟩
example (x : word) (h : bv_unsigned x < 5) :
    bv_unsigned x < 6 ∧ Z_to_bv 64 (2 + 3) = Z_to_bv 64 5 := by
  fail_if_success sym_sc
  exact ⟨by omega, by vm_closed⟩
example (x : word) (h : bv_unsigned x < 5) :
    bv_unsigned x < 6 ∧ bv_unsigned (Z_to_bv 64 (2 ^ 64 + 5)) < 10 := by
  fail_if_success sym_sc
  exact ⟨by omega, by vm_closed⟩
example : bv_unsigned (Z_to_bv 64 (2 ^ 64 + 5)) < 10 := by
  fail_if_success sym_sc
  vm_closed
-- Premises are introduced first, as Rocq's `split` does.
example (x : word) : bv_unsigned x < 5 → x = x := by sym_sc
example : ∀ w : word, w = w := by sym_sc
example (x : word) : bv_unsigned x < 5 → bv_unsigned x < 6 → x = x := by sym_sc
example : ∀ w : word, bv_unsigned w < 5 → w = w := by sym_sc
example (x : word) : bv_unsigned x < 5 → bv_unsigned x < 6 ∧ x = x := by sym_sc
example (x : word) : bv_unsigned x < 5 → True := by sym_sc
example (x : word) (h : bv_unsigned x < 5) : bv_unsigned x < 6 ∧ (bv_unsigned x < 7 → x = x) := by
  sym_sc
example (x : word) (h : bv_unsigned x < 5) : bv_unsigned x < 6 ∧ (True → x = x) := by sym_sc
private def ZzImp (P Q : Prop) : Prop := P → Q
private def ZzImpEq (x : word) : Prop := bv_unsigned x < 5 → x = x
example (x : word) : ZzImp (bv_unsigned x < 5) (x = x) := by sym_sc
example (x : word) : ZzImpEq x := by sym_sc
-- `∧`, `True` and `↔` behind a definition split as well.
private def Zz7And (P Q : Prop) : Prop := P ∧ Q
private def Zz7True : Prop := True
private def Zz7Iff (P Q : Prop) : Prop := P ↔ Q
example (x : word) (h : bv_unsigned x < 5) : Zz7And (bv_unsigned x < 6) (bv_unsigned x < 7) := by
  sym_sc
example (x : word) (h : bv_unsigned x < 5) : bv_unsigned x < 6 ∧ Zz7True := by sym_sc
example (x : word) (h : bv_unsigned x < 5) : Zz7Iff (bv_unsigned x < 6) (bv_unsigned x ≤ 5) := by
  sym_sc
example (x : word) : bv_unsigned x < 5 → Zz7Iff (bv_unsigned x < 6) (bv_unsigned x ≤ 5) := by
  sym_sc
-- No constructor applies once the premise is introduced: fails, as Rocq's
-- does.
example (x : word) (P : Prop) (hP : P) : bv_unsigned x < 5 → P := by
  fail_if_success sym_sc
  intro
  exact hP
example (P : Prop) : P → P := by
  fail_if_success sym_sc
  exact id
-- An equation behind a definition: fails, where Rocq's `split` closes it.
private def ZzEq (a b : word) : Prop := a = b
example (x : word) : ZzEq x x := by
  fail_if_success sym_sc
  exact rfl
example (x : word) (h : bv_unsigned x < 5) : bv_unsigned x < 6 ∧ ZzEq x x := by
  fail_if_success sym_sc
  exact ⟨by omega, rfl⟩
-- With two goals open, it closes the first and leaves the second.
example (x : word) (h : bv_unsigned x < 5) : bv_unsigned x < 6 ∧ (bv_unsigned x < 7 ∧ True) := by
  constructor; sym_sc; guard_target =ₛ bv_unsigned x < 7 ∧ True; sym_sc
-- `↔` splits into two implications, which neither closer proves: fails,
-- as Rocq's does.
example (P : Prop) : P ↔ P := by
  fail_if_success sym_sc
  exact Iff.rfl
-- A conjunct that a hypothesis states closes here and not in Rocq; bounds
-- with a real solution and no integer one fail here and close in Rocq.
example (x : word) (P : Prop) (hP : P) (h : bv_unsigned x < 5) : bv_unsigned x < 6 ∧ P := by
  sym_sc
example (a b : Int) (h1 : 27 ≤ 11 * a + 13 * b) (h2 : 11 * a + 13 * b ≤ 45)
    (h3 : -10 ≤ 7 * a - 9 * b) (h4 : 7 * a - 9 * b ≤ 4) : bv_unsigned (Z_to_bv 64 a) < 0 := by
  fail_if_success sym_sc
  exfalso
  have ha : a = 1 ∨ a = 2 := by omega
  rcases ha with rfl | rfl <;> omega
-- `u_norm_deep` runs before `sym_u_norm`, and the first `sym_imm_norm`
-- before both, as in Rocq (`rdn_side` likewise).
example (x : word) (h0 : 1 ≤ bv_unsigned x) (h1 : bv_unsigned x < 2 ^ 40)
    (_hB : 1 ≤ bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1)))
    (_hB' : bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1)) < 2 ^ 40)
    (h3 : bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1 - 1)) ≤ 7) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1)) - 1)) < 8 := by
  sym_sc
example (x : word) (h0 : 1 ≤ bv_unsigned x) (h1 : bv_unsigned x < 2 ^ 40)
    (_hB : 1 ≤ bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1)))
    (_hB' : bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1)) < 2 ^ 40)
    (h3 : bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1 - 1)) ≤ 7) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1)) - 1)) < 8 := by
  rdn_side
example (z : Int) (h0 : 0 ≤ z) (h1 : z < 2 ^ 60) (hI : 10 ≤ bv_unsigned (Z_to_bv 64 z))
    (hI2 : bv_unsigned (Z_to_bv 64 z) < 2 ^ 60) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 z) - 10)) + 10 = z := by
  fail_if_success sym_sc
  fail_if_success rdn_side
  rw [StepTac.u_Z2bv (bv_unsigned (Z_to_bv 64 z) - 10) (by omega) (by omega),
    StepTac.u_Z2bv z (by omega) (by omega)]
  omega
example (x : word) (h1 : 8 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned x + bv_signed (0xff8#12))) + 16))
      = bv_unsigned x + 8 := by
  sym_sc
example (x : word) (h1 : 8 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned x + bv_signed (0xff8#12))) + 16))
      = bv_unsigned x + 8 := by
  rdn_side

/-! ### `u_norm_deep` and `u_norm_deep_in` -/

-- A width expression on the projection: Lean collapses it, while Rocq's
-- `u_norm_deep` leaves the spelling unchanged.
example (z : Int) (h0 : 0 ≤ z) (h1 : z < 2 ^ 64) :
    @bv_unsigned (32 + 32) (Z_to_bv 64 z) = z := by
  u_norm_deep
  guard_target =ₛ z = z
  rfl

example (rsp : word) (h1 : 4096 ≤ bv_unsigned rsp) (h2 : bv_unsigned rsp < 2 ^ 47) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 96)) - 160))
      = bv_unsigned rsp - 256 := by
  u_norm_deep
  omega
example (rsp : word) (h1 : 4096 ≤ bv_unsigned rsp) (h2 : bv_unsigned rsp < 2 ^ 47)
    (h : bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 96)) - 160)) = 7) :
    False := by
  u_norm_deep_in h
  omega
-- A hypothesis the rewrite makes reflexive stays an equation, as in Rocq.
example (x : word) (h1 : 0 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 64)
    (h : bv_unsigned (Z_to_bv 64 (bv_unsigned x)) = bv_unsigned x) :
    bv_unsigned x = bv_unsigned x := by
  u_norm_deep_in h
  exact h
-- Nothing to rewrite: a no-op, not a failure.
example (a : Int) (h : a < 5) : a < 6 := by
  u_norm_deep
  omega
-- The projection inside a conjunction, a disjunction and a negation, and
-- alone; `sym_sc` and `rdn_side` close the first two as well, as in Rocq.
example (rsp : word) (h1 : 4096 ≤ bv_unsigned rsp) (h2 : bv_unsigned rsp < 2 ^ 47) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 96)) = bv_unsigned rsp - 96 ∧ 0 ≤ bv_unsigned rsp := by
  u_norm_deep
  omega
example (rsp : word) (h1 : 4096 ≤ bv_unsigned rsp) (h2 : bv_unsigned rsp < 2 ^ 47) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 96)) = bv_unsigned rsp - 96 ∧ 0 ≤ bv_unsigned rsp := by
  sym_sc
example (rsp : word) (h1 : 4096 ≤ bv_unsigned rsp) (h2 : bv_unsigned rsp < 2 ^ 47) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 96)) = bv_unsigned rsp - 96 ∧ 0 ≤ bv_unsigned rsp := by
  rdn_side
example (rsp : word) (h1 : 4096 ≤ bv_unsigned rsp) (h2 : bv_unsigned rsp < 2 ^ 47) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 96)) = bv_unsigned rsp - 96 ∨ bv_unsigned rsp = 0 := by
  u_norm_deep
  omega
example (rsp : word) (h1 : 4096 ≤ bv_unsigned rsp) (h2 : bv_unsigned rsp < 2 ^ 47) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 96)) = bv_unsigned rsp - 96 ∨ bv_unsigned rsp = 0 := by
  sym_sc
example (rsp : word) (h1 : 4096 ≤ bv_unsigned rsp) (h2 : bv_unsigned rsp < 2 ^ 47) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 96)) = bv_unsigned rsp - 96 ∨ bv_unsigned rsp = 0 := by
  rdn_side
example (rsp : word) (h1 : 4096 ≤ bv_unsigned rsp) (h2 : bv_unsigned rsp < 2 ^ 47)
    (h : ¬ bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 96)) = bv_unsigned rsp - 96) : False := by
  u_norm_deep_in h
  omega
example (rsp : word) (h1 : 4096 ≤ bv_unsigned rsp) (h2 : bv_unsigned rsp < 2 ^ 47) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 96)) = bv_unsigned rsp - 96 := by
  u_norm_deep
  omega
-- The first instance's side conditions fail and the second's hold: the
-- second collapses, where `sym_u_norm` stops at the first; Rocq's
-- `u_norm_deep` and `u_norm` do the same.
example (x : word) (h0 : 0 ≤ bv_unsigned x) (h1 : bv_unsigned x < 2 ^ 40) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1)) + bv_unsigned (Z_to_bv 64 (bv_unsigned x + 1))
      = bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1)) + bv_unsigned x + 1 := by
  fail_if_success (sym_u_norm; omega)
  u_norm_deep
  omega
-- An instance under a binder whose `z` is the bound variable is passed
-- over, and the later one collapses, as in Rocq.
example (x : word) (h0 : 0 ≤ bv_unsigned x) (h1 : bv_unsigned x < 2 ^ 40) :
    (∀ y : Int, bv_unsigned (Z_to_bv 64 y) = bv_unsigned (Z_to_bv 64 y)) ∧
      bv_unsigned (Z_to_bv 64 (bv_unsigned x)) = bv_unsigned x := by
  u_norm_deep
  exact ⟨fun _ => rfl, rfl⟩
-- So is one whose `z` holds a bound variable that reduces away.
example (c : Int) (hc0 : 0 ≤ c) (hc1 : c < 2 ^ 64) :
    (∀ h : 0 ≤ c, bv_unsigned (Z_to_bv 64 (Subtype.val (⟨c, h⟩ : {x : Int // 0 ≤ x}))) = c) ∧
      bv_unsigned (Z_to_bv 64 c) = c := by
  u_norm_deep; exact ⟨fun _ => StepTac.u_Z2bv c hc0 hc1, rfl⟩
-- Instances in a premise, under a `fun` and in a `let` value collapse.
example (rsp : word) (h1 : 4096 ≤ bv_unsigned rsp) (h2 : bv_unsigned rsp < 2 ^ 47) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 96)) = 0 → False := by
  u_norm_deep; guard_target =ₛ bv_unsigned rsp - 96 = 0 → False; omega
example (x : word) (h1 : 16 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40) :
    ∃ y : Int, y = bv_unsigned (Z_to_bv 64 (bv_unsigned x - 16)) + 16 := by
  u_norm_deep; guard_target =ₛ ∃ y : Int, y = bv_unsigned x - 16 + 16; exact ⟨_, rfl⟩
example (x : word) (h1 : 16 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40) :
    let k := bv_unsigned (Z_to_bv 64 (bv_unsigned x - 16)); k + 16 = bv_unsigned x := by
  u_norm_deep; guard_target =ₛ let k := bv_unsigned x - 16; k + 16 = bv_unsigned x
  intro k; omega
-- So do instances in a conclusion, in a `let` body, after a tactic `have`
-- and under a projection.
example (x : word) (h1 : 16 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40) :
    0 ≤ bv_unsigned x → bv_unsigned (Z_to_bv 64 (bv_unsigned x - 16)) + 16 = bv_unsigned x := by
  u_norm_deep; guard_target =ₛ 0 ≤ bv_unsigned x → bv_unsigned x - 16 + 16 = bv_unsigned x
  intro; omega
example (x : word) (h1 : 16 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40) :
    let k : Int := 16; bv_unsigned (Z_to_bv 64 (bv_unsigned x - 16)) + k = bv_unsigned x := by
  u_norm_deep; guard_target =ₛ let k : Int := 16; bv_unsigned x - 16 + k = bv_unsigned x
  intro k; omega
example (x : word) (h1 : 16 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned x - 16)) + 16 = bv_unsigned x := by
  have _hh : (1 : Int) ≤ 2 := by omega
  u_norm_deep
  guard_target =ₛ bv_unsigned x - 16 + 16 = bv_unsigned x
  omega
example (x : word) (h1 : 16 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40) :
    ((bv_unsigned (Z_to_bv 64 (bv_unsigned x - 16)), (0 : Int)) : Int × Int).1 + 16 = bv_unsigned x := by
  delta Prod.fst
  u_norm_deep
  guard_target =~ ((bv_unsigned x - 16, (0 : Int)) : Int × Int).1 + 16 = bv_unsigned x
  dsimp only
  omega
-- The guard: the outer instance's side conditions follow from `hA`, but
-- its argument still holds a projection, so it is passed over, and the
-- inner one's fail: nothing collapses, as in Rocq.
example (x : word) (_h0 : bv_unsigned x = 0)
    (hA : bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1)) = 2 ^ 64 - 1) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1)) - 1)) = 2 ^ 64 - 2 := by
  fail_if_success (u_norm_deep; omega)
  rw [StepTac.u_Z2bv _ (by omega) (by omega)]
  omega
-- The same guard is what leaves the goal as `h3` states it: rewriting the
-- outer instance, whose side conditions follow from `_h1` and `_h2`, would
-- leave a goal `omega` cannot close.  Closes, as in Rocq.
example (x : word) (_h0 : bv_unsigned x = 0)
    (_h1 : 1 ≤ bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1)))
    (_h2 : bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1)) ≤ 2 ^ 64 - 1)
    (h3 : bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1)) - 1)) = 2 ^ 64 - 2) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1)) - 1)) = 2 ^ 64 - 2 := by
  u_norm_deep
  omega
-- Through `sym_sc` and `rdn_side`, `sym_u_norm` then rewrites the outer
-- instance, and the goal is no longer the one `h3` states: both fail, as
-- Rocq's do.
example (x : word) (_h0 : bv_unsigned x = 0)
    (_h1 : 1 ≤ bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1)))
    (_h2 : bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1)) ≤ 2 ^ 64 - 1)
    (h3 : bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1)) - 1)) = 2 ^ 64 - 2) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1)) - 1)) = 2 ^ 64 - 2 := by
  fail_if_success sym_sc
  fail_if_success rdn_side
  exact h3
-- An argument holding a `Z_to_bv 64` literal is guarded too, even where
-- the literal's reading is known: fails, as Rocq's does.
example (x : word) (h1 : 0 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40)
    (h5 : bv_signed (Z_to_bv 64 5) = 5) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned x + bv_signed (Z_to_bv 64 5))) = bv_unsigned x + 5 := by
  fail_if_success (u_norm_deep; omega)
  rw [h5, StepTac.u_Z2bv _ (by omega) (by omega)]
example (x : word) (h1 : 0 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40)
    (h5 : bv_signed (Z_to_bv (nat_lit 64) 5) = 5) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned x + bv_signed (Z_to_bv (nat_lit 64) 5))) = bv_unsigned x + 5 := by
  u_norm_deep
  guard_target =ₛ bv_unsigned (Z_to_bv 64 (bv_unsigned x + bv_signed (Z_to_bv (nat_lit 64) 5)))
    = bv_unsigned x + 5
  rw [h5, StepTac.u_Z2bv _ (by omega) (by omega)]
-- A literal of another width is not: the argument's `Z_to_bv 12` does not
-- stop the rewrite, as in Rocq.
example (x : word) (h1 : 0 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40)
    (h5 : bv_signed (Z_to_bv 12 (-8)) = -8) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned x + 8 + bv_signed (Z_to_bv 12 (-8)))) = bv_unsigned x := by
  u_norm_deep
  omega
example (x : word) (h1 : 0 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40)
    (h5 : bv_signed (Z_to_bv 32 (-8)) = -8) (h6 : bv_signed (Z_to_bv 65 (-8)) = -8) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned x + 16 + bv_signed (Z_to_bv 32 (-8))
      + bv_signed (Z_to_bv 65 (-8)))) = bv_unsigned x := by
  u_norm_deep
  omega
-- The guard in a hypothesis.
example (x : word) (_h0 : bv_unsigned x = 0)
    (hA : bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1)) = 2 ^ 64 - 1)
    (g : bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1)) - 1)) = 7) :
    False := by
  fail_if_success (u_norm_deep_in g; omega)
  rw [StepTac.u_Z2bv _ (by omega) (by omega)] at g
  omega
-- The inner instance collapses and the outer one's side conditions then
-- need the other disjunct's case: fails, as Rocq's does.
example (x : word) (h1 : 1 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1)) - 1))
      = bv_unsigned x - 2 ∨ bv_unsigned x = 1 := by
  fail_if_success (u_norm_deep; omega)
  rcases (show bv_unsigned x = 1 ∨ 2 ≤ bv_unsigned x by omega) with h | h
  · exact Or.inr h
  · u_norm_deep
    omega
-- With two goals open, both rewrite in the first alone and leave the
-- second, and the `h` in its context, as they were, as Rocq's do.
example (rsp : word) (h1 : 4096 ≤ bv_unsigned rsp) (h2 : bv_unsigned rsp < 2 ^ 47)
    (h : bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 8)) = 5000) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 96)) = bv_unsigned rsp - 96 ∧
      bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 8)) = 5000 := by
  constructor
  u_norm_deep
  · omega
  · exact h
example (rsp : word) (h1 : 4096 ≤ bv_unsigned rsp) (h2 : bv_unsigned rsp < 2 ^ 47)
    (h : bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 8)) = 5000) :
    bv_unsigned rsp = 5008 ∧ bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 8)) = 5000 := by
  constructor
  u_norm_deep_in h
  · omega
  · exact h
-- Every copy of the instance is rewritten.
example (z : Int) (h : bv_unsigned (Z_to_bv 64 z) = z ∧ bv_unsigned (Z_to_bv 64 z) ≤ 5)
    (h0 : 0 ≤ z) : z ≤ 5 := by
  u_norm_deep_in h
  exact h.2
-- In a hypothesis the order is part of the answer.  `a`'s instance comes
-- first and collapses; that takes away the link between `b` and the bound
-- `hT` states, so `b`'s side conditions then fail and it is passed over.
-- Fails, as Rocq's does; collapsing `b`'s first would close it.
example (a b : Int) (_ha0 : 0 ≤ a) (_ha1 : a < 2 ^ 64 - 1)
    (hT : 0 ≤ bv_unsigned (Z_to_bv 64 a) ∧ bv_unsigned (Z_to_bv 64 a) ≤ 5)
    (h : b = 2 * bv_unsigned (Z_to_bv 64 a) ∧ bv_unsigned (Z_to_bv 64 b) = 3) : False := by
  fail_if_success (u_norm_deep_in h; omega)
  rw [StepTac.u_Z2bv b (by omega) (by omega)] at h
  omega
-- The search starts again after each rewrite, so the outer instance, bare
-- once the inner one collapses, comes before `b`'s, whose side conditions
-- then fail, as in Rocq.
example (a b : Int) (_ha0 : 0 ≤ a) (_ha1 : a < 2 ^ 64 - 1)
    (hT : 0 ≤ bv_unsigned (Z_to_bv 64 (a + 0)) ∧ bv_unsigned (Z_to_bv 64 (a + 0)) ≤ 5)
    (h : b = 2 * bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) + 0)) ∧
      bv_unsigned (Z_to_bv 64 b) = 3) : False := by
  fail_if_success (u_norm_deep_in h; omega)
  u_norm_deep_in h
  guard_hyp h :ₛ b = 2 * (a + 0) ∧ bv_unsigned (Z_to_bv 64 b) = 3
  rw [StepTac.u_Z2bv (a + 0) (by omega) (by omega)] at hT
  rw [StepTac.u_Z2bv b (by omega) (by omega)] at h
  omega
-- The same behind a width-12 copy of `b`, which is not an instance and so
-- does not bring `b`'s ahead of `a`'s.  Fails, as Rocq's does.
example (a b : Int) (_ha0 : 0 ≤ a) (_ha1 : a < 2 ^ 64 - 1)
    (hT : 0 ≤ bv_unsigned (Z_to_bv 64 a) ∧ bv_unsigned (Z_to_bv 64 a) ≤ 5)
    (h : 0 ≤ bv_unsigned (Z_to_bv 12 b) ∧ b = 2 * bv_unsigned (Z_to_bv 64 a) ∧
      bv_unsigned (Z_to_bv 64 b) = 3) : False := by
  fail_if_success (u_norm_deep_in h; omega)
  rw [StepTac.u_Z2bv b (by omega) (by omega)] at h
  omega

/-! ### `vm_closed` -/

example : Z_to_bv 64 5 + Z_to_bv 64 3 = Z_to_bv 64 8 := by
  vm_closed
-- A `let`-bound variable the goal uses is unfolded, as Rocq's
-- `check_closed_term` unfolds it.
example : (let y : word := Z_to_bv 64 5; y + Z_to_bv 64 3 = Z_to_bv 64 8) := by
  intro y
  vm_closed

example (x : word) (h : x = Z_to_bv 64 8) : x = Z_to_bv 64 8 := by
  fail_if_success vm_closed
  exact h
example : ∃ w : word, Z_to_bv 64 5 + Z_to_bv 64 3 = w := by
  constructor
  fail_if_success vm_closed
  rfl
-- With two goals open, it closes the first and leaves the second.
example : Z_to_bv 64 5 + Z_to_bv 64 3 = Z_to_bv 64 8 ∧ Z_to_bv 64 1 + Z_to_bv 64 1 = Z_to_bv 64 2 := by
  constructor; vm_closed; guard_target =ₛ Z_to_bv 64 1 + Z_to_bv 64 1 = Z_to_bv 64 2; vm_closed
-- `decide`'s own evaluation does not get through `reg_get`; the kernel's does.
example : LinuxProcessSemantics.Riscv.Sem.reg_get
    (bvmap_set (17 : BitVec 5) (Z_to_bv 64 93) bvmap_empty) 17 = Z_to_bv 64 93 := by
  fail_if_success decide
  vm_closed
-- A `let` of a local that the goal does not use: closes.
example (x : word) : let _z := x; (5 : Int) + 3 = 8 := by
  vm_closed
-- A β-redex that a `let` unfolding leaves still mentions `x`: refused.
example (x : word) : (fun _ : word => Z_to_bv 64 5) x = Z_to_bv 64 5 := by
  let y : word := Z_to_bv 64 5
  show (fun _ : word => y) x = y
  fail_if_success vm_closed
  rfl
-- A closed `≤`, and word equations that hold only modulo `2 ^ 64`,
-- close in Lean; Rocq's `vm_closed` refuses these three twins.
example : bv_unsigned (Z_to_bv 64 5) ≤ 8 := by
  vm_closed
example : Z_to_bv 64 16 + Z_to_bv 64 (-8) = Z_to_bv 64 8 := by
  vm_closed
example : Z_to_bv 64 (-8) = Z_to_bv 64 (2 ^ 64 - 8) := by
  vm_closed
-- A closed goal with no `Decidable` instance is refused in Lean;
-- Rocq's `vm_closed` closes the function equation.
example : (fun b : BitVec 8 => b) = id := by
  fail_if_success vm_closed
  rfl

/-! ### `sym_close_open` and `sym_f_equal` -/

example (x : word) : x = x := by
  sym_close_open
example (x : word) : Z_to_bv 64 (bv_unsigned x - 16 + 16) = Z_to_bv 64 (bv_unsigned x) := by
  sym_close_open
-- Offsets on which `rfl` at default transparency runs into `maxRecDepth`.
example (x : word) :
    Z_to_bv 64 (bv_unsigned x + 2040 - 2048) = Z_to_bv 64 (bv_unsigned x - 8) := by
  sym_close_open
example (x : word) :
    Z_to_bv 64 (bv_unsigned x + 2 ^ 63 - 2 ^ 63) = Z_to_bv 64 (bv_unsigned x) := by
  sym_close_open
-- Offset arguments of different functions, on which `apply congrFun` at
-- default transparency runs into `maxRecDepth`: the third alternative closes.
example (F G : Int → word) (x : word)
    (h : bv_unsigned (F (bv_unsigned x + 2040 - 2048)) = bv_unsigned (G (bv_unsigned x - 8))) :
    F (bv_unsigned x + 2040 - 2048) = G (bv_unsigned x - 8) := by
  sym_close_open
-- With two goals open, it closes the first and leaves the second.
example (x y : word) : x = x ∧ y = y := by
  constructor; sym_close_open; guard_target =ₛ y = y; sym_close_open
-- The outer `Z_to_bv` of a nested projection: `sym_u_norm` meets the outer
-- instance first, whose side conditions `omega` cannot see hold, and
-- stops, so it fails, as Rocq's does; `u_norm_deep` closes it.
example (x : word) (h1 : 16 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40) :
    Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned x - 16)) + 16) = x := by
  fail_if_success sym_close_open
  apply PropExec.bv_eq_of_unsigned
  u_norm_deep
  omega
-- The third alternative, with bounds for its side conditions in context
-- and without: without them it fails, as Rocq's does.
example (x : word) (h1 : 0 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 64) :
    Z_to_bv 64 (bv_unsigned x) = x := by
  sym_close_open
example (x : word) : Z_to_bv 64 (bv_unsigned x) = x := by
  fail_if_success sym_close_open
  have h := x.isLt
  apply PropExec.bv_eq_of_unsigned
  rw [StepTac.u_Z2bv _ (by unfold bv_unsigned; omega) (by unfold bv_unsigned; omega)]
-- The third alternative with nothing for `sym_u_norm` to rewrite.
example (x y : word) (h : bv_unsigned x = bv_unsigned y) : x = y := by
  sym_close_open
-- An `Int` equation over a projection: nothing applies, so it fails, as
-- Rocq's does; `u_norm_deep` then `omega` closes it.
example (x : word) (h1 : 16 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned x - 16)) + 16 = bv_unsigned x := by
  fail_if_success sym_close_open
  u_norm_deep
  omega

example : decide (bv_unsigned (Z_to_bv 64 5) < 2 ^ 63) = true := by
  fail_if_success sym_close_open
  vm_closed
example : Z_to_bv 64 5 + Z_to_bv 64 3 = Z_to_bv 64 8 := by
  fail_if_success sym_close_open
  vm_closed
example (x : word) : v_addi x 16 = Z_to_bv 64 (bv_unsigned x + 16) := by
  fail_if_success sym_close_open
  rfl
-- Two literals equal only modulo `2 ^ 64`: fails, as Rocq's does.
example : Z_to_bv 64 (-8) = Z_to_bv 64 (2 ^ 64 - 8) := by
  fail_if_success sym_close_open
  vm_closed
-- `↔` closes by `rfl`, as in Rocq.
example (P : Prop) : P ↔ P := by
  sym_close_open
-- Two different operators: `sym_f_equal` fails, as stdpp's `f_equal`
-- makes no progress, and `omega` closes the whole goal.
example (a c : Int) (h1 : a = 5) (h2 : c = 11) : a + 4 = c - 2 := by
  fail_if_success sym_f_equal
  sym_close_open
-- The argument goals it leaves go to `omega` whole: it never splits one
-- (`a + 1 = 1 + a` would become `a = 1` and `1 = a`).
example (a b : Int) : (a + 1) + (b + 1) = (1 + a) + (1 + b) := by
  sym_close_open
example (x : word) : Z_to_bv 64 (bv_unsigned x + 1) = Z_to_bv 64 (1 + bv_unsigned x) := by
  sym_close_open
-- It splits the function side again: a pair, which `omega` cannot take
-- whole, becomes its two components.  Closes, as Rocq's does.
example (a b : Int) : ((a + 1, b + 1) : Int × Int) = (1 + a, 1 + b) := by
  sym_close_open
-- A function whose result type depends on the argument: `congrFun` splits
-- it, as stdpp's `f_equal_dep` does.  Closes, as Rocq's does.
example (F : Int → (n : Nat) → BitVec n) (x : Int) : F (x + 1) 64 = F (1 + x) 64 := by
  sym_close_open
-- An argument goal `rfl` closes is closed, as stdpp's `try reflexivity`
-- closes it, and not left for `omega`, which fails on a word equation.
example (F : Int → word → word) (a : Int) (x : word) : F (a + 1) x = F (1 + a) x := by
  sym_close_open
-- The function side's own argument goal is left open.
example (F : Int → word → word) (a : Int) (x : word) : F (a + 1) x = F (1 + a) x := by
  sym_f_equal
  guard_target =ₛ a + 1 = 1 + a
  omega
-- It works on the first goal alone.
example (F : Int → Int) (a : Int) (y : word) : F (a + 0) = F a ∧ y = y := by
  constructor
  sym_f_equal
  · guard_target =ₛ a + 0 = a
    omega
  · guard_target =ₛ y = y
    rfl
-- A side that applies a definition to an argument, and splits only once it
-- is unfolded (`bv_unsigned x` is `(x.toNat : Int)`): `sym_f_equal` fails,
-- as stdpp's `f_equal` makes no progress on the same shape.
example (n : Nat) (x : word) (h : n = x.toNat) : (n : Int) = bv_unsigned x := by
  fail_if_success sym_f_equal
  unfold bv_unsigned
  rw [h]
-- A side that is a constant: stdpp's `apply f_equal_help` unfolds it
-- and splits the equation, and Rocq's `sym_close_open` then closes it.
-- Both fail here.
private def sixteenW : word := Z_to_bv 64 16
private def sixteenI : Int := 4 + 12
example (z : Int) (h : z = 16) : Z_to_bv 64 z = sixteenW := by
  fail_if_success sym_f_equal
  fail_if_success sym_close_open
  subst h; rfl
example (a : Int) (h : a = 12) : 4 + a = sixteenI := by
  fail_if_success sym_f_equal
  fail_if_success sym_close_open
  unfold sixteenI; omega
-- A function goal that holds only once `toW` is unfolded: stdpp's
-- `reflexivity` closes `Z_to_bv 64 = toW` by conversion, and Rocq's
-- `sym_close_open` then closes the goal.  Both fail here.
private def toW (z : Int) : word := Z_to_bv 64 z
example (a b : Int) (h : a = b) : Z_to_bv 64 a = toW b := by
  fail_if_success sym_f_equal
  fail_if_success sym_close_open
  subst h; rfl
-- An argument equal only once `zzFive` is unfolded, of a function whose
-- result type depends on it.
private def zzFive : Nat := 5
example (F : Int → (n : Nat) → BitVec n) (a : Int) : F (a + 1) zzFive = F (1 + a) 5 := by
  fail_if_success sym_close_open
  rw [show a + 1 = 1 + a by omega]; rfl

example (F : Int → Int) : F (2 + 3) = F 5 := by
  sym_f_equal
  guard_target =ₛ (2 + 3 : Int) = 5
  omega
example (F : Int → Int) : F (2 + 3) = F 5 := by
  sym_close_open
-- `omega` closes a goal a hypothesis states: an argument goal and a
-- whole word equation, both of which Rocq's fails on.
example (x y z : word) (h : y = z) : x + y = x + z := by
  sym_close_open
example (x : word) (h : x = Z_to_bv 64 8) : x = Z_to_bv 64 8 := by
  sym_close_open

/-! ### `rdn_side` -/

example (v x : word) (h1 : 16 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40) :
    ((word_to_le_bytes 8 v).length : Int) + bv_unsigned (Z_to_bv 64 (bv_unsigned x - 16))
      < 2 ^ 41 := by
  rdn_side
-- A cross-call frame: the projection nests two deep.
example (rsp : word) (h1 : 4096 ≤ bv_unsigned rsp) (h2 : bv_unsigned rsp < 2 ^ 47) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 96)) - 160)) + 8
      ≤ bv_unsigned rsp := by
  rdn_side
-- The length of a literal list (Rocq `cbn [length]`).
example (x : word) (a b c : BitVec 8) (h1 : 16 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40) :
    (([a, b, c] : List (BitVec 8)).length : Int) + bv_unsigned (Z_to_bv 64 (bv_unsigned x - 16))
      < 2 ^ 41 := by
  rdn_side
-- Literal immediates, read before the projection collapses.
example (v x : word) (h1 : 16 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40) :
    ((word_to_le_bytes 8 v).length : Int)
      + bv_unsigned (Z_to_bv 64 (bv_unsigned x + bv_signed (0xff0#12))) < 2 ^ 41 := by
  rdn_side
example (v x : word) (h1 : 16 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40) :
    ((word_to_le_bytes 8 v).length : Int)
      + bv_unsigned (Z_to_bv 64 (bv_unsigned x + bv_unsigned (5 : word))) < 2 ^ 41 := by
  rdn_side
example (v x : word) (h1 : 16 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40) :
    ((word_to_le_bytes 8 v).length : Int)
      + bv_unsigned (Z_to_bv 64 (bv_unsigned x + bv_signed (4088 : BitVec 12))) < 2 ^ 41 := by
  rdn_side
example (v x : word) (h1 : 16 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40) :
    ((word_to_le_bytes 8 v).length : Int)
      + bv_unsigned (Z_to_bv 64 (bv_unsigned x + bv_unsigned (5#64))) < 2 ^ 41 := by
  rdn_side
example (v x : word) (h1 : 16 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40) :
    ((word_to_le_bytes 8 v).length : Int) + bv_unsigned (Z_to_bv 64 (bv_unsigned x
      + bv_signed (BitVec.ofNatLT 4088 (by decide) : BitVec 12)
      + bv_unsigned (BitVec.ofNatLT 5 (by decide) : word))) < 2 ^ 41 := by
  rdn_side
example (v x : word) (h1 : 16 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40) :
    ((word_to_le_bytes 8 v).length : Int) + bv_unsigned (Z_to_bv 64 (bv_unsigned x
      + bv_signed (BitVec.ofFin ⟨4088, by decide⟩ : BitVec 12)
      + bv_unsigned (BitVec.ofFin ⟨5, by decide⟩ : word))) < 2 ^ 41 := by
  rdn_side
example (F : Int → Int) : F (bv_signed (0#12)) = F 0 := by rdn_side
-- No projection at all.
example (v : word) (x : Int) (h : x < 5) : ((word_to_le_bytes 8 v).length : Int) + x < 20 := by
  rdn_side
example (v : word) : (word_to_le_bytes 8 v).length = 8 := by
  rdn_side
-- Every length is rewritten.
example (v w : word) :
    ((word_to_le_bytes 8 v).length : Int) + ((word_to_le_bytes 4 w).length : Int) = 12 := by
  rdn_side
-- The rewrite runs before the length is computed, so a cons in front of
-- the bytes hides them from it: fails, as Rocq's does.
example (v : word) (a : BitVec 8) : ((a :: word_to_le_bytes 8 v).length : Int) < 20 := by
  fail_if_success rdn_side
  rw [List.length_cons, CatExec.length_N_to_le_bytes]
  omega
-- `dsimp` β-reduces, as `cbn` does.
example (v : word) : (fun y : Int => y) ((word_to_le_bytes 8 v).length : Int) < 20 := by
  rdn_side
-- `True` closes, as in Rocq (by `dsimp` here, by `lia` there).
example : True := by
  rdn_side
-- A `True` conjunct fails here, with no `split` before `omega`; Rocq's
-- `lia` closes it.
example (x : word) (h1 : 16 ≤ bv_unsigned x) (h2 : bv_unsigned x < 2 ^ 40) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned x - 16)) < 2 ^ 41 ∧ True := by
  fail_if_success rdn_side
  sym_sc
-- An equation reflexive up to reducible unfolding: `dsimp` closes it
-- here; Rocq's `rdn_side` fails on it.
example (x : word) : x = x := by
  rdn_side
-- With two goals open, it closes the first and leaves the second.
example (x : Int) (h : x < 5) : x < 6 ∧ x < 7 := by
  constructor; rdn_side; guard_target =ₛ x < 7; rdn_side
-- `sym_u_norm` collapses the outer projection, and its rewrite leaves the
-- word equation that makes open, as Rocq's does: `omega` fails on it.
example (x : word) (_h0 : bv_unsigned x = 0)
    (hA : bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1)) = 2 ^ 64 - 1) :
    Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1)) - 1)))
      = Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1)) - 1) := by
  fail_if_success rdn_side
  rw [StepTac.u_Z2bv (bv_unsigned (Z_to_bv 64 (bv_unsigned x - 1)) - 1) (by omega) (by omega)]

-- The keywords are not reserved tokens: the names still parse as identifiers.
example (sym_sc vm_closed u_norm_deep u_norm_deep_in sym_close_open rdn_side sym_imm_norm
    sym_f_equal : Nat)
    (h : sym_sc + vm_closed + u_norm_deep + u_norm_deep_in + sym_close_open + rdn_side
      + sym_imm_norm + sym_f_equal = 0) :
    sym_sc = 0 := by
  omega

end LinuxProcessSemantics.Common.SymSide
