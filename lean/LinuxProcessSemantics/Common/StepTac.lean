import Lean
import LinuxProcessSemantics.Common.SeqExec
import LinuxProcessSemantics.Common.PropExec
import LinuxProcessSemantics.Common.MmapSim
import LinuxProcessSemantics.Common.StreamSim
import LinuxProcessSemantics.Common.DrainSim

/-! # Common.StepTac — the shared value lemmas of the step-chaining layer

Ported from `theories/Common/StepTac.v` at
2cde689f94c086b868999970834b76a25616b94a: the part of it `cat1024_ns`'s
`Proof.v` reaches (`Print All Dependencies` of its
`strong_universal`, ticket E-proof-library), with the Rocq statements.

The Rocq file is mostly Ltac (the step-chaining, sp-normalization and
vm-guard tactics); the original ticket did not port those tactics.  The
canonical computed-value form is `Z_to_bv 64 z` with `z` a plain-`Int`
expression; `u_Z2bv` collapses `bv_unsigned (Z_to_bv 64 z)` for the
in-range side conditions.

Everything else in the Rocq file was left unported by that ticket;
cat1024_ns reaches none of it.  Sections appended at the end of this file
since complete the tactic families and DispatchSmoke tests. -/

namespace LinuxProcessSemantics.Common.StepTac

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.SeqExec

/-- `bv_unsigned (Z_to_bv 64 z)` collapses to `z` when in range —
the glue that lets nested `v_addi` rewrites feed their own side
conditions to `omega`. -/
theorem u_Z2bv (z : Int) (hlo : 0 ≤ z) (hhi : z < 2 ^ 64) :
    bv_unsigned (Z_to_bv 64 z) = z := by
  rw [Z_to_bv_unsigned, bv_wrap64_mod]
  exact Int.emod_eq_of_lt hlo hhi

/-- Literal-immediate corollaries of `SeqExec.v_addi_m`, one per small
negative-immediate constant used across the examples (`rw` needs the
LHS stated with a literal `-k`).  Conclusions are in the
`Z_to_bv 64 (...)` canonical form. -/
theorem v_addi_m16 (x : word) (h16 : 16 ≤ bv_unsigned x) :
    v_addi x (-16) = Z_to_bv 64 (bv_unsigned x - 16) :=
  v_addi_m x 16 h16 (by decide)

theorem v_addi_m32 (x : word) (h32 : 32 ≤ bv_unsigned x) :
    v_addi x (-32) = Z_to_bv 64 (bv_unsigned x - 32) :=
  v_addi_m x 32 h32 (by decide)

/-- Non-negative immediate, term-level form of Rocq's `PropExec.v_addi_nneg`
(itself in `PropExec` since E-grep_args_ns; cat1024_ns uses this form). -/
theorem v_addi_nneg_t (x : word) (imm : Int) (_hnn : 0 ≤ imm)
    (_hlt : bv_unsigned x + imm < 2 ^ 64) :
    v_addi x imm = Z_to_bv 64 (bv_unsigned x + imm) := rfl

/-- Upper bound on the initial stack image (feeds every read lemma's
no-overflow side condition; the numbers come from `valid_argv`/
`valid_envp`).

Derived rather than computed since issue #492: the layout arithmetic
is `PropExec.build_stack_bytes_within_span` and the `valid_argv`/
`valid_envp` arithmetic is `Run.entry_stack_span_bound`, and this is
their composition, so the same derivation backs both this bound and
`Run.entry_stack_fits`. -/
theorem bsb_bound (ph : PhdrInfo) (sp : word) (a e : List (List byte)) (uid hw : word)
    (rnd : EntryDraw) (hva : valid_argv a) (hve : valid_envp e) :
    ((build_stack_bytes ph sp a e uid hw rnd).length : Int) ≤ 2240000 := by
  have h1 := build_stack_bytes_within_span ph sp a e uid hw rnd
  have h2 := entry_stack_span_bound a e hva hve
  unfold entry_stack_span_max at h2
  omega

/-! ## Additions for ticket E-proof-library-2c: `word_add_nat`

Ported from the same Rocq file at the baseline the header names, with the
Rocq statement, for `Common/MuslStrlen.lean`'s `argv_ptr_room` and
`argv_word_readable` and `Common/ArgvEnv.lean`'s `read_argv_ptr_w`.
Rocq's `Z.of_nat n` is the cast `(n : Int)`. -/

/-- The wrapping word/nat offset add in the canonical `Z_to_bv` form
(hypothesis-free: both sides wrap identically). -/
theorem word_add_nat (a : word) (n : Nat) :
    a + nat_to_word n = Z_to_bv 64 (bv_unsigned a + (n : Int)) := by
  apply bv_eq_of_unsigned
  rw [bv_unsigned_add, nat_to_word, Z_to_bv_unsigned, Z_to_bv_unsigned, bv_wrap64_mod,
    bv_wrap64_mod, bv_wrap64_mod, Int.add_emod_emod]

end LinuxProcessSemantics.Common.StepTac

/-! ## Additions for ticket E-grep_args_ns (StepTac batch 1)

Ports the closedness guard, literal/pc normalization and `bveq` from
`theories/Common/StepTac.v` at f44244ad6b8041aa83053d9ca91e090037ed743b.
Lean's value-returning interface is `MetaM Expr`; script-facing names are
tactic-category syntax only, so they remain usable as identifiers.
Local `let` definitions replace Rocq's `set`, word literals are `OfNat`
numerals at `BitVec 64`, and evaluation uses Meta reduction followed by a
kernel check (values), or `decide +kernel` (closed propositions). No user
code is evaluated natively. Lean has no Rocq `timeout 30`; `maxHeartbeats`
is the nearest work bound, and this section does not change it.
-/

namespace LinuxProcessSemantics.Common.StepTac

open Lean Meta Elab Tactic
open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.ExitSim

/-- Rocq's value-returning `expand_ctx_defs p`: transitively zeta-delta
expand local let definitions occurring in `e`, including their types and
bodies. Ordinary context variables stay free. The public Meta function is
the interface; no tactic form is needed by the Rocq scripts. -/
def expandCtxDefs (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun t => do
    if let .fvar id := t then
      if let some v ← id.getValue? then
        return .visit (← instantiateMVars v)
    return .continue)

/-- Rocq's `check_closed_term`, for Lean-side callers. Instantiate assigned
metavariables, expand local let definitions, then reject metavariables
BEFORE free variables. Unlike a context-clearing probe, unrelated goal
metavariables have no effect. Universe metavariables are also rejected. -/
def checkClosedTerm (e : Expr) : MetaM Unit := do
  let p ← expandCtxDefs (← instantiateMVars e)
  if p.hasMVar then throwError "check_closed_term: {e} contains an evar"
  if p.hasFVar then throwError "check_closed_term: {e} mentions a context variable"

/-- Rocq's `check_closed_term p`: elaborate in the main goal's context,
then call `checkClosedTerm`. Succeeds without changing the goal; Lean
elaboration may resolve implicit arguments before the guard runs. -/
elab "check_closed_term " p:term : tactic => withMainContext do
  checkClosedTerm (← elabTerm p none)

/-- Syntactic counterpart of Rocq's `@BV _ _ _` literal test, defaulting
to words (the optional width also serves register/immediate tactics). Like SymSide's private `litWord?`, accepts `OfNat`, `ofNat`,
`ofNatLT`, and `ofFin (Fin.mk ...)`; it does not evaluate computed words.
The returned numeral is the spelling, before reduction modulo `2^width`. -/
def wordLit? (e : Expr) (width : Nat := 64) : MetaM (Option Nat) := do
  let num? (t : Expr) := t.nat? <|> t.rawNatLit?
  if e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 2).isAppOf ``BitVec.instOfNat then
    let ty ← whnfR (e.getArg! 0)
    if ty.isAppOfArity ``BitVec 1 && num? (ty.getArg! 0) == some width then
      return (e.getArg! 1).rawNatLit?
  if e.isAppOfArity ``BitVec.ofNat 2 || e.isAppOfArity ``BitVec.ofNatLT 3 then
    if num? (e.getArg! 0) == some width then return num? (e.getArg! 1)
  if e.isAppOfArity ``BitVec.ofFin 2 && num? (e.getArg! 0) == some width then
    let f := e.getArg! 1
    if f.isAppOfArity ``Fin.mk 3 then return num? (f.getArg! 1)
  return none

private def closedNatValue (e : Expr) : MetaM Nat := do
  let e ← whnf e
  if e.isConstOf ``Nat.zero then return 0
  let some n := e.rawNatLit?
    | throwError "vm_eval: result is not a Nat literal: {e}"
  return n

/-- Rocq's value-returning `vm_eval t`. Guard BEFORE reducing anything;
use Meta `whnf` at default transparency to expose a Nat, Int constructor,
or a word's `toNat`, then reify a numeral. Only Nat, Int and BitVec 64
results are supported, unlike Rocq's arbitrary normal forms. An opaque or
otherwise stuck result fails. Each returned value is checked immediately
by the kernel on an equality proof by conversion, and proofs using it are
kernel-checked again. The closed equality is checked in an empty local
context, so unrelated local definitions with assigned metavariables do not
confuse the kernel. No VM/native execution of user definitions is used. -/
def vmEval (e : Expr) : MetaM Expr := do
  checkClosedTerm e
  withTransparency .default do
    let p ← expandCtxDefs (← instantiateMVars e)
    let ty ← whnf (← inferType p)
    let lit ← if ty.isConstOf ``Nat then
        pure (mkNatLit (← closedNatValue p))
      else if ty.isConstOf ``Int then
        let v ← whnf p
        if v.isAppOfArity ``Int.ofNat 1 then
          pure (mkIntLit (Int.ofNat (← closedNatValue v.appArg!)))
        else if v.isAppOfArity ``Int.negSucc 1 then
          pure (mkIntLit (Int.negSucc (← closedNatValue v.appArg!)))
        else throwError "vm_eval: result is not an Int literal: {v}"
      else if ty.isAppOfArity ``BitVec 1 then
        unless (← whnf ty.appArg!).rawNatLit? == some 64 do
          throwError "vm_eval: expected a BitVec 64 literal"
        mkNumeral (mkConst ``word)
          (← closedNatValue (← mkAppM ``BitVec.toNat #[p]))
      else throwError "vm_eval: expected a Nat, Int, or BitVec 64 literal, got {ty}"
    let lit ← instantiateMVars lit
    let proof ← instantiateMVars (mkExpectedPropHint (← mkEqRefl lit) (← mkEq p lit))
    withLCtx {} #[] (checkWithKernel proof)
    return lit

/-- Rocq's `vm_eval t`, in script position: silently check that `t`
evaluates to a supported literal, leaving the goal unchanged. Value
callers use `vmEval`; a leading-keyword term elaborator would reserve
`vm_eval` as an identifier, so this is tactic-category syntax only. -/
elab "vm_eval " t:term : tactic => withMainContext do
  discard <| vmEval (← elabTerm t none)

/-- Rocq's value-returning `word_lit p`: evaluate `bv_unsigned p` through
`vmEval` and return its unsigned numeral modulo `2^64`. Lean uses
`OfNat.ofNat` at `BitVec 64`, not stdpp's proof-carrying `BV` constructor;
the result is definitionally equal as well as propositionally equal to
`p`, and the conversion is kernel-checked before returning it. -/
def wordLit (e : Expr) : MetaM Expr := do
  let u ← vmEval (← mkAppM ``bv_unsigned #[e])
  unless ← isDefEq (← inferType e) (mkApp (mkConst ``BitVec) (mkNatLit 64)) do
    throwError "word_lit: expected BitVec 64"
  let some z ← getIntValue? u | throwError "word_lit: expected an unsigned Int literal"
  let lit ← mkNumeral (mkConst ``word) (z.toNat % 2 ^ 64)
  let lit ← instantiateMVars lit
  let p ← expandCtxDefs (← instantiateMVars e)
  let proof ← instantiateMVars (mkExpectedPropHint (← mkEqRefl lit) (← mkEq p lit))
  withLCtx {} #[] (checkWithKernel proof)
  return lit

/-- Rocq's `word_lit p` in script position, like `vm_eval`: validate the
literal silently without changing the goal. Value callers use `wordLit`;
tactic-only syntax keeps `word_lit` available as an identifier. -/
elab "word_lit " p:term : tactic => withMainContext do
  discard <| wordLit (← elabTerm p none)

private def wlitReplace (p : Expr) : TacticM Unit := do
  let lit ← wordLit p
  let eq ← mkEq p lit
  let proof ← Term.elabTerm (← `(by decide +kernel)) (some eq)
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  let g ← getMainGoal
  let result ← g.rewrite (← g.getType) proof
  replaceMainGoal [← g.replaceTargetEq result.eNew result.eqProof]

/-- Rocq's `wlit_replace p`: rewrite every occurrence in the first goal
using `p = literal`, proved by `decide +kernel` on the BitVec equation
itself (Rocq first applies `bv_eq`). `wordLit` guards evaluation. Lean's
rewrite also matches definitionally equal occurrences; hypotheses stay
unchanged and the rewritten goal is left open, even if reflexive. -/
elab "wlit_replace " p:term : tactic => withMainContext do
  wlitReplace (← elabTerm p none)

private def wlitExpr (p : Expr) : TacticM Unit := do
  if (← wordLit? p).isSome then return
  wlitReplace p

/-- Rocq's `wlit p`: literal no-op, otherwise try `wlit_replace p`.
Lean's extra literal spellings are in `wordLit?`. -/
elab "wlit " p:term : tactic => withMainContext do
  let e ← elabTerm p none
  let saved ← saveState
  try wlitExpr e
  catch _ => saved.restore

private def normPcState (st : Expr) : TacticM Unit := do
  let st ← instantiateMVars st
  if st.hasMVar then return
  if st.isAppOfArity ``PropExec.mkst 4 then wlitExpr (st.getArg! 1)

/-- Rocq's `norm_pc_state st`: instantiate assigned metavariables, skip
any state still containing one, then run `wlit` on the pc of a syntactic
four-argument `PropExec.mkst`. An argument that does not elaborate fails,
as in Rocq; every later failure leaves the goal unchanged, as `wlit`'s
`try` does. -/
elab "norm_pc_state " st:term : tactic => withMainContext do
  let e ← elabTerm st none
  let saved ← saveState
  try normPcState e
  catch _ => saved.restore

-- (full Lean name, total arity including implicit parameters, zero-based state index).
private def normPcTable : Array (Name × Nat × Nat) := #[
  (``LinuxProcessSemantics.Common.CatSim.msteps, 3, 1),
  (``LinuxProcessSemantics.Common.CatSim.to_wexit, 4, 1),
  (``LinuxProcessSemantics.Common.MmapSim.twm, 5, 1),
  (``LinuxProcessSemantics.Common.MmapSim.twm_pend, 6, 1),
  (``LinuxProcessSemantics.Common.MmapSim.twm_tail, 6, 1),
  (``LinuxProcessSemantics.Common.MmapSim.tmw, 7, 1),
  (``LinuxProcessSemantics.Common.StreamSim.to_wr, 4, 3),
  (``LinuxProcessSemantics.Common.StreamSim.to_rd, 4, 3),
  (``LinuxProcessSemantics.Common.WallSim.to_wall, 5, 2),
  (``LinuxProcessSemantics.Common.WallSim.to_wall_tail, 5, 2),
  (``LinuxProcessSemantics.Common.WallSim.to_wallexit, 5, 4),
  (``LinuxProcessSemantics.Common.ExitSim.to_exit, 3, 2),
  (``LinuxProcessSemantics.Common.DrainSim.to_out, 3, 2),
  -- {A : Type} precedes segs, cnt, f, out, ec, LH, a, ms.
  (``LinuxProcessSemantics.Common.DrainSim.to_rd, 9, 8)]

/-- Rocq's `norm_pc`: dispatch on the syntactic goal head and full Lean
arity using `normPcTable`, then `norm_pc_state`. Unknown heads and failures leave the goal alone. -/
elab "norm_pc" : tactic => do
  let saved ← saveState
  try withMainContext do
    let t ← instantiateMVars (← getMainTarget)
    for (name, arity, idx) in normPcTable do
      if t.isAppOfArity name arity then
        normPcState (t.getArg! idx)
        return
  catch _ => saved.restore

/-- Rocq's `bveq`: apply `bv_eq_of_unsigned` (any BitVec width), then
triage the unsigned equation. Closed: `decide +kernel`; containing an
unassigned metavariable: fail before evaluation OR conversion; open and
evar-free: `rfl` only, with the OPEN diagnostic if conversion fails.
Local let definitions count as their bodies, and universe metavariables
also count as evars. Lean has no `timeout 30`; the ambient `maxHeartbeats`
is the nearest bound. Closed failures report kernel evaluation failure,
not Rocq's 30-second timeout claim. -/
elab "bveq" : tactic => withMainContext do
  evalTactic (← `(tactic| apply bv_eq_of_unsigned))
  withMainContext do
    let g ← getMainTarget
    let closed ← try checkClosedTerm g; pure true catch _ => pure false
    if closed then
      try evalTactic (← `(tactic| decide +kernel))
      catch _ => throwError "bveq: kernel evaluation did not close this closed goal"
    else
      let expanded ← expandCtxDefs (← instantiateMVars g)
      if expanded.hasMVar then
        throwError "bveq: the goal contains an evar — vm_compute must not see it; instantiate the machine state (eexists / chain_step) before normalizing."
      try evalTactic (← `(tactic| rfl))
      catch _ =>
        throwError "bveq: the goal is OPEN (it mentions a context variable) and kernel conversion did not close it — resolve the register and memory projections first (getr_resolve, regupd_resolve) and try again."

-- Rocq smoke tests (the two wlits calls are spelled as the corresponding
-- single-redex wlit calls: the batch intentionally does not port wlits).
example : v_addi (Z_to_bv 64 5) 3 = Z_to_bv 64 8 := by bveq

example (regs : bvmap 5 word) (v : word) : getr (regupd regs 11 v) 11 = v := by
  fail_if_success bveq
  getr_resolve
  rfl

example (v : word) : ∃ w : word, w = v := by
  refine ⟨?_, ?_⟩
  rotate_left
  check_closed_term (v_addi (Z_to_bv 64 5) 3)
  fail_if_success check_closed_term (v_addi v 4)
  fail_if_success run_tac checkClosedTerm (← getMainTarget)
  let k := Z_to_bv 64 7
  check_closed_term (v_addi k 1)
  let k2 := v_addi v 1
  fail_if_success check_closed_term (v_addi k2 1)
  run_tac
    let u ← vmEval (← elabTerm (← `(bv_unsigned (v_addi (Z_to_bv 64 5) 3))) none)
    unless (← getIntValue? u) == some 8 do throwError "expected literal 8"
  fail_if_success vm_eval (bv_unsigned (v_addi v 4))
  rfl

example (v : word) : v_addi v 4 = v_addi v 4 := by
  wlit (v_addi v 4)
  guard_target =ₛ v_addi v 4 = v_addi v 4
  rfl

example (v : word) :
    (v_addi (Z_to_bv 64 5) 3, v_addi v 4) = (Z_to_bv 64 8, v_addi v 4) := by
  wlit (v_addi (Z_to_bv 64 5) 3)
  guard_target =ₛ ((8 : word), v_addi v 4) = (Z_to_bv 64 8, v_addi v 4)
  exact congrArg (fun w : word => (w, v_addi v 4)) (by bveq)

-- Transitive local definitions; open and evar guards run before reduction.
example (v : word) : True := by
  let a := Z_to_bv 64 7
  let b := v_addi a 1
  check_closed_term b
  vm_eval b
  word_lit b
  let c := v_addi v 1
  let d := v_addi c 1
  fail_if_success check_closed_term d
  fail_if_success vm_eval d
  fail_if_success word_lit d
  fail_if_success wlit_replace d
  fail_if_success check_closed_term (v_addi (5 : word) _)
  fail_if_success vm_eval (v_addi (5 : word) _)
  fail_if_success vm_eval True
  exact True.intro

example : True := by
  vm_eval (2 + 3 : Nat)
  vm_eval (-8 : Int)
  vm_eval (v_addi (0 : word) (-1))
  run_tac
    let n ← vmEval (← elabTerm (← `((2 + 3 : Nat))) none)
    unless (← getNatValue? n) == some 5 do throwError "expected Nat 5"
    let z ← vmEval (← elabTerm (← `((-8 : Int))) none)
    unless (← getIntValue? z) == some (-8) do throwError "expected Int -8"
    let w ← wordLit (← elabTerm (← `(v_addi (0 : word) (-1))) none)
    unless (← wordLit? w) == some (2 ^ 64 - 1) do throwError "expected wrapped word"
  exact True.intro

example (r : bvmap 5 word) (m rom : word → Option byte) :
    mkst r (v_addi (5 : word) 3) m rom = mkst r 8 m rom := by
  wlit (v_addi (5 : word) 3)
  guard_target =ₛ mkst r (8 : word) m rom = mkst r (8 : word) m rom
  with_reducible rfl

example (v : word) : (8 : word) = 8 ∧ v = v := by
  constructor
  · wlit (8 : word)
    guard_target =ₛ (8 : word) = 8
    rfl
  · wlit v
    guard_target =ₛ v = v
    rfl

example (segs : List MemImageType.Segment) (r : bvmap 5 word)
    (m rom : word → Option byte) :
    msteps segs (mkst r (v_addi (5 : word) 3) m rom) (mkst r 8 m rom) := by
  norm_pc
  guard_target =ₛ msteps segs (mkst r (8 : word) m rom) (mkst r (8 : word) m rom)
  exact msteps.mst_refl _

example (segs : List MemImageType.Segment) (r : bvmap 5 word)
    (m rom : word → Option byte) (code : word)
    (h : to_exit segs code (mkst r 8 m rom)) :
    to_exit segs code (mkst r (v_addi (5 : word) 3) m rom) := by
  norm_pc
  guard_target =ₛ to_exit segs code (mkst r (8 : word) m rom)
  exact h

example (segs : List MemImageType.Segment) (r : bvmap 5 word)
    (m rom : word → Option byte) :
    ∃ st, msteps segs (mkst r (v_addi (5 : word) 3) m rom) st := by
  refine ⟨?_, ?_⟩
  rotate_left
  norm_pc_state (mkst r (v_addi (5 : word) 3) m rom)
  run_tac
    let t ← getMainTarget
    unless (← wordLit? ((t.getArg! 1).getArg! 1)) == some 8 do
      throwError "norm_pc_state did not normalize the pc"
  exact msteps.mst_refl _

example (segs : List MemImageType.Segment) (r : bvmap 5 word)
    (m rom : word → Option byte) :
    ∃ r', msteps segs (mkst r' (v_addi (5 : word) 3) m rom) (mkst r 8 m rom) := by
  refine ⟨?_, ?_⟩
  rotate_left
  run_tac
    let before ← getMainTarget
    evalTactic (← `(tactic| norm_pc))
    unless before == (← instantiateMVars (← getMainTarget)) do
      throwError "norm_pc changed an evar-bearing state"
  exact msteps.mst_refl _

example (r : bvmap 5 word) (m rom : word → Option byte) :
    mkst r (v_addi (5 : word) 3) m rom = mkst r 8 m rom := by
  norm_pc
  guard_target =ₛ mkst r (v_addi (5 : word) 3) m rom = mkst r 8 m rom
  rfl

example (v : word) : ∃ w : word, w = v := by
  refine ⟨?_, ?_⟩
  rotate_left
  fail_if_success bveq
  rfl

-- Open but convertible is the safe third branch; bytes work too.
example (v : word) : v = v := by bveq
example : (5 : byte) + 3 = 8 := by bveq

-- Literal recognition agrees with SymSide, without treating redexes or
-- a byte literal as already-normalized words.
example : True := by
  run_tac
    for stx in #[← `((5 : word)), ← `(5#64),
        ← `((BitVec.ofNatLT 5 (by decide) : word)),
        ← `((BitVec.ofFin ⟨5, by decide⟩ : word))] do
      unless (← wordLit? (← elabTerm stx none)) == some 5 do
        throwError "wordLit? missed a literal spelling"
    for stx in #[← `(v_addi (5 : word) 3), ← `((5 : byte))] do
      unless (← wordLit? (← elabTerm stx none)).isNone do
        throwError "wordLit? accepted a computed word or a different width"
  exact True.intro

-- Constructor zero must evaluate too; a closed unsupported value must not.
example : True := by
  vm_eval Nat.zero
  vm_eval (Int.ofNat Nat.zero)
  vm_eval (Nat.succ Nat.zero)
  fail_if_success vm_eval (none : Option Nat)
  run_tac
    let z ← vmEval (mkConst ``Nat.zero)
    unless (← getNatValue? z) == some 0 do throwError "expected Nat zero"
  exact True.intro

-- Every occurrence is rewritten, including below a binder, and the second
-- goal is not touched. The guarded syntax rejects a first-occurrence-only port.
example :
    (∀ x : word, (v_addi (5 : word) 3, v_addi (5 : word) 3, x) = (8, 8, x)) ∧
    v_addi (5 : word) 3 = v_addi (5 : word) 3 := by
  constructor
  · wlit_replace (v_addi (5 : word) 3)
    guard_target =ₛ ∀ x : word, ((8 : word), (8 : word), x) = (8, 8, x)
    intro x
    with_reducible rfl
  · guard_target =ₛ v_addi (5 : word) 3 = v_addi (5 : word) 3
    rfl

-- Guard precedence and assigned-evar instantiation are observable without
-- executing an open term. The failure must be the evar diagnostic, even
-- with a free variable present; once assigned, it is the variable diagnostic.
example (v : word) : v = v := by
  run_tac
    let v := (← getMainTarget).getArg! 1
    let hole ← mkFreshExprMVar (mkConst ``word)
    let eq ← mkEq hole v
    let err ← try checkClosedTerm eq; pure "" catch ex => ex.toMessageData.toString
    unless err.endsWith "contains an evar" do throwError "wrong guard precedence: {err}"
    hole.mvarId!.assign v
    let err ← try checkClosedTerm eq; pure "" catch ex => ex.toMessageData.toString
    unless err.endsWith "mentions a context variable" do throwError "wrong open diagnostic: {err}"
    let hole ← mkFreshExprMVar (mkConst ``word)
    hole.mvarId!.assign (← elabTerm (← `((8 : word))) none)
    checkClosedTerm hole
    discard <| vmEval hole
  rfl

-- An abstract state has no constructor shape; a known shape with an open
-- pc is skipped. Neither path may fail or change the goal.
example (segs : List MemImageType.Segment) (st : RiscvSemantics.machine_state) :
    msteps segs st st := by
  norm_pc_state st
  norm_pc
  guard_target =ₛ msteps segs st st
  exact msteps.mst_refl _

example (segs : List MemImageType.Segment) (r : bvmap 5 word)
    (pc : word) (m rom : word → Option byte) :
    msteps segs (mkst r (v_addi pc 3) m rom) (mkst r (v_addi pc 3) m rom) := by
  norm_pc
  guard_target =ₛ msteps segs (mkst r (v_addi pc 3) m rom) (mkst r (v_addi pc 3) m rom)
  exact msteps.mst_refl _

-- Each tactic keyword remains an ordinary identifier outside tactic syntax.
example (check_closed_term vm_eval word_lit wlit_replace wlit
    norm_pc_state norm_pc bveq : Nat)
    (h : check_closed_term + vm_eval + word_lit + wlit_replace
      + wlit + norm_pc_state + norm_pc + bveq = 0) : bveq = 0 := by
  omega

end LinuxProcessSemantics.Common.StepTac

/-! ## Additions for ticket E-grep_args_ns (StepTac batch 2: lemmas)

All remaining lemmas and definitions outside `DispatchSmoke` in
`theories/Common/StepTac.v` at f44244ad6b80, in source order. Statements
and hypothesis order agree: `Z` is `Int`, `N`/`nat` are `Nat`, `S` is
`Nat.succ`, `Z.ltb`/`Z.leb` are `decide`, and `forallb` is `List.all`.
`v_add_comm` is protected because SymExec exports a different statement
under that name. No lemma or definition outside `DispatchSmoke` is unported.
-/

namespace LinuxProcessSemantics.Common.StepTac

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.SeqExec

/-- Rocq's literal negative-immediate corollary, with the same bound. -/
theorem v_addi_m1 (x : word) (h : 1 ≤ bv_unsigned x) :
    v_addi x (-1) = Z_to_bv 64 (bv_unsigned x - 1) :=
  v_addi_m x 1 h (by decide)

/-- Rocq's literal negative-immediate corollary, with the same bound. -/
theorem v_addi_m48 (x : word) (h : 48 ≤ bv_unsigned x) :
    v_addi x (-48) = Z_to_bv 64 (bv_unsigned x - 48) :=
  v_addi_m x 48 h (by decide)

/-- Rocq's literal negative-immediate corollary, with the same bound. -/
theorem v_addi_m64 (x : word) (h : 64 ≤ bv_unsigned x) :
    v_addi x (-64) = Z_to_bv 64 (bv_unsigned x - 64) :=
  v_addi_m x 64 h (by decide)

/-- Rocq's literal negative-immediate corollary, with the same bound. -/
theorem v_addi_m80 (x : word) (h : 80 ≤ bv_unsigned x) :
    v_addi x (-80) = Z_to_bv 64 (bv_unsigned x - 80) :=
  v_addi_m x 80 h (by decide)

/-- Byte disequality transfers to its unsigned reading, as in Rocq. -/
theorem byte_nz_u (b : byte) (hb : b ≠ Z_to_bv 8 0) : bv_unsigned b ≠ 0 := by
  intro h
  apply hb
  apply bv_eq_of_unsigned
  exact h

/-- Unsigned reading of a zero-extended byte; same Rocq statement. -/
theorem u_zext8 (b : byte) :
    bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b := by
  have h := u8_range b
  exact u_Z2bv _ h.1 (by omega)

/-- Truncation recovers the byte; same Rocq statement. -/
theorem zext8_byte (b : byte) :
    Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned b))) = b := by
  rw [u_zext8]
  apply bv_eq_of_unsigned
  rw [Z_to_bv_unsigned]
  have h := u8_range b
  change bv_unsigned b % 256 = bv_unsigned b
  exact Int.emod_eq_of_lt h.1 h.2

/-- Same Rocq byte-literal disequality and paired range hypothesis. -/
theorem byte_neq_lit_u (b : byte) (z : Int) (hz : 0 ≤ z ∧ z < 256)
    (hb : b ≠ Z_to_bv 8 z) : bv_unsigned b ≠ z := by
  intro h
  apply hb
  apply bv_eq_of_unsigned
  rw [h, Z_to_bv_unsigned]
  exact (Int.emod_eq_of_lt hz.1 hz.2).symm

/-- Same Rocq false branch comparison of zero-extended bytes. -/
theorem c_eq_zext_lit_false (b : byte) (z : Int) (hz : 0 ≤ z ∧ z < 256)
    (hb : b ≠ Z_to_bv 8 z) :
    c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 z) = false := by
  have hn := byte_neq_lit_u b z hz hb
  unfold c_eq bv_eqb
  apply decide_eq_false
  intro h
  have hu := congrArg bv_unsigned h
  rw [u_zext8, u_Z2bv z hz.1 (by omega)] at hu
  exact hn hu

/-- In-range natural offset; Rocq's `Z.of_nat` is the Int cast. -/
theorem u_ntw (n : Nat) (hn : (n : Int) < 2 ^ 64) :
    bv_unsigned (nat_to_word n) = (n : Int) :=
  u_Z2bv _ (by omega) hn

/-- Wrapping addition of zero, with Rocq's `nat_to_word` spelling. -/
theorem word_add_nat_0 (x : word) : x + nat_to_word 0 = x := by
  change x + (0 : word) = x
  exact BitVec.add_zero x

/-- Incrementing a symbolic base plus natural offset; no bound. -/
theorem word_add_nat_1 (a : word) (m : Nat) :
    v_addi (a + nat_to_word m) 1 = a + nat_to_word (Nat.succ m) := by
  rw [word_add_nat, word_add_nat]
  unfold v_addi
  apply bv_eq_of_unsigned
  simp only [Z_to_bv_unsigned, bv_wrap64_mod, Int.emod_add_emod]
  congr 1

/-- Decrementing a successor offset; no bound, as in Rocq. -/
theorem word_add_nat_m1 (a : word) (m : Nat) :
    v_addi (a + nat_to_word (Nat.succ m)) (-1) = a + nat_to_word m := by
  rw [word_add_nat, word_add_nat]
  unfold v_addi
  apply bv_eq_of_unsigned
  simp only [Z_to_bv_unsigned, bv_wrap64_mod, Int.emod_add_emod]
  congr 1
  omega

/-- Rocq's RHS is word addition, not `v_add`. Protected to avoid the
existing, differently stated `SymExec.v_add_comm`. -/
protected theorem v_add_comm (x y : word) : v_add x y = y + x := by
  apply bv_eq_of_unsigned
  rw [v_add, Z_to_bv_unsigned, bv_unsigned_add, Int.add_comm]

/-- Explicit wrapping addition; keeps Rocq's overflow hypothesis. -/
theorem v_add_wrap (x y : word) (_hw : 2 ^ 64 ≤ bv_unsigned x + bv_unsigned y) :
    v_add x y = Z_to_bv 64 (bv_unsigned x + bv_unsigned y - 2 ^ 64) := by
  apply bv_eq_of_unsigned
  simp only [v_add, Z_to_bv_unsigned, bv_wrap64_mod]
  omega

/-- Subtracting from zero gives two's-complement negation, as in Rocq. -/
theorem v_sub_0_neg (y : word) :
    v_sub (Z_to_bv 64 0) y = Z_to_bv 64 (-bv_unsigned y) := by
  unfold v_sub
  change Z_to_bv 64 (0 - bv_unsigned y) = _
  rw [Int.zero_sub]

/-- Small negative integer's unsigned word reading; same ordered bounds. -/
theorem u_neg_small (z : Int) (hz0 : 0 < z) (hz : z ≤ 2 ^ 64) :
    bv_unsigned (Z_to_bv 64 (-z)) = 2 ^ 64 - z := by
  rw [Z_to_bv_unsigned, bv_wrap64_mod]
  omega

/-- Increment a negative down-counter; Rocq's successor is `Nat.succ`. -/
theorem v_addi_neg_S (d : Nat) :
    v_addi (Z_to_bv 64 (-(Nat.succ d : Int))) 1 = Z_to_bv 64 (-(d : Int)) := by
  apply bv_eq_of_unsigned
  simp only [v_addi, Z_to_bv_unsigned, bv_wrap64_mod, Int.emod_add_emod]
  congr 1
  omega

/-- Rocq's two-segment avoidance; `Z.ltb` is `decide` in Lean. -/
theorem range_avoids_two (s0 s1 : Segment) (a n : Int)
    (h0 : decide (a < (s0.seg_base : Int) + (s0.seg_size : Int)) = false)
    (h1 : decide (a < (s1.seg_base : Int) + (s1.seg_size : Int)) = false) :
    range_avoids_ro_segs [s0, s1] a n = true := by
  simp only [range_avoids_ro_segs, List.all_cons, List.all_nil, h0, h1,
    Bool.and_false, Bool.not_false, Bool.or_true, Bool.and_true]

/-- Rocq's `forallb`/`Z.leb` become `List.all`/`decide`; same predicate. -/
def ro_segs_below (segs : List Segment) (data_base : Int) : Bool :=
  segs.all (fun seg => seg_writable seg ||
    decide ((seg.seg_base : Int) + (seg.seg_size : Int) ≤ data_base))

/-- Any range above the read-only segments avoids them, in Rocq order. -/
theorem range_avoids_ro_above (segs : List Segment) (data_base addr n : Int)
    (hbelow : ro_segs_below segs data_base = true) (haddr : data_base ≤ addr) :
    range_avoids_ro_segs segs addr n = true := by
  simp only [ro_segs_below, List.all_eq_true] at hbelow
  simp only [range_avoids_ro_segs, List.all_eq_true]
  intro seg hin
  have h := hbelow seg hin
  cases hw : seg_writable seg
  · simp only [hw, Bool.false_or, decide_eq_true_eq] at h
    have ha : decide (addr < (seg.seg_base : Int) + (seg.seg_size : Int)) = false :=
      decide_eq_false (by omega)
    simp only [ha, Bool.and_false, Bool.not_false, Bool.false_or]
  · simp only [Bool.true_or]

end LinuxProcessSemantics.Common.StepTac

/-! ## Additions for ticket E-grep_args_ns (StepTac batch 2: tactics)

Support tactics from `theories/Common/StepTac.v` at f44244ad6b80. Script names stay tactic-only syntax; local lets, kernel
conversion/evaluation and `omega` replace Rocq's context definitions, VM
and `lia`, using batch 1's public Meta interface. `wordLit?` now accepts an
optional width (default 64), so immediate/register literals of every width
use the same recognizer without changing its word-only default.
Instruction dispatch (`stepi_search`, `stepi`, `stepiv`, `stepiwv`, `stepj`,
`stepjr`, `stepi_at`, `stepw_addr`, `stepw_val`, `stepw_addr_hyps`, `stepw`,
`stepsd`, `stepld`, `smoke`) is batch 3's, in the section after this one.
-/

namespace LinuxProcessSemantics.Common.StepTac

open Lean Meta Elab Tactic
open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.ExitSim

private def chainStepNames : Array Name := #[
  ``CatSim.msteps.mst_step, ``CatSim.to_wexit.tw_step,
  ``LinuxProcessSemantics.Common.MmapSim.twm.twm_step,
  ``LinuxProcessSemantics.Common.MmapSim.twm_tail.twmt_step,
  ``LinuxProcessSemantics.Common.MmapSim.tmw.tmw_step,
  ``LinuxProcessSemantics.Common.StreamSim.to_wr.twr_step,
  ``LinuxProcessSemantics.Common.StreamSim.to_rd.trd_step,
  ``LinuxProcessSemantics.Common.WallSim.to_wall_tail.twt_step,
  ``LinuxProcessSemantics.Common.WallSim.twe_step,
  ``LinuxProcessSemantics.Common.DrainSim.to_out.tout_step,
  ``LinuxProcessSemantics.Common.DrainSim.to_rd.trd_step,
  ``ExitSim.to_exit.te_step]

/-- Rocq's ordered `first [eapply ...]`, implemented with Lean `apply`
and `newGoals := .nonDependentOnly`, preserving pending-syscall,
step, continuation goals.
`WallSim.twe_step` is a theorem, not a constructor, in Lean as in Rocq.
-/
elab "chain_step" : tactic => do
  for name in chainStepNames do
    let saved ← saveState
    try
      evalApplyLikeTactic (fun g e => g.apply e { newGoals := .nonDependentOnly })
        (mkIdent name)
      return
    catch _ => saved.restore
  throwError "chain_step: no step constructor applies"

/-- Rocq's backward-compatible alias, with exactly `chain_step`'s goals. -/
macro "step_intro" : tactic => `(tactic| chain_step)

private def sweepLiterals (names : Array Name) (replace : Expr → TacticM Unit) :
    TacticM Unit := withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  for name in names do
    let candidates ← IO.mkRef (#[] : Array Expr)
    discard <| Meta.transform t (pre := fun s => do
      if s.isAppOfArity name 2 then candidates.modify (·.push s)
      return .continue)
    for p in (← candidates.get) do
      let saved ← saveState
      try
        replace p
        return
      catch _ => saved.restore
  throwError "literal sweep: no candidate succeeds"

/-- Rocq's backtracking `repeat match`: try every occurrence of `v_addi`,
then `btgt`, `v_jalr`, `v_auipc`, in that priority order. A failed open
candidate restores the tactic state and advances to the next occurrence;
the first success restarts the sweep. Stop only when no candidate succeeds.
Uses batch 1's numeral form and leaves the rewritten first goal open. -/
elab "wlits" : tactic => do
  repeat
    let saved ← saveState
    try sweepLiterals #[``v_addi, ``btgt, ``v_jalr, ``v_auipc] wlitReplace
    catch _ => saved.restore; return

private def wlitClosed (p : Expr) : TacticM Unit := do
  checkClosedTerm p
  let u ← vmEval (← mkAppM ``bv_unsigned #[p])
  let lit ← mkAppM ``Z_to_bv #[mkNatLit 64, u]
  let proof ← Term.elabTerm (← `(by bveq)) (some (← mkEq p lit))
  Term.synthesizeSyntheticMVarsNoPostponing
  let g ← getMainGoal
  let r ← g.rewrite (← g.getType) (← instantiateMVars proof)
  replaceMainGoal [← g.replaceTargetEq r.eNew r.eqProof]

/-- Rocq's guarded `wlit_closed p`: evaluate the unsigned reading with
`vmEval`, prove equality by `bveq`, and rewrite to `Z_to_bv 64 u`, never
to an OfNat word numeral. Lean rewriting also finds convertible matches;
hypotheses and later goals stay unchanged.
The equality proved is `p = Z_to_bv 64 u`; Rocq’s `replace` proves the reverse
orientation. -/
elab "wlit_closed " p:term : tactic => withMainContext do
  wlitClosed (← elabTerm p none)

/-- Rocq's `v_addi`/`v_add`/`v_sub` sweep with `wlit_closed`'s spelling.
Rocq's ordinary `match` backtracks after a failed open candidate, so this
sweep skips it and tries subsequent occurrences and arms. No open redex
is evaluated. Only the first goal is rewritten and remains open. -/
elab "wlits_closed" : tactic => do
  repeat
    let saved ← saveState
    try sweepLiterals #[``v_addi, ``v_add, ``v_sub] wlitClosed
    catch _ => saved.restore; return

private def bitLiteral? (e : Expr) : MetaM (Option (Nat × Nat)) := do
  let ty ← whnfR (← inferType e)
  if ty.isAppOfArity ``BitVec 1 then
    if let some width ← getNatValue? ty.appArg! then
      if let some k ← wordLit? e width then return some (width, k)
  return none

/-- Rocq's literal-only conditional reduction, including five-bit register
literals. Lean's Bool `if` elaborates as `ite (bv_eqb a b = true)`;
`cond (bv_eqb a b)` is supported too. Both operands must be syntactic
BitVec literals. Replace just the conditional by conversion, without
simplifying unrelated terms or closing the goal. -/
elab "reduce_bv_eqb_ifs" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let t' ← Meta.transform t (post := fun s => do
    let candidate := if s.isAppOfArity ``ite 5 then
        let c := s.getArg! 1
        if c.isAppOfArity ``Eq 3 && c.getArg! 2 == mkConst ``Bool.true then
          some (c.getArg! 1, s.getArg! 3, s.getArg! 4)
        else none
      else if s.isAppOfArity ``cond 4 then
        some (s.getArg! 1, s.getArg! 2, s.getArg! 3)
      else none
    if let some (c, yes, no) := candidate then
      if c.isAppOfArity ``bv_eqb 3 then
        if let (some (n, a), some (m, b)) ←
            return (← bitLiteral? (c.getArg! 1), ← bitLiteral? (c.getArg! 2)) then
          if n == m then
            let v := if a % 2 ^ n == b % 2 ^ n then yes else no
            unless ← withAtLeastTransparency .default (isDefEq s v) do
              throwError "reduce_bv_eqb_ifs: literal guard did not reduce"
            return .done v
    return .continue)
  if t' != t then replaceMainGoal [← g.replaceTargetDefEq t']

/-- Rocq's ordered post-step sequence: literal conditionals, repeated
`List.drop_zero` rewriting (Rocq `rewrite ?skipn_O`), then `norm_pc`.
The repeat is parenthesized so Lean does not absorb
`norm_pc` into its body when no drop-zero redex is present.
`rewrite` deliberately leaves reflexive goals open. -/
macro "step_simpl" : tactic => `(tactic|
  (reduce_bv_eqb_ifs; (repeat rewrite [List.drop_zero]); norm_pc))

/-- Rocq's `repeat rewrite u_Z2bv by lia`, identical to SymBranch's
`sym_u_norm` alias: stop at the first instance whose two side conditions
`omega` cannot close; work on the first goal and leave it open. -/
macro "u_norm" : tactic => `(tactic|
  repeat (focus (rewrite [StepTac.u_Z2bv]; rotate_left; omega; omega)))

private def intNumeral (v : Int) : MetaM Expr := do
  if 0 ≤ v then mkNumeral (mkConst ``Int) v.toNat
  else mkAppM ``Neg.neg #[← mkNumeral (mkConst ``Int) (-v).toNat]

/-- Rocq's literal signed/unsigned readings, with SymSide's
`sym_imm_norm` behavior. `wordLit?`'s optional width supports every BitVec
width, including encoded immediates. Syntactically compute the numeral,
then check conversion at at least default transparency; nonliteral words
stay untouched. Invalid proof-backed literals fail conversion, as in the
`sym_` alias. Only the first goal changes and stays open.
A proof-backed literal whose spelling disagrees with its value makes `imm_norm`
fail here; Rocq’s repeat-match leaves it unchanged. -/
elab "imm_norm" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let t' ← Meta.transform t (post := fun s => do
    let uns := s.isAppOfArity ``bv_unsigned 2
    if uns || s.isAppOfArity ``bv_signed 2 then
      if let some (n, k) ← bitLiteral? s.appArg! then
        let u : Int := ((k % 2 ^ n : Nat) : Int)
        let v ← intNumeral (if uns || 2 * u < 2 ^ n then u else u - 2 ^ n)
        let raise (o : Options) :=
          exponentiation.threshold.set o (max (exponentiation.threshold.get o) n)
        unless ← withOptions raise (withAtLeastTransparency .default (isDefEq s v)) do
          throwError "imm_norm: {s} does not reduce to {v}"
        return .done v
    return .continue)
  if t' != t then replaceMainGoal [← g.replaceTargetDefEq t']

private def spNormStep : TacticM Unit := withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let candidates ← IO.mkRef (#[] : Array Expr)
  discard <| Meta.transform t (pre := fun s => do
    if s.isAppOfArity ``v_addi 2 &&
        ((s.getArg! 0).find? (·.isAppOfArity ``v_addi 2)).isNone then
      candidates.modify (·.push s)
    return .continue)
  for p in (← candidates.get) do
    let x ← Term.exprToSyntax (p.getArg! 0)
    let i ← Term.exprToSyntax (p.getArg! 1)
    for name in #[``v_addi_m80, ``v_addi_m64, ``v_addi_m48, ``v_addi_m32,
        ``v_addi_m16, ``v_addi_m1, ``v_addi_nneg_t] do
      let saved ← saveState
      try
        if name == ``v_addi_nneg_t then
          evalTactic (← `(tactic| focus
            (rewrite [$(mkIdent name) $x $i]; rotate_left;
             u_norm; omega; u_norm; omega)))
        else
          evalTactic (← `(tactic| focus
            (rewrite [$(mkIdent name) $x]; rotate_left; u_norm; omega)))
        return
      catch _ => saved.restore
  throwError "sp_norm: no justified innermost addition"

/-- Rocq's `imm_norm`, then innermost `v_addi` rewriting, trying m80,
m64, m48, m32, m16, m1, nneg in order. Each side condition uses
`u_norm; omega`; each successful iteration finishes with `u_norm`.
Rocq's `cbn [Z.to_N]` is a no-op: Lean's `Z_to_bv` uses `BitVec.ofInt`,
so these rewrites introduce no `Z.to_N` wrapper. Unsupported offsets or
unprovable bounds leave that addition unchanged and backtrack to the next
occurrence, as does Rocq's level-zero failure on a nested base.
A proof-backed literal whose spelling disagrees with its value makes `imm_norm`
fail here; Rocq’s repeat-match leaves it unchanged. -/
elab "sp_norm" : tactic => do
  evalTactic (← `(tactic| imm_norm))
  repeat
    let saved ← saveState
    try
      spNormStep
      evalTactic (← `(tactic| u_norm))
    catch _ => saved.restore; return

/-- Rocq's bool_decide VM cast becomes `decide +kernel`. Closed decidable
goals are checked by the kernel; open equations whose decision is stuck
fail. Unlike `bveq`, this is a general decidable-goal closer. -/
macro "vm_refl_bv" : tactic => `(tactic| decide +kernel)

/-- Rocq's `erewrite rdn_ext` wrapper. Lean's `rdn_ext` takes segs, k,
m1, m2, a, no-overflow, pointwise in that order. Ordinary Lean `rewrite`
also exposes m2 as a goal; this Meta rewrite keeps it as a shared evar,
restoring Rocq's three-goal order: main, no-overflow, pointwise. Discharge
no-overflow with `imm_norm; u_norm; omega`, then introduce the point and
normalize its reverted bound. Leaves main then pointwise, with any later
caller goals untouched.
A proof-backed literal whose spelling disagrees with its value makes `imm_norm`
fail here; Rocq’s repeat-match leaves it unchanged. -/
elab "rdn_ext_lit" : tactic => withMainContext do
  let goals ← getGoals
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some p := t.find? (·.isAppOfArity ``rdn 4)
    | throwError "rdn_ext_lit: no rdn occurrence"
  let m2 ← mkFreshExprMVar (← inferType (p.getArg! 1))
  let lemma ← mkAppM ``PropExec.rdn_ext
    #[p.getArg! 0, p.getArg! 3, p.getArg! 1, m2, p.getArg! 2]
  let (premises, _, _) ← forallMetaTelescopeReducing (← inferType lemma)
  unless premises.size == 2 do throwError "rdn_ext_lit: unexpected rdn_ext premises"
  let r ← g.rewrite t (mkAppN lemma premises)
  let main ← g.replaceTargetEq r.eNew r.eqProof
  setGoals [premises[0]!.mvarId!]
  evalTactic (← `(tactic| (imm_norm; u_norm; omega)))
  unless (← getGoals).isEmpty do throwError "rdn_ext_lit: no-overflow remains"
  setGoals [premises[1]!.mvarId!]
  let x := mkIdent ((← getLCtx).getUnusedName `x)
  let hx := mkIdent ((← getLCtx).getUnusedName `Hx)
  evalTactic (← `(tactic| (intro $x:ident $hx:ident; revert $hx:ident; imm_norm; u_norm; intro $hx:ident)))
  setGoals (main :: (← getGoals) ++ goals.tail!)

end LinuxProcessSemantics.Common.StepTac

namespace LinuxProcessSemantics.Common.StepTac

open Lean Meta Elab Tactic
open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.ExitSim

-- Step constructors must leave exactly pending-syscall, step, continuation.
example (segs : List MemImageType.Segment) (s t : machine_state)
    (hp : s.ms_svc_pending = none) (hs : step segs s = MachineOk t) :
    msteps segs s t := by
  chain_step
  · guard_target =ₛ s.ms_svc_pending = none
    exact hp
  · exact hs
  · guard_target =ₛ msteps segs t t
    exact msteps.mst_refl _

example (segs : List MemImageType.Segment) (s t : machine_state) (code : word)
    (hp : s.ms_svc_pending = none) (hs : step segs s = MachineOk t)
    (ht : to_exit segs code t) : to_exit segs code s := by
  step_intro
  · guard_target =ₛ s.ms_svc_pending = none
    exact hp
  · exact hs
  · guard_target =ₛ to_exit segs code t
    exact ht

-- `WallSim.twe_step` is a lemma, not a constructor: with the buffer list
-- abstract, `to_wallexit` does not unfold, so `tw_step` and `twt_step`
-- fail and the ninth alternative applies, with the same three goals.
example (segs : List MemImageType.Segment) (fd : word) (s t : machine_state)
    (bufs : List (List byte)) (code : word)
    (hp : s.ms_svc_pending = none) (hs : step segs s = MachineOk t)
    (hw : WallSim.to_wallexit segs fd bufs code t) :
    WallSim.to_wallexit segs fd bufs code s := by
  chain_step
  · guard_target =ₛ s.ms_svc_pending = none
    exact hp
  · exact hs
  · guard_target =ₛ WallSim.to_wallexit segs fd bufs code t
    exact hw

example : True := by
  fail_if_success chain_step
  fail_if_success step_intro
  exact True.intro

example : (v_addi (5 : word) 3, btgt (8 : word) 4,
    v_jalr (12 : word) 1, v_auipc (4 : word) 1) = (8, 12, 12, 5) := by
  wlits
  guard_target =ₛ ((8 : word), (12 : word), (12 : word), (5 : word)) = (8, 12, 12, 5)
  with_reducible rfl

-- An open first occurrence must not hide a later closed one or another arm.
example (v : word) : (v_addi v 4, v_addi (5 : word) 3, btgt (8 : word) 4) =
    (v_addi v 4, 8, 12) := by
  wlits
  guard_target =ₛ (v_addi v 4, (8 : word), (12 : word)) = (v_addi v 4, 8, 12)
  wlits
  guard_target =ₛ (v_addi v 4, (8 : word), (12 : word)) = (v_addi v 4, 8, 12)
  with_reducible rfl

example (v : word) : v_addi v 0 = v := by
  wlits
  guard_target =ₛ v_addi v 0 = v
  fail_if_success (wlits; with_reducible rfl)
  exact PropExec.v_addi_0 v

example (v : word) : (v_addi (5 : word) 3, v_addi v 4) = (8, v_addi v 4) := by
  wlits
  guard_target =ₛ ((8 : word), v_addi v 4) = (8, v_addi v 4)
  with_reducible rfl

example : v_addi (5 : word) 3 = Z_to_bv 64 8 := by
  wlit_closed (v_addi (5 : word) 3)
  guard_target = Z_to_bv 64 8 = Z_to_bv 64 8
  with_reducible rfl

example (v : word) : v_addi v 0 = v := by
  fail_if_success wlit_closed (v_addi v 0)
  exact PropExec.v_addi_0 v

example (v : word) :
    (v_addi v 4, v_addi (5 : word) 3, v_add (4 : word) 5, v_sub (9 : word) 6) =
    (v_addi v 4, Z_to_bv 64 8, Z_to_bv 64 9, Z_to_bv 64 3) := by
  wlits_closed
  guard_target = (v_addi v 4, Z_to_bv 64 8, Z_to_bv 64 9, Z_to_bv 64 3) =
    (v_addi v 4, Z_to_bv 64 8, Z_to_bv 64 9, Z_to_bv 64 3)
  with_reducible rfl

example (v : word) : v_addi v 0 = v := by
  wlits_closed
  guard_target =ₛ v_addi v 0 = v
  fail_if_success (wlits_closed; with_reducible rfl)
  exact PropExec.v_addi_0 v

example (x y : Nat) : (if bv_eqb (0 : reg) 0 then x else y) = x := by
  reduce_bv_eqb_ifs
  guard_target =ₛ x = x
  with_reducible rfl

example (x y : Nat) : (if bv_eqb (3 : reg) 0 then x else y) = y := by
  reduce_bv_eqb_ifs
  guard_target =ₛ y = y
  with_reducible rfl

example (x y : Nat) : cond (bv_eqb (3 : word) 3) x y = x := by
  reduce_bv_eqb_ifs
  guard_target =ₛ x = x
  with_reducible rfl

example (r : reg) (x y : Nat) (h : bv_eqb r 0 = true) :
    (if bv_eqb r 0 then x else y) = x := by
  reduce_bv_eqb_ifs
  guard_target =ₛ (if bv_eqb r 0 then x else y) = x
  fail_if_success (reduce_bv_eqb_ifs; with_reducible rfl)
  simp only [h, ite_true]

example (segs : List MemImageType.Segment) (r : bvmap 5 word)
    (m rom : word → Option byte) :
    msteps (List.drop 0 segs)
      (mkst (if bv_eqb (0 : reg) 0 then r else r) (v_addi (5 : word) 3) m rom)
      (mkst r 8 m rom) := by
  step_simpl
  guard_target =ₛ msteps segs (mkst r (8 : word) m rom) (mkst r (8 : word) m rom)
  exact msteps.mst_refl _

example (n : Nat) (xs : List Nat) (h : xs.drop n = []) : xs.drop n = [] := by
  step_simpl
  guard_target =ₛ xs.drop n = []
  fail_if_success (step_simpl; with_reducible rfl)
  exact h

example (z : Int) (h0 : 0 ≤ z) (h1 : z < 2 ^ 64) :
    bv_unsigned (Z_to_bv 64 z) = z := by
  u_norm
  guard_target =ₛ z = z
  with_reducible rfl


example (z : Int) : bv_unsigned (Z_to_bv 64 (-1)) + bv_unsigned (Z_to_bv 64 z) =
    bv_unsigned (Z_to_bv 64 (-1)) + bv_unsigned (Z_to_bv 64 z) := by
  u_norm
  guard_target =ₛ bv_unsigned (Z_to_bv 64 (-1)) + bv_unsigned (Z_to_bv 64 z) =
    bv_unsigned (Z_to_bv 64 (-1)) + bv_unsigned (Z_to_bv 64 z)
  with_reducible rfl

example : bv_signed (4080 : BitVec 12) + bv_unsigned (5 : word) = -16 + 5 := by
  imm_norm
  guard_target =ₛ (-16 : Int) + 5 = -16 + 5
  with_reducible rfl

example (h : 7 < 2 ^ 2) : bv_unsigned (BitVec.ofNatLT 7 h : BitVec 2) = 7 := by
  fail_if_success imm_norm
  rfl

example (v : word) : bv_unsigned v = bv_unsigned v := by
  imm_norm
  guard_target =ₛ bv_unsigned v = bv_unsigned v
  with_reducible rfl

example (sp : word) (lo : 128 ≤ bv_unsigned sp) (hi : bv_unsigned sp < 2 ^ 63) :
    v_addi (v_addi sp (-80)) 16 = Z_to_bv 64 (bv_unsigned sp - 80 + 16) := by
  sp_norm
  guard_target = Z_to_bv 64 (bv_unsigned sp - 80 + 16) =
    Z_to_bv 64 (bv_unsigned sp - 80 + 16)
  with_reducible rfl

example (sp : word) (lo : 16 ≤ bv_unsigned sp) :
    v_addi sp (bv_signed (4080 : BitVec 12)) = Z_to_bv 64 (bv_unsigned sp - 16) := by
  sp_norm
  guard_target = Z_to_bv 64 (bv_unsigned sp - 16) = Z_to_bv 64 (bv_unsigned sp - 16)
  with_reducible rfl

example (sp : word) : v_addi sp (-80) = Z_to_bv 64 (bv_unsigned sp - 80) := by
  sp_norm
  guard_target =ₛ v_addi sp (-80) = Z_to_bv 64 (bv_unsigned sp - 80)
  fail_if_success (sp_norm; with_reducible rfl)
  unfold v_addi
  congr 1

example : (5 : byte) + 3 = 8 := by vm_refl_bv
example (v : word) : v_addi v 0 = v := by
  fail_if_success vm_refl_bv
  exact PropExec.v_addi_0 v

example (segs : List MemImageType.Segment) (m1 m2 : word → Option byte)
    (bs : List byte) (hr : rdn segs m2 (Z_to_bv 64 8) 2 = some bs)
    (he : ∀ x : word, 8 ≤ bv_unsigned x ∧ bv_unsigned x < 10 → m1 x = m2 x) :
    rdn segs m1 (Z_to_bv 64 8) 2 = some bs := by
  rdn_ext_lit
  · exact hr
  · guard_target =ₛ m1 x = m2 x
    guard_hyp Hx : 8 ≤ bv_unsigned x ∧ bv_unsigned x < 8 + ((2 : Nat) : Int)
    exact he x (by omega)

example : True := by
  fail_if_success rdn_ext_lit
  exact True.intro

-- A valid ROM rewrite must not manufacture its no-overflow premise.
example (segs : List MemImageType.Segment) (m : word → Option byte)
    (a : word) (n : Nat) : rdn segs m a n = rdn segs m a n := by
  fail_if_success rdn_ext_lit
  rfl

example (segs : List MemImageType.Segment) (m : word → Option byte) :
    rdn segs m (Z_to_bv 64 (2 ^ 64 - 1)) 2 =
      rdn segs m (Z_to_bv 64 (2 ^ 64 - 1)) 2 := by
  fail_if_success rdn_ext_lit
  rfl

-- No side-condition bounds: u_norm must leave the first projection alone.
example (z : Int) (h : bv_unsigned (Z_to_bv 64 z) = z) :
    bv_unsigned (Z_to_bv 64 z) = z := by
  fail_if_success (u_norm; with_reducible rfl)
  exact h

example (z : Int) (h0 : 0 ≤ z) (h1 : z < 2 ^ 64) :
    (bv_unsigned (Z_to_bv 64 (-1)), bv_unsigned (Z_to_bv 64 z)) =
    (bv_unsigned (Z_to_bv 64 (-1)), z) := by
  u_norm
  guard_target =ₛ (bv_unsigned (Z_to_bv 64 (-1)), bv_unsigned (Z_to_bv 64 z)) =
    (bv_unsigned (Z_to_bv 64 (-1)), z)
  fail_if_success (u_norm; with_reducible rfl)
  rw [u_Z2bv z h0 h1]

-- The register-literal guard is symmetric, and closed computed operands
-- are still not syntactic literals.
example (r : reg) (x y : Nat) (h : bv_eqb 0 r = false) :
    (if bv_eqb 0 r then x else y) = y := by
  reduce_bv_eqb_ifs
  guard_target =ₛ (if bv_eqb 0 r then x else y) = y
  fail_if_success (reduce_bv_eqb_ifs; with_reducible rfl)
  simp only [h, Bool.false_eq_true, ↓reduceIte]

example (x y : Nat) : (if bv_eqb (v_addi (1 : word) 2) 3 then x else y) = x := by
  reduce_bv_eqb_ifs
  guard_target =ₛ (if bv_eqb (v_addi (1 : word) 2) 3 then x else y) = x
  fail_if_success (reduce_bv_eqb_ifs; with_reducible rfl)
  have h : bv_eqb (v_addi (1 : word) 2) 3 = true := by decide
  simp only [h, ite_true]

-- Every negative literal arm must fire, while unsupported -2 stays put.
example (sp : word) (lo : 80 ≤ bv_unsigned sp) :
    (v_addi sp (-64), v_addi sp (-48), v_addi sp (-32), v_addi sp (-1)) =
    (Z_to_bv 64 (bv_unsigned sp - 64), Z_to_bv 64 (bv_unsigned sp - 48),
     Z_to_bv 64 (bv_unsigned sp - 32), Z_to_bv 64 (bv_unsigned sp - 1)) := by
  sp_norm
  with_reducible rfl

example (sp : word) (lo : 2 ≤ bv_unsigned sp) :
    v_addi sp (-2) = Z_to_bv 64 (bv_unsigned sp - 2) := by
  sp_norm
  guard_target =ₛ v_addi sp (-2) = Z_to_bv 64 (bv_unsigned sp - 2)
  fail_if_success (sp_norm; with_reducible rfl)
  exact SeqExec.v_addi_m sp 2 lo (by decide)

-- Later goals and hypotheses are untouched by literal normalization.
example (z : Int) (h0 : 0 ≤ z) (h1 : z < 2 ^ 64)
    (h : bv_unsigned (Z_to_bv 64 z) = z) :
    bv_unsigned (Z_to_bv 64 z) = z ∧ bv_unsigned (Z_to_bv 64 z) = z := by
  constructor
  · u_norm
    guard_hyp h :ₛ bv_unsigned (Z_to_bv 64 z) = z
    guard_target =ₛ z = z
    with_reducible rfl
  · guard_target =ₛ bv_unsigned (Z_to_bv 64 z) = z
    exact h

-- Every new tactic keyword remains an ordinary identifier.
example (chain_step step_intro wlits wlit_closed wlits_closed reduce_bv_eqb_ifs
    step_simpl u_norm imm_norm sp_norm vm_refl_bv rdn_ext_lit : Nat)
    (h : chain_step + step_intro + wlits + wlit_closed + wlits_closed + reduce_bv_eqb_ifs
      + step_simpl + u_norm + imm_norm + sp_norm + vm_refl_bv + rdn_ext_lit = 0) :
    rdn_ext_lit = 0 := by omega

-- The first candidate has no bound; the later candidate must still rewrite.
example (x sp : word) (lo : 80 ≤ bv_unsigned sp) :
    (v_addi x (-80), v_addi sp (-80)) =
    (v_addi x (-80), Z_to_bv 64 (bv_unsigned sp - 80)) := by
  sp_norm
  guard_target = (v_addi x (-80), Z_to_bv 64 (bv_unsigned sp - 80)) =
    (v_addi x (-80), Z_to_bv 64 (bv_unsigned sp - 80))
  sp_norm
  with_reducible rfl

end LinuxProcessSemantics.Common.StepTac

/-! ## StepTac batch 3: instruction dispatch

Pinned to `theories/Common/StepTac.v` at f44244ad6b80. Fetch and decode
arguments are terms; proof-script arguments are parenthesized tactic sequences.
The `is_ecall` closer tries conversion first, as Rocq does, then a hypothesis
for abstract words (Lean's variable-based dispatch tests need this extension).
All applications keep dependent metavariables hidden, like Rocq `eapply`.
-/
namespace LinuxProcessSemantics.Common.StepTac

open Lean Meta Elab Tactic
open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.DecodeC
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.CatExec

private def applyStep (t : Term) : TacticM Unit := do
  evalApplyLikeTactic (fun g e => g.apply e { newGoals := .nonDependentOnly }) t

-- Run a script on precisely one goal, preserving all later goals. Unlike
-- `<;>`, this does not run continuation normalization on a divisor premise.
private def onFirst (script : TacticM Unit) : TacticM Unit := do
  let g ← getMainGoal
  let rest := (← getGoals).tail!
  setGoals [g]
  script
  setGoals ((← getGoals) ++ rest)

private def closeFirst (t : TSyntax `tactic) : TacticM Unit :=
  onFirst do
    evalTactic t
    unless (← getGoals).isEmpty do throwError "step tactic: side condition remains"

private def fetchDecode (f d : Term) : TacticM Unit := do
  closeFirst (← `(tactic| exact $f))
  closeFirst (← `(tactic| first | rfl | assumption))
  closeFirst (← `(tactic| exact $d))

private def inChain (instruction : TacticM Unit) : TacticM Unit := do
  onFirst do
    evalTactic (← `(tactic| chain_step))
    closeFirst (← `(tactic| rfl))
    let gs ← getGoals
    unless gs.length == 2 do throwError "step tactic: expected step and continuation"
    setGoals [gs[0]!]
    instruction
    let premises ← getGoals
    setGoals [gs[1]!]
    evalTactic (← `(tactic| step_simpl))
    setGoals (premises ++ (← getGoals))

-- Syntactic matching deliberately does not unfold a user's decode wrapper:
-- an unrecognized shape takes Rocq's search/default arm.
private def decodeShape (d : Term) : TacticM (Name × Name) := withMainContext do
  let ty ← instantiateMVars (← inferType (← elabTerm d none))
  unless ty.isAppOfArity ``Eq 3 do return (.anonymous, .anonymous)
  let rhs := ty.getArg! 2
  unless rhs.isAppOfArity ``Option.some 2 do return (.anonymous, .anonymous)
  let pair := rhs.appArg!
  unless pair.isAppOfArity ``Prod.mk 4 do return (.anonymous, .anonymous)
  let sh := pair.getArg! 2
  return (sh.getAppFn.constName?.getD .anonymous,
    if sh.getAppNumArgs > 0 then ((sh.getArg! 0).getAppFn.constName?.getD .anonymous) else .anonymous)

private def stepName (short : String) : Name :=
  Name.str `LinuxProcessSemantics.Common.PropExec ("step_" ++ short)

private def seqStepName (short : String) : Name :=
  Name.str `LinuxProcessSemantics.Common.SeqExec ("step_" ++ short)

private def plainStep (name : Name) (f d : Term) : TacticM Unit := withMainContext do
  -- Rocq supplies F/eq_refl/D before checking the resulting step equality.
  -- Applying a bare lemma first can get stuck unifying its unknown rd's
  -- conditional writeback with an already simplified successor state.
  let info ← getConstInfo name
  let n ← forallTelescopeReducing info.type fun xs _ => do
    for i in [:xs.size] do
      if ← isProp (← inferType xs[i]!) then return i
    throwError "stepi_search: missing fetch premise"
  let mut args : Array Term := #[]
  for _ in [:n] do args := args.push (← `(_))
  args := args.push f
  args := args.push (← `(by first | rfl | assumption))
  args := args.push d
  evalTactic (← `(tactic| exact ($(mkIdent name) $args*)))

private def searchNames : Array Name := #[
  ``PropExec.step_addi,
  ``PropExec.step_add,
  ``PropExec.step_sub,
  ``PropExec.step_slli,
  ``PropExec.step_auipc,
  ``PropExec.step_lui,
  ``PropExec.step_addiw,
  ``PropExec.step_andi,
  ``PropExec.step_sltiu,
  ``PropExec.step_xori,
  ``PropExec.step_srli,
  ``PropExec.step_mul,
  ``PropExec.step_ori,
  ``PropExec.step_subw,
  ``PropExec.step_slti,
  ``PropExec.step_srai,
  ``PropExec.step_and,
  ``PropExec.step_or,
  ``PropExec.step_xor,
  ``PropExec.step_sll,
  ``PropExec.step_srl,
  ``PropExec.step_sra,
  ``PropExec.step_slt,
  ``PropExec.step_sltu,
  ``PropExec.step_addw,
  ``PropExec.step_sllw,
  ``PropExec.step_srlw,
  ``PropExec.step_sraw,
  ``PropExec.step_slliw,
  ``PropExec.step_srliw,
  ``PropExec.step_sraiw,
  ``PropExec.step_mulh,
  ``PropExec.step_mulhsu,
  ``PropExec.step_mulhu,
  ``PropExec.step_div,
  ``PropExec.step_rem,
  ``PropExec.step_mulw,
  ``PropExec.step_divw,
  ``PropExec.step_divuw,
  ``PropExec.step_remw,
  ``PropExec.step_remuw]

/-- The fixed Rocq alternative order, applied directly to a step equality.

Unlike Rocq’s `eq_refl`, ecall closure also accepts a hypothesis after
conversion fails. -/
elab "stepi_search " f:term:max d:term:max : tactic => do
  onFirst do
    for name in searchNames do
      let saved ← saveState
      try
        plainStep name f d
        return
      catch _ => saved.restore
    throwError "stepi_search: no instruction alternative applies"

private def dispatchName (d : Term) : TacticM (Option String) := do
  let (ctor, op) ← decodeShape d
  if ctor == ``instr.OpImm && op == ``aluop.ALU_ADD then return some "addi"
  if ctor == ``instr.OpImm && op == ``aluop.ALU_AND then return some "andi"
  if ctor == ``instr.OpImm && op == ``aluop.ALU_OR then return some "ori"
  if ctor == ``instr.OpImm && op == ``aluop.ALU_XOR then return some "xori"
  if ctor == ``instr.OpImm && op == ``aluop.ALU_SLT then return some "slti"
  if ctor == ``instr.OpImm && op == ``aluop.ALU_SLTU then return some "sltiu"
  if ctor == ``instr.Op && op == ``aluop.ALU_ADD then return some "add"
  if ctor == ``instr.Op && op == ``aluop.ALU_SUB then return some "sub"
  if ctor == ``instr.Op && op == ``aluop.ALU_AND then return some "and"
  if ctor == ``instr.Op && op == ``aluop.ALU_OR then return some "or"
  if ctor == ``instr.Op && op == ``aluop.ALU_XOR then return some "xor"
  if ctor == ``instr.Op && op == ``aluop.ALU_SLL then return some "sll"
  if ctor == ``instr.Op && op == ``aluop.ALU_SRL then return some "srl"
  if ctor == ``instr.Op && op == ``aluop.ALU_SRA then return some "sra"
  if ctor == ``instr.Op && op == ``aluop.ALU_SLT then return some "slt"
  if ctor == ``instr.Op && op == ``aluop.ALU_SLTU then return some "sltu"
  if ctor == ``instr.Op32 && op == ``aluop.ALU_ADD then return some "addw"
  if ctor == ``instr.Op32 && op == ``aluop.ALU_SUB then return some "subw"
  if ctor == ``instr.Op32 && op == ``aluop.ALU_SLL then return some "sllw"
  if ctor == ``instr.Op32 && op == ``aluop.ALU_SRL then return some "srlw"
  if ctor == ``instr.Op32 && op == ``aluop.ALU_SRA then return some "sraw"
  if ctor == ``instr.OpImm32 then return some "addiw"
  if ctor == ``instr.ShiftImm && op == ``aluop.ALU_SLL then return some "slli"
  if ctor == ``instr.ShiftImm && op == ``aluop.ALU_SRL then return some "srli"
  if ctor == ``instr.ShiftImm && op == ``aluop.ALU_SRA then return some "srai"
  if ctor == ``instr.ShiftImm32 && op == ``aluop.ALU_SLL then return some "slliw"
  if ctor == ``instr.ShiftImm32 && op == ``aluop.ALU_SRL then return some "srliw"
  if ctor == ``instr.ShiftImm32 && op == ``aluop.ALU_SRA then return some "sraiw"
  if ctor == ``instr.Auipc then return some "auipc"
  if ctor == ``instr.Lui then return some "lui"
  if ctor == ``instr.Mul && op == ``mulop.M_MUL then return some "mul"
  if ctor == ``instr.Mul && op == ``mulop.M_MULH then return some "mulh"
  if ctor == ``instr.Mul && op == ``mulop.M_MULHSU then return some "mulhsu"
  if ctor == ``instr.Mul && op == ``mulop.M_MULHU then return some "mulhu"
  if ctor == ``instr.Mul && op == ``mulop.M_DIV then return some "div"
  if ctor == ``instr.Mul && op == ``mulop.M_REM then return some "rem"
  if ctor == ``instr.Mul && op == ``mulop.M_DIVU then return some "divu"
  if ctor == ``instr.Mul && op == ``mulop.M_REMU then return some "remu"
  if ctor == ``instr.Mul32 && op == ``mulop.M_MUL then return some "mulw"
  if ctor == ``instr.Mul32 && op == ``mulop.M_DIV then return some "divw"
  if ctor == ``instr.Mul32 && op == ``mulop.M_DIVU then return some "divuw"
  if ctor == ``instr.Mul32 && op == ``mulop.M_REM then return some "remw"
  if ctor == ``instr.Mul32 && op == ``mulop.M_REMU then return some "remuw"
  return none

/-- Chain one ALU instruction using decode-shape dispatch, with the ordered
`stepi_search` fallback. Divu/remu retain their optional assumption/omega
closer and leave a remaining nonzero premise before the continuation.
Unlike Rocq’s `eq_refl`, ecall closure also accepts a hypothesis after
conversion fails. -/
elab "stepi " f:term:max d:term:max : tactic => do
  inChain do
    match ← dispatchName d with
    | none => evalTactic (← `(tactic| stepi_search $f $d))
    | some short =>
      if short == "divu" || short == "remu" then
        applyStep (mkIdent (seqStepName short))
        fetchDecode f d
        evalTactic (← `(tactic| try first | assumption | omega))
      else plainStep (stepName short) f d

private def valueStep (name : Name) (f d v : Term) (tac : TSyntax ``Parser.Tactic.tacticSeq) :
    TacticM Unit := do
  applyStep (← `($(mkIdent name) (v := $v)))
  fetchDecode f d
  closeFirst (← `(tactic| rfl))
  evalTactic (← `(tactic| ($tac:tacticSeq)))

/-- Pre-normalized writeback dispatch, in Rocq order, with the addi fallback.
All `_at` alternatives are in SeqExec; script syntax is `stepiv F D vv (tac)`.
A selected arm's failure does not fall through to the default.
Unlike Rocq’s `eq_refl`, ecall closure also accepts a hypothesis after
conversion fails. -/
elab "stepiv " f:term:max d:term:max v:term:max " (" tac:tacticSeq ")" : tactic => do
  inChain do
    let short ← dispatchName d
    let name := match short with
      | some s => if #["addi", "andi", "ori", "xori", "sltiu", "slli", "srli",
          "srai", "add", "sub", "addiw", "mul", "lui", "auipc"].contains s
          then s else "addi"
      | none => "addi"
    valueStep (seqStepName (name ++ "_at")) f d v tac

/-- The addiw-only pre-normalized writeback wrapper; same five side goals
as `stepiv`, with the caller script in the last position.
Unlike Rocq’s `eq_refl`, ecall closure also accepts a hypothesis after
conversion fails. -/
elab "stepiwv " f:term:max d:term:max v:term:max " (" tac:tacticSeq ")" : tactic => do
  inChain (valueStep (seqStepName "addiw_at") f d v tac)

/-- Chain jal, trying the no-link PropExec lemma before SeqExec's linking
lemma, then run `step_simpl` on the continuation.
Unlike Rocq’s `eq_refl`, ecall closure also accepts a hypothesis after
conversion fails. -/
elab "stepj " f:term:max d:term:max : tactic => do
  inChain do
    for name in #[stepName "jal_x0", seqStepName "jal_link"] do
      let saved ← saveState
      try
        plainStep name f d
        return
      catch _ => saved.restore
    throwError "stepj: neither jal alternative applies"

/-- Chain jalr, trying x0 then linking, with target proof `tac` after the
link-register guard (linking only). The target should be closed for norm_pc.
Unlike Rocq’s `eq_refl`, ecall closure also accepts a hypothesis after
conversion fails. -/
elab "stepjr " f:term:max d:term:max v:term:max " (" tac:tacticSeq ")" : tactic => do
  inChain do
    for short in #["jalr_x0", "jalr_link"] do
      let saved ← saveState
      try
        applyStep (← `($(mkIdent (seqStepName short)) (tgt := $v)))
        fetchDecode f d
        if short == "jalr_link" then closeFirst (← `(tactic| rfl))
        evalTactic (← `(tactic| ($tac:tacticSeq)))
        return
      catch _ => saved.restore
    throwError "stepjr: neither jalr alternative applies"

/-- Addi with Rocq's baked-in value closer. `congr 1 <;> omega` replaces
`f_equal; lia`; the last unsigned-equality path is closedness guarded.
Unlike Rocq’s `eq_refl`, ecall closure also accepts a hypothesis after
conversion fails. -/
elab "stepi_at " f:term:max d:term:max v:term:max : tactic => do
  inChain do
    applyStep (← `(SeqExec.step_addi_at (v := $v)))
    fetchDecode f d
    closeFirst (← `(tactic| rfl))
    evalTactic (← `(tactic|
      (getr_resolve; regupd_resolve; reduce_bv_eqb_ifs; sp_norm)))
    for closer in #[← `(tactic| rfl), ← `(tactic| omega),
        ← `(tactic| congr 1 <;> omega)] do
      let saved ← saveState
      try
        closeFirst closer
        return
      catch _ => saved.restore
    evalTactic (← `(tactic| apply bv_eq_of_unsigned))
    withMainContext do checkClosedTerm (← instantiateMVars (← getMainTarget))
    evalTactic (← `(tactic| decide +kernel))

/-- Resolve store address, normalize sp arithmetic, then use Rocq's
conversion / congruence-arithmetic / guarded bitvector closers. -/
macro "stepw_addr" : tactic => `(tactic|
  (getr_resolve; regupd_resolve; sp_norm
   first | rfl | congr 1 <;> omega | bveq))

private def betaGoal : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  -- Revisit substitutions: headBeta in a postorder walk would miss an
  -- application introduced under a constructor by reducing its parent.
  let t' ← Core.betaReduce t
  if t' != t then replaceMainGoal [← g.replaceTargetDefEq t']

/-- Resolve store value, fully beta-reduce without delta/zeta reduction,
simplify literal guards, then try conversion, sp normalization with
congruence arithmetic, and bveq. -/
elab "stepw_val" : tactic => do
  evalTactic (← `(tactic| (getr_resolve; regupd_resolve)))
  betaGoal
  evalTactic (← `(tactic|
    (reduce_bv_eqb_ifs
     first | rfl | (sp_norm; first | rfl | congr 1 <;> omega) | bveq)))

private def rewriteRegHyp : TacticM Unit := withMainContext do
  let target ← getMainTarget
  for decl in (← getLCtx).decls.toArray.reverse do
    let some decl := decl | continue
    unless decl.isImplementationDetail do
      let ty ← instantiateMVars decl.type
      if ty.isAppOfArity ``Eq 3 then
        let lhs := ty.getArg! 1
        if lhs.isAppOfArity ``LinuxProcessSemantics.Riscv.Sem.reg_get 2 &&
            (target.find? (· == lhs)).isSome then
          let saved ← saveState
          try
            let g ← getMainGoal
            let r ← g.rewrite target decl.toExpr
            if r.eNew == target then throwError "unchanged"
            replaceMainGoal [← g.replaceTargetEq r.eNew r.eqProof]
            return
          catch _ => saved.restore
  throwError "stepw_addr_hyps: no register equation"

/-- The retry-loop address closer: resolve register updates, repeatedly
rewrite matching Sem.reg_get equations, normalize immediates and addi-zero,
then use the same ordered sp/arithmetic/bitvector closers as Rocq.
A proof-backed literal whose spelling disagrees with its value makes `imm_norm`
fail here; Rocq’s repeat-match leaves it unchanged. -/
elab "stepw_addr_hyps" : tactic => do
  evalTactic (← `(tactic| (getr_resolve; regupd_resolve)))
  repeat
    let saved ← saveState
    try rewriteRegHyp
    catch _ => saved.restore; break
  evalTactic (← `(tactic|
    (imm_norm; repeat rewrite [PropExec.v_addi_0]
     sp_norm
     first | rfl | congr 1 <;> omega | bveq)))

private def storeStep (name : Name) (f d a v : Term) : TacticM Unit := do
  applyStep (← `($(mkIdent name) (a := $a) (v := $v)))
  fetchDecode f d

/-- Store-width dispatch in sd/sw/sh/sb order.
No silent width fallback.
The address/value closers precede the caller's `(oktac)`; sb additionally
sets its byte by reflexivity before store_ok.
Unlike Rocq’s `eq_refl`, ecall closure also accepts a hypothesis after
conversion fails. -/
elab "stepw " f:term:max d:term:max a:term:max v:term:max " (" oktac:tacticSeq ")" : tactic => do
  inChain do
    let (ctor, width) ← decodeShape d
    unless ctor == ``instr.Store do throwError "stepw: expected Store decode"
    let name ← if width == ``msize.SZ8 then pure (seqStepName "sd_at")
      else if width == ``msize.SZ4 then pure (seqStepName "sw_at")
      else if width == ``msize.SZ2 then pure (seqStepName "sh_at")
      else if width == ``msize.SZ1 then
        pure ``LinuxProcessSemantics.Common.MmapSim.step_sb_at
      else throwError "stepw: unsupported store width"
    storeStep name f d a v
    closeFirst (← `(tactic| stepw_addr))
    closeFirst (← `(tactic| stepw_val))
    if width == ``msize.SZ1 then closeFirst (← `(tactic| rfl))
    evalTactic (← `(tactic| ($oktac:tacticSeq)))

/-- Retry-loop sd: `(vtac)` proves the value and `(oktac)` proves store_ok;
address resolution uses `stepw_addr_hyps`.
Unlike Rocq’s `eq_refl`, ecall closure also accepts a hypothesis after
conversion fails. -/
elab "stepsd " f:term:max d:term:max a:term:max v:term:max " (" vtac:tacticSeq ")" " ("
    oktac:tacticSeq ")" : tactic => do
  inChain do
    storeStep (seqStepName "sd_at") f d a v
    closeFirst (← `(tactic| stepw_addr_hyps))
    -- Rocq's bracket applies each script only to its corresponding goal.
    onFirst (evalTactic (← `(tactic| ($vtac:tacticSeq))))
    -- Keep any goals left by vtac before those left by oktac.
    let gs ← getGoals
    let ok := gs.getLast!
    setGoals [ok]
    evalTactic (← `(tactic| ($oktac:tacticSeq)))
    setGoals (gs.dropLast ++ (← getGoals))

/-- Retry-loop ld: fix bs to eight little-endian bytes, replace the read
address using `stepw_addr_hyps`, run `(readtac)`, then bytes_le_to_Z_8.
Unlike Rocq’s `eq_refl`, ecall closure also accepts a hypothesis after
conversion fails.
The address proof is `ad = aexp`; Rocq’s `replace` proves `aexp = ad`. Lean
searches for `rdn` anywhere in the goal; Rocq requires a goal headed by `rdn … =
…`. -/
elab "stepld " f:term:max d:term:max a:term:max v:term:max " (" readtac:tacticSeq ")" : tactic => do
  inChain do
    applyStep (← `(PropExec.step_ld (bs := word_to_le_bytes 8 $v) (v := $v)))
    fetchDecode f d
    onFirst do
      withMainContext do
        let g ← getMainGoal
        let t ← instantiateMVars (← g.getType)
        let some rd := t.find? (·.isAppOfArity ``rdn 4)
          | throwError "stepld: expected rdn obligation"
        let addr ← elabTerm a (some (← inferType (rd.getArg! 2)))
        let eqTy ← mkEq (rd.getArg! 2) addr
        let proof ← Term.elabTerm (← `(by stepw_addr_hyps)) (some eqTy)
        Term.synthesizeSyntheticMVarsNoPostponing
        let r ← g.rewrite t (← instantiateMVars proof)
        replaceMainGoal [← g.replaceTargetEq r.eNew r.eqProof]
      evalTactic (← `(tactic| ($readtac:tacticSeq)))
    let gs ← getGoals
    setGoals [gs.getLast!]
    closeFirst (← `(tactic| exact bytes_le_to_Z_8 _))
    setGoals gs.dropLast

end LinuxProcessSemantics.Common.StepTac

namespace LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.DecodeC
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.CatExec

section DispatchTests
variable (segs : List MemImageType.Segment) (regs : bvmap 5 word)
  (mem rom : word → Option byte) (w : BitVec 32)

example (pc : word) (rd rs : reg) (imm : BitVec 12)
    (hf : fetch_word segs pc = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.OpImm .ALU_ADD rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk
      (mkst (if bv_eqb rd 0 then regs else
        regupd regs rd (v_addi (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom) := by
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.OpImm .ALU_ADD 10 11 1, 4)) :
    msteps segs (mkst regs 0x10000 mem rom)
      (mkst (regupd regs 10 (v_addi (getr regs 11) (bv_signed (1 : BitVec 12))))
      0x10004 mem rom) := by
  stepi (id hf) (id hd)
  guard_target =ₛ msteps segs
    (mkst (regupd regs 10 (v_addi (getr regs 11) (bv_signed (1 : BitVec 12))))
      0x10004 mem rom)
      (mkst (regupd regs 10 (v_addi (getr regs 11) (bv_signed (1 : BitVec 12))))
      0x10004 mem rom)
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.OpImm .ALU_ADD 10 11 1, 4)) :
    msteps segs (mkst regs 0x10000 mem rom)
      (mkst (regupd regs 10 (v_addi (getr regs 11) 1)) 0x10004 mem rom) := by
  stepiv hf hd (v_addi (getr regs 11) 1) (rfl)
  guard_target =ₛ msteps segs
    (mkst (regupd regs 10 (v_addi (getr regs 11) 1)) 0x10004 mem rom)
      (mkst (regupd regs 10 (v_addi (getr regs 11) 1)) 0x10004 mem rom)
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.OpImm32 10 11 1, 4)) :
    msteps segs (mkst regs 0x10000 mem rom)
      (mkst (regupd regs 10 (v_addiw (getr regs 11) 1)) 0x10004 mem rom) := by
  stepiwv hf hd (v_addiw (getr regs 11) 1) (rfl)
  guard_target =ₛ msteps segs
    (mkst (regupd regs 10 (v_addiw (getr regs 11) 1)) 0x10004 mem rom)
      (mkst (regupd regs 10 (v_addiw (getr regs 11) 1)) 0x10004 mem rom)
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.OpImm .ALU_ADD 10 0 1, 4)) :
    msteps segs (mkst regs 0x10000 mem rom)
      (mkst (regupd regs 10 1) 0x10004 mem rom) := by
  stepi_at hf hd (1 : word)
  guard_target =ₛ msteps segs (mkst (regupd regs 10 1) 0x10004 mem rom)
      (mkst (regupd regs 10 1) 0x10004 mem rom)
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Jal 0 8, 4)) :
    msteps segs (mkst regs 0x10000 mem rom)
      (mkst regs 0x10008 mem rom) := by
  stepj hf hd
  guard_target =ₛ msteps segs (mkst regs 0x10008 mem rom)
      (mkst regs 0x10008 mem rom)
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Jalr 0 1 0, 4)) (hr : getr regs 1 = (0x20000 : word)) :
    msteps segs (mkst regs 0x10000 mem rom)
      (mkst regs 0x20000 mem rom) := by
  stepjr hf hd (0x20000 : word) (exact hr)
  guard_target =ₛ msteps segs (mkst regs 0x20000 mem rom)
      (mkst regs 0x20000 mem rom)
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Store .SZ8 2 10 0, 4))
    (hok : RiscvSemantics.store_ok segs mem (v_addi (getr regs 2) 0) 8 = true) :
    msteps segs (mkst regs 0x10000 mem rom)
      (mkst regs 0x10004 (wbytes mem (v_addi (getr regs 2) 0)
      (word_to_le_bytes 8 (getr regs 10))) rom) := by
  stepw hf hd (v_addi (getr regs 2) 0) (getr regs 10) (exact hok)
  guard_target =ₛ msteps segs
    (mkst regs 0x10004 (wbytes mem (v_addi (getr regs 2) 0)
      (word_to_le_bytes 8 (getr regs 10))) rom) (mkst regs 0x10004 (wbytes mem (v_addi (getr regs 2) 0)
      (word_to_le_bytes 8 (getr regs 10))) rom)
  exact msteps.mst_refl _

example (a v : word) (hf : fetch_word segs (0x10000 : word) = some w)
    (he : is_ecall w = false) (hd : decode_any w = some (.Store .SZ8 2 10 0, 4))
    (hr : reg_get regs 2 = a) (hv : getr regs 10 = v)
    (hok : RiscvSemantics.store_ok segs mem a 8 = true) :
    msteps segs (mkst regs 0x10000 mem rom)
      (mkst regs 0x10004 (wbytes mem a (word_to_le_bytes 8 v)) rom) := by
  stepsd hf hd a v (exact hv) (exact hok)
  guard_target =ₛ msteps segs (mkst regs 0x10004 (wbytes mem a (word_to_le_bytes 8 v)) rom) (mkst regs 0x10004 (wbytes mem a (word_to_le_bytes 8 v)) rom)
  exact msteps.mst_refl _

example (a v : word) (hf : fetch_word segs (0x10000 : word) = some w)
    (he : is_ecall w = false) (hd : decode_any w = some (.Load .SZ8 true 10 2 0, 4))
    (hr : reg_get regs 2 = a) (hread : rdn segs mem a 8 = some (word_to_le_bytes 8 v)) :
    msteps segs (mkst regs 0x10000 mem rom)
      (mkst (regupd regs 10 v) 0x10004 mem rom) := by
  stepld hf hd a v (exact hread)
  guard_target =ₛ msteps segs (mkst (regupd regs 10 v) 0x10004 mem rom)
      (mkst (regupd regs 10 v) 0x10004 mem rom)
  exact msteps.mst_refl _

-- A divisor proof that assumption/omega cannot consume must stay BEFORE
-- the independently normalized continuation, as in the Rocq dispatch arm.
example (hf : fetch_word segs (0x10000 : word) = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.Mul .M_DIVU 10 10 11, 4))
    (hnz : True → bv_unsigned (getr regs 11) ≠ 0) :
    msteps segs (mkst regs 0x10000 mem rom)
      (mkst (regupd regs 10 (v_divu (getr regs 10) (getr regs 11))) 0x10004 mem rom) := by
  stepi hf hd
  · guard_target =ₛ bv_unsigned (getr regs 11) ≠ 0
    exact hnz True.intro
  · guard_target =ₛ msteps segs
      (mkst (regupd regs 10 (v_divu (getr regs 10) (getr regs 11))) 0x10004 mem rom)
      (mkst (regupd regs 10 (v_divu (getr regs 10) (getr regs 11))) 0x10004 mem rom)
    exact msteps.mst_refl _

-- A user tactic may leave its value proof open without sending step_simpl
-- to that proof instead of the continuation.
example (hf : fetch_word segs (0x10000 : word) = some w) (he : is_ecall w = false)
    (hd : decode_any w = some (.OpImm .ALU_ADD 10 11 1, 4)) :
    msteps segs (mkst regs 0x10000 mem rom)
      (mkst (regupd regs 10 (v_addi (getr regs 11) 1)) 0x10004 mem rom) := by
  stepiv hf hd (v_addi (getr regs 11) 1) (skip)
  · guard_target = v_addi (getr regs 11) (bv_signed (1 : BitVec 12)) =
      v_addi (getr regs 11) 1
    rfl
  · guard_target =ₛ msteps segs
      (mkst (regupd regs 10 (v_addi (getr regs 11) 1)) 0x10004 mem rom)
      (mkst (regupd regs 10 (v_addi (getr regs 11) 1)) 0x10004 mem rom)
    exact msteps.mst_refl _

-- Each dispatcher must reject a mismatching decode on a real chain goal.
-- Reflexive closure afterwards also checks failure restored the chain state.
example (hf : fetch_word segs (0x10000 : word) = some w)
    (he : is_ecall w = false)
    (hd : decode_any w = some (.FenceI 0 0 0, 4)) :
    msteps segs (mkst regs 0x10000 mem rom)
      (mkst regs 0x10000 mem rom) := by
  have _ := hf
  have _ := he
  have _ := hd
  fail_if_success stepi hf hd
  fail_if_success stepiv hf hd (0 : word) (rfl)
  fail_if_success stepiwv hf hd (0 : word) (rfl)
  fail_if_success stepi_at hf hd (0 : word)
  fail_if_success stepj hf hd
  fail_if_success stepjr hf hd (0 : word) (rfl)
  fail_if_success stepw hf hd (0 : word) (0 : word) (rfl)
  fail_if_success stepsd hf hd (0 : word) (0 : word) (rfl) (rfl)
  fail_if_success stepld hf hd (0 : word) (0 : word) (rfl)
  exact msteps.mst_refl _

-- Fix the successor to an actual ADDI result so the search reaches the
-- supplied decode, rather than rejecting an opaque successor before it.
example (pc : word) (hf : fetch_word segs pc = some w)
    (he : is_ecall w = false)
    (hd : decode_any w = some (.OpImm .ALU_ADD 10 11 1, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk
      (mkst (regupd regs 10 (v_addi (getr regs 11) 1)) (v_addi pc 4) mem rom) := by
  have bad : decode_any (0x0000100f : BitVec 32) = some (.FenceI 0 0 0, 4) := by
    vm_refl_bv
  have _ := bad
  fail_if_success stepi_search hf bad
  stepi_search hf hd

example (x : word) : v_addi (getr (regupd regs 2 x) 2) 0 = v_addi x 0 := by
  stepw_addr
example (x : word) : (fun y : word => y) (getr (regupd regs 10 x) 10) = x := by
  stepw_val
example (x : word) (hr : reg_get regs 2 = x) : v_addi (getr regs 2) 0 = x := by
  stepw_addr_hyps
example (x y : word) (h : True → x = y) : x = y := by
  fail_if_success stepw_addr
  fail_if_success stepw_val
  fail_if_success stepw_addr_hyps
  exact h True.intro
-- cbv beta must revisit a redex introduced inside the pair, while leaving
-- an abstract function application alone. Pin the intermediate stage used
-- by stepw_val before its final conversion closer can hide the difference.
example (x y : word) (f : word → word) (h : x = y) :
    ((fun k : word → word => (k x, f x)) (fun z => z)) = (y, f x) := by
  run_tac betaGoal
  guard_target =ₛ (x, f x) = (y, f x)
  fail_if_success guard_target =ₛ (((fun z : word => z) x), f x) = (y, f x)
  exact congrArg (fun z => (z, f x)) h

example (a v : word) (hf : fetch_word segs (0x10000 : word) = some w)
    (he : is_ecall w = false) (hd : decode_any w = some (.Store .SZ8 2 10 0, 4))
    (hr : reg_get regs 2 = a) (hv : getr regs 10 = v)
    (hok : RiscvSemantics.store_ok segs mem a 8 = true) :
    msteps segs (mkst regs 0x10000 mem rom)
      (mkst regs 0x10004 (wbytes mem a (word_to_le_bytes 8 v)) rom) := by
  stepsd hf hd a v (skip) (skip)
  · guard_target =ₛ getr regs 10 = v
    exact hv
  · guard_target =ₛ RiscvSemantics.store_ok segs mem a 8 = true
    exact hok
  · guard_target =ₛ msteps segs (mkst regs 0x10004 (wbytes mem a (word_to_le_bytes 8 v)) rom)
      (mkst regs 0x10004 (wbytes mem a (word_to_le_bytes 8 v)) rom)
    exact msteps.mst_refl _

end DispatchTests

end LinuxProcessSemantics.Common.StepTac

namespace LinuxProcessSemantics.Common.StepTac
open Lean Elab Tactic
open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.DecodeC
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.CatExec

/-- DispatchSmoke's scaffold: introduce fetch, prove the concrete decode by
kernel decision, create the final-state metavariable, stepi, then mst_refl.
The Lean decoder covers all these integer encodings, so no generated Rocq
decode table is needed. `smoke enc sh` takes two terms. -/
elab "smoke " enc:term:max sh:term:max : tactic => do
  evalTactic (← `(tactic|
    (intro hf
     have hd : decode_any $enc = some ($sh, 4) := by vm_refl_bv
     refine ⟨?_, ?_⟩
     rotate_left
     stepi hf hd
     exact msteps.mst_refl _)))

section DispatchSmoke
variable (segs : List MemImageType.Segment) (regs : bvmap 5 word)
  (mem rom : word → Option byte)

-- OpImm ALU_SLT 10 10 1
example : fetch_word segs (0x10000 : word) = some (0x00152513 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x00152513 : BitVec 32) (.OpImm .ALU_SLT 10 10 1)

-- ShiftImm ALU_SRA 10 10 1
example : fetch_word segs (0x10000 : word) = some (0x40155513 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x40155513 : BitVec 32) (.ShiftImm .ALU_SRA 10 10 1)

-- Op ALU_AND 10 10 11
example : fetch_word segs (0x10000 : word) = some (0x00B57533 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x00B57533 : BitVec 32) (.Op .ALU_AND 10 10 11)

-- Op ALU_OR 10 10 11
example : fetch_word segs (0x10000 : word) = some (0x00B56533 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x00B56533 : BitVec 32) (.Op .ALU_OR 10 10 11)

-- Op ALU_XOR 10 10 11
example : fetch_word segs (0x10000 : word) = some (0x00B54533 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x00B54533 : BitVec 32) (.Op .ALU_XOR 10 10 11)

-- Op ALU_SLL 10 10 11
example : fetch_word segs (0x10000 : word) = some (0x00B51533 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x00B51533 : BitVec 32) (.Op .ALU_SLL 10 10 11)

-- Op ALU_SRL 10 10 11
example : fetch_word segs (0x10000 : word) = some (0x00B55533 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x00B55533 : BitVec 32) (.Op .ALU_SRL 10 10 11)

-- Op ALU_SRA 10 10 11
example : fetch_word segs (0x10000 : word) = some (0x40B55533 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x40B55533 : BitVec 32) (.Op .ALU_SRA 10 10 11)

-- Op ALU_SLT 10 10 11
example : fetch_word segs (0x10000 : word) = some (0x00B52533 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x00B52533 : BitVec 32) (.Op .ALU_SLT 10 10 11)

-- Op ALU_SLTU 10 10 11
example : fetch_word segs (0x10000 : word) = some (0x00B53533 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x00B53533 : BitVec 32) (.Op .ALU_SLTU 10 10 11)

-- Op32 ALU_ADD 10 10 11
example : fetch_word segs (0x10000 : word) = some (0x00B5053B : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x00B5053B : BitVec 32) (.Op32 .ALU_ADD 10 10 11)

-- Op32 ALU_SLL 10 10 11
example : fetch_word segs (0x10000 : word) = some (0x00B5153B : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x00B5153B : BitVec 32) (.Op32 .ALU_SLL 10 10 11)

-- Op32 ALU_SRL 10 10 11
example : fetch_word segs (0x10000 : word) = some (0x00B5553B : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x00B5553B : BitVec 32) (.Op32 .ALU_SRL 10 10 11)

-- Op32 ALU_SRA 10 10 11
example : fetch_word segs (0x10000 : word) = some (0x40B5553B : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x40B5553B : BitVec 32) (.Op32 .ALU_SRA 10 10 11)

-- OpImm32 10 10 1
example : fetch_word segs (0x10000 : word) = some (0x0015051B : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x0015051B : BitVec 32) (.OpImm32 10 10 1)

-- ShiftImm32 ALU_SLL 10 10 1
example : fetch_word segs (0x10000 : word) = some (0x0015151B : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x0015151B : BitVec 32) (.ShiftImm32 .ALU_SLL 10 10 1)

-- ShiftImm32 ALU_SRL 10 10 1
example : fetch_word segs (0x10000 : word) = some (0x0015551B : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x0015551B : BitVec 32) (.ShiftImm32 .ALU_SRL 10 10 1)

-- ShiftImm32 ALU_SRA 10 10 1
example : fetch_word segs (0x10000 : word) = some (0x4015551B : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x4015551B : BitVec 32) (.ShiftImm32 .ALU_SRA 10 10 1)

-- Mul M_MULH 10 10 11
example : fetch_word segs (0x10000 : word) = some (0x02B51533 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x02B51533 : BitVec 32) (.Mul .M_MULH 10 10 11)

-- Mul M_MULHSU 10 10 11
example : fetch_word segs (0x10000 : word) = some (0x02B52533 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x02B52533 : BitVec 32) (.Mul .M_MULHSU 10 10 11)

-- Mul M_MULHU 10 10 11
example : fetch_word segs (0x10000 : word) = some (0x02B53533 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x02B53533 : BitVec 32) (.Mul .M_MULHU 10 10 11)

-- Mul M_DIV 10 10 11
example : fetch_word segs (0x10000 : word) = some (0x02B54533 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x02B54533 : BitVec 32) (.Mul .M_DIV 10 10 11)

-- Mul M_REM 10 10 11
example : fetch_word segs (0x10000 : word) = some (0x02B56533 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x02B56533 : BitVec 32) (.Mul .M_REM 10 10 11)

-- Mul32 M_MUL 10 10 11
example : fetch_word segs (0x10000 : word) = some (0x02B5053B : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x02B5053B : BitVec 32) (.Mul32 .M_MUL 10 10 11)

-- Mul32 M_DIV 10 10 11
example : fetch_word segs (0x10000 : word) = some (0x02B5453B : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x02B5453B : BitVec 32) (.Mul32 .M_DIV 10 10 11)

-- Mul32 M_DIVU 10 10 11
example : fetch_word segs (0x10000 : word) = some (0x02B5553B : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x02B5553B : BitVec 32) (.Mul32 .M_DIVU 10 10 11)

-- Mul32 M_REM 10 10 11
example : fetch_word segs (0x10000 : word) = some (0x02B5653B : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x02B5653B : BitVec 32) (.Mul32 .M_REM 10 10 11)

-- Mul32 M_REMU 10 10 11
example : fetch_word segs (0x10000 : word) = some (0x02B5753B : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x02B5753B : BitVec 32) (.Mul32 .M_REMU 10 10 11)

example (hf : fetch_word segs (0x10000 : word) = some (0x02B55533 : BitVec 32))
    (hnz : bv_unsigned (getr regs 11) ≠ 0) :
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  have hd : decode_any (0x02B55533 : BitVec 32) = some (.Mul .M_DIVU 10 10 11, 4) := by
    vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi hf hd
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some (0x02B57533 : BitVec 32))
    (hnz : bv_unsigned (getr regs 11) ≠ 0) :
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  have hd : decode_any (0x02B57533 : BitVec 32) = some (.Mul .M_REMU 10 10 11, 4) := by
    vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi hf hd
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some (0x00151513 : BitVec 32)) :
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  have hd : decode_any (0x00151513 : BitVec 32) = some (.ShiftImm .ALU_SLL 10 10 1, 4) := by
    vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepiv hf hd (v_slli (getr regs 10) 1) (rfl)
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some (0x00157513 : BitVec 32)) :
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  have hd : decode_any (0x00157513 : BitVec 32) = some (.OpImm .ALU_AND 10 10 1, 4) := by
    vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepiv hf hd (v_andi (getr regs 10) 1) (rfl)
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some (0x00A13023 : BitVec 32))
    (hok : RiscvSemantics.store_ok segs mem (v_addi (getr regs 2) 0) 8 = true) :
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  have hd : decode_any (0x00A13023 : BitVec 32) = some (.Store .SZ8 2 10 0, 4) := by
    vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepw hf hd (v_addi (getr regs 2) 0) (getr regs 10) (exact hok)
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some (0x00A12023 : BitVec 32))
    (hok : RiscvSemantics.store_ok segs mem (v_addi (getr regs 2) 0) 4 = true) :
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  have hd : decode_any (0x00A12023 : BitVec 32) = some (.Store .SZ4 2 10 0, 4) := by
    vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepw hf hd (v_addi (getr regs 2) 0) (getr regs 10) (exact hok)
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some (0x00A11023 : BitVec 32))
    (hok : RiscvSemantics.store_ok segs mem (v_addi (getr regs 2) 0) 2 = true) :
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  have hd : decode_any (0x00A11023 : BitVec 32) = some (.Store .SZ2 2 10 0, 4) := by
    vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepw hf hd (v_addi (getr regs 2) 0) (getr regs 10) (exact hok)
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some (0x00A10023 : BitVec 32))
    (hok : RiscvSemantics.store_ok segs mem (v_addi (getr regs 2) 0) 1 = true) :
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  have hd : decode_any (0x00A10023 : BitVec 32) = some (.Store .SZ1 2 10 0, 4) := by
    vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepw hf hd (v_addi (getr regs 2) 0) (getr regs 10) (exact hok)
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some (0x0080006F : BitVec 32)) :
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  have hd : decode_any (0x0080006F : BitVec 32) = some (.Jal 0 8, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepj hf hd
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some (0x008000EF : BitVec 32)) :
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  have hd : decode_any (0x008000EF : BitVec 32) = some (.Jal 1 8, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepj hf hd
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some (0x00008067 : BitVec 32))
    (hr : getr regs 1 = (0x20000 : word)) :
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  have hd : decode_any (0x00008067 : BitVec 32) = some (.Jalr 0 1 0, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepjr hf hd (0x20000 : word) (exact hr)
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some (0x000500E7 : BitVec 32))
    (hr : getr regs 10 = (0x20000 : word)) :
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  have hd : decode_any (0x000500E7 : BitVec 32) = some (.Jalr 1 10 0, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepjr hf hd (0x20000 : word) (exact hr)
  exact msteps.mst_refl _

-- Reject a lying smoke shape even though the reflexive chain is provable.
example : fetch_word segs (0x10000 : word) = some (0x00152513 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  fail_if_success smoke (0x00152513 : BitVec 32) (.OpImm .ALU_ADD 10 10 1)
  intro _
  exact ⟨_, msteps.mst_refl _⟩

-- Direct search coverage, including decodes that stepi dispatches without search.

example (hf : fetch_word segs (0x10000 : word) = some (0x00150513 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x00150513 : BitVec 32) = some (.OpImm .ALU_ADD 10 10 1, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x00b50533 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x00b50533 : BitVec 32) = some (.Op .ALU_ADD 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x40b50533 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x40b50533 : BitVec 32) = some (.Op .ALU_SUB 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x00151513 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x00151513 : BitVec 32) = some (.ShiftImm .ALU_SLL 10 10 1, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x00001517 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x00001517 : BitVec 32) = some (.Auipc 10 1, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x00001537 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x00001537 : BitVec 32) = some (.Lui 10 1, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x0015051b : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x0015051b : BitVec 32) = some (.OpImm32 10 10 1, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x00157513 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x00157513 : BitVec 32) = some (.OpImm .ALU_AND 10 10 1, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x00153513 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x00153513 : BitVec 32) = some (.OpImm .ALU_SLTU 10 10 1, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x00154513 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x00154513 : BitVec 32) = some (.OpImm .ALU_XOR 10 10 1, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x00155513 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x00155513 : BitVec 32) = some (.ShiftImm .ALU_SRL 10 10 1, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x02b50533 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x02b50533 : BitVec 32) = some (.Mul .M_MUL 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x00156513 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x00156513 : BitVec 32) = some (.OpImm .ALU_OR 10 10 1, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x40b5053b : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x40b5053b : BitVec 32) = some (.Op32 .ALU_SUB 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x00152513 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x00152513 : BitVec 32) = some (.OpImm .ALU_SLT 10 10 1, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x40155513 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x40155513 : BitVec 32) = some (.ShiftImm .ALU_SRA 10 10 1, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x00b57533 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x00b57533 : BitVec 32) = some (.Op .ALU_AND 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x00b56533 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x00b56533 : BitVec 32) = some (.Op .ALU_OR 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x00b54533 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x00b54533 : BitVec 32) = some (.Op .ALU_XOR 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x00b51533 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x00b51533 : BitVec 32) = some (.Op .ALU_SLL 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x00b55533 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x00b55533 : BitVec 32) = some (.Op .ALU_SRL 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x40b55533 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x40b55533 : BitVec 32) = some (.Op .ALU_SRA 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x00b52533 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x00b52533 : BitVec 32) = some (.Op .ALU_SLT 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x00b53533 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x00b53533 : BitVec 32) = some (.Op .ALU_SLTU 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x00b5053b : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x00b5053b : BitVec 32) = some (.Op32 .ALU_ADD 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x00b5153b : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x00b5153b : BitVec 32) = some (.Op32 .ALU_SLL 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x00b5553b : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x00b5553b : BitVec 32) = some (.Op32 .ALU_SRL 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x40b5553b : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x40b5553b : BitVec 32) = some (.Op32 .ALU_SRA 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x0015151b : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x0015151b : BitVec 32) = some (.ShiftImm32 .ALU_SLL 10 10 1, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x0015551b : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x0015551b : BitVec 32) = some (.ShiftImm32 .ALU_SRL 10 10 1, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x4015551b : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x4015551b : BitVec 32) = some (.ShiftImm32 .ALU_SRA 10 10 1, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x02b51533 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x02b51533 : BitVec 32) = some (.Mul .M_MULH 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x02b52533 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x02b52533 : BitVec 32) = some (.Mul .M_MULHSU 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x02b53533 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x02b53533 : BitVec 32) = some (.Mul .M_MULHU 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x02b54533 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x02b54533 : BitVec 32) = some (.Mul .M_DIV 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x02b56533 : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x02b56533 : BitVec 32) = some (.Mul .M_REM 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x02b5053b : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x02b5053b : BitVec 32) = some (.Mul32 .M_MUL 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x02b5453b : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x02b5453b : BitVec 32) = some (.Mul32 .M_DIV 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x02b5553b : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x02b5553b : BitVec 32) = some (.Mul32 .M_DIVU 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x02b5653b : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x02b5653b : BitVec 32) = some (.Mul32 .M_REM 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

example (hf : fetch_word segs (0x10000 : word) = some (0x02b5753b : BitVec 32)) :
    ∃ t, RiscvSemantics.step segs (mkst regs 0x10000 mem rom) = MachineOk t := by
  have hd : decode_any (0x02b5753b : BitVec 32) = some (.Mul32 .M_REMU 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepi_search hf hd

-- Dispatch arms absent from Rocq’s original smoke list.

example : fetch_word segs (0x10000 : word) = some (0x00157513 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x00157513 : BitVec 32) (.OpImm .ALU_AND 10 10 1)

example : fetch_word segs (0x10000 : word) = some (0x00156513 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x00156513 : BitVec 32) (.OpImm .ALU_OR 10 10 1)

example : fetch_word segs (0x10000 : word) = some (0x00154513 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x00154513 : BitVec 32) (.OpImm .ALU_XOR 10 10 1)

example : fetch_word segs (0x10000 : word) = some (0x00153513 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x00153513 : BitVec 32) (.OpImm .ALU_SLTU 10 10 1)

example : fetch_word segs (0x10000 : word) = some (0x00b50533 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x00b50533 : BitVec 32) (.Op .ALU_ADD 10 10 11)

example : fetch_word segs (0x10000 : word) = some (0x40b50533 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x40b50533 : BitVec 32) (.Op .ALU_SUB 10 10 11)

example : fetch_word segs (0x10000 : word) = some (0x40b5053b : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x40b5053b : BitVec 32) (.Op32 .ALU_SUB 10 10 11)

example : fetch_word segs (0x10000 : word) = some (0x00151513 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x00151513 : BitVec 32) (.ShiftImm .ALU_SLL 10 10 1)

example : fetch_word segs (0x10000 : word) = some (0x00155513 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x00155513 : BitVec 32) (.ShiftImm .ALU_SRL 10 10 1)

example : fetch_word segs (0x10000 : word) = some (0x00001517 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x00001517 : BitVec 32) (.Auipc 10 1)

example : fetch_word segs (0x10000 : word) = some (0x00001537 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x00001537 : BitVec 32) (.Lui 10 1)

example : fetch_word segs (0x10000 : word) = some (0x02b50533 : BitVec 32) →
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  smoke (0x02b50533 : BitVec 32) (.Mul .M_MUL 10 10 11)

example (hf : fetch_word segs (0x10000 : word) = some (0x00156513 : BitVec 32)) :
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  have hd : decode_any (0x00156513 : BitVec 32) = some (.OpImm .ALU_OR 10 10 1, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepiv hf hd (v_ori (getr regs 10) 1) (rfl)
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some (0x00154513 : BitVec 32)) :
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  have hd : decode_any (0x00154513 : BitVec 32) = some (.OpImm .ALU_XOR 10 10 1, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepiv hf hd (v_xori (getr regs 10) 1) (rfl)
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some (0x00153513 : BitVec 32)) :
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  have hd : decode_any (0x00153513 : BitVec 32) = some (.OpImm .ALU_SLTU 10 10 1, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepiv hf hd (v_sltiu (getr regs 10) 1) (rfl)
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some (0x00155513 : BitVec 32)) :
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  have hd : decode_any (0x00155513 : BitVec 32) = some (.ShiftImm .ALU_SRL 10 10 1, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepiv hf hd (v_srli (getr regs 10) 1) (rfl)
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some (0x40155513 : BitVec 32)) :
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  have hd : decode_any (0x40155513 : BitVec 32) = some (.ShiftImm .ALU_SRA 10 10 1, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepiv hf hd (v_srai (getr regs 10) 1) (rfl)
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some (0x00b50533 : BitVec 32)) :
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  have hd : decode_any (0x00b50533 : BitVec 32) = some (.Op .ALU_ADD 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepiv hf hd (v_add (getr regs 10) (getr regs 11)) (rfl)
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some (0x40b50533 : BitVec 32)) :
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  have hd : decode_any (0x40b50533 : BitVec 32) = some (.Op .ALU_SUB 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepiv hf hd (v_sub (getr regs 10) (getr regs 11)) (rfl)
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some (0x0015051b : BitVec 32)) :
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  have hd : decode_any (0x0015051b : BitVec 32) = some (.OpImm32 10 10 1, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepiv hf hd (v_addiw (getr regs 10) 1) (rfl)
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some (0x02b50533 : BitVec 32)) :
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  have hd : decode_any (0x02b50533 : BitVec 32) = some (.Mul .M_MUL 10 10 11, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepiv hf hd (v_mul (getr regs 10) (getr regs 11)) (rfl)
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some (0x00001537 : BitVec 32)) :
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  have hd : decode_any (0x00001537 : BitVec 32) = some (.Lui 10 1, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepiv hf hd (v_lui (Z_shiftl (bv_signed (1 : BitVec 20)) 12)) (rfl)
  exact msteps.mst_refl _

example (hf : fetch_word segs (0x10000 : word) = some (0x00001517 : BitVec 32)) :
    ∃ t, msteps segs (mkst regs 0x10000 mem rom) t := by
  have hd : decode_any (0x00001517 : BitVec 32) = some (.Auipc 10 1, 4) := by vm_refl_bv
  refine ⟨?_, ?_⟩
  rotate_left
  stepiv hf hd (v_auipc (0x10000 : word) (Z_shiftl (bv_signed (1 : BitVec 20)) 12)) (rfl)
  exact msteps.mst_refl _

end DispatchSmoke

-- New keywords must remain legal term identifiers, including smoke.
example (stepi_search stepi stepiv stepiwv stepj stepjr stepi_at
    stepw_addr stepw_val stepw_addr_hyps stepw stepsd stepld smoke : Nat)
    (h : stepi_search + stepi + stepiv + stepiwv + stepj + stepjr + stepi_at +
      stepw_addr + stepw_val + stepw_addr_hyps + stepw + stepsd + stepld + smoke = 0) :
    True := by
  have _ := h
  exact True.intro

end LinuxProcessSemantics.Common.StepTac

namespace LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.CatSim

-- Rocq's `match goal with H : reg_get ?R ?r = _` tries the most recent
-- hypothesis first; with two equations for one register, Rocq rewrites by h2
-- (checked under coqc), so only the newest equation closes this goal.
example (regs : bvmap 5 word) (a b : word) (_h1 : reg_get regs 2 = a) (h2 : reg_get regs 2 = b) :
    v_addi (getr regs 2) 0 = b := by
  stepw_addr_hyps

-- Rocq's rdn_ext_lit names the introduced point `x` and bound `Hx`, so a
-- script can use them.
example (segs : List MemImageType.Segment) (m1 m2 : word → Option byte)
    (bs : List byte) (hr : rdn segs m2 (Z_to_bv 64 8) 2 = some bs)
    (he : ∀ x : word, 8 ≤ bv_unsigned x ∧ bv_unsigned x < 10 → m1 x = m2 x) :
    rdn segs m1 (Z_to_bv 64 8) 2 = some bs := by
  rdn_ext_lit
  · exact hr
  · exact he x (by omega)

-- With bufs = [], to_wallexit unfolds to to_wexit, so the second alternative
-- (tw_step) applies before twe_step, as in Rocq's order.
example (segs : List MemImageType.Segment) (fd : word) (s t : machine_state) (code : word)
    (hp : s.ms_svc_pending = none) (hs : step segs s = MachineOk t)
    (hw : WallSim.to_wallexit segs fd [] code t) :
    WallSim.to_wallexit segs fd [] code s := by
  chain_step
  · exact hp
  · exact hs
  · guard_target =ₛ to_wexit segs t [] code
    exact hw

-- An argument that does not elaborate fails, as Rocq's argument
-- interpretation does, before any rollback.
example : True := by
  fail_if_success wlit (no_such_identifier_here)
  fail_if_success norm_pc_state (no_such_identifier_here)
  exact True.intro
end LinuxProcessSemantics.Common.StepTac

namespace LinuxProcessSemantics.Common.StepTac
open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.CatSim
section NormPcRows
variable (segs : List MemImageType.Segment) (r : bvmap 5 word)
  (m rom : word → Option byte) (model : State.Model) (code fd cnt : word)
  (bufs : List (List byte)) (bs : List byte) (k : RiscvSemantics.machine_state → Prop)
  (t : RiscvSemantics.machine_state) (f : Nat → byte → Option Nat) (out : Nat → List byte)
  (lh : Nat → RiscvSemantics.machine_state → Prop) (a : Nat)

example (h : to_wexit segs (mkst r (8 : word) m rom) bufs code) :
    to_wexit segs (mkst r (v_addi (5 : word) 3) m rom) bufs code := by
  norm_pc
  guard_target =ₛ to_wexit segs (mkst r (8 : word) m rom) bufs code
  exact h

example (h : MmapSim.twm segs (mkst r (8 : word) m rom) model bufs code) :
    MmapSim.twm segs (mkst r (v_addi (5 : word) 3) m rom) model bufs code := by
  norm_pc
  guard_target =ₛ MmapSim.twm segs (mkst r (8 : word) m rom) model bufs code
  exact h

example (h : MmapSim.twm_pend segs (mkst r (8 : word) m rom) model bs bufs code) :
    MmapSim.twm_pend segs (mkst r (v_addi (5 : word) 3) m rom) model bs bufs code := by
  norm_pc
  guard_target =ₛ MmapSim.twm_pend segs (mkst r (8 : word) m rom) model bs bufs code
  exact h

example (h : MmapSim.twm_tail segs (mkst r (8 : word) m rom) model bs bufs code) :
    MmapSim.twm_tail segs (mkst r (v_addi (5 : word) 3) m rom) model bs bufs code := by
  norm_pc
  guard_target =ₛ MmapSim.twm_tail segs (mkst r (8 : word) m rom) model bs bufs code
  exact h

example (h : MmapSim.tmw segs (mkst r (8 : word) m rom) model bufs code bufs code) :
    MmapSim.tmw segs (mkst r (v_addi (5 : word) 3) m rom) model bufs code bufs code := by
  norm_pc
  guard_target =ₛ MmapSim.tmw segs (mkst r (8 : word) m rom) model bufs code bufs code
  exact h

example (h : StreamSim.to_wr segs k bs (mkst r (8 : word) m rom)) :
    StreamSim.to_wr segs k bs (mkst r (v_addi (5 : word) 3) m rom) := by
  norm_pc
  guard_target =ₛ StreamSim.to_wr segs k bs (mkst r (8 : word) m rom)
  exact h

example (h : StreamSim.to_rd segs k cnt (mkst r (8 : word) m rom)) :
    StreamSim.to_rd segs k cnt (mkst r (v_addi (5 : word) 3) m rom) := by
  norm_pc
  guard_target =ₛ StreamSim.to_rd segs k cnt (mkst r (8 : word) m rom)
  exact h

example (h : WallSim.to_wall segs fd (mkst r (8 : word) m rom) bs k) :
    WallSim.to_wall segs fd (mkst r (v_addi (5 : word) 3) m rom) bs k := by
  norm_pc
  guard_target =ₛ WallSim.to_wall segs fd (mkst r (8 : word) m rom) bs k
  exact h

example (h : WallSim.to_wall_tail segs fd (mkst r (8 : word) m rom) bs k) :
    WallSim.to_wall_tail segs fd (mkst r (v_addi (5 : word) 3) m rom) bs k := by
  norm_pc
  guard_target =ₛ WallSim.to_wall_tail segs fd (mkst r (8 : word) m rom) bs k
  exact h

example (h : WallSim.to_wallexit segs fd bufs code (mkst r (8 : word) m rom)) :
    WallSim.to_wallexit segs fd bufs code (mkst r (v_addi (5 : word) 3) m rom) := by
  norm_pc
  guard_target =ₛ WallSim.to_wallexit segs fd bufs code (mkst r (8 : word) m rom)
  exact h

example (h : DrainSim.to_out segs bs (mkst r (8 : word) m rom)) :
    DrainSim.to_out segs bs (mkst r (v_addi (5 : word) 3) m rom) := by
  norm_pc
  guard_target =ₛ DrainSim.to_out segs bs (mkst r (8 : word) m rom)
  exact h

example (h : DrainSim.to_rd segs cnt f out code lh a (mkst r (8 : word) m rom)) :
    DrainSim.to_rd segs cnt f out code lh a (mkst r (v_addi (5 : word) 3) m rom) := by
  norm_pc
  guard_target =ₛ DrainSim.to_rd segs cnt f out code lh a (mkst r (8 : word) m rom)
  exact h
end NormPcRows
end LinuxProcessSemantics.Common.StepTac
