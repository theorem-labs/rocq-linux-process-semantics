import LinuxProcessSemantics.Common.ImageBytes
import LinuxProcessSemantics.Common.StepTac
import LinuxProcessSemantics.Common.SymExec
import LinuxProcessSemantics.Common.ExitSim
import LinuxProcessSemantics.Common.StreamSim
import LinuxProcessSemantics.Common.SymSide
import LinuxProcessSemantics.Common.ShapeAlg
import LinuxProcessSemantics.Common.WallSim
import LinuxProcessSemantics.Common.DrainSim
import LinuxProcessSemantics.Common.MmapSim

/-!
# Common.SymTac — symbolic block normalization and chain attachment

Ports the lemma layer and the normalization, register-reading and chain tactics
of `theories/Common/SymTac.v` (baseline
`2cde689f94c086b868999970834b76a25616b94a`, with the later `realizes` arm).
`chain_mst` leaves the machine-step premise before the advanced chain premise.
Closed symbolic register syntax is reduced separately from its valuation.

The block wrappers `sym_block`, `sym_block_ex`, `sym_chain` and their PC
helpers `sym_pc_Z`, `sym_pc_lit` are ported. The executor is reduced only
on closed symbolic syntax; its equation is checked by the kernel.

Representation spellings: `Forall P l` is `∀ p ∈ l, P p`, `fst`/`snd`
are `.1`/`.2`, and `StreamSim`'s section parameters are explicit.
`sext`, `low32`, `alu32`, `v_lw` and `v_addiw` retain their Rocq names.
The tactic layer uses `sym_u_norm`, `sym_imm_norm`, `sym_f_equal`, and
`vm_closed` for the corresponding Rocq helpers. There is no `model` simp
set; the model closers use the named `MmapSim` rules instead.
-/

namespace LinuxProcessSemantics.Common.SymTac

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr hiding msize_bytes
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.CatExec
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Common.SymExec

/-! ## 1. Pinning entry registers -/

/-- Apply a list of `(register, expr)` pins to a symbolic register file.
Left to right, so a later pin of the same register wins. -/
def sr_pins (ps : List (reg × expr)) (sr : List expr) : List expr :=
  match ps with
  | [] => sr
  | (r, e) :: rest => sr_pins rest (sr_upd sr (ridx r) e)

/-- The caller's side of a pin list: each pinned register really does hold
the value its `expr` denotes. -/
def pins_ok (E : env) (regs : bvmap 5 word) (ps : List (reg × expr)) : Prop :=
  ∀ p ∈ ps, getr regs p.1 = edenot E p.2

theorem regs_ok_pins (E : env) (ps : List (reg × expr)) (sr : List expr)
    (regs : bvmap 5 word) (hr : regs_ok E sr regs) (hp : pins_ok E regs ps) :
    regs_ok E (sr_pins ps sr) regs := by
  induction ps generalizing sr with
  | nil => exact hr
  | cons p rest ih =>
    obtain ⟨r, e⟩ := p
    exact ih (sr_upd sr (ridx r) e)
      (regs_ok_pin E sr regs r e hr (hp (r, e) (List.mem_cons.2 (Or.inl rfl))))
      (fun q hq => hp q (List.mem_cons.2 (Or.inr hq)))

/-! ## 2. Value normalization for the post-state reader -/

/-- A `mv rd,rs` is `addi rd,rs,0`; the smart constructor cannot fold it (the
base is symbolic), so EVERY register copy in a compiled prologue denotes as
`alu64 ADD x 0`.  One lemma collapses all of them, which is why a shuffled
argument register reads back without a per-instruction script. -/
theorem alu64_add_0 (x : word) : alu64 .ALU_ADD x (Z_to_bv 64 0) = x := by
  rw [alu_add]
  unfold v_add
  rw [u_Z_to_bv64_0]
  exact v_addi_0 x

theorem aluw_add_0 (x : word) :
    sext 64 (alu32 .ALU_ADD (low32 x) (low32 (Z_to_bv 64 0))) = v_lw x := by
  rw [low32_lit, alu32_add_0]
  exact b_lw_val x

theorem aluw_addi_lit (a : word) (k : Int) :
    sext 64 (alu32 .ALU_ADD (low32 a) (low32 (Z_to_bv 64 k))) = v_addiw a k := by
  rw [low32_lit]
  change Z_to_bv 64 (bv_signed (low32 a + Z_to_bv 32 k)) = _
  unfold v_addiw
  congr 1
  rw [bv_signed_swrap]
  unfold bv_swrap bv_wrap bv_half_modulus bv_modulus bv_unsigned low32 bv_extract Z_to_bv
  rw [BitVec.toNat_add, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_ofInt]
  omega

theorem bdenot_var (E : env) (n : Nat) : bdenot E (SBVar n) = E n := rfl

theorem bdenot_lit (E : env) : bdenot E SBLit = Z_to_bv 64 0 := rfl

theorem edenot_lit (E : env) (z : Int) : edenot E (ELit z) = Z_to_bv 64 z := rfl

theorem edenot_var (E : env) (n : Nat) : edenot E (EVar n) = E n := rfl

/-- `v_addi` IS `Z_to_bv 64 (bv_unsigned x + i)` definitionally; as a rewrite
rule with the displacement a VARIABLE it normalizes any offset, where Rocq's
`StepTac.sp_norm` Ltac (unported) only knows the negative constants it has
named lemmas for.
A reflectively executed block produces whatever displacement the compiler
chose. -/
theorem v_addi_Z (x : word) (i : Int) : v_addi x i = Z_to_bv 64 (bv_unsigned x + i) := rfl

theorem adenot_var (E : env) (n : Nat) (k : Int) :
    adenot E (SA (SBVar n) k) = Z_to_bv 64 (bv_unsigned (E n) + k) := rfl

theorem adenot_lit (E : env) (k : Int) : adenot E (SA SBLit k) = Z_to_bv 64 k := by
  change Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0) + k) = _
  rw [u_Z_to_bv64_0, Int.zero_add]

/-- Reduce the valuation's list and index plumbing, keeping word operations folded. -/
macro "sym_env_cbn" : tactic => `(tactic|
  try simp only [Eplus, Nat.blt, Nat.ble, Nat.reduceSub, Nat.reduceAdd,
    Nat.reduceLT, Bool.false_eq_true,
    ite_true, ite_false, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
    List.append_nil, List.cons_append, List.nil_append, Prod.fst, Prod.snd,
    saddr.a_base, saddr.a_off, sentry.e_addr, sentry.e_width, sentry.e_val])

section
open Lean Meta Elab Tactic

private def intLit? (e : Expr) : Option Int :=
  if let some n := e.nat? then some (Int.ofNat n)
  else if e.isAppOfArity ``Neg.neg 3 then
    e.appArg!.nat?.map (fun n => -(Int.ofNat n))
  else if e.isAppOfArity ``Int.ofNat 1 then e.appArg!.rawNatLit?.map Int.ofNat
  else if e.isAppOfArity ``Int.negSucc 1 then e.appArg!.rawNatLit?.map Int.negSucc
  else none

private def intSyntax (z : Int) : TacticM (TSyntax `term) :=
  if z ≥ 0 then pure (Syntax.mkNumLit (toString z.toNat))
  else do `(term| - $(Syntax.mkNumLit (toString (-z).toNat)))

/-- The syntactic literal guard used by `sym_z_norm`. -/
elab "sym_z_lit " k:term : tactic => withMainContext do
  let e ← elabTerm k (some (mkConst ``Int))
  unless (intLit? e).isSome do throwError "sym_z_lit: expected an integer literal"

private def closed (e : Expr) : Bool := !e.hasFVar && !e.hasMVar && !e.hasLooseBVars

/-- Convert only selected closed subterms, with the kernel checking conversion. -/
private def convertClosed (f : Expr → MetaM (Option Expr)) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let t' ← Meta.transform t (post := fun e => do
    if let some v ← f e then
      unless ← isDefEq e v do throwError "sym normalization: conversion failed"
      return .done v
    return .continue)
  if t != t' then replaceMainGoal [← g.replaceTargetDefEq t']

private def wordLiteral (e : Expr) (positiveOnly : Bool) : MetaM (Option Expr) := do
  if e.isAppOfArity ``Z_to_bv 2 && closed e then
    let zexpr ← if positiveOnly then pure e.appArg! else reduce e.appArg!
    if let some z := intLit? zexpr then
      if positiveOnly && z ≤ 0 then return none
      if let some n := e.appFn!.appArg!.nat? <|> e.appFn!.appArg!.rawNatLit? then
        return some (← mkNumeral (mkApp (mkConst ``BitVec) (mkNatLit n))
          (z % (2 ^ n : Int)).toNat)
  return none

elab "sym_env_norm" : tactic => focus do
  evalTactic (← `(tactic| (
    sym_env_cbn;
    (try simp only [adenot_var, adenot_lit, bdenot_var, bdenot_lit,
      edenot_lit, edenot_var, u_Z_to_bv64_0]);
    all_goals sym_env_cbn)))
  unless (← getGoals).isEmpty do
    convertClosed fun e => do
      if e.isAppOfArity ``getr 2 then
        if let some r ← wordLiteral e.appArg! false then
          return some (mkApp e.appFn! r)
      return none

/-- Fold the literal displacements in the four Rocq patterns. -/
elab "sym_z_norm" : tactic => do
  repeat
    if (← getGoals).isEmpty then break
    let changed ← withMainContext do
      let t ← instantiateMVars (← getMainTarget)
      let found ← IO.mkRef (none : Option (Expr × TSyntax `term))
      let _ ← Meta.transform t (pre := fun e => do
        if (← found.get).isSome then return .done e
        if e.isAppOfArity ``Z_to_bv 2 &&
            (e.getArg! 0).nat? == some 64 then
          let z := e.appArg!
          if z.isAppOfArity ``HAdd.hAdd 6 then
            let a := z.getArg! 4
            let k := z.getArg! 5
            if let some k2 := intLit? k then
              let ks ← intSyntax k2
              if intLit? a == some 0 then
                found.set (some (z, ks))
              else if a.isAppOfArity ``HSub.hSub 6 then
                if let some k1 := intLit? (a.getArg! 5) then
                  let av ← Term.exprToSyntax (a.getArg! 4)
                  let v ← intSyntax (k1 - k2)
                  found.set (some (z, ← `(term| $av - $v)))
              else if a.isAppOfArity ``HAdd.hAdd 6 then
                if let some k1 := intLit? (a.getArg! 5) then
                  let av ← Term.exprToSyntax (a.getArg! 4)
                  let v ← intSyntax (k1 + k2)
                  found.set (some (z, ← `(term| $av + $v)))
              if (← found.get).isNone && k2 < 0 then
                let av ← Term.exprToSyntax a
                let v ← intSyntax (-k2)
                found.set (some (z, ← `(term| $av - $v)))
        return .continue)
      if let some (old, new) := (← found.get) then
        let old ← Term.exprToSyntax old
        evalTactic (← `(tactic| rewrite [show ($old : Int) = $new from by omega]))
        return true
      return false
    if !changed then break

/-- Literal conversion is restricted to store addresses and byte encodings. -/
elab "sym_lit_norm" : tactic =>
  convertClosed fun e => do
    if e.isAppOfArity ``wbytes 3 then
      if let some a ← wordLiteral (e.getArg! 1) true then
        return some (mkAppN e.getAppFn #[e.getArg! 0, a, e.getArg! 2])
    if e.isAppOfArity ``word_to_le_bytes 2 then
      if let some v ← wordLiteral e.appArg! true then
        return some (mkApp e.appFn! v)
    return none
end

macro "sym_addr_norm" : tactic => `(tactic| focus (
  sym_imm_norm;
  (try simp only [v_addi_Z]);
  all_goals (sym_env_norm; all_goals (sym_u_norm; sym_z_norm))))

macro "sym_norm" : tactic => `(tactic| focus (
  (try dsimp only [edenot, sr_get, List.getD, ridx, sym_state.s_regs,
    sym_state.s_pc, sym_state.s_log, sym_state.s_next, branch_taken]);
  (try simp only [alu64_add_0, aluw_add_0]);
  (try simp only [aluw_addi_lit]);
  (try simp only [alu_add, alu_sub, alu_and, alu_or, alu_xor,
    alu_slt, alu_sltu, alu_sll, alu_srl, alu_sra]);
  (try simp only [v_add_lit, v_sub_lit]);
  all_goals sym_addr_norm))

macro "sym_mem_norm" : tactic => `(tactic| focus (
  (try dsimp only [mem_denot, sentry.e_addr, sentry.e_width, sentry.e_val]);
  all_goals sym_norm;
  all_goals sym_lit_norm))

/-! ## 3. Attaching an `msteps` to whichever chain relation the goal is in -/

theorem msteps_to_exit (segs : List Segment) (code : word) (ms ms' : machine_state)
    (h : msteps segs ms ms') (he : to_exit segs code ms') : to_exit segs code ms := by
  induction h with
  | mst_refl => exact he
  | mst_step ms ms1 _ hp hs _ ih => exact .te_step ms ms1 hp hs (ih he)

theorem msteps_to_wr (segs : List Segment) (LH : machine_state → Prop) (bs : List byte)
    (ms ms' : machine_state) (h : msteps segs ms ms') (hw : StreamSim.to_wr segs LH bs ms') :
    StreamSim.to_wr segs LH bs ms := by
  induction h with
  | mst_refl => exact hw
  | mst_step ms ms1 _ hp hs _ ih => exact .twr_step ms ms1 hp hs (ih hw)

theorem msteps_lh_next (segs : List Segment) (LH : machine_state → Prop)
    (ms ms' : machine_state) (h : msteps segs ms ms')
    (hl : StreamSim.lh_next segs LH ms') : StreamSim.lh_next segs LH ms := by
  obtain ⟨m, hm, hL⟩ := hl
  exact ⟨m, msteps_trans segs ms ms' m h hm, hL⟩

/-- The named allocator rules replace Rocq's `model` rewrite database. -/
macro "sym_halted" : tactic => `(tactic| first
  | rfl
  | assumption
  | ((try simp only [MmapSim.mmap_model_halted, MmapSim.munmap_model_halted]);
      first | rfl | assumption)
  | ((try dsimp only [config.cfg_model, m_halted]);
      (try simp only [MmapSim.mmap_model_halted, MmapSim.munmap_model_halted]);
      first | rfl | assumption))

macro "sym_no_lazy" : tactic => `(tactic| focus (
  (try dsimp only [config.cfg_model]);
  all_goals (
    (repeat first
      | rewrite [MmapSim.mmap_model_lazy]
      | apply MmapSim.munmap_model_no_lazy);
    first | rfl | assumption)))

macro "chain_mst" : tactic => `(tactic| first
  | apply CatSim.msteps_to_wexit
  | apply MmapSim.msteps_twm
  | apply MmapSim.msteps_twm_tail
  | apply MmapSim.msteps_tmw
  | apply StreamSim.msteps_to_rd
  | apply msteps_to_wr
  | apply WallSim.msteps_to_wall_tail
  | apply WallSim.msteps_to_wallexit
  | apply DrainSim.msteps_to_rd
  | apply DrainSim.msteps_to_out
  | apply msteps_to_exit
  | apply msteps_lh_next
  | (apply ShapeAlg.rz_msteps
     · sym_halted
     · sym_no_lazy)
  | apply CatSim.msteps_trans)

theorem chain_mst_realizes (segs : List Segment) (ms ms' : machine_state)
    (model : Model) (T : ShapeAlg.TSet) (hh : m_halted model = none)
    (hlazy : m_vm_lazy model = []) (hms : msteps segs ms ms')
    (hr : ShapeAlg.realizes segs (config.mkCfg ms' model) T) :
    ShapeAlg.realizes segs (config.mkCfg ms model) T := by
  chain_mst
  · exact hms
  · exact hr

theorem chain_mst_realizes_mmap (segs : List Segment) (ms ms' : machine_state)
    (model : Model) (a n : word) (T : ShapeAlg.TSet) (hh : m_halted model = none)
    (hlazy : m_vm_lazy model = []) (hms : msteps segs ms ms')
    (hr : ShapeAlg.realizes segs (config.mkCfg ms' (MmapSim.mmap_model a n model)) T) :
    ShapeAlg.realizes segs (config.mkCfg ms (MmapSim.mmap_model a n model)) T := by
  chain_mst
  · exact hms
  · exact hr

/-! ## 4. Reading a block's post-state back -/

/-- The last alternative evaluates a closed goal only. -/
elab "sym_close" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| first
    | sym_close_open
    | (run_tac do
        let t ← Lean.Elab.Tactic.getMainTarget
        if t.hasFVar || t.hasMVar then throwError "sym_close: open goal"
       vm_closed)))

elab "sym_regs " h:ident : tactic => Lean.Elab.Tactic.focus do
  Lean.Elab.Tactic.evalTactic (← `(tactic| (
    getr_resolve;
    regupd_resolve;
    (repeat (focus (rewrite [← getr_nz]; rotate_left; reg_neq_tac)));
    (repeat rewrite [$h:ident _]))))
  unless (← Lean.Elab.Tactic.getGoals).isEmpty do
    convertClosed fun e => do
      if e.isAppOfArity ``sr_get 2 && closed e then
        return some (← Lean.Meta.reduce e)
      return none
    Lean.Elab.Tactic.evalTactic (← `(tactic| sym_norm))

/-- The asserted register equality is named `this` in Lean. -/
macro "sym_reg " h:ident R:term:max r:term:max v:term:max tac:tactic : tactic =>
  `(tactic| have $(Lean.mkIdent `this) : getr $R $r = $v := by sym_regs $h <;> $tac)

/-! ## 5. Block wrappers -/

/-- Count list syntax, without elaborating or reducing its elements. -/
private def literalLengthAux : Nat → Lean.Syntax → Lean.MacroM Nat
  | 0, _ => Lean.Macro.throwError "list_len: list literal too deep"
  | fuel + 1, s => do
  match s with
  | `(term| [$xs,*]) => return xs.getElems.size
  | `(term| $h :: $t) => let _ := h; return 1 + (← literalLengthAux fuel t)
  | `(term| List.nil) => return 0
  | `(term| @List.nil $_) => return 0
  | `(term| List.cons $_ $t) => return 1 + (← literalLengthAux fuel t)
  | `(term| @List.cons $_ $_ $t) => return 1 + (← literalLengthAux fuel t)
  | `(term| ($l)) => literalLengthAux fuel l
  | `(term| ($l : $_)) => literalLengthAux fuel l
  | _ => Lean.Macro.throwError "list_len: expected a list literal"

private def literalLength (s : Lean.Syntax) : Lean.MacroM Nat :=
  literalLengthAux 100000 s

open Lean Parser in
@[term_parser] def listLenTerm := leading_parser
  nonReservedSymbol "list_len" true >> termParser maxPrec

macro_rules
  | `(term| list_len $l) => do
    return Lean.Syntax.mkNumLit (toString (← literalLength l))

macro "sym_sc_auto" : tactic => `(tactic| first
  | with_reducible rfl
  | ((repeat' ((repeat intro); first
      | apply And.intro | exact True.intro | apply Iff.intro | with_reducible rfl)) <;> omega))

elab "sym_pin_auto" : tactic => Lean.Elab.Tactic.focus do
  let s ← Lean.Elab.Tactic.saveState
  try
    Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible rfl))
    return
  catch _ => s.restore
  Lean.Elab.Tactic.withMainContext do
    for h in ← Lean.getLCtx do
      if h.isImplementationDetail || !h.type.isAppOfArity ``regs_ok 3 then continue
      let s ← Lean.Elab.Tactic.saveState
      try
        let hn := Lean.mkIdent h.userName
        Lean.Elab.Tactic.evalTactic (← `(tactic| sym_regs $hn; all_goals sym_close_open))
        return
      catch _ => s.restore
    throwError "sym_pin_auto: no matching regs_ok fact"

private theorem forall_mem_empty {α : Type} (P : α → Prop) :
    (∀ x ∈ ([] : List α), P x) ↔ True :=
  ⟨fun _ => True.intro, fun _ => List.forall_mem_nil P⟩

section
open Lean Meta Elab Tactic
open LinuxProcessSemantics.Common.StepTac

private def goalState : TacticM Expr := do
  let t ← instantiateMVars (← getMainTarget)
  let some st := t.find? (·.isAppOfArity ``mkst 4)
    | throwError "sym_pc_Z: expected a mkst state in the goal"
  return st

/-- Put the first syntactic `mkst` PC into the executor's integer spelling.
Already spelled `Z_to_bv` PCs are left alone, including open ones. -/
elab "sym_pc_Z" : tactic => withMainContext do
  let st ← goalState
  let p := st.getArg! 1
  if p.isAppOfArity ``Z_to_bv 2 && (p.getArg! 0).nat? == some 64 then return
  checkClosedTerm p
  let u ← vmEval (← mkAppM ``bv_unsigned #[p])
  let v := mkApp2 (mkConst ``Z_to_bv) (mkNatLit 64) u
  let g ← getMainGoal
  let t ← g.getType
  replaceMainGoal [← g.replaceTargetDefEq (t.replace fun e => if e == p then some v else none)]

/-- Try `wlit` on the first syntactic `mkst` PC. -/
elab "sym_pc_lit" : tactic => do
  let saved ← saveState
  try withMainContext do
    let p ← Term.exprToSyntax ((← goalState).getArg! 1)
    evalTactic (← `(tactic| wlit $p))
  catch _ => saved.restore

/-- Attach a factored block, leaving the advanced chain with a literal PC. -/
macro "sym_chain " h:ident : tactic => `(tactic| (
  sym_pc_Z; chain_mst; (focus exact $h); norm_pc; sym_pc_lit))

private inductive CharTree where
  | run : Nat → Char → CharTree
  | join : Nat → CharTree → CharTree → CharTree

private def treeChars : CharTree → List Char
  | .run n c => List.replicate n c
  | .join _ l r => treeChars l ++ treeChars r

private def treeSize : CharTree → Nat
  | .run n _ => n
  | .join n _ r => n + treeSize r

private def treeValid : CharTree → Bool
  | .run _ _ => true
  | .join n l r => (n == treeSize l) && (treeValid l && treeValid r)

private def treeAscii : CharTree → Bool
  | .run n c => (n == 0) || (c.utf8Size == 1)
  | .join _ l r => treeAscii l && treeAscii r

private theorem treeAscii_eq (tree : CharTree) :
    (treeChars tree).all (fun c => c.utf8Size == 1) = treeAscii tree := by
  induction tree with
  | run n c =>
    by_cases hn : n = 0 <;> simp [treeChars, treeAscii, List.all_replicate, hn]
  | join n l r il ir => simp only [treeChars, treeAscii, List.all_append, il, ir]

private def treeGet (tree : CharTree) (i : Nat) (fallback : Char) : Char :=
  match tree with
  | .run n c => if i < n then c else fallback
  | .join n l r => if i < n then treeGet l i fallback else treeGet r (i - n) fallback

private theorem treeChars_length (tree : CharTree) (hv : treeValid tree = true) :
    (treeChars tree).length = treeSize tree := by
  induction tree with
  | run n c => simp only [treeChars, treeSize, List.length_replicate]
  | join n l r il ir =>
    simp only [treeValid, Bool.and_eq_true, beq_iff_eq] at hv
    obtain ⟨hn, hl, hr⟩ := hv
    simp only [treeChars, List.length_append, treeSize, il hl, ir hr, hn]

private theorem treeGet_eq (tree : CharTree) (hv : treeValid tree = true)
    (i : Nat) (fallback : Char) :
    treeGet tree i fallback = (treeChars tree).getD i fallback := by
  induction tree generalizing i with
  | run n c =>
    simp only [treeGet, treeChars, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl
  | join n l r il ir =>
    simp only [treeValid, Bool.and_eq_true, beq_iff_eq] at hv
    obtain ⟨hn, hl, hr⟩ := hv
    simp only [treeGet, treeChars, List.getD_eq_getElem?_getD, List.getElem?_append,
      treeChars_length l hl, ← hn]
    split
    · exact il hl i
    · exact ir hr (i - n)

private def cachedHex (cs : CharTree) (len i : Nat) : Option byte :=
  if 2 * i + 1 < len then
    let h := hex_nybble (treeGet cs (2 * i) '0').toUInt8
    let l := hex_nybble (treeGet cs (2 * i + 1) '0').toUInt8
    if h < 16 ∧ l < 16 then some (Z_to_bv 8 ((h * 16 + l : Nat) : Int)) else none
  else none

private theorem cachedHex_eq (cs : CharTree) (len i : Nat)
    (hlen : len = treeSize cs) (hv : treeValid cs = true) :
    cachedHex cs len i = ImageBytes.hex_chars_byte_at (treeChars cs) i := by
  subst len
  unfold cachedHex ImageBytes.hex_chars_byte_at
  simp only [treeChars_length cs hv, treeGet_eq cs hv]
  split
  · simp only [List.getElem_eq_getD '0']
  · rfl

private def cachedSegmentByte (chunks : List (Nat × CharTree)) (off : Nat) : Option byte :=
  match chunks with
  | [] => none
  | (len, cs) :: rest =>
    if off < len / 2 then cachedHex cs len off
    else cachedSegmentByte rest (off - len / 2)

private theorem cachedSegmentByte_eq (chunks : List (Nat × CharTree))
    (hlen : ∀ c ∈ chunks, c.1 = treeSize c.2 ∧ treeValid c.2 = true) (off : Nat) :
    cachedSegmentByte chunks off =
      ImageBytes.ascii_segment_byte_at (chunks.map (fun c => treeChars c.2)) off := by
  induction chunks generalizing off with
  | nil => rfl
  | cons c rest ih =>
    obtain ⟨len, cs⟩ := c
    have hc := hlen (len, cs) List.mem_cons_self
    have ht : ∀ c ∈ rest, c.1 = treeSize c.2 ∧ treeValid c.2 = true :=
      fun c hm => hlen c (List.mem_cons_of_mem _ hm)
    change len = treeSize cs ∧ treeValid cs = true at hc
    simp only [cachedSegmentByte, List.map_cons, ImageBytes.ascii_segment_byte_at, treeChars_length cs hc.2, ← hc.1]
    split
    · exact cachedHex_eq cs len off hc.1 hc.2
    · exact ih ht _

private def cachedSegmentRead (chunks : List (Nat × CharTree)) (off n : Nat) :
    Option (List byte) :=
  match n with
  | 0 => some []
  | n + 1 =>
    match cachedSegmentByte chunks off with
    | none => none
    | some b =>
      match cachedSegmentRead chunks (off + 1) n with
      | none => none
      | some bs => some (b :: bs)

private theorem cachedSegmentRead_eq (chunks : List (Nat × CharTree))
    (hlen : ∀ c ∈ chunks, c.1 = treeSize c.2 ∧ treeValid c.2 = true) (off n : Nat) :
    cachedSegmentRead chunks off n =
      ImageBytes.ascii_segment_read_bytes (chunks.map (fun c => treeChars c.2)) off n := by
  induction n generalizing off with
  | zero => rfl
  | succ n ih =>
    simp only [cachedSegmentRead, ImageBytes.ascii_segment_read_bytes,
      cachedSegmentByte_eq chunks hlen, ih]
    rfl

-- The UTF-8 encoding behind a string literal is expensive to unfold at every
-- fetch. Keep the original segments, with certified ASCII character chunks.
private abbrev ExecutorImage := List (Segment × List (Nat × CharTree))

private def chunkStrings (cs : List (Nat × CharTree)) : List String :=
  (cs.map (fun c => treeChars c.2)).map String.ofList

private def chunksValid (cs : List (Nat × CharTree)) : Bool :=
  cs.all (fun c => ((c.1 == treeSize c.2) && treeValid c.2) && treeAscii c.2)

private def imageOk (image : ExecutorImage) : Prop :=
  ∀ entry ∈ image, entry.1.seg_bytes = (entry.2.map (fun c => treeChars c.2)).map String.ofList ∧
    ∀ cs ∈ entry.2, (cs.1 = treeSize cs.2 ∧ treeValid cs.2 = true) ∧
      (treeChars cs.2).all (fun c => c.utf8Size == 1) = true

private theorem imageOk_nil : imageOk [] := by intro e h; cases h

private theorem imageOk_cons (seg : Segment) (cs : List (Nat × CharTree)) (rest : ExecutorImage)
    (hb : seg.seg_bytes = (cs.map (fun c => treeChars c.2)).map String.ofList)
    (ha : cs.all (fun chars => ((chars.1 == treeSize chars.2) && treeValid chars.2) &&
      treeAscii chars.2) = true)
    (ht : imageOk rest) : imageOk ((seg, cs) :: rest) := by
  intro entry he
  rcases List.mem_cons.mp he with rfl | he
  · refine ⟨hb, ?_⟩
    intro c hc
    have hh := List.all_eq_true.mp ha c hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hh
    exact ⟨hh.1, (treeAscii_eq c.2).trans hh.2⟩
  · exact ht entry he

private def imageRead (image : ExecutorImage) (addr : Int) (n : Nat) : Option (List byte) :=
  match image with
  | [] => none
  | (seg, cs) :: rest =>
    if (seg.seg_base : Int) ≤ addr && addr + n ≤ (seg.seg_base : Int) + seg.seg_size then
      if seg_executable seg && !seg_writable seg then
        cachedSegmentRead cs (addr - seg.seg_base).toNat n
      else none
    else imageRead rest addr n

private theorem imageRead_eq (image : ExecutorImage) (h : imageOk image)
    (pc : word) (n : Nat) :
    code_read (image.map Prod.fst) pc n = imageRead image (bv_unsigned pc) n := by
  induction image with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨seg, cs⟩ := entry
    have ⟨hb, hc⟩ := h _ List.mem_cons_self
    have hl : ∀ c ∈ cs, c.1 = treeSize c.2 ∧ treeValid c.2 = true := fun c hm => (hc c hm).1
    have ha : ∀ chars ∈ cs.map (fun c => treeChars c.2), chars.all (fun c => c.utf8Size == 1) = true := by
      intro chars hm
      obtain ⟨c, hmem, heq⟩ := List.mem_map.mp hm
      subst chars
      exact (hc c hmem).2
    have ht : imageOk rest := fun e he => h e (List.mem_cons_of_mem _ he)
    by_cases hc : (decide ((seg.seg_base : Int) ≤ bv_unsigned pc) &&
        decide (bv_unsigned pc + n ≤ (seg.seg_base : Int) + seg.seg_size)) = true
    · simp only [List.map_cons, code_read, find_segment, imageRead, hc, ↓reduceIte]
      rw [hb, ImageBytes.segment_read_bytes_ascii _ ha, cachedSegmentRead_eq cs hl]
    · simpa only [List.map_cons, code_read, find_segment, imageRead, hc, Bool.false_eq_true, ↓reduceIte]
        using ih ht

private def imageFetch (image : ExecutorImage) (pc : Int) : Option (BitVec 32) :=
  let addr := Z_to_bv 64 pc
  if !(bv_unsigned addr % 2 = 0) then none
  else match imageRead image (bv_unsigned addr) 4 with
    | some [b0, b1, b2, b3] => some (le4 b3 b2 b1 b0)
    | _ => none

private theorem imageFetch_eq (image : ExecutorImage) (h : imageOk image) (pc : Int) :
    fetch_word (image.map Prod.fst) (Z_to_bv 64 pc) = imageFetch image pc := by
  simp only [fetch_word, imageFetch, imageRead_eq image h]
  rfl

-- This is sym_exec with only its fetch operation abstracted. The equation
-- below proves the abstraction for all fuel, directions and symbolic states.
private def execNext (w : Option (BitVec 32)) (dirs : List Bool) (rds : List expr)
    (ss : sym_state) (acc : List sidecond) :
    Option (List Bool × List expr × sym_state × List sidecond) :=
    match w with
    | none => none
    | some w =>
      if is_ecall w then none else
      match LinuxProcessSemantics.Riscv.DecodeC.decode_any w with
      | none => none
      | some (i, sz) =>
        if !(decide (sz = 4)) then none else
        match i with
        | .Branch c rs1 rs2 imm =>
          match dirs with
          | [] => none
          | t :: dirs' => some (dirs', rds,
              sjump ss (if t then s_pc ss + bv_signed imm else s_pc ss + 4),
              SCBr t c (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2) :: acc)
        | _ =>
          match sym_step i ss rds with
          | some (ss', scs, rds') => some (dirs, rds', ss', scs ++ acc)
          | none => none

private def execFetch (fetch : Int → Option (BitVec 32)) (fuel : Nat)
    (dirs : List Bool) (rds : List expr) (ss : sym_state) (acc : List sidecond) :
    sym_state × List sidecond :=
  match fuel with
  | 0 => (ss, acc)
  | f + 1 => match execNext (fetch (s_pc ss)) dirs rds ss acc with
    | none => (ss, acc)
    | some (dirs', rds', ss', acc') => execFetch fetch f dirs' rds' ss' acc'

private theorem execFetch_next (fetch : Int → Option (BitVec 32)) (fuel : Nat)
    (dirs : List Bool) (rds : List expr) (ss : sym_state) (acc : List sidecond)
    (w : Option (BitVec 32)) (dirs' : List Bool) (rds' : List expr)
    (ss' : sym_state) (acc' : List sidecond)
    (hw : fetch (s_pc ss) = w)
    (hn : execNext w dirs rds ss acc = some (dirs', rds', ss', acc')) :
    execFetch fetch (fuel + 1) dirs rds ss acc = execFetch fetch fuel dirs' rds' ss' acc' := by
  simp only [execFetch, hw, hn]

private theorem execFetch_stop (fetch : Int → Option (BitVec 32)) (fuel : Nat)
    (dirs : List Bool) (rds : List expr) (ss : sym_state) (acc : List sidecond)
    (w : Option (BitVec 32)) (hw : fetch (s_pc ss) = w)
    (hn : execNext w dirs rds ss acc = none) :
    execFetch fetch (fuel + 1) dirs rds ss acc = (ss, acc) := by
  simp only [execFetch, hw, hn]

private theorem execFetch_eq (segs : List Segment) (fetch : Int → Option (BitVec 32))
    (h : ∀ pc, fetch_word segs (Z_to_bv 64 pc) = fetch pc)
    (fuel : Nat) (dirs : List Bool) (rds : List expr) (ss : sym_state) (acc : List sidecond) :
    sym_exec segs fuel dirs rds ss acc = execFetch fetch fuel dirs rds ss acc := by
  induction fuel generalizing dirs rds ss acc with
  | zero => rfl
  | succ fuel ih =>
    rw [sym_exec, execFetch, h]
    simp only [execNext, ih]
    cases hw : fetch (s_pc ss) with
    | none => rfl
    | some w =>
      by_cases he : is_ecall w = true
      · simp only [he, ↓reduceIte]
      · simp only [he, Bool.false_eq_true, ↓reduceIte]
        cases hd : LinuxProcessSemantics.Riscv.DecodeC.decode_any w with
        | none => rfl
        | some p =>
          obtain ⟨i, sz⟩ := p
          by_cases hs : (!decide (sz = 4)) = true
          · simp only [hs, ↓reduceIte]
          · simp only [hs, Bool.false_eq_true, ↓reduceIte]
            cases i <;> simp only
            all_goals first
              | (cases dirs <;> rfl)
              | (split <;> simp_all only)

-- Balanced append trees and runs keep certificate syntax shallow even for
-- multi-KiB chunks. This inspects literal syntax; it does not evaluate Lean
-- definitions with compiled code. The kernel checks every certificate below.
private def charTree (s : String) : Expr := Id.run do
  let chars := s.toList.toArray
  let mut parts : Array (Nat × Expr) := #[]
  let mut i := 0
  while i < chars.size do
    let c := chars[i]!
    let mut j := i + 1
    while j < chars.size && chars[j]! == c do j := j + 1
    parts := parts.push (j - i, mkApp2 (mkConst ``CharTree.run) (mkNatLit (j - i)) (toExpr c))
    i := j
  if parts.isEmpty then return mkApp2 (mkConst ``CharTree.run) (mkNatLit 0) (toExpr '0')
  while parts.size > 1 do
    let mut next := #[]
    for k in [: (parts.size + 1) / 2] do
      let a := parts[2 * k]!
      next := next.push (if 2 * k + 1 < parts.size then
        let b := parts[2 * k + 1]!
        (a.1 + b.1, mkApp3 (mkConst ``CharTree.join) (mkNatLit a.1) a.2 b.2)
        else a)
    parts := next
  return parts[0]!.2

private def conversionProof (a b : Expr) : MetaM Expr := do
  let proof := mkExpectedPropHint (← mkEqRefl b) (← mkEq a b)
  withLCtx {} #[] (checkWithKernel (ShareCommon.shareCommon proof))
  return proof

-- A monolithic literal's expanded character list is deeper than the default
-- kernel recursion limit. Prime inference with short overlapping suffixes,
-- then use kernel-reduced list equality to relate it to the shallow tree.
-- These are ordinary reflexivity lets, retained in the returned proof: the
-- final declaration checks every certificate again, with unchanged limits.
private def literalCertificate (s : String) (tree : Expr) : MetaM Expr := do
  let x := mkStrLit s
  let ct := mkConst ``Char
  let lt := mkApp (mkConst ``List [Level.zero]) ct
  let st := mkConst ``String
  let mut cs := mkApp (mkConst ``List.nil [Level.zero]) ct
  let mut suffixes := #[]
  let chars := s.toList.reverse.toArray
  for i in [:chars.size] do
    cs := mkApp3 (mkConst ``List.cons [Level.zero]) ct (toExpr chars[i]!) cs
    if i % 64 == 63 then suffixes := suffixes.push cs
  let rhs := mkApp (mkConst ``String.ofList) cs
  let hraw := mkExpectedPropHint (mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) st x)
    (mkApp3 (mkConst ``Eq [Level.succ Level.zero]) st x rhs)
  let csTree := mkApp (mkConst ``treeChars) tree
  let beq ← synthInstance (mkApp (mkConst ``BEq [Level.zero]) lt)
  let lawful ← synthInstance (mkApp2 (mkConst ``LawfulBEq [Level.zero]) lt beq)
  let hb ← mkEqRefl (mkConst ``Bool.true)
  let hc := mkAppN (mkConst ``LawfulBEq.eq_of_beq [Level.zero]) #[lt, beq, lawful, cs, csTree, hb]
  let htree := mkAppN (mkConst ``congrArg [Level.succ Level.zero, Level.succ Level.zero])
    #[lt, st, cs, csTree, mkConst ``String.ofList, hc]
  let mut p := mkAppN (mkConst ``Eq.trans [Level.succ Level.zero])
    #[st, x, rhs, mkApp (mkConst ``String.ofList) csTree, hraw, htree]
  for suffix in suffixes.reverse do
    let pty := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) lt suffix suffix
    let pv := mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) lt suffix
    p := mkLet `prime pty pv p
  return ShareCommon.shareCommon p

private theorem cons_eq_of_eq {α : Type} {a b : α} {xs ys : List α}
    (ha : a = b) (hs : xs = ys) : a :: xs = b :: ys := by
  cases ha
  cases hs
  rfl

private def certifyImageAux : Nat → Expr → MetaM (Expr × Expr)
  | 0, _ => throwError "sym_block: segment list too long"
  | fuel + 1, segs => do
  let xs ← withTransparency .default <| whnf segs
  if xs.isAppOfArity ``List.nil 1 then
    let ty := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``Segment)
      (mkApp (mkConst ``List [Level.zero])
        (mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``Nat)
          (mkConst ``CharTree)))
    return (← mkListLit ty [], mkConst ``imageOk_nil)
  unless xs.isAppOfArity ``List.cons 3 do throwError "sym_block: expected a closed segment list"
  let seg := xs.getArg! 1
  let bytes ← withTransparency .default <| whnf (← mkAppM ``Segment.seg_bytes #[seg])
  let mut chunks := bytes
  let mut cs : List Expr := []
  let mut certs : List Expr := []
  while chunks.isAppOfArity ``List.cons 3 do
    let str ← withTransparency .default <| whnf (chunks.getArg! 1)
    let .lit (.strVal str) := str
      | throwError "sym_block: expected literal hex chunks"
    unless str.toList.all (fun c => c.utf8Size == 1) do
      throwError "sym_block: expected ASCII hex chunks"
    let tree := charTree str
    cs := (← mkAppM ``Prod.mk #[mkNatLit str.length, tree]) :: cs
    certs := (← literalCertificate str tree) :: certs
    chunks ← withTransparency .default <| whnf (chunks.getArg! 2)
  unless chunks.isAppOfArity ``List.nil 1 do throwError "sym_block: expected a closed chunk list"
  let charTy := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``Nat)
    (mkConst ``CharTree)
  let chars ← mkListLit charTy cs.reverse
  let mapped := mkApp (mkConst ``chunkStrings) chars
  let nil := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``String)
  let mut hb ← mkEqRefl nil
  for cert in certs do
    hb ← mkAppM ``cons_eq_of_eq #[cert, hb]
  hb := mkExpectedPropHint hb (← mkEq (← mkAppM ``Segment.seg_bytes #[seg]) mapped)
  withLCtx {} #[] (checkWithKernel (ShareCommon.shareCommon hb))
  let all := mkApp (mkConst ``chunksValid) chars
  let ha ← conversionProof all (mkConst ``Bool.true)
  let (rest, ht) ← certifyImageAux fuel (xs.getArg! 2)
  let entry ← mkAppM ``Prod.mk #[seg, chars]
  let image ← mkAppM ``List.cons #[entry, rest]
  let h ← mkAppM ``imageOk_cons #[seg, chars, rest, hb, ha, ht]
  return (image, h)

private def certifyImage (segs : Expr) : MetaM (Expr × Expr) :=
  certifyImageAux 1000000 segs

private def executorValueAux (env : Lean.Environment) : Nat → Expr → MetaM Expr
  | 0, _ => throwError "sym_block: executor result too deep"
  | fuel + 1, e => do
  let v ← match Lean.Kernel.whnf env {} (ShareCommon.shareCommon e) with
    | .ok v => pure v
    | .error err => throwKernelException err
  if let .lit _ := v then return v
  let .const name _ := v.getAppFn
    | throwError "sym_block: executor result is not constructor data"
  let .ctorInfo info ← getConstInfo name
    | throwError "sym_block: executor result is not constructor data: {name}"
  let mut args := v.getAppArgs
  for i in [info.numParams:args.size] do
    args := args.set! i (← executorValueAux env fuel args[i]!)
  let v := mkAppN v.getAppFn args
  if v.isAppOfArity ``Int.ofNat 1 || v.isAppOfArity ``Int.negSucc 1 then
    let some z := intLit? v | throwError "sym_block: nonliteral integer in executor result"
    return mkIntLit z
  return v

private def executorValue (env : Lean.Environment) (e : Expr) : MetaM Expr :=
  executorValueAux env 1000000 e

private def kernelWhnf (e : Expr) : MetaM Expr := do
  ofExceptKernelException (Lean.Kernel.whnf (← getEnv) {} (ShareCommon.shareCommon e))

private def fetchLiteral (e : Expr) : MetaM (Expr × Expr) := do
  let v ← kernelWhnf e
  let v ← if v.isAppOfArity ``Option.some 2 then do
      let n ← kernelWhnf (← mkAppM ``BitVec.toNat #[v.getArg! 1])
      unless n.rawNatLit?.isSome do throwError "sym_block: nonliteral fetched word"
      let w := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 32) n
      mkAppM ``Option.some #[w]
    else pure v
  return (v, ← conversionProof e v)

private def runExecutor (fetch : Expr) (fuel : Nat)
    (dirs rds ss acc : Expr) : MetaM (Expr × Expr) := do
  let e ← mkAppM ``execFetch #[fetch, mkNatLit fuel, dirs, rds, ss, acc]
  match fuel with
  | 0 => do
    let v ← mkAppM ``Prod.mk #[ss, acc]
    return (v, ← conversionProof e v)
  | fuel + 1 => do
  let pc ← mkAppM ``sym_state.s_pc #[ss]
  let (w, hw) ← fetchLiteral (mkApp fetch pc)
  let step ← mkAppM ``execNext #[w, dirs, rds, ss, acc]
  let next ← executorValue (← getEnv) step
  let hn ← conversionProof step next
  let args := #[fetch, mkNatLit fuel, dirs, rds, ss, acc, w]
  if next.isAppOfArity ``Option.none 1 then
    let v ← mkAppM ``Prod.mk #[ss, acc]
    return (v, ← mkAppM ``execFetch_stop (args ++ #[hw, hn]))
  unless next.isAppOfArity ``Option.some 2 do throwError "sym_block: invalid executor step"
  let frame := next.getArg! 1
  let dirs' := frame.getArg! 2
  let rds' := (frame.getArg! 3).getArg! 2
  let ss' := ((frame.getArg! 3).getArg! 3).getArg! 2
  let acc' := ((frame.getArg! 3).getArg! 3).getArg! 3
  let h ← mkAppM ``execFetch_next (args ++ #[dirs', rds', ss', acc', hw, hn])
  let (v, tail) ← runExecutor fetch fuel dirs' rds' ss' acc'
  return (v, ← mkEqTrans h tail)

/-- Certify a closed image once, then compose kernel-checked fetch and step
equations. Kernel reduction alone still repeatedly expands a large chunk's
UTF-8 encoding; the certified tree makes each fetch independent of that scan.
Integer constructors are re-spelled as numerals for the existing normalizers.
The valuation never enters this term. -/
private def executorLiteral (e : Expr) : MetaM (Expr × Expr) := do
  checkClosedTerm e
  let e ← expandCtxDefs (← instantiateMVars e)
  -- Images not represented by ASCII literals use direct kernel reduction.
  let certified ← try pure (some (← certifyImage (e.getArg! 0))) catch _ => pure none
  let some (image, h) := certified | do
    let v ← executorValue (← getEnv) e
    return (v, ← conversionProof e v)
  let fetch ← mkAppM ``imageFetch #[image]
  let hf ← mkAppM ``imageFetch_eq #[image, h]
  let args := e.getAppArgs
  let bridge ← mkAppM ``execFetch_eq (#[e.getArg! 0, fetch, hf] ++ args[1:].toArray)
  let fuel ← kernelWhnf (args[1]!)
  let some fuel := fuel.rawNatLit? | throwError "sym_block: nonliteral fuel"
  let dirs ← executorValue (← getEnv) args[2]!
  let rds ← executorValue (← getEnv) args[3]!
  let ss ← executorValue (← getEnv) args[4]!
  let acc ← executorValue (← getEnv) args[5]!
  let (v, computed) ← runExecutor fetch fuel dirs rds ss acc
  checkClosedTerm v
  let proof ← mkEqTrans bridge computed
  withLCtx {} #[] (checkWithKernel (ShareCommon.shareCommon proof))
  return (v, proof)

private def blockCore (segs ms fuel dirs rds ps pvals rvals : TSyntax `term)
    (R H Hms : TSyntax `ident) (attach : Bool) : TacticM Unit := withMainContext do
  let entry ← instantiateMVars (← elabTerm ms (some (mkConst ``machine_state)))
  unless entry.isAppOfArity ``mkst 4 do
    throwError "sym_block_ex: expected mkst regs (Z_to_bv 64 pc) mem rom"
  let pc := entry.getArg! 1
  unless pc.isAppOfArity ``Z_to_bv 2 && (pc.getArg! 0).nat? == some 64 do
    throwError "sym_block_ex: expected mkst regs (Z_to_bv 64 pc) mem rom"
  let regs ← Term.exprToSyntax (entry.getArg! 0)
  let mem ← Term.exprToSyntax (entry.getArg! 2)
  let rom ← Term.exprToSyntax (entry.getArg! 3)
  let pc ← Term.exprToSyntax pc.appArg!
  let ss0 ← `(SS $pc (sr_pins $ps sr_id) [] (32 + list_len $pvals))
  let EE ← `(Eplus $regs ($pvals ++ $rvals))
  let ex ← elabTerm (← `(sym_exec $segs $fuel $dirs $rds $ss0 [])) none
  let (value, proof) ← executorLiteral ex
  unless value.isAppOfArity ``Prod.mk 4 do throwError "sym_block: executor did not reduce to a pair"
  let ss1 ← Term.exprToSyntax (value.getArg! 2)
  let scs ← Term.exprToSyntax (value.getArg! 3)
  let proof ← Term.exprToSyntax proof
  let scTy ← elabTerm (← `(scs_denot $segs $mem $EE $scs)) (some (mkSort .zero))
  let stTy ← elabTerm (← `(st_ok $EE $mem $rom $ss0 $ms)) (some (mkSort .zero))
  let sc ← mkFreshExprSyntheticOpaqueMVar scTy
  let st ← mkFreshExprSyntheticOpaqueMVar stTy
  let continuation ← getGoals
  setGoals [sc.mvarId!]
  evalTactic (← `(tactic| (
    simp only [scs_denot, List.forall_mem_cons, forall_mem_empty, and_true];
    (try dsimp only [sc_denot, sc_flat, adenot, bdenot, saddr.a_base, saddr.a_off]);
    (try sym_norm); (try sym_sc_auto))))
  let scGoals ← getGoals
  setGoals [st.mvarId!]
  evalTactic (← `(tactic| (
    refine ⟨$regs, rfl, regs_ok_pins $EE $ps sr_id $regs
      (regs_ok_Eplus $regs ($pvals ++ $rvals)) ?_, True.intro⟩
    simp only [pins_ok, List.forall_mem_cons, forall_mem_empty, and_true, Prod.fst, Prod.snd]
    all_goals (repeat' apply And.intro)
    all_goals (sym_env_norm; try sym_pin_auto))))
  let pinGoals ← getGoals
  setGoals continuation
  let sc ← Term.exprToSyntax sc
  let st ← Term.exprToSyntax st
  evalTactic (← `(tactic|
    obtain ⟨$R, $H, $Hms⟩ := sym_exec_ex $segs $fuel $dirs $rds $ss0 []
      $ss1 $scs $EE $mem $rom $ms $proof $sc $st))
  evalTactic (← `(tactic| dsimp only [sym_state.s_pc, sym_state.s_regs,
    sym_state.s_log, mem_denot] at $Hms:ident))
  if attach then
    evalTactic (← `(tactic| (
      chain_mst; (focus exact $Hms); clear $Hms;
      (try sym_mem_norm); norm_pc; sym_pc_lit)))
  setGoals (scGoals ++ pinGoals ++ (← getGoals))

/-- Execute a block and prepend its machine steps to the current chain.
Unclosed side conditions precede unclosed pins, then the advanced chain. -/
elab "sym_block " segs:term:max fuel:term:max dirs:term:max rds:term:max
    ps:term:max pvals:term:max rvals:term:max R:ident H:ident : tactic => focus do
  evalTactic (← `(tactic| sym_pc_Z))
  withMainContext do
    let ms ← Term.exprToSyntax (← goalState)
    let Hms ← mkFreshUserName `Hms
    blockCore segs ms fuel dirs rds ps pvals rvals R H (mkIdent Hms) true

/-- Execute an explicitly supplied entry state, adding the exit register
file, its `regs_ok` fact and its `msteps`, without changing the target. -/
elab "sym_block_ex " segs:term:max ms:term:max fuel:term:max dirs:term:max rds:term:max
    ps:term:max pvals:term:max rvals:term:max R:ident H:ident Hms:ident : tactic => focus do
  blockCore segs ms fuel dirs rds ps pvals rvals R H Hms false
end

section Tests
set_option linter.unusedVariables false

-- Normalizers are allowed to succeed without progress. Their negative tests
-- require closure, so a no-op does not count as a successful proof.
example (R : bvmap 5 word) (x y : word) : Eplus R [x, y] 33 = y := by
  sym_env_cbn
example (R : bvmap 5 word) (x : word) : Eplus R [x] 8 = getr R 8 := by
  sym_env_norm
  all_goals rfl
example : True := by
  sym_z_lit (-8)
  trivial
example (k : Int) : True := by
  fail_if_success sym_z_lit k
  trivial
example (a : Int) : Z_to_bv 64 (a - 32 + -8) = Z_to_bv 64 (a - 40) := by
  sym_z_norm
  rfl
example (a : Int) : Z_to_bv 64 (a + 3 + 5) = Z_to_bv 64 (a + 8) := by
  sym_z_norm
  rfl
example : Z_to_bv 64 (0 + 5) = Z_to_bv 64 5 := by
  sym_z_norm
  rfl
example (a : Int) : Z_to_bv 64 (a + -8) = Z_to_bv 64 (a - 8) := by
  sym_z_norm
  rfl
example (x : word) : v_addi x (-8) = Z_to_bv 64 (bv_unsigned x - 8) := by
  sym_addr_norm
  rfl
example (m : word → Option byte) :
    wbytes m (Z_to_bv 64 77824) (word_to_le_bytes 8 (Z_to_bv 64 69664)) =
      wbytes m 77824 (word_to_le_bytes 8 69664) := by
  sym_lit_norm
  with_reducible rfl
example (E : env) : edenot E (EAlu .ALU_ADD (EVar 2) (ELit 0)) = E 2 := by
  sym_norm
example (E : env) (m : word → Option byte) :
    mem_denot E m [SE (SA SBLit 77824) 8 (ELit 69664)] =
      wbytes m 77824 (word_to_le_bytes 8 69664) := by
  sym_mem_norm
  with_reducible rfl

example : True := by
  fail_if_success have : Z_to_bv 64 1 = Z_to_bv 64 2 := by sym_env_cbn
  fail_if_success have : Z_to_bv 64 1 = Z_to_bv 64 2 := by sym_env_norm
  fail_if_success have : Z_to_bv 64 1 = Z_to_bv 64 2 := by sym_z_norm
  fail_if_success have : Z_to_bv 64 1 = Z_to_bv 64 2 := by sym_addr_norm
  fail_if_success have : Z_to_bv 64 1 = Z_to_bv 64 2 := by sym_lit_norm
  fail_if_success have : Z_to_bv 64 1 = Z_to_bv 64 2 := by sym_norm
  fail_if_success have : Z_to_bv 64 1 = Z_to_bv 64 2 := by sym_mem_norm
  fail_if_success have : Z_to_bv 64 1 = Z_to_bv 64 2 := by sym_close
  trivial

example (m : Model) (a n : word) (h : m_halted m = none) :
    m_halted (MmapSim.mmap_model a n (MmapSim.munmap_model a n m)) = none := by
  sym_halted
example (m : Model) (a n : word) (h : m_vm_lazy m = []) :
    m_vm_lazy (MmapSim.mmap_model a n (MmapSim.munmap_model a n m)) = [] := by
  sym_no_lazy
example (m : Model) : True := by
  fail_if_success have : m_halted m = none := by sym_halted
  fail_if_success have : m_vm_lazy m = [] := by sym_no_lazy
  trivial
example (a : Int) : Z_to_bv 64 (a + 3 - 2) = Z_to_bv 64 (a + 1) := by
  sym_close
example (x : word) : x = x := by sym_close
example : Z_to_bv 64 (-1) = (18446744073709551615 : word) := by sym_close

example (E : env) (R : bvmap 5 word) (h : regs_ok E [ELit 0, EVar 32] R) :
    getr R 1 = E 32 := by
  sym_regs h
example (E : env) (R : bvmap 5 word) (h : regs_ok E [ELit 0, EVar 32] R) :
    getr R 1 = E 32 := by
  sym_reg h R (1 : reg) (E 32) (rfl)
  exact this
example (E : env) (R : bvmap 5 word) (h : regs_ok E [ELit 0, EVar 32] R) : True := by
  fail_if_success have : getr R 1 = v_addi (E 32) 1 := by sym_regs h; sym_close
  fail_if_success sym_reg h R (1 : reg) (v_addi (E 32) 1) (sym_close)
  trivial

example (x y : word) : list_len [x, y, v_addi x 8] = 3 := rfl
example (x : word) : list_len (x :: [] : List word) = 1 := rfl
example (xs : List word) : True := by
  fail_if_success have : Nat := list_len xs
  trivial
example (n : Int) (h : 0 ≤ n) : 0 ≤ n + 8 ∧ n < n + 8 := by sym_sc_auto
example (n : Int) : True := by
  fail_if_success have : n < 0 := by sym_sc_auto
  trivial
example (E : env) (R : bvmap 5 word) (h : regs_ok E [ELit 0, EVar 32] R) :
    getr R 1 = E 32 := by sym_pin_auto
example (R : bvmap 5 word) (x : word) : True := by
  fail_if_success have : getr R 1 = x := by sym_pin_auto
  trivial

example : True := by
  fail_if_success chain_mst
  trivial

example (segs : List Segment) (ms ms' : machine_state) (bufs : List (List byte)) (code : word)
    (hms : msteps segs ms ms') (hr : CatSim.to_wexit segs ms' bufs code) :
    CatSim.to_wexit segs ms bufs code := by
  chain_mst
  · exact hms
  · exact hr

example (segs : List Segment) (ms ms' : machine_state) (model : Model) (bufs : List (List byte)) (code : word)
    (hms : msteps segs ms ms') (hr : MmapSim.twm segs ms' model bufs code) :
    MmapSim.twm segs ms model bufs code := by
  chain_mst
  · exact hms
  · exact hr

example (segs : List Segment) (ms ms' : machine_state) (model : Model) (bs : List byte) (bufs : List (List byte)) (code : word)
    (hms : msteps segs ms ms') (hr : MmapSim.twm_tail segs ms' model bs bufs code) :
    MmapSim.twm_tail segs ms model bs bufs code := by
  chain_mst
  · exact hms
  · exact hr

example (segs : List Segment) (ms ms' : machine_state) (model : Model) (bf bs : List (List byte)) (cf cs : word)
    (hms : msteps segs ms ms') (hr : MmapSim.tmw segs ms' model bf cf bs cs) :
    MmapSim.tmw segs ms model bf cf bs cs := by
  chain_mst
  · exact hms
  · exact hr

example (segs : List Segment) (ms ms' : machine_state) (LH : machine_state → Prop) (cnt : word)
    (hms : msteps segs ms ms') (hr : StreamSim.to_rd segs LH cnt ms') :
    StreamSim.to_rd segs LH cnt ms := by
  chain_mst
  · exact hms
  · exact hr

example (segs : List Segment) (ms ms' : machine_state) (LH : machine_state → Prop) (bs : List byte)
    (hms : msteps segs ms ms') (hr : StreamSim.to_wr segs LH bs ms') :
    StreamSim.to_wr segs LH bs ms := by
  chain_mst
  · exact hms
  · exact hr

example (segs : List Segment) (ms ms' : machine_state) (fd : word) (bs : List byte) (K : machine_state → Prop)
    (hms : msteps segs ms ms') (hr : WallSim.to_wall_tail segs fd ms' bs K) :
    WallSim.to_wall_tail segs fd ms bs K := by
  chain_mst
  · exact hms
  · exact hr

example (segs : List Segment) (ms ms' : machine_state) (fd : word) (bufs : List (List byte)) (code : word)
    (hms : msteps segs ms ms') (hr : WallSim.to_wallexit segs fd bufs code ms') :
    WallSim.to_wallexit segs fd bufs code ms := by
  chain_mst
  · exact hms
  · exact hr

example (segs : List Segment) (ms ms' : machine_state) (A : Type) (cnt ec : word) (f : A → byte → Option A) (out : A → List byte) (LH : A → machine_state → Prop) (a : A)
    (hms : msteps segs ms ms') (hr : DrainSim.to_rd segs cnt f out ec LH a ms') :
    DrainSim.to_rd segs cnt f out ec LH a ms := by
  chain_mst
  · exact hms
  · exact hr

example (segs : List Segment) (ms ms' : machine_state) (bs : List byte)
    (hms : msteps segs ms ms') (hr : DrainSim.to_out segs bs ms') :
    DrainSim.to_out segs bs ms := by
  chain_mst
  · exact hms
  · exact hr

example (segs : List Segment) (ms ms' : machine_state) (code : word)
    (hms : msteps segs ms ms') (hr : to_exit segs code ms') :
    to_exit segs code ms := by
  chain_mst
  · exact hms
  · exact hr

example (segs : List Segment) (ms ms' : machine_state) (LH : machine_state → Prop)
    (hms : msteps segs ms ms') (hr : StreamSim.lh_next segs LH ms') :
    StreamSim.lh_next segs LH ms := by
  chain_mst
  · exact hms
  · exact hr

example (segs : List Segment) (ms ms' : machine_state) (target : machine_state)
    (hms : msteps segs ms ms') (hr : msteps segs ms' target) :
    msteps segs ms target := by
  chain_mst
  · exact hms
  · exact hr

-- Open right-hand sides keep the target visible for exact shape checks.
example (R : bvmap 5 word) (x y : word) (h : x = y) : Eplus R [x] 32 = y := by
  sym_env_cbn
  guard_target =ₛ x = y
  exact h
example (R : bvmap 5 word) (x : word) (h : getr R 8 = x) : Eplus R [] 8 = x := by
  sym_env_norm
  guard_target =~ getr R 8 = x
  exact h
example (E : env) (R : bvmap 5 word) (x : word)
    (h : regs_ok E [ELit 0, EVar 32] R) (hx : E 32 = x) : getr R 1 = x := by
  sym_regs h
  guard_target =ₛ E 32 = x
  exact hx
example (a : Int) (x : word) (h : Z_to_bv 64 (a - 40) = x) :
    Z_to_bv 64 (a - 32 + -8) = x := by
  sym_z_norm
  guard_target =ₛ Z_to_bv 64 (a - 40) = x
  exact h
example (x : word) (h : Z_to_bv 64 5 = x) : Z_to_bv 64 (0 + 5) = x := by
  sym_z_norm
  guard_target =ₛ Z_to_bv 64 5 = x
  exact h
example (a b : word) (h : Z_to_bv 64 (bv_unsigned a - 8) = b) : v_addi a (-8) = b := by
  sym_addr_norm
  guard_target =~ Z_to_bv 64 (bv_unsigned a - 8) = b
  exact h
example (E : env) (x : word) (h : E 2 = x) :
    edenot E (EAlu .ALU_ADD (EVar 2) (ELit 0)) = x := by
  sym_norm
  guard_target =ₛ E 2 = x
  exact h
-- An open word in the store payload stays folded.
example (x : word) (h : word_to_le_bytes 8 x = []) : word_to_le_bytes 8 x = [] := by
  sym_lit_norm
  guard_target =ₛ word_to_le_bytes 8 x = []
  exact h
-- Normalize the first goal without touching the second goal.
example (E : env) (x : word) (h : E 2 = x) :
    edenot E (EVar 2) = x ∧ edenot E (EVar 2) = x := by
  constructor
  sym_norm
  · exact h
  · guard_target =ₛ edenot E (EVar 2) = x
    exact h

example (m : Model) (a n : word) :
    m_halted (MmapSim.mmap_model a n
      { m with m_proc := { m.m_proc with procst_halted := none } }) = none := by
  sym_halted
example (m : Model) (a n : word) :
    m_vm_lazy (MmapSim.mmap_model a n
      { m with m_vm := { m.m_vm with vmst_lazy := [] } }) = [] := by
  sym_no_lazy
example (x : word) : list_len (List.cons x (List.nil : List word)) = 1 := rfl
example (x : word) : list_len (@List.cons word x (@List.nil word)) = 1 := rfl
-- A failed candidate restores the context before trying the earlier fact.
example (E F : env) (R : bvmap 5 word)
    (wrong : regs_ok F [ELit 0, EVar 33] R)
    (h : regs_ok E [ELit 0, EVar 32] R) : getr R 1 = E 32 := by
  sym_pin_auto
example (a k : Int) (x : word) (h : Z_to_bv 64 (a + k + 8) = x) :
    Z_to_bv 64 (a + k + 8) = x := by
  sym_z_norm
  guard_target =ₛ Z_to_bv 64 (a + k + 8) = x
  exact h
example (x y : word) : True := by
  fail_if_success have : x = y := by sym_close
  trivial

example (E : env) (m : word → Option byte) : mem_denot E m [] = m := by
  sym_mem_norm
example (segs : List Segment) (ms : machine_state) (model : Model) (T : ShapeAlg.TSet)
    (hr : ShapeAlg.realizes segs (config.mkCfg ms model) T) :
    ShapeAlg.realizes segs (config.mkCfg ms model) T := by
  fail_if_success chain_mst
  exact hr
example (segs : List Segment) (ms : machine_state) (model : Model) (T : ShapeAlg.TSet)
    (hh : m_halted model = none)
    (hr : ShapeAlg.realizes segs (config.mkCfg ms model) T) :
    ShapeAlg.realizes segs (config.mkCfg ms model) T := by
  fail_if_success chain_mst
  exact hr

-- Tactic keywords remain available as identifiers.
example (sym_env_cbn : Nat) : sym_env_cbn = sym_env_cbn := rfl
example (sym_env_norm : Nat) : sym_env_norm = sym_env_norm := rfl
example (sym_z_lit : Nat) : sym_z_lit = sym_z_lit := rfl
example (sym_z_norm : Nat) : sym_z_norm = sym_z_norm := rfl
example (sym_addr_norm : Nat) : sym_addr_norm = sym_addr_norm := rfl
example (sym_lit_norm : Nat) : sym_lit_norm = sym_lit_norm := rfl
example (sym_norm : Nat) : sym_norm = sym_norm := rfl
example (sym_mem_norm : Nat) : sym_mem_norm = sym_mem_norm := rfl
example (sym_halted : Nat) : sym_halted = sym_halted := rfl
example (sym_no_lazy : Nat) : sym_no_lazy = sym_no_lazy := rfl
example (chain_mst : Nat) : chain_mst = chain_mst := rfl
example (sym_close : Nat) : sym_close = sym_close := rfl
example (sym_regs : Nat) : sym_regs = sym_regs := rfl
example (sym_reg : Nat) : sym_reg = sym_reg := rfl
example (list_len : Nat) : list_len = list_len := rfl
example (sym_sc_auto : Nat) : sym_sc_auto = sym_sc_auto := rfl
example (sym_pin_auto : Nat) : sym_pin_auto = sym_pin_auto := rfl

-- addi x5,x0,7; add x6,x5,x5; ecall. The executor stops AT ecall.
private def tinyBlock : List Segment :=
  [⟨4096, 12, "rx", ["930270003383520073000000"]⟩]

example (regs : bvmap 5 word) (mem rom : word → Option byte) (code : word)
    (finish : ∀ R : bvmap 5 word, getr R 6 = (14 : word) →
      to_exit tinyBlock code (mkst R 4104 mem rom)) :
    to_exit tinyBlock code (mkst regs 4096 mem rom) := by
  sym_block tinyBlock 3 [] [] [] [] [] R H
  guard_target =ₛ to_exit tinyBlock code (mkst R 4104 mem rom)
  fail_if_success have : getr R 6 = (15 : word) := by sym_regs H; sym_close
  apply finish R
  sym_regs H
  sym_close

example (regs : bvmap 5 word) (mem rom : word → Option byte) :
    ∃ R, getr R 6 = (14 : word) ∧
      msteps tinyBlock (mkst regs (Z_to_bv 64 4096) mem rom)
        (mkst R (Z_to_bv 64 4104) mem rom) := by
  sym_block_ex tinyBlock (mkst regs (Z_to_bv 64 4096) mem rom)
    3 [] [] [] [] [] R H Hms
  have steps : msteps tinyBlock (mkst regs (Z_to_bv 64 4096) mem rom)
      (mkst R (Z_to_bv 64 4104) mem rom) := Hms
  refine ⟨R, ?_, steps⟩
  sym_regs H
  sym_close

example (regs : bvmap 5 word) (mem rom : word → Option byte) (code : word)
    (finish : ∀ R, to_exit tinyBlock code (mkst R 4104 mem rom)) :
    to_exit tinyBlock code (mkst regs 4096 mem rom) := by
  sym_block_ex tinyBlock (mkst regs (Z_to_bv 64 4096) mem rom)
    3 [] [] [] [] [] R H Hms
  guard_target =ₛ to_exit tinyBlock code (mkst regs 4096 mem rom)
  sym_chain Hms
  guard_target =ₛ to_exit tinyBlock code (mkst R 4104 mem rom)
  exact finish R

example (regs : bvmap 5 word) (mem rom : word → Option byte) (code : word)
    (h : to_exit tinyBlock code (mkst regs 4096 mem rom)) :
    to_exit tinyBlock code (mkst regs 4096 mem rom) := by
  sym_pc_Z
  guard_target =ₛ to_exit tinyBlock code (mkst regs (Z_to_bv 64 4096) mem rom)
  sym_pc_lit
  guard_target =ₛ to_exit tinyBlock code (mkst regs 4096 mem rom)
  exact h

example : True := by
  fail_if_success sym_block tinyBlock 3 [] [] [] [] [] R H
  trivial
example (regs : bvmap 5 word) (mem rom : word → Option byte) (ms : machine_state) : True := by
  fail_if_success sym_block_ex tinyBlock ms 3 [] [] [] [] [] R H Hms
  fail_if_success sym_block_ex tinyBlock (mkst regs 4096 mem rom) 3 [] [] [] [] [] R H Hms
  trivial
example (regs : bvmap 5 word) (mem rom : word → Option byte) (code : word)
    (Hms : msteps tinyBlock (mkst regs (Z_to_bv 64 4100) mem rom)
      (mkst regs (Z_to_bv 64 4104) mem rom))
    (h : to_exit tinyBlock code (mkst regs 4096 mem rom)) :
    to_exit tinyBlock code (mkst regs 4096 mem rom) := by
  fail_if_success sym_chain Hms
  exact h
example (regs : bvmap 5 word) (pc code : word) (mem rom : word → Option byte)
    (h : to_exit tinyBlock code (mkst regs pc mem rom)) :
    to_exit tinyBlock code (mkst regs pc mem rom) := by
  fail_if_success sym_pc_Z
  exact h

example (sym_pc_Z sym_pc_lit sym_block sym_block_ex sym_chain : Nat) :
    sym_pc_Z + sym_pc_lit + sym_block + sym_block_ex + sym_chain =
    sym_pc_Z + sym_pc_lit + sym_block + sym_block_ex + sym_chain := rfl

-- beq x1,x2,+4, followed by ecall: unresolved branch, then two pins.
private def branchBlock : List Segment :=
  [⟨4096, 8, "rx", ["6382200073000000"]⟩]

example (regs : bvmap 5 word) (mem rom : word → Option byte) (a b code : word)
    (hb : Unit → bv_eqb a b = true)
    (h1 : Unit → getr regs 1 = a) (h2 : Unit → getr regs 2 = b)
    (finish : ∀ R, to_exit branchBlock code (mkst R 4100 mem rom)) :
    to_exit branchBlock code (mkst regs 4096 mem rom) := by
  sym_block branchBlock 2 [true] [] [(1, EVar 32), (2, EVar 33)] [a, b] [] R H
  · guard_target =ₛ bv_eqb a b = true
    exact hb ()
  · guard_target =~ getr regs 1 = a
    exact h1 ()
  · guard_target =~ getr regs 2 = b
    exact h2 ()
  · guard_target =ₛ to_exit branchBlock code (mkst R 4100 mem rom)
    exact finish R

example (regs : bvmap 5 word) (mem rom : word → Option byte) (pc : Int)
    (fuel : Nat) (segs : List Segment) : True := by
  fail_if_success sym_block_ex tinyBlock (mkst regs (Z_to_bv 64 pc) mem rom)
    3 [] [] [] [] [] R H Hms
  fail_if_success sym_block_ex tinyBlock (mkst regs (Z_to_bv 64 4096) mem rom)
    fuel [] [] [] [] [] R H Hms
  fail_if_success sym_block_ex segs (mkst regs (Z_to_bv 64 4096) mem rom)
    3 [] [] [] [] [] R H Hms
  trivial

-- sd x5,0(x6); ecall. Stores exercise the exit memory spelling.
private def storeBlock : List Segment :=
  [⟨4096, 8, "rx", ["2330530073000000"]⟩]

example (regs : bvmap 5 word) (mem rom : word → Option byte) (code : word)
    (hs : Unit → store_ok storeBlock mem (Z_to_bv 64 8192) 8 = true)
    (h5 : Unit → getr regs 5 = Z_to_bv 64 7)
    (h6 : Unit → getr regs 6 = Z_to_bv 64 8192)
    (finish : ∀ R, to_exit storeBlock code
      (mkst R 4100 (wbytes mem 8192 (word_to_le_bytes 8 7)) rom)) :
    to_exit storeBlock code (mkst regs 4096 mem rom) := by
  sym_block storeBlock 2 [] [] [(5, ELit 7), (6, ELit 8192)] [] [] R H
  · exact ⟨by omega, hs ()⟩
  · exact h5 ()
  · exact h6 ()
  · guard_target =~ to_exit storeBlock code
      (mkst R 4100 (wbytes mem 8192 (word_to_le_bytes 8 7)) rom)
    exact finish R

-- alloc_join_ns target_epilogue's exact words and PCs (six ld, addi sp,
-- jalr, then addi a7 at the return address). The executable image is one
-- 4096-byte/8192-character chunk, matching TargetMemImage_segment_001.
-- Unused bytes are zero; offset 0xf00 also carries forty addi x5,x5,1
-- instructions for the upper end of the block-size regression.
private def epilogueBlock : List Segment :=
  [⟨0x1000000, 4096, "r--", []⟩,
   ⟨0x1001000, 4096, "r-x", ["000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009308d00573000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008330810203340102833481010339010183398100033a0100130101036780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000093821200938212009382120093821200938212009382120093821200938212009382120093821200938212009382120093821200938212009382120093821200938212009382120093821200938212009382120093821200938212009382120093821200938212009382120093821200938212009382120093821200938212009382120093821200938212009382120093821200938212009382120093821200730000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"]⟩]


example (regs : bvmap 5 word) (mem rom : word → Option byte) (saved : word)
    (h2 : getr regs 2 = Z_to_bv 64 8192)
    (reads : ∀ (a : word) (v : word),
      (a, v) ∈ [(8192, 0), (8200, 0), (8208, 0), (8216, 0),
        (8224, saved), (8232, 0x1001178)] →
      ∃ bs, rdn epilogueBlock mem a 8 = some bs ∧ bytes_le_to_Z bs = bv_unsigned v) :
    ∃ R, getr R 17 = (93 : word) ∧
      msteps epilogueBlock (mkst regs (Z_to_bv 64 0x10012b0) mem rom)
        (mkst R (Z_to_bv 64 0x100117c) mem rom) := by
  sym_block_ex epilogueBlock (mkst regs (Z_to_bv 64 0x10012b0) mem rom)
    9 [] [ELit 0x1001178, EVar 33, ELit 0, ELit 0, ELit 0, ELit 0]
    [(2, EVar 32)] [Z_to_bv 64 8192, saved] [] R H Hms
  · repeat' apply And.intro
    all_goals first
      | decide +kernel
      | exact reads _ (0 : word) (by simp [Z_to_bv])
      | exact reads _ saved (by simp [Z_to_bv])
      | exact reads _ (0x1001178 : word) (by simp [Z_to_bv])
  · exact h2
  · have steps : msteps epilogueBlock (mkst regs (Z_to_bv 64 0x10012b0) mem rom)
        (mkst R (Z_to_bv 64 0x100117c) mem rom) := Hms
    fail_if_success have : getr R 17 = (94 : word) := by sym_regs H; sym_close
    have restored : getr R 8 = saved := by sym_regs H
    refine ⟨R, ?_, steps⟩
    sym_regs H
    sym_close

example (regs : bvmap 5 word) (mem rom : word → Option byte) (saved code : word)
    (h2 : getr regs 2 = Z_to_bv 64 8192)
    (reads : ∀ (a : word) (v : word),
      (a, v) ∈ [(8192, 0), (8200, 0), (8208, 0), (8216, 0),
        (8224, saved), (8232, 0x1001178)] →
      ∃ bs, rdn epilogueBlock mem a 8 = some bs ∧ bytes_le_to_Z bs = bv_unsigned v)
    (finish : ∀ R, getr R 17 = (93 : word) → getr R 8 = saved →
      to_exit epilogueBlock code (mkst R 0x100117c mem rom)) :
    to_exit epilogueBlock code (mkst regs 0x10012b0 mem rom) := by
  sym_block epilogueBlock 9 []
    [ELit 0x1001178, EVar 33, ELit 0, ELit 0, ELit 0, ELit 0]
    [(2, EVar 32)] [Z_to_bv 64 8192, saved] [] R H
  · repeat' apply And.intro
    all_goals first
      | decide +kernel
      | exact reads _ (0 : word) (by simp [Z_to_bv])
      | exact reads _ saved (by simp [Z_to_bv])
      | exact reads _ (0x1001178 : word) (by simp [Z_to_bv])
  · exact h2
  · guard_target =ₛ to_exit epilogueBlock code (mkst R 0x100117c mem rom)
    apply finish R
    · sym_regs H; sym_close
    · sym_regs H

example (regs : bvmap 5 word) (mem rom : word → Option byte) (code : word)
    (h5 : getr regs 5 = Z_to_bv 64 0)
    (finish : ∀ R, getr R 5 = (40 : word) →
      to_exit epilogueBlock code (mkst R 0x1001fa0 mem rom)) :
    to_exit epilogueBlock code (mkst regs 0x1001f00 mem rom) := by
  sym_block epilogueBlock 40 [] [] [(5, ELit 0)] [] [] R H
  · exact h5
  · guard_target =ₛ to_exit epilogueBlock code (mkst R 0x1001fa0 mem rom)
    fail_if_success have : getr R 5 = (41 : word) := by sym_regs H; sym_close
    apply finish R
    sym_regs H
    sym_close

example (regs : bvmap 5 word) (mem rom : word → Option byte) : True := by
  fail_if_success sym_block_ex epilogueBlock (mkst regs 0x10012b0 mem rom)
    9 [] [ELit 0x1001178, EVar 33, ELit 0, ELit 0, ELit 0, ELit 0]
    [(2, EVar 32)] [Z_to_bv 64 8192, Z_to_bv 64 0] [] R H Hms
  trivial

-- A wrong cached size or an invalid tree cannot supply an image certificate.
example : chunksValid [(8, .run 8 '0')] = true := rfl
example : chunksValid [(9, .run 8 '0')] = false := rfl
example : chunksValid [(2, .join 2 (.run 1 '0') (.run 1 '1'))] = false := rfl
-- Unicode chunks use the original fetch and stop at invalid hex.
private def unicodeBlock : List Segment := [⟨4096, 8, "rx", ["é0000000"]⟩]
example (regs : bvmap 5 word) (mem rom : word → Option byte) :
    ∃ R, msteps unicodeBlock (mkst regs (Z_to_bv 64 4096) mem rom)
      (mkst R (Z_to_bv 64 4096) mem rom) := by
  sym_block_ex unicodeBlock (mkst regs (Z_to_bv 64 4096) mem rom)
    1 [] [] [] [] [] R H Hms
  fail_if_success
    have wrong : msteps unicodeBlock (mkst regs (Z_to_bv 64 4096) mem rom)
        (mkst R (Z_to_bv 64 4100) mem rom) := Hms
  exact ⟨R, Hms⟩

open Lean Meta Elab Tactic in
example : True := by
  fail_if_success run_tac
    let original := String.ofList (List.replicate 8192 '0')
    let wrong := charTree (String.ofList (List.replicate 8191 '0') ++ "1")
    let cert ← literalCertificate original wrong
    withLCtx {} #[] (checkWithKernel cert)
  trivial

-- Odd chunk tails are discarded per chunk; fetch may cross a chunk boundary.
private def splitBlock : List Segment := [⟨4096, 8, "rx", ["930", "02700073000000"]⟩]
example (regs : bvmap 5 word) (mem rom : word → Option byte) :
    ∃ R, getr R 5 = (7 : word) ∧
      msteps splitBlock (mkst regs (Z_to_bv 64 4096) mem rom)
        (mkst R (Z_to_bv 64 4100) mem rom) := by
  sym_block_ex splitBlock (mkst regs (Z_to_bv 64 4096) mem rom)
    2 [] [] [] [] [] R H Hms
  fail_if_success have : getr R 5 = (8 : word) := by sym_regs H; sym_close
  refine ⟨R, ?_, Hms⟩
  sym_regs H
  sym_close

-- Selection precedes permissions, so the second overlapping segment is not used.
private def coveredBlock : List Segment :=
  ⟨4096, 12, "r--", []⟩ :: tinyBlock
example (regs : bvmap 5 word) (mem rom : word → Option byte) :
    ∃ R, msteps coveredBlock (mkst regs (Z_to_bv 64 4096) mem rom)
      (mkst R (Z_to_bv 64 4096) mem rom) := by
  sym_block_ex coveredBlock (mkst regs (Z_to_bv 64 4096) mem rom)
    3 [] [] [] [] [] R H Hms
  fail_if_success
    have wrong : msteps coveredBlock (mkst regs (Z_to_bv 64 4096) mem rom)
        (mkst R (Z_to_bv 64 4104) mem rom) := Hms
  exact ⟨R, Hms⟩

end Tests

end LinuxProcessSemantics.Common.SymTac
