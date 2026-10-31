import Lean
import Lean.Compiler.ImplementedByAttr

/-! Mechanically enforced proof and execution trust boundary.

The environment supplies declaration ownership and attributes, so renamed
identifiers or attributes attached after a definition do not evade the check.
The companion tool compares the reported imported modules with source files;
an unimported source file cannot silently disappear from this audit.
-/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Policy

open Lean Elab Command Meta

def allowed_axioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

def isProjectModule (n : Name) : Bool := n.getRoot == `LinuxProcessSemantics

def declarationModule (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

/-- This checks definitions and unused axioms as well as named theorems.

The `isUnsafe` rejection reads the environment's own record of a
declaration the kernel checked only under the unsafe rules, which no
attribute check would find: under the pinned toolchain (leanprover/lean4
v4.34.0) an `unsafe def` is a definition carrying `DefinitionSafety.unsafe`,
and an `unsafe inductive` is added with the flag
(`Lean.Elab.MutualInductive`) that `ConstantInfo.isUnsafe` reads back off
its type, constructors and recursor (`Lean.Declaration`).

A `partial def` is deliberately NOT read off the environment, and the
reason is worth keeping because `ConstantInfo.isPartial` looks like the
obvious arm.  `partial def f` becomes an `opaque` `f` holding an inhabitant
of the type, plus the body that actually runs as `f._unsafe_rec` with
`DefinitionSafety.partial` (`addAndCompilePartial` and
`addAndCompilePartialRec`, `Lean.Elab.PreDefinition.Main` and `Basic`).
But structural recursion, well-founded recursion and `partial_fixpoint`
compile their code through the very same `addAndCompilePartialRec`
(`Lean.Elab.PreDefinition.Structural.Main`, `WF.Main` and
`PartialFixpoint.Main`), so every computable recursive definition has a
`.partial` twin beside its kernel-checked value (`shouldGenCodeFor` gates
the twin: not a theorem, not `noncomputable`) -- `State.pipe_end_live` was
the first one an `isPartial` arm refused when it was tried.  The
environment cannot tell a `partial def` from a recursive `def` without
encoding one toolchain's shape for it, an `opaque` public name beside a
`_unsafe_rec`.  `tools/check_lean_policy.py` refuses the keyword in the
source instead, which is the language's own record of it, and names the
bound neither half reaches.

Why the distinction matters here: a partial definition's public name is a
constant nothing can be proven about, and its compiled body is a
declaration the kernel checked only under the partial rules -- typed, with
no termination shown and nothing tying it to the public name.  A trace
runner folding one would print verdicts resting on the second, which is
what guard G1 exists to prevent. -/
def auditEnvironment : CommandElabM Unit := do
  let env ← getEnv
  let mut declarations := 0
  let mut theorems := 0
  for (n, ci) in env.constants.toList do
    if isProjectModule (declarationModule env n) then
      declarations := declarations + 1
      if ci.isTheorem then theorems := theorems + 1
      if ci.isAxiom then
        throwError "lean policy: project axiom {n} is forbidden"
      if ci.isUnsafe then
        throwError "lean policy: unsafe declaration {n} is forbidden"
      if let some implementation := Compiler.getImplementedBy? env n then
        throwError "lean policy: runtime substitution on {n} uses {implementation}"
      if isExtern env n then
        throwError "lean policy: external implementation on {n} is forbidden"
      let axs ← liftCoreM (collectAxioms n)
      for ax in axs do
        unless allowed_axioms.contains ax do
          throwError "lean policy: {n} depends on forbidden axiom {ax}"
  let modules := (env.header.moduleNames.push env.mainModule).filter isProjectModule
  let report := Json.mkObj [
    ("modules", toJson (modules.map Name.toString)),
    ("declarations", toJson declarations), ("theorems", toJson theorems)]
  logInfo m!"LEAN_POLICY_REPORT {report.compress}"

/-- A theorem's name alone is insufficient: pin its entire type to a fully
qualified public contract, including every quantified input and premise. -/
elab "#pin_theorem " decl:ident " : " expected:term : command => do
  let name ← liftCoreM (realizeGlobalConstNoOverloadWithInfo decl)
  let env ← getEnv
  let some info := env.find? name | throwError "lean policy: missing theorem {name}"
  unless info.isTheorem do
    throwError "lean policy: pinned declaration {name} is not a theorem"
  liftTermElabM do
    let expectedType ← Term.elabType expected
    Term.synthesizeSyntheticMVarsNoPostponing
    let expectedType ← instantiateMVars expectedType
    if expectedType.hasMVar then
      throwError "lean policy: expected statement contains unresolved metavariables"
    unless ← isDefEq info.type expectedType do
      throwError "lean policy: statement mismatch for {name}; expected {expectedType}, found {info.type}"

end LinuxProcessSemantics.LinuxProcessSem.Checks.Policy
