import OssFuzzTheorems.libreac.fuzz_knock.Statements
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_heard
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_step
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.LLVMFuzzerTestOneInput
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.memset
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_init

/-! # The axiom walk

Printed at every build of this module. Each theorem below must depend on
`propext`, `Classical.choice` and `Quot.sound` and on nothing else: no
`sorryAx`, no `axiom` of this project, no `Lean.ofReduceBool` (which is what a
`native_decide` leaves behind).

`#print axioms`, not a grep for `sorry`, is the gate: in Lean `stop` is
`repeat sorry`, so a file can be free of the word and still carry the axiom. -/

-- The image of `fuzz_knock.plain` is well formed.
#print axioms OssFuzzTheorems.libreac.fuzz_knock.Images.plain_wf
#print axioms OssFuzzTheorems.libreac.fuzz_knock.Images.ubsan_wf

-- The released statement is the model's own `halts_allowed_T_scfg_budgets`.
#print axioms OssFuzzTheorems.Core.Shapes.halts_within_budget_is_lps
#print axioms OssFuzzTheorems.Core.Shapes.halts_may_fail_is_lps
#print axioms OssFuzzTheorems.Core.Shapes.agrees_in_is_lps

-- The program functions converted in this slice.
#print axioms
  OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_heard.reac_knock_heard_holds
#print axioms
  OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_step.reac_knock_step_holds
#print axioms
  OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.LLVMFuzzerTestOneInput.knock_big_holds
#print axioms
  OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.memset.memset_holds
#print axioms
  OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_init.reac_knock_init_holds
