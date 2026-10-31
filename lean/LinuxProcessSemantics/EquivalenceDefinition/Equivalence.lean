import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.Base
import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ErrorFree
import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.Scfg
import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.Budgets
import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.Va

/-! rocq-baseline: 1807c1e25ce12708f5cc85213f2df4bf03d978da
divergence: bugs/accept-queue-cannot-run-out.md -- inherited
divergence: bugs/va-size-declines-every-non-sv48-run.md -- inherited -/

/-! # The program-equivalence contract

The split keeps each port ticket's additions in its own part, so independent
ports do not edit the same declaration file. -/
