-- Ports rocq-linux-process-semantics f1006fe8:theories/EquivalenceDefinition/Equivalence.v
import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.Base
import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ErrorFree
import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.Scfg
import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.Budgets
import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.Va

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058
divergence: bugs/accept-queue-cannot-run-out.md -- inherited
divergence: bugs/va-size-declines-every-non-sv48-run.md -- inherited -/

/-! # The program-equivalence contract

The split keeps each port ticket's additions in its own part, so independent
ports do not edit the same declaration file. -/
