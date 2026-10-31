-- Ports rocq-linux-process-semantics f1006fe8:theories/EquivalenceDefinition/MeasureLib.v
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.Prelude
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.FiniteSupport
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.GeoStdin
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.ScaleMix
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.GeoStdinVarying
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.Calibrated
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.GeoFile
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.GeoFileHeader
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.Alphabet
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.GeoFileHeaderAlphabet
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.GeoFileVarying
import LinuxProcessSemantics.EquivalenceDefinition.MeasureLib.FullSupport

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058 -/

/-! # EquivalenceDefinition.MeasureLib — the weight library a task writes against

Mirrors `theories/EquivalenceDefinition/MeasureLib.v`, which is 15,334 Rocq
lines in one file. The Lean port splits it into the twelve parts this module
imports, one per banner family of the Rocq file, so that two ports of different
families never edit the same file. Every declaration keeps its Rocq name, and
every part declares in the one namespace
`LinuxProcessSemantics.EquivalenceDefinition.MeasureLib`, so a reader of the
Rocq file finds each name where the Rocq file puts it.

The parts, with the Rocq lines each holds:

| part | Rocq lines | what it holds |
| --- | --- | --- |
| `Prelude` | 1256-1833 | the rational-arithmetic fills, `CoreDistribution`, `cd_lift`, `core_sum`, `qsum`, `core_indicator` |
| `FiniteSupport` | 1834-3005 | the finite-support combinator and `Example_D` |
| `GeoStdin` | 3006-3658 | geometric standard input over a fixed environment |
| `ScaleMix` | 3659-5259 | scaling and mixture, and `Worked_D` |
| `GeoStdinVarying` | 5260-7100 | geometric standard input over a varying launch-time environment |
| `Calibrated` | 7101-8095 | the calibrated mixture |
| `GeoFile` | 8096-8985 | geometric file contents over a fixed environment |
| `GeoFileHeader` | 8986-10041 | geometric file contents behind a fixed header |
| `Alphabet` | 10042-10455 | byte lists over a fixed alphabet |
| `GeoFileHeaderAlphabet` | 10456-11450 | the header family over an alphabet |
| `GeoFileVarying` | 11451-13129 | geometric file contents over a varying environment |
| `FullSupport` | 13130-15335 | the full-support base family |

WHO READS THIS. Nothing in `theories/` outside the demonstrations requires
`MeasureLib.v`: thirteen `.v` files name it at `f1006fe8`, and eleven of them
are demonstrations. Its consumers are submissions. On
`origin/ossv/recipes` of oss-verify-proofs-internal, 747 files reference it —
739 of them a `projects/<project>/<harness>/Distribution.v`, one per harness
over 298 projects — and they use 16 of its names, whose closure inside the file
is 64 declarations. That measurement is in the pull request that adds this
module.
-/
