import LinuxProcessSemantics.Riscv.Prelude
import LinuxProcessSemantics.Riscv.Instr
import LinuxProcessSemantics.Riscv.Decode
import LinuxProcessSemantics.Riscv.DecodeC
import LinuxProcessSemantics.Riscv.Sem
import LinuxProcessSemantics.LinuxProcessSem.BvBase
import LinuxProcessSemantics.LinuxProcessSem.MemImageType
import LinuxProcessSemantics.LinuxProcessSem.Fs
import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
import LinuxProcessSemantics.LinuxProcessSem.State
import LinuxProcessSemantics.LinuxProcessSem.Monad
import LinuxProcessSemantics.LinuxProcessSem.SysSimp
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei
import LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
-- Syscall twins are not listed here: the table above is generated from one
-- registry file per twin (tools/gen_lean_registry.py) and imports every twin
-- through Sys.Registry, and their Checks/Cases files are built by the module
-- glob and audited by Checks/All, so a port adds files and edits no import.
-- The base's own Cases modules stay listed, the table's pins among them.
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.SyscallTable
-- The checked table's pins, generated from the arm files under Checks/Arms/
-- (tools/gen_lean_checked.py); nothing imports them, so this line does.
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.CheckedTable
import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.StackLayout
import LinuxProcessSemantics.LinuxProcessSem.Run
import LinuxProcessSemantics.EquivalenceDefinition.Classifier
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.State
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Run
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Monad
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs
import LinuxProcessSemantics.EquivalenceDefinition.MustExit
import LinuxProcessSemantics.LinuxProcessSem.Checks.Examples
import LinuxProcessSemantics.LinuxProcessSem.StreamLaws
import LinuxProcessSemantics.LinuxProcessSem.Checks.OmniPilot
import LinuxProcessSemantics.LinuxProcessSem.Checks.PilotMemory
import LinuxProcessSemantics.LinuxProcessSem.Checks.PilotEntry
import LinuxProcessSemantics.LinuxProcessSem.Checks.ImageBytes
import LinuxProcessSemantics.Examples.rwx_flag_ns.Proof
import LinuxProcessSemantics.Examples.rwx_flag_ns.Checks
import LinuxProcessSemantics.LinuxProcessSem.Checks.ExitBridge
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Sys.Uapi
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Sys.Uapi.Fs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Sys.Uapi.Net
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Sys.Uapi.Sched
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Sys.Uapi.Time
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Sys.Uapi.Signal
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Sys.Uapi.Mm
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.BvBase
-- The RISC-V model's own witness files (slice ZR), ported from
-- rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Riscv*.v.
-- Nothing else imports them, so these lines do.
import LinuxProcessSemantics.LinuxProcessSem.Checks.RiscvAlignment
import LinuxProcessSemantics.LinuxProcessSem.Checks.RiscvSegmentChunks
import LinuxProcessSemantics.LinuxProcessSem.Checks.RiscvDefinedIllegal
import LinuxProcessSemantics.LinuxProcessSem.Checks.RiscvAtomicAlignment
import LinuxProcessSemantics.LinuxProcessSem.Checks.RiscvAccessReporting
import LinuxProcessSemantics.LinuxProcessSem.Checks.RiscvCompressedFetch
-- The in-Lean checks of the FP semantics; nothing else imports them.
import LinuxProcessSemantics.Riscv.FpuTests
-- canary: 2026-10-29-0602: the pipeline's daily proof that a one-line change merges unattended (lean-port-ops jobs/canary-job.sh)
