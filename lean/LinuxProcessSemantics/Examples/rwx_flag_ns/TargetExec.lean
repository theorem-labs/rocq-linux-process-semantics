import LinuxProcessSemantics.Common.PropExec
import LinuxProcessSemantics.Common.ExitSim
import LinuxProcessSemantics.Examples.rwx_flag_ns.rwx_flag_ns_code

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! The target's six actual instructions, through the production decoder
and effect interpreter. The store permission is checked against the
generated image; the load reads the byte just stored. The derivation is
independent of the starting integer-register map and memory overlay, so the final
initial-state theorem does not need a restriction on the process input.

`target_exit` twins `rwx_flag_ns_target.v`'s `target_wexit`, and
`rwx_flag_ns_defs.v`'s `target_store_ok` is answered by the generated
`target_store_flag` fact of `rwx_flag_ns_code`.
-/

namespace LinuxProcessSemantics.Examples.rwx_flag_ns.TargetExec

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Examples.rwx_flag_ns.TargetMemImage
open LinuxProcessSemantics.Examples.rwx_flag_ns.rwx_flag_ns_code

private def regs1 (r : bvmap 5 word) : bvmap 5 word := bvmap_set 10 0x1002000 r
private def regs2 (r : bvmap 5 word) : bvmap 5 word := bvmap_set 11 5 (regs1 r)
private def regs4 (r : bvmap 5 word) : bvmap 5 word := bvmap_set 10 5 (regs2 r)
private def regs5 (r : bvmap 5 word) : bvmap 5 word := bvmap_set 17 93 (regs4 r)
private def flag_mem (m : word → Option byte) : word → Option byte :=
  write_to_mem m 0x10021a8 [5]

private theorem step_1001190 (r : bvmap 5 word) (m rom : word → Option byte) :
    step target_segs (mkst r 0x1001190 m rom) =
      MachineOk (mkst (regs1 r) 0x1001194 m rom) := by
  rw [step_of_fetch target_segs (mkst r 0x1001190 m rom) 0x01002537 TF_1001190]
  apply decode_exec_of_interp _ _ _ _ _ _ _ _ _ (.Lui 10 0x1002)
    (by decide +kernel) TD_1001190
  rfl

private theorem step_1001194 (r : bvmap 5 word) (m rom : word → Option byte) :
    step target_segs (mkst (regs1 r) 0x1001194 m rom) =
      MachineOk (mkst (regs2 r) 0x1001198 m rom) := by
  rw [step_of_fetch target_segs (mkst (regs1 r) 0x1001194 m rom) 0x00500593 TF_1001194]
  apply decode_exec_of_interp _ _ _ _ _ _ _ _ _ (.OpImm .ALU_ADD 11 0 5)
    (by decide +kernel) TD_1001194
  rfl

private theorem step_1001198 (r : bvmap 5 word) (m rom : word → Option byte) :
    step target_segs (mkst (regs2 r) 0x1001198 m rom) =
      MachineOk (mkst (regs2 r) 0x100119c (flag_mem m) rom) := by
  rw [step_of_fetch target_segs (mkst (regs2 r) 0x1001198 m rom) 0x1ab50423 TF_1001198]
  apply decode_exec_of_interp _ _ _ _ _ _ _ _ _ (.Store .SZ1 10 11 0x1a8)
    (by decide +kernel) TD_1001198
  have hr10 : reg_get (regs2 r) 10 = (0x1002000 : word) := by
    simp [reg_get, regs2, regs1]
  have hr11 : reg_get (regs2 r) 11 = (5 : word) := by
    simp [reg_get, regs2]
  simp only [exec, rget, is_x0, hr10, hr11]
  change interp_eff target_segs
      (.EStore 8 0x10021a8 5 (.EDone (core.Core (regs2 r) bvmap_empty 0x100119c 0 none))) m = _
  exact interp_store target_segs 8 0x10021a8 5 _ m
    (store_ok_of_empty target_segs m 0x10021a8 1 target_store_flag)

private theorem step_100119c (r : bvmap 5 word) (m rom : word → Option byte) :
    step target_segs (mkst (regs2 r) 0x100119c (flag_mem m) rom) =
      MachineOk (mkst (regs4 r) 0x10011a0 (flag_mem m) rom) := by
  rw [step_of_fetch target_segs (mkst (regs2 r) 0x100119c (flag_mem m) rom)
    0x1a854503 TF_100119c]
  apply decode_exec_of_interp _ _ _ _ _ _ _ _ _ (.Load .SZ1 false 10 10 0x1a8)
    (by decide +kernel) TD_100119c
  have hr10 : reg_get (regs2 r) 10 = (0x1002000 : word) := by
    simp [reg_get, regs2, regs1]
  simp only [exec, rget, is_x0, hr10]
  change interp_eff target_segs
      (.ELoad 8 0x10021a8 (fun v => .EDone
        (core.Core (bvmap_set 10 (zext 64 v) (regs2 r)) bvmap_empty 0x10011a0 0 none)))
      (flag_mem m) = _
  exact interp_load target_segs 8 0x10021a8 [5] _ _ (flag_mem m)
    (read_written_byte target_segs m 0x10021a8 5) rfl

private theorem step_10011a0 (r : bvmap 5 word) (m rom : word → Option byte) :
    step target_segs (mkst (regs4 r) 0x10011a0 (flag_mem m) rom) =
      MachineOk (mkst (regs5 r) 0x10011a4 (flag_mem m) rom) := by
  rw [step_of_fetch target_segs (mkst (regs4 r) 0x10011a0 (flag_mem m) rom)
    0x05d00893 TF_10011a0]
  apply decode_exec_of_interp _ _ _ _ _ _ _ _ _ (.OpImm .ALU_ADD 17 0 93)
    (by decide +kernel) TD_10011a0
  rfl

private theorem step_10011a4 (r : bvmap 5 word) (m rom : word → Option byte) :
    step target_segs (mkst (regs5 r) 0x10011a4 (flag_mem m) rom) =
      MachineOk { mkst (regs5 r) 0x10011a4 (flag_mem m) rom with
        ms_svc_pending := some 93 } := by
  rw [step_of_fetch target_segs (mkst (regs5 r) 0x10011a4 (flag_mem m) rom)
    0x00000073 TF_10011a4]
  have hr17 : reg_get (regs5 r) 17 = (93 : word) := by simp [reg_get, regs5]
  change MachineOk { mkst (regs5 r) 0x10011a4 (flag_mem m) rom with
    ms_svc_pending := some (reg_get (regs5 r) 17) } = _
  rw [hr17]

theorem target_to_exit (r : bvmap 5 word) (m rom : word → Option byte) :
    to_exit target_segs 5 (mkst r 0x1001190 m rom) := by
  apply to_exit.te_step _ _ rfl (step_1001190 r m rom)
  apply to_exit.te_step _ _ rfl (step_1001194 r m rom)
  apply to_exit.te_step _ _ rfl (step_1001198 r m rom)
  apply to_exit.te_step _ _ rfl (step_100119c r m rom)
  apply to_exit.te_step _ _ rfl (step_10011a0 r m rom)
  apply to_exit.te_step _ _ rfl (step_10011a4 r m rom)
  apply to_exit.te_here _ 93 rfl
  · exact Or.inl (by decide +kernel)
  · simp [ms_gpr, mkst, reg_get, regs5, regs4, Z_to_bv]

theorem target_exit (sp : word) (argv envp : List (List byte)) (uid hwcap : word)
    (draw : EntryDraw) :
    to_exit Target.loaded_segments 5
      (init_machine_state Target.loaded_segments Target.init_pc Target.phdrs sp draw argv envp uid hwcap) := by
  rw [init_mkst]
  exact target_to_exit _ _ _

end LinuxProcessSemantics.Examples.rwx_flag_ns.TargetExec
