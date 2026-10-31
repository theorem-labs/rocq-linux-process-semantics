import LinuxProcessSemantics.Common.PropExec
import LinuxProcessSemantics.Common.WxExec
import LinuxProcessSemantics.Common.ExitSim
import LinuxProcessSemantics.Examples.rwx_flag_ns.rwx_flag_ns_code

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570
unported: argcN -- rwx_flag_ns_source.v's section definition; `source_exit` binds the loaded count as the machine expression `argc` rather than naming it
unported: envp_ptr -- rwx_flag_ns_source.v's section definition; `source_exit` keeps _start's computed pointer as the machine expression `ep`, so `envp_ptr_eq` needs no twin
unported: stext_lo -- rwx_flag_ns_defs.v's .text bound; the `mem_clear` frame premise names the literal 0x10078
unported: stext_hi -- rwx_flag_ns_defs.v's .text bound; the `mem_clear` frame premise names the literal 0x100e4 -/

/-! Symbolic execution of the unchanged source snapshot.

The stack pointer, argument/environment bytes, hardware-capability word and
both entry byte draws remain quantified.
The startup code's loaded count and computed pointer are retained as their
actual machine expressions: the exit proof does not need to identify the
pointer with a mathematical argv layout. Every load and store still executes.
The frame premise covers exactly the source text extent from the reference
`rwx_flag_ns_defs.v`; both stores preserve it by disjointness.

`source_exit` twins `rwx_flag_ns_source.v`'s `source_wexit`: the `to_wexit`
derivation with no output is this `to_exit` derivation. The private
`source_no_ro_exec` is `rwx_flag_ns_defs.v`'s lemma of that name, and that
file's `source_store_ok` is answered by the generated `source_store_environ`
and `source_store_flag` facts of `rwx_flag_ns_code`, one per store.
-/

namespace LinuxProcessSemantics.Examples.rwx_flag_ns.SourceExec

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.DecodeC
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.WxExec
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Examples.rwx_flag_ns.SourceMemImage
open LinuxProcessSemantics.Examples.rwx_flag_ns.rwx_flag_ns_code

private theorem source_no_ro_exec : no_ro_exec source_segs = true := by decide +kernel

private theorem decoded_step {regs regs' : bvmap 5 word} {pc pc' : word}
    {m m' rom : word → Option byte} {w : BitVec 32} {i : instr}
    (hc : mem_clear m 0x10078 0x100e4)
    (hlo : 0x10078 ≤ bv_unsigned pc) (hhi : bv_unsigned pc + 4 ≤ 0x100e4)
    (hf : fetch_word_wx source_segs pc = some w)
    (hne : is_ecall w = false) (hd : decode_any w = some (i, 4))
    (hi : interp_eff source_segs (exec 4 i (core.Core regs bvmap_empty pc 0 none)) m =
      MachineOk (core.Core regs' bvmap_empty pc' 0 none, m')) :
    RiscvSemantics.step source_segs (mkst regs pc m rom) =
      MachineOk (mkst regs' pc' m' rom) := by
  rw [step_of_fetch_ov source_segs (mkst regs pc m rom) w
    (fetch_word_none_no_ro_exec source_segs pc source_no_ro_exec)
    (fetch_word_ov_of_wx source_segs m pc w 0x10078 0x100e4 hc hlo hhi (by decide) hf)]
  exact decode_exec_of_interp source_segs regs regs' pc pc' m m' rom w i hne hd hi

private theorem ecall_step (regs : bvmap 5 word) (m rom : word → Option byte)
    (hc : mem_clear m 0x10078 0x100e4) (hr17 : reg_get regs 17 = (93 : word)) :
    RiscvSemantics.step source_segs (mkst regs 0x100a8 m rom) =
      MachineOk { mkst regs 0x100a8 m rom with ms_svc_pending := some 93 } := by
  rw [step_of_fetch_ov source_segs (mkst regs 0x100a8 m rom) 0x73
    (fetch_word_none_no_ro_exec source_segs 0x100a8 source_no_ro_exec)
    (fetch_word_ov_of_wx source_segs m 0x100a8 0x73 0x10078 0x100e4 hc
      (by decide) (by decide) (by decide) SF_100a8)]
  change MachineOk { mkst regs 0x100a8 m rom with
    ms_svc_pending := some (reg_get regs 17) } = _
  rw [hr17]

theorem source_exit (sp : word) (argv envp : List (List byte)) (uid hwcap : word)
    (draw : EntryDraw)
    (hlo : sp_window_lo ≤ bv_unsigned sp) (hhi : bv_unsigned sp ≤ sp_window_hi) :
    to_exit source_segs 5
      (init_machine_state source_segs Source.init_pc source_phdrs sp draw argv envp uid hwcap) := by
  let m0 := wrap_mem source_phdrs sp argv envp uid hwcap draw
  let rom := fun addr => match memory_read source_segs addr 1 with
    | some (b :: _) => some b | _ => none
  let argc := bv_extract 0 64 (le_bytes_to_word (word_le8 (len_word argv)))
  let shifted := alu64 .ALU_SLL argc (zext 64 (3 : BitVec 6))
  let ep := (sp + 8 + shifted) + 8
  let epBytes := Z_to_le_bytes 8 (bv_unsigned ep)
  let m1 := write_to_mem m0 0x100e8 epBytes
  let m2 := write_to_mem m1 0x100e4 [5]
  let r0 := regupd (regupd bvmap_empty 10 0) 2 sp
  let r1 := regupd r0 3 0x11078
  let r2 := regupd r1 3 0x108e5
  let r3 := regupd r2 10 argc
  let r4 := regupd r3 11 (sp + 8)
  let r5 := regupd r4 5 shifted
  let r6 := regupd r5 12 (sp + 8 + shifted)
  let r7 := regupd r6 12 ep
  let r8 := regupd r7 6 0x10094
  let r9 := regupd r8 6 0x100e8
  let r10 := regupd r9 1 0x100a4
  let r11 := regupd r10 15 0x10000
  let r12 := regupd r11 14 5
  let r13 := regupd r12 10 5
  let r14 := regupd r13 17 93
  have hc0 : mem_clear m0 0x10078 0x100e4 := by
    apply mem_clear_wrap
    unfold sp_window_lo at hlo
    unfold stack_max_size
    omega
  have hlen : epBytes.length = 8 := length_Z_to_le_bytes _ _
  have hc1 : mem_clear m1 0x10078 0x100e4 :=
    mem_clear_wbytes m0 0x100e8 epBytes _ _ hc0 (Or.inl (by decide))
      (by rw [hlen]; decide)
  have hc2 : mem_clear m2 0x10078 0x100e4 :=
    mem_clear_wbytes m1 0x100e4 [5] _ _ hc1 (Or.inl (by decide)) (by decide)
  have hargc : ov_read_bytes source_segs m0 sp 8 = some (word_le8 (len_word argv)) := by
    apply read_argc_ov
    unfold sp_window_hi bv_unsigned at hhi
    omega
  have h1 : RiscvSemantics.step source_segs (mkst r0 0x10078 m0 rom) =
      MachineOk (mkst r1 0x1007c m0 rom) := by
    apply decoded_step (pc := 0x10078) (w := 0x00001197) hc0 (by decide) (by decide) SF_10078 (by decide) SD_10078
    rfl
  have h2 : RiscvSemantics.step source_segs (mkst r1 0x1007c m0 rom) =
      MachineOk (mkst r2 0x10080 m0 rom) := by
    apply decoded_step (pc := 0x1007c) (w := 0x86d18193) hc0 (by decide) (by decide) SF_1007c (by decide) SD_1007c
    have hr : reg_get r1 3 = (0x11078 : word) := by simp [r1, reg_get, regupd]
    simp only [exec, rget, is_x0, hr]
    rfl
  have h3 : RiscvSemantics.step source_segs (mkst r2 0x10080 m0 rom) =
      MachineOk (mkst r3 0x10084 m0 rom) := by
    apply decoded_step (pc := 0x10080) (w := 0x00013503) hc0 (by decide) (by decide) SF_10080 (by decide) SD_10080
    have hr : reg_get r2 2 = sp := by simp [r2, r1, r0, reg_get, regupd]
    simp only [exec, rget, is_x0, hr]
    change interp_eff source_segs (.ELoad 64 (sp + 0)
      (fun v => .EDone (core.Core (regupd r2 10 v) bvmap_empty 0x10084 0 none))) m0 = _
    have hz : sp + (0 : word) = sp := BitVec.add_zero sp
    rw [hz]
    exact interp_load source_segs 64 sp (word_le8 (len_word argv))
      (fun v => .EDone (core.Core (regupd r2 10 v) bvmap_empty 0x10084 0 none))
      (core.Core r3 bvmap_empty 0x10084 0 none) m0 hargc rfl
  have h4 : RiscvSemantics.step source_segs (mkst r3 0x10084 m0 rom) =
      MachineOk (mkst r4 0x10088 m0 rom) := by
    apply decoded_step (pc := 0x10084) (w := 0x00810593) hc0 (by decide) (by decide) SF_10084 (by decide) SD_10084
    have hr : reg_get r3 2 = sp := by simp [r3, r2, r1, r0, reg_get, regupd]
    simp only [exec, rget, is_x0, hr]
    rfl
  have h5 : RiscvSemantics.step source_segs (mkst r4 0x10088 m0 rom) =
      MachineOk (mkst r5 0x1008c m0 rom) := by
    apply decoded_step (pc := 0x10088) (w := 0x00351293) hc0 (by decide) (by decide) SF_10088 (by decide) SD_10088
    have hr : reg_get r4 10 = argc := by simp [r4, r3, reg_get, regupd]
    simp only [exec, rget, is_x0, hr]
    rfl
  have h6 : RiscvSemantics.step source_segs (mkst r5 0x1008c m0 rom) =
      MachineOk (mkst r6 0x10090 m0 rom) := by
    apply decoded_step (pc := 0x1008c) (w := 0x00558633) hc0 (by decide) (by decide) SF_1008c (by decide) SD_1008c
    have hr11 : reg_get r5 11 = sp + 8 := by simp [r5, r4, reg_get, regupd]
    have hr5 : reg_get r5 5 = shifted := by simp [r5, reg_get, regupd]
    simp only [exec, rget, is_x0, hr11, hr5]
    rfl
  have h7 : RiscvSemantics.step source_segs (mkst r6 0x10090 m0 rom) =
      MachineOk (mkst r7 0x10094 m0 rom) := by
    apply decoded_step (pc := 0x10090) (w := 0x00860613) hc0 (by decide) (by decide) SF_10090 (by decide) SD_10090
    have hr : reg_get r6 12 = sp + 8 + shifted := by simp [r6, reg_get, regupd]
    simp only [exec, rget, is_x0, hr]
    rfl
  have h8 : RiscvSemantics.step source_segs (mkst r7 0x10094 m0 rom) =
      MachineOk (mkst r8 0x10098 m0 rom) := by
    apply decoded_step (pc := 0x10094) (w := 0x00000317) hc0 (by decide) (by decide) SF_10094 (by decide) SD_10094
    rfl
  have h9 : RiscvSemantics.step source_segs (mkst r8 0x10098 m0 rom) =
      MachineOk (mkst r9 0x1009c m0 rom) := by
    apply decoded_step (pc := 0x10098) (w := 0x05430313) hc0 (by decide) (by decide) SF_10098 (by decide) SD_10098
    have hr : reg_get r8 6 = (0x10094 : word) := by simp [r8, reg_get, regupd]
    simp only [exec, rget, is_x0, hr]
    rfl
  have h10 : RiscvSemantics.step source_segs (mkst r9 0x1009c m0 rom) =
      MachineOk (mkst r9 0x100a0 m1 rom) := by
    apply decoded_step (pc := 0x1009c) (w := 0x00c33023) hc0 (by decide) (by decide) SF_1009c (by decide) SD_1009c
    have hr6 : reg_get r9 6 = (0x100e8 : word) := by simp [r9, reg_get, regupd]
    have hr12 : reg_get r9 12 = ep := by simp [r9, r8, r7, reg_get, regupd]
    simp only [exec, rget, is_x0, hr6, hr12]
    change interp_eff source_segs (.EStore 64 0x100e8 ep
      (.EDone (core.Core r9 bvmap_empty 0x100a0 0 none))) m0 = _
    exact interp_store _ 64 0x100e8 ep _ m0
      (store_ok_of_empty _ _ _ _ source_store_environ)
  have h11 : RiscvSemantics.step source_segs (mkst r9 0x100a0 m1 rom) =
      MachineOk (mkst r10 0x100d0 m1 rom) := by
    apply decoded_step (pc := 0x100a0) (w := 0x030000ef) hc1 (by decide) (by decide) SF_100a0 (by decide) SD_100a0
    rfl
  have h12 : RiscvSemantics.step source_segs (mkst r10 0x100d0 m1 rom) =
      MachineOk (mkst r11 0x100d4 m1 rom) := by
    apply decoded_step (pc := 0x100d0) (w := 0x000107b7) hc1 (by decide) (by decide) SF_100d0 (by decide) SD_100d0
    rfl
  have h13 : RiscvSemantics.step source_segs (mkst r11 0x100d4 m1 rom) =
      MachineOk (mkst r12 0x100d8 m1 rom) := by
    apply decoded_step (pc := 0x100d4) (w := 0x00500713) hc1 (by decide) (by decide) SF_100d4 (by decide) SD_100d4
    rfl
  have h14 : RiscvSemantics.step source_segs (mkst r12 0x100d8 m1 rom) =
      MachineOk (mkst r12 0x100dc m2 rom) := by
    apply decoded_step (pc := 0x100d8) (w := 0x0ee78223) hc1 (by decide) (by decide) SF_100d8 (by decide) SD_100d8
    have hr15 : reg_get r12 15 = (0x10000 : word) := by simp [r12, r11, reg_get, regupd]
    have hr14 : reg_get r12 14 = (5 : word) := by simp [r12, reg_get, regupd]
    simp only [exec, rget, is_x0, hr15, hr14]
    exact interp_store _ 8 0x100e4 5 _ m1
      (store_ok_of_empty _ _ _ _ source_store_flag)
  have h15 : RiscvSemantics.step source_segs (mkst r12 0x100dc m2 rom) =
      MachineOk (mkst r13 0x100e0 m2 rom) := by
    apply decoded_step (pc := 0x100dc) (w := 0x0e47c503) hc2 (by decide) (by decide) SF_100dc (by decide) SD_100dc
    have hr15 : reg_get r12 15 = (0x10000 : word) := by simp [r12, r11, reg_get, regupd]
    simp only [exec, rget, is_x0, hr15]
    exact interp_load _ 8 0x100e4 [5] _ _ m2 (read_written_byte _ m1 _ 5) (by rfl)
  have h16 : RiscvSemantics.step source_segs (mkst r13 0x100e0 m2 rom) =
      MachineOk (mkst r13 0x100a4 m2 rom) := by
    apply decoded_step (pc := 0x100e0) (w := 0x00008067) hc2 (by decide) (by decide) SF_100e0 (by decide) SD_100e0
    have hr1 : reg_get r13 1 = (0x100a4 : word) := by
      simp [r13, r12, r11, r10, reg_get, regupd]
    simp only [exec, rget, is_x0, hr1]
    rfl
  have h17 : RiscvSemantics.step source_segs (mkst r13 0x100a4 m2 rom) =
      MachineOk (mkst r14 0x100a8 m2 rom) := by
    apply decoded_step (pc := 0x100a4) (w := 0x05d00893) hc2 (by decide) (by decide) SF_100a4 (by decide) SD_100a4
    rfl
  let final := { mkst r14 0x100a8 m2 rom with ms_svc_pending := some 93 }
  have h18 : RiscvSemantics.step source_segs (mkst r14 0x100a8 m2 rom) = MachineOk final := by
    exact ecall_step r14 m2 rom hc2 (by simp [r14, reg_get, regupd])
  have hend : to_exit source_segs 5 final :=
    to_exit.te_here final 93 rfl (Or.inl (by decide))
      (by simp [final, mkst, ms_gpr, r14, r13, reg_get, regupd, Z_to_bv])
  rw [init_mkst]
  exact to_exit.te_step _ _ rfl h1 <| to_exit.te_step _ _ rfl h2 <|
    to_exit.te_step _ _ rfl h3 <| to_exit.te_step _ _ rfl h4 <|
    to_exit.te_step _ _ rfl h5 <| to_exit.te_step _ _ rfl h6 <|
    to_exit.te_step _ _ rfl h7 <| to_exit.te_step _ _ rfl h8 <|
    to_exit.te_step _ _ rfl h9 <| to_exit.te_step _ _ rfl h10 <|
    to_exit.te_step _ _ rfl h11 <| to_exit.te_step _ _ rfl h12 <|
    to_exit.te_step _ _ rfl h13 <| to_exit.te_step _ _ rfl h14 <|
    to_exit.te_step _ _ rfl h15 <| to_exit.te_step _ _ rfl h16 <|
    to_exit.te_step _ _ rfl h17 <| to_exit.te_step _ _ rfl h18 hend

end LinuxProcessSemantics.Examples.rwx_flag_ns.SourceExec
