import LinuxProcessSemantics.LinuxProcessSem.Run
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude

/-! Entry regressions for the pilot's reference update.

These inspect initialized process memory, so an auxv helper that serializes
the right value cannot hide initialization using a fixed capability word.
The reference is `StackLayout.auxv_entries` and `Run.init_config` at
7f386a77d4d3877f162c91f06b7e4fcc1d998e61. The fixture has argc, two argv
slots and one envp slot before auxv; the HWCAP value begins at byte 88.
-/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.PilotEntry

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude

def capability_input (hwcap : word) : ProcInput :=
  { demo_input [] IEof with in_argv := [[]], in_hwcap := hwcap }

def capability_config (hwcap : word) : config :=
  init_config [] 0 demo_phdrs demo_sp 0 0 demo_draw demo_limit (capability_input hwcap)

theorem capability_entry_present (hwcap : word) :
    (auxv_entries demo_phdrs 0 demo_uid hwcap)[3]? = some (AT_HWCAP, hwcap) := rfl

/-- Literal expectations also pin the tag and common capability bits;
comparing only against the model's own constants would miss their drift. -/
theorem scalar_capability_pair :
    ov_read_bytes [] (capability_config hwcap_rv64gc).cfg_ms.ms_mem (demo_sp + 80) 16 =
      some [16, 0, 0, 0, 0, 0, 0, 0, 0x2d, 0x11, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem vector_capability_pair :
    ov_read_bytes [] (capability_config hwcap_rv64gcv).cfg_ms.ms_mem (demo_sp + 80) 16 =
      some [16, 0, 0, 0, 0, 0, 0, 0, 0x2d, 0x11, 0x20, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem wrong_capability_tag_rejected :
    (capability_config hwcap_rv64gc).cfg_ms.ms_mem (demo_sp + 80) ≠ some 17 := by
  decide +kernel

theorem wrong_shared_capability_bit_rejected :
    (capability_config hwcap_rv64gc).cfg_ms.ms_mem (demo_sp + 88) ≠ some 0x2c := by
  decide +kernel

theorem scalar_capability_byte :
    (capability_config hwcap_rv64gc).cfg_ms.ms_mem (demo_sp + 90) = some 0 := by
  decide +kernel

theorem vector_capability_byte :
    (capability_config hwcap_rv64gcv).cfg_ms.ms_mem (demo_sp + 90) = some 0x20 := by
  decide +kernel

theorem scalar_cannot_publish_vector_bit :
    (capability_config hwcap_rv64gc).cfg_ms.ms_mem (demo_sp + 90) ≠ some 0x20 := by
  rw [scalar_capability_byte]
  decide +kernel

theorem vector_cannot_publish_fixed_scalar_mask :
    (capability_config hwcap_rv64gcv).cfg_ms.ms_mem (demo_sp + 90) ≠ some 0 := by
  rw [vector_capability_byte]
  decide +kernel

theorem missing_capability_entry_rejected :
    (auxv_entries demo_phdrs 0 demo_uid hwcap_rv64gc)[3]? ≠ some (AT_PAGESZ, 4096) := by
  decide +kernel

theorem capability_masks_preserve_layout :
    (auxv_bytes demo_phdrs 0 demo_uid hwcap_rv64gc).length =
      (auxv_bytes demo_phdrs 0 demo_uid hwcap_rv64gcv).length := by
  rw [length_auxv_bytes, length_auxv_bytes]

theorem old_auxv_extent_rejected :
    (auxv_bytes demo_phdrs 0 demo_uid hwcap_rv64gc).length ≠ 144 := by
  rw [length_auxv_bytes]
  decide +kernel

end LinuxProcessSemantics.LinuxProcessSem.Checks.PilotEntry
