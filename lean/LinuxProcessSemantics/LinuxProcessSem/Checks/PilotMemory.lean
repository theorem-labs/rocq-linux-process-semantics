import LinuxProcessSemantics.Common.WxExec

/-! Counterexamples to weakening the writable-code frame premises.

These fixtures exercise the production memory and fetch definitions. The
expected byte values are explicit, so changing a helper and its bridge
theorem together cannot make a stale instruction word pass these checks.
The stack cases also pin both ends of the zero-filled window and argc.
The relevant reference definitions are in `RiscvSemantics.v`, `StackLayout.v`,
`Run.v`, and `Common/WxExec.v` at commit `7f386a77d4d3877f162c91f06b7e4fcc1d998e61`.
-/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.PilotMemory

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.WxExec

def empty_mem : word → Option byte := fun _ => none

def rwx_seg : Segment :=
  ⟨0x1000, 16, "rwx", ["13055000730000000000000000000000"]⟩

theorem rwx_static_fetch : fetch_word_wx [rwx_seg] 0x1000 = some (0x00500513#32) := by
  decide +kernel

theorem rwx_not_immutable : fetch_word [rwx_seg] 0x1000 = none := by
  apply fetch_word_none_no_ro_exec
  decide +kernel

theorem data_store_keeps_code_clear :
    mem_clear (write_to_mem empty_mem 0x1008 [0xa5, 0x5a]) 0x1000 0x1008 := by
  apply mem_clear_wbytes
  · intro _ _
    rfl
  · exact Or.inl (by decide +kernel)
  · decide +kernel

theorem data_store_preserves_fetch :
    fetch_word_ov [rwx_seg] (write_to_mem empty_mem 0x1008 [0xa5, 0x5a]) 0x1000 =
      some (0x00500513#32) := by
  apply fetch_word_ov_of_wx _ _ _ _ 0x1000 0x1008 data_store_keeps_code_clear
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact rwx_static_fetch

theorem code_store_changes_fetch :
    fetch_word_ov [rwx_seg] (write_to_mem empty_mem 0x1000 [0xef]) 0x1000 =
      some (0x005005ef#32) := by
  decide +kernel

theorem stale_static_fetch_rejected :
    fetch_word_ov [rwx_seg] (write_to_mem empty_mem 0x1000 [0xef]) 0x1000 ≠
      some (0x00500513#32) := by
  rw [code_store_changes_fetch]
  decide +kernel

theorem overlapping_write_invalidates_frame :
    ¬ mem_clear (write_to_mem empty_mem 0x1000 [0xef]) 0x1000 0x1008 := by
  intro h
  have ha := h 0x1000 (by decide +kernel)
  change some (0xef#8) = none at ha
  cases ha

theorem wrapping_write_touches_zero :
    write_to_mem empty_mem 0xffffffffffffffff [1, 2] 0 = some 2 := by
  decide +kernel

theorem last_nonwrapping_byte_preserves_frame :
    mem_clear (write_to_mem empty_mem 0xffffffffffffffff [1]) 0 4 := by
  apply mem_clear_wbytes
  · intro _ _
    rfl
  · exact Or.inl (by decide +kernel)
  · decide +kernel

theorem wrapping_write_invalidates_frame :
    ¬ mem_clear (write_to_mem empty_mem 0xffffffffffffffff [1, 2]) 0 4 := by
  intro h
  have hz := h 0 (by decide +kernel)
  rw [wrapping_write_touches_zero] at hz
  cases hz

/-- Integer range disjointness alone does not justify the frame: the
byte-writing operation uses wrapping machine addresses. -/
theorem unchecked_wrap_frame_rule_rejected :
    ¬ (∀ (m : word → Option byte) (addr : word) (bs : List byte) (lo hi : Int),
      mem_clear m lo hi →
      (hi ≤ bv_unsigned addr ∨ bv_unsigned addr + (bs.length : Int) ≤ lo) →
      mem_clear (write_to_mem m addr bs) lo hi) := by
  intro h
  exact wrapping_write_invalidates_frame
    (h empty_mem 0xffffffffffffffff [1, 2] 0 4 (by intro _ _; rfl)
      (Or.inl (by decide +kernel)))

def test_ph : PhdrInfo := ⟨0x10040, 56, 1⟩
def test_sp : word := 0x7fff90000000
def test_argv : List (List byte) := [[0x61], [0x62], []]
def test_hwcap : word := 0x20112d
def test_draw : EntryDraw :=
  ⟨0x100f0e0d0c0b0a090807060504030201, fun a => bv_extract 0 8 a⟩
def test_stack : word → Option byte :=
  wrap_mem test_ph test_sp test_argv [] 0 test_hwcap test_draw

theorem argc_ignores_auxv_and_entry_draw (hwcap : word) (draw : EntryDraw) :
    ov_read_bytes [] (wrap_mem test_ph test_sp test_argv [] 0 hwcap draw) test_sp 8 =
      some [3, 0, 0, 0, 0, 0, 0, 0] := by
  rw [read_argc_ov [] test_ph test_sp test_argv [] 0 hwcap draw (by decide +kernel)]
  decide +kernel

theorem argc_three :
    ov_read_bytes [] test_stack test_sp 8 = some [3, 0, 0, 0, 0, 0, 0, 0] := by
  exact argc_ignores_auxv_and_entry_draw test_hwcap test_draw

theorem wrong_argc_rejected :
    ov_read_bytes [] test_stack test_sp 8 ≠ some [2, 0, 0, 0, 0, 0, 0, 0] := by
  rw [argc_three]
  decide +kernel

theorem stack_zero_window_first_byte : test_stack 0x7fff8f800000 = some 0 := by
  decide +kernel

theorem stack_zero_window_last_byte : test_stack 0x7fff8fffffff = some 0 := by
  decide +kernel

theorem stack_zero_window_below : test_stack 0x7fff8f7fffff = none := by
  decide +kernel

theorem missing_stack_backing_rejected : test_stack 0x7fff8f800000 ≠ none := by
  rw [stack_zero_window_first_byte]
  decide +kernel

theorem enlarged_stack_window_rejected : test_stack 0x7fff8f7fffff ≠ some 0 := by
  rw [stack_zero_window_below]
  decide +kernel

theorem stack_pointer_is_argc : test_stack test_sp = some 3 := by
  decide +kernel

theorem zeroing_argc_rejected : test_stack test_sp ≠ some 0 := by
  rw [stack_pointer_is_argc]
  decide +kernel

/- The written block ends at offset 0xe8, inside its last mapped page.
Use nonzero entropy and address-dependent slack so a zero-filled or
block-truncated replacement cannot pass these checks. -/
theorem written_stack_block_length :
    (build_stack_bytes test_ph test_sp test_argv [] 0 test_hwcap test_draw).length = 0xe8 := by
  decide +kernel

theorem entropy_draw_is_materialized :
    ov_read_bytes [] test_stack (test_sp + 0xd8) 16 =
      some [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] := by
  decide +kernel

theorem auxv_random_points_to_entropy :
    ov_read_bytes [] test_stack (test_sp + 0xb0) 16 =
      some [25, 0, 0, 0, 0, 0, 0, 0, 0xd8, 0, 0, 0x90, 0xff, 0x7f, 0, 0] := by
  decide +kernel

theorem pre_hwcap_random_pointer_rejected :
    ov_read_bytes [] test_stack (test_sp + 0xb8) 8 ≠
      some [0xc8, 0, 0, 0x90, 0xff, 0x7f, 0, 0] := by
  decide +kernel

theorem zeroed_entropy_rejected : test_stack (test_sp + 0xd8) ≠ some 0 := by
  decide +kernel

theorem stack_page_tail_first_byte : test_stack (test_sp + 0xe8) = some 0xe8 := by
  decide +kernel

theorem stack_page_tail_next_byte : test_stack (test_sp + 0xe9) = some 0xe9 := by
  decide +kernel

theorem block_truncated_tail_rejected : test_stack (test_sp + 0xe8) ≠ none := by
  rw [stack_page_tail_first_byte]
  decide +kernel

theorem zeroed_page_tail_rejected : test_stack (test_sp + 0xe8) ≠ some 0 := by
  rw [stack_page_tail_first_byte]
  decide +kernel

theorem reused_page_tail_byte_rejected : test_stack (test_sp + 0xe9) ≠ some 0xe8 := by
  rw [stack_page_tail_next_byte]
  decide +kernel

theorem stack_page_tail_last_byte : test_stack (test_sp + 0xfff) = some 0xff := by
  decide +kernel

theorem stack_page_top_unmapped : test_stack (test_sp + 0x1000) = none := by
  decide +kernel

theorem enlarged_stack_page_rejected : test_stack (test_sp + 0x1000) ≠ some 0 := by
  rw [stack_page_top_unmapped]
  decide +kernel

end LinuxProcessSemantics.LinuxProcessSem.Checks.PilotMemory
