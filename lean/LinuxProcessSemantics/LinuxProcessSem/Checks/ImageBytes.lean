import LinuxProcessSemantics.Common.ImageBytes

/-! Concrete rejection checks for the ASCII certificate boundary.

These cases pin the existing hex/chunk reader's answers, including its
per-chunk floor division for an odd trailing nybble. The image generator
deliberately accepts a narrower input syntax (complete lowercase pairs).
-/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.ImageBytes

open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.Common.ImageBytes

theorem lowercase_pair_read : hex_byte_at "af" 0 = some 0xaf := by decide +kernel
theorem wrong_pair_value_rejected : hex_byte_at "af" 0 ≠ some 0xae := by decide +kernel
theorem uppercase_nybble_declined : hex_byte_at "aF" 0 = none := by decide +kernel
theorem uppercase_not_normalized : hex_byte_at "aF" 0 ≠ some 0xaf := by decide +kernel
theorem invalid_ascii_declined : hex_byte_at "ag" 0 = none := by decide +kernel
theorem odd_pair_declined : hex_byte_at "a" 0 = none := by decide +kernel
theorem invalid_nybble_not_zero : hex_chars_byte_at ['g', '5'] 0 ≠ some 0 := by decide +kernel
theorem odd_pair_not_padded : hex_chars_byte_at ['a'] 0 ≠ some 0xa0 := by decide +kernel

theorem chunk_order_read :
    ascii_segment_read_bytes [['1', '3'], ['7', '3']] 0 2 = some [0x13, 0x73] := by decide +kernel
theorem reversed_chunk_order_rejected :
    ascii_segment_read_bytes [['1', '3'], ['7', '3']] 0 2 ≠ some [0x73, 0x13] := by decide +kernel

theorem separate_chunks_read : segment_read_bytes ["ab0", "cd"] 0 2 = some [0xab, 0xcd] := by
  decide +kernel

theorem dangling_nybble_not_carried :
    segment_read_bytes ["ab0", "cd"] 0 2 ≠ some [0xab, 0x0c] := by decide +kernel

theorem ascii_bridge_preserves_odd_chunks :
    segment_read_bytes ["ab0", "cd"] 0 2 =
      ascii_segment_read_bytes [['a', 'b', '0'], ['c', 'd']] 0 2 := by
  exact segment_read_bytes_ascii [['a', 'b', '0'], ['c', 'd']] (by
    intro cs h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> decide +kernel) 0 2

theorem utf8_continuation_not_hex : hex_byte_at "aé" 0 = none := by decide +kernel
theorem ascii_bridge_condition_holds :
    (['a', '5'].all fun c => c.utf8Size == 1) = true := by decide +kernel
theorem non_ascii_bridge_condition_fails :
    (['a', 'é'].all fun c => c.utf8Size == 1) = false := by decide +kernel
theorem non_ascii_certificate_rejected :
    (['a', 'é'].all fun c => c.utf8Size == 1) ≠ true := by decide +kernel

-- U+0130 has low byte 0x30. Omitting the ASCII premise would therefore
-- invent the byte 0x01 although the actual UTF-8 starts with invalid 0xc4.
theorem truncated_character_helper_can_read :
    hex_chars_byte_at ['İ', '1'] 0 = some 0x01 := by decide +kernel
theorem actual_utf8_does_not_read_that_byte :
    hex_byte_at "İ1" 0 ≠ some 0x01 := by decide +kernel
theorem truncating_character_requires_failed_premise :
    (['İ', '1'].all fun c => c.utf8Size == 1) ≠ true := by decide +kernel

theorem header_read_in_bounds :
    (ascii_segment_read_bytes [['a', 'b', 'c', 'd']] 0 2).isSome = true := by
  exact ascii_segment_read_bytes_single_isSome _ (by decide +kernel) 0 2 (by decide +kernel)

theorem header_past_end_rejected :
    (ascii_segment_read_bytes [['a', 'b', 'c', 'd']] 0 3).isSome ≠ true := by decide +kernel

end LinuxProcessSemantics.LinuxProcessSem.Checks.ImageBytes
