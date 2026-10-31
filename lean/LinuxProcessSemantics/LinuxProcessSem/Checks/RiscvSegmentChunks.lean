-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/RiscvSegmentChunks.v
import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics

/-! # Segment payload chunks are invisible to memory semantics

`elf-snapshot` divides a large logical ELF segment into bounded primitive
strings.  These checks pin the load and fetch behavior at the join: the
join is not a mapping or permission boundary. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.RiscvSegmentChunks

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics

def chunked_segment : Segment :=
  { seg_base := 0x100, seg_size := 5, seg_perms := "r-x",
    seg_bytes := ["1122", "334455"] }

def chunked_segments : List Segment := [chunked_segment]

theorem chunk_join_byte_before :
    segment_byte_at chunked_segment.seg_bytes 1 = some (Z_to_bv 8 0x22) := by
  rfl

theorem chunk_join_byte_after :
    segment_byte_at chunked_segment.seg_bytes 2 = some (Z_to_bv 8 0x33) := by
  rfl

theorem data_read_crosses_chunk_join :
    memory_read chunked_segments (Z_to_bv 64 0x101) 4 =
      some [Z_to_bv 8 0x22, Z_to_bv 8 0x33,
            Z_to_bv 8 0x44, Z_to_bv 8 0x55] := by
  rfl

theorem instruction_fetch_crosses_chunk_join :
    fetch_word chunked_segments (Z_to_bv 64 0x100) =
      some (Z_to_bv 32 0x44332211) := by
  rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.RiscvSegmentChunks
