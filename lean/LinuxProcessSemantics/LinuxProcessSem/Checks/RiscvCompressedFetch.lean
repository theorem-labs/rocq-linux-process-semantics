-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/RiscvCompressedFetch.v
import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
import LinuxProcessSemantics.Riscv.DecodeC

/-! # LinuxProcessSem.Checks.RiscvCompressedFetch — RVC length-correct fetch checks

Regression checks for the halfword-granular instruction fetch
(`fetch_half`/`fetch_tail`, used by `step` when the four-byte
`fetch_word` fast path fails).  The case these pin: a compressed
(2-byte) instruction in the LAST two bytes of an executable segment,
which a fetch that always read four bytes would fault on.  It is
fetched from exactly the two bytes it occupies.

The fixtures use minimally-sized executable segments so the boundary
is exact: a 2-byte segment can back a compressed instruction but
never a four-byte read, which is precisely the case `fetch_word`
could not handle. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.RiscvCompressedFetch

open LinuxProcessSemantics.Riscv
open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.DecodeC
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics

-- NOT opened: `Sem`, whose `step` would shadow `RiscvSemantics.step`,
-- the function every `step` check below is about.

/-- A 2-byte executable segment holding `c.li a0, 5` (= 0x4515, bytes
15 45 little-endian).  There is no room for a four-byte read. -/
def cli_segment : Segment := {
  seg_base := 0x100,
  seg_size := 2,
  seg_perms := "r-x",
  seg_bytes := ["1545"] }
def cli_segments : List Segment := [cli_segment]

/-- A 2-byte executable segment holding only the LOW half of a 32-bit
`addi x0,x0,0` (0x00000013, low half 0x0013, bytes 13 00).  The low
two bits are 0b11, so this parcel announces a 32-bit instruction
whose second parcel is not mapped. -/
def trunc32_segment : Segment := {
  seg_base := 0x100,
  seg_size := 2,
  seg_perms := "r-x",
  seg_bytes := ["1300"] }
def trunc32_segments : List Segment := [trunc32_segment]

/-- A 4-byte executable segment whose first parcel is `c.li a0, 5` and
whose SECOND parcel is nonzero (ff ff).  Both fetches are defined
here; they differ in the (decoder-dead) upper 16 bits. -/
def cli_pad_segment : Segment := {
  seg_base := 0x100,
  seg_size := 4,
  seg_perms := "r-x",
  seg_bytes := ["1545ffff"] }
def cli_pad_segments : List Segment := [cli_pad_segment]

/-- A 4-byte executable segment holding the full 32-bit `addi x0,x0,0`. -/
def addi_segment : Segment := {
  seg_base := 0x100,
  seg_size := 4,
  seg_perms := "r-x",
  seg_bytes := ["13000000"] }
def addi_segments : List Segment := [addi_segment]

/-- Rocq keeps the (unused) segment argument so every fixture reads the
same way; the Lean twin keeps it for the same reason. -/
def st0 (_segs : List Segment) (pc : word) : machine_state := {
  ms_regs := bvmap_empty, ms_fregs := bvmap_empty,
  ms_pc_val := pc,
  ms_svc_pending := none,
  ms_resv := none, ms_fcsr := Z_to_bv 32 0,
  ms_mem := fun _ => none,
  ms_rom := fun _ => none }

/- ================================================================= -/
/- THE FIX: a compressed instruction in the last 2 bytes of a segment -/
/- ================================================================= -/

/-- The four-byte fast path cannot read this instruction — only two
bytes are mapped. -/
theorem cli_fetch_word_fails :
    fetch_word cli_segments (Z_to_bv 64 0x100) = none := by
  decide +kernel

/-- The length-correct fetch reads exactly the two-byte parcel. -/
theorem cli_fetch_tail_ok :
    fetch_tail cli_segments (Z_to_bv 64 0x100) = some (Z_to_bv 32 0x4515) := by
  decide +kernel

/-- And so `step` runs it: a0 := 5, pc += 2. -/
theorem cli_step_runs :
    (match step cli_segments (st0 cli_segments (Z_to_bv 64 0x100)) with
     | MachineOk ms' => (bv_unsigned (ms_pc ms'), bv_unsigned (ms_gpr ms' 0))
     | _ => ((0 : Int), (0 : Int))) = (0x102, 5) := by
  decide +kernel

/- ================================================================= -/
/- A 32-bit instruction still requires all four bytes                -/
/- ================================================================= -/

/-- A 32-bit encoding whose second parcel is unmapped is a genuine
fault: `fetch_tail` returns `none` and `step` is `MachineFault`.
(Contrast the compressed case above — the length-correct fetch does
NOT weaken the fault for truly-missing bytes.) -/
theorem trunc32_fetch_tail_fails :
    fetch_tail trunc32_segments (Z_to_bv 64 0x100) = none := by
  decide +kernel

theorem trunc32_step_illegal :
    step trunc32_segments (st0 trunc32_segments (Z_to_bv 64 0x100)) = MachineFault := by
  rfl

/- ================================================================= -/
/- Agreement where both fetches are defined: the word fetch matches   -/
/- the two-halfword fetch, on representative fixtures.                -/
/- ================================================================= -/

/-- For a compressed instruction with four mapped bytes, `fetch_word`
and `fetch_tail` differ only in the upper 16 bits (FFFF vs 0000)
that the decoder never reads — `decode_any` agrees, so the two
fetches drive the same step. -/
theorem cli_pad_fetch_word :
    fetch_word cli_pad_segments (Z_to_bv 64 0x100) = some (Z_to_bv 32 0xFFFF4515) := by
  decide +kernel

theorem cli_pad_fetch_tail :
    fetch_tail cli_pad_segments (Z_to_bv 64 0x100) = some (Z_to_bv 32 0x00004515) := by
  decide +kernel

theorem cli_pad_decode_agrees :
    decode_any (Z_to_bv 32 0xFFFF4515) = decode_any (Z_to_bv 32 0x00004515) := by
  decide +kernel

/-- (Rocq states this through `bool_decide` rather than a raw equality:
the decoded `bv` fields reduce to equal values but not
syntactically-equal proof terms — see the note in `Riscv/Decode.v`.
Lean's `BitVec` carries no such proof, so the decidable equality is
stated directly; the computed result is the same.) -/
theorem cli_pad_decodes_to_cli :
    decode_any (Z_to_bv 32 0x00004515)
      = some (instr.OpImm aluop.ALU_ADD (Z_to_bv 5 10) (Z_to_bv 5 0) (Z_to_bv 12 5), (2 : Int)) := by
  decide +kernel

/-- For a full 32-bit instruction with four mapped bytes, the two
fetches are literally equal. -/
theorem addi_fetch_word_eq_tail :
    fetch_word addi_segments (Z_to_bv 64 0x100)
      = fetch_tail addi_segments (Z_to_bv 64 0x100) := by
  decide +kernel

/- ================================================================= -/
/- Alignment: the halfword fetch still gates on pc mod 2             -/
/- ================================================================= -/

/-- A misaligned PC faults through the fallback too — `fetch_tail`
keeps the IALIGN=16 gate, so an odd PC is `none` and `step` is
`MachineFault` even though the compressed instruction is mapped. -/
theorem cli_misaligned_fetch_tail_none :
    fetch_tail cli_segments (Z_to_bv 64 0x101) = none := by
  decide +kernel

theorem cli_misaligned_step_illegal :
    step cli_segments (st0 cli_segments (Z_to_bv 64 0x101)) = MachineFault := by
  rfl

/-- Lean-only, and the reason the two above are not vacuous.  `cli_segment`
is two bytes long, so a halfword read at `0x101` leaves the segment and
would be `none` with no alignment gate at all.  `addi_segment` is four
bytes, so the halfword at `0x101` is mapped, executable and entirely
inside the segment, and only the IALIGN=16 gate can refuse it.  Deleting
that gate from `fetch_tail` turns this pin red; it leaves
`cli_misaligned_fetch_tail_none` green.  The Rocq file has the same two
checks over the same two-byte fixture and no such witness
(`RiscvCompressedFetch.v:25-31,154-159`). -/
theorem addi_misaligned_fetch_tail_none :
    fetch_tail addi_segments (Z_to_bv 64 0x101) = none := by
  decide +kernel

/-- The same for the externally visible step. -/
theorem addi_misaligned_step_fault :
    step addi_segments (st0 addi_segments (Z_to_bv 64 0x101)) = MachineFault := by
  rfl

/- ================================================================= -/
/- WHY the fetch failed: the model declining vs. the process crashing -/
/- ================================================================= -/

/-! The fetch layer declines some reads for reasons no MMU would
enforce, and `step` must NOT report those as crashes — see
`RiscvSemantics.fetch_failure`.  These fixtures pin the two
sides of that split on the same instruction bytes, so only the
segment's permissions and hex distinguish them. -/

/-- A w+x segment holding a perfectly good `addi x0,x0,0`.  Real
hardware executes this page, and so does the model: the static
`fetch_word` (immutable-code gate, `x /\ ~w`) refuses it, but
`step` falls through to the overlay-aware `fetch_word_ov`, which
reads the writable overlay first and the segment image underneath —
the same view data loads use.  (A fetch that refused w+x outright,
reporting `MachineUnmodeled`, would make an RWX-linked source image
error on its first fetch and satisfy `Run.all_traces_error`
vacuously.) -/
def wx_segment : Segment := {
  seg_base := 0x100,
  seg_size := 4,
  seg_perms := "rwx",
  seg_bytes := ["13000000"] }
def wx_segments : List Segment := [wx_segment]

theorem wx_fetch_word_fails :
    fetch_word wx_segments (Z_to_bv 64 0x100) = none := by
  decide +kernel

/-- The static projection `fetch_word_wx` (what a w+x image's generated
fetch lemmas are stated over) and the overlay-aware fetch on an
empty overlay agree on the image bytes. -/
theorem wx_fetch_word_wx_ok :
    fetch_word_wx wx_segments (Z_to_bv 64 0x100) = some (Z_to_bv 32 0x13) := by
  decide +kernel

theorem wx_fetch_word_ov_ok :
    fetch_word_ov wx_segments (fun _ => none) (Z_to_bv 64 0x100)
      = some (Z_to_bv 32 0x13) := by
  rfl

theorem wx_step_runs :
    (match step wx_segments (st0 wx_segments (Z_to_bv 64 0x100)) with
     | MachineOk ms' => bv_unsigned (ms_pc ms')
     | _ => (0 : Int)) = 0x104 := by
  decide +kernel

/-- And the overlay SHADOWS the image: with a store's bytes sitting
over the fetched address (here rewriting `addi x0,x0,0` into the
compressed `c.li a0, 5`, 0x4515), the next fetch at that address
executes the NEW bytes — self-modifying code in a w+x segment is
modeled faithfully rather than proved against stale code. -/
theorem wx_overlay_shadows_fetch :
    (match step wx_segments
            { ms_regs := bvmap_empty, ms_fregs := bvmap_empty,
              ms_pc_val := Z_to_bv 64 0x100,
              ms_svc_pending := none,
              ms_resv := none, ms_fcsr := Z_to_bv 32 0,
              ms_mem := write_to_mem (fun _ => none) (Z_to_bv 64 0x100)
                          [Z_to_bv 8 0x15, Z_to_bv 8 0x45],
              ms_rom := fun _ => none } with
     | MachineOk ms' => (bv_unsigned (ms_pc ms'), bv_unsigned (ms_gpr ms' 0))
     | _ => ((0 : Int), (0 : Int))) = (0x102, 5) := by
  decide +kernel

/-- The same bytes in a segment mapped WITHOUT 'x' is a genuine NX
fault: a real kernel kills the process. -/
def nx_segment : Segment := {
  seg_base := 0x100,
  seg_size := 4,
  seg_perms := "rw-",
  seg_bytes := ["13000000"] }
def nx_segments : List Segment := [nx_segment]

theorem nx_step_fault :
    step nx_segments (st0 nx_segments (Z_to_bv 64 0x100)) = MachineFault := by
  rfl

/-- An executable, non-writable segment whose snapshot hex is not
decodable — `hex_nybble` rejects 'A'-'F', so an uppercase image
silently reads as unmapped (see the `hex_byte_at` guard).  That is a
defect of the SNAPSHOT, not of the program, so it is unmodeled too:
a bad image must never be able to launder a target through the
escape. -/
def badhex_segment : Segment := {
  seg_base := 0x100,
  seg_size := 4,
  seg_perms := "r-x",
  seg_bytes := ["1300A000"] }
def badhex_segments : List Segment := [badhex_segment]

theorem badhex_fetch_tail_fails :
    fetch_tail badhex_segments (Z_to_bv 64 0x100) = none := by
  decide +kernel

theorem badhex_step_unmodeled :
    step badhex_segments (st0 badhex_segments (Z_to_bv 64 0x100)) = MachineUnmodeled := by
  rfl

/-- Fetch is per-PARCEL, and each parcel may come from either KIND of
executable segment: here the pc's first parcel sits in an ordinary
r-x segment and the UPPER parcel of the 32-bit encoding falls in a
w+x segment.  `fetch_tail_any` reads parcel 0 from the static image
and parcel 1 through the overlay view, and the instruction runs —
matching hardware, where permissions are per page and an
instruction may straddle a boundary.  Compare
`trunc32_step_illegal`, the identical shape with the upper parcel
genuinely unmapped, which stays `MachineFault`. -/
def split_wx_segments : List Segment :=
  [ { seg_base := 0x100, seg_size := 2,
      seg_perms := "r-x", seg_bytes := ["1300"] }
  , { seg_base := 0x102, seg_size := 2,
      seg_perms := "rwx", seg_bytes := ["0000"] } ]

theorem split_wx_first_parcel_ok :
    fetch_half split_wx_segments (Z_to_bv 64 0x100) = some (Z_to_bv 16 0x0013) := by
  decide +kernel

theorem split_wx_step_runs :
    (match step split_wx_segments (st0 split_wx_segments (Z_to_bv 64 0x100)) with
     | MachineOk ms' => bv_unsigned (ms_pc ms')
     | _ => (0 : Int)) = 0x104 := by
  decide +kernel

/-- A pc outside every segment stays a fault: a wild jump is a crash. -/
theorem unmapped_step_fault :
    step [] (st0 [] (Z_to_bv 64 0x100)) = MachineFault := by
  rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.RiscvCompressedFetch
