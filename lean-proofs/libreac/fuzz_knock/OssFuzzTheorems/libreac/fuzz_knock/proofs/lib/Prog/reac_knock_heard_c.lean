-- Ports oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:projects/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_heard_c.v
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Img0
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Exec
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.MState
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Step
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Frame
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_struct
import LinuxProcessSemantics.Common.SeqExec
import LinuxProcessSemantics.Common.SymExec

/-! `lib/Prog/reac_knock_heard_c.v`: the contract of `reac_knock_heard`.

`reac_knock_heard`, as `fuzz_knock.plain` holds it (the words are the ones
`Image/PlainCode.lean` proves the image carries at these addresses):

    0x12d9c  00052603  lw   a2, 0(a0)      -- a2 := (int32) s->state
    0x12da0  00b53c23  sd   a1, 24(a0)     -- s->heard := now
    0x12da4  00060463  beq  a2, x0, +8     -- if state == 0 goto 0x12dac
    0x12da8  00008067  jalr x0, 0(ra)      -- return
    0x12dac  00200593  addi a1, x0, 2      -- a1 := 2
    0x12db0  00b52023  sw   a1, 0(a0)      -- s->state := 2
    0x12db4  00008067  jalr x0, 0(ra)      -- return

First converted for OSSV-265 slice T (`probe/ossv265-t/Probe/Heard.lean` of
theorem-labs/oss-verify-proofs-internal, branch `mcsl/lean-convert-probe`);
restated here over `Img0.rsegs`, the whole four-segment image, and over the
`lib/Lib/` vocabulary the project now carries. -/

namespace OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_heard_c

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.Riscv.Instr
open LinuxProcessSemantics.Riscv.Sem
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.CatExec
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Exec (evt)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.MState (ret_pc)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Step (rw_cells)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Frame (munch wmono)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_struct (knock_cells)

/-- `lib/Prog/reac_knock_heard_c.v:9`: the entry of `reac_knock_heard` in
`fuzz_knock.plain`. -/
def REAC_KNOCK_HEARD : Int := 0x12d9c

/-- The memory the call leaves: `s->heard := now` always, and `s->state := 2`
when the stored state word is zero.

The test is Rocq's own, on the INTEGER the first cell holds
(`lib/Prog/reac_knock_heard_c.v:25`, `if Z.eqb st 0 then 2 else st`). Rocq
gets from the sign-extended `lw` result to that test with
`knock_sx32_unsigned` (`lib/Prog/reac_knock_struct.v:12-28`) and
`knock_sx32_eqb` (`lib/Prog/reac_knock_struct.v:30-36`), which rest on stdpp's
`bv_swrap` lemma set. The Lean model carries no twin of that set (OSSV-265
gaps row T-12), but the two lemmas follow from Lean's own `Int` arithmetic;
`reac_knock_heard.lean` proves them, so the contract keeps Rocq's test and
T-12 does not bite here. -/
def heard_mem (regs : bvmap 5 word) (mem : word → Option byte) (st : Int)
    : word → Option byte :=
  let m1 := wbytes mem (v_addi (getr regs 10) 24) (word_to_le_bytes 8 (getr regs 11))
  if st = 0 then
    wbytes m1 (v_addi (getr regs 10) 0) (word_to_le_bytes 4 (Z_to_bv 64 2))
  else m1

/-- The twin of `reac_knock_heard_contract`
(`lib/Prog/reac_knock_heard_c.v:11-27`), over `Img0.rsegs`.

Differences from the Rocq statement, each forced by vocabulary the Lean model
does not carry, and each a row of the OSSV-265 gaps ledger:

* **T-6; rows W6 and W7 of the K1 line-by-line review.** The state is
  `PropExec.mkst`, which pins `ms_fregs := bvmap_empty`, `ms_fcsr := 0` and
  `ms_resv := none`; Rocq's `MS` (`lib/Lib/MState.v:16-19`) leaves all three
  free, in the start state and in the post-state, and Rocq's `step_gen`
  (`lib/Lib/MState.v:71-83`) is proved over the general state. Every step
  lemma of `LinuxProcessSemantics.Common.SeqExec`/`SymExec` is stated over
  `mkst`, so this contract says nothing about a machine whose float
  registers, CSR or reservation differ, and does not state that the call
  leaves them unchanged.
* **T-10.** The register file is a `bvmap 5 word` read by `getr`, not the 31
  named words of `mkR` (`lib/Lib/Frame.v:20-26`). "Only `a1` and `a2` changed" is
  stated as `∀ r, r ≠ 11 → r ≠ 12 → getr regs' r = getr regs r`.
* **T-11; row W1.** `rw_cells` is here, as Rocq has it, but the first
  cell's four bytes are taken as the extra hypotheses `hread`/`hbs`: the Rocq
  bridge from `rw_cells` to a 4-byte read (`lib/Lib/Cells.v:94-109`,
  `lib/Lib/Step.v:28-31`) has no Lean twin, and `proofs/lib/Lib/Step.lean`
  carries the statement of `rw_cells` only. The two `store_ok` side
  conditions the Rocq proof gets from `rw_cells` by `rw_cells_store_ok`
  (`lib/Lib/Step.v:70-76`) are NOT hypotheses: they are derived from the
  `wr_at` conjunct in `reac_knock_heard.lean`.
* **T-12 does NOT bite.** The post-state's first cell is Rocq's own
  `if Z.eqb st 0 then 2 else st`, on the stored integer (see `heard_mem`).
* **K1-1; row W8.** The post-state's memory is given EXPLICITLY, as
  `heard_mem`, where Rocq states it as
  `rw_cells rsegs m' a0 (knock_cells (if st =? 0 then 2 else st) …)`
  (`lib/Prog/reac_knock_heard_c.v:24-25`). The overlay pins every byte, so it
  is stronger about the bytes, but a caller does not get `cells_at m'` or
  `wr_at m' a0 40` back: turning the overlay into `rw_cells` needs the
  write-side lemmas of `lib/Lib/Step.v` (824 lines, of which the Lean port
  carries the one definition `rw_cells` itself). Rocq's other two post
  conjuncts, `munch` and `wmono` (`lib/Lib/Frame.v:71-74`,
  `lib/Prog/reac_knock_heard_c.v:22-23`), are stated and proved as Rocq has
  them.

What is NOT weakened, against slice T: the walk is over `Img0.rsegs`, the
whole four-segment image, not a 28-byte window; the return address is
`ret_pc ra` (`lib/Lib/MState.v:140`), Rocq's own spelling, not the model's
`v_jalr ra 0` (gaps row T-9 is closed by `PropExec.b_jalr`); and `munch`,
`wmono` and `rw_cells` are the `lib/Lib/` declarations, not local copies. -/
def reac_knock_heard_contract : Prop :=
  ∀ (regs : bvmap 5 word) (mem : word → Option byte)
    (st : Int) (p1 opened due heard : word) (g : Int) (p2 : word)
    (bs : List byte),
    0 ≤ st → st < 2 ^ 32 → 0 ≤ g → g < 2 ^ 32 →
    rw_cells Img0.rsegs mem (bv_unsigned (getr regs 10))
      (knock_cells st p1 opened due heard g p2) →
    rdn Img0.rsegs mem (v_addi (getr regs 10) 0) 4 = some bs →
    bytes_le_to_Z bs = st →
    evt Img0.rsegs
      (fun ms' => ∃ (regs' : bvmap 5 word) (mem' : word → Option byte),
        ms' = mkst regs' (ret_pc (getr regs 1)) mem' (seg_rom Img0.rsegs) ∧
        (∀ r : reg, r ≠ 11 → r ≠ 12 → getr regs' r = getr regs r) ∧
        munch [(bv_unsigned (getr regs 10), bv_unsigned (getr regs 10) + 40)] mem mem' ∧
        wmono Img0.rsegs mem mem' ∧
        mem' = heard_mem regs mem st)
      (mkst regs (Z_to_bv 64 REAC_KNOCK_HEARD) mem (seg_rom Img0.rsegs))

end OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_heard_c
