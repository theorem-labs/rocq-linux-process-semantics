-- Ports oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:projects/libreac/fuzz_knock/proofs/lib/Prog/LLVMFuzzerTestOneInput_c.v
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Exec
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Frame
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.MState
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Img0

/-! `lib/Prog/LLVMFuzzerTestOneInput_c.v`: the contract of the fuzz harness
entry `LLVMFuzzerTestOneInput` of `fuzz_knock.plain`.

Every path in this docstring is in theorem-labs/oss-verify-proofs-internal
`ossv/recipes` `9b0ac6f0e6`, under `projects/libreac/fuzz_knock/proofs/`.

Three differences from the Rocq statement, all forced by the Lean library and
each carried as a gaps-ledger row of OSSV-265:

* K1H-1 (`lib/Prog/LLVMFuzzerTestOneInput_c.v:25-27,32-33`). Rocq's `MS` builds
  a `machine_state` whose `ms_fregs`, `ms_fcsr` and `ms_resv` are the section
  variables `F`, `fc` and `None`, so the contract says that the float registers
  and the reservation come out as they went in. The Lean step lemmas are stated
  over `LinuxProcessSemantics.Common.PropExec.mkst`, which pins all three
  (`mkst` sets `ms_fregs := bvmap_empty`, `ms_fcsr := 0`, `ms_resv := none`), so
  the Lean contract runs from, and lands in, a state with those three pinned.
  This is the same weakening as OSSV-265 gaps row T-6.
* K1H-2 (`lib/Prog/LLVMFuzzerTestOneInput_c.v:12,25-26,32`). Rocq names the 31
  registers and rebuilds them with `mkR`, so "`ra`, `sp`, `gp`, `tp`, `s0`-`s11`
  come out as they went in, `a0` comes out `0`, and the caller-saved registers
  are free" is read off the two `mkR` applications. A Lean register file is a
  `bvmap 5 word` read by `getr`, so the same claim is the pair
  `getr regs' 10 = 0` and an equation over `knock_preserved`; the registers that
  are in neither are the ones the Rocq statement leaves free. This is OSSV-265
  gaps row T-10.
* K1H-3 (`lib/Prog/LLVMFuzzerTestOneInput_c.v:19`). Rocq's `bv_unsigned sp mod
  16 = 0` is `Z.modulo`; Lean's `%` on `Int` is `Int.emod`. The two agree on a
  non-negative dividend and a positive divisor, which `bv_unsigned` and `16`
  are, so the hypothesis is the same one. -/

namespace OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.LLVMFuzzerTestOneInput_c

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.Common.PropExec
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Img0 (rsegs)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Mem (bytes_at mem_inv)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Frame (munch wmono stk)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Exec (evt)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.MState (ret_pc)

/-- `lib/Prog/LLVMFuzzerTestOneInput_c.v:8`: the entry of
`LLVMFuzzerTestOneInput` in `fuzz_knock.plain`. -/
def LLVM_KNOCK : Int := 0x12adc

/-- `lib/Prog/LLVMFuzzerTestOneInput_c.v:9`: the bytes below `sp` the call
owns. -/
def LLVM_KNOCK_STACK : Int := 176

/-- The registers the Rocq post-state of
`lib/Prog/LLVMFuzzerTestOneInput_c.v:25-26` rebuilds with the value they had in
the pre-state of line 32: `ra`, `sp`, `gp`, `tp` and `s0`-`s11`. The ones the
list omits, other than `a0`, are the ones Rocq's post-state gives a primed
(free) variable: `t0`-`t2`, `a1`-`a7` and `t3`-`t6`. See K1H-2 above. -/
def knock_preserved : List reg :=
  [1, 2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- `lib/Prog/LLVMFuzzerTestOneInput_c.v:11-33`.

`LLVMFuzzerTestOneInput(data, len)`, entered with `a0` a pointer to `data` and
`a1` its length, returns to `ret_pc ra` with `a0 = 0`, having touched no byte
outside `[sp - 176, sp)`, having unmade no writable byte, having kept the
overlay off the read-only image, and leaving the caller's stack window below
`lo` as readable and writable as it was.

The hypotheses, in the Rocq order: the bytes are in memory
(`:14`); `a1` is their length (`:15`); the overlay shadows no read-only byte
(`:16`); `[lo, sp)` is a usable stack (`:17`); the frame fits in it (`:18`); the
stack is 16-byte aligned (`:19`); the input buffer does not overlap the frame
(`:20`); and the buffer's end does not pass `2^63` (`:21`). -/
def knock_main_contract : Prop :=
  ∀ (regs : bvmap 5 word) (m : word → Option byte) (lo : Int) (data : List byte),
    bytes_at rsegs m (bv_unsigned (getr regs 10)) data →
    bv_unsigned (getr regs 11) = (data.length : Int) →
    mem_inv rsegs m →
    stk rsegs m lo (bv_unsigned (getr regs 2)) →
    lo + LLVM_KNOCK_STACK ≤ bv_unsigned (getr regs 2) →
    bv_unsigned (getr regs 2) % 16 = 0 →
    (bv_unsigned (getr regs 10) + (data.length : Int) ≤ lo
      ∨ bv_unsigned (getr regs 2) ≤ bv_unsigned (getr regs 10)) →
    bv_unsigned (getr regs 10) + (data.length : Int) < 2 ^ 63 →
    evt rsegs
      (fun ms' => ∃ (regs' : bvmap 5 word) (m' : word → Option byte),
        ms' = mkst regs' (ret_pc (getr regs 1)) m' (seg_rom rsegs)
        ∧ getr regs' 10 = Z_to_bv 64 0
        ∧ (∀ r ∈ knock_preserved, getr regs' r = getr regs r)
        ∧ munch [(bv_unsigned (getr regs 2) - LLVM_KNOCK_STACK,
                  bv_unsigned (getr regs 2))] m m'
        ∧ wmono rsegs m m'
        ∧ mem_inv rsegs m'
        ∧ stk rsegs m' lo (bv_unsigned (getr regs 2)))
      (mkst regs (Z_to_bv 64 LLVM_KNOCK) m (seg_rom rsegs))

end OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.LLVMFuzzerTestOneInput_c
