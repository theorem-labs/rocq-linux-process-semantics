-- Ports oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:projects/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_init_c.lean
-- Ports oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:projects/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_init_c.v

import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Img0
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Exec
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Frame
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.MState
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_struct

/-! `lib/Prog/reac_knock_init_c.v`: the contract of `reac_knock_init`.

`reac_knock_init(struct reac_knock *s, uint64_t now)` zeroes the 40-byte
structure and then sets `s->opened := now` and `s->due := now + 500000000`.
As `fuzz_knock.plain` holds it, at `0x12d50`, 76 bytes, 19 instructions:

    0x12d50  fe010113  addi  sp, sp, -32
    0x12d54  00113c23  sd    ra, 24(sp)
    0x12d58  00813823  sd    s0, 16(sp)
    0x12d5c  00913423  sd    s1, 8(sp)
    0x12d60  00058413  addi  s0, a1, 0        -- s0 := now
    0x12d64  00050493  addi  s1, a0, 0        -- s1 := s
    0x12d68  02800613  addi  a2, x0, 40
    0x12d6c  00000593  addi  a1, x0, 0
    0x12d70  695070ef  jal   ra, 0x1ac04      -- memset(s, 0, 40)
    0x12d74  1dcd6537  lui   a0, 0x1dcd6
    0x12d78  5005051b  addiw a0, a0, 0x500    -- a0 := 500000000
    0x12d7c  00a40533  add   a0, s0, a0
    0x12d80  0084b423  sd    s0, 8(s1)        -- s->opened := now
    0x12d84  00a4b823  sd    a0, 16(s1)       -- s->due := now + 500000000
    0x12d88  01813083  ld    ra, 24(sp)
    0x12d8c  01013403  ld    s0, 16(sp)
    0x12d90  00813483  ld    s1, 8(sp)
    0x12d94  02010113  addi  sp, sp, 32
    0x12d98  00008067  jalr  x0, 0(ra)

Every path in a docstring of this file is in
theorem-labs/oss-verify-proofs-internal `ossv/recipes` `9b0ac6f0e6`, under
`projects/libreac/fuzz_knock/proofs/`, unless it names its own repository.

Two differences from the Rocq statement, both of them the ones OSSV-265 slice
T already recorded for `reac_knock_heard`:

* `lib/Prog/reac_knock_init_c.v:32-33` builds the state with `MS`, which leaves
  `ms_fregs`, `ms_fcsr` and `ms_resv` free; the Lean library's step lemmas are
  stated over `LinuxProcessSemantics.Common.PropExec.mkst`, which pins all
  three, so the contract is over `mkst` and the Rocq parameters `F` and `fc`
  are gone (gaps row T-6).
* `lib/Prog/reac_knock_init_c.v:13-13` names the 31 registers one by one and
  `mkR` rebuilds them; a Lean register file is one `bvmap 5 word` read by
  `getr`, so "`ra sp gp tp s0 s1 s2..s11` come back unchanged" is the
  quantified equation over `init_clobbers` below (gaps row T-10). -/

namespace OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_init_c

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.Common.PropExec
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Mem (mem_inv)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Cells (cell)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Step (rw_cells)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Frame (munch wmono stk)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Exec (evt)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.MState (ret_pc)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_struct (L_NS knock_cells)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Img0 (rsegs)

/-- `lib/Prog/reac_knock_init_c.v:9`. -/
def REAC_KNOCK_INIT : Int := 0x12d50

/-- `lib/Prog/reac_knock_init_c.v:10`. -/
def REAC_KNOCK_INIT_FRAME : Int := 32

/-- The registers the call may leave changed: `t0 t1 t2` (5–7), `a0`–`a7`
(10–17) and `t3`–`t6` (28–31).

This is the Lean form of the Rocq post-state's `mkR`
(`lib/Prog/reac_knock_init_c.v:23-24`), which rebinds exactly these and keeps
`ra sp gp tp s0 s1 s2 .. s11` (gaps row T-10). -/
def init_clobbers (r : reg) : Bool :=
  [5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31].contains r

/-- The twin of `reac_knock_init_contract`
(`lib/Prog/reac_knock_init_c.v:12-33`).

Given a writable 40-byte block at `a0`, a memory invariant, a stack window
`[lo, bv_unsigned sp)` with at least `REAC_KNOCK_INIT_FRAME` bytes of frame,
and `sp ≤ a0`, the function returns to `ret_pc ra` having written
`knock_cells 0 0 a1 (a1 + L_NS) 0 0 0` at `a0`; it touches only
`[sp - 32, sp)` and `[a0, a0 + 40)`, and keeps `mem_inv` and the stack
window. -/
def reac_knock_init_contract : Prop :=
  ∀ (regs : bvmap 5 word) (m : word → Option byte) (lo : Int) (junk : List byte),
    rw_cells rsegs m (bv_unsigned (getr regs 10)) [cell.CB 40 junk] →
    mem_inv rsegs m →
    stk rsegs m lo (bv_unsigned (getr regs 2)) →
    lo + REAC_KNOCK_INIT_FRAME ≤ bv_unsigned (getr regs 2) →
    bv_unsigned (getr regs 2) ≤ bv_unsigned (getr regs 10) →
    evt rsegs
      (fun ms' => ∃ (regs' : bvmap 5 word) (m' : word → Option byte),
        ms' = mkst regs' (ret_pc (getr regs 1)) m' (seg_rom rsegs)
        ∧ (∀ r : reg, init_clobbers r = false → getr regs' r = getr regs r)
        ∧ munch
            [(bv_unsigned (getr regs 2) - REAC_KNOCK_INIT_FRAME,
              bv_unsigned (getr regs 2)),
             (bv_unsigned (getr regs 10), bv_unsigned (getr regs 10) + 40)] m m'
        ∧ wmono rsegs m m'
        ∧ mem_inv rsegs m'
        ∧ stk rsegs m' lo (bv_unsigned (getr regs 2))
        ∧ rw_cells rsegs m' (bv_unsigned (getr regs 10))
            (knock_cells 0 (Z_to_bv 64 0) (getr regs 11)
              (Z_to_bv 64 (bv_unsigned (getr regs 11) + L_NS))
              (Z_to_bv 64 0) 0 (Z_to_bv 64 0)))
      (mkst regs (Z_to_bv 64 REAC_KNOCK_INIT) m (seg_rom rsegs))

end OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_init_c
