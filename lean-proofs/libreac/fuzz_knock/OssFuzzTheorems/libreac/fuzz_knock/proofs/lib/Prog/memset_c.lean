-- Ports oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:projects/libreac/fuzz_knock/proofs/lib/Prog/memset_c.lean
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Step
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Frame
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Exec
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.MState
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Img0

/-! `lib/Prog/memset_c.v`: the contract of musl's `memset`, at `0x1ac04` of
`fuzz_knock.plain`.

The Rocq file is 25 lines; every declaration below names the Rocq line it is
translated from. Paths without a repository are in
theorem-labs/oss-verify-proofs-internal `ossv/recipes` `9b0ac6f0e6`, under
`projects/libreac/fuzz_knock/proofs/`.

Two differences from the Rocq statement, both forced by the Lean library and
already recorded for slice T:

* Rocq's `MS` leaves `ms_fregs`, `ms_fcsr` and `ms_resv` free; the Lean step
  lemmas are stated over `PropExec.mkst`, which pins all three (gaps row T-6).
  So the pre- and post-states here are `mkst`, and the Rocq `F` (the float
  register file) and `fc` (the `fcsr`) have no parameter here.
* Rocq's `mkR` builds the integer register file from 31 named words, so
  "`a0` is unchanged and `t0`, `a1` … `a7`, `t3` … `t6` are anything" is read
  off the shape of the state. A Lean register file is a `bvmap 5 word` read by
  `getr`, so the same statement is the quantified equation `memset_frame`
  (gaps row T-10) over the caller-saved registers Rocq's `memset_post` leaves
  free. -/

namespace OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.memset_c

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.Common.PropExec
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Mem (mem_inv)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Frame (munch wmono)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Step (rw_cells)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Exec (evt)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.MState (ret_pc)

/-- `lib/Prog/memset_c.v:8`. -/
def MEMSET : Int := 0x1ac04

/-- The registers `memset_post` (`lib/Prog/memset_c.v:13`) leaves free: `t0`,
`t1`, `t2`, `a1` … `a7` and `t3` … `t6`, the caller-saved set. Every other
register of the Rocq post-state is the word the pre-state had. -/
def memset_clobber : List reg := [5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

/-- `lib/Prog/memset_c.v:13`, as a `bvmap` register file: the call changes no
register outside `memset_clobber`. -/
def memset_frame (regs regs' : bvmap 5 word) : Prop :=
  ∀ r : reg, r ∉ memset_clobber → getr regs' r = getr regs r

/-- `lib/Prog/memset_c.v:10-17`: the post-state of a `memset` call, with `a0`,
`a1` and `a2` read from the pre-state's register file `regs`.

`c`, the byte the call writes, is `a1`'s low byte, Rocq's
`Z_to_bv 8 (bv_unsigned a1 mod 256)`. -/
def memset_post (regs : bvmap 5 word) (m : word → Option byte) :
    machine_state → Prop :=
  fun ms' => ∃ (regs' : bvmap 5 word) (m' : word → Option byte),
    ms' = mkst regs' (ret_pc (getr regs 1)) m' (seg_rom Img0.rsegs)
    ∧ memset_frame regs regs'
    ∧ munch [(bv_unsigned (getr regs 10),
              bv_unsigned (getr regs 10) + bv_unsigned (getr regs 12))] m m'
    ∧ wmono Img0.rsegs m m'
    ∧ mem_inv Img0.rsegs m'
    ∧ rw_cells Img0.rsegs m' (bv_unsigned (getr regs 10))
        [.CB (bv_unsigned (getr regs 12)).toNat
           (List.replicate (bv_unsigned (getr regs 12)).toNat
             (Z_to_bv 8 (bv_unsigned (getr regs 11) % 256)))]

/-- `lib/Prog/memset_c.v:19-25`: from a state at `memset`'s entry whose `a0`
points at `a2` writable bytes of any content, the machine reaches a state in
which those bytes all hold `a1`'s low byte, nothing outside them changed, and
the pc is the return address. -/
def memset_contract : Prop :=
  ∀ (regs : bvmap 5 word) (m : word → Option byte) (junk : List byte),
    rw_cells Img0.rsegs m (bv_unsigned (getr regs 10))
        [.CB (bv_unsigned (getr regs 12)).toNat junk] →
    mem_inv Img0.rsegs m →
    evt Img0.rsegs (memset_post regs m)
      (mkst regs (Z_to_bv 64 MEMSET) m (seg_rom Img0.rsegs))

end OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.memset_c
