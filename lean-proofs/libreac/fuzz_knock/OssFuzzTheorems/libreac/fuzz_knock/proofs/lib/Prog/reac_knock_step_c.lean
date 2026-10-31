-- Ports oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:projects/libreac/fuzz_knock/proofs/lib/Prog/reac_knock_step_c.v
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Exec
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Frame
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.MState
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Step
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_struct
import LinuxProcessSemantics.Common.CatExec
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Img0

/-! `lib/Prog/reac_knock_step_c.v`: the contract of `reac_knock_step`.

`reac_knock_step`, as `fuzz_knock.plain` holds it (0x12db8, 96 bytes,
24 instructions; `a0` is the `struct reac_knock *`, `a1` the time `t`):

    0x12db8  lw    a2, 0(a0)        -- a2 := (int32) s->state
    0x12dbc  addi  a3, x0, 2
    0x12dc0  beq   a2, a3, 0x12dd8  -- state == 2 ?
    0x12dc4  bne   a2, x0, 0x12dd0  -- state != 0 -> return 0
    0x12dc8  ld    a3, 16(a0)       -- a3 := s->due
    0x12dcc  bgeu  a1, a3, 0x12e04  -- t >= due -> fire
    0x12dd0  addi  a2, x0, 0
    0x12dd4  jal   x0, 0x12e10
    0x12dd8  ld    a3, 24(a0)       -- a3 := s->heard
    0x12ddc  addi  a2, x0, 0
    0x12de0  bgeu  a3, a1, 0x12e10  -- t <= heard -> return 0
    0x12de4  sub   a5, a1, a3       -- a5 := t - heard
    0x12de8  lui   a4, 0x1dcd6
    0x12dec  addiw a4, a4, 0x500    -- a4 := 500000000 (L_NS)
    0x12df0  bltu  a5, a4, 0x12e10  -- t - heard < L_NS -> return 0
    0x12df4  add   a3, a3, a4       -- a3 := heard + L_NS
    0x12df8  sw    x0, 0(a0)        -- s->state := 0
    0x12dfc  sd    a3, 16(a0)       -- s->due := heard + L_NS
    0x12e00  bltu  a1, a3, 0x12dd0  -- t < due' ?  (never, see the proof)
    0x12e04  addi  a2, x0, 1
    0x12e08  sw    a2, 0(a0)        -- s->state := 1
    0x12e0c  sw    a2, 32(a0)       -- s->g := 1
    0x12e10  addi  a0, a2, 0
    0x12e14  jalr  x0, 0(ra)

Differences from the Rocq contract, all of them forced by the Lean library:

* the state is `PropExec.mkst`, which pins `ms_fregs`, `ms_fcsr` and
  `ms_resv`, where Rocq's `MS` leaves all three free, and the register file
  is a `bvmap 5 word` read by `getr`, not Rocq's 31 named words built by
  `mkR` (OSSV-265 gaps rows T-6 and T-10);
* Rocq's `rw_cells` hypothesis stands for both the reads the function makes
  and the writability of what it stores; the Lean port of `lib/Lib/Step.v`
  carries neither the read bridge nor the write bridge (gaps row T-11), so
  the three reads are taken as `rdn` hypotheses and the three stores as
  `store_ok` hypotheses, as OSSV-265 slice T's probe did
  (`probe/ossv265-t/Probe/Heard.lean` of theorem-labs/oss-verify-proofs-internal,
  branch `mcsl/lean-convert-probe` `4054974252`), and the post-state's memory
  is given byte for byte by `knock_step_mem` instead of by `rw_cells` on
  `knock_cells st' p1 opened due' heard g' p2` (gaps row K1-1).
  `knock_step_mem` writes exactly `le4 (Z_to_bv 64 st')` at offset 0,
  `le8 due'` at offset 16 and `le4 (Z_to_bv 64 g')` at offset 32, which are
  the three cells of `knock_cells` that `knock_step_f` changes. -/

namespace OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_step_c

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.Common.CatExec (wbytes)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Mem (le4 le8)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Frame (munch wmono)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.MState (ret_pc)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Exec (evt)
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_struct (L_NS)

/-- `lib/Prog/reac_knock_step_c.v:9`. -/
def REAC_KNOCK_STEP : Int := 0x12db8

/-- `lib/Prog/reac_knock_step_c.v:11-18`: the decision the function makes, as
`(return value, new state, new due, new g)`. Rocq's `Z.eqb st 2` and
`Z.eqb st 0` are Lean's decidable `st = 2` and `st = 0`, and Rocq's
`orb (_ <=? _) (_ <? _)` is the decidable disjunction. -/
def knock_step_f (st g : Int) (due heard t : word) : Int × Int × word × Int :=
  if st = 2 then
    if bv_unsigned t ≤ bv_unsigned heard ∨ bv_unsigned t - bv_unsigned heard < L_NS
    then (0, st, due, g)
    else (1, 1, Z_to_bv 64 (bv_unsigned heard + L_NS), 1)
  else if st = 0 then
    if bv_unsigned t < bv_unsigned due then (0, st, due, g) else (1, 1, due, 1)
  else (0, st, due, g)

/-- The post-state's memory, byte for byte: the Lean stand-in for the Rocq
contract's `rw_cells rsegs m' (bv_unsigned a0) (knock_cells st' p1 opened due'
heard g' p2)` (`lib/Prog/reac_knock_step_c.v:35`), which the Lean port cannot
state (gaps row K1-1, see the file docstring).

The three arms are the three paths of `knock_step_f`: no store at all when the
function returns 0; `state := 1` and `g := 1` when a due time has come; and,
when the listen window has run out, the same two stores after `state := 0` and
`due := heard + L_NS`, in the order the code makes them. -/
def knock_step_mem (a0 : word) (m : word → Option byte) (st : Int)
    (due heard t : word) : word → Option byte :=
  if st = 2 then
    if bv_unsigned t ≤ bv_unsigned heard ∨ bv_unsigned t - bv_unsigned heard < L_NS
    then m
    else
      wbytes (wbytes (wbytes (wbytes m (v_addi a0 0) (le4 (Z_to_bv 64 0)))
          (v_addi a0 16) (le8 (Z_to_bv 64 (bv_unsigned heard + L_NS))))
          (v_addi a0 0) (le4 (Z_to_bv 64 1)))
        (v_addi a0 32) (le4 (Z_to_bv 64 1))
  else if st = 0 then
    if bv_unsigned t < bv_unsigned due then m
    else wbytes (wbytes m (v_addi a0 0) (le4 (Z_to_bv 64 1)))
      (v_addi a0 32) (le4 (Z_to_bv 64 1))
  else m

/-- `lib/Prog/reac_knock_step_c.v:20-37`.

`st` is the stored state, `g` the stored generation counter, `due` and `heard`
the two stored times, `getr regs 10` the structure pointer and `getr regs 11`
the time `t` the caller passes. The frame conjunct is stronger than Rocq's,
which lets `a0`…`a5` change: the function writes only `a0`, `a2`, `a3`, `a4`
and `a5`. -/
def reac_knock_step_contract : Prop :=
  ∀ (regs : bvmap 5 word) (mem : word → Option byte) (st g : Int)
    (due heard : word) (bs0 bsd bsh : List byte),
    0 ≤ st → st < 2 ^ 32 →
    -- the three fields the function reads, as the model reads them
    rdn Img0.rsegs mem (v_addi (getr regs 10) 0) 4 = some bs0 →
    bytes_le_to_Z bs0 = st →
    rdn Img0.rsegs mem (v_addi (getr regs 10) 16) 8 = some bsd →
    bytes_le_to_Z bsd = bv_unsigned due →
    rdn Img0.rsegs mem (v_addi (getr regs 10) 24) 8 = some bsh →
    bytes_le_to_Z bsh = bv_unsigned heard →
    -- the three fields it stores to lie in the writable view: the `wr_at`
    -- conjunct of Rocq's `rw_cells`
    store_ok Img0.rsegs mem (v_addi (getr regs 10) 0) 4 = true →
    store_ok Img0.rsegs mem (v_addi (getr regs 10) 16) 8 = true →
    store_ok Img0.rsegs mem (v_addi (getr regs 10) 32) 4 = true →
    -- the structure does not wrap the address space: the first conjuncts of
    -- Rocq's `bytes_at` and `wr_at`
    bv_unsigned (getr regs 10) + 40 ≤ 2 ^ 64 →
    evt Img0.rsegs
      (fun ms' => ∃ (regs' : bvmap 5 word) (m' : word → Option byte),
        ms' = mkst regs' (ret_pc (getr regs 1)) m' (seg_rom Img0.rsegs) ∧
        munch [(bv_unsigned (getr regs 10), bv_unsigned (getr regs 10) + 40)] mem m' ∧
        wmono Img0.rsegs mem m' ∧
        m' = knock_step_mem (getr regs 10) mem st due heard (getr regs 11) ∧
        getr regs' 10 = Z_to_bv 64 (knock_step_f st g due heard (getr regs 11)).1 ∧
        ∀ r : reg, r ≠ 10 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 →
          getr regs' r = getr regs r)
      (mkst regs (Z_to_bv 64 REAC_KNOCK_STEP) mem (seg_rom Img0.rsegs))

end OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Prog.reac_knock_step_c
