-- Ports oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:projects/libreac/fuzz_knock/proofs/lib/Lib/Cells.v
import OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Mem

/-! `lib/Lib/Cells.v`: a C object as a list of little-endian cells.

The five arms and the predicates the `lib/Prog/` contracts name: eight of the
Rocq file's 13 definitions, and none of its 18 lemmas. The file is 227 lines;
what is left out is `cell_at`, `cell_upd`, `cb_pieces`, `cb_split` and
`cb_split_ok`, and the reading, writing and splitting theory about them. Every
path in this docstring is in theorem-labs/oss-verify-proofs-internal
`ossv/recipes` `9b0ac6f0e6`, under `projects/libreac/fuzz_knock/proofs/`. -/

namespace OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Cells

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Mem

/-- `lib/Lib/Cells.v:15-20`. -/
inductive cell where
  | C8 (v : word)
  | C4 (v : word)
  | C2 (v : word)
  | C1 (b : byte)
  | CB (n : Nat) (bs : List byte)

/-- `lib/Lib/Cells.v:22-23`. -/
def csize : cell → Nat
  | .C8 _ => 8
  | .C4 _ => 4
  | .C2 _ => 2
  | .C1 _ => 1
  | .CB n _ => n

/-- `lib/Lib/Cells.v:24-25`. -/
def cbytes : cell → List byte
  | .C8 v => le8 v
  | .C4 v => le4 v
  | .C2 v => le2 v
  | .C1 b => [b]
  | .CB _ bs => bs

/-- `lib/Lib/Cells.v:26-27`. -/
def cells_size : List cell → Nat
  | [] => 0
  | c :: cs => csize c + cells_size cs

/-- `lib/Lib/Cells.v:28-29`. -/
def cells_bytes : List cell → List byte
  | [] => []
  | c :: cs => cbytes c ++ cells_bytes cs

/-- `lib/Lib/Cells.v:30`. -/
def cell_wf : cell → Prop
  | .CB n bs => bs.length = n
  | _ => True

/-- `lib/Lib/Cells.v:31-32`. -/
def cells_wf : List cell → Prop
  | [] => True
  | c :: cs => cell_wf c ∧ cells_wf cs

/-- `lib/Lib/Cells.v:91-92`. -/
def cells_at (segs : List Segment) (m : word → Option byte) (A : Int)
    (cs : List cell) : Prop :=
  bytes_at segs m A (cells_bytes cs) ∧ cells_wf cs

end OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Lib.Cells
