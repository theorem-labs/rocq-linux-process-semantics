import LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite
import LinuxProcessSemantics.Common.SimInv
import LinuxProcessSemantics.Common.ExitSim
import LinuxProcessSemantics.Common.PropExec
import LinuxProcessSemantics.Common.CatSim
import LinuxProcessSemantics.Common.CatExec
import LinuxProcessSemantics.Common.SeqExec
import LinuxProcessSemantics.Common.StreamExec
import LinuxProcessSemantics.Common.WallSim
import LinuxProcessSemantics.Common.StreamSim

/-! rocq-baseline: f62e8cc141d23e60acdf614311e52aac5662dd56 -/

/-! # Common.DrainSim — drain-then-emit read-loop simulation

Ported from `theories/Common/DrainSim.v`, with the Rocq statements
(ticket E-proof-library-2b).  The file was read at the commit named
above (`nightly/09-30-2026`); it is unchanged there from
2cde689f94c086b868999970834b76a25616b94a, the baseline of the
`StreamSim.lean` and `WallSim.lean` it builds on.

What shape of binary the library covers, and what its per-binary
obligation `H_LH` asks, is argued in the Rocq file's header.  The
`StreamSim` and `WallSim` names this file reaches beyond #1298's and
E-proof-library-2a's ports are appended to those files, in their sections
headed "Additions for E-proof-library-2b".

Representation spellings:
- Rocq `fst`/`snd` are `.1`/`.2`, `Z.of_nat (length bs)` is the cast
  `(bs.length : Int)`, `flat_map` is `List.flatMap`, `concat` is
  `List.flatten`, and `(_ <= _)%nat` is `Nat`'s `≤`.
- Rocq's combined `(0 < bv_unsigned cnt <= rw_bytes_max)%Z` is the
  conjunction `0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max`.
- `out_tail`'s Rocq `match s with IEof => … | ICons _ _ => …` is a match on
  `s.uncons`, as `StreamSim.eof_tail`'s is; the statements, `IEof`
  included, are unchanged.
- Rocq Section variables become explicit leading arguments, in the order
  Rocq's sections declare them: `f` for `procs`; `cnt f out ec` for Rocq's
  section `Traces` (`out` alone for `out_tail`); and for Rocq's `Drain`, `segs cnt
  Hcnt f out ec Hec LH H_LH`, each declaration taking the ones it uses,
  hypotheses included where the Rocq proof uses them.  Rocq's `Context {A :
  Type}` is an implicit `{A : Type}`.
- Rocq's generated `to_out_ind` and `to_rd_ind` are stated as theorems,
  since Lean generates no non-dependent `_ind`.
- Rocq's `N` entry pc is `Nat` and its `Z` budget is `Int`; the image and
  entry constructors are `Image.mkImage` and `ExecEntry.mkEntry`. -/

namespace LinuxProcessSemantics.Common.DrainSim

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.ReadWrite
open LinuxProcessSemantics.LinuxProcessSem.Specs
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.OmniRun
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
open LinuxProcessSemantics.Common.SimInv
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.Common.CatSim
open LinuxProcessSemantics.Common.SeqExec
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.Common.StreamSim

/-! ## Abstract byte-stream processing -/

/-- Fold the bytes `bs` through `f` from `a`, stopping at the first byte
`f` aborts on. -/
def procs {A : Type} (f : A → byte → Option A) : A → List byte → Option A
  | a, [] => some a
  | a, b :: rest =>
    match f a b with
    | some a' => procs f a' rest
    | none => none

theorem procs_app {A : Type} (f : A → byte → Option A) (bs1 bs2 : List byte) (a : A) :
    procs f a (bs1 ++ bs2) =
      match procs f a bs1 with
      | some a' => procs f a' bs2
      | none => none := by
  induction bs1 generalizing a with
  | nil => rfl
  | cons b bs1 ih =>
    simp only [List.cons_append, procs]
    cases f a b with
    | none => rfl
    | some a' => exact ih a'

/-! ## The abstract trace set -/

/-- An admissible read block for the `cnt`-byte chunked reader. -/
def block_ok (cnt : word) (bs : List byte) : Prop :=
  1 ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ bv_unsigned cnt

/-- All read events of a list of blocks, in order, delivered on channel
`rch`. -/
def reads_ch (rch : word) (blocks : List (List byte)) : List event :=
  List.flatMap (fun bs => List.map (ReadEv rch) bs) blocks

theorem reads_ch_cons (rch : word) (bs : List byte) (blocks : List (List byte)) :
    reads_ch rch (bs :: blocks) = List.map (ReadEv rch) bs ++ reads_ch rch blocks :=
  rfl

/-- All read events of a list of blocks, in order, on channel 0, the only
channel a read can name (`ReadWrite.read_spec` answers -EBADF on every
other). -/
def reads (blocks : List (List byte)) : List event :=
  reads_ch (Z_to_bv 64 0) blocks

theorem reads_cons (bs : List byte) (blocks : List (List byte)) :
    reads (bs :: blocks) = List.map (ReadEv (Z_to_bv 64 0)) bs ++ reads blocks :=
  reads_ch_cons (Z_to_bv 64 0) bs blocks

/-- What the run emits after its last read block: the write-out and exit 0
appear exactly in the chunkings that consumed the whole stream. -/
def out_tail {A : Type} (out : A → List byte) (s : InputStream) (a : A)
    (fs : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs) : List event :=
  match s.uncons with
  | none => List.map (WriteEv (Z_to_bv 64 1)) (out a) ++ [ExitEv (Z_to_bv 64 0) fs]
  | some _ => []

/-- Traces admissible from abstract state `a` on the remaining input `s`,
with reads delivered on channel `rch`: either every block read so far
processes, or the last one aborts and the run exits `ec`.  `rch` is a
parameter of the trace algebra only. -/
def drain_from_ch {A : Type} (cnt : word) (f : A → byte → Option A) (out : A → List byte)
    (ec : word) (rch : word) (a : A) (fs : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs)
    (s : InputStream) (tr : List event) : Prop :=
  (∃ blocks s' a',
    chunks cnt s blocks s' ∧
    procs f a blocks.flatten = some a' ∧
    is_prefix tr (reads_ch rch blocks ++ out_tail out s' a' fs)) ∨
  (∃ blocks bs s' a',
    chunks cnt s (blocks ++ [bs]) s' ∧
    procs f a blocks.flatten = some a' ∧
    procs f a' bs = none ∧
    is_prefix tr (reads_ch rch (blocks ++ [bs]) ++ [ExitEv ec fs]))

/-- The same, reading channel 0. -/
def drain_from {A : Type} (cnt : word) (f : A → byte → Option A) (out : A → List byte)
    (ec : word) (a : A) (fs : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs)
    (s : InputStream) (tr : List event) : Prop :=
  drain_from_ch cnt f out ec (Z_to_bv 64 0) a fs s tr

theorem drain_from_ch_prefix {A : Type} (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (rch : word) (a : A)
    (fs : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs) (s : InputStream)
    (tr tr' : List event) (H : drain_from_ch cnt f out ec rch a fs s tr)
    (Hp' : is_prefix tr' tr) :
    drain_from_ch cnt f out ec rch a fs s tr' := by
  rcases H with ⟨blocks, s', a', HC, Hp, Hpref⟩ |
    ⟨blocks, bs, s', a', HC, Hp, Hn, Hpref⟩
  · exact Or.inl ⟨blocks, s', a', HC, Hp, is_prefix_trans _ _ _ Hp' Hpref⟩
  · exact Or.inr ⟨blocks, bs, s', a', HC, Hp, Hn, is_prefix_trans _ _ _ Hp' Hpref⟩

theorem drain_from_prefix {A : Type} (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (a : A)
    (fs : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs) (s : InputStream)
    (tr tr' : List event) (H : drain_from cnt f out ec a fs s tr)
    (Hp' : is_prefix tr' tr) :
    drain_from cnt f out ec a fs s tr' :=
  drain_from_ch_prefix cnt f out ec (Z_to_bv 64 0) a fs s tr tr' H Hp'

theorem drain_from_ch_nil {A : Type} (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (rch : word) (a : A)
    (fs : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs) (s : InputStream) :
    drain_from_ch cnt f out ec rch a fs s [] :=
  Or.inl ⟨[], s, a, chunks.chunks_nil s, rfl, is_prefix_nil _⟩

theorem drain_from_nil {A : Type} (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (a : A)
    (fs : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs) (s : InputStream) :
    drain_from cnt f out ec a fs s [] :=
  drain_from_ch_nil cnt f out ec (Z_to_bv 64 0) a fs s

/-- At end of input: the finishing phase. -/
theorem drain_from_ch_out {A : Type} (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (rch : word) (a : A)
    (fs : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs) (tr : List event)
    (Hp : is_prefix tr (List.map (WriteEv (Z_to_bv 64 1)) (out a) ++
      [ExitEv (Z_to_bv 64 0) fs])) :
    drain_from_ch cnt f out ec rch a fs IEof tr := by
  refine Or.inl ⟨[], IEof, a, chunks.chunks_nil IEof, rfl, ?_⟩
  simpa [reads_ch, out_tail, uncons_eof] using Hp

theorem drain_from_out {A : Type} (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (a : A)
    (fs : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs) (tr : List event)
    (Hp : is_prefix tr (List.map (WriteEv (Z_to_bv 64 1)) (out a) ++
      [ExitEv (Z_to_bv 64 0) fs])) :
    drain_from cnt f out ec a fs IEof tr :=
  drain_from_ch_out cnt f out ec (Z_to_bv 64 0) a fs tr Hp

theorem drain_from_ch_block {A : Type} (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (rch : word) (a a1 : A)
    (fs : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs) (s : InputStream) (bs : List byte)
    (tr : List event)
    (Hlo : 1 ≤ (bs.length : Int)) (Hhi : (bs.length : Int) ≤ bv_unsigned cnt)
    (Hpre : (stream_take s bs.length).1 = bs)
    (Hs : procs f a bs = some a1)
    (H : drain_from_ch cnt f out ec rch a1 fs (stream_take s bs.length).2 tr) :
    drain_from_ch cnt f out ec rch a fs s (List.map (ReadEv rch) bs ++ tr) := by
  rcases H with ⟨blocks, s', a', HC, Hp, Hpref⟩ |
    ⟨blocks, bsE, s', a', HC, Hp, Hn, Hpref⟩
  · refine Or.inl ⟨bs :: blocks, s', a',
      chunks.chunks_cons s bs blocks s' Hlo Hhi Hpre HC, ?_, ?_⟩
    · simpa only [List.flatten_cons, procs_app, Hs] using Hp
    · rw [reads_ch_cons, List.append_assoc]
      exact is_prefix_app_mono _ _ _ Hpref
  · refine Or.inr ⟨bs :: blocks, bsE, s', a', ?_, ?_, Hn, ?_⟩
    · exact chunks.chunks_cons s bs (blocks ++ [bsE]) s' Hlo Hhi Hpre HC
    · simpa only [List.flatten_cons, procs_app, Hs] using Hp
    · rw [List.cons_append, reads_ch_cons, List.append_assoc]
      exact is_prefix_app_mono _ _ _ Hpref

theorem drain_from_block {A : Type} (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (a a1 : A)
    (fs : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs) (s : InputStream) (bs : List byte)
    (tr : List event)
    (Hlo : 1 ≤ (bs.length : Int)) (Hhi : (bs.length : Int) ≤ bv_unsigned cnt)
    (Hpre : (stream_take s bs.length).1 = bs)
    (Hs : procs f a bs = some a1)
    (H : drain_from cnt f out ec a1 fs (stream_take s bs.length).2 tr) :
    drain_from cnt f out ec a fs s (List.map (ReadEv (Z_to_bv 64 0)) bs ++ tr) :=
  drain_from_ch_block cnt f out ec (Z_to_bv 64 0) a a1 fs s bs tr Hlo Hhi Hpre Hs H

theorem drain_from_ch_err {A : Type} (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (rch : word) (a : A)
    (fs : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs) (s : InputStream) (bs : List byte)
    (tr : List event)
    (Hlo : 1 ≤ (bs.length : Int)) (Hhi : (bs.length : Int) ≤ bv_unsigned cnt)
    (Hpre : (stream_take s bs.length).1 = bs)
    (Hn : procs f a bs = none)
    (Hp : is_prefix tr [ExitEv ec fs]) :
    drain_from_ch cnt f out ec rch a fs s (List.map (ReadEv rch) bs ++ tr) := by
  refine Or.inr ⟨[], bs, (stream_take s bs.length).2, a, ?_, rfl, Hn, ?_⟩
  · exact chunks.chunks_cons s bs [] (stream_take s bs.length).2 Hlo Hhi Hpre
      (chunks.chunks_nil _)
  · simpa only [List.nil_append, reads_ch, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] using is_prefix_app_mono (List.map (ReadEv rch) bs) _ _ Hp

theorem drain_from_err {A : Type} (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (a : A)
    (fs : LinuxProcessSemantics.LinuxProcessSem.Fs.Fs) (s : InputStream) (bs : List byte)
    (tr : List event)
    (Hlo : 1 ≤ (bs.length : Int)) (Hhi : (bs.length : Int) ≤ bv_unsigned cnt)
    (Hpre : (stream_take s bs.length).1 = bs)
    (Hn : procs f a bs = none)
    (Hp : is_prefix tr [ExitEv ec fs]) :
    drain_from cnt f out ec a fs s (List.map (ReadEv (Z_to_bv 64 0)) bs ++ tr) :=
  drain_from_ch_err cnt f out ec (Z_to_bv 64 0) a fs s bs tr Hlo Hhi Hpre Hn Hp

/-! ## Model plumbing -/

theorem fd1chan_with_stdin (s : InputStream) (m : Model) (H : fd1chan m) :
    fd1chan (with_stdin s m) :=
  H

theorem m_fds_with_stdin (s : InputStream) (m : Model) :
    m_fds (with_stdin s m) = m_fds m :=
  rfl

/-! ## The generic drain-loop theory -/

/-- The state runs (deterministically) to some `LH a` loop-head state. -/
def lh_next {A : Type} (segs : List Segment) (LH : A → machine_state → Prop) (a : A)
    (ms : machine_state) : Prop :=
  ∃ ms', msteps segs ms ms' ∧ LH a ms'

/-- A write-pending ecall state that delivers exactly `bs` to stdout,
through WallSim's put-style retry loop, and then reaches exit 0. -/
def WrFin (segs : List Segment) (bs : List byte) (ms : machine_state) : Prop :=
  1 ≤ bs.length ∧ to_wall segs (Z_to_bv 64 1) ms bs (to_exit segs (Z_to_bv 64 0))

/-- The finishing phase: emit `bs` (empty = no write) then exit 0. -/
inductive to_out (segs : List Segment) : List byte → machine_state → Prop
  | tout_exit : ∀ ms, to_exit segs (Z_to_bv 64 0) ms → to_out segs [] ms
  | tout_wr : ∀ bs ms, WrFin segs bs ms → to_out segs bs ms
  | tout_step : ∀ bs ms ms',
      ms.ms_svc_pending = none →
      step segs ms = MachineOk ms' →
      to_out segs bs ms' → to_out segs bs ms

/-- Rocq's generated induction principle for `to_out`.  Lean generates no
non-dependent `_ind`: `to_out.rec`, and the `recOn`/`casesOn` built on it,
take a motive over the derivation, so it is stated here with the Rocq
statement. -/
theorem to_out_ind (segs : List Segment) (P : List byte → machine_state → Prop)
    (f : ∀ ms, to_exit segs (Z_to_bv 64 0) ms → P [] ms)
    (f0 : ∀ bs ms, WrFin segs bs ms → P bs ms)
    (f1 : ∀ bs ms ms', ms.ms_svc_pending = none → step segs ms = MachineOk ms' →
      to_out segs bs ms' → P bs ms' → P bs ms) :
    ∀ l m, to_out segs l m → P l m := by
  intro l m h
  induction h with
  | tout_exit ms he => exact f ms he
  | tout_wr bs ms hw => exact f0 bs ms hw
  | tout_step bs ms ms' hs hst h ih => exact f1 bs ms ms' hs hst h ih

/-- A read-pending ecall state (fd 0, count `cnt`, buffer a1 writable) at
abstract state `a`, together with both continuations.  The `access_okb`
conjunct is `StreamSim.ReadPend`'s, whose docstring carries the kernel
argument for it.  `buf_modeled (out a)` is carried here, on the states the
binary reaches: it is what discharges the write gate for the finishing
phase's writes (`CatSim.buf_modeled` says how), and the per-binary proof
knows its own length caps where a claim about `out` at every abstract state
would not. -/
def ReadPend {A : Type} (segs : List Segment) (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (LH : A → machine_state → Prop) (a : A)
    (ms : machine_state) : Prop :=
  ∃ buf x8,
    ms.ms_svc_pending = some x8 ∧
    bv_unsigned x8 = 63 ∧
    ms_gpr ms 0 = Z_to_bv 64 0 ∧
    ms_gpr ms 1 = buf ∧
    ms_gpr ms 2 = cnt ∧
    (∃ w, read_bytes_map (ms_writable_byte segs ms) buf cnt = some w) ∧
    access_okb buf (bv_unsigned cnt) = true ∧
    to_out segs (out a) (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) ∧
    buf_modeled (out a) ∧
    (∀ bs, 1 ≤ (bs.length : Int) → (bs.length : Int) ≤ bv_unsigned cnt →
      match procs f a bs with
      | some a' => lh_next segs LH a'
          (advance_past_svc (apply_effect ms (mkEffect (len_word bs) [(buf, bs)] [])))
      | none => to_exit segs ec
          (advance_past_svc (apply_effect ms (mkEffect (len_word bs) [(buf, bs)] []))))

/-- Straight line of instructions to a read-pending state. -/
inductive to_rd {A : Type} (segs : List Segment) (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (LH : A → machine_state → Prop) :
    A → machine_state → Prop
  | trd_here : ∀ a ms, ReadPend segs cnt f out ec LH a ms → to_rd segs cnt f out ec LH a ms
  | trd_step : ∀ a ms ms',
      ms.ms_svc_pending = none →
      step segs ms = MachineOk ms' →
      to_rd segs cnt f out ec LH a ms' → to_rd segs cnt f out ec LH a ms

/-- Rocq's generated induction principle for `to_rd`.  Lean generates no
non-dependent `_ind`: `to_rd.rec`, and the `recOn`/`casesOn` built on it,
take a motive over the derivation, so it is stated here with the Rocq
statement. -/
theorem to_rd_ind {A : Type} (segs : List Segment) (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (LH : A → machine_state → Prop)
    (P : A → machine_state → Prop)
    (f0 : ∀ a ms, ReadPend segs cnt f out ec LH a ms → P a ms)
    (f1 : ∀ a ms ms', ms.ms_svc_pending = none → step segs ms = MachineOk ms' →
      to_rd segs cnt f out ec LH a ms' → P a ms' → P a ms) :
    ∀ a m, to_rd segs cnt f out ec LH a m → P a m := by
  intro a m h
  induction h with
  | trd_here ms hr => exact f0 a ms hr
  | trd_step ms ms' hs hst h ih => exact f1 a ms ms' hs hst h ih

theorem msteps_to_rd {A : Type} (segs : List Segment) (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (LH : A → machine_state → Prop)
    (a : A) (ms ms' : machine_state) (H : msteps segs ms ms')
    (Hrd : to_rd segs cnt f out ec LH a ms') :
    to_rd segs cnt f out ec LH a ms := by
  induction H with
  | mst_refl _ => exact Hrd
  | mst_step ms0 ms1 _ Hsvc Hstep _ IH =>
      exact to_rd.trd_step a ms0 ms1 Hsvc Hstep (IH Hrd)

theorem msteps_to_out (segs : List Segment) (bs : List byte) (ms ms' : machine_state)
    (H : msteps segs ms ms') (Ho : to_out segs bs ms') : to_out segs bs ms := by
  induction H with
  | mst_refl ms => exact Ho
  | mst_step ms0 ms1 _ Hsvc Hstep _ IH =>
    exact to_out.tout_step bs ms0 ms1 Hsvc Hstep (IH Ho)

/-- A finishing phase IS a write-all tail derivation down to the exit line
(the `to_out` instruction prefix becomes `twt_step`s). -/
theorem to_out_wall_tail (segs : List Segment) (bs : List byte) (ms : machine_state)
    (H : to_out segs bs ms) :
    to_wall_tail segs (Z_to_bv 64 1) ms bs (to_exit segs (Z_to_bv 64 0)) := by
  induction H with
  | tout_exit ms Hte =>
    exact to_wall_tail.twt_done ms _ Hte
  | tout_wr bs ms HWF =>
    obtain ⟨Hnb, Hw⟩ := HWF
    exact to_wall_tail.twt_more ms bs _ Hnb Hw
  | tout_step bs ms ms' Hsvc Hstep _ IH =>
    exact to_wall_tail.twt_step ms ms' bs _ Hsvc Hstep IH

theorem lh_next_to_rd {A : Type} (segs : List Segment) (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (LH : A → machine_state → Prop)
    (H_LH : ∀ a ms, LH a ms → to_rd segs cnt f out ec LH a ms)
    (a : A) (ms : machine_state) (H : lh_next segs LH a ms) :
    to_rd segs cnt f out ec LH a ms :=
  match H with
  | ⟨ms', Hm, HL⟩ => msteps_to_rd segs cnt f out ec LH a ms ms' Hm (H_LH a ms' HL)

/-! ### Straight lines are event-free star runs -/

theorem to_rd_star {A : Type} (segs : List Segment) (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (LH : A → machine_state → Prop)
    (a : A) (ms : machine_state) (model : Model)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hrd : to_rd segs cnt f out ec LH a ms) :
    ∃ msR, ReadPend segs cnt f out ec LH a msR ∧
      star segs (config.mkCfg ms model) [] (config.mkCfg msR model) := by
  induction Hrd with
  | trd_here ms HRP => exact ⟨ms, HRP, star.star_refl _⟩
  | trd_step ms ms' Hsvc Hstep _ IH =>
    obtain ⟨msR, HRP, Hstar⟩ := IH
    have hi : sstep segs (config.mkCfg ms model) [] (SNext (config.mkCfg ms' model)) :=
      sstep.sstep_instr ms model ms' model Hh Hsvc
        (by rw [mi_account_step_no_lazy _ _ _ Hlazy, Hstep])
    exact ⟨msR, HRP, star.star_step _ [] _ [] _ hi Hstar⟩

theorem msteps_star (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (H : msteps segs ms ms') :
    star segs (config.mkCfg ms model) [] (config.mkCfg ms' model) := by
  induction H with
  | mst_refl ms => exact star.star_refl _
  | mst_step ms ms1 ms2 Hsvc Hstep _ IH =>
    have hi : sstep segs (config.mkCfg ms model) [] (SNext (config.mkCfg ms1 model)) :=
      sstep.sstep_instr ms model ms1 model Hh Hsvc
        (by rw [mi_account_step_no_lazy _ _ _ Hlazy, Hstep])
    exact star.star_step _ [] _ [] _ hi IH

/-! ### The finishing phase: admissibility and exhaustiveness -/

theorem to_out_star_admits (segs : List Segment) (bs : List byte) (ms : machine_state)
    (model : Model) (Hfd1 : fd1chan model) (Hh : m_halted model = none)
    (Hlazy : m_vm_lazy model = []) (Ho : to_out segs bs ms) (Hbm : buf_modeled bs) :
    ∃ c, star segs (config.mkCfg ms model)
      (List.map (WriteEv (Z_to_bv 64 1)) bs ++ [ExitEv (Z_to_bv 64 0) (m_fs model)]) c := by
  induction Ho with
  | tout_exit ms Hte =>
    obtain ⟨c, Hstar⟩ := to_exit_star_admits segs (Z_to_bv 64 0) ms model Hh Hlazy Hte
    rw [band0_255] at Hstar
    exact ⟨c, Hstar⟩
  | tout_wr bs ms HWF =>
    obtain ⟨_, Hwl⟩ := HWF
    refine to_wall_star_admits segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
      ms bs _ Hwl Hbm model _ Hh Hlazy (fd1chan_fdchan model Hfd1) ?_
    intro ms' Hex
    obtain ⟨c, Hstar⟩ := to_exit_star_admits segs (Z_to_bv 64 0) ms' model Hh Hlazy Hex
    rw [band0_255] at Hstar
    exact ⟨c, Hstar⟩
  | tout_step bs ms ms' Hsvc Hstep _ IH =>
    obtain ⟨c, Hstar⟩ := IH Hbm
    have hi : sstep segs (config.mkCfg ms model) [] (SNext (config.mkCfg ms' model)) :=
      sstep.sstep_instr ms model ms' model Hh Hsvc
        (by rw [mi_account_step_no_lazy _ _ _ Hlazy, Hstep])
    exact ⟨c, star.star_step _ [] _ _ _ hi Hstar⟩

theorem to_out_star_only (segs : List Segment) (bs : List byte) (ms : machine_state)
    (model : Model) (Hfd1 : fd1chan model) (Hh : m_halted model = none)
    (Hlazy : m_vm_lazy model = []) (Ho : to_out segs bs ms) (Hbm : buf_modeled bs) :
    ∀ tr c, star segs (config.mkCfg ms model) tr c →
      is_prefix tr
        (List.map (WriteEv (Z_to_bv 64 1)) bs ++ [ExitEv (Z_to_bv 64 0) (m_fs model)]) := by
  induction Ho with
  | tout_exit ms Hte =>
    intro tr c Hstar
    rcases to_exit_star_only segs (Z_to_bv 64 0) ms model Hh Hlazy Hte tr c Hstar with h | h
    · subst tr
      exact is_prefix_nil _
    · subst tr
      rw [band0_255]
      exact is_prefix_refl _
  | tout_wr bs ms HWF =>
    intro tr c Hstar
    obtain ⟨_, Hwl⟩ := HWF
    apply to_wall_star_only segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
      ms bs _ Hwl Hbm model _ Hh Hlazy (fd1chan_fdchan model Hfd1) ?_ tr c Hstar
    intro ms' tr' c' Hex Hstar'
    rcases to_exit_star_only segs (Z_to_bv 64 0) ms' model Hh Hlazy Hex tr' c' Hstar' with h | h
    · subst tr'
      exact is_prefix_nil _
    · subst tr'
      rw [band0_255]
      exact is_prefix_refl _
  | tout_step bs ms ms' Hsvc Hstep Ho IH =>
    intro tr c Hstar
    cases Hstar with
    | star_refl _ => exact is_prefix_nil _
    | star_step _ evs c2 tr2 c3 Hss Hstar2 =>
      obtain ⟨Hevs, Hc2⟩ :=
        sstep_instr_inv segs ms model ms' evs (SNext c2) Hlazy Hsvc Hstep Hss
      subst evs
      cases Hc2
      exact IH Hbm tr2 _ Hstar2

/-! ### Channel-read spec facts at count `cnt`

Thin corollaries of `StreamSim`'s `cnt`-parameterized `read0_*` family,
instantiated at Rocq's section variables `cnt` and `Hcnt`. -/

theorem read0_check_eof_cnt (segs : List Segment) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (ms : machine_state) (x8 : word) (model : Model) (w : List byte)
    (Hno : bv_unsigned x8 = 63)
    (Hfd : fd_lookup (m_fds model) (Z_to_bv 64 0) = some (FdEntry.FdChannel (Z_to_bv 64 0)))
    (Heof : m_stdin model = IEof)
    (Hg0 : ms_gpr ms 0 = Z_to_bv 64 0) (Hg2 : ms_gpr ms 2 = cnt)
    (Hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w)
    (Haok : access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true) :
    check_read (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
      (mkEffect (Z_to_bv 64 0) [] []) model = CheckOk model [] :=
  StreamSim.read0_check_eof cnt Hcnt segs ms x8 model w Hno Hfd Heof Hg0 Hg2 Hw Haok

theorem read0_ok_eof_cnt (segs : List Segment) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (ms : machine_state) (x8 : word) (model : Model) (w : List byte)
    (Hno : bv_unsigned x8 = 63)
    (Hfd : fd_lookup (m_fds model) (Z_to_bv 64 0) = some (FdEntry.FdChannel (Z_to_bv 64 0)))
    (Heof : m_stdin model = IEof)
    (Hg0 : ms_gpr ms 0 = Z_to_bv 64 0) (Hg2 : ms_gpr ms 2 = cnt)
    (Hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w)
    (Haok : access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true) :
    syscall_spec (sys_input segs ms x8) model
      (Ok (mkEffect (Z_to_bv 64 0) [] []) model []) :=
  StreamSim.read0_ok_eof cnt Hcnt segs ms x8 model w Hno Hfd Heof Hg0 Hg2 Hw Haok

theorem read0_check_bytes_cnt (segs : List Segment) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (ms : machine_state) (x8 : word) (model : Model) (w bs : List byte)
    (Hno : bv_unsigned x8 = 63)
    (Hfd : fd_lookup (m_fds model) (Z_to_bv 64 0) = some (FdEntry.FdChannel (Z_to_bv 64 0)))
    (Hg0 : ms_gpr ms 0 = Z_to_bv 64 0) (Hg2 : ms_gpr ms 2 = cnt)
    (Hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w)
    (Haok : access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true)
    (Hlo : 1 ≤ (bs.length : Int)) (Hhi : (bs.length : Int) ≤ bv_unsigned cnt)
    (Hpre : (stream_take (m_stdin model) bs.length).1 = bs) :
    check_read (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
      (mkEffect (len_word bs) [(ms_gpr ms 1, bs)] []) model
      = CheckOk (with_stdin (stream_take (m_stdin model) bs.length).2 model)
          (List.map (ReadEv (Z_to_bv 64 0)) bs) :=
  StreamSim.read0_check_bytes cnt Hcnt segs ms x8 model w bs Hno Hfd Hg0 Hg2 Hw Haok
    Hlo Hhi Hpre

theorem read0_ok_bytes_cnt (segs : List Segment) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (ms : machine_state) (x8 : word) (model : Model) (w bs : List byte)
    (Hno : bv_unsigned x8 = 63)
    (Hfd : fd_lookup (m_fds model) (Z_to_bv 64 0) = some (FdEntry.FdChannel (Z_to_bv 64 0)))
    (Hg0 : ms_gpr ms 0 = Z_to_bv 64 0) (Hg2 : ms_gpr ms 2 = cnt)
    (Hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w)
    (Haok : access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true)
    (Hlo : 1 ≤ (bs.length : Int)) (Hhi : (bs.length : Int) ≤ bv_unsigned cnt)
    (Hpre : (stream_take (m_stdin model) bs.length).1 = bs) :
    syscall_spec (sys_input segs ms x8) model
      (Ok (mkEffect (len_word bs) [(ms_gpr ms 1, bs)] [])
        (with_stdin (stream_take (m_stdin model) bs.length).2 model)
        (List.map (ReadEv (Z_to_bv 64 0)) bs)) :=
  StreamSim.read0_ok_bytes cnt Hcnt segs ms x8 model w bs Hno Hfd Hg0 Hg2 Hw Haok
    Hlo Hhi Hpre

theorem read0_ok_inv_cnt (segs : List Segment) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (ms : machine_state) (x8 : word) (model : Model) (buf : word)
    (w : List byte) (eff : SyscallEffect) (model' : Model) (evs : List event)
    (Hno : bv_unsigned x8 = 63)
    (Hfd : fd_lookup (m_fds model) (Z_to_bv 64 0) = some (FdEntry.FdChannel (Z_to_bv 64 0)))
    (Hg0 : ms_gpr ms 0 = Z_to_bv 64 0) (Hg1 : ms_gpr ms 1 = buf) (Hg2 : ms_gpr ms 2 = cnt)
    (Hw : read_bytes_map (ms_writable_byte segs ms) buf cnt = some w)
    (Haok : access_okb buf (bv_unsigned cnt) = true)
    (Hspec : syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)) :
    (m_stdin model = IEof ∧ eff = mkEffect (Z_to_bv 64 0) [] [] ∧
      model' = model ∧ evs = []) ∨
    (∃ bs : List byte,
      1 ≤ (bs.length : Int) ∧
      (bs.length : Int) ≤ bv_unsigned cnt ∧
      (stream_take (m_stdin model) bs.length).1 = bs ∧
      eff = mkEffect (len_word bs) [(buf, bs)] [] ∧
      model' = with_stdin (stream_take (m_stdin model) bs.length).2 model ∧
      evs = List.map (ReadEv (Z_to_bv 64 0)) bs) :=
  StreamSim.read0_ok_inv cnt Hcnt segs ms x8 model buf w eff model' evs Hno Hfd Hg0 Hg1 Hg2
    Hw Haok Hspec

theorem read0_no_err_cnt (segs : List Segment) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (ms : machine_state) (x8 : word) (model : Model) (w : List byte)
    (Hno : bv_unsigned x8 = 63)
    (Hfd : fd_lookup (m_fds model) (Z_to_bv 64 0) = some (FdEntry.FdChannel (Z_to_bv 64 0)))
    (Hg0 : ms_gpr ms 0 = Z_to_bv 64 0) (Hg2 : ms_gpr ms 2 = cnt)
    (Hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w)
    (Haok : access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true) :
    ¬ syscall_spec (sys_input segs ms x8) model Unmodeled :=
  StreamSim.read0_no_unmodeled cnt Hcnt segs ms x8 model w Hno Hfd Hg0 Hg2 Hw Haok

theorem sstep_read_inv_cnt (segs : List Segment) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (ms : machine_state) (model : Model) (buf x8 : word) (w : List byte)
    (evs : List event) (st : step_to)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd_lookup (m_fds model) (Z_to_bv 64 0) = some (FdEntry.FdChannel (Z_to_bv 64 0)))
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 63)
    (Hg0 : ms_gpr ms 0 = Z_to_bv 64 0) (Hg1 : ms_gpr ms 1 = buf) (Hg2 : ms_gpr ms 2 = cnt)
    (Hw : read_bytes_map (ms_writable_byte segs ms) buf cnt = some w)
    (Haok : access_okb buf (bv_unsigned cnt) = true)
    (Hss : sstep segs (config.mkCfg ms model) evs st) :
    (m_stdin model = IEof ∧ evs = [] ∧
      st = SNext (config.mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) model)) ∨
    (∃ bs : List byte,
      1 ≤ (bs.length : Int) ∧
      (bs.length : Int) ≤ bv_unsigned cnt ∧
      (stream_take (m_stdin model) bs.length).1 = bs ∧
      evs = List.map (ReadEv (Z_to_bv 64 0)) bs ∧
      st = SNext (config.mkCfg
        (advance_past_svc (apply_effect ms (mkEffect (len_word bs) [(buf, bs)] [])))
        (with_stdin (stream_take (m_stdin model) bs.length).2 model))) :=
  StreamSim.sstep_read_inv cnt Hcnt segs ms model buf x8 w evs st Hh Hlazy Hfd Hsvc Hno
    Hg0 Hg1 Hg2 Hw Haok Hss

/-! ### Admissibility: every drain trace is realized -/

/-- One loop iteration: deliver block `bs` off the front of the model's
input and land at the successor state with the shortened input. -/
theorem drain_read_step (segs : List Segment) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (bs : List byte) (ms : machine_state) (model : Model) (buf x8 : word) (w : List byte)
    (HM : M_loop model)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : bv_unsigned x8 = 63)
    (Hg0 : ms_gpr ms 0 = Z_to_bv 64 0) (Hg1 : ms_gpr ms 1 = buf)
    (Hg2 : ms_gpr ms 2 = cnt)
    (Hw : read_bytes_map (ms_writable_byte segs ms) buf cnt = some w)
    (Haok : access_okb buf (bv_unsigned cnt) = true)
    (Hlo : 1 ≤ (bs.length : Int)) (Hhi : (bs.length : Int) ≤ bv_unsigned cnt)
    (Hpre : (stream_take (m_stdin model) bs.length).1 = bs) :
    sstep segs (config.mkCfg ms model) (List.map (ReadEv (Z_to_bv 64 0)) bs)
      (SNext (config.mkCfg
        (advance_past_svc (apply_effect ms (mkEffect (len_word bs) [(buf, bs)] [])))
        (with_stdin (stream_take (m_stdin model) bs.length).2 model))) := by
  obtain ⟨Hfd0, _, Hh, Hlazy⟩ := HM
  refine sstep.sstep_syscall ms model x8
    (mkEffect (len_word bs) [(buf, bs)] [])
    (with_stdin (stream_take (m_stdin model) bs.length).2 model)
    (with_stdin (stream_take (m_stdin model) bs.length).2 model)
    (List.map (ReadEv (Z_to_bv 64 0)) bs) Hh Hsvc ?_ Hh ?_
  · rw [← Hg1] at Hw Haok ⊢
    exact read0_ok_bytes_cnt segs cnt Hcnt ms x8 model w bs
      Hno Hfd0 Hg0 Hg2 Hw Haok Hlo Hhi Hpre
  · exact materialize_model_accesses_no_lazy _ _
      (by rw [m_vm_lazy_with_stdin]; exact Hlazy)

theorem drain_star_admits_ok {A : Type} (segs : List Segment) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (f : A → byte → Option A) (out : A → List byte) (ec : word)
    (LH : A → machine_state → Prop)
    (H_LH : ∀ a ms, LH a ms → to_rd segs cnt f out ec LH a ms)
    (s : InputStream) (blocks : List (List byte)) (s' : InputStream)
    (HC : chunks cnt s blocks s') :
    ∀ (a a' : A) (ms : machine_state) (model : Model),
      M_loop model → m_stdin model = s → to_rd segs cnt f out ec LH a ms →
      procs f a blocks.flatten = some a' →
      ∃ c, star segs (config.mkCfg ms model)
        (reads blocks ++ out_tail out s' a' (m_fs model)) c := by
  induction HC with
  | chunks_nil s =>
    intro a a' ms model HM Hst Hrd Hp
    have ha : a = a' := Option.some.inj Hp
    subst a'
    obtain ⟨Hfd0, Hfd1, Hh, Hlazy⟩ := HM
    cases hu : s.uncons with
    | none =>
      have hb : s.byte_at 0 = none := by
        unfold InputStream.uncons at hu
        cases hb : s.byte_at 0 with
        | none => rfl
        | some b =>
          rw [hb] at hu
          cases hu
      have hs : s = IEof := InputStream.eq_eof_of_head_none s hb
      subst hs
      obtain ⟨msR, ⟨buf, x8, Hsvc, Hno, Hg0, Hg1, Hg2, ⟨w, Hw⟩,
        Haok, Hout, Hobm, _⟩, Hstar0⟩ :=
        to_rd_star segs cnt f out ec LH a ms model Hh Hlazy Hrd
      subst buf
      have hspec := read0_ok_eof_cnt segs cnt Hcnt msR x8 model w
        Hno Hfd0 Hst Hg0 Hg2 Hw Haok
      have HssE := sstep.sstep_syscall msR model x8
        (mkEffect (Z_to_bv 64 0) [] []) model model [] Hh Hsvc hspec Hh
        (materialize_model_accesses_no_lazy model _ Hlazy)
      rw [apply_effect_no_write] at HssE
      obtain ⟨c, Hstar2⟩ := to_out_star_admits segs (out a) _ model
        Hfd1 Hh Hlazy Hout Hobm
      have hall := star_trans _ _ _ _ _ _ Hstar0
        (star.star_step _ _ _ _ _ HssE Hstar2)
      exact ⟨c, hall⟩
    | some p =>
      have ht : out_tail out s a (m_fs model) = [] := by
        unfold out_tail
        rw [hu]
      refine ⟨config.mkCfg ms model, ?_⟩
      rw [ht]
      exact star.star_refl _
  | chunks_cons s bs blocks s'' Hlo Hhi Hpre _ IH =>
    intro a a' ms model HM Hst Hrd Hp
    rw [List.flatten_cons, procs_app] at Hp
    cases hp : procs f a bs with
    | none => simp only [hp] at Hp; cases Hp
    | some a1 =>
      simp only [hp] at Hp
      have HM' : M_loop (with_stdin (stream_take s bs.length).2 model) := by
        rw [← Hst]
        exact M_loop_take bs.length model HM
      obtain ⟨Hfd0, Hfd1, Hh, Hlazy⟩ := HM
      obtain ⟨msR, ⟨buf, x8, Hsvc, Hno, Hg0, Hg1, Hg2, ⟨w, Hw⟩,
        Haok, Hout, Hobm, Hbytes⟩, Hstar0⟩ :=
        to_rd_star segs cnt f out ec LH a ms model Hh Hlazy Hrd
      have Hcont := Hbytes bs Hlo Hhi
      rw [hp] at Hcont
      have Hrd1 := lh_next_to_rd segs cnt f out ec LH H_LH a1 _ Hcont
      have HssR := drain_read_step segs cnt Hcnt bs msR model buf x8 w
        ⟨Hfd0, Hfd1, Hh, Hlazy⟩ Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hlo Hhi
        (by rw [Hst]; exact Hpre)
      rw [Hst] at HssR
      obtain ⟨c, Hstar3⟩ := IH a1 a' _ _ HM' rfl Hrd1 Hp
      have hall := star_trans _ _ _ _ _ _ Hstar0
        (star.star_step _ _ _ _ _ HssR Hstar3)
      refine ⟨c, ?_⟩
      rw [reads_cons, List.append_assoc]
      exact hall

theorem drain_star_admits_err {A : Type} (segs : List Segment) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (f : A → byte → Option A) (out : A → List byte) (ec : word)
    (Hec : bv_unsigned ec < 256)
    (LH : A → machine_state → Prop)
    (H_LH : ∀ a ms, LH a ms → to_rd segs cnt f out ec LH a ms)
    (s : InputStream) (blocks : List (List byte)) (s1 : InputStream)
    (HC : chunks cnt s blocks s1) :
    ∀ (a a' : A) (bsE : List byte) (ms : machine_state) (model : Model),
      M_loop model → m_stdin model = s → to_rd segs cnt f out ec LH a ms →
      procs f a blocks.flatten = some a' →
      1 ≤ (bsE.length : Int) → (bsE.length : Int) ≤ bv_unsigned cnt →
      (stream_take s1 bsE.length).1 = bsE →
      procs f a' bsE = none →
      ∃ c, star segs (config.mkCfg ms model)
        (reads (blocks ++ [bsE]) ++ [ExitEv ec (m_fs model)]) c := by
  induction HC with
  | chunks_nil s =>
    intro a a' bsE ms model HM Hst Hrd Hp HloE HhiE HpreE Hn
    have haa : a = a' := Option.some.inj Hp
    subst a'
    have Hh := HM.2.2.1
    have Hlazy := HM.2.2.2
    obtain ⟨msR, ⟨buf, x8, Hsvc, Hno, Hg0, Hg1, Hg2, ⟨w, Hw⟩,
      Haok, _, _, Hbytes⟩, Hstar0⟩ :=
      to_rd_star segs cnt f out ec LH a ms model Hh Hlazy Hrd
    have Hcont := Hbytes bsE HloE HhiE
    rw [Hn] at Hcont
    have HM' : M_loop (with_stdin (stream_take s bsE.length).2 model) := by
      rw [← Hst]
      exact M_loop_take bsE.length model HM
    obtain ⟨_, _, Hh', Hlazy'⟩ := HM'
    have HssR := drain_read_step segs cnt Hcnt bsE msR model buf x8 w
      HM Hsvc Hno Hg0 Hg1 Hg2 Hw Haok HloE HhiE (by rw [Hst]; exact HpreE)
    rw [Hst] at HssR
    obtain ⟨c, Hstar2⟩ := to_exit_star_admits segs ec _
      (with_stdin (stream_take s bsE.length).2 model) Hh' Hlazy' Hcont
    rw [land_255_small ec Hec] at Hstar2
    have hall := star_trans _ _ _ _ _ _ Hstar0
      (star.star_step _ _ _ _ _ HssR Hstar2)
    refine ⟨c, ?_⟩
    simpa only [List.nil_append, reads, reads_ch, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, m_fs, with_stdin] using hall
  | chunks_cons s bs blocks s'' Hlo Hhi Hpre _ IH =>
    intro a a' bsE ms model HM Hst Hrd Hp HloE HhiE HpreE Hn
    rw [List.flatten_cons, procs_app] at Hp
    cases Hp1 : procs f a bs with
    | none => simp only [Hp1] at Hp; cases Hp
    | some a1 =>
      simp only [Hp1] at Hp
      have Hh := HM.2.2.1
      have Hlazy := HM.2.2.2
      obtain ⟨msR, ⟨buf, x8, Hsvc, Hno, Hg0, Hg1, Hg2, ⟨w, Hw⟩,
        Haok, _, _, Hbytes⟩, Hstar0⟩ :=
        to_rd_star segs cnt f out ec LH a ms model Hh Hlazy Hrd
      have Hcont := Hbytes bs Hlo Hhi
      rw [Hp1] at Hcont
      have HM' : M_loop (with_stdin (stream_take s bs.length).2 model) := by
        rw [← Hst]
        exact M_loop_take bs.length model HM
      have HssR := drain_read_step segs cnt Hcnt bs msR model buf x8 w
        HM Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hlo Hhi (by rw [Hst]; exact Hpre)
      rw [Hst] at HssR
      have Hrd1 := lh_next_to_rd segs cnt f out ec LH H_LH a1 _ Hcont
      obtain ⟨c, Hstar3⟩ := IH a1 a' bsE _ _ HM' rfl Hrd1 Hp HloE HhiE HpreE Hn
      have hall := star_trans _ _ _ _ _ _ Hstar0
        (star.star_step _ _ _ _ _ HssR Hstar3)
      refine ⟨c, ?_⟩
      rw [List.cons_append, reads_cons, List.append_assoc]
      exact hall

/-! ### Exhaustiveness: every run trace is a drain trace -/

theorem star_drain_only {A : Type} (segs : List Segment) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (f : A → byte → Option A) (out : A → List byte) (ec : word)
    (Hec : bv_unsigned ec < 256)
    (LH : A → machine_state → Prop)
    (H_LH : ∀ a ms, LH a ms → to_rd segs cnt f out ec LH a ms)
    (c0 : config) (tr : List event) (c' : config) (Hstar : star segs c0 tr c') :
    ∀ (a : A) (ms : machine_state) (model : Model),
      c0 = config.mkCfg ms model → M_loop model → to_rd segs cnt f out ec LH a ms →
      drain_from cnt f out ec a (m_fs model) (m_stdin model) tr := by
  induction Hstar with
  | star_refl c =>
    intro a ms model _ _ _
    exact drain_from_nil cnt f out ec a (m_fs model) (m_stdin model)
  | star_step c1 evs c2 tr2 c3 Hss Hrest IH =>
    intro a ms model Heq HM Hrd
    subst Heq
    obtain ⟨Hfd0, Hfd1, Hh, Hlazy⟩ := HM
    cases Hrd with
    | trd_here _ HRP =>
      obtain ⟨buf, x8, Hsvc, Hno, Hg0, Hg1, Hg2, ⟨w, Hw⟩,
        Haok, Hout, Hobm, Hbytes⟩ := HRP
      rcases sstep_read_inv_cnt segs cnt Hcnt ms model buf x8 w evs (SNext c2)
          Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss with
        ⟨Hs, Hevs, Hc2⟩ | ⟨bs, Hlo, Hhi, Hpre, Hevs, Hc2⟩
      · cases Hc2
        subst Hevs
        have Hpref := to_out_star_only segs (out a) _ model Hfd1 Hh Hlazy
          Hout Hobm tr2 c3 Hrest
        simp only [List.nil_append]
        rw [Hs]
        exact drain_from_out cnt f out ec a (m_fs model) tr2 Hpref
      · cases Hc2
        subst Hevs
        have Hcont := Hbytes bs Hlo Hhi
        cases hp : procs f a bs with
        | some a1 =>
          rw [hp] at Hcont
          have Hrd1 := lh_next_to_rd segs cnt f out ec LH H_LH a1 _ Hcont
          exact drain_from_block cnt f out ec a a1 (m_fs model) (m_stdin model)
            bs tr2 Hlo Hhi Hpre hp
            (IH a1 _ _ rfl (M_loop_take bs.length model ⟨Hfd0, Hfd1, Hh, Hlazy⟩) Hrd1)
        | none =>
          rw [hp] at Hcont
          apply drain_from_err cnt f out ec a (m_fs model) (m_stdin model)
            bs tr2 Hlo Hhi Hpre hp
          rcases to_exit_star_only segs ec _
              (with_stdin (stream_take (m_stdin model) bs.length).2 model)
              Hh (by rw [m_vm_lazy_with_stdin]; exact Hlazy)
              Hcont tr2 c3 Hrest with h | h
          · subst h
            exact is_prefix_nil _
          · subst h
            rw [land_255_small ec Hec]
            exact is_prefix_refl _
    | trd_step _ ms' Hsvc Hstep Hrd' =>
      obtain ⟨Hevs, Hc2⟩ :=
        sstep_instr_inv segs ms model ms' evs (SNext c2) Hlazy Hsvc Hstep Hss
      cases Hc2
      subst Hevs
      exact IH a _ model rfl ⟨Hfd0, Hfd1, Hh, Hlazy⟩ Hrd'

/-! ### No error: the phase invariant -/

def dinv {A : Type} (segs : List Segment) (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (LH : A → machine_state → Prop) (c : config) : Prop :=
  (M_loop c.cfg_model ∧ ∃ a, to_rd segs cnt f out ec LH a c.cfg_ms) ∨
  (fd1chan c.cfg_model ∧ m_halted c.cfg_model = none ∧
    m_vm_lazy c.cfg_model = [] ∧
    ∃ rest, buf_modeled rest ∧
      to_wall_tail segs (Z_to_bv 64 1) c.cfg_ms rest (to_exit segs (Z_to_bv 64 0))) ∨
  on_path segs (Z_to_bv 64 0) c ∨
  on_path segs ec c

theorem wall_out_dinv_step {A : Type} (segs : List Segment) (cnt : word)
    (f : A → byte → Option A) (out : A → List byte) (ec : word)
    (LH : A → machine_state → Prop)
    (rest : List byte) (ms : machine_state) (model : Model) (evs : List event)
    (ms' : machine_state) (model' : Model)
    (Hfd1 : fd1chan model) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hbm : buf_modeled rest)
    (Ht : to_wall_tail segs (Z_to_bv 64 1) ms rest (to_exit segs (Z_to_bv 64 0)))
    (Hss : sstep segs (config.mkCfg ms model) evs (SNext (config.mkCfg ms' model'))) :
    dinv segs cnt f out ec LH (config.mkCfg ms' model') := by
  have Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model :=
    fd1chan_fdchan model Hfd1
  cases Ht with
  | twt_done _ _ Hk =>
    exact Or.inr (Or.inr (Or.inl
      (on_path_step segs (Z_to_bv 64 0) _ evs _
        (Or.inl ⟨Hh, Hlazy, Hk⟩) Hss)))
  | twt_more _ rest _ _ Hwl =>
    obtain ⟨n, _, _, _, Hc2, Ht2⟩ :=
      sstep_to_wall_inv segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
        ms rest (to_exit segs (Z_to_bv 64 0)) model evs _
        Hh Hlazy Hfdc Hbm Hwl Hss
    cases Hc2
    exact Or.inr (Or.inl
      ⟨Hfd1, Hh, Hlazy, rest.drop n, buf_modeled_skipn n rest Hbm, Ht2⟩)
  | twt_step _ msS' rest _ Hsvc Hstep Ht' =>
    obtain ⟨_, Hc2⟩ :=
      sstep_instr_inv segs ms model msS' evs _ Hlazy Hsvc Hstep Hss
    cases Hc2
    exact Or.inr (Or.inl ⟨Hfd1, Hh, Hlazy, rest, Hbm, Ht'⟩)

theorem dinv_step {A : Type} (segs : List Segment) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (f : A → byte → Option A) (out : A → List byte) (ec : word)
    (LH : A → machine_state → Prop)
    (H_LH : ∀ a ms, LH a ms → to_rd segs cnt f out ec LH a ms)
    (c : config) (evs : List event) (c' : config)
    (Hinv : dinv segs cnt f out ec LH c) (Hss : sstep segs c evs (SNext c')) :
    dinv segs cnt f out ec LH c' := by
  obtain ⟨ms, model⟩ := c
  obtain ⟨ms', model'⟩ := c'
  rcases Hinv with ⟨HM, a, Hrd⟩ | ⟨Hfd1, Hh, Hlazy, rest, Hbm, Ht⟩ | Hop | Hop
  · obtain ⟨Hfd0, Hfd1, Hh, Hlazy⟩ := HM
    cases Hrd with
    | trd_here _ HRP =>
      obtain ⟨buf, x8, Hsvc, Hno, Hg0, Hg1, Hg2, ⟨w, Hw⟩, Haok,
        Hout, Hobm, Hbytes⟩ := HRP
      rcases sstep_read_inv_cnt segs cnt Hcnt ms model buf x8 w evs _
          Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss with
        ⟨_, _, Hc2⟩ | ⟨bs, Hlo, Hhi, _, _, Hc2⟩
      · cases Hc2
        exact Or.inr (Or.inl ⟨Hfd1, Hh, Hlazy, out a, Hobm,
          to_out_wall_tail segs (out a) _ Hout⟩)
      · cases Hc2
        have Hcont := Hbytes bs Hlo Hhi
        cases hp : procs f a bs with
        | none =>
          rw [hp] at Hcont
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Hh, Hlazy, Hcont⟩)))
        | some a1 =>
          rw [hp] at Hcont
          exact Or.inl ⟨M_loop_take bs.length model ⟨Hfd0, Hfd1, Hh, Hlazy⟩,
            a1, lh_next_to_rd segs cnt f out ec LH H_LH a1 _ Hcont⟩
    | trd_step _ ms1 Hsvc Hstep Hrd' =>
      obtain ⟨_, Hc2⟩ := sstep_instr_inv segs ms model ms1 evs _ Hlazy Hsvc Hstep Hss
      cases Hc2
      exact Or.inl ⟨⟨Hfd0, Hfd1, Hh, Hlazy⟩, a, Hrd'⟩
  · exact wall_out_dinv_step segs cnt f out ec LH rest ms model evs ms' model'
      Hfd1 Hh Hlazy Hbm Ht Hss
  · exact Or.inr (Or.inr (Or.inl (on_path_step segs (Z_to_bv 64 0) _ evs _ Hop Hss)))
  · exact Or.inr (Or.inr (Or.inr (on_path_step segs ec _ evs _ Hop Hss)))

theorem dinv_no_error {A : Type} (segs : List Segment) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (f : A → byte → Option A) (out : A → List byte) (ec : word)
    (LH : A → machine_state → Prop)
    (c : config) (evs : List event) (Hinv : dinv segs cnt f out ec LH c) :
    ¬ sstep segs c evs SError := by
  intro Hss
  obtain ⟨ms, model⟩ := c
  rcases Hinv with ⟨HM, a, Hrd⟩ | ⟨Hfd1, Hh, Hlazy, rest, Hbm, Ht⟩ | Hop | Hop
  · obtain ⟨Hfd0, _, Hh, Hlazy⟩ := HM
    cases Hrd with
    | trd_here _ HRP =>
      obtain ⟨buf, x8, Hsvc, Hno, Hg0, Hg1, Hg2, ⟨w, Hw⟩, Haok, _, _, _⟩ := HRP
      rcases sstep_read_inv cnt Hcnt segs ms model buf x8 w evs SError
          Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss with
        ⟨_, _, Hc2⟩ | ⟨_, _, _, _, _, Hc2⟩
      · cases Hc2
      · cases Hc2
    | trd_step _ ms1 Hsvc Hstep _ =>
      obtain ⟨_, Hc2⟩ := sstep_instr_inv segs ms model ms1 evs SError Hlazy Hsvc Hstep Hss
      cases Hc2
  · have Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model := fd1chan_fdchan model Hfd1
    cases Ht with
    | twt_done _ _ Hk =>
      exact on_path_no_error segs (Z_to_bv 64 0) _ evs (Or.inl ⟨Hh, Hlazy, Hk⟩) Hss
    | twt_more _ _ _ _ Hwl =>
      exact to_wall_no_error_sstep segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
        ms rest (to_exit segs (Z_to_bv 64 0)) model evs Hh Hlazy Hfdc Hbm Hwl Hss
    | twt_step _ msS' _ _ HsvcS HstepS _ =>
      obtain ⟨_, Hc2⟩ := sstep_instr_inv segs ms model msS' evs SError Hlazy HsvcS HstepS Hss
      cases Hc2
  · exact on_path_no_error segs (Z_to_bv 64 0) _ evs Hop Hss
  · exact on_path_no_error segs ec _ evs Hop Hss

theorem star_dinv {A : Type} (segs : List Segment) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (f : A → byte → Option A) (out : A → List byte) (ec : word)
    (LH : A → machine_state → Prop)
    (H_LH : ∀ a ms, LH a ms → to_rd segs cnt f out ec LH a ms) :
    ∀ c tr c', dinv segs cnt f out ec LH c → star segs c tr c' →
      dinv segs cnt f out ec LH c' :=
  star_inv segs (dinv segs cnt f out ec LH) (dinv_step segs cnt Hcnt f out ec LH H_LH)

theorem to_rd_no_error {A : Type} (segs : List Segment) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (f : A → byte → Option A) (out : A → List byte) (ec : word)
    (LH : A → machine_state → Prop)
    (H_LH : ∀ a ms, LH a ms → to_rd segs cnt f out ec LH a ms)
    (a : A) (ms : machine_state) (model : Model)
    (HM : M_loop model) (Hrd : to_rd segs cnt f out ec LH a ms) :
    ¬ reaches_error segs (config.mkCfg ms model) :=
  inv_no_reaches_error segs (dinv segs cnt f out ec LH)
    (dinv_step segs cnt Hcnt f out ec LH H_LH) (dinv_no_error segs cnt Hcnt f out ec LH)
    _ (Or.inl ⟨HM, a, Hrd⟩)

/-! ### Whole-run packaging from the initial state -/

theorem drain_obs_iff {A : Type} (segs : List Segment) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (f : A → byte → Option A) (out : A → List byte) (ec : word)
    (Hec : bv_unsigned ec < 256)
    (LH : A → machine_state → Prop)
    (H_LH : ∀ a ms, LH a ms → to_rd segs cnt f out ec LH a ms)
    (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int)
    (inp : ProcInput) (a0 : A)
    (Hrd : to_rd segs cnt f out ec LH a0 (init_machine_state segs pc ph sp rnd inp.in_argv
      inp.in_envp inp.in_uid inp.in_hwcap)) :
    ∀ tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr ↔
      drain_from cnt f out ec a0 inp.in_fs inp.in_stdin tr := by
  intro tr
  have HM0 := init_M_loop (segments_reserved segs) brk0 mb sp lim inp
  constructor
  · rintro ⟨tr', c, Hstar, Hp⟩
    have Hd := star_drain_only segs cnt Hcnt f out ec Hec LH H_LH
      _ tr' c Hstar a0 _ _ rfl HM0 Hrd
    exact drain_from_prefix cnt f out ec a0 inp.in_fs inp.in_stdin tr' tr Hd Hp
  · intro Hd
    rcases Hd with ⟨blocks, s', a', HC, Hp, Hpref⟩ |
      ⟨blocks, bsE, s', a', HC, Hp, Hn, Hpref⟩
    · obtain ⟨c, Hstar⟩ :=
        drain_star_admits_ok segs cnt Hcnt f out ec LH H_LH
          inp.in_stdin blocks s' HC a0 a' _ _ HM0 rfl Hrd Hp
      exact ⟨_, c, Hstar, Hpref⟩
    · obtain ⟨s1, HC1, HC2⟩ :=
        chunks_split cnt blocks [bsE] inp.in_stdin s' HC
      obtain ⟨HloE, HhiE, HpreE, _⟩ := chunks_single_inv cnt s1 bsE s' HC2
      obtain ⟨c, Hstar⟩ :=
        drain_star_admits_err segs cnt Hcnt f out ec Hec LH H_LH
          inp.in_stdin blocks s1 HC1 a0 a' bsE _ _ HM0 rfl Hrd Hp
          HloE HhiE HpreE Hn
      exact ⟨_, c, Hstar, Hpref⟩

theorem drain_no_error {A : Type} (segs : List Segment) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (f : A → byte → Option A) (out : A → List byte) (ec : word)
    (LH : A → machine_state → Prop)
    (H_LH : ∀ a ms, LH a ms → to_rd segs cnt f out ec LH a ms)
    (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int)
    (inp : ProcInput) (a0 : A)
    (Hrd : to_rd segs cnt f out ec LH a0 (init_machine_state segs pc ph sp rnd inp.in_argv
      inp.in_envp inp.in_uid inp.in_hwcap)) :
    ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) :=
  to_rd_no_error segs cnt Hcnt f out ec LH H_LH a0 _ _
    (init_M_loop (segments_reserved segs) brk0 mb sp lim inp) Hrd

/-! ### The omni reading

As for `StreamSim`, the loop invariant is a proof of `OmniRun.coexec …
never_errors` by coinduction, and the trace characterisation is the
prefix judgment. -/

theorem to_rd_coexec {A : Type} (segs : List Segment) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (f : A → byte → Option A) (out : A → List byte) (ec : word)
    (LH : A → machine_state → Prop)
    (H_LH : ∀ a ms, LH a ms → to_rd segs cnt f out ec LH a ms)
    (a : A) (ms : machine_state) (model : Model)
    (HM : M_loop model) (Hrd : to_rd segs cnt f out ec LH a ms) :
    coexec segs (config.mkCfg ms model) never_errors :=
  inv_coexec segs (dinv segs cnt f out ec LH)
    (dinv_step segs cnt Hcnt f out ec LH H_LH) (dinv_no_error segs cnt Hcnt f out ec LH)
    _ (Or.inl ⟨HM, a, Hrd⟩)

theorem drain_omni_corun {A : Type} (segs : List Segment) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (f : A → byte → Option A) (out : A → List byte) (ec : word)
    (LH : A → machine_state → Prop)
    (H_LH : ∀ a ms, LH a ms → to_rd segs cnt f out ec LH a ms)
    (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int)
    (inp : ProcInput) (a0 : A)
    (Hrd : to_rd segs cnt f out ec LH a0 (init_machine_state segs pc ph sp rnd inp.in_argv
      inp.in_envp inp.in_uid inp.in_hwcap)) :
    omni_corun (Image.mkImage segs pc ph) lim (ExecEntry.mkEntry sp brk0 mb rnd) inp
      never_errors :=
  to_rd_coexec segs cnt Hcnt f out ec LH H_LH a0 _ _
    (init_M_loop (segments_reserved segs) brk0 mb sp lim inp) Hrd

theorem drain_omni_cosafe {A : Type} (segs : List Segment) (cnt : word)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (f : A → byte → Option A) (out : A → List byte) (ec : word)
    (Hec : bv_unsigned ec < 256)
    (LH : A → machine_state → Prop)
    (H_LH : ∀ a ms, LH a ms → to_rd segs cnt f out ec LH a ms)
    (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int)
    (inp : ProcInput) (a0 : A)
    (Hrd : to_rd segs cnt f out ec LH a0 (init_machine_state segs pc ph sp rnd inp.in_argv
      inp.in_envp inp.in_uid inp.in_hwcap)) :
    omni_cosafe (Image.mkImage segs pc ph) lim (ExecEntry.mkEntry sp brk0 mb rnd) inp
      (drain_from cnt f out ec a0 inp.in_fs inp.in_stdin) := by
  have Hobs := drain_obs_iff segs cnt Hcnt f out ec Hec LH H_LH
    pc ph sp brk0 mb rnd lim inp a0 Hrd
  refine (cosafe_obs_iff segs (init_config segs pc ph sp brk0 mb rnd lim inp)
    (drain_from cnt f out ec a0 inp.in_fs inp.in_stdin) ?_).2 ?_
  · intro tr tr' Htr Hp
    exact (Hobs tr').1
      (obs_trace_prefix_closed segs _ tr tr' ((Hobs tr).2 Htr) Hp)
  · intro tr Htr
    exact (Hobs tr).1 Htr

/-! ## Pair equivalence

`drain_from cnt f out ec a0 fs0 stdin0` does not mention the binary, so two
binaries that both satisfy it are observably equivalent, on the same input
stream and at the same chunk count `cnt`. -/

/-- The omni equivalence of two drain loops on the same input stream, at
the two role budgets. -/
theorem drain_omni_strong_equiv (A : Type) (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (a0 : A)
    (source_segs : List Segment) (rLH : A → machine_state → Prop) (rpc : Nat)
    (rph : PhdrInfo) (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (target_segs : List Segment) (aLH : A → machine_state → Prop) (apc : Nat)
    (aph : PhdrInfo) (asp abrk amb : word) (arnd : EntryDraw) (inp : ProcInput)
    (Hec : bv_unsigned ec < 256)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (HrLH : ∀ a ms, rLH a ms → to_rd source_segs cnt f out ec rLH a ms)
    (HaLH : ∀ a ms, aLH a ms → to_rd target_segs cnt f out ec aLH a ms)
    (Hr : to_rd source_segs cnt f out ec rLH a0
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap))
    (Ha : to_rd target_segs cnt f out ec aLH a0
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)) :
    omni_strong_equiv (Image.mkImage source_segs rpc rph) (Image.mkImage target_segs apc aph)
      (ExecEntry.mkEntry rsp rbrk rmb rrnd) (ExecEntry.mkEntry asp abrk amb arnd) inp := by
  refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
  · exact coexec_conseq _ _ _ _
      (drain_omni_corun source_segs cnt Hcnt f out ec rLH HrLH
        rpc rph rsp rbrk rmb rrnd source_alloc_limit inp a0 Hr)
      (never_errors_covered _)
  · refine (trace_equiv_iff_omni _ _ _ _ _ _ _).1 ?_
    intro tr
    exact (drain_obs_iff source_segs cnt Hcnt f out ec Hec rLH HrLH
        rpc rph rsp rbrk rmb rrnd source_alloc_limit inp a0 Hr tr).trans
      (drain_obs_iff target_segs cnt Hcnt f out ec Hec aLH HaLH
        apc aph asp abrk amb arnd target_alloc_limit inp a0 Ha tr).symm
  · exact drain_omni_corun target_segs cnt Hcnt f out ec aLH HaLH
      apc aph asp abrk amb arnd target_alloc_limit inp a0 Ha

theorem drain_strong_equiv (A : Type) (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (a0 : A)
    (source_segs : List Segment) (rLH : A → machine_state → Prop) (rpc : Nat)
    (rph : PhdrInfo) (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (aLH : A → machine_state → Prop) (apc : Nat)
    (aph : PhdrInfo) (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (inp : ProcInput)
    (Hec : bv_unsigned ec < 256)
    (Hcnt : 0 < bv_unsigned cnt ∧ bv_unsigned cnt ≤ rw_bytes_max)
    (HrLH : ∀ a ms, rLH a ms → to_rd source_segs cnt f out ec rLH a ms)
    (HaLH : ∀ a ms, aLH a ms → to_rd target_segs cnt f out ec aLH a ms)
    (Hr : to_rd source_segs cnt f out ec rLH a0
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap))
    (Ha : to_rd target_segs cnt f out ec aLH a0
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)) :
    EquivalenceDefinition.Equivalence.modeled
        (run (Image.mkImage source_segs rpc rph) rlim (ExecEntry.mkEntry rsp rbrk rmb rrnd) inp) ∧
      EquivalenceDefinition.Equivalence.equiv
        (run (Image.mkImage source_segs rpc rph) rlim (ExecEntry.mkEntry rsp rbrk rmb rrnd) inp)
        (run (Image.mkImage target_segs apc aph) alim (ExecEntry.mkEntry asp abrk amb arnd)
          inp) := by
  refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
  · exact no_error_run_modeled source_segs rpc rph rsp rbrk rmb rrnd rlim inp
      (drain_no_error source_segs cnt Hcnt f out ec rLH HrLH
        rpc rph rsp rbrk rmb rrnd rlim inp a0 Hr)
  · intro tr
    exact (drain_obs_iff source_segs cnt Hcnt f out ec Hec rLH HrLH
        rpc rph rsp rbrk rmb rrnd rlim inp a0 Hr tr).trans
      (drain_obs_iff target_segs cnt Hcnt f out ec Hec aLH HaLH
        apc aph asp abrk amb arnd alim inp a0 Ha tr).symm
  · exact drain_no_error target_segs cnt Hcnt f out ec aLH HaLH
      apc aph asp abrk amb arnd alim inp a0 Ha

end LinuxProcessSemantics.Common.DrainSim
