import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs
import LpsRunner.Trace
import LpsRunner.Declines

/-! # LpsRunner.Replay — the recorded run, judged again by the Lean checker

Test tooling: nothing under `LpsRunner/` is part of the trusted
specification, and no proof depends on it.

This is `testing/syscall-check/main.ml`'s `--replay` for the Lean
checker: the model is seeded from the trace header exactly as `replay`
there seeds it, every `syscall` record is turned into the
`(SyscallInput, SyscallEffect)` pair the checker was given, and
`Checks.ExecutableSpecs.check_syscall_for_run` is folded over the run --
the model threads forward on an admitted step and is left alone
otherwise, as `run_check` leaves it.  Each record earns a verdict word,
and the runner compares it with the one recorded: the same arm, and on
`ok` the same observable events, run for run and byte for byte
(`trace.ml`'s `events_equal` over both sides' `coalesce`).

WHAT IS MIRRORED FROM `main.ml`, by name, so a reader can hold the two
side by side:

- `replay`'s `init_model` call: the header's `load_segments`,
  `initial_brk`, `effective_mmap_base`, `entry_sp` and `alloc_limit`, and
  a `ProcInput` with empty `in_argv`, `in_envp`, `in_image_fs` and `in_tmp`
  (the model's `in_fs` is their seed, empty too), the header's
  `stdin` as the input stream, the peers as the connection queue
  (`peer_queue`, `peer_addr`, `peer_script`), the credentials, `nofile`,
  `entry_sigmask`, `hwcap`, `abort_terminal` and `va_size`.  `in_urandom`
  is the empty stream: the harness declares an empty random device for
  every run and the trace format carries none (`main.ml`'s `init_model`
  literal says why).
- the `in_mem` lookup: the recorded runs, absent bytes answering `none`;
  the `in_wmem` view: `some 0` inside a recorded range and `none`
  outside, as `replay`'s `in_wmem` answers `Some z0` -- the checker asks
  whether a byte is writable, never what it holds.
- `run_check`'s Sv48 gate: a run declaring another address-space size is
  `unmodeled` at every syscall before the checker is asked.
- the stop at the first disagreement: past it the two model states have
  parted and nothing further is comparable.  `--continue` keeps judging
  after one, on a model that may have parted, and marks every later
  verdict as such; it exists for the coverage measurement of
  `docs/lean-port/TESTING.md` (L1), which wants the pair of verdicts at
  every occurrence, and is not a claim that those verdicts are
  comparable.

WHAT IS NOT, each reported as recorded rather than re-derived: the
post-state digest, BLAKE2b-256 over `trace.ml`'s canonical slice text
(`TRACE.md` "The post-state digest"), which this runner has no BLAKE2b to
recompute, so an admitted step is held to its events and not to the
digest -- the half `main.exe --replay` also holds it to and this runner
cannot; the final file-system comparison (`fs_compare`); and the
`brk_in_window` note `replay` prints about the header's break.  The
create-mode check no replay makes.  Because the digest is not compared,
the exit status here is the OCaml replay's for the syscall verdicts only:
a run whose every verdict and event list is reproduced exits 0 here even
where the OCaml replay would exit 1 on the digest or the file system.

A VERDICT AFTER A DIVERGENCE IS NOT COMPARABLE.  The fold stops at the
first record whose verdict was not reproduced, which is `replay`'s own
rule; `--continue` judges on instead, and every later verdict is marked
`afterDivergence` and counted as incomparable rather than as an agreement
or a disagreement.  The reason is that the model carried forward is
advanced only on `ok`: a record the Lean checker declines contributes
none of its recorded effects, so the next record is judged against a
state no Rocq run ever held.  What goes missing is exactly the effects of
the unported arms.  The shape is general -- an `unmodeled` `munmap`
leaves its region mapped, so a later `mmap` returning that address is
refused -- and the example the corpus used to hold is gone with its arm:
until #1300 registered `write`, an `unmodeled` `write` left its
`eff_copyins` unmaterialized (`State.Backing.syscall_effect_accesses`),
so a later `mmap` fitted an allocation budget (`VmMaps.vm_limit`,
`State/Vm.lean`) the recorded run had already spent.  The one write the
checker still declines is one the record declines too, so it has no
effects to lose.  Registering `openat` (#1360) brought the
shape back on another number: an `openat` of the append word, which the
row declines, opens nothing, so the writes to the descriptor the
recorded run was handed are refused (`write_window/007`).  Read across
a divergence, the two checkers' verdicts measure the
size of the port frontier and not a disagreement between them.

AN UNMODELED VERDICT NAMES ITS SOURCE.  A `CheckUnmodeled` from
`check_syscall_for_run` is either an arm's own decline or the table's
`none` arm, and the two mean different things for the port (the second is
a checker not yet ported, or a number outside the Lean model).
`armStatus` reads both tables to say which, and `LpsRunner.Declines`
supplies the header line a declared decline rests on.  The `--json` output
carries the same fields for the comparison tool of ticket H4, whose
rule is that an `unmodeled` verdict counts as reproduced only when the
number is in `checked_table`.

THE TRUST STATEMENT.  Every verdict here is the value of
`check_syscall_for_run`, a definition in a `LinuxProcessSemantics.*`
module that `Checks/Policy.lean`'s audit walks, applied to inputs decoded
by this tooling.  What the verdict rests on beyond that definition is the
Lean compiler and its core runtime -- the `Nat`, `ByteArray` and `String`
primitives are `extern`, outside the audit's project-only walk -- exactly
as the Rocq checker's verdicts rest on the OCaml extraction and runtime.
The summary line says so. -/

namespace LpsRunner.Replay

open LinuxProcessSemantics.Riscv.Prelude (word)
open LinuxProcessSemantics.LinuxProcessSem.BvBase (byte)
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude (check_result)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch (lookup_ca)
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table (checked_table)
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch (lookup_arm)
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable (spec_table)
open LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs (check_syscall_for_run)
open LpsRunner.Codec (Word MemRuns Ranges)
open LpsRunner.Trace

/-- The checker a fold runs: `check_syscall_for_run`'s type.  A parameter so
that `LpsRunner.Tests` can drive the fold through a fixture table
(`Checks.ExecutableSpecs.check_syscall_for_run_in`); the runner passes the
real one and nothing else. -/
abbrev Checker := SyscallInput → SyscallEffect → Model → Option check_result

/-! ## From the record to the model's types -/

/-- A decoded word as the model's `BitVec 64`; the bound was checked at
decode time and travels with the value, so nothing wraps here. -/
def toWord (w : Word) : word := BitVec.ofNatLT w.val w.lt

def toByte (b : UInt8) : byte := BitVec.ofNat 8 b.toNat

def bytesToListAux (b : ByteArray) : Nat → List byte → List byte
  | 0, acc => acc
  | k + 1, acc => bytesToListAux b k (toByte (b.get! k) :: acc)

/-- A `ByteArray` as the `List byte` an effect's write carries. -/
def bytesToList (b : ByteArray) : List byte := bytesToListAux b b.size []

/-- The bytes of a string as the model's input stream (`main.ml`'s
`stream_of_string`): the byte at `i` while there is one, then the end. -/
def streamOfBytes (s : ByteArray) : InputStream where
  byte_at := fun i => if i < s.size then some (toByte (s.get! i)) else none
  sticky := by
    intro i h
    by_cases hi : i < s.size
    · simp only [hi, ↓reduceIte, reduceCtorEq] at h
    · have h' : ¬ (i + 1 < s.size) := by omega
      simp only [h', ↓reduceIte]

/-- What a peer says, then its ending (`main.ml`'s `peer_script`). -/
def scriptOfPeer (p : Peer) : NetStream where
  cell_at := fun i =>
    if i < p.bytes.size then .NByte (toByte (p.bytes.get! i))
    else if p.rst then .NRst else .NFin
  sticky := by
    intro i h
    by_cases hi : i < p.bytes.size
    · simp only [hi, ↓reduceIte, NetCell.isTerminal, Bool.false_eq_true] at h
    · have h' : ¬ (i + 1 < p.bytes.size) := by omega
      simp only [hi, h', ↓reduceIte]

/-- `main.ml`'s `peer_port_base`: the `i`-th peer listens on `4000 + i`. -/
def peerPortBase : Nat := 4000

/-- The `i`-th peer's address as `main.ml`'s `peer_addr` builds it:
127.0.0.1 and the port, both as the words a riscv64 program reads out of
`sin_addr` and `sin_port`. -/
def peerAddr (i : Nat) : PeerAddr :=
  let port := peerPortBase + i
  PeerAddr.mkPeer (BitVec.ofNat 32 0x0100007f)
    (BitVec.ofNat 16 (((port &&& 0xff) <<< 8) ||| (port >>> 8)))

/-- The connection queue (`main.ml`'s `peer_queue`): the peers in order,
then the silent environment. -/
def queueOfPeers (peers : List Peer) : NetQueue :=
  ⟨fun i =>
    match peers[i]? with
    | some p => (peerAddr i, scriptOfPeer p)
    | none => net_silent.conn_at (i - peers.length)⟩

def vaSizeOf : Trace.VaSize → LinuxProcessSemantics.LinuxProcessSem.State.VaSize
  | .sv39 => .Sv39
  | .sv48 => .Sv48
  | .sv57 => .Sv57

/-- The `ProcInput` `main.ml`'s `replay` builds from the header. -/
def procInputOf (h : Header) : ProcInput :=
  { in_argv := [], in_envp := [], in_image_fs := [], in_tmp := []
    in_stdin := streamOfBytes h.stdin
    in_urandom := IEof
    in_uid := toWord h.uid, in_gid := toWord h.gid
    in_groups := h.groups.map toWord
    in_net := queueOfPeers h.peers
    in_nofile := toWord h.nofile
    in_sigmask := toWord h.entry_sigmask
    in_hwcap := toWord h.hwcap
    in_abort_terminal := h.abort_terminal
    in_va_size := vaSizeOf h.va_size }

/-- The model the run starts from: `init_model` on the header, argument
for argument `main.ml`'s `replay`. -/
def seedModel (h : Header) : Model :=
  init_model (h.load_segments.map fun (b, l) => (toWord b, toWord l))
    (toWord h.initial_brk) (toWord h.effective_mmap_base) (toWord h.entry_sp)
    (h.alloc_limit : Int) (procInputOf h)

/-- The pair's input: registers as recorded, memory served from the runs,
the writable view from the ranges. -/
def inputOf (r : Syscall) : SyscallInput :=
  { in_sysno := toWord r.sysno
    in_args := r.args.map toWord
    in_mem := fun w => (r.in_mem.lookup w.toNat).map toByte
    in_wmem := fun w => if r.in_wmem.contains w.toNat then some (BitVec.ofNat 8 0) else none }

/-- The pair's effect: the six ledgers as recorded. -/
def effectOf (e : Effect) : SyscallEffect :=
  { eff_ret := toWord e.ret
    eff_writes := e.writes.map fun (a, b) => (toWord a, bytesToList b)
    eff_zeros := e.zeros.map fun (b, l) => (toWord b, toWord l)
    eff_unmaps := e.unmaps.map fun (b, l) => (toWord b, toWord l)
    eff_copies := e.copies.map fun (s, d, l) => MemCopy.mkCopy (toWord s) (toWord d) (toWord l)
    eff_copyins := e.copyins.map fun (a, n) => (toWord a, n) }

/-! ## Judging -/

/-- Where an `unmodeled` verdict came from, read off the two tables. -/
inductive ArmStatus where
  /-- an arm of `checked_table` answered for this number -/
  | checked
  /-- `spec_table` carries the number and `checked_table` does not: the
  checker is not yet ported, and the table's `none` arm declined -/
  | specOnly
  /-- neither table carries the number: it is outside the Lean model -/
  | absent
deriving DecidableEq

def ArmStatus.name : ArmStatus → String
  | .checked => "checked" | .specOnly => "spec_only" | .absent => "absent"

def armStatus (n : Nat) : ArmStatus :=
  match lookup_ca checked_table (n : Int) with
  | some _ => .checked
  | none =>
    match lookup_arm spec_table (n : Int) with
    | some _ => .specOnly
    | none => .absent

/-- The Lean checker's answer in the trace's terms.  `ok` carries the
step's events as runs; the post-state digest is not re-derived (the module
header says why), so `ok` has no digest here.  `unrenderable` is a step
whose events the format has no shape for: `trace.ml`'s `events_of_model`
fails on an `ExitEv` or `KillEv`, since no syscall step emits one
(`Sys/Kernel/Exit.v`, `exit_spec`'s docstring), and this runner reports
rather than invents. -/
inductive Judged where
  | ok (events : List Event)
  | reject
  | unmodeled
  | fault
  | unrenderable (reason : String)

def Judged.name : Judged → String
  | .ok _ => "ok" | .reject => "reject" | .unmodeled => "unmodeled" | .fault => "fault"
  | .unrenderable _ => "unrenderable"

def Judged.describe : Judged → String
  | .ok evs => s!"ok ({eventCount evs} events)"
  | .unrenderable r => s!"unrenderable ({r})"
  | v => v.name

/-- By constructor, not by rendered name: `arm` classification and the
explanation lines key on this, and a renamed string must not move them. -/
def Judged.isUnmodeled : Judged → Bool
  | .unmodeled => true
  | _ => false

def eventsOfModelAux : List event → List Event → Except String (List Event)
  | [], acc => .ok acc.reverse
  | .ReadEv ch b :: rest, acc => eventsOfModelAux rest (⟨.read, ⟨ch.toNat, ch.isLt⟩, ByteArray.mk #[UInt8.ofNat b.toNat]⟩ :: acc)
  | .WriteEv ch b :: rest, acc => eventsOfModelAux rest (⟨.write, ⟨ch.toNat, ch.isLt⟩, ByteArray.mk #[UInt8.ofNat b.toNat]⟩ :: acc)
  | _ :: _, _ => .error "a syscall step emitted an exit or kill event, which the trace has no shape for"

/-- The model's byte events as the format's runs (`trace.ml`'s
`events_of_model`): one run per byte, then coalesced.  Written with an
accumulator because a step's events are one per BYTE of its transfer: a
mapped recursion here is one stack frame per byte, and at `main.ml`'s
`write_capture_max` (4 MiB, 2^22 events) that shape died of deep
recursion -- a crash where the contract says exit 1.  Reachable since
#1300 put the `write` arm, which emits `WriteEv`, in `checked_table`;
`LpsRunner.Tests` pins the 2^22-event bound. -/
def eventsOfModel (l : List event) : Except String (List Event) := eventsOfModelAux l []

/-- The recorded verdict against the Lean one: the same arm, and on `ok`
the same runs (`trace.ml`'s `verdict_equal`, minus the digest). -/
def agrees (recorded : Verdict) (lean : Judged) : Bool :=
  match recorded, lean with
  | .ok e _, .ok e' => e == e'
  | .reject, .reject | .unmodeled, .unmodeled | .fault, .fault => true
  | _, _ => false

/-- One record judged: `run_check`'s answer, and the model to go on with
(advanced on `ok`, unchanged otherwise). -/
def judge (checker : Checker) (va : Trace.VaSize) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) : Judged × Model :=
  if va != .sv48 then (.unmodeled, m)
  else
    match checker i eff m with
    | some (.CheckOk m' evs) =>
      match eventsOfModel evs with
      | .ok runs => (.ok (coalesce runs), m')
      | .error r => (.unrenderable r, m')
    | some .CheckReject => (.reject, m)
    | some .CheckUnmodeled => (.unmodeled, m)
    | none => (.fault, m)

/-- One occurrence's line: what was recorded, what the Lean checker says,
and, for an `unmodeled`, where it came from. -/
structure Occurrence where
  seq : Nat
  occurrence : Nat
  sysno : Nat
  name : ByteArray
  ret : Nat
  mutation : Option ByteArray
  recorded : Verdict
  lean : Judged
  /-- the Lean `unmodeled` came from the address-space gate, not the checker -/
  vaDeclined : Bool
  arm : Option ArmStatus
  /-- judged after an earlier disagreement, under `--continue` -/
  afterDivergence : Bool

def Occurrence.agree (o : Occurrence) : Bool := agrees o.recorded o.lean

/-- Is this line's comparison with the recorded verdict worth anything?
Only before the run's first divergence; the module header says why. -/
def Occurrence.comparable (o : Occurrence) : Bool := !o.afterDivergence

structure FoldResult where
  occurrences : Array Occurrence
  model : Model
  /-- the `seq` of the first record whose verdict was not reproduced -/
  firstDisagreement : Option Nat
  /-- records judged (all of them under `--continue`) -/
  judged : Nat
  /-- of those, the ones judged before the run's first divergence: the
  only ones whose recorded verdict this run can be held to -/
  comparable : Nat
  reproduced : Nat

/-- The fold state between records. -/
structure FoldState where
  model : Model
  occurrences : Array Occurrence
  firstDisagreement : Option Nat
  judged : Nat
  comparable : Nat
  reproduced : Nat
  stopped : Bool

/-- Judge one record and record the outcome. -/
def step (checker : Checker) (cont : Bool) (va : Trace.VaSize) (st : FoldState) (r : Syscall)
    : FoldState :=
  if st.stopped then st
  else
    let (v, m') := judge checker va st.model (inputOf r) (effectOf r.effect)
    let occ : Occurrence :=
      { seq := r.seq, occurrence := r.occurrence, sysno := r.sysno.val, name := r.name
        ret := r.effect.ret.val, mutation := r.mutation, recorded := r.verdict, lean := v
        vaDeclined := va != .sv48
        arm := if v.isUnmodeled && va == .sv48 then some (armStatus r.sysno.val) else none
        afterDivergence := st.firstDisagreement.isSome }
    let agree := occ.agree
    let first := if agree then st.firstDisagreement else st.firstDisagreement <|> some r.seq
    { model := m', occurrences := st.occurrences.push occ, firstDisagreement := first
      judged := st.judged + 1
      comparable := st.comparable + (if occ.comparable then 1 else 0)
      reproduced := st.reproduced + (if agree && occ.comparable then 1 else 0)
      stopped := !agree && !cont }

/-- Every record through the checker, from the seeded model. -/
def fold (checker : Checker) (cont : Bool) (t : Trace) : FoldResult :=
  let st0 : FoldState :=
    { model := seedModel t.header, occurrences := #[], firstDisagreement := none
      judged := 0, comparable := 0, reproduced := 0, stopped := false }
  let st := t.syscalls.foldl (step checker cont t.header.va_size) st0
  { occurrences := st.occurrences, model := st.model, firstDisagreement := st.firstDisagreement
    judged := st.judged, comparable := st.comparable, reproduced := st.reproduced }

/-- The runner's fold: the real checker over `checked_table`. -/
def replay (cont : Bool) (t : Trace) : FoldResult := fold check_syscall_for_run cont t

/-! ## Rendering -/

def showBytes := Codec.showBytes

/-- What a number the spec carries and the checked table lacks rests on: the
`arm_*` register entries when the table registers arms one by one, else the
checked table's own header block. -/
def specOnlyCites (ix : Declines.Index) : List String :=
  match ix.armRegister with
  | [] => (ix.tableHeader.map Declines.citeBlock).toList
  | arms => arms.map Declines.Decline.cite

/-- The `unmodeled` explanation for a line: the arm status in words, then
the header lines it rests on. -/
def explainUnmodeled (ix : Declines.Index) (o : Occurrence) : List String :=
  if o.vaDeclined then
    ["the task declares another address-space size and the model answers only under sv48: every syscall of this run is declined (Equivalence.strong_equiv_va)"]
  else
    -- A citation needs a decline marker that spells `(n)`.
    -- The message reports when the index has no such marker.
    let cited (n : Nat) : List String :=
      match ix.forNumber n with
      | [] => [s!"no decline marker names ({n}), so nothing is cited here (a decline register or a header's prose may still declare it)"]
      | ds => ds.map fun d => s!"rests on {d.cite}"
    match o.arm with
    | some .checked =>
      s!"arm {o.sysno} in checked_table declined this call's shape" :: cited o.sysno
    | some .specOnly =>
      [s!"no arm for {o.sysno} in checked_table; spec_table carries {o.sysno}, so the checker is not yet ported (declared decline)"]
        ++ (specOnlyCites ix).map fun c => s!"rests on {c}"
    | some .absent =>
      s!"no arm for {o.sysno} in checked_table or spec_table: the number is outside the Lean model" :: cited o.sysno
    | none => []

/-- The human verdict line, `run_check`'s shape with both verdicts. -/
def humanLine (o : Occurrence) : String :=
  let mutTag := match o.mutation with | some m => s!"  [mutate {showBytes m}]" | none => ""
  let tag :=
    if o.agree || !o.comparable then ""
    else "  *** recorded as " ++ o.recorded.describe ++ ", the Lean checker says " ++ o.lean.describe ++ " ***"
  let div :=
    if o.comparable then ""
    else "  (after a divergence, so judged against a model earlier declines left stale: not comparable with the recorded " ++ o.recorded.describe ++ ")"
  s!"  [{o.seq}] {showBytes o.name} ({o.sysno}) #{o.occurrence} ret={o.ret}: {o.lean.describe}{mutTag}{tag}{div}"

/-- The `--json` verdict record: one object per occurrence, flat.
`recorded_post` is the digest copied from the record; nothing here
re-derives it (the module header says why), and no Lean-side digest is
emitted. -/
def jsonLine (ix : Declines.Index) (trace : String) (o : Occurrence) : String :=
  let recordedEvents : Json.Flat := match o.recorded with | .ok e _ => .nat (eventCount e) | _ => .null
  let leanEvents : Json.Flat := match o.lean with | .ok e => .nat (eventCount e) | _ => .null
  let post : Json.Flat := match o.recorded with | .ok _ d => .str d | _ => .null
  let declared : List String :=
    if o.vaDeclined then []
    else match o.arm with
      | some .specOnly => specOnlyCites ix
      | some _ => (ix.forNumber o.sysno).map Declines.Decline.cite
      | none => []
  Json.renderObject [
    ("record", .str "verdict"),
    ("trace", .str trace),
    ("seq", .nat o.seq),
    ("occurrence", .nat o.occurrence),
    ("sysno", .nat o.sysno),
    ("syscall", .str (showBytes o.name)),
    ("ret", .str (toString o.ret)),
    ("mutation", match o.mutation with | some m => .str (showBytes m) | none => .null),
    ("recorded", .str o.recorded.name),
    ("recorded_events", recordedEvents),
    ("recorded_post", post),
    ("lean", .str o.lean.name),
    ("lean_events", leanEvents),
    ("agree", .bool o.agree),
    ("va_declined", .bool o.vaDeclined),
    ("arm", match o.arm with | some a => .str a.name | none => .null),
    ("declared", .strs declared),
    ("after_divergence", .bool o.afterDivergence),
    ("comparable", .bool o.comparable)]

/-- The trust statement, printed with every summary. -/
def trustLine : String :=
  "verdicts: LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.check_syscall_for_run over Checks.Sys.Table.checked_table, compiled by Lean; they rest on the Lean compiler and core runtime (Nat, ByteArray, String externs are outside Checks/Policy.lean's project-only walk), as the Rocq checker's rest on the OCaml extraction"

end LpsRunner.Replay
