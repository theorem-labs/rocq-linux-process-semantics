import LpsRunner.Replay

/-! # LpsRunner.Main — `lake exe lps_runner`

Test tooling: nothing under `LpsRunner/` is part of the trusted
specification, and no proof depends on it.

```
lps_runner [--json] [--continue] [--lean-src DIR] TRACE...
lps_runner --decode-only TRACE...
lps_runner --measure TRACE...
```

Reads each trace (`testing/syscall-check/TRACE.md`), seeds the model from
its header, judges every recorded syscall with the Lean checker and
prints one verdict per occurrence beside the recorded one
(`LpsRunner.Replay` says what is mirrored from `main.ml --replay`).

Exit status, as `main.exe --replay`'s for the syscall verdicts: 0 when
every recorded verdict of every trace was reproduced, events included; 1
when one was not (named by `seq`); 2 when a trace could not be read -- a
malformed line, an unknown or missing field, a record out of place, no
`final` record, or a word the Lean model's 64-bit `BitVec` cannot hold --
or on a usage error.  The post-state digest and the file-system verdict
are reported, not re-derived (`LpsRunner.Replay` says why), so they never
move the status here where they can move the OCaml replay's.

`--json` writes one JSON object per line instead of the human lines: a
`verdict` record per occurrence, a `summary` record per trace, and one
`run` record at the end; the field names are `LpsRunner.Replay.jsonLine`'s
and are what the comparison tool of ticket H4 reads.  `--continue` keeps
judging past the first disagreement (`Replay` says on what terms).
`--lean-src DIR` lets an `unmodeled` line cite the header line a declared
decline rests on (`LpsRunner.Declines`).  `--decode-only` reads and
validates the traces without judging; `--measure` times the model's own
byte reader over each record's captured memory, the cost the write arm
pays per transfer. -/

namespace LpsRunner.Main

open LpsRunner.Trace
open LpsRunner.Replay
open LinuxProcessSemantics.LinuxProcessSem.State (readable_bytes m_halted)

def usage : String :=
  "usage: lps_runner [--json] [--continue] [--lean-src DIR] TRACE...\n" ++
  "       lps_runner --decode-only TRACE...\n" ++
  "       lps_runner --measure TRACE...\n" ++
  "\n" ++
  "Replays recorded syscall traces (testing/syscall-check/TRACE.md) through the\n" ++
  "Lean checker and prints one verdict per occurrence beside the recorded one.\n" ++
  "Exit 0: every recorded verdict reproduced; 1: one was not; 2: a trace could\n" ++
  "not be read, or a usage error.\n" ++
  "  --json          one JSON object per line (verdict, summary, run records)\n" ++
  "  --continue      judge past the first disagreement; later verdicts are judged\n" ++
  "                  against a model earlier declines left stale and are reported\n" ++
  "                  as not comparable with the recorded ones\n" ++
  "  --lean-src DIR  cite the header marker for a declared decline\n" ++
  "  --decode-only   read and validate the traces; judge nothing\n" ++
  "  --measure       time State.readable_bytes over each record's captured memory\n" ++
  Replay.trustLine ++ "\n"

structure Options where
  json : Bool := false
  cont : Bool := false
  decodeOnly : Bool := false
  measure : Bool := false
  leanSrc : Option String := none
  traces : List String := []

def parseArgs : List String → Options → Except String Options
  | [], o =>
    if o.traces.isEmpty then .error "no trace given"
    -- `--decode-only` and `--measure` print human lines only, and `--json`
    -- promises a stream of records: the pair would hand a line-by-line
    -- consumer text it cannot parse, so it is refused up front
    else if o.json ∧ (o.decodeOnly ∨ o.measure) then .error "--json has no record for --decode-only or --measure"
    else .ok { o with traces := o.traces.reverse }
  | "--json" :: rest, o => parseArgs rest { o with json := true }
  | "--continue" :: rest, o => parseArgs rest { o with cont := true }
  | "--decode-only" :: rest, o => parseArgs rest { o with decodeOnly := true }
  | "--measure" :: rest, o => parseArgs rest { o with measure := true }
  | "--lean-src" :: d :: rest, o =>
    if d.startsWith "--" then .error s!"--lean-src needs a directory, not {d}"
    else parseArgs rest { o with leanSrc := some d }
  | ["--lean-src"], _ => .error "--lean-src needs a directory"
  | a :: rest, o =>
    if a.startsWith "--" then .error s!"unknown option {a}"
    else parseArgs rest { o with traces := a :: o.traces }

def describeEnding : Option Ending → String
  | none => "no terminal event"
  | some e => e.describe

def describeFs (f : Final) : String :=
  match f.final_fs, f.fs_verdict with
  | some _, some v => s!"recorded {v.name} (not re-derived by lps_runner)"
  | none, none => "not compared by the recorded run"
  | _, _ => "the record carries a listing without a verdict, or a verdict without a listing"

def haltedOf (m : LinuxProcessSemantics.LinuxProcessSem.State.Model) : String :=
  match m_halted m with
  | some c => s!"halted with {c.toNat}"
  | none => "running"

/-- The decode-only line: the trace validated, nothing judged. -/
def decodeLine (path : String) (t : Trace) (ms : Nat) : String :=
  s!"decoded {path}: {showBytes t.header.probe}{caseSuffix t}, {t.syscalls.size} syscall record(s), {ms} ms"
where
  caseSuffix (t : Trace) : String :=
    match t.header.case? with | some c => s!" ({showBytes c})" | none => ""

/-- `--measure`: the model's byte reader over every captured run of every
record, timed; the largest run is what the write arm walks. -/
def measureTrace (path : String) (t : Trace) : IO Unit := do
  let mut worst : Nat × Nat × Nat := (0, 0, 0)   -- (bytes, microseconds, seq)
  for r in t.syscalls do
    let input := inputOf r
    let mut recBytes := 0
    let mut recUs := 0   -- microseconds
    for (addr, run) in r.in_mem.runs do
      match Codec.word "in_mem run" addr, Codec.word "in_mem run" run.size with
      | .ok a, .ok len =>
        let t0 ← IO.monoNanosNow
        let n := (readable_bytes input.in_mem (toWord a) (toWord len)).length
        -- an action that needs `n` before the second clock reading, so the
        -- compiler cannot sink the reader's evaluation past it
        if n != run.size then
          IO.println s!"  [{r.seq}] run at {addr}: readable_bytes returned {n} of {run.size} bytes"
        let t1 ← IO.monoNanosNow
        recBytes := recBytes + n
        recUs := recUs + (t1 - t0) / 1000
      | _, _ => IO.println s!"  [{r.seq}] run at {addr} is outside the 64-bit address space; skipped"
    if r.in_mem.runs.size > 0 then
      IO.println s!"  [{r.seq}] {showBytes r.name} ({r.sysno.val}): {r.in_mem.runs.size} run(s), {recBytes} bytes read by readable_bytes in {recUs} us"
    if recBytes > worst.1 then worst := (recBytes, recUs, r.seq)
  IO.println s!"MEASURE {path}: largest record seq {worst.2.2} read {worst.1} bytes in {worst.2.1} us"

/-- The `--json` record for a trace the reader refused: status 2, the
reason, no verdicts.  Without it a stream over several traces gives a
consumer no object to attach the refusal to. -/
def refusedLine (path reason : String) : String :=
  Json.renderObject [("record", .str "summary"), ("trace", .str path),
    ("judged", .nat 0), ("comparable", .nat 0), ("reproduced", .nat 0),
    ("error", .str reason), ("status", .nat 2)]

/-- One trace: read, seed, judge, report.  Returns the exit status. -/
def runTrace (opts : Options) (ix : Declines.Index) (path : String) : IO Nat := do
  let t0 ← IO.monoMsNow
  let read? ← try pure (some (← IO.FS.readBinFile path)) catch e =>
    -- the error names the path itself
    IO.eprintln s!"lps_runner: {e}"
    pure none
  let some bytes := read? | do
    if opts.json then IO.println (refusedLine path s!"could not read {path}")
    return 2
  match Trace.read path bytes with
  | .error m =>
    IO.eprintln s!"lps_runner: {m}"
    -- under `--json` the refusal is a record too, so a consumer counting
    -- traces sees this one as unjudged rather than absent
    if opts.json then IO.println (refusedLine path m)
    return 2
  | .ok t =>
    let t1 ← IO.monoMsNow
    if opts.decodeOnly then
      IO.println (decodeLine path t (t1 - t0))
      return 0
    if opts.measure then
      IO.println (decodeLine path t (t1 - t0))
      measureTrace path t
      return 0
    let r := Replay.replay opts.cont t
    let t2 ← IO.monoMsNow
    let status := if r.firstDisagreement.isSome then 1 else 0
    if opts.json then
      for o in r.occurrences do
        IO.println (jsonLine ix path o)
      IO.println (Json.renderObject [
        ("record", .str "summary"), ("trace", .str path),
        ("probe", .str (showBytes t.header.probe)),
        ("case", match t.header.case? with | some c => .str (showBytes c) | none => .null),
        ("kernel_release", .str (showBytes t.header.kernel_release)),
        ("va_size", .str t.header.va_size.name),
        ("records", .nat t.syscalls.size), ("judged", .nat r.judged),
        ("comparable", .nat r.comparable),
        ("reproduced", .nat r.reproduced),
        ("first_disagreement", match r.firstDisagreement with | some s => .nat s | none => .null),
        ("ending", .str (describeEnding t.final.ending)),
        ("model_halted", .str (haltedOf r.model)),
        ("fs", .str (describeFs t.final)),
        ("decode_ms", .nat (t1 - t0)), ("judge_ms", .nat (t2 - t1)),
        ("status", .nat status)])
    else
      let caseText := match t.header.case? with | some c => s!" ({showBytes c})" | none => ""
      IO.println s!"Replaying {path}: {showBytes t.header.probe}{caseText}, recorded under Linux {showBytes t.header.kernel_release}"
      for o in r.occurrences do
        IO.println (humanLine o)
        if o.lean.isUnmodeled then
          for l in explainUnmodeled ix o do
            IO.println s!"        {l}"
      IO.println s!"  final: {describeEnding t.final.ending}; stragglers {t.final.stragglers}; model {haltedOf r.model}; file system: {describeFs t.final}"
      let unjudged := t.syscalls.size - r.judged
      let incomparable := r.judged - r.comparable
      let tail := match r.firstDisagreement with
        | some s => s!"; first disagreement at seq {s}" ++ (if unjudged > 0 then s!"; {unjudged} record(s) not judged" else "")
            ++ (if incomparable > 0 then s!"; {incomparable} judged past it and not comparable" else "")
        | none => ""
      IO.println s!"REPLAY {path}: {r.reproduced} of {r.comparable} recorded verdicts reproduced{tail}; decode {t1 - t0} ms, judge {t2 - t1} ms"
    return status

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprint usage
    return 2
  if args.contains "--help" then
    IO.print usage
    return 0
  match parseArgs args {} with
  | .error m =>
    IO.eprintln s!"lps_runner: {m}"
    IO.eprint usage
    return 2
  | .ok opts =>
    -- a `--lean-src` that cannot be walked is a usage error (2), not the
    -- exit 1 an uncaught exception would produce, which is the code for "a
    -- verdict was not reproduced"
    let ix? ← match opts.leanSrc with
      | some d =>
        try pure (some (← Declines.Index.load d)) catch e =>
          IO.eprintln s!"lps_runner: --lean-src {d}: {e}"
          pure none
      | none => pure (some Declines.Index.empty)
    let some ix := ix? | return 2
    let mut worst : Nat := 0
    let mut n : Nat := 0
    let mut judgedAny := false
    for p in opts.traces do
      let s ← runTrace opts ix p
      worst := max worst s
      n := n + 1
      if s < 2 then judgedAny := true
    if opts.json then
      IO.println (Json.renderObject [("record", .str "run"), ("traces", .nat n),
        ("status", .nat worst), ("trust", .str Replay.trustLine)])
    -- the trust statement follows every judged summary: a refused trace
    -- beside a judged one (exit 2 for the run) does not silence it, and a run
    -- that judged nothing has no verdict for it to be about
    else if !opts.decodeOnly && !opts.measure && judgedAny then
      IO.println Replay.trustLine
    return worst.toUInt32

end LpsRunner.Main

def main (args : List String) : IO UInt32 := LpsRunner.Main.main args
