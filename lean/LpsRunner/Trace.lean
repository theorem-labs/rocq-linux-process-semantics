import LpsRunner.Json
import LpsRunner.Codec

/-! # LpsRunner.Trace — the three records of a recorded run, read strictly

Test tooling: nothing under `LpsRunner/` is part of the trusted
specification, and no proof depends on it.

`testing/syscall-check/TRACE.md` says what the records mean and
`testing/syscall-check/trace.ml` is the byte layout, reader and writer
both; this module is `trace.ml`'s reader again, for format
`lps-syscall-trace/2`, and every rule below is one of its:

- THE READER IS STRICT.  Every object is checked against the exact key set
  of its kind (`header_keys`, `syscall_keys`, `effect_keys`, `final_keys`
  and the nested `file`, `peer`, `seed`, `write`, `copy` and `ending`
  shapes): an unknown key is refused naming it, a missing key is refused
  naming it, a key given twice is refused.  A field the reader dropped
  would be a claim nobody judged; a field it defaulted would be a claim
  nobody made.
- The `format` field is checked before the header's key set, so a trace
  of another format is refused as that and not as a header with the wrong
  fields.
- A `syscall` record's `seq` must be the next in sequence, its `args`
  exactly six words, its `verdict` one of the four; on `ok` its `events`
  are the step's observable channel I/O as runs, coalesced on reading so
  a record that split a run compares as the run it stands for, and its
  `post` the 64-digit digest of the state the step left; on any other
  verdict both are empty (`events` `[]`, `post` `null`).  An event with
  no bytes is refused rather than dropped.
- The file is a header, then syscalls, then one final record and nothing
  after it; a trace with no final record was cut short and is refused as
  incomplete rather than replayed as a whole run.

Two things are this reader's and not `trace.ml`'s.  A word that does not
fit the Lean model's `BitVec 64` is refused (`LpsRunner.Codec.word` says
why the OCaml reader has no such bound), and the captured memory runs are
sorted and checked disjoint on the way into the binary-searched
`MemRuns` (`Codec.MemRuns.ofList` says why an overlap is refused rather
than reconciled).  Both refuse; neither fabricates.

Every reader returns `Except String`, and `read` prefixes the path and
line of the record it was reading, as `trace.ml`'s `read` does. -/

namespace LpsRunner.Trace

open LpsRunner.Json (Json Result)
open LpsRunner.Codec (Word MemRuns Ranges)

/-- The format this reader accepts; `trace.ml`'s `format_version`. -/
def formatVersion : String := "lps-syscall-trace/2"

/-! ## The decoded records -/

/-- One regular file of a directory listing. -/
structure FileEntry where
  name : ByteArray
  mode : Nat
  size : Nat
  contents : ByteArray
  ino : Nat
  mtime_sec : Nat
  mtime_nsec : Nat

/-- One `--peer`: what it sends, and whether it ends with a RST. -/
structure Peer where
  bytes : ByteArray
  rst : Bool

/-- One `--seed-file`. -/
structure Seed where
  name : ByteArray
  contents : ByteArray

/-- The task's address-space declaration, as the header spells it. -/
inductive VaSize where
  | sv39 | sv48 | sv57
deriving DecidableEq

def VaSize.name : VaSize → String
  | .sv39 => "sv39" | .sv48 => "sv48" | .sv57 => "sv57"

/-- The run header: everything `State.init_model` is seeded from, and what
the case was.  Field for field `trace.ml`'s `header`; words the model
holds are `Word`; words no arm reads (`mmap_base`) and the budget
(`alloc_limit`, a `Nat` here, cast to the model's `Int` at seeding) stay
unbounded as they are in the OCaml reader. -/
structure Header where
  probe : ByteArray
  case? : Option ByteArray
  argv : List ByteArray
  stdin : ByteArray
  peers : List Peer
  seeds : List Seed
  mutations : List ByteArray
  fs_check : Bool
  alloc_limit : Nat
  abort_terminal : Bool
  va_size : VaSize
  kernel_release : ByteArray
  load_segments : List (Word × Word)
  entry_sp : Word
  initial_brk : Word
  mmap_base : Nat
  effective_mmap_base : Word
  uid : Word
  gid : Word
  groups : List Word
  nofile : Word
  entry_sigmask : Word
  hwcap : Word
  umask : Nat
  initial_fs : List FileEntry

/-- The `SyscallEffect` as recorded: its six fields, in its order. -/
structure Effect where
  ret : Word
  writes : List (Word × ByteArray)
  zeros : List (Word × Word)
  unmaps : List (Word × Word)
  copies : List (Word × Word × Word)
  copyins : List (Word × Nat)

/-- One run of channel I/O: the maximal sequence of consecutive model
events of one kind on one channel, with their bytes (`trace.ml`'s `ev`,
`TRACE.md` "The events").  The model's `State.event` is one byte per
constructor; a write of a hundred bytes is one run of a hundred. -/
inductive EvKind where
  | read
  | write
deriving DecidableEq

def EvKind.name : EvKind → String
  | .read => "read" | .write => "write"

structure Event where
  kind : EvKind
  channel : Word
  bytes : ByteArray

/-- Two runs are the same run: same kind, channel and bytes. -/
def Event.beq (a b : Event) : Bool :=
  a.kind == b.kind && a.channel.val == b.channel.val && a.bytes.data.toList == b.bytes.data.toList

instance : BEq Event := ⟨Event.beq⟩

/-- Merge adjacent runs of one kind on one channel (`trace.ml`'s
`coalesce`): idempotent, the identity on a list already in maximal runs,
and what both sides go through so that two event lists compare canonically. -/
def coalesceAux : List Event → Option Event → List Event → List Event
  | [], none, acc => acc.reverse
  | [], some cur, acc => (cur :: acc).reverse
  | e :: rest, none, acc => coalesceAux rest (some e) acc
  | e :: rest, some cur, acc =>
    if e.kind == cur.kind && e.channel.val == cur.channel.val then
      coalesceAux rest (some { cur with bytes := cur.bytes ++ e.bytes }) acc
    else coalesceAux rest (some e) (cur :: acc)

def coalesce (l : List Event) : List Event := coalesceAux l none []

/-- The number of model events a run list stands for: one per byte
(`trace.ml`'s `event_count`, the format-1 count). -/
def eventCount (l : List Event) : Nat := l.foldl (fun n e => n + e.bytes.size) 0

/-- Whether the recorded digest is 64 lowercase hex digits (`trace.ml`'s
`is_digest`). -/
def isDigest (s : ByteArray) : Bool :=
  s.size == 64 && s.data.toList.all fun c => (Codec.hexNyb c).isSome

/-- The checker's four answers, as `trace.ml`'s `verdict`: `ok` carries what
an admitted step is held to on replay, its events run for run and the
digest of the state it left. -/
inductive Verdict where
  | ok (events : List Event) (post : String)
  | reject
  | unmodeled
  | fault

def Verdict.name : Verdict → String
  | .ok _ _ => "ok" | .reject => "reject" | .unmodeled => "unmodeled" | .fault => "fault"

/-- `ok (n events)`, or the bare name. -/
def Verdict.describe : Verdict → String
  | .ok evs _ => s!"ok ({eventCount evs} events)"
  | v => v.name


/-- One judged syscall: the pair the checker was given and what it said. -/
structure Syscall where
  seq : Nat
  occurrence : Nat
  sysno : Word
  name : ByteArray
  args : List Word
  in_mem : MemRuns
  in_wmem : Ranges
  effect : Effect
  mutation : Option ByteArray
  verdict : Verdict

inductive Ending where
  | exited (code : Nat)
  | signaled (signal : Nat)
  | timed_out

def Ending.describe : Ending → String
  | .exited c => s!"exited {c}"
  | .signaled s => s!"killed by signal {s}"
  | .timed_out => "timed out"

inductive FsVerdict where
  | «match» | mismatch | unkeyable
deriving DecidableEq

def FsVerdict.name : FsVerdict → String
  | .«match» => "match" | .mismatch => "mismatch" | .unkeyable => "unkeyable"

/-- The run's end. -/
structure Final where
  ending : Option Ending
  stragglers : Nat
  final_fs : Option (List FileEntry)
  fs_verdict : Option FsVerdict

structure Trace where
  header : Header
  syscalls : Array Syscall
  final : Final

/-! ## Decoding, strictly -/

/-- `trace.ml`'s `fields`: an object's members checked against EXACTLY the
key set `keys` -- each present once and nothing else -- returned for
lookup.  Every record kind goes through it, so this is the whole of the
unknown-field refusal. -/
def fields (what : String) (keys : List String) (j : Json) : Result (List (String × Json)) :=
  match j with
  | .obj kvs =>
    match kvs.find? (fun (k, _) => !keys.contains k) with
    | some (k, _) => .error s!"{what}: unknown field \"{k}\""
    | none =>
      match kvs.find? (fun (k, _) => (kvs.filter (fun (k', _) => k' == k)).length > 1) with
      | some (k, _) => .error s!"{what}: field \"{k}\" given twice"
      | none =>
        match keys.find? (fun k => !(kvs.any (fun (k', _) => k' == k))) with
        | some k => .error s!"{what}: missing field \"{k}\""
        | none => .ok kvs
  | _ => .error s!"{what}: not an object"

/-- A member `fields` has already required. -/
def get (kvs : List (String × Json)) (k : String) : Result Json :=
  match kvs.lookup k with
  | some v => .ok v
  | none => .error s!"internal: field \"{k}\" absent after the key-set check"

def asWordNat (what : String) (j : Json) : Result Nat :=
  match j with
  | .str s => Codec.decimal what s
  | _ => .error s!"{what}: not a decimal-string word"

/-- A word the model holds: decimal, and below `2^64` (`Codec.wordOfDecimal`
refuses the length before it computes a value). -/
def asWord (what : String) (j : Json) : Result Word :=
  match j with
  | .str s => Codec.wordOfDecimal what s
  | _ => .error s!"{what}: not a decimal-string word"

def asInt (what : String) (j : Json) : Result Int :=
  match j with
  | .int n => .ok n
  | _ => .error s!"{what}: not an integer"

def asNonneg (what : String) (j : Json) : Result Nat := do
  let n ← asInt what j
  if n < 0 then .error s!"{what}: {n} is negative" else .ok n.toNat

def asBool (what : String) (j : Json) : Result Bool :=
  match j with
  | .bool b => .ok b
  | _ => .error s!"{what}: not a boolean"

def asString (what : String) (j : Json) : Result ByteArray :=
  match j with
  | .str s => .ok s
  | _ => .error s!"{what}: not a string"

def asStringOpt (what : String) (j : Json) : Result (Option ByteArray) :=
  match j with
  | .null => .ok none
  | .str s => .ok (some s)
  | _ => .error s!"{what}: not a string or null"

def asList {α : Type} (what : String) (f : String → Json → Result α) (j : Json) : Result (List α) :=
  match j with
  | .arr xs => (xs.zipIdx).mapM fun (x, i) => f s!"{what}[{i}]" x
  | _ => .error s!"{what}: not a list"

def asPair {α β : Type} (what : String) (f : String → Json → Result α) (g : String → Json → Result β)
    (j : Json) : Result (α × β) :=
  match j with
  | .arr [a, b] => do
    let x ← f s!"{what}[0]" a
    let y ← g s!"{what}[1]" b
    pure (x, y)
  | _ => .error s!"{what}: not a two-element list"

def asHex (what : String) (j : Json) : Result ByteArray := do
  let s ← asString what j
  Codec.hex what s

/-- A `[base, len]` range of two model words. -/
def asRange (what : String) (j : Json) : Result (Word × Word) := asPair what asWord asWord j

/-- An ASCII string for a field that names a kind (`va_size`, `verdict`,
`ending.kind`, `fs_verdict`), compared against the alternatives. -/
def asAscii (what : String) (j : Json) : Result String := do
  let s ← asString what j
  Json.keyOfBytes 0 s |>.mapError fun _ => s!"{what}: not an ASCII string"

/-! ### The key sets, spelled as `trace.ml` spells them -/

def fileKeys : List String := ["name", "mode", "size", "contents", "ino", "mtime_sec", "mtime_nsec"]

def headerKeys : List String := [
  "record", "format", "probe", "case", "argv", "stdin", "peers", "seed_files",
  "mutations", "fs_check", "alloc_limit", "abort_terminal", "va_size",
  "kernel_release", "load_segments", "entry_sp", "initial_brk", "mmap_base",
  "effective_mmap_base", "uid", "gid", "groups", "nofile", "entry_sigmask",
  "hwcap", "umask", "initial_fs"]

def effectKeys : List String := ["ret", "writes", "zeros", "unmaps", "copies", "copyins"]

def syscallKeys : List String := [
  "record", "seq", "occurrence", "sysno", "syscall", "args", "in_mem", "in_wmem",
  "effect", "mutation", "verdict", "events", "post"]

def eventKeys : List String := ["kind", "channel", "bytes"]

def finalKeys : List String := ["record", "ending", "stragglers", "final_fs", "fs_verdict"]

def fsVerdicts : List String := ["match", "mismatch", "unkeyable"]

/-! ### The records -/

def fileOfJson (what : String) (j : Json) : Result FileEntry := do
  let g ← fields what fileKeys j
  let name ← get g "name" >>= asString s!"{what}.name"
  let mode ← get g "mode" >>= asNonneg s!"{what}.mode"
  let size ← get g "size" >>= asWordNat s!"{what}.size"
  let contents ← get g "contents" >>= asHex s!"{what}.contents"
  let ino ← get g "ino" >>= asWordNat s!"{what}.ino"
  let mtime_sec ← get g "mtime_sec" >>= asWordNat s!"{what}.mtime_sec"
  let mtime_nsec ← get g "mtime_nsec" >>= asNonneg s!"{what}.mtime_nsec"
  pure { name, mode, size, contents, ino, mtime_sec, mtime_nsec }

def peerOfJson (what : String) (j : Json) : Result Peer := do
  let g ← fields what ["bytes", "ending"] j
  let bytes ← get g "bytes" >>= asHex s!"{what}.bytes"
  let ending ← get g "ending" >>= asAscii s!"{what}.ending"
  let rst ← match ending with
    | "fin" => pure false
    | "rst" => pure true
    | e => .error s!"{what}.ending: \"{e}\" is not fin or rst"
  pure { bytes, rst }

def seedOfJson (what : String) (j : Json) : Result Seed := do
  let g ← fields what ["name", "contents"] j
  let name ← get g "name" >>= asString s!"{what}.name"
  let contents ← get g "contents" >>= asHex s!"{what}.contents"
  pure { name, contents }

/-- The header.  The format is checked first, before the key set. -/
def headerOfJson (j : Json) : Result Header := do
  match j with
  | .obj kvs =>
    match kvs.lookup "format" with
    | some (.str f) =>
      if f.data.toList == formatVersion.toUTF8.data.toList then pure ()
      else .error s!"header: format \"{Codec.showBytes f}\" is not \"{formatVersion}\""
    | some _ => .error "header: format is not a string"
    | none => .error "header: missing field \"format\""
  | _ => pure ()
  let g ← fields "header" headerKeys j
  let vaName ← get g "va_size" >>= asAscii "header.va_size"
  let va_size ← match vaName with
    | "sv39" => pure VaSize.sv39
    | "sv48" => pure VaSize.sv48
    | "sv57" => pure VaSize.sv57
    | v => .error s!"header.va_size: \"{v}\" is not sv39, sv48 or sv57"
  let probe ← get g "probe" >>= asString "header.probe"
  let case? ← get g "case" >>= asStringOpt "header.case"
  let argv ← get g "argv" >>= asList "header.argv" asString
  let stdin ← get g "stdin" >>= asHex "header.stdin"
  let peers ← get g "peers" >>= asList "header.peers" peerOfJson
  let seeds ← get g "seed_files" >>= asList "header.seed_files" seedOfJson
  let mutations ← get g "mutations" >>= asList "header.mutations" asString
  let fs_check ← get g "fs_check" >>= asBool "header.fs_check"
  let alloc_limit ← get g "alloc_limit" >>= asWordNat "header.alloc_limit"
  let abort_terminal ← get g "abort_terminal" >>= asBool "header.abort_terminal"
  let kernel_release ← get g "kernel_release" >>= asString "header.kernel_release"
  let load_segments ← get g "load_segments" >>= asList "header.load_segments" asRange
  let entry_sp ← get g "entry_sp" >>= asWord "header.entry_sp"
  let initial_brk ← get g "initial_brk" >>= asWord "header.initial_brk"
  let mmap_base ← get g "mmap_base" >>= asWordNat "header.mmap_base"
  let effective_mmap_base ← get g "effective_mmap_base" >>= asWord "header.effective_mmap_base"
  let uidN ← get g "uid" >>= asNonneg "header.uid"
  let uid ← Codec.word "header.uid" uidN
  let gidN ← get g "gid" >>= asNonneg "header.gid"
  let gid ← Codec.word "header.gid" gidN
  let groupsN ← get g "groups" >>= asList "header.groups" asNonneg
  let groups ← groupsN.mapM (Codec.word "header.groups")
  let nofile ← get g "nofile" >>= asWord "header.nofile"
  let entry_sigmask ← get g "entry_sigmask" >>= asWord "header.entry_sigmask"
  let hwcap ← get g "hwcap" >>= asWord "header.hwcap"
  let umask ← get g "umask" >>= asNonneg "header.umask"
  let initial_fs ← get g "initial_fs" >>= asList "header.initial_fs" fileOfJson
  pure { probe, case?, argv, stdin, peers, seeds, mutations, fs_check, alloc_limit,
         abort_terminal, va_size, kernel_release, load_segments, entry_sp, initial_brk,
         mmap_base, effective_mmap_base, uid, gid, groups, nofile, entry_sigmask, hwcap,
         umask, initial_fs }

def writeOfJson (what : String) (j : Json) : Result (Word × ByteArray) := do
  let g ← fields what ["addr", "bytes"] j
  let addr ← get g "addr" >>= asWord s!"{what}.addr"
  let bytes ← get g "bytes" >>= asHex s!"{what}.bytes"
  pure (addr, bytes)

def copyOfJson (what : String) (j : Json) : Result (Word × Word × Word) := do
  let g ← fields what ["src", "dst", "len"] j
  let src ← get g "src" >>= asWord s!"{what}.src"
  let dst ← get g "dst" >>= asWord s!"{what}.dst"
  let len ← get g "len" >>= asWord s!"{what}.len"
  pure (src, dst, len)

/-- A copy-in `[addr, len]`: the address a model word, the length the
`Nat` it counts (a Peano `nat` in the extraction). -/
def copyinOfJson (what : String) (j : Json) : Result (Word × Nat) :=
  asPair what asWord asWordNat j

def effectOfJson (what : String) (j : Json) : Result Effect := do
  let g ← fields what effectKeys j
  let ret ← get g "ret" >>= asWord s!"{what}.ret"
  let writes ← get g "writes" >>= asList s!"{what}.writes" writeOfJson
  let zeros ← get g "zeros" >>= asList s!"{what}.zeros" asRange
  let unmaps ← get g "unmaps" >>= asList s!"{what}.unmaps" asRange
  let copies ← get g "copies" >>= asList s!"{what}.copies" copyOfJson
  let copyins ← get g "copyins" >>= asList s!"{what}.copyins" copyinOfJson
  pure { ret, writes, zeros, unmaps, copies, copyins }

/-- A captured run `{addr, bytes}`; the address is a lookup key and stays
a `Nat`, since a run the model cannot reach is unreachable rather than
wrong. -/
def runOfJson (what : String) (j : Json) : Result (Nat × ByteArray) := do
  let g ← fields what ["addr", "bytes"] j
  let addr ← get g "addr" >>= asWordNat s!"{what}.addr"
  let bytes ← get g "bytes" >>= asHex s!"{what}.bytes"
  pure (addr, bytes)

def wmemRangeOfJson (what : String) (j : Json) : Result (Nat × Nat) :=
  asPair what asWordNat asWordNat j

/-- One recorded event run.  An event with no bytes stands for no event and
is refused rather than dropped: a reader that dropped it would judge a claim
the writer never makes, since `coalesce` over one-byte runs cannot produce
one. -/
def eventOfJson (what : String) (j : Json) : Result Event := do
  let g ← fields what eventKeys j
  let channel ← get g "channel" >>= asWord s!"{what}.channel"
  let bytes ← get g "bytes" >>= asHex s!"{what}.bytes"
  if bytes.size == 0 then throw s!"{what}.bytes: an event with no bytes"
  let kind ← get g "kind" >>= asAscii s!"{what}.kind"
  match kind with
  | "read" => pure { kind := .read, channel, bytes }
  | "write" => pure { kind := .write, channel, bytes }
  | k => .error s!"{what}.kind: \"{k}\" is not read or write"

def syscallOfJson (j : Json) : Result Syscall := do
  let g ← fields "syscall" syscallKeys j
  let args ← get g "args" >>= asList "syscall.args" asWord
  if args.length != 6 then
    throw s!"syscall.args: {args.length} arguments, not six"
  -- the events as recorded, then coalesced, so a record that split a run
  -- compares as the run it stands for
  let events ← coalesce <$> (get g "events" >>= asList "syscall.events" eventOfJson)
  let postBytes ← get g "post" >>= asStringOpt "syscall.post"
  let post ← match postBytes with
    | some d =>
      if isDigest d then pure (some (String.ofList (d.data.toList.map fun c => Char.ofNat c.toNat)))
      else .error s!"syscall.post: \"{Codec.showBytes d}\" is not a 64-digit lowercase hex digest"
    | none => pure none
  let verdictName ← get g "verdict" >>= asAscii "syscall.verdict"
  let verdict ← match verdictName with
    | "ok" =>
      match post with
      | some d => pure (Verdict.ok events d)
      | none => .error "syscall.post: an admitted step records its post-state digest"
    | "reject" => pure Verdict.reject
    | "unmodeled" => pure Verdict.unmodeled
    | "fault" => pure Verdict.fault
    | v => .error s!"syscall.verdict: \"{v}\" is not ok, reject, unmodeled or fault"
  match verdict with
  | .ok _ _ => pure ()
  | _ =>
    if !events.isEmpty then
      throw s!"syscall.events: {eventCount events} events on a verdict that admits none"
    if post.isSome then throw "syscall.post: a digest on a verdict that leaves no state"
  let seq ← get g "seq" >>= asNonneg "syscall.seq"
  let occurrence ← get g "occurrence" >>= asNonneg "syscall.occurrence"
  let sysno ← get g "sysno" >>= asWord "syscall.sysno"
  let name ← get g "syscall" >>= asString "syscall.syscall"
  let runs ← get g "in_mem" >>= asList "syscall.in_mem" runOfJson
  let in_mem ← MemRuns.ofList "syscall.in_mem" runs
  let ranges ← get g "in_wmem" >>= asList "syscall.in_wmem" wmemRangeOfJson
  let in_wmem := Ranges.ofList ranges
  let effect ← get g "effect" >>= effectOfJson "syscall.effect"
  let mutation ← get g "mutation" >>= asStringOpt "syscall.mutation"
  pure { seq, occurrence, sysno, name, args, in_mem, in_wmem, effect, mutation, verdict }

def endingOfJson (j : Json) : Result (Option Ending) := do
  match j with
  | .null => pure none
  | .obj kvs =>
    match kvs.lookup "kind" with
    | some (.str k) =>
      match Json.keyOfBytes 0 k with
      | .ok "exited" => do
        let g ← fields "final.ending" ["kind", "code"] j
        let code ← get g "code" >>= asNonneg "final.ending.code"
        pure (some (.exited code))
      | .ok "signaled" => do
        let g ← fields "final.ending" ["kind", "signal"] j
        let signal ← get g "signal" >>= asNonneg "final.ending.signal"
        pure (some (.signaled signal))
      | .ok "timed_out" => do
        let _ ← fields "final.ending" ["kind"] j
        pure (some .timed_out)
      | _ => .error s!"final.ending.kind: \"{Codec.showBytes k}\" is not exited, signaled or timed_out"
    | _ => .error "final.ending: no kind"
  | _ => .error "final.ending: not an object or null"

def finalOfJson (j : Json) : Result Final := do
  let g ← fields "final" finalKeys j
  let ending ← get g "ending" >>= endingOfJson
  let stragglers ← get g "stragglers" >>= asNonneg "final.stragglers"
  let final_fs ← match ← get g "final_fs" with
    | .null => pure none
    | l => some <$> asList "final.final_fs" fileOfJson l
  let fsv ← get g "fs_verdict" >>= asStringOpt "final.fs_verdict"
  let fs_verdict ← match fsv with
    | none => pure none
    | some v =>
      match Json.keyOfBytes 0 v with
      | .ok "match" => pure (some FsVerdict.«match»)
      | .ok "mismatch" => pure (some FsVerdict.mismatch)
      | .ok "unkeyable" => pure (some FsVerdict.unkeyable)
      | _ => .error s!"final.fs_verdict: \"{Codec.showBytes v}\" is not match, mismatch or unkeyable"
  pure { ending, stragglers, final_fs, fs_verdict }

/-! ## The file -/

/-- The lines of a file, split at newlines as OCaml's `input_line` splits
them: a trailing newline ends the last line and opens no empty one. -/
def splitLines (s : ByteArray) : Nat → Nat → Nat → List ByteArray → List ByteArray
  | 0, start, _, acc => (if start < s.size then [s.extract start s.size] else []).reverseAux acc |>.reverse
  | fuel + 1, start, i, acc =>
    if i < s.size then
      if s.get! i == 0x0a then splitLines s fuel (i + 1) (i + 1) (s.extract start i :: acc)
      else splitLines s fuel start (i + 1) acc
    else (if start < s.size then [s.extract start s.size] else []).reverseAux acc |>.reverse

def lines (s : ByteArray) : List ByteArray := splitLines s (s.size + 1) 0 0 []

/-- The record kind of a parsed line. -/
def kindOf (j : Json) : Result String :=
  match j with
  | .obj kvs =>
    match kvs.lookup "record" with
    | some (.str k) => Json.keyOfBytes 0 k |>.mapError fun _ => "a record with no \"record\" kind"
    | _ => .error "a record with no \"record\" kind"
  | _ => .error "not a JSON object"

/-- Parse one line and classify it, failing at `path:lineno`. -/
def parseLine (path : String) (lineno : Nat) (line : ByteArray) : Result (String × Json) := do
  let j ← Json.parse line |>.mapError fun m => s!"{path}:{lineno}: {m}"
  let k ← kindOf j |>.mapError fun m => s!"{path}:{lineno}: {m}"
  pure (k, j)

/-- The syscall records after the header, in sequence, then the final
record and nothing after it.  `n` is the sequence number expected next and
`lineno` the line about to be read. -/
def readBody (path : String) : List ByteArray → Nat → Nat → Array Syscall →
    Result (Array Syscall × Final)
  | [], _, _, _ => .error s!"{path}: the trace ends without its final record (the run was cut short)"
  | line :: rest, lineno, n, acc => do
    let (k, j) ← parseLine path lineno line
    match k with
    | "syscall" =>
      let s ← syscallOfJson j |>.mapError fun m => s!"{path}:{lineno}: {m}"
      if s.seq != n then throw s!"{path}:{lineno}: syscall seq {s.seq} where {n} was expected"
      readBody path rest (lineno + 1) (n + 1) (acc.push s)
    | "final" =>
      let f ← finalOfJson j |>.mapError fun m => s!"{path}:{lineno}: {m}"
      match rest with
      | [] => pure (acc, f)
      | _ => .error s!"{path}:{lineno + 1}: a record after the final one"
    | k => .error s!"{path}:{lineno}: unknown record kind \"{k}\""

/-- The whole trace, read strictly. -/
def read (path : String) (bytes : ByteArray) : Result Trace := do
  match lines bytes with
  | [] => .error s!"{path}: empty trace"
  | first :: rest =>
    let (k, j) ← parseLine path 1 first
    if k != "header" then throw s!"{path}:1: the first record is \"{k}\", not the header"
    let header ← headerOfJson j |>.mapError fun m => s!"{path}:1: {m}"
    let (syscalls, final) ← readBody path rest 2 0 #[]
    pure { header, syscalls, final }

end LpsRunner.Trace
