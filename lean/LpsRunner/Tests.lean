import LpsRunner.Trace
import LpsRunner.Declines
import LpsRunner.Replay

/-! # LpsRunner.Tests — the codecs and the record reader, run by the kernel

Test tooling: nothing under `LpsRunner/` is part of the trusted
specification, and no proof depends on it.

The codec examples are closed by `decide +kernel`: the reader is run by
Lean's kernel on a literal input and its answer compared with the one the
format requires; the proof term is `of_decide_eq_true rfl` and rests on no
axiom.  The record-reader and register cases are `#guard` checks instead,
each section saying why the kernel is not the right evaluator there; a
`#guard` fails the build on `false` exactly as a failed `decide` does.  Each rule `testing/syscall-check/trace.ml` states has a case
that accepts what it accepts and a case that refuses what it refuses, so
that a reader which stopped enforcing the rule fails to build.  The cases
are stated against the format, not against the OCaml reader's code: the
sentence of `TRACE.md` or the `trace.ml` function each rule comes from is
named beside it. -/

namespace LpsRunner.Tests

open LpsRunner.Json
open LpsRunner.Codec
open LpsRunner.Trace

/-! ## Projections a decidable equality can compare -/

def okMsg {α : Type} (r : Except String α) : Option String :=
  match r with | .ok _ => none | .error e => some e

/-- A value rendered for comparison: strings as hex, objects and lists
in order, bounded by fuel over the nesting depth. -/
def debug : Nat → Json → String
  | 0, _ => "…"
  | fuel + 1, j =>
    match j with
    | .null => "null"
    | .bool true => "true"
    | .bool false => "false"
    | .int n => toString n
    | .str s => "s:" ++ String.join (s.data.toList.map hex2)
    | .arr xs => "[" ++ String.intercalate "," (xs.map (debug fuel)) ++ "]"
    | .obj kvs => "{" ++ String.intercalate "," (kvs.map fun (k, v) => k ++ "=" ++ debug fuel v) ++ "}"

def parsed (s : String) : Option String :=
  match Json.parse s.toUTF8 with | .ok j => some (debug 16 j) | .error _ => none

def parseErr (s : String) : Option String := okMsg (Json.parse s.toUTF8)

/-! ## JSON: `trace.ml`'s `parse`

Integers only, decimal strings for words, bytes as hex (`TRACE.md`,
"Numbers"). -/

example : parsed "null" = some "null" := by decide +kernel
example : parsed " true " = some "true" := by decide +kernel
example : parsed "false" = some "false" := by decide +kernel
example : parsed "[]" = some "[]" := by decide +kernel
example : parsed "[ ]" = some "[]" := by decide +kernel
example : parsed "{}" = some "{}" := by decide +kernel
example : parsed "[1,-2,0]" = some "[1,-2,0]" := by decide +kernel
example : parsed "{\"a\":1,\"b\":[true,null]}" = some "{a=1,b=[true,null]}" := by decide +kernel
example : parsed "\"ab\"" = some "s:6162" := by decide +kernel

/-- A fraction or an exponent is refused rather than rounded. -/
example : parseErr "1.5" = some "non-integer number at byte 0: no field is a float" := by decide +kernel
example : parseErr "[1e3]" = some "non-integer number at byte 1: no field is a float" := by decide +kernel
/-- No leading zeros; `0` and `-0` alone are numbers. -/
example : parseErr "018" = some "number with a leading zero at byte 0" := by decide +kernel
example : parsed "0" = some "0" := by decide +kernel
example : parsed "-0" = some "0" := by decide +kernel
example : parseErr "-" = some "bad number at byte 0" := by decide +kernel
/-- OCaml's `int`: `2^62 - 1` fits, `2^62` does not. -/
example : parsed "4611686018427387903" = some "4611686018427387903" := by decide +kernel
example : parseErr "4611686018427387904" = some "integer 4611686018427387904 does not fit an OCaml int" := by decide +kernel
example : parseErr "-4611686018427387905" = some "integer -4611686018427387905 does not fit an OCaml int" := by decide +kernel
/-- Past `2^62` the digits are counted, not accumulated: the value a 25-digit
number would have is never computed, and the refusal names the digit count. -/
example : parseErr "1000000000000000000000000" = some "a 25-digit integer at byte 0 does not fit an OCaml int" := by decide +kernel
example : parseErr "[-1000000000000000000000000]" = some "a 25-digit integer at byte 1 does not fit an OCaml int" := by decide +kernel

/-- The eight escapes, `\u`, and a surrogate pair as its UTF-8. -/
example : parsed "\"\\n\\t\\\"\\\\\\/\"" = some "s:0a09225c2f" := by decide +kernel
example : parsed "\"\\u0041\"" = some "s:41" := by decide +kernel
example : parsed "\"\\u00e9\"" = some "s:c3a9" := by decide +kernel
example : parsed "\"\\ud83d\\ude00\"" = some "s:f09f9880" := by decide +kernel
example : parseErr "\"\\ud83d\"" = some "unpaired surrogate at byte 7" := by decide +kernel
example : parseErr "\"\\ude00\"" = some "unpaired surrogate at byte 7" := by decide +kernel
example : parseErr "\"\\ud83d\\u0041\"" = some "unpaired surrogate at byte 13" := by decide +kernel
example : parseErr "\"\\x\"" = some "bad escape at byte 2" := by decide +kernel
example : parseErr "\"\\u12\"" = some "truncated \\u escape at byte 3" := by decide +kernel
/-- A raw control character is refused; a raw byte outside ASCII is kept. -/
example : parseErr "\"a\tb\"" = some "control character in string at byte 2" := by decide +kernel
example : (Json.parse (ByteArray.mk #[0x22, 0x80, 0x22]) |>.toOption.map (debug 4)) = some "s:80" := by decide +kernel
example : parseErr "\"abc" = some "unterminated string" := by decide +kernel

example : parseErr "nul" = some "unrecognized token at byte 0" := by decide +kernel
example : parseErr "" = some "unexpected end of line" := by decide +kernel
example : parseErr "[1 2]" = some "expected , or ] at byte 3" := by decide +kernel
example : parseErr "{\"a\" 1}" = some "expected ':' at byte 5, found '1'" := by decide +kernel
example : parseErr "{1:2}" = some "expected '\"' at byte 1, found '1'" := by decide +kernel
example : parseErr "[1]x" = some "trailing content at byte 3" := by decide +kernel
/-- A key given twice parses (the record readers refuse it). -/
example : parsed "{\"a\":1,\"a\":2}" = some "{a=1,a=2}" := by decide +kernel
/-- The runner's own JSON output passes UTF-8 through and escapes only the
quote, the backslash and control characters. -/
example : Json.quote "é\"\\\n" = "\"é\\\"\\\\\\u000a\"" := by decide +kernel
/-- A key outside ASCII is refused (the key sets are ASCII, so it could only
be an unknown field). -/
example : parseErr "{\"\u00e9\":1}" = some "object key at byte 1 is not ASCII" := by decide +kernel

/-! ## Words and bytes: `trace.ml`'s `as_word` and `as_hex` -/

def dec (s : String) : Except String Nat := Codec.decimal "w" s.toUTF8
def okNat (r : Except String Nat) : Option Nat := match r with | .ok n => some n | .error _ => none

example : okNat (dec "0") = some 0 := by decide +kernel
example : okNat (dec "18446744073709551607") = some 18446744073709551607 := by decide +kernel
example : okMsg (dec "") = some "w: \"\" is not a decimal word" := by decide +kernel
example : okMsg (dec "-1") = some "w: \"-1\" is not a decimal word" := by decide +kernel
example : okMsg (dec "0x10") = some "w: \"0x10\" is not a decimal word" := by decide +kernel

def okWord (r : Except String Word) : Option Nat := match r with | .ok w => some w.val | .error _ => none

/-- The Lean side's bound: `2^64 - 1` is a word, `2^64` is refused naming the field. -/
example : okWord (Codec.word "syscall.effect.ret" 18446744073709551615) = some 18446744073709551615 := by decide +kernel
example : okMsg (Codec.word "syscall.effect.ret" 18446744073709551616)
    = some "syscall.effect.ret: 18446744073709551616 does not fit the Lean model's 64-bit word (the checker's word is unbounded; TRACE.md, Numbers)" := by decide +kernel

def decW (s : String) : Except String Word := Codec.wordOfDecimal "w" s.toUTF8

/-- The word reader refuses on length what it could only refuse by value:
leading zeros do not count, 20 significant digits are still read exactly
(`2^64` itself keeps its message), and a 21st is refused without computing
the value -- a hand-made word of a million digits is refused in the time
it takes to scan it, not the minutes `acc * 10 + d` would take. -/
example : okWord (decW "000018446744073709551615") = some 18446744073709551615 := by decide +kernel
example : okWord (decW "0") = some 0 := by decide +kernel
example : okWord (decW "00000000000000000000000000") = some 0 := by decide +kernel
example : okMsg (decW "18446744073709551616")
    = some "w: 18446744073709551616 does not fit the Lean model's 64-bit word (the checker's word is unbounded; TRACE.md, Numbers)" := by decide +kernel
example : okMsg (decW "100000000000000000000")
    = some "w: a 21-digit word does not fit the Lean model's 64-bit word (the checker's word is unbounded; TRACE.md, Numbers)" := by decide +kernel
example : okMsg (decW "0100000000000000000000")
    = some "w: a 21-digit word does not fit the Lean model's 64-bit word (the checker's word is unbounded; TRACE.md, Numbers)" := by decide +kernel
example : okMsg (decW "1x") = some "w: \"1x\" is not a decimal word" := by decide +kernel

def hx (s : String) : Except String ByteArray := Codec.hex "b" s.toUTF8
def okBytes (r : Except String ByteArray) : Option (List UInt8) :=
  match r with | .ok b => some b.data.toList | .error _ => none

example : okBytes (hx "") = some [] := by decide +kernel
example : okBytes (hx "00ff7a") = some [0, 255, 122] := by decide +kernel
example : okMsg (hx "abc") = some "b: odd-length hex" := by decide +kernel
example : okMsg (hx "0A") = some "b: 'A' is not a lowercase hex digit" := by decide +kernel
example : okMsg (hx "zz") = some "b: 'z' is not a lowercase hex digit" := by decide +kernel

/-! ## Runs and ranges: served by binary search -/

def runs3 : Except String MemRuns :=
  MemRuns.ofList "m" [(100, ByteArray.mk #[1, 2, 3]), (10, ByteArray.mk #[7]), (200, ByteArray.mk #[9, 9])]

def lookupAt (r : Except String MemRuns) (a : Nat) : Option UInt8 :=
  match r with | .ok m => m.lookup a | .error _ => none

/-- Inside each run, at both ends, and in every gap. -/
example : lookupAt runs3 10 = some 7 := by decide +kernel
example : lookupAt runs3 9 = none := by decide +kernel
example : lookupAt runs3 11 = none := by decide +kernel
example : lookupAt runs3 100 = some 1 := by decide +kernel
example : lookupAt runs3 102 = some 3 := by decide +kernel
example : lookupAt runs3 103 = none := by decide +kernel
example : lookupAt runs3 200 = some 9 := by decide +kernel
example : lookupAt runs3 201 = some 9 := by decide +kernel
example : lookupAt runs3 202 = none := by decide +kernel
example : lookupAt runs3 0 = none := by decide +kernel
example : lookupAt (MemRuns.ofList "m" []) 0 = none := by decide +kernel
/-- Two runs sharing a byte are refused, naming the second's address. -/
example : okMsg (MemRuns.ofList "m" [(10, ByteArray.mk #[1, 2]), (11, ByteArray.mk #[3])])
    = some "m: two runs overlap at address 11" := by decide +kernel
/-- Adjacent runs are not an overlap. -/
example : lookupAt (MemRuns.ofList "m" [(10, ByteArray.mk #[1, 2]), (12, ByteArray.mk #[3])]) 12 = some 3 := by decide +kernel
/-- A run of no bytes gives no byte twice, wherever it is listed: inside a
run, at a run's start before or after it.  The OCaml reader inserts nothing
for it, and the answer here does not depend on the list's order. -/
example : lookupAt (MemRuns.ofList "m" [(10, ByteArray.mk #[1, 2]), (11, ByteArray.mk #[])]) 11 = some 2 := by decide +kernel
example : lookupAt (MemRuns.ofList "m" [(10, ByteArray.mk #[1, 2]), (10, ByteArray.mk #[])]) 10 = some 1 := by decide +kernel
example : lookupAt (MemRuns.ofList "m" [(10, ByteArray.mk #[]), (10, ByteArray.mk #[1, 2])]) 10 = some 1 := by decide +kernel
example : lookupAt (MemRuns.ofList "m" [(10, ByteArray.mk #[])]) 10 = none := by decide +kernel

def rs : Ranges := Ranges.ofList [(100, 10), (50, 5), (105, 10), (200, 0)]

example : rs.contains 50 = true := by decide +kernel
example : rs.contains 54 = true := by decide +kernel
example : rs.contains 55 = false := by decide +kernel
example : rs.contains 100 = true := by decide +kernel
example : rs.contains 114 = true := by decide +kernel
example : rs.contains 115 = false := by decide +kernel
example : rs.contains 200 = false := by decide +kernel
example : rs.contains 0 = false := by decide +kernel
/-- Overlapping and adjacent ranges merge into one. -/
example : rs.ranges.toList = [(50, 5), (100, 15), (200, 0)] := by decide +kernel
/-- A range nested inside an earlier one keeps the earlier one's end. -/
example : (Ranges.ofList [(100, 10), (102, 2)]).ranges.toList = [(100, 10)] := by decide +kernel
example : (Ranges.ofList [(100, 10), (102, 2)]).contains 108 = true := by decide +kernel

/-! ## The records: `trace.ml`'s `fields` and the three readers

These are `#guard` checks rather than kernel decisions: a record-length
line is some six hundred bytes, and the kernel's evaluator takes minutes
per example over it (each byte access walks the array's list model), where
the compiled reader takes microseconds.  A `#guard` runs the compiled term
at build time and fails the build on `false`; it tests tooling and proves
nothing, which is all a test of tooling can do. -/

/-- The header's fields, one `"key":value` each, so a variant of the line
(a field added, dropped or doubled) is a list edit rather than a textual
replacement the kernel would have to search for. -/
def headerFields : List String := [
  "\"record\":\"header\"", "\"format\":\"lps-syscall-trace/2\"", "\"probe\":\"p\"", "\"case\":null",
  "\"argv\":[\"p\"]", "\"stdin\":\"\"", "\"peers\":[]", "\"seed_files\":[]", "\"mutations\":[]",
  "\"fs_check\":true", "\"alloc_limit\":\"549755813888\"", "\"abort_terminal\":false", "\"va_size\":\"sv48\"",
  "\"kernel_release\":\"6.18.46\"", "\"load_segments\":[[\"65536\",\"4096\"]]", "\"entry_sp\":\"140737213384720\"",
  "\"initial_brk\":\"653164544\"", "\"mmap_base\":\"140735519621120\"", "\"effective_mmap_base\":\"140735519596544\"",
  "\"uid\":1000", "\"gid\":1000", "\"groups\":[]", "\"nofile\":\"1024\"", "\"entry_sigmask\":\"0\"", "\"hwcap\":\"4397\"",
  "\"umask\":18", "\"initial_fs\":[]"]

def objectOf (fields : List String) : String := "{" ++ String.intercalate "," fields ++ "}"

def headerLine : String := objectOf headerFields

/-- The header with one field's text swapped. -/
def headerSwapping (old new : String) : String :=
  objectOf (headerFields.map fun f => if f == old then new else f)

/-- A 64-digit digest, as a recorded `post` is. -/
def digest : String := "eb649d8eb136a24a09054465500f8894" ++ "5ff0123456789abcdef0123456789abc"

/-- A syscall record, parametrised where the tests vary it: `events` is the
JSON list text, `post` the JSON value text (`null` or a quoted digest). -/
def syscallWith (seq : Nat) (args : String) (bytesHex : String) (ret : String) (verdict : String)
    (events : String) (post : String) : String :=
  objectOf ["\"record\":\"syscall\"", "\"seq\":" ++ toString seq, "\"occurrence\":1", "\"sysno\":\"93\"",
    "\"syscall\":\"exit\"", "\"args\":[" ++ args ++ "]",
    "\"in_mem\":[{\"addr\":\"4096\",\"bytes\":\"" ++ bytesHex ++ "\"}]",
    "\"in_wmem\":[[\"8192\",\"4096\"]]",
    "\"effect\":{\"ret\":\"" ++ ret ++ "\",\"writes\":[],\"zeros\":[],\"unmaps\":[],\"copies\":[],\"copyins\":[]}",
    "\"mutation\":null", "\"verdict\":\"" ++ verdict ++ "\"", "\"events\":" ++ events, "\"post\":" ++ post]

def sixArgs : String := "\"261\",\"0\",\"0\",\"0\",\"0\",\"0\""

def quoted (s : String) : String := "\"" ++ s ++ "\""

/-- An `ok` record with no events and the digest; any other verdict with
neither. -/
def syscallLine (verdict : String) : String :=
  if verdict == "ok" then syscallWith 0 sixArgs "0a0b" "0" verdict "[]" (quoted digest)
  else syscallWith 0 sixArgs "0a0b" "0" verdict "[]" "null"

def okWith (events : String) (post : String) : String :=
  syscallWith 0 sixArgs "0a0b" "0" "ok" events post

def ev (kind ch bytes : String) : String :=
  "{\"kind\":\"" ++ kind ++ "\",\"channel\":\"" ++ ch ++ "\",\"bytes\":\"" ++ bytes ++ "\"}"

def finalLine : String :=
  "{\"record\":\"final\",\"ending\":{\"kind\":\"exited\",\"code\":5},\"stragglers\":0,\"final_fs\":[],\"fs_verdict\":\"match\"}"

def traceOf (ls : List String) : ByteArray := (String.intercalate "\n" ls ++ "\n").toUTF8

def readErr (ls : List String) : Option String := okMsg (Trace.read "t" (traceOf ls))

def readCount (ls : List String) : Option Nat :=
  match Trace.read "t" (traceOf ls) with | .ok t => some t.syscalls.size | .error _ => none

/-! A well-formed trace reads, and its record carries what was written. -/
#guard (readCount [headerLine, syscallLine "ok", finalLine]) == (some 1)
#guard ((match Trace.read "t" (traceOf [headerLine, syscallLine "ok", finalLine]) with
    | .ok t => (t.syscalls[0]?).map fun s => (s.sysno.val, s.verdict.name, s.in_mem.lookup 4097, s.in_wmem.contains 12287)
    | .error _ => none)) == (some (93, "ok", some 0x0b, true))

/-! The reader is strict: an unknown field, a missing one, one given twice. -/
#guard (readErr [objectOf (headerFields ++ ["\"extra\":1"]), finalLine])
    == (some "t:1: header: unknown field \"extra\"")
#guard (readErr [objectOf (headerFields.filter (· != "\"umask\":18")), finalLine])
    == (some "t:1: header: missing field \"umask\"")
#guard (readErr [objectOf (headerFields ++ ["\"umask\":18"]), finalLine])
    == (some "t:1: header: field \"umask\" given twice")

/-! The format is checked before the key set. -/
#guard (readErr [headerSwapping "\"format\":\"lps-syscall-trace/2\"" "\"format\":\"lps-syscall-trace/1\"", finalLine])
    == (some "t:1: header: format \"lps-syscall-trace/1\" is not \"lps-syscall-trace/2\"")
#guard (readErr [objectOf (headerFields.filter (· != "\"format\":\"lps-syscall-trace/2\"")), finalLine])
    == (some "t:1: header: missing field \"format\"")
#guard (readErr [headerSwapping "\"va_size\":\"sv48\"" "\"va_size\":\"sv40\"", finalLine])
    == (some "t:1: header.va_size: \"sv40\" is not sv39, sv48 or sv57")

/-! Six arguments; events only on `ok`; a known verdict. -/
#guard (readErr [headerLine, syscallWith 0 "\"261\",\"0\",\"0\",\"0\",\"0\"" "0a0b" "0" "ok" "[]" (quoted digest), finalLine])
    == (some "t:2: syscall.args: 5 arguments, not six")
#guard (readErr [headerLine, syscallWith 0 sixArgs "0a0b" "0" "reject" ("[" ++ ev "write" "1" "41" ++ "]") "null", finalLine])
    == (some "t:2: syscall.events: 1 events on a verdict that admits none")
#guard (readErr [headerLine, syscallWith 0 sixArgs "0a0b" "0" "reject" "[]" (quoted digest), finalLine])
    == (some "t:2: syscall.post: a digest on a verdict that leaves no state")
#guard (readErr [headerLine, okWith "[]" "null", finalLine])
    == (some "t:2: syscall.post: an admitted step records its post-state digest")
#guard (readErr [headerLine, okWith "[]" (quoted "abc"), finalLine])
    == (some "t:2: syscall.post: \"abc\" is not a 64-digit lowercase hex digest")
#guard (readErr [headerLine, okWith "[]" (quoted (digest.drop 1).toString), finalLine])
    == (some ("t:2: syscall.post: \"" ++ (digest.drop 1).toString ++ "\" is not a 64-digit lowercase hex digest"))
#guard (readErr [headerLine, okWith "[]" (quoted ("A" ++ (digest.drop 1).toString)), finalLine])
    == (some ("t:2: syscall.post: \"A" ++ (digest.drop 1).toString ++ "\" is not a 64-digit lowercase hex digest"))
#guard (readErr [headerLine, okWith ("[" ++ ev "write" "1" "" ++ "]") (quoted digest), finalLine])
    == (some "t:2: syscall.events[0].bytes: an event with no bytes")
#guard (readErr [headerLine, okWith ("[" ++ ev "exit" "1" "41" ++ "]") (quoted digest), finalLine])
    == (some "t:2: syscall.events[0].kind: \"exit\" is not read or write")
#guard (readErr [headerLine, okWith ("[" ++ ev "write" "1" "41" ++ "]") "null", finalLine])
    == (some "t:2: syscall.post: an admitted step records its post-state digest")
/-! Coalescing: two adjacent runs of one kind on one channel are one run; a
channel or kind change opens another. -/
def runsOf (events : String) : Option (List (String × Nat × Nat)) :=
  match Trace.read "t" (traceOf [headerLine, okWith events (quoted digest), finalLine]) with
  | .ok t =>
    match t.syscalls[0]? with
    | some r =>
      match r.verdict with
      | .ok evs _ => some (evs.map fun e => (e.kind.name, e.channel.val, e.bytes.size))
      | _ => none
    | none => none
  | .error _ => none
#guard runsOf ("[" ++ ev "write" "1" "41" ++ "," ++ ev "write" "1" "4243" ++ "]") == some [("write", 1, 3)]
#guard runsOf ("[" ++ ev "write" "1" "41" ++ "," ++ ev "write" "2" "42" ++ "," ++ ev "read" "2" "43" ++ "]")
    == some [("write", 1, 1), ("write", 2, 1), ("read", 2, 1)]
#guard runsOf "[]" == some []
/-! F3: the nested shapes' refusals. -/
#guard (readErr [headerSwapping "\"peers\":[]" "\"peers\":[{\"bytes\":\"00\",\"ending\":\"eof\"}]", finalLine])
    == (some "t:1: header.peers[0].ending: \"eof\" is not fin or rst")
#guard (readErr [headerSwapping "\"uid\":1000" "\"uid\":-1", finalLine])
    == (some "t:1: header.uid: -1 is negative")
#guard (readErr [headerLine, "{\"record\":\"final\",\"ending\":{\"kind\":\"vanished\"},\"stragglers\":0,\"final_fs\":null,\"fs_verdict\":null}"])
    == (some "t:2: final.ending.kind: \"vanished\" is not exited, signaled or timed_out")
#guard (readErr [headerLine, "{\"record\":\"final\",\"ending\":null,\"stragglers\":0,\"final_fs\":[],\"fs_verdict\":\"maybe\"}"])
    == (some "t:2: final.fs_verdict: \"maybe\" is not match, mismatch or unkeyable")
#guard (readErr [headerLine, syscallWith 0 sixArgs "0a0b" "0" "reject" "[]" "null", "{\"record\":\"final\",\"ending\":null,\"stragglers\":-1,\"final_fs\":null,\"fs_verdict\":null}"])
    == (some "t:3: final.stragglers: -1 is negative")
#guard (readErr [headerLine, syscallLine "maybe", finalLine])
    == (some "t:2: syscall.verdict: \"maybe\" is not ok, reject, unmodeled or fault")
#guard (readCount [headerLine, syscallLine "fault", finalLine]) == (some 1)

/-! The words the model holds are bounded; a hex byte string is lowercase. -/
#guard (readErr [headerLine, syscallWith 0 sixArgs "0a0b" "18446744073709551616" "ok" "[]" (quoted digest), finalLine])
    == (some "t:2: syscall.effect.ret: 18446744073709551616 does not fit the Lean model's 64-bit word (the checker's word is unbounded; TRACE.md, Numbers)")
#guard (readErr [headerLine, syscallWith 0 sixArgs "0A0B" "0" "ok" "[]" (quoted digest), finalLine])
    == (some "t:2: syscall.in_mem[0].bytes: 'A' is not a lowercase hex digit")

/-! Sequence, order and completeness of the file. -/
#guard (readErr [headerLine, syscallWith 1 sixArgs "0a0b" "0" "ok" "[]" (quoted digest), finalLine])
    == (some "t:2: syscall seq 1 where 0 was expected")
#guard (readErr [headerLine, finalLine, syscallLine "ok"])
    == (some "t:3: a record after the final one")
#guard (readErr [headerLine, syscallLine "ok"])
    == (some "t: the trace ends without its final record (the run was cut short)")
#guard (readErr [syscallLine "ok", finalLine])
    == (some "t:1: the first record is \"syscall\", not the header")
/-! An empty file is an empty trace; a file holding one empty line is a
line that is not a record. -/
#guard (okMsg (Trace.read "t" ByteArray.empty)) == (some "t: empty trace")
#guard (readErr []) == (some "t:1: unexpected end of line")
#guard (readErr [headerLine, "{\"record\":\"other\"}", finalLine])
    == (some "t:2: unknown record kind \"other\"")
#guard (readErr [headerLine, "nonsense", finalLine])
    == (some "t:2: unrecognized token at byte 0")

end LpsRunner.Tests

namespace LpsRunner.Tests.DeclinesTests

/-! ## The `unported:` register: `LpsRunner.Declines`

The header grammar of `docs/lean-port/BRIEF.md` section 3, as
`tools/check_lean_spec_parity.py` reads it.  These are `#guard` checks,
not kernel decisions: `String.splitOn` and its neighbours are not
kernel-reducible, and a `decide +kernel` over them does not stop.  A
`#guard` evaluates the compiled term at build time and fails the build on
`false`; it is a test of tooling, not a proof, and the tooling it tests
proves nothing either. -/

open LpsRunner.Declines

def twoEntries : String :=
  "import Foo\n\n" ++ openDelim ++ " rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b\n" ++
  "unported: brk_spec -- brk (214) is not ported; the table declines it\n" ++
  "unported: arm_exit -- waits on the exit checker " ++ closeDelim ++ "\n\nnamespace Foo\n"

def oneLine : String :=
  "import Foo\n\n" ++ openDelim ++ " rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b " ++ closeDelim ++
  "\n\n" ++ openDelim ++ " # Prose\nunported: not_an_entry -- outside the block " ++ closeDelim ++ "\n"

def cites (file text : String) : List String := (entriesOf file text).map Decline.cite

/-! Two entries, the second on the closing line; nothing outside the block. -/
#guard cites "F.lean" twoEntries
    == ["F.lean:4: unported: brk_spec -- brk (214) is not ported; the table declines it",
        "F.lean:5: unported: arm_exit -- waits on the exit checker"]
#guard blockOf "F.lean" twoEntries == some ("F.lean", 3)
/-! A one-line block registers nothing, and a later comment is not the block. -/
#guard cites "F.lean" oneLine == []
#guard blockOf "F.lean" oneLine == some ("F.lean", 3)
/-! No block at all. -/
#guard blockOf "F.lean" "import Foo\ndef x := 1\n" == none
#guard cites "F.lean" "import Foo\ndef x := 1\n" == []
/-- The queries: by number in the reason, by the `arm_` name prefix, and the
table header by path. -/
def ix : Index := ⟨entriesOf "Sys/Mm/Mmap.lean" twoEntries,
  [("x/LinuxProcessSem/Checks/Cases/Checks/Sys/TableGuards.lean", 9), ("x/LinuxProcessSem/Checks/Sys/TableGuards.lean", 5), ("y.lean", 3)]⟩
#guard (ix.forNumber 214).map Decline.name == ["brk_spec"]
#guard (ix.forNumber 215).map Decline.name == []
#guard ix.armRegister.map Decline.name == ["arm_exit"]
/-! A Cases file of the same name would sort before the guards' file and
share its suffix; the header cited is the guards' own. -/
#guard ix.tableHeader == some ("x/LinuxProcessSem/Checks/Sys/TableGuards.lean", 5)
#guard (Index.tableHeader ⟨[], [("x/LinuxProcessSem/Checks/Cases/Checks/Sys/TableGuards.lean", 9)]⟩).isNone
/-! The generated table is no source file and carries no header; the old
hand-written path is not what is cited. -/
#guard (Index.tableHeader ⟨[], [("x/LinuxProcessSem/Checks/Sys/Table.lean", 5)]⟩).isNone
/-! A dotted entry name (`Checks.Sys.Table.arm_exit`; the parity checker
keys on the last component) is in the arm register too. -/
#guard (Index.armRegister ⟨[{ file := "F", line := 1, name := "Checks.Sys.Table.arm_exit", reason := "r" }], []⟩).length == 1
/-! A module-doc comment that is not the header (prose first, the block
after) is skipped, and the block behind it is read. -/
def proseFirst : String :=
  openDelim ++ " # A title\nunported: not_the_register -- prose " ++ closeDelim ++ "\n\n" ++ twoEntries
#guard cites "F.lean" proseFirst == ["F.lean:7: unported: brk_spec -- brk (214) is not ported; the table declines it",
                                     "F.lean:8: unported: arm_exit -- waits on the exit checker"]
#guard blockOf "F.lean" proseFirst == some ("F.lean", 6)
/-! The number is matched as `(n)`, not as a digit run: `2140` is not 214. -/
#guard (Index.forNumber ⟨entriesOf "F" (openDelim ++ " rocq-baseline: abc\nunported: x -- see (2140) " ++ closeDelim ++ "\n"), []⟩ 214).length == 0
/-! An `unported:` line without the ` -- ` separator is not an entry. -/
#guard (entryOf "F" 1 "unported: name_only").isNone
#guard (entryOf "F" 1 "  unported: a -- b -- c  ").map (fun d => (d.name, d.reason)) == some ("a", "b -- c")

def partialBlock : String :=
  openDelim ++ " " ++ headerTag ++ " abc\n" ++
  "partial: arm_x -- some shapes (119) remain unsupported\n" ++
  "unported: arm_y -- the checker remains unported\n" ++ closeDelim ++ "\n" ++
  "partial: outside -- outside the header\n"

#guard (entriesOf "F" partialBlock).map Decline.name == ["arm_x", "arm_y"]
#guard (entriesOf "F" partialBlock).map Decline.cite ==
  ["F:2: partial: arm_x -- some shapes (119) remain unsupported",
   "F:3: unported: arm_y -- the checker remains unported"]
#guard (Index.armRegister ⟨entriesOf "F" partialBlock, []⟩).map Decline.name == ["arm_y"] &&
  (entriesOf "F" partialBlock).length == 2
#guard (entriesOf "F" (partialBlock.replace "unported: arm_y"
  "drift-ticket: arm_x R-Fixture -- port the changed body again\nunported: arm_y")).map Decline.name ==
  ["arm_x", "arm_y"]
#guard (entryOf "F" 1 "partial: name_only").isNone &&
  (entryOf "F" 1 "partial: x -- some shapes remain unsupported").isSome

end LpsRunner.Tests.DeclinesTests

namespace LpsRunner.Tests.FoldTests

/-! ## The fold: `LpsRunner.Replay.fold` over a fixture checker

`Replay.Checker` is a parameter so that these `#guard`s can drive the fold
through a checker that answers by syscall number -- `CheckOk` with one
write event on channel 1 for number 1, `CheckReject` for 2,
`CheckUnmodeled` for 3, the materialization fault for 4 -- on records
built in place.  What they pin is the fold's own behaviour, which
`check_syscall_for_run` reaches only through a ported arm:
an admitted step agreeing run for run, an events disagreement, the stop at
the first disagreement and `--continue`'s marking, and the Sv48 gate. -/

open LpsRunner.Trace
open LpsRunner.Codec (Word)
open LpsRunner.Replay
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude (check_result)

def w (n : Nat) (h : n < Codec.wordBound := by decide) : Word := ⟨n, h⟩

def header (va : Trace.VaSize) : Header :=
  { probe := "p".toUTF8, case? := none, argv := [], stdin := ByteArray.empty, peers := [], seeds := [],
    mutations := [], fs_check := false, alloc_limit := 549755813888, abort_terminal := false, va_size := va,
    kernel_release := "6.18.46".toUTF8, load_segments := [(w 65536, w 4096)], entry_sp := w 140737213384720,
    initial_brk := w 653164544, mmap_base := 140735519621120, effective_mmap_base := w 140735519596544,
    uid := w 1000, gid := w 1000, groups := [], nofile := w 1024, entry_sigmask := w 0, hwcap := w 4397,
    umask := 18, initial_fs := [] }

def emptyEffect : Effect := { ret := w 0, writes := [], zeros := [], unmaps := [], copies := [], copyins := [] }

def record (seq sysno : Nat) (h : sysno < Codec.wordBound := by decide) (v : Verdict) : Syscall :=
  { seq, occurrence := 1, sysno := ⟨sysno, h⟩, name := "x".toUTF8, args := [w 0, w 0, w 0, w 0, w 0, w 0],
    in_mem := ⟨#[]⟩, in_wmem := ⟨#[]⟩, effect := emptyEffect, mutation := none, verdict := v }

def writeA : Event := ⟨.write, w 1, ByteArray.mk #[0x41]⟩

/-- The fixture checker: by syscall number, an admitted write of `A` on
channel 1, a rejection, a decline, a fault. -/
def fixture : Checker := fun i _ m =>
  match i.in_sysno.toNat with
  | 1 => some (.CheckOk m [.WriteEv (BitVec.ofNat 64 1) (BitVec.ofNat 8 0x41)])
  | 2 => some .CheckReject
  | 3 => some .CheckUnmodeled
  | 5 => some (.CheckOk m [.ExitEv (BitVec.ofNat 64 0) []])
  | 6 => some (.CheckOk m [.WriteEv (BitVec.ofNat 64 1) (BitVec.ofNat 8 0x41), .WriteEv (BitVec.ofNat 64 1) (BitVec.ofNat 8 0x41)])
  -- the two arms that read the model: 7 admits with `limst_nofile` set to
  -- 7, 8 rejects exactly when it sees that value
  | 7 => some (.CheckOk { m with m_lim := { m.m_lim with limst_nofile := BitVec.ofNat 64 7 } } [])
  | 8 => if m.m_lim.limst_nofile == BitVec.ofNat 64 7 then some .CheckReject else some (.CheckOk m [])
  | _ => none

def traceOf (va : Trace.VaSize) (recs : List Syscall) : Trace :=
  { header := header va, syscalls := recs.toArray,
    final := { ending := none, stragglers := 0, final_fs := none, fs_verdict := none } }

def okA : Verdict := .ok [writeA] "d"
/-- An admitted step with no event. -/
def okNone : Verdict := .ok [] "d"
def okOtherDigest : Verdict := .ok [⟨.write, w 1, ByteArray.mk #[0x41]⟩] "other-digest"
def okB : Verdict := .ok [⟨.write, w 1, ByteArray.mk #[0x42]⟩] "d"
def okCh2 : Verdict := .ok [⟨.write, w 2, ByteArray.mk #[0x41]⟩] "d"
/-- Two bytes on one channel as the format records them: one run. -/
def okAA : Verdict := .ok [⟨.write, w 1, ByteArray.mk #[0x41, 0x41]⟩] "d"
/-- The same two bytes as two runs: not the canonical form the reader
produces (`trace.ml`'s `coalesce` at read time), so not what `judge` emits. -/
def okAthenA : Verdict := .ok [writeA, writeA] "d"

/-- `judged`, `comparable`, `reproduced`, the first disagreement, then
per occurrence whether it agreed and whether it came after a divergence.
`comparable` counts the records judged before the run's first divergence:
the only ones whose recorded verdict the run can be held to, and the
denominator `reproduced` is taken over. -/
def summary (r : FoldResult) : Nat × Nat × Nat × Option Nat × List Bool × List Bool :=
  (r.judged, r.comparable, r.reproduced, r.firstDisagreement,
   r.occurrences.toList.map (·.agree), r.occurrences.toList.map (·.afterDivergence))

/-! Every arm reproduced: the admitted write run for run (the digest is not
compared), the rejection, the decline, the fault. -/
#guard summary (fold fixture false (traceOf .sv48 [record 0 1 (v := okA), record 1 2 (v := .reject), record 2 3 (v := .unmodeled), record 3 4 (v := .fault)]))
    == (4, 4, 4, none, [true, true, true, true], [false, false, false, false])
#guard summary (fold fixture false (traceOf .sv48 [record 0 1 (v := okOtherDigest)])) == (1, 1, 1, none, [true], [false])
/-! An events disagreement: other bytes, or another channel, on an admitted step. -/
#guard summary (fold fixture false (traceOf .sv48 [record 0 1 (v := okB)])) == (1, 1, 0, some 0, [false], [false])
#guard summary (fold fixture false (traceOf .sv48 [record 0 1 (v := okCh2)])) == (1, 1, 0, some 0, [false], [false])
/-! A verdict disagreement on every other arm. -/
#guard summary (fold fixture false (traceOf .sv48 [record 0 2 (v := okA)])) == (1, 1, 0, some 0, [false], [false])
#guard summary (fold fixture false (traceOf .sv48 [record 0 3 (v := .reject)])) == (1, 1, 0, some 0, [false], [false])
#guard summary (fold fixture false (traceOf .sv48 [record 0 4 (v := .unmodeled)])) == (1, 1, 0, some 0, [false], [false])
/-! The stop at the first disagreement, and `--continue` judging past it
with the later verdicts marked.  Record 2 agrees under `--continue`, and
is counted in neither `comparable` nor `reproduced`: the model it was
judged against lost record 1's effects when the checker declined it, so
the agreement is not one between the two checkers (`Replay`'s header). -/
#guard summary (fold fixture false (traceOf .sv48 [record 0 1 (v := okA), record 1 2 (v := .unmodeled), record 2 3 (v := .unmodeled)]))
    == (2, 2, 1, some 1, [true, false], [false, false])
#guard summary (fold fixture true (traceOf .sv48 [record 0 1 (v := okA), record 1 2 (v := .unmodeled), record 2 3 (v := .unmodeled)]))
    == (3, 2, 1, some 1, [true, false, true], [false, false, true])
/-! The Sv48 gate: another declaration declines every record before the
checker is asked, so the recorded `ok` is not reproduced and the decline
is marked as the gate's. -/
#guard summary (fold fixture true (traceOf .sv39 [record 0 1 (v := okA), record 1 3 (v := .unmodeled)]))
    == (2, 1, 0, some 0, [false, true], [false, true])
#guard (fold fixture true (traceOf .sv39 [record 0 1 (v := okA)])).occurrences.toList.map (fun o => (o.vaDeclined, o.arm.isNone)) == [(true, true)]
#guard (fold fixture true (traceOf .sv48 [record 0 3 (v := .unmodeled)])).occurrences.toList.map (fun o => (o.vaDeclined, o.arm.map ArmStatus.name)) == [(false, some "absent")]
/-! A step whose events the format has no shape for (an `ExitEv`) is
reported as `unrenderable`, agrees with no recorded verdict, and parts. -/
#guard (fold fixture true (traceOf .sv48 [record 0 5 (v := okA)])).occurrences.toList.map (fun o => (o.lean.name, o.agree)) == [("unrenderable", false)]
#guard summary (fold fixture false (traceOf .sv48 [record 0 5 (v := .reject)])) == (1, 1, 0, some 0, [false], [false])
/-! `judge` coalesces the model's one-byte events into the format's runs
before comparing (`trace.ml`'s `events_of_model` then `coalesce`): two
bytes on one channel are one recorded run, and a `judge` that forgot to
coalesce would agree with the two-run spelling instead. -/
#guard summary (fold fixture false (traceOf .sv48 [record 0 6 (v := okAA)])) == (1, 1, 1, none, [true], [false])
#guard summary (fold fixture false (traceOf .sv48 [record 0 6 (v := okAthenA)])) == (1, 1, 0, some 0, [false], [false])
/-! `eventsOfModel` is an accumulator, not a map: a step's events are one
per byte, so an admitted write of `main.ml`'s `write_capture_max` (4 MiB) is
2^22 of them, and the mapped shape recursed once per event and died of deep
recursion at exactly that size.  The bound is the corpus's own, not a
convenience: `write_window/010.jsonl` already carries a 262174-byte
capture, and a write arm in `checked_table` is what makes the checker emit
its bytes. -/
#guard (eventsOfModel (List.replicate 4194304 (.WriteEv (BitVec.ofNat 64 1) (BitVec.ofNat 8 0x41)))).toOption.map (fun l => (l.length, (coalesce l).map (·.bytes.size)))
    == some (4194304, [4194304])
/-! `seedModel` places the header's fields where `main.ml`'s `replay` passes
them to `init_model`: the break, the entry sp, the effective mmap base, the
allocation limit and the credentials are read back from the seeded model. -/
#guard (let m := seedModel (header .sv48); let vm := m_vmmaps m
  (vm.vm_brk == toWord (w 653164544), vm.vm_init_sp == toWord (w 140737213384720),
   vm.vm_mmap_base == toWord (w 140735519596544), vm.vm_limit == 549755813888,
   (m_creds m).cr_uid == toWord (w 1000), (m_creds m).cr_gid == toWord (w 1000),
   m_nofile m == toWord (w 1024), m_sigmask m == toWord (w 0)))
    == (true, true, true, true, true, true, true, true)
/-! The model the next arm sees is the one the last admitted step handed
back, and none other.  Arms 7 and 8 read it (7 sets `limst_nofile` to 7,
8 rejects exactly on seeing that), so these guards are not closed by a
fold that never threads the model: arm 8 alone sees the seeded value; after
arm 7 it sees 7; a rejection and a decline in between leave it there, and a
decline before any admitted step leaves the seed. -/
#guard (fold fixture true (traceOf .sv48 [record 0 8 (v := okNone)])).reproduced == 1
#guard (fold fixture true (traceOf .sv48 [record 0 7 (v := okNone), record 1 8 (v := .reject)])).reproduced == 2
#guard (fold fixture true (traceOf .sv48 [record 0 7 (v := okNone), record 1 2 (v := .reject), record 2 8 (v := .reject)])).reproduced == 3
#guard (fold fixture true (traceOf .sv48 [record 0 7 (v := okNone), record 1 3 (v := .unmodeled), record 2 8 (v := .reject)])).reproduced == 3
#guard (fold fixture true (traceOf .sv48 [record 0 3 (v := .unmodeled), record 1 8 (v := okNone)])).reproduced == 2
-- ...and the guards above can fail: arm 8 recorded as rejecting from the seed is a disagreement
#guard (fold fixture true (traceOf .sv48 [record 0 8 (v := .reject)])).reproduced == 0
/-! `comparable` is the negation of `afterDivergence`, occurrence for
occurrence: the field the H4 comparison reads to tell a disagreement from
a record judged past one. -/
#guard (fold fixture true (traceOf .sv48 [record 0 1 (v := okA), record 1 2 (v := .unmodeled), record 2 3 (v := .unmodeled)])).occurrences.toList.map
    (fun o => (o.comparable, o.comparable == !o.afterDivergence)) == [(true, true), (true, true), (false, true)]

end LpsRunner.Tests.FoldTests
