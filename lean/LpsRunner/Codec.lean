import LpsRunner.Json

/-! # LpsRunner.Codec — words, bytes and the captured memory of a record

Test tooling: nothing under `LpsRunner/` is part of the trusted
specification, and no proof depends on it.

The trace format (`testing/syscall-check/TRACE.md`, "Numbers") carries
every 64-bit quantity as a decimal string and every byte string as
lowercase hex, and `testing/syscall-check/trace.ml`'s `as_word` and
`as_hex` say what is refused: a word that is not a non-empty run of
decimal digits, a hex string of odd length or with a digit outside
`0-9a-f`.  This module reads both, totally, and adds the one refusal the
Lean side owes and the OCaml side does not: a word the Lean model cannot
hold.

WORDS ARE BOUNDED HERE AND UNBOUNDED THERE.  The checker's word type is
Rocq's `bv 64`, whose extraction erases the range proof, so the OCaml
replay reads a word as an unbounded integer and a `--mutate ret=2^64`
case (`tests/set_tid.c`, case `two`) records a pair the OCaml checker
really judged.  The Lean model's word is `BitVec 64`, which cannot
represent that value, and wrapping it would judge a pair nobody recorded.
So `word` refuses a value at or above `2^64` naming the field, the record
is refused as a whole, and the runner exits 2 for that trace.  The
corpus holds exactly one such record (`traces/set_tid/022.jsonl`, pinned
by `tools/test_lps_runner.py`'s decode of the whole corpus), and
`LpsRunner.Tests` pins the refusal.

THE CAPTURED MEMORY IS SERVED BY BINARY SEARCH.  A `syscall` record's
`in_mem` is a list of address-ordered byte runs -- a `write`'s or
`pwrite64`'s source buffer, and each `writev` iov, is captured up to 4 MiB
(`main.ml`'s `write_capture_max`); the other captures (paths, iovec arrays,
structs) are what the arm read and carry no such cap -- and the checker
asks the lookup one byte at a time.  The OCaml replay hashes every byte; here the runs are
kept as `ByteArray`s in an array sorted by start address, and a lookup
finds its run by binary search and indexes into it.  `in_wmem` is a list
of ranges and the same search decides membership.  A `List`-backed
lookup would be O(n) per byte, quadratic over a transfer, which is what
`docs/lean-port/ADVERSARIAL.md` (F6) refused. -/

namespace LpsRunner.Codec

/-- `2^64`, the bound a model word must satisfy. -/
def wordBound : Nat := 2 ^ 64

def isDigit (c : UInt8) : Bool := 0x30 ≤ c ∧ c ≤ 0x39

/-- A byte string as printable text, for messages: printable ASCII as it
is, anything else as `\xNN`. -/
def showBytes (b : ByteArray) : String :=
  String.join (b.data.toList.map fun c =>
    if 0x20 ≤ c ∧ c < 0x7f ∧ c ≠ 0x22 ∧ c ≠ 0x5c then String.singleton (Char.ofNat c.toNat)
    else s!"\\x{Json.hex2 c}")

/-- The value of a run of decimal digits. -/
def digitsValue (s : ByteArray) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | fuel + 1, i, acc =>
    if i < s.size then digitsValue s fuel (i + 1) (acc * 10 + ((s.get! i).toNat - 0x30))
    else acc

/-- `trace.ml`'s `as_word` on the string's bytes: a non-empty run of
decimal digits, of any length.  The value is exact, and `digitsValue` is a
bignum product per digit, so a hand-made numeral of a million digits in
an unbounded position (`asWordNat`: a run's address, a budget, a seeded
file's size) costs about a minute where OCaml's GMP takes none; the
answer is the same, and only the `Word` positions, whose 64-bit ceiling
makes the count decisive, refuse on length (`wordOfDecimal`). -/
def decimal (what : String) (s : ByteArray) : Except String Nat :=
  if s.size == 0 ∨ ¬ s.data.toList.all isDigit then
    .error s!"{what}: \"{showBytes s}\" is not a decimal word"
  else .ok (digitsValue s (s.size + 1) 0 0)

/-- A lowercase hex digit's value. -/
def hexNyb (c : UInt8) : Option Nat :=
  if 0x30 ≤ c ∧ c ≤ 0x39 then some (c.toNat - 0x30)
  else if 0x61 ≤ c ∧ c ≤ 0x66 then some (c.toNat - 0x61 + 10)
  else none

def hexPairs (what : String) (s : ByteArray) : Nat → Nat → ByteArray → Except String ByteArray
  | 0, _, acc => .ok acc
  | fuel + 1, i, acc =>
    if i + 1 < s.size then
      match hexNyb (s.get! i), hexNyb (s.get! (i + 1)) with
      | some a, some b => hexPairs what s fuel (i + 2) (acc.push (UInt8.ofNat (a * 16 + b)))
      | none, _ => .error s!"{what}: {Json.showByte (s.get! i)} is not a lowercase hex digit"
      | _, none => .error s!"{what}: {Json.showByte (s.get! (i + 1))} is not a lowercase hex digit"
    else .ok acc

/-- `trace.ml`'s `as_hex`: bytes as lowercase hex, two digits each. -/
def hex (what : String) (s : ByteArray) : Except String ByteArray :=
  if s.size % 2 == 1 then .error s!"{what}: odd-length hex"
  else hexPairs what s (s.size / 2 + 1) 0 (ByteArray.emptyWithCapacity (s.size / 2))

/-- A word the Lean model can hold: a natural number below `2^64`, with
the proof, so that the model-side conversion cannot wrap. -/
structure Word where
  val : Nat
  lt : val < wordBound

instance : Repr Word := ⟨fun w _ => repr w.val⟩

/-- The bound the Lean side owes: refused at or above `2^64`, naming the
field and the value (the module header says why the OCaml side does not). -/
def word (what : String) (n : Nat) : Except String Word :=
  if h : n < wordBound then .ok ⟨n, h⟩
  else .error s!"{what}: {n} does not fit the Lean model's 64-bit word (the checker's word is unbounded; TRACE.md, Numbers)"

/-- How many `0` bytes the string opens with. -/
def leadingZeros (s : ByteArray) : Nat := (s.data.toList.takeWhile (· == 0x30)).length

/-- `decimal` then `word`, without computing a value no word can hold.
`2^64` has 20 digits, so a word of more than 20 significant digits is
refused on its length alone; up to 20 the value is exact and `word`'s own
message names it.  The set refused is `word`'s: nothing bounds the length
of a hand-made trace's word, and `digitsValue` costs the square of the
digit count -- a million-digit word takes minutes to refuse by value and
one pass to refuse by length. -/
def wordOfDecimal (what : String) (s : ByteArray) : Except String Word :=
  if s.size == 0 ∨ ¬ s.data.toList.all isDigit then
    .error s!"{what}: \"{showBytes s}\" is not a decimal word"
  else
    let digits := s.size - leadingZeros s
    if digits > 20 then
      .error s!"{what}: a {digits}-digit word does not fit the Lean model's 64-bit word (the checker's word is unbounded; TRACE.md, Numbers)"
    else word what (digitsValue s (s.size + 1) 0 0)

/-! ## Sorted runs and ranges -/

/-- Insert into a list sorted by the key. -/
def insertBy {α : Type} (key : α → Nat) (x : α) : List α → List α
  | [] => [x]
  | y :: rest => if key x ≤ key y then x :: y :: rest else y :: insertBy key x rest

/-- Insertion sort by the key; stable, and structural, so `LpsRunner.Tests`
can run it in the kernel.  The lists it sorts are a record's runs and
ranges, a few dozen entries at most.  On the writer's output, which is
already ascending, it is linear; a hand-made list in descending key order
is quadratic, and a few hundred thousand such entries take minutes.  That
is a cost, not an answer: the sorted result and every verdict are the
same, so no bound is placed here (a bound the harness needed would be a
harness limit, AGENTS.md's "dependency runs one way"). -/
def sortBy {α : Type} (key : α → Nat) : List α → List α
  | [] => []
  | x :: rest => insertBy key x (sortBy key rest)

/-- The number of leading entries whose key is at most `a`, in a key-sorted
array; a binary search on `[lo, hi)` with fuel. -/
def countLE {α : Type} (arr : Array α) (key : α → Nat) (a : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      match arr[mid]? with
      | some x => if key x ≤ a then countLE arr key a fuel (mid + 1) hi else countLE arr key a fuel lo mid
      | none => lo
    else lo

/-- The last entry whose key is at most `a`, if any. -/
def findLE {α : Type} (arr : Array α) (key : α → Nat) (a : Nat) : Option α :=
  match countLE arr key a (arr.size + 1) 0 arr.size with
  | 0 => none
  | k + 1 => arr[k]?

/-- The pre-syscall memory of a record: address-ordered, disjoint runs. -/
structure MemRuns where
  runs : Array (Nat × ByteArray)

/-- Adjacent runs must not overlap: a byte the record gave twice could have
been given two values, and the OCaml reader's hash table would keep
whichever it inserted last.  Refused rather than reconciled. -/
def disjointRuns : List (Nat × ByteArray) → Option Nat
  | (a1, b1) :: (a2, b2) :: rest =>
    if a1 + b1.size > a2 then some a2 else disjointRuns ((a2, b2) :: rest)
  | _ => none

/-- Runs as read: sorted by start (the writer emits them in address
order, so this is the identity on a real trace) and checked disjoint.  A
run of no bytes is dropped first: it gives no byte and so can give none
twice, and the OCaml reader inserts nothing for it (`main.ml`, the
`in_mem` loop); kept, it would count as an overlap when listed at or
inside another run and not when listed before one, an answer that
depended on the list's order.  The writer's `mem_runs` never opens a
run without a byte, so this is about hand-made traces. -/
def MemRuns.ofList (what : String) (l : List (Nat × ByteArray)) : Except String MemRuns :=
  let sorted := sortBy (·.1) (l.filter fun (_, b) => b.size > 0)
  match disjointRuns sorted with
  | some a => .error s!"{what}: two runs overlap at address {a}"
  | none => .ok ⟨sorted.toArray⟩

/-- The byte at address `a`, if a run holds it. -/
def MemRuns.lookup (m : MemRuns) (a : Nat) : Option UInt8 :=
  match findLE m.runs (·.1) a with
  | some (start, bytes) => if a < start + bytes.size then some (bytes.get! (a - start)) else none
  | none => none

/-- How many bytes the runs hold. -/
def MemRuns.bytes (m : MemRuns) : Nat := m.runs.foldl (fun acc (_, b) => acc + b.size) 0

/-- The writable view of a record: sorted, merged ranges `(base, len)`. -/
structure Ranges where
  ranges : Array (Nat × Nat)

/-- Merge overlapping and adjacent ranges of a base-sorted list into a
disjoint union; membership is the same as in the list, and a binary search
needs the union. -/
def mergeRanges : List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | [], acc => acc.reverse
  | (b, l) :: rest, [] => mergeRanges rest [(b, l)]
  | (b, l) :: rest, (pb, pl) :: acc =>
    if b ≤ pb + pl then mergeRanges rest ((pb, max (pb + pl) (b + l) - pb) :: acc)
    else mergeRanges rest ((b, l) :: (pb, pl) :: acc)

def Ranges.ofList (l : List (Nat × Nat)) : Ranges :=
  ⟨(mergeRanges (sortBy (·.1) l) []).toArray⟩

/-- Whether some range holds address `a` (`main.ml`'s `range_hides`, which
`replay`'s `in_wmem` answers `Some z0` by). -/
def Ranges.contains (r : Ranges) (a : Nat) : Bool :=
  match findLE r.ranges (·.1) a with
  | some (base, len) => a < base + len
  | none => false

/-- How many bytes the ranges cover. -/
def Ranges.bytes (r : Ranges) : Nat := r.ranges.foldl (fun acc (_, l) => acc + l) 0

end LpsRunner.Codec
