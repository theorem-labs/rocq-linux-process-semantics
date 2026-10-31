/-! # LpsRunner.Json — the strict JSON a trace record is written in

Test tooling: nothing under `LpsRunner/` is part of the trusted
specification, and no proof depends on it.

One line of a trace is one JSON object, and `testing/syscall-check/trace.ml`
is the authority on what that object may contain: `parse` there is a
recursive-descent reader that admits integers only (a fraction or an
exponent is refused rather than rounded, a leading zero is refused rather
than read), refuses control characters inside strings, requires every
`\u` surrogate to be paired, and refuses trailing content.  This module is
that reader again, over the bytes of one line, so that the Lean runner
accepts exactly the lines the OCaml replay accepts and refuses the rest
naming the byte.  Where the two disagree, `trace.ml` is what a trace is.

Two representation choices follow from the format rather than from taste:

- A JSON string is kept as its BYTES.  `trace.ml` writes strings byte for
  byte, so a file name in a directory listing can carry a byte that is not
  UTF-8 (`traces/faccessat_spec/063.jsonl` does), and a Lean `String`
  cannot hold it.  Object KEYS are the one place a `String` is needed, for
  comparison against the record's key set; a key is decoded as ASCII and a
  key outside ASCII is refused, which is what the strict key-set check
  would have done to it one step later.
- A JSON number is bounded to the OCaml `int` the format means by it
  (`trace.ml`: `integer %s does not fit an OCaml int`).  Every 64-bit
  word of the format travels as a decimal STRING for exactly this reason,
  and `LpsRunner.Codec` reads those.

Every loop is structural recursion on a fuel argument and every function
is total, with no definition left unfinished, so the reader can be run by the
kernel in `LpsRunner.Tests` as well as compiled.  The fuel a caller passes
is derived from the input length and cannot run out on any input, so the
`out of fuel` arms are unreachable; they exist so the definitions are
total rather than because a trace can reach them. -/

namespace LpsRunner.Json

/-- A JSON value as the trace format uses it: integers only, strings as
bytes, objects as an ordered member list (duplicates are kept so the
record readers can refuse them). -/
inductive Json where
  | null
  | bool (b : Bool)
  | int (n : Int)
  | str (s : ByteArray)
  | arr (xs : List Json)
  | obj (kvs : List (String × Json))

/-- A parse result: the value or the reason, as `trace.ml`'s `Malformed`. -/
abbrev Result (α : Type) := Except String α

/-- The byte at `i`, or `none` past the end. -/
@[inline] def at? (s : ByteArray) (i : Nat) : Option UInt8 :=
  if i < s.size then some (s.get! i) else none

/-- OCaml's `int` range on a 64-bit host, which `trace.ml`'s `number` holds
every JSON number to (`int_of_string_opt`). -/
def ocamlMaxInt : Int := 2 ^ 62 - 1
def ocamlMinInt : Int := -(2 ^ 62)

/-- A hex digit as a character. -/
def hexChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat (0x30 + n) else Char.ofNat (0x61 + n - 10)

/-- Two lowercase hex digits. -/
def hex2 (c : UInt8) : String :=
  String.ofList [hexChar (c.toNat / 16), hexChar (c.toNat % 16)]

/-- A byte as OCaml's `%C` would show it, for messages. -/
def showByte (c : UInt8) : String :=
  if 0x20 ≤ c ∧ c < 0x7f then s!"'{Char.ofNat c.toNat}'" else s!"'\\x{hex2 c}'"

/-- Skip JSON whitespace (space, tab, newline, carriage return). -/
def skipWs (s : ByteArray) (i : Nat) : Nat → Nat
  | 0 => i
  | fuel + 1 =>
    match at? s i with
    | some 0x20 | some 0x09 | some 0x0a | some 0x0d => skipWs s (i + 1) fuel
    | _ => i

/-- Whether `lit` is the bytes of `s` starting at `i`. -/
def litAt (s : ByteArray) (i : Nat) : List UInt8 → Bool
  | [] => true
  | c :: rest => at? s i == some c && litAt s (i + 1) rest

/-- A `\u` escape's hex digit (both cases, as `trace.ml`'s `hex4`). -/
def escNyb (c : UInt8) : Option Nat :=
  if 0x30 ≤ c ∧ c ≤ 0x39 then some (c.toNat - 0x30)
  else if 0x61 ≤ c ∧ c ≤ 0x66 then some (c.toNat - 0x61 + 10)
  else if 0x41 ≤ c ∧ c ≤ 0x46 then some (c.toNat - 0x41 + 10)
  else none

/-- The four hex digits of a `\u` escape at `i`. -/
def hex4 (s : ByteArray) (i : Nat) : Result Nat :=
  if i + 4 > s.size then .error s!"truncated \\u escape at byte {i}"
  else
    match escNyb (s.get! i), escNyb (s.get! (i + 1)), escNyb (s.get! (i + 2)),
        escNyb (s.get! (i + 3)) with
    | some a, some b, some c, some d => .ok (((a * 16 + b) * 16 + c) * 16 + d)
    | _, _, _, _ => .error s!"bad \\u escape at byte {i}"

/-- Append the UTF-8 encoding of code point `cp`, as `trace.ml`'s `add_utf8`. -/
def addUtf8 (b : ByteArray) (cp : Nat) : ByteArray :=
  if cp < 0x80 then b.push (UInt8.ofNat cp)
  else if cp < 0x800 then
    (b.push (UInt8.ofNat (0xc0 ||| (cp >>> 6)))).push (UInt8.ofNat (0x80 ||| (cp &&& 0x3f)))
  else if cp < 0x10000 then
    ((b.push (UInt8.ofNat (0xe0 ||| (cp >>> 12)))).push
        (UInt8.ofNat (0x80 ||| ((cp >>> 6) &&& 0x3f)))).push
      (UInt8.ofNat (0x80 ||| (cp &&& 0x3f)))
  else
    (((b.push (UInt8.ofNat (0xf0 ||| (cp >>> 18)))).push
        (UInt8.ofNat (0x80 ||| ((cp >>> 12) &&& 0x3f)))).push
        (UInt8.ofNat (0x80 ||| ((cp >>> 6) &&& 0x3f)))).push
      (UInt8.ofNat (0x80 ||| (cp &&& 0x3f)))

/-- The body of a string whose opening quote is at `i - 1`: the decoded
bytes and the index after the closing quote.  Escapes are `trace.ml`'s
eight plus `\u` with paired surrogates; a raw control character is refused;
a raw byte outside ASCII is kept as it is. -/
def strBody (s : ByteArray) : Nat → Nat → ByteArray → Result (ByteArray × Nat)
  | 0, _, _ => .error "unterminated string"
  | fuel + 1, i, acc =>
    match at? s i with
    | none => .error "unterminated string"
    | some 0x22 => .ok (acc, i + 1)
    | some 0x5c =>
      match at? s (i + 1) with
      | some 0x22 => strBody s fuel (i + 2) (acc.push 0x22)
      | some 0x5c => strBody s fuel (i + 2) (acc.push 0x5c)
      | some 0x2f => strBody s fuel (i + 2) (acc.push 0x2f)
      | some 0x62 => strBody s fuel (i + 2) (acc.push 0x08)
      | some 0x66 => strBody s fuel (i + 2) (acc.push 0x0c)
      | some 0x6e => strBody s fuel (i + 2) (acc.push 0x0a)
      | some 0x72 => strBody s fuel (i + 2) (acc.push 0x0d)
      | some 0x74 => strBody s fuel (i + 2) (acc.push 0x09)
      | some 0x75 =>
        match hex4 s (i + 2) with
        | .error e => .error e
        | .ok cp =>
          if 0xd800 ≤ cp ∧ cp < 0xdc00 then
            -- a high surrogate: the low half must follow as another \u.  The
            -- byte in each refusal is the one trace.ml's `string` names: the
            -- index after the quartet its `hex4` had just read.
            if at? s (i + 6) == some 0x5c ∧ at? s (i + 7) == some 0x75 then
              match hex4 s (i + 8) with
              | .error e => .error e
              | .ok lo =>
                if lo < 0xdc00 ∨ lo > 0xdfff then .error s!"unpaired surrogate at byte {i + 12}"
                else strBody s fuel (i + 12)
                  (addUtf8 acc (0x10000 + (cp - 0xd800) * 0x400 + (lo - 0xdc00)))
            else .error s!"unpaired surrogate at byte {i + 6}"
          else if 0xdc00 ≤ cp ∧ cp < 0xe000 then .error s!"unpaired surrogate at byte {i + 6}"
          else strBody s fuel (i + 6) (addUtf8 acc cp)
      | _ => .error s!"bad escape at byte {i + 1}"
    | some c =>
      if c < 0x20 then .error s!"control character in string at byte {i}"
      else strBody s fuel (i + 1) (acc.push c)

/-- Decimal digits from `i`: their value, the index after them, and how many
there were.  Once the value has passed `2^62` -- outside an OCaml `int` on
either sign, so refused whatever follows -- the digits are counted and no
longer accumulated: `acc * 10 + d` over a million digits is a bignum
product per digit and takes minutes, and nothing bounds the digit count
of a hand-made trace.  A saturated value is above `2^62` and not the
number's; `number` reports by digit count then. -/
def digitsAt (s : ByteArray) : Nat → Nat → Nat → Nat → Nat × Nat × Nat
  | 0, i, acc, n => (acc, i, n)
  | fuel + 1, i, acc, n =>
    match at? s i with
    | some c =>
      if 0x30 ≤ c ∧ c ≤ 0x39 then
        digitsAt s fuel (i + 1) (if acc > 2 ^ 62 then acc else acc * 10 + (c.toNat - 0x30)) (n + 1)
      else (acc, i, n)
    | none => (acc, i, n)

/-- A JSON number at `i`: an integer in OCaml's `int` range, with no
leading zero and no fraction or exponent. -/
def number (s : ByteArray) (i : Nat) : Result (Json × Nat) :=
  let neg := at? s i == some 0x2d
  let start := if neg then i + 1 else i
  let (v, j, n) := digitsAt s (s.size + 1) start 0 0
  if n == 0 then .error s!"bad number at byte {i}"
  else if n > 1 ∧ at? s start == some 0x30 then .error s!"number with a leading zero at byte {i}"
  else
    match at? s j with
    | some 0x2e | some 0x65 | some 0x45 =>
      .error s!"non-integer number at byte {i}: no field is a float"
    | _ =>
      let value : Int := if neg then -(v : Int) else v
      if value > ocamlMaxInt ∨ value < ocamlMinInt then
        -- `2^62` has 19 digits: a 20th puts the value above `2^62` whatever
        -- the digits, and `digitsAt` may have stopped accumulating (it does
        -- once the prefix passes `2^62`), so `v` need not be the number and
        -- the refusal names the count instead
        if n > 19 then .error s!"a {n}-digit integer at byte {i} does not fit an OCaml int"
        else .error s!"integer {value} does not fit an OCaml int"
      else .ok (.int value, j)

/-- An object key: the string's bytes as ASCII.  A key outside ASCII is
refused here; the record readers would refuse it as an unknown field. -/
def keyOfBytes (i : Nat) (kb : ByteArray) : Result String :=
  if kb.data.toList.all (· < 0x80) then .ok (String.ofList (kb.data.toList.map fun c => Char.ofNat c.toNat))
  else .error s!"object key at byte {i} is not ASCII"

mutual
  /-- A value at `i` (leading whitespace allowed) and the index after it. -/
  def value (s : ByteArray) : Nat → Nat → Result (Json × Nat)
    | 0, i => .error s!"out of fuel at byte {i}"
    | fuel + 1, i =>
      let i := skipWs s i (s.size + 1)
      match at? s i with
      | none => .error "unexpected end of line"
      | some 0x6e =>
        if litAt s i [0x6e, 0x75, 0x6c, 0x6c] then .ok (.null, i + 4)
        else .error s!"unrecognized token at byte {i}"
      | some 0x74 =>
        if litAt s i [0x74, 0x72, 0x75, 0x65] then .ok (.bool true, i + 4)
        else .error s!"unrecognized token at byte {i}"
      | some 0x66 =>
        if litAt s i [0x66, 0x61, 0x6c, 0x73, 0x65] then .ok (.bool false, i + 5)
        else .error s!"unrecognized token at byte {i}"
      | some 0x22 =>
        match strBody s (s.size + 1) (i + 1) ByteArray.empty with
        | .ok (b, j) => .ok (.str b, j)
        | .error e => .error e
      | some 0x5b =>
        let j := skipWs s (i + 1) (s.size + 1)
        if at? s j == some 0x5d then .ok (.arr [], j + 1) else items s fuel j []
      | some 0x7b =>
        let j := skipWs s (i + 1) (s.size + 1)
        if at? s j == some 0x7d then .ok (.obj [], j + 1) else members s fuel j []
      | some c =>
        if c == 0x2d ∨ (0x30 ≤ c ∧ c ≤ 0x39) then number s i
        else .error s!"unexpected {showByte c} at byte {i}"

  /-- The elements of a non-empty array from `i`, accumulated in reverse. -/
  def items (s : ByteArray) : Nat → Nat → List Json → Result (Json × Nat)
    | 0, i, _ => .error s!"out of fuel at byte {i}"
    | fuel + 1, i, acc =>
      match value s fuel i with
      | .error e => .error e
      | .ok (v, j) =>
        let j := skipWs s j (s.size + 1)
        match at? s j with
        | some 0x2c => items s fuel (j + 1) (v :: acc)
        | some 0x5d => .ok (.arr (v :: acc).reverse, j + 1)
        | _ => .error s!"expected , or ] at byte {j}"

  /-- The members of a non-empty object from `i`, accumulated in reverse. -/
  def members (s : ByteArray) : Nat → Nat → List (String × Json) → Result (Json × Nat)
    | 0, i, _ => .error s!"out of fuel at byte {i}"
    | fuel + 1, i, acc =>
      let i := skipWs s i (s.size + 1)
      match at? s i with
      | some 0x22 =>
        match strBody s (s.size + 1) (i + 1) ByteArray.empty with
        | .error e => .error e
        | .ok (kb, j) =>
          match keyOfBytes i kb with
          | .error e => .error e
          | .ok k =>
            let j := skipWs s j (s.size + 1)
            match at? s j with
            | some 0x3a =>
              match value s fuel (j + 1) with
              | .error e => .error e
              | .ok (v, j2) =>
                let j2 := skipWs s j2 (s.size + 1)
                match at? s j2 with
                | some 0x2c => members s fuel (j2 + 1) ((k, v) :: acc)
                | some 0x7d => .ok (.obj ((k, v) :: acc).reverse, j2 + 1)
                | _ => .error s!"expected , or } at byte {j2}"
            | some c => .error s!"expected ':' at byte {j}, found {showByte c}"
            | none => .error s!"expected ':' at byte {j}, found end of line"
      | some c => .error s!"expected '\"' at byte {i}, found {showByte c}"
      | none => .error s!"expected '\"' at byte {i}, found end of line"
end

/-- The fuel `parse` hands the reader: every step of `value`, `items` and
`members` either consumes a byte or precedes one that does, so twice the
length plus a constant is never exhausted. -/
def fuelFor (s : ByteArray) : Nat := 2 * s.size + 4

/-- One line as one JSON value, whole: whitespace may surround it, anything
else after it is refused. -/
def parse (s : ByteArray) : Result Json :=
  match value s (fuelFor s) 0 with
  | .error e => .error e
  | .ok (v, j) =>
    let j := skipWs s j (s.size + 1)
    if j == s.size then .ok v else .error s!"trailing content at byte {j}"

/-- The kind of value, for messages. -/
def Json.kind : Json → String
  | .null => "null"
  | .bool _ => "a boolean"
  | .int _ => "an integer"
  | .str _ => "a string"
  | .arr _ => "a list"
  | .obj _ => "an object"

/-- The member list of an object, or `none`. -/
def Json.members? : Json → Option (List (String × Json))
  | .obj kvs => some kvs
  | _ => none

/-! ## Rendering, for the runner's own `--json` output

The runner's verdict lines are flat objects: strings, integers, booleans,
`null` and lists of strings.  A flat encoder is total without recursion
over the nested `Json` type, and it is all the output needs. -/

/-- A flat output value. -/
inductive Flat where
  | null
  | bool (b : Bool)
  | nat (n : Nat)
  | str (s : String)
  | strs (xs : List String)

/-- A JSON string literal of a Lean string: `"`, `\` and control characters
escaped, everything else -- UTF-8 included -- written as it is, so a path
with a non-ASCII character reaches a JSON reader unchanged. -/
def quote (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '"' then "\\\""
    else if c == '\\' then "\\\\"
    else if c.toNat < 0x20 then s!"\\u00{hex2 (UInt8.ofNat c.toNat)}"
    else String.singleton c) ++ "\""

def Flat.render : Flat → String
  | .null => "null"
  | .bool true => "true"
  | .bool false => "false"
  | .nat n => toString n
  | .str s => quote s
  | .strs xs => "[" ++ String.intercalate "," (xs.map quote) ++ "]"

/-- One flat object, members in the order given. -/
def renderObject (kvs : List (String × Flat)) : String :=
  "{" ++ String.intercalate "," (kvs.map fun (k, v) => quote k ++ ":" ++ v.render) ++ "}"

end LpsRunner.Json
