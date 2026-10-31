/-! # LpsRunner.Declines — the header lines a declared decline rests on

Test tooling: nothing under `LpsRunner/` is part of the trusted
specification, and no proof depends on it.

An `unmodeled` verdict has three possible sources, and the runner names
which (`LpsRunner.Replay.ArmStatus`): an arm in `checked_table` declined
the call's shape; `spec_table` carries the number but `checked_table` does
not yet, so the checker declines a call the spec answers (the fail-closed
answer while the port is under way, `Checks/Sys/TableGuards.lean`'s header); or
neither table carries the number.  The last two are DECLARED declines in
the sense of `docs/lean-port/BRIEF.md` section 3: a Rocq definition left
out of a twin is registered as an `unported: <name> -- <reason>` line in
that twin's `rocq-baseline` header block, and where the reason names a
syscall it does so as `<name> (<number>)`.  Most reasons name no number
at all (the `open_append` and `open_rdwr` lines of `Sys/Fs/Open.lean` do
not), so `forNumber` is often empty and the verdict line then carries the arm status alone.
The checked table registers no arm one by one (`Checks/Sys/TableGuards.lean`,
whose header says why; the table itself is generated), so a checker not
yet ported rests on that header block itself.

This module reads those registers, so that a verdict line can cite the
header line the decline rests on rather than only its number.  The `--lean-src` option supplies the Lean source root.
The reader walks every `.lean` file under that root.
It finds a module-doc comment that opens with the baseline tag and a commit sha.
The `headerTag` value joins the word `rocq-baseline` and a colon.
The reader indexes unported and partial markers until the comment closes.
This text reader supplies citations for the grammar that `tools/check_lean_spec_parity.py` enforces.
It requires the opener and tag on one line.
It requires the literal ` -- ` separator and reads the first matching block.
The parity checker also permits a newline after the opener and other whitespace around `--`.
That checker requires forty hex digits in the sha.
A header that this reader misses loses its citation.
That omission cannot change a verdict.

The reader ignores partial markers outside the baseline header.
A partial marker never registers an unported checker arm.
A drift-ticket can name the same definition.
This reader does not load the lean-declines JSON register.
Header citations forgive no occurrence.

WHAT IS NOT READ.  A decline can be declared in three other places this
reader does not open: the decline registers `tools/check_decline_registers.py`
compares against the table (a statement such as `Checks/Cases/Kernel/Exit.lean`'s
`sysno_95_is_unmodeled`), a header reason that names the number without
the `(n)` spelling, and the generated table's own `declined` comments.  The reader cites an absent number only when a marker spells its number.
The reader also needs a numbered reason to cite a checked arm's decline.
The output states when no such citation exists.  Every uncited
`absent` verdict the corpus records AGREES with the recorded one.
A registration can change that, so no count is written here:
how many of each, over the whole corpus under `--continue` and in the
prefix a default run reaches, is counted in `tools/lps_runner_totals.json`,
which the close writes (`tools/lps_runner_totals.py` says why a figure
every registration moves is kept there and not here), and that file is
what to read when a registration changes them.  The `absent` example
is a fail-closed probe of a number the
Rocq model never carried either -- `creds_unmodeled`'s getppid (173) is
one -- which records `unmodeled`, the Lean answer is the same,
the runner exits 0 on that one-record trace, and the explanation is
printed all the same (`Main.lean` prints it for every unmodeled verdict
of a HUMAN run; a `--json` run prints no explanation at all, and carries
the same two facts as the `arm` field and an empty `declared`); the
checked shape is every decline of `checked_table`'s arms.  Which arms
those are, and of each decline its trace, whether it agrees and what it
cites, is one line of that file's `checked_declines`, not this sentence.
A checked decline arises in two ways.  One is a shape the Rocq arm
answers through a definition the twin registers as `unported:`, in
lines that do not spell `(n)`, and in the corpus such a
decline is always a disagreement with a record that answers.  The other
is a decline the checker itself makes with no header line behind it at
all.  In the corpus the record declines that call too and the line
agrees; past a run's first divergence, though, on the stale model
`LpsRunner/Replay.lean`'s header describes, such a decline can meet a
record that answers.  Each decline of either source is a line of its
own there rather than a reader's count, so a further decline of an arm
already registered, or one that disagrees, is a new line, which a set of
arm NAMES could not show.  Since #1304 ported its MAP_FIXED_NOREPLACE
shapes, mmap's declines are all of the second source.
That the uncited `absent` shape never disagrees
is why the test has to renumber a record to reach that pair.  What a port
moves is a number's
status, not this rule: socket (198) was such an uncited `absent` number
until `Sys/Net/Socket.lean` gave it a spec, and its line now rests on the
checked table's header block as `spec_only`.  The converse is as literal:
`forNumber` matches any unported or partial reason that spells `(n)`.
An absent number can therefore cite a sibling's line.  Every
checked decline's citation is one line of
`tools/lps_runner_totals.json`, compared exactly only where the mode is
strict: on a pull request into a day branch a moved citation is printed
and fails nothing, and the close is the reader who finds it, in the diff
its own write commits.  Two queries serve the verdict
line:

- `forNumber n`: the entries whose reason mentions `(n)`, the convention
  the twins use for a syscall number;
- `armRegister` selects only `unported:` entries whose last name component begins `arm_`.
  These entries register checker arms that remain unported.
  When that register is empty, `tableHeader` locates the TableGuards header for a spec without a checked arm.

Both are text, read at runtime, and the runner says so on the line: the
citation is a pointer into the tree for a reader, not a claim the checker
made.  With no `--lean-src` the runner still names the arm status; only
the header lines are absent. -/

namespace LpsRunner.Declines

/-- One decline marker in a header block. -/
structure Decline where
  file : String
  line : Nat
  name : String
  reason : String
  kind : String := "unported"

def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r'

def dropWs : List Char → List Char
  | c :: rest => if isWs c then dropWs rest else c :: rest
  | [] => []

/-- Both ends trimmed of spaces, tabs and carriage returns. -/
def trim (s : String) : String :=
  String.ofList (dropWs (dropWs s.toList).reverse).reverse

/-- Whether `pat` occurs in `hay` (`pat` non-empty). -/
def contains (hay pat : String) : Bool := (hay.splitOn pat).length > 1

/-- The module-doc comment opener a header block starts with, the tag that
follows it, and the comment delimiter that closes it; each spelled in two
pieces so that this file's own comments and code can name them.  For the
tag that is load-bearing, not cosmetic: `tools/check_lean_test_monotonic.py`
applies the parity header reader (`tools/check_lean_spec_parity.py`,
`parse_header`) to every `.lean` file under `lean/` a PR changes -- at the
head for a file the PR leaves behind, and at the merge base for one it did
not create -- and that reader refuses any file carrying the tag, with its
colon, anywhere in the file, without a block it can parse, since a claim
it cannot read must not pass as no claim.  A literal here therefore reddens that guard on
the next PR that touches the file (PR #1201's lps-runner fix did, on
`local/lean-test-monotonic`).  `Tests.lean`'s fixtures still spell the
tag beside a sha, which the guard reads as a claim-shaped block it cannot
parse at any merge base that carries it, and that refusal no head can
cure; the entry is
bugs/lps-runner-tests-fixtures-are-a-header-block-the-guard-cannot-read.md.
`tools/test_lps_runner.py` holds this file and its other siblings
readable and pins `Tests.lean` as the one the reader refuses. -/
def openDelim : String := "/" ++ "-!"
def headerTag : String := "rocq-" ++ "baseline:"
def closeDelim : String := "-" ++ "/"

/-- `s` without the block's closing delimiter, if it ends the block on this
line. -/
def stripClose (s : String) : String :=
  match (s.splitOn closeDelim) with
  | before :: _ => before
  | [] => s

/-- Read an unported or partial marker from a header line. -/
def entryOf (file : String) (lineNo : Nat) (raw : String) : Option Decline :=
  let l := trim (stripClose raw)
  let kind := if l.startsWith "partial:" then "partial" else "unported"
  let tag := kind ++ ":"
  if l.startsWith tag then
    let rest := trim (l.drop tag.length).toString
    match rest.splitOn " -- " with
    | name :: reasonParts =>
      if name.isEmpty || reasonParts.isEmpty then none
      else some { file, line := lineNo, name := trim name, kind,
                  reason := trim (String.intercalate " -- " reasonParts) }
    | [] => none
  else none

/-- Whether a line opens a header block. -/
def isOpener (l : String) : Bool :=
  let t := trim l
  t.startsWith openDelim && (trim (t.drop 3).toString).startsWith headerTag

/-- The lines of the header block: from the module-doc line opening with
the tag to the line carrying the closing delimiter, inclusive;
empty when the file has no block. -/
def headerLines (ls : List String) : List (String × Nat) :=
  let numbered := ls.zipIdx 1
  let opened := numbered.dropWhile fun (l, _) => !(isOpener l)
  match opened with
  | [] => []
  | first :: rest =>
    if contains first.1 closeDelim then [first]
    else
      let body := rest.takeWhile fun (l, _) => !(contains l closeDelim)
      let closing := (rest.drop body.length).take 1
      first :: body ++ closing


/-- Every decline marker in one file's header block. -/
def entriesOf (file : String) (text : String) : List Decline :=
  (headerLines (text.splitOn "\n")).filterMap fun (l, n) => entryOf file n l

/-- Where a file's header block opens, if it has one: `(file, line)`. -/
def blockOf (file : String) (text : String) : Option (String × Nat) :=
  match headerLines (text.splitOn "\n") with
  | (_, n) :: _ => some (file, n)
  | [] => none

/-- The register holds each decline marker and each header block in the source tree. -/
structure Index where
  entries : List Decline
  blocks : List (String × Nat)

def Index.empty : Index := ⟨[], []⟩

/-- The checked table's header, `Checks/Sys/TableGuards.lean` (the table is
generated from the arm files and carries none): what a number `spec_table`
carries and `checked_table` does not yet rests on, since the arms are not
registered one by one there (its header says why). -/
def Index.tableHeader (ix : Index) : Option (String × Nat) :=
  -- the project path, not a bare suffix, so that a Cases twin of the same
  -- name could not be taken for it
  ix.blocks.find? fun (f, _) => f.endsWith "LinuxProcessSem/Checks/Sys/TableGuards.lean"

def citeBlock (b : String × Nat) : String := s!"{b.1}:{b.2}: the header block"

/-- Entries whose reason names syscall number `n` as `(n)`. -/
def Index.forNumber (ix : Index) (n : Nat) : List Decline :=
  ix.entries.filter fun d => contains d.reason s!"({n})"

/-- The last dotted component of a name: the parity checker keys entries on
it, so `Checks.Sys.Table.arm_exit` and `arm_exit` are the same entry. -/
def lastComponent (name : String) : String :=
  match (name.splitOn ".").getLast? with
  | some c => c
  | none => name

/-- The checker-arm register: entries named `arm_…`. -/
def Index.armRegister (ix : Index) : List Decline :=
  ix.entries.filter fun d => d.kind == "unported" && (lastComponent d.name).startsWith "arm_"

/-- Cite the exact marker kind and source line. -/
def Decline.cite (d : Decline) : String :=
  s!"{d.file}:{d.line}: {d.kind}: {d.name} -- {d.reason}"

/-- Read every `.lean` under `root`. -/
def Index.load (root : System.FilePath) : IO Index := do
  let files ← root.walkDir
  let leanFiles := files.filter fun p => p.extension == some "lean"
  let sorted := leanFiles.qsort fun a b => a.toString < b.toString
  let mut entries : List Decline := []
  let mut blocks : List (String × Nat) := []
  for p in sorted do
    let text ← IO.FS.readFile p
    entries := entries ++ entriesOf p.toString text
    match blockOf p.toString text with
    | some b => blocks := blocks ++ [b]
    | none => pure ()
  pure ⟨entries, blocks⟩

end LpsRunner.Declines
