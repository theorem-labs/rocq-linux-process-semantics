#!/usr/bin/env python3
"""Generate the Lean checked table and its per-arm obligations from one arm file per checker twin.

Every `lean: verify <syscall>` PR used to edit the same three hand-written
files -- `Checks/Sys/Table.lean` (a block, a table line and an import),
`Checks/VmMapsDisjoint/Arms.lean` (a fact and an alternative) and
`Checks/Invariants.lean` (one fact and one alternative per registered
invariant) -- and, beside them, the pins in `Checks/Cases/Invariants.lean`
and the table-shape literal in `Checks/Cases/Checks/Sys/Mm/Mmap.lean`.
The lines each PR added sat next to the lines the previous one had added,
so every landing made every other open registration CONFLICTING: #1215
(brk, munmap) and #1234 (eventfd2) edited the same seven lean files and
five mutation patches over them on one day, and the second was rebased
onto the first to land.  `tools/gen_lean_registry.py` did this for the
spec side (T22, T31); this is the checker side (T80), and it reuses that
tool's reader of the registry files, its refusal type and its
source-shadowing and stale-product checks rather than restating them.

WHAT A REGISTRATION WRITES.  One file per CHECKER TWIN, shared only by the
arms one checker twin answers (exit and exit_group; brk, munmap and mmap):

    lean/LinuxProcessSemantics/LinuxProcessSem/Checks/Arms/<Mirror>.lean

for the checker twin `Checks/Sys/<Mirror>.lean`, importing that twin,
`Checks.InvariantRegistry`, `Sys.SyscallTable` and `SysSimp`, and holding,
for every arm `arm_<name>` it registers:

  in `namespace …Checks.Sys.Table`
    def arm_<name> : CheckedArm where
      ca_arm := SpecArm.mkSpecArm <number> …
    @[arm_unfold] theorem ca_check_arm_<name> …
    @[arm_unfold] theorem ca_witness_arm_<name> …
    @[arm_unfold] theorem sa_spec_arm_<name> …
    @[arm_unfold] theorem ca_no_arm_<name> : ca_no arm_<name> = <number> := rfl

  in `namespace …Checks.VmMapsDisjoint.Arms`
    theorem arm_<name>_preserves_vm : arm_preserves_vm arm_<name> := …

  in `namespace …Checks.Invariants`, once per entry `inv_<p>` of
  `Checks/InvariantRegistry.lean`'s `invariant_registry`
    theorem <p>_arm_<name> : arm_preserves inv_<p> arm_<name> := …

The namespaces are the ones the declarations had in the three hand-written
files, so no full name moved and nothing that names one changed.  Anything
else may stand in the file (docstrings, helper lemmas the facts are built
from); what this reads is the declarations above.

WHAT THIS WRITES.  Four modules, NONE COMMITTED: `lean/lakefile.lean`'s
`generatedInput` facet runs this tool once per module on every build and
writes each under `lean/.lake/generated/`, which is gitignored, and
`.gitignore` names each at its source path too, to catch a by-hand run that
put one back.

  `Checks.Sys.Table` -- `checked_table`, every arm in number order (which
  is `spec_table`'s order: `gen_lean_registry.rocq_arms` refuses an
  unsorted Rocq table), a simp lookup theorem for each arm, a miss theorem
  taking one number inequality per arm, and the two guard theorems over it, whose
  predicates and prose are `Checks/Sys/TableGuards.lean`'s.
  `Checks.VmMapsDisjoint.Arms` -- `checked_table_preserves_vm`, one
  `| with_reducible exact arm_<name>_preserves_vm` per arm above the closing `| skip`,
  then `vm_arm_uncovered`; and `lookup_ca_preserves_vm_wf`.
  `Checks.InvariantCoverage` -- `registry_preserves`, one
  `| with_reducible exact <p>_arm_<name>` per (entry, arm) pair in registry order and then
  table order, then `inv_arm_uncovered`.  `Checks/Invariants.lean` states
  the dispatcher corollaries on top of it.
  `Checks.Cases.CheckedTable` -- the pins: the table's numbers as a literal
  (the one `Checks/Cases/Checks/Sys/Mm/Mmap.lean` used to restate at every
  registration), `lookups_agree_at` at each arm's number, and a
  `#guard_msgs` of each fact's elaborated type, so a fact restated under its
  name with a type the alternative cannot `exact` fails at elaboration as
  well as here.  The umbrella `LinuxProcessSemantics.lean` imports it, so
  the audit reaches it.

WHY EACH ALTERNATIVE IS `with_reducible exact`.  `first` tries every
earlier alternative on every goal.  At default transparency a failing
`exact` unfolds `arm_preserves` and both arms' `ca_check` bodies before it
fails, and with 22 arms that made `registry_preserves` cost 43.5 s, past
the default heartbeat limit; under `with_reducible` the arm constants are
not unfolded, so a wrong alternative fails at once and the 66 goals close
in 0.42 s.  The same rule means a goal is closed by its own pair's fact
alone: `arm_exit_group` and `arm_exit` share `check_exit`, and a plain
`exact` let the `arm_exit` alternative close `arm_exit_group`'s goal
(testing/lean-mutations/invariants-drop-shared-checker-arm pins that it no
longer does).  The fallbacks after the alternations stay for a fact that
is present and does not elaborate at the type its header states (which
`Checks.Cases.CheckedTable`'s `#guard_msgs` catches first).

RULES, each a refusal naming the file:

  ARM-1  an arm file's checker twin `Checks/Sys/<Mirror>.lean` exists, and
         the file imports it, `Checks.InvariantRegistry`, `Sys.SyscallTable`
         and `SysSimp`;
  ARM-2  a definition of type `CheckedArm` or named `arm_<...>`, or a
         theorem whose name carries `arm_`, in any other spelling (a modifier, an
         attribute, a `set_option`/`open ... in` prefix, indentation, a
         qualified type, `:=`) is refused, so no arm is read past; every
         `def arm_<name> : CheckedArm where` stands at column 0 in
         `namespace …Checks.Sys.Table`, its next line is
         `ca_arm := SpecArm.mkSpecArm <number> …`, and its four `arm_unfold`
         lemmas stand in the same namespace, each written
         `@[arm_unfold] theorem <lemma>_arm_<name>`, the number lemma
         stating the number `ca_arm` builds;
  ARM-3  every arm has `theorem arm_<name>_preserves_vm : arm_preserves_vm
         arm_<name> :=` in `namespace …Checks.VmMapsDisjoint.Arms`, header
         text for text up to whitespace, no binders;
  ARM-4  every arm has, for every registry entry `inv_<p>`,
         `theorem <p>_arm_<name> : arm_preserves inv_<p> arm_<name> :=` in
         `namespace …Checks.Invariants`, likewise;
  ARM-5  an arm name and a number are each one arm's across every file, and
         the number is one some file under `Sys/Registry/` registers
         (`gen_lean_registry.registry_arms`, the one reader of them); an
         entry is listed once in `invariant_registry`;
  ARM-6  a fact shaped like ARM-3's or ARM-4's, or an `arm_unfold` lemma,
         for an arm its file does not define is refused: it is a
         registration half-written or half-moved, and nothing would render
         it;
  ARM-7  no arm file registers nothing, and the registry's list and the
         arm files are each read non-empty: a reader that read nothing
         would render a table that declines everything as a tree with
         nothing wrong.

LIMITS.  Nothing here elaborates Lean.  A `CheckedArm` whose `ca_arm` is not
`spec_table`'s arm for its number is the build's to refuse
(`checked_table_arms`); a fact whose header ARM-3/ARM-4 accept but whose
proof is wrong is the build's; a `sorry` is the policy audit's.  The
declarations are read at column 0 with comments and strings blanked, in the
namespace the `namespace`/`end` lines around them open, and a declaration
this reader does not see is a fact it reports missing -- the failure is a
refusal, never a pass.  `#guard_msgs` compares text: the one-line and the
wrapped rendering of `#check` differ at Lean's format width (120), and the
render follows that rule; a toolchain that changes the width fails the pins
loudly and is a prompt to reread `guard_msg` here, not to loosen them.

    python3 tools/gen_lean_checked.py --check [ROOT]
    python3 tools/gen_lean_checked.py --print MODULE [ROOT]
    python3 tools/gen_lean_checked.py --out-dir DIR --module NAME [ROOT]
"""
import argparse
import collections
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_lean_pins import blank_comments_and_strings  # noqa: E402
import gen_lean_registry as registry  # noqa: E402
from gen_lean_registry import Refusal, read  # noqa: E402

LEAN_TREE = registry.LEAN_TREE
MODULE = registry.MODULE
ARMS_DIR = LEAN_TREE + "/Checks/Arms"
ARMS_MODULE = MODULE + ".Checks.Arms"
CHECKS_SYS = LEAN_TREE + "/Checks/Sys"
INVARIANT_REGISTRY = LEAN_TREE + "/Checks/InvariantRegistry.lean"
TABLE_NS = MODULE + ".Checks.Sys.Table"
ARMS_NS = MODULE + ".Checks.VmMapsDisjoint.Arms"
INV_NS = MODULE + ".Checks.Invariants"
CASES_NS = MODULE + ".Checks.Cases.CheckedTable"
# Module name -> the source path that module would have had.  The lakefile
# declares exactly these as the roots of its `CheckedTable` library, and
# `--module` takes one of them.  The first two are hand-written files this
# replaced, at their old paths; the third carries what was the alternation
# half of the still hand-written `Checks/Invariants.lean`, and the fourth is
# new.  Prose names them by these paths, and tools/check_citations.py's
# ALLOWED_MISSING carries each one no tracked path already ends with.
GENERATED = {
    TABLE_NS: LEAN_TREE + "/Checks/Sys/Table.lean",
    ARMS_NS: LEAN_TREE + "/Checks/VmMapsDisjoint/Arms.lean",
    MODULE + ".Checks.InvariantCoverage": LEAN_TREE + "/Checks/InvariantCoverage.lean",
    CASES_NS: LEAN_TREE + "/Checks/Cases/CheckedTable.lean",
}
CHECK_HINT = "python3 tools/gen_lean_checked.py --check ."
# What every arm file imports; ARM-1.  The twin's own import is added per file.
REQUIRED_IMPORTS = (
    MODULE + ".Checks.InvariantRegistry",
    MODULE + ".Sys.SyscallTable",
    MODULE + ".SysSimp",
)
UNFOLD_LEMMAS = ("ca_check", "ca_witness", "sa_spec", "ca_no")
# Lean's `format.width`: a `#check` message longer than this is wrapped
# after ` :`, and `#guard_msgs` compares the text it printed.
FORMAT_WIDTH = 120

ARM_DEF = re.compile(r"^def arm_([a-z0-9_]+) : CheckedArm where\s*$")
# What ARM_DEF, UNFOLD and THEOREM do not take is read once more by
# stray_arm_decl: any definition named `arm_<...>` or of result type
# `CheckedArm`, and any theorem whose name carries `arm_`, however spelled --
# modifiers, attributes, `set_option ... in`, `open ... in`, indentation,
# binders, a qualified type, the `:=` form.  Such a line is an arm, an unfold
# lemma or a fact the reader would otherwise skip in silence: when an arm's
# definition, lemmas and facts are all spelled so, the arm drops out of every
# render together and its number is declined (the deep review of #1255 found
# `set_option maxHeartbeats 400000 in` on each `arm_exit_group` declaration
# dropping 94 with no refusal).  It is refused (ARM-2) rather than left out.
# A keyword alone on its line, its name on the next (valid Lean), is refused
# too, and a data declaration whose signature continues past its name is
# read on through the lines that follow until `:=` or `where` (the third deep
# review of #1255 found `def` / `arm_ghost : CheckedArm where` on two lines
# dropping the arm with no refusal).  What is still not seen: a prefix on a
# line of its own before a prefixed declaration.  A miss fails closed (the number
# is declined, never answered wrongly); what turns it red is a hand-written
# pin naming the arm, such as a `lookup_ca checked_table … = some arm_<name>`.
#
# A declaration's prefixes, stripped one at a time: attributes, `set_option
# ... in`, `open ... in`, and the modifiers.  What is left starts with the
# declaration keyword, and is read by DECL.
DECL_PREFIX = re.compile(r"(?:@\[[^\]]*\]|set_option\s+\S+\s+\S+\s+in\b"
                         r"|open\b(?:(?!\bin\b).)*\bin\b"
                         r"|(?:private|protected|noncomputable|partial|unsafe|nonrec)\b)\s*")
DECL = re.compile(r"(def|abbrev|instance|opaque|axiom|theorem|lemma)\b\s*([^\s:({\[]*)(.*)$")
DATA_KEYWORDS = ("def", "abbrev", "instance", "opaque", "axiom")
# The result type `CheckedArm`, qualified or parenthesized, ending the
# signature: not a function over arms (`CheckedArm → Nat`, `(c : CheckedArm)`).
ARM_TYPE = re.compile(r":\s*\(*\s*(?:[\w.]+\.)?CheckedArm\s*\)*\s*(?:where\b|:=|$)")


def stray_arm_decl(line, following=()):
    """What a line the canonical readers (ARM_DEF, UNFOLD, THEOREM) did not
    take declares, when it would register something, else None: a data
    declaration named `arm_<...>` or of result type `CheckedArm`, or a
    theorem whose name carries `arm_` (an unfold lemma or a fact), however
    prefixed or indented.  `following` is the lines after it, read when the
    declaration's signature continues past the line.  ARM-2 refuses it
    rather than leave it unread; the comment above says what it still does
    not see."""
    pos = len(line) - len(line.lstrip())
    while True:
        m = DECL_PREFIX.match(line, pos)
        if not m or m.end() == pos:
            break
        pos = m.end()
    d = DECL.match(line, pos)
    if not d:
        return None
    kw, name, rest = d.groups()
    if not name and not rest.strip():
        return "puts its name on a later line"
    if kw in DATA_KEYWORDS and not rest.strip():
        for more in following:
            rest += " " + more.strip()
            if ":=" in more or re.search(r"\bwhere\b", more):
                break
    if kw in DATA_KEYWORDS:
        if name.startswith("arm_") or ARM_TYPE.search(rest):
            return "defines a `CheckedArm`"
        return None
    return "states an `arm_unfold` lemma or a fact" if "arm_" in name else None


CA_ARM = re.compile(r"^\s+ca_arm := SpecArm\.mkSpecArm (\d+)\b")
UNFOLD = re.compile(r"^@\[arm_unfold\] theorem (" + "|".join(UNFOLD_LEMMAS) + r")_arm_([a-z0-9_]+)\b")
THEOREM = re.compile(r"^theorem ([A-Za-z_][A-Za-z0-9_']*)")
VM_FACT = re.compile(r"^arm_([a-z0-9_]+)_preserves_vm$")
LIST_ENTRY = re.compile(r"^\s+(inv_[A-Za-z0-9_]+) ::\s*$")

ArmDecl = collections.namedtuple("ArmDecl", "rel line name number mirror")


def arm_files(root):
    """Repository-relative paths of every arm file, sorted (the registry
    lister's rule for what is a source file and what is a sidecar)."""
    base = os.path.join(root, ARMS_DIR)
    out = []
    if os.path.isdir(base):
        for dirpath, _, names in os.walk(base):
            for name in names:
                if registry.is_registry_source(name):
                    full = os.path.join(dirpath, name)
                    out.append(os.path.relpath(full, root).replace(os.sep, "/"))
    return sorted(out)


def mirror_of(rel):
    return rel[len(ARMS_DIR) + 1:-len(".lean")]


def module_of(rel):
    return ARMS_MODULE + "." + mirror_of(rel).replace("/", ".")


def invariants(root):
    """The entries of `invariant_registry`, in order: `["inv_vm_wf", …]`."""
    if not os.path.exists(os.path.join(root, INVARIANT_REGISTRY)):
        raise Refusal(f"{INVARIANT_REGISTRY}: no such file; the registry is what "
                      "every arm owes one fact per entry of")
    lines = blank_comments_and_strings(read(root, INVARIANT_REGISTRY)).splitlines()
    try:
        start = lines.index("def invariant_registry : List Invariant :=")
    except ValueError:
        raise Refusal(f"{INVARIANT_REGISTRY}: no `def invariant_registry : List Invariant :=` "
                      "line at column 0; the list is read one `  inv_<p> ::` line at a time")
    out = []
    for line in lines[start + 1:]:
        m = LIST_ENTRY.match(line)
        if m:
            if m.group(1) in out:
                # a repeat renders every alternative and pin of that entry
                # twice and counts it twice; ARM-5's "one each" for the list
                raise Refusal(f"{INVARIANT_REGISTRY}: `{m.group(1)}` is listed twice in "
                              "`invariant_registry`; ARM-5")
            out.append(m.group(1))
            continue
        if line.strip() == "[]":
            break
        raise Refusal(f"{INVARIANT_REGISTRY}: `{line.strip()}` in `invariant_registry` is "
                      "neither `  inv_<p> ::` nor the closing `  []`")
    else:
        raise Refusal(f"{INVARIANT_REGISTRY}: `invariant_registry` has no closing `  []`")
    if not out:
        raise Refusal(f"{INVARIANT_REGISTRY}: `invariant_registry` is empty; ARM-7")
    return out


def header(lines, i):
    """A declaration's header, from line `i` to its first `:=`, whitespace
    collapsed, or None when no `:=` is found before the next column-0 line."""
    parts = []
    for j in range(i, len(lines)):
        if j > i and lines[j][:1] not in ("", " "):
            return None
        line = lines[j]
        if ":=" in line:
            parts.append(line.split(":=", 1)[0])
            return " ".join(" ".join(parts).split())
        parts.append(line)
    return None


def read_arm_file(root, rel, entries):
    """`[ArmDecl]` for one arm file, or a Refusal naming what is missing."""
    mirror = mirror_of(rel)
    twin = f"{CHECKS_SYS}/{mirror}.lean"
    if not os.path.exists(os.path.join(root, twin)):
        raise Refusal(f"{rel}: ARM-1: no checker twin {twin}; an arm file is named for the "
                      "checker twin whose checker its arms dispatch to")
    text = read(root, rel)
    # imports read from the blanked text: an `import` inside a block comment
    # imports nothing, and ARM-1 is about what the file imports
    blanked = blank_comments_and_strings(text)
    imports = set(re.findall(r"^import\s+(\S+)\s*$", blanked, re.M))
    want = set(REQUIRED_IMPORTS) | {MODULE + ".Checks.Sys." + mirror.replace("/", ".")}
    missing = sorted(want - imports)
    if missing:
        raise Refusal(f"{rel}: ARM-1: does not import {', '.join(missing)}")
    lines = blanked.splitlines()
    stack = []
    arms, unfold, theorems = [], collections.defaultdict(dict), {}
    for i, line in enumerate(lines):
        m = re.match(r"^namespace\s+(\S+)\s*$", line)
        if m:
            stack.append(m.group(1))
            continue
        m = re.match(r"^end\s+(\S+)\s*$", line)
        if m:
            if not stack or stack[-1] != m.group(1):
                raise Refusal(f"{rel}:{i + 1}: `end {m.group(1)}` closes no open namespace of that name")
            stack.pop()
            continue
        ns = stack[-1] if stack else None
        m = ARM_DEF.match(line)
        if m:
            name = m.group(1)
            if ns != TABLE_NS:
                raise Refusal(f"{rel}:{i + 1}: ARM-2: arm_{name} is declared outside "
                              f"`namespace {TABLE_NS}`")
            n = CA_ARM.match(lines[i + 1]) if i + 1 < len(lines) else None
            if not n:
                raise Refusal(f"{rel}:{i + 1}: ARM-2: arm_{name}'s first field is not "
                              "`ca_arm := SpecArm.mkSpecArm <number> …`")
            arms.append(ArmDecl(rel, i + 1, name, int(n.group(1)), mirror))
            continue
        m = UNFOLD.match(line)
        if m:
            if ns != TABLE_NS:
                raise Refusal(f"{rel}:{i + 1}: ARM-2: {m.group(1)}_arm_{m.group(2)} is declared "
                              f"outside `namespace {TABLE_NS}`")
            unfold[m.group(2)][m.group(1)] = (i, header(lines, i))
            continue
        m = THEOREM.match(line)
        if m:
            theorems[m.group(1)] = (ns, i, header(lines, i))
            continue
        what = stray_arm_decl(line, lines[i + 1:i + 6])
        if what:
            raise Refusal(f"{rel}:{i + 1}: ARM-2: `{line.strip()}` {what} in a shape this "
                          "reader does not read (a modifier, an attribute, a `... in` "
                          "prefix, indentation, a split line); write it in the shape ARM-2 names at "
                          "column 0, or it would be left out of the render in silence")
    if stack:
        raise Refusal(f"{rel}: `namespace {stack[-1]}` is never closed")
    if not arms:
        raise Refusal(f"{rel}: ARM-7: registers no arm (no `def arm_<name> : CheckedArm where` "
                      "at column 0); delete the file or give it its arm")
    names = {a.name for a in arms}
    for name, got in unfold.items():
        if name not in names:
            lemma = sorted(got)[0]
            raise Refusal(f"{rel}:{got[lemma][0] + 1}: ARM-6: {lemma}_arm_{name} is an "
                          f"`arm_unfold` lemma for arm_{name}, which this file does not define; "
                          "nothing renders it")
    prefixes = [e[len("inv_"):] for e in entries]
    for a in arms:
        got = unfold.get(a.name, {})
        for lemma in UNFOLD_LEMMAS:
            if lemma not in got:
                raise Refusal(f"{rel}: ARM-2: arm_{a.name} has no `@[arm_unfold] theorem "
                              f"{lemma}_arm_{a.name}`; without it `simp only [arm_unfold]` "
                              "leaves the arm folded and every fact over it is stuck")
        no = got["ca_no"][1]
        want_no = f"@[arm_unfold] theorem ca_no_arm_{a.name} : ca_no arm_{a.name} = {a.number}"
        if no != want_no:
            raise Refusal(f"{rel}:{got['ca_no'][0] + 1}: ARM-2: `{no}` is not `{want_no} := rfl`")
        owed = [(ARMS_NS, f"arm_{a.name}_preserves_vm", f"arm_preserves_vm arm_{a.name}", "ARM-3")]
        owed += [(INV_NS, f"{p}_arm_{a.name}", f"arm_preserves inv_{p} arm_{a.name}", "ARM-4")
                 for p in prefixes]
        for ns, thm, typ, rule in owed:
            want_h = f"theorem {thm} : {typ}"
            got_t = theorems.get(thm)
            if got_t is None:
                raise Refusal(f"{rel}: {rule}: arm_{a.name} owes `{want_h} :=` in "
                              f"`namespace {ns}`, and the file does not state it")
            if got_t[0] != ns:
                raise Refusal(f"{rel}:{got_t[1] + 1}: {rule}: {thm} is declared in "
                              f"`namespace {got_t[0]}`, not `{ns}`, so the alternation "
                              "that names it would not resolve it")
            if got_t[2] != want_h:
                raise Refusal(f"{rel}:{got_t[1] + 1}: {rule}: `{got_t[2]}` is not `{want_h}`; a "
                              "fact of another type, or one taking binders, under the pair's "
                              "name is an alternative `first` skips in silence")
    for thm, (ns, i, _) in theorems.items():
        m = VM_FACT.match(thm)
        stray = m.group(1) if m else None
        for p in prefixes:
            if stray is None and thm.startswith(p + "_arm_"):
                stray = thm[len(p) + len("_arm_"):]
        if stray is not None and stray not in names:
            raise Refusal(f"{rel}:{i + 1}: ARM-6: {thm} is a fact for arm_{stray}, which this "
                          "file does not define; nothing renders it")
    return arms


def checked(root):
    """(arms in number order, registry entries), every rule above applied."""
    entries = invariants(root)
    files = arm_files(root)
    if not files:
        raise Refusal(f"{ARMS_DIR}: no arm file; ARM-7")
    arms = []
    for rel in files:
        arms.extend(read_arm_file(root, rel, entries))
    registered = registry.registry_arms(root)
    by_name, by_number = {}, {}
    for a in arms:
        for seen, key, what in ((by_name, a.name, "arm name"), (by_number, a.number, "number")):
            if key in seen:
                raise Refusal(f"{a.rel}:{a.line}: ARM-5: {what} {key} is registered here and at "
                              f"{seen[key].rel}:{seen[key].line}")
            seen[key] = a
        if a.number not in registered:
            raise Refusal(f"{a.rel}:{a.line}: ARM-5: arm_{a.name} checks number {a.number}, "
                          f"which no file under {registry.REGISTRY_DIR} registers; "
                          "`spec_table` does not carry it")
    return sorted(arms, key=lambda a: a.number), entries


# ---------------------------------------------------------------- renders
NOTE = """GENERATED by `tools/gen_lean_checked.py` from the arm files under
`Checks/Arms/`, into `lean/.lake/generated/` on every build
(`lean/lakefile.lean`'s `generatedInput` facet); NOT A SOURCE FILE.  It is
not committed and never edited: a registration writes its arm's file, and a
copy of this module in the source tree is refused by `--check` in the
`generated-docs` job and by `tools/check_lean_policy.py` after a build."""


def opens(*names):
    return "\n".join(f"open {n}" for n in names)


def render_table(arms, entries):
    imports = "".join(f"import {m}\n" for m in sorted({module_of(a.rel) for a in arms}))
    rows = "".join(f"  arm_{a.name} ::\n" for a in arms)
    # Each refine consumes just one row; neither defeq nor simp traverses
    # the tail.  One simp over the whole table still grows recursion depth.
    lookups = []
    for i, a in enumerate(arms):
        steps = "".join(
            f"  refine lookup_ca_cons_of_ne (by rw [ca_no_arm_{b.name}]; decide) ?_\n"
            for b in arms[:i])
        lookups.append(f"""/-- The table's own contents at {a.number}: the lookup finds `arm_{a.name}`. -/
@[simp] theorem lookup_ca_checked_table_{a.name} :
    lookup_ca checked_table {a.number} = some arm_{a.name} := by
  unfold checked_table
{steps}  exact lookup_ca_cons_self ca_no_arm_{a.name}

""")
    absent_hyps = "".join(f"    (h_{a.name} : {a.number} ≠ n)\n" for a in arms)
    absent_steps = "".join(
        f"  refine lookup_ca_cons_of_ne (by rw [ca_no_arm_{a.name}]; exact h_{a.name}) ?_\n"
        for a in arms)
    return f"""import {MODULE}.Checks.Sys.TableGuards
{imports}
/-! # LinuxProcessSem.Checks.Sys.Table — the checked surface

{NOTE}

`checked_table` in syscall-number order, which is `spec_table`'s, its
per-arm lookup facts, and the two guards `Checks/Sys/TableGuards.lean`
defines and argues, applied to it.
Rocq: `Checks/Sys/Dispatch.v`'s `checked_table`. -/

namespace {TABLE_NS}

{opens(MODULE + ".State", MODULE + ".Monad", MODULE + ".Sys.Dispatch", MODULE + ".Sys.SyscallTable",
       MODULE + ".Checks.Sys.Prelude", MODULE + ".Checks.Sys.Dispatch")}

/-- The checked surface, in syscall-number order, one arm file's arm per
line.  Rocq: `Dispatch.checked_table`. -/
def checked_table : List CheckedArm :=
{rows}  []

/-- The half of Rocq's `checked_table_arms` that holds while the port is
partial; `Checks/Sys/TableGuards.lean` says what the other half waits on.
The list is walked arm by arm, and each arm's case is `rfl` — the arm's
`ca_arm` IS the term `spec_table` lists, so the lookup computes to it.  An
arm that is not that term stops the walk at its own case, which names it. -/
theorem checked_table_arms : arms_agree checked_table := by
  unfold arms_agree checked_table
  repeat' first
    | exact List.forall_mem_nil _
    | refine List.forall_mem_cons.mpr ⟨?_, ?_⟩
    | rfl

/-- The order guard on the real table: an arm whose number `spec_table`
does not carry, two arms in the wrong order, and a number twice.  `decide`
rather than `rfl`: a failure names the proposition it refuted, where `rfl`
reports only that two constants differ; the lists that print are the
literal ones in the refutations of `Checks/Cases/Checks/Sys/Table.lean`. -/
theorem checked_table_follows_spec_table : numbers_follow checked_table := by
  decide

{''.join(lookups)}\
/-- The table's own contents exclude a number unequal to every row's.
Separate premises let callers discharge each literal inequality with
`apply lookup_ca_checked_table_none <;> decide`, without a list walk. -/
theorem lookup_ca_checked_table_none (n : Int)
{absent_hyps}    : lookup_ca checked_table n = none := by
  unfold checked_table
{absent_steps}  rfl

end {TABLE_NS}
"""


def render_arms(arms, entries):
    alts = "".join(f"    | with_reducible exact arm_{a.name}_preserves_vm\n" for a in arms)
    return f"""import {MODULE}.Checks.Sys.Table

/-! # LinuxProcessSem.Checks.VmMapsDisjoint.Arms — every arm preserves the ledger

{NOTE}

The second part of the `theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`
twin: `checked_table_preserves_vm`, the alternation with one alternative
per arm of `checked_table`, each naming the `arm_<name>_preserves_vm` its
arm file states, and the dispatcher-level corollary.
`Checks/VmMapsDisjoint.lean` holds the invariant, the lemmas and the
tactics; `tools/gen_lean_checked.py`'s docstring says why the alternation
is still one. -/

namespace {ARMS_NS}

{opens("LinuxProcessSemantics.Riscv.Prelude", MODULE + ".State", MODULE + ".Checks.Sys.Prelude",
       MODULE + ".Checks.Sys.Dispatch", TABLE_NS, MODULE + ".Checks.VmMapsDisjoint")}

/-- Every arm of the checked surface preserves the ledger invariant.
Rocq: `VmMapsDisjoint.checked_table_preserves_vm`.  One alternative per
arm, in `checked_table`'s order, closed by `skip`, and the fallback as the
step after it. -/
theorem checked_table_preserves_vm : ∀ c ∈ checked_table, arm_preserves_vm c := by
  vm_arms_split checked_table
  all_goals first
{alts}    | skip
  all_goals vm_arm_uncovered

/-- …and therefore so does the arm the dispatcher finds.  No syscall is
named here, and nothing in this proof grows when one is added.  This is
Rocq's `check_syscall_preserves_vm_wf` stated over the lookup
`check_syscall` is a `match` on; the theorem over `check_syscall` itself is
`Checks/Invariants.lean`'s `check_syscall_preserves`. -/
theorem lookup_ca_preserves_vm_wf (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (c : CheckedArm)
    (hlk : lookup_ca checked_table (bv_unsigned i.in_sysno) = some c)
    (h : c.ca_check i eff m = CheckOk m' evs) (hwf : vm_wf (m_vmmaps m)) :
    vm_wf (m_vmmaps m') :=
  checked_table_preserves_vm c (lookup_ca_In checked_table _ c hlk) i eff m m' evs h hwf

end {ARMS_NS}
"""


def render_coverage(arms, entries):
    alts = "".join(f"    | with_reducible exact {e[len('inv_'):]}_arm_{a.name}\n" for e in entries for a in arms)
    return f"""import {MODULE}.Checks.Sys.Table

/-! # LinuxProcessSem.Checks.InvariantCoverage — every registered invariant, every arm

{NOTE}

`registry_preserves`: one alternative per (invariant, arm) pair, registry
order and then table order, each naming the `<invariant>_arm_<name>` its
arm file states; the split and the fallback are
`Checks/InvariantRegistry.lean`'s, and `Checks/Invariants.lean` states the
dispatcher corollaries over this. -/

namespace {INV_NS}

{opens(TABLE_NS, MODULE + ".Checks.Sys.Dispatch")}

/-- EVERY REGISTERED INVARIANT IS PRESERVED BY EVERY REGISTERED ARM. -/
theorem registry_preserves :
    ∀ inv ∈ invariant_registry, ∀ c ∈ checked_table, arm_preserves inv c := by
  inv_arms_split invariant_registry, checked_table
  all_goals first
{alts}    | skip
  all_goals inv_arm_uncovered

end {INV_NS}
"""


def guard_msg(full, typ):
    """The docstring `#guard_msgs` compares a `#check {full}` against."""
    msg = f"{full} : {typ}"
    if len(msg) <= FORMAT_WIDTH:
        return f"/-- info: {msg} -/\n"
    return f"/--\ninfo: {full} :\n  {typ}\n-/\n"


def render_pins(arms, entries):
    numbers = ", ".join(str(a.number) for a in arms)
    out = [f"""import {MODULE}.Checks.Invariants

/-! # Checks.Cases.CheckedTable — the checked table's per-arm pins

{NOTE}

Not part of the trusted specification.  Three kinds of pin, each a closed
computation or an elaboration over the model's own definitions and none a
kernel claim, rendered for every arm so that a registration adds none of
them by hand: the table's numbers, the premise
`Checks/Invariants.lean`'s `syscall_spec_preserves` takes at each arm's
number, and the elaborated type of every fact the two alternations name. -/

namespace {CASES_NS}

{opens(MODULE + ".Checks.Sys.Dispatch", TABLE_NS, MODULE + ".Checks.VmMapsDisjoint", INV_NS)}

/-- The table holds exactly the arm files' arms, in number order.
model: `checked_table`'s numbers against the arm files the generator read -/
theorem checked_table_numbers : checked_table.map ca_no = [{numbers}] := by decide

"""]
    for a in arms:
        out.append(f"""/-- `{a.name}` ({a.number}), `Checks/Arms/{a.mirror}.lean`'s arm: the premise
`syscall_spec_preserves` takes holds at its number, off the table itself.
model: `lookups_agree_at_of_found` at `arm_{a.name}` over `checked_table` -/
theorem lookups_agree_at_arm_{a.name} : Checks.ExecutableSpecs.lookups_agree_at {a.number} :=
  Checks.ExecutableSpecs.lookups_agree_at_of_found {a.number} arm_{a.name}
    lookup_ca_checked_table_{a.name}

""")
    for a in arms:
        out.append(guard_msg(f"{ARMS_NS}.arm_{a.name}_preserves_vm", f"arm_preserves_vm arm_{a.name}"))
        out.append(f"#guard_msgs in #check {ARMS_NS}.arm_{a.name}_preserves_vm\n")
    for e in entries:
        p = e[len("inv_"):]
        for a in arms:
            out.append(guard_msg(f"{INV_NS}.{p}_arm_{a.name}", f"arm_preserves {e} arm_{a.name}"))
            out.append(f"#guard_msgs in #check {p}_arm_{a.name}\n")
    out.append(f"\nend {CASES_NS}\n")
    return "".join(out)


RENDER = {
    TABLE_NS: render_table,
    ARMS_NS: render_arms,
    MODULE + ".Checks.InvariantCoverage": render_coverage,
    CASES_NS: render_pins,
}


def generate(root):
    """{source path: text} for every generated module, or a Refusal."""
    arms, entries = checked(root)
    return {GENERATED[mod]: render(arms, entries) for mod, render in RENDER.items()}


# ---------------------------------------------------------------- commands
def stale(root, want):
    """The build products that exist and differ from what the arm files now
    generate; `gen_lean_registry.stale`'s rule over this tool's modules."""
    out = []
    for mod, rel in sorted(GENERATED.items()):
        out_rel = registry.module_rel(mod)
        path = os.path.join(root, out_rel)
        if os.path.exists(path) and read(root, out_rel) != want[rel]:
            out.append(out_rel)
    return out


def check(root):
    """Refuse a tree that cannot generate, a source copy of a build product,
    and a build product that is stale or edited by hand."""
    want = generate(root)
    bad = []
    by_path = {rel: mod for mod, rel in GENERATED.items()}
    for rel in registry.shadowing(root, want):
        bad.append(f"{rel}: a source copy of a build product; `lean/lakefile.lean` writes "
                   f"{by_path[rel]} under {registry.GENERATED_DIR}/ on every build, so this "
                   "file is a second copy of one module. Delete it, and put what it held in "
                   "the arm's file under Checks/Arms/.")
    for out_rel in stale(root, want):
        bad.append(f"{out_rel}: stale or edited build product; it differs from what the arm "
                   "files now generate. A build rewrites it only when an input it is "
                   "traced on changed, and compiles a hand edit as edited, so delete it "
                   "and rebuild; nothing is committed either way.")
    if bad:
        for line in bad:
            print(line, file=sys.stderr)
        print(f"gen_lean_checked.py: {len(bad)} generated file(s) refused.  Run\n  {CHECK_HINT}\n"
              "again once each file above is gone or rebuilt; the generated files are never "
              "committed and never edited by hand.", file=sys.stderr)
        return 1
    arms, entries = checked(root)
    print(f"gen_lean_checked.py: {len(want)} generated files current "
          f"({len(arms)} arms over {len(arm_files(root))} arm files, "
          f"{len(entries)} invariants, {len(arms) * len(entries)} pairs)")
    return 0


def write_module(root, out_dir, module):
    """Write one generated module under `out_dir` at its module path; the
    registry tool's rules: everything computed first, rewritten only when
    the text changes, one module per run because the facet is per module."""
    if module not in GENERATED:
        raise Refusal(f"--module {module}: not a generated module ({', '.join(sorted(GENERATED))})")
    text = generate(root)[GENERATED[module]]
    path = os.path.join(out_dir, *module.split(".")) + ".lean"
    os.makedirs(os.path.dirname(path), exist_ok=True)
    current = read(os.path.dirname(path), os.path.basename(path)) if os.path.exists(path) else None
    if current != text:
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(text)
    print(f"gen_lean_checked.py: {module} "
          f"{'unchanged' if current == text else 'written'} at {path}")
    return 0


def build_parser():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--check", action="store_true",
                   help="fail on a source copy or a stale build product")
    g.add_argument("--print", metavar="MODULE", help="one generated module, to stdout")
    g.add_argument("--out-dir", help="write one module under this directory "
                                     "(the lakefile's facet; needs --module)")
    ap.add_argument("--module", help="which generated module --out-dir writes")
    ap.add_argument("root", nargs="?", default=".", help="repository root")
    return ap


def main(argv=None):
    ap = build_parser()
    args = ap.parse_args(argv)
    if args.out_dir is not None and not args.module:
        ap.error("--out-dir needs --module: the facet writes one module per run")
    if args.module and args.out_dir is None:
        ap.error("--module is only for --out-dir")
    try:
        if args.check:
            return check(args.root)
        if args.out_dir is not None:
            return write_module(args.root, args.out_dir, args.module)
        if args.print not in GENERATED:
            raise Refusal(f"--print {args.print}: not a generated module "
                          f"({', '.join(sorted(GENERATED))})")
        sys.stdout.write(generate(args.root)[GENERATED[args.print]])
        return 0
    except Refusal as e:
        print(f"gen_lean_checked.py: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
