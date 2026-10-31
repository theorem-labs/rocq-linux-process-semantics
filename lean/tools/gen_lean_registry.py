#!/usr/bin/env python3
"""Generate the Lean syscall table and its pins from one registry file per twin.

Every `lean: port <syscall>` PR used to edit the same three places: the arm
list in `lean/LinuxProcessSemantics/LinuxProcessSem/Sys/SyscallTable.lean`
(an `import`, an `open` and one arm line), and two import lines in the root
`lean/LinuxProcessSemantics.lean`.  So every landing made every other open
port CONFLICTING, and each then rebased, rebuilt and re-reviewed.  The
retrospective (docs/lean-port/RETRO.md, table R4) counted 45 rebases in one
evening on the base tickets' shared lines (State.lean, the umbrella
import); the table was the ports' copy of the same shape, and on
2026-09-16 the first two ports to land (#751, #781) conflicted every other
open port through it.
docs/merge-commutativity.md's invariant is that adding a thing creates files
and edits none, and this tool is how the table gets there.

WHAT A PORT WRITES.  One registry file per TWIN -- shared only by the
tickets that split one twin, which add one line each to it (the four S
tickets of Fs/ReadWrite.v all write Sys/Registry/Fs/ReadWrite.lean; a
rebase there keeps both sides) and never another twin's:

    lean/LinuxProcessSemantics/LinuxProcessSem/Sys/Registry/<Mirror>.lean

for the twin `Sys/<Mirror>.lean` it registers, holding one line per arm,

    def <name>_arm : SpecArm := SpecArm.mkSpecArm <number> (fun i => Sys.<Mirror>.<spec> …)

inside `namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Registry.<Mirror>`,
importing `Sys.Dispatch` and the twin and opening only what the table opens
(OPENS below).  The spec is named from `Sys` because the generated table
opens no twin -- one `open` line per twin was the second of the three
conflict points -- and a name that resolves in the registry's scope then
resolves in the table's.  Nothing else belongs in a registry file: every
non-blank line has to be one of the shapes this reads, or the file is
refused, so nothing can hide in a directory the parity checker skips.

WHAT THIS WRITES.  Two files, NEITHER COMMITTED: `lean/lakefile.lean`'s
`generatedInput` facet runs this tool on every build and writes both under
`lean/.lake/generated/`, which is gitignored, and `.gitignore` names them at
their old source paths too -- not because git would otherwise pick them up,
but to catch a by-hand run that put one back, the way the
`theories/Examples/*/Checker.v` pattern there does for dune's generated
checkers.  T22 gave every arm its own registry
file and left these two committed, which moved the conflict one level down
rather than away: measured on the 09-14 day branch on 2026-09-19, 20 commits
of the previous two days touched each of the two -- the same 20 `lean: port`
PRs -- while the busiest single fragment under `Sys/Registry/` took 2, and
105 of the 135 `origin/*` branches carrying `Sys/SyscallTable.lean` held a
blob different from the tip's while 24 of the 30 fragments differed on no
branch at all.

  `Sys/SyscallTable.lean`, `spec_table` with ONE LINE PER ARM OF THE ROCQ
  TABLE (`theories/LinuxProcessSem/Sys/SyscallTable.v`), in Rocq's order:
  a registered arm is its `def` body's `(fun i => …)` copied verbatim, after
  the number re-aligned to the column,

      /- <name>          -/ SpecArm.mkSpecArm <number> (fun i => …) ::

  and an unregistered Rocq arm is a comment holding the same position, so
  the table's shape is Rocq's whatever the registry holds.  The arm text is
  copied rather than referenced because the table is the trusted artifact
  and a reader of it must see the term the build compiles; that the copy
  elaborates to the registry's own constant is pinned by the second file's
  `rfl`s.  The imports are two static lines: `Sys.Dispatch` and
  `Sys.Registry.All`, a module `lean/lakefile.lean` writes under
  `.lake/generated` from the modules under `Sys/Registry/` on every build,
  so a port edits no import list.

  `Checks/Cases/SyscallTable.lean`, one theorem per Rocq arm in the same
  order: `lookup_arm spec_table <number> = some Sys.Registry.<Mirror>.<name>_arm`
  for a registered arm, closed by `rfl`, so the build itself checks that the
  copied text elaborates to the registry's constant, and
  `lookup_arm spec_table <number> = none` for an unregistered one, the L3
  decline shape `check_decline_registers.py` reads off the registry.

WHAT A READER READS.  No tool reads the generated text: a build product
cannot answer `git show <ref>:<path>`, and the two jobs that grade a port
(`generated-docs`, and the guards `lean` runs before its `lake build`) have
no Lean build to have produced it.  Every tool that needs the registered
arms calls `registry_arms` below -- ONE reader, over the committed registry
files, fail-closed on an empty read -- and gets the same `(number, name,
spec, expr)` tuples this generator renders from.  `arms_in_texts` is the
same reader over texts a caller fetched itself, which is how
`lean_port_arms.py` and `lean_port_health.py` read a ref: they list the
registry directory at it and scan the fragments, where they used to
`git show` the table.  The rule for anything new: a question about WHICH
arms are registered is asked of the registry files, and a question about
the RENDER -- the order of the table, its imports, its placeholder shape --
is asked of `render_table`/`render_pins` and tested in
`test_gen_lean_registry.py`, because nothing else can see the render.
(`check_copyin_parity.py`, `check_surface_claims.py` and `specdeps.py` read
the Rocq table only, and are untouched by any of this.)

`--out-dir DIR --module NAME` writes one of the two modules under `DIR` at
its module path, which is what the lakefile's facet runs, once per module,
with a dependency array; `--check` recomputes both and refuses a tree that
cannot generate them, a source-tree copy shadowing the build product, and a
build product that is stale, which is what the `generated-docs` job runs.
Both compute everything before they open anything, so a refusal writes
nothing.  The invariant a rebase gets from this: a generated file is never
in a diff, so it can never conflict.

RULES, each a refusal naming the file and line:

  REG-1  a registry file's mirror twin `Sys/<Mirror>.lean` exists, and the
         file imports exactly `Sys.Dispatch` and that twin;
  REG-2  the namespace is `…Sys.Registry.<Mirror>`, opened once, closed
         by a matching `end` with nothing after it (an arm after `end` is
         outside the namespace, and the pins name it inside), and every
         `open` is one of OPENS;
  REG-3  every arm is a Rocq arm: its number is in the Rocq table with
         that name, its spec is the one Rocq's arm applies, spelled
         `Sys.<Mirror>.<spec>`, and its arguments are Rocq's, text for text
         up to Lean namespace qualification (a Lean arm reading `in_arg i 0`
         where Rocq reads `in_arg i 1` is the bug this rule is for);
         `<Mirror>.lean` defines the spec.  Eleven Rocq arms apply helpers
         that live outside the four namespaces OPENS lists -- `sig32`
         (Kernel/Signal), `cred_uids`, `cred_gids` and their setters
         (Kernel/Sys), the `Creds` projections `cr_uid`, `cr_euid`,
         `cr_gid`, `cr_egid` (State) -- and a registry line spells those
         qualified, `Sys.Kernel.Signal.sig32`, `Creds.cr_uid`, because
         neither the registry file nor the table opens their namespaces;
         the comparison drops every `Upper.` qualifier from the Lean text
         first, so the rule still holds the order, arity and names of the
         arguments to Rocq's, and then holds each qualifier to the Lean
         home of the helper's Rocq definition: `Sys.<M>.` for a
         `Definition` in `theories/LinuxProcessSem/Sys/<M>.v`, `<Record>.`
         for a field of a Rocq `Record` -- so a qualifier cannot pick a
         same-named constant from another namespace, and a helper Rocq
         defines where the table already looks (State.v) is written
         unqualified, as Rocq writes it;
  REG-4  a number is registered once in a file (REG-3 already keeps two
         files from registering one number: it ties the number to the
         file of the twin defining its spec, and there is one file per
         twin);
  REG-5  every other non-blank line is refused;
  REG-6  a twin that defines a spec Rocq dispatches has registered every
         arm Rocq dispatches to it: a port that lands the definition and
         not the arm is the silent narrowing the Lean table's "subset of
         the Rocq one" rule exists to name (`check_syscall_docs.py` holds
         the subset direction, failing on a Lean arm with no Rocq twin;
         this pins that the subset is not narrower than the tree).  The
         twin is read with its re-exported parts (the parity checker's
         split-twin shape), comments blanked, every declaration modifier
         admitted; a `private` definition counts here and is refused under
         REG-3, since the table, another module, cannot name it.
  REG-7  a registry file's PROSE -- its header docstring, its comments and
         any string literal, which between them are every place in a Lean
         file a `--flag` token can stand, since `--` opens a comment
         anywhere an arm line could hold one -- names no command-line flag
         this tool does not accept.
         A registry file's header is boilerplate the next port copies
         from a sibling: nothing renders it (the scaffold deliberately
         writes no registry file) and nothing read it either, so a
         sentence that goes stale in one file propagates into every file
         added after it.  All 31 headers standing on 2026-09-21 told
         their reader to "run it with `--write` after editing this file,
         and commit what it regenerates" -- the pre-T31 instruction, by
         then naming a flag `main` does not take and asking for what
         `--check` refuses, a committed copy of a build product.  It runs
         after REG-1 to REG-5 on the same file, so a file wrong in its
         prose and in an arm line reports the arm.
         The accepted set is read off the parser `build_parser` returns
         rather than listed again here, so a flag deleted from the CLI
         refuses every comment that still names it, this rule and the
         thing it checks being one edit apart.

  ROCQ   the Rocq table is read fail-closed: no arms, an unsorted table, a
         duplicated number or an arm line this reader does not match all
         refuse rather than generate from a partial read.

LIMITS.  Nothing here elaborates Lean: REG-3 compares text, so an arm that
is Rocq's text for text but resolves a name to a different constant through
the four opens is the build's to catch (the `rfl` pins are where it fails).
A qualified helper is held to the Lean home of its Rocq definition (REG-3
above), which rules out a same-named constant in another namespace; what it
does not check is that the Lean twin of that home defines the helper at
all, which the build does.  A helper Rocq defines in two files is refused as
ambiguous rather than guessed.  Beyond qualification the comparison is
exact, so an argument Lean would have to spell otherwise than Rocq does --
there is none in the Rocq table today: the eleven qualified helpers are the
whole difference, and `test_gen_lean_registry.py` recomputes that list --
would need this rule relaxed by a `tools:` change with the reason recorded
here.  A Rocq table change (a new arm, a relabelled one) changes a
placeholder line, which no PR has to commit any more: the next build
renders it.  REG-7 reads a token and not the sentence around it, so a
registry comment naming ANOTHER tool's flag is refused as well; none does
today, and the alternative -- matching the flag against the script named
nearest it -- is a guess about prose, which is what let the stale sentence
stand.  A comment naming an accepted flag is not checked for saying
anything true about it: REG-7 is a rule against an instruction that cannot
be followed, not a proofreader -- the other half of the retired sentence,
"commit what it regenerates", names no flag and passes, and so would a
header saying it beside `--check`.  The token rule also reads a line
comment written without the space after `--` (`--todo`) as naming a flag
and refuses it; write `-- todo`.  That refusal is wrong about the token
and right about the file: nothing in a registry file is prose the table
needs, so the cost is one edit and the alternative, a guess about which
`--word`s are comments, is the guess this rule replaces.

    python3 tools/gen_lean_registry.py --check [ROOT]
    python3 tools/gen_lean_registry.py --print [ROOT]        # the table, to stdout
    python3 tools/gen_lean_registry.py --print-pins [ROOT]   # the pins, to stdout
    python3 tools/gen_lean_registry.py --out-dir DIR --module NAME [ROOT]
"""
import argparse
import collections
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_lean_pins import blank_comments_and_strings  # noqa: E402
import check_lean_spec_parity as parity  # noqa: E402
import check_spec_file_map  # noqa: E402

ROCQ_SYS = "theories/LinuxProcessSem/Sys"
ROCQ_TABLE = ROCQ_SYS + "/SyscallTable.v"
LEAN_TREE = "lean/LinuxProcessSemantics/LinuxProcessSem"
LEAN_SYS = LEAN_TREE + "/Sys"
REGISTRY_DIR = LEAN_SYS + "/Registry"
# The two build products.  `TABLE` and `PINS` are the SOURCE paths they no
# longer occupy: what `--check` refuses to find there, what `.gitignore`
# names, and the keys `generate` returns.  The lakefile's facet writes each
# under GENERATED_DIR at its module path.
TABLE = LEAN_SYS + "/SyscallTable.lean"
PINS = LEAN_TREE + "/Checks/Cases/SyscallTable.lean"
LEAN_DIR = "lean"
GENERATED_DIR = LEAN_DIR + "/.lake/generated"
MODULE = "LinuxProcessSemantics.LinuxProcessSem"
SYS_MODULE = MODULE + ".Sys"
REGISTRY_MODULE = SYS_MODULE + ".Registry"
# The generated import list, a sibling of the registry modules and not their
# prefix: lean/lakefile.lean's SysRegistry comment says why the name matters.
REGISTRY_UMBRELLA = REGISTRY_MODULE + ".All"
DISPATCH_MODULE = SYS_MODULE + ".Dispatch"
# Module name -> the source path that module would have had.  The lakefile
# declares exactly these two as the roots of its `SysTable` library, and
# `--module` takes one of them.
GENERATED = {
    MODULE + ".Sys.SyscallTable": TABLE,
    MODULE + ".Checks.Cases.SyscallTable": PINS,
}

# What the generated table opens, and so the only namespaces a registry file
# may open: a name resolving through any other `open` would resolve in the
# registry and not in the table.
OPENS = (
    "LinuxProcessSemantics.Riscv.Prelude",
    MODULE + ".State",
    SYS_MODULE + ".Syscall",
    DISPATCH_MODULE,
)

# What a refusal tells the reader to do.  There is no `--write`: the two
# files are the build's to render, so the fix for a source-tree copy is to
# delete it, and the fix for a stale build product is to build.
CHECK_HINT = "python3 tools/gen_lean_registry.py --check ."

# `  (* getcwd          *) mkSpecArm  17%Z (fun i => getcwd_spec (in_arg i 1) i) ::`
ROCQ_ARM = re.compile(
    r"^\s*\(\*\s*([A-Za-z0-9_]+)\s*\*\)\s*mkSpecArm\s+(\d+)%Z\s+(\(fun i => .+\))\s*::\s*$")
# The token both tables write an arm with, counted against what the
# readers match: an arm written in a shape a reader skips is an arm
# every caller reports as unregistered.
ARM_TOKEN = re.compile(r"\bmkSpecArm\b")
# `def flock_arm : SpecArm := SpecArm.mkSpecArm 32 (fun i => Sys.Fs.Locks.flock_spec … i)`
LEAN_ARM = re.compile(
    r"^def ([a-z0-9_]+)_arm : SpecArm := SpecArm\.mkSpecArm (\d+) (\(fun i => .+\))$")
# The applied spec inside `(fun i => <qualifier><spec><rest>)`.  The name
# ends at `_spec` and nothing may continue it: `\b` alone would take
# `read_spec'` -- a different Lean constant -- as `read_spec` applied to a
# body starting with the prime, and every rule here would then pair the
# arm with `read_spec`'s twin while the table dispatched elsewhere.
HEAD = re.compile(r"^\(fun i => ((?:[A-Za-z0-9_']+\.)*)([A-Za-z0-9_']+_spec)(?![\w'])(.*)\)$", re.S)
# A Lean namespace qualifier on an identifier: one or more `Upper.` segments
# before a name.  Lowercase dotted names (`i.in_sysno`) are projections and
# stay; Rocq spells no qualifier in its arms.
QUALIFIER = re.compile(r"\b(?:[A-Z][A-Za-z0-9_']*\.)+(?=[A-Za-z_])")
# The same qualifier with the name it qualifies, for the home check.
QUALIFIED = re.compile(r"\b((?:[A-Z][A-Za-z0-9_']*\.)+)([A-Za-z_][A-Za-z0-9_']*)")
# A top-level `def`/`abbrev` in a twin or one of its parts: attributes, then
# any of Lean's declaration modifiers (the parity checker's list), then the
# keyword and the name.  Only `private` matters here: the generated table
# is another module and cannot name a private def.
LEAN_DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?P<mods>(?:(?:" + "|".join(parity.LEAN_MODIFIERS) + r")\s+)*)"
    r"(?:def|abbrev)\s+(?P<name>[^\s:(\[{]+)")
# Rocq's definitions and record fields, for a qualifier's home.
ROCQ_ANY_DEF = re.compile(r"^(?:Definition|Fixpoint)\s+([A-Za-z_][A-Za-z0-9_']*)", re.M)
ROCQ_RECORD = re.compile(r"\bRecord\s+([A-Za-z_][A-Za-z0-9_']*)\b[^{]*\{(.*?)\}", re.S)
ROCQ_FIELD = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_']*)\s*:", re.M)
ROCQ_TREE = "theories/LinuxProcessSem"
# A long option named in prose (REG-7).  `--` has to begin the token, not
# follow a word character or another hyphen, and be followed by a letter: so
# `-- word` (this file's own dash; the registry headers write an em dash),
# `well--formed` and a TeX `---dash` are not flags.  A line comment written
# without the space, `--todo`, IS one to this rule; see LIMITS.
PROSE_FLAG = re.compile(r"(?<![\w-])--[a-z][a-z0-9-]*")
LEAN_IMPORT = re.compile(r"^import\s+(\S+)\s*$")
LEAN_OPEN = re.compile(r"^open\s+(\S+)\s*$")
LEAN_NAMESPACE = re.compile(r"^namespace\s+(\S+)\s*$")
LEAN_END = re.compile(r"^end\s+(\S+)\s*$")
LABEL_WIDTH = 15


class Refusal(Exception):
    """A tree this tool will not generate from, with the reason."""


def read(root, rel):
    """The text at `root/rel`, or a Refusal: a file this cannot open or
    decode is a tree it will not generate from, said in one sentence
    rather than a traceback whose last line names an errno and no file
    of ours.  `rocq_arms` and `registry_files` check for existence first,
    so what reaches this is the unexpected case -- a permission, bytes
    that are not UTF-8, a directory where the Rocq table or a twin was.
    (A directory under a registry file's name never reaches here: the
    registry walk lists files alone, so it leaves the walk short of arms
    and `arms_in_texts` refuses that instead.)"""
    try:
        with open(os.path.join(root, rel), encoding="utf-8") as fh:
            return fh.read()
    except OSError as e:
        raise Refusal(f"{rel}: cannot read it ({e.strerror or e})")
    except UnicodeDecodeError as e:
        raise Refusal(f"{rel}: not UTF-8 text ({e.reason} at byte {e.start})")


# ------------------------------------------------------------- the one reader
# `(rel, line)` say where the arm is written, so a caller reports the registry
# file a reader of the generated table used to report.
Arm = collections.namedtuple("Arm", "rel line number name spec expr")


def arms_in_texts(items):
    """`{number: Arm}` over registry-file texts: `items` is an iterable of
    `(rel, text)`.  THE reader for every tool that needs the registered arms
    (this module's "WHAT A READER READS"), so that the spelling of an arm
    line is matched in one place and a fragment shape this cannot read is
    refused rather than skipped by five tools in five ways.

    Fail-closed four ways, because a reader that answers "no arms", or one
    arm fewer, reads in every caller as a tree with nothing wrong: an empty
    result is a Refusal; so is a number two files register -- `lookup_arm` is
    first-match-wins, so the second arm would be dead, and a caller counting
    arms would count it; so is a file with more `mkSpecArm` tokens than
    this matched, which is how an arm written in a shape nobody reads (the
    `<| fun i => …` spelling) would otherwise pass as absent; and so is an
    arm applying no `<name>_spec`, which has a number and dispatches to
    something no tool here can pair with a twin.
    Comments and strings are blanked first (`check_lean_pins`' reader), so a
    commented-out arm is not an arm.  A non-arm line is NOT refused here: the
    registry files carry imports, a namespace and docstrings, and REG-5, which
    refuses everything else, is `parse_registry`'s rule and needs the Rocq
    table this reader deliberately does not."""
    out = {}
    for rel, text in items:
        clean = blank_comments_and_strings(text)
        found = 0
        for lineno, line in enumerate(clean.splitlines(), 1):
            m = LEAN_ARM.match(line.rstrip())
            if not m:
                continue
            found += 1
            name, number, expr = m.group(1), int(m.group(2)), m.group(3)
            head = HEAD.match(expr)
            if not head:
                raise Refusal(f"{rel}:{lineno}: arm {number} applies no "
                              f"`<name>_spec`: {expr!r}; a reader that skipped "
                              "it would report every other arm agreeing")
            if number in out:
                raise Refusal(f"{rel}:{lineno}: number {number} is registered "
                              f"twice, here and at {out[number].rel}:"
                              f"{out[number].line}; lookup_arm is "
                              "first-match-wins, so the second arm is dead")
            out[number] = Arm(rel, lineno, number, name, head.group(2), expr)
        written = len(ARM_TOKEN.findall(clean))
        if found != written:
            raise Refusal(f"{rel}: {written} arms are written and {found} "
                          "could be read; an arm this skips is one every "
                          "caller reports as unregistered, and the shape that "
                          "does it is Lean -- `SpecArm.mkSpecArm 226 <| fun i "
                          "=> …` matches nothing here")
    if not out:
        raise Refusal(f"{REGISTRY_DIR}: read no arm out of the registry files. "
                      "Either none registers one or the "
                      "`def <name>_arm : SpecArm := SpecArm.mkSpecArm <number> "
                      "(fun i => …)` shape changed and this reader no longer "
                      "matches it; both would have every caller report a tree "
                      "with no modeled syscall as a tree with nothing wrong")
    return out


def registry_arms(root):
    """`{number: Arm}` for the working tree at `root`."""
    return arms_in_texts((rel, read(root, rel)) for rel in registry_files(root))


# How long a git call this makes may take before it is a refusal rather
# than a hang: the publisher runs on a timer, and a `git` that never
# returns is the one failure that shows on no page at all.
REF_TIMEOUT = 60


def registry_arms_at_ref(root, ref, run=subprocess.run, timeout=REF_TIMEOUT):
    """`{number: Arm}` as of a git ref, for the two callers that grade a ref
    they have no worktree of (`lean_port_arms.py`, `lean_port_health.py`).
    The registry files are committed, so a ref can answer this; the generated
    table cannot be read this way at all, which is why those two moved here.

    A Refusal carries the reason, and both callers turn it into their own
    "this ref was not read" answer rather than into zero arms.  Every way
    this can fail is one: a git that exits nonzero, a git that cannot be
    started at all, a git that hangs past `timeout`, and a listed path
    whose bytes are not text -- the last because `git show` decodes
    strict, so an `._`-prefixed AppleDouble sidecar committed beside a
    registry file (the accident .gitignore's own comment records) could
    otherwise reach a caller as UnicodeDecodeError, past every handler
    either one has.  `is_registry_source` keeps those
    sidecars out of both listers at once; the decode guard stands behind
    it for the file this has not thought of."""
    def git(*args):
        try:
            return run(["git", "-C", root, *args], capture_output=True, text=True,
                       timeout=timeout)
        except subprocess.TimeoutExpired:
            raise Refusal(f"{ref}: git {args[0]} did not finish in {timeout}s")
        except UnicodeDecodeError:
            raise Refusal(f"{ref}: git {args[0]} answered bytes that are not UTF-8 text")
        except OSError as e:
            # no git on PATH, or a `root` that is not a directory: the
            # publisher's timer would otherwise see a traceback, not a
            # branch that was not read
            raise Refusal(f"{ref}: git {args[0]} could not run ({e.strerror or e})")

    ls = git("ls-tree", "-r", "--name-only", "-z", ref, "--", REGISTRY_DIR + "/")
    if ls.returncode != 0:
        raise Refusal(f"{ref}: git ls-tree exited {ls.returncode}: "
                      f"{(ls.stderr or '').strip()[:160]}")
    rels = [r for r in ls.stdout.split("\0") if is_registry_source(r)]
    if not rels:
        raise Refusal(f"{ref} has no {REGISTRY_DIR}")

    def fetch(rel):
        r = git("show", f"{ref}:{rel}")
        if r.returncode != 0:
            raise Refusal(f"{ref}: git show {rel} exited {r.returncode}")
        return r.stdout
    return arms_in_texts((rel, fetch(rel)) for rel in rels)


# ---------------------------------------------------------------- Rocq side
def rocq_arms(root):
    """The Rocq table's arms in file order, each
    `(number, name, spec, expr, file)`: `expr` is the `(fun i => …)` text and
    `file` the `Sys/…` path (below theories/LinuxProcessSem) defining `spec`.
    Fail-closed: a table this cannot read whole is not generated from."""
    path = os.path.join(root, ROCQ_TABLE)
    if not os.path.exists(path):
        raise Refusal(f"{ROCQ_TABLE}: no such file; the Rocq table is the "
                      "universe the Lean table is a subset of")
    arms, written = [], 0
    for lineno, line in enumerate(read(root, ROCQ_TABLE).splitlines(), 1):
        written += len(ARM_TOKEN.findall(line))
        m = ROCQ_ARM.match(line)
        if not m:
            continue
        head = HEAD.match(m.group(3))
        if not head or head.group(1):
            raise Refusal(f"{ROCQ_TABLE}:{lineno}: arm applies no bare "
                          f"`<name>_spec`: {m.group(3)!r}")
        arms.append((int(m.group(2)), m.group(1), head.group(2), m.group(3)))
    if not arms:
        raise Refusal(f"{ROCQ_TABLE}: read no arms out of spec_table; either "
                      "the table is empty or its shape changed, and a Lean "
                      "table generated from nothing would decline everything "
                      "while reading as complete")
    if len(arms) != written:
        raise Refusal(f"{ROCQ_TABLE}: {written} arms are written and "
                      f"{len(arms)} could be read; an arm this skips is one "
                      "the Lean table would silently lack")
    numbers = [n for n, *_ in arms]
    if numbers != sorted(numbers):
        raise Refusal(f"{ROCQ_TABLE}: spec_table is not sorted by number; the "
                      "generated table follows Rocq's order and this refuses "
                      "to copy a disorder")
    dup = sorted(n for n in set(numbers) if numbers.count(n) > 1)
    if dup:
        raise Refusal(f"{ROCQ_TABLE}: number(s) {dup} written twice; "
                      "lookup_arm is first-match-wins, so one arm is dead")
    where = defining_files(root, {spec for _, _, spec, _ in arms})
    return [(n, name, spec, expr, where[spec]) for n, name, spec, expr in arms]


def defining_files(root, specs):
    """spec name -> `Sys/…` path (below theories/LinuxProcessSem) that
    defines it, refusing none and two.  The walk is check_spec_file_map.py's
    (one reader of `Definition`/`Fixpoint <name>_spec` for the tree, not a
    copy); that tool exits where this raises, so its exit is turned into a
    Refusal with the same text."""
    saved = check_spec_file_map.SYS
    check_spec_file_map.SYS = ROCQ_SYS
    try:
        return check_spec_file_map.defining_files(root, specs)
    except SystemExit as e:
        raise Refusal(str(e))
    finally:
        check_spec_file_map.SYS = saved


# ---------------------------------------------------------------- registries
def is_registry_source(path):
    """Is `path` one of the registry files, rather than something beside
    them?  The two listers below -- the working tree's and the git ref's --
    ask this and nothing else, because a rule only one of them applies is a
    disagreement about what the registry IS: the `._`-prefixed AppleDouble
    sidecars .gitignore's comment records reaching this index by accident
    are files `git ls-tree` will list and `os.walk` will find alike."""
    name = os.path.basename(path)
    return name.endswith(".lean") and not name.startswith("._")


def registry_files(root):
    """Repository-relative paths of every registry file, sorted."""
    base = os.path.join(root, REGISTRY_DIR)
    out = []
    if os.path.isdir(base):
        for dirpath, _, names in os.walk(base):
            for name in names:
                if is_registry_source(name):
                    full = os.path.join(dirpath, name)
                    out.append(os.path.relpath(full, root).replace(os.sep, "/"))
    return sorted(out)


def twin_declares(root, mirror, spec):
    """How `Sys/<mirror>.lean` declares `spec` at top level: 'def' for a
    `def`/`abbrev` the generated table can name, 'private' for one it cannot,
    None for no declaration.  The twin's re-exported parts are read too --
    check_lean_spec_parity.twin_parts, the split-twin shape that checker
    admits -- and comments and strings are blanked first: a `def` quoted in
    a docstring is not a definition, a commented-out one is not either."""
    lean_rel = f"Sys/{mirror}.lean"
    text = read(root, f"{LEAN_TREE}/{lean_rel}")
    lean_set = set(parity.lean_twin_files(root))
    files = [text] + [read(root, f"{LEAN_TREE}/{part}")
                      for part in parity.twin_parts(lean_rel, text, lean_set)]
    found = None
    for ltext in files:
        pending = ""
        for line in blank_comments_and_strings(ltext).splitlines():
            # A line of attributes and modifiers alone is the PREFIX of the
            # declaration on the next line, and Lean reads the two as one:
            # `private\ndef foo_spec` is a private definition.  Joined the
            # way parity's `lean_decls` joins it, through the same
            # LEAN_MODIFIER_LINE, because reading the `def` line by itself
            # answers "def" for a spec no other module can name, and REG-3
            # would then pass a registry line whose generated table does
            # not compile.
            if parity.LEAN_MODIFIER_LINE.match(line):
                pending += line.strip() + " "
                continue
            if pending and line.strip():
                line, pending = pending + line.lstrip(), ""
            m = LEAN_DECL.match(line)
            if not m or m.group("name").rsplit(".", 1)[-1] != spec:
                continue
            if "private" in m.group("mods").split():
                found = found or "private"
                continue
            return "def"
    return found


def rocq_helper_sites(root):
    """name -> [('def', <path below theories/LinuxProcessSem>) | ('field',
    <Record>), …] for every Definition, Fixpoint and record field of the
    Rocq tree, comments stripped (check_lean_spec_parity's reader): where a
    qualified helper in a registry line has to come from."""
    sites = {}
    base = os.path.join(root, ROCQ_TREE)
    for dirpath, _, names in os.walk(base):
        for name in sorted(names):
            if not name.endswith(".v"):
                continue
            rel = os.path.relpath(os.path.join(dirpath, name), base).replace(os.sep, "/")
            text = parity.strip_rocq_comments(read(root, f"{ROCQ_TREE}/{rel}"))
            for m in ROCQ_ANY_DEF.finditer(text):
                sites.setdefault(m.group(1), []).append(("def", rel))
            for m in ROCQ_RECORD.finditer(text):
                for field in ROCQ_FIELD.findall(m.group(2)):
                    sites.setdefault(field, []).append(("field", m.group(1)))
    return sites


def qualifier_home(sites, name):
    """`(qualifier, None)`: the one qualifier a registry line may put on
    `name` -- `Sys.<M>.` for a Definition in Sys/<M>.v, `<Record>.` for a
    record field -- or `(None, reason)` when it may carry none: Rocq defines
    it where the table's opens already reach (State.v), or nowhere, or in
    two places."""
    found = sites.get(name, [])
    if not found:
        return None, (f"Rocq defines no `{name}` (no Definition, Fixpoint or "
                      f"record field under {ROCQ_TREE}), so a qualifier has "
                      "nothing to name")
    if len(found) > 1:
        return None, (f"Rocq defines `{name}` in more than one place ("
                      + ", ".join(f"{k} {w}" for k, w in found)
                      + "), so which one the qualifier means cannot be checked")
    kind, where = found[0]
    if kind == "field":
        return f"{where}.", None
    if where.startswith("Sys/"):
        return "Sys." + where[len("Sys/"):-len(".v")].replace("/", ".") + ".", None
    return None, (f"Rocq defines `{name}` in {where}, whose Lean twin the "
                  "table reaches through its opens; write it unqualified, "
                  "as Rocq does")


def cli_flags():
    """Every long option this tool accepts, off the parser's own actions.
    `_actions` is argparse's only enumeration of them -- the public API
    parses and formats, it does not list -- and the alternative, a tuple of
    flag names beside `build_parser`, is the second copy REG-7 exists to
    stop: it would go stale exactly as the registry headers did."""
    return {opt for action in build_parser()._actions
            for opt in action.option_strings if opt.startswith("--")}


def prose_flags(text):
    """`(lineno, flag)` for every long option `text` names.  The whole text
    is scanned rather than the comments alone, because in Lean the token
    cannot be anything else: `--` opens a comment wherever an arm line
    could hold it, and the only other place it survives is a string
    literal, which is prose for this rule's purpose.  That premise is
    pinned on the real registry files by
    `test_gen_lean_registry.py`, so the day an arm line can carry one this
    reader is told to grow the blanked-text half rather than quietly
    refusing code."""
    for m in PROSE_FLAG.finditer(text):
        yield text.count("\n", 0, m.start()) + 1, m.group(0)


def parse_registry(root, rel, rocq, sites=None):
    """`(mirror, [(number, name, expr, line)])` for one registry file, or a
    Refusal.  `rocq` is `rocq_arms(root)`; `sites` is `rocq_helper_sites(root)`,
    computed here when not given."""
    if sites is None:
        sites = rocq_helper_sites(root)
    mirror = rel[len(REGISTRY_DIR) + 1:-len(".lean")]          # e.g. Fs/Locks
    twin_rel = f"{LEAN_SYS}/{mirror}.lean"
    if not os.path.exists(os.path.join(root, twin_rel)):
        raise Refusal(f"{rel}: REG-1: registers arms for {twin_rel}, which "
                      "does not exist; a registry file is one per twin")
    twin_module = f"{SYS_MODULE}.{mirror.replace('/', '.')}"
    want_ns = f"{REGISTRY_MODULE}.{mirror.replace('/', '.')}"
    rocq_by_number = {n: (name, spec, expr, file) for n, name, spec, expr, file in rocq}
    imports, opens, namespace, ended, arms = [], [], None, False, []
    raw = read(root, rel)
    clean = blank_comments_and_strings(raw)
    for lineno, line in enumerate(clean.splitlines(), 1):
        line = line.rstrip()
        if not line.strip():
            continue
        if ended:
            raise Refusal(f"{rel}:{lineno}: REG-2: a line after `end {namespace}`: "
                          f"{line.strip()!r}; an arm there is outside the "
                          "namespace the pins name it in")
        m = LEAN_IMPORT.match(line)
        if m:
            imports.append(m.group(1))
            continue
        m = LEAN_NAMESPACE.match(line)
        if m:
            if namespace is not None:
                raise Refusal(f"{rel}:{lineno}: REG-2: a second namespace")
            if m.group(1) != want_ns:
                raise Refusal(f"{rel}:{lineno}: REG-2: namespace is "
                              f"{m.group(1)}, not {want_ns}; the pins name the "
                              "arm through the mirror's namespace")
            namespace = m.group(1)
            continue
        m = LEAN_OPEN.match(line)
        if m:
            if m.group(1) not in OPENS:
                raise Refusal(f"{rel}:{lineno}: REG-2: opens {m.group(1)}, "
                              "which the generated table does not open, so a "
                              "name resolving through it here would not "
                              f"resolve there; the table opens {', '.join(OPENS)}")
            opens.append(m.group(1))
            continue
        m = LEAN_END.match(line)
        if m:
            if m.group(1) != namespace:
                raise Refusal(f"{rel}:{lineno}: REG-2: `end {m.group(1)}` "
                              f"closes no `namespace {want_ns}`")
            ended = True
            continue
        m = LEAN_ARM.match(line)
        if m:
            if namespace is None:
                raise Refusal(f"{rel}:{lineno}: REG-2: an arm before the namespace")
            name, number, expr = m.group(1), int(m.group(2)), m.group(3)
            if number not in rocq_by_number:
                raise Refusal(f"{rel}:{lineno}: REG-3: {number} is not an arm "
                              f"of {ROCQ_TABLE}; the Lean table is a subset "
                              "of the Rocq one")
            rname, rspec, rexpr, rfile = rocq_by_number[number]
            if name != rname:
                raise Refusal(f"{rel}:{lineno}: REG-3: {number} is "
                              f"{rname!r} in {ROCQ_TABLE}, not {name!r}")
            if rfile != f"Sys/{mirror}.v":
                raise Refusal(f"{rel}:{lineno}: REG-3: {rspec} is defined in "
                              f"{rfile}, so {number} belongs to "
                              f"{REGISTRY_DIR}/{rfile[len('Sys/'):-2]}.lean, "
                              "not here")
            head = HEAD.match(expr)
            if not head:
                raise Refusal(f"{rel}:{lineno}: REG-3: arm applies no "
                              f"`Sys.<Mirror>.<name>_spec`: {expr!r}")
            qualifier, spec, rest = head.groups()
            want_q = f"Sys.{mirror.replace('/', '.')}."
            if spec != rspec:
                raise Refusal(f"{rel}:{lineno}: REG-3: applies {spec}, and "
                              f"Rocq's arm {number} applies {rspec}")
            if qualifier != want_q:
                raise Refusal(f"{rel}:{lineno}: REG-3: {spec} is spelled "
                              f"{qualifier}{spec}; spell it {want_q}{spec}, "
                              "the name the generated table resolves")
            rhead = HEAD.match(rexpr)
            if QUALIFIER.sub("", rest) != rhead.group(3):
                raise Refusal(f"{rel}:{lineno}: REG-3: arguments are "
                              f"`{rest.strip()}`, and Rocq's arm {number} "
                              f"reads `{rhead.group(3).strip()}`; the arm is "
                              "the Rocq one text for text, up to a "
                              "`Namespace.` qualifier on a helper")
            for q, x in QUALIFIED.findall(rest):
                want, why = qualifier_home(sites, x)
                if want is None:
                    raise Refusal(f"{rel}:{lineno}: REG-3: `{q}{x}` is "
                                  f"qualified, and {why}")
                if q != want:
                    raise Refusal(f"{rel}:{lineno}: REG-3: `{x}` is spelled "
                                  f"`{q}{x}`; Rocq defines it at "
                                  f"{sites[x][0][1]}, so its Lean name here "
                                  f"is `{want}{x}`")
            declared = twin_declares(root, mirror, spec)
            if declared is None:
                raise Refusal(f"{rel}:{lineno}: REG-3: {twin_rel} defines no "
                              f"{spec}; the arm would dispatch to nothing")
            if declared == "private":
                raise Refusal(f"{rel}:{lineno}: REG-3: {twin_rel} defines "
                              f"{spec} as `private`, which the generated "
                              "table, another module, cannot name")
            arms.append((number, name, expr, lineno))
            continue
        raise Refusal(f"{rel}:{lineno}: REG-5: a line this does not read: "
                      f"{line.strip()!r}.  A registry file holds imports, "
                      "the namespace, `open`s from the table's list and "
                      "`def <name>_arm : SpecArm := SpecArm.mkSpecArm <n> "
                      "(fun i => …)` lines, one per line, and nothing else")
    want_imports = sorted([DISPATCH_MODULE, twin_module])
    if sorted(imports) != want_imports:
        raise Refusal(f"{rel}: REG-1: imports {sorted(imports)}; a registry "
                      f"file imports exactly {want_imports}")
    if namespace is None:
        raise Refusal(f"{rel}: REG-2: no `namespace {want_ns}`")
    if not ended:
        raise Refusal(f"{rel}: REG-2: no `end {want_ns}`")
    seen = {}
    for number, name, _, lineno in arms:
        if number in seen:
            raise Refusal(f"{rel}:{lineno}: REG-4: {number} is registered "
                          f"twice in this file (line {seen[number]} too)")
        seen[number] = lineno
    # REG-7 last: the prose is read only once the code has passed REG-1 to
    # REG-5, so a file wrong in both reports the arm defect it reported
    # before this rule existed, and no earlier refusal changes place.
    accepted = cli_flags()
    for lineno, flag in prose_flags(raw):
        if flag not in accepted:
            raise Refusal(f"{rel}:{lineno}: REG-7: the prose names `{flag}`, "
                          f"which gen_lean_registry.py does not accept; it "
                          f"takes {', '.join(sorted(accepted))}.  A header "
                          "here is what the next registry file is copied "
                          "from, so an instruction that cannot be followed "
                          "is one every later file gets too")
    return mirror, arms


def registry(root, rocq):
    """number -> (mirror, name, expr) over every registry file, REG-6
    applied.  Two files cannot register one number: REG-3 ties a number to
    the registry file of the twin defining its spec, and there is one file
    per twin, so REG-4 is a rule about one file."""
    by_number = {}
    sites = rocq_helper_sites(root)
    for rel in registry_files(root):
        mirror, arms = parse_registry(root, rel, rocq, sites)
        for number, name, expr, _ in arms:
            by_number[number] = (mirror, name, expr)
    for number, name, spec, _, rfile in rocq:
        if number in by_number:
            continue
        mirror = rfile[len("Sys/"):-len(".v")]
        twin_rel = f"{LEAN_SYS}/{mirror}.lean"
        if os.path.exists(os.path.join(root, twin_rel)) \
                and twin_declares(root, mirror, spec):
            raise Refusal(f"{twin_rel}: REG-6: defines {spec}, which Rocq "
                          f"dispatches at {number} ({name}), and no registry "
                          f"file registers {number}; add\n"
                          f"  def {name}_arm : SpecArm := SpecArm.mkSpecArm "
                          f"{number} (fun i => Sys.{mirror.replace('/', '.')}"
                          f".{spec} …)\nto {REGISTRY_DIR}/{mirror}.lean, or "
                          "the arm declines while the file reads as ported")
    return by_number


# ---------------------------------------------------------------- rendering
TABLE_HEADER = f"""import {DISPATCH_MODULE}
import {REGISTRY_UMBRELLA}

/-! # LinuxProcessSem.Sys.SyscallTable — the modeled syscall surface, one line each

GENERATED by `tools/gen_lean_registry.py` from the files under
`Sys/Registry/`, into `lean/.lake/generated/` on every build
(`lean/lakefile.lean`'s `generatedInput` facet); NOT A SOURCE FILE.  It is
not committed and never edited: a copy of it in the source tree is a second
definition of this module, refused by `--check` in the `generated-docs` job
and by `tools/check_lean_policy.py` after a build.

Mirrors `theories/LinuxProcessSem/Sys/SyscallTable.v`, which answers to
`arch/riscv/kernel/syscall_table.c`.  This list IS the modeled surface:
`Specs.syscall_spec` dispatches over it and `Specs.modeled_sysnos` is read
off it.

TRUST BOUNDARY: this file is part of the trusted specification.  What is
trusted is the text below, which is each registry file's `(fun i => …)`
body copied verbatim after the arm's number (re-aligned to the column);
`Checks/Cases/SyscallTable.lean` pins, by `rfl`, that each copy elaborates
to the registry's constant.

ONE LINE PER ARM OF THE ROCQ TABLE, in Rocq's order: an arm some file under
`Sys/Registry/` registers is written out, and one no file registers is a
comment holding its place: that number is one the Lean model declines
(`unmodeled`, fail closed; `lean/README.md` has the proof contract).  So the
Lean table is a subset of the Rocq one by construction, and a port replaces
its own line without touching another's.
Two ports cannot conflict here at all: the line they would each have
rewritten is in no diff, because this file is in no commit.  The spec names are
spelled from `Sys` because nothing here opens a twin: the arms reach their
twins through `Sys.Registry.All`, the import list `lean/lakefile.lean`
writes from the registry directory on every build. -/

namespace {SYS_MODULE}.SyscallTable

{chr(10).join(f"open {o}" for o in OPENS)}

def spec_table : List SpecArm :=
"""

TABLE_FOOTER = f"""  []

end {SYS_MODULE}.SyscallTable
"""

PINS_HEADER = f"""import {MODULE}.Specs

/-! # Checks.Cases.SyscallTable — the table is the registry, number by number

GENERATED by `tools/gen_lean_registry.py` from the files under
`Sys/Registry/`, into `lean/.lake/generated/` on every build; not committed,
not edited, and not part of the trusted specification.

One theorem per arm of the Rocq table (`theories/LinuxProcessSem/Sys/
SyscallTable.v`), in its order.  For a number some registry file registers,
the table's lookup answers that file's constant, closed by `rfl`, and a
second theorem, `syscall_at_<number>`, states that `syscall_spec` on an input
carrying that number IS the arm's spec on the same input; it is `dispatch_arm`
at the first theorem, because a bare `rfl` makes the kernel unfold the whole
table and a few arms (`sched_setscheduler`, `getgroups`) exceed its recursion
limit.
That second theorem is what lets a pin file import the twin and not `Specs`:
a routing pin (`syscall_spec` reaches the twin's spec) is stated here, and
the twin's own pins are stated on its spec.  The first: the arm
text the generator copied into `Sys/SyscallTable.lean` elaborates to the
same term as the registry's `def`, or the build fails here.  For a number
no registry file registers, the lookup answers `none`, which is the L3
decline shape `tools/check_decline_registers.py` reads, so that register
and the table cannot disagree.  Every theorem carries `model:` evidence:
these are closed computations over the model's own definitions, not
kernel claims. -/

namespace {MODULE}.Checks.Cases.SyscallTable

open {DISPATCH_MODULE}
open {SYS_MODULE}.SyscallTable
open {MODULE}.Specs
open {MODULE}.State
open {MODULE}.Monad
open {MODULE}.BvBase
open LinuxProcessSemantics.Riscv.Prelude

"""

PINS_FOOTER = f"""end {MODULE}.Checks.Cases.SyscallTable
"""

MODEL_LINE = "model: a closed lookup over the generated table; the registry file is its source. -/"
MODEL_BRIDGE_LINE = "model: `dispatch_arm` at the lookup pin above; the registry file is its source. -/"
MODEL_NONE_LINE = "model: a closed lookup over the generated table; no registry file registers this number. -/"


def label(name):
    return f"/- {name:<{LABEL_WIDTH}} -/"


def render_table(rocq, reg):
    lines = [TABLE_HEADER]
    for number, name, _, _, _ in rocq:
        if number in reg:
            _, _, expr = reg[number]
            lines.append(f"  {label(name)} SpecArm.mkSpecArm {number:>3} {expr} ::\n")
        else:
            lines.append(f"  {label(name)} -- {number}: declined; no registry file registers it\n")
    lines.append(TABLE_FOOTER)
    return "".join(lines)


def render_pins(rocq, reg):
    lines = [PINS_HEADER]
    for number, name, _, _, _ in rocq:
        if number in reg:
            mirror, rname, _ = reg[number]
            const = f"Sys.Registry.{mirror.replace('/', '.')}.{rname}_arm"
            lines.append(f"/-- `{name}` ({number}) dispatches to `{const}`, the arm "
                         f"`Sys/Registry/{mirror}.lean` registers.\n{MODEL_LINE}\n"
                         f"theorem sysno_{number} : lookup_arm spec_table {number} = some {const} := rfl\n\n"
                         f"/-- `syscall_spec` on any input carrying number {number} is `{const}`'s spec on that input.\n"
                         f"{MODEL_BRIDGE_LINE}\n"
                         f"theorem syscall_at_{number} (args : List word) (mem wmem : word → Option byte) :\n"
                         f"    syscall_spec (SyscallInput.mkInput {number} args mem wmem)\n"
                         f"      = {const}.sa_spec (SyscallInput.mkInput {number} args mem wmem) := by\n"
                         f"  funext m o\n"
                         f"  exact propext (dispatch_arm spec_table _ m o _ sysno_{number})\n\n")
        else:
            lines.append(f"/-- `{name}` ({number}) is a Rocq arm no registry file registers: the table declines it.\n"
                         f"{MODEL_NONE_LINE}\n"
                         f"theorem sysno_{number} : lookup_arm spec_table {number} = none := rfl\n\n")
    lines.append(PINS_FOOTER)
    return "".join(lines)


def generate(root):
    """{relative path: text} for both generated files, or a Refusal."""
    rocq = rocq_arms(root)
    reg = registry(root, rocq)
    return {TABLE: render_table(rocq, reg), PINS: render_pins(rocq, reg)}


# ---------------------------------------------------------------- commands
def module_rel(module):
    """The repository-relative path the lakefile's facet writes `module` to."""
    return GENERATED_DIR + "/" + module.replace(".", "/") + ".lean"


def shadowing(root, want):
    """The SOURCE paths a build product is also committed at.

    An in-source copy is not a stale file to refresh but a second definition
    of a module Lake resolves to the generated library: `lake build` keeps
    passing (the ordinary library's glob walk registers the module's job
    under a key naming the package and the module before the import is
    resolved -- lean_mutate.shadowed_sources has the Lake reference), while
    `check_lean_policy.py` refuses the pair as a `duplicate Lean module` and
    a `lake build <module>` by name reads whichever copy won.  So this is
    refused here too, without a toolchain: `generated-docs` has none, and a
    port that runs a generator by hand and commits the result is exactly the
    shape the refusal is for.  `lexists`: a symlink at the path whose
    target is gone is still an entry git tracks and Lake's directory walk
    lists as a `.lean` module, so it is refused like a file."""
    return [rel for rel in sorted(want) if os.path.lexists(os.path.join(root, rel))]


def stale(root, want):
    """The build products that exist and differ from what the registry now
    generates.  A product that does not exist is not stale -- nothing has
    built it, and the next build writes it -- so this is empty on every
    machine with no `.lake`, which is every run of the `generated-docs` job."""
    out = []
    for rel, text in sorted(want.items()):
        out_rel = module_rel(module_for(rel))
        path = os.path.join(root, out_rel)
        if os.path.exists(path) and read(root, out_rel) != text:
            out.append(out_rel)
    return out


def module_for(rel):
    """The module name of a generated source path."""
    for module, path in GENERATED.items():
        if path == rel:
            return module
    raise Refusal(f"{rel}: not one of the generated modules "
                  f"({', '.join(sorted(GENERATED))})")


def check(root):
    """Refuse a tree that cannot generate, a source copy of a build product,
    and a build product that is stale; the summary line is an interface --
    every port brief's DONE list matches it by regular expression."""
    want = generate(root)
    bad = []
    for rel in shadowing(root, want):
        bad.append(f"{rel}: a source copy of a build product; "
                   f"`lean/lakefile.lean` writes {module_for(rel)} under "
                   f"{GENERATED_DIR}/ on every build, so this file is a "
                   "second copy of one module. Delete it: nothing has to be "
                   "regenerated or committed.")
    for out_rel in stale(root, want):
        bad.append(f"{out_rel}: stale build product; it differs from what the "
                   "registry files now generate. The next `lake build` "
                   "rewrites it; nothing is committed either way.")
    if bad:
        for line in bad:
            print(line, file=sys.stderr)
        print(f"gen_lean_registry.py: {len(bad)} generated file(s) refused.  "
              f"Run\n  {CHECK_HINT}\nagain once each file above is gone or "
              "rebuilt; the two generated files are never committed and never "
              "edited by hand.", file=sys.stderr)
        return 1
    print(f"gen_lean_registry.py: {len(want)} generated files current "
          f"({registered(root, want)} arms registered)")
    return 0


def registered(root, want):
    return len(re.findall(r"\bmkSpecArm\s+\d+\b", want[TABLE].split("def spec_table", 1)[1]))


def write_module(root, out_dir, module):
    """Write one generated module under `out_dir`, at its module path.

    Everything is computed before anything is opened, so a refusal leaves the
    tree as it was, and the file is rewritten only when its text changes, so
    a build whose registry did not move does not touch a product Lake has
    already traced.  One module per run because the lakefile's facet is
    per-module: two facet jobs may run at once, and each writing both files
    would have them write each other's."""
    if module not in GENERATED:
        raise Refusal(f"--module {module}: not a generated module "
                      f"({', '.join(sorted(GENERATED))})")
    text = generate(root)[GENERATED[module]]
    path = os.path.join(out_dir, *module.split(".")) + ".lean"
    os.makedirs(os.path.dirname(path), exist_ok=True)
    current = read(os.path.dirname(path), os.path.basename(path)) if os.path.exists(path) else None
    if current != text:
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(text)
    print(f"gen_lean_registry.py: {module} "
          f"{'unchanged' if current == text else 'written'} at {path}")
    return 0


def build_parser():
    """The CLI.  Built here rather than inside `main` so that REG-7 can ask
    it what this tool accepts: the rule and the thing it checks are then one
    definition, and a flag renamed or deleted is refused in the prose that
    still names it by the same edit."""
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--check", action="store_true",
                   help="fail on a source copy or a stale build product")
    g.add_argument("--print", action="store_true", help="the table, to stdout")
    g.add_argument("--print-pins", action="store_true", help="the pins, to stdout")
    g.add_argument("--out-dir", help="write one module under this directory "
                                     "(the lakefile's facet; needs --module)")
    ap.add_argument("--module", help="which generated module --out-dir writes")
    ap.add_argument("root", nargs="?", default=".", help="repository root")
    return ap


def main(argv=None):
    ap = build_parser()
    args = ap.parse_args(argv)
    # The pair is checked before anything is dispatched, so the rule holds
    # for every mode: `--check --module X` used to reach `check` and drop
    # the argument, which reads as a checked module and is a whole-tree
    # check of both.
    if args.out_dir is not None and not args.module:
        ap.error("--out-dir needs --module: the facet writes one module per run")
    if args.module and args.out_dir is None:
        ap.error("--module is only for --out-dir")
    try:
        if args.check:
            return check(args.root)
        if args.out_dir is not None:
            return write_module(args.root, args.out_dir, args.module)
        sys.stdout.write(generate(args.root)[PINS if args.print_pins else TABLE])
        return 0
    except Refusal as e:
        print(f"gen_lean_registry.py: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
