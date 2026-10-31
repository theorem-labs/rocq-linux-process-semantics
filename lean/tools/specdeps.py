#!/usr/bin/env python3
"""Definition-level dependency graph of the syscall specs, from the sources.

No build needed. Parses every top-level Definition / Fixpoint / Inductive /
Record under theories/LinuxProcessSem (minus Checks/), records which known
names each body mentions, and closes transitively from each `<name>_spec`
that `Sys/SyscallTable.v`'s spec_table dispatches to.

Usage:
  specdeps.py                     # port-order table for all syscalls
  specdeps.py openat              # everything openat needs, topologically sorted
  specdeps.py openat --dot > g.dot
  specdeps.py --syscall-dot > s.dot   # syscall -> syscall edges (A's closure contains B_spec)
  specdeps.py --order              # greedy port order maximising reuse (what ledger.html shows)
  specdeps.py --json               # the graph as JSON, what ledger.html embeds
  specdeps.py --html OUT           # render docs/lean-port/ledger.html
  --root DIR with any of these reads a checkout elsewhere; the default is the one this file is in
"""
import os, posixpath, re, sys, subprocess, collections, functools

# tools/ sits directly under the repository root; --root overrides for a checkout elsewhere.
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if "--root" in sys.argv:
    ROOT = os.path.abspath(sys.argv[sys.argv.index("--root") + 1])
TH = os.path.join(ROOT, "theories")
LPS = os.path.join(TH, "LinuxProcessSem")
STATEMENTS_TREE = "EquivalenceDefinition"

LEMMA_KEYWORDS = ("Lemma", "Theorem", "Fact", "Remark", "Corollary", "Proposition")
HEAD = re.compile(
    r"^\s*(?:Local\s+|Global\s+|Program\s+|#\[[^\]]*\]\s*)*"
    r"(Definition|Fixpoint|CoFixpoint|Inductive|Record|Variant|Class|Instance|Structure|Notation|Let|"
    + "|".join(LEMMA_KEYWORDS) + r")\s+"
    r"(?:\"[^\"]*\"|([A-Za-z_][A-Za-z0-9_']*))", re.S)
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
KEYWORDS = set("""fun match with end if then else let in forall exists fix cofix
Type Set Prop return as _ struct measure wf""".split())


# A pure function of the text, asked the same question many times: one site
# generation (tools/lean_port_status.py) walks the tree through parse_tree and
# direct_requires nine times over, 1323 calls on 175 distinct files and 4.1 CPU
# seconds, measured 2026-09-22.  So a text is lexed once per process; the
# bound only caps what a long-lived caller holds.
@functools.lru_cache(maxsize=1024)
def strip_comments(src):
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("(*", i):
            depth += 1; i += 2; continue
        if depth and src.startswith("*)", i):
            depth -= 1; i += 2; continue
        if depth:
            i += 1; continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 1
            out.append('""'); i = j + 1; continue
        out.append(src[i]); i += 1
    return "".join(out)


def sentences(src):
    # a sentence ends at '.' followed by whitespace or EOF; '..' never ends one
    buf, i, n = [], 0, len(src)
    while i < n:
        c = src[i]
        buf.append(c)
        if c == "." and (i + 1 == n or src[i + 1].isspace()) and not (i > 0 and src[i - 1] == "."):
            yield "".join(buf); buf = []
        i += 1
    if "".join(buf).strip():
        yield "".join(buf)


def definition_sentences(parts, path):
    """Keep transparent lemma proof blocks, omit opaque ones, refuse unknown closers.

    Both readers supply comment-stripped sentences with strings shielded by
    their own lexer. A later declaration must not supply a missing closer.
    Section Let names use the file module, just like Local Definition names;
    readers must pass every entered name to check_repeated_bindings below.
    """
    parts = iter(parts)
    for sentence in parts:
        head = HEAD.match(sentence)
        if not head or head.group(1) not in LEMMA_KEYWORDS:
            yield sentence
            continue
        block = [sentence]
        for part in parts:
            closer = part.strip()
            match = re.fullmatch(r"[\s{}+*-]*(Defined|Qed)\s*\.", closer)
            if match:
                if match.group(1) == "Defined":
                    yield "\n".join(block + [part])
                break
            if (HEAD.match(part) or re.match(
                    r"\s*(?:Section|End|Module|CoInductive|Abbreviation|Admitted|Abort|Save)\b", part)):
                sys.exit(f"{path}: cannot determine proof closer for {head.group(2)}: "
                         "expected Defined. or Qed. before " + closer)
            block.append(part)
        else:
            sys.exit(f"{path}: cannot determine proof closer for {head.group(2)}: "
                     "expected Defined. or Qed. before end of file")


def check_repeated_bindings(seen, names, kind, path):
    """Refuse a repeated name in one file when either binding is a Let.

    The bounded readers do not resolve section scopes: the graph and the
    body hash would otherwise read different bindings of the same name.
    Each reader supplies every name it enters, including mutual aliases,
    and a fresh `seen` per file. Repeated non-Let names already occur in
    the tree and retain their existing treatment.
    """
    for name in names:
        if name in seen and (kind == "Let" or seen[name] == "Let"):
            sys.exit(f"{path}: repeated binding for {name} involving Let: "
                     "cannot resolve section scopes for the dependency graph and body hash")
        seen[name] = kind


def tree_paths(root=None):
    """(root, theories dir, theories/LinuxProcessSem dir) for `root`, or for
    the checkout this file is in when `root` is None.  The module-level
    ROOT/TH/LPS are what the command line reads; a caller that imports this
    module -- tools/check_lean_spec_parity.py builds a twin's closure over a
    `--root` of its own -- passes its root here instead of rebinding them."""
    if root is None:
        return ROOT, TH, LPS
    root = os.path.abspath(root)
    th = os.path.join(root, "theories")
    return root, th, os.path.join(th, "LinuxProcessSem")


def modname(path, th=None):
    rel = os.path.relpath(path, TH if th is None else th)[:-2]
    return "LinuxProcessSemantics." + rel.replace(os.sep, ".")


def rocq_trees(th, statements=False):
    return [os.path.join(th, "LinuxProcessSem")] + (
        [os.path.join(th, STATEMENTS_TREE)] if statements else [])


def parse_tree(include_checks=False, root=None, *, statements=False):
    """Top-level definitions under LinuxProcessSem, optionally EquivalenceDefinition, keyed (module, name).

    The Checks/ tree is skipped by default: the ledger is about the specs, and
    the executable checkers, witnesses and worked cases there would appear as
    users of every definition.  `include_checks=True` walks it too, which is
    what tools/lean_port_brief.py needs to close a C ticket's checker
    (Checks/Sys/<X>.v, Checks/Witness/<X>.v and the arm in
    Checks/Sys/Dispatch.v) over the same graph as the spec it checks.
    `statements=True` also walks theories/EquivalenceDefinition, without a Checks filter."""
    root, th, lps = tree_paths(root)
    defs = {}          # (module, name) -> dict(kind, body, file)
    by_name = collections.defaultdict(list)
    for tree in rocq_trees(th, statements):
        for dp, _, fs in os.walk(tree):
            if tree == lps and "/Checks" in dp and not include_checks:
                continue
            for f in sorted(fs):
                if not f.endswith(".v"):
                    continue
                path = os.path.join(dp, f)
                mod = modname(path, th)
                with open(path) as fh:
                    src = strip_comments(fh.read())
                seen = {}
                for s in definition_sentences(sentences(src), os.path.relpath(path, root)):
                    m = HEAD.match(s)
                    if not m or not m.group(2):
                        continue
                    kind, name = m.group(1), m.group(2)
                    names = [name]
                    if kind in ("Fixpoint", "CoFixpoint", "Inductive"):
                        names += re.findall(r"\bwith\s+([A-Za-z_][A-Za-z0-9_']*)", s)
                    check_repeated_bindings(seen, names, kind, os.path.relpath(path, root))
                    key = (mod, name)
                    defs[key] = dict(kind=kind, body=s, file=os.path.relpath(path, root), aliases=set(names))
                    for nm in names:
                        by_name[nm].append(key)
                    # constructors / record fields resolve to the type that owns them
                    if kind in ("Inductive", "Variant", "Record", "Structure", "Class"):
                        body = s[m.end():]
                        for c in re.findall(r"(?:^|\||\{|;)\s*([A-Za-z_][A-Za-z0-9_']*)\s*(?::|\(|\{)", body):
                            if c != name:
                                by_name[c].append(key)
    return defs, by_name


# The module list of a `Require` sentence: dotted names separated by whitespace, up to the
# sentence's own full stop (a `.` followed by whitespace or the end of the file).  A module
# name's dots are part of the name, so `Fs.ReadWrite.` ends at its LAST dot: the earlier
# `[^.]*?` stopped at the first one and read `Require Export Prelude Fs.ReadWrite.` -- the one
# Checks sentence of Fcntl.v and of the other Checks/Sys files importing ReadWrite's checker --
# as no import at all.
_MODULES = r"((?:[A-Za-z0-9_.]*[A-Za-z0-9_]\s+)*[A-Za-z0-9_.]*[A-Za-z0-9_])\s*\.(?=\s|$)"


def direct_requires(root=None, *, statements=False):
    """module -> the modules it names in its own `From … Require` sentences (no closure).

    The half of file_requires below that reads the tree: every module under
    theories/LinuxProcessSem names its requirements with `From LinuxProcessSemantics.<pkg>
    Require [Import|Export] a b c.` (one or several, possibly wrapped over lines), and the
    module name is the path.  Import, Export and a bare `Require` all count: a body may mention
    a name it sees through either of the first two, and the third (Checks/RiscvDefinedIllegal.v's
    `Require Sem.`, kept un-Imported so `Sem.step` does not shadow) is a compile dependency and a
    Lean `import` all the same.  The plan generator reads THIS map for a ticket's import edges
    (tools/lean_port_graph.py, derive_edges rule 3): what a file's own imports are is a fact
    about that file; what they pull in transitively is the closure below.
    `statements=True` includes EquivalenceDefinition modules in that map too."""
    _root, th, _lps = tree_paths(root)
    direct = {}
    for tree in rocq_trees(th, statements):
        for dirpath, _dirs, names in os.walk(tree):
            for name in sorted(names):
                if not name.endswith(".v"):
                    continue
                path = os.path.join(dirpath, name)
                rel = os.path.relpath(path, th)[:-2]
                mod = "LinuxProcessSemantics." + rel.replace(os.sep, ".")
                with open(path, errors="replace") as fh:
                    text = strip_comments(fh.read())
                deps = set()
                for m in re.finditer(r"From\s+(LinuxProcessSemantics(?:\.[A-Za-z0-9_]+)*)\s+Require\s+(?:(?:Import|Export)\s+)?" + _MODULES, text, re.S):
                    pkg, mods = m.group(1), m.group(2).split()
                    deps |= {pkg + "." + x for x in mods}
                for m in re.finditer(r"(?<![\w.])Require\s+(?:(?:Import|Export)\s+)?" + _MODULES, text, re.S):
                    deps |= {x for x in m.group(1).split() if x.startswith("LinuxProcessSemantics.")}
                direct[mod] = deps
    return direct


def file_requires(root=None, *, statements=False):
    """module -> set of transitively required modules, read from the `From … Require` sentences.

    coqdep would answer this exactly, but it needs a Rocq toolchain and this generator
    runs where the docs job runs, without one.  The source is enough (direct_requires
    reads it); this is its transitive closure over both Import and Export, since a
    name visible through either is a name a body may mention.  `statements=True`
    also follows the requirements of EquivalenceDefinition modules."""
    direct = direct_requires(root, statements=statements)
    memo = {}
    def close(m):
        if m in memo:
            return memo[m]
        memo[m] = set()
        acc = set()
        for d in direct.get(m, ()):
            acc.add(d); acc |= close(d)
        memo[m] = acc
        return acc
    return {m: close(m) for m in direct}


def build_graph(include_checks=False, root=None, *, statements=False):
    """Definition references, optionally including statements visible through Require or locally."""
    defs, by_name = parse_tree(include_checks, root, statements=statements)
    reqs = file_requires(root, statements=statements)
    # Qualified references can start at any component of a module path.
    ours = {part for module in reqs for part in module.split(".")}
    edges = {}
    ambiguous = collections.Counter()
    for key, d in defs.items():
        mod = key[0]
        visible = reqs.get(mod, set()) | {mod}
        m = HEAD.match(d["body"])
        body = d["body"][m.end():]
        deps = set()
        # Keep all visible qualified matches because import shadowing is not modeled here.
        for tok in IDENT.findall(body):
            qualifier = None
            if "." in tok:
                head, last = tok.split(".")[0], tok.split(".")[-1]
                if head not in ours:
                    continue
                qualifier = tok.rsplit(".", 1)[0]
                tok = last
            if qualifier is None and (tok in KEYWORDS or tok in d["aliases"]):
                continue
            cands = [k for k in by_name.get(tok, ()) if k != key
                     and (not defs[k]["file"].startswith(f"theories/{STATEMENTS_TREE}/")
                          or k[0] in visible)]
            if not cands:
                continue
            same = [k for k in cands if k[0] == mod]
            vis = [k for k in cands if k[0] in visible]
            qualified = [k for k in cands if qualifier is not None
                         and (k[0] == qualifier or k[0].endswith("." + qualifier))]
            visible_qualified = [k for k in qualified if k[0] in visible]
            pick = visible_qualified or qualified or same or vis or cands
            if len(set(pick)) > 1:
                ambiguous[tok] += 1
            if len(set(visible_qualified)) > 1:
                deps.update(visible_qualified)
            else:
                deps.add(pick[0])
        edges[key] = deps
    return defs, by_name, edges, ambiguous


def spec_table():
    with open(os.path.join(LPS, "Sys/SyscallTable.v")) as fh:
        src = fh.read()
    arms = re.findall(r"\(\*\s*([a-z0-9_]+)\s*\*\)\s*mkSpecArm\s+(\d+)%Z\s+\(fun\s+\w+\s*=>\s*([A-Za-z_][A-Za-z0-9_']*)", src)
    return [(name, int(no), spec) for name, no, spec in arms]


def closure(edges, start):
    seen, order = set(), []
    def visit(k):
        if k in seen:
            return
        seen.add(k)
        for d in sorted(edges.get(k, ())):
            visit(d)
        order.append(k)           # post-order: dependencies first
    visit(start)
    return order


def frontier_closure(edges, start, expand):
    """Post-order closure from `start` that walks INTO a definition's body only where
    `expand(key)` holds.  Every key reached is returned, dependencies first; a key
    `expand` refuses is a leaf: recorded as reached, its body never read.

    This is what a port ticket needs from the tree, as opposed to what the ledger
    shows.  `closure` reads every body it reaches, which is right for the ledger
    (porting mmap does mean porting everything under it) and wrong for a ticket's
    edges: State.v's `with_tid` rebuilds ProcState field by field, so its body
    names `m_sigaltstack_installed`, `m_statpins` and the rest, while the Lean
    `with_tid` is one structure update that names none of them.  A spec that
    calls a setter uses the setter; it does not rebuild the record.  The ticket
    generator therefore expands only the files that are ported arm by arm (the
    spec files under Sys/ and their checker and witness twins) and stops at
    every base definition, which is how twenty-seven tickets that "needed" the
    signal-state ticket through a setter became the three that read its names."""
    seen, order = set(), []
    def visit(k):
        if k in seen:
            return
        seen.add(k)
        if expand(k):
            for d in sorted(edges.get(k, ())):
                visit(d)
        order.append(k)
    visit(start)
    return order


def spec_keys(by_name):
    """Dispatcher arm name -> the (module, name) key of the spec function it calls."""
    return {name: by_name[spec][0] for name, _no, spec in spec_table() if by_name.get(spec)}


def checker_starts(defs, by_name):
    """Dispatcher arm name -> the Checks/ definitions its `arm_<name>` block in
    Checks/Sys/Dispatch.v names.  The block's Definition sentence is only the
    type (`arm_x : CheckedArm.`); the checker and witness are named inside the
    proof, so the identifiers of the whole block are read and resolved to the
    definitions under Checks/ that carry those names."""
    with open(os.path.join(LPS, "Checks/Sys/Dispatch.v")) as fh:
        dispatch = strip_comments(fh.read())
    blocks = {m.group(1): m.group(2) for m in re.finditer(
        r"Definition\s+arm_([a-z0-9_]+)\s*:\s*CheckedArm\s*\.(.*?)(?:Defined|Qed)\s*\.", dispatch, re.S)}
    check_mods = {k[0] for k in defs if "/Checks/" in defs[k]["file"]}
    starts = {}
    for arm, block in blocks.items():
        keys = set()
        for tok in set(IDENT.findall(block)):
            keys |= {k for k in by_name.get(tok, ()) if k[0] in check_mods and k[1] == tok}
        starts[arm] = keys
    return starts


TREE_PREFIX = "theories/LinuxProcessSem/"


def tree_relpath(path):
    """A root-relative Rocq path spelled relative to theories/LinuxProcessSem."""
    return posixpath.relpath(path, TREE_PREFIX)


def tag_of(defs, key):
    """A definition as `<path relative to theories/LinuxProcessSem>:<name>`, the spelling
    plan.json's provides, needs and uses carry."""
    return f"{tree_relpath(defs[key]['file'])}:{key[1]}"


def arm_closures(walked, graph=None):
    """Per dispatcher arm, the frontier closure of its spec (`uses`) and of its
    checker (`checker_uses`), as sorted tag lists.  `walked` is the set of Rocq
    paths (relative to theories/LinuxProcessSem) whose bodies the walk enters; every
    other definition reached is a leaf.  `graph` is build_graph(include_checks=True)'s
    result, passed by a caller that already has it."""
    defs, by_name, edges, _ambiguous = graph or build_graph(include_checks=True)
    expand = lambda k: tree_relpath(defs[k]["file"]) in walked
    starts = checker_starts(defs, by_name)
    out = {}
    for arm, key in spec_keys(by_name).items():
        uses = {tag_of(defs, k) for k in frontier_closure(edges, key, expand)}
        checker = {tag_of(defs, k) for s in starts.get(arm, ()) for k in frontier_closure(edges, s, expand)}
        out[arm] = dict(uses=sorted(uses), checker_uses=sorted(checker))
    return out


def base_defs(closures):
    """The definitions every syscall's closure contains.  The ledger page shades these as the
    shared base and leaves them out of each row's "new" count: porting any one syscall ports
    all of them, so they say nothing about which syscall to port next."""
    sets = [set(c) for c in closures.values()]
    return set.intersection(*sets) if sets else set()


def greedy_order(closures, ported=()):
    """The port order the ledger page shows by default, as (syscall, new definitions) rows.

    At each step: the syscall whose closure adds the fewest definitions not yet ported and
    not in the shared base, ties broken by closure size, then by name.  `ported` names the
    syscalls already done: they come first, in table order and adding nothing, and their
    closures count as ported before the first greedy step -- the page's ticked rows.

    This is the Python twin of `greedy` in tools/lean_port_templates/ledger.html, which the
    page runs under JavaScript; tools/test_specdeps.py runs that JavaScript under node on the
    same data and requires the two to agree row for row.  One difference is deliberate and
    that test is what bounds it: the page breaks name ties with localeCompare and this with
    plain string order, which agree on every name spec_table has today."""
    done = set(base_defs(closures))
    for name in ported:
        done |= set(closures[name])
    remaining = {n: c for n, c in closures.items() if n not in ported}
    rows = [(n, []) for n in closures if n in ported]
    while remaining:
        name = min(remaining, key=lambda n: (len(set(remaining[n]) - done), len(remaining[n]), n))
        new = [k for k in remaining[name] if k not in done]
        rows.append((name, new))
        done |= set(new)
        del remaining[name]
    return rows


def main():
    valued = {sys.argv[i + 1] for i, a in enumerate(sys.argv) if a in ("--root", "--html") and i + 1 < len(sys.argv)}
    args = [a for a in sys.argv[1:] if not a.startswith("--") and a not in valued]
    flags = {a for a in sys.argv[1:] if a.startswith("--")}
    defs, by_name, edges, ambiguous = build_graph()
    table = spec_table()
    spec_key = {}
    for name, no, spec in table:
        ks = by_name.get(spec, [])
        if not ks:
            print(f"warning: {spec} not found", file=sys.stderr); continue
        spec_key[name] = ks[0]
    spec_of_key = collections.defaultdict(list)
    for name, k in spec_key.items():
        spec_of_key[k].append(name)
    closures = {name: closure(edges, k) for name, k in spec_key.items()}

    if ambiguous and "--quiet" not in flags:
        print("ambiguous short names (resolved by import visibility, first candidate kept): "
              + ", ".join(sorted(ambiguous)), file=sys.stderr)

    if "--syscall-dot" in flags:
        print("digraph syscalls {\n  rankdir=LR; node [shape=box];")
        for name in closures:
            for k in closures[name]:
                for other in spec_of_key.get(k, ()):
                    if other != name:
                        print(f'  "{name}" -> "{other}";')
        print("}")
        return

    if args:
        name = args[0]
        if name not in closures:
            sys.exit(f"unknown syscall {name!r}; known: {' '.join(sorted(closures))}")
        order = closures[name]
        if "--dot" in flags:
            print(f'digraph "{name}" {{\n  rankdir=LR; node [shape=box, fontname=monospace];')
            inset = set(order)
            for k in order:
                d = defs[k]
                lbl = f"{k[1]}\\n{d['file'].replace('theories/LinuxProcessSem/', '')}"
                shape = "octagon" if k in spec_of_key else "box"
                print(f'  "{k[1]}" [label="{lbl}", shape={shape}];')
                for dep in edges[k]:
                    if dep in inset:
                        print(f'  "{k[1]}" -> "{dep[1]}";')
            print("}")
            return
        print(f"{name}: {len(order)} definitions, dependencies first\n")
        print(f"{'definition':40} {'kind':10} {'file':45} shared-with")
        for k in order:
            d = defs[k]
            users = sorted(s for s, c in closures.items() if s != name and k in c)
            tag = ",".join(spec_of_key[k]) if k in spec_of_key and spec_of_key[k] != [name] else ""
            share = f"{len(users)} syscalls" if users else "only this one"
            if tag:
                share += f"  (spec of {tag})"
            print(f"{k[1]:40} {d['kind']:10} {d['file'].replace('theories/LinuxProcessSem/', ''):45} {share}")
        return

    if "--order" in flags:
        print(f"shared base: {len(base_defs(closures))} definitions in every closure, not counted as new")
        print(f"{'#':>3} {'syscall':16} {'sysno':>5} {'closure':>7} {'new':>4}  new definitions")
        for i, (name, new) in enumerate(greedy_order(closures), 1):
            no = next(n for nm, n, _ in table if nm == name)
            print(f"{i:>3} {name:16} {no:>5} {len(closures[name]):>7} {len(new):>4}  "
                  + " ".join(k[1] for k in new[:8]) + (" ..." if len(new) > 8 else ""))
        return

    print(f"{'syscall':16} {'sysno':>5} {'closure':>7}  {'same spec function as':28} calls the spec of")
    for name, no, spec in table:
        if name not in closures:
            continue
        same = sorted(o for o in spec_of_key[spec_key[name]] if o != name)
        calls = sorted({o for k in closures[name] for o in spec_of_key.get(k, ()) if o != name} - set(same))
        print(f"{name:16} {no:>5} {len(closures[name]):>7}  {' '.join(same):28} {' '.join(calls)}")


def export_json():
    import json
    defs, by_name, edges, ambiguous = build_graph()
    table = spec_table()
    spec_key = {name: by_name[spec][0] for name, no, spec in table if by_name.get(spec)}
    closures = {name: closure(edges, k) for name, k in spec_key.items()}
    used = sorted({k for c in closures.values() for k in c})
    idx = {k: i for i, k in enumerate(used)}
    users = collections.defaultdict(list)
    for name, c in closures.items():
        for k in c:
            users[k].append(name)
    nodes = [dict(name=k[1], kind=defs[k]["kind"], file=defs[k]["file"].replace("theories/LinuxProcessSem/", ""),
                  deps=sorted(idx[d] for d in edges[k] if d in idx), users=len(users[k]),
                  line=defs[k]["body"].count("\n") + 1) for k in used]
    sys_ = [dict(name=name, sysno=no, spec=spec, closure=[idx[k] for k in closures[name]], specId=idx[spec_key[name]])
            for name, no, spec in table if name in closures]
    return json.dumps(dict(nodes=nodes, syscalls=sys_), separators=(",", ":"))


def render_html(facts=None):
    """docs/lean-port/ledger.html as a string: the template under tools/lean_port_templates with
    the graph spliced in and the shared navigation filled.  A plain file, viewable from a
    checkout or GitHub Pages; no build needed."""
    here = os.path.dirname(os.path.abspath(__file__))
    template = os.path.join(here, "lean_port_templates", "ledger.html")
    with open(template) as fh:
        text = fh.read()
    assert text.count("__DATA__") == 1, template
    sys.path.insert(0, here)
    import lean_port_nav
    skeleton = ('<!doctype html>\n<html lang="en">\n<head>\n<meta charset="utf-8">\n'
                '<meta name="viewport" content="width=device-width,initial-scale=1">\n'
                '<style>:root{color-scheme:light dark}body{margin:0;font:14px system-ui,sans-serif}'
                'img{max-width:100%}[hidden]{display:none!important}</style>\n')
    # The ledger's payload is a `<script type="application/json">` block, which the tokenizer treats
    # exactly like any other script: a `<` in it can end the element early.  Nothing in this graph is
    # chosen outside the repository today -- the strings are Rocq identifiers, kinds and `theories/`
    # paths -- but that is a property of the inputs, not of the splice, so it goes through the same
    # escape as every other page's payload.
    body = lean_port_nav.fill(text.replace("__DATA__", lean_port_nav.escape_script_text(export_json())), "ledger", facts)
    # the template opens with <title> and <link>/<style>; the first block-level tag starts the body
    i = body.find("\n<nav")
    if i < 0:
        i = body.find("\n<header")
    return skeleton + body[:i] + "\n</head>\n<body>" + body[i:] + "\n</body>\n</html>\n"


def write_html(out_path):
    with open(out_path, "w") as fh:
        fh.write(render_html())


if __name__ == "__main__":
    # Under the guard so that importing this module -- lean_port_status.py does, for the
    # ledger -- never reads the importer's argv: `--json` there would print a graph.
    if "--json" not in sys.argv and "--html" not in sys.argv:
        main()
    if "--json" in sys.argv:
        sys.stdout.write(export_json())
    if "--html" in sys.argv:
        write_html(sys.argv[sys.argv.index("--html") + 1])
