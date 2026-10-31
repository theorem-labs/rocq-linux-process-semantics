#!/usr/bin/env python3
"""Explicit Cases families, from a working tree or a git revision.

Paths are repository-relative POSIX paths. The anchor's direct imports are
its registry, in source order; directory enumeration only detects omissions.
A View is a read-only snapshot for one check, not a process-global cache.
Checker Cases remain monoliths; splitting them is deliberately unsupported.
"""
import argparse
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys

BASE = "lean/LinuxProcessSemantics/LinuxProcessSem/"
CASES = BASE + "Checks/Cases/"
MODULE = "LinuxProcessSemantics.LinuxProcessSem.Checks.Cases."
# Existing namespace overlaps, not direct-import families: the base Fs model,
# per-subsystem Uapi pins, and the checker invariant's separately built pins.
STANDALONE = {CASES + p for p in ("Fs.lean", "Sys/Uapi.lean", "Checks/VmMapsDisjoint.lean")}


class FamilyError(ValueError):
    """A registry cannot be read unambiguously; callers must fail closed."""


def merge_helpers(rel, tables):
    merged = {}
    for found in tables:
        overlap = merged.keys() & found.keys()
        if overlap:
            raise FamilyError(f"{rel}: ambiguous family helper {sorted(overlap)[0]}")
        merged.update(found)
    return merged


def imports(text):
    """Read the import header, stopping at the first declaration command.

    Like parity's twin_parts this reads direct imports only. The existing
    parity regex reads just one name per line; here multi-import lines are
    supported and unreadable imports are refused. Skipping nested comments
    before parsing avoids scanning megabytes of proofs on each brief fill.
    """
    out, depth = [], 0
    for raw in text.lstrip("\ufeff").splitlines():
        clean, i = [], 0
        while i < len(raw):
            if raw.startswith("/-", i):
                depth += 1
                clean.append(" ")
                i += 2
            elif depth and raw.startswith("-/", i):
                depth -= 1
                i += 2
            elif depth:
                i += 1
            elif raw.startswith("--", i):
                break
            else:
                clean.append(raw[i])
                i += 1
        line = "".join(clean).strip()
        if not line or line in ("module", "prelude"):
            continue
        if (re.fullmatch(r"(?:public|private|meta)(?:\s+(?:public|private|meta))*", line)
                or re.match(r"(?:module|prelude)\b", line)):
            raise FamilyError("unsupported Cases import header: " + line)
        m = re.match(r"(?:(?:public|private|meta)\s+)*import(?:\s+(.*))?$", line)
        if not m:
            if re.match(r"(?:(?:public|private|meta)\s+)*import\b", line):
                raise FamilyError("unreadable Cases import: " + line)
            return out
        words = (m[1] or "").split()
        if words and words[0] in ("all", "runtime"):
            words.pop(0)
        if not words or any(not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", w)
                            for w in words):
            raise FamilyError("unreadable Cases import: " + line)
        out.extend(words)
    if depth:
        raise FamilyError("unclosed comment in Cases import header")
    return out


class View:
    def __init__(self, root, revision=None):
        self.root, self.revision = Path(root), revision
        self._texts, self._families = {}, {}
        if revision is None:
            self.paths = {p.relative_to(self.root).as_posix()
                          for p in (self.root / CASES).rglob("*.lean")}
        else:
            self.paths = {p for p in self.git("ls-tree", "-rz", "--name-only", revision, "--", CASES).split("\0")
                          if p.endswith(".lean")}
        self._registry = None

    def git(self, *args):
        p = subprocess.run(["git", "-C", str(self.root), *args], capture_output=True, text=True)
        if p.returncode:
            raise FamilyError(p.stderr.strip() or "cannot read git Cases tree")
        return p.stdout

    def read(self, path):
        if path not in self._texts:
            try:
                self._texts[path] = (self.git("show", f"{self.revision}:{path}") if self.revision
                                     else (self.root / path).read_text())
            except OSError as e:
                raise FamilyError(f"{path}: {e}") from e
        return self._texts[path]

    def ancestor(self, path):
        stem = PurePosixPath(path).parent
        while str(stem).startswith(CASES.rstrip("/")):
            candidate = str(stem) + ".lean"
            # Fs.lean pins the base filesystem model; Fs/ holds independent
            # syscall mirrors. This pre-existing namespace is not a split.
            if candidate in self.paths and candidate not in STANDALONE:
                return candidate
            stem = stem.parent
        return None

    def registry(self):
        if self._registry is None:
            # Only anchors can own members. Member-to-member imports are dependencies.
            self._registry = {}
            for p in sorted(self.paths):
                if self.ancestor(p) is None:
                    self._registry[p] = ["lean/" + m.replace(".", "/") + ".lean"
                                         for m in imports(self.read(p)) if m.startswith(MODULE)]
        return self._registry

    def family(self, anchor):
        if not anchor.startswith(CASES) or not anchor.endswith(".lean") or ".." in PurePosixPath(anchor).parts:
            raise FamilyError(f"{anchor}: not a Cases anchor path")
        if anchor not in self.paths:
            raise FamilyError(f"{anchor}: missing Cases anchor")
        if self.ancestor(anchor):
            raise FamilyError(f"{anchor}: nested Cases anchor")
        if anchor in self._families:
            return self._families[anchor]
        prefix = anchor[:-5] + "/"
        direct = ["lean/" + m.replace(".", "/") + ".lean"
                  for m in imports(self.read(anchor)) if m.startswith(MODULE)]
        parts = list(dict.fromkeys(p for p in direct if p.startswith(prefix)))
        if parts and anchor in STANDALONE:
            raise FamilyError(f"{anchor}: existing standalone namespace cannot become a split family")
        if parts and anchor.startswith(CASES + "Checks/"):
            raise FamilyError(f"{anchor}: splitting checker Cases is unsupported")
        unlisted = sorted(p for p in self.paths if p.startswith(prefix) and p not in parts) if anchor not in STANDALONE else []
        if unlisted:
            raise FamilyError(f"{anchor}: unimported Cases member {unlisted[0]}")
        for p in parts:
            if p not in self.paths:
                raise FamilyError(f"{anchor}: missing imported Cases member {p}")
            if self.ancestor(p) != anchor or any(q.startswith(p[:-5] + "/") for q in self.paths):
                raise FamilyError(f"{p}: nested Cases anchor")
            for mod in imports(self.read(p)):
                dep = "lean/" + mod.replace(".", "/") + ".lean"
                if dep.startswith(prefix) and dep not in parts:
                    raise FamilyError(f"{p}: member import not registered by anchor: {dep}")
            if re.search(r"rocq[-_]cases\s*:", self.read(p), re.I):
                raise FamilyError(f"{p}: rocq-cases header in member; keep the register in {anchor}")
            others = [a for a, ps in self.registry().items() if a != anchor and p in ps]
            if others:
                raise FamilyError(f"{p}: member imported by two anchors: {anchor}, {others[0]}")
        # An anchor cannot import somebody else's member even when that owner
        # has not yet been requested by the caller.
        for p in direct:
            other = self.ancestor(p)
            if other and other != anchor:
                raise FamilyError(f"{p}: member imported by two anchors: {other}, {anchor}")
        result = [anchor, *parts]
        self._families[anchor] = result
        return result

    def owner(self, path):
        if not path or not path.startswith(CASES) or not path.endswith(".lean"):
            return None
        anchor = self.ancestor(path)
        if anchor:
            members = self.family(anchor)
            if path in members:
                return anchor
            if path in self.paths:
                raise FamilyError(f"{path}: unimported Cases member")
            return None
        if path in self.paths:
            self.family(path)
            return path
        return None

    def text(self, anchor):
        return "\n".join(self.read(p) for p in self.family(anchor))

    def helpers(self, path):
        """Owned files reachable from this member (the anchor sees all members)."""
        anchor = self.owner(path)
        if not anchor:
            return [path]
        members = self.family(anchor)
        if path == anchor:
            return members
        reached, todo = set(), [path]
        while todo:
            p = todo.pop()
            if p in reached:
                continue
            reached.add(p)
            todo.extend(q for m in imports(self.read(p))
                        if (q := "lean/" + m.replace(".", "/") + ".lean") in members)
        return [p for p in members if p in reached]


def family(root, anchor_rel):
    return View(root).family(anchor_rel)


def owner(root, path):
    return View(root).owner(path)


def owner_at(root, revision, path):
    return View(root, revision).owner(path)


def touched(root, old, new, paths, enrolled):
    """Logical enrolled specs touched at either end, including removed owners."""
    selected = set()
    paths = list(paths)
    for revision in (old, new):
        view = View(root, revision)
        for path in paths:
            anchor = view.owner(path)
            if anchor:
                selected.add(anchor[len(CASES):-5].replace("/", "."))
            if path.startswith(BASE + "Sys/") and path.endswith(".lean"):
                name = path[len(BASE + "Sys/"):-5]
                selected.add(name.replace("/", "."))
    return selected & set(enrolled)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    command = sub.add_parser("touched")
    command.add_argument("--root", type=Path, default=Path.cwd())
    command.add_argument("--old", required=True)
    command.add_argument("--new", required=True)
    command.add_argument("--spec", action="append", help="logical spec to select (default: enrolled scores)")
    args = parser.parse_args()
    paths = sys.stdin.read().split("\0")
    enrolled = args.spec if args.spec is not None else (
        p.stem for p in (args.root / "tools/lean_mutation/scores").glob("*.json"))
    try:
        for name in sorted(touched(args.root, args.old, args.new, paths, enrolled)):
            print(name)
        print("lean_cases_family: touched ok")
    except FamilyError as e:
        parser.exit(1, f"{e}\n")


if __name__ == "__main__":
    main()
