#!/usr/bin/env python3
"""check_one.py — type-check one .v file against the INSTALLED model.

A full `dune build` of this repository takes about 45 CPU-minutes, and CI
takes longer still.  A new file that imports the model and has a typo in it
— a numeral read in the wrong scope, a name that stdpp also defines, a
`Proof.` with no goal, a lemma that does not exist — fails in the first
second of its own compile.  This script gets you that first second without
building anything: it hands the file to `rocq compile` against the model
that opam already installed, and prints the compiler's own message.

    python3 tools/check_one.py theories/LinuxProcessSem/Procs.v

One file takes about a second once the model is installed: the cost is
loading the .vo files your file imports, not building anything.

Nothing is written into your working tree: the .vo goes to a scratch
directory that the script removes.  The exit status is 0 only when every
file given compiled.

WHICH MODEL ANSWERED IS THE WHOLE ANSWER.  This script compiles your file
against an installed library.  If that library is a different revision of
the model from the one your file will be read against, you do not get an
error: you get an ANSWER, and it is the wrong one.  More than one image of
this model exists at a time — one carrying the last released pin, one
built from the revision head — and they disagree about the start state,
the memory-mapping rules, the socket arms, the `valid_input` accessors and
the order of the launch predicate.  A file that uses any of those compiles
clean against one and not the other.

So the script never picks for you.  It has NO default image: either you
stand in a switch and it uses that switch, or you name an image.  Before
it compiles anything inside an image it works out which revision of the
model that image carries — from the image's `org.theorem.lps.commit` or
`org.opencontainers.image.revision` label, and failing that by hashing
the model sources the image installed and matching them against the
commits of this repository, which a missing or wrong label cannot defeat.
It prints that commit, and it says how the commit sits against your HEAD:
an ancestor of your work, ahead of your work, or — the case to watch —
neither, which means your branch and that image are on different lines of
development, and the answer you get is about a model your file will never
be read against.  An image whose model it cannot identify is refused.

The difference between two models is not always a missing lemma that
fails loudly.  Measured between the two images that exist today:
`State.mkProcState` takes TWELVE fields on `main` and FIFTEEN on the
revision line, so the same constructor application is complete on one
and partial on the other.  AN ARITY ERROR ON A CONSTRUCTOR SUCH AS
`mkProcState` USUALLY MEANS THE IMAGE'S MODEL IS NOT THE LINE YOU WROTE
AGAINST, NOT THAT YOUR FILE IS WRONG.  Read the printed model commit
against the commit your file is based on BEFORE you read the error.

Today neither image carries `main`: one carries the released pin, one the
revision head, and the revision head is NOT an ancestor of `main`.  So an
author working from `main` has no exact image, and the script says so for
them — it prints the ancestry rather than leaving it to be guessed.

HOW TO IDENTIFY AN IMAGE NOBODY LABELLED.  Of the eight versions of the
checker image in the registry today, exactly one carries the label, and
it is the revision line.  That proportion will be true again, so here is
the method, which the script also runs for you: hash every model source
the image installed, the way git hashes a blob, and match the set against
the commits of this repository.  201 files identified the released-pin
image as a single commit, all 201 matching and none differing, and
`git merge-base --is-ancestor <that commit> main` then said whether it is
on your line.  A label can be absent or wrong; the sources cannot.  Where
you have established the commit some other way, `--model-commit SHA`
asserts it, and the output then records that you asserted it rather than
that the image said it.

IN A CONTAINER.  `--image IMAGE` (or CHECK_ONE_IMAGE=IMAGE) runs the same
check inside that image.  The working directory is mounted read-only at
the same path, so every file you name must be under it, and the check
still cannot write to your tree.

    python3 tools/check_one.py --image IMAGE theories/LinuxProcessSem/Procs.v

WHAT IT CHECKS.  Each file is compiled on its own, with the default load
path, so `From LinuxProcessSemantics... Require Import ...` resolves to the
library under COQLIB/user-contrib — the one `opam install` put there.  This
is the same way CI's `opam install` lane uses the installed packages (see
.github/workflows/ci.yml).  So the case it is for is the case it is good
at: a NEW file, not yet part of any package, that imports the model.

It reads the warning flags out of the project's top-level `dune` and
passes them, so a deprecation that the build makes an error — this
repository makes `Notation ident := term` one — is an error here too.

WHAT IT CANNOT CATCH.  State this to anyone you hand it to.

  * It checks against the INSTALLED library, never against your working
    tree.  A lemma you just added to theories/Riscv/Prelude.v is invisible
    here, and one you just deleted still resolves.  A green check on an
    EDITED file that the library already contains means almost nothing.
    Read that limit again if you are working a revision: a revision whose
    changes are mostly edits to files the library already has gets nothing
    from this script for those files — not a weaker answer, no answer.
    What it does reach there are the new, self-contained witness files,
    theories/LinuxProcessSem/Checks/Cases/ above all, which are many and
    are each a file of their own.  That is the real audience.
  * It does not check one new file against another new file of the same
    branch: each file is compiled alone, and a `Require` of a module that
    only your branch has will not resolve.
  * It compiles only the files you name.  A change of yours that breaks
    some later file of the repository passes here.
  * A switch or image can carry one package of the four and not the
    others.  The checker images carry `rocq-linux-process-semantics-core`
    alone, so nothing under theories/Common/ or theories/Examples/ can be
    checked against them: a file importing LinuxProcessSemantics.Common
    or .Examples is reported NOT CHECKED, and counted as a failure,
    rather than compiled into a missing-file error.
  * It does not run the rest of CI: tools/gen_checker.py --check/--verify,
    .github/check_assumptions.py (which is what audits the axioms of a
    proof), tools/test_elf_snapshot.py, or the Rocq 9.3 and dev lanes.
  * Your switch is not CI's.  A file that needs a package you installed and
    CI does not passes here and fails there.
  * It reads the top-level `dune` only.  A per-directory `dune` that sets
    other flags, and anything a dune rule generates before the build (for
    example theories/BridgeDeps.v), is not accounted for.

It is a spell checker, not the build.  `dune build` is still the thing that
says the repository is sound.

WHICH FAILURES IT REACHES.  It reaches the ones the compiler decides by
reading the file: a tactic that names a constant defined sixty lines
below it, a numeral in the wrong scope, a shadowed name, an orphan
`Proof.`, a lemma that does not exist.  It comes back in a second with
the compiler's own message.  It does not reach what only running the
proof finds: a file that works for seven minutes and then dies on a
signal, one that exhausts memory, one that takes an hour.  Those need the
build, with the time and the memory the build has.  Knowing which of the
two a failure is, before you spend forty minutes on it, is the point.

HINTS.  Beside a failure the check adds a line for a mistake this
repository produces again and again, whose message is accurate but does
not name the cause.  Five so far: a numeral read in `bv_scope` where `Z`,
`positive` or `nat` was wanted, which is the most repeated of all and is
fixed by writing the scope (`0x1101c%Z`); a name that is stdpp's rather
than Stdlib's, `filter` above all, which does not announce the shadowing;
a `bv_eqb` lemma that does not exist, because Riscv/Prelude.v defines the
function and nothing about it; a `Proof.` with no goal; and an inversion
pattern short of branches, where the fact wanted is that every
constructor needs one, including the arms the conclusion rules out.

A hint is keyed to WHAT THE COMPILER SAID, never to what the source looks
like, and it never changes the verdict.  That is deliberate: `0x1101c` as
a bit-vector literal and `0x1101c` where a `Z` was wanted are the same
characters, so a lint that read the source would have to guess, and a
guess that cries wolf costs more than the error it replaces.  The
elaborated type is not a guess.  A correct file gets no hint because it
gets no failure.

What earns a hint: the message is accurate, and the fact the reader needs
is not in it.  What does not: a message whose cause lies in the proof's
history rather than in the error.  `Found no subterm matching` is the
standing example — an earlier `cbn` may have consumed the occurrence —
and a hint there would guess at what happened before, which is the thing
this design refuses to do.

ON THE EXIT STATUS.  `rocq compile` (and `coqc`) exit 1 when a command
fails, so for a compiler the exit status is the whole answer, and this
script reads nothing else: a valid file that prints a line starting with
`Error:` of its own accord (`idtac "Error: ..."`) still passes.  A repl is
the opposite: `rocq repl` and `coqtop` exit 0 even when a command failed
and printed `Error:` (measured: exit 0 with two `Error:` lines of output),
so a check built on one that reads only the exit status reports success on
a broken file.  If you point --rocq at a repl, this script therefore also
fails the file on an `Error:` line.  Either way it never reports success
on a failed command.

ON NATIVE COMPILATION.  The images this repository is checked in set
COQ_NATIVE_COMPILER_DEFAULT=no (`rocq c -config`), so nothing here builds
native code: proofs that compute do so through vm_compute, and the timings
you see are the bytecode ones.

WHAT A CALLER MUST TEST.  The last line of every run is a fixed token:

    CHECK-ONE-RESULT: pass
    CHECK-ONE-RESULT: fail

Test THAT, not the exit status alone.  The exit status cannot tell you
that this program ran: a truncated or empty copy of it — a redirect that
created the file before the command that was to fill it failed, which has
happened — is a valid Python program that does nothing and exits 0, and a
caller reading only the status calls that a pass.  The token is printed
on every path out, including a refusal and a crash, so its ABSENCE means
the check did not run.

    python3 tools/check_one.py FILE.v | tee /dev/stderr | \
        grep -qx 'CHECK-ONE-RESULT: pass'

A run inside an image prints the token twice, once from the copy in the
container and once from the copy you started; they always agree, and
neither is suppressed, because a mechanism that silences the token is
the defect this token exists to catch.

The same reasoning as the model gate above: an instrument that cannot say
what it measured must not be read as having measured anything.
"""

from __future__ import annotations

import argparse
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import time

# A file of the installed theory. Its presence is what tells us that
# `opam install rocq-linux-process-semantics-core` has happened in this
# switch, which is the one prerequisite the check has.
INSTALLED_MARKER = os.path.join("user-contrib", "LinuxProcessSemantics")

# The last line of every run, and the only thing a caller should test.
# Fixed, so a machine reader asserts on a token rather than on prose that
# may be reworded: `CHECK-ONE-RESULT: pass` or `CHECK-ONE-RESULT: fail`.
RESULT_PREFIX = "CHECK-ONE-RESULT:"


def rocq_command(explicit: str | None) -> list[str]:
    """The command that compiles a file: `rocq compile`, or `coqc`."""
    if explicit:
        return shlex.split(explicit)
    if shutil.which("rocq"):
        return ["rocq", "compile"]
    if shutil.which("coqc"):
        return ["coqc"]
    sys.exit(
        "check_one.py: found neither `rocq` nor `coqc` on PATH.\n"
        "  Run inside the opam switch that has the model installed, for\n"
        "  example `opam exec -- python3 tools/check_one.py <file.v>`."
    )


def coqlib(rocq: list[str]) -> str | None:
    """COQLIB, read from the compiler itself (`rocq c -config`)."""
    try:
        out = subprocess.run(
            rocq + ["-config"], capture_output=True, text=True, timeout=120
        ).stdout
    except (OSError, subprocess.SubprocessError):
        return None
    for line in out.splitlines():
        key, _, value = line.partition("=")
        if key.strip() == "COQLIB":
            return value.strip()
    return None


# The theory each opam package installs under LinuxProcessSemantics/. An
# image or switch can carry one package and not the others: the checker
# images carry `-core` alone, so a file that imports the proof library or
# an example cannot be checked against them at all.
SUBTHEORIES = {
    "Common": "rocq-linux-process-semantics-common",
    "Examples": "rocq-linux-process-semantics-examples",
}


def check_installed(rocq: list[str]) -> str:
    """Fail now, with the reason, rather than inside every file's errors.

    Returns the directory the model is installed in.
    """
    lib = coqlib(rocq)
    if lib is None:
        sys.exit(
            "check_one.py: `%s -config` did not report COQLIB; is the\n"
            "  compiler usable in this switch?" % " ".join(rocq)
        )
    model = os.path.join(lib, INSTALLED_MARKER)
    if not os.path.isdir(model):
        sys.exit(
            "check_one.py: the model is not installed in this switch.\n"
            "  Looked for: %s\n"
            "  Install it:  opam install rocq-linux-process-semantics\n"
            "  (From a clone: opam pin add --no-action . && opam install\n"
            "  rocq-linux-process-semantics.)" % model
        )
    absent = sorted(name for name in SUBTHEORIES
                    if not os.path.isdir(os.path.join(model, name)))
    if absent:
        print(
            "check_one.py: this switch has the core package only. %s %s not\n"
            "  installed (%s), so a file that imports %s cannot be checked\n"
            "  here at all."
            % (" and ".join(absent),
               "is" if len(absent) == 1 else "are",
               ", ".join(SUBTHEORIES[name] for name in absent),
               " or ".join("LinuxProcessSemantics." + name
                           for name in absent)),
            flush=True,
        )
    return model


def needs_absent_theory(path: str, model: str) -> str | None:
    """The sub-theory a file imports that this switch does not have."""
    try:
        with open(path, encoding="utf-8", errors="replace") as handle:
            text = handle.read()
    except OSError:
        return None
    for name in sorted(SUBTHEORIES):
        if ("LinuxProcessSemantics." + name) in text and not os.path.isdir(
                os.path.join(model, name)):
            return name
    return None


def is_repl(rocq: list[str]) -> bool:
    """True when the configured command is a repl, not a compiler."""
    return any(part in ("repl", "coqtop", "rocqtop") for part in rocq)


def env_flags(dune: str) -> list[str]:
    """The tokens of the (flags ...) field of a dune file's (env ...)."""
    try:
        with open(dune, encoding="utf-8") as handle:
            text = handle.read()
    except OSError:
        return []
    # dune comments run from ';' to the end of the line.
    text = "\n".join(line.split(";", 1)[0] for line in text.splitlines())
    start = text.find("(flags")
    if start < 0:
        return []
    depth = 0
    for end, char in enumerate(text[start:], start):
        depth += (char == "(") - (char == ")")
        if depth == 0:
            break
    else:
        return []
    tokens = text[start + len("(flags") : end].split()
    return [t for t in tokens if t != ":standard"]


def project_flags(path: str) -> list[str]:
    """The warning flags the dune build gives every theory of this project.

    Read from the project's own top-level `dune`, not copied into this
    script, so the check cannot drift from the build: the repository makes
    `Notation ident := term` an error there, and it must be an error here.
    A per-directory `dune` that overrides them is not read.
    """
    directory = os.path.dirname(os.path.abspath(path))
    while True:
        if os.path.isfile(os.path.join(directory, "dune-project")):
            return env_flags(os.path.join(directory, "dune"))
        parent = os.path.dirname(directory)
        if parent == directory:
            return []
        directory = parent


# A hint is keyed to what the COMPILER said, never to what the source
# looks like.  That is the whole design: `0x1101c` and a genuine
# bit-vector literal are the same characters, so a syntactic lint would
# guess and be wrong; the elaborated type is not a guess.  A hint is
# printed only beside a failure, and it never changes the verdict.
#
# Each entry is for a mistake this repository produces repeatedly, whose
# message is accurate but does not name the cause.
HINTS = (
    (r'has type "[^"]*bv \?n[^"]*" while it is expected to have type',
     "a bare numeral in this position was read in bv_scope, which\n"
     "    Riscv/Prelude.v opens, so it elaborated as a bit-vector rather\n"
     "    than the type wanted. Write the scope: 0x1101c%Z, 12%positive,\n"
     "    3%nat."),
    (r"Cannot infer the implicit parameter n of BV",
     "a bare numeral was read in bv_scope and its width cannot be\n"
     "    inferred here. Write the scope you mean (%Z, %positive, %nat),\n"
     "    or give the width."),
    (r"Decision \(",
     "this is stdpp's function, not Stdlib's: stdpp.base, which\n"
     "    Riscv/Prelude.v exports through the bitvector library, shadows\n"
     "    several Stdlib names (`filter` above all). stdpp's takes a\n"
     "    Prop-valued predicate and a Decision instance. Qualify it:\n"
     "    List.filter."),
    (r'The variable (bv_\w+) was not found',
     "Riscv/Prelude.v defines bv_eqb and no lemmas about it, so\n"
     "    bv_eqb_refl and bv_eqb_eq do not exist. Unfold bv_eqb and use\n"
     "    Z.eqb_refl or Z.eqb_eq."),
    (r"No proof-editing in progress",
     "a Proof., Qed. or tactic with no goal open: usually a second\n"
     "    Proof. block left after the proof above it was completed."),
    (r"Expects a disjunctive pattern with (\d+) branches",
     "an inversion pattern must have one branch per CONSTRUCTOR of the\n"
     "    relation, not one per case that can occur: the arms your\n"
     "    conclusion already rules out still need a branch. Drop the `as`\n"
     "    clause, or name the missing arms. A count that changed under you\n"
     "    means the relation gained or lost a constructor."),
)


def hints_for(output: str) -> list[str]:
    """The hints whose compiler message appears in this file's output."""
    return [text for pattern, text in HINTS if re.search(pattern, output)]


def check_file(path: str, rocq: list[str], scratch: str, timeout: int) -> bool:
    """Compile one file. Print what the compiler said. True when it passed."""
    out_vo = os.path.join(scratch, os.path.basename(path)[:-2] + ".vo")
    # -q: ignore the user's rcfile, so the check does not depend on it.
    # -noglob and -o: write nothing beside the source.
    argv = rocq + project_flags(path) + ["-q", "-noglob", "-o", out_vo, path]
    print("$ " + " ".join(shlex.quote(a) for a in argv), flush=True)
    started = time.monotonic()
    try:
        proc = subprocess.run(
            argv, capture_output=True, text=True, timeout=timeout
        )
    except subprocess.TimeoutExpired:
        print("%s: FAIL (no answer in %ds)" % (path, timeout))
        return False
    elapsed = time.monotonic() - started
    output = (proc.stdout or "") + (proc.stderr or "")
    sys.stdout.write(output)
    if output and not output.endswith("\n"):
        sys.stdout.write("\n")
    # A compiler's exit status decides, and nothing else: a valid file may
    # print a line that starts with `Error:` of its own accord (`idtac
    # "Error: ..."`), and that is not a failure.  A repl exits 0 over a
    # failed command, so for a repl the text is all there is: then, and
    # only then, an `Error:` line is a failure.
    ok = proc.returncode == 0
    if ok and is_repl(rocq):
        ok = not any(line.startswith("Error:") for line in output.splitlines())
    print(
        "%s: %s in %.1fs (exit %d)"
        % (path, "OK" if ok else "FAIL", elapsed, proc.returncode),
        flush=True,
    )
    if not ok:
        for hint in hints_for(output):
            print("  hint: %s" % hint, flush=True)
    return ok


# The labels an image of this model carries. The first is the one this
# repository's images set; the second is the OCI standard field that a
# build sets from the source commit.
MODEL_COMMIT_LABELS = ("org.theorem.lps.commit", "org.opencontainers.image.revision")


def label_commit(docker: str, image: str) -> str | None:
    """The LPS commit an image's labels claim, or None when they claim none."""
    template = "".join("{{index .Config.Labels %s}}\n" % '"%s"' % label
                       for label in MODEL_COMMIT_LABELS)
    proc = subprocess.run(
        [docker, "image", "inspect", "--format", template, image],
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        sys.exit(
            "check_one.py: cannot inspect %s:\n%s"
            % (image, (proc.stderr or "").strip())
        )
    for line in proc.stdout.splitlines():
        value = line.strip()
        if value and value != "<no value>":
            return value
    return None


# Reads the model sources the image installed and prints one
# `<git blob sha1> <path>` line each, which is what `git ls-tree -r` prints
# for the commit they came from.
FINGERPRINT = r"""
import hashlib, os, sys
roots = [p for p in ("/home/opam/lps", os.environ.get("LPS_SOURCE", ""))
         if p and os.path.isdir(p)]
if not roots:
    sys.exit(3)
root = roots[0]
for base, _, files in os.walk(root):
    for name in files:
        full = os.path.join(base, name)
        with open(full, "rb") as handle:
            data = handle.read()
        head = ("blob %d" % len(data)).encode() + b"\0"
        print(hashlib.sha1(head + data).hexdigest(),
              os.path.relpath(full, root))
"""


def git(repo: str, *argv: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["git", "-C", repo, *argv], capture_output=True, text=True
    )


def fingerprint_commit(docker: str, image: str, repo: str) -> str | None:
    """The commit whose tree the image's installed model sources are.

    A label can be absent or wrong; the sources cannot.  Every file the
    image installed is hashed the way git hashes a blob, and the result is
    matched against the commits of this repository.  The answer is cached
    in the git directory, because it cannot change for a given image.
    """
    # In a worktree .git is a file, not a directory, so ask git where its
    # directory actually is rather than assuming.
    gitdir = git(repo, "rev-parse", "--absolute-git-dir").stdout.strip()
    cache = os.path.join(gitdir, "check-one-images") if gitdir else ""
    key = os.path.join(cache, image.rsplit(":", 1)[-1][:64] + ".txt") if cache else ""
    if key and os.path.isfile(key):
        with open(key, encoding="utf-8") as handle:
            found = handle.read().strip()
        return found or None
    proc = subprocess.run(
        [docker, "run", "--rm", "--network", "none", image,
         "python3", "-c", FINGERPRINT],
        capture_output=True,
        text=True,
    )
    blobs = {}
    for line in proc.stdout.splitlines():
        sha, _, path = line.partition(" ")
        if path:
            blobs[path] = sha
    found = None
    if blobs:
        # One file decides the candidates; the whole set confirms one.
        witness = max(blobs, key=lambda p: (p.endswith(".v"), len(p)))
        for commit in git(repo, "log", "--all", "--format=%H", "--",
                          witness).stdout.split():
            if git(repo, "rev-parse", "%s:%s" % (commit, witness)
                   ).stdout.strip() != blobs[witness]:
                continue
            tree = {}
            for line in git(repo, "ls-tree", "-r", "--format=%(objectname) "
                            "%(path)", commit).stdout.splitlines():
                sha, _, path = line.partition(" ")
                tree[path] = sha
            if all(tree.get(p) == sha for p, sha in blobs.items()):
                found = commit
                break
    if key:
        try:
            os.makedirs(cache, exist_ok=True)
            with open(key, "w", encoding="utf-8") as handle:
                handle.write(found or "")
        except OSError:
            pass
    return found


def ancestry(repo: str, commit: str) -> str:
    """How the model you are about to answer from sits against your work."""
    head = git(repo, "rev-parse", "HEAD").stdout.strip()
    if not head:
        return "  This is not a git checkout, so nothing was compared."
    if head.startswith(commit) or commit.startswith(head):
        return "  It is exactly what you have checked out."
    older = git(repo, "merge-base", "--is-ancestor", commit, head).returncode == 0
    newer = git(repo, "merge-base", "--is-ancestor", head, commit).returncode == 0
    if older:
        return ("  It is an ancestor of your HEAD (%s): older than your work,\n"
                "  on the same line of development." % head[:8])
    if newer:
        return ("  Your HEAD (%s) is an ancestor of it: this model is ahead of\n"
                "  your work, on the same line of development." % head[:8])
    return (
        "  WARNING: neither it nor your HEAD (%s) is an ancestor of the other.\n"
        "  Your branch and this image are on DIFFERENT lines of development.\n"
        "  A file can be right on one and wrong on the other, and what you\n"
        "  get here is an answer, not an error. Use an image whose model is\n"
        "  an ancestor of your base." % head[:8]
    )


def run_in_image(image: str, args: argparse.Namespace) -> int:
    """Re-run this script inside a container that has the model installed."""
    docker = shutil.which("docker")
    if docker is None:
        sys.exit("check_one.py: --image needs `docker` on PATH.")
    repo = os.path.realpath(os.getcwd())
    # Which model answered is the whole answer, so an image whose model
    # cannot be identified is refused: that is the very case this check
    # exists for, a silent wrong answer rather than an error. A commit the
    # caller asserts is not unknown, it is attributed, so it satisfies the
    # gate — and the output says which of the three it was, because a
    # reader keeps that line.
    commit, how = args.model_commit, "ASSERTED BY THE CALLER; the image does not say so"
    if commit is None:
        commit = label_commit(docker, image)
        how = "as %s labels it" % image
    if commit is None:
        commit = fingerprint_commit(docker, image, repo)
        how = ("identified by hashing the model sources the image installed;"
               "\n  the image does not say so")
    if commit is None:
        sys.exit(
            "check_one.py: cannot tell which revision of the model %s\n"
            "  carries. It has no %s label, and the sources it installed\n"
            "  match no commit of this repository. This check will not\n"
            "  answer from an unknown model: a wrong one returns a wrong\n"
            "  answer, not an error. Fetch the missing commits, pass\n"
            "  --model-commit SHA if you have established it another way,\n"
            "  or stand in a switch that has the model installed and drop\n"
            "  --image." % (image, " or ".join(MODEL_COMMIT_LABELS))
        )
    print(
        "check_one.py: answering from the model at %s, %s.\n%s"
        % (commit, how, ancestry(repo, commit)),
        flush=True,
    )
    root = os.path.realpath(os.getcwd())
    script = os.path.realpath(__file__)
    inside = []
    for path in args.files:
        real = os.path.realpath(path)
        if os.path.commonpath([root, real]) != root or real == root:
            sys.exit(
                "check_one.py: --image mounts the working directory only, and\n"
                "  %s resolves outside it (%s). Run the check from a\n"
                "  directory that contains every file you name." % (path, real)
            )
        # What the container gets is the path inside the mount, so a name
        # that reached its file through a symlinked directory still names
        # the same file there.
        inside.append(os.path.relpath(real, root))
    mounts = ["-v", "%s:%s:ro" % (root, root)]
    if os.path.commonpath([root, script]) != root:
        mounts += ["-v", "%s:%s:ro" % (script, script)]
    inner = ["python3", script, "--timeout", str(args.timeout)]
    if args.rocq:
        inner += ["--rocq", args.rocq]
    argv = (
        [docker, "run", "--rm", "--network", "none"]
        + mounts
        + ["-w", root, image]
        + inner
        + ["--"]
        + inside
    )
    print("$ " + " ".join(shlex.quote(a) for a in argv), flush=True)
    return subprocess.run(argv).returncode


def positive_int(text: str) -> int:
    value = int(text)
    if value < 1:
        raise argparse.ArgumentTypeError("must be a whole number of seconds, at least 1")
    return value


def main() -> int:
    parser = argparse.ArgumentParser(
        prog="check_one.py",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("files", metavar="FILE.v", nargs="+", help="the files to check")
    parser.add_argument(
        "--rocq",
        metavar="CMD",
        help="the compiler to run (default: `rocq compile`, else `coqc`)",
    )
    parser.add_argument(
        "--image",
        metavar="IMAGE",
        default=os.environ.get("CHECK_ONE_IMAGE"),
        help="run the check inside this container image instead of this "
        "switch (or set CHECK_ONE_IMAGE). There is NO default: an image "
        "carries one revision of the model, and the wrong one returns a "
        "wrong answer rather than an error. The check identifies the model "
        "the image carries, prints it, and says how it sits against your "
        "HEAD, before it compiles anything. The working directory is "
        "mounted read-only at the same path",
    )
    parser.add_argument(
        "--model-commit",
        metavar="SHA",
        help="the commit of the model the image carries, when you have "
        "established it another way; skips the identification",
    )
    parser.add_argument(
        "--timeout",
        metavar="SECONDS",
        type=positive_int,
        default=900,
        help="give up on a file after this long (default: 900)",
    )
    args = parser.parse_args()

    for path in args.files:
        if not path.endswith(".v"):
            sys.exit("check_one.py: %s is not a .v file." % path)
        if not os.path.isfile(path):
            sys.exit("check_one.py: %s does not exist." % path)

    if args.image:
        return run_in_image(args.image, args)

    rocq = rocq_command(args.rocq)
    model = check_installed(rocq)

    failed = []
    with tempfile.TemporaryDirectory(prefix="check-one-") as scratch:
        for path in args.files:
            absent = needs_absent_theory(path, model)
            if absent:
                # Compiling would report a missing file and leave the
                # reader to work out why. Say it instead: this switch
                # cannot answer for this file, which is not the same as
                # the file being wrong.
                print(
                    "%s: NOT CHECKED. It imports LinuxProcessSemantics.%s,\n"
                    "  which this switch does not have (%s). Install that\n"
                    "  package, or use a switch or image that carries it."
                    % (path, absent, SUBTHEORIES[absent]),
                    flush=True,
                )
                failed.append(path)
                continue
            if not check_file(path, rocq, scratch, args.timeout):
                failed.append(path)
    if failed:
        print("\ncheck_one.py: %d of %d failed: %s"
              % (len(failed), len(args.files), " ".join(failed)))
        return 1
    print("\ncheck_one.py: %d of %d passed (against the INSTALLED model; "
          "`dune build` still decides the repository)."
          % (len(args.files), len(args.files)))
    return 0


if __name__ == "__main__":
    # The verdict line, not the exit status, is the contract. A process
    # that never ran this program — an empty or truncated copy of it, a
    # shell redirect that created the file before the command that was to
    # fill it failed — exits 0 and says nothing, and a caller that reads
    # only the status calls that a pass. So every path out of this program
    # prints the verdict, including a refusal and a crash, and a caller
    # asserts that the line is there.
    status = 1
    try:
        status = main()
    except SystemExit as exit_request:
        code = exit_request.code
        if isinstance(code, int) or code is None:
            status = code or 0
        else:
            print(code, file=sys.stderr)
            status = 1
    finally:
        print("%s %s" % (RESULT_PREFIX, "pass" if status == 0 else "fail"),
              flush=True)
    sys.exit(status)
