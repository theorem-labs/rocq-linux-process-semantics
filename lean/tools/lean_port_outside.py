#!/usr/bin/env python3
"""The work the plan does not name: PRs and windows with no ticket, grouped by what they are.

A third of the day's merges are not plan tickets -- fixes the back-review found in arms
already ported, the guards Q11 added, the ops kit, CI, the generated pages.  Until this page
existed that work was invisible: the plan's ticket table did not hold it and the derivation
reported each one as a contradiction, so the site said "112 contradictions" where it should
have said "91 pieces of work nobody planned and everybody did".

The rule this page rests on: **an unmapped PR is not a contradiction.**  A contradiction is a
real inconsistency between sources -- a merged PR whose arm is not in the table, a ticket the
sources once called done and no longer do.  A PR with no plan ticket is a fact about the plan,
not a fault in the derivation, and the answer to it is to show the work, not to hide it behind
a number nobody can act on.  What this page must never do is disagree with the derivation
about WHICH PRs have a ticket: the attribution is lean_port_state.py's alone, and everything
here keys off the `ticket` field it wrote.

THE KINDS, decided by the head branch first and the title's component second.  The branch is
what the launcher chose and the title is what the author typed, so the branch is the more
reliable of the two -- `tests/guard-lean-build-visible` is a guard however its title begins,
and it begins `ci:`.  The title's component is the word before its first colon, which
AGENTS.md pins to `component: action`, so reading it is reading the repository's own
convention rather than guessing at prose.

  fix      a fix to an arm already ported (lean/fix-*, or a `lean: fix:` title)
  port     Lean port work with no plan ticket: a base change, a pins file, an example
           repair.  This group is the one that should shrink -- every row in it is work the
           attribution could claim, and a row that stays is a ticket the plan is missing.
  guard    a guard or a test added to catch a class of mistake (tests/*)
  kit      the ops kit and the process it runs (tools/*, process/*)
  ci       the workflows and the merge gate's plumbing (ci/*)
  docs     the pages, the briefs and the prose (docs/*, `comments:`)
  model    the Rocq model's own work, which is not the Lean port at all: an `lps-*` branch,
           or a `spec:`/`syscalls:`/`riscv:`/`testing:`/`bugs:` component.  It shares the day
           branch and the merge gate, so it is in the day's totals and in nobody's port
           ticket, correctly
  other    anything the rules above do not name -- listed, never folded into a neighbour

THE SUBJECT of a fix is the arm it repairs: the longest arm name the branch slug contains,
which is how the fix branches are named (`lean/fix-mmap-span-pins-and-min-addr-premise` ->
mmap).  A slug naming no arm has no subject rather than a guessed one.

WINDOWS are grouped the same way, over the windows the derivation could not map to a ticket
(`kind: "other"`) and the ones it filed as back-review or fix windows (`kind: "review"`): an
integration window, a process ticket that was never added to the plan (SEC1, PA5, P13), or
something else.  Service windows are the kit's jobs and belong on the Machines page, not
here; ticket and deep-review windows belong to their ticket or PR.
"""
import argparse
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lean_port_state as state  # noqa: E402
import lean_port_time as ptime  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DOCS = os.path.join(ROOT, "docs", "lean-port")
DATA = os.path.join(DOCS, "data")
OUTSIDE = os.path.join(DATA, "outside.json")

# The derivation's contradiction kinds this page answers, and so removes from the self-check.
# The filter lives here rather than in the self-check because this page is the reason it is
# sound: an unmapped PR stops being a contradiction exactly when something shows it instead --
# so `real_contradictions` removes one of these only when the PR or window it names IS a row
# of this page, and keeps it otherwise.  Delete a name from this tuple and the self-check counts
# it again, which is the right move the day the attribution can claim every PR.
#
# What the filter removes today is narrower than its name: since the derivation stopped calling
# every unmapped PR a contradiction, a "PR with no ticket" is raised only for an open PR that
# changes a Lean spec, registry or pins file and names no ticket and no arm.  Those are the
# `port` rows below -- Lean port work the plan has no ticket for -- and the self-check says so.
OUTSIDE_KINDS = ("PR with no ticket", "window with no ticket")
# The window kinds this page lists: the ones the derivation could not map to a ticket (`other`)
# and the back-review and fix windows it files as `review`.  Service windows are the kit's jobs
# and belong on the Machines page; ticket and deep-review windows belong to their ticket or PR.
WINDOW_KINDS = ("other", "review")

KINDS = state.OUTSIDE_KIND_NAMES
KIND_LABEL = {"fix": "fixes to ported arms", "port": "Lean port work with no ticket",
              "guard": "guards and tests", "kit": "kit and process", "ci": "CI",
              "docs": "docs and pages", "model": "the Rocq model, not the port", "other": "everything else"}
KIND_BLURB = {
    "fix": "what a review found wrong in an arm that had already merged",
    "port": "a base change, a pins file, an example repair: work the attribution could claim, and a ticket the plan is missing",
    "guard": "a check that refuses the next instance of a mistake",
    "kit": "the coordinator's scripts, the launcher, the gate, the process",
    "ci": "the workflows and the required contexts",
    "docs": "these pages, the briefs, the prose and the citations",
    "model": "the Rocq development's own work; it shares the day branch and the gate, and belongs to no port ticket",
    "other": "work none of the rules above names; read the title",
}
# The classifier is the derivation's (lean_port_state.outside_kind); these names are kept so a
# reader of this file finds the rule where the docstring describes it.
BRANCH_KIND = state.BRANCH_KIND
TITLE_KIND = state.TITLE_KIND
WINDOW_GROUPS = (("review", re.compile(r"^(?:review|fix|finish|review-back)-")),
                 ("integration", re.compile(r"^(?:integrate|nightly|day)-")),
                 ("process", re.compile(r"^[A-Z][A-Za-z0-9]*\d+[a-z]?$")))
WINDOW_GROUP_LABEL = {"review": "back-review and fix windows", "integration": "day-branch integration",
                      "process": "process tickets the plan never held", "other": "everything else"}


def _pr_number(subject):
    m = re.match(r"^#(\d+)$", str(subject or "").strip())
    return int(m.group(1)) if m else None


def real_contradictions(st):
    """The derivation's contradictions minus the ones this page answers.

    A "PR with no ticket" leaves the self-check only when that PR is a row of this page (the
    derivation gave it no ticket), and a "window with no ticket" only when the window is one this
    page lists; a contradiction of either kind naming something this page does not show stays
    counted, so the filter cannot hide more than the page shows.  What is left is an inconsistency
    between two sources that cannot both be right -- a merged PR whose arm is not in the table, a
    ticket the sources called done and no longer do -- and the target for that number is zero."""
    st = st or {}
    shown_prs = {p.get("number") for p in st.get("prs") or [] if not p.get("ticket")}
    shown_windows = {w.get("window") for w in st.get("windows") or [] if w.get("kind") in WINDOW_KINDS}
    out = []
    for c in st.get("contradictions") or []:
        kind, subject = c.get("kind"), c.get("subject")
        if kind == "PR with no ticket" and _pr_number(subject) in shown_prs:
            continue
        if kind == "window with no ticket" and subject in shown_windows:
            continue
        out.append(c)
    return out


def hidden_contradictions(st):
    """The contradictions `real_contradictions` leaves out, for the self-check to name rather than count."""
    left = {id(c) for c in real_contradictions(st)}
    return [c for c in (st or {}).get("contradictions") or [] if id(c) not in left]


# The kind of an unmapped PR is the derivation's answer, computed once, in lean_port_state.
kind_of = state.outside_kind


def subject_of(pr, arms):
    """The arm a PR touches, or None.

    The longest matching arm name wins, so `fix-fstat-...` is not read as `stat` where both
    are arms.  Word boundaries are the slug's hyphens and underscores: a slug containing
    `readv` must not answer `read`."""
    head = (pr.get("head") or pr.get("branch") or "")
    tokens = set(re.split(r"[/_-]+", head.lower()))
    hits = sorted((a for a in arms if a.lower() in tokens), key=len, reverse=True)
    return hits[0] if hits else None


def window_group(name):
    for group, rx in WINDOW_GROUPS:
        if rx.match(name or ""):
            return group
    return "other"


def pr_rows(st, arms):
    """Every PR the derivation mapped to no ticket, newest first, with its kind and subject."""
    out = []
    for p in st.get("prs") or []:
        if p.get("ticket"):
            continue
        out.append(dict(number=p["number"], title=p.get("title") or "", branch=p.get("head"), url=p.get("url"),
                        state="merged" if p.get("merged") else p.get("state") or "open",
                        merged_at=p.get("merged_at"), created=p.get("created"), base=p.get("base"),
                        kind=kind_of(p), subject=subject_of(p, arms), author=p.get("author"),
                        windows=p.get("windows") or [], queue=p.get("queue"),
                        additions=p.get("additions", 0), deletions=p.get("deletions", 0)))
    out.sort(key=lambda r: -r["number"])
    return out


def window_rows(st):
    """Every live window the derivation mapped to no ticket and did not call a service window:
    its `other` windows and its `review` windows (the back-review and fix windows, which the
    `review` group below exists for and which a filter on `other` alone dropped)."""
    out = []
    exported = (st.get("freshness") or {}).get("windows")
    for w in st.get("windows") or []:
        if w.get("kind") not in WINDOW_KINDS:
            continue
        out.append(dict(window=w.get("window"), group=window_group(w.get("window")), host=w.get("host"),
                        state=w.get("state"), branch=w.get("branch"), pr=w.get("pr"),
                        worktree=w.get("worktree"), effort=w.get("effort"),
                        last_line=ptime.pacific_clocks(w.get("last_line"), exported)))
    out.sort(key=lambda r: (r["group"], r["window"] or ""))
    return out


def by_day(st, days=10):
    """Merges per UTC day over every PR, split into plan work and work outside it.

    Over EVERY PR, not only the unmapped ones: the day's total is the question, and a page
    that counted only what it owns would answer a third of it.  Nothing marks the current day:
    the generated file holds no clock reading, and the page's caption says only that the last
    bucket may be a partial day."""
    rows = {}
    for p in st.get("prs") or []:
        if not p.get("merged") or not p.get("merged_at"):
            continue
        d = rows.setdefault(p["merged_at"][:10], dict(day=p["merged_at"][:10], plan=0, outside=0))
        d["outside" if not p.get("ticket") else "plan"] += 1
    return [rows[d] for d in sorted(rows)][-days:]


def counts(prs, windows):
    by_kind = {}
    for k in KINDS:
        rs = [p for p in prs if p["kind"] == k]
        by_kind[k] = dict(total=len(rs), merged=sum(1 for p in rs if p["state"] == "merged"),
                          open=sum(1 for p in rs if p["state"] == "open"),
                          closed=sum(1 for p in rs if p["state"] == "closed"))
    groups = {}
    for w in windows:
        groups[w["group"]] = groups.get(w["group"], 0) + 1
    return dict(prs=len(prs), merged=sum(1 for p in prs if p["state"] == "merged"),
                open=sum(1 for p in prs if p["state"] == "open"), by_kind=by_kind,
                windows=len(windows), by_group=groups)


def payload(st, inventory=None):
    """data/outside.json: the unmapped PRs and windows, their kinds, and the day's totals."""
    st = st or {}
    arms = {s["name"] for s in (inventory or {}).get("syscalls", [])}
    prs = pr_rows(st, arms)
    windows = window_rows(st)
    return dict(generated="tools/lean_port_outside.py, from data/state.json and data/inventory.json",
                kinds=list(KINDS), kind_label=KIND_LABEL, kind_blurb=KIND_BLURB,
                window_group_label=WINDOW_GROUP_LABEL,
                prs=prs, windows=windows, counts=counts(prs, windows), by_day=by_day(st))


def render(p):
    return json.dumps(p, indent=1, sort_keys=True) + "\n"


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--json", action="store_true", help="print the derived payload")
    a = ap.parse_args(argv)
    if not a.json:
        ap.print_help()
        return 2
    sys.stdout.write(render(payload(state.load_json(os.path.join(DATA, "state.json"), {}),
                                    state.load_json(os.path.join(DATA, "inventory.json"), {}))))
    return 0


if __name__ == "__main__":
    sys.exit(main())
