#!/usr/bin/env python3
"""Ticket and PR state for the Lean port: docs/lean-port/data/progress.json.

The tree can say which arms have a Lean twin (tools/lean_port_status.py
computes that), but not which ticket someone is working on, which PR is under
review, or what happened today.  That is what this file records, and this
script is the one way to change it, so the coordinator never edits JSON:

    tools/lean_port_progress.py set A6 in_review --pr 723     # a ticket moved
    tools/lean_port_progress.py pr 716 --review fixes_pending # a PR's review state
    tools/lean_port_progress.py today "what happened, one line"
    tools/lean_port_progress.py show                          # the counts, as text

Every writing command stamps `updated` with the current UTC minute, rewrites
the file, and regenerates the pages with `lean_port_status.py --write` unless
`--no-regen` is given.  That stamp is the only clock reading anywhere in the
generated site, which is what keeps `lean_port_status.py --verify` stable.

Ticket states are `todo`, `blocked`, `in_progress`, `in_review`, `deep_review`,
`conflicting`, `mergeable` and `done`; a ticket absent from the file is `todo`.
A PR listed under `prs` carries what GitHub knows (title, branch, open/merged)
and `review`, the state of the local review an ordinary PR gets —
`needs_review`, `in_review`, `fixes_pending` or `approved`.

Since the owner's rule that no state is recorded by hand, this file is a
DERIVED CACHE: tools/lean_port_state.py computes every ticket and PR state from
GitHub, the ops kit's window export, the reports and the tree, and writes it
here for the pages to read.  `set` and `pr` therefore refuse: the way to change
a state is to change its source and press Update (or run
`tools/lean_port_status.py --write --github`).  `today` is still a hand-written
line, because it is a note, not a state.

DRIFT HOLDS A TICKET OPEN.  When the Rocq moves under a finished twin, the two
accepted fixes are to port the delta and move the twin's `rocq-baseline:` to
the commit that was read, or to file the re-port as a `drift-ticket: <name>
<ticket> -- <reason>` line in the twin's parity header naming the ticket
whose `provides` carries the definition -- the file's own S ticket for one it
ports, a base A or K ticket for one it only reaches, and neither the V ticket
(which declares none) nor the C ticket (which provides only under Checks/, a
subtree no spec twin's closure reaches) (docs/lean-port/BRIEF.md sections 1
and 6).  The
second fix is a register of work somebody owes, so it costs something only
while the ticket it names is open: tools/check_lean_spec_parity.py refuses a
line naming a ticket this file calls `done`, and this file refuses to record
that state -- `set <ticket> done`, and `set_ticket` under any caller, is
refused while a twin's header names `<ticket>`, with the drifted definition and
the twin quoted.  The two state one rule from both ends: a line cannot outlive
the ticket, and the ticket cannot be CLAIMED done over the line.  Claimed, not
reached: the refusal is on the claim and not on the observation.  `apply_merges`
records that a PR merged, which is a fact and not this file's to refuse, and
tools/lean_port_state.py derives every state from GitHub and writes this file
with `save`, never through `set_ticket`, so a merge can still leave the board in
the state a line forbids.  That contradiction -- a done ticket a twin still
names -- is the parity checker's to report, which it does by name, in a
required context.

    tools/lean_port_progress.py drift                         # the lines, and who they hold open

The twins are read with the parity checker's own file list and header parser
(`drift_tickets`), so that the two tools cannot disagree about what a
`drift-ticket:` line is.  Everything that could make the register short of a
line is refused instead of read as no drift: a root with no twin under it, a
header the parity parser refuses, a listed file that is not UTF-8, a
`drift-ticket:` line in a Lean file that list leaves out, which the parity
checker never reads, and one in a file it does read but outside the header
block, which is the same nothing in the file where a line belongs.  They are all the vacuous
direction, in which every ticket is free of lines because nothing was read.
"""
import argparse
import datetime
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import check_lean_spec_parity as parity  # noqa: E402  (the twin list and header parser drift_tickets reads with)

DOCS = os.path.join(ROOT, "docs", "lean-port")
PROGRESS = os.path.join(DOCS, "data", "progress.json")
PLAN = os.path.join(DOCS, "data", "plan.json")

STATES = ("todo", "blocked", "in_progress", "in_review", "deep_review", "conflicting", "mergeable", "done")
DERIVED_MESSAGE = ("ticket and PR state is derived from GitHub, the window export, the reports and the tree; "
                   "change the source and run `tools/lean_port_status.py --write --github` (or press Update)")
REVIEWS = ("needs_review", "in_review", "fixes_pending", "approved")
PR_STATES = ("open", "merged", "closed")
REPO_URL = "https://github.com/theorem-labs/linux-process-semantics"


class ProgressError(ValueError):
    pass


def now_utc():
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d %H:%MZ")


def load(path=PROGRESS):
    with open(path) as fh:
        data = json.load(fh)
    data.setdefault("updated", "")
    data.setdefault("today", "")
    # when the `today` line was written: `updated` moves on every Update, so the line cannot be dated by it
    data.setdefault("today_at", "")
    data.setdefault("tickets", {})
    data.setdefault("prs", [])
    for tid, t in data["tickets"].items():
        if t.get("state") not in STATES:
            raise ProgressError(f"{path}: ticket {tid} has state {t.get('state')!r}, not one of {STATES}")
    for p in data["prs"]:
        if p.get("state") not in PR_STATES:
            raise ProgressError(f"{path}: PR #{p.get('number')} has state {p.get('state')!r}, not one of {PR_STATES}")
        if p.get("review") not in REVIEWS + (None,):
            raise ProgressError(f"{path}: PR #{p.get('number')} has review {p.get('review')!r}, not one of {REVIEWS}")
    return data


def dumps(data):
    """One ticket or PR per line, so a diff of the file reads as a change log."""
    tickets = ",\n".join(f'  {json.dumps(k)}: {json.dumps(v, separators=(", ", ": "))}'
                         for k, v in data["tickets"].items())
    prs = ",\n".join("  " + json.dumps(p, separators=(", ", ": ")) for p in data["prs"])
    return ("{\n"
            f' "updated": {json.dumps(data["updated"])},\n'
            f' "today": {json.dumps(data["today"])},\n'
            f' "today_at": {json.dumps(data.get("today_at", ""))},\n'
            f' "tickets": {{\n{tickets}\n }},\n'
            f' "prs": [\n{prs}\n ]\n'
            "}\n")


def save(data, path=PROGRESS):
    with open(path, "w") as fh:
        fh.write(dumps(data))


def plan_ids(path=PLAN):
    with open(path) as fh:
        return [n["id"] for n in json.load(fh)["nodes"]]


def find_pr(data, number):
    for p in data["prs"]:
        if p["number"] == number:
            return p
    return None


def github_pr(number, run=subprocess.run):
    """What GitHub knows about PR `number`, or None when `gh` cannot answer."""
    try:
        r = run(["gh", "pr", "view", str(number), "--json", "number,title,state,headRefName,mergedAt,url"],
                capture_output=True, text=True, timeout=60)
    except (OSError, subprocess.SubprocessError):
        return None
    if r.returncode != 0:
        return None
    try:
        j = json.loads(r.stdout)
    except ValueError:
        return None
    state = {"OPEN": "open", "MERGED": "merged", "CLOSED": "closed"}.get(j.get("state"), "open")
    return dict(number=int(j["number"]), title=j.get("title", ""), branch=j.get("headRefName", ""),
                state=state, merged=bool(j.get("mergedAt")) or state == "merged", url=j.get("url", ""))


def upsert_pr(data, number, title=None, branch=None, state=None, review=None, url=None, merged=None):
    p = find_pr(data, number)
    if p is None:
        p = dict(number=number, title="", branch="", state="open", merged=False, review=None,
                 url=f"{REPO_URL}/pull/{number}")
        data["prs"].append(p)
        data["prs"].sort(key=lambda x: x["number"])
    if title is not None:
        p["title"] = title
    if branch is not None:
        p["branch"] = branch
    if state is not None:
        if state not in PR_STATES:
            raise ProgressError(f"PR state must be one of {PR_STATES}, not {state!r}")
        p["state"] = state
        p["merged"] = state == "merged" if merged is None else merged
    elif merged is not None:
        p["merged"] = merged
        if merged:
            p["state"] = "merged"
    if review is not None:
        if review not in REVIEWS:
            raise ProgressError(f"review must be one of {REVIEWS}, not {review!r}")
        p["review"] = review
    if url is not None:
        p["url"] = url
    return p


DRIFT_LINE = re.compile(r"^[ \t]*(drift-ticket:.*)$", re.M)


def stray_drift_lines(root, twins):
    """[(path, line)] for every `drift-ticket:` line outside `twins` in the
    mirrored tree: everything under LEAN_BASE, which is where a twin could be.
    (`lean/`'s examples, its root module and its lakefile are not scanned.)

    The twin list is what tools/check_lean_spec_parity.py reads; a line anywhere
    else is inert -- no ownership rule holds it, no done check refuses it, and no
    drift it names is silenced -- so it is reported rather than counted.  The scan
    is textual and decodes with `errors="replace"`, because a line this is looking
    for is ASCII and a file it cannot decode must not hide one.  Every line is
    reported, not the first: a second file with a line is a second re-port nobody
    holds.
    """
    base = os.path.join(root, parity.LEAN_BASE)
    known = {os.path.normpath(os.path.join(base, rel)) for rel in twins}
    out = []
    for dirpath, _, names in os.walk(base):
        for name in sorted(names):
            if not name.endswith(".lean"):
                continue
            full = os.path.normpath(os.path.join(dirpath, name))
            if full in known:
                continue
            with open(full, encoding="utf-8", errors="replace") as fh:
                text = fh.read()
            for m in DRIFT_LINE.finditer(text):
                rel = os.path.relpath(full, root).replace(os.sep, "/")
                out.append((rel, m.group(1).strip()))
    return sorted(out)


def drift_tickets(root=None):
    """{ticket: [(twin, drifted name, reason)]} over every Lean twin's parity header.

    `twin` is the path below the repository root and `drifted name` is the line's
    own spelling, bare or `<file>.v:<name>` when it had to be qualified.  Read
    with tools/check_lean_spec_parity.py's `lean_twin_files` and `parse_header`
    rather than a second reader here: that checker refuses a line naming a done
    ticket and this one refuses recording that state, so the two have to agree on
    what a line is, on where a header may sit and on which files carry one.

    Nothing the parity checker lists is skipped.  A file that checker holds to
    carrying no header at all (a registry file under Sys/Registry/) holds its
    ticket open here if it does carry one, which is the safe direction while that
    checker turns red on it.  What that list leaves out is the rest of `lean/` --
    the Checks/ twins above all, which carry a `rocq-baseline:` of their own and
    are held by tools/check_lean_cases_parity.py instead.  A `drift-ticket:` line
    there is read by nobody: it holds no ticket open and silences no drift check,
    so it is a re-port an author believes is filed and is not.  `stray_drift_lines`
    finds those and the read is refused rather than returning a register that is
    quietly short of them.
    """
    root = ROOT if root is None else root
    twins = parity.lean_twin_files(root)
    if not twins:
        # The vacuous read: with no twin in hand every ticket is free of lines,
        # so a wrong root would silence the rule instead of failing.
        raise ProgressError(f"no Lean twin read under {root}/{parity.LEAN_BASE}, so no ticket "
                            "could be held open by one; the drift register was not read")
    stray = stray_drift_lines(root, twins)
    if stray:
        shown = "".join(f"\n  {lean}: {line}" for lean, line in stray)
        raise ProgressError(
            f"a `drift-ticket:` line sits in a file tools/check_lean_spec_parity.py does not "
            f"read, so it files nothing and holds no ticket open:{shown}\nMove the line to the "
            "twin whose parity header the checker reads, or port the delta; a re-port filed where "
            "nothing looks is the silent middle this register exists to prevent.")
    held = {}
    for rel in sorted(twins):
        lean = f"{parity.LEAN_BASE}/{rel}"
        try:
            with open(os.path.join(root, parity.LEAN_BASE, rel), encoding="utf-8") as fh:
                text = fh.read()
        except UnicodeDecodeError as e:
            # A file the twin list names but nothing can decode (an AppleDouble
            # sidecar, a truncated write): its header is unread, so the register is
            # short by however many lines it carries.  Name it rather than crash.
            raise ProgressError(f"{lean}: is not UTF-8 ({e}), so its parity header and any "
                                "drift-ticket line in it were not read") from e
        block = parity.HEADER.search(text)
        try:
            claim = parity.parse_header(text, lean)
        except SystemExit as e:  # parse_header reports a header it cannot read by exiting
            raise ProgressError(f"{lean}: the parity header cannot be read ({e}), so neither can the "
                                "drift-ticket lines it may carry; run `tools/check_lean_spec_parity.py "
                                "--root .`") from e
        outside = [m.group(1).strip() for m in DRIFT_LINE.finditer(text)
                   if not (block and block.start() <= m.start() < block.end())]
        if outside:
            # Right file, wrong place: parse_header reads the block and nothing
            # else, so this line files no re-port and silences no drift -- the
            # same nothing a line in an unread file does, and the likelier
            # mistake, since the twin IS where a line belongs.
            shown = "".join(f"\n  {line}" for line in outside)
            raise ProgressError(
                f"{lean}: a `drift-ticket:` line sits outside the parity header block, where "
                f"tools/check_lean_spec_parity.py does not read it:{shown}\nMove it inside the "
                "`/-! rocq-baseline: ... -/` block; a line below it holds no ticket open.")
        for t in (claim[2] if claim else ()):
            name = f"{t['file']}:{t['name']}" if t["file"] else t["name"]
            held.setdefault(t["ticket"], []).append((lean, name, t["reason"]))
    return held


def drift_refusal(ticket, state, drifts=None):
    """Why `ticket` may not be recorded in `state`, or None.

    Only `done` is refused, and only for a ticket a twin's header names: every
    other state leaves the re-port owed and visible, which is what the line is
    for.  `drifts` is `drift_tickets()`'s register; a caller passes its own only
    to read a fixture tree, and the default reads this checkout, so a caller that
    does not think about drift is still held to it.
    """
    if state != "done":
        return None
    held = (drift_tickets() if drifts is None else drifts).get(ticket, [])
    if not held:
        return None
    lines = "".join(f"\n  {name} moved under {lean} -- {reason}" for lean, name, reason in held)
    return (f"{ticket} cannot be recorded done: a twin's parity header still files a re-port "
            f"against it, so a Rocq definition it owns has moved and nobody has ported the "
            f"difference:{lines}\nPort the delta, move that twin's `rocq-baseline:` to the commit "
            "you read and drop the line; until then the ticket is open. Recording it done would "
            "also turn the parity checker red, which refuses a drift-ticket line naming a done "
            "ticket (tools/check_lean_spec_parity.py).")


def set_ticket(data, ticket, state, pr=None, branch=None, ids=None, fetch=github_pr, drifts=None):
    """Move `ticket` to `state`; link it to PR `pr` (fetched from GitHub when new).

    `done` is refused while a twin's parity header files a drift re-port against
    the ticket (`drift_refusal`); `drifts` is that register, read from this
    checkout unless a caller hands one in.  The default is what holds a caller
    that never thought about drift, and it is the reason a test driving this
    function over a FIXTURE tree should pass `drifts={}`: left to the default it
    reads the twins of the real checkout, which is neither the tree it built nor
    a tree it controls.
    """
    if ids is not None and ticket not in ids:
        raise ProgressError(f"unknown ticket {ticket!r}: not in plan.json")
    if state not in STATES:
        raise ProgressError(f"state must be one of {STATES}, not {state!r}")
    why = drift_refusal(ticket, state, drifts)
    if why is not None:
        raise ProgressError(why)
    entry = dict(data["tickets"].get(ticket, {}))
    entry["state"] = state
    if pr is not None:
        entry["pr"] = pr
        known = find_pr(data, pr)
        if known is None:
            fetched = fetch(pr) if fetch else None
            known = upsert_pr(data, pr, **({k: v for k, v in fetched.items() if k != "number"} if fetched else {}))
        if branch is None and known.get("branch"):
            branch = known["branch"]
    if branch is not None:
        entry["branch"] = branch
    if state == "todo":
        entry = {"state": "todo"}  # back to the start: a PR or branch left behind would re-mark it done on merge
    data["tickets"][ticket] = entry
    return entry


def apply_merges(data):
    """A ticket whose PR merged is done.  Returns the tickets that moved."""
    merged = {p["number"] for p in data["prs"] if p.get("merged")}
    moved = []
    for tid, t in data["tickets"].items():
        if t.get("pr") in merged and t.get("state") != "done":
            t["state"] = "done"
            moved.append(tid)
    return moved


def refresh_from_github(data, fetch=github_pr):
    """Refresh every listed PR from GitHub; mark tickets done when their PR merged.

    Returns (changed, unreachable): whether anything moved, and the PR numbers
    `gh` could not answer for (the file's copy stands for those)."""
    changed, unreachable = False, []
    for p in list(data["prs"]):
        g = fetch(p["number"])
        if g is None:
            unreachable.append(p["number"])
            continue
        before = dict(p)
        upsert_pr(data, p["number"], title=g["title"], branch=g["branch"], state=g["state"], url=g["url"], merged=g["merged"])
        changed = changed or p != before
    moved = apply_merges(data)
    return changed or bool(moved), unreachable


def counts(data, ids):
    """Ticket counts per state over every plan ticket (absent means todo)."""
    c = {s: 0 for s in STATES}
    for tid in ids:
        c[data["tickets"].get(tid, {}).get("state", "todo")] += 1
    return c


def regenerate():
    subprocess.run([sys.executable, os.path.join(ROOT, "tools", "lean_port_status.py"), "--write"], check=True, cwd=ROOT)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("set", help="(retired: state is derived) move a ticket to a state")
    s.add_argument("ticket")
    s.add_argument("state", choices=STATES)
    s.add_argument("--pr", type=int)
    s.add_argument("--branch")
    p = sub.add_parser("pr", help="(retired: state is derived) record a PR's review state")
    p.add_argument("number", type=int)
    p.add_argument("--review", choices=REVIEWS)
    p.add_argument("--title")
    p.add_argument("--branch")
    p.add_argument("--state", choices=PR_STATES)
    t = sub.add_parser("today", help="the one-line 'what happened today'")
    t.add_argument("line")
    sub.add_parser("show", help="print the counts")
    sub.add_parser("drift", help="the drift-ticket lines the twins carry, and the tickets they hold open")
    for x in (s, p, t):
        x.add_argument("--no-regen", action="store_true", help="rewrite progress.json but do not regenerate the pages")
    args = ap.parse_args(argv)

    if args.cmd == "drift":
        try:
            held = drift_tickets()
        except ProgressError as e:
            print(f"lean_port_progress.py: {e}", file=sys.stderr)
            return 2
        for ticket in sorted(held):
            for lean, name, reason in held[ticket]:
                print(f"  {ticket:<14} {name} in {lean} -- {reason}")
        lines = sum(len(v) for v in held.values())
        # "twin file(s)", not "twins": lean_twin_files returns the twins, their parts and
        # the registry files, so this count is above the "N twins" the parity checker
        # prints two steps earlier in the same job, and saying so keeps a reader from
        # reading one number as a contradiction of the other.
        print(f"lean_port_progress.py: {len(parity.lean_twin_files(ROOT))} twin file(s) read "
              f"(twins, their parts and registry files), {lines} drift-ticket "
              f"line(s), {len(held)} ticket(s) that cannot be recorded done")
        return 0
    data = load(PROGRESS)   # the module's path read at call time, not the default bound at definition
    ids = plan_ids()
    if args.cmd == "show":
        c = counts(data, ids)
        print(f"updated {data['updated']}: " + ", ".join(f"{k} {v}" for k, v in c.items()))
        for tid, e in data["tickets"].items():
            print(f"  {tid:<10} {e['state']:<12} " + (f"#{e['pr']} " if e.get("pr") else "") + e.get("branch", ""))
        return 0
    try:
        if args.cmd == "set":
            # The drift refusal first, when it applies: it names work somebody owes,
            # where the derived message only says where a state comes from.
            raise ProgressError(drift_refusal(args.ticket, args.state) or DERIVED_MESSAGE)
        elif args.cmd == "pr":
            raise ProgressError(DERIVED_MESSAGE)
        elif args.cmd == "today":
            data["today"] = args.line
            data["today_at"] = now_utc()
    except ProgressError as e:
        print(f"lean_port_progress.py: {e}", file=sys.stderr)
        return 2
    data["updated"] = now_utc()
    save(data, PROGRESS)
    print(f"lean_port_progress.py: wrote {os.path.relpath(PROGRESS, ROOT)} (updated {data['updated']})")
    if not args.no_regen:
        regenerate()
    return 0


if __name__ == "__main__":
    sys.exit(main())
