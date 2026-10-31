#!/usr/bin/env python3
"""Derive every ticket's and PR's state from the sources of truth, never from a hand-kept file.

    tools/lean_port_state.py --refresh          # re-read the sources (ops export, GitHub, reports, tree), then derive
    tools/lean_port_state.py --derive           # derive again from the committed snapshots and this checkout
    tools/lean_port_state.py --json             # the derived state, to stdout

The owner's rule: the dashboard is accurate at any point, or at least the Update button
makes it so.  So docs/lean-port/data/progress.json is a DERIVED CACHE, written here and
read by the pages, and nothing writes a ticket's state by hand.  The sources, each with
its own freshness stamp on every page:

  (a) GitHub: every PR merged, closed or open since the port began (PORT_SINCE), against any
      `nightly/*` day branch or `main`, with its head branch, state, mergeability, merge time,
      reviews and comments -- data/github.json.  The PRs are found by DATE, never by base branch:
      the day branch a PR merged into is deleted when the day lands on `main` (#794 deleted
      nightly/09-11-2026 on 2026-09-17), and a merge must outlive its base.  One light search
      call per week of the port's life for the merges, one list-mode page for the closed PRs
      (the search index misses some of those), one call for the open ones, and one heavy call
      over the open PRs.  A merged or closed PR the previous snapshot holds and GitHub stops
      listing is kept: a merge never unhappens.
  (b) The ops kit's export, /home/harshikaa/lean-port-ops/state/windows.json (written by
      export_state.sh, run here first): every window with its worktree, branch, head,
      account, session, effort, tmux state, last pane line and, in fleet mode, the host its
      tmux window runs on; the accounts; the coordinator's build slots; the fleet's `hosts`
      (cores, slots, load, windows, reachable) and the windows on a host that did not answer.  This module adds the LAUNCH RECORD the kit keeps beside it: the worktree
      each window was launched in (briefs/.full-<window>.md, .dirs/<window>) and the deep
      reviews launched (.deep-reviewed-<PR>) -- data/windows.json.
  (c) The tree: the arms the Lean syscall table holds, the spec files with a Lean twin,
      and the parity checker's verdict per twin -- read from this checkout at --write.
  (d) The reports, /home/harshikaa/lean-port-ops/reports/<window>.md and
      deep-review-<PR>.md: the last verdict word each ends with, and the kit's review-record
      blocks inside it -- data/reports.json.  A deep review's verdict is read from its record
      (here or among the PR's comments, whichever host it ran on) at the PR's own head, and only
      then from a deep-review-<PR>.md this checkout happens to hold.
  (e) STATUS.md, the human log, rendered as it is.

A PR maps to a ticket by (in this order) the `Ticket:` line of its body, the live window
whose branch it is, the launch record (a window named like a ticket, launched in the
worktree whose branch it is), the window that made its review record (the kit's block in
reports/<window>.md or among its comments), a `(ticket X)` or `(reopens X)` in its title,
the syscall its `lean: port <name> (<n>)` title names (the plan's S ticket for that arm), or a
branch slug that starts with a ticket id. In derive and attribute, a prefix match requires a changed
file matching the ticket's FILES unless the title or Ticket: line names that ticket.
The same rules, read over the committed
snapshots for a PR that has not merged, are `attribute`: tools/lean_port_brief.py --event / --pr lints
the PR's ticket as done before the merge, so a partial port is refused on the PR rather than on the
integration head hours later (#980).  A merged `lean: base:` PR is attributed
by the same rules and listed on its ticket; on an S ticket it completes the ticket only while every
syscall the ticket ports is in the Lean table: a base PR is the port itself (#784) or a prerequisite
carved out of a frozen file (#909), and only the table tells which.  A PR none of these reach is work
outside the plan -- listed under `outside` by kind (fixes to ported arms, lean base, guards
and tests, kit and process, CI, docs, rocq spec) with the arms and files it touches and the
window that authored it -- and a contradiction only when it changes a Lean spec, registry
or pin file and names no arm.

A ticket's state is then a pure function (`ticket_state`), in this precedence: conflicting /
mergeable / deep review / in review while it has an OPEN PR (GitHub's mergeability plus the
two verdicts, author and deep review) -- an open follow-up PR is the ticket's current state
even after an earlier PR merged, which is what the owner's rule means by "if its PR is
open"; done if its PR merged; in progress if a window exists for it; blocked if a
dependency is not done; todo otherwise.  Every state carries the reason it was chosen.  The contradictions the derivation finds (a ticket the cache
had done with an open PR, a window with no ticket, a PR with no ticket, an arm in the
table with no merged PR, a ticket done with no arm) are listed, not hidden.
"""
import argparse
import datetime
import fnmatch
import glob
import importlib.util
import json
import os
import re
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lean_cases_family as cases_family  # noqa: E402
import lean_port_progress as progress  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DOCS = os.path.join(ROOT, "docs", "lean-port")
DATA = os.path.join(DOCS, "data")
GITHUB = os.path.join(DATA, "github.json")
WINDOWS = os.path.join(DATA, "windows.json")
REPORTS = os.path.join(DATA, "reports.json")
STATE = os.path.join(DATA, "state.json")
PLAN = os.path.join(DATA, "plan.json")
INVENTORY = os.path.join(DATA, "inventory.json")
OVERRIDES = os.path.join(DATA, "ticket_overrides.json")  # the manual escape: a ticket closed with no PR at all
OPS_DIR = os.path.join(os.path.expanduser("~"), "lean-port-ops")
REPO = "theorem-labs/linux-process-semantics"
REPO_URL = f"https://github.com/{REPO}"
DAY_BRANCH_FILE = os.path.join(OPS_DIR, "day-branch")
DEFAULT_DAY = "nightly/09-11-2026"
# The port's first PRs were opened on 2026-09-15; GitHub is asked for everything merged, closed or opened since,
# whatever base branch it had.  Moving this earlier only adds pre-port PRs, which the derivation then reports as
# PRs with no ticket; moving it later erases merges.
PORT_SINCE = "2026-09-15"
PORT_BASE = re.compile(r"^(nightly/.+|main)$")  # the bases the port's PRs land on: a day branch, or main for what skips the day

STATES = ("todo", "blocked", "in_progress", "in_review", "deep_review", "conflicting", "mergeable", "done")
STATE_LABEL = {"todo": "not started", "blocked": "blocked", "in_progress": "in progress", "in_review": "in review",
               "deep_review": "deep review", "conflicting": "conflicting", "mergeable": "mergeable", "done": "done"}
QUEUES = ("mergeable", "conflicting", "awaiting verdict", "awaiting deep review", "unknown", "merged", "closed")
VERDICT = re.compile(r"\b(DO NOT MERGE|MERGE AFTER FIXES|MERGE|APPROVE|REJECT)\b")
# `(ticket X)` names any plan id, `S-Fs-Locks` as much as `A2` (the old `[A-Z]\d+` shape missed every S/C/V ticket);
# `(reopens X)` is the same rule under the name a later PR uses to take a done ticket back.  Membership in the plan
# is checked where the match is used, so a bracketed word that is no ticket maps nothing.
TITLE_TICKET = re.compile(r"\((?:ticket|reopens) ([A-Za-z][A-Za-z0-9_-]*)\)")
TITLE_PORT = re.compile(r"^lean: port\b")
# A `lean: base:` PR is reviewed as infrastructure.  For a K or A ticket it IS the deliverable (K1's #766, A15's
# #779).  On an S ticket it is either the port itself (#784, brk and munmap) or what the spec window carved out of a
# frozen file on the way to its `lean: port <name> (<n>)` PR (Sys/Uaccess.lean for #909); the title cannot tell the
# two apart and the Lean table can.  Attributed to the ticket by the rules below like any PR; see `completes_ticket`.
BASE_TITLE = re.compile(r"^lean:\s*base:")
PORT_ARM = re.compile(r"\b([a-z][a-z0-9_]*) \((\d+)\)")
LAUNCH_PROMPT = re.compile(r"^#\s*(?:Ticket\s+)?([A-Z]\d+[a-z]?|[SCV]-[A-Za-z0-9-]+|E-[A-Za-z0-9_-]+)(?![A-Za-z0-9_-])")
PROJECT_SLUG = "-home-harshikaa-linux-process-semantics"
WORKTREE_INFIX = "--claude-worktrees-"
CLAUDE_DIR = os.path.join(os.path.expanduser("~"), ".claude", "projects")

# The kit's windows that are not agents -- the coordinator, the watchers, the jobs -- map to no ticket and are not
# a contradiction.  The exact names are the kit's own list (tools/lean-port-ops/lpo.py, SERVICE_WINDOWS: "a new job
# window is added here, not to five regexes"), read from the committed copy so the two never drift; the kit
# does not name its suffixed job windows (integrate-<day>, deliver-<what>, job-<what>), so those are the
# patterns here.  This tuple and that set are the whole allowlist: a window matching neither is an agent, and
# one that maps to no ticket is reported.
def _kit_service_windows(path=os.path.join(ROOT, "tools", "lean-port-ops", "lpo.py")):
    spec = importlib.util.spec_from_file_location("lpo_for_state", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return frozenset(mod.SERVICE_WINDOWS)


JOB_WINDOW_NAMES = _kit_service_windows()
SERVICE_WINDOWS = JOB_WINDOW_NAMES  # the name #908 gave the same set; one source, two names
JOB_WINDOW_PATTERNS = (re.compile(r"^integrate-.+$"), re.compile(r"^deliver-.+$"), re.compile(r"^job-.+$"))


def is_job_window(name):
    """True for the kit's own windows: the exact names it lists and the suffixed jobs it launches."""
    return name in JOB_WINDOW_NAMES or any(p.match(name) for p in JOB_WINDOW_PATTERNS)



def now_iso():
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def load_json(path, default):
    try:
        with open(path) as f:
            return json.load(f)
    except (OSError, ValueError):
        return default


def dump_json(path, data):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as f:
        json.dump(data, f, indent=1, sort_keys=True)
        f.write("\n")


def day_branch():
    try:
        with open(DAY_BRANCH_FILE) as f:
            return f.read().strip() or DEFAULT_DAY
    except OSError:
        return DEFAULT_DAY


# --------------------------------------------------------------------------
# (a) GitHub
# --------------------------------------------------------------------------

# `mergeable` makes GitHub compute a merge for every PR asked, and asked for hundreds at once its GraphQL
# answers 502; so the light calls over every PR leave it out and the heavy call asks it, with the reviews
# and comments, for the open PRs only, which are the ones whose queue state needs them.
GH_LIGHT = "number,title,body,headRefName,headRefOid,baseRefName,state,createdAt,mergedAt,closedAt,updatedAt,url,isDraft,reviewDecision,additions,deletions,author"
TICKET_LINE = re.compile(r"^\W{0,3}Ticket\W{0,3}:\s*(.+?)\s*$", re.M | re.I)  # the PR body's own declaration, first such line
RECORD_OPEN = "--- review-record ---"  # the kit's review record (tools/lean-port-ops/lpo.py); `window:` inside names the reviewer's window
RECORD_FIELD = re.compile(r"^(pr|reviewer|window|head):\s*(\S+)\s*$", re.M)
# The verdict line is matched whole and strictly: `lpo.py record` writes one of these three words and refuses
# anything else, so a `verdict:` line of any other shape is prose inside a block, not a recorded verdict, and
# reading a word out of it would invent one.  `recorded-at` orders two records; a record written before the
# kit stamped them carries none, and sorts first.
RECORD_VERDICT = re.compile(r"^verdict:[ \t]*(MERGE AFTER FIXES|DO NOT MERGE|MERGE)[ \t]*$", re.M)
RECORD_AT = re.compile(r"^recorded-at:\s*(\S+)\s*$", re.M)
FILES_CAP = 200  # paths kept per PR; a PR touching more is a regeneration or a rename sweep, and the first 200 say what it is
PORT_BRANCH = re.compile(r"^(lean|spec)/")  # a ticket's branch shapes (BRIEF.md section 10); a window on one that names no ticket is reported
LEAN_SPEC_PATH = re.compile(r"^lean/LinuxProcessSemantics/LinuxProcessSem/(?:Sys/(?:Registry/)?|Checks/Cases/)(.+)\.lean$")
GH_HEAVY = "number,mergeable,reviews,comments"
GH_RETRIES = 2
GH_SHIM_REFUSED = 75   # lib/gh_shim.sh refused the call: the stored header reading says the GraphQL budget is spent
GH_RATE_LIMITED = re.compile(r"API rate limit (already )?exceeded", re.I)   # gh 2.100's words for the primary limit, as the shim greps them


def _gh_list(args, run, log, sleep=time.sleep):
    for attempt in range(GH_RETRIES + 1):
        try:
            r = run(["gh", "pr", "list"] + args, capture_output=True, text=True, timeout=180)
        except (OSError, subprocess.SubprocessError) as e:
            log(f"state: gh failed: {e}")
            return None
        if r.returncode == 0:
            try:
                return json.loads(r.stdout)
            except ValueError:
                log("state: gh pr list answered something that is not JSON")
                return None
        log(f"state: gh pr list exited {r.returncode}: {(r.stderr or '').strip()[:200]}")
        # a spent GraphQL budget is not retried: it answered each of the three tries with the same refusal, and every
        # retry was one more call against the budget the fleet had run out of (T74).  That is GitHub's own refusal or
        # lib/gh_shim.sh's (exit 75, made without asking GitHub).  Any other failure -- a 504, GraphQL's "Something
        # went wrong ... timeout", a reset connection -- is transient and is tried again, as it always was: a heavy
        # call lost to one of them reads every open PR's records, reviews and mergeability as unknown for the pass.
        if r.returncode == GH_SHIM_REFUSED or GH_RATE_LIMITED.search(r.stderr or ""):
            return None
        if attempt < GH_RETRIES and "502" in (r.stderr or ""):
            sleep(4)  # GitHub's GraphQL 502s are transient; a second try usually answers
    return None


GH_SEARCH_LIMIT = 1000  # GitHub's search API answers at most this many per query; a window that fills it is refused, not truncated
GH_WINDOW_DAYS = 7
# A list-mode `gh pr list` (no `--search`) has no date filter, only the newest N by creation; this many is the page it
# reads.  What is older reaches the snapshot through the dated search or the copy carried forward from the last one.
GH_PAGE = 500


def date_windows(since, today, days=GH_WINDOW_DAYS):
    """Inclusive [first, last] day ranges of `days` days covering since..today, as ISO strings; the last is clamped to today."""
    a = datetime.date.fromisoformat(since)
    end = datetime.date.fromisoformat(today)
    out = []
    while a <= end:
        b = min(a + datetime.timedelta(days=days - 1), end)
        out.append((a.isoformat(), b.isoformat()))
        a = b + datetime.timedelta(days=1)
    return out


def ticket_line(body):
    """The `Ticket: ...` line of a PR body, or None: what the author declared, kept whole for the reader and scanned for a plan id."""
    m = TICKET_LINE.search(body or "")
    return m.group(1)[:200] if m else None


SQUASH_TITLE = re.compile(r"^(.*) \(#(\d+)\)\s*$")  # GitHub's squash-merge subject line
REVERT_FOOTER = re.compile(r"^This reverts commit ([0-9a-f]{7,40})\.?\s*$", re.M)
GIT_REC = "\x1e"  # between commits
GIT_SEP = "\x1f"  # between a commit's own fields


def git_merge_rows(root=ROOT, run=subprocess.run, log=print, since=PORT_SINCE, refs=None):
    """Every squash-merge commit reachable from `main` or a day branch, since `since`, as rows of
    data/github.json's shape, keyed by PR number -- a merge is a fact local history already carries, so this
    reads it without a GitHub call.  GitHub's squash merge writes the PR's own title as the commit subject
    (`<title> (#N)`) and the PR's body as the commit body, so the same `Ticket:` line `attribute` reads from a
    live PR is read here from the merge commit alone -- this is what makes a ticket's `done` state recoverable
    even when data/github.json has gone stale (nobody ran `--refresh`, or GitHub's search missed it): `derive`
    folds these rows into the ones it got from the snapshot, never the other way, so a snapshot row's mergeability,
    reviews and comments are kept whenever it has one.

    `refs` is read from `git for-each-ref` by default: every local and remote `main` and `nightly/*` tip. A day
    branch deleted after landing on `main` (#794, #906) still has its commits reachable from `main`'s history, so
    dropping the ref does not drop the merges it carried. A commit a later `git revert` names in its own
    "This reverts commit <sha>." footer is dropped -- the standard footer `git revert` writes, not a guess from
    the title -- so a merge that was undone does not read its ticket done. Returns {} when `git` cannot answer or
    no ref is found, never a partial read: a caller folds this into richer data and an empty read must cost
    nothing, not look like "no merges happened"."""
    if refs is None:
        r = run(["git", "for-each-ref", "--format=%(refname)",
                 "refs/heads/main", "refs/heads/nightly/*",
                 "refs/remotes/origin/main", "refs/remotes/origin/nightly/*"],
                cwd=root, capture_output=True, text=True, timeout=60)
        if r.returncode != 0:
            log(f"state: git for-each-ref failed: {(r.stderr or '').strip()[:200]}")
            return {}
        refs = sorted({ln.strip() for ln in r.stdout.splitlines() if ln.strip()})
    if not refs:
        log("state: no main/nightly ref found; git merge history was not read")
        return {}
    fmt = f"{GIT_REC}%H{GIT_SEP}%s{GIT_SEP}%b"
    try:
        r = run(["git", "log", *refs, f"--since={since}", f"--format={fmt}"],
                cwd=root, capture_output=True, text=True, timeout=180)
    except (OSError, subprocess.SubprocessError) as e:
        log(f"state: git log failed: {e}")
        return {}
    if r.returncode != 0:
        log(f"state: git log exited {r.returncode}: {(r.stderr or '').strip()[:200]}")
        return {}
    commits = []
    for rec in r.stdout.split(GIT_REC)[1:]:
        parts = rec.split(GIT_SEP, 2)
        if len(parts) == 3:
            commits.append(dict(sha=parts[0].strip(), subject=parts[1].strip(), body=parts[2]))
    reverted = {m.group(1) for c in commits for m in REVERT_FOOTER.finditer(c["body"])}
    files_by_sha = _git_commit_files(root, refs, since, run, log)
    rows = {}
    for c in commits:
        if any(c["sha"].startswith(s) or s.startswith(c["sha"]) for s in reverted):
            continue
        m = SQUASH_TITLE.match(c["subject"])
        if not m:
            continue
        number = int(m.group(2))
        rows[str(number)] = dict(number=number, title=c["subject"], head="", head_sha=c["sha"], base="",
                                 state="merged", merged=True, mergeable=None, created="", merged_at=None,
                                 closed_at=None, url=f"{REPO_URL}/pull/{number}", ticket_line=ticket_line(c["body"]),
                                 files=files_by_sha.get(c["sha"]), records=[])
    return rows


def _git_commit_files(root, refs, since, run, log):
    """{sha: [path, ...][:FILES_CAP]} for every commit `git_merge_rows` reads, from one `git log --name-only`
    call -- so a git-derived row can answer `files_known` honestly instead of reading as a GitHub call that
    failed (the message `derive`'s contradiction report uses for `files is None`), which `pr_arms` and the
    `outside` classifier would otherwise report as a PR GitHub did not answer for every single commit with no
    `Ticket:` line -- the overwhelming majority of a day's commits.  {} on any git failure, same fail-closed
    shape as the caller's own log reads."""
    try:
        r = run(["git", "log", *refs, f"--since={since}", "--name-only", f"--format={GIT_REC}%H"],
                cwd=root, capture_output=True, text=True, timeout=180)
    except (OSError, subprocess.SubprocessError) as e:
        log(f"state: git log --name-only failed: {e}")
        return {}
    if r.returncode != 0:
        log(f"state: git log --name-only exited {r.returncode}: {(r.stderr or '').strip()[:200]}")
        return {}
    out = {}
    for rec in r.stdout.split(GIT_REC)[1:]:
        lines = rec.splitlines()
        if not lines:
            continue
        out[lines[0].strip()] = [ln for ln in lines[1:] if ln.strip()][:FILES_CAP]
    return out


def record_fields(text):
    """Every review-record block in a text, as dicts of its pr/reviewer/window lines, the verdict it records and
    the head that verdict is for (the kit posts one block per record).

    `verdict` is None when the block names none in the shape the kit writes, and `head` is None when the block
    carries no head line: each is what this reader knows and never a guess, and `record_verdict` counts a record
    with either missing for nothing."""
    out = []
    for chunk in (text or "").split(RECORD_OPEN)[1:]:
        body = chunk.split("--- end review-record ---")[0]
        f = {k: v for k, v in RECORD_FIELD.findall(body)}
        if f.get("pr", "").isdigit():
            v, at = RECORD_VERDICT.search(body), RECORD_AT.search(body)
            out.append(dict(pr=int(f["pr"]), reviewer=f.get("reviewer"), window=f.get("window"),
                            verdict=v.group(1) if v else None, head=f.get("head"), at=at.group(1) if at else None))
    return out


def record_verdict(pr_row, reviewer, reports):
    """The verdict `reviewer` recorded for this PR's CURRENT head, or None.

    Two things this answers that reading a report file by name does not.  A record reaches this reader by two
    routes and a review uses whichever its host has: the kit appends the block to a report file here and posts the
    same block as a PR comment, so a review that ran on another host, or one that appended to the author window's
    report rather than a `deep-review-<PR>.md` of its own, is in the comments and nowhere else.  And a record
    speaks for the diff it names: the gate accepts one only at the PR's own head, so a record at an earlier head
    is not this head's verdict and is not reported as one.  Records are matched by head sha, never by recency
    alone; `recorded-at` only orders two records that both speak for this head."""
    head = pr_row.get("head_sha")
    if not head:
        return None
    recs = [r for src in list(reports.values()) + [pr_row] for r in (src.get("records") or [])
            if r.get("pr") == pr_row.get("number") and r.get("reviewer") == reviewer
            and r.get("verdict") and r.get("head") == head]
    return max(recs, key=lambda r: r.get("at") or "")["verdict"] if recs else None


def _gh_files(number, run, log):
    """The paths a PR touches, capped at FILES_CAP; None when gh cannot answer (the caller reports the unknown, never guesses)."""
    try:
        r = run(["gh", "pr", "view", str(number), "--json", "files"], capture_output=True, text=True, timeout=120)
    except (OSError, subprocess.SubprocessError) as e:
        log(f"state: gh pr view {number} failed: {e}")
        return None
    if r.returncode != 0:
        log(f"state: gh pr view {number} --json files exited {r.returncode}: {(r.stderr or '').strip()[:200]}")
        return None
    try:
        d = json.loads(r.stdout)
    except ValueError:
        log(f"state: gh pr view {number} --json files answered no JSON")
        return None
    files = d.get("files") if isinstance(d, dict) else None
    if not isinstance(files, list):
        return None
    return [f["path"] for f in files if isinstance(f, dict) and isinstance(f.get("path"), str)][:FILES_CAP]


def _gh_search(args, run, log, what):
    """One light call; None when gh fails or when the answer fills the search ceiling (a truncated list would erase PRs)."""
    part = _gh_list(args + ["--limit", str(GH_SEARCH_LIMIT), "--json", GH_LIGHT], run, log)
    if part is None:
        return None
    if len(part) >= GH_SEARCH_LIMIT:
        log(f"state: {what} answered {len(part)} PRs, the search ceiling; the snapshot is kept rather than truncated")
        return None
    return part


def fetch_github(base, run=subprocess.run, log=print, previous=None, since=PORT_SINCE, today=None):
    """Every PR merged, closed or opened since `since`, whatever its base, as data/github.json's shape; None when gh
    cannot answer.

    The PRs are found by their dates, not by their base branch: `gh pr list --base` on a day branch answers as long
    as GitHub keeps the ref name on the PRs, but the set of day branches that ever existed is knowable only from the
    PRs themselves, and the first reader here (`day_bases`, retired 2026-09-17) learnt it from the last hundred
    merged PRs, which the 09-11 merges scrolled out of within two days of the day landing on main.  So: one search
    per `GH_WINDOW_DAYS`-day window of the port's life for the merged PRs (a window is small enough never to reach
    the search ceiling, and bounded per window rather than by one global limit), one for the closed-unmerged PRs,
    one for the open ones, then one heavy call with mergeability, reviews and comments over the open PRs only:
    asking mergeability for hundreds of PRs at once makes GitHub's GraphQL answer 502.

    Each PR also carries its `Ticket:` body line, the review records among its comments (open PRs, whose comments the
    heavy call reads) and the paths it touches.  The paths come from one `gh pr view --json files` per PR -- asked in
    bulk, GitHub's GraphQL answers 504 -- and are reused from the previous snapshot for every PR whose `updatedAt` has
    not moved, or that was merged or closed already in that snapshot (its files cannot change since); a PR open then
    and finished now is asked once more, since a push just before the merge changed its files.  A steady Update asks
    only for what is new.

    The closed-unmerged PRs come from a list-mode page instead of a search: GitHub's search index does not hold every
    closed PR (on 2026-09-17 `closed:>=2026-09-15 is:unmerged` answered 6 of the 11 that `gh pr list --state closed`
    listed -- #812, #841, #842, #844 and #857 were missing from the index and present in the list).  The merged
    PRs the two modes answer were compared the same day and agreed, so the dated search stays the reader for merges,
    which is the set that reaches back over the port's whole life; the page also contributes the merges it holds, in
    case the index ever misses one of those too.

    A merged or closed PR the previous snapshot holds that GitHub did not list this time is kept, with a log line
    saying so: a merge never unhappens, and losing one would turn its ticket back to not started; a closed PR can be
    reopened, but then the open call lists it and that copy wins.  Terminal PRs from before `since` are not kept:
    they are outside the port's life."""
    today = today or datetime.datetime.now(datetime.timezone.utc).date().isoformat()
    rows = []
    for a, b in date_windows(since, today):
        part = _gh_search(["--state", "merged", "--search", f"merged:{a}..{b}"], run, log, f"the merges of {a}..{b}")
        if part is None:
            return None
        rows.extend(part)
    page = _gh_list(["--state", "closed", "--limit", str(GH_PAGE), "--json", GH_LIGHT], run, log)  # MERGED and CLOSED both
    if page is None:
        return None
    rows.extend(p for p in page if isinstance(p, dict) and ((p.get("state") == "CLOSED" and (p.get("closedAt") or "")[:10] >= since)
                                                            or (p.get("state") == "MERGED" and (p.get("mergedAt") or "")[:10] >= since)))
    part = _gh_search(["--state", "open"], run, log, "the open PRs")
    if part is None:
        return None
    rows.extend(part)
    heavy = _gh_list(["--state", "open", "--limit", "100", "--json", GH_HEAVY], run, log)
    if heavy is None:
        log("state: mergeability and reviews of the open PRs could not be read; they read UNKNOWN in this snapshot")
        heavy = []
    extra = {h["number"]: h for h in heavy if isinstance(h, dict) and "number" in h}
    prs = {}
    for p in rows:
        if not isinstance(p, dict) or not isinstance(p.get("number"), int):
            continue
        if not PORT_BASE.match(p.get("baseRefName") or ""):
            continue
        st = {"OPEN": "open", "MERGED": "merged", "CLOSED": "closed"}.get(p.get("state"))
        if st is None:
            log(f"state: PR #{p.get('number')} has GitHub state {p.get('state')!r}, which this reader does not know; left out")
            continue
        h = extra.get(p["number"], {})
        prs[str(p["number"])] = dict(
            number=p["number"], title=p.get("title", ""), head=p.get("headRefName", ""), head_sha=p.get("headRefOid", ""),
            base=p.get("baseRefName", base),
            ticket_line=ticket_line(p.get("body")),
            records=[r for x in h.get("comments") or [] for r in record_fields(x.get("body")) if r["pr"] == p["number"]],
            state=st, merged=st == "merged", mergeable=h.get("mergeable") or "UNKNOWN", created=p.get("createdAt"),
            merged_at=p.get("mergedAt"), closed_at=p.get("closedAt"), updated=p.get("updatedAt"), url=p.get("url", ""),
            draft=bool(p.get("isDraft")), review_decision=p.get("reviewDecision") or "",
            additions=p.get("additions", 0), deletions=p.get("deletions", 0), author=(p.get("author") or {}).get("login", ""),
            reviews=[dict(user=(x.get("author") or {}).get("login", ""), state=x.get("state", ""), at=x.get("submittedAt"),
                          title=(x.get("body") or "").split("\n")[0][:120]) for x in h.get("reviews") or []],
            comments=[dict(user=(x.get("author") or {}).get("login", ""), at=x.get("createdAt"),
                           head=(x.get("body") or "").split("\n")[0][:120]) for x in h.get("comments") or []])
    kept = []
    prev = (previous or {}).get("prs")
    prev = prev if isinstance(prev, dict) else {}
    for k, p in prev.items():
        if k in prs or not str(k).isdigit() or not isinstance(p, dict) or p.get("state") not in ("merged", "closed") or not PORT_BASE.match(p.get("base") or ""):
            continue
        if ((p.get("merged_at") if p.get("state") == "merged" else p.get("closed_at")) or "")[:10] < since:
            continue  # merged or closed before the port began: outside its life, not a loss
        prs[k] = p
        kept.append(k)
    if kept:
        log(f"state: {len(kept)} merged or closed PRs kept from the previous snapshot; GitHub's answer did not list them: "
            + ", ".join("#" + k for k in sorted(kept, key=int)[:8]) + (" ..." if len(kept) > 8 else ""))
    asked, unknown = 0, []
    for k, p in prs.items():
        q = prev.get(k) if isinstance(prev.get(k), dict) else None
        if q and p["state"] != "open" and not p.get("records") and isinstance(q.get("records"), list):
            p["records"] = q["records"]  # the heavy call reads comments for open PRs only: a merge keeps the records it had
        if k in kept and isinstance(p.get("files"), list):
            continue
        # a PR's files are reused when nothing about it moved, or when it was already finished last time; one that
        # was open then and is finished now is asked once more, since a push just before the merge changed its files
        if q and isinstance(q.get("files"), list) and (q.get("updated") == p.get("updated")
                                                       or (p["state"] != "open" and q.get("state") in ("merged", "closed"))):
            p["files"] = q["files"]
            continue
        asked += 1
        p["files"] = _gh_files(k, run, log)
        if p["files"] is None:
            unknown.append(k)
    if asked:
        log(f"state: asked GitHub for the files of {asked} PRs" + (f"; {len(unknown)} unanswered: " + ", ".join("#" + k for k in unknown[:8]) if unknown else ""))
    return dict(as_of=now_iso(), base=base, prs=prs)


# --------------------------------------------------------------------------
# (b) the ops kit's export, plus the launch record
# --------------------------------------------------------------------------

def launch_record(ops_dir):
    """window -> worktree slug it was launched in, from .dirs/<window> and briefs/.full-<window>.md."""
    out = {}
    for f in sorted(glob.glob(os.path.join(ops_dir, "briefs", ".full-*.md"))):
        name = os.path.basename(f)[len(".full-"):-3]
        try:
            with open(f, errors="replace") as fh:
                m = re.search(r"Your worktree: (\S+?)\.?\s", fh.read())
        except OSError:
            continue
        if m:
            out[name] = os.path.basename(m.group(1).rstrip("/"))
    for f in sorted(glob.glob(os.path.join(ops_dir, ".dirs", "*"))):
        try:
            with open(f) as fh:
                out[os.path.basename(f)] = os.path.basename(fh.read().strip().rstrip("/"))
        except OSError:
            continue
    return out


def launch_record_transcripts(claude_dir=CLAUDE_DIR):
    """worktree slug -> ticket id, from the first prompt of the worktree's earliest session
    (`# Ticket A2 ...`, `# Q0: ...`): the launch record for windows older than the kit's own."""
    out = {}
    for d in sorted(glob.glob(os.path.join(claude_dir, PROJECT_SLUG + WORKTREE_INFIX + "*"))):
        slug = os.path.basename(d)[len(PROJECT_SLUG + WORKTREE_INFIX):]
        for f in sorted(glob.glob(os.path.join(d, "*.jsonl"))):
            first = None
            try:
                with open(f, "rb") as fh:
                    for i, line in enumerate(fh):
                        if i > 400:
                            break
                        try:
                            r = json.loads(line)
                        except ValueError:
                            continue
                        if r.get("type") != "user":
                            continue
                        c = (r.get("message") or {}).get("content")
                        text = c if isinstance(c, str) else " ".join(b.get("text", "") for b in (c or []) if isinstance(b, dict) and b.get("type") == "text")
                        if text.strip() and not text.lstrip().startswith("<"):
                            first = text
                            break
            except OSError:
                continue
            m = LAUNCH_PROMPT.match((first or "").lstrip())
            if m:
                out[slug] = m.group(1)
                break
    return out


def export_windows(ops_dir, run=subprocess.run, log=print, claude_dir=CLAUDE_DIR):
    """Run the kit's export_state.sh and read its file; None when the kit is absent or the export fails."""
    script = os.path.join(ops_dir, "export_state.sh")
    out_path = os.path.join(ops_dir, "state", "windows.json")
    if os.path.exists(script):
        try:
            r = run([script], capture_output=True, text=True, timeout=300)
            if r.returncode != 0:
                log(f"state: export_state.sh exited {r.returncode}: {(r.stderr or '').strip()[:200]}")
        except (OSError, subprocess.SubprocessError) as e:
            log(f"state: export_state.sh failed: {e}")
    exported = load_json(out_path, None)
    if exported is None:
        return None
    exported["launches"] = launch_record(ops_dir)
    exported["launch_tickets"] = launch_record_transcripts(claude_dir) if os.path.isdir(claude_dir) else {}
    exported["deep_reviews"] = sorted(int(os.path.basename(f)[len(".deep-reviewed-"):])
                                      for f in glob.glob(os.path.join(ops_dir, ".deep-reviewed-*"))
                                      if os.path.basename(f)[len(".deep-reviewed-"):].isdigit())
    exported["windows"] = sorted(exported.get("windows", []), key=lambda w: w.get("window", ""))
    return exported


# --------------------------------------------------------------------------
# (d) the reports
# --------------------------------------------------------------------------

def read_reports(reports_dir):
    """stem -> the last verdict word the report ends with (or None) and when it was written."""
    reports, latest = {}, None
    for f in sorted(glob.glob(os.path.join(reports_dir, "*.md"))):
        try:
            with open(f, errors="replace") as fh:
                text = fh.read()
            mtime = datetime.datetime.fromtimestamp(os.stat(f).st_mtime, datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
        except OSError:
            continue
        stem = os.path.basename(f)[:-3]
        if "pr-body" in stem or stem.endswith("PENDING"):
            continue  # a PR-body draft or a placeholder is not a report
        tail = "\n".join(text.rstrip().splitlines()[-3:])
        words = VERDICT.findall(tail)
        head = "\n".join(text.splitlines()[:15])  # the PR a report is about is declared in its header, not anywhere a number appears
        m = re.search(r"^(?:PR|\*\*PR\*\*)[: ]+.*?(?:/pull/|#)(\d{3,5})\b", head, re.M)
        reports[stem] = dict(verdict=words[-1] if words else None, at=mtime, pr=int(m.group(1)) if m else None,
                             kind="deep" if stem.startswith("deep-review-") else "author",
                             records=record_fields(text))  # the kit's review records appended by review_record.sh, pr and window each
        latest = max(latest or mtime, mtime)
    return dict(as_of=latest, reports=reports)


# --------------------------------------------------------------------------
# (c) the tree
# --------------------------------------------------------------------------

def missing_deliverables(plan, root=ROOT):
    """The FILES patterns of the plan the checkout does not hold, as a set.  A pattern is a path under the
    repository root, glob or plain (`State/*.lean` is how A15 and A2 list a split module), and matches when at
    least one file exists for it.  What it is for: `completes_ticket`."""
    out = set()
    for node in plan.get("nodes", []):
        for pattern in node.get("files") or []:
            if not isinstance(pattern, str) or not pattern:
                continue
            if not glob.glob(os.path.join(root, pattern)):
                out.add(pattern)
    return out


def tree_facts(inventory, root=ROOT, run=subprocess.run, plan=None):
    """What this checkout says: its sha, the Lean arms, the spec files with a twin, parity per twin, and (given the
    plan) the deliverable files it lacks."""
    sha = None
    try:
        r = run(["git", "rev-parse", "HEAD"], capture_output=True, text=True, cwd=root, timeout=30)
        if r.returncode == 0:
            sha = r.stdout.strip()[:12]
    except (OSError, subprocess.SubprocessError):
        pass
    parity = {}
    try:
        r = run([sys.executable, os.path.join(root, "tools", "check_lean_spec_parity.py"), "--root", root, "--json"],
                capture_output=True, text=True, cwd=root, timeout=300)
        if r.returncode in (0, 1) and r.stdout.strip():
            rows = json.loads(r.stdout)  # {"files": {rocq file: {claimed, missing, drifted, lean, ...}}, "unclaimed": [...]}
            files = rows.get("files") if isinstance(rows, dict) and isinstance(rows.get("files"), dict) else rows
            for rocq, row in (files.items() if isinstance(files, dict) else []):
                if isinstance(row, dict) and isinstance(row.get("lean"), str):
                    parity[rocq.replace("theories/LinuxProcessSem/", "")] = dict(
                        claimed=bool(row.get("claimed")), missing=len(row.get("missing") or []), drifted=row.get("drifted"))
    except (OSError, subprocess.SubprocessError, ValueError):
        parity = {}
    arms = [s for s in inventory.get("syscalls", []) if s.get("lean")]
    arm_files = {s["name"]: s["file"][:-2] for s in inventory.get("syscalls", []) if isinstance(s.get("file"), str) and s["file"].endswith(".v")}
    return dict(sha=sha, arms_total=len(inventory.get("syscalls", [])), lean_arms=sorted(s["name"] for s in arms), arm_files=arm_files,
                lean_files=sorted(f["file"] for f in inventory.get("files", []) if f.get("lean_lines")),
                missing_files=sorted(missing_deliverables(plan, root=root)) if plan is not None else [],
                parity=parity)


# --------------------------------------------------------------------------
# Mapping PRs, windows and reports to tickets
# --------------------------------------------------------------------------

def slug_ticket(slug, plan_ids):
    """The ticket a branch or worktree slug names, or None: the whole slug, else its first token."""
    if not slug:
        return None
    s = slug.lower().split("/")[-1]
    lower = {t.lower(): t for t in plan_ids}
    if s in lower:
        return lower[s]
    head = s.split("-")[0]
    return lower.get(head)


def title_ticket(title, arm_ticket, plan_ids):
    m = TITLE_TICKET.search(title or "")
    if m and m.group(1) in plan_ids:
        return m.group(1), "title names the ticket"
    if TITLE_PORT.match(title or ""):
        for name, _num in PORT_ARM.findall(title):
            if name in arm_ticket:
                return arm_ticket[name], f"title ports {name}"
    return None, None


def arm_tickets(plan):
    """arm name -> the S ticket that ports it (P1 for mmap: the template PR)."""
    out = {}
    for n in plan.get("nodes", []):
        if n.get("track") in ("S", "P"):
            for a in n.get("syscalls", []) or []:
                if a not in out or (n["track"] == "S" and out[a][0] != "S"):
                    out[a] = n["id"]
    return out


def ticket_in_line(line, plan_ids):
    """(ticket, declared) for a `Ticket:` line, or (None, False).  `Ticket: A8 follow-up ...` DECLARES A8: the first word is
    the ticket, and it is the author's own statement, so no lower rule is consulted and the PR reopens the ticket.
    `Ticket: review-back-3 (second review of PR #763, ticket A11; no plan ticket of its own)` only MENTIONS A11: the
    PR is attributed to A11 (it is A11's work being reworked) but does not reopen it, and the lower rules still speak."""
    words = re.findall(r"[A-Za-z][A-Za-z0-9_-]*", line or "")
    for i, tok in enumerate(words):
        if tok in plan_ids:
            return tok, i == 0
    return None, False


def tickets_in_line(line, plan_ids):
    """Every plan id a `Ticket:` line mentions, in order, once each: a line naming two is a disagreement to report."""
    out = []
    for tok in re.findall(r"[A-Za-z][A-Za-z0-9_-]*", line or ""):
        if tok in plan_ids and tok not in out:
            out.append(tok)
    return out


def pr_reopens(pr, tid, plan_ids):
    """Whether an open PR puts a done ticket back in review: only an explicit statement does -- a `(reopens X)` or
    `(ticket X)` in the title, or a body `Ticket:` line declaring X.  A follow-up attributed by any other rule (a
    window, a record, a slug, a mention) is listed on the ticket and the ticket stays done: the merge is a fact."""
    m = TITLE_TICKET.search(pr.get("title") or "")
    if m and m.group(1) == tid:
        return True
    t, declared = ticket_in_line(pr.get("ticket_line"), plan_ids)
    return declared and t == tid


def deliverable_missing(node, missing_files):
    """Whether the checkout lacks a file the ticket's plan FILES promise, which makes it not done whatever PR is
    mapped to it.

    Two live shapes, both reading a ticket done with its twin absent, and neither caught by the arms rule in
    `completes_ticket`.  #989 -- `tools: lean-port: a base PR completes an S ticket only with its arms ported`,
    two files under tools/ and no Lean file -- was mapped to S-Fs-ReadWrite-write because its body names that
    ticket as the example, and its title is not `lean: base:`, so the arms rule let it through while the Lean tree
    holds no Sys/Fs/ReadWrite.lean.  K1 is the shape from the other side: #766 ported the Prelude half of a ticket
    whose FILES list Checks/Sys/Uaccess.lean too, and K is not an S track.  Both made the brief linter's PROVIDES
    rule demand names no twin defines, so `generated-docs` -- a required context -- was red on the day branch and
    on every PR against it (2026-09-18).

    Existence, not content: `missing_deliverables` globs, since A15 and A2 list split modules as `State/*.lean`
    and `Sys/Uapi/*.lean`.  Dropping a merge now visibly blocks an otherwise launchable ticket with a reason and
    a `found` entry: a relaunch is right only for unfinished work, which the tree cannot distinguish from a rename,
    and fails anyway when the old branch exists."""
    return any(f in missing_files for f in node.get("files") or [])


def completes_ticket(pr, node=None, lean_arms=()):
    """Whether a merged PR closes the ticket it maps to.  Every merge does, except a `lean: base:` PR's on an S
    ticket whose syscalls are not all in the Lean table.  Two S-track shapes carry that title and the title cannot
    tell them apart: #784 (`lean: base: port brk (214) and munmap (215) ...`) is the port itself and left brk and
    munmap in the table, so it completes; #909 (`lean: base: port write_source ...`, body `Ticket:
    S-Fs-ReadWrite-write`) is the prerequisite its window carved out of the frozen Sys/Uaccess.lean on the way to
    the `lean: port write (64)` PR and left no write arm -- yet it read the ticket done on 2026-09-18, the brief
    linter's PROVIDES rule then demanded the eight names the ticket provides, and generated-docs was red on every PR.
    The table is the key the `ticket done without its arm` check already uses; the PR stays listed on its ticket
    either way.  On any other track the base PR is the ticket's own deliverable (K1's #766, A15's #779) and
    completes it.  That half stops holding the day a non-S ticket gets a `lean: base:` prerequisite of its own, and
    there is no table to ask for those tracks.  The S half stops holding for a ticket whose deliverable is a
    `lean: base:` PR while its plan syscalls are not all registered -- none today; the `ticket done without its arm`
    check is what would surface that plan/tree disagreement.

    The tree's own half of "done" is not here but in `deliverable_missing`, which `derive` applies to every
    recorded merge at once: this predicate answers for a PR, and a record whose PR row GitHub no longer lists
    survives that question (see `derive`) while an absent deliverable must sink it anyway.  #989 -- `tools: lean-port: a base PR completes an S ticket only with its arms ported`, which
    touches two files under tools/ and no Lean file at all -- was mapped to S-Fs-ReadWrite-write because its body
    names that ticket as the example, and read it done on 2026-09-18 while the Lean tree holds no
    Sys/Fs/ReadWrite.lean.  K1 is the same shape from the other side: #766 ported the Prelude half of a ticket
    whose FILES list Checks/Sys/Uaccess.lean too, and the ticket read done with that file absent.  Both made the
    brief linter's PROVIDES rule demand names no twin defines, so `generated-docs` -- a required context -- was
    red on the day branch and on every PR against it."""
    if not pr.get("merged"):
        return False
    if not (node and node.get("track") == "S" and BASE_TITLE.match(pr.get("title") or "")):
        return True
    return all(a in lean_arms for a in node.get("syscalls") or [])


def attribution_maps(plan_ids, windows, reports, prs):
    """The maps the PR-to-ticket rules read beyond the PR's own fields, plus the set of launch slugs and PR numbers
    whose ticket came from a name prefix, from the ops export and the reports
    (`windows`, `reports`: data/windows.json and data/reports.json as loaded) and the PR rows (`prs`: number -> row):
    branch -> the live window on it; worktree slug -> the ticket whose window was launched there (a review-<N>/
    fix-<N>/finish-<N> window launched in a ticket's worktree counts for that ticket, and the transcript's launch
    prompt for windows older than the kit); PR number -> the ticket of such a review or fix window; PR number -> the
    author windows that recorded a verdict for it, from the reports (every PR) and the PR's own comments (open PRs)
    -- deep-review windows record too and name no ticket, so only `reviewer: window` counts.

    One builder for `derive` and for the pre-merge check (`attribute`, which tools/lean_port_brief.py runs on a pull
    request before it merges), so the two read a PR by the same maps: what can differ between them is only how
    fresh the snapshots are, since `derive` runs after --refresh rewrote them and a CI checkout reads the committed
    copies."""
    live = [w for w in (windows.get("windows") or []) if w.get("window")]
    launches = windows.get("launches") or {}
    rep = reports.get("reports") or {}
    branch_window = {}
    for w in live:
        if w.get("branch") and not is_job_window(w["window"]):
            branch_window.setdefault(w["branch"], w["window"])
    launch_window = {slug: w for w, slug in launches.items() if w in plan_ids}
    prefix_launch = set()
    pr_hint = {}  # PR number -> ticket, from a review-<N>/fix-<N> window launched in a ticket's worktree
    for w, slug in launches.items():
        m = re.match(r"^(?:review|fix|finish)-(.+)$", w)
        if not m or w in plan_ids:
            continue
        tail = m.group(1)
        source = tail if slug_ticket(tail, plan_ids) else slug
        t = slug_ticket(source, plan_ids)
        if t:
            prefix = source.lower().split("/")[-1] != t.lower()
            if slug not in launch_window:
                launch_window[slug] = t
                if prefix:
                    prefix_launch.add(slug)
            if tail.isdigit() and int(tail) not in pr_hint:
                pr_hint[int(tail)] = t
                if prefix:
                    prefix_launch.add(int(tail))
    for slug, t in (windows.get("launch_tickets") or {}).items():  # the transcript's launch prompt, for windows older than the kit
        if t in plan_ids and (slug not in launch_window or slug in prefix_launch):
            launch_window[slug] = t
            prefix_launch.discard(slug)
    record_windows = {}
    for stem, r in rep.items():
        for rec in r.get("records") or []:
            if rec.get("reviewer") == "window" and rec.get("window") and isinstance(rec.get("pr"), int):
                record_windows.setdefault(rec["pr"], []).append(rec["window"])
    for n, p in prs.items():
        for rec in p.get("records") or []:
            if rec.get("reviewer") == "window" and rec.get("window") and rec.get("pr") == n:
                record_windows.setdefault(n, []).append(rec["window"])
    return branch_window, launch_window, pr_hint, record_windows, prefix_launch


def pr_row(number, title, body, head, base=""):
    """A PR row of data/github.json's shape from the fields every source of a pull request carries -- a GitHub
    event payload, `gh pr view`, the snapshot itself -- so `attribute` reads a PR that is not in the snapshot yet by
    the rules `derive` reads the snapshot's rows by.  The body is reduced to its `Ticket:` line here, as
    fetch_github reduces it, and the row carries no review records: those come from the snapshot when the PR is in
    it, and a PR read from its event payload alone has none to offer."""
    return dict(number=number, title=title or "", head=head or "", base=base or "", ticket_line=ticket_line(body or ""), records=[])


def event_pr(payload):
    """The pull request a GitHub event payload (the `GITHUB_EVENT_PATH` document) is about, as a row for
    `attribute`, or None when the payload is not a pull_request event's -- a push, a merge_group or a
    workflow_dispatch carries no `pull_request` object, and a caller in a workflow declared on all four treats that
    as "no PR here", never as a PR with empty fields (which would attribute by an empty head to nothing anyway, but
    silently).  Reads `pull_request.number`, `.title`, `.body`, `.head.ref` and `.base.ref`, the fields the local
    CI's synthesised payload carries too (tools/lean-port-ops/ci/local_ci.py, event_payload)."""
    pr = payload.get("pull_request") if isinstance(payload, dict) else None
    if not isinstance(pr, dict):
        return None
    head = pr.get("head") if isinstance(pr.get("head"), dict) else {}
    base = pr.get("base") if isinstance(pr.get("base"), dict) else {}
    number = pr.get("number") if isinstance(pr.get("number"), int) and not isinstance(pr.get("number"), bool) else None
    return pr_row(number, pr.get("title"), pr.get("body"), head.get("ref"), base.get("ref"))


def attribute(pr, plan, github, windows, reports):
    """(ticket, how) for one PR row by the module docstring's rules, read over the committed snapshots (`github`,
    `windows`, `reports`: data/github.json, data/windows.json and data/reports.json as loaded, each `{}` when
    absent), or (None, why) when no rule reaches a ticket.  The first rule that applies wins, as in `derive`; a
    PR whose head is a day branch is the day's integration PR, not a ticket's work, and is refused before any rule
    is asked, as `derive` drops those rows; a PR whose base is neither a day branch nor main is one fetch_github
    never fetches (PORT_BASE), so `derive` never sees it and this refuses it too -- an empty base, which only a
    hand-made row has, is unknown rather than wrong and is not refused.  This is the pre-merge reading of a PR:
    what `derive` would attribute it to once merged, minus whatever the snapshots have not been refreshed to see
    (a window that opened after the last export) and minus the ledger of recorded merges `derive` also reads
    (state.json's done_prs), which names merged PRs only and so never a PR read before its merge."""
    plan_ids = {n["id"] for n in plan.get("nodes", [])}
    if (pr.get("head") or "").startswith("nightly/"):
        return None, "its head is a day branch, the day's integration PR rather than a ticket's work"
    if pr.get("base") and not PORT_BASE.match(pr["base"]):
        return None, f"its base {pr['base']!r} is neither a day branch nor main, a PR the snapshot never fetches (PORT_BASE)"
    prs = {int(k): dict(v) for k, v in (github.get("prs") or {}).items()}
    maps = attribution_maps(plan_ids, windows, reports, prs)
    ticket_files = {n["id"]: n.get("files") or [] for n in plan.get("nodes", [])}
    answers = pr_ticket_answers(pr, plan_ids, arm_tickets(plan), *maps, ticket_files=ticket_files)
    if answers:
        return answers[0]
    return None, ("no rule reaches a ticket: the body has no `Ticket:` line naming one, the title neither names one "
                  "in parentheses nor ports an arm the plan lists, the head branch's slug is not a ticket id, and "
                  "no window, launch record or review record in the snapshots is on this branch")


def file_glob_matches(path, pattern):
    """Match FILES like glob.glob's default: no recursive ** or implicit hidden paths."""
    parts, patterns = path.split("/"), pattern.split("/")
    return len(parts) == len(patterns) and all((not p.startswith(".") or g.startswith("."))
                                             and fnmatch.fnmatchcase(p, g) for p, g in zip(parts, patterns))


def pr_ticket_answers(pr, plan_ids, arm_ticket, branch_window, launch_window, pr_hint=None, record_windows=None,
                      prefix_launch=None, *, ticket_files=None, refused=None):
    """Every (ticket, how) the rules of the module docstring give for a PR, in rule order; [] when none applies.
    With ticket_files (ticket -> FILES globs), a prefix match credits a ticket only when the PR names it or changes a
    file matching its FILES; each (ticket, PR number) refused that way is added to `refused`."""
    head = pr.get("head", "")
    out = []
    t, declared = ticket_in_line(pr.get("ticket_line"), plan_ids)
    if declared:
        return [(t, "the body's Ticket: line declares it")]
    named = set()
    title = TITLE_TICKET.search(pr.get("title") or "")
    if title and title.group(1) in plan_ids:
        named.add(title.group(1))

    def accepts(t, prefix):
        if not prefix or ticket_files is None or t in named:
            return True
        if any(file_glob_matches(f, pattern) for f in pr.get("files") or []
               for pattern in ticket_files.get(t) or []):
            return True
        if refused is not None:
            refused.add((t, pr.get("number")))
        return False

    # `Ticket: K10-prereq-run (the prerequisite of K10, ...)` names a work item whose id only starts with K10: its
    # mention of K10 is a prefix claim, gated like a branch prefix.
    words = re.findall(r"[A-Za-z][A-Za-z0-9_-]*", pr.get("ticket_line") or "")
    prefix_named = slug_ticket(words[0], plan_ids) if words else None
    mentions = [(m, "the body's Ticket: line mentions it") for m in tickets_in_line(pr.get("ticket_line"), plan_ids)
                if m != prefix_named or accepts(m, True)]
    out[:0] = mentions
    named.update(t for t, _ in mentions)

    w = branch_window.get(head)
    if w in plan_ids:
        out.append((w, f"window {w} is on this branch"))
    for slug in (head.split("/")[-1], head.split("/")[-1].removeprefix("lean-")):
        w = launch_window.get(slug)
        if w in plan_ids and accepts(w, slug in (prefix_launch or ())):
            out.append((w, f"window {w} was launched in this branch's worktree"))
            break
    t = (pr_hint or {}).get(pr.get("number"))
    if t and accepts(t, pr.get("number") in (prefix_launch or ())):
        out.append((t, f"a review or fix window for #{pr.get('number')} was launched in {t}'s worktree"))
    for w in (record_windows or {}).get(pr.get("number"), []):
        t = w if w in plan_ids else slug_ticket(w, plan_ids)
        if t and accepts(t, w.lower().split("/")[-1] != t.lower()):
            out.append((t, f"its review record was made from window {w}"))
            break
    t, how = title_ticket(pr.get("title", ""), arm_ticket, plan_ids)
    if t:
        out.append((t, how))
    t = slug_ticket(head, plan_ids)
    if t and accepts(t, head.lower().split("/")[-1] != t.lower()):
        out.append((t, "branch slug starts with the ticket id"))
    return out


def pr_ticket(pr, plan_ids, arm_ticket, branch_window, launch_window, pr_hint=None):
    """(ticket, how) for a PR: the first rule that applies; (None, None) when none does."""
    answers = pr_ticket_answers(pr, plan_ids, arm_ticket, branch_window, launch_window, pr_hint)
    return answers[0] if answers else (None, None)


def window_ticket(w, plan_ids, pr_of_branch, ticket_of_pr):
    name = w.get("window", "").split("/")[-1]
    lower = {t.lower(): t for t in plan_ids}
    t = name if name in plan_ids else lower.get(name.lower())
    if t:
        return t
    br = w.get("branch", "")
    if br in pr_of_branch and pr_of_branch[br] in ticket_of_pr:
        return ticket_of_pr[pr_of_branch[br]]
    return lower.get(os.path.basename(w.get("worktree", "") or "").lower())


# --------------------------------------------------------------------------
# Work outside the plan
# --------------------------------------------------------------------------

# The kinds a PR with no ticket is filed under.  ONE classifier: the Outside-the-plan page
# (tools/lean_port_outside.py) used to carry a second one with a different vocabulary and a
# different order of reading, and the two disagreed on 71 of the 89 unmapped PRs in one snapshot,
# so data/state.json and data/outside.json named the same PR two different things.  The page's
# rule is kept, because it is the documented one: the head branch is read FIRST -- the launcher
# chose it, so `tests/guard-lean-build-visible` is a guard however its title begins -- and the
# title's component (the word before the first colon; AGENTS.md pins `component: action`) second.
#
#   fix    a fix to an arm already ported (lean/fix-*, or a `lean: fix:` title)
#   port   Lean port work with no plan ticket: a base change, a pins file, an example repair
#   guard  a guard or a test added to catch a class of mistake (tests/*)
#   kit    the ops kit and the process it runs (tools/*, process/*)
#   ci     the workflows and the merge gate's plumbing (ci/*)
#   docs   the pages, the briefs and the prose (docs/*, comments/*, `comments:`)
#   model  the Rocq model's own work, not the port at all: an `lps-*` branch, or a `spec:`,
#          `syscalls:`, `riscv:`, `testing:` or `bugs:` component
#   other  anything the rules above do not name -- listed, never folded into a neighbour
OUTSIDE_KIND_NAMES = ("fix", "port", "guard", "kit", "ci", "docs", "model", "other")
BRANCH_KIND = (("lean/fix-", "fix"), ("tests/", "guard"), ("tools/", "kit"), ("process/", "kit"),
               ("ci/", "ci"), ("docs/", "docs"), ("comments/", "docs"), ("lean/", "port"),
               ("lps-", "model"))   # the Rocq development's own branch convention
TITLE_KIND = {"lean": "port", "lean-port": "port", "lean-assurance": "port", "tools": "kit", "ci": "ci",
              "docs": "docs", "comments": "docs", "spec": "model", "syscalls": "model", "riscv": "model",
              "testing": "model", "bugs": "model"}


def outside_kind(pr):
    """Which kind of work an unmapped PR is, from its branch first and its title's component second."""
    head = (pr.get("head") or pr.get("branch") or "").lower()
    title = (pr.get("title") or "").lower()
    if head.startswith("lean/") and not head.startswith("lean/fix-") and title.startswith("lean: fix:"):
        return "fix"        # the title is the author's own word for what the change is
    for prefix, kind in BRANCH_KIND:
        if head.startswith(prefix):
            return kind
    if title.startswith("lean: fix:"):
        return "fix"
    component = title.split(":")[0].strip().rstrip(",").split(",")[0].strip()
    return TITLE_KIND.get(component, "other")


def pr_arms(pr, arm_files, errors=None):
    """The arms a PR is about: the Lean spec, registry or pin files it touches (by the arm's mirror path) and the arm
    names its title uses as words.  Returns (arms, lean spec/check paths touched, files known?).
    Family lookup failures use the original path and are appended to errors when supplied."""
    files = pr.get("files")
    known = isinstance(files, list)
    by_stem = {}
    for arm, stem in (arm_files or {}).items():
        by_stem.setdefault(stem, []).append(arm)
    arms, spec_paths = set(), []
    families = None
    history = None
    for path in files or []:
        owned = None
        try:
            if path.startswith(cases_family.CASES) and path.endswith(".lean"):
                if families is None:
                    families = cases_family.View(ROOT)
                owned = families.owner(path)
                member_shape = (path.startswith(cases_family.CASES)
                                and not path.startswith(cases_family.CASES + "Checks/")
                                and (families.ancestor(path) is not None
                                     or path[len(cases_family.CASES):].count("/") >= 2))
                if member_shape and pr.get("head_sha"):
                    # Remote heads need not have been fetched for the board. Where
                    # history is available it owns the answer, not today's checkout.
                    if history is None:
                        exists = subprocess.run(["git", "-C", ROOT, "cat-file", "-e", pr["head_sha"] + "^{commit}"],
                                                capture_output=True).returncode == 0
                        history = cases_family.View(ROOT, pr["head_sha"]) if exists else False
                    if history:
                        owned = history.owner(path)
                        if owned is None:
                            # The deletion can precede other commits on the PR.
                            last = history.git("log", "-1", "--format=%H", pr["head_sha"], "--", path).strip()
                            if last and subprocess.run(["git", "-C", ROOT, "cat-file", "-e", last + "^"],
                                                       capture_output=True).returncode == 0:
                                owned = cases_family.owner_at(ROOT, last + "^", path)
        except cases_family.FamilyError as e:
            owned = None
            # A failed registry read can leave a partial cache in either view.
            families = history = None
            if errors is not None:
                errors.append(str(e))
        m = LEAN_SPEC_PATH.match(owned or path)
        if m:
            spec_paths.append(path)
            arms.update(by_stem.get(m.group(1), []))
    title = pr.get("title") or ""
    if title.startswith("lean:"):  # `lean: fix: mmap: ...` names the arm in component position; a plain word (`read the record`) does not
        arms.update(c.strip() for c in title.split(":")[1:-1] if c.strip() in (arm_files or {}))
        m = TITLE_PORT.match(title)
        if m:
            arms.update(name for name, _num in PORT_ARM.findall(title) if name in (arm_files or {}))
    return sorted(arms), spec_paths, known


# --------------------------------------------------------------------------
# The state function
# --------------------------------------------------------------------------

def pr_queue(pr, author_verdict, deep_verdict, deep_state):
    """Where an open PR sits: mergeable / conflicting / awaiting verdict / awaiting deep review / unknown."""
    if pr.get("merged"):
        return "merged"
    if pr.get("state") == "closed":
        return "closed"
    if pr.get("mergeable") == "CONFLICTING":
        return "conflicting"
    if author_verdict == "MERGE" and deep_verdict == "MERGE" and pr.get("mergeable") == "MERGEABLE":
        return "mergeable"
    if author_verdict != "MERGE":
        return "awaiting verdict"
    if deep_verdict != "MERGE":
        return "awaiting deep review"
    return "unknown"


def ticket_state(open_prs, merged_prs, windows, deps_done, deps_open=(), milestone=False, human=False):
    """The owner's rule, as a pure function.  Returns (state, reason).

    open_prs: the ticket's open PRs with their queue state (dicts with number, queue);
    merged_prs: numbers of its merged PRs; windows: names of live windows for it;
    deps_done: whether every dependency is done; deps_open: the ones that are not, for the reason;
    milestone: a track-M node, which opens no PR and so is done once every dependency is -- under the
    merged-PR rule alone a milestone read `todo` forever, and once V-pilot-decision became a dependency
    of the V tickets their launch (launch_watch.py excludes a ticket with a dependency not done) waited on
    a state nothing could reach; human: the named person records it (V-pilot-decision) by landing a PR on
    a branch named for the ticket (slug_ticket: the slug is the id, lower-cased), so it is not derived."""
    if open_prs:
        p = sorted(open_prs, key=lambda x: -x["number"])[0]
        q = p["queue"]
        if q == "conflicting":
            return "conflicting", f"PR #{p['number']} conflicts with the day branch"
        if q == "mergeable":
            return "mergeable", f"PR #{p['number']} has both verdicts and is mergeable"
        if q == "awaiting deep review":
            return "deep_review", f"PR #{p['number']} waits for its deep review"
        if q == "unknown":
            return "in_review", f"PR #{p['number']} has both verdicts; GitHub has not computed its mergeability yet"
        return "in_review", f"PR #{p['number']} is open and waits for its verdict"
    if merged_prs:
        return "done", f"PR #{max(merged_prs)} merged"
    if windows:
        return "in_progress", f"window {sorted(windows)[0]} is open"
    if not deps_done:
        shown = list(deps_open)[:4]
        return "blocked", "waits on " + (", ".join(shown) + (f" and {len(deps_open) - 4} more" if len(deps_open) > 4 else "")) if shown else "a dependency is not done"
    if milestone and not human:
        return "done", "every dependency is done (a milestone opens no PR)"
    if human:
        return "todo", "awaits the human decision: a merged PR on a branch named for this ticket records it"
    return "todo", "no PR, no window"


def derive(plan, github, windows, reports, tree, previous, day=None, git_merges=None, overrides=None):
    """Everything the pages show about state, from the five sources (plus `git_merges`, a sixth, optional one).
    Pure: no clock, no I/O.

    `git_merges` is `git_merge_rows`'s read of local history, as data/github.json's shape keyed by PR number
    (string keys, like github's own).  It only ever ADDS a merge the snapshot missed or UPGRADES a row the
    snapshot still calls open to merged -- never the reverse, and never a field the snapshot's own row already
    carries (mergeability, reviews, comments, files): a stale github.json is still richer than git log wherever
    it has an answer, and git log is only the fallback for what a stale or rate-limited `--refresh` lost.

    `overrides` is docs/lean-port/data/ticket_overrides.json's shape, `{ticket: {"state", "reason"}}` -- the
    manual escape for a ticket closed with no PR behind it at all (the rule above this file, and `human`
    before it, both answer only the shapes they know). Applied last, after every derived state: an override
    cannot be out-voted by a later rule reading the same ticket differently, which is the point of it, but it is
    still validated against the ticket set and the state enum so a typo fails loud rather than silently doing
    nothing."""
    nodes = {n["id"]: n for n in plan.get("nodes", [])}
    plan_ids = set(nodes)
    arm_ticket = arm_tickets(plan)
    prs = {int(k): dict(v) for k, v in (github.get("prs") or {}).items()}
    for k, row in (git_merges or {}).items():
        n = int(k)
        if n not in prs:
            prs[n] = dict(row)
        elif not prs[n].get("merged") and row.get("merged"):
            prs[n] = dict(prs[n], merged=True, state="merged",
                          ticket_line=prs[n].get("ticket_line") or row.get("ticket_line"))
    live = [w for w in (windows.get("windows") or []) if w.get("window")]
    launches = windows.get("launches") or {}
    deep_launched = set(windows.get("deep_reviews") or [])
    rep = reports.get("reports") or {}

    maps = attribution_maps(plan_ids, windows, reports, prs)
    record_windows = maps[3]
    ticket_files = {t: n.get("files") or [] for t, n in nodes.items()}
    refused, answered = set(), {}

    # PRs -> tickets.  When two rules name different tickets the first wins and the disagreement is a
    # contradiction, not a silent choice.
    prs = {n: p for n, p in prs.items() if not (p.get("head") or "").startswith("nightly/")}  # a day's integration PR is the day branch itself, not a ticket's work
    ticket_of_pr, how_of_pr, disagreements = {}, {}, []
    for n, p in prs.items():
        answers = pr_ticket_answers(p, plan_ids, arm_ticket, *maps, ticket_files=ticket_files, refused=refused)
        answered[n] = {t for t, _ in answers}
        if answers:
            ticket_of_pr[n], how_of_pr[n] = answers[0]
            if len({t for t, _ in answers}) > 1:
                disagreements.append((n, answers))
    # Every PR the snapshot holds is the port's: the fetch already bounds it to the port's life (PORT_SINCE) and to
    # `nightly/*` and `main` bases, so a PR against main that no ticket claims is work outside the plan to list, not
    # a base to drop.  (Until 2026-09-17 only the bases some ticketed PR targeted survived here, which silently lost
    # every unticketed PR against main -- #868, #869, #873 that day.)
    # The ledger of merged PRs per ticket.  A merge is a fact about the past: once an Update has seen PR #N merged for
    # a ticket, the ticket stays done whether or not a later GitHub answer still lists #N (its day branch is deleted
    # when the day lands on main, and a search can fall short).  The one thing that takes a recorded merge back is
    # GitHub listing #N again as NOT merged -- which cannot happen to a real merge, so it means the record was wrong
    # -- and that is when "ticket regressed" fires.  A later OPEN PR for the ticket (a `(reopens X)` title, or any
    # rule mapping it) puts the ticket in that PR's state by the precedence above without touching the record.
    def ledger(key):  # previous[key]: ticket -> PR numbers, believed only in the plan and only as ints
        d = (previous or {}).get(key)
        return {t: {n for n in v if isinstance(n, int)} for t, v in (d.items() if isinstance(d, dict) else ()) if t in plan_ids and isinstance(v, list)}
    prev_tickets = (previous or {}).get("tickets")
    prev_tickets = prev_tickets if isinstance(prev_tickets, dict) else {}
    recorded = {t: v for t, v in ledger("done_prs").items() if v}
    for tid, t in prev_tickets.items():  # the first Update with a ledger seeds it from the last state's done tickets
        if tid in plan_ids and isinstance(t, dict) and t.get("state") == "done" and isinstance(t.get("pr"), int):
            recorded.setdefault(tid, set()).add(t["pr"])
    lean_arms = set(tree.get("lean_arms") or [])
    missing_files = set(tree.get("missing_files") or [])
    for n, t in ticket_of_pr.items():
        if completes_ticket(prs[n], nodes[t], lean_arms):
            recorded.setdefault(t, set()).add(n)
    # A record that would not complete its ticket today -- a `lean: base:` PR on an S ticket whose arms are not in
    # the table (#909, recorded under the rule before this one) -- is dropped whether GitHub lists it merged or not,
    # and silently: the merge is real, so nothing regressed, and a record that never completed the ticket cannot
    # un-complete it either.  For a record GitHub no longer lists (the ledger's reason to exist: a deleted day
    # branch, a search that fell short) the title comes from the last state's own PR rows, which the last Update
    # that still listed the PR wrote: the rows are rebuilt from the current snapshot every Update, so the title
    # survives exactly one Update past the loss, and a record it condemns is dropped in that same Update, after
    # which nothing remains to bring the ticket back.  A record with no title anywhere is kept, since a merge is a
    # fact about the past; that is the one route by which a base record could read its ticket done again, closed
    # today because the committed previous state carries #909's row, and the `ticket done without its arm` check
    # below says so when the table disagrees.  Keying the unlisted case on the table alone was tried and would drop
    # a real `lean: port` merge whose ticket lists arms the PR did not port (#832 for S-Net-Socket-lifecycle) the
    # first time a snapshot lost it.  A listed record GitHub says is NOT merged is kept here for the regression
    # check just below.
    # A tree fact outranks a record (`deliverable_missing`).  The filter below keeps a record whose PR row is gone
    # anywhere ("a merge is a fact about the past"), and that is the one route by which a record could bring a
    # ticket back; a deliverable the checkout does not hold is not a claim about the past but about this checkout,
    # so it drops the record whatever GitHub still lists, and this is the rule's ONE application: `completes_ticket`
    # is left answering about the PR alone.
    # The record it drops is kept in `dropped_prs` and read back here, so the block outlives the Update that saw the
    # PR last (a ledger-only record would otherwise be gone one Update later, and the ticket launchable again), and a
    # corrected FILES list credits the merge once more.
    for tid, ns in ledger("dropped_prs").items():
        recorded.setdefault(tid, set()).update(ns)
    # A listed PR's refused prefix cannot keep a stale ticket record alive, whether its file list is empty or unknown:
    # an unknown list is no evidence that the PR wrote a deliverable.
    for tid, n in refused:
        if n in prs and tid not in answered[n] and tid in recorded:
            recorded[tid].discard(n)
            if not recorded[tid]:
                del recorded[tid]
    missing_merged = {}
    for tid in [t for t in recorded if deliverable_missing(nodes[t], missing_files)]:
        missing_merged[tid] = (sorted(recorded[tid]), sorted(f for f in nodes[tid]["files"] if f in missing_files))
        del recorded[tid]
    prev_prs = {p["number"]: p for p in ((previous or {}).get("prs") or []) if isinstance(p, dict) and "number" in p}
    for tid in list(recorded):
        node = nodes[tid]
        recorded[tid] = {n for n in recorded[tid]
                         if (row := prs.get(n) or prev_prs.get(n)) is None or completes_ticket(dict(row, merged=True), node, lean_arms)}
        if not recorded[tid]:
            del recorded[tid]
    # ticket -> recorded PRs GitHub now lists as not merged: the record was wrong there.  Carried from the last
    # state too (`unmerged_prs`), so the regression is reported on every Update until a merge records the ticket again.
    unmerged = {t: v for t, v in ledger("unmerged_prs").items() if v}
    for tid in list(recorded):
        wrong = {n for n in recorded[tid] if n in prs and not prs[n].get("merged")}
        if wrong:
            unmerged.setdefault(tid, set()).update(wrong)
            recorded[tid] -= wrong
        if not recorded[tid]:
            del recorded[tid]
    for tid in list(unmerged):
        if recorded.get(tid):
            del unmerged[tid]
    # A listed merge the ledger holds and no rule reaches any more (its window closed, say) is still the ticket's PR:
    # it is attributed from the record rather than reported as work outside the plan.  One recorded for a ticket and
    # mapped today to another is a disagreement between the record and the rules, reported, and the record stands.
    ledger_disputes = []
    for tid, ns in sorted(recorded.items()):
        for n in sorted(ns):
            if n not in prs or not prs[n].get("merged"):
                continue
            if n not in ticket_of_pr:
                ticket_of_pr[n], how_of_pr[n] = tid, f"the ledger records this merge for {tid}"
            elif ticket_of_pr[n] != tid:
                ledger_disputes.append((n, tid, ticket_of_pr[n]))


    pr_of_branch = {}
    for n, p in sorted(prs.items()):
        if p.get("head"):
            pr_of_branch[p["head"]] = n  # the newest PR on a branch wins

    # windows -> tickets
    # The kit's own windows (the lead, its jobs) run in the main checkout; every agent runs in a worktree under
    # <main>/.claude/worktrees/.  So the main checkout is the worktree some other window's worktree lies under,
    # and a window there is the kit's whatever it is called -- no name list needed beyond the kit's known services.
    wts = [os.path.normpath(w["worktree"]) for w in live if w.get("worktree")]
    main_wts = {r for r in wts if any(x.startswith(r + "/.claude/worktrees/") for x in wts)}
    win_rows = []
    for w in live:
        name = w["window"]
        service = is_job_window(name) or (bool(w.get("worktree")) and os.path.normpath(w["worktree"]) in main_wts)
        t = None if service else window_ticket(w, plan_ids, pr_of_branch, ticket_of_pr)
        kind = ("service" if service else "deep review" if name.startswith("deep-review-")
                else "review" if name.startswith(("review-", "fix-", "finish-")) else "ticket" if t else "other")
        pr = pr_of_branch.get(w.get("branch", ""))
        m = re.match(r"deep-review-(\d+)$", name)
        if m:
            pr = int(m.group(1))
        win_rows.append(dict(w, ticket=t, kind=kind, pr=pr))

    # verdicts per PR: the author's (its ticket window's report or pane) and the deep review's
    window_of_slug = {slug: w for w, slug in launches.items()}

    def report_ticket(stem):
        if stem in plan_ids:
            return stem
        w = window_of_slug.get(stem)
        if w in plan_ids:
            return w
        return slug_ticket(stem, plan_ids)

    pr_rows = {}
    for n, p in sorted(prs.items()):
        t = ticket_of_pr.get(n)
        author, author_from = None, ""
        for stem, r in rep.items():
            if r["kind"] != "author" or not r["verdict"]:
                continue
            rt = report_ticket(stem)
            speaks = (t is not None and rt == t) or (r.get("pr") == n and rt in (None, t)) or (rt is None and stem == p.get("head", "").split("/")[-1])
            if speaks and r["at"] > author_from:
                author, author_from = r["verdict"], r["at"]
        for w in win_rows:  # the pane's own verdict line, when the window sits at one
            if w.get("pr") == n and w.get("kind") in ("ticket", "other") and w.get("state") == "VERDICT":
                words = VERDICT.findall(w.get("last_line") or "")
                if words:
                    author, author_from = words[-1], windows.get("generated_at")
        # The record comes first because it is the one bound to a head: a `deep-review-<PR>.md` in this checkout
        # answers with the last verdict word it ends with, whatever diff that was for, so a record at this head
        # overrides it and a record at an earlier head leaves it to answer as before.  `stale` is that earlier
        # head: a deep review happened, the diff moved since, and another round is owed -- which `none`, the word
        # for a PR no deep review ever read, does not say.  The author verdict above keeps its looser sources (the
        # report tail, the pane's last line), so the two halves of this row are not read to the same standard: a
        # row can carry an author MERGE whose record the gate refuses as stale, and `gate.sh` remains what says a
        # PR may merge.
        deep = rep.get(f"deep-review-{n}", {})
        deep_verdict = record_verdict(p, "deep", rep) or deep.get("verdict")
        deep_records = any(r.get("pr") == n and r.get("reviewer") == "deep" and r.get("verdict")
                           for src in list(rep.values()) + [p] for r in (src.get("records") or []))
        deep_state = ("verdict" if deep_verdict else "running" if any(w["window"] == f"deep-review-{n}" for w in live)
                      else "launched" if n in deep_launched else "stale" if deep_records else "none")
        queue = pr_queue(p, author, deep_verdict, deep_state)
        family_errors = []
        arms, spec_paths, files_known = pr_arms(p, tree.get("arm_files") or {}, errors=family_errors)
        author_windows = sorted({w["window"] for w in win_rows if w.get("pr") == n and w["kind"] in ("ticket", "other")}
                                | set(record_windows.get(n, [])))
        pr_rows[n] = dict(p, ticket=t, ticket_how=how_of_pr.get(n), author_verdict=author, deep_verdict=deep_verdict,
                          deep_state=deep_state, queue=queue, kind=None if t else outside_kind(p), arms=arms, spec_paths=spec_paths,
                          files_known=files_known, family_error="; ".join(family_errors) or None, author_windows=author_windows,
                          windows=sorted(w["window"] for w in win_rows if w.get("pr") == n))

    # tickets
    prs_of_ticket = {}
    for n, r in pr_rows.items():
        if r["ticket"]:
            prs_of_ticket.setdefault(r["ticket"], []).append(r)
    windows_of_ticket = {}
    for w in win_rows:
        if w["ticket"] and w["kind"] == "ticket":
            windows_of_ticket.setdefault(w["ticket"], []).append(w["window"])
    tickets = {}
    order = list(nodes)
    overrides = {t: v for t, v in (overrides or {}).items()
                if t in plan_ids and isinstance(v, dict) and v.get("state") in STATES}
    done = {tid for tid in order if recorded.get(tid) or overrides.get(tid, {}).get("state") == "done"}  # blocked reads the deps' states
    # A milestone (track M) is done once every dependency is (ticket_state), which a milestone depending on a
    # milestone learns only after the first is marked, so the pass repeats until `done` is a fixpoint; the loop
    # is over a finite set that only grows, so it ends.
    while True:
        done_before = set(done)
        tickets = {}
        for tid in order:
            n = nodes[tid]
            rows = prs_of_ticket.get(tid, [])
            merged = sorted(recorded.get(tid, ()))
            open_rows = [r for r in rows if r["state"] == "open"]
            followups = sorted(r["number"] for r in open_rows) if merged and not any(pr_reopens(r, tid, plan_ids) for r in open_rows) else []
            open_prs = [dict(number=r["number"], queue=r["queue"]) for r in open_rows if r["number"] not in followups]
            deps_open_list = sorted(d for d in n.get("deps", []) if d not in done)
            deps_done = not deps_open_list
            st, why = ticket_state(open_prs, merged, windows_of_ticket.get(tid, []), deps_done, deps_open_list,
                                   milestone=n.get("track") == "M", human=bool(n.get("human")))
            if st == "todo" and tid in missing_merged:
                ns, paths = missing_merged[tid]
                st, why = "blocked", (f"PR #{ns[-1]} merged, but the plan's FILES name {', '.join(paths)}, "
                                      "which this checkout lacks: correct the plan if the file moved, or record the ticket by hand")
            if tid in overrides:  # the manual escape for a ticket closed with no PR: wins over every derived rule
                st, why = overrides[tid]["state"], f"recorded by hand: {overrides[tid].get('reason', 'no reason given')}"
            if st == "done":
                done.add(tid)
            if followups:
                why += "; follow-up " + ", ".join(f"#{m}" for m in followups) + " open"
            pr = (sorted(open_prs, key=lambda x: -x["number"])[0]["number"] if open_prs else max(merged) if merged else None)
            prr = pr_rows.get(pr) if pr else None
            if st == "done" and pr is not None and str(pr) not in (github.get("prs") or {}):
                why += " (recorded at an earlier Update; GitHub no longer lists it)"
            tickets[tid] = dict(state=st, reason=why, pr=pr, branch=prr["head"] if prr else None,
                                queue=prr["queue"] if prr and prr["state"] == "open" else None,
                                windows=windows_of_ticket.get(tid, []), deps_open=sorted(d for d in n.get("deps", []) if d not in done),
                                author_verdict=prr["author_verdict"] if prr else None, deep_verdict=prr["deep_verdict"] if prr else None,
                                prs=sorted({r["number"] for r in rows} | set(merged)), followups=followups)
        if done == done_before:
            break

    # contradictions.  A ticket regressed when a merge made it done and GitHub now lists that PR as not merged --
    # `unmerged` above, carried forward so it is reported on every Update until a merge records the ticket again.
    # Nothing else is a regression: a done ticket with a later open PR is in that PR's state, a ticket whose merged
    # PR GitHub stopped listing is still done (the ledger), and a ticket the hand-kept progress.json once said done
    # with no PR behind it (P2, P3, P5 and T5 on 2026-09-17: process tickets closed by hand, and T5 whose PR #719 no
    # rule reaches) was never derived done, so it cannot fall out of it -- nothing here comes from a hand-kept file.
    # `ever_done` is what a merge ever made done: the ledger's keys plus the tickets that lost theirs.
    found = []
    for tid, (ns, paths) in sorted(missing_merged.items()):
        found.append(dict(kind="merged ticket missing a deliverable", subject=tid,
                          text=f"{tid}: merged PRs {', '.join('#' + str(n) for n in ns)}; "
                               f"the plan's FILES name {', '.join(paths)}, which this checkout lacks; an override settles the "
                               "ticket's state but not this entry: correct the plan's FILES"))
    ever_done = (set(recorded) | set(unmerged)) & plan_ids
    for tid in sorted(unmerged):
        t = tickets[tid]
        found.append(dict(kind="ticket regressed", subject=tid,
                          text=f"{tid} was done at an earlier Update; the sources now say {STATE_LABEL[t['state']]} ({t['reason']}); "
                               f"GitHub lists its PR {', '.join('#' + str(n) for n in sorted(unmerged[tid]))} as not merged"))
    for n, tid, now in ledger_disputes:
        found.append(dict(kind="PR recorded for another ticket", subject=f"#{n}",
                          text=f"#{n} is recorded as {tid}'s merge but the rules now map it to {now} ({how_of_pr.get(n)}); both tickets count it"))
    for n, answers in disagreements:
        found.append(dict(kind="PR maps to two tickets", subject=f"#{n}",
                          text=f"#{n}: " + "; ".join(f"{t} ({how})" for t, how in answers) + f" -- {answers[0][0]} was taken"))
    for rocq, par in sorted((tree.get("parity") or {}).items()):
        if par.get("claimed") and (par.get("missing") or par.get("drifted")):
            found.append(dict(kind="parity", subject=rocq,
                              text=f"{rocq}: the Lean twin claims parity but " + (f"{par['missing']} definitions are missing" if par.get("missing") else "its Rocq file has drifted since its baseline")))
    slots_total, slots_busy = windows.get("build_slots"), windows.get("build_slots_busy")
    if isinstance(slots_total, int) and isinstance(slots_busy, int) and slots_busy > slots_total:
        found.append(dict(kind="build slots over capacity", subject="build slots",
                          text=f"the export says {slots_busy} build slots are busy of {slots_total}: the kit's slot count and its lock files disagree"))

    # what changed since the previous Update, so the page can say so without a hand-written log
    prev_queue = {n: p.get("queue") for n, p in prev_prs.items()}
    delta = dict(since=(previous or {}).get("freshness", {}).get("github") if isinstance((previous or {}).get("freshness"), dict) else None,
                 prs_opened=sorted(n for n in pr_rows if n not in prev_prs and pr_rows[n]["state"] == "open"),
                 prs_merged=sorted(n for n, r in pr_rows.items() if r["merged"] and not prev_prs.get(n, {}).get("merged")),
                 turned_mergeable=sorted(n for n, r in pr_rows.items() if r["queue"] == "mergeable" and prev_queue.get(n) not in (None, "mergeable") ),
                 turned_conflicting=sorted(n for n, r in pr_rows.items() if r["queue"] == "conflicting" and prev_queue.get(n) not in (None, "conflicting")),
                 tickets_done=sorted(t for t, v in tickets.items() if v["state"] == "done" and prev_tickets.get(t, {}).get("state") != "done") if prev_tickets else [],
                 contradictions_before=len((previous or {}).get("contradictions") or []) if isinstance((previous or {}).get("contradictions"), list) else None,
                 contradictions_now=len(found))

    # what needs a human, derived: mergeable PRs wait on the coordinator, windows at a verdict or parked, limited accounts
    needs = []
    for n, r in sorted(pr_rows.items()):
        if r["queue"] == "mergeable":
            needs.append(dict(kind="merge", text=f"#{n} ({r['ticket'] or r['head']}) has both verdicts and no conflict: the coordinator merges it"))
    for w in win_rows:
        if w.get("state") == "VERDICT" and w["kind"] in ("ticket", "review", "deep review", "other"):
            needs.append(dict(kind="verdict", text=f"window {w['window']} sits at a verdict{(' for #' + str(w['pr'])) if w.get('pr') else ''}: read it, merge or answer"))
        if w.get("state") == "LIMIT":
            needs.append(dict(kind="parked", text=f"window {w['window']} is parked on a usage limit"))
    for a in windows.get("accounts") or []:
        if isinstance(a, dict) and a.get("state") not in (None, "ok"):
            needs.append(dict(kind="account", text=f"account {a.get('account')} is {a.get('state')}"))
    for n, r in sorted(pr_rows.items()):
        if r["queue"] == "conflicting":
            needs.append(dict(kind="rebase", text=f"#{n} ({r['ticket'] or r['head']}) conflicts with the day branch: its author window rebases"))
    # Work outside the plan: the agent windows and the PRs no ticket claims.  They are real work and are listed as
    # such, by kind, with what they touch; a contradiction is reserved for the cases the plan should have covered --
    # a window on a ticket's branch shape (lean/, spec/) that names no ticket, and a PR that changes a Lean spec,
    # registry or pin file and names no arm (or whose files GitHub did not answer, which is reported, not guessed).
    outside_windows = []
    for w in win_rows:
        if w["kind"] in ("other", "review"):
            outside_windows.append(dict(window=w["window"], branch=w.get("branch"), pr=w.get("pr"), kind=w["kind"], state=w.get("state"), host=w.get("host")))
        if w["kind"] == "other" and PORT_BRANCH.match(w.get("branch") or ""):
            found.append(dict(kind="window with no ticket", subject=w["window"],
                              text=f"window {w['window']} is on a ticket branch shape ({w.get('branch')}) but names no ticket"))
        if w.get("state") == "VERDICT" and w["kind"] in ("ticket", "other") and not w.get("pr"):
            found.append(dict(kind="verdict without a PR", subject=w["window"],
                              text=f"window {w['window']} shows a verdict but its branch {w.get('branch') or '?'} has no PR"))
    outside_prs = []
    for n, r in sorted(pr_rows.items(), reverse=True):
        if r["ticket"]:
            continue
        outside_prs.append(dict(number=n, title=r["title"], head=r["head"], base=r["base"], state=r["state"], merged=r["merged"], url=r["url"],
                                merged_at=r.get("merged_at"), created=r.get("created"), queue=r["queue"], kind=r["kind"], arms=r["arms"],
                                spec_paths=r["spec_paths"], files=(r.get("files") or [])[:12] if r["files_known"] else None,
                                family_error=r["family_error"], author_windows=r["author_windows"], ticket_line=r.get("ticket_line")))
        if r["state"] == "closed":
            continue
        if not r["files_known"]:
            found.append(dict(kind="PR with no ticket", subject=f"#{n}",
                              text=f"#{n} ({r['head']}: {r['title'][:60]}) maps to no ticket and GitHub did not answer which files it touches"))
        elif r["spec_paths"] and not r["arms"]:
            found.append(dict(kind="PR with no ticket", subject=f"#{n}",
                              text=f"#{n} ({r['head']}: {r['title'][:60]}) changes {r['spec_paths'][0].split('LinuxProcessSem/')[-1]}"
                                   + (f" and {len(r['spec_paths']) - 1} more" if len(r['spec_paths']) > 1 else "") + " but names no ticket and no arm"))
    outside_counts = {}
    for o in outside_prs:
        outside_counts[o["kind"]] = outside_counts.get(o["kind"], 0) + 1
    outside = dict(prs=outside_prs, windows=sorted(outside_windows, key=lambda w: w["window"]), counts=outside_counts,
                   merged=sum(1 for o in outside_prs if o["merged"]), open=sum(1 for o in outside_prs if o["state"] == "open"))
    for arm in sorted(lean_arms):
        t = arm_ticket.get(arm)
        if not t:
            found.append(dict(kind="arm without a ticket", subject=arm, text=f"arm {arm} is in the Lean table but no ticket ports it"))
        elif not recorded.get(t):  # a later open PR puts the ticket past done; the arm is still in the table by a merge
            found.append(dict(kind="arm without a merged PR", subject=arm,
                              text=f"arm {arm} is in the Lean table but its ticket {t} is {STATE_LABEL[tickets.get(t, {}).get('state', 'todo')]} and has no merged PR"))
    for tid, n in sorted(nodes.items()):
        if n.get("track") == "S" and tickets[tid]["state"] == "done":
            missing = [a for a in n.get("syscalls", []) or [] if a not in lean_arms]
            if missing:
                found.append(dict(kind="ticket done without its arm", subject=tid,
                                  text=f"{tid} is done (PR #{tickets[tid]['pr']}) but {', '.join(missing)} is not in the Lean table"))

    # The window, PR and arm kinds above were appended after the delta was built, so its
    # "now" count missed every one of them: the committed state carried 11 contradictions
    # beside a delta reading `12 -> 0`.  Count the finished list.
    delta["contradictions_now"] = len(found)

    counts = {s: 0 for s in STATES}
    for t in tickets.values():
        counts[t["state"]] += 1
    queues = {q: 0 for q in QUEUES}
    for r in pr_rows.values():
        queues[r["queue"]] += 1
    win_states = {}
    for w in win_rows:
        if w["kind"] != "service":
            win_states[w.get("state") or "?"] = win_states.get(w.get("state") or "?", 0) + 1
    return dict(
        day=day or github.get("base") or DEFAULT_DAY,
        freshness=dict(github=github.get("as_of"), windows=windows.get("generated_at"), reports=reports.get("as_of"),
                       tree=tree.get("sha"), launches=len(launches)),
        counts=counts, queues=queues, window_states=win_states,
        tickets=tickets, prs=[pr_rows[n] for n in sorted(pr_rows, reverse=True)],
        windows=sorted(win_rows, key=lambda w: w["window"]), accounts=windows.get("accounts") or [],
        build_slots=dict(total=windows.get("build_slots"), busy=windows.get("build_slots_busy")),
        hosts=[dict(h) for h in (windows.get("hosts") or []) if isinstance(h, dict)],
        unreachable_windows=sorted(windows.get("unreachable_windows") or []),
        tree=dict(sha=tree.get("sha"), arms_total=tree.get("arms_total"), lean_arms=tree.get("lean_arms") or [],
                  lean_files=tree.get("lean_files") or [], parity=tree.get("parity") or {},
                  parity_summary=dict(twins=len(tree.get("parity") or {}), claiming=sum(1 for p in (tree.get("parity") or {}).values() if p.get("claimed")),
                                      missing=sum(1 for p in (tree.get("parity") or {}).values() if p.get("claimed") and p.get("missing")))),
        ever_done=sorted(ever_done), done_prs={t: sorted(v) for t, v in sorted(recorded.items())},
        dropped_prs={t: ns for t, (ns, _) in sorted(missing_merged.items())},
        unmerged_prs={t: sorted(v) for t, v in sorted(unmerged.items())}, outside=outside,
        contradictions=found, delta=delta, needs=needs)


def progress_from_state(state, previous, updated=None):
    """The derived progress.json: the same shape the pages already read, with the derived states."""
    prog = dict(updated=updated or (previous or {}).get("updated", ""), today=(previous or {}).get("today", ""),
                today_at=(previous or {}).get("today_at", ""), tickets={}, prs=[])
    for tid, t in sorted(state["tickets"].items()):
        if t["state"] == "todo" and not t["pr"]:
            continue
        e = dict(state=t["state"])
        if t["pr"]:
            e["pr"] = t["pr"]
        if t["branch"]:
            e["branch"] = t["branch"]
        prog["tickets"][tid] = e
    for r in state["prs"]:
        review = ("approved" if r["queue"] == "mergeable" else "fixes_pending" if r["author_verdict"] in ("MERGE AFTER FIXES", "DO NOT MERGE")
                  else "in_review" if r["queue"] in ("awaiting deep review", "conflicting") or r["author_verdict"] else "needs_review")
        prog["prs"].append(dict(number=r["number"], title=r["title"], branch=r["head"], state=r["state"], merged=r["merged"],
                                review=review if r["state"] == "open" else None, url=r["url"]))
    prog["prs"].sort(key=lambda p: p["number"])
    return prog


# --------------------------------------------------------------------------
# Driving it
# --------------------------------------------------------------------------

def kept_github_path(ops_dir):
    return os.path.join(ops_dir, "state", "github-snapshot.json")


def previous_github(ops_dir):
    """The snapshot fetch_github reuses files from: the newer, by `as_of`, of the committed data/github.json and the
    copy the last refresh kept under the ops kit.

    Why a kept copy.  Both refreshers run in a checkout they reset to the day tip before every pass (launch_watch.py's
    state checkout, pages-publish's docs worktree), so the snapshot a pass wrote is gone by the next one and the
    `previous` it reads is whatever was last COMMITTED -- on 2026-09-23 the copy of 09-19, which ends at #1091.  Every
    PR since then is one `gh pr view --json files` per pass: 131 of them (measured by running this function with the
    file views stubbed), 147 GraphQL points a pass, and launch-watch passes about fifteen times an hour (the 244-264 s
    burst gaps).  With the kept copy a pass asks only for the PRs whose `updatedAt` moved since the last one.  It
    changes which previous fetch_github reads, not what it may reuse from it: its own rule (fetch_github's docstring)
    is applied to a newer previous.

    The kept copy is always the newer once a refresh has run, so a hand correction to data/github.json is not read
    until state/github-snapshot.json is deleted."""
    committed = load_json(GITHUB, None)
    kept = load_json(kept_github_path(ops_dir), None)
    snaps = [x for x in (committed, kept) if isinstance(x, dict) and isinstance(x.get("prs"), dict)]
    return max(snaps, key=lambda x: str(x.get("as_of") or "")) if snaps else committed


def keep_github(ops_dir, g):
    """Keep this refresh's snapshot under the ops kit (atomically), where the next pass of either refresher finds it.
    A checkout with no kit beside it (CI, a hand run elsewhere) keeps nothing."""
    d = os.path.join(ops_dir, "state")
    if not os.path.isdir(d):
        return False
    tmp = f"{kept_github_path(ops_dir)}.{os.getpid()}"
    with open(tmp, "w") as f:
        json.dump(g, f, sort_keys=True)
    os.replace(tmp, kept_github_path(ops_dir))
    return True


def refresh_sources(ops_dir=OPS_DIR, base=None, run=subprocess.run, log=print):
    """Re-read (a), (b) and (d) into their snapshots.  Each source that cannot be read keeps its committed copy."""
    base = base or day_branch()
    log("state: exporting the windows (export_state.sh)")
    w = export_windows(ops_dir, run=run, log=log)
    if w is None:
        log(f"state: no ops export under {ops_dir}; keeping data/windows.json")
    else:
        dump_json(WINDOWS, w)
        log(f"state: {len(w['windows'])} windows as of {w.get('generated_at')}")
    log(f"state: fetching every PR merged, closed or opened since {PORT_SINCE} from GitHub")
    g = fetch_github(base, run=run, log=log, previous=previous_github(ops_dir))
    if g is None:
        log("state: GitHub unreachable; keeping data/github.json")
    else:
        dump_json(GITHUB, g)
        keep_github(ops_dir, g)
        log(f"state: {len(g['prs'])} PRs as of {g['as_of']}")
    log("state: reading the reports")
    r = read_reports(os.path.join(ops_dir, "reports"))
    if r["reports"]:
        dump_json(REPORTS, r)
        log(f"state: {len(r['reports'])} reports, newest {r['as_of']}")
    else:
        log(f"state: no reports under {ops_dir}; keeping data/reports.json")


def derive_and_write(updated=None, inventory=None, log=print, root=ROOT):
    """Derive from the committed snapshots and this checkout; write state.json and progress.json."""
    plan = load_json(PLAN, {"nodes": []})
    inv = inventory if inventory is not None else load_json(INVENTORY, {})
    previous_progress = load_json(progress.PROGRESS, {})
    previous = load_json(STATE, None) or previous_progress  # the last derived state; the hand-kept file only the first time
    log("state: reading the tree (arms, twins, parity)")
    tree = tree_facts(inv, root=root, plan=plan)
    log("state: reading local git history for merges a stale snapshot might miss")
    git_merges = git_merge_rows(root=root, log=log)
    log("state: deriving ticket and PR state")
    st = derive(plan, load_json(GITHUB, {}), load_json(WINDOWS, {}), load_json(REPORTS, {}), tree, previous,
               git_merges=git_merges, overrides=load_json(OVERRIDES, {}))
    dump_json(STATE, st)
    prog = progress_from_state(st, previous_progress, updated=updated)
    progress.save(prog, path=progress.PROGRESS)  # the path as it is now: `save`'s default was bound when the module loaded
    c = st["counts"]
    log(f"state: {c['done']} done, {c['in_review'] + c['deep_review'] + c['mergeable'] + c['conflicting']} in review, "
        f"{c['in_progress']} in progress, {c['blocked']} blocked, {c['todo']} not started; {len(st['contradictions'])} contradictions")
    return st


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--refresh", action="store_true", help="re-read the ops export, GitHub and the reports, then derive")
    ap.add_argument("--derive", action="store_true", help="derive from the committed snapshots and this checkout")
    ap.add_argument("--json", action="store_true", help="print the derived state")
    ap.add_argument("--ops-dir", default=OPS_DIR)
    a = ap.parse_args(argv)
    if a.refresh:
        refresh_sources(a.ops_dir)
        derive_and_write(updated=progress.now_utc())
    elif a.derive:
        derive_and_write()
    if a.json:
        json.dump(load_json(STATE, {}), sys.stdout, indent=1)
        return 0
    if not (a.refresh or a.derive):
        ap.print_help()
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
