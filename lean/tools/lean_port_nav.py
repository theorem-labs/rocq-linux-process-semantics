"""The one place the Lean port's site navigation is defined.

Every page under docs/lean-port/ is rendered from a template under
tools/lean_port_templates/ by one of four generators (lean_port_status.py,
lean_port_graph.py, lean_port_budget.py, specdeps.py).  Each template carries
two placeholders that this module fills, so the bar, the top strip, the
breadcrumb and each page's one-line role exist once:

    <!--__NAV__-->        the shared bar, the top strip, then the "you are here" line
    <!--__ROLE__-->       the page's question: what it answers and what it does not

The reading order rides on the breadcrumb, which carries the previous and next
page: a second copy at the foot of the page bought nothing and cost every page
57px of the one screen the folded components have to fit in.

The reading order is the order of PAGES, and PAGES is in three groups, ordered
by what a reader deciding about the project needs first rather than by what the
fleet looks at most.  BAR_GROUP, the first, is the only one the bar spells out:
the whole project in plain language (TL;DR), how far along it is (Progress),
what it costs (Budget), and how the work is actually done (How it works).  The
two after it sit behind the bar's `More` disclosure -- `now`, the three pages
that answer what is happening at this minute (Pipeline, Outside the plan,
Machines), and `reference`, the six that answer where a detail lives (System
map, Board, Ticket graph, Dependency ledger, Plan, Parallelism).

Four visible PAGE links is the point.  The bar carried nine, each a page
someone needed once; a reader who has to choose between nine cannot see that
the first one answers their question.  Nothing was deleted to get to four:
every page is one click away, in a labelled group, and the pages the fleet
lives in keep their own shortcut at the end of the bar.  Four is the count of
page links this file writes, not of everything a reader can click: the bar
also carries the `what needs a human` shortcut, and lp-glossary.js appends its
own link at run time, so the rendered bar has two more than the static one.  A page belongs in the bar when
someone who has never seen this project would open it; in `now` when a reader
who looked an hour ago would look again; in `reference` when they would not.

A page's role sentence is the only copy; the site map on the Progress page
renders the same sentences from the same list.

The top strip is the same on every page: arms merged on main and on the day
branch, PRs open and how many are mergeable now, the work no ticket names,
windows working / at a verdict / idle / parked, contradictions, when the state
was last updated, the Update button, and one freshness line per source (GitHub,
the window export, the reports, the tree).  Its numbers come from the payloads
the running `--write` computed (`strip_facts`' arguments: the state, the
inventory, progress.json, the arms and outside payloads) and, for the money
tile, from data/budget.json read at render time; a caller that passes nothing
gets the committed data files instead, and a page rendered without them shows
dashes rather than a number nobody computed.
"""
import json
import os
from html import escape

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DOCS = os.path.join(ROOT, "docs", "lean-port")

# (key, file, short label, the question the page answers and what it is not, group)
PAGES = [
    ("tldr", "tldr.html", "TL;DR",
     "What is being built, why, how far along it is, what it has cost and what could go wrong -- "
     "the whole project in plain language, for a reader who has never seen it. Every other page is "
     "a detail of this one.", "story"),
    ("index", "index.html", "Progress",
     "How many syscall arms are done, how deeply are they verified, and how fast are they landing? "
     "Not what any one PR is waiting on: that is Pipeline.", "story"),
    ("budget", "budget.html", "Budget",
     "What has the port cost so far, what does a merged arm cost, and what will the rest cost? "
     "Not where any ticket's state lives: that is Progress.", "story"),
    ("architecture", "architecture.html", "How it works",
     "How is the work actually done -- the machines, the agents in their windows, the steps a "
     "change goes through, the branches, the rails that stop a wrong answer, and where it jams? "
     "Not how far along any of it is: that is Progress.", "story"),
    ("pipeline", "pipeline.html", "Pipeline",
     "What is landing today? Every open PR, the stage it is in, who owns it, how long it has waited "
     "and the exact next action. Not what the change contains: follow the link.", "now"),
    ("outside", "outside.html", "Outside the plan",
     "What is being done that no plan ticket names -- fixes, guards, the kit, CI, docs, the Rocq model? "
     "It counts in the day's totals and it is not a contradiction.", "now"),
    ("machines", "machines.html", "Machines",
     "Is the machinery running? Windows per host, load, each standing job's last pass, and the incidents. "
     "Not what those windows are working on: that is Pipeline.", "now"),
    ("map", "map.html", "System map",
     "Who does what, on which machine, and what the work is checked against -- the whole system as one "
     "picture, in plain words. Not how far along it is: that is Progress; not each step in detail: that is How it works.",
     "reference"),
    ("board", "board.html", "Board",
     "What state is each spec file and each dispatcher arm in, and how has Rocq moved under them? "
     "Not the plan, not the ticket list, not the money.", "reference"),
    ("graph", "graph.html", "Ticket graph",
     "What depends on what, and what is next? Each ticket's scope, state, slack and the critical path. "
     "Not the per-file inventory and not the narrative.", "reference"),
    ("ledger", "ledger.html", "Dependency ledger",
     "Which Rocq definitions does each syscall's spec reach, and in what order to port them? "
     "Not where tickets, file sizes or progress live.", "reference"),
    ("plan", "plan.html", "Plan",
     "What is left, in what order, and which decisions wait on the owner? Why the port is shaped this way and "
     "how tests are judged. Its figures are the per-track ticket counts and the states beside each ticket, both "
     "computed at every Update; any other number lives on another page and is linked instead of repeated.",
     "reference"),
    ("parallelism", "parallelism.html", "Parallelism",
     "What changes if more agents run at once, or fewer? Days to finish and cost against the number of agents, "
     "recomputed from the work left and the port's merge pace on dated assumptions.", "reference"),
]
KEYS = [p[0] for p in PAGES]
GROUPS = (("story", "The project"), ("now", "Today"), ("reference", "Reference"))
BAR_GROUP = GROUPS[0][0]   # the one group the bar spells out; the others sit behind its `More` disclosure
ASSETS = ["lp-common.css", "lp-update.js", "lp-glossary.js", "lp-age.js"]  # shared by every page; copied beside the pages by the generator
# How old the data behind a page may be before the strip's age turns red (the owner's ask of 2026-09-25).  The age is
# measured from the stamp, which the generator takes when it derives the state, before it renders the pages.  So the
# oldest a healthy page gets is one press spacing plus what an Update does after its stamp.  jobs/dash-preview.sh
# presses every fifteen minutes, on its 180 s pass, so presses land up to eighteen minutes apart.  After the stamp an
# Update derives the state, scans main, the kit and the records, writes the graph twice, scans the budget and renders
# the pages.  No Update has been timed from its stamp to its last write; only parts of one have: `--render-into` over
# the committed data took 15 s on 2026-09-25, and all_outputs (the inventory and every page, writing nothing) 10 s on
# 2026-09-26.  The scans of main, the kit and the records are not timed.  Thirty minutes leaves twelve for the whole
# of it.  It is a threshold, not a bound: lean_port_serve.run_generator allows a generation thirty minutes, and one
# slower than twelve turns the age red on purpose, since a generation that slow is worth looking at as much as a
# missed press, a stopped job or a stopped server.
LP_DATA_RED_MINUTES = 30

STYLE = """<style>
  .lp-nav { display: flex; flex-wrap: wrap; align-items: center; gap: 4px 18px; padding: 6px 20px; border-bottom: 1px solid rgba(127,127,127,0.35); font-family: "Archivo", "IBM Plex Sans", "Helvetica Neue", Arial, sans-serif; font-size: 13.5px; }
  .lp-nav .lp-brand { font-weight: 700; letter-spacing: 0.06em; text-transform: uppercase; font-size: 12px; opacity: 0.7; margin-right: 6px; }
  .lp-nav a { color: inherit; text-decoration: none; padding: 3px 2px; border-bottom: 2px solid transparent; opacity: 0.8; }
  .lp-nav a:hover, .lp-nav a:focus-visible { opacity: 1; border-bottom-color: currentColor; outline: none; }
  .lp-nav a[aria-current="page"] { opacity: 1; font-weight: 600; border-bottom-color: currentColor; }
  .lp-nav .lp-sep { width: 1px; height: 15px; background: currentColor; opacity: 0.25; margin: 0 -6px; }
  .lp-nav .lp-status { margin-left: auto; opacity: 0.7; }
  /* the rest of the site, behind one disclosure.  Absolutely positioned so opening it draws OVER the
     page instead of pushing every component down a panel's height -- the fold budget is measured with
     it shut, and a reader who opens it has not changed the page underneath. */
  .lp-more { position: relative; }
  .lp-more > summary { list-style: none; cursor: pointer; padding: 3px 2px; opacity: 0.8; border-bottom: 2px solid transparent; }
  .lp-more > summary::-webkit-details-marker { display: none; }
  .lp-more > summary:hover, .lp-more > summary:focus-visible { opacity: 1; border-bottom-color: currentColor; outline: none; }
  .lp-more[data-here] > summary { opacity: 1; font-weight: 600; border-bottom-color: currentColor; }
  .lp-more .lp-menu { position: absolute; z-index: 30; top: calc(100% + 6px); left: 0; min-width: 210px; padding: 8px 4px; border: 1px solid rgba(127,127,127,0.45); border-radius: 5px; background: var(--lp-surface, #fff); box-shadow: 0 6px 18px rgba(0,0,0,0.18); }
  .lp-more .lp-menu a { display: block; padding: 4px 12px; border-bottom: none; }
  .lp-more .lp-menu a:hover, .lp-more .lp-menu a:focus-visible { background: rgba(127,127,127,0.14); border-bottom: none; }
  .lp-more .lp-menu .lp-menu-h { margin: 6px 12px 2px; font-size: 10.5px; text-transform: uppercase; letter-spacing: 0.08em; opacity: 0.6; font-weight: 700; }
  /* the per-source freshness, behind its own disclosure: four stamps nobody reads on the way to a
     number, and one line of chrome every page pays for */
  .lp-fresh-d > summary { padding: 3px 16px; font-family: "Archivo", "IBM Plex Sans", "Helvetica Neue", Arial, sans-serif; font-size: 11.5px; opacity: 0.65; cursor: pointer; border-bottom: 1px solid rgba(127,127,127,0.18); }
  .lp-fresh-d[open] > summary { border-bottom: none; }
  .lp-fresh-d > summary:hover, .lp-fresh-d > summary:focus-visible { opacity: 1; outline: none; }
  .lp-fresh-d > summary .warn { opacity: 1; font-weight: 600; }
  .lp-crumb { display: flex; flex-wrap: wrap; align-items: baseline; gap: 4px 14px; padding: 4px 20px; font-family: "Archivo", "IBM Plex Sans", "Helvetica Neue", Arial, sans-serif; font-size: 12.5px; opacity: 0.75; border-bottom: 1px solid rgba(127,127,127,0.18); }
  .lp-crumb a { color: inherit; }
  .lp-crumb .lp-pn { margin-left: auto; display: flex; gap: 14px; }
  .lp-role { font-family: "Archivo", "IBM Plex Sans", "Helvetica Neue", Arial, sans-serif; font-size: 14px; line-height: 1.5; opacity: 0.8; max-width: 72ch; margin: 4px 0 0; }
  /* the way back to the story from a page of figures: this site's root is Progress, and a reader
     who arrives at a table of numbers has no way to know the explanation exists. */
  .lp-newhere { font-family: "Archivo", "IBM Plex Sans", "Helvetica Neue", Arial, sans-serif; font-size: 13px; line-height: 1.4; margin: 6px 0 0; opacity: 0.9; }
</style>"""


def script_payload(payload):
    """`payload` as JSON for embedding in an HTML `<script>`, with every `<` escaped as `\\u003c`.

    HTML ends a script at the first `</script>` in the raw text, before any JavaScript runs, so a
    string in the payload that CONTAINS one closes the script and everything after it is parsed as
    markup.  The payloads here carry pull-request titles, window pane lines and ticket prose --
    text a person outside this repository can choose -- so the sequence has to be escaped.

    The escape is on `<` alone rather than on `</`, and the difference is a second attack the
    narrower rule leaves open: `<!--<script` contains no `</`, survives a `</`-only escape
    verbatim, and puts the tokenizer into script-data-double-escaped state, where the page's own
    `</script>` no longer closes the element and the rest of the document is swallowed as script
    text.  That one breaks the page rather than executing anything, but it is free to close and a
    reader should not have to know which of the two sequences is covered.  `<` can only occur
    inside a JSON string -- every structural character is one of `{}[],:` -- so escaping it
    globally cannot corrupt the JSON, and `\\u003c` is what the parser reads back as `<`.

    It lives here because payloads that were escaped and payloads that were not sat in different
    modules and looked alike: nothing compared them, and the board, the graph and the budget went
    out unescaped for as long as nobody happened to read the right line.  `json.dumps` alone is
    not enough, and the difference is invisible at the call site."""
    return escape_script_text(json.dumps(payload, separators=(",", ":")))


def escape_script_text(text):
    """The same escape for JSON already serialised elsewhere (the ledger's, which is built as text)."""
    return text.replace("<", "\\u003c")


def script_json(payload, name="DATA"):
    """`const <name> = <payload>;` for a page's inline `<script>`, escaped by `script_payload`."""
    return f"const {name} = " + script_payload(payload) + ";"


def _index(key):
    if key not in KEYS:
        raise KeyError(f"unknown page {key!r}; pages are {KEYS}")
    return KEYS.index(key)


def _load(name):
    try:
        with open(os.path.join(DOCS, "data", name)) as f:
            return json.load(f)
    except (OSError, ValueError):
        return None


def strip_facts(state=None, inventory=None, progress=None, arms=None, outside=None, budget=None):
    """What the top strip shows, from the derived state files; None where a file is absent.

    `arms_main` is arms.json's own count and is None, not zero, when nothing read origin/main:
    a strip that rendered 0 there would say the port had landed nothing, which is a different
    claim from "this checkout did not look"."""
    state = _load("state.json") if state is None else state
    inventory = _load("inventory.json") if inventory is None else inventory
    progress = _load("progress.json") if progress is None else progress
    arms = _load("arms.json") if arms is None else arms
    outside = _load("outside.json") if outside is None else outside
    facts = dict(arms_merged=None, arms_total=None, arms_main=None, arms_day=None, mergeable=None, open_prs=None,
                 outside=None, outside_open=None, working=None, verdict=None, idle=None, parked=None, service=[],
                 updated=None, contradictions=None, github=None, windows=None, reports=None, tree=None,
                 cost=None, cost_per_arm=None, cost_per_item=None)
    if inventory:
        syscalls = inventory.get("syscalls", [])
        facts["arms_total"] = len(syscalls)
        facts["arms_merged"] = sum(1 for s in syscalls if s.get("lean"))
    if arms:
        c = arms.get("counts") or {}
        facts["arms_total"] = c.get("total", facts["arms_total"])
        # `by_stage`, the key lean_port_arms.counts() actually writes.  This read `stage` for a
        # while, which is in no payload, so both lookups were permanently None and the tile fell
        # back to inventory.json's count under the fixed label "on the day branch".  It read right
        # only while main held nothing and the two counts coincided; the first integration merge
        # would have made the headline tile of every page quietly wrong.
        by_stage = c.get("by_stage") or {}
        facts["arms_day"] = by_stage.get("day")
        facts["arms_main"] = by_stage.get("main") if (arms.get("main") or {}).get("read") else None
    if outside:
        c = outside.get("counts") or {}
        facts["outside"], facts["outside_open"] = c.get("prs"), c.get("open")
    if state:
        q = state.get("queues") or {}
        facts["mergeable"] = q.get("mergeable")
        facts["open_prs"] = sum(v for k, v in q.items() if k not in ("merged", "closed"))
        ws = state.get("window_states") or {}
        facts["working"] = ws.get("WORKING", 0)
        facts["verdict"] = ws.get("VERDICT", 0)
        facts["idle"] = ws.get("IDLE", 0) + ws.get("EXITED", 0)
        facts["parked"] = ws.get("LIMIT", 0)
        facts["contradictions"] = len(_real_contradictions(state))
        facts["service"] = sorted(w["window"] for w in (state.get("windows") or []) if w.get("kind") == "service")
        fr = state.get("freshness") or {}
        facts.update(github=fr.get("github"), windows=fr.get("windows"), reports=fr.get("reports"), tree=fr.get("tree"))
    if progress:
        facts["updated"] = progress.get("updated") or None
    b = _load("budget.json") if budget is None else budget
    if b:
        facts["cost"] = (b.get("total") or {}).get("cost")
        # arms.json's own count when it was read: a 0 there is an answer (nothing has merged),
        # not a missing figure to fall back from.
        merged = (arms or {}).get("counts", {}).get("merged")
        merged = facts["arms_merged"] if merged is None else merged
        # rounded as lean_port_budget.recalibrate rounds its per_arm, which the story pages quote
        # beside this strip: unrounded, the two could format a dollar apart at a half-dollar
        if facts["cost"] is not None and merged:
            facts["cost_per_arm"] = round(facts["cost"] / merged, 2)
        # the figure the owner's $500 limit reads (2026-09-22): spend charged to S, C and V tickets
        # over the merged items, as lean_port_budget.per_item_of computes it -- not re-derived here
        facts["cost_per_item"] = ((b.get("per_item") or {}).get("attributed") or {}).get("per_item")
    return facts


def _real_contradictions(state):
    """The self-check's own filter, not a second copy of it: what Outside the plan does not answer."""
    import lean_port_outside as outside
    return outside.real_contradictions(state)


def _pt(iso):
    import lean_port_time as ptime
    return ptime.pt_iso(iso) if iso else "never"


def strip_html(facts=None):
    """The strip that is the same on every page.  Static numbers from the derived state; lp-update.js
    drives the Update button and refreshes the live half when the site is served."""
    import lean_port_time as ptime
    f = strip_facts() if facts is None else facts
    n = lambda v: "—" if v is None else str(v)
    updated = ptime.pt_stamp(f["updated"]) if f["updated"] else "never"
    # The data's age, computed by lp-age.js when the page is read (the page holds the instant, never an interval),
    # red past LP_DATA_RED_MINUTES.  No stamp, no age: a dash would read as fresh.
    at = ptime.stamp_ms(f["updated"]) if f["updated"] else None
    # The label gives up "last update" to the tile's title when the age is there: the strip holds one row at
    # 1340px (test_lean_port_viewport.py), and "last update (Pacific) · 5d 20h old" did not fit in it.
    upd_label = ("last update (Pacific)" if at is None else
                 f'Pacific<small> &middot; <span class="lp-age" id="lp-age" data-at="{at}" data-red="{LP_DATA_RED_MINUTES}" '
                 f'title="how old the data on this page is; red past {LP_DATA_RED_MINUTES} minutes">&mdash;</span> old</small>')
    contra = f["contradictions"]
    contra_html = ("" if contra is None else
                   f'<a class="lp-tile{" bad" if contra else " good"}" href="index.html#h-selfcheck"><span class="v">{contra}</span><span class="k">contradiction{"s" if contra != 1 else ""}</span></a>')
    # per item replaces per arm on the line: with a dozen arms left, an arm no longer measures the
    # work, and an item (a merged spec, checker or conformance ticket) does.  Per arm moves to the
    # title, since the strip is one row on every page (test_lean_port_viewport) and both figures
    # beside "spent" wrapped it at 1366px on the scan of 2026-09-22.
    per_arm = "" if f.get("cost_per_arm") is None else f" &middot; ${f['cost_per_arm']:,.0f} per merged arm"
    if f.get("cost_per_item") is not None:
        arm = "" if f.get("cost_per_arm") is None else f"; ${f['cost_per_arm']:,.0f} per merged arm, counting everything spent"
        per_arm = (f' &middot; <span title="per merged spec, checker or conformance item: the spend charged to S, C and V tickets'
                   f' over the items merged, against the $500 limit{arm}">${f["cost_per_item"]:,.0f} per item</span>')
    # A missing derivation is the one thing on that line a reader must not have to open a disclosure to
    # see, so it rides on the summary instead of inside the panel.
    warn = ('' if not (f['github'] is None and f['windows'] is None) else
            ' · <span class="warn">no derived state yet: press Update or run tools/lean_port_status.py --write --github</span>')
    money_html = ("" if f.get("cost") is None else
                  f'<a class="lp-tile" href="budget.html"><span class="v">${f["cost"]:,.0f}</span>'
                  f'<span class="k">spent<small>{per_arm}</small></span></a>')
    # the derivation's service windows ride on the strip so the live refresh classifies windows the same way
    arms_v = (f'{n(f["arms_main"])}<small> on main</small>' if f["arms_main"] is not None
              else f'{n(f["arms_day"] if f["arms_day"] is not None else f["arms_merged"])}<small> on the day branch</small>')
    arms_k = ("" if f["arms_main"] is None or f["arms_day"] is None else
              f'<small> · {f["arms_day"]} on the day branch</small>')
    return f"""<div class="lp-strip" id="lp-strip" data-service="{escape(','.join(f.get('service') or []))}">
  <a class="lp-tile" href="index.html#c-stage"><span class="v">{arms_v}</span><span class="k"><dfn data-term="arm">arms</dfn> of {n(f['arms_total'])}{arms_k}</span></a>
  <a class="lp-tile" href="pipeline.html"><span class="v" data-live="mergeable">{n(f['mergeable'])}</span><span class="k">PRs mergeable now<small data-live="open_prs">{'' if f['open_prs'] is None else f" · {f['open_prs']} open"}</small></span></a>
  <a class="lp-tile" href="outside.html"><span class="v">{n(f['outside'])}</span><span class="k">outside the plan<small>{'' if f['outside_open'] is None else f" · {f['outside_open']} open"}</small></span></a>
  <a class="lp-tile" href="machines.html"><span class="v"><span data-live="working">{n(f['working'])}</span><small> <dfn data-term="working">working</dfn></small> <span data-live="verdict">{n(f['verdict'])}</span><small> <dfn data-term="at a verdict">at a verdict</dfn></small> <span data-live="idle">{n(f['idle'])}</span><small> <dfn data-term="idle">idle</dfn></small> <span data-live="parked">{n(f['parked'])}</span><small> <dfn data-term="parked">parked</dfn></small></span><span class="k">windows</span></a>
  {money_html}
  {contra_html}
  <div class="lp-tile lp-upd" title="the last Update, Pacific time"><span class="v" id="lp-updated">{escape(updated)}</span><span class="k">{upd_label}</span></div>
  <form class="lp-update" id="lp-update" aria-live="polite"><button type="submit" id="lp-update-btn" title="Recomputes every state from GitHub, the windows, the reports and the tree, then reloads."><span class="spin" aria-hidden="true"></span><span class="txt">Update</span></button><span class="hint" id="lp-update-hint"></span><pre class="log" id="lp-update-log" hidden></pre></form>
</div>
<details class="lp-fresh-d" id="lp-fresh-d"><summary id="lp-fresh-s">Where these numbers come from{warn}</summary>
<div class="lp-fresh" id="lp-fresh">Sources: GitHub as of <b>{escape(_pt(f['github']))}</b> · windows as of <b>{escape(_pt(f['windows']))}</b> · reports as of <b>{escape(_pt(f['reports']))}</b> · tree at <b><code>{escape(f['tree'] or '—')}</code></b> (the checkout of the last Update)</div></details>"""


def _link(k, f, label, current):
    return f'<a href="{f}"{" aria-current=\"page\"" if k == current else ""}>{escape(label)}</a>'


# The one page the strip is NOT on.  Everywhere else it is the same six tiles, and a reader of a
# dashboard wants them; the TL;DR is written for somebody who has never seen this project, and
# opening it on `118 outside the plan · 0 parked · 7 contradictions` is four kinds of fleet jargon
# before its first sentence.  That page renders the same figures as its own cards, in words, and
# carries the update stamp in its closing line -- so nothing is lost, and the reader meets the
# sentence first.  Its Update button goes with it: every script that touches the strip null-checks
# it (lp-update.js's `strip &&`), and the page's own line says where the button is.
NO_STRIP = ("tldr",)


def nav_html(current, facts=None):
    """The shared bar, the top strip and the breadcrumb line for page `current`.

    The bar spells out BAR_GROUP and puts every other group behind one `More` disclosure, labelled
    by group inside.  When `current` is one of those, the summary says which -- otherwise the bar of
    a page in the More list marks nothing as current and reads as though the reader were nowhere.

    A page in NO_STRIP gets the bar and the breadcrumb and no strip; the comment there says why."""
    i = _index(current)
    links = "".join(_link(k, f, label, current) for k, f, label, _, g in PAGES if g == BAR_GROUP)
    menu = ""
    for group, glabel in GROUPS:
        if group == BAR_GROUP:
            continue
        menu += f'<p class="lp-menu-h">{escape(glabel)}</p>' + "".join(
            _link(k, f, label, current) for k, f, label, _, g in PAGES if g == group)
    here = next((label for k, _f, label, _r, g in PAGES if k == current and g != BAR_GROUP), None)
    summary = "More" if here is None else f"More: {escape(here)}"
    more = (f'<details class="lp-more"{"" if here is None else " data-here=\"1\""}>'
            f'<summary>{summary} &#9662;</summary>'
            f'<div class="lp-menu">{menu}</div></details>')
    bar = (f'<nav class="lp-nav" aria-label="Lean port pages"><span class="lp-brand">Lean port</span>{links}'
           f'<span class="lp-sep" aria-hidden="true"></span>{more}'
           f'<a class="lp-status" href="pipeline.html#c-red">what needs a human</a></nav>')
    prev_ = PAGES[i - 1] if i > 0 else None
    next_ = PAGES[i + 1] if i + 1 < len(PAGES) else None
    pn = ""
    if prev_:
        pn += f'<a href="{prev_[1]}" rel="prev">&larr; {escape(prev_[2])}</a>'
    if next_:
        pn += f'<a href="{next_[1]}" rel="next">{escape(next_[2])} &rarr;</a>'
    crumb = (f'<div class="lp-crumb" aria-label="You are here"><span>You are here:</span>'
             f'<span><a href="index.html">Lean port</a> &rsaquo; <b>{escape(PAGES[i][2])}</b></span>'
             f'<span>page {i + 1} of {len(PAGES)}</span><span class="lp-pn">{pn}</span></div>')
    strip = "" if current in NO_STRIP else strip_html(facts) + "\n"
    return bar + "\n" + strip + crumb


def role_html(current):
    """The page's question, rendered under its title."""
    return f'<p class="lp-role">{escape(PAGES[_index(current)][3])}</p>'


HEAD_ASSETS = ('<link rel="stylesheet" href="lp-common.css">\n<script defer src="lp-update.js"></script>\n'
               '<script defer src="lp-glossary.js"></script>\n<script defer src="lp-age.js"></script>')


def fill(template, current, facts=None):
    """Replace the two placeholders in `template` for page `current`.

    Every placeholder must be present exactly once: a template that lost one
    would silently ship without navigation otherwise."""
    out = template
    for marker, html in (("<!--__NAV__-->", nav_html(current, facts)), ("<!--__ROLE__-->", role_html(current))):
        assert out.count(marker) == 1, f"{current}: expected one {marker}, found {out.count(marker)}"
        out = out.replace(marker, html)
    # The stylesheet and the shared assets belong in the head.  A template that carries its own
    # <head> gets them before </head>; the ledger's template starts inside the head
    # (specdeps.render_html wraps it), so there they go first.
    if out.count("</head>") == 1:
        out = out.replace("</head>", STYLE + "\n" + HEAD_ASSETS + "\n</head>")
    else:
        assert "</head>" not in out and "<body" not in out, f"{current}: a template with a body must have one </head>"
        out = STYLE + "\n" + HEAD_ASSETS + "\n" + out
    return out
