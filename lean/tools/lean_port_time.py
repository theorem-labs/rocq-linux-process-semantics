"""Times on the Lean port's site are shown in Pacific time.

Data stays as written: progress.json's `updated` is a UTC minute, STATUS.md is
typed in whatever zone its author used, transcripts and GitHub speak UTC.  The
generators convert at render time through this module, so every timestamp a
reader sees is America/Los_Angeles with its zone label, PST or PDT, computed
from the date by the zone database rather than assumed.

    pt_stamp("2026-09-16 02:58Z")            -> "2026-09-15 19:58 PDT"
    pt_iso("2026-01-10T02:58:00Z")           -> "01-09 18:58 PST"
    pt_text("- 02:55 UTC: merged", day)      -> "- 19:55 PDT: merged"

`pt_text` rewrites the UTC times inside a line of prose.  A bare "HH:MM UTC"
or "HH:MMZ" carries no date, so the caller passes the date the line belongs
to (`day`, a UTC date), which decides PST against PDT and the day boundary.
A line already written as "HH:MM AM/PM PT (HH:MM UTC)" collapses to the one
Pacific time.  Nothing here reads the clock.
"""
import datetime
import re
from zoneinfo import ZoneInfo

PACIFIC = ZoneInfo("America/Los_Angeles")
UTC = datetime.timezone.utc

STAMP = re.compile(r"^(\d{4})-(\d{2})-(\d{2}) (\d{2}):(\d{2})Z$")
# "08:55 PM PT (03:55 UTC)": a hand-converted time with its UTC source beside it
PT_WITH_UTC = re.compile(r"\b\d{1,2}:\d{2} ?[AP]M P[SD]?T \((\d{1,2}):(\d{2}) ?(?:UTC|Z)\)")
# "02:55 UTC", "02:55Z", "at 00:27 UTC"; not the "Z" of an ISO stamp with seconds
# (the second lookbehind keeps the clock of a full "YYYY-MM-DD HH:MM" stamp for STAMP_IN_TEXT,
# so an impossible date such as 2026-02-30 stays whole instead of having its clock converted)
UTC_TIME = re.compile(r"(?<![\d:])(?<!\d\d-\d\d )(\d{1,2}):(\d{2})(?!:\d) ?(?:UTC|Z)\b")
# "2026-09-16 02:58 UTC", "2026-09-16 02:58Z", or the kit's log stamp `date -u +%Y-%m-%dT%H:%M:%SZ`
# ("2026-09-17T18:41:03Z watchdog: ...") inside prose: date and clock move together, whatever day the text belongs to.
# The left edge is "not a word character": "(", "[", "=", "-", a space or the start all precede real stamps.
STAMP_IN_TEXT = re.compile(r"(?<!\w)(\d{4})-(\d{2})-(\d{2})[T ](\d{1,2}):(\d{2})(?::\d{2})? ?(?:UTC|Z)\b")


def stamps_in_text(text):
    """Every dated UTC stamp in `text` as Pacific with its own date ("2026-09-17 11:41 PDT"); other text unchanged.
    An impossible date ("2026-02-30T18:41Z") is left as written: the callers' clock rules then decide its clock."""
    if not text:
        return text

    def stamped(m):
        try:
            u = datetime.datetime(int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(4)), int(m.group(5)), tzinfo=UTC)
        except ValueError:
            return m.group(0)
        p = to_pacific(u)
        return p.strftime("%Y-%m-%d %H:%M ") + label(p)
    return STAMP_IN_TEXT.sub(stamped, text)


def to_pacific(dt):
    """A UTC datetime as a Pacific one (aware in, aware out)."""
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=UTC)
    return dt.astimezone(PACIFIC)


def label(dt_pacific):
    """PST or PDT for an aware Pacific datetime."""
    return dt_pacific.strftime("%Z")


def pt_stamp(updated):
    """progress.json's `updated` ("YYYY-MM-DD HH:MMZ") as "YYYY-MM-DD HH:MM PDT"; anything else unchanged."""
    m = STAMP.match(updated or "")
    if not m:
        return updated
    y, mo, d, h, mi = map(int, m.groups())
    p = to_pacific(datetime.datetime(y, mo, d, h, mi, tzinfo=UTC))
    return p.strftime("%Y-%m-%d %H:%M ") + label(p)


def stamp_ms(updated):
    """progress.json's `updated` ("YYYY-MM-DD HH:MMZ") as epoch milliseconds, or None: the form a
    page carries a stamp in for lp-age.js, which turns it into an age when the page is read."""
    m = STAMP.match(updated or "")
    if not m:
        return None
    y, mo, d, h, mi = map(int, m.groups())
    return int(datetime.datetime(y, mo, d, h, mi, tzinfo=UTC).timestamp() * 1000)


def pt_iso(iso):
    """An ISO UTC instant ("2026-09-16T02:58:00Z" or with an offset) as "MM-DD HH:MM PDT"; None stays None."""
    if not iso:
        return iso
    p = to_pacific(datetime.datetime.fromisoformat(iso.replace("Z", "+00:00")))
    return p.strftime("%m-%d %H:%M ") + label(p)


def day_of(updated):
    """The UTC date of a stamp like progress.json's `updated`, as the `day` pt_text takes."""
    m = STAMP.match(updated or "")
    return datetime.date(*map(int, m.groups()[:3])) if m else None


def pt_text(text, day):
    """Rewrite every UTC time in `text` as Pacific, dating each by `day` (a UTC date).

    With no `day` the text is returned as it is: a time without a date cannot be
    labelled PST or PDT honestly."""
    if day is None or not text:
        return text

    def clock(h, mi, whole, d=None):
        # A clock that is not one ("25:00 UTC", a typo in the note) is left as written rather
        # than turning a page regeneration into a traceback.
        try:
            d = d or day
            p = to_pacific(datetime.datetime(d.year, d.month, d.day, int(h), int(mi), tzinfo=UTC))
        except ValueError:
            return whole
        return (p.strftime("%Y-%m-%d %H:%M ") if d is not day else p.strftime("%H:%M ")) + label(p)

    text = stamps_in_text(text)
    text = PT_WITH_UTC.sub(lambda m: clock(m.group(1), m.group(2), m.group(0)), text)
    return UTC_TIME.sub(lambda m: clock(m.group(1), m.group(2), m.group(0)), text)


# --------------------------------------------------------------------------
# A pane line's clocks
# --------------------------------------------------------------------------
# The two shapes an agent's own output uses, which pt_text above does not read: a bare UTC
# clock inside a log line, and the CLI's twelve-hour "done 8:03 PM".  Both are the machine's
# clock, and the machine runs on UTC.  They live here rather than beside the page that shows
# them because the site has one rule about time -- every clock a reader sees is Pacific -- and
# a second implementation of it is a second answer.
# A dated stamp is taken first, by STAMP_IN_TEXT above -- the same pattern prose uses, in a
# shorter format, because a pane line has no room for the year.  CLOCK's lookbehinds then
# stand behind that: with neither, the MINUTES of a stamp read as a clock of their own --
# `2026-09-17T18:10:00Z` has a word boundary before `10:00Z` but none before `18`, so a
# bare-clock pattern matches the tail and rewrites the stamp to `2026-09-17T18` + `03:00 PDT`.
# It misfires exactly when a stamp's minute is also a valid hour, and silently, since the
# result still looks like a time.
#
# The three lookbehinds, and why not `\b(?<!:)`: that pair refused every clock a digit or a
# colon precedes, which is the minutes of a stamp -- but also `logs/x.log:18:41:03Z` (grep's
# own shape), `end:18:41Z` and a bare `T18:41Z`, all of them pane lines the earlier converter
# handled and its deleted test pinned.  So: not after a digit (a stamp's second field), not
# after `<digit>:` (a stamp's minutes), and not after `MM-DD ` or `MM-DDT` -- the clock of an
# impossible stamp such as 2026-02-30T18:41:03Z, which STAMP_IN_TEXT left whole so that a
# typo stays a typo instead of half-converting into a plausible time.
CLOCK = re.compile(r"(?<!\d)(?<!\d:)(?<!\d\d-\d\d[T ])(\d{1,2}):(\d{2})(?::\d{2})?\s?(?:UTC|Z)\b")
CLOCK_12 = re.compile(r"\b(\d{1,2}):(\d{2})\s?(AM|PM)\b(?!\s?P[SD]?T)")  # the CLI's own "done 8:03 PM": the machine's clock, which is UTC


def pacific_clocks(text, day_iso):
    """A pane line's UTC clocks ("19:16:32Z E0: nudged", "2026-09-17T18:41:03Z watchdog: ...",
    "done 8:03 PM") as Pacific, a bare clock dated by the export's day and a stamp by its own;
    other text unchanged.  The machine runs on UTC, so the CLI's twelve-hour clock is UTC too.

    With no `day_iso` a bare clock is left as written -- it cannot be labelled PST or PDT
    honestly -- but a dated stamp carries its own date and is converted regardless; a job with
    neither heartbeat nor log gets no day, and its lines used to reach the page as UTC whole."""
    if not text:
        return text

    def at(h, mi):
        try:
            u = datetime.datetime(day.year, day.month, day.day, h, mi, tzinfo=datetime.timezone.utc)
        except ValueError:
            return None
        p = to_pacific(u)
        return p.strftime("%H:%M ") + label(p)

    def conv(m):
        return at(int(m.group(1)), int(m.group(2))) or m.group(0)

    def conv12(m):
        h = int(m.group(1)) % 12 + (12 if m.group(3) == "PM" else 0)
        return at(h, int(m.group(2))) or m.group(0)

    def stamped(m):
        # Month and day, not the year: the kit writes its own log stamps into pane lines and the
        # machines page shows them in a column.  An impossible date is left as written, the way
        # stamps_in_text leaves it, so a typo stays a typo rather than becoming a plausible time.
        try:
            u = datetime.datetime(int(m.group(1)), int(m.group(2)), int(m.group(3)),
                                  int(m.group(4)), int(m.group(5)), tzinfo=UTC)
        except ValueError:
            return m.group(0)
        p = to_pacific(u)
        return p.strftime("%m-%d %H:%M ") + label(p)
    # An ISO instant inside a log line IS a clock the reader sees, unlike one in prose (pt_text
    # converts those with their own date, and its tests pin the format): these lines are the kit
    # talking about when it did something, and the site shows Pacific.
    text = STAMP_IN_TEXT.sub(stamped, text)
    if not day_iso:
        return text
    day = datetime.datetime.fromisoformat(day_iso.replace("Z", "+00:00")).date()
    return CLOCK_12.sub(conv12, CLOCK.sub(conv, text))
