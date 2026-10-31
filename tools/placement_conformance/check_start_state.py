#!/usr/bin/env python3
"""check_start_state.py - EVIDENCE, no longer the A4 check.

THIS SCRIPT IS NOT THE CHECK ANY MORE.  A4 of dispatch://OSSV-257 is checked
by start_state_to_rocq.py, which emits a Rocq file per log whose lemmas Rocq
closes with vm_compute against the model's own source.  What this script
compares the record with is the PYTHON TRANSCRIPTION below: a second model of
the entry block that nothing proves agrees with the first.  Its run stands as
the first evidence that the ten records agree with the model -- 110 verdicts
over 10 records, 0 failures, reports/a4-start-state.md of the entry lane's
clone -- and it reads two things the Rocq files do not: the vDSO image
against the kernel build's own vdso.so, and the vvar mapping's distance below
AT_SYSINFO_EHDR.  It is no longer in the trusted path.

It reads a real Linux launch against a transcription of the LPS entry model.

    check_start_state.py LOG [LOG ...] [--vdso FILE] [--quiet]

Each LOG is a start-state log that run-kernel.sh wrote (one launch object,
the "run" key "fixture" or "long").  The script rebuilds, from the launch
facts the log records, what LPS says the start state must be, and compares it
with what the kernel did.  It prints a verdict for each of A4's three
sub-checks (dispatch://OSSV-257, acceptance A4):

  1. Run.entry_launch_ok_va holds of the recorded stack end, stack pointer
     and mmap base, under the recorded launch facts.
  2. LPS's block equals the recorded bytes from sp to the stack end, byte for
     byte apart from the sixteen AT_RANDOM bytes, and the recorded auxiliary
     vector equals StackLayout.auxv_entries entry for entry, AT_MINSIGSTKSZ
     against State.min_sigframe_size and the eight cache words against
     State.cache_size_word and State.cache_geometry_word over the recorded
     devicetree.
  3. The recorded vDSO image is the one the kernel build carries, and the
     vvar mapping starts four pages below AT_SYSINFO_EHDR.

THE TRANSCRIPTION BELOW IS WHAT A6 HAS TO READ.  Everything between the
marker "MODEL TRANSCRIPTION BEGINS" and "MODEL TRANSCRIPTION ENDS" is a
transcription of rocq-linux-process-semantics branch revision/entry, files
theories/LinuxProcessSem/StackLayout.v, State.v and Run.v, with the Rocq name
of each definition on its own line.  A reviewer checks those names against
the Rocq source, and the Rocq source against Linux v6.18.46, commit
1f99e9ab748f.  Nothing outside the markers states what the model says.

Why this file is no longer the check: the transcription is a SECOND model of
the entry block.  A reviewer can read it against the Rocq source, but nothing
proves the two agree, so a disagreement between them would show up as a
passing Python check and a failing Rocq one -- or, worse, the reverse.
start_state_to_rocq.py removes the second model: it emits the record as LPS
terms and lets Rocq compute the block from StackLayout.v itself.
"""

import argparse
import hashlib
import json
import os
import re
import sys

# ======================= MODEL TRANSCRIPTION BEGINS ========================
# Every function here is one definition of the model.  The Rocq name is in
# the docstring; the body is the Rocq body, in Python.

PAGE = 4096                       # State.page_size
TWO64 = 1 << 64
STACK_MAX_SIZE = 8 * 1024 * 1024  # State.stack_max_size
STACK_RND_MAX = 0x3FFFF000        # Run.stack_rnd_max
MMAP_MIN_GAP = 128 * 1024 * 1024  # Run.mmap_min_gap
RT_SIGFRAME_SIZE = 1088           # State.rt_sigframe_size
E2BIG_LIMIT = 2097152             # Run.e2big_limit

# State.va_stack_top
VA_STACK_TOP = {"Sv39": 1 << 38, "Sv48": 0x800000000000, "Sv57": 0x800000000000}
# State.mmap_rnd_bits_max
MMAP_RND_BITS_MAX = {"Sv39": 24, "Sv48": 33, "Sv57": 33}

# StackLayout, the auxv tags
AT = {
    "NULL": 0, "PHDR": 3, "PHENT": 4, "PHNUM": 5, "PAGESZ": 6, "BASE": 7,
    "FLAGS": 8, "ENTRY": 9, "UID": 11, "EUID": 12, "GID": 13, "EGID": 14,
    "HWCAP": 16, "CLKTCK": 17, "SECURE": 23, "RANDOM": 25,
    "RSEQ_FEATURE_SIZE": 27, "RSEQ_ALIGN": 28, "EXECFN": 31,
    "SYSINFO_EHDR": 33, "L1I_CACHESIZE": 40, "L1I_CACHEGEOMETRY": 41,
    "L1D_CACHESIZE": 42, "L1D_CACHEGEOMETRY": 43, "L2_CACHESIZE": 44,
    "L2_CACHEGEOMETRY": 45, "L3_CACHESIZE": 46, "L3_CACHEGEOMETRY": 47,
    "MINSIGSTKSZ": 51,
}
AT_NAME = {v: k for k, v in AT.items()}

HWCAP_RV64GC = 0x112D             # StackLayout.hwcap_rv64gc
HWCAP_RV64GCV = 0x20112D          # StackLayout.hwcap_rv64gcv


def le8(v):
    """BvBase.word_le8."""
    return (v % TWO64).to_bytes(8, "little")


def page_round_up(n):
    """State.page_round_up_Z."""
    return (n + PAGE - 1) // PAGE * PAGE


def align_down16(x):
    """Run.align_down16."""
    return x - x % 16


def flatten_strings(strs):
    """StackLayout.flatten_strings."""
    return b"".join(s + b"\0" for s in strs)


def string_addrs(base, strs):
    """StackLayout.string_addrs."""
    ptrs, addr = [], base
    for s in strs:
        ptrs.append(addr)
        addr = (addr + len(s) + 1) % TWO64
    return ptrs, addr


def block_items(argv, envp):
    """StackLayout.block_items."""
    return len(argv) + len(envp) + 3


def auxv_count(rseq):
    """StackLayout.auxv_count."""
    return 29 if rseq else 27


def auxv_size(rseq):
    """StackLayout.auxv_size."""
    return 16 * auxv_count(rseq)


def block_head_size(rseq, argv, envp):
    """StackLayout.block_head_size (C)."""
    items = block_items(argv, envp)
    return 8 * items + auxv_size(rseq) + 8 * (items % 2) + 16


def launch_string_bytes(argv, envp, execfn):
    """StackLayout.launch_string_bytes (L)."""
    return (len(flatten_strings(argv)) + len(flatten_strings(envp))
            + len(execfn) + 1)


def string_base_addr(top, argv, envp, execfn):
    """StackLayout.string_base_addr (the address of argv[0])."""
    return (top - (8 + launch_string_bytes(argv, envp, execfn))) % TWO64


def at_execfn_ptr(top, execfn):
    """StackLayout.at_execfn_ptr."""
    return (top - (8 + len(execfn) + 1)) % TWO64


def at_random_ptr(sp, rseq, argv, envp):
    """StackLayout.at_random_ptr."""
    return (sp + block_head_size(rseq, argv, envp) - 16) % TWO64


def block_pad_len(rseq, sp, top, argv, envp, execfn):
    """StackLayout.block_pad_len (Z.to_nat clamps a negative to 0)."""
    n = (top - 8 - launch_string_bytes(argv, envp, execfn) - sp
         - block_head_size(rseq, argv, envp))
    return max(0, n)


class CacheLeaf(object):
    """State.CacheLeaf."""

    def __init__(self, acpi=False, size=0, assoc=0, line=0):
        self.acpi, self.size, self.assoc, self.line = acpi, size, assoc, line


CACHE_LEAF_ABSENT = CacheLeaf()   # State.cache_leaf_absent


class CacheView(object):
    """State.CacheView."""

    def __init__(self, l1i=None, l1d=None, l2=None, l3=None):
        self.l1i = l1i or CacheLeaf()
        self.l1d = l1d or CacheLeaf()
        self.l2 = l2 or CacheLeaf()
        self.l3 = l3 or CacheLeaf()


def cache_ways(leaf):
    """State.cache_ways."""
    if leaf.acpi:
        return leaf.assoc % 2 ** 8
    if leaf.assoc not in (0, 1) and leaf.size != 0 and leaf.line != 0:
        return (leaf.size // leaf.assoc) // leaf.line
    return 0


def cache_line(leaf):
    """State.cache_line."""
    return leaf.line % 2 ** 16 if leaf.acpi else leaf.line


def cache_size_word(leaf):
    """State.cache_size_word."""
    return leaf.size % 2 ** 32


def cache_geometry_word(leaf):
    """State.cache_geometry_word."""
    return ((cache_ways(leaf) * 2 ** 16) | cache_line(leaf)) % 2 ** 32


class KernelBuild(object):
    """State.KernelBuild, with each field already decoded.

    The model encodes each field so that every value names a real machine;
    this checker carries the DECODED value (the value of vdso_text_pages,
    stack_guard_gap_pages, mmap_rnd_bits, launch_vlenb), because that is what
    a recorded boot gives.  The encodings themselves are checked by
    encodable() below.
    """

    def __init__(self, thp, vdso_text_pages, aslr, guard_pages, rnd_bits,
                 rseq, vlenb, cache):
        self.thp = thp
        self.vdso_text_pages = vdso_text_pages
        self.aslr = aslr
        self.guard_pages = guard_pages
        self.rnd_bits = rnd_bits
        self.rseq = rseq
        self.vlenb = vlenb
        self.cache = cache

    def encodable(self, va):
        """Every decoded value is in the range the model's encoding admits:
        State.vdso_text_pages, State.stack_guard_gap_pages,
        State.mmap_rnd_bits, State.launch_vlenb."""
        bad = []
        if not 1 <= self.vdso_text_pages <= 16:
            bad.append("vdso_text_pages %d outside 1..16" % self.vdso_text_pages)
        if not 0 <= self.guard_pages < 0x4ABA6A2AC:
            bad.append("stack_guard_gap %d pages outside 0..0x4aba6a2ab"
                       % self.guard_pages)
        if not 18 <= self.rnd_bits <= MMAP_RND_BITS_MAX[va]:
            bad.append("mmap_rnd_bits %d outside 18..%d"
                       % (self.rnd_bits, MMAP_RND_BITS_MAX[va]))
        if self.vlenb and self.vlenb not in [16 * 2 ** k for k in range(10)]:
            bad.append("vlenb %d is not 16*2^k, k<10" % self.vlenb)
        return bad


def stack_guard_gap_bytes(kb):
    """State.stack_guard_gap_bytes."""
    return PAGE * kb.guard_pages


def hwcap_has_v(hwcap):
    """State.hwcap_has_v."""
    return bool((hwcap >> 21) & 1)


def min_sigframe_size(kb, hwcap):
    """State.min_sigframe_size (AT_MINSIGSTKSZ)."""
    vlenb = kb.vlenb if hwcap_has_v(hwcap) else (0 if kb.vlenb == 0 else kb.vlenb)
    vsz = 0 if vlenb == 0 else 8 + 48 + 32 * vlenb
    return (RT_SIGFRAME_SIZE + vsz + 15) // 16 * 16


def vdso_text_base(kb, mbase):
    """Run.vdso_text_base (the AT_SYSINFO_EHDR value)."""
    return (mbase - kb.vdso_text_pages * PAGE) % TWO64


def launch_cache_words(kb):
    """Run.launch_cache_words: the eight auxv words, in auxv order."""
    out = []
    for leaf in (kb.cache.l1i, kb.cache.l1d, kb.cache.l2, kb.cache.l3):
        out.append(cache_size_word(leaf))
        out.append(cache_geometry_word(leaf))
    return out


def auxv_entries(kb, mbase, ph, entry, uid, gid, hwcap, at_random, at_execfn):
    """StackLayout.auxv_entries, applied to Run.launch_auxv."""
    cw = launch_cache_words(kb)
    ents = [
        (AT["SYSINFO_EHDR"], vdso_text_base(kb, mbase)),
        (AT["L1I_CACHESIZE"], cw[0]), (AT["L1I_CACHEGEOMETRY"], cw[1]),
        (AT["L1D_CACHESIZE"], cw[2]), (AT["L1D_CACHEGEOMETRY"], cw[3]),
        (AT["L2_CACHESIZE"], cw[4]), (AT["L2_CACHEGEOMETRY"], cw[5]),
        (AT["L3_CACHESIZE"], cw[6]), (AT["L3_CACHEGEOMETRY"], cw[7]),
        (AT["MINSIGSTKSZ"], min_sigframe_size(kb, hwcap)),
        (AT["HWCAP"], hwcap),
        (AT["PAGESZ"], 4096),
        (AT["CLKTCK"], 100),
        (AT["PHDR"], ph[0]), (AT["PHENT"], ph[1]), (AT["PHNUM"], ph[2]),
        (AT["BASE"], 0), (AT["FLAGS"], 0), (AT["ENTRY"], entry),
        (AT["UID"], uid), (AT["EUID"], uid),
        (AT["GID"], gid), (AT["EGID"], gid),
        (AT["SECURE"], 0),
        (AT["RANDOM"], at_random), (AT["EXECFN"], at_execfn),
    ]
    if kb.rseq:
        ents += [(AT["RSEQ_FEATURE_SIZE"], 28), (AT["RSEQ_ALIGN"], 32)]
    return ents + [(AT["NULL"], 0)]


def build_stack_bytes(kb, mbase, ph, entry, sp, top, argv, envp, execfn,
                      uid, gid, hwcap, rnd16):
    """StackLayout.build_stack_bytes (Run.entry_stack_image applies it to the
    input, the mmap base and the draw)."""
    items = block_items(argv, envp)
    sbase = string_base_addr(top, argv, envp, execfn)
    argv_ptrs, env_base = string_addrs(sbase, argv)
    envp_ptrs, _ = string_addrs(env_base, envp)
    ents = auxv_entries(kb, mbase, ph, entry, uid, gid, hwcap,
                        at_random_ptr(sp, kb.rseq, argv, envp),
                        at_execfn_ptr(top, execfn))
    auxv = b"".join(le8(t) + le8(v) for t, v in ents)
    head = (le8(len(argv))
            + b"".join(le8(p) for p in argv_ptrs) + le8(0)
            + b"".join(le8(p) for p in envp_ptrs) + le8(0)
            + auxv
            + b"\0" * (8 * (items % 2))
            + rnd16)
    strs = flatten_strings(argv) + flatten_strings(envp) + execfn + b"\0"
    pad = block_pad_len(kb.rseq, sp, top, argv, envp, execfn)
    return head + b"\0" * pad + strs + b"\0" * 8


def valid_stack_top_va(va, aslr, top):
    """Run.valid_stack_top_va (rule 1)."""
    t0 = VA_STACK_TOP[va]
    draw = (STACK_RND_MAX + PAGE) if aslr else PAGE
    return (top % PAGE == 0) and (top <= t0) and (t0 - draw <= top)


def launch_sp_hi(top, kb, argv, envp, execfn):
    """Run.launch_sp_hi."""
    return (align_down16(top - 8 - launch_string_bytes(argv, envp, execfn))
            - block_head_size(kb.rseq, argv, envp))


def launch_sp_lo(top, kb, argv, envp, execfn):
    """Run.launch_sp_lo."""
    return (align_down16(top - 8 - launch_string_bytes(argv, envp, execfn)
                         - 4095)
            - block_head_size(kb.rseq, argv, envp))


def valid_launch_sp(top, kb, argv, envp, execfn, sp):
    """Run.valid_launch_sp (rule 2)."""
    return (sp % 16 == 0
            and launch_sp_lo(top, kb, argv, envp, execfn) <= sp
            <= launch_sp_hi(top, kb, argv, envp, execfn))


def mmap_max_gap(va):
    """Run.mmap_max_gap."""
    return VA_STACK_TOP[va] // 6 * 5


def mmap_gap(va, kb):
    """Run.mmap_gap (mm/util.c, mmap_base, in 64-bit unsigned arithmetic)."""
    rlim = STACK_MAX_SIZE
    pad = stack_guard_gap_bytes(kb) + (STACK_RND_MAX if kb.aslr else 0)
    g = rlim + pad if ((rlim + pad) % TWO64) > rlim else rlim
    if g < MMAP_MIN_GAP and MMAP_MIN_GAP < mmap_max_gap(va):
        return MMAP_MIN_GAP
    if g > mmap_max_gap(va):
        return mmap_max_gap(va)
    return g


def mmap_base_of(va, kb, rnd):
    """Run.mmap_base_of."""
    return page_round_up(VA_STACK_TOP[va] - mmap_gap(va, kb) - rnd)


def valid_launch_base(va, kb, mbase):
    """Run.valid_launch_base (rule 3): returns (holds, r, base_at_r_zero)."""
    top_base = mmap_base_of(va, kb, 0)
    delta = top_base - mbase
    if delta < 0 or delta % PAGE:
        return False, None, top_base
    r = delta // PAGE
    if not kb.aslr:
        return r == 0, r, top_base
    return r < 2 ** kb.rnd_bits, r, top_base


def entry_launch_ok_va(va, kb, argv, envp, execfn, top, sp, mbase):
    """Run.entry_launch_ok_va."""
    ok1 = valid_stack_top_va(va, kb.aslr, top)
    ok2 = valid_launch_sp(top, kb, argv, envp, execfn, sp)
    ok3, r, _ = valid_launch_base(va, kb, mbase)
    return ok1, ok2, ok3, r


def launch_bytes(argv, envp, execfn):
    """Run.launch_bytes."""
    return (launch_string_bytes(argv, envp, execfn)
            + 8 * (len(argv) + len(envp)))


def stack_window_lo(kb, mbase, top):
    """Run.stack_window_lo."""
    return max(top - STACK_MAX_SIZE, mbase + stack_guard_gap_bytes(kb))


VDSO_VVAR_PAGES = 4               # State.vdso_vvar_pages
# ======================== MODEL TRANSCRIPTION ENDS =========================


# ------------------------------------------------------------- the record --

class Record(object):
    """One launch, as the probe and run-kernel.sh wrote it."""

    def __init__(self, path):
        self.path = path
        self.header = []
        obj = None
        with open(path, "r", encoding="utf-8") as fh:
            for line in fh:
                if line.startswith("#"):
                    self.header.append(line.rstrip("\n"))
                elif line.startswith("{"):
                    if obj is None:
                        obj = json.loads(line)
        if obj is None:
            raise SystemExit("%s: no launch object" % path)
        self.j = obj
        self.run = obj.get("run", "?")
        self.argv = [s.encode("utf-8", "surrogateescape") for s in obj["argv"]]
        self.envp = [s.encode("utf-8", "surrogateescape") for s in obj["envp"]]
        self.execfn = obj["execfn"].encode("utf-8", "surrogateescape")
        self.sp = obj["sp_at_start"]
        self.stack_end = obj["stack_end"]
        self.vvar_start = obj["vvar_start"]
        self.stack_bytes = bytes.fromhex(obj["stack_bytes"])
        self.vdso_image = bytes.fromhex(obj["vdso_image"])
        self.auxv_raw = bytes.fromhex(obj["auxv"])
        self.maps = obj["maps"]
        self.cmdline = obj.get("cmdline", "")
        self.config = obj.get("config", [])
        self.dt_cache = obj.get("dt_cache", {})
        self.vlenb = obj.get("vlenb")
        self.rnd_bits = obj.get("mmap_rnd_bits", 0)
        self.randomize_va_space = obj.get("randomize_va_space", 0)
        self.auxv = decode_auxv(self.auxv_raw)
        self.auxd = dict(self.auxv)
        self.vdso_lo, self.vdso_hi = maps_range(self.maps, "[vdso]")
        self.mmap_base = self.vdso_hi   # the vDSO text sits just below the base

    def config_is(self, key, value="y"):
        return ("%s=%s" % (key, value)) in self.config


def decode_auxv(raw):
    out = []
    for i in range(len(raw) // 16):
        tag = int.from_bytes(raw[16 * i:16 * i + 8], "little")
        val = int.from_bytes(raw[16 * i + 8:16 * i + 16], "little")
        out.append((tag, val))
        if tag == 0:
            break
    return out


def maps_range(maps, tag):
    for line in maps.splitlines():
        if line.rstrip().endswith(tag):
            lo, hi = line.split()[0].split("-")
            return int(lo, 16), int(hi, 16)
    return 0, 0


def guard_pages_of(cmdline):
    m = re.search(r"stack_guard_gap=(\d+)", cmdline)
    # mm/mmap.c, cmdline_parse_stack_guard_gap: the default is 256 pages.
    return int(m.group(1)) if m else 256


def dt_leaf(props, prefix):
    """One CacheLeaf out of a devicetree node's properties, as Linux reads
    them (drivers/base/cacheinfo.c, cache_of_set_props: cache-size,
    cache-sets, cache-line-size then cache-block-size, with the i- and d-
    forms for a split level).  cl_assoc carries the SET count, which
    State.cache_ways divides by."""
    size = props.get(prefix + "cache-size")
    sets = props.get(prefix + "cache-sets")
    line = props.get(prefix + "cache-line-size")
    if line is None:
        line = props.get(prefix + "cache-block-size")
    if size is None and sets is None and line is None:
        return None
    return CacheLeaf(False, size or 0, sets or 0, line or 0)


def cache_view_of(dt_cache):
    """State.CacheView out of the recorded devicetree nodes."""
    nodes = list(dt_cache.items())
    view = CacheView()
    if not nodes:
        return view
    cpu_props = nodes[0][1]
    view.l1i = dt_leaf(cpu_props, "i-") or CacheLeaf()
    view.l1d = dt_leaf(cpu_props, "d-") or CacheLeaf()
    level = 2
    for _, props in nodes[1:]:
        lvl = props.get("cache-level", level)
        leaf = dt_leaf(props, "") or CacheLeaf()
        if lvl == 2:
            view.l2 = leaf
        elif lvl == 3:
            view.l3 = leaf
        level = lvl + 1
    return view


def kernel_build_of(rec):
    """State.KernelBuild out of the recorded launch facts."""
    return KernelBuild(
        thp=rec.config_is("CONFIG_TRANSPARENT_HUGEPAGE"),
        vdso_text_pages=max(1, (rec.vdso_hi - rec.vdso_lo) // PAGE),
        aslr=(rec.randomize_va_space != 0 and "norandmaps" not in rec.cmdline),
        guard_pages=guard_pages_of(rec.cmdline),
        rnd_bits=rec.rnd_bits,
        rseq=rec.config_is("CONFIG_RSEQ"),
        vlenb=rec.vlenb or 0,
        cache=cache_view_of(rec.dt_cache),
    )


# ------------------------------------------------------------ the checks --

class Report(object):
    def __init__(self):
        self.lines = []
        self.verdicts = {}
        self.disagreements = []

    def say(self, fmt, *args):
        self.lines.append(fmt % args if args else fmt)

    def verdict(self, name, ok, note=""):
        self.verdicts[name] = bool(ok)
        self.say("  %-28s %s%s", name, "PASSED" if ok else "FAILED",
                 ("  " + note) if note else "")

    def differ(self, what, model, kernel):
        self.disagreements.append((what, model, kernel))
        self.say("  DISAGREEMENT %s: model %s, kernel %s", what, model, kernel)


def check_rules(rec, kb, va, rep):
    """A4 sub-check 1: Run.entry_launch_ok_va."""
    ok1, ok2, ok3, r = entry_launch_ok_va(
        va, kb, rec.argv, rec.envp, rec.execfn,
        rec.stack_end, rec.sp, rec.mmap_base)
    t0 = VA_STACK_TOP[va]
    rep.say("  stack_end        0x%x  (stack top 0x%x, below it %d pages)",
            rec.stack_end, t0, (t0 - rec.stack_end) // PAGE)
    rep.say("  sp_at_start      0x%x  (window [0x%x, 0x%x])", rec.sp,
            launch_sp_lo(rec.stack_end, kb, rec.argv, rec.envp, rec.execfn),
            launch_sp_hi(rec.stack_end, kb, rec.argv, rec.envp, rec.execfn))
    rep.say("  mmap base        0x%x  (model's r = %s, mmap_rnd_bits %d)",
            rec.mmap_base, r, kb.rnd_bits)
    rep.say("  pad              %d bytes (arch_align_stack, 0..4095)",
            block_pad_len(kb.rseq, rec.sp, rec.stack_end, rec.argv, rec.envp,
                          rec.execfn))
    for bad in kb.encodable(va):
        rep.differ("KernelBuild encoding", "cannot encode", bad)
    rep.verdict("valid_stack_top_va", ok1)
    rep.verdict("valid_launch_sp", ok2)
    rep.verdict("valid_launch_base", ok3,
                "" if ok3 else "no r gives this base")
    lb = launch_bytes(rec.argv, rec.envp, rec.execfn)
    rep.say("  launch_bytes     %d (Run.valid_launch limit %d)", lb, E2BIG_LIMIT)
    # State.mmap_rnd_bits_max is the model's claim about the sysctl's ceiling
    # (arch/riscv/mm/init.c, set_mmap_rnd_bits_max).  The kernel publishes it.
    kmax = rec.j.get("mmap_rnd_bits_max")
    if kmax is not None:
        rep.say("  mmap_rnd_bits_max model %d, kernel %d",
                MMAP_RND_BITS_MAX[va], kmax)
        if kmax != MMAP_RND_BITS_MAX[va]:
            rep.differ("mmap_rnd_bits_max", MMAP_RND_BITS_MAX[va], kmax)
            return False
    return ok1 and ok2 and ok3


def check_block(rec, kb, rep):
    """A4 sub-check 2: the block and the auxiliary vector."""
    ph = (rec.auxd.get(AT["PHDR"], 0), rec.auxd.get(AT["PHENT"], 0),
          rec.auxd.get(AT["PHNUM"], 0))
    entry = rec.auxd.get(AT["ENTRY"], 0)
    uid = rec.auxd.get(AT["UID"], 0)
    gid = rec.auxd.get(AT["GID"], 0)
    hwcap = rec.auxd.get(AT["HWCAP"], 0)

    # The sixteen AT_RANDOM bytes are a draw: the model takes them from the
    # entry, so the comparison feeds the recorded ones in and the rest of the
    # block is what the model computes.
    rnd_ptr = rec.auxd.get(AT["RANDOM"], 0)
    off = rnd_ptr - rec.sp
    rnd16 = (rec.stack_bytes[off:off + 16]
             if 0 <= off <= len(rec.stack_bytes) - 16 else b"\0" * 16)

    model = build_stack_bytes(kb, rec.mmap_base, ph, entry, rec.sp,
                              rec.stack_end, rec.argv, rec.envp, rec.execfn,
                              uid, gid, hwcap, rnd16)
    actual = rec.stack_bytes
    len_ok = len(model) == len(actual)
    if not len_ok:
        rep.differ("block length", len(model), len(actual))
    first_diff = None
    for i in range(min(len(model), len(actual))):
        if model[i] != actual[i]:
            first_diff = i
            break
    bytes_ok = len_ok and first_diff is None
    if first_diff is not None:
        lo = max(0, first_diff - 16)
        rep.differ("block byte at sp+%d (0x%x)" % (first_diff,
                                                   rec.sp + first_diff),
                   model[lo:first_diff + 16].hex(),
                   actual[lo:first_diff + 16].hex())
    rep.say("  block length     %d bytes, stack_end - sp = %d",
            len(model), rec.stack_end - rec.sp)
    argv0 = int.from_bytes(actual[8:16], "little") if len(actual) >= 16 else 0
    rep.say("  argv[0] - sp     %d (model %d)", argv0 - rec.sp,
            string_base_addr(rec.stack_end, rec.argv, rec.envp, rec.execfn)
            - rec.sp)
    rep.verdict("block bytes", bytes_ok,
                "apart from the 16 AT_RANDOM bytes")

    model_ents = auxv_entries(kb, rec.mmap_base, ph, entry, uid, gid, hwcap,
                              at_random_ptr(rec.sp, kb.rseq, rec.argv,
                                            rec.envp),
                              at_execfn_ptr(rec.stack_end, rec.execfn))
    rep.say("  auxv entries     model %d, kernel %d",
            len(model_ents), len(rec.auxv))
    aux_ok = True
    if len(model_ents) != len(rec.auxv):
        aux_ok = False
        rep.differ("auxv entry count", len(model_ents), len(rec.auxv))
    for i in range(max(len(model_ents), len(rec.auxv))):
        m = model_ents[i] if i < len(model_ents) else None
        k = rec.auxv[i] if i < len(rec.auxv) else None
        if m != k:
            aux_ok = False
            rep.differ("auxv entry %d" % i, fmt_ent(m), fmt_ent(k))
    rep.verdict("auxv entries", aux_ok)

    want = min_sigframe_size(kb, hwcap)
    got = rec.auxd.get(AT["MINSIGSTKSZ"])
    if want != got:
        rep.differ("AT_MINSIGSTKSZ", want, got)
    rep.say("  AT_MINSIGSTKSZ   model %d, kernel %s (vlenb %s, hwcap 0x%x)",
            want, got, rec.vlenb, hwcap)
    sig_ok = want == got
    rep.verdict("AT_MINSIGSTKSZ", sig_ok)

    cw = launch_cache_words(kb)
    cache_tags = [AT["L1I_CACHESIZE"], AT["L1I_CACHEGEOMETRY"],
                  AT["L1D_CACHESIZE"], AT["L1D_CACHEGEOMETRY"],
                  AT["L2_CACHESIZE"], AT["L2_CACHEGEOMETRY"],
                  AT["L3_CACHESIZE"], AT["L3_CACHEGEOMETRY"]]
    cache_ok = True
    for tag, word in zip(cache_tags, cw):
        got = rec.auxd.get(tag)
        if got is None and word == 0:
            continue   # the kernel emits no entry and the model says zero
        if got != word:
            cache_ok = False
            rep.differ("AT_%s" % AT_NAME[tag], word, got)
    rep.say("  cache words      model %s", [hex(x) for x in cw])
    rep.say("  cache words      kernel %s",
            [hex(rec.auxd[t]) for t in cache_tags if t in rec.auxd])
    rep.verdict("cache words", cache_ok)
    return bytes_ok and aux_ok and sig_ok and cache_ok


def fmt_ent(e):
    if e is None:
        return "(absent)"
    return "(%s=%d, 0x%x)" % (AT_NAME.get(e[0], e[0]), e[0], e[1])


def check_vdso(rec, kb, rep, vdso_file):
    """A4 sub-check 3: the vDSO image and the vvar mapping."""
    ehdr = rec.auxd.get(AT["SYSINFO_EHDR"], 0)
    rep.say("  AT_SYSINFO_EHDR  0x%x, [vdso] 0x%x-0x%x, [vvar] start 0x%x",
            ehdr, rec.vdso_lo, rec.vdso_hi, rec.vvar_start)
    elf_ok = rec.vdso_image[:4] == b"\x7fELF"
    place_ok = ehdr == rec.vdso_lo
    vvar_ok = rec.vvar_start == ehdr - VDSO_VVAR_PAGES * PAGE
    if not vvar_ok:
        rep.differ("vvar start", "0x%x (AT_SYSINFO_EHDR - 4 pages)"
                   % (ehdr - VDSO_VVAR_PAGES * PAGE), "0x%x" % rec.vvar_start)
    base_ok = ehdr == vdso_text_base(kb, rec.mmap_base)
    rep.say("  vdso text pages  %d (model's vdso_text_pages encoding: 1..16)",
            kb.vdso_text_pages)
    digest = hashlib.sha256(rec.vdso_image).hexdigest()
    rep.say("  vdso image       %d bytes, sha256 %s", len(rec.vdso_image),
            digest)
    file_ok = None
    if vdso_file and os.path.exists(vdso_file):
        with open(vdso_file, "rb") as fh:
            built = fh.read()
        file_ok = rec.vdso_image[:len(built)] == built
        rep.say("  kernel's vdso.so %d bytes, sha256 %s, %s", len(built),
                hashlib.sha256(built).hexdigest(),
                "the mapped bytes are its bytes" if file_ok else "DIFFERS")
        if not file_ok:
            rep.differ("vDSO image", "the build's vdso.so",
                       "the mapped pages differ")
    rep.verdict("vdso is an ELF", elf_ok)
    rep.verdict("vdso at AT_SYSINFO_EHDR", place_ok and base_ok)
    rep.verdict("vvar four pages below", vvar_ok)
    if file_ok is not None:
        rep.verdict("vdso is the build's", file_ok)
    return elf_ok and place_ok and base_ok and vvar_ok and (file_ok is not False)


def check_one(path, va, vdso_file):
    rec = Record(path)
    kb = kernel_build_of(rec)
    rep = Report()
    rep.say("== %s  (run %s)", os.path.basename(path), rec.run)
    rep.say("  execfn %r  argc %d  envc %d", rec.execfn.decode("latin1"),
            len(rec.argv), len(rec.envp))
    rep.say("  facts: rseq=%s aslr=%s guard=%d pages rnd_bits=%d vlenb=%s "
            "thp=%s", kb.rseq, kb.aslr, kb.guard_pages, kb.rnd_bits,
            rec.vlenb, kb.thp)
    rep.say("  C = %d, L = %d, items = %d, auxv_count = %d",
            block_head_size(kb.rseq, rec.argv, rec.envp),
            launch_string_bytes(rec.argv, rec.envp, rec.execfn),
            block_items(rec.argv, rec.envp), auxv_count(kb.rseq))
    rep.say(" A4.1 Run.entry_launch_ok_va")
    ok1 = check_rules(rec, kb, va, rep)
    rep.say(" A4.2 the block and the auxiliary vector")
    ok2 = check_block(rec, kb, rep)
    rep.say(" A4.3 the vDSO image and the vvar mapping")
    ok3 = check_vdso(rec, kb, rep, vdso_file)
    return rec, kb, rep, (ok1, ok2, ok3)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("logs", nargs="+")
    ap.add_argument("--va", default="Sv48", choices=sorted(VA_STACK_TOP))
    ap.add_argument("--vdso", default="",
                    help="the vdso.so the kernel build carries")
    ap.add_argument("--json", default="", help="write the verdicts here")
    args = ap.parse_args()

    all_ok, out = True, {}
    for path in args.logs:
        _, _, rep, oks = check_one(path, args.va, args.vdso)
        print("\n".join(rep.lines))
        print("  A4.1 %s   A4.2 %s   A4.3 %s"
              % tuple("passed" if o else "FAILED" for o in oks))
        print("")
        out[os.path.basename(path)] = {
            "verdicts": rep.verdicts,
            "sub_checks": {"A4.1": oks[0], "A4.2": oks[1], "A4.3": oks[2]},
            "disagreements": [list(map(str, d)) for d in rep.disagreements],
        }
        all_ok = all_ok and all(oks)
    if args.json:
        with open(args.json, "w", encoding="utf-8") as fh:
            json.dump(out, fh, indent=1, sort_keys=True)
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
