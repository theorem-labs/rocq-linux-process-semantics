#!/usr/bin/env python3
"""merge_launch.py - put the boot's own facts into the probe's launch line.

run-kernel.sh calls this after every boot.  The probe writes the facts it can
read for itself; three facts it cannot read are the kernel's .config, the
devicetree the firmware handed the kernel, and the boot command line.  This
script adds them to the launch object (the first JSON line) under the keys
"config", "dt_cache" and "cmdline", keeps every key the probe wrote and keeps
the key order, and writes the log with its provenance header.

The devicetree cache properties are the ones Linux v6.18.46 (commit
1f99e9ab748f) reads in drivers/base/cacheinfo.c, cache_of_set_props and
cache_size/cache_get_line_size/cache_associativity: cache-size, cache-sets,
cache-line-size, cache-block-size and their i- and d- forms, on the boot CPU
node and on each node its next-level-cache chain reaches.  An absent property
is an absent key, so a kernel that reports no cache at all gives {}.

Usage:
  merge_launch.py --config .config --dtb D --cmdline S --raw R --header H \\
      --out-dir OUT --name TAG [--mode place|startstate] [--prefix P]
"""

import argparse
import json
import os
import struct
import sys

# The .config lines that decide the start state.  CONFIG_RSEQ adds the two
# AT_RSEQ_* auxv entries (fs/binfmt_elf.c, create_elf_tables);
# CONFIG_TRANSPARENT_HUGEPAGE and CONFIG_COMPAT_BRK change placement and the
# initial break; CONFIG_RISCV_ISA_V decides AT_HWCAP's V bit and so
# AT_MINSIGSTKSZ (arch/riscv/kernel/signal.c, get_rt_frame_size);
# CONFIG_ARCH_MMAP_RND_BITS* bound vm.mmap_rnd_bits (arch/riscv/Kconfig);
# CONFIG_MSEAL_SYSTEM_MAPPINGS seals the vDSO pair (mm/mseal.c).
CONFIG_PREFIXES = (
    "CONFIG_RSEQ",
    "CONFIG_TRANSPARENT_HUGEPAGE",
    "CONFIG_COMPAT_BRK",
    "CONFIG_RISCV_ISA_V",
    "CONFIG_ARCH_MMAP_RND_BITS",
    "CONFIG_MSEAL_SYSTEM_MAPPINGS",
    "CONFIG_LSM_MMAP_MIN_ADDR",
    "CONFIG_DEFAULT_MMAP_MIN_ADDR",
    "CONFIG_RISCV_ISA_ZICBOM",
    "CONFIG_HAVE_RSEQ",
)

CACHE_PROPS = (
    "cache-size",
    "cache-sets",
    "cache-line-size",
    "cache-block-size",
    "cache-level",
    "cache-unified",
    "i-cache-size",
    "i-cache-sets",
    "i-cache-line-size",
    "i-cache-block-size",
    "d-cache-size",
    "d-cache-sets",
    "d-cache-line-size",
    "d-cache-block-size",
)


def config_lines(path):
    """The whole lines of [path] that name a key of CONFIG_PREFIXES."""
    out = []
    with open(path, "r", encoding="utf-8", errors="replace") as fh:
        for line in fh:
            line = line.rstrip("\n")
            body = line
            if body.startswith("# "):
                body = body[2:]
            key = body.split("=", 1)[0].split(" ", 1)[0]
            if key.startswith(CONFIG_PREFIXES):
                out.append(line)
    return out


def parse_fdt(blob):
    """Every node of a flattened devicetree: path -> {property: bytes}."""
    fields = struct.unpack(">10I", blob[:40])
    magic, off_struct, off_strings = fields[0], fields[2], fields[3]
    boot_cpu, size_strings, size_struct = fields[7], fields[8], fields[9]
    if magic != 0xD00DFEED:
        raise ValueError("not a flattened devicetree: magic %#x" % magic)
    strings = blob[off_strings:off_strings + size_strings]
    pos, end = off_struct, off_struct + size_struct
    stack, nodes = [], {}
    while pos < end:
        (tok,) = struct.unpack(">I", blob[pos:pos + 4])
        pos += 4
        if tok == 1:  # FDT_BEGIN_NODE
            z = blob.index(b"\0", pos)
            stack.append(blob[pos:z].decode("utf-8", "replace"))
            pos = (z + 4) & ~3
            nodes.setdefault(node_path(stack), {})
        elif tok == 2:  # FDT_END_NODE
            stack.pop()
        elif tok == 3:  # FDT_PROP
            ln, nameoff = struct.unpack(">II", blob[pos:pos + 8])
            pos += 8
            z = strings.index(b"\0", nameoff)
            name = strings[nameoff:z].decode("utf-8", "replace")
            nodes[node_path(stack)][name] = blob[pos:pos + ln]
            pos = (pos + ln + 3) & ~3
        elif tok == 4:  # FDT_NOP
            continue
        elif tok == 9:  # FDT_END
            break
        else:
            raise ValueError("bad devicetree token %d at %d" % (tok, pos - 4))
    return nodes, boot_cpu


def node_path(stack):
    parts = [p for p in stack if p]
    return "/" + "/".join(parts)


def prop_value(raw):
    if len(raw) == 0:
        return True
    if len(raw) == 4:
        return struct.unpack(">I", raw)[0]
    if len(raw) == 8:
        return struct.unpack(">Q", raw)[0]
    return raw.hex()


def dt_cache(dtb_path):
    """The cache properties of the boot CPU and of its next-level caches."""
    if not dtb_path or not os.path.exists(dtb_path):
        return {}
    with open(dtb_path, "rb") as fh:
        nodes, boot_cpu = parse_fdt(fh.read())
    cpus = sorted(p for p in nodes
                  if p.startswith("/cpus/cpu@") and p.count("/") == 2)
    chosen = None
    for path in cpus:
        reg = nodes[path].get("reg")
        if reg is not None and len(reg) == 4 and struct.unpack(">I", reg)[0] == boot_cpu:
            chosen = path
            break
    if chosen is None and cpus:
        chosen = cpus[0]
    if chosen is None:
        return {}
    by_phandle = {}
    for path, props in nodes.items():
        for key in ("phandle", "linux,phandle"):
            raw = props.get(key)
            if raw is not None and len(raw) == 4:
                by_phandle[struct.unpack(">I", raw)[0]] = path
    out, path, seen = {}, chosen, set()
    while path is not None and path not in seen:
        seen.add(path)
        props = nodes.get(path, {})
        got = {}
        for name in CACHE_PROPS:
            if name in props:
                got[name] = prop_value(props[name])
        out[path] = got
        nxt = props.get("next-level-cache") or props.get("l2-cache")
        if nxt is None or len(nxt) != 4:
            break
        path = by_phandle.get(struct.unpack(">I", nxt)[0])
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--config", required=True)
    ap.add_argument("--dtb", default="")
    ap.add_argument("--cmdline", required=True)
    ap.add_argument("--raw", required=True)
    ap.add_argument("--header", required=True)
    ap.add_argument("--out-dir", required=True)
    ap.add_argument("--name", required=True)
    ap.add_argument("--mode", default="place")
    ap.add_argument("--prefix", default="linux-6.18.46")
    args = ap.parse_args()

    extra = [
        ("config", config_lines(args.config)),
        ("dt_cache", dt_cache(args.dtb)),
        ("cmdline", args.cmdline),
    ]
    with open(args.header, "r", encoding="utf-8") as fh:
        header = fh.read()

    merged, runs = [], {}
    with open(args.raw, "r", encoding="utf-8", errors="replace") as fh:
        for line in fh:
            line = line.strip()
            if not line.startswith("{"):
                continue
            obj = json.loads(line, object_pairs_hook=dict)
            if "maps" in obj:  # the launch object, not a call
                for key, val in extra:
                    obj[key] = val
                runs.setdefault(obj.get("run", "place"), []).append(obj)
            merged.append(json.dumps(obj, separators=(",", ":")))

    written = []
    if args.mode == "startstate":
        if not runs:
            sys.exit("merge_launch.py: no launch object in %s" % args.raw)
        for run, objs in runs.items():
            if len(objs) != 1:
                sys.exit("merge_launch.py: %d '%s' launches in %s"
                         % (len(objs), run, args.raw))
            path = os.path.join(args.out_dir,
                                "%s-%s-%s.log" % (args.prefix, args.name, run))
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(header)
                fh.write(json.dumps(objs[0], separators=(",", ":")) + "\n")
            written.append(path)
    else:
        path = os.path.join(args.out_dir, "%s.log" % args.name)
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(header)
            fh.write("\n".join(merged) + "\n")
        written.append(path)

    for path in written:
        print(path)


if __name__ == "__main__":
    main()
