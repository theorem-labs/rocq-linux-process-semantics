#!/usr/bin/env python3
"""patch_dtb.py - give the boot CPU a cache hierarchy in the devicetree.

qemu's -M virt writes no cache property at all, so a boot of it leaves every
AT_L*_CACHE* word zero and says nothing about the model's cache formulas
(State.cache_ways, State.cache_size_word, State.cache_geometry_word).  This
script reads the devicetree qemu dumped and writes one in which the boot CPU
carries split L1 caches and a unified L2, exactly the properties Linux
v6.18.46 (commit 1f99e9ab748f) reads in drivers/base/cacheinfo.c,
cache_of_set_props.  Booting qemu with -dtb on the result makes the kernel
publish eight non-zero cache words, which check_start_state.py then reads
against the model.

    patch_dtb.py IN.dtb OUT.dtb

The values are a plain 4-way/8-way/16-way hierarchy, chosen so that each
auxv word is distinct and no ways count is a power of the set count:

    L1I  32 KiB, 64 sets,  64-byte line  -> 8 ways
    L1D  32 KiB, 128 sets, 32-byte line  -> 8 ways
    L2  512 KiB, 1024 sets, 64-byte line -> 8 ways
"""

import struct
import sys

FDT_BEGIN_NODE, FDT_END_NODE, FDT_PROP, FDT_NOP, FDT_END = 1, 2, 3, 4, 9

L1I = [("i-cache-size", 32 * 1024), ("i-cache-sets", 64),
       ("i-cache-line-size", 64), ("i-cache-block-size", 64)]
L1D = [("d-cache-size", 32 * 1024), ("d-cache-sets", 128),
       ("d-cache-line-size", 32), ("d-cache-block-size", 32)]
L2 = [("cache-size", 512 * 1024), ("cache-sets", 1024),
      ("cache-line-size", 64), ("cache-block-size", 64), ("cache-level", 2)]


class Node(object):
    def __init__(self, name):
        self.name = name
        self.props = []      # (name, bytes), in order
        self.children = []

    def set(self, name, raw):
        for i, (n, _) in enumerate(self.props):
            if n == name:
                self.props[i] = (name, raw)
                return
        self.props.append((name, raw))

    def walk(self):
        yield self
        for c in self.children:
            for n in c.walk():
                yield n

    def child(self, name):
        for c in self.children:
            if c.name == name:
                return c
        return None


def parse(blob):
    f = struct.unpack(">10I", blob[:40])
    if f[0] != 0xD00DFEED:
        raise SystemExit("not a devicetree")
    off_struct, off_strings, off_rsv = f[2], f[3], f[4]
    boot_cpu, size_strings, size_struct = f[7], f[8], f[9]
    strings = blob[off_strings:off_strings + size_strings]
    pos, end = off_struct, off_struct + size_struct
    root, stack = None, []
    while pos < end:
        (tok,) = struct.unpack(">I", blob[pos:pos + 4])
        pos += 4
        if tok == FDT_BEGIN_NODE:
            z = blob.index(b"\0", pos)
            node = Node(blob[pos:z].decode())
            pos = (z + 4) & ~3
            if stack:
                stack[-1].children.append(node)
            else:
                root = node
            stack.append(node)
        elif tok == FDT_END_NODE:
            stack.pop()
        elif tok == FDT_PROP:
            ln, nameoff = struct.unpack(">II", blob[pos:pos + 8])
            pos += 8
            z = strings.index(b"\0", nameoff)
            stack[-1].props.append((strings[nameoff:z].decode(),
                                    blob[pos:pos + ln]))
            pos = (pos + ln + 3) & ~3
        elif tok == FDT_NOP:
            continue
        elif tok == FDT_END:
            break
        else:
            raise SystemExit("bad token %d" % tok)
    rsv = blob[off_rsv:off_struct]
    return root, rsv, boot_cpu


def emit(root):
    strings, offsets = bytearray(), {}

    def soff(name):
        if name not in offsets:
            offsets[name] = len(strings)
            strings.extend(name.encode() + b"\0")
        return offsets[name]

    out = bytearray()

    def node(n):
        out.extend(struct.pack(">I", FDT_BEGIN_NODE))
        raw = n.name.encode() + b"\0"
        raw += b"\0" * ((-len(raw)) % 4)
        out.extend(raw)
        for name, val in n.props:
            out.extend(struct.pack(">III", FDT_PROP, len(val), soff(name)))
            out.extend(val)
            out.extend(b"\0" * ((-len(val)) % 4))
        for c in n.children:
            node(c)
        out.extend(struct.pack(">I", FDT_END_NODE))

    node(root)
    out.extend(struct.pack(">I", FDT_END))
    return bytes(out), bytes(strings)


def build(root, rsv, boot_cpu):
    struct_blk, strings_blk = emit(root)
    off_rsv = 40
    off_struct = off_rsv + len(rsv)
    off_strings = off_struct + len(struct_blk)
    total = off_strings + len(strings_blk)
    head = struct.pack(">10I", 0xD00DFEED, total, off_struct, off_strings,
                       off_rsv, 17, 16, boot_cpu, len(strings_blk),
                       len(struct_blk))
    return head + rsv + struct_blk + strings_blk


def u32(v):
    return struct.pack(">I", v)


def main():
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    with open(sys.argv[1], "rb") as fh:
        root, rsv, boot_cpu = parse(fh.read())

    phandles = [struct.unpack(">I", v)[0]
                for n in root.walk() for k, v in n.props
                if k in ("phandle", "linux,phandle") and len(v) == 4]
    l2_phandle = max(phandles) + 1 if phandles else 1

    cpus = root.child("cpus")
    if cpus is None:
        raise SystemExit("no /cpus node")
    l2 = Node("l2-cache0")
    l2.set("compatible", b"cache\0")
    l2.set("cache-unified", b"")
    for name, val in L2:
        l2.set(name, u32(val))
    l2.set("phandle", u32(l2_phandle))
    cpus.children.append(l2)

    n = 0
    for cpu in cpus.children:
        if not cpu.name.startswith("cpu@"):
            continue
        for name, val in L1I + L1D:
            cpu.set(name, u32(val))
        cpu.set("next-level-cache", u32(l2_phandle))
        n += 1
    if n == 0:
        raise SystemExit("no cpu@ node under /cpus")

    with open(sys.argv[2], "wb") as fh:
        fh.write(build(root, rsv, boot_cpu))
    print("%s: %d cpu nodes given L1I/L1D, one L2 (phandle %d)"
          % (sys.argv[2], n, l2_phandle))


if __name__ == "__main__":
    main()
