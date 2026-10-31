#!/usr/bin/env python3
"""start_state_to_rocq.py — turn a start-state log into a Rocq check.

A start-state log is what tools/placement_conformance/probe.c wrote on a
real booted Linux v6.18.46 riscv64 kernel in "pc_mode=startstate".  This
turns its one launch object into a Rocq file that states the recorded launch
as LPS terms and closes three lemmas by computation:

    launch_ok   Run.entry_launch_ok_va holds of the recorded stack end,
                stack pointer and mmap base, under the recorded launch facts;
    block_ok    Run.entry_stack_image, THE MODEL'S OWN BLOCK, equals the
                bytes the kernel wrote between sp and the stack end — every
                byte, the sixteen AT_RANDOM bytes included, because the draw
                carries them;
    auxv_ok     StackLayout.auxv_entries equals the vector decoded from the
                recorded /proc/self/auxv.

    start_state_to_rocq.py LOG --out F.v [--name NAME] [--va {Sv39,Sv48,Sv57}]
                               [--perturb-byte K [--sibling MODULE]]

With --perturb-byte K the file is a NEGATIVE CONTROL: byte K of the recorded
block is moved by one, the lemma becomes "the model's block is NOT this one",
and the file compiles only if the model refuses it.  A block_ok that had
stopped computing anything would be green on its own, so the build carries a
negative beside the shortest record and beside the longest one, each moving
a byte in a different part of the block.

This is the A4 check of dispatch://OSSV-257.  It supersedes
check_start_state.py, which compared the record with a PYTHON transcription
of the model: a second model of the entry block that nothing proved agreed
with the first.  Here the model is read from the Rocq source by Rocq, and
nothing in this file states what the model says.

WHAT THIS FILE COMPUTES, and why none of it is trusted.  Everything emitted
below is either a fact copied out of the record, or the mmap draw [r].  The
draw is a WITNESS: Run.valid_launch_base is an existential, so the proof has
to name the r the record implies, and this script inverts Run.mmap_base_of
to find it.  A wrong r does not make a wrong lemma pass — the proof's last
step recomputes mmap_base_of at that r inside Rocq and demands the recorded
base — it only makes the file fail to compile.

WHERE THE PhdrInfo AND THE IMAGE ENTRY COME FROM.  The probe writes no ELF
header of its own, so AT_PHDR, AT_PHENT, AT_PHNUM and AT_ENTRY are read out
of the recorded auxiliary vector.  Those four of the vector's twenty-nine
entries are therefore fed in rather than checked by auxv_ok; the other
twenty-five, and the whole of block_ok, are the model's.  The header of each
generated file says so.
"""

import argparse
import hashlib
import json
import pathlib
import sys
import textwrap

PAGE = 4096
TWO64 = 1 << 64

# Run.va_stack_top and Run.stack_rnd_max, needed only to invert
# Run.mmap_base_of for the witness r.  Rocq checks the result.
VA_STACK_TOP = {"Sv39": 1 << 38, "Sv48": 0x800000000000, "Sv57": 0x800000000000}
MMAP_RND_BITS_MAX = {"Sv39": 24, "Sv48": 33, "Sv57": 33}
STACK_RND_MAX = 0x3FFFF000
STACK_MAX_SIZE = 8 * 1024 * 1024
MMAP_MIN_GAP = 128 * 1024 * 1024

AT_PHDR, AT_PHENT, AT_PHNUM = 3, 4, 5
AT_ENTRY, AT_UID, AT_GID, AT_HWCAP, AT_RANDOM = 9, 11, 13, 16, 25

# State.vdso_vvar_pages
VDSO_VVAR_PAGES = 4


class LogError(Exception):
    pass


# ----------------------------------------------------------------- reading --


def read_record(path):
    """The header comment lines and the one launch object of a log."""
    header, obj = [], None
    for line in pathlib.Path(path).read_text().splitlines():
        if line.startswith("#"):
            header.append(line)
        elif line.startswith("{") and obj is None:
            obj = json.loads(line)
    if obj is None:
        raise LogError(f"{path}: no launch object")
    for key in ("maps", "auxv", "stack_bytes", "sp_at_start", "stack_end",
                "argv", "envp", "execfn", "brk0", "config", "cmdline",
                "dt_cache", "mmap_rnd_bits", "randomize_va_space",
                "vvar_start", "vdso_image"):
        if key not in obj:
            raise LogError(f"{path}: the launch object has no {key!r}")
    return header, obj


def header_value(header, key):
    for line in header:
        if line.startswith("# " + key + ": "):
            return line[len(key) + 4:]
    return "?"


def decode_auxv(raw):
    """The recorded /proc/self/auxv as (type, value) pairs, AT_NULL last."""
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
    return None


def guard_pages_of(cmdline):
    """The stack_guard_gap boot parameter in pages.  mm/mmap.c,
    cmdline_parse_stack_guard_gap, Linux v6.18.46, commit 1f99e9ab748f: the
    default is 256 pages."""
    for word in cmdline.split():
        if word.startswith("stack_guard_gap="):
            return int(word.split("=", 1)[1])
    return 256


def dt_leaf(props, prefix):
    """One cache leaf out of a devicetree node's properties, the way Linux
    reads them (drivers/base/cacheinfo.c, cache_of_set_props, Linux v6.18.46,
    commit 1f99e9ab748f): cache-size, cache-sets, then cache-line-size or
    cache-block-size, with the i- and d- forms at a split level.  The middle
    field is the SET count, which State.cache_ways divides by."""
    size = props.get(prefix + "cache-size")
    sets = props.get(prefix + "cache-sets")
    line = props.get(prefix + "cache-line-size")
    if line is None:
        line = props.get(prefix + "cache-block-size")
    if size is None and sets is None and line is None:
        return None
    return (size or 0, sets or 0, line or 0)


def cache_leaves(dt_cache):
    """The four leaves ARCH_DLINFO publishes, in its order: L1 instruction,
    L1 data, L2 unified, L3 unified."""
    absent = (0, 0, 0)
    nodes = list(dt_cache.items())
    l1i = l1d = l2 = l3 = absent
    names = {"l1i": "", "l1d": "", "l2": "", "l3": ""}
    if nodes:
        cpu_name, cpu_props = nodes[0]
        l1i = dt_leaf(cpu_props, "i-") or absent
        l1d = dt_leaf(cpu_props, "d-") or absent
        if l1i != absent:
            names["l1i"] = cpu_name
        if l1d != absent:
            names["l1d"] = cpu_name
        level = 2
        for name, props in nodes[1:]:
            lvl = props.get("cache-level", level)
            leaf = dt_leaf(props, "") or absent
            if lvl == 2:
                l2, names["l2"] = leaf, name
            elif lvl == 3:
                l3, names["l3"] = leaf, name
            level = lvl + 1
    return (l1i, l1d, l2, l3), names


# ----------------------------------------------------- the facts, decoded --


def facts(path, header, obj, va):
    """Every number the generated file carries, read out of the record."""
    auxv = decode_auxv(bytes.fromhex(obj["auxv"]))
    aux = dict(auxv)
    for tag, name in ((AT_PHDR, "AT_PHDR"), (AT_PHENT, "AT_PHENT"),
                      (AT_PHNUM, "AT_PHNUM"), (AT_ENTRY, "AT_ENTRY"),
                      (AT_RANDOM, "AT_RANDOM"), (AT_HWCAP, "AT_HWCAP")):
        if tag not in aux:
            raise LogError(f"{path}: the recorded auxv has no {name}")

    vdso = maps_range(obj["maps"], "[vdso]")
    if vdso is None:
        raise LogError(f"{path}: no [vdso] mapping in the launch object")
    text_pages = (vdso[1] - vdso[0]) // PAGE
    if not 1 <= text_pages <= 16:
        raise LogError(f"{path}: the vDSO text is {text_pages} pages; "
                       "State.vdso_text_pages holds 1 to 16")
    # arch/riscv/kernel/vdso.c, __setup_additional_pages: the pair is mapped
    # directly below mm->mmap_base before anything else, so the text's end is
    # the base.
    mbase = vdso[1]

    # THE IMAGE'S PhdrInfo AND ENTRY POINT.  The probe publishes its own ELF
    # header under "elf" (probe.c, read_elf_facts), and that is the source to
    # use: taking the four values back out of the recorded auxiliary vector
    # would make the four entries AT_PHDR, AT_PHENT, AT_PHNUM and AT_ENTRY of
    # auxv_ok say nothing.  A record written by a probe older than that key
    # falls back to the vector, and the generated file says so.
    elf = obj.get("elf")
    if isinstance(elf, dict) and {"base", "phoff", "phdr", "phentsize",
                                  "phnum", "entry"} <= set(elf):
        if elf["phdr"] != elf["base"] + elf["phoff"]:
            raise LogError(
                f"{path}: the record's elf.phdr is {elf['phdr']:#x} but "
                f"elf.base + elf.phoff is "
                f"{elf['base'] + elf['phoff']:#x}")
        phdr = (elf["phdr"], elf["phentsize"], elf["phnum"])
        img_entry = elf["entry"]
        elf_source = True
    else:
        phdr = (aux[AT_PHDR], aux[AT_PHENT], aux[AT_PHNUM])
        img_entry = aux[AT_ENTRY]
        elf_source = False

    sp = obj["sp_at_start"]
    top = obj["stack_end"]
    stack_bytes = bytes.fromhex(obj["stack_bytes"])
    if len(stack_bytes) != top - sp:
        raise LogError(f"{path}: the record holds {len(stack_bytes)} stack "
                       f"bytes but stack_end - sp_at_start is {top - sp}")
    off = aux[AT_RANDOM] - sp
    if not 0 <= off <= len(stack_bytes) - 16:
        raise LogError(f"{path}: AT_RANDOM points at {aux[AT_RANDOM]:#x}, "
                       f"which is not sixteen bytes inside the recorded block")
    random16 = stack_bytes[off:off + 16]

    rnd_bits = obj["mmap_rnd_bits"]
    if not 18 <= rnd_bits <= MMAP_RND_BITS_MAX[va]:
        raise LogError(f"{path}: vm.mmap_rnd_bits is {rnd_bits}, outside the "
                       f"18..{MMAP_RND_BITS_MAX[va]} State.mmap_rnd_bits "
                       f"encodes under {va}")
    guard = guard_pages_of(obj["cmdline"])
    if not 0 <= guard < 0x4ABA6A2AC:
        raise LogError(f"{path}: stack_guard_gap is {guard} pages, outside "
                       "the range State.stack_guard_gap_pages encodes")

    hwcap = aux[AT_HWCAP]
    # State.hwcap_has_v, State.launch_vlenb: with the V bit the encoding is
    # 16 * 2^(kb_vlenb mod 10), so only a power-of-two multiple of 16 can be
    # stated; without it the machine's vlenb reaches no auxv word and the
    # encoding's zero is the one that gives AT_MINSIGSTKSZ its F-only value.
    has_v = bool((hwcap >> 21) & 1)
    vlenb = obj.get("vlenb")
    if has_v:
        if not vlenb:
            raise LogError(f"{path}: AT_HWCAP {hwcap:#x} carries V but the "
                           "record has no vlenb")
        k, probe = None, 16
        for i in range(10):
            if probe == vlenb:
                k = i
                break
            probe *= 2
        if k is None:
            raise LogError(f"{path}: vlenb {vlenb} is not 16 * 2^k for k < 10, "
                           "so State.launch_vlenb cannot state it")
        kb_vlenb = k
    else:
        if vlenb:
            raise LogError(f"{path}: AT_HWCAP {hwcap:#x} has no V bit but the "
                           f"record carries vlenb {vlenb}")
        kb_vlenb = 0

    aslr = obj["randomize_va_space"] != 0 and "norandmaps" not in obj["cmdline"]
    leaves, leaf_names = cache_leaves(obj["dt_cache"])

    return {
        "path": path,
        "log": pathlib.Path(path).name,
        "sha256": hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest(),
        "run": obj.get("run", "?"),
        "header": header,
        "auxv": auxv,
        "argv": [s.encode("utf-8", "surrogateescape") for s in obj["argv"]],
        "envp": [s.encode("utf-8", "surrogateescape") for s in obj["envp"]],
        "execfn": obj["execfn"].encode("utf-8", "surrogateescape"),
        "uid": aux.get(AT_UID, 0),
        "gid": aux.get(AT_GID, 0),
        "hwcap": hwcap,
        "phdr": phdr,
        "img_entry": img_entry,
        "elf_source": elf_source,
        "sp": sp,
        "top": top,
        "brk0": obj["brk0"],
        "mbase": mbase,
        "vdso_lo": vdso[0],
        "vvar_start": obj["vvar_start"],
        "text_pages": text_pages,
        "stack_bytes": stack_bytes,
        "random16": random16,
        "random_off": off,
        "thp": "CONFIG_TRANSPARENT_HUGEPAGE=y" in obj["config"],
        "rseq": "CONFIG_RSEQ=y" in obj["config"],
        "aslr": aslr,
        "rva": obj["randomize_va_space"],
        "guard": guard,
        "rnd_bits": rnd_bits,
        "vlenb": vlenb or 0,
        "kb_vlenb": kb_vlenb,
        "leaves": leaves,
        "leaf_names": leaf_names,
        "cmdline": obj["cmdline"],
        "va": va,
    }


def mmap_draw_witness(f):
    """r, the page draw arch_mmap_rnd made, as Run.mmap_base_of implies it.

    A HINT, not a check: launch_ok recomputes mmap_base_of at this r inside
    Rocq.  mm/util.c, mmap_base, Linux v6.18.46, commit 1f99e9ab748f.
    """
    va = f["va"]
    top0 = VA_STACK_TOP[va]
    pad = PAGE * f["guard"] + (STACK_RND_MAX if f["aslr"] else 0)
    gap = STACK_MAX_SIZE + pad if ((STACK_MAX_SIZE + pad) % TWO64
                                   > STACK_MAX_SIZE) else STACK_MAX_SIZE
    max_gap = top0 // 6 * 5
    if gap < MMAP_MIN_GAP and MMAP_MIN_GAP < max_gap:
        gap = MMAP_MIN_GAP
    elif gap > max_gap:
        gap = max_gap
    base_at_zero = (top0 - gap + PAGE - 1) // PAGE * PAGE
    delta = base_at_zero - f["mbase"]
    if delta < 0 or delta % PAGE:
        raise LogError(
            f"{f['path']}: no page draw gives the recorded mmap base "
            f"{f['mbase']:#x}: Run.mmap_base_of at r = 0 is "
            f"{base_at_zero:#x} and the difference is {delta} bytes")
    r = delta // PAGE
    if f["aslr"]:
        if r >= 2 ** f["rnd_bits"]:
            raise LogError(f"{f['path']}: the draw the base implies is "
                           f"{r}, which vm.mmap_rnd_bits {f['rnd_bits']} "
                           "cannot produce")
    elif r != 0:
        raise LogError(f"{f['path']}: the launch did not randomize, so the "
                       f"draw must be 0, and the base implies {r}")
    return r, base_at_zero


# ------------------------------------------------------------------ Rocq -----


def byte_list(bs, indent, per_line=16):
    """A [list byte] written as [map (Z_to_bv 8) [..]]'s argument."""
    if not bs:
        return "[]"
    rows = []
    for i in range(0, len(bs), per_line):
        rows.append("; ".join("%3d" % b for b in bs[i:i + per_line]))
    pad = " " * indent
    return "[ " + (";\n" + pad).join(rows) + " ]"


def string_list(strs, indent):
    """A [list (list byte)] written as [map (map (Z_to_bv 8)) [..]]'s
    argument, one string per line."""
    if not strs:
        return "[]"
    pad = " " * indent
    rows = ["[" + "; ".join(str(b) for b in s) + "]" for s in strs]
    return "[ " + (";\n" + pad).join(rows) + " ]"


def auxv_list(entries, indent):
    pad = " " * indent
    rows = ["(%d, %#x)" % (t, v) for t, v in entries]
    out, line = [], ""
    for row in rows:
        if line and len(line) + len(row) + 2 > 64:
            out.append(line)
            line = row
        else:
            line = (line + "; " + row) if line else row
    if line:
        out.append(line)
    return "[ " + (";\n" + pad).join(out) + " ]"


def leaf_term(leaf):
    size, sets, line = leaf
    return "mkCacheLeaf false %d%%N %d%%N %d%%N" % (size, sets, line)


def para(text):
    """One comment paragraph, wrapped to the file's width."""
    return textwrap.fill(" ".join(text.split()), width=74,
                         initial_indent="    ", subsequent_indent="    ")


HEADER = '''(** * {module} — {title}

    GENERATED by tools/placement_conformance/start_state_to_rocq.py from
    tests/placement/{log}
    (sha256 {sha256}).
    Do not edit: change the log or the generator.

{record_note}

{checked_note}

{phdr_note}

    See tools/placement_conformance/README.md, where the probe and the boot
    script live (branch revision/place), and reports/a4-start-state.md. *)

From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType.
Import ListNotations.
Local Open Scope Z_scope.

(** ** The launch facts the boot reported

{facts_note} *)
Definition rec_kernel : KernelBuild :=
  mkKernelBuild {thp} {kb_vdso}%N {aslr} {guard}%N {kb_rnd_bits}%N {rseq}
    {kb_vlenb}%N
    (mkCacheView
      ({l1i})
      ({l1d})
      ({l2})
      ({l3})).

(** The argument vector, the environment and the exec file name, byte for
    byte as the probe recorded them. *)
Definition rec_argv : list (list byte) :=
  map (map (Z_to_bv 8))
  {argv}.

Definition rec_envp : list (list byte) :=
  map (map (Z_to_bv 8))
  {envp}.

Definition rec_execfn : list byte :=
  map (Z_to_bv 8) {execfn}.

(** The launch's input.  The image file system, the standard input, the
    supplementary groups, the network, the signal mask and the private /tmp
    reach no part of the entry block, so they are the empty or silent
    values; the credentials and AT_HWCAP are the recorded ones.

{hwcap_note} *)
Definition rec_input : ProcInput :=
  mkProcInput_full rec_argv rec_envp [] IEof
    (Z_to_bv 64 {uid}) (Z_to_bv 64 {gid}) []
    net_silent default_nofile (Z_to_bv 64 0) (Z_to_bv 64 {hwcap:#x})
    false {va} default_urandom [] rec_kernel rec_execfn.

(** The image, as {phdr_src}: the phdr table at
    {phdr_addr:#x}, {phdr_num} entries of {phdr_ent} bytes, and an entry point
    of {img_entry:#x}. *)
Definition rec_phdr : PhdrInfo := mkPhdrInfo {phdr_addr:#x}%N {phdr_ent}%N {phdr_num}%N.
Definition rec_img_entry : word := Z_to_bv 64 {img_entry:#x}.

(** The entry.  [ed_top] is the recorded stack end and [ed_random] is the
    sixteen bytes the record holds at AT_RANDOM, which is sp + {random_off}.
    [ed_vdso] reaches no byte of the block. *)
Definition rec_sp : word := Z_to_bv 64 {sp:#x}.
Definition rec_brk : word := Z_to_bv 64 {brk0:#x}.
Definition rec_mbase : word := Z_to_bv 64 {mbase:#x}.
Definition rec_top : word := Z_to_bv 64 {top:#x}.
Definition rec_random : bv 128 := Z_to_bv 128 {random:#x}.

Definition rec_draw : EntryDraw := mkDraw rec_random rec_top vdso_keeps_all.
Definition rec_entry : ExecEntry := mkEntry rec_sp rec_brk rec_mbase rec_draw.

(** The {block_len} bytes the kernel left between sp and the stack end. *)
Definition rec_stack_bytes : list byte :=
  map (Z_to_bv 8)
  {bytes}.

(** The {auxv_count} entries of the recorded /proc/self/auxv, in the order the
    kernel wrote them. *)
Definition rec_auxv : list (word * word) :=
  map (fun tv => (Z_to_bv 64 (fst tv), Z_to_bv 64 (snd tv)))
  {auxvl}.

(** ** Two bit vectors are equal when their unsigned values are

    [bv] carries a well-formedness witness beside its value, and the
    witnesses the two sides of [block_ok] carry come from different lemmas
    of stdpp -- [bv_extract]'s and [Z_to_bv]'s -- which are [Qed]-opaque, so
    [vm_compute] reduces the VALUES to the same literals and leaves the
    witnesses unreduced.  [bv_wf] is proof-irrelevant ([bv_wf_pi]), which is
    what [bv_eq] rests on, so the witness cannot carry information: these two
    lemmas lift the equality of the values to the equality of the lists, and
    everything they are applied to below is still closed by computation. *)
Local Lemma bv_list_eq : forall (n : N) (l1 l2 : list (bv n)),
  map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  intros n l1. induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H;
    try discriminate H; [reflexivity|].
  injection H as Hhd Htl.
  f_equal; [exact (proj2 (bv_eq n x y) Hhd) | exact (IH l2 Htl)].
Qed.

Local Lemma bv_pair_list_eq : forall (n : N) (l1 l2 : list (bv n * bv n)),
  map (fun p => (bv_unsigned (fst p), bv_unsigned (snd p))) l1
  = map (fun p => (bv_unsigned (fst p), bv_unsigned (snd p))) l2 -> l1 = l2.
Proof.
  intros n l1. induction l1 as [|[a b] l1 IH]; intros [|[c d] l2] H; cbn in H;
    try discriminate H; [reflexivity|].
  injection H as Hfst Hsnd Htl.
  f_equal;
    [f_equal; [exact (proj2 (bv_eq n a c) Hfst) | exact (proj2 (bv_eq n b d) Hsnd)]
    | exact (IH l2 Htl)].
Qed.

{lemmas}'''

POSITIVE = '''(** ** The three lemmas

    THE START STATE IS ONE LINUX GIVES.  [Run.valid_launch_base] is an
    existential over the page draw [arch_mmap_rnd] (mm/util.c) made, so
    the proof names it; everything else is computation.

{r_note} *)
Lemma launch_ok : entry_launch_ok_va {va} rec_entry rec_input.
Proof.
  unfold rec_entry. cbn [entry_launch_ok_va].
  split; [|split].
  - unfold valid_stack_top_va. repeat split; vm_compute; congruence.
  - unfold valid_launch_sp. repeat split; vm_compute; congruence.
  - exists {r}. split; [lia|].
    split; [{aslr_true_arm}|].
    split; [{aslr_false_arm}|].
    vm_compute. reflexivity.
Qed.

(** THE BLOCK IS THE KERNEL'S, BYTE FOR BYTE.  Nothing is excluded. *)
Lemma block_ok :
  entry_stack_image rec_input rec_mbase rec_phdr rec_img_entry rec_sp rec_draw
  = rec_stack_bytes.
Proof. apply bv_list_eq. vm_compute. reflexivity. Qed.

(** AND THE VECTOR IS THE KERNEL'S.  The two addresses the vector carries —
    AT_RANDOM and AT_EXECFN — are the model's own [at_random_ptr] and
    [at_execfn_ptr], not the recorded values. *)
Lemma auxv_ok :
  auxv_entries (launch_auxv rec_input rec_mbase) rec_phdr rec_img_entry
    (in_uid rec_input) (in_gid rec_input) (in_hwcap rec_input)
    (at_random_ptr rec_sp (kb_rseq rec_kernel) (in_argv rec_input)
       (in_envp rec_input))
    (at_execfn_ptr rec_top (in_execfn rec_input))
  = rec_auxv.
Proof. apply bv_pair_list_eq. vm_compute. reflexivity. Qed.
'''

NEGATIVE = '''(** ** THE NEGATIVE CONTROL

    [rec_stack_bytes] above is NOT what the kernel wrote: byte {perturb} of
    the recorded block, which the kernel left at {perturb_was}, is {perturb_now}
    here.  Everything else is the record.  So the model must REFUSE this
    block, and this file compiles only if it does.

    Without this file a [block_ok] that had stopped computing anything —
    a model whose block collapsed to the term it is compared with, a proof
    that closed by assumption — would still be green.  Its admitted
    neighbour is {sibling}, the same record with the byte the kernel
    wrote. *)
Lemma block_differs :
  entry_stack_image rec_input rec_mbase rec_phdr rec_img_entry rec_sp rec_draw
  <> rec_stack_bytes.
Proof.
  intro H. apply (f_equal (map bv_unsigned)) in H. vm_compute in H.
  discriminate H.
Qed.
'''


def emit(f, module, r, base_at_zero):
    leaves = f["leaves"]
    names = f["leaf_names"]
    reported = [k for k in ("l1i", "l1d", "l2", "l3") if names[k]]
    if reported:
        cache_note = ", ".join("%s from %s" % (k.upper(), names[k])
                               for k in reported)
    else:
        cache_note = ("the boot reported no cache node, so every "
                      "AT_L*_CACHE* word is zero")
    if f["aslr"]:
        r_note = ("this launch randomized, and the base %#x is %d page(s) "
                  "below %#x, the base of the same build with no draw, so "
                  "the draw was %d, which vm.mmap_rnd_bits %d admits."
                  % (f["mbase"], r, base_at_zero, r, f["rnd_bits"]))
        aslr_true_arm = "intros _; vm_compute; congruence"
        aslr_false_arm = "intros Hc; vm_compute in Hc; discriminate Hc"
    else:
        r_note = ("this launch did not randomize, so the draw was 0 and the "
                  "base is Run.mmap_base_of with no draw, %#x."
                  % base_at_zero)
        aslr_true_arm = "intros Hc; vm_compute in Hc; discriminate Hc"
        aslr_false_arm = "intros _; reflexivity"

    if f["hwcap"] == 0x112D:
        hwcap_note = "AT_HWCAP %#x is StackLayout.hwcap_rv64gc" % f["hwcap"]
    elif f["hwcap"] == 0x20112D:
        hwcap_note = "AT_HWCAP %#x is StackLayout.hwcap_rv64gcv" % f["hwcap"]
    else:
        hwcap_note = ("AT_HWCAP %#x is neither of the two masks "
                      "Run.valid_hwcap admits" % f["hwcap"])

    if f["vlenb"]:
        vlenb_note = (", which State.launch_vlenb decodes as the recorded "
                      "vlenb of %d" % f["vlenb"])
    else:
        vlenb_note = (", the no-vector-unit value: AT_HWCAP carries no V bit, "
                      "so the probe read no VLENB CSR and AT_MINSIGSTKSZ is "
                      "State.rt_sigframe_size rounded up")
    guard_note = ("names no stack_guard_gap, so it is the boot default of "
                  "256 pages"
                  if "stack_guard_gap=" not in f["cmdline"]
                  else "names stack_guard_gap=%d" % f["guard"])
    norandmaps_note = (" and the boot command line carries norandmaps"
                       if "norandmaps" in f["cmdline"] else "")

    if f["elf_source"]:
        phdr_src = "the probe's own ELF header says it is"
        phdr_note = (
            "WHAT IS FED IN RATHER THAN CHECKED.  Nothing of the block and "
            "nothing of the vector.  [rec_phdr] and [rec_img_entry] are the "
            "probe's OWN ELF header, which the record carries under \"elf\" "
            "(probe.c, read_elf_facts: e_phoff over the image base, "
            "e_phentsize, e_phnum and e_entry, read out of the mapped "
            "image), so AT_PHDR, AT_PHENT, AT_PHNUM and AT_ENTRY are the "
            "kernel's copy of the header checked against the header.")
    else:
        phdr_src = "the recorded vector publishes it"
        phdr_note = (
            "WHAT IS FED IN RATHER THAN CHECKED.  This record predates the "
            "\"elf\" key of probe.c, so AT_PHDR, AT_PHENT, AT_PHNUM and "
            "AT_ENTRY -- four of the vector's %d entries -- come from the "
            "recorded vector itself and are [rec_phdr] and [rec_img_entry] "
            "below; those four entries of [auxv_ok] say nothing.  The other "
            "%d, and every byte of [block_ok] outside the four eight-byte "
            "value slots they fill, are the model's.  Re-capture the record "
            "with a probe that writes \"elf\" and the four become a check."
            % (len(f["auxv"]), len(f["auxv"]) - 4))

    record_note = para(
        "THE RECORD.  %s under %s, %s, boot command line \"%s\".  The probe "
        "ran as the \"%s\" launch: argc %d, envc %d, exec file name \"%s\" "
        "of %d byte(s).  The kernel put the stack end at %#x and the entry "
        "stack pointer at %#x, so the block is %d bytes; the break was %#x, "
        "the mmap base, which is the end of the vDSO pair, %#x, the vDSO "
        "text %d page(s) at %#x and the vvar mapping at %#x."
        % (header_value(f["header"], "kernel"),
           header_value(f["header"], "qemu"),
           header_value(f["header"], "machine"), f["cmdline"], f["run"],
           len(f["argv"]), len(f["envp"]), f["execfn"].decode("latin1"),
           len(f["execfn"]), f["top"], f["sp"], len(f["stack_bytes"]),
           f["brk0"], f["mbase"], f["text_pages"], f["vdso_lo"],
           f["vvar_start"]))

    facts_note = para(
        "[kb_vdso] is %d, which [State.vdso_text_pages] decodes as %d "
        "page(s), the size of the [vdso] mapping.  [kb_guard] is the "
        "[stack_guard_gap] boot parameter in pages "
        "([cmdline_parse_stack_guard_gap], mm/mmap.c; this boot %s).  "
        "[kb_rnd_bits] is %d, which [State.mmap_rnd_bits] decodes as "
        "[vm.mmap_rnd_bits] = %d.  [kb_aslr] is %s: the boot read "
        "[randomize_va_space] = %d%s.  [kb_vlenb] is %d%s.  The four cache "
        "leaves are the devicetree's (%s), read the way [cache_of_set_props] "
        "(drivers/base/cacheinfo.c) reads them, with the SET count in "
        "[cl_assoc] as [State.cache_ways] expects."
        % (f["text_pages"] - 1, f["text_pages"], guard_note,
           f["rnd_bits"] - 18, f["rnd_bits"],
           "true" if f["aslr"] else "false", f["rva"], norandmaps_note,
           f["kb_vlenb"], vlenb_note, cache_note))


    if f["perturb"] is None:
        title = "a real kernel's start state, against the entry model"
        checked_note = para(
            "WHAT IS CHECKED.  [launch_ok] is [Run.entry_launch_ok_va]: the "
            "recorded stack end, stack pointer and mmap base are a start "
            "state a Linux v6.18.46 (commit 1f99e9ab748f) launch can give, "
            "under the recorded launch facts.  [block_ok] is the heart of "
            "it: [Run.entry_stack_image], the MODEL'S block, computed here "
            "by Rocq from the model's own source, equals the %d bytes the "
            "kernel wrote, every byte of them.  The sixteen AT_RANDOM bytes "
            "are not excluded: they are the record's, carried in "
            "[ed_random] of the draw, where [StackLayout.build_stack_bytes] "
            "reads them.  [auxv_ok] is [StackLayout.auxv_entries] against "
            "the vector decoded from the recorded /proc/self/auxv."
            % len(f["stack_bytes"]))
        lemmas = POSITIVE.format(
            va=f["va"], r=r, r_note=para(r_note),
            aslr_true_arm=aslr_true_arm, aslr_false_arm=aslr_false_arm)
    else:
        k, was, now = f["perturb"], f["perturb_was"], f["stack_bytes"][f["perturb"]]
        title = "A NEGATIVE CONTROL: a start state no kernel wrote"
        checked_note = para(
            "WHAT IS CHECKED.  That the model REFUSES a block that is not "
            "Linux's.  One byte of the recorded block is moved, and the "
            "file compiles only if [Run.entry_stack_image] disagrees with "
            "it.  The admitted neighbour is %s, the same record with the "
            "byte the kernel wrote; a checker change has to keep both, and "
            "a [block_ok] that had stopped computing would keep only the "
            "first." % f["sibling"])
        lemmas = NEGATIVE.format(perturb=k, perturb_was=was, perturb_now=now,
                                 sibling=f["sibling"])
    return HEADER.format(
        module=module,
        title=title,
        log=f["log"],
        sha256=f["sha256"],
        record_note=record_note,
        checked_note=checked_note,
        facts_note=facts_note,
        block_len=len(f["stack_bytes"]),
        auxv_count=len(f["auxv"]),
        thp="true" if f["thp"] else "false",
        kb_vdso=f["text_pages"] - 1,
        aslr="true" if f["aslr"] else "false",
        guard=f["guard"],
        kb_rnd_bits=f["rnd_bits"] - 18,
        rseq="true" if f["rseq"] else "false",
        kb_vlenb=f["kb_vlenb"],
        l1i=leaf_term(leaves[0]), l1d=leaf_term(leaves[1]),
        l2=leaf_term(leaves[2]), l3=leaf_term(leaves[3]),
        argv=string_list(f["argv"], 2),
        envp=string_list(f["envp"], 2),
        execfn="[" + "; ".join(str(b) for b in f["execfn"]) + "]",
        uid=f["uid"], gid=f["gid"], hwcap=f["hwcap"],
        hwcap_note=para(hwcap_note),
        va=f["va"],
        phdr_addr=f["phdr"][0], phdr_ent=f["phdr"][1], phdr_num=f["phdr"][2],
        img_entry=f["img_entry"],
        phdr_src=phdr_src, phdr_note=para(phdr_note),
        sp=f["sp"], brk0=f["brk0"], mbase=f["mbase"], top=f["top"],
        random=int.from_bytes(f["random16"], "little"),
        random_off=f["random_off"],
        bytes=byte_list(f["stack_bytes"], 2),
        auxvl=auxv_list(f["auxv"], 2),
        lemmas=lemmas,
    )


# ------------------------------------------------------------------ main -----


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("log")
    ap.add_argument("--out", required=True)
    ap.add_argument("--name", default=None, help="the module name to write")
    ap.add_argument("--va", default="Sv48", choices=sorted(VA_STACK_TOP))
    ap.add_argument("--perturb-byte", type=int, default=None,
                    help="move this byte of the recorded block by one and "
                         "emit the negative control: the model must refuse "
                         "the block")
    ap.add_argument("--sibling", default=None,
                    help="the admitted neighbour's module name, for the "
                         "negative control's comment")
    args = ap.parse_args(argv)

    try:
        header, obj = read_record(args.log)
        f = facts(args.log, header, obj, args.va)
        r, base_at_zero = mmap_draw_witness(f)
        f["perturb"] = args.perturb_byte
        f["sibling"] = args.sibling or "the unperturbed file of this record"
        if args.perturb_byte is not None:
            if not 0 <= args.perturb_byte < len(f["stack_bytes"]):
                raise LogError(
                    f"{args.log}: --perturb-byte {args.perturb_byte} names "
                    f"no byte; the block is {len(f['stack_bytes'])} bytes")
            bs = bytearray(f["stack_bytes"])
            f["perturb_was"] = bs[args.perturb_byte]
            bs[args.perturb_byte] = (bs[args.perturb_byte] + 1) % 256
            f["stack_bytes"] = bytes(bs)
    except LogError as exc:
        print(f"start_state_to_rocq.py: {exc}", file=sys.stderr)
        return 2

    module = args.name or pathlib.Path(args.out).stem
    pathlib.Path(args.out).write_text(emit(f, module, r, base_at_zero))
    print(f"{args.out}: {len(f['stack_bytes'])} block bytes, "
          f"{len(f['auxv'])} auxv entries, mmap draw {r}, "
          f"vdso text {f['text_pages']} page(s)"
          + ("" if args.perturb_byte is None
             else f", byte {args.perturb_byte} moved: NEGATIVE"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
