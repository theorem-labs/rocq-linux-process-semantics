#!/usr/bin/env python3
"""log_to_rocq.py — turn a placement conformance log into a Rocq replay.

A log is what tools/placement_conformance/probe.c wrote on a real kernel (or
under qemu-user).  This turns it into a Rocq file that builds the launch state
the log describes and walks every call of the log through the LPS checker
(Checks.ExecutableSpecs.check_syscall), demanding CheckOk at each step.  The
lemma is closed by computation, so the file compiles exactly when LPS places
every one of those mappings where the kernel placed it.

    log_to_rocq.py LOG --out F.v --kb-thp {0,1} [--expect-base ADDR]
                       [--expect {ok,reject}] [--perturb K] [--name NAME]

  --kb-thp         was the kernel built with CONFIG_TRANSPARENT_HUGEPAGE?  It
                   is a property of the kernel the log came from, which no
                   line of the log reports, so the caller states it.
  --expect-base    fail unless the mmap base the log shows is this address.
                   Under "norandmaps" Linux's base is STACK_TOP - MIN_GAP
                   (2^47 - 128 MiB = 0x7ffff8000000; Linux v6.18.46,
                   mm/util.c, mmap_base), and the base the log shows is the
                   top of the vDSO pair: so the check passes only if the
                   first search of the run was the vDSO pair's.
  --expect reject  emit "replay … = false" instead of "= true": what the
                   qemu-user log is for.  QEMU user mode places a mapping
                   where its own allocator puts it, so LPS must refuse it.
  --perturb K      move the return value of call K (0-based, over the call
                   lines of the log) by --perturb-pages pages.  A replay of a
                   perturbed log must fail; that is the check that the replay
                   has teeth.

THE LAUNCH STATE comes from the log's first line:

  * the reserved ledger is every mapping of /proc/self/maps except the stack,
    the heap and the vDSO pair: the probe's own image.  The pair is NOT put in
    the list, because State.init_model appends it itself from the kernel build
    (State.vdso_reserved);
  * the mmap base is the TOP of the vDSO pair, which is where Linux put the
    pair: __setup_additional_pages asks get_unmapped_area for the whole pair
    before anything else is mapped below the base (Linux v6.18.46,
    fs/binfmt_elf.c, ARCH_SETUP_ADDITIONAL_PAGES; arch/riscv/kernel/vdso.c);
  * the vDSO text size is the [vdso] mapping's size, as 1 + (n mod 16) pages
    (State.vdso_text_pages);
  * the stack pointer is field 28 of /proc/self/stat (mm->start_stack), and
    the break is what brk(0) answered.

THE EFFECTS are what Linux did, written in the model's vocabulary:

  * an anonymous PROT_NONE grant unmaps its range, a readable or writable one
    zero-fills it (State.SyscallEffect, and the worked cases in
    Checks/Cases/Mm/Mmap.v);
  * munmap unmaps the range it was given;
  * an mremap grow in place zero-fills the new tail; a move zero-fills the new
    tail, unmaps the old range and copies the old bytes to the new address; a
    shrink unmaps the tail;
  * a brk grow zero-fills the pages it adds, a shrink unmaps the pages it
    frees;
  * a failing call has the errno as its return value and does nothing.

Every number in a log line is the 64-bit register value as a signed decimal,
so each is taken modulo 2^64 here.
"""

import argparse
import json
import pathlib
import sys

PAGE = 4096
TWO64 = 1 << 64
VVAR_PAGES = 4  # VDSO_NR_PAGES == __VDSO_PAGES == 4 (arch/riscv/include/asm/vdso.h)
SOURCE_ALLOC_LIMIT = 0x400000000  # State.source_alloc_limit, 16 GiB

SYS_BRK, SYS_MUNMAP, SYS_MREMAP, SYS_MMAP = 214, 215, 216, 222

PROT_NONE = 0
MAP_FIXED_NOREPLACE = 0x100000

# The maps lines that are not the image: the model derives them itself.
NOT_IMAGE = ("[stack]", "[vvar]", "[vvar_vclock]", "[vdso]", "[heap]", "[vsyscall]")


def u64(v):
    return v % TWO64


def page_up(n):
    return (n + PAGE - 1) // PAGE * PAGE


def page_down(n):
    return n // PAGE * PAGE


class LogError(Exception):
    pass


# ----------------------------------------------------------------- reading --


def read_log(path):
    launch, calls = None, []
    for line in pathlib.Path(path).read_text().splitlines():
        if not line.startswith("{"):
            continue
        try:
            rec = json.loads(line)
        except json.JSONDecodeError as exc:
            raise LogError(f"{path}: cannot read a line: {exc}") from exc
        if "maps" in rec:
            if launch is not None:
                raise LogError(f"{path}: two launch lines")
            launch = rec
        elif "sysno" in rec:
            calls.append(rec)
        else:
            raise LogError(f"{path}: a line is neither a launch nor a call")
    if launch is None:
        raise LogError(f"{path}: no launch line")
    if not calls:
        raise LogError(f"{path}: no calls")
    return launch, calls


def parse_maps(text):
    """[(lo, hi, perms, name)] of /proc/self/maps."""
    out = []
    for line in text.splitlines():
        if not line.strip():
            continue
        head, _, rest = line.partition(" ")
        lo, _, hi = head.partition("-")
        fields = rest.split(None, 4)
        name = fields[4].strip() if len(fields) > 4 else ""
        out.append((int(lo, 16), int(hi, 16), fields[0], name))
    return out


def named(maps, name):
    for lo, hi, _perms, nm in maps:
        if nm == name:
            return lo, hi
    return None


def launch_state(launch, log_name):
    maps = parse_maps(launch["maps"])
    vdso = named(maps, "[vdso]")
    if vdso is None:
        raise LogError(f"{log_name}: no [vdso] mapping in the launch line")
    vvar = named(maps, "[vvar]")
    text_pages = (vdso[1] - vdso[0]) // PAGE
    if not 1 <= text_pages <= 16:
        raise LogError(
            f"{log_name}: the vDSO text is {text_pages} pages; the model holds 1 to 16"
        )
    notes = []
    if vvar is None:
        # qemu-user maps no vvar.  The model reserves four pages below the
        # text all the same, which is one of the ways qemu-user is not Linux.
        notes.append("the log has no [vvar] mapping, so the four vvar pages "
                     "below the text are the model's, not the log's")
    else:
        if vvar[1] != vdso[0]:
            notes.append(f"the vvar mapping ends at {vvar[1]:#x} and the text "
                         f"starts at {vdso[0]:#x}: the pair is not contiguous")
        if (vvar[1] - vvar[0]) // PAGE != VVAR_PAGES:
            notes.append(f"the vvar mapping is {(vvar[1] - vvar[0]) // PAGE} "
                         f"pages, not {VVAR_PAGES}")
    reserved = [(lo, hi - lo) for lo, hi, _p, nm in maps if nm not in NOT_IMAGE]
    return {
        "reserved": reserved,
        "mbase": vdso[1],
        "vvar_lo": vvar[0] if vvar else vdso[0] - VVAR_PAGES * PAGE,
        "text_pages": text_pages,
        "sp": int(launch["startstack"]),
        "brk0": int(launch["brk0"]),
        "mmu": launch.get("mmu", ""),
        "dac_mmap_min_addr": launch.get("dac_mmap_min_addr"),
        "notes": notes,
    }


# ------------------------------------------------------------------ Rocq -----


def w(v):
    """A 64-bit word literal."""
    return f"Z_to_bv 64 {u64(v):#x}"


def ret_word(ret):
    if -4095 <= ret < 0:
        return f"errno_ret {-ret}"
    return w(ret)


def pairs(items):
    return "[" + "; ".join(f"({w(a)}, {w(n)})" for a, n in items) + "]"


def copies(items):
    return ("[" + "; ".join(f"mkCopy ({w(s)}) ({w(d)}) ({w(n)})"
                            for s, d, n in items) + "]")


def effect(ret, zeros, unmaps, cps):
    return (f"mkEffectU ({ret_word(ret)}) [] {pairs(zeros)} {pairs(unmaps)} "
            f"{copies(cps)} []")


def step_input(sysno, args):
    cells = "; ".join(w(a) for a in args)
    return f"mkInput ({w(sysno)}) [{cells}] (fun _ => None) (fun _ => None)"


def build_steps(calls, brk0, log_name):
    """[(input, effect, comment)], in the order the probe called them."""
    steps, brk = [], brk0
    for k, call in enumerate(calls):
        sysno = call["sysno"]
        args = [u64(a) for a in call["args"]]
        while len(args) < 6:
            args.append(0)
        ret = int(call["ret"])
        failed = -4095 <= ret < 0
        zeros, unmaps, cps, note = [], [], [], ""
        if sysno == SYS_MMAP:
            addr, length, prot, flags = args[0], args[1], args[2], args[3]
            if failed:
                note = "refused"
            else:
                n = page_up(length)
                if prot == PROT_NONE:
                    unmaps = [(ret, n)]
                else:
                    zeros = [(ret, n)]
                note = "PROT_NONE grant" if prot == PROT_NONE else "grant"
            if flags & MAP_FIXED_NOREPLACE:
                note += ", MAP_FIXED_NOREPLACE"
            if addr:
                note += f", hint {addr:#x}"
        elif sysno == SYS_MUNMAP:
            if not failed:
                unmaps = [(args[0], page_up(args[1]))]
            note = "munmap" if not failed else "munmap refused"
        elif sysno == SYS_MREMAP:
            old, old_n, new_n = args[0], page_up(args[1]), page_up(args[2])
            if failed:
                note = "mremap refused"
            elif new_n > old_n:
                if ret == old:
                    zeros = [(old + old_n, new_n - old_n)]
                    note = "mremap grew in place"
                else:
                    zeros = [(ret + old_n, new_n - old_n)]
                    unmaps = [(old, old_n)]
                    cps = [(old, ret, old_n)]
                    note = "mremap moved"
            elif new_n < old_n:
                unmaps = [(old + new_n, old_n - new_n)]
                note = "mremap shrank"
            else:
                note = "mremap kept its size"
        elif sysno == SYS_BRK:
            want = args[0]
            if ret == want and want != brk:
                if page_up(want) > page_up(brk):
                    zeros = [(page_up(brk), page_up(want) - page_up(brk))]
                elif page_up(want) < page_up(brk):
                    unmaps = [(page_up(want), page_up(brk) - page_up(want))]
                note = "brk moved"
                brk = want
            else:
                note = "brk unchanged"
        else:
            raise LogError(f"{log_name}: call {k} has sysno {sysno}, "
                           "which this harness does not write")
        steps.append((step_input(sysno, args), effect(ret, zeros, unmaps, cps),
                      f"{k}: {note}, ret {u64(ret):#x}"))
    return steps


HEADER = """(** * {module} — a real kernel's placements, replayed through the checker

    GENERATED by tools/placement_conformance/log_to_rocq.py from
    {log}.  Do not edit: change the log or the generator.

    {provenance}

    Every call the probe made on that kernel is walked through
    [Checks.ExecutableSpecs.check_syscall] from the launch state the log
    reports, and every step must answer [CheckOk].  So this file compiles
    exactly when LPS places each of those mappings where the kernel placed
    it.  See tools/placement_conformance/README.md. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
Import ListNotations.
Open Scope bv_scope.

(** The kernel build the log came from.  Two fields are MEASURED from
    this boot: whether it was built with CONFIG_TRANSPARENT_HUGEPAGE,
    and the size of its vDSO text ({text_pages} page(s), so [kb_vdso]
    is {kb_vdso_text}).  [kb_aslr] is the boot's own: false under
    `norandmaps`, true otherwise.

    The remaining five are [State.default_kernel]'s, and the replay
    does not depend on them: [Sys/Mm/Mmap.linux_place] reads [kb_thp],
    and [State.vdso_reserved] reads [kb_vdso], and nothing in a
    placement reads the guard gap, the randomisation width, rseq, the
    vector length or the cache words.  A start-state replay does read
    them, and that is what tools/placement_conformance's start-state
    rules are for. *)
Definition replay_kernel : KernelBuild :=
  mkKernelBuild {thp} {kb_vdso_text}%N {kb_aslr}
    (kb_guard default_kernel) (kb_rnd_bits default_kernel)
    (kb_rseq default_kernel) (kb_vlenb default_kernel)
    (kb_cache default_kernel).

(** The launch.  Nothing below reads the argument vector, the environment,
    the file system or the credentials, so they are empty or ordinary; the
    three fields that decide a placement — the reserved ledger, the mmap
    base and the stack pointer — are the log's. *)
Definition replay_input : ProcInput :=
  mkProcInput_full [] [] [] IEof (Z_to_bv 64 1000) (Z_to_bv 64 1000) []
    net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc false Sv48
    default_urandom [] replay_kernel default_execfn.

(** The probe's own image, as /proc/self/maps reported it.  The vDSO pair is
    not here: [init_model] appends it from [replay_kernel]. *)
Definition replay_reserved : list (word * word) :=
  {reserved}.

Definition replay_init : Model :=
  init_model replay_reserved ({brk0}) ({mbase}) ({sp})
    source_alloc_limit replay_input.

(** One pair per call of the log: what the probe asked, and what the kernel
    did.  The comment on each is its index in the log, what the call did, and
    the value the kernel returned. *)
Definition replay_steps : list (SyscallInput * SyscallEffect) :=
  [
{steps}
  ].

(** Walk the trace: [false] at the first step the checker does not accept. *)
Fixpoint replay (m : Model) (steps : list (SyscallInput * SyscallEffect))
    : bool :=
  match steps with
  | [] => true
  | (i, e) :: rest =>
      match check_syscall i e m with
      | CheckOk m' _ => replay m' rest
      | _ => false
      end
  end.
"""

OK_LEMMA = """
Lemma replay_ok : replay replay_init replay_steps = true.
Proof. vm_compute. reflexivity. Qed.
"""

REJECT_LEMMA = """
(** THE NEGATIVE.  The placements in this log are not Linux's, so the model
    must refuse one of them. *)
Lemma replay_rejected : replay replay_init replay_steps = false.
Proof. vm_compute. reflexivity. Qed.
"""


def emit(state, steps, module, log, expect, provenance):
    # A Rocq list separates its elements with ';'.  The ',' inside each
    # element is the pair of the call and its effect.
    body = ";\n".join(f"    (* {c} *)\n    ({i},\n     {e})"
                      for i, e, c in steps)
    reserved = ("[ " + ";\n    ".join(f"({w(a)}, {w(n)})"
                                      for a, n in state["reserved"]) + " ]"
                if state["reserved"] else "[]")
    text = HEADER.format(
        module=module,
        log=log,
        provenance=provenance,
        text_pages=state["text_pages"],
        kb_vdso_text=state["text_pages"] - 1,
        thp="true" if state["thp"] else "false",
        kb_aslr="false" if "norandmaps" in str(log) else "true",
        reserved=reserved,
        brk0=w(state["brk0"]),
        mbase=w(state["mbase"]),
        sp=w(state["sp"]),
        steps=body,
    )
    return text + (OK_LEMMA if expect == "ok" else REJECT_LEMMA)


# ------------------------------------------------------------------ main -----


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("log")
    ap.add_argument("--out", required=True)
    ap.add_argument("--kb-thp", type=int, choices=(0, 1), required=True)
    ap.add_argument("--expect-base", default=None,
                    help="fail unless the log's mmap base is this address")
    ap.add_argument("--expect", choices=("ok", "reject"), default="ok")
    ap.add_argument("--perturb", type=int, default=None,
                    help="move the return value of this call")
    ap.add_argument("--perturb-pages", type=int, default=1,
                    help="by this many pages, up or down (default 1)")
    ap.add_argument("--name", default=None, help="the module name to write")
    args = ap.parse_args(argv)

    try:
        launch, calls = read_log(args.log)
        state = launch_state(launch, args.log)
        state["thp"] = bool(args.kb_thp)

        if args.expect_base is not None:
            want = int(args.expect_base, 0)
            if state["mbase"] != want:
                print(f"log_to_rocq.py: {args.log}: the mmap base the log "
                      f"shows is {state['mbase']:#x}, not {want:#x}: the vDSO "
                      f"pair does not end at the base, so the pair was not "
                      f"the run's first search", file=sys.stderr)
                return 2
        if args.perturb is not None:
            if not 0 <= args.perturb < len(calls):
                print(f"log_to_rocq.py: --perturb {args.perturb} names no "
                      f"call; the log has {len(calls)}", file=sys.stderr)
                return 2
            calls[args.perturb] = dict(calls[args.perturb])
            calls[args.perturb]["ret"] = (int(calls[args.perturb]["ret"])
                                          + args.perturb_pages * PAGE)

        steps = build_steps(calls, state["brk0"], args.log)
    except LogError as exc:
        print(f"log_to_rocq.py: {exc}", file=sys.stderr)
        return 2

    module = args.name or pathlib.Path(args.out).stem
    provenance = (f"The kernel reported mmu {state['mmu']!r}; "
                  f"/proc/sys/vm/mmap_min_addr read "
                  f"{state['dac_mmap_min_addr']} (dac_mmap_min_addr only). "
                  f"The mmap base is {state['mbase']:#x}, the vvar mapping "
                  f"starts at {state['vvar_lo']:#x}, the stack pointer is "
                  f"{state['sp']:#x} and the break is {state['brk0']:#x}.")
    if args.perturb is not None:
        provenance += (f"  Call {args.perturb}'s return value has been moved "
                       f"{abs(args.perturb_pages)} page(s) "
                       f"{'up' if args.perturb_pages > 0 else 'down'}: this "
                       f"file is a negative control.")
    for note in state["notes"]:
        provenance += f"  NOTE: {note}."

    pathlib.Path(args.out).write_text(
        emit(state, steps, module, args.log, args.expect, provenance))
    print(f"{args.out}: {len(steps)} steps, base {state['mbase']:#x}, "
          f"vdso text {state['text_pages']} page(s), "
          f"expect {args.expect}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
