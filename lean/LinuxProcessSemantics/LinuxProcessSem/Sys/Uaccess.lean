import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Uaccess — the user-buffer boundary

Mirrors `theories/LinuxProcessSem/Sys/Uaccess.v`.  Every other file under
`Sys/` answers to one kernel SOURCE file; this one answers to kernel
HEADERS, and holds what the specs share rather than any one syscall's
behaviour.  The predicate it transcribes is `__access_ok`
(include/asm-generic/access_ok.h, `__access_ok`, at stable v6.18.46 /
1f99e9ab748f), which is the file `State.access_okb`'s note cites for the
same predicate.  The `access_ok` wrapping it is that header's `#ifndef
access_ok` fallback on most architectures, but NOT on riscv64: with
`CONFIG_RISCV_ISA_SUPM` (arch/riscv/Kconfig, `RISCV_ISA_SUPM`: `depends on
64BIT`, `default y`) the arch defines its own `#define access_ok(addr,
size) likely(__access_ok(untagged_addr(addr), size))`
(arch/riscv/include/asm/uaccess.h, `access_ok`, v6.18.46), whose
`untagged_addr` is the identity while the process's pointer-masking length
is zero — which it is on every `execve`, and stays so until
`prctl(PR_SET_TAGGED_ADDR_CTRL)` or a tracer sets it.  That argument, with
its citations, is on `State.access_okb` in theories/LinuxProcessSem/State.v;
the Lean `State.lean` does not carry it yet, and this file transcribes the
comparison alone.
include/linux/uaccess.h defines NEITHER of them — it pulls the arch header
in and only USES `access_ok` — in `_inline_copy_from_user` and
`_inline_copy_to_user`, which is where the copy helpers reach it
(`copy_from_user` and `copy_to_user` call `check_copy_size` and then one of
those two; on riscv through the out-of-line `_copy_from_user` and
`_copy_to_user` of lib/usercopy.c at v6.18.46, since
arch/riscv/include/asm/uaccess.h at that version defines neither
`INLINE_COPY_FROM_USER` nor `INLINE_COPY_TO_USER`), in
`copy_from_user_inatomic_nontemporal`, and in the fallback
`#define user_access_begin(ptr,len) access_ok(ptr, len)`
(include/linux/uaccess.h at v6.18.46) — so it is named here for the copy
helpers, not for the range test.  `State.copy_bytes_map`'s docstring
carries the same reading, naming both `_inline_*` helpers.

TRUST BOUNDARY: this file is part of the trusted specification.
`Specs.lean` holds the dispatcher; see that file's header for the
representation and fail-closed conventions every spec here follows.

Every definition keeps the Rocq name and shape.  Two spellings differ from
Rocq without changing a value: Rocq's `Z.leb` Bool tests are Lean's
decidable `≤` on `Int`, and Rocq's `negb` is `!`.  The docstrings carry
the kernel citation each decision rests on — file, function and version —
and the `rw_bytes_max` argument in full, verbatim from the Rocq definition
as the port ticket requires, with five of its citations completed by the
file and version beside the name and nothing else changed; the rest point
at the Rocq definition for the argument, so there is one place to correct
it. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall

/-- The argument below is the Rocq definition's, carried verbatim.  Its
extraction paragraphs describe the ROCQ checker — `Z.to_nat`, Peano `nat`,
the OCaml stack — which has no Lean counterpart yet; they are kept because
the constant's value is set by that argument and nowhere else, and the
numbers they refer to live in bugs/rw-bytes-max-ceiling.md and
bugs/extraction-stack-limit-unpinned.md, not here.
`tools/check_rw_bytes_max_mirrors.py` holds this literal, and every
harness copy of the value, to the Rocq constant: it reads
`theories/LinuxProcessSem/Sys/Uaccess.v` for the value and this line by the
`def rw_bytes_max : Int := <digits>` spelling its docstring names, and
exits non-zero on any disagreement (the `generated-docs` job runs it), so a
move of the Rocq constant fails there until this line and the probes
follow; `check_lean_spec_parity.py --drift --strict` (the lean-drift
workflow) reports the same move as drift of this twin's source.
`Checks.Cases.Uaccess.rw_bytes_max_is_2_17` is the tripwire against a local
edit of this line between runs of that tool.  What no tool compares is the
ARGUMENT below with the Rocq comment it was copied from: a re-read that
advances this file's `rocq-baseline` header owes that comparison by hand.

WHAT THIS CONSTANT STILL BOUNDS, after two issues took most of it
away: the hole a write or a growing `ftruncate` may open past
end-of-file (`ReadWrite.modeled_file_gap`,
`Open.modeled_truncate_gap`), the buffer a `getrandom` may name, and
the total a socket send may gather.  IT NO LONGER CAPS A TRANSFER'S
COUNT in either direction.  Reads outgrew it in issue #416 — their
recursion is capped by the file or the stream they read from — and
writes in issue #460, once `State.readable_bytes` stopped spending
stack depth and a length-sized unary numeral on the count a call
names.  A READ's count now faces the kernel's own two tests and
nothing else — `State.access_okb` on the range, then the
`MAX_RW_COUNT` clamp (`State.rw_count_clamp`).  A WRITE's faces
`modeled_rw_range` below, which is this constant OR that same range
test, and then the same clamp.

THE HOLE IS NOT THE COUNT, and that is why one survived and the
other did not.  A hole is the distance from the file's end to the
write's offset — bytes the model has to BUILD because it holds a
file as a flat byte list, where Linux leaves a sparse file's hole
costing nothing.  No per-call count bounds it: a one-byte write at a
far offset opens an arbitrarily large one.  A COUNT, by contrast,
now costs the model a chunk-count numeral 4096 times smaller than
itself and a list bounded by what is actually mapped.

THIS IS A MODELING BOUND, NOT A KERNEL ONE, and it is here because
the alternative is a crash.  Linux settles a huge scalar count in
three cheap steps and then does the transfer.  In `vfs_read` and
`vfs_write` (fs/read_write.c at v6.18.46), after the `FMODE_*`
tests and in this order:

- `if (unlikely(!access_ok(buf, count))) return -EFAULT;`;
- `rw_verify_area` (fs/read_write.c at v6.18.46), whose first statement is
  `if (unlikely((ssize_t) count < 0)) return -EINVAL;`;
- `if (count > MAX_RW_COUNT) count = MAX_RW_COUNT;`, with
  `#define MAX_RW_COUNT (INT_MAX & PAGE_MASK)` — 0x7ffff000 — in
  include/linux/fs.h (`MAX_RW_COUNT`, v6.18.46).

The first is `State.access_okb` and the third is
`State.rw_count_clamp`, and both are now what the read AND write
arms apply; none of the three bounds what the model can EVALUATE,
which is what this constant is for on the paths it still guards.
THE ORDER MATTERS for
one errno.  `access_ok` runs first, and on riscv64 it is the generic
`__access_ok` (include/asm-generic/access_ok.h, v6.18.46) with its limit
at `State.TASK_SIZE` = 2^47, so a
`count` that is negative as `ssize_t` — at least 2^63 — has already
been answered -EFAULT before `rw_verify_area`'s sign test is reached:
on a kernel with an MMU the -EINVAL is UNREACHABLE through the
read/write syscalls, and modeling the sign test would put -EINVAL
where Linux returns -EFAULT.  The MMU is doing the work in that
argument, so state it: `__access_ok` returns true without looking at
either operand when CONFIG_ALTERNATE_USER_ADDRESS_SPACE is set or
CONFIG_MMU is not, and a nommu riscv64 kernel reaches that same
generic `__access_ok` through asm-generic/uaccess.h.  On such a
kernel -EINVAL is what a negative `count` gets.  This model has
`mmap` and page permissions and so describes MMU kernels only.

So above the bound the model declines on the paths it still guards;
it does not invent an errno, and it does not clamp — a clamp would
have it report a short transfer where Linux transferred everything.

2^17 IS SET FROM BELOW BY A PROOF, NOT BY A PROGRAM, and the
distinction matters because it is the difference between "no slack
exists" and "no slack exists as currently written".  What that proof
now constrains is the theories/Common WRITE-NODE FAMILY rather than
the spec: `CatSim.buf_modeled` is still stated at this constant and
is what those lemmas hand `write_source_of_rw` to see the walk they
were written against.  That is a library convenience, not a bound
the spec has — a write past it is judged, it just has no ready-made
node in that family.

The chain is: a single argv string may be 131071 bytes
(`Run.valid_argv`, from Linux's `MAX_ARG_STRLEN` of 32 pages
(include/uapi/linux/binfmts.h, v6.18.46) less its NUL), and
`Examples.brk_rev_ns` writes argv[1] reversed followed by a newline.  `brk_rev_ns_source.bufs_modeled_out` discharges
`buf_modeled` for that write from `nN_le` — the 131071 cap — giving
131071 + 1 = 131072, the constant on the nose.  Lower the bound by
one and that lemma's `lia` fails, the write is `unmodeled`, and since
`unmodeled` puts a run in `Run.reaches_error` the example's
equivalence theorem stops being provable rather than merely weakening.
So the constant cannot be lowered without touching that proof.

WHAT IS NOT TRUE is that the program can perform such a write.  It
cannot: `brk_rev_ns`'s own source and target both return 3 for an
argument longer than 65536 bytes (source/program.c and
target/program.zig, the `n > 65536` guard), so the largest write it
can ever execute is 65537 bytes.  `bufs_modeled_out` sits in a
section where only `2 <= length av` is in scope and the program's own
cap is not, so it reaches for the argv bound instead of the tighter
one that is actually available; `alloc_join_ns_source` does the
tighter thing for its own buffer.  Threading the 65536 guard into the
section would let the constant go as low as 65537.  That is a real
option, deliberately not taken here: 2^17 is a rounder number to
explain and nothing needs the room, but the reason to keep it is
convenience, and it should not be recorded as a program requirement
it is not.

FROM ABOVE the constraint is real but soft, and NO SINGLE NUMBER
SHOULD BE QUOTED FOR IT.  The mechanism: `BvBase.word_to_nat` is
`Z.to_nat`, and Checks/Extraction.v imports ExtrOcamlZBigInt but not
ExtrOcamlNatInt, so `nat` stays genuine unary Peano and `Z.to_nat`
bottoms out in `Pos.to_nat = iter_op add`.  `iter_op`'s doubling keeps
the NUMBER of additions logarithmic, but Peano `add` is `S (add p m)`,
not tail-recursive, so the largest intermediate addition costs stack
depth proportional to the length.  The places below consult that
length, all but the last of them by recursing with it, and every one
of them before a single memory lookup, so what a caller sees when
one of them goes over is `Stack overflow` and exit 2 — or, on an
OCaml 4 native build, a bare SIGSEGV — a status no verdict maps to.
THEY DO NOT ALL GO OVER AT THE SAME DEPTH, and reading them as one
number is the mistake that sent the measurements in
bugs/rw-bytes-max-ceiling.md at `word_to_nat` alone.  Measured on
the OCaml 5 the opam file requires, at the same argument, that
conversion costs a thousandth of what `State.readable_bytes` costs.
The others are not measured.  The list, and which of them this
constant still stands in front of:

- `State.readable_bytes`, for a `write`, and `gather_prefix`, which
  calls it, for a `writev`.  NEITHER IS ON THE LIST ANY MORE: both
  were the reason the write count was bounded, and both got the
  chunked tail-recursive treatment described on `State.wmem_chunk`
  (issue #460).  What a write now converts to a unary numeral is the
  CHUNK COUNT, `count` over 4096; what it still pays is a list as
  long as the mapped prefix it actually reads, which is bounded by
  the process's memory rather than by the call;
- `Fs.file_write`'s `repeat` and `firstn`, for a write to a file.
  Only the `repeat` is sized by the HOLE, which is what
  `ReadWrite.modeled_file_gap` bounds.  The `firstn` is sized by the ABSOLUTE
  offset, so this bound does not bound it and cannot: it is capped
  by the file's own length, and a file's length is the cost this
  constant explicitly does not cover (see the last paragraph, and
  bugs/rw-bytes-max-ceiling.md).  An append to a long file pays it
  with a gap of zero;
- `Fs.file_truncate`'s `repeat` and `firstn`, for an `ftruncate`.
  Both are sized by the NEW LENGTH, and both are built from the one
  numeral `word_to_nat len`, which `Open.modeled_truncate_gap` bounds by
  the file's length plus this constant — one-sidedly, so in both
  directions.  That is the SAME exposure as `file_write` above, not
  a better one: the file's own length is still uncovered, so a
  shrink of a long file builds a numeral the size of that file with
  the gap negative;
- `State.read_bytes_map` over `buflen`, for a `getrandom` — which
  is why `Random.getrandom_spec` carries this same guard.  THIS ONE
  NO LONGER RECURSES WITH THE LENGTH: it was rewritten into the
  chunked tail-recursive accumulator described on
  `State.wmem_chunk`, so its depth no longer scales with `buflen`
  and the largest numeral it builds is the CHUNK COUNT, `buflen` over
  4096 rather than `buflen`; what it still pays is a list that long.
  The guard stays because that cost is real, and because the same
  number of bytes should be the same transfer whichever call names
  it — not because this path would crash.

A `read` IS ON NEITHER SIDE OF THAT LIST, and used to be listed
here by mistake: `Fs.file_read`'s numeral is
`word_to_nat_bounded count (length rest)` — capped at what is left
of the file BEFORE the conversion, the cap-and-prove-equal
technique described below — so a file read is charged for the file
it holds (the cost this constant explicitly does not cover, see
the last paragraph) and never for the `count` it names.  The
OFFSET does not cross into `nat` at all: `Fs.file_from` walks the
file in `Z` and in tail position.  A channel read consumes `count`
only through `Z` comparisons (`Syscall.w_is0`, and the
`length bs <= ...` side condition), and the prefix it delivers is
bounded by the input stream.  The follow-on walks of a delivering
read (`State.read_bytes_map` and `delivered_writes` over the
DELIVERED bytes, the checker's `wmem_ok`) are all sized by that
same file- or stream-bounded delivery.  That is why the file,
channel and directory read arms of `ReadWrite.read_spec` are not
guarded here: their guard is `State.access_okb` and nothing else,
with Linux's own `MAX_RW_COUNT` clamp (`State.rw_count_clamp`)
bounding what a delivery may claim.

ONE READ PATH DID RECURSE ON `count` ITSELF, and the sentence above
was wrong about it until issue #666: the PIPE read arm delivered
`firstn (word_to_nat count) q`, which builds the count as a unary
numeral before it looks at the queue, and consumed the queue with
the same numeral.  It was the only thing `modeled_rw_count` was
buying on that arm — a pipe delivers at most `PIPE_BUF`
(include/uapi/linux/limits.h, v6.18.46) bytes whatever the count — and
`State.pipe_take` removes it by taking the minimum
against the queue's own length in `Z` first.  The socket arm never
had the defect (`State.net_take_z` walks in `positive`) and carried
the guard only by inheritance.  Neither arm recurses on `count` now;
both carry `modeled_rw_range` instead, for the RANGE and not for the
size.

How deep the recursion may go before it dies is a property of the
OCAML MAJOR VERSION, and so of whichever runtime builds the checker,
rather than of this development.  The opam file pins that major
version (`ocaml >= "5.0"`) for exactly this reason, and pins nothing
else about the runtime.

BOTH DIRECTIONS WALK IN CHUNKS NOW, and what the ceiling costs is a
LIST rather than a stack.  `readable_bytes` is
`State.readable_bytes_chunks` over `State.readable_bytes_acc`: the
inner walk extends a reversed accumulator through a tail call, the
outer loop hands out at most `State.wmem_chunk` bytes of fuel at a
time, and one `rev_append` restores byte order.
`State.readable_bytes_eq` is the equation proofs go through, in the
shape `State.read_bytes_map_eq` set on the read side, and no
admitted behaviour changed.  The write side therefore has the shape
the read side's `State.read_bytes_map` already had — and it got it
for this reason: the treatment is what let issue #460 retire the
write and writev count gates.

WHAT THAT LEAVES, precisely.  The stack depth scales with `count` on
neither direction, and the largest unary numeral either builds is
the CHUNK COUNT, `count` over 4096.  What a transfer still pays per
byte is its OUTPUT LIST — one cons per mapped byte it actually reads
— which is bounded by the process's memory rather than by the call,
and which is the cost this constant explicitly does not cover (see
the last paragraph).  THE QUADRATIC THIS PARAGRAPH USED TO DESCRIBE
WAS A PROPERTY OF THE ONE-FRAME-PER-BYTE WALK and went with it: it
was a minor collection rescanning a stack one frame per byte deep,
and there is no such stack any more.

ONE PREREQUISITE OF THE THREE IS LEFT, and it is the cheapest.
`OCAMLRUNPARAM` is still not pinned wherever this repository invokes
the extracted checker, so the minor heap and the stack ceiling are
whatever the invoking shell leaves them.  The other two are done:
the harness's own linear memory scan was the second (`mem_fun`
builds its table once per capture), and the rewrite above was the
third.  bugs/rw-bytes-max-ceiling.md numbers all three and records
which one is still unowned.  None of them is a semantic question.

The measurements are properties of the toolchain rather than of
this specification.  bugs/rw-bytes-max-ceiling.md and
bugs/extraction-stack-limit-unpinned.md record them, with the
numbers; this comment deliberately does not repeat them, because two
copies of a measurement is one copy that will drift.

THE BOUND WAS REACHED BY A REAL PROGRAM, AND NO LONGER DECLINES IT.
A survey of the target corpus found a single `write` in sbase's
`paste` an order of magnitude past this constant (the size, and what
the survey was, are in bugs/rw-bytes-max-ceiling.md).  THAT WRITE IS
JUDGED NOW: after issues #460 and #666 no arm asks about a
transfer's SIZE at all.  What the transfer arms that still gate a
range carry is `modeled_rw_range`, which admits any count at a
buffer inside the address space, and every other transfer arm asks
`access_ok` and nothing else.  So the paragraph ABOVE about
`brk_rev_ns` — that no modeled example performs such a write — is a
statement about the examples in this tree and not about programs,
and what stands between that program and a run is COST rather than a
modeled decline.  Priority 1 was never at stake, since a decline is
explicit and fails closed; priority 3 is no longer at stake for the
count.  What this constant still declines is the past-end-of-file
HOLE, `getrandom`'s buffer and the socket sends — none of which that
survey measured.
THE PROOF SIDE HAS THE ROOM: nothing in this tree bounds the
constant from above any more — the walk cap a raise used to meet
first, `access_ok_walk_max`, went with the address-space bracket
(`State.access_okb` is the range test now and walks nothing) — so a
raise meets only the proofs that assume a count under it, the
`Hcnt`-shaped hypotheses in theories/Common; the entry below records
what the old cap's two builds showed.  So the numeral is the cheap
half, and moving it alone is the misleading move: it would widen what
the spec admits while leaving the one unowned prerequisite unbuilt,
and the first thing anyone would notice is a conformance run that
stopped finishing.

WHY A SEMANTIC BOUND AND NOT A REPRESENTATION FIX.  The cheaper
technique is to CAP the numeral and prove the capped definition equal
to the uncapped one, which narrows nothing and adds no premise.  This
file uses it where it applies — `Fs.file_from` and
`Fs.file_read_unguarded` are exactly that.  It does not apply to
`State.readable_bytes`, for a reason worth stating so nobody retries
it: the technique spends a bound you already have, and here there is
none.  `readable_bytes` walks `mp : word -> option byte`, a bare
function; the cap it would need is the length of the mapped run at
the address, which is not definable from a function with no
computable support.  `Fs.file_read` was capped by `length data`
because its output was already bounded by a byte list the model
holds — whereas `readable_bytes`'s numeral bounds its OWN output,
which is `count` bytes long precisely when the bytes are mapped.

And the obstruction survives the obvious repair.  Even if memory were
re-represented as a finite interval structure, the smallest run the
model structurally guarantees is the 8 MiB zero-mapped stack every
run has (`Run.init_machine_state`), and an anonymous grant may be
`State.target_alloc_limit` — 512 GiB.  A correct cap is not a small
cap: 8 MiB is 64x this constant and was already past the depth the
extraction was measured to die at.

WHICH IS WHY THE REPAIR THAT LANDED WAS NEITHER OF THESE.  Capping
could not bound `readable_bytes`'s walk and re-representing memory
could not either, so issue #460 changed the walk's SHAPE instead —
chunked and tail-recursive, as the ceiling paragraphs above describe
— and that needed no bound at all.  This paragraph and the one
before it are kept because the argument still holds of anything that
would try to CAP a walk over a bare `mp`, which is a thing nobody
should retry; they no longer say that the write direction must
therefore ship a semantic size bound, because it does not ship
one.

COST TO THE THEOREM: a source and a target that diverge only on a
write or a growing `ftruncate` opening a larger hole past
end-of-file than `rw_bytes_max`, or on a `getrandom` or a socket
send naming more than it, are not distinguished by
`Equivalence.strong_universal_T`.  A write naming more than
`rw_bytes_max` BYTES was on that list until #460 and #666 and is not
on it any more.  The narrowing is one-sided, so it
admits nothing unsound: a TARGET that performs such a call reaches
`Run.reaches_error` and is rejected outright.

NOT covered here, and deliberately: the cost of every path below
still scales with the length of the file the model is holding, since
that file IS a byte list — `Fs.file_write` walks it on every write —
and a run GROWS that file itself, a chain of writes each opening a
legal hole reaching any length.  So this is not only about
`Fs.valid_fs`'s initial images, and bounding those would not close it;
bounding it at all changes what the theorem quantifies over rather
than what a syscall admits.

THE BOUND THEREFORE DOES NOT CLOSE ITS OWN CLASS, and that should be
read as a limit rather than as a claim.  It bounds ONE syscall, and
the quantity that drives the recursion is reachable by ITERATION: a
loop of `lseek(fd, off += rw_bytes_max, SEEK_SET); write(fd, b, 1)`
performs only writes this spec judges — each names one byte and opens
a hole of exactly `rw_bytes_max`, so `modeled_rw_range` and
`ReadWrite.modeled_file_gap` both hold at every step — yet after 2048 turns the
file is 2^28 bytes long, which is the depth the extraction is
measured to die at.  Nothing here rejects that run; each step is a
legal transfer, and it is the accumulated LENGTH, which no per-call
guard sees, that does the damage.  What this constant buys is that a
SINGLE syscall cannot do it — the crash costs a program 2048 calls
instead of one, and is no longer reachable by accident.  Closing the
class needs a bound on the state, not on the call, and that is the
change to what the theorem quantifies over described above. -/
def rw_bytes_max : Int := 131072

/-- `count` is a transfer size the model will judge.  This is the gate
`getrandom` and the socket sends still carry, and the shape the hole
guards are written in.

A Lean transfer arm that still gates a count uses `modeled_rw_range`
below, and every other transfer arm carries no count gate at all.  Which
Rocq arms those are is the argument on `modeled_rw_count` in
`theories/LinuxProcessSem/Sys/Uaccess.v`, and the rule is enforced over
the Rocq tree alone: `tools/check_write_arm_count_rule.py` reads
`theories/LinuxProcessSem/Sys/Fs/ReadWrite.v` and no Lean file, so a ported
read or write arm is held to it by review until that tool learns the Lean
twin. -/
def modeled_rw_count (count : word) : Bool :=
  bv_unsigned count ≤ rw_bytes_max

/-- THE GATE FOR AN ARM THAT HAS NOT ALREADY DECIDED THE RANGE, and the
whole of what issue #460 left of the write-side bound.

Above `rw_bytes_max` the model asks LINUX'S OWN QUESTION about the
range — `State.access_okb`, i.e. `buf + count <= State.TASK_SIZE`, the
`__access_ok` test (include/asm-generic/access_ok.h, v6.18.46) — and
declines when the answer is no.  Which arms carry it, why the old
constant survives as the first disjunct, and why `access_ok` is the
right second disjunct, is the argument on the Rocq definition
(`theories/LinuxProcessSem/Sys/Uaccess.v`, `modeled_rw_range`); the two
facts a reader of this file needs are these.

THE TWO ORDERS ANSWER THE SAME SHAPE DIFFERENTLY, and both answers
are admissible.  A count above `rw_bytes_max` at a buffer whose
range leaves the address space is `unmodeled` through an arm that
asks this gate first, and -EFAULT through an arm that asks
`access_ok` first, which is Linux's answer.  A decline is never
wrong, so this is a difference in how much the model judges, not in
what it judges.

WHAT IS DECLINED, then, is a transfer above `rw_bytes_max` whose
range leaves the user address space — where Linux answers -EFAULT
(`vfs_write`, fs/read_write.c at v6.18.46: `access_ok` before
`rw_verify_area`) and this model says `unmodeled` instead.  Below the
bound the gate is constantly true whatever the range, so the model
does NOT have an -EFAULT arm for an out-of-range scalar write;
bugs/write-out-of-range-short-write.md owns that gap, which this
definition deliberately neither widens nor closes. -/
def modeled_rw_range (buf count : word) : Bool :=
  modeled_rw_count count || access_okb buf (bv_unsigned count)

/-! `State.access_okb` over a word-sized count, in the two directions a
proof needs.  Both halves of `__access_ok` follow from the single
inequality `buf + count ≤ TASK_SIZE`, because both operands are
non-negative — so a proof holding a link-time buffer and a small count
discharges the guard with one `omega`, and a proof holding the guard
gets the exact end back.  Twins of the Rocq lemmas of the same names. -/

theorem access_okb_intro (buf count : word)
    (h : bv_unsigned buf + bv_unsigned count ≤ TASK_SIZE) :
    access_okb buf (bv_unsigned count) = true := by
  unfold access_okb
  unfold bv_unsigned at h ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem access_okb_le (buf count : word)
    (h : access_okb buf (bv_unsigned count) = true) :
    bv_unsigned buf + bv_unsigned count ≤ TASK_SIZE := by
  unfold access_okb at h
  unfold bv_unsigned at h ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  omega

/-- `access_ok_zero buf count k`: what an arm answers once the kernel
has decided to move NO bytes — `k` is that arm's zero answer.

Linux checks the buffer range in `vfs_read` / `vfs_write` before it
dispatches on the fd (fs/read_write.c at v6.18.46: `FMODE_READ` or
`FMODE_WRITE`, then `FMODE_CAN_*`, then `access_ok(buf, count)`,
then `rw_verify_area`), and `import_ubuf` (lib/iov_iter.c at v6.18.46)
range-tests for `getrandom`, `sendto` and `recvfrom`, so the check
runs on a zero-length transfer exactly as on any other.  For `getrandom`
two tests come BEFORE it — the flag word, -EINVAL, and the entropy wait,
-EAGAIN or a sleep (drivers/char/random.c, `SYSCALL_DEFINE3(getrandom)`,
v6.18.46) — so an arm porting it keeps them ahead of this guard.  IN THE
OTHER
ORDER, and the difference is invisible only below the clamp:
`import_ubuf` caps `len` at `MAX_RW_COUNT` and tests `access_ok` on the
CAPPED length, where `vfs_read` and `vfs_write` test the count the call
named and clamp afterwards.  At or under `MAX_RW_COUNT` the two agree;
above it they do not, and the `count-top` / `count-past` pins in
`Checks.Cases.Uaccess` sit there, with counts near 2^47: they are stated
on `read`, where `vfs_read` tests the named count, and under
`import_ubuf`'s order the `count-past` shape would NOT fault, since the
capped range `[0x10000, 0x10000 + MAX_RW_COUNT)` is in bounds.  So a
`getrandom` or socket arm may reach this guard only with a count the
clamp leaves alone, or must carry the clamp-first reading instead; in
Rocq the `rw_bytes_max` gate ahead of `getrandom`'s guard is what keeps
its count under the clamp.  For `sendto` and `recvfrom` the
range test does precede the fd lookup (net/socket.c at v6.18.46,
`__sys_sendto` and `__sys_recvfrom` each call `import_ubuf` first and
reach the -EBADF of their `fd_empty` test only after it), so -EFAULT
beats -EBADF there.  The arms this
guards used to return `k` without consulting `buf` at all, which
answered 0 where Linux answers -EFAULT.

TWO ANSWERS AND NO THIRD.  `State.access_okb` is the kernel's own
predicate at the pinned commit, with its limit the one `TASK_SIZE`
the Sv48 premise fixes, so there is no range the model cannot
decide and no `unmodeled` arm here.  Note that -EFAULT is the RANGE
verdict, not a copy fault: a range the kernel accepts but has
nothing mapped at still returns the arm's zero answer, because no
byte is copied. -/
def access_ok_zero (buf count : word) (k : Sys SyscallEffect) : Sys SyscallEffect :=
  if access_okb buf (bv_unsigned count) then k else err_ret EFAULT

/-! Discharge the guards.  Stated in the `!… = false` form the guards
are written in, so a proof that has the inequality in hand rewrites once
and reduces.  Twins of the Rocq lemmas of the same names. -/

theorem rw_count_in_range (count : word) (h : bv_unsigned count ≤ rw_bytes_max) :
    (!modeled_rw_count count) = false := by
  unfold modeled_rw_count
  simp only [h, decide_true, Bool.not_true]

/-- The scalar-write gate under the OLD bound: its first disjunct, so a
proof that discharged `modeled_rw_count` discharges this unchanged. -/
theorem rw_range_in_range (buf count : word) (h : bv_unsigned count ≤ rw_bytes_max) :
    (!modeled_rw_range buf count) = false := by
  unfold modeled_rw_range modeled_rw_count
  simp only [h, decide_true, Bool.true_or, Bool.not_true]

/-- ... and above it, the range test is what admits the transfer. -/
theorem rw_range_of_access_ok (buf count : word)
    (h : access_okb buf (bv_unsigned count) = true) :
    (!modeled_rw_range buf count) = false := by
  unfold modeled_rw_range
  simp only [h, Bool.or_true, Bool.not_true]

/-- The write-side bound sits far inside the `MAX_RW_COUNT` clamp, so a
count a write judges is one the clamp leaves alone. -/
theorem rw_count_clamp_of_rw (count : word) (h : bv_unsigned count ≤ rw_bytes_max) :
    rw_count_clamp count = bv_unsigned count := by
  apply rw_count_clamp_small
  unfold rw_bytes_max at h
  unfold MAX_RW_COUNT
  omega

/-- THE SOURCE PREFIX A WRITE MAY MOVE, stated once for the spec, the
acceptor and the progress witness so that no arm can clamp on one side
and not on the other — the shape `State.writev_gathered` gives the
vectored direction.

Linux clamps a scalar transfer at `MAX_RW_COUNT` before it reaches the
write operation (`State.rw_count_clamp`): `vfs_write` (fs/read_write.c,
v6.18.46) applies it after `rw_verify_area` (fs/read_write.c, v6.18.46)
and before the `->write` or `->write_iter` call, so the bytes a `write`
can copy out of the user buffer are the readable prefix of the CLAMPED
range, never of the count the call named.  At or below `MAX_RW_COUNT` the
clamp is a no-op and this is exactly `State.readable_bytes` at the named
count (`write_source_small`).  That bound is 0x7ffff000 — `INT_MAX` with
its low page masked off (include/linux/fs.h, `MAX_RW_COUNT`, v6.18.46) —
and NOT every count under 2^31: the 4095 counts from 0x7ffff001 to
`INT_MAX` are clamped too, and `Checks/Cases/Uaccess.lean` pins the edge.

This definition is total, and the range test is not in it.  `vfs_write`
refuses the whole range with -EFAULT through `access_ok`
(arch/riscv/include/asm/uaccess.h, v6.18.46) before it clamps, so a count
that runs past the top of the address space, or a buffer that wraps,
never reaches this prefix on Linux; the arm's gate (`modeled_rw_range`,
`access_okb`) answers first, and what this definition computes for such a
range is never consulted.

Why the PREFIX and not the whole range or nothing, for a regular file.
`generic_perform_write` (mm/filemap.c, v6.18.46) copies folio by folio
with `copy_folio_from_iter_atomic` (lib/iov_iter.c, v6.18.46).  A copy
that stops short counts the bytes that landed and goes round again from
the first that did not — or, when `->write_end` rejects the short copy,
is retried at the copied length — and the loop answers -EFAULT only when
the current position will not fault in at all and nothing has been
written yet.  So a write that RETURNS has moved every readable byte
before the first unreadable one, and -EFAULT is its answer only when
that prefix is empty.  That is the file arm's exact answer, and it rests
on the copier making progress whenever the first byte is readable — the
loop's own "Ensure forward progress" premise.  riscv's scalar copier
keeps that premise only in its byte-copy paths: the word paths report a
fault from the start of the word or eight-word batch they were in
(`fallback_scalar_usercopy_sum_enabled`, arch/riscv/lib/uaccess.S,
v6.18.46; the vector path hands its remainder to the same routine,
arch/riscv/lib/riscv_v_helpers.c, v6.18.46), so once the readable
remainder is shorter than that unit, with at least `9*SZREG-1` bytes
still asked, the retries copy nothing while
`fault_in_iov_iter_readable` (lib/iov_iter.c, v6.18.46) keeps succeeding
on the readable page, and the loop never ends.  That is no return at all
rather than a different one, and a deviation from the contract the loop
states rather than a behaviour to model: it changes no value this
definition or the file arm names.

A pipe is not that exact: `anon_pipe_write` (fs/pipe.c, v6.18.46) copies
a page at a time with `copy_page_from_iter` (lib/iov_iter.c, v6.18.46),
and a short copy is -EFAULT whenever nothing has been counted yet,
however long the readable prefix was.  Rocq's pipe arm declines a source
it cannot read whole and says there why the decline is conservative
rather than forced by the kernel; the channel arm answers the prefix and
refuses that -EFAULT, a soundness gap recorded in
bugs/write-channel-partial-source-efault-refused.md.

qemu-user reads no prefix at all.  Its `write` locks the whole range
before the host call (`TARGET_NR_write` in linux-user/syscall.c, through
`lock_user` in linux-user/uaccess.c and `page_check_range` in
accel/tcg/user-exec.c, QEMU 11.1.1) and answers -EFAULT for a source
with any unreadable byte inside the count, whatever the fd.  An arm that
delivers exactly this prefix therefore refuses a real answer of a
supported implementation on every fd kind, not only the pipe; that is
the write port's question, named here because this is where the prefix
is defined.

What each arm makes of the prefix is the arm's; this definition only
says which bytes the kernel could have read. -/
def write_source (mp : word → Option byte) (buf count : word) : List byte :=
  readable_bytes mp buf (Z_to_bv 64 (rw_count_clamp count))

theorem write_source_length_le (mp : word → Option byte) (buf count : word) :
    ((write_source mp buf count).length : Int) ≤ rw_count_clamp count := by
  unfold write_source
  have h := readable_bytes_length_le mp buf (Z_to_bv 64 (rw_count_clamp count))
  rw [rw_count_clamp_word] at h
  exact h

/-- Below the clamp it IS the walk at the named count, which is what a
proof holding a concrete count needs. -/
theorem write_source_small (mp : word → Option byte) (buf count : word)
    (h : bv_unsigned count ≤ MAX_RW_COUNT) :
    write_source mp buf count = readable_bytes mp buf count := by
  unfold write_source
  rw [rw_count_clamp_small count h]
  unfold bv_unsigned Z_to_bv
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- And the old write-side bound sits far inside the clamp, so a proof
that already holds `count ≤ rw_bytes_max` sees the same walk. -/
theorem write_source_of_rw (mp : word → Option byte) (buf count : word)
    (h : bv_unsigned count ≤ rw_bytes_max) :
    write_source mp buf count = readable_bytes mp buf count := by
  apply write_source_small
  unfold rw_bytes_max at h
  unfold MAX_RW_COUNT
  omega

/-- The effect write list for `bs` delivered bytes at `buf`: no entry
when no byte moves.  This is the CANONICAL zero-byte shape — a read
that delivers nothing (file at end-of-file, `count = 0`) has effect
`mkEffect 0 [] []` on every fd kind, the same shape as a zero-byte
channel read, rather than a vacuous `(buf, [])` entry. -/
def delivered_writes (buf : word) (bs : List byte) : List (word × List byte) :=
  match bs with
  | [] => []
  | _ :: _ => [(buf, bs)]

end LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
