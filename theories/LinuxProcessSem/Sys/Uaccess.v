(** * LinuxProcessSem.Sys.Uaccess — the user-buffer boundary

    Every other file under [Sys/] answers to one kernel SOURCE file;
    this one answers to kernel HEADERS, and holds what the specs share
    rather than any one syscall's behaviour.  The predicate it
    transcribes is [__access_ok] and the generic [access_ok] wrapping it
    (include/asm-generic/access_ok.h, [__access_ok] and the [#ifndef
    access_ok] fallback, at stable v6.18.46 / 1f99e9ab748f), which is
    the file [State.access_okb]'s note cites for the same predicate.
    include/linux/uaccess.h defines NEITHER of them — it pulls the arch
    header in and only USES [access_ok], in [copy_{to,from}_user] and in
    the fallback [#define user_access_begin(ptr,len) access_ok(ptr, len)]
    — so it is named here for the copy helpers, not for the range
    test.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export
  Syscall.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** WHAT THIS CONSTANT BOUNDS: the hole a write or a growing [ftruncate] may open past
    end-of-file ([ReadWrite.modeled_file_gap],
    [Open.modeled_truncate_gap]), the buffer a [getrandom] may name, and
    the total a socket send may gather.  IT DOES NOT CAP A TRANSFER'S
    COUNT in either direction.  A read's recursion is capped by the file
    or the stream it reads from, and [State.readable_bytes] spends
    neither stack depth nor a length-sized unary numeral on the count a
    write names.  A transfer's count faces the kernel's own two tests —
    [State.access_okb] on the range, then the [MAX_RW_COUNT] clamp
    ([State.rw_count_clamp]) — and, on the arms [modeled_rw_range]
    names, that gate in front of them, which is this constant OR that
    same range test.

    THE HOLE IS NOT THE COUNT, and that is why this constant bounds the
    one and not the other.  A hole is the distance from the file's end to the
    write's offset — bytes the model has to BUILD because it holds a
    file as a flat byte list, where Linux leaves a sparse file's hole
    costing nothing.  No per-call count bounds it: a one-byte write at a
    far offset opens an arbitrarily large one.  A COUNT, by contrast,
    costs the model a chunk-count numeral 4096 times smaller than
    itself and a list bounded by what is actually mapped.

    THIS IS A MODELING BOUND, NOT A KERNEL ONE, and it is here because
    the alternative is a crash.  Linux settles a huge scalar count in
    three cheap steps and then does the transfer.  In [vfs_read] and
    [vfs_write] (fs/read_write.c at v6.18.46), after the [FMODE_*]
    tests and in this order:

    - [if (unlikely(!access_ok(buf, count))) return -EFAULT;];
    - [rw_verify_area], whose first statement is
      [if (unlikely((ssize_t) count < 0)) return -EINVAL;];
    - [if (count > MAX_RW_COUNT) count = MAX_RW_COUNT;], with
      [#define MAX_RW_COUNT (INT_MAX & PAGE_MASK)] — 0x7ffff000 — in
      include/linux/fs.h.

    The first is [State.access_okb] and the third is
    [State.rw_count_clamp], and both are what the read AND write
    arms apply; none of the three bounds what the model can EVALUATE,
    which is what this constant is for on the paths it guards.
    THE ORDER MATTERS for
    one errno.  [access_ok] runs first, and on riscv64 it is the generic
    [__access_ok] with its limit at [State.TASK_SIZE] = 2^47, so a
    [count] that is negative as [ssize_t] — at least 2^63 — has already
    been answered -EFAULT before [rw_verify_area]'s sign test is reached:
    on a kernel with an MMU the -EINVAL is UNREACHABLE through the
    read/write syscalls, and modeling the sign test would put -EINVAL
    where Linux returns -EFAULT.  The MMU is doing the work in that
    argument, so state it: [__access_ok] returns true without looking at
    either operand when CONFIG_ALTERNATE_USER_ADDRESS_SPACE is set or
    CONFIG_MMU is not, and a nommu riscv64 kernel reaches that same
    generic [__access_ok] through asm-generic/uaccess.h.  On such a
    kernel -EINVAL is what a negative [count] gets.  This model has
    [mmap] and page permissions and so describes MMU kernels only.

    So above the bound the model declines on the paths it guards;
    it does not invent an errno, and it does not clamp — a clamp would
    have it report a short transfer where Linux transferred everything.

    2^17 IS SET FROM BELOW BY A PROOF, NOT BY A PROGRAM, and the
    distinction matters because it is the difference between "no slack
    exists" and "no slack exists as currently written".  What that proof
    constrains is the theories/Common WRITE-NODE FAMILY rather than
    the spec: [CatSim.buf_modeled] is stated at this constant and
    is what those lemmas hand [write_source_of_rw] to see the walk they
    were written against.  That is a library convenience, not a bound
    the spec has — a write past it is judged, it just has no ready-made
    node in that family.

    The chain is: a single argv string may be 131071 bytes
    ([Run.valid_argv], from Linux's MAX_ARG_STRLEN of 32 pages less its
    NUL), and [Examples.brk_rev_ns] writes argv[1] reversed followed by a
    newline.  [brk_rev_ns_source.bufs_modeled_out] discharges
    [buf_modeled] for that write from [nN_le] — the 131071 cap — giving
    131071 + 1 = 131072, the constant on the nose.  Lower the bound by
    one and that lemma's [lia] fails, the write is [unmodeled], and since
    [unmodeled] puts a run in [Run.reaches_error] the example's
    equivalence theorem stops being provable rather than merely weakening.
    So the constant cannot be lowered without touching that proof.

    WHAT IS NOT TRUE is that the program can perform such a write.  It
    cannot: [brk_rev_ns]'s own source and target both return 3 for an
    argument longer than 65536 bytes (source/program.c and
    target/program.zig, the [n > 65536] guard), so the largest write it
    can ever execute is 65537 bytes.  [bufs_modeled_out] sits in a
    section where only [2 <= length av] is in scope and the program's own
    cap is not, so it reaches for the argv bound instead of the tighter
    one that is actually available; [alloc_join_ns_source] does the
    tighter thing for its own buffer.  Threading the 65536 guard into the
    section would let the constant go as low as 65537.  That is a real
    option, deliberately not taken here: 2^17 is a rounder number to
    explain and nothing needs the room, but the reason to keep it is
    convenience, and it should not be recorded as a program requirement
    it is not.

    FROM ABOVE the constraint is real but soft, and NO SINGLE NUMBER
    SHOULD BE QUOTED FOR IT.  The mechanism: [BvBase.word_to_nat] is
    [Z.to_nat], and Checks/Extraction.v imports ExtrOcamlZBigInt but not
    ExtrOcamlNatInt, so [nat] stays genuine unary Peano and [Z.to_nat]
    bottoms out in [Pos.to_nat = iter_op add].  [iter_op]'s doubling keeps
    the NUMBER of additions logarithmic, but Peano [add] is [S (add p m)],
    not tail-recursive, so the largest intermediate addition costs stack
    depth proportional to the length.  The places below consult that
    length, all but the last of them by recursing with it, and every one
    of them before a single memory lookup, so what a caller sees when
    one of them goes over is [Stack overflow] and exit 2 — or, on an
    OCaml 4 native build, a bare SIGSEGV — a status no verdict maps to.
    THEY DO NOT ALL GO OVER AT THE SAME DEPTH, so do not read them as
    one number.  Measured on OCaml 5, at the same argument,
    [word_to_nat] costs a thousandth of what [State.readable_bytes] costs.
    The others are not measured.  The list, and which of them this
    constant stands in front of:

    - [State.readable_bytes], for a [write], and [gather_prefix], which
      calls it, for a [writev].  THIS CONSTANT STANDS IN FRONT OF
      NEITHER: both use the chunked tail-recursive walk described on
      [State.wmem_chunk].  What a write converts to a unary numeral is the
      CHUNK COUNT, [count] over 4096; what it pays is a list as
      long as the mapped prefix it actually reads, which is bounded by
      the process's memory rather than by the call;
    - [Fs.file_write]'s [repeat] and [firstn], for a write to a file.
      Only the [repeat] is sized by the HOLE, which is what
      [ReadWrite.modeled_file_gap] bounds.  The [firstn] is sized by the ABSOLUTE
      offset, so this bound does not bound it and cannot: it is capped
      by the file's own length, and a file's length is the cost this
      constant explicitly does not cover (see the last paragraph).  An append to a long file pays it
      with a gap of zero;
    - [Fs.file_truncate]'s [repeat] and [firstn], for an [ftruncate].
      Both are sized by the NEW LENGTH, and both are built from the one
      numeral [word_to_nat len], which [Open.modeled_truncate_gap] bounds by
      the file's length plus this constant — one-sidedly, so in both
      directions.  That is the SAME exposure as [file_write] above, not
      a better one: the file's own length is still uncovered, so a
      shrink of a long file builds a numeral the size of that file with
      the gap negative;
    - [State.read_bytes_map] over [buflen], for a [getrandom] — which
      is why [Random.getrandom_spec] carries this same guard.  THIS ONE
      DOES NOT RECURSE WITH THE LENGTH: it is the
      chunked tail-recursive accumulator described on
      [State.wmem_chunk], so its depth does not scale with [buflen]
      and the largest numeral it builds is the CHUNK COUNT, [buflen] over
      4096 rather than [buflen]; what it pays is a list that long.
      The guard stays because that cost is real, and because the same
      number of bytes should be the same transfer whichever call names
      it — not because this path would crash.

    A [read] IS ON NEITHER SIDE OF THAT LIST: [Fs.file_read]'s numeral is
    [word_to_nat_bounded count (length rest)] — capped at what is left
    of the file BEFORE the conversion, the cap-and-prove-equal
    technique described below — so a file read is charged for the file
    it holds (the cost this constant explicitly does not cover, see
    the last paragraph) and never for the [count] it names.  The
    OFFSET does not cross into [nat] at all: [Fs.file_from] walks the
    file in [Z] and in tail position.  A channel read consumes [count]
    only through [Z] comparisons ([Syscall.w_is0], and the
    [length bs <= ...] side condition), and the prefix it delivers is
    bounded by the input stream.  The follow-on walks of a delivering
    read ([State.read_bytes_map] and [delivered_writes] over the
    DELIVERED bytes, the checker's [wmem_ok]) are all sized by that
    same file- or stream-bounded delivery.  That is why the file,
    channel and directory read arms of [ReadWrite.read_spec] are not
    guarded here: their guard is [State.access_okb] and nothing else,
    with Linux's own [MAX_RW_COUNT] clamp ([State.rw_count_clamp])
    bounding what a delivery may claim.

    THE PIPE AND SOCKET READ ARMS DO NOT RECURSE ON [count] EITHER.
    [State.pipe_take] takes the minimum of [count] and the queue's own
    length in [Z] before it builds a numeral — a pipe delivers at most
    PIPE_BUF bytes whatever the count — and [State.net_take_z] walks in
    [positive].  Both arms carry [modeled_rw_range], for the RANGE and
    not for the size.

    How deep the recursion may go before it dies is a property of the
    OCAML MAJOR VERSION, and so of whichever runtime builds the checker,
    rather than of this development.

    BOTH DIRECTIONS WALK IN CHUNKS, and what the ceiling costs is a
    LIST rather than a stack.  [readable_bytes] is
    [State.readable_bytes_chunks] over [State.readable_bytes_acc]: the
    inner walk extends a reversed accumulator through a tail call, the
    outer loop hands out at most [State.wmem_chunk] bytes of fuel at a
    time, and one [rev_append] restores byte order.
    [State.readable_bytes_eq] is the equation proofs go through, in the
    shape [State.read_bytes_map_eq] set on the read side.  The write
    side therefore has the shape of the read side's
    [State.read_bytes_map], and that is why the write and writev arms
    need no count gate.

    WHAT THAT LEAVES, precisely.  The stack depth scales with [count] on
    neither direction, and the largest unary numeral either builds is
    the CHUNK COUNT, [count] over 4096.  What a transfer still pays per
    byte is its OUTPUT LIST — one cons per mapped byte it actually reads
    — which is bounded by the process's memory rather than by the call,
    and which is the cost this constant explicitly does not cover (see
    the last paragraph).

    ONE PREREQUISITE IS NOT MET.  Nothing in this repository sets
    [OCAMLRUNPARAM] for the extracted checker, so the minor heap and
    the stack ceiling are whatever the invoking shell leaves them.
    That is not a semantic question.

    The measurements are properties of the toolchain rather than of
    this specification, and this comment does not give them.

    REAL PROGRAMS MAKE WRITES PAST THIS CONSTANT, AND THE MODEL JUDGES
    THEM.  A single [write] in sbase's [paste] is an order of magnitude
    past it.  No arm asks about a
    transfer's SIZE at all.  What the transfer arms that gate a
    range carry is [modeled_rw_range], which admits any count at a
    buffer inside the address space, and every other transfer arm asks
    [access_ok] and nothing else.  So the paragraph ABOVE about
    [brk_rev_ns] — that no modeled example performs such a write — is a
    statement about the examples in this tree and not about programs,
    and what stands between that program and a run is COST rather than a
    modeled decline.  Priority 1 is not at stake, since a decline is
    explicit and fails closed; priority 3 is not at stake for the
    count.  What this constant declines is the past-end-of-file
    HOLE, [getrandom]'s buffer and the socket sends.
    THE PROOF SIDE HAS THE ROOM: nothing in this tree bounds the
    constant from above ([State.access_okb] is a range test and walks
    nothing), so a
    raise meets only the proofs that assume a count under it, the
    [Hcnt]-shaped hypotheses in theories/Common.  So the numeral is the cheap
    half, and moving it alone is the misleading move: it would widen what
    the spec admits while leaving the [OCAMLRUNPARAM] prerequisite unmet.

    WHY A SEMANTIC BOUND AND NOT A REPRESENTATION FIX.  The cheaper
    technique is to CAP the numeral and prove the capped definition equal
    to the uncapped one, which narrows nothing and adds no premise.  This
    file uses it where it applies — [Fs.file_from] and
    [Fs.file_read_unguarded] are exactly that.  It does not apply to
    [State.readable_bytes], for a reason worth stating so nobody retries
    it: the technique spends a bound you already have, and here there is
    none.  [readable_bytes] walks [mp : word -> option byte], a bare
    function; the cap it would need is the length of the mapped run at
    the address, which is not definable from a function with no
    computable support.  [Fs.file_read] was capped by [length data]
    because its output was already bounded by a byte list the model
    holds — whereas [readable_bytes]'s numeral bounds its OWN output,
    which is [count] bytes long precisely when the bytes are mapped.

    And the obstruction survives the obvious repair.  Even if memory were
    re-represented as a finite interval structure, the smallest run the
    model structurally guarantees is the zero-mapped stack every run
    has ([Run.init_machine_state]: 8 MiB less the entry image, so more
    than 5 MiB), and an anonymous grant may be
    [State.target_alloc_limit] — 512 GiB.  A correct cap is not a small
    cap: 5 MiB is 40x this constant.

    WHICH IS WHY THE WALK USES NEITHER OF THESE.  Capping
    cannot bound [readable_bytes]'s walk and re-representing memory
    cannot either, so the walk's SHAPE does the work instead —
    chunked and tail-recursive, as the ceiling paragraphs above describe
    — and that needs no bound at all.  The argument of the two
    paragraphs before this one holds of anything that
    would try to CAP a walk over a bare [mp]; the write direction does
    not need a semantic size bound.

    COST TO THE THEOREM: a source and a target that diverge only on a
    write or a growing [ftruncate] opening a larger hole past
    end-of-file than [rw_bytes_max], or on a [getrandom] or a socket
    send naming more than it, are not distinguished by
    [Equivalence.strong_universal_T].  A write naming more than
    [rw_bytes_max] BYTES is not on that list.  The narrowing is one-sided, so it
    admits nothing unsound: a TARGET that performs such a call reaches
    [Run.reaches_error] and is rejected outright.

    NOT covered here, and deliberately: the cost of every path below
    still scales with the length of the file the model is holding, since
    that file IS a byte list — [Fs.file_write] walks it on every write —
    and a run GROWS that file itself, a chain of writes each opening a
    legal hole reaching any length.  So this is not only about
    [Fs.valid_fs]'s initial images, and bounding those would not close it;
    bounding it at all changes what the theorem quantifies over rather
    than what a syscall admits.

    THE BOUND THEREFORE DOES NOT CLOSE ITS OWN CLASS, and that should be
    read as a limit rather than as a claim.  It bounds ONE syscall, and
    the quantity that drives the recursion is reachable by ITERATION: a
    loop of [lseek(fd, off += rw_bytes_max, SEEK_SET); write(fd, b, 1)]
    performs only writes this spec judges — each names one byte and opens
    a hole of exactly [rw_bytes_max], so [modeled_rw_range] and
    [ReadWrite.modeled_file_gap] both hold at every step — yet after 2048 turns the
    file is 2^28 bytes long, which is the depth the extraction is
    measured to die at.  Nothing here rejects that run; each step is a
    legal transfer, and it is the accumulated LENGTH, which no per-call
    guard sees, that does the damage.  What this constant buys is that a
    SINGLE syscall cannot do it — the crash costs a program 2048 calls
    instead of one, and is not reachable by accident.  Closing the
    class needs a bound on the state, not on the call, and that is the
    change to what the theorem quantifies over described above. *)
Definition rw_bytes_max : Z := 131072%Z.

(** [count] is a transfer size the model will judge.  This is the gate
    [getrandom] and the socket sends carry, and the shape the hole
    guards are written in.  NO ARM OF [ReadWrite] USES IT.
    Every arm that gates a count uses [modeled_rw_range] below —
    every judging arm of [ReadWrite.write_spec], named at
    [modeled_rw_range], and [ReadWrite.read_spec]'s
    socket and pipe arms — and every other read
    and write arm carries no count gate at all (see [rw_bytes_max]). *)
Definition modeled_rw_count (count : word) : bool :=
  (bv_unsigned count <=? rw_bytes_max)%Z.

(** THE GATE FOR AN ARM THAT HAS NOT ALREADY DECIDED THE RANGE, and the
    whole of the write-side bound.

    Above [rw_bytes_max] the model asks LINUX'S OWN QUESTION about the
    range — [State.access_okb], i.e. [buf + count <= State.TASK_SIZE] —
    and declines when the answer is no.

    WHICH ARM ASKS WHAT, and this is the one place the tree says it.
    Every transfer arm of [ReadWrite] asks [vfs_read]'s or
    [vfs_write]'s [access_ok] on the count the call NAMED
    (fs/read_write.c, [vfs_read] and [vfs_write]) and answers -EFAULT
    when it refuses.  The arms differ only in what stands in front of it:

    - NOTHING: [ReadWrite.read_spec]'s /dev/null, channel, file,
      directory and /dev/urandom arms, all of [pread64], and
      [pwrite64]'s one judging arm, where [rw_range_of_access_ok] below
      is the proof that this gate would be constantly true.
    - THIS GATE: [ReadWrite.write_spec]'s channel, plain-file,
      read-write-file, append and pipe arms, its /dev/null arm (through
      [ReadWrite.write_range_gate]), and [ReadWrite.read_spec]'s SOCKET
      and PIPE arms.  Below the gate the socket and pipe read arms and the
      channel and pipe write arms ask it at the head of each path that
      moves bytes, and on each path that moves none through
      [access_ok_zero], which is the same test; that is why it appears in
      two places on those arms rather than once.  The plain-file,
      read-write-file and append arms ask it first under the gate, so the
      [access_ok_zero] inside [ReadWrite.write_file_tail] decides nothing
      on any of its three callers, those three arms.
    - [State.import_iovecs], for [readv] and [writev]: an [access_ok] on
      every descriptor's uncapped length, before a byte moves.

    EVERY WALK A TRANSFER ARM MAKES IS THEREFORE BEHIND THE TEST, and a
    reader can check it without trusting this note: each walk covers at
    most the clamped count, which is at most the named count, so
    [buf + len <= buf + count <= State.TASK_SIZE] and no walk passes the
    top of the user address space, let alone wraps at 2^64.

    WHAT THE DELIVERING PATHS ANSWERED BEFORE THEY ASKED.  The write
    arms other than append and /dev/null, and the socket and pipe read
    arms on their delivering paths, used to let the walk speak for the
    range: a small count at a range [access_ok] refuses was a short or
    full transfer where Linux answers -EFAULT, and at a buffer straddling
    2^64 a transfer of bytes the walk reached by wrapping
    ([State.copy_bytes_map]'s note has the wrap).  Every other path of
    those arms already asked, so the one path without the guard was the
    one that moved bytes.

    THE RULE IS ABOUT ORDER.  The gate stays AHEAD of each arm's own
    test, so the gate decides first whether the model judges the call
    at all.

    THE TWO ORDERS ANSWER THE SAME SHAPE DIFFERENTLY, and both answers
    are admissible.  A count above [rw_bytes_max] at a buffer whose
    range leaves the address space is [unmodeled] through [write] — the
    gate is reached first — and -EFAULT through [pwrite64] on a
    write-only fd, which is Linux's answer.  A decline is never wrong,
    so this is a difference in how much the model judges, not in what it
    judges.  Aligning them means either moving each arm's [access_ok]
    above its gate, which is a widening, or putting a gate on
    [pwrite64], which would be dead code; neither is folded in here.

    The read arms that carry it read it exactly as the write arms do,
    and the paragraphs below apply unchanged to both.

    WHY [rw_bytes_max] IS THE FIRST DISJUNCT.  Below it the gate is
    [modeled_rw_count], so a proof that discharges [modeled_rw_count]
    discharges this gate with no new fact, and the call reaches the
    arm's own [access_ok], which answers a small count at an
    unaddressable buffer -EFAULT as Linux does.  This note used to give
    a second reason: that the model had no -EFAULT arm for an
    out-of-range scalar transfer, because adding one would make every
    judgement depend on a stack-layout fact the model does not carry.
    That reason is withdrawn.  [State.access_okb] compares the call's
    two arguments with the literal [State.TASK_SIZE] and reads no model
    state at all.  What a proof of a delivering transfer owes is the
    range itself, [buf + count <= TASK_SIZE] ([access_okb_intro]); for a
    buffer in the initial argv/envp block [Run.entry_stack_fits]
    supplies it, since it puts the block at or below
    [State.sp_window_hi], which is [State.TASK_SIZE].

    WHY [access_ok] IS THE RIGHT SECOND DISJUNCT.  Above [rw_bytes_max]
    it admits exactly the calls the arm's own [access_ok] then passes, so
    what the gate declines is only what Linux answers -EFAULT.

    WHAT IS DECLINED, then, is a transfer above [rw_bytes_max] whose
    range leaves the user address space — where Linux answers -EFAULT
    and this model says [unmodeled] instead.  Fail-closed: every count
    is admitted at an in-range buffer, up to and past the kernel's own
    [MAX_RW_COUNT] clamp ([State.rw_count_clamp], applied by
    [write_source]).

    writev and readv need no analogue: [State.import_iovecs] already
    applies [access_ok] to every descriptor's uncapped length, so a
    vectored transfer is range-checked before a byte moves. *)
Definition modeled_rw_range (buf count : word) : bool :=
  modeled_rw_count count || access_okb buf (bv_unsigned count).

(** [State.access_okb] over a word-sized count, in the two directions a
    proof needs.  Both halves of [__access_ok] follow from the single
    inequality [buf + count <= TASK_SIZE], because both operands are
    non-negative — so a proof holding a link-time buffer and a small
    count discharges the guard with one [lia], and a proof holding the
    guard gets the exact end back. *)
Lemma access_okb_intro : forall (buf count : word),
  (bv_unsigned buf + bv_unsigned count <= TASK_SIZE)%Z ->
  access_okb buf (bv_unsigned count) = true.
Proof.
  intros buf count H. unfold access_okb.
  pose proof (bv_unsigned_in_range 64 buf) as [Hb _].
  pose proof (bv_unsigned_in_range 64 count) as [Hc _].
  apply Bool.andb_true_iff. split; apply Z.leb_le; lia.
Qed.

Lemma access_okb_le : forall (buf count : word),
  access_okb buf (bv_unsigned count) = true ->
  (bv_unsigned buf + bv_unsigned count <= TASK_SIZE)%Z.
Proof.
  intros buf count H. unfold access_okb in H.
  apply Bool.andb_true_iff in H as [_ H]. apply Z.leb_le in H. lia.
Qed.

(** [access_ok_zero buf count k]: what an arm answers once the kernel
    has decided to move NO bytes — [k] is that arm's zero answer.

    Linux checks the buffer range in [vfs_read] / [vfs_write] before it
    dispatches on the fd (fs/read_write.c at v6.18.46: [FMODE_READ] or
    [FMODE_WRITE], then [FMODE_CAN_*], then [access_ok(buf, count)],
    then [rw_verify_area]), and [import_ubuf] (lib/iov_iter.c at v6.18.46) does the
    same for [getrandom], [sendto] and [recvfrom], so the check runs on
    a zero-length transfer exactly as on any other.  Without this
    guard an arm would answer 0 where Linux answers -EFAULT.

    TWO ANSWERS AND NO THIRD.  [State.access_okb] is the kernel's own
    predicate at v6.18.46, with its limit the one [TASK_SIZE]
    the Sv48 premise fixes, so there is no range the model cannot
    decide and no [unmodeled] arm here.  Note that -EFAULT is the RANGE
    verdict, not a copy fault: a range the kernel accepts but has
    nothing mapped at still returns the arm's zero answer, because no
    byte is copied. *)
Definition access_ok_zero (buf count : word) (k : Sys SyscallEffect)
    : Sys SyscallEffect :=
  if access_okb buf (bv_unsigned count) then k else err_ret EFAULT.

(** Discharge the guards.  Stated in the [negb … = false] form the
    guards are written in, so a proof that has the inequality in hand
    rewrites once and reduces. *)

Lemma rw_count_in_range : forall count,
  (bv_unsigned count <= rw_bytes_max)%Z ->
  negb (modeled_rw_count count) = false.
Proof.
  intros count H. unfold modeled_rw_count.
  now rewrite (proj2 (Z.leb_le _ _) H).
Qed.

(** The scalar-write gate under [rw_bytes_max]: its first disjunct, so a
    proof that discharges [modeled_rw_count] discharges this too. *)
Lemma rw_range_in_range : forall buf count,
  (bv_unsigned count <= rw_bytes_max)%Z ->
  negb (modeled_rw_range buf count) = false.
Proof.
  intros buf count H. unfold modeled_rw_range, modeled_rw_count.
  now rewrite (proj2 (Z.leb_le _ _) H).
Qed.

(** ... and above it, the range test is what admits the transfer. *)
Lemma rw_range_of_access_ok : forall buf count,
  access_okb buf (bv_unsigned count) = true ->
  negb (modeled_rw_range buf count) = false.
Proof.
  intros buf count H. unfold modeled_rw_range.
  rewrite H. now rewrite Bool.orb_true_r.
Qed.

(** The write-side bound sits far inside the [MAX_RW_COUNT] clamp, so a
    count a write judges is one the clamp leaves alone. *)
Lemma rw_count_clamp_of_rw : forall count,
  (bv_unsigned count <= rw_bytes_max)%Z ->
  rw_count_clamp count = bv_unsigned count.
Proof.
  intros count H. apply rw_count_clamp_small.
  unfold rw_bytes_max in H. unfold MAX_RW_COUNT. lia.
Qed.

(** THE SOURCE PREFIX A WRITE MAY MOVE, stated once for the spec, the
    acceptor and the progress witness so that no arm can clamp on one
    side and not on the other — the shape [State.writev_gathered] gives
    the vectored direction.

    Linux clamps a scalar transfer at [MAX_RW_COUNT] before it reaches
    the write operation ([State.rw_count_clamp]; [vfs_write] applies it
    after [rw_verify_area], fs/read_write.c at v6.18.46), so the bytes a
    [write] can copy out of the user buffer are the readable prefix of
    the CLAMPED range, never of the count the call named.  Below 2^31 the
    clamp is a no-op and this is exactly [State.readable_bytes] at the
    named count.

    EVERY CALLER HAS ASKED [access_ok] ON THE NAMED COUNT FIRST (the
    list at [modeled_rw_range]), so this walk covers at most
    [rw_count_clamp count <= count] bytes from a [buf] with
    [buf + count <= State.TASK_SIZE]: it never leaves the user address
    space.  That is why the walk itself carries no range test. *)
Definition write_source (mp : word -> option byte) (buf count : word)
    : list byte :=
  readable_bytes mp buf (Z_to_bv 64 (rw_count_clamp count)).

Lemma write_source_length_le : forall mp buf count,
  (Z.of_nat (length (write_source mp buf count)) <= rw_count_clamp count)%Z.
Proof.
  intros mp buf count. unfold write_source.
  pose proof (readable_bytes_length_le mp buf (Z_to_bv 64 (rw_count_clamp count))).
  now rewrite rw_count_clamp_word in *.
Qed.

(** Below the clamp it IS the walk at the named count, which is what a
    proof holding a concrete count needs. *)
Lemma write_source_small : forall mp buf count,
  (bv_unsigned count <= MAX_RW_COUNT)%Z ->
  write_source mp buf count = readable_bytes mp buf count.
Proof.
  intros mp buf count H. unfold write_source.
  now rewrite (rw_count_clamp_small _ H), Z_to_bv_bv_unsigned.
Qed.

(** And [rw_bytes_max] sits far inside the clamp, so a proof
    that already holds [count <= rw_bytes_max] sees the same walk. *)
Lemma write_source_of_rw : forall mp buf count,
  (bv_unsigned count <= rw_bytes_max)%Z ->
  write_source mp buf count = readable_bytes mp buf count.
Proof.
  intros mp buf count H. apply write_source_small.
  unfold rw_bytes_max in H. unfold MAX_RW_COUNT. lia.
Qed.

(** The effect write list for [bs] delivered bytes at [buf]: no entry
    when no byte moves.  This is the CANONICAL zero-byte shape — a read
    that delivers nothing (file at end-of-file, [count = 0]) has effect
    [mkEffect 0 [] []] on every fd kind, the same shape as a zero-byte
    channel read, rather than a vacuous [(buf, [])] entry. *)
Definition delivered_writes (buf : word) (bs : list byte) : list (word * list byte) :=
  match bs with
  | [] => []
  | _ :: _ => [(buf, bs)]
  end.
