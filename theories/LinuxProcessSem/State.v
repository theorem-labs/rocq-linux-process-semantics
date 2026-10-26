(** * LinuxProcessSem.State — syscall inputs, effects, model state, and events

    TRUST BOUNDARY: this file is part of the trusted specification.

    Machine quantities are [word = bv 64], memory bytes are [byte =
    bv 8].  Range arithmetic (page rounding, interval overlap, the
    grant top) is done in [Z] over [bv_unsigned], giving bound
    checks their unbounded-integer meaning (see BvBase.v).

    The syscall model is GENERATIVE and NON-DETERMINISTIC: given the
    syscall's inputs (number, register arguments, pre-syscall memory), the
    relational spec ([Specs.syscall_spec]) describes the set of admissible
    [SyscallEffect]s — the return value plus ordinary writes and symbolic
    zero, unmap, and pre-effect-copy ranges in user memory.  The trace
    semantics ([Run.v]) picks any admissible
    effect and applies it deterministically, so a syscall can only touch
    the memory it declares (framing holds by construction; no separate
    frame side-conditions are needed).

    This file: numeric/ABI helpers, [SyscallInput]/[SyscallEffect], the
    [Model] state threaded across a run, observable [event]s, and the
    fd-table/VmMaps helpers. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   Numeric helpers (Linux riscv64 ABI conventions)
   ========================================================================= *)

Definition two_pow_64 : Z := (2 ^ 64)%Z.
Definition page_size : Z := 4096%Z.

(** Page rounding, in [Z] over unsigned values (a length within a page
    of 2^64 would wrap under [bv] arithmetic; [Z] does not
    wrap, and the allocator bound checks below rely on that). *)
Definition page_round_up_Z (n : Z) : Z :=
  ((n + page_size - 1) / page_size * page_size)%Z.
Definition page_round_down_Z (n : Z) : Z :=
  (n / page_size * page_size)%Z.

(** A nonzero length rounds up to at least one whole page.  Every arm
    that refuses a zero length and then records [page_round_up_Z] of it
    is recording a range that names real bytes, and this is the step
    from the one to the other. *)
Lemma page_round_up_Z_pos : forall n,
  (0 < n)%Z -> (page_size <= page_round_up_Z n)%Z.
Proof.
  intros n Hn. unfold page_round_up_Z, page_size in *.
  assert (H1 : (1 <= (n + 4096 - 1) / 4096)%Z).
  { apply Z.div_le_lower_bound; lia. }
  lia.
Qed.

(** A page-aligned window swallows whole pages: if [x] lies in
    [[lo, hi)] and both ends are page aligned, so is the whole page [x]
    is on.  This is what makes a page-granular fact about a single BYTE
    inside a page-aligned request a fact about the request. *)
Lemma page_round_down_Z_within : forall lo hi x,
  (lo mod page_size = 0)%Z ->
  (hi mod page_size = 0)%Z ->
  (lo <= x < hi)%Z ->
  (lo <= page_round_down_Z x /\ page_round_down_Z x + page_size <= hi)%Z.
Proof.
  intros lo hi x Hlo Hhi Hx. unfold page_round_down_Z, page_size in *.
  pose proof (Z.div_mod lo 4096 ltac:(lia)) as Hdl.
  pose proof (Z.div_mod hi 4096 ltac:(lia)) as Hdh.
  pose proof (Z.div_le_mono lo x 4096 ltac:(lia) ltac:(lia)) as Hmono.
  pose proof (Z.div_lt_upper_bound x 4096 (hi / 4096) ltac:(lia) ltac:(lia))
    as Hup.
  lia.
Qed.

(** Maximum dynamic stack size below the initial SP (Linux default
    [RLIMIT_STACK] = 8 MiB).  The whole region
    [init_sp - stack_max_size, init_sp) models the zero-mapped Linux
    stack (see [Run.init_machine_state]). *)
Definition stack_max_size : Z := (8 * 1024 * 1024)%Z.

(** The initial stack pointer is chosen NON-DETERMINISTICALLY at [execve]
    (ASLR): any 16-byte-aligned value in [sp_window_lo, sp_window_hi]
    ([Run.valid_sp]), quantified INDEPENDENTLY for the two binaries in
    [Equivalence.strong_universal_T].  The window and ceiling are
    unsigned-address constants, kept as [Z].

    THE WINDOW IS THE Sv48 KERNEL'S, and only that one.  Linux riscv64
    puts the stack top at [STACK_TOP = DEFAULT_MAP_WINDOW = 1 <<
    (MMAP_VA_BITS - 1)] (arch/riscv/include/asm/processor.h), which is
    [0x8000_0000_0000] wherever the kernel runs Sv48 or Sv57
    ([MMAP_VA_BITS] saturates at 48, arch/riscv/include/asm/pgtable.h).
    [randomize_stack_top] then subtracts up to [STACK_RND_MASK <<
    PAGE_SHIFT] — on riscv64 [0x3ffff] pages, just under 1 GiB
    (arch/riscv/include/asm/elf.h; note riscv OVERRIDES the generic 8
    MiB mask) — and the initial stack image sits above the SP.  So
    [sp_window_hi] is [STACK_TOP] itself and [sp_window_lo] is 2 GiB
    below it, covering the 1 GiB of randomization plus the largest
    image [valid_argv]/[valid_envp] admit, with margin.

    WHAT THIS DELIBERATELY LEAVES OUT, and why: an Sv39
    kernel puts [STACK_TOP] at [0x40_0000_0000] instead.  Covering both
    would make the window span the gap between two address-space sizes —
    255 GiB to 128 TiB — which is mostly a region no stack is ever in.
    The model is about the Sv48 configuration; on an Sv39 kernel it says
    nothing.

    Width costs the proofs nothing either way — every example reasons
    about [sp] symbolically, through these two bounds and the 16-byte
    alignment — so the window is narrow because a narrow one says
    something, not to save work. *)
Definition sp_window_lo : Z := 0x7fff80000000%Z.
Definition sp_window_hi : Z := 0x800000000000%Z.

(** Maximum ASLR displacement of the initial program break above the
    page-rounded image top ([reserved_top] of the LOAD reservations).
    THIS IS THE KERNEL'S OWN REACH, not a round number around it, and
    the derivation is the whole reason the constant is what it is.

    On Linux riscv64 [execve] first sets the break to the page-rounded
    top of the image, [ELF_PAGEALIGN] of [elf_brk] (fs/binfmt_elf.c,
    [load_elf_binary]).  With randomisation off ([randomize_va_space]
    there, the value has to exceed 1) that is where it stays, which is
    the band's floor.  With it on, the break moves one page up and is
    then displaced by [arch_randomize_brk] -> [randomize_page(_, SZ_1G)]
    (mm/util.c).  [randomize_page] turns the 1 GiB range into a count of
    pages and adds a whole number of pages STRICTLY BELOW that count —
    so the displacement is a multiple of the page size and is at most
    1 GiB minus one page.  It rounds a start that is not page-aligned up
    first, which this path never reaches, the start being the
    page-rounded image top plus a page; and that branch could only
    shorten the reach anyway, because it takes the rounding back out of
    the range before dividing.  One page up plus at most 1 GiB minus one
    page is exactly 1 GiB above the image top, and the largest draw
    attains it, so the reach is 1 GiB and that is this constant
    ([Run.valid_brk]).  Read at the citation baseline, Linux v6.18.46:
    [load_elf_binary] (fs/binfmt_elf.c:1330) sets the break to the
    page-rounded top, gates randomisation at fs/binfmt_elf.c:1332, adds
    the page at fs/binfmt_elf.c:1338 and calls [arch_randomize_brk] at
    fs/binfmt_elf.c:1340; [randomize_page] is mm/util.c:371-386 and
    [arch_randomize_brk] is mm/util.c:390-397.

    NOT ALL THREE ARE THE SAME AS THEY WERE AT v6.12.1.  [randomize_page] and
    [arch_randomize_brk] are unchanged, line numbers aside.
    [load_elf_binary]'s break block is NOT: at the baseline the
    static-PIE move is additionally gated on [CONFIG_COMPAT_BRK] being
    off, it sets [elf_brk] BEFORE the page-alignment rather than
    [mm->brk] after it, and it records a [brk_moved] flag that makes the
    one-page
    gap conditional instead of an else-arm.  None of that moves the
    bound.  For an [ET_EXEC] image the flag is false, so the gap applies
    and the reach is the image top plus exactly 1 GiB, as above.

    THE ONE PAGE UP IS NOT UNCONDITIONAL, and that is why this whole band
    is image-relative.  [load_elf_binary] (fs/binfmt_elf.c:1323-1329)
    has a second arm: for an [ET_DYN] image with no [PT_INTERP], on an
    architecture with [CONFIG_ARCH_HAS_ELF_RANDOMIZE] — riscv is one,
    through the [ARCH_WANT_DEFAULT_TOPDOWN_MMAP_LAYOUT] that
    arch/riscv/Kconfig:84 selects — and outside [CONFIG_COMPAT_BRK], the
    break is not bumped but MOVED, to [ELF_ET_DYN_BASE], which has
    nothing to do with where the image landed.  The arm the derivation
    above follows is the other one, the one-page gap.  The model takes
    that arm: it assumes the image is [ET_EXEC].  Nothing in
    these theories states that restriction, and [tools/elf_snapshot.py] never reads
    [e_type], so a static PIE can be snapshotted and run, and for one of
    those [Run.valid_brk] is false of the break Linux really gives it.
    That is a known gap.  It is not what this constant is about,
    but a reader of the derivation has to know which arm it assumes.

    WHY NOT WIDER.  A margin above the derivation is not a Linux behaviour:
    it admits initial breaks no supported implementation places, and one
    of them lands inside the low shadow the sealed ASan runtime reserves
    ([Checks/Cases/Mm/Mmap.v]), so statements about that runtime would
    be made under a placement that cannot occur.  Keeping the band
    to the kernel's own reach is design priority 2 (README.md), and it costs
    priority 3 nothing, because the region it excludes holds no placement
    any supported implementation produces.  qemu-user stays inside the
    band with room to spare, at the page-rounded image top, with no
    displacement at all.  [load_elf_image] (linux-user/elfload.c:3442,
    QEMU 8.2.2) puts it there, under the comment "Usual start for brk is
    after all sections of the main executable":

      info->brk = TARGET_PAGE_ALIGN(hiaddr + load_bias);

    The caller hands that value to [target_set_brk] (the call is at
    linux-user/main.c:990, QEMU 8.2.2), which stores it and does not
    move it: its body (linux-user/syscall.c:807, QEMU v8.2.10) is

      target_brk = TARGET_PAGE_ALIGN(new_brk);
      initial_target_brk = target_brk;

    That re-alignment is a no-op HERE and only here, because the value
    [load_elf_image] hands over is page-aligned already; the function
    itself makes no such promise about an arbitrary argument.  Nothing
    on the path randomises the break, so qemu-user sits at the band's
    floor.  QEMU is not vendored in this repository, so a reader
    following these citations fetches the release tree: elfload.c and
    main.c above read at 8.2.2, the [target_set_brk] body at v8.2.10,
    where the elfload.c line is 3478 and the main.c line is unchanged.

    Like the SP window, the break is quantified INDEPENDENTLY for the two
    binaries ([Equivalence.strong_universal_T]) — it is not snapshot data,
    and a target may not assume the source's break placement. *)
Definition brk_aslr_max : Z := (1 * 1024 * 1024 * 1024)%Z.

(** MMAP-BASE FLOOR: the smallest [mm->mmap_base] a covered kernel
    computes for a top-down layout under the configuration SCOPE.md
    names.  = 0x154555557000.

    riscv64 has no [arch_pick_mmap_layout] of its own — it selects
    [CONFIG_ARCH_WANT_DEFAULT_TOPDOWN_MMAP_LAYOUT]
    (arch/riscv/Kconfig:84, Linux v6.18.46, commit 1f99e9ab748f), so the
    generic one in mm/util.c:465-479 applies.  Its default (non-legacy)
    arm computes

      mm->mmap_base = mmap_base(random_factor, rlim_stack)

    with (mm/util.c:434-463, [mmap_base])

      gap  = rlim_stack->rlim_cur + stack_guard_gap [+ STACK_RND_MASK pages],
      gap  clamped to [MIN_GAP, MAX_GAP],
      base = PAGE_ALIGN(STACK_TOP - gap - rnd)

    where [MIN_GAP = SZ_128M], [MAX_GAP = STACK_TOP / 6 * 5]
    (mm/util.c:431-432), and [rnd = arch_mmap_rnd()] is [k] pages with
    [k < 2^vm.mmap_rnd_bits] (mm/util.c:399-411).  [stack_guard_gap] is
    a boot parameter of any page count (mm/mmap.c:941-954), so the gap
    reaches [MAX_GAP] even under the 8 MiB stack limit.

    THE NAMED ASSUMPTION (SCOPE.md, "Assumptions that the model does not
    check"): [vm.mmap_rnd_bits] is at most 24, or [stack_guard_gap] is
    at most 0x4aba6a2ab000 bytes (about 74.7 TiB,
    [Checks.Cases.MmapBase.floor_guard_max]).  The sysctl's range is
    [mmap_rnd_bits_min .. mmap_rnd_bits_max] (mm/mmap.c:1528-1536): 18
    (arch/riscv/Kconfig:260-262) up to [MMAP_VA_BITS - PAGE_SHIFT - 3]
    (arch/riscv/mm/init.c:850-853), which is 33 under Sv48.  Its boot
    value [CONFIG_ARCH_MMAP_RND_BITS] is at most
    [ARCH_MMAP_RND_BITS_MAX = 24] (arch/Kconfig:1208-1212,
    arch/riscv/Kconfig:269-271); only root raises it further.  With the
    Sv48 [STACK_TOP = 0x800000000000] this whole model assumes (see
    [sp_window_lo]) and 24 bits, the smallest value is

      PAGE_ALIGN(0x800000000000 - 0x800000000000/6*5 - 0xffffff000)
      = PAGE_ALIGN(0x155555555557 - 0xffffff000) = 0x154555557000.

    With more bits AND a larger guard (more than that bound at 33 bits,
    about 106.6 TiB at 25), Linux goes below it; with more bits and a
    smaller guard (the hardened [vm.mmap_rnd_bits = 33] with the default
    guard of 256 pages) it does not.  The legacy layout (an
    [ADDR_COMPAT_LAYOUT] personality or [vm.legacy_va_layout = 1],
    mm/util.c:413-425) puts the base at [TASK_UNMAPPED_BASE] =
    0x2aaaaab000 plus the draw (mm/util.c:472-474), which can be under
    this floor; SCOPE.md names the top-down layout as an assumption too.

    [Run.valid_mmap_base] admits any page-aligned base from this floor
    up to [mmap_base_max] below, and that band is EXACTLY the set of
    bases Linux gives under those assumptions:
    [Checks.Cases.MmapBase.sv48_band_is_linux_set] proves it against a
    Rocq statement of the computation above, and the examples next to it
    show that each assumption is needed.

    WHY NOT LOWER, to the smallest base Linux gives without the
    assumptions: no spec arm reads the base (placement is admissibility
    alone, see [Mmap.mmap_spec]'s placement section), but the ASan plan
    checker reads this floor.  [Common.AsanInit] starts its placement
    split at [AsanPlanCore.MBASE_MIN] = this value, and
    [AsanPlacement.kHighMemBeg_below_mmap_base_min] needs it above the
    ASan high shadow.  A lower floor would make those proofs false.  The
    predicate is also a conjunct of [Run.valid_entry] and a required step
    of [Equivalence.image_brk_satisfiable_entry], so neither it nor this
    constant may be removed. *)
Definition mmap_base_min : Z := 0x154555557000%Z.

(** MMAP-BASE CAP: the largest [mm->mmap_base] any covered kernel
    computes for a top-down layout.  = 0x7ffff8000000 = [STACK_TOP] -
    [MIN_GAP].

    The same [mmap_base] (mm/util.c, Linux v6.18.46, commit
    1f99e9ab748f) clamps [gap] UP to [MIN_GAP = SZ_128M] whenever the
    stack rlimit plus the guard and randomisation pad falls short of it,
    and [rnd] is never negative, so [PAGE_ALIGN(STACK_TOP - gap - rnd)]
    is largest — exactly [STACK_TOP - MIN_GAP] — when randomisation is
    off ([norandmaps], [randomize_va_space = 0], [ADDR_NO_RANDOMIZE])
    and the stack rlimit is at or below [MIN_GAP - stack_guard_gap].
    With the default 8 MiB rlimit, [PF_RANDOMIZE] and 18 bits of
    [mmap_rnd_bits], the band is [0x7fff7f702000, 0x7fffbf701000];
    every knob moves it down from this cap, never up.

    This cap is a fact about [mm->mmap_base], not about grants: a run's
    grants are bounded by ITS stack through [alloc_top], and a base
    admitted here may sit above that bound (see [alloc_top]'s note). *)
Definition mmap_base_max : Z := (sp_window_hi - 128 * 1024 * 1024)%Z.

(** THE TOP OF THE USER ADDRESS SPACE, [TASK_SIZE] = 0x800000000000 = 2^47:
    the limit riscv64's [access_ok] compares a user range against, and
    the bound [munmap] refuses a range past.  ONE exact constant, not a
    bracket, and every claim below is against stable Linux v6.18.46
    (commit 1f99e9ab748f).

    WHAT LINUX COMPARES AGAINST.  [__access_ok] is
    [(size <= TASK_SIZE_MAX) && (addr <= TASK_SIZE_MAX - size)]
    (include/asm-generic/access_ok.h, [__access_ok]), and that header
    defines [TASK_SIZE_MAX] as [TASK_SIZE] under [#ifndef TASK_SIZE_MAX].
    At that commit riscv defines no [TASK_SIZE_MAX] of its own —
    [git grep TASK_SIZE_MAX -- arch/riscv] is empty — so the fallback is
    what riscv64 uses.  [TASK_SIZE] for a 64-bit task is [TASK_SIZE_64] =
    [PGDIR_SIZE * PTRS_PER_PGD / 2] (arch/riscv/include/asm/pgtable.h,
    [TASK_SIZE_64]; the [CONFIG_COMPAT] split picks [TASK_SIZE_32] only
    when [is_compat_task()], i.e. [TIF_32BIT], which a 64-bit ELF never
    has — arch/riscv/include/asm/compat.h).  [PTRS_PER_PGD] is 512 and
    [PGDIR_SIZE] is [1 << PGDIR_SHIFT] with [PGDIR_SHIFT] read from the
    RUNTIME globals [pgtable_l4_enabled] / [pgtable_l5_enabled]
    (arch/riscv/include/asm/pgtable-64.h, [PGDIR_SHIFT]): 30, 39 or 48
    for Sv39, Sv48 or Sv57, so [TASK_SIZE] is 2^38, 2^47 or 2^56 for ONE
    kernel image depending on how it booted.  The depth is chosen by
    [set_satp_mode] (arch/riscv/mm/init.c): a hardware probe, narrowed
    by [no4lvl] / [no5lvl] on the command line
    (arch/riscv/kernel/pi/cmdline_early.c, [match_noXlvl]: [no5lvl]
    forces [SATP_MODE_48]) or by the device tree's [mmu-type].

    THE PREMISE, STATED ONCE: the kernel this model describes runs with
    Sv48 page tables, so [TASK_SIZE] is 2^47.  The address-space
    size is a declared parameter of the run ([VaSize] below,
    [ProcInput]'s [in_va_size]), so the premise is what the [Sv48]
    declaration asserts, and a statement declared otherwise is refused
    rather than answered against this number
    ([Equivalence.strong_equiv_va]).  It is a boot-time fact, not a
    property of the binary, and nothing a trace reveals can check
    it — a QEMU [virt] machine boots Linux at Sv57 unless told otherwise,
    where every value here would be 2^56 and this constant would answer
    -EFAULT throughout [(2^47, 2^56]] where Linux answers.  [no5lvl] on
    the kernel command line makes such a machine boot Sv48.  The same configuration is
    what the rest of this file is about ([sp_window_hi] is this
    number; the note above [valid_sp] says the model says nothing on an
    Sv39 kernel).  An Sv57 boot is outside the model rather than
    modeled wrongly.

    WHAT IT DECIDES.  [access_okb] below is [__access_ok] with this
    limit, so a range is refused exactly when its exact end is past 2^47:
    [access_ok(2^47, 0)] passes and [access_ok(2^47 + 1, 0)] and
    [access_ok(2^47 - 1, 2)] fail.  [Mmap.munmap_spec]'s range test is the same number through
    [do_vmi_munmap]'s [start > TASK_SIZE || len > TASK_SIZE-start ->
    -EINVAL] (mm/vma.c, [do_vmi_munmap]), which for a page-aligned start
    and a nonzero length is exactly [start + PAGE_ALIGN(len) > TASK_SIZE].

    LINUX HISTORY.  Commit ad5643cf2f69 ("riscv: Define TASK_SIZE_MAX for
    __access_ok()") made riscv64's [TASK_SIZE_MAX] the constant
    [LONG_MAX], first released in v6.10-rc1; commit 890ba5be6335
    reverted it — [get_user_pages_fast] accepts addresses in
    [[TASK_SIZE, LONG_MAX)] and [futex] reaches it — first released in
    v6.16-rc4 and backported to v6.12.36 and v6.15.5.  A kernel inside
    that window compares against [LONG_MAX], not [TASK_SIZE].  v6.18.46
    is outside it, so one exact constant is right here. *)
Definition TASK_SIZE : Z := 0x800000000000%Z.

(** * The address-space size as a declared parameter of the run

    [TASK_SIZE] above, [sp_window_hi] and everything derived from them
    are the Sv48 kernel's numbers, and the paragraphs above them say so
    at length.  What they could not say is WHICH kernel a particular
    statement is about: the size is a boot-time fact of the machine a
    task runs on, not a property of the binary, and a proof made under
    one size says nothing about another.  So the size is a value the
    task DECLARES, carried in [ProcInput] as [in_va_size] and pinned by
    [Run.valid_input] and its per-size variants, the way the abort
    declaration is; a statement's quantifier then names the kernel it
    speaks about, and a reader does not have to know that "the model"
    means Sv48.

    The three values are the three page-table depths riscv64 Linux can
    boot with ([set_satp_mode], arch/riscv/mm/init.c; the runtime
    globals [pgtable_l4_enabled] / [pgtable_l5_enabled] pick
    [PGDIR_SHIFT], arch/riscv/include/asm/pgtable-64.h).  Two numbers
    follow from the depth and they do NOT move together, which is the
    reason the functions below are separate rather than one table:

    - [va_task_size] is [TASK_SIZE_64 = PGDIR_SIZE * PTRS_PER_PGD / 2]
      (arch/riscv/include/asm/pgtable.h, [TASK_SIZE_64]): 2^38, 2^47 or
      2^56.  It is the limit [access_ok] and [munmap] compare against.
    - [va_stack_top] is [STACK_TOP = DEFAULT_MAP_WINDOW = 1 <<
      (MMAP_VA_BITS - 1)] (arch/riscv/include/asm/processor.h), and
      [MMAP_VA_BITS_64] is [VA_BITS] CAPPED AT 48
      (arch/riscv/include/asm/pgtable.h, [MMAP_VA_BITS_64]), so it is
      2^38 under Sv39 and 2^47 under BOTH Sv48 and Sv57: an Sv57 kernel
      places its stacks and its top-down mmap base exactly where an Sv48
      one does, and differs only in how far up a program may reach.
      All at Linux v6.18.46, commit 1f99e9ab748f.

    The window and the mmap band are derived from [va_stack_top] by the
    same arguments the Sv48 constants above spell out: the window is the
    top and 2 GiB below it, the cap is the top less [MIN_GAP].  Under
    Sv57 the floor is Sv48's too: [vm.mmap_rnd_bits] has the same range,
    because [mmap_rnd_bits_max] is [MMAP_VA_BITS - PAGE_SHIFT - 3]
    (arch/riscv/mm/init.c:850-853) and [MMAP_VA_BITS] is 48 for both.
    Under Sv39, [STACK_TOP - MAX_GAP] is under 2^36 while
    [arch_mmap_rnd] can subtract up to [(2^24 - 1)] pages (24 is
    [mmap_rnd_bits_max] there), so [mmap_base]'s own subtraction
    (mm/util.c:461) goes below zero and wraps in the kernel's unsigned
    arithmetic.  No program starts from a wrapped base: the vDSO cannot
    be placed and [execve] kills the task past its point of no return
    (the Sv39 section of [Checks.Cases.MmapBase] cites each step).  So
    the Sv39 instance admits every page-aligned base from 0 up to its
    cap, and [Checks.Cases.MmapBase.sv39_band_is_linux_set] proves that
    this is exactly the set of bases Linux gives that do not wrap.  One
    base of that set also starts no program: with a base of exactly 0
    the top-down search's top is [0 - 1] (mm/vma.h:502), so the vDSO
    search fails the same way.  The band keeps 0; this costs precision
    only, as no spec arm reads the base.

    WHAT THE DECLARATION BUYS TODAY, stated here so nobody reads more
    into it: the spec arms below still compare against [TASK_SIZE], the
    Sv48 constant, because that number is read at hundreds of sites
    through [access_okb] and the range tests, and the declared
    size is not threaded through them.  So the
    statements sealed under either other size are REFUSED rather than
    answered with the wrong limit: [Equivalence.strong_equiv_va] holds
    only of an [Sv48] input, and [Run.run] itself is the Sv48 run
    whatever the input declares -- which is why every obligation must
    be stated through the sealed families and not over [Run.run]
    directly.  The entry-state predicates ([Run.valid_sp_va] and its
    siblings) do read the declared size, so the window a statement
    quantifies over is the right one for its kernel even where the
    statement is refused. *)
Inductive VaSize := Sv39 | Sv48 | Sv57.

(** The two numbers that are not already named above, as literal
    constants: 2^38 is both
    [TASK_SIZE_64] and [STACK_TOP] under Sv39, 2^56 is [TASK_SIZE_64]
    under Sv57. *)
Definition sv39_task_size : Z := 0x4000000000%Z.
Definition sv57_task_size : Z := 0x100000000000000%Z.

(** [TASK_SIZE_64] per depth.  [Sv48] is [TASK_SIZE] itself, by
    definition and not by coincidence. *)
Definition va_task_size (v : VaSize) : Z :=
  match v with
  | Sv39 => sv39_task_size
  | Sv48 => TASK_SIZE
  | Sv57 => sv57_task_size
  end.

(** [STACK_TOP] per depth; [Sv48] and [Sv57] share it (see above), and
    under Sv39 it coincides with the whole user address space. *)
Definition va_stack_top (v : VaSize) : Z :=
  match v with
  | Sv39 => sv39_task_size
  | Sv48 => sp_window_hi
  | Sv57 => sp_window_hi
  end.

Definition va_sp_window_hi (v : VaSize) : Z := va_stack_top v.
Definition va_sp_window_lo (v : VaSize) : Z :=
  (va_stack_top v - 2 * 1024 * 1024 * 1024)%Z.

Definition va_mmap_base_max (v : VaSize) : Z :=
  (va_stack_top v - 128 * 1024 * 1024)%Z.
Definition va_mmap_base_min (v : VaSize) : Z :=
  match v with
  | Sv39 => 0%Z
  | Sv48 => mmap_base_min
  | Sv57 => mmap_base_min
  end.


(** ALLOCATION BUDGETS: the anonymous backing a run has committed
    ([State.vm_backing_used]) — the [vm_limit] each
    role's run is seeded with in [Equivalence.strong_equiv].  Fixed
    constants, so the out-of-memory point of a program with unbounded
    allocation is FORCED: no quantified value of the run moves the
    budget, and once it is spent only the failure resolutions remain.

    FORCED IS NOT A FUNCTION OF THE GRANT-AND-FREE HISTORY, and the
    stronger reading is false.  [live_bytes] sums the [vm_maps] entry
    sizes and those entries can overlap, so two runs granting and
    freeing the same sizes reach different totals depending on where the
    grants landed — [Checks.VmMapsDisjoint]'s
    [placement_changes_the_granted_byte_count] exhibits the pair.
    Placement does move the point.  What carries the obligation
    instead is that [Equivalence.equiv] compares whole trace SETS: the
    target must reproduce every OOM point the source can reach, not one
    canonical one.

    The TARGET budget is deliberately much larger than the source's:
    the headroom lets a target trade memory for simplicity (less
    compact data structures, auxiliary bookkeeping).  The flip side is
    that a target nearing the source's budget must SELF-LIMIT — take
    its failure path where the source's semantics forces failure — since
    trace equality forbids it succeeding where the source cannot.

    These are abstract backing guarantees, deliberately distinct from
    [TASK_SIZE], which bounds virtual address space.  Ordinary anonymous
    memory is charged when it becomes accessible.  MAP_NORESERVE is the
    exception: an accessible range is recorded as lazy and each page is
    charged atomically on its first successful instruction or syscall access.
    A PROT_NONE reservation occupies [vm_maps] and blocks overlapping
    placement but consumes no backing budget; making a non-NORESERVE slice
    read-write consumes the slice then.  The target's 512 GiB leaves the
    source's 16 GiB 32x headroom. *)
Definition source_alloc_limit : Z := 0x400000000%Z.   (* 16 GiB *)
Definition target_alloc_limit : Z := 0x8000000000%Z.  (* 512 GiB *)

(** a0 encodes a kernel error iff it is [-errno] for errno in [1,4095]
    (two's complement in 64 bits, i.e. unsigned in [2^64-4095, 2^64-1]). *)
Definition addr_is_error_b (ret : word) : bool :=
  Z.ltb (two_pow_64 - 4096) (bv_unsigned ret).

(** [-e] as the 64-bit return register value. *)
Definition errno_ret (e : Z) : word := Z_to_bv 64 (- e).

(** Errno values the model returns deterministically. *)
Definition EPERM  : Z := 1%Z.
Definition ENOENT : Z := 2%Z.
Definition ESRCH  : Z := 3%Z.
Definition EBADF  : Z := 9%Z.
Definition ECHILD : Z := 10%Z.
Definition EFAULT : Z := 14%Z.
Definition EEXIST : Z := 17%Z.
Definition ENOTDIR : Z := 20%Z.
Definition EISDIR : Z := 21%Z.
Definition EINVAL : Z := 22%Z.
Definition ENOTTY : Z := 25%Z.
Definition ESPIPE : Z := 29%Z.
Definition EPIPE  : Z := 32%Z.
Definition ERANGE : Z := 34%Z.
Definition ENAMETOOLONG : Z := 36%Z.
Definition ENOTEMPTY : Z := 39%Z.

(** Errno values the per-syscall failure-injection sets draw from
    (see [Syscall.errno_from] and the [*_errnos] lists).  EINVAL above is
    NOT among them: every syscall that can return it does so
    deterministically, from arguments the model reads.

    WHICH BLOCK A VALUE SITS IN IS PROSE, NOT A FACT ANYTHING READS.  The
    split records how the modeled surface uses each errno today, and it
    stops being true the moment a syscall uses one the other way.  Three
    values already break it: EPERM, which the credential specs return
    deterministically while [Namei.unlinkat_errnos] also draws it as an
    alternative, and ENOENT and ENAMETOOLONG, which several specs return
    deterministically while [DPath.getcwd_errnos] draws both — a value
    can be both, and the split cannot say so.  [Kernel.Sys.setsid_spec] is a
    THIRD shape the split has no room for: it offers EPERM as one arm of
    an [alt] until a setsid has succeeded and returns it deterministically
    after, so the same value is alternative and deterministic in the same
    spec, decided by state rather than by arguments — and it is drawn from
    no [*_errnos] list at all.  Nothing depends on the
    placement; the load-bearing facts are the VALUE and the [*_errnos]
    list that names it. *)
Definition EINTR  : Z := 4%Z.
Definition ENOMEM : Z := 12%Z.
Definition EACCES : Z := 13%Z.
Definition EBUSY  : Z := 16%Z.
Definition ENFILE : Z := 23%Z.
Definition EMFILE : Z := 24%Z.
Definition EROFS  : Z := 30%Z.

(** Other Errno values *)
(* Injected on exactly one shape: a credential setter that moves the REAL
   uid, where the kernel's [set_user] and [set_cred_ucounts] allocate and
   can fail (see [Kernel.Sys.setid_errnos]).  It is deliberately NOT in
   any other syscall's injection set — admitting a blocking-style EAGAIN
   where no kernel produces one would add nondeterminism a target could
   hide behavior in, and programs handle it inconsistently anyway. *)
Definition EAGAIN : Z := 11%Z.

(** Socket errno values.  All from the asm-generic table
    (include/uapi/asm-generic/errno.h and errno-base.h, v6.12), which
    riscv64 uses unchanged — arch/riscv has no errno.h of its own, and
    include/uapi/asm-generic/Kbuild lists errno.h as mandatory-y, so the
    generic header is the one that applies. *)
Definition ENOTSOCK        : Z := 88%Z.
Definition EMSGSIZE        : Z := 90%Z.
Definition ENOPROTOOPT     : Z := 92%Z.
Definition EPROTONOSUPPORT : Z := 93%Z.
Definition ESOCKTNOSUPPORT : Z := 94%Z.
Definition EOPNOTSUPP      : Z := 95%Z.
Definition EAFNOSUPPORT    : Z := 97%Z.
Definition EADDRINUSE      : Z := 98%Z.
Definition ECONNRESET      : Z := 104%Z.
Definition EISCONN         : Z := 106%Z.
Definition ENOTCONN        : Z := 107%Z.
Definition ETIMEDOUT       : Z := 110%Z.

(** The one value in this block NO spec returns.  It names the canonical
    outcome of the connection attempt [Net.Socket.connect_spec] declines,
    so that [Checks.Cases.Net.Socket] can pin that the declined arm
    answers [Unmodeled] to a real errno rather than to a bare 111. *)
Definition ECONNREFUSED    : Z := 111%Z.

(* =========================================================================
   Syscall inputs and effects
   ========================================================================= *)

Record SyscallInput := mkInput {
  in_sysno : word;              (* a7 at ecall *)
  in_args  : list word;         (* a0..a5 at ecall (decoded register values) *)
  in_mem   : word -> option byte; (* pre-syscall memory: byte-level
                               [addr -> option byte], writable memory merged
                               over ROM (exactly what the process can read);
                               [None] = address not mapped.  Used for syscall
                               SOURCE buffers (write data, openat paths),
                               which may live in .rodata. *)
  in_wmem  : word -> option byte; (* the WRITABLE view: the writable overlay
                               merged over writable ('w') segments only —
                               exactly the addresses the kernel may write into
                               ([RiscvSemantics.ms_writable_byte]).  Syscall
                               OUTPUT buffers (read/getrandom destinations)
                               must be fully defined here, the analogue of the
                               kernel's copy_to_user EFAULT check; an output
                               buffer that is unmapped or read-only is
                               [unmodeled] (fail closed), except that [read]
                               answers [-EFAULT] when not even the FIRST byte
                               it would deliver can land, as the kernel does
                               (see [ReadWrite.read_spec]). *)
}.

Definition in_arg (i : SyscallInput) (k : nat) : word :=
  nth k (in_args i) (Z_to_bv 64 0).

(** One symbolic memory copy.  Keeping the preserved prefix of a moved
    anonymous mapping as three words, rather than materializing its bytes,
    makes large [mremap] effects O(1). *)
Record MemCopy := mkCopy {
  copy_src : word;
  copy_dst : word;
  copy_len : word;
}.

(** What a syscall does to the machine: the a0 return value, the byte
    ranges it writes into user memory, the ranges it ZERO-FILLS
    (anonymous grants, mprotect exposure, and mremap growth), the ranges it
    UNMAPS (munmap, mremap, and PROT_NONE mappings), and the ranges it copies
    from a pre-effect snapshot.
    [Run.apply_effect] applies these deterministically; everything else
    (other GPRs, SP, PC, ROM, all other memory) is preserved by
    construction.

    [eff_zeros] ranges are (base, size) pairs — kept symbolic rather than
    materialized as byte lists so a multi-megabyte grant stays O(1) in
    the spec, the checker, and proofs.

    [eff_unmaps] is NOT expressible as a write: every covered byte
    becomes UNMAPPED ([None] in the writable overlay), so a later load
    from it faults — as a real munmapped page does — instead of reading
    stale bytes.  munmap, mremap, every successful PROT_NONE mmap, and a
    brk SHRINK (the freed page-aligned heap tail) emit it;
    [Run.apply_effect] erases the
    ranges before zeros and writes are applied.

    [eff_copies] snapshots its sources from the PRE-EFFECT memory.  This is
    essential for a moved [mremap]: the old range is unmapped by the same
    effect, but its preserved prefix must still be installed at the new
    address.  [Run.apply_effect] applies unmaps, then zeros, then these
    snapshot copies, then ordinary writes.

    [eff_copyins] records ranges that the syscall already read from user
    memory while selecting this outcome.  It is outcome data because the same
    errno can be returned either before or after a copy_from_user. *)
Record SyscallEffect := mkEffectU {
  eff_ret    : word;
  eff_writes : list (word * list byte); (* (base address, bytes), applied in order *)
  eff_zeros  : list (word * word);      (* (base address, size) zero-filled ranges *)
  eff_unmaps : list (word * word);      (* (base address, size) unmapped ranges *)
  eff_copies : list MemCopy;            (* pre-effect (source, destination, size) copies *)
  eff_copyins : list (word * nat)       (* ranges already read from user memory *)
}.

(** The common no-unmap/no-copy/no-copyin domain convenience. *)
Abbreviation mkEffect r ws zs := (mkEffectU r ws zs [] [] []).

Definition with_copyins (reads : list (word * nat)) (eff : SyscallEffect)
    : SyscallEffect :=
  mkEffectU (eff_ret eff) (eff_writes eff) (eff_zeros eff)
    (eff_unmaps eff) (eff_copies eff) reads.

(* =========================================================================
   Reading user memory (buffers and NUL-terminated strings)
   ========================================================================= *)

(** Read [len] consecutive bytes starting at [a], or [None] if any byte in
    the range is unmapped.  Addresses advance with wrapping [bv] addition
    (a buffer straddling the top of the
    address space is not something a real process can hand the kernel). *)
Fixpoint read_bytes_aux (mp : word -> option byte) (a : word) (k : nat)
    : option (list byte) :=
  match k with
  | O => Some []
  | S k' =>
      match mp a with
      | None => None
      | Some b => match read_bytes_aux mp (a + 1) k' with
                  | Some r => Some (b :: r)
                  | None => None
                  end
      end
  end.

(** [read_bytes_aux] is the shape proofs use, and NOT what the checker
    may execute on a long range: the recursion rebuilds its list on the
    way OUT, one stack frame per byte, and the extracted checker dies of
    that between 2^17 and 2^18 frames on an OCaml 4 runtime, and pays
    for it in quadratic TIME rather than dying on the OCaml 5 the opam
    file requires — which
    the read count window
    makes reachable, since a delivered prefix may be
    [MAX_RW_COUNT] long.  [read_bytes_map] therefore EXECUTES as a
    chunked accumulator loop: [read_bytes_acc] extends its accumulator
    with the walked bytes REVERSED and returns through a tail call, the
    chunk loop hands the fuel out [wmem_chunk] bytes at a time so no
    unary numeral scales with the length either (the depth a Peano
    conversion survives is a property of the OCaml runtime
    configuration, which nothing here fixes),
    and one [rev_append] at the end restores byte order.
    [read_bytes_map_eq] is the equation every proof goes through;
    nothing outside this block unfolds [read_bytes_map]'s body. *)
Definition wmem_chunk : Z := 4096%Z.

Fixpoint read_bytes_acc (mp : word -> option byte) (a : word) (k : nat)
    (acc : list byte) : option (list byte) :=
  match k with
  | O => Some acc
  | S k' => match mp a with
            | None => None
            | Some b => read_bytes_acc mp (a + 1) k' (b :: acc)
            end
  end.

Fixpoint read_bytes_chunks (mp : word -> option byte) (a : word)
    (q k : nat) (acc : list byte) : option (list byte) :=
  match q with
  | O => Some acc
  | S q' => match read_bytes_acc mp a k acc with
            | None => None
            | Some acc' => read_bytes_chunks mp (a + nat_to_word k) q' k acc'
            end
  end.

Definition read_bytes_map (mp : word -> option byte) (a len : word)
    : option (list byte) :=
  let n := bv_unsigned len in
  match read_bytes_chunks mp a (Z.to_nat (n / wmem_chunk))
          (Z.to_nat wmem_chunk) [] with
  | None => None
  | Some acc =>
      match read_bytes_acc mp (a + Z_to_bv 64 (n / wmem_chunk * wmem_chunk))
              (Z.to_nat (n mod wmem_chunk)) acc with
      | None => None
      | Some acc' => Some (rev_append acc' [])
      end
  end.

Lemma read_bytes_acc_aux : forall mp k a acc,
  read_bytes_acc mp a k acc
  = match read_bytes_aux mp a k with
    | None => None
    | Some w => Some (rev_append w acc)
    end.
Proof.
  induction k as [|k IH]; intros a acc; cbn; [reflexivity|].
  destruct (mp a); [|reflexivity]. rewrite IH.
  destruct (read_bytes_aux mp (a + 1) k); reflexivity.
Qed.

Lemma read_bytes_aux_split : forall mp j k a,
  read_bytes_aux mp a (j + k)
  = match read_bytes_aux mp a j with
    | None => None
    | Some w1 =>
        match read_bytes_aux mp (a + nat_to_word j) k with
        | None => None
        | Some w2 => Some (w1 ++ w2)
        end
    end.
Proof.
  induction j as [|j IH]; intros k a; cbn [read_bytes_aux Nat.add].
  - replace (a + nat_to_word 0)%bv with a.
    2: { apply bv_eq. unfold nat_to_word.
         rewrite bv_add_unsigned, Z_to_bv_unsigned.
         change (Z.of_nat 0) with 0%Z.
         rewrite bv_wrap_0, Z.add_0_r.
         rewrite bv_wrap_small; [reflexivity|apply bv_unsigned_in_range]. }
    destruct (read_bytes_aux mp a k); reflexivity.
  - destruct (mp a); [|reflexivity].
    rewrite IH.
    replace (a + 1 + nat_to_word j)%bv with (a + nat_to_word (S j))%bv.
    2: { apply bv_eq. unfold nat_to_word.
         rewrite !bv_add_unsigned, !Z_to_bv_unsigned.
         rewrite Nat2Z.inj_succ.
         change (bv_unsigned (1 : word)) with 1%Z.
         unfold bv_wrap.
         rewrite !Zplus_mod_idemp_r, !Zplus_mod_idemp_l.
         f_equal. lia. }
    destruct (read_bytes_aux mp (a + 1) j) as [w1|]; [|reflexivity].
    destruct (read_bytes_aux mp (a + nat_to_word (S j)) k) as [w2|];
      reflexivity.
Qed.

Lemma rev_append_app : forall (A : Type) (l1 l2 acc : list A),
  rev_append (l1 ++ l2) acc = rev_append l2 (rev_append l1 acc).
Proof. induction l1; intros; cbn; [reflexivity|apply IHl1]. Qed.

Lemma read_bytes_chunks_flat : forall mp q k a acc,
  read_bytes_chunks mp a q k acc
  = match read_bytes_aux mp a (q * k) with
    | None => None
    | Some w => Some (rev_append w acc)
    end.
Proof.
  induction q as [|q IH]; intros k a acc; cbn [read_bytes_chunks Nat.mul];
    [reflexivity|].
  rewrite read_bytes_aux_split, read_bytes_acc_aux.
  destruct (read_bytes_aux mp a k) as [w1|]; [|reflexivity].
  rewrite IH.
  destruct (read_bytes_aux mp (a + nat_to_word k) (q * k)) as [w2|];
    [|reflexivity].
  now rewrite rev_append_app.
Qed.

Lemma read_bytes_map_eq : forall mp a len,
  read_bytes_map mp a len = read_bytes_aux mp a (word_to_nat len).
Proof.
  intros mp a len. unfold read_bytes_map. cbv zeta.
  rewrite read_bytes_chunks_flat.
  pose proof (bv_unsigned_in_range 64 len) as Hr.
  unfold bv_modulus in Hr.
  set (n := bv_unsigned len) in *.
  assert (Hq : (0 <= n / wmem_chunk)%Z)
    by (apply Z.div_pos; [lia|unfold wmem_chunk; lia]).
  assert (Hm : (0 <= n mod wmem_chunk < wmem_chunk)%Z)
    by (apply Z.mod_pos_bound; unfold wmem_chunk; lia).
  replace (a + Z_to_bv 64 (n / wmem_chunk * wmem_chunk))%bv
    with (a + nat_to_word (Z.to_nat (n / wmem_chunk) * Z.to_nat wmem_chunk))%bv.
  2: { apply bv_eq. unfold nat_to_word.
       rewrite !bv_add_unsigned, !Z_to_bv_unsigned.
       rewrite Nat2Z.inj_mul, !Z2Nat.id by (unfold wmem_chunk in *; lia).
       reflexivity. }
  pose proof (read_bytes_aux_split mp
                (Z.to_nat (n / wmem_chunk) * Z.to_nat wmem_chunk)
                (Z.to_nat (n mod wmem_chunk)) a) as Hsplit.
  replace (Z.to_nat (n / wmem_chunk) * Z.to_nat wmem_chunk
           + Z.to_nat (n mod wmem_chunk))%nat
    with (word_to_nat len) in Hsplit.
  2: { unfold word_to_nat.
       rewrite <- Z2Nat.inj_mul by (unfold wmem_chunk in *; lia).
       rewrite <- Z2Nat.inj_add
         by (try apply Z.mul_nonneg_nonneg; unfold wmem_chunk in *; lia).
       f_equal. rewrite Z.mul_comm. fold n. apply Z.div_mod.
       unfold wmem_chunk; lia. }
  rewrite Hsplit.
  destruct (read_bytes_aux mp a
              (Z.to_nat (n / wmem_chunk) * Z.to_nat wmem_chunk))
    as [w1|]; [|reflexivity].
  rewrite read_bytes_acc_aux.
  destruct (read_bytes_aux mp
              (a + nat_to_word (Z.to_nat (n / wmem_chunk)
                                * Z.to_nat wmem_chunk))
              (Z.to_nat (n mod wmem_chunk))) as [w2|]; [|reflexivity].
  rewrite !rev_append_rev, !app_nil_r.
  rewrite rev_app_distr, !rev_involutive. reflexivity.
Qed.

(** The longest READABLE PREFIX of [a, a+len): the consecutive mapped
    bytes starting at [a], stopping at the first unmapped byte (or at
    [len]).  This is what a real kernel's copy_from_user can move before
    faulting — see [ReadWrite.write_spec]'s short-write semantics.

    [readable_bytes_aux] is the shape proofs use, and — exactly as with
    [read_bytes_aux] above — NOT what the checker may execute on a long
    range: it rebuilds its list on the way OUT, one stack frame per byte,
    and it converts [len] to a unary numeral before the first memory
    lookup.  Both costs scale with the COUNT a [write] names, and the
    write direction does not bound that count by [Uaccess.rw_bytes_max];
    the execution shape below is what makes that safe. *)
Fixpoint readable_bytes_aux (mp : word -> option byte) (a : word) (k : nat)
    : list byte :=
  match k with
  | O => []
  | S k' =>
      match mp a with
      | None => []
      | Some b => b :: readable_bytes_aux mp (a + 1) k'
      end
  end.

Lemma readable_bytes_aux_length_le : forall mp k a,
  (length (readable_bytes_aux mp a k) <= k)%nat.
Proof.
  induction k as [|k IH]; intros a; cbn; [lia|].
  destruct (mp a); cbn; [|lia]. specialize (IH (a + 1)%bv). lia.
Qed.

(** [readable_bytes] EXECUTES as the chunked accumulator loop
    [read_bytes_map] carries, with one extra thing to carry: this walk
    may STOP EARLY, so the accumulator pair reports whether the [k] bytes
    it was given were all mapped.  [false] is what ends the chunk loop —
    the prefix is complete at that point and no later chunk can extend
    it.  The [k]-byte inner walk is where the stack depth is spent, and
    it is [wmem_chunk], not [len]; the only unary numeral that scales
    with [len] is the chunk COUNT, which is [wmem_chunk] times smaller.
    One [rev_append] at the end restores byte order.

    [readable_bytes_eq] is the equation every proof goes through; nothing
    outside this block unfolds [readable_bytes]'s body. *)
Fixpoint readable_bytes_acc (mp : word -> option byte) (a : word) (k : nat)
    (acc : list byte) : bool * list byte :=
  match k with
  | O => (true, acc)
  | S k' =>
      match mp a with
      | None => (false, acc)
      | Some b => readable_bytes_acc mp (a + 1) k' (b :: acc)
      end
  end.

Fixpoint readable_bytes_chunks (mp : word -> option byte) (a : word)
    (q k : nat) (acc : list byte) : bool * list byte :=
  match q with
  | O => (true, acc)
  | S q' =>
      match readable_bytes_acc mp a k acc with
      | (false, acc') => (false, acc')
      | (true, acc') => readable_bytes_chunks mp (a + nat_to_word k) q' k acc'
      end
  end.

Definition readable_bytes (mp : word -> option byte) (a len : word)
    : list byte :=
  let n := bv_unsigned len in
  match readable_bytes_chunks mp a (Z.to_nat (n / wmem_chunk))
          (Z.to_nat wmem_chunk) [] with
  | (false, acc) => rev_append acc []
  | (true, acc) =>
      rev_append (snd (readable_bytes_acc mp
                         (a + Z_to_bv 64 (n / wmem_chunk * wmem_chunk))
                         (Z.to_nat (n mod wmem_chunk)) acc)) []
  end.

Lemma readable_bytes_acc_flat : forall mp k a acc,
  readable_bytes_acc mp a k acc
  = (Nat.eqb (length (readable_bytes_aux mp a k)) k,
     rev_append (readable_bytes_aux mp a k) acc).
Proof.
  induction k as [|k IH]; intros a acc; cbn [readable_bytes_acc readable_bytes_aux];
    [reflexivity|].
  destruct (mp a) as [b|]; [|reflexivity].
  rewrite IH. reflexivity.
Qed.

(** Splitting the walk at [j]: the second part is reached exactly when
    the first ran to its full length — one unmapped byte in the first
    [j] ends the whole prefix. *)
Lemma readable_bytes_aux_split : forall mp j k a,
  readable_bytes_aux mp a (j + k)
  = if Nat.eqb (length (readable_bytes_aux mp a j)) j
    then readable_bytes_aux mp a j ++ readable_bytes_aux mp (a + nat_to_word j) k
    else readable_bytes_aux mp a j.
Proof.
  induction j as [|j IH]; intros k a; cbn [readable_bytes_aux Nat.add].
  - replace (a + nat_to_word 0)%bv with a; [reflexivity|].
    apply bv_eq. unfold nat_to_word.
    rewrite bv_add_unsigned, Z_to_bv_unsigned.
    change (Z.of_nat 0) with 0%Z.
    rewrite bv_wrap_0, Z.add_0_r.
    rewrite bv_wrap_small; [reflexivity|apply bv_unsigned_in_range].
  - destruct (mp a) as [b|]; [|reflexivity].
    rewrite IH.
    replace (a + 1 + nat_to_word j)%bv with (a + nat_to_word (S j))%bv.
    2: { apply bv_eq. unfold nat_to_word.
         rewrite !bv_add_unsigned, !Z_to_bv_unsigned.
         rewrite Nat2Z.inj_succ.
         change (bv_unsigned (1 : word)) with 1%Z.
         unfold bv_wrap.
         rewrite !Zplus_mod_idemp_r, !Zplus_mod_idemp_l.
         f_equal. lia. }
    cbn [length Nat.eqb].
    destruct (Nat.eqb (length (readable_bytes_aux mp (a + 1) j)) j);
      reflexivity.
Qed.

Lemma readable_bytes_chunks_flat : forall mp q k a acc,
  readable_bytes_chunks mp a q k acc
  = (Nat.eqb (length (readable_bytes_aux mp a (q * k))) (q * k),
     rev_append (readable_bytes_aux mp a (q * k)) acc).
Proof.
  induction q as [|q IH]; intros k a acc;
    cbn [readable_bytes_chunks Nat.mul]; [reflexivity|].
  rewrite readable_bytes_acc_flat.
  pose proof (readable_bytes_aux_length_le mp k a) as Hle.
  rewrite readable_bytes_aux_split.
  destruct (Nat.eqb (length (readable_bytes_aux mp a k)) k) eqn:Hk.
  - rewrite IH, rev_append_app, length_app.
    apply Nat.eqb_eq in Hk. rewrite Hk.
    f_equal.
    destruct (Nat.eqb (length (readable_bytes_aux mp (a + nat_to_word k) (q * k)))
                      (q * k)) eqn:E; symmetry.
    + apply Nat.eqb_eq. apply Nat.eqb_eq in E. lia.
    + apply Nat.eqb_neq. apply Nat.eqb_neq in E. lia.
  - apply Nat.eqb_neq in Hk.
    replace (Nat.eqb (length (readable_bytes_aux mp a k)) (k + q * k)) with false;
      [reflexivity|].
    symmetry. apply Nat.eqb_neq. lia.
Qed.

Lemma readable_bytes_eq : forall mp a len,
  readable_bytes mp a len = readable_bytes_aux mp a (word_to_nat len).
Proof.
  intros mp a len. unfold readable_bytes. cbv zeta.
  rewrite readable_bytes_chunks_flat.
  pose proof (bv_unsigned_in_range 64 len) as Hr.
  unfold bv_modulus in Hr.
  set (n := bv_unsigned len) in *.
  assert (Hq : (0 <= n / wmem_chunk)%Z)
    by (apply Z.div_pos; [lia|unfold wmem_chunk; lia]).
  assert (Hm : (0 <= n mod wmem_chunk < wmem_chunk)%Z)
    by (apply Z.mod_pos_bound; unfold wmem_chunk; lia).
  replace (a + Z_to_bv 64 (n / wmem_chunk * wmem_chunk))%bv
    with (a + nat_to_word (Z.to_nat (n / wmem_chunk) * Z.to_nat wmem_chunk))%bv.
  2: { apply bv_eq. unfold nat_to_word.
       rewrite !bv_add_unsigned, !Z_to_bv_unsigned.
       rewrite Nat2Z.inj_mul, !Z2Nat.id by (unfold wmem_chunk in *; lia).
       reflexivity. }
  pose proof (readable_bytes_aux_split mp
                (Z.to_nat (n / wmem_chunk) * Z.to_nat wmem_chunk)
                (Z.to_nat (n mod wmem_chunk)) a) as Hsplit.
  replace (Z.to_nat (n / wmem_chunk) * Z.to_nat wmem_chunk
           + Z.to_nat (n mod wmem_chunk))%nat
    with (word_to_nat len) in Hsplit.
  2: { unfold word_to_nat.
       rewrite <- Z2Nat.inj_mul by (unfold wmem_chunk in *; lia).
       rewrite <- Z2Nat.inj_add
         by (try apply Z.mul_nonneg_nonneg; unfold wmem_chunk in *; lia).
       f_equal. rewrite Z.mul_comm. fold n. apply Z.div_mod.
       unfold wmem_chunk; lia. }
  destruct (Nat.eqb (length (readable_bytes_aux mp a
                       (Z.to_nat (n / wmem_chunk) * Z.to_nat wmem_chunk)))
                    (Z.to_nat (n / wmem_chunk) * Z.to_nat wmem_chunk)) eqn:Hfull.
  - cbn [snd]. rewrite readable_bytes_acc_flat. cbn [snd].
    rewrite Hsplit, !rev_append_rev, !app_nil_r.
    rewrite rev_app_distr, !rev_involutive. reflexivity.
  - rewrite Hsplit, !rev_append_rev, !app_nil_r, rev_involutive. reflexivity.
Qed.

(** The readable prefix never exceeds the requested count. *)
Lemma readable_bytes_length_le : forall mp a len,
  (Z.of_nat (length (readable_bytes mp a len)) <= bv_unsigned len)%Z.
Proof.
  intros mp a len. rewrite readable_bytes_eq. unfold word_to_nat.
  pose proof (readable_bytes_aux_length_le mp (Z.to_nat (bv_unsigned len)) a).
  destruct (bv_unsigned_in_range _ len). lia.
Qed.

(** Linux PATH_MAX: a pathname's content may be at most 4095 bytes, i.e.
    4096 counting the NUL — [path_max] is the bound Linux's [getname()]
    enforces, and it counts the terminator, so a 4095-byte path plus its
    NUL fits and a 4096-byte one does not. *)
Definition path_max : nat := 4096%nat.

(** Pathname bytes counted as read: through the first NUL, the first
    unreadable byte, or [path_max].  This is the count the model records,
    and it is SHORTER than what [getname()] issues —
    [strncpy_from_user] loads whole words, so it runs past the NUL to the
    end of that word (lib/strncpy_from_user.c, [do_strncpy_from_user];
    byte-identical v6.10 through v6.16 — the FILE is not, so the window
    belongs to the function).  The answer is unaffected: that loop is clamped
    below TASK_SIZE and falls back to a byte loop when a word load faults,
    so no verdict moves.  Only the recorded read set is short. *)
Fixpoint cstr_access_len_aux (mp : word -> option byte) (a : word) (fuel : nat)
    : nat :=
  match fuel with
  | O => O
  | S fuel' =>
      match mp a with
      | None => 1%nat
      | Some b =>
          if bv_eqb b (Z_to_bv 8 0) then 1%nat
          else S (cstr_access_len_aux mp (a + 1) fuel')
      end
  end.

(** Reading a pathname out of user memory has three outcomes, and Linux
    distinguishes all three: the string, [-ENAMETOOLONG] (no NUL within
    PATH_MAX), and [-EFAULT] (an unmapped byte before the NUL).  Both
    failures are ordinary kernel returns, NOT modeling gaps — keeping
    them apart is what lets [Open.openat_spec] answer an errno instead
    of declining to interpret the call. *)
Inductive cstr_result :=
| CstrOk (p : list byte)   (* NUL-terminated within PATH_MAX *)
| CstrTooLong              (* no NUL within PATH_MAX        -> -ENAMETOOLONG *)
| CstrFault.               (* unmapped byte before the NUL  -> -EFAULT *)

Fixpoint read_cstr_aux (mp : word -> option byte) (a : word) (k : nat)
    : cstr_result :=
  match k with
  | O => CstrTooLong             (* no NUL within the length bound *)
  | S k' =>
      match mp a with
      | None => CstrFault        (* unmapped byte before the NUL *)
      | Some b =>
          if bv_eqb b (Z_to_bv 8 0) then CstrOk []
          else match read_cstr_aux mp (a + 1) k' with
               | CstrOk r => CstrOk (b :: r)
               | r => r          (* propagate the failure verbatim *)
               end
      end
  end.

Definition read_cstr (mp : word -> option byte) (a : word)
    : cstr_result :=
  read_cstr_aux mp a path_max.

(** Read one little-endian 64-bit word at [a] ([BvBase.le_bytes_to_word]
    decodes index 0 as least significant), or [None] if any of the 8
    bytes is unmapped — for reading 8-byte fields of in-memory kernel
    structures (the iovec array of readv/writev). *)
Definition read_u64 (mp : word -> option byte) (a : word) : option word :=
  match read_bytes_map mp a (Z_to_bv 64 8) with
  | Some bs => Some (le_bytes_to_word bs)
  | None => None
  end.

(** Read [cnt] [struct iovec] entries starting at [a] — on LP64 each is
    16 bytes: [iov_base] then [iov_len], both 8-byte little-endian words
    — or [None] if any byte of the array is unmapped.

    This is the layout decode ALONE: no length or address validation.
    Both specs import through [copy_iovecs_aux] below, which walks the
    same layout and additionally answers [ImpFault]/[ImpInval], so
    nothing in the model calls this.  Its consumer is a caller of the
    extracted checker, which must decide which guest ranges to capture
    BEFORE it knows whether the import succeeds — a validating decoder
    would hand it nothing for exactly the traces the model then needs
    memory for.  It is an explicit extraction root for that reason
    (Checks/Extraction.v).  The entry point that turns a word count into
    [k] is [read_iovecs], stated below [IOV_MAX] because it bounds the
    count by it. *)
Fixpoint read_iovecs_aux (mp : word -> option byte) (a : word) (k : nat)
    : option (list (word * word)) :=
  match k with
  | O => Some []
  | S k' =>
      match read_u64 mp a, read_u64 mp (a + 8) with
      | Some base, Some len =>
          match read_iovecs_aux mp (a + 16) k' with
          | Some r => Some ((base, len) :: r)
          | None => None
          end
      | _, _ => None
      end
  end.

(** Linux caps the aggregate transfer described by an iovec array at
    [MAX_RW_COUNT = 0x7ffff000] (include/linux/fs.h, [MAX_RW_COUNT] =
    [INT_MAX & PAGE_MASK], v6.18.46).  Keep the cap here, next to the
    structural helpers which consume it, so readv's trusted spec and
    executable checker cannot drift apart.

    [INT_MAX & PAGE_MASK] is a HOST property: Linux computes this from the
    page size the running kernel booted with, so the literal below is the
    4 KiB-page value, and a 16 KiB or 64 KiB host clamps lower
    (0x7fffc000, 0x7fff0000) than this constant names.  4 KiB-page hosts
    are therefore the honest scope of the constant, and that is a scope of
    the model rather than a bug to fix here: making it configurable would
    put a host property into a model constant. *)
Definition MAX_RW_COUNT : Z := 0x7ffff000%Z.

(** The SCALAR form of the same clamp: a plain read or write is capped
    at [MAX_RW_COUNT] before the transfer —
    [if (count > MAX_RW_COUNT) count = MAX_RW_COUNT;] in [vfs_read]
    (fs/read_write.c:566-567) and [vfs_write] (:680-681), both at
    v6.18.46 — after [access_ok] and [rw_verify_area] and ahead of the
    [->read]/[->write] dispatch, so the caller of an over-clamp count
    sees a SHORT transfer, not an error.  Computed in [Z]; the result is
    at most [MAX_RW_COUNT], far under 2^64, so a use site may re-enter
    [word] with [Z_to_bv] without wrapping.

    EVERY SCALAR TRANSFER ARM CONSUMES IT, on both directions: on the read
    side [Fs.ReadWrite.read_spec]'s channel, file, socket and pipe
    arms, and [pread64_spec]; on the write side every arm, where
    [Uaccess.write_source] is the clamped source prefix, including
    [pwrite64_spec], which reads its source through [write_source] like
    the rest. *)
Definition rw_count_clamp (count : word) : Z :=
  Z.min (bv_unsigned count) MAX_RW_COUNT.

Lemma rw_count_clamp_small : forall count,
  (bv_unsigned count <= MAX_RW_COUNT)%Z ->
  rw_count_clamp count = bv_unsigned count.
Proof. intros count H. unfold rw_count_clamp. lia. Qed.

Lemma rw_count_clamp_range : forall count,
  (0 <= rw_count_clamp count <= MAX_RW_COUNT)%Z.
Proof.
  intros count. unfold rw_count_clamp, MAX_RW_COUNT.
  pose proof (bv_unsigned_in_range 64 count). lia.
Qed.

(** The clamped count re-entered as a [word].  [MAX_RW_COUNT] is far under
    2^64, so the round trip is the identity and a spec may name the
    clamped transfer as a [word] without a wrapping side condition. *)
Lemma rw_count_clamp_word : forall count,
  bv_unsigned (Z_to_bv 64 (rw_count_clamp count)) = rw_count_clamp count.
Proof.
  intros count. pose proof (rw_count_clamp_range count) as H.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold MAX_RW_COUNT in H. unfold bv_modulus. lia.
Qed.

(** Linux UIO_MAXIOV: the largest iovec count a single readv/writev may
    pass; anything larger fails with -EINVAL (lib/iov_iter.c
    [iovec_from_user], testing [nr_segs > UIO_MAXIOV]; the constant is
    [UIO_MAXIOV = 1024] in include/uapi/linux/uio.h; both v6.18.46).
    Lives beside [MAX_RW_COUNT] because [import_iovecs] below tests
    both. *)
Definition IOV_MAX : Z := 1024%Z.

(** Decode the iovec array a [readv]/[writev] of count [cnt] passes,
    stopping after [IOV_MAX] entries.

    The bound is there because [nat] extracts to a unary Peano numeral:
    the unbounded [word_to_nat cnt] materializes [cnt] successors before
    the first descriptor is read, so a large [cnt] overflows the extracted
    checker's stack even when the very first entry is unmapped.
    [word_to_nat_bounded] keeps the comparison in [Z] and never builds
    more than [IOV_MAX] of them.

    Stopping there loses nothing the kernel could produce, so this is
    faithful rather than an approximation.  A count above [IOV_MAX] is
    [-EINVAL] from [iovec_from_user] (lib/iov_iter.c, v6.18.46)
    BEFORE [copy_iovec_from_user] touches a descriptor, and the one path
    that skips that test — the [nr_segs == 1] short-circuit described at
    [import_iovecs] — imports a single entry.  No call the kernel admits
    imports more than [IOV_MAX] descriptors.  [read_iovecs_unguarded]
    proves the bound is invisible at and below it. *)
Definition read_iovecs (mp : word -> option byte) (a cnt : word)
    : option (list (word * word)) :=
  read_iovecs_aux mp a (word_to_nat_bounded cnt (Z.to_nat IOV_MAX)).

Lemma read_iovecs_unguarded : forall mp a cnt,
  (bv_unsigned cnt <= IOV_MAX)%Z ->
  read_iovecs mp a cnt = read_iovecs_aux mp a (word_to_nat cnt).
Proof.
  intros mp a cnt Hle. pose proof (bv_unsigned_in_range 64 cnt) as Hr.
  unfold read_iovecs. rewrite word_to_nat_bounded_eq_min.
  rewrite Nat.min_l; [reflexivity|].
  unfold word_to_nat. apply Z2Nat.inj_le; unfold IOV_MAX in *; lia.
Qed.

(** riscv64 [access_ok], transcribed.  Linux's [__access_ok] is

      [(size <= TASK_SIZE_MAX) && (addr <= TASK_SIZE_MAX - size)]

    (include/asm-generic/access_ok.h, [__access_ok], at v6.18.46 /
    1f99e9ab748f), and on riscv64 at that commit [TASK_SIZE_MAX] is the
    header's own [#ifndef TASK_SIZE_MAX] fallback to [TASK_SIZE] — see
    that constant above for the derivation and the Sv48 premise it
    rests on.  [access_okb] below is that comparison with [TASK_SIZE]
    substituted: two comparisons and no page-table walk, so an unmapped
    range ending at or below 2^47 passes and a mapped one ending past it
    fails.  Written as a SUBTRACTION, as the kernel writes it, so the
    sum [base + len] is never formed and a range that wraps 2^64 is
    refused rather than folded back inside.

    Every user-range verdict in the model goes through this one
    definition: [import_iovecs] applies it to the descriptor array and
    to each destination, and [Uaccess.access_ok_zero] and the scalar arms
    apply it to their buffers.  There is no second spelling of the limit
    to keep in step with it.

    WHAT [__access_ok] HAS THAT THIS DOES NOT, in two halves.  The first
    is the pointer-masking wrapper.  With [CONFIG_RISCV_ISA_SUPM]
    (arch/riscv/Kconfig: [bool], [depends on 64BIT], [default y]) riscv64
    defines its own [access_ok] as [__access_ok(untagged_addr(addr),
    size)] (arch/riscv/include/asm/uaccess.h, [access_ok]).  This
    predicate does not untag.  That costs nothing here, because the
    untagging is the IDENTITY for every process this model can describe.
    Every citation below is at v6.18.46 unless it names another tag.

    - [untagged_addr] masks [PMLEN] bits.  Under [CONFIG_MMU] — the
      configuration modeled here — [__untagged_addr_remote]
      (arch/riscv/include/asm/uaccess.h) is the ARITHMETIC, sign-extending
      shift [(long)(addr << pmlen) >> pmlen]; the logical
      [(addr << pmlen) >> pmlen] is the [!CONFIG_MMU] branch.  Both are the
      identity at [pmlen = 0], and the function returns [addr] outright
      when SUPM is absent.
    - [PMLEN] is zero on every [execve]: [activate_mm]
      (arch/riscv/include/asm/mmu_context.h) assigns
      [next->context.pmlen = 0] unconditionally, and [flush_thread]
      (arch/riscv/kernel/process.c) resets the hardware [ENVCFG_PMM] to
      [ENVCFG_PMM_PMLEN_0] alongside it.  THIS is the premise the
      argument rests on.
    - A nonzero [pmlen] is set only by [set_tagged_addr_ctrl]
      (arch/riscv/kernel/process.c, the [mm->context.pmlen = pmlen]
      store), which has TWO callers, not one:
      [prctl(PR_SET_TAGGED_ADDR_CTRL, ...)] (kernel/sys.c, the
      [PR_SET_TAGGED_ADDR_CTRL] arm of [SYSCALL_DEFINE5(prctl)]), and
      PTRACE_SETREGSET with [NT_RISCV_TAGGED_ADDR_CTRL]
      (arch/riscv/kernel/ptrace.c, [tagged_addr_ctrl_set]; both arrived
      in v6.13 in one series, commits 2e1743085887 and 78844482a1c9, so
      there was never a release in which prctl was the only route).
      A TRACER can therefore enable masking for a tracee that never calls
      prctl.  Documentation/arch/riscv/uabi.rst: "Pointer masking is
      disabled by default.  To enable it, userspace must call
      PR_SET_TAGGED_ADDR_CTRL".  No Kconfig default sets it and the
      [abi.tagged_addr_disabled] sysctl only ever FORBIDS enabling.
    - [pmlen] lives in [mm->context], NOT in [thread_struct], so it IS
      inherited across fork and clone ([dup_mm]'s [memcpy] of the whole
      [mm_struct] in kernel/fork.c, and [CLONE_VM] sharing the [mm]
      outright in [copy_mm]); riscv's [init_new_context] resets [context.id] and the
      [MM_CONTEXT_LOCK_PMLEN] bit but never [pmlen].  Inheritance does not
      weaken anything here, because the [execve] reset above runs on the
      binary this model starts from.

    Neither route is reachable in this model, but the two are ruled
    out at different granularities.  [ptrace] is syscall 117 on riscv64
    (include/uapi/asm-generic/unistd.h; riscv64 uses the generic table)
    and is outside [Specs.modeled_sysnos] — as is [execve] — so it falls
    through the dispatcher to [Monad.unmodeled], fail closed, before any
    tagged pointer can reach this predicate.  [prctl] is 167 and IS in
    [Specs.modeled_sysnos]: it answers [PR_CAPBSET_READ] and nothing
    else, so what is declined is the OPTION rather than the number, and
    [PR_SET_TAGGED_ADDR_CTRL] (55) is declined inside
    [Kernel.Sys.prctl_spec] instead of at the dispatcher.  Neither step
    is left to this comment:
    [Checks.ProcessCreation.prctl_tagged_addr_ctrl_unmodeled] and
    [Checks.ProcessCreation.ptrace_unmodeled] prove them for option 55 of
    167 and for all of 117 against [Specs.syscall_spec] itself, so giving
    117 an arm breaks the build here rather than silently falsifying this
    paragraph.  The tripwire on 167 holds although that number has an arm,
    because the answered options are a closed list of their own,
    [Kernel.Sys.prctl_modeled_options], which
    [Checks.ProcessCreation.prctl_modeled_options_are] pins EXACTLY: an
    edit teaching [prctl] a second option fails that pin, and whoever
    makes it has to come back here.
    [clone] (220) and [clone3] (435) ARE in [Specs.modeled_sysnos], but
    only for a flag word that shares no address space
    ([Fork.clone_fork_flags_b],
    [Checks.ProcessCreation.clone_sharing_flags_unmodeled]), so no
    process this model admits an outcome for can write another's
    [mm->context].  (riscv64 has no [fork] syscall of its own: [fork] IS
    [clone(SIGCHLD)], which this model answers.)

    THE TRACER IS AN ASSUMPTION, not a consequence: no process outside
    this one attaches to it.  That is a closed-world assumption about
    the ENVIRONMENT, which no artifact in this repository checks.  It does
    not follow from the limits on 220, since a tracer is an independently
    started process; modeling [clone] parent-side does not weaken it,
    but it does add a second population to it, because a child this
    model never steps could attach to its own parent.  Under that
    assumption, every execution the model admits an outcome for has
    [pmlen = 0].

    That settles the tagging half.  The other half is a BUILD
    CONFIGURATION: [__access_ok] returns true for every range, before it
    reaches the comparison this predicate transcribes, under
    [CONFIG_ALTERNATE_USER_ADDRESS_SPACE] or with [CONFIG_MMU] off.  On
    such a build [access_okb] still declines ranges the kernel accepts,
    which is exactly an under-approximation.

    The two are NOT alike, and only one of them is a choice.  riscv
    cannot select [CONFIG_ALTERNATE_USER_ADDRESS_SPACE]: it is defined in
    arch/Kconfig with no prompt and is selected only by parisc, s390,
    [SPARC64] and m68k's [CPU_HAS_ADDRESS_SPACES] (arch/Kconfig at
    v6.18.46), none of them this architecture.  [CONFIG_MMU] IS a choice, and
    riscv64 can be built without it — arch/riscv/Kconfig's [config MMU]
    is a prompted bool defaulting to y with no [depends on], and
    arch/riscv/configs/nommu_virt_defconfig is a shipped RV64 build that
    turns it off.  So this model is scoped to the MMU half by decision,
    not by impossibility, and a nommu riscv64 kernel is a real
    configuration in which [access_okb] is an under-approximation.

    The claim is scoped rather than hedged on purpose: build for nommu
    and this is the sentence that breaks.

    This is a fail-closed gap in the ordinary way, not a known
    limitation. *)
Definition access_okb (base : word) (len : Z) : bool :=
  ((len <=? TASK_SIZE)%Z && (bv_unsigned base <=? TASK_SIZE - len)%Z)%bool.

(** [copy_to_user]/[copy_from_user] IS [access_ok] AND THEN THE COPY
    (include/linux/uaccess.h's [_inline_copy_to_user] and
    [_inline_copy_from_user] at v6.18.46 each test [access_ok] over the
    whole range and only then call the raw copy), and this pairs the two
    halves.
    [read_bytes_map] is the copy alone: it advances with WRAPPING [bv]
    addition, so a range whose base sits in the last bytes of the address
    space walks off the top and back in at 0, and where [mp] backs both
    halves it answers [Some] — a range fully "readable" that Linux
    refuses outright.  [access_okb] sums in [Z] and so refuses it.

    A spec modeling a [copy_to_user] or a [copy_from_user] should reach
    for this and not for the bare walk.  [Net.Socket.socketpair_dest_writable],
    [Kernel.Signal.write_oset], [EventPoll.copy_from_user_ok] and
    [Fs.Pipe.pipe2_spec] each spell the same pair by hand,
    [access_okb] and then [read_bytes_map]; moving them onto this
    definition is the follow-up, so that the range question has one
    spelling.  A spec that reaches for the bare walk alone is claiming
    the range question is asked somewhere else, and owes the argument
    in place.

    THE LENGTH IS A [Z] because [access_okb]'s is.

    A structural repair — an [IMAGE_WF] conjunct
    bounding every loaded segment — would remove the wrapping
    walks at the source.  The range test stays either way: it is what
    turns a refused range into -EFAULT rather than into an unmapped
    walk's [None]. *)
Definition copy_bytes_map (mp : word -> option byte) (a : word) (len : Z)
    : option (list byte) :=
  if access_okb a len then read_bytes_map mp a (Z_to_bv 64 len) else None.

(** The half the walk alone cannot see: a range [access_okb] refuses is
    [None] here however the memory map answers.  This is the property
    every caller's decline rests on, so it is stated once rather than
    re-derived per arm. *)
Lemma copy_bytes_map_refused : forall mp a len,
  access_okb a len = false -> copy_bytes_map mp a len = None.
Proof. intros mp a len H. unfold copy_bytes_map. rewrite H. reflexivity. Qed.

(** ...and the other direction, which is what keeps the guard from being
    a blanket refusal: on a range [access_okb] accepts, this is exactly
    the walk it always was. *)
Lemma copy_bytes_map_accepted : forall mp a len,
  access_okb a len = true ->
  copy_bytes_map mp a len = read_bytes_map mp a (Z_to_bv 64 len).
Proof. intros mp a len H. unfold copy_bytes_map. rewrite H. reflexivity. Qed.

(** The three outcomes of importing an iovec array (lib/iov_iter.c
    [__import_iovec], v6.18.46): the imported entries, a [-EFAULT] from an
    unreadable descriptor or a failed [access_ok], or a [-EINVAL] from a
    count over [IOV_MAX] or a length that is negative as [ssize_t]. *)
Inductive iov_import : Type :=
  | ImpOk (iovs : list (word * word))
  | ImpFault
  | ImpInval.

(** One [struct iovec] (LP64: 8-byte little-endian [iov_base] then
    [iov_len]) as [copy_iovec_from_user] fetches it: BOTH fields are
    loaded — [iov_len], then [iov_base], each an [unsafe_get_user] with
    its own fixup — and only then is the sign of [iov_len] tested.  So a
    field that cannot be read is [-EFAULT] whatever the length says, and
    a length that is negative as [ssize_t] is [-EINVAL] only once both
    fields have been read. *)
Inductive iov_entry : Type :=
  | IovEntry (base len : word)
  | IovFault
  | IovInval.

Definition read_iovec_entry (mp : word -> option byte) (a : word)
    : iov_entry :=
  match read_u64 mp a, read_u64 mp (a + 8) with
  | Some base, Some len =>
      if (2 ^ 63 <=? bv_unsigned len)%Z then IovInval else IovEntry base len
  | _, _ => IovFault
  end.

(** [copy_iovec_from_user] (lib/iov_iter.c, v6.18.46): ONE interleaved
    pass in index order — per entry both fields, then
    [if (len < 0) return -EINVAL] — so the FIRST error in INDEX ORDER
    decides the call.

    The interleaving is v6.4 and later.  Up to v6.3 the function did a
    bulk [copy_from_user] of the whole array followed by a separate
    length loop, so [-EFAULT] beat [-EINVAL] regardless of index; commit
    487c20b016dc ("iov: improve copy_iovec_from_user() code generation",
    Linus Torvalds, first in v6.4-rc1) changed it, with the errno
    precedence an unremarked side effect of what was sold as a codegen
    change. *)
Fixpoint copy_iovecs_aux (mp : word -> option byte) (a : word) (k : nat)
    : iov_import :=
  match k with
  | O => ImpOk []
  | S k' =>
      match read_iovec_entry mp a with
      | IovFault => ImpFault
      | IovInval => ImpInval
      | IovEntry base len =>
          match copy_iovecs_aux mp (a + 16) k' with
          | ImpOk r => ImpOk ((base, len) :: r)
          | r => r
          end
      end
  end.

(** Descriptors actually attempted by [copy_iovecs_aux], one 16-byte
    range per descriptor reached.  The walk stops on the same first
    unreadable descriptor or negative length, so an errno path records
    only the prefix the kernel inspected. *)
Fixpoint copy_iovecs_accesses (mp : word -> option byte) (a : word) (k : nat)
    : list (word * nat) :=
  match k with
  | O => []
  | S k' =>
      (a, 16%nat) ::
      match read_iovec_entry mp a with
      | IovEntry _ _ => copy_iovecs_accesses mp (a + 16) k'
      | _ => []
      end
  end.

(** [__import_iovec]'s per-segment [access_ok(iov_base, len)] on the
    UNCAPPED length (lib/iov_iter.c, v6.18.46), applied to a zero-length
    entry as well as to any other. *)
Definition iovs_access_okb (iovs : list (word * word)) : bool :=
  forallb (fun bl => access_okb (fst bl) (bv_unsigned (snd bl))) iovs.

(** Truncate an iovec sequence at [MAX_RW_COUNT], exactly as
    [__import_iovec]'s loop does with [len > MAX_RW_COUNT - total_len]
    (lib/iov_iter.c, v6.18.46).  Entries after the cap remain present with
    length zero: the kernel imports and address-checks the whole array
    before I/O, even though no bytes from those entries can be
    transferred. *)
Fixpoint cap_iovecs_aux (iovs : list (word * word)) (left : Z)
    : list (word * word) :=
  match iovs with
  | [] => []
  | (base, len) :: rest =>
      let n := Z.min left (bv_unsigned len) in
      (base, Z_to_bv 64 n) :: cap_iovecs_aux rest (left - n)
  end.

Definition cap_iovecs (iovs : list (word * word)) : list (word * word) :=
  cap_iovecs_aux iovs MAX_RW_COUNT.

(** The iovec import path (lib/iov_iter.c, v6.18.46): [import_iovec] is a
    one-line wrapper that passes [in_compat_syscall()] to
    [__import_iovec], which does the work, for readv and writev alike.
    The entries come back UNCAPPED — the kernel clamps inside
    [__import_iovec]'s loop, the model afterwards, in the consumers
    ([ReadWrite.readv_imported], [ReadWrite.writev_spec]'s gather),
    after the per-entry [access_ok] the loop applies to the uncapped
    length has been decided.
    ([Net.Socket.sendmsg_spec] imports with [copy_iovecs_aux] and
    so lacks the per-segment [access_ok] this function adds.)

    - A count of exactly ONE takes a DIFFERENT function with the OPPOSITE
      cap/[access_ok] order: [__import_iovec_ubuf] copies the single
      descriptor ([copy_iovec_from_user] with [nr_segs = 1], so the same
      [read_iovec_entry] order) and hands it to [import_ubuf], which caps
      to [MAX_RW_COUNT] FIRST and only then applies [access_ok] to the
      CAPPED length.  The [nr_segs == 1] short-circuit is the first
      statement of [__import_iovec], ahead of its call to
      [iovec_from_user], hence ahead of that function's [UIO_MAXIOV] test
      and of its heap allocation.  So [readv(fd, iov, 1)] never reports
      [-EINVAL] for a count over [IOV_MAX] — 1 is not over it — and,
      because the count reaches [__import_iovec] through an [unsigned]
      parameter, a raw count of [2^32 + 1] truncates to 1 and takes this
      path too.

    - For every other count the array is copied first
      ([copy_iovecs_aux], index-ordered [-EFAULT]/[-EINVAL]) and only
      then walked a SECOND time for [access_ok] on the UNCAPPED length —
      [__import_iovec]'s per-segment loop tests [access_ok] before it
      applies that same loop's [MAX_RW_COUNT] clamp.  The two passes are
      why an [-EINVAL] at ANY index beats an [access_ok] [-EFAULT] at
      any index, while an unreadable descriptor and a negative length
      race in index order.

    [copy_iovec_from_user] opens with [user_access_begin] over
    [nr_segs] descriptors, an [access_ok] on the descriptor array
    itself; that is the [access_okb a ...] test on each branch. *)
Definition import_iovecs (mp : word -> option byte) (a n : word)
    : iov_import :=
  if bv_eqb n (Z_to_bv 64 1) then
    if negb (access_okb a 16) then ImpFault
    else match read_iovec_entry mp a with
         | IovFault => ImpFault
         | IovInval => ImpInval
         | IovEntry base len =>
             if negb (access_okb base (Z.min (bv_unsigned len) MAX_RW_COUNT))
             then ImpFault
             else ImpOk [(base, len)]
         end
  else if bv_eqb n (Z_to_bv 64 0) then ImpOk []
  else if (IOV_MAX <? bv_unsigned n)%Z then ImpInval
  else if negb (access_okb a (16 * bv_unsigned n)) then ImpFault
  else match copy_iovecs_aux mp a (word_to_nat n) with
       | ImpOk iovs =>
           if iovs_access_okb iovs then ImpOk iovs else ImpFault
       | r => r
       end.

Definition import_iovecs_accesses (mp : word -> option byte) (a n : word)
    : list (word * nat) :=
  if bv_eqb n (Z_to_bv 64 1) then
    if negb (access_okb a 16) then [] else [(a, 16%nat)]
  else if bv_eqb n (Z_to_bv 64 0) then []
  else if (IOV_MAX <? bv_unsigned n)%Z then []
  else if negb (access_okb a (16 * bv_unsigned n)) then []
  else copy_iovecs_accesses mp a (word_to_nat n).

(** The copy-in ledger for the prefix of an iovec sequence a transfer of
    [left] bytes actually touched.  [word_to_nat_bounded] rather than
    [Nat.min (word_to_nat len) left] for the reason given at its
    definition: a capped [iov_len] reaches [MAX_RW_COUNT], and the
    [Nat.min] spelling materializes that as a unary numeral before it
    compares, on a call that may have delivered one byte. *)
Fixpoint iov_prefix_accesses (iovs : list (word * word)) (left : nat)
    : list (word * nat) :=
  match iovs, left with
  | _, O => []
  | [], _ => []
  | (base, len) :: rest, _ =>
      let n := word_to_nat_bounded len left in
      if Nat.eqb n 0 then iov_prefix_accesses rest left
      else (base, n) :: iov_prefix_accesses rest (left - n)
  end.

(** Scatter [bs] across destination iovecs in order.  Every nonempty piece
    must be writable in [mp]; zero-length entries are skipped and produce no
    vacuous effect write.  [None] means either that [bs] exceeds the aggregate
    capacity or that some byte which would be delivered is not writable. *)
Fixpoint scatter_iovecs (mp : word -> option byte)
    (iovs : list (word * word)) (bs : list byte)
    : option (list (word * list byte)) :=
  match bs with
  | [] => Some []
  | _ :: _ =>
      match iovs with
      | [] => None
      | (base, len) :: rest =>
          let n := word_to_nat_bounded len (length bs) in
          let here := firstn n bs in
          let later := skipn n bs in
          match here with
          | [] => scatter_iovecs mp rest later
          | _ :: _ =>
              match read_bytes_map mp base (len_word here),
                    scatter_iovecs mp rest later with
              | Some _, Some writes => Some ((base, here) :: writes)
              | _, _ => None
              end
          end
      end
  end.

Lemma scatter_iovecs_concat : forall mp iovs bs writes,
  scatter_iovecs mp iovs bs = Some writes ->
  concat (map snd writes) = bs.
Proof.
  intros mp iovs. induction iovs as [|[base len] rest IH]; intros bs writes H.
  - destruct bs; cbn in H; inversion H; reflexivity.
  - destruct bs as [|b bs']; [cbn in H; inversion H; reflexivity|].
    cbn in H.
    remember (word_to_nat_bounded len (length (b :: bs'))) as n.
    remember (firstn n (b :: bs')) as here.
    remember (skipn n (b :: bs')) as later.
    cbn in Heqn.
    rewrite <- Heqn in H.
    rewrite <- Heqhere, <- Heqlater in H.
    destruct here as [|h hs].
    + apply IH in H.
      pose proof (firstn_skipn n (b :: bs')) as E.
      rewrite <- Heqhere, <- Heqlater in E. cbn in E. now rewrite H.
    + destruct (read_bytes_map mp base (len_word (h :: hs))) as [ok|] eqn:Hr;
        [|discriminate].
      destruct (scatter_iovecs mp rest later) as [tail|] eqn:Ht;
        [|discriminate].
      inversion H; clear H; subst writes.
      apply IH in Ht.
      cbn. rewrite Ht.
      pose proof (firstn_skipn n (b :: bs')) as E.
      rewrite <- Heqhere, <- Heqlater in E. exact E.
Qed.

(** An empty delivery performs no writes, independently of the vector. *)
Lemma scatter_iovecs_nil : forall mp iovs,
  scatter_iovecs mp iovs [] = Some [].
Proof. intros mp iovs. destruct iovs; reflexivity. Qed.

(** Whether a one-byte scatter succeeds depends only on the destination
    vector and its writability, not on the value of the byte. *)
Lemma scatter_iovecs_singleton_some : forall mp iovs b writes b',
  scatter_iovecs mp iovs [b] = Some writes ->
  exists writes', scatter_iovecs mp iovs [b'] = Some writes'.
Proof.
  intros mp iovs. induction iovs as [|[base len] rest IH];
    intros b writes b' H; [discriminate|].
  cbn [scatter_iovecs] in H |- *.
  rewrite !word_to_nat_bounded_eq_min in H |- *.
  destruct (word_to_nat len) as [|n] eqn:Hlen.
  - cbn in H |- *.
    eapply IH; exact H.
  - cbn in H |- *.
    rewrite !Nat.min_0_r in H |- *. cbn in H |- *.
    try rewrite !scatter_iovecs_nil in H.
    try rewrite !scatter_iovecs_nil.
    destruct (read_bytes_map mp base (len_word [b])) eqn:Hread;
      [|discriminate].
    inversion H; subst writes. clear H.
    change (read_bytes_map mp base (Z_to_bv 64 1) = Some l) in Hread.
    replace (len_word [b']) with (Z_to_bv 64 1) by reflexivity.
    rewrite Hread. eexists. reflexivity.
Qed.

(** Gather the source bytes of each iovec in order into one flat byte
    string ([None] if any source byte is unreadable) — exactly the
    buffer an equivalent single [write] would write. *)
Fixpoint gather_iovecs (mp : word -> option byte) (iovs : list (word * word))
    : option (list byte) :=
  match iovs with
  | [] => Some []
  | (base, len) :: r =>
      match read_bytes_map mp base len with
      | None => None
      | Some bs =>
          match gather_iovecs mp r with
          | Some rest => Some (bs ++ rest)
          | None => None
          end
      end
  end.

(** The GATHERABLE PREFIX of an iovec sequence: the bytes a real
    kernel's writev moves before faulting.  Linux consumes the iovecs
    in order, copy_from_user-ing each source buffer as it goes, so a
    fault inside an iovec delivers that iovec's readable prefix and
    stops — the flattened analogue of [readable_bytes].  Equals the
    full flattening exactly when every source byte is readable (i.e.
    when [gather_iovecs] succeeds); zero-length iovecs are skipped
    without touching their base pointer, as on Linux.  The
    completeness test compares lengths in [Z] over the unsigned value
    (no wrapping). *)
Fixpoint gather_prefix (mp : word -> option byte) (iovs : list (word * word))
    : list byte :=
  match iovs with
  | [] => []
  | (base, len) :: r =>
      let bs := readable_bytes mp base len in
      if (Z.of_nat (length bs) =? bv_unsigned len)%Z
      then bs ++ gather_prefix mp r
      else bs
  end.

(** Total byte count an iovec list requests (writev's EFAULT gate:
    a delivery of zero bytes is an error only when something was
    actually requested).  Summed in [Z] over unsigned lengths, so the
    total cannot wrap. *)
Fixpoint iovs_total (iovs : list (word * word)) : Z :=
  match iovs with
  | [] => 0%Z
  | (_, len) :: r => (bv_unsigned len + iovs_total r)%Z
  end.

Lemma iovs_total_nonneg : forall iovs, (0 <= iovs_total iovs)%Z.
Proof.
  induction iovs as [|[base len] rest IH]; cbn; [lia|].
  pose proof (bv_unsigned_in_range _ len). lia.
Qed.

(** [cap_iovecs] IS the kernel's aggregate clamp, and this is the only
    statement of that in the tree: capping a vector leaves an aggregate of
    exactly [Z.min] of the original aggregate and [MAX_RW_COUNT].  Stated
    here rather than beside [cap_iovecs] because [iovs_total] is defined
    below it.

    The generalized form quantifies over the budget [left] still unspent,
    which is what the induction needs; the top-level [iovs_total_cap]
    instantiates it at [MAX_RW_COUNT]. *)
Lemma iovs_total_cap_aux : forall iovs left,
  (0 <= left)%Z ->
  (iovs_total (cap_iovecs_aux iovs left) = Z.min (iovs_total iovs) left)%Z.
Proof.
  induction iovs as [|[base len] rest IH]; intros left Hleft;
    cbn [iovs_total cap_iovecs_aux]; [lia|].
  pose proof (bv_unsigned_in_range 64 len).
  pose proof (iovs_total_nonneg rest).
  rewrite Z_to_bv_unsigned, bv_wrap_small by lia.
  rewrite IH by lia.
  lia.
Qed.

Lemma iovs_total_cap : forall iovs,
  (iovs_total (cap_iovecs iovs) = Z.min (iovs_total iovs) MAX_RW_COUNT)%Z.
Proof.
  intros iovs. unfold cap_iovecs.
  apply iovs_total_cap_aux. unfold MAX_RW_COUNT. lia.
Qed.

(** The bytes a writev moves, and the -EFAULT gate in front of them,
    each stated ONCE for the whole tree.  [__import_iovec] applies the
    aggregate [MAX_RW_COUNT] clamp inside its per-segment loop for BOTH
    directions, so the write side must gather over [cap_iovecs] exactly
    as the read side scatters over it.  Every writev body — the
    relational spec, the acceptor and the progress witness, each with
    one channel arm and one file arm — goes through these two, so there
    is no per-arm clamp left to forget on one side and remember on the
    other. *)
Definition writev_gathered (mp : word -> option byte)
    (iovs0 : list (word * word)) : list byte :=
  gather_prefix mp (cap_iovecs iovs0).

(* =========================================================================
   Standard input: an explicit INPUT of the semantics
   ========================================================================= *)

(** The bytes the process will read from standard input, supplied UP
    FRONT as a parameter of the run ([Run.run]'s [stdin0] argument,
    universally quantified in [Equivalence.strong_universal_T] exactly
    like argv, envp and the initial file system).  A program's behavior
    is therefore a FUNCTION of its input rather than of an internal
    nondeterministic choice: the environment does not invent bytes (or
    an EOF position) mid-run.

    The type is a COLIST — a coinductive stream that may also STOP:

    - [ICons b s] — the next byte is [b], and [s] is what follows;
    - [IEof]      — the input ends here.

    Being coinductive, it covers INFINITE inputs (a never-ending pipe,
    [yes] into the program); the [IEof] constructor is what lets it also
    express a finite input, which a plain [Stream byte] cannot.

    EOF IS STICKY BY CONSTRUCTION: [IEof] has no successor, so once a
    read observes it there is nothing left to deliver and every later
    read observes [IEof] again.  Stickiness is not a model
    invariant that a spec could accidentally break; it is a property of the
    representation.

    No validity predicate is needed: the elements are [byte = bv 8], so
    "every byte really is a byte" holds by typing.

    Only channel 0 (stdin) is readable in this model — stdout/stderr are
    write-only ([FdEntry]) — so one stream suffices; there is no
    per-channel indexing. *)
CoInductive InputStream : Type :=
  | IEof : InputStream
  | ICons (b : byte) (rest : InputStream).

(** Take up to [k] bytes off the front of [s]: the bytes actually
    available (fewer than [k] when the input ends first) together with
    the REMAINING stream.  This is the whole of what a read consumes;
    [ReadWrite.read_spec] chooses how many bytes a given read delivers
    (short reads are real) but not WHICH — those come from here.

    Indexed by a [nat] rather than a [word]: the index is always the
    length of a delivered byte list, never guest arithmetic, so no
    wrapping is possible. *)
Fixpoint stream_take (s : InputStream) (k : nat) : list byte * InputStream :=
  match k with
  | O => ([], s)
  | S k' =>
      match s with
      | IEof => ([], IEof)
      | ICons b s' => let r := stream_take s' k' in (b :: fst r, snd r)
      end
  end.

(** The bytes a read of at most [k] delivers. *)
Definition stream_bytes (s : InputStream) (k : nat) : list byte :=
  fst (stream_take s k).

(** What is left after such a read. *)
Definition stream_rest (s : InputStream) (k : nat) : InputStream :=
  snd (stream_take s k).

Lemma stream_take_eof : forall k, stream_take IEof k = ([], IEof).
Proof. destruct k; reflexivity. Qed.

Lemma stream_take_cons : forall b s k,
  stream_take (ICons b s) (S k)
  = (b :: fst (stream_take s k), snd (stream_take s k)).
Proof. reflexivity. Qed.

(** A read never delivers more than it was asked for. *)
Lemma stream_take_length : forall k s,
  (length (fst (stream_take s k)) <= k)%nat.
Proof.
  induction k as [|k IH]; intro s; cbn; [lia|].
  destruct s as [|b s']; cbn; [lia|]. specialize (IH s'). lia.
Qed.

(** Taking exactly as many bytes as were delivered is idempotent: the
    delivered list is the stream's prefix of its own length.  (Used to
    read the choice condition of [ReadWrite.read_spec] both ways.) *)
Lemma stream_take_bytes_self : forall k s,
  fst (stream_take s (length (fst (stream_take s k))))
  = fst (stream_take s k).
Proof.
  induction k as [|k IH]; intro s; [reflexivity|].
  destruct s as [|b s']; [reflexivity|].
  cbn [stream_take fst snd length]. rewrite IH. reflexivity.
Qed.

Lemma stream_take_rest_self : forall k s,
  snd (stream_take s (length (fst (stream_take s k))))
  = snd (stream_take s k).
Proof.
  induction k as [|k IH]; intro s; [reflexivity|].
  destruct s as [|b s']; [reflexivity|].
  cbn [stream_take fst snd length]. rewrite IH. reflexivity.
Qed.

(** A nonempty delivery is only possible from a nonempty stream. *)
Lemma stream_take_nil_of_eof : forall k, fst (stream_take IEof k) = [].
Proof. intro k. rewrite stream_take_eof. reflexivity. Qed.

(** Taking [a + b] bytes is taking [a], then [b] from what is left. *)
Lemma stream_take_add : forall a b s,
  stream_take s (a + b)%nat
  = (fst (stream_take s a) ++ fst (stream_take (snd (stream_take s a)) b),
     snd (stream_take (snd (stream_take s a)) b)).
Proof.
  induction a as [|a IH]; intros b s; cbn [Nat.add stream_take fst snd].
  - destruct (stream_take s b); reflexivity.
  - destruct s as [|c s'].
    + rewrite stream_take_eof. reflexivity.
    + cbn [stream_take fst snd]. rewrite IH. reflexivity.
Qed.

(** [stream_take] indexed by a [Z] count, for the one place the count is
    the kernel's aggregate rather than the length of a delivered list:
    the bytes the source could supply to a read of [n], which decides
    whether a partially writable destination is declined
    ([ReadWrite.read_spec], [ReadWrite.readv_imported]).  [n] there can
    be [MAX_RW_COUNT], and [stream_take s (Z.to_nat n)] would build that
    many unary successors in the extracted checker before looking at the
    stream.  This recurses on the BINARY digits of [n] instead — each
    digit takes two halves, stopping as soon as the stream ends — so the
    cost is the bytes actually taken plus one step per digit, and no
    unary numeral is ever built.  [stream_take_z_eq] says it computes
    exactly [stream_take] at [Z.to_nat n]; the spec uses this spelling so
    that the checker, which is the same term, can run it. *)
Fixpoint stream_take_pos (s : InputStream) (p : positive)
    : list byte * InputStream :=
  match p with
  | xH => stream_take s 1
  | xO p' =>
      let r1 := stream_take_pos s p' in
      match snd r1 with
      | IEof => (fst r1, IEof)
      | s1 => let r2 := stream_take_pos s1 p' in (fst r1 ++ fst r2, snd r2)
      end
  | xI p' =>
      let r1 := stream_take_pos s p' in
      match snd r1 with
      | IEof => (fst r1, IEof)
      | s1 =>
          let r2 := stream_take_pos s1 p' in
          match snd r2 with
          | IEof => (fst r1 ++ fst r2, IEof)
          | s2 => let r3 := stream_take s2 1 in
                  (fst r1 ++ fst r2 ++ fst r3, snd r3)
          end
      end
  end.

Definition stream_take_z (s : InputStream) (n : Z) : list byte * InputStream :=
  match n with
  | Zpos p => stream_take_pos s p
  | _ => ([], s)
  end.

Lemma stream_take_pos_eq : forall p s,
  stream_take_pos s p = stream_take s (Pos.to_nat p).
Proof.
  induction p as [p IH|p IH|]; intro s; cbn [stream_take_pos].
  - rewrite Pos2Nat.inj_xI.
    replace (S (2 * Pos.to_nat p))%nat
      with (Pos.to_nat p + (Pos.to_nat p + 1))%nat by lia.
    rewrite stream_take_add, (stream_take_add (Pos.to_nat p) 1), !IH.
    destruct (snd (stream_take s (Pos.to_nat p))) as [|b rest] eqn:H1.
    + rewrite !stream_take_eof. cbn [fst snd app]. rewrite app_nil_r.
      reflexivity.
    + rewrite IH.
      destruct (snd (stream_take (ICons b rest) (Pos.to_nat p)))
        as [|b' rest'] eqn:H2.
      * rewrite stream_take_eof. cbn [fst snd app]. rewrite app_nil_r.
        reflexivity.
      * reflexivity.
  - rewrite Pos2Nat.inj_xO.
    replace (2 * Pos.to_nat p)%nat with (Pos.to_nat p + Pos.to_nat p)%nat
      by lia.
    rewrite stream_take_add, !IH.
    destruct (snd (stream_take s (Pos.to_nat p))) as [|b rest] eqn:H1.
    + rewrite stream_take_eof. cbn [fst snd app]. rewrite app_nil_r.
      reflexivity.
    + rewrite IH. reflexivity.
  - reflexivity.
Qed.

Lemma stream_take_z_eq : forall s n,
  stream_take_z s n = stream_take s (Z.to_nat n).
Proof.
  intros s [|p|p]; cbn [stream_take_z Z.to_nat]; [reflexivity| |reflexivity].
  apply stream_take_pos_eq.
Qed.

(* -------------------------------------------------------------------------
   A stream that never ends
   ------------------------------------------------------------------------- *)

(** A STREAM THAT NEVER REACHES [IEof].

    COINDUCTIVE, AND THAT IS FORCED rather than stylistic.  It is the
    exact dual of [EquivalenceDefinition.FinInput.finite_stream], which
    is inductive because a derivation there must reach [IEof] in a
    bounded number of steps.  Here nothing is ever reached, so a
    derivation is a productive corecursion instead and the only way to
    build one is a [cofix].  [stream_const_infinite] below is the
    worked witness.

    WHAT IT IS FOR.  [in_stdin] and [in_net] carry no validity clause
    and should not: a pipe that ends is a real pipe, and a program has
    to survive it.  The RANDOM DEVICE is not like that.
    [Sys.Fs.ReadWrite.read_urandom] takes the whole clamped count from
    the declared stream and DECLINES if fewer bytes come back, because a
    short read from this device is not something Linux does:
    [urandom_read_iter] is [get_random_bytes_user] over the imported
    iterator, and that loops until the iterator is drained, stopping
    early only where [copy_to_iter] copies short or a signal is pending
    at a page boundary (drivers/char/random.c, Linux v6.18.46; both
    functions are the same in v6.12.1).  The pool is never empty once initialised, and
    [urandom_read_iter] does not wait for it to be.  So a finite
    declaration does not describe a device at all, and a clause ruling
    one out narrows nothing a real /dev/urandom can do.

    IT IS NOT A CLAIM THAT THE STREAM IS UNIFORM, or unpredictable, or
    anything else about its contents.  It says only that reading it
    always yields as many bytes as were asked for, which is what the
    arm needs and the whole of what this predicate says. *)
CoInductive stream_infinite : InputStream -> Prop :=
| stream_infinite_cons : forall b s,
    stream_infinite s -> stream_infinite (ICons b s).

Lemma stream_infinite_not_eof : ~ stream_infinite IEof.
Proof. intro H. inversion H. Qed.

(** THE ONE FACT EVERY CONSUMER WANTS: a take off an endless stream
    delivers exactly as many bytes as it asked for. *)
Lemma stream_take_infinite_length : forall k s,
  stream_infinite s -> length (fst (stream_take s k)) = k.
Proof.
  induction k as [|k IH]; intros s Hs; [reflexivity|].
  destruct s as [|b s']; [now destruct (stream_infinite_not_eof Hs)|].
  inversion Hs as [b' s'' Hs' Heq]; subst.
  cbn [stream_take]. cbn [fst length]. now rewrite (IH s' Hs').
Qed.

(** ...AND THE INVARIANT SURVIVES THE READ, which is what makes the
    clause an input clause rather than one that has to be re-established
    at every step: the remainder of an endless stream is endless, so a
    model whose [m_urandom] started endless stays endless however many
    reads it serves. *)
Lemma stream_infinite_rest : forall k s,
  stream_infinite s -> stream_infinite (snd (stream_take s k)).
Proof.
  induction k as [|k IH]; intros s Hs; [exact Hs|].
  destruct s as [|b s']; [now destruct (stream_infinite_not_eof Hs)|].
  inversion Hs as [b' s'' Hs' Heq]; subst.
  cbn [stream_take snd]. now apply IH.
Qed.

(** The same two, in the [Z]-indexed spelling [read_urandom] uses. *)
Lemma stream_take_z_infinite_length : forall s n,
  stream_infinite s -> (0 <= n)%Z ->
  Z.of_nat (length (fst (stream_take_z s n))) = n.
Proof.
  intros s n Hs Hn. rewrite stream_take_z_eq.
  rewrite (stream_take_infinite_length _ _ Hs). lia.
Qed.

Lemma stream_take_z_infinite_rest : forall s n,
  stream_infinite s -> stream_infinite (snd (stream_take_z s n)).
Proof.
  intros s n Hs. rewrite stream_take_z_eq. now apply stream_infinite_rest.
Qed.

(** THE WITNESS, so the clause is not one nothing satisfies: the
    constant stream.  A launch really can declare it — it is a
    perfectly good description of a device that happened to hand out one
    byte value — and it is the fixtures' declaration. *)
CoFixpoint stream_const (b : byte) : InputStream := ICons b (stream_const b).

(** A [CoFixpoint] constant does not reduce on its own; it reduces only
    as the scrutinee of a [match].  Putting it in that position is what
    this one-level case analysis is for — the same "frob" step
    [EquivalenceDefinition.FinInput.stream_decompose] makes, restated
    here because [State] is upstream of that file. *)
Lemma stream_const_unfold : forall b,
  stream_const b = ICons b (stream_const b).
Proof.
  intro b.
  transitivity (match stream_const b with
                | IEof => IEof
                | ICons c r => ICons c r
                end).
  - destruct (stream_const b); reflexivity.
  - reflexivity.
Qed.

Lemma stream_const_infinite : forall b, stream_infinite (stream_const b).
Proof.
  cofix IH. intro b. rewrite stream_const_unfold.
  apply stream_infinite_cons. apply IH.
Qed.

(** THE RANDOM STREAM A FIXTURE GETS WHEN IT DOES NOT SAY.  It is a
    FIXTURE DEFAULT and appears in no theorem: it is what [mkProcInput]
    fills [in_urandom] with, for positional literals that do not
    give the field.

    IT IS NOT [IEof], and that is not cosmetic.
    [Run.valid_urandom] asks that a launch's declared random stream
    never end, so [IEof] is not a declaration any valid input can
    carry, and a fixture that used it would fail its own validity pin.
    Zero bytes forever is the shortest thing that does satisfy the
    clause; the VALUE is arbitrary and nothing reads it. *)
Definition default_urandom : InputStream := stream_const (Z_to_bv 8 0).

Lemma default_urandom_infinite : stream_infinite default_urandom.
Proof. apply stream_const_infinite. Qed.

(* =========================================================================
   The network environment: what a hostile peer may do
   ========================================================================= *)

(** ONE CONNECTION'S SCRIPT, from the local program's point of view.

    A TCP peer on an established connection can do exactly four things
    that the reading side can tell apart, and this type has one
    constructor for each.  Every kernel citation here is v6.12:

    - [NCons b rest] — it sent the byte [b], and then went on to [rest];
    - [NFin]         — it closed its sending half (FIN).  A read
                       delivers 0 (net/ipv4/tcp_input.c [tcp_fin] sets
                       RCV_SHUTDOWN and SOCK_DONE), and every later read
                       delivers 0 again;
    - [NRst]         — it reset the connection (RST).  ONE read answers
                       -ECONNRESET and every later read delivers 0;
    - [NTimedOut]    — it stopped acknowledging until the retransmit
                       timer gave up (net/ipv4/tcp_timer.c [tcp_write_err]).
                       ONE read answers -ETIMEDOUT, then 0.

    COINDUCTIVE, so a peer that never stops sending is expressible —
    the same reason [InputStream] is coinductive.

    THE TERMINALS ARE NULLARY ON PURPOSE.  A peer cannot send anything
    after a FIN or a RST, so "nothing follows a terminal" is a property
    of the REPRESENTATION rather than an invariant a spec could break —
    the house rule [InputStream] states for [IEof].  It also means
    validity holds BY TYPING: the payload of [NCons] is a [byte], the
    terminals carry nothing, so there is no [valid_net] side condition
    for [Run.valid_input] to carry.

    WHY EXACTLY {RST, TIMEDOUT} AND NOTHING ELSE.  Those are the only
    two errnos a peer can force on the read side of an established
    AF_INET/SOCK_STREAM socket with default options and no cooperation
    from the local program.  -EAGAIN needs O_NONBLOCK, -EINTR needs a
    signal, -EHOSTUNREACH/-ENETUNREACH need IP_RECVERR, and none of the
    three is in the modeled surface — so admitting them would model
    something the model cannot reach.

    WHY ONE ERROR AND THEN END-OF-STREAM, rather than a sticky error.
    include/net/sock.h [sock_error] reads the pending error with an
    [xchg], so it is consumed by the read that reports it; and the RST
    path's tcp_done sets [sk_shutdown = SHUTDOWN_MASK].  The read after
    an -ECONNRESET therefore returns 0.  A sticky error would be a
    plausible answer Linux does not give. *)
CoInductive NetStream : Type :=
  | NFin      : NetStream
  | NRst      : NetStream
  | NTimedOut : NetStream
  | NCons (b : byte) (rest : NetStream).

(** Take up to [k] bytes off the front of a connection's script: the
    bytes actually available (fewer than [k] when a terminal comes
    first) together with the REMAINING script.  The exact analogue of
    [stream_take], with the three terminals where [IEof] is.

    Indexed by a [nat] rather than a [word] for the same reason: the
    index is always the length of a delivered byte list, never guest
    arithmetic, so no wrapping is possible. *)
Fixpoint net_take (s : NetStream) (k : nat) : list byte * NetStream :=
  match k with
  | O => ([], s)
  | S k' =>
      match s with
      | NCons b s' => let r := net_take s' k' in (b :: fst r, snd r)
      | _ => ([], s)
      end
  end.

(** The bytes a read of at most [k] delivers. *)
Definition net_bytes (s : NetStream) (k : nat) : list byte :=
  fst (net_take s k).

(** What is left after such a read. *)
Definition net_rest (s : NetStream) (k : nat) : NetStream :=
  snd (net_take s k).

Lemma net_take_zero : forall s, net_take s 0 = ([], s).
Proof. reflexivity. Qed.

Lemma net_take_fin : forall k, net_take NFin k = ([], NFin).
Proof. destruct k; reflexivity. Qed.

Lemma net_take_rst : forall k, net_take NRst k = ([], NRst).
Proof. destruct k; reflexivity. Qed.

Lemma net_take_timedout : forall k, net_take NTimedOut k = ([], NTimedOut).
Proof. destruct k; reflexivity. Qed.

Lemma net_take_cons : forall b s k,
  net_take (NCons b s) (S k)
  = (b :: fst (net_take s k), snd (net_take s k)).
Proof. reflexivity. Qed.

(** A read never delivers more than it was asked for. *)
Lemma net_take_length : forall k s, (length (fst (net_take s k)) <= k)%nat.
Proof.
  induction k as [|k IH]; intro s; cbn; [lia|].
  destruct s as [| | |b s']; cbn; try lia. specialize (IH s'). lia.
Qed.

(** Taking exactly as many bytes as were delivered is idempotent: the
    delivered list is the script's prefix of its own length.  No consumer
    yet -- it is here for the same reason its stdin twin
    [stream_take_bytes_self] is, which is that reading the choice
    condition of a read spec BOTH WAYS needs it, and the first proof
    about a socket-reading program will.  Stated rather than claimed to
    be in use. *)
Lemma net_take_bytes_self : forall k s,
  fst (net_take s (length (fst (net_take s k))))
  = fst (net_take s k).
Proof.
  induction k as [|k IH]; intro s; [reflexivity|].
  destruct s as [| | |b s']; try reflexivity.
  cbn [net_take fst length]. rewrite IH. reflexivity.
Qed.

(** Re-taking exactly what was delivered leaves the same remainder — the
    lemma the read spec needs to know that consuming [length bs] bytes
    and consuming "the bytes it chose" are the same step. *)
Lemma net_take_rest_self : forall k s,
  snd (net_take s (length (fst (net_take s k))))
  = snd (net_take s k).
Proof.
  induction k as [|k IH]; intro s; [reflexivity|].
  destruct s as [| | |b s']; try reflexivity.
  cbn [net_take fst snd length]. rewrite IH. reflexivity.
Qed.

(** A nonempty delivery is only possible from a script whose head is a
    byte: each terminal delivers nothing, at every length. *)
Lemma net_take_nil_of_fin : forall k, fst (net_take NFin k) = [].
Proof. intro k. rewrite net_take_fin. reflexivity. Qed.
Lemma net_take_nil_of_rst : forall k, fst (net_take NRst k) = [].
Proof. intro k. rewrite net_take_rst. reflexivity. Qed.
Lemma net_take_nil_of_timedout : forall k, fst (net_take NTimedOut k) = [].
Proof. intro k. rewrite net_take_timedout. reflexivity. Qed.

(** The [NetStream] halves of [stream_take_add] and [stream_take_z]; see
    those for why the [Z]-indexed take exists and how it stays cheap. *)
Lemma net_take_add : forall a b s,
  net_take s (a + b)%nat
  = (fst (net_take s a) ++ fst (net_take (snd (net_take s a)) b),
     snd (net_take (snd (net_take s a)) b)).
Proof.
  induction a as [|a IH]; intros b s; cbn [Nat.add net_take fst snd].
  - destruct (net_take s b); reflexivity.
  - destruct s as [| | |c s'].
    + rewrite net_take_fin. reflexivity.
    + rewrite net_take_rst. reflexivity.
    + rewrite net_take_timedout. reflexivity.
    + cbn [net_take fst snd]. rewrite IH. reflexivity.
Qed.

Definition net_ended (s : NetStream) : bool :=
  match s with NCons _ _ => false | _ => true end.

Lemma net_take_ended : forall s k, net_ended s = true -> net_take s k = ([], s).
Proof. intros [| | |b s'] k H; try (destruct k; reflexivity). discriminate. Qed.

Fixpoint net_take_pos (s : NetStream) (p : positive)
    : list byte * NetStream :=
  match p with
  | xH => net_take s 1
  | xO p' =>
      let r1 := net_take_pos s p' in
      if net_ended (snd r1) then r1
      else let r2 := net_take_pos (snd r1) p' in (fst r1 ++ fst r2, snd r2)
  | xI p' =>
      let r1 := net_take_pos s p' in
      if net_ended (snd r1) then r1
      else
        let r2 := net_take_pos (snd r1) p' in
        if net_ended (snd r2) then (fst r1 ++ fst r2, snd r2)
        else let r3 := net_take (snd r2) 1 in
             (fst r1 ++ fst r2 ++ fst r3, snd r3)
  end.

Definition net_take_z (s : NetStream) (n : Z) : list byte * NetStream :=
  match n with
  | Zpos p => net_take_pos s p
  | _ => ([], s)
  end.

Lemma net_take_pos_eq : forall p s,
  net_take_pos s p = net_take s (Pos.to_nat p).
Proof.
  induction p as [p IH|p IH|]; intro s; cbn [net_take_pos].
  - rewrite Pos2Nat.inj_xI.
    replace (S (2 * Pos.to_nat p))%nat
      with (Pos.to_nat p + (Pos.to_nat p + 1))%nat by lia.
    rewrite net_take_add, (net_take_add (Pos.to_nat p) 1), !IH.
    destruct (net_ended (snd (net_take s (Pos.to_nat p)))) eqn:H1.
    + rewrite !(net_take_ended _ _ H1). cbn [fst snd app]. rewrite app_nil_r.
      now destruct (net_take s (Pos.to_nat p)).
    + destruct (net_ended (snd (net_take (snd (net_take s (Pos.to_nat p)))
                                          (Pos.to_nat p)))) eqn:H2.
      * rewrite (net_take_ended _ _ H2). cbn [fst snd app]. rewrite app_nil_r.
        now destruct (net_take (snd (net_take s (Pos.to_nat p))) (Pos.to_nat p)).
      * reflexivity.
  - rewrite Pos2Nat.inj_xO.
    replace (2 * Pos.to_nat p)%nat with (Pos.to_nat p + Pos.to_nat p)%nat
      by lia.
    rewrite net_take_add, !IH.
    destruct (net_ended (snd (net_take s (Pos.to_nat p)))) eqn:H1.
    + rewrite (net_take_ended _ _ H1). cbn [fst snd app]. rewrite app_nil_r.
      now destruct (net_take s (Pos.to_nat p)).
    + reflexivity.
  - reflexivity.
Qed.

Lemma net_take_z_eq : forall s n,
  net_take_z s n = net_take s (Z.to_nat n).
Proof.
  intros s [|p|p]; cbn [net_take_z Z.to_nat]; [reflexivity| |reflexivity].
  apply net_take_pos_eq.
Qed.

(** The address the peer's SYN carried: its IP source address and its
    TCP source port, both verbatim from the wire, both entirely the
    peer's choice.  Stored in NETWORK byte order, the order
    [struct sockaddr_in] holds them in and [inet_getname] copies them
    out in.

    NOTHING IN THIS MODEL READS IT YET.  [accept] with a non-NULL
    address argument is unmodeled here because [SyscallEffect] has no
    address export: the write [move_addr_to_user] performs cannot be
    expressed at all.  THAT is the blocker, and not the absence of a
    caller worth having — [getsockname] (204) and [getpeername] (205)
    are modeled, and decline their own address write over the same
    missing export.  So the peer address never reaches the guest
    and never reaches a trace.  It is carried anyway because it is a
    real degree of freedom of the environment — two connections that
    send identical bytes from different addresses are different
    connections on Linux — and because carrying it now keeps the shape
    of [ProcInput] stable when the call that reports it is modeled. *)
Record PeerAddr := mkPeer {
  pa_addr : bv 32;              (* sin_addr.s_addr, network order *)
  pa_port : bv 16               (* sin_port, network order *)
}.

(** THE CONNECTIONS THE ENVIRONMENT OFFERS, in the order [accept] hands
    them over.

    INFINITE — there is no nil.  [accept] must be RECEPTIVE
    ([Checks.Progress.receptive]: every syscall has an admissible
    outcome in every state), and a blocking [accept] on an exhausted
    queue has no answer at all: not a success, not an errno, and
    [Unmodeled] would make every source that loops on [accept] fail
    [modeled] on the one input that runs the queue out.  Since the queue
    is universally quantified, some input always would.

    THAT IS AN UNDER-APPROXIMATION: it excludes the environment in which [accept] blocks
    forever.  A source that would hang on Linux instead accepts another
    connection here, so a hang is not a behavior the theorem can
    distinguish.

    Being unable to run out is a different problem from being unable to
    FAIL, and it is fixed differently: [Net.Socket.accept4_spec] carries a
    live errno branch under [alt], so fd exhaustion and the environment
    failures the model does not decide still have an answer. *)
CoInductive NetQueue : Type :=
  | NConn (peer : PeerAddr) (script : NetStream) (rest : NetQueue).

(** THE QUIET ENVIRONMENT: connection after connection, each from
    0.0.0.0:0 with nothing to say — the peer opens the connection and
    closes its sending half at once, so every read on an accepted socket
    delivers 0.

    It is one point of the input space and carries no special status;
    it is here because fixtures and callers of the extracted checker both need
    SOME queue to name, and a queue that says nothing is the only one
    whose bytes neither of them has to predict.  Proofs about programs
    quantify over [in_net], as [Equivalence.strong_equiv] does — they do
    not use this. *)
CoFixpoint net_silent : NetQueue :=
  NConn (mkPeer (Z_to_bv 32 0) (Z_to_bv 16 0)) NFin net_silent.

(** The head connection's peer, script, and the queue behind it. *)
Definition nq_peer (q : NetQueue) : PeerAddr :=
  match q with NConn p _ _ => p end.
Definition nq_script (q : NetQueue) : NetStream :=
  match q with NConn _ s _ => s end.
Definition nq_rest (q : NetQueue) : NetQueue :=
  match q with NConn _ _ r => r end.

(* =========================================================================
   Model state — threaded across the whole run
   ========================================================================= *)

(** THE LIFE OF A SOCKET, as much of it as this model covers.

    Only AF_INET/SOCK_STREAM sockets ever enter the fd table:
    [Net.Socket.socket_spec] declines every other domain and type, so a
    [FdSocket] is always a TCP socket and the domain, type and protocol
    need not be stored.  (That is also why "listen on a UDP socket is
    -EOPNOTSUPP" never arises here: there are no UDP sockets.)

    - [SkFresh]      — created by [socket], not yet bound.  [read] is
                       -ENOTCONN; [accept] and a second [bind] are
                       -EINVAL; [listen] succeeds, autobinding an
                       ephemeral port (net/ipv4/inet_connection_sock.c:
                       inet_csk_listen_start).
    - [SkBound]      — [bind] accepted.  The address is not stored
                       because the only bind the model accepts is
                       INADDR_ANY on port 0; every other address needs
                       port-table state a one-process model does not
                       have, and is declined rather than guessed.
    - [SkListening]  — [listen] accepted.  [accept] draws from the
                       environment's queue; [read] is -ENOTCONN.
    - [SkConnected peer chan rx] — handed over by [accept].  [peer] is
                       the address the SYN carried, [chan] is the trace
                       channel this connection's bytes are reported on
                       (see [Net.Socket.conn_channel]), and [rx] is what the
                       peer has left to say.
    - [SkReset peer chan] — the peer's error has already been reported to
                       the program once (citations v6.12).  Reads answer 0 from here on,
                       exactly as they do once [rx] is [NFin] — so this
                       constructor changes NO read behaviour.  It exists
                       because those two are DIFFERENT TCP STATES and
                       collapsing them would be a wrong answer for the
                       send side.  A consumed FIN leaves the socket in
                       CLOSE_WAIT, which is in [tcp_sendmsg_locked]'s
                       accepted mask [TCPF_ESTABLISHED | TCPF_CLOSE_WAIT]
                       and where a send SUCCEEDS; a consumed RST or
                       timeout ran net/ipv4/tcp.c [tcp_done], leaving
                       TCP_CLOSE, where net/core/stream.c:
                       sk_stream_wait_connect answers -EPIPE.  Recording
                       the difference in the REPRESENTATION rather than
                       in a flag is the same move [NetStream]'s nullary
                       terminals make: the state that cannot send is a
                       different constructor, not a boolean somebody has
                       to remember to check.

    THE PER-CONNECTION STATE LIVES IN THE CONSTRUCTOR, not in fields
    beside it, so a listening socket cannot carry a byte stream and a
    fresh socket cannot carry a channel id: the states that have no
    stream have no place to put one.  And the socket state lives IN THE
    FD ENTRY rather than in a side table indexed by the entry, so
    [close] disposing of the fd disposes of the socket too — there is no
    table for a closed socket to leak into, and a reissued fd cannot
    inherit a dead peer's script. *)
Inductive SockState :=
  | SkFresh
  | SkBound
  | SkListening
  | SkConnected (peer : PeerAddr) (chan : word) (rx : NetStream)
  | SkReset (peer : PeerAddr) (chan : word).

(** [PIPE_BUF] (include/uapi/linux/limits.h), which on riscv64 is also
    [PAGE_SIZE]: the size of the page a pipe buffers bytes in, and the
    largest transfer Linux writes atomically. *)
Definition PIPE_BUF : Z := 4096%Z.

(** What the model records for one pipe: the bytes the queue currently
    holds, and how much of the PAGE those bytes live in has been written
    into — the merge high-water mark.

    Both are needed, and the second is the subtle one.  Everything this
    block asserts is fs/pipe.c at v6.18.46 (commit 1f99e9ab748f).  Linux
    buffers a pipe in whole pages held in a ring [alloc_pipe_info] sizes
    at [PIPE_DEF_BUFFERS] (:795, :824), whose value 16 is
    include/linux/pipe_fs_i.h, and counts fullness in
    SLOTS, not bytes ([pipe_full] against [pipe->max_usage], :510).  A
    write tops up the last slot only when
    [buf->offset + buf->len + chars <= PAGE_SIZE] ([anon_pipe_write]'s
    merge test, :480-483), and a READ does not give that room back:
    [anon_pipe_read] advances [buf->offset] by exactly what it consumed
    and shortens [buf->len] (:350-351), leaving their SUM — the
    watermark — unchanged.  So the bytes a pipe can hold before it blocks
    is not 16 pages of data but a function of the write sizes: sixteen
    2049-byte writes fill it at 32784 bytes, and a pathological
    write/read alternation fills it at sixteen.  A byte-counted capacity
    would therefore admit full writes where Linux blocks.

    The model keeps the mark instead and stays inside ONE slot, which is
    the whole of what it has to prove: with [pipe_write_room] below, a
    modeled pipe's ring occupancy is never more than one, so [pipe_full]
    is never true and no modeled write can block.  A write that would
    need a second slot is declined rather than guessed at. *)
Definition PipeBuf : Type := list byte * Z.

(** An open file descriptor, carrying its ACCESS MODE so the model can
    enforce -EBADF on wrong-direction I/O, as Linux does:

    - [FdChannel chan]: an external channel.  Channel fds only come from
      [init_model], and their mode is determined by the channel id:
      stdin (0) is read-only, stdout (1) and stderr (2) are write-only.
      That is the direction PIPED STDIO has, and it is an ASSUMPTION
      about the environment rather than a fact about the fd number:
      Linux reads the direction off the description's [FMODE_*] bits,
      so a process handed a connected socket on fd 0 — every
      inetd-style server — may write it, and this model answers -EBADF.
    - [FdFile p off]: a file opened O_RDONLY (read-only); write is
      -EBADF.
    - [FdFileW p off]: a file opened O_WRONLY|O_CREAT|O_TRUNC
      (write-only); read is -EBADF.
    - [FdFileA p off]: a file opened O_WRONLY|O_CREAT|O_APPEND
      (write-only, APPEND MODE); read is -EBADF.  A SEPARATE
      CONSTRUCTOR RATHER THAN A FLAG ON [FdFileW], and the reason is
      which arms have to notice.  The two kinds differ in where a write
      LANDS: [iocb_flags] (include/linux/fs.h) turns O_APPEND into
      IOCB_APPEND, and [generic_write_checks] (mm/filemap.c) then
      overwrites the iocb's position with [i_size_read(inode)], so every
      write through this fd goes to the CURRENT end of the file whatever
      [off] says and whatever an [lseek] did to it (Linux v6.18.46).  A
      boolean field on [FdFileW] would leave every existing [FdFileW _ _]
      arm silently absorbing an append fd -- including
      [Fs.Fcntl.setfl_noop_on], whose 0 for such an fd would be UNSOUND
      (see that definition).  A constructor makes each of those a compile
      error instead, which is the whole reason this type enumerates.

      [off] IS STILL CARRIED, and not because a write reads it: it is
      [f_pos], which [lseek] still repositions and reports on an append
      fd, and which a write leaves at the new end of file.  Nothing
      derives a write POSITION from it.
    - [FdFileRW p off]: a file opened O_RDWR (READ-WRITE), possibly
      with O_CREAT, O_TRUNC or O_EXCL; see [Open.rdwr_open_word].  It is
      the only file kind on which BOTH directions answer: a read is the
      [FdFile] arm and a write the [FdFileW] arm, at the one [f_pos]
      both of them advance.  That single shared position is the whole
      of what makes this a kind rather than a pair of fds: Linux keeps
      [f_pos] on the [struct file], not on the access mode, so a read
      of n bytes moves the offset the next WRITE lands at, and a
      program that reads a header and then writes over the record after
      it depends on exactly that.

      A SEPARATE CONSTRUCTOR RATHER THAN A FLAG, for the reason the
      whole type enumerates: every existing [FdFile _ _] arm answers
      -EBADF to a write and every [FdFileW _ _] arm -EBADF to a read,
      and both of those are WRONG for this kind rather than
      conservative.  A flag would leave each of them absorbing an
      O_RDWR fd silently and reporting a -EBADF Linux never returns —
      a modeled wrong answer, not a gap.  A constructor makes each site
      a compile error.

      [off] IS AN ORDINARY [f_pos], unlike [FdFileA]'s: reads and
      writes both start there and both advance it, and [lseek] moves
      it for either direction.
    - [FdDir]: a directory fd (from [openat] of "." or "..", the two
      paths that name a directory without a lookup; see
      [Open.path_is_dirref]).  It carries NO path, which is what makes
      those two answerable by one arm: nothing below can tell the
      working directory from its parent.  No I/O: read yields
      -EISDIR and write -EBADF, as Linux does on an O_RDONLY directory
      fd; directory enumeration (getdents64) answers only where nothing
      is listed — [filldir64]'s -EINVAL for a buffer too small for any
      entry — and the LISTING itself stays unmodeled and fail-closed,
      which is what keeps the missing path from mattering
      ([Readdir.getdents64_spec]).
    - [FdSocket sk]: an AF_INET/SOCK_STREAM socket, carrying its whole
      state (see [SockState]).  READABLE — a socket is never opened
      write-only, so the -EBADF gate must let it through and the read
      specs answer for it; a socket fd that failed that gate would
      report a FALSE -EBADF, which is a modeled wrong answer rather than
      a modeling gap.  WRITING one is unmodeled, permanently: on a reset
      connection write(2) returns -EPIPE *and raises SIGPIPE*, whose
      default action kills the thread group
      (net/core/stream.c [sk_stream_error], kernel/signal.c [get_signal]),
      and a spec's outcomes are [Ok] and [Unmodeled] only — "the process
      died" has no encoding, and halting with 141 cannot be told apart
      from a voluntary exit(141).  The socket write path is
      sendto/sendmsg with MSG_NOSIGNAL, which is decidable from a
      syscall argument; it is not modeled here.
    - [FdPipe id writer]: ONE END of a pipe (from [pipe2]; see
      [Pipe.pipe2_spec]).  [id] names the pipe — BOTH ends carry the
      same one — and [writer] says which end this is: [false] is the
      read end (fd[0]; read-only, write is -EBADF) and [true] the write
      end (fd[1]; write-only, read is -EBADF).  That is fs/pipe.c's own
      split: [create_pipe_files] opens [res[0]] O_RDONLY and [res[1]]
      O_WRONLY, and [__do_pipe_flags] hands them back as [fd[0] = fdr]
      and [fd[1] = fdw].  The buffered bytes live in the model's
      [m_pipes] side table, keyed by [id], because they are shared
      BETWEEN the two ends: a byte written through the write end is read
      back through the read end, and neither fd owns it.  This is the
      first fd whose contents come from the program itself rather than
      from the environment or the file system.

      NOT EVERY SITE DISPATCHING ON FD KIND ANSWERS A PIPE END WITH
      MODELED BEHAVIOR.  Where this development has no derivation to
      offer — whether a pipe end is pollable, what [fstat] reports, what
      [clone] may do with one — the arm FAILS CLOSED and names what a
      real answer would have to be derived from, rather than guessing.
      An [FdEntry] match that a new constructor does not break is a
      match that would absorb it silently, so those sites enumerate.
    - [FdDevNull rd wr]: the character device /dev/null (major 1, minor
      3), opened by [Open.openat_spec]'s arm for exactly that pathname
      ([Uapi.devnull_path]).  It is the first descriptor whose object
      is a DEVICE rather than a file, a channel, a socket or a pipe,
      and the point of it is that it carries NOTHING: Linux's
      [null_fops] (drivers/char/mem.c, v6.18.46) reads 0 bytes
      ([read_null]), discards every write and reports the count
      ([write_null]), and pins [f_pos] at 0 on every [lseek]
      ([null_lseek]), so no modeled operation on the descriptor can
      observe a position, a buffer or a peer.  [rd] and [wr] are the
      access mode the open granted — [do_dentry_open] (fs/open.c) sets
      FMODE_READ and FMODE_WRITE from it — and they decide the one
      thing that IS observable: [vfs_read] and [vfs_write]
      (fs/read_write.c) answer -EBADF on a descriptor lacking the
      mode, ahead of the device.  [openat] mints [FdDevNull true false]
      for O_RDONLY, [false true] for O_WRONLY and [true true] for
      O_RDWR; [false false] is not constructible.

      THE ENVIRONMENT ASSUMPTION IT RESTS ON is stated at the openat
      arm and nowhere else: the environment's /dev/null is the null device.
      Every arm below that answers for this kind derives its answer
      from [null_fops] and the VFS path that reaches it, and every arm
      that cannot fails closed, so that a held-open /dev/null costs a
      run nothing and a program that does something with it the model
      has no derivation for is declined rather than guessed.
    - [FdUrandom]: the character device /dev/urandom (major 1, minor
      9), opened read-only by [Open.openat_spec]'s arm for exactly that
      pathname ([Uapi.urandom_path]); the write and read-write words
      are declined there, so the kind carries no access mode -- every
      descriptor of it has FMODE_READ and lacks FMODE_WRITE.  Its
      reads deliver the front of the run's DECLARED stream,
      [m_urandom] (seeded from [ProcInput]'s [in_urandom]), and advance
      it; the bytes are an input of the run, not a choice, and the
      same stream is read on both sides of an equivalence.  Linux's
      [urandom_fops] (drivers/char/random.c, v6.18.46) reads nothing
      off the [struct file] -- [urandom_read_iter] consults the
      generator and the iterator only, [noop_llseek] hands back an
      [f_pos] no modeled operation moves -- so nothing on the
      descriptor is observable beyond the bytes, and one stream serves
      every descriptor.  The arms that answer for it derive the answer
      from [urandom_fops] and the VFS path that reaches it; the rest
      fail closed.  THE ENVIRONMENT ASSUMPTION IT RESTS ON -- the
      environment's /dev/urandom is the random device -- is stated once, at
      the openat arm, and pointed to from everywhere else. *)
Inductive FdEntry :=
  | FdChannel (chan : word)
  | FdFile (p : path) (offset : word)
  | FdFileW (p : path) (offset : word)
  | FdFileA (p : path) (offset : word)
  | FdFileRW (p : path) (offset : word)
  | FdDir
  | FdSocket (sk : SockState)
  | FdPipe (id : word) (writer : bool)
  | FdDevNull (rd wr : bool)
  | FdUrandom.

(** Virtual-memory bookkeeping: a ledger of allocator decisions the model
    has already committed to (the flat byte-map memory can't encode
    "allocated but untouched").  Intervals are (base, size) pairs of
    words; all overlap/bound arithmetic on them happens in [Z] over
    [bv_unsigned] (see [iv_overlap]).  Seven purposes:
    (a) [vm_reserved] — the address space the kernel already used at
        [execve]: the page-rounded LOAD segments of the binary
        ([Run.segments_reserved]).  IMMUTABLE for the whole run, and held
        in a separate field on purpose: [munmap] removes [vm_maps]
        entries by base address, and a stray [munmap(seg_base, …)] must
        not be able to unreserve the binary image;
    (b) [vm_maps] — live anonymous mappings as [(lo, size)] intervals,
        including brk-grow grants — so allocator grants are handed out
        DISJOINT from each other and from the image ([region_free]
        against [vm_reserved ++ vm_maps]).  Read that as a PAGE-granular
        guarantee, which is what it is: no page-aligned address is ever
        owned by two entries, and every base a syscall can name is page
        aligned, so a base determines its entry.  Byte-level overlap IS
        reachable, because a brk grow within one page is checked by
        neither [region_free] nor Linux itself (see [live_bytes] below);
    (c) [vm_noaccess] — physical page ranges currently protected with
        PROT_NONE.  Ordinarily they are subranges of [vm_maps].  A brk
        shrink within its final page is the deliberate exception: the
        byte-granular [vm_maps] tail is removed while Linux keeps the whole
        page mapped and protected, so [vm_noaccess] may transiently extend
        to [PAGE_ALIGN(vm_brk)].  It still blocks placement through the
        containing brk page; mprotect also requires [vm_maps] containment,
        so the logical tail cannot be exposed until a same-page regrow owns
        it again.  Protected pages consume budget through their logical
        [vm_maps] ownership, and the machine overlay contains no bytes for
        them until a modeled mprotect makes them rw again;
    (d) [vm_start_brk] — Linux's [mm->start_brk]: the ASLR-placed base of
        the heap, set at [execve] ([Run.mi_init_brk]) and IMMUTABLE for
        the whole run.  It is the kernel's [min_brk]: a [brk] request
        below it is INVALID (returns the break unchanged), including
        requests in the ASLR gap between the image top and the base;
    (e) [vm_brk] — the CURRENT program break — to model [brk] (return the
        unchanged break, and anchor the zero-fill of a grow);
    (f) [vm_limit] — the BACKED-MEMORY BUDGET of this run, in bytes:
        no operation may push charged anonymous backing
        ([vm_backing_used], including first-touched sparse pages) above it.
        Once the budget is spent, ordinary eager allocator operations admit
        only their failure resolutions; a MAP_NORESERVE grant may still
        reserve virtual space, but an access that would materialize another
        page takes the fault/error transition.  The
        out-of-memory point is forced, at a bound that is a function of
        the program's own grant/free history rather than of the
        quantified ASLR placements.  A parameter of the run
        (like the initial break), IMMUTABLE once seeded by
        [Run.mi_alloc_limit]; [Equivalence.strong_equiv] pins it to
        [source_alloc_limit]/[target_alloc_limit] per role, and a
        caller may seed smaller budgets to make
        exhaustion cheap to reach;
    (g) [vm_mmap_base] — Linux's [mm->mmap_base]: the top-down search
        bound of [get_unmapped_area], set once at [execve]
        ([arch_pick_mmap_layout] via the generic mm/util.c layout — see
        [mmap_base_min]) and IMMUTABLE for the whole run.  Like the
        initial break it is a quantified parameter of the run
        ([Run.mi_mmap_base], any [Run.valid_mmap_base] value,
        independent per binary).  NO SPEC ARM READS THIS FIELD'S VALUE.
        Preference-free placement says only
        that the address is page-aligned, inside the user address space
        and disjoint from every recorded mapping — a rule with no base
        in it (the argument is in [Mmap.mmap_spec]'s placement section).
        The field is NOT thereby inert and must not be removed as one:
        [Run.valid_mmap_base] is a conjunct of [Run.valid_entry], which
        [Equivalence.strong_universal_T] quantifies its entries under,
        and discharging it is a required step of
        [Equivalence.image_brk_satisfiable_entry], the tree's
        anti-vacuity lemma.  It is the PREDICATE that is load-bearing in
        the spec, not the value.  Outside the spec, the ASan plan
        checker's placement gate ([Common.AsanCeil.placement_ok], taken
        as its named [placement_policy] hypothesis) reads the value, and
        [Common.AsanInit] relies on the predicate's floor (see
        [mmap_base_min]).
        A base of 0 is what [mkVmMaps] seeds and means only "no base
        recorded"; no state reachable from [State.init_model] under
        [Run.valid_mmap_base] carries it;
    (h) [vm_init_sp] — the stack pointer [execve] handed this run
        ([Run.mi_init_sp], any [Run.valid_sp] value, quantified
        independently per binary), IMMUTABLE for the whole run.  The
        allocator reads it through [alloc_top] below: it is what keeps
        every grant off THIS run's stack.  The stack itself has no
        reservation entry — see [alloc_top] for why a bound does the
        job a reservation would. *)
Record VmMaps := mkVmMapsFull {
  vm_reserved  : list (word * word);
  vm_maps      : list (word * word);
  vm_noaccess  : list (word * word);
  vm_start_brk : word;
  vm_brk       : word;
  vm_limit     : Z;
  vm_mmap_base : word;
  vm_init_sp   : word;
}.

(** ALLOCATION TOP: no allocator grant (anonymous mmap, brk grow, a
    moved or grown mremap) may reach at or above this address, so every
    grant is disjoint from the dynamic stack [sp - stack_max_size, sp)
    and from the argv/envp/auxv block above [sp] — for the [sp] THIS run
    was started with.

    A bound rather than a reservation entry, on purpose: [region_free]
    over a list holding a symbolic [sp]-based interval turns every
    concrete [grant_ok ... = true] in the examples into an open [bv]
    term, while one [Z] inequality keeps [sp] a single [lia] atom.  The
    price is that a hinted grant INTO the stack band — which Linux
    honours when the hint is free — is refused here rather than
    declined.

    Computed in [Z] from a [word], so it is below 2^64 for every ledger
    ([alloc_top_lt]) with no wrap argument: that is what lets a proof
    conclude from [a + n <= alloc_top h] that [a + n] is a real address
    and never an encoded errno.

    [stack_max_size] stays a constant.  [Sys.v]'s [prlimit64] note
    argues why [RLIMIT_STACK] is not modelled; until it is, 8 MiB is the
    only stack size the model knows. *)
Definition alloc_top (h : VmMaps) : Z :=
  (bv_unsigned (vm_init_sp h) - stack_max_size)%Z.

(** The whole stack fits above the top, so a grant that ends at or
    below it ends a stack's width short of 2^64 — room enough that its
    address can never be read as an encoded errno. *)
Lemma alloc_top_room : forall h, (alloc_top h + stack_max_size < two_pow_64)%Z.
Proof.
  intros h. unfold alloc_top, two_pow_64.
  pose proof (bv_unsigned_in_range 64 (vm_init_sp h)) as [_ Hhi].
  unfold bv_modulus in Hhi. cbn in Hhi. lia.
Qed.

Lemma alloc_top_lt : forall h, (alloc_top h < two_pow_64)%Z.
Proof.
  intros h. pose proof (alloc_top_room h). unfold stack_max_size in *. lia.
Qed.

(** One page above the top is still an address: the brk gate tests the
    page above the installed ones ([Sys/Mm/Mmap.brk_grow_ok]), and this
    is the bound that keeps that range from wrapping. *)
Lemma alloc_top_page_lt : forall h, (alloc_top h + page_size < two_pow_64)%Z.
Proof.
  intros h. pose proof (alloc_top_room h).
  unfold stack_max_size, page_size in *. lia.
Qed.

Lemma stack_max_size_val : stack_max_size = 8388608%Z.
Proof. reflexivity. Qed.

(** Put [alloc_top_room] in scope for every ledger a hypothesis
    mentions, with [stack_max_size]'s value beside it, so a [lia] that
    needs a grant's end to be a word — or to clear the errno band —
    can find both without the proof naming the ledger, which a [subst]
    may have renamed. *)
Ltac alloc_top_bounds :=
  repeat match goal with
  | H : context [alloc_top ?h] |- _ =>
      lazymatch goal with
      | _ : (alloc_top h + stack_max_size < two_pow_64)%Z |- _ => fail
      | _ => pose proof (alloc_top_room h)
      end
  | |- context [alloc_top ?h] =>
      lazymatch goal with
      | _ : (alloc_top h + stack_max_size < two_pow_64)%Z |- _ => fail
      | _ => pose proof (alloc_top_room h)
      end
  end;
  lazymatch goal with
  | _ : stack_max_size = _ |- _ => idtac
  | _ => pose proof stack_max_size_val
  end.

(** Compatibility constructor for ledgers containing only rw memory.
    Existing examples and allocator simulations need not mention the
    empty protection ledger, nor the placement base (seeded 0, which
    means "no base recorded" and which nothing in the spec reads; see
    the [vm_mmap_base] note above).  The stack pointer is seeded at the
    BOTTOM of the SP window, so a hand-built ledger's [alloc_top] is the
    smallest any admissible run has: what such a ledger admits, every
    run admits. *)
Definition mkVmMaps (reserved maps : list (word * word))
    (start_brk brk : word) (limit : Z) : VmMaps :=
  mkVmMapsFull reserved maps [] start_brk brk limit (Z_to_bv 64 0)
    (Z_to_bv 64 sp_window_lo).

Lemma alloc_top_mkVmMaps : forall reserved maps start_brk brk limit,
  alloc_top (mkVmMaps reserved maps start_brk brk limit) = 0x7fff7f800000%Z.
Proof. reflexivity. Qed.

(** Bytes currently granted by a ledger: the sum of its interval sizes.

    The [vm_maps] intervals are pairwise disjoint AT PAGE GRANULARITY —
    no page-aligned address is owned by two entries — which
    [Checks/VmMapsDisjoint.check_syscall_preserves_vm_wf] proves is
    preserved by every modeled syscall from [init_model] on.  They are
    NOT pairwise disjoint byte for byte, so this sum is NEITHER AN UPPER
    NOR A LOWER BOUND on the granted-and-not-freed bytes — two sub-page
    brk gaps move it in OPPOSITE directions — both for [vm_live_bytes]
    here and downstream in [vm_backed_bytes] and [vm_backing_used], which
    measure this same sum over ledgers derived from [vm_maps] by
    subtraction.

    OVER-COUNT, from a brk GROW that does not cross a page boundary.
    [Sys/Mm/Mmap.brk_grants] records the logical range [[old, r)] while
    [Sys/Mm/Mmap.brk_grow_ok] tests the page-rounded one (plus the page
    above it) and tests nothing when that range is EMPTY, as it is for
    such a grow, so the grant enters with no address-space test
    and entries can overlap — the same bytes counted twice.  That one is
    FAITHFUL rather than a slip: [SYSCALL_DEFINE1(brk)] takes its
    [oldbrk == newbrk] early exit before consulting any VMA, so Linux too
    lets the break walk over bytes another mapping owns (reachable by
    unmapping the brk VMA and mapping over it).
    [Checks/VmMapsDisjoint] carries a checked six-syscall execution that
    reaches exactly that state.  Over-counting can only bring the forced
    out-of-memory point EARLIER, which is the safe direction.

    UNDER-COUNT, from a brk SHRINK that does not cross a page boundary,
    and this one is a KNOWN INCONSISTENCY rather than faithful modelling.
    [Sys/Mm/Mmap.brk_maps_next]'s shrink arm subtracts the RAW range
    [[r, b)] from [vm_maps], while [Sys/Mm/Mmap.brk_unmaps] reports the
    PAGE-ROUNDED one, which is empty for such a shrink.  So the effect
    says nothing was freed, Linux's [oldbrk == newbrk] exit frees no VMA
    at all, and the ledger drops the bytes anyway:
    [Checks/VmMapsDisjoint]'s [wit_step6] shrinks the break by 10 bytes
    inside one page and the ledger goes from [[(65536, 4096)]] to
    [[(65536, 1990); (67536, 2096)]] — 4096 bytes to 4086, ten granted,
    unfreed, still-mapped bytes gone from the sum.  Under-counting moves
    the forced out-of-memory point LATER, which is the UNSAFE direction,
    and no gate compensates for it.  The two are not reconciled.

    [munmap], a shrinking [mremap], and a [brk] shrink return their bytes
    to the budget by shrinking the ledger.  Placement plays no part — the
    budget meters BYTES, not addresses — which is what makes the forced
    out-of-memory point deterministic. *)
Fixpoint live_bytes (maps : list (word * word)) : Z :=
  match maps with
  | [] => 0%Z
  | (_, sz) :: r => (bv_unsigned sz + live_bytes r)%Z
  end.
Definition vm_live_bytes (h : VmMaps) : Z := live_bytes (vm_maps h).

(** [Model] IS A RECORD OF SUBSYSTEMS, not a flat list of fields, and the
    reason is the setters.  A flat record needs one setter per field and each
    one has to restate every field it does not change, so adding a field
    rewrites every setter -- and a change about clocks and a change about
    credentials collide over state neither one shares.  Nested, a new field
    inside a subsystem touches only that subsystem's record and its own
    setters.

    The accessors and [mkModel] below give a flat view, so nothing outside
    this file sees the nesting: [m_fds m] reads the fd table, and [mkModel]
    takes the seven components in order.

    ORDINARY PROJECTIONS, deliberately.  The example proofs reduce with
    explicit constant lists ([cbn [with_fds m_fds ...]]), and [cbn] with a
    list unfolds only what the list names -- which a PRIMITIVE projection
    cannot be.  Making these primitive would put the nesting beyond the reach
    of every such list. *)

(** The open file descriptors, and the pipes some of them name.

    [fdst_pipes] is the PIPE BUFFERS, keyed by pipe id (see [pipe_lookup]).
    A side table rather than a payload on [FdEntry] because the queue is
    SHARED by two fds and outlives either of them ([close] of one end leaves
    the other end's view intact).  It sits in this subsystem because every
    reference to a pipe in this model is an fd in [fdst_table], and the two
    are read together: which ends are still open is derived from the table
    ([pipe_end_live]) rather than counted.  Not observable: pipe bytes never
    reach the trace, so two runs that differ only in what a pipe holds are
    still equivalent — see [Pipe.pipe2_spec]. *)
Record FdState := mkFdState {
  fdst_table : list (word * FdEntry);
  fdst_pipes : list (word * PipeBuf);
}.

(** The virtual-memory subsystem.  [vmst_lazy] records page-aligned sparse
    anonymous reservations whose backing is charged on first data access;
    [vmst_materialized] is the deduplicated set of page bases already charged.
    These are process-accounting ledgers, not physical frames or page tables. *)
Record VmState := mkVmState {
  vmst_maps : VmMaps;
  vmst_lazy : list (word * word);
  vmst_materialized : list word;
}.

(** The channels.  Standard input carries the UNCONSUMED remainder of the
    run's input stream (see [InputStream]); the network carries the
    connections [accept] has not yet handed over, which is the same kind
    of thing for the same reason. *)
Record IoState := mkIoState {
  iost_stdin : InputStream;
  iost_urandom : InputStream;
    (* the UNCONSUMED remainder of the random device's declared byte
       stream -- seeded from [in_urandom] and consumed by every read of
       an [FdUrandom] descriptor, exactly as [iost_stdin] is seeded from
       [in_stdin] and consumed by a read of channel 0.  One stream for
       the device rather than one per descriptor, because the
       declaration is about what the DEVICE hands out in order, and
       Linux's generator has no per-file state either
       ([urandom_read_iter], drivers/char/random.c, v6.18.46, reads
       nothing off the [struct file]) *)
  iost_net : NetQueue;
    (* the connections [accept] has NOT yet handed over — seeded from
       [in_net] and consumed one per successful accept, exactly as
       [iost_stdin] is seeded from [in_stdin] and consumed by read *)
  iost_conn_ix : word;
    (* how many connections [accept] HAS handed over.  Its only use is
       naming the trace channel of the next one: see
       [Net.Socket.conn_channel] *)
}.

(** The interpreted file system. *)
Record FsState := mkFsState { fsst_image : Fs.Fs }.

(** The process's UNIX credentials.  Six ids, in the kernel's own
    grouping ([include/linux/cred.h], [struct cred]): the REAL id, which
    says who owns the process; the EFFECTIVE id, which every permission
    check consults; and the SAVED set-id, which a process that has
    dropped its effective id may return to.  Each is a [word] holding a
    32-bit value, because every one of these syscalls declares its
    arguments [uid_t]/[gid_t] and the kernel truncates a 64-bit register
    to that width before it looks at the value (see [Syscall.uid32]).

    The kernel's [struct cred] carries fields this record does not, each
    because nothing the model can observe depends on it:

    - [fsuid]/[fsgid], the ids filesystem permission checks use.  They
      follow [euid]/[egid] on every setter modeled here, and the model's
      file system ([Fs.Fs]) has no permission bits, so no modeled
      syscall can tell them apart from the effective ids.
    - the CAPABILITY sets.  See [creds_privileged] below for what the
      model puts in their place and what that assumes about the
      environment.

    The supplementary GROUP LIST *is* carried, as [cr_groups], and the
    reason is [getgroups] (158): [Kernel.Groups.getgroups_spec] reports
    its LENGTH, so the list is observable.  The
    other two channels a real process could read it through stay shut —
    [Fs] has no group checks, and the model has no /proc, which is the
    least obvious of the three (fs/proc/array.c, [task_state], the
    [Groups:] line).  Carrying the ELEMENTS as well as the length is
    deliberate: they are what [getgroups]'s array-writing form would
    copy out, and what [Kernel.Groups.setgroups_spec]'s successful half
    would write, so both of those declines are declines of the WRITE and
    not of the state.  A [Creds] that held only a count would have to
    change shape before either could be finished. *)
Record Creds := mkCreds {
  cr_uid  : word;   (* real user id *)
  cr_euid : word;   (* effective user id *)
  cr_suid : word;   (* saved set-user-id *)
  cr_gid  : word;   (* real group id *)
  cr_egid : word;   (* effective group id *)
  cr_sgid : word;   (* saved set-group-id *)
  cr_groups : list word
    (* the supplementary group list, in the order the kernel stores it:
       [struct group_info]'s [gid] array, whose [ngroups] is what
       [Sys.Kernel.Groups.getgroups_spec] reports.  Each element is a
       [gid_t], which is [__kernel_gid32_t] and so 32 bits wide
       (include/uapi/asm-generic/posix_types.h), held in a [word] the
       same way the six ids above are. *)
}.

(** WHAT "PRIVILEGED" MEANS HERE, and what it assumes.

    The kernel never asks whether a caller is root.  Each credential
    setter asks [ns_capable_setid(old->user_ns, CAP_SETUID)] (or
    CAP_SETGID), which reads one bit out of [cred->cap_effective]
    (Linux v6.18.46, commit 1f99e9ab748f, kernel/capability.c,
    [ns_capable_setid]; security/commoncap.c, [cap_capable_helper], the
    inline the tracing wrapper [cap_capable] calls — v6.14 moved the
    loop out of [cap_capable] to add a tracepoint, and the answer it
    computes for the init user namespace,
    [cap_raised(cred->cap_effective, cap) ? 0 : -EPERM], is unchanged
    from v6.10 through v6.18).  The model carries no capability sets,
    so it answers the question with the effective uid instead.

    That is exact, not a guess, PROVIDED: the init user namespace; the
    executed binary carries no file capabilities; no ambient
    capabilities; default securebits — none of SECURE_NOROOT,
    SECURE_KEEP_CAPS, SECURE_NO_SETUID_FIXUP; and an UNNARROWED
    capability bounding set.  The last is easy to miss and is not
    implied by the others: [handle_privileged_root] grants legacy root
    [new->cap_permitted = cap_combine(old->cap_bset, old->cap_inheritable)]
    (security/commoncap.c), so an ancestor that ran
    [prctl(PR_CAPBSET_DROP, CAP_SETUID)] leaves every later exec with
    euid 0 and no CAP_SETUID at all.  Under those,
    [cap_emulate_setxuid] (security/commoncap.c, byte-identical at all
    six tags in the window) runs on every [set*uid] and maintains

      CAP_SETUID in cap_effective  <->  euid = 0

    in both directions: it clears [cap_effective] on every euid 0 ->
    non-0 transition, restores [cap_effective = cap_permitted] on
    non-0 -> 0, and clears [cap_permitted] outright once ALL of uid,
    euid and suid have left 0.  The last case is absorbing rather than a
    counterexample: from it, [__sys_setuid]'s unprivileged branch can
    reach only the (non-zero) real and saved uids and [__sys_setresuid]'s
    only the three (non-zero) old ids, so euid = 0 is unreachable and
    both sides of the biconditional stay false forever.  [setgid] and
    [setresgid] never touch capabilities at all.

    Each excluded condition breaks the biconditional in a DIFFERENT
    direction, which is why they are assumptions and not slack: file
    capabilities, ambient capabilities and a non-init user namespace give
    a non-root process the capability (the model would then refuse a call
    the kernel allows); SECURE_NOROOT and a narrowed bounding set
    withhold it from root (the model would allow a call the kernel
    refuses).  A run in any of those environments is outside this model.

    [init_model] pins the process's starting point to an ordinary exec —
    it derives the effective and saved ids from the real ones rather than
    taking them as input — which is the same world. *)
Definition creds_privileged (c : Creds) : bool :=
  bv_eqb (cr_euid c) (Z_to_bv 64 0).

(** The process itself: whether it has halted, its identity, who it runs
    as, and whether it has led a session. *)
Record ProcState := mkProcState {
  procst_halted : option word;   (* [Some x] once the process is OVER.  Two
                                    ways to get there and the payload differs:
                                    after exit/exit_group it is the exit code
                                    ([Kernel.Exit.exit_spec]), and after a
                                    fatal signal it is the SIGNAL NUMBER
                                    (whichever of [Kernel.Signal.send_sigabrt]
                                    and [Kernel.Signal.sigmask_deliver_model]
                                    took it).
                                    [procst_killed] is what says which, and it
                                    is read by exactly two places --
                                    [Run.sstep_exit], which declines a death by
                                    signal, and [Run.sstep_killed], which
                                    takes it.  Every other rule reads only
                                    whether this field is [None], which is the
                                    reason a kill writes it at all: a process
                                    that has been killed must stop executing
                                    instructions, and that is the premise those
                                    rules already carry *)
  procst_tid : option word;      (* the process identity, pinned by whichever
                                    of set_tid_address, getpid and a
                                    SUCCESSFUL setsid runs first; the kernel
                                    picks it at clone time, the model records
                                    it the first time it becomes observable,
                                    and every later query returns the same
                                    value.  That all three report the SAME
                                    value is not general: set_tid_address
                                    returns [task_pid_vnr(current)], a tid,
                                    and setsid returns the group leader's
                                    vpid, a tgid.  They coincide because this
                                    model has one thread.  That rests on
                                    the clone FLAG WORD, not on the
                                    number: [clone] (220) and [clone3]
                                    (435) are modeled, but
                                    [Fork.clone_fork_flags_b] admits
                                    [SIGCHLD] alone and
                                    [Checks.ProcessCreation.clone_sharing_flags_unmodeled]
                                    (with
                                    [clone3_sharing_flags_unmodeled]
                                    the same for 435) forces
                                    [Unmodeled] on any bit of
                                    [clone_sharing_bits], [CLONE_THREAD]
                                    among them.  Widening that predicate
                                    breaks the proof rather than this
                                    comment *)
  procst_creds : Creds;          (* the process's credentials: seeded from the
                                    run's [ProcInput] by [init_model] and
                                    mutated by the credential setters
                                    ([Kernel.Sys.setid_spec] and its
                                    siblings) *)
  procst_setsid_succeeded : bool; (* whether a setsid has already succeeded,
                                    which is what makes every later one
                                    -EPERM.  Only a success is recorded: a
                                    failure can be followed by a success on a
                                    real kernel.  The asymmetry is
                                    [Kernel.Sys.setsid_spec]'s subject *)
  procst_sigmask : word;         (* the signals the process has BLOCKED --
                                    Linux's [task_struct.blocked], as the one
                                    64-bit word riscv64's [sigset_t] is
                                    ([Uapi.NSIG_BYTES] = 8, [_NSIG] = 64).
                                    Seeded from [ProcInput]'s [in_sigmask] by
                                    [init_model] and changed only by
                                    [Kernel.Signal.rt_sigprocmask_spec].

                                    IT IS AN INPUT, NOT A CONSTANT, because
                                    execve does not reset the mask: [fs/exec.c]
                                    never names [blocked] and
                                    [begin_new_exec]'s [flush_signal_handlers]
                                    walks [sighand->action] only (Linux
                                    v6.18.46, commit 1f99e9ab748f).  So the
                                    mask a process starts with is entirely the
                                    launching environment's, exactly as
                                    [in_uid] and the ASLR'd stack pointer are.

                                    ONE WORD, NOT A BYTE LIST, the opposite of
                                    [limst_core]: that field is stored as bytes
                                    to avoid a round trip through a decoded
                                    pair, and this one is stored decoded
                                    because the three [how] arithmetics
                                    ([sigorsets], [sigandnsets], assignment --
                                    kernel/signal.c, [sigprocmask]) are
                                    bitwise operations on it.  The encoding
                                    happens once, where the mask is copied out
                                    to [oset] *)
  procst_children : bool         (* whether this process has acquired a child
                                    or a tracee.  [false] in [mkModel];
                                    [Kernel.Fork.clone_resolve] sets it on its
                                    SUCCESS branch and nothing else does, so
                                    [Kernel.Exit.wait4_spec] stops answering
                                    -ECHILD for a process that now has
                                    something to reap.  See the launcher
                                    premise on [Kernel.Exit.wait4_spec]
                                    and [Checks.Examples.wait4_with_a_child_is_unmodeled],
                                    which is the tripwire and does not live in
                                    a file a process-creation change would
                                    edit. *);
  procst_utsname : option (list byte)
    (* THE UTS NAME the process is told about, as the 390 bytes
       [uname] (160) copies out -- [struct new_utsname], six 65-byte
       C-string fields (include/uapi/linux/utsname.h, Linux v6.18.46,
       commit 1f99e9ab748f) -- pinned the first time a [uname] READS
       it, exactly as [LimState.limst_core] pins RLIMIT_CORE and
       [procst_tid] pins the tid.  [None] means no [uname] has
       observed it yet.

       WHY IT IS PINNED RATHER THAN CHOSEN AFRESH.  Three of the six
       fields -- [nodename], [release] and [version] -- are settled by
       the kernel BUILD and by the boot-time hostname, not by anything
       in kernel/sys.c, so the model cannot know them; but they do not
       change under a process either.  Nothing in
       [Specs.modeled_sysnos] writes one: [sethostname] (161) and
       [setdomainname] (162) have no dispatcher arm.  A [choose]
       resolved afresh at each call would therefore admit a trace in
       which two [uname] calls disagree about which kernel is running,
       which no Linux machine produces -- the same argument
       [Sys.Kernel.Sched.Syscalls.sched_getaffinity_spec] makes for the
       CPU set it declines to answer for, and the note above [Record
       Model] is where the three mechanisms are compared.

       WHY IT IS PROCESS STATE.  Linux keeps it in the UTS NAMESPACE
       ([current->nsproxy->uts_ns->name], include/linux/utsname.h's
       [utsname]), not in [task_struct].  This model has exactly one
       process in exactly one namespace, so the distinction has nothing
       to bite on here; if a second namespace ever becomes reachable
       this field moves rather than gains a case.

       BYTES, NOT SIX DECODED STRINGS, for [limst_core]'s reason: the
       model only ever COPIES this field out, so storing it decoded
       would oblige the spec and the checker to agree on a round trip
       neither otherwise needs. *);
  procst_sigaltstack_installed : bool
                                 (* whether a [sigaltstack] has left
                                    [sas_ss_size] NON-ZERO -- an alternate
                                    stack is installed, not merely that the
                                    record has been assigned to.  [false] in
                                    [mkModel]: [execve] clears the stack
                                    ([begin_new_exec] sets
                                    [me->sas_ss_sp = me->sas_ss_size = 0],
                                    fs/exec.c, Linux v6.18.46, commit
                                    1f99e9ab748f), so a starting process has
                                    none installed.

                                    ONE BIT, AND WHY ONE IS ALL THAT IS USABLE.
                                    [Kernel.Signal.sigaltstack_spec] answers
                                    only while the recorded SIZE is 0, because
                                    both of the record's readers take the USER
                                    STACK POINTER as an argument
                                    -- [on_sig_stack] and [sas_ss_flags]
                                    (include/linux/sched/signal.h) -- and
                                    [SyscallInput] carries a0..a5 and no sp.
                                    While [sas_ss_size] is 0 both answer the
                                    same thing for EVERY sp (not on the stack;
                                    SS_DISABLE); a size at or above
                                    [Uapi.MINSIGSTKSZ] ends that, and it is
                                    [do_sigaltstack]'s install branch alone
                                    that stores one.  So a stored
                                    [ss_sp]/[ss_size] would buy no answer this
                                    bit does not, and the spec declines once it
                                    is set.

                                    NOT EVERY SUCCESSFUL WRITE SETS IT.
                                    [do_sigaltstack] (kernel/signal.c) runs
                                    [ss_size = 0; ss_sp = NULL] before the
                                    store on its SS_DISABLE branch, so a
                                    disable assigns all three fields and still
                                    leaves the answerable (NULL, 0, ss_flags)
                                    shape.  The bit stays [false] there on
                                    purpose: setting it would decline calls
                                    the model can still answer.  What the
                                    invariant says is that while it is [false]
                                    the record is (NULL, 0, F) for some flags
                                    word F this model does not track, and
                                    every arm of the spec answers the same for
                                    every F. *)
;
  procst_killed : bool           (* whether the halt above is a DEATH BY SIGNAL
                                    rather than an exit.  The process was
                                    terminated by the signal [procst_halted]
                                    carries, with the default disposition,
                                    which a waiting parent reads as WIFSIGNALED
                                    and a shell renders as 128+that number.

                                    A FLAG BESIDE [procst_halted] RATHER THAN A
                                    SECOND [option word], and the reason is the
                                    invariant it makes free: [m_killed] below
                                    reads this field THROUGH [procst_halted],
                                    so "a killed process is over" holds by
                                    construction rather than by everybody
                                    remembering to write both -- see
                                    [m_killed_of_m_halted_none], which is the
                                    fact every one-step inversion in
                                    theories/Common/ uses to rule the kill rule
                                    out of a configuration that is still
                                    running.  Two independent [option]s would
                                    make that a proof obligation on each
                                    writer, and a writer that forgot it would
                                    break no proof.

                                    ONLY [State.with_killed] sets it, its only
                                    callers are in
                                    [Sys.Kernel.Signal], and SIGABRT is the only
                                    signal any of them sends --
                                    [Kernel.Signal.tkill_spec] is the one arm
                                    that can send a signal at all. *)
;
  procst_sigabrt_pending : bool  (* SIGABRT has been sent to this process and
                                    is BLOCKED, so it sits in
                                    [task->pending.signal] waiting for the mask
                                    to let it through (kernel/signal.c,
                                    [send_signal_locked]; Linux v6.18.46,
                                    commit 1f99e9ab748f).

                                    A BOOL AND NOT A SIGSET, because at most
                                    one signal can ever be in it: the only arm
                                    that sends a signal is
                                    [Kernel.Signal.tkill_spec], and the only
                                    signal it sends is SIGABRT.  A [sigset_t]
                                    here would be a field whose other 63 bits
                                    no reachable state can set, and the name
                                    would stop saying that.  The day a second
                                    signal becomes sendable this widens rather
                                    than gains a case.

                                    WHY THE STATE EXISTS AT ALL, given that the
                                    model delivers no signals from outside: it
                                    is where musl's [abort] leaves SIGABRT.
                                    [raise] blocks the application signals
                                    first, SIGABRT among them, so the [tkill]
                                    lands on a BLOCKED signal and the process
                                    does not die there; it dies on the return
                                    path from the [rt_sigprocmask] that
                                    restores the old mask.  Without this field
                                    the abort path could only be declined *)
;
  procst_abort_terminal : bool   (* THE ONE FIELD OF THIS RECORD THAT IS NOT
                                    KERNEL STATE.  It is the task's
                                    declaration of whether the model covers the
                                    abort path at all, seeded by [init_model]
                                    from [ProcInput]'s [in_abort_terminal] and
                                    written by nothing.  [false] -- what
                                    [Run.valid_input] pins --
                                    makes [Kernel.Signal.tkill_spec] decline
                                    every call, as if 130 and 131 had no arm
                                    at all.

                                    WHY IT RIDES IN THE MODEL rather than
                                    beside [Run.SpuriousCfg]: that
                                    configuration FILTERS outcomes a spec
                                    already admits, so it can live outside the
                                    model and be applied at [Run.sstep_cfg].
                                    This one decides what a spec admits, so it
                                    has to reach the spec, and the only channel
                                    a spec has to the run's parameters is the
                                    model.  [Run.valid_input] and
                                    [Run.valid_input_abort] are what put it in
                                    the STATEMENT, where a reader can see which
                                    stance a proof was made under; a statement
                                    that pins neither asserts both *)
;
  procst_statpins : list (Fs.path * list byte)
    (* THE `struct stat` EACH STATTED FILE WAS FIRST SEEN WITH, keyed by
       path -- the 128 bytes [Fs.Stat.fstat_spec] delivered the first
       time that file was statted, kept so that a LATER stat of the same
       file cannot disagree with it about which file it is.  A path with
       no entry has not been statted yet.

       WHY A PIN AT ALL, and it is [procst_utsname]'s argument on a
       different value.  Of the twenty members of the delivered struct
       the model derives one, [st_size], and knows four more to be zero
       padding; the rest -- the device, the inode, the mode, the link
       count, the owning ids, the block size, the block count and the
       three timestamps -- are the environment's, because [Fs.Fs] is a
       map from path to CONTENTS and carries none of them.  Chosen
       AFRESH at each call they would admit a trace in which two
       [fstat]s of one unchanged file report different inodes, which no
       Linux machine produces.  Chosen ONCE and recorded, they cannot.

       ONLY THE STABLE MEMBERS ARE HELD AGAINST A LATER CALL, and which
       those are is [Uapi.stat_stable_eqb]'s subject rather than this
       field's: the whole 128 bytes are stored, and the comparison
       ignores [st_size], [st_blocks] and the timestamps, every one of
       which a write moves.  Storing the whole buffer and comparing part
       of it -- rather than storing a projection -- keeps the two halves
       of that decision in one place, next to the layout they are
       offsets into.

       NOT IN [Fs], DELIBERATELY.  [Fs.Fs] is [ExitEv]'s payload and is
       compared with [=] (Fs.v, CANONICAL FORM), so a nondeterministic
       value inside it would cost the examples statements they prove
       -- [Examples.cp_ns]'s [m_fs model = fs_set fs0v dstp
       (firstn k D)] is not provable if [fs_set] does not determine
       its result.  That is
       why the pin lives here: process state is observed by no
       event.

       KEYED BY PATH, WHICH IS THIS MODEL'S INODE.  Linux keys it by
       inode, and the difference shows only where two paths name one
       inode or one path names two -- neither of which [Fs]'s flat,
       link-free namespace can express (Fs.v). *)
}.

(** The resource limits the process has been observed to have. *)
Record LimState := mkLimState {
  limst_core : option (list byte)
    (* RLIMIT_CORE as the 16 bytes of the [struct rlimit64] the kernel would
       copy out, pinned the first time a prlimit64 READS it, exactly as
       [procst_tid] pins the tid.  The limits a process starts with are
       inherited from its parent, so the model does not know them a priori:
       the environment chooses the pair (the kernel maintains soft <= hard)
       and the model records it, after which every later read returns it and
       a modeled set replaces it.  [None] means no prlimit64 has observed it
       yet.

       BYTES, NOT A DECODED PAIR, so the model only ever DECODES a limit and
       never re-encodes one; storing [(soft, hard)] would oblige the spec and
       the checker to agree on a round trip neither otherwise needs.

       [prlimit64] ANSWERS ONLY RLIMIT_CORE, and that is a separate matter
       from which limits this record carries: [limst_nofile] below is a
       limit the model KNOWS and [prlimit64] still declines. *);
  limst_nofile : word
    (* RLIMIT_NOFILE's SOFT limit, [rlim_cur], as an [unsigned long] -- the
       width [rlimit()] returns (include/linux/sched/signal.h,
       [task_rlimit], Linux v6.18.46, commit 1f99e9ab748f).

       AN INPUT OF THE RUN, not an observation: unlike [limst_core], which
       is pinned the first time a prlimit64 reads it, this one is seeded by
       [init_model] from [ProcInput]'s [in_nofile] and never changes.  It
       has to be an input for the same reason the launching uid is one --
       the limits a process starts with are its parent's, so the model does
       not know them and quantifies over them instead.  It never changes
       because no syscall in [Specs.modeled_sysnos] writes one: [setrlimit]
       (164) has no dispatcher arm, and [prlimit64] (261) has one but
       answers only RLIMIT_CORE.  An arm that answered a NOFILE set would
       have to make this field mutable, and [Sys.Fs.File.dup3_spec] is
       where the cost of that would land.

       ONLY THE SOFT LIMIT.  [rlim_max] is not carried because nothing
       reads it: [ksys_dup3] tests [rlimit(RLIMIT_NOFILE)], which is
       [rlim_cur], and the one syscall that would report the pair
       ([prlimit64]) declines this resource.  That decline is therefore
       load-bearing in both directions -- it is why the hard limit may be
       absent, and answering it would need the field. *)
}.

(** The clocks the process can read. *)
Record TimeState := mkTimeState {
  timest_clock : word
    (* CLOCK_MONOTONIC, in NANOSECONDS.  Held in state, rather than chosen
       afresh per call, because MONOTONICITY IS THE GUARANTEE: the field
       exists so that a later reading can be required not to precede an
       earlier one, which a per-call choice has nothing to compare against.
       It counts from an unspecified origin, so its absolute value means
       nothing and only differences do; the model starts it at 0, one of the
       origins Linux is free to pick.  See
       [Kernel.Time.PosixTimers.clock_gettime_spec]. *)
}.

(** THREE WAYS THIS MODEL CARRIES A FACT IT CANNOT KNOW A PRIORI, and
    nothing above says how to choose between them, which is what this
    note is for.  Each field below already argues its own case; what was
    missing is the comparison, and a new environment fact is the one
    place the wrong choice is cheap to make and expensive to find.

    - QUANTIFIED INPUT.  A [ProcInput] field, seeded by [init_model] —
      the record is the list, so none is written here.  The obligation
      quantifies over the input, so the theorem holds for every value
      the launching environment could have chosen that satisfies
      [Run.valid_input]; the bound is part of the claim and
      [limst_nofile]'s comment names its own.  Right when the LAUNCHING
      ENVIRONMENT settles the value, whether or not the program can
      later change it — several of these are mutable afterwards.
    - PINNED AT FIRST OBSERVATION.  [limst_core], [procst_tid] and
      [procst_utsname], each
      of which names its own trigger.  The environment chooses, the
      model records what it revealed, and every later query must answer
      the same.  Right when the value is NOT settled in the input —
      because nothing constructing a run would know to supply it — but
      must be self-consistent once seen.
    - CARRIED AND ADVANCED.  [timest_clock], whose own comment gives the
      reason.  Right when the constraint is BETWEEN observations rather
      than on any one of them.

    The first two are already contrasted in place, most sharply by
    [limst_nofile], which calls itself an input "unlike [limst_core],
    which is pinned the first time a prlimit64 reads it" — two fields of
    ONE record taking opposite answers.  What no field can say, and the
    reason this note exists, is which answer a NEW one should take.

    THE PENDING CASE, named because it is what made this note worth
    writing: [Sys.Kernel.Sched.Syscalls.sched_getaffinity_spec] declines
    for want of a CPU set, and wants the SECOND mechanism — its own
    spec argues why, and is not repeated here.  Naming that is not the
    same as building it, and it is not built. *)
Record Model := mkModelOf {
  m_fd   : FdState;
  m_vm   : VmState;
  m_io   : IoState;
  m_fsys : FsState;
  m_proc : ProcState;
  m_lim  : LimState;
  m_time : TimeState;
}.

(** The accessors the rest of the development uses; they hide the
    nesting. *)
Definition m_fds (m : Model) : list (word * FdEntry) := fdst_table (m_fd m).
Definition m_pipes (m : Model) : list (word * PipeBuf) := fdst_pipes (m_fd m).
Definition m_vmmaps (m : Model) : VmMaps := vmst_maps (m_vm m).
Definition m_vm_lazy (m : Model) : list (word * word) := vmst_lazy (m_vm m).
Definition m_vm_materialized (m : Model) : list word :=
  vmst_materialized (m_vm m).
Definition m_stdin (m : Model) : InputStream := iost_stdin (m_io m).
Definition m_urandom (m : Model) : InputStream := iost_urandom (m_io m).
Definition m_net (m : Model) : NetQueue := iost_net (m_io m).
Definition m_conn_ix (m : Model) : word := iost_conn_ix (m_io m).
Definition m_fs (m : Model) : Fs.Fs := fsst_image (m_fsys m).
Definition m_halted (m : Model) : option word := procst_halted (m_proc m).
Definition m_tid (m : Model) : option word := procst_tid (m_proc m).
Definition m_setsid_succeeded (m : Model) : bool :=
  procst_setsid_succeeded (m_proc m).
Definition m_has_children (m : Model) : bool := procst_children (m_proc m).
Definition m_sigaltstack_installed (m : Model) : bool :=
  procst_sigaltstack_installed (m_proc m).
Definition m_sigmask (m : Model) : word := procst_sigmask (m_proc m).
(** The signal that killed the process, or [None] if it exited or is
    still running.  READ THROUGH [procst_halted] on purpose: the payload
    is the halt's, and the flag only says how to read it.  That is what
    makes [m_killed_of_m_halted_none] hold with no side condition. *)
Definition m_killed (m : Model) : option word :=
  if procst_killed (m_proc m) then procst_halted (m_proc m) else None.
Definition m_sigabrt_pending (m : Model) : bool :=
  procst_sigabrt_pending (m_proc m).
Definition m_abort_terminal (m : Model) : bool :=
  procst_abort_terminal (m_proc m).
Definition m_utsname (m : Model) : option (list byte) :=
  procst_utsname (m_proc m).
Definition m_statpins (m : Model) : list (Fs.path * list byte) :=
  procst_statpins (m_proc m).
Definition m_rlimit_core (m : Model) : option (list byte) := limst_core (m_lim m).
Definition m_nofile (m : Model) : word := limst_nofile (m_lim m).
Definition m_clock (m : Model) : word := timest_clock (m_time m).
Definition m_creds (m : Model) : Creds := procst_creds (m_proc m).

(** The id the kernel itself answers with when it has no id to answer:
    [DEFAULT_OVERFLOWUID] / [DEFAULT_OVERFLOWGID], both 65534
    (include/linux/highuid.h), which [from_kuid_munged] substitutes for
    an id that does not map into the caller's namespace
    (kernel/user_namespace.c).  It is what [mkModel] gives a model built
    WITHOUT a [ProcInput], below.

    Not zero, and that is the point.  Zero would make every such model a
    ROOT process, and [creds_privileged] reads the effective uid: a
    worked example that meant to say nothing about privilege would have
    been saying the most permissive thing there is.  A model that needs
    root says so, with [with_creds]. *)
Definition overflow_id : word := Z_to_bv 64 65534.

(** The soft RLIMIT_NOFILE a model built WITHOUT a [ProcInput] gets:
    [INR_OPEN_CUR], the value [INIT_RLIMITS] gives the init task
    (include/asm-generic/resource.h; include/uapi/linux/fs.h,
    [#define INR_OPEN_CUR 1024], Linux v6.18.46, commit 1f99e9ab748f).
    It is what a process is launched with on a system where nobody
    changed the limit, so a fixture that means to say nothing about the
    descriptor limit says the ordinary thing.

    Not a permissiveness choice the way [overflow_id] is: 0 would make
    every [dup3] in such a fixture -EBADF and RLIM_INFINITY is not a
    value [do_prlimit] lets NOFILE hold at all (kernel/sys.c refuses a
    hard limit above [sysctl_nr_open]).  A run built from a [ProcInput]
    never sees this: [init_model] installs [in_nofile] over it. *)
Definition default_nofile : word := Z_to_bv 64 1024.

(** [mkModel] keeps the flat constructor's argument order, so every site that
    builds a model is unchanged.  The random device's stream starts
    EMPTY here ([IEof]) for the reason the accept queue starts silent:
    it is an input of the run, and the one place that installs one is
    [init_model], through [with_urandom]. *)
Definition mkModel (fds : list (word * FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : option word)
    (tid : option word) (rlim : option (list byte)) : Model :=
  mkModelOf (mkFdState fds []) (mkVmState vm [] [])
            (mkIoState stdin IEof net_silent (Z_to_bv 64 0)) (mkFsState fs)
            (mkProcState halted tid
               (mkCreds overflow_id overflow_id overflow_id
                        overflow_id overflow_id overflow_id [])
               false (Z_to_bv 64 0) false None false false false false [])
            (mkLimState rlim default_nofile)
            (mkTimeState (Z_to_bv 64 0)).

(** Field-update helpers.  Each one rebuilds only its own subsystem and
    carries the other five across, so a new field inside a subsystem touches
    that subsystem's setters and no others. *)
Definition with_fds (fds : list (word * FdEntry)) (m : Model) : Model :=
  mkModelOf (mkFdState fds (m_pipes m)) (m_vm m) (m_io m) (m_fsys m) (m_proc m)
    (m_lim m) (m_time m).
Definition with_pipes (ps : list (word * PipeBuf)) (m : Model) : Model :=
  mkModelOf (mkFdState (m_fds m) ps) (m_vm m) (m_io m) (m_fsys m) (m_proc m)
    (m_lim m) (m_time m).
Definition with_vmmaps (h : VmMaps) (m : Model) : Model :=
  mkModelOf (m_fd m)
    (mkVmState h (m_vm_lazy m) (m_vm_materialized m))
    (m_io m) (m_fsys m) (m_proc m) (m_lim m) (m_time m).
Definition with_vm_backing (lazy : list (word * word))
    (materialized : list word) (m : Model) : Model :=
  mkModelOf (m_fd m) (mkVmState (m_vmmaps m) lazy materialized)
    (m_io m) (m_fsys m) (m_proc m) (m_lim m) (m_time m).
Definition with_stdin (s : InputStream) (m : Model) : Model :=
  mkModelOf (m_fd m) (m_vm m) (mkIoState s (m_urandom m) (m_net m) (m_conn_ix m))
            (m_fsys m) (m_proc m) (m_lim m) (m_time m).
(** The random device's remaining stream.  [init_model] installs the
    declared one; every later call is a read on [FdUrandom] advancing
    past the bytes it delivered ([Fs.ReadWrite.read_urandom]). *)
Definition with_urandom (s : InputStream) (m : Model) : Model :=
  mkModelOf (m_fd m) (m_vm m) (mkIoState (m_stdin m) s (m_net m) (m_conn_ix m))
            (m_fsys m) (m_proc m) (m_lim m) (m_time m).
(** Seed the accept queue.  Its only caller is [init_model], which is
    the point: the queue is an INPUT of the run, so the one place that
    may install one is the one that turns a [ProcInput] into a model.
    Every later change to it goes through [with_accepted], which cannot
    install a queue, only advance past its head. *)
Definition with_net (q : NetQueue) (m : Model) : Model :=
  mkModelOf (m_fd m) (m_vm m) (mkIoState (m_stdin m) (m_urandom m) q (m_conn_ix m))
            (m_fsys m) (m_proc m) (m_lim m) (m_time m).

(** Install a new file-system image, DROPPING THE STAT PIN of every path
    the new image does not hold.

    THE FILTER IS NOT BOOKKEEPING; IT IS THE PIN'S CORRECTNESS
    CONDITION.  [procst_statpins] holds a path's inode identity for the
    life of the file, and [unlinkat] (35) -- the one modeled syscall
    that takes a key OUT of the map -- destroys it.  A pin that survived
    the removal would be held against the NEXT file created at that
    name, which Linux gives a different inode, so
    [Fs.Stat.fstat_file_spec] would reject the conforming trace
    `create f; fstat; unlink f; create f; fstat`.  Every other writer of
    this field passes a map that still holds the path it is about --
    [Open.create_wronly]'s O_TRUNC keeps the key, and so do
    [ReadWrite.write_spec] and [Open.ftruncate_spec] -- so the filter is
    inert for all of them, which is what makes routing the invalidation
    through this one setter equivalent to putting it in [unlinkat] and
    cheaper than remembering to.

    A CREATE OVER AN EXISTING FILE KEEPS THE PIN, and should: O_TRUNC
    resizes an inode rather than replacing it, and [st_size] is not a
    member the pin holds fixed anyway. *)
Definition statpins_restrict (fs : Fs.Fs) (ps : list (Fs.path * list byte))
    : list (Fs.path * list byte) :=
  List.filter (fun e => match Fs.fs_lookup fs (fst e) with
                   | Some _ => true
                   | None => false
                   end) ps.

Definition with_fs (fs : Fs.Fs) (m : Model) : Model :=
  mkModelOf (m_fd m) (m_vm m) (m_io m) (mkFsState fs)
            (mkProcState (m_halted m) (m_tid m) (m_creds m)
                         (m_setsid_succeeded m) (m_sigmask m)
                         (m_has_children m) (m_utsname m)
                         (m_sigaltstack_installed m)
                         (procst_killed (m_proc m)) (m_sigabrt_pending m)
                         (m_abort_terminal m)
                         (statpins_restrict fs (m_statpins m)))
            (m_lim m) (m_time m).
(** Halt the process by an EXIT, which is the other half of what the
    kill flag distinguishes: this clears it, so a model this produced has
    [m_killed] [None] whatever it had before.  Nothing can reach it with
    the flag already set -- every rule that consumes a syscall outcome
    requires the process to be running -- and clearing rather than
    carrying is what makes [m_killed_with_halted] the [None] the two
    terminal rules need to stay disjoint. *)
Definition with_halted (code : word) (m : Model) : Model :=
  mkModelOf (m_fd m) (m_vm m) (m_io m) (m_fsys m)
            (mkProcState (Some code) (m_tid m) (m_creds m)
                         (m_setsid_succeeded m) (m_sigmask m)
                         (procst_children (m_proc m)) (m_utsname m)
                         (m_sigaltstack_installed m)
                         false (m_sigabrt_pending m)
                         (m_abort_terminal m) (m_statpins m))
            (m_lim m) (m_time m).
Definition with_tid (tid : word) (m : Model) : Model :=
  mkModelOf (m_fd m) (m_vm m) (m_io m) (m_fsys m)
            (mkProcState (m_halted m) (Some tid) (m_creds m)
                         (m_setsid_succeeded m) (m_sigmask m)
                         (procst_children (m_proc m)) (m_utsname m)
                         (m_sigaltstack_installed m)
                         (procst_killed (m_proc m)) (m_sigabrt_pending m)
                         (m_abort_terminal m) (m_statpins m))
            (m_lim m) (m_time m).
Definition with_rlimit_core (bs : list byte) (m : Model) : Model :=
  mkModelOf (m_fd m) (m_vm m) (m_io m) (m_fsys m) (m_proc m)
            (mkLimState (Some bs) (m_nofile m)) (m_time m).
(** Record the UTS name the environment revealed.
    [Kernel.Sys.uname_spec] is the only caller and it calls this only
    on the branch where [m_utsname] was [None], so the pin is written
    once and never overwritten: [uname] (160) is a pure read, and the two
    syscalls that WRITE a utsname field -- [sethostname] (161) and
    [setdomainname] (162) -- have no arm in
    [Sys.SyscallTable.spec_table].  That is what makes the repeat check
    in [Checks.Sys.Kernel.Sys]'s [check_uname_copy] an equality rather than a
    relation, and adding either syscall means giving this a second writer
    in the same commit. *)
Definition with_utsname (bs : list byte) (m : Model) : Model :=
  mkModelOf (m_fd m) (m_vm m) (m_io m) (m_fsys m)
            (mkProcState (m_halted m) (m_tid m) (m_creds m)
                         (m_setsid_succeeded m) (m_sigmask m)
                         (m_has_children m) (Some bs)
                         (m_sigaltstack_installed m)
                         (procst_killed (m_proc m)) (m_sigabrt_pending m)
                         (m_abort_terminal m) (m_statpins m))
            (m_lim m) (m_time m).
(** Look a file's stat pin up by path.  [None] means no [fstat] has
    delivered a [struct stat] for that file yet, which is the branch
    that CREATES one.  Linear over an association list, like
    [Fs.fs_lookup] and [fd_lookup] beside it. *)
Fixpoint statpin_lookup (ps : list (Fs.path * list byte)) (p : Fs.path)
    : option (list byte) :=
  match ps with
  | [] => None
  | (q, bs) :: rest => if Fs.path_eqb q p then Some bs else statpin_lookup rest p
  end.

(** Record the [struct stat] a file was first seen with.
    [Fs.Stat.fstat_spec] is the only caller and it calls this only on
    the branch where [statpin_lookup] was [None], so a path's pin is
    written once and never overwritten -- which is what lets
    [Checks.Sys.Fs.Stat]'s repeat check be a comparison against the
    stored bytes rather than a relation between two calls.  The entry is
    CONSED rather than merged into a sorted list on purpose: unlike
    [Fs.fs_set], nothing observes this field's representation, so it
    owes no canonical form.

    A second writer would have to argue why the pin may move.  There is
    no such argument for the members [Uapi.stat_stable_eqb] compares --
    no [chmod], [chown] or [link] arm exists in
    [Sys.SyscallTable.spec_table] -- so adding one means revisiting that
    predicate in the same commit, not adding a call here. *)
Definition with_statpin (p : Fs.path) (bs : list byte) (m : Model) : Model :=
  mkModelOf (m_fd m) (m_vm m) (m_io m) (m_fsys m)
            (mkProcState (m_halted m) (m_tid m) (m_creds m)
                         (m_setsid_succeeded m) (m_sigmask m)
                         (m_has_children m) (m_utsname m)
                         (m_sigaltstack_installed m)
                         (procst_killed (m_proc m)) (m_sigabrt_pending m)
                         (m_abort_terminal m)
                         ((p, bs) :: m_statpins m))
            (m_lim m) (m_time m).

(** Seed the soft descriptor limit.  Its only caller is [init_model], for
    the reason [with_net] gives: the limit is an INPUT of the run, so the
    one place that may install one is the one that turns a [ProcInput]
    into a model.  Unlike [with_net], which [with_accepted] later
    advances past, there is no second writer of any kind — see
    [limst_nofile] for why there can be none — which is also the
    difference between this and [with_rlimit_core]. *)
(** Seed the task's abort-path declaration.  Its only caller is
    [init_model], for the reason [with_net] and [with_nofile] give: the
    declaration is a parameter of the RUN, so the one place that may
    install it is the one that turns a [ProcInput] into a model.  Unlike
    those two it has no reader anywhere in the model's own state
    transitions either -- [Kernel.Signal.tkill_spec] reads it and nothing
    writes it after this -- so the field is constant along every run, and
    that is what lets [Run.valid_input] pin a whole statement's stance by
    pinning one field of the input. *)
Definition with_abort_terminal (b : bool) (m : Model) : Model :=
  mkModelOf (m_fd m) (m_vm m) (m_io m) (m_fsys m)
            (mkProcState (m_halted m) (m_tid m) (m_creds m)
                         (m_setsid_succeeded m) (m_sigmask m)
                         (m_has_children m) (m_utsname m)
                         (m_sigaltstack_installed m)
                         (procst_killed (m_proc m)) (m_sigabrt_pending m) b
                         (m_statpins m))
            (m_lim m) (m_time m).

Definition with_nofile (n : word) (m : Model) : Model :=
  mkModelOf (m_fd m) (m_vm m) (m_io m) (m_fsys m) (m_proc m)
            (mkLimState (m_rlimit_core m) n) (m_time m).
Definition with_creds (c : Creds) (m : Model) : Model :=
  mkModelOf (m_fd m) (m_vm m) (m_io m) (m_fsys m)
            (mkProcState (m_halted m) (m_tid m) c
                         (m_setsid_succeeded m) (m_sigmask m)
                         (procst_children (m_proc m)) (m_utsname m)
                         (m_sigaltstack_installed m)
                         (procst_killed (m_proc m)) (m_sigabrt_pending m)
                         (m_abort_terminal m) (m_statpins m))
            (m_lim m) (m_time m).
Definition with_setsid_succeeded (m : Model) : Model :=
  mkModelOf (m_fd m) (m_vm m) (m_io m) (m_fsys m)
            (mkProcState (m_halted m) (m_tid m) (m_creds m)
                         true (m_sigmask m) (procst_children (m_proc m))
                         (m_utsname m) (m_sigaltstack_installed m)
                         (procst_killed (m_proc m)) (m_sigabrt_pending m)
                         (m_abort_terminal m) (m_statpins m))
            (m_lim m) (m_time m).

(** Record that the process now has something to reap.
    [Kernel.Fork.clone_resolve] calls this on its success branch, and only
    there — the errno alternative creates nothing and the shared-file
    decline never reaches a resolution.

    MONOTONE ONCE SET, and that is load-bearing rather than incidental:
    [Kernel.Exit.wait4_spec]'s -ECHILD gate reads this field at a LATER
    call than the one that sets it, so the two lemmas only compose while
    nothing clears it in between.  Every setter above either passes
    [m_proc m] through wholesale or carries [procst_children (m_proc m)]
    explicitly, and [mkProcState] is constructed nowhere outside this
    file.  A new setter that rebuilds [ProcState] without carrying this
    field breaks the composition WITHOUT breaking either side's proofs:
    the gate would still be proved, the creating arm's setter would still
    be proved, and the model would answer -ECHILD for a caller that has a
    child.  Two true lemmas and still a hole.  If you add a [ProcState]
    construction site, carry this field. *)
Definition with_children (m : Model) : Model :=
  mkModelOf (m_fd m) (m_vm m) (m_io m) (m_fsys m)
            (mkProcState (m_halted m) (m_tid m) (m_creds m)
                         (m_setsid_succeeded m) (m_sigmask m) true
                         (m_utsname m) (m_sigaltstack_installed m)
                         (procst_killed (m_proc m)) (m_sigabrt_pending m)
                         (m_abort_terminal m) (m_statpins m))
            (m_lim m) (m_time m).
(** Install a new blocked mask.  [Kernel.Signal.rt_sigprocmask_spec] is
    the only caller, and the only kernel path that reaches
    [__set_task_blocked] from a syscall this model answers: every other
    one -- [rt_sigsuspend] (133), [rt_sigtimedwait] (137),
    [epoll_pwait] (22), [io_pgetevents] (292), [io_uring_enter] (426),
    [ptrace] (117) and sigreturn (139) -- is outside
    [Specs.modeled_sysnos], and [pselect6] (72) and [ppoll] (73) reach
    their own mask arguments only through [Fs.Select]'s [PsSigReal] and
    [PpSigReal], both of which are [unmodeled].  THOSE TWO ARE THE
    FRAGILE HALF: each is an absence, so relaxing either means moving
    the mask here in the same commit, the way [set_user_sigmask] and
    [restore_saved_sigmask_unless] move it in fs/select.c. *)
Definition with_sigmask (s : word) (m : Model) : Model :=
  mkModelOf (m_fd m) (m_vm m) (m_io m) (m_fsys m)
            (mkProcState (m_halted m) (m_tid m) (m_creds m)
                         (m_setsid_succeeded m) s (m_has_children m)
                         (m_utsname m) (m_sigaltstack_installed m)
                         (procst_killed (m_proc m)) (m_sigabrt_pending m)
                         (m_abort_terminal m) (m_statpins m))
            (m_lim m) (m_time m).

(** Record that a [sigaltstack] has installed an alternate stack.
    [Kernel.Signal.sigaltstack_spec] is the only caller, and it calls this
    on exactly the branch where [do_sigaltstack] (kernel/signal.c) stores a
    NON-ZERO [t->sas_ss_size] -- never on an errno branch, which leaves the
    record alone; never on the no-change fast path, which returns before
    the lock is taken; and never on the SS_DISABLE branch, which reaches
    the same three assignments but zeroes [ss_size] and [ss_sp] first and
    so leaves the record in the zero-size shape the spec can still answer
    from.

    MONOTONE ONCE SET, like [with_children], and for a stronger reason:
    nothing in this model can shrink the recorded size back to zero -- the
    one call that could, a later SS_DISABLE, is declined by the very bit
    this sets -- so a setter that cleared it would be claiming the process
    is back in a state it cannot reach.  Every [ProcState] setter above
    carries the field across; a new one that does not would let the spec
    answer a [sigaltstack] from a zero-size record after an install moved
    it. *)
Definition with_sigaltstack_installed (m : Model) : Model :=
  mkModelOf (m_fd m) (m_vm m) (m_io m) (m_fsys m)
            (mkProcState (m_halted m) (m_tid m) (m_creds m)
                         (m_setsid_succeeded m) (m_sigmask m)
                         (m_has_children m) (m_utsname m) true
                         (procst_killed (m_proc m)) (m_sigabrt_pending m)
                         (m_abort_terminal m) (m_statpins m))
            (m_lim m) (m_time m).

(** Record that SIGABRT has been sent and is BLOCKED, so it waits in
    [task->pending.signal] instead of ending the process
    (kernel/signal.c, [send_signal_locked] adds to the pending set and
    [recalc_sigpending] leaves a blocked signal there; Linux v6.18.46,
    commit 1f99e9ab748f).  [Kernel.Signal.tkill_spec] is the only caller.

    NOTHING CLEARS IT, and that is not an omission.  The kernel dequeues
    a pending signal when it delivers it ([dequeue_signal] from
    [get_signal]), but the only delivery this model has is the FATAL one:
    SIGABRT's disposition in a modeled run is SIG_DFL by construction --
    [Kernel.Signal.rt_sigaction_spec] declines every install for a signal
    outside SIGINT and SIGTERM -- so the step that would clear the field
    is the step that ends the process, and no later state can read it.
    A second sendable signal, or a catchable SIGABRT, brings the clear
    with it. *)
Definition with_sigabrt_pending (m : Model) : Model :=
  mkModelOf (m_fd m) (m_vm m) (m_io m) (m_fsys m)
            (mkProcState (m_halted m) (m_tid m) (m_creds m)
                         (m_setsid_succeeded m) (m_sigmask m)
                         (m_has_children m) (m_utsname m)
                         (m_sigaltstack_installed m)
                         (procst_killed (m_proc m)) true (m_abort_terminal m)
                         (m_statpins m))
            (m_lim m) (m_time m).

(** End the process by a fatal signal.  It writes the signal number into
    [procst_halted], because a killed process is over and every rule that
    asks whether the process is still running asks that field
    ([Run.sstep_instr] and its
    siblings).  Which of the two terminal rules fires is then decided by
    [procst_killed] alone -- [Run.sstep_exit] declines a death by signal
    and [Run.sstep_killed] takes it -- so the two cannot both apply.

    IT HAS TWO CALLERS, and which is which decides what guards them.
    [Kernel.Signal.send_sigabrt] is the SEND, and it sits behind the
    task's declaration.  [Kernel.Signal.sigmask_deliver_model] is the
    DELIVERY inside [rt_sigprocmask], and it does NOT: it branches on
    [procst_sigabrt_pending], because a signal already pending has to be
    taken by the mask install that uncovers it whatever the task
    declared.  A reader checking the declaration-off claim needs both
    rows — see [Run.decl_off_frame], whose hypothesis carries the pending
    bit for exactly this reason, and
    [Checks.Cases.Kernel.Signal.decl_off_frame_one_sided_refuted], which
    refutes the version that names only the declaration.  SIGABRT is the
    only argument either caller is ever given. *)
Definition with_killed (sig : word) (m : Model) : Model :=
  mkModelOf (m_fd m) (m_vm m) (m_io m) (m_fsys m)
            (mkProcState (Some sig) (m_tid m) (m_creds m)
                         (m_setsid_succeeded m) (m_sigmask m)
                         (m_has_children m) (m_utsname m)
                         (m_sigaltstack_installed m)
                         true (m_sigabrt_pending m)
                         (m_abort_terminal m) (m_statpins m))
            (m_lim m) (m_time m).

(** The invariant the two fields are written under, stated where the
    setter is: a killed process is a halted process, and the two payloads
    agree.  [Run.sstep_killed] does not need it -- it reads
    [m_killed] -- but every rule that stops a running process does, and
    this is what says those rules stop a killed one. *)
Lemma killed_is_halted : forall sig m,
  m_halted (with_killed sig m) = Some sig
  /\ m_killed (with_killed sig m) = Some sig.
Proof. intros sig m. split; reflexivity. Qed.

(** A PROCESS THAT IS STILL RUNNING HAS NOT BEEN KILLED, with no side
    condition and no premise about who wrote what.  This is what the flag
    representation buys, and every one-step inversion in
    theories/Common/ consumes it: a configuration whose [m_halted] is
    [None] cannot be the target of [Run.sstep_killed], so an inversion
    that already ruled out [Run.sstep_exit] rules out both terminal
    rules together. *)
Lemma m_killed_of_m_halted_none : forall m,
  m_halted m = None -> m_killed m = None.
Proof.
  intros m H. unfold m_killed, m_halted in *.
  destruct (procst_killed (m_proc m)); [exact H | reflexivity].
Qed.

Definition with_clock (t : word) (m : Model) : Model :=
  mkModelOf (m_fd m) (m_vm m) (m_io m) (m_fsys m) (m_proc m) (m_lim m)
            (mkTimeState t).

(** Hand over the head of the accept queue: the fd table gains the
    accepted socket, the queue advances past the connection just taken,
    and the handed-over count goes up by one.  ONE helper rather than
    three, because the three moves are one event — [accept] is the only
    thing that changes any of them, and it always changes all three. *)
Definition with_accepted (fds : list (word * FdEntry)) (m : Model) : Model :=
  mkModelOf (mkFdState fds (m_pipes m)) (m_vm m)
    (mkIoState (m_stdin m) (m_urandom m) (nq_rest (m_net m))
               (m_conn_ix m + Z_to_bv 64 1))
    (m_fsys m) (m_proc m) (m_lim m) (m_time m).

(* =========================================================================
   Observable trace events
   ========================================================================= *)

(** The observables are BYTE-LEVEL channel I/O plus exit.  Bytes are
    [bv 8]; channel ids and the exit code are [word]. *)
Inductive event :=
  | ReadEv  (ch : word) (b : byte)
  | WriteEv (ch : word) (b : byte)
  | ExitEv  (code : word) (fs : Fs.Fs)
  | KillEv  (sig : word) (fs : Fs.Fs).
(** [KillEv] is the OTHER way a process ends: killed by [sig] with the
    default disposition, which is what a waiting parent reads as
    WIFSIGNALED and a shell renders as 128+[sig].  It carries the final
    file system for [ExitEv]'s reason and it is a SEPARATE constructor for
    a reason of its own: [exit(134)] and a death by SIGABRT are different
    events to everything that observes this process, and folding the
    second into the first would make a model in which a program can fake
    its own abort.  The only rule that emits one is [Run.sstep_killed],
    and the only signal that reaches it is SIGABRT -- see
    [procst_killed]. *)

(* =========================================================================
   fd table helpers
   ========================================================================= *)

Fixpoint fd_lookup (fds : list (word * FdEntry)) (fd : word)
    : option FdEntry :=
  match fds with
  | [] => None
  | (k, e) :: r => if bv_eqb k fd then Some e else fd_lookup r fd
  end.

Definition fd_insert (fds : list (word * FdEntry)) (fd : word) (e : FdEntry)
    : list (word * FdEntry) :=
  (fd, e) :: List.filter (fun p => negb (bv_eqb (fst p) fd)) fds.

Definition fd_remove (fds : list (word * FdEntry)) (fd : word)
    : list (word * FdEntry) :=
  List.filter (fun p => negb (bv_eqb (fst p) fd)) fds.

(** Lowest unused fd — the descriptor the kernel hands out at open, as
    Linux does (see [File.lowest_fd]/[Open.openat_spec]).  The scan is
    fuel-bounded at 4096 candidates, so the result is always <= 4096
    (never confusable with an error-encoded return); if all of 0..4095
    are taken the returned candidate may be occupied, and the openat
    spec's freeness side-condition then leaves only the errno branch. *)
Fixpoint alloc_fd_aux (fds : list (word * FdEntry)) (cand : word) (fuel : nat)
    : word :=
  match fuel with
  | O => cand
  | S f => match fd_lookup fds cand with
           | None => cand
           | Some _ => alloc_fd_aux fds (cand + 1) f
           end
  end.
Definition alloc_fd (fds : list (word * FdEntry)) : word :=
  alloc_fd_aux fds (Z_to_bv 64 0) 4096.

(** The SECOND descriptor a call that reserves two takes: the lowest
    free one strictly above [alloc_fd fds].  A syscall reserving a pair
    calls [get_unused_fd_flags] twice, and the first reservation is in
    the bitmap by the time the second runs, so the second skips it —
    [Net.Socket.socketpair_spec]'s [fd1] and [fd2] exactly.  Carries the
    same FUEL as [alloc_fd] over a range that starts one higher, so it
    returns at most 8193 — still far below the error-encoding window,
    and callers test both results for freeness for the same reason
    [Fs.File.lowest_fd] does. *)
Definition alloc_fd2 (fds : list (word * FdEntry)) : word :=
  alloc_fd_aux fds (alloc_fd fds + 1) 4096.

(* =========================================================================
   Pipe helpers — the [fdst_pipes] side table and the fd ends that name it
   ========================================================================= *)

(** The state of pipe [id], or [None] for an id no [pipe2] handed out.
    Same shape as [fd_lookup]: first match wins, and [pipe_insert] keeps
    at most one entry per id. *)
Fixpoint pipe_lookup (ps : list (word * PipeBuf)) (id : word)
    : option PipeBuf :=
  match ps with
  | [] => None
  | (k, st) :: r => if bv_eqb k id then Some st else pipe_lookup r id
  end.

(** Bind [id] to [st], replacing any existing binding. *)
Definition pipe_insert (ps : list (word * PipeBuf)) (id : word)
    (st : PipeBuf) : list (word * PipeBuf) :=
  (id, st) :: List.filter (fun p => negb (bv_eqb (fst p) id)) ps.

(** MAY A WRITE OF [n] BYTES LAND IN THE SLOT THE PIPE ALREADY USES?
    Every claim below is fs/pipe.c [anon_pipe_read] (:269) /
    [anon_pipe_write] (:431) at v6.18.46, the pair [pipeanon_fops]
    (:1257-1266) installs on an anonymous pipe.

    - an EMPTY queue means the ring is empty too: [anon_pipe_read]
      releases a buffer as soon as its last byte is taken
      ([if (!buf->len)] then [pipe_update_tail], :359-362, which is
      [pipe_buf_release] at :242 followed by [pipe->tail = ++tail]), so no
      live slot survives a full drain.  The write starts a fresh page, and
      any [n] up to [PIPE_BUF] fits in it — including [n = PIPE_BUF]
      exactly, which skips the merge path ([chars = n & (PAGE_SIZE-1)] at
      :477 is 0, and :478 tests [chars]) and takes the whole page;
    - a NONEMPTY queue is one slot with [used] bytes of its page already
      spoken for, and the top-up succeeds exactly when [used + n] still
      fits (:480-483).  The other two merge conditions hold by
      construction: [!was_empty] because the queue is nonempty, and
      [PIPE_BUF_FLAG_CAN_MERGE] because every buffer a modeled pipe holds
      was put there by [anon_pipe_write], which sets that flag on every
      page it allocates (:536-539 — the other branch is packet mode, which
      needs O_DIRECT and so a [pipe2] flag [Pipe.pipe2_spec] declines;
      only splice/vmsplice pages clear it, and neither is modeled).
      [pipe_buf_confirm] is a no-op for [anon_pipe_buf_ops] (:223-227),
      which has no [.confirm].

    Anything else — a transfer over [PIPE_BUF], or a top-up that would
    overflow the page — needs a SECOND slot, which is where slot
    accounting and therefore blocking start to matter.  Declined. *)
Definition pipe_write_room (st : PipeBuf) (n : Z) : bool :=
  match st with
  | ([], _) => (n <=? PIPE_BUF)%Z
  | (_ :: _, used) => (used + n <=? PIPE_BUF)%Z
  end.

(** The queue after appending [bs].  An empty queue restarts the mark at
    the new page's fill; a nonempty one carries it up. *)
Definition pipe_append (st : PipeBuf) (bs : list byte) : PipeBuf :=
  match st with
  | ([], _) => (bs, Z.of_nat (length bs))
  | (q, used) => (q ++ bs, (used + Z.of_nat (length bs))%Z)
  end.

(** The bytes a read of [n] takes off the front of a pipe's queue.

    [firstn (word_to_nat count) q] is the natural spelling, but
    [word_to_nat] builds a UNARY NUMERAL of the count
    before it ever looks at [q], so [read(pipefd, buf, 1 << 20)] would cost
    the extracted checker a million constructors to deliver at most
    PIPE_BUF bytes.  Taking the minimum against the
    queue's own length in [Z] first removes that cost: the numeral is
    bounded by the QUEUE, so the count may be anything.

    [pipe_take_firstn] is the equation proofs go through; the two agree
    for every nonnegative [n]. *)
Definition pipe_take (q : list byte) (n : Z) : list byte :=
  firstn (Z.to_nat (Z.min n (Z.of_nat (length q)))) q.

Lemma firstn_min_length : forall (A : Type) (l : list A) (n : nat),
  firstn (Nat.min n (length l)) l = firstn n l.
Proof.
  intros A l n. destruct (Nat.le_gt_cases n (length l)) as [Hle|Hgt].
  - now rewrite Nat.min_l by lia.
  - rewrite Nat.min_r by lia. now rewrite !firstn_all2 by lia.
Qed.

Lemma pipe_take_firstn : forall q n,
  (0 <= n)%Z -> pipe_take q n = firstn (Z.to_nat n) q.
Proof.
  intros q n Hn. unfold pipe_take.
  rewrite Z2Nat.inj_min, Nat2Z.id. apply firstn_min_length.
Qed.

Lemma pipe_take_length : forall q n,
  (Z.of_nat (length (pipe_take q n)) <= Z.max 0 n)%Z.
Proof.
  intros q n. unfold pipe_take. rewrite length_firstn. lia.
Qed.

(** The queue after a read of [k] bytes.  The mark does not move: the
    bytes a reader consumed are at the FRONT of the page and stay
    unavailable to writers.

    [k] is a [nat] and stays one: every caller passes the LENGTH OF THE
    DELIVERED PREFIX, which [pipe_take] has already bounded by the
    queue, so no count reaches this in unary.  [skipn (length (firstn k
    q)) q = skipn k q], so passing the delivered length is the same
    queue the count would have left. *)
Definition pipe_consume (st : PipeBuf) (k : nat) : PipeBuf :=
  (skipn k (fst st), snd st).

Lemma skipn_min_length : forall (A : Type) (l : list A) (n : nat),
  skipn (Nat.min n (length l)) l = skipn n l.
Proof.
  intros A l n. destruct (Nat.le_gt_cases n (length l)) as [Hle|Hgt].
  - now rewrite Nat.min_l by lia.
  - rewrite Nat.min_r by lia. now rewrite !skipn_all2 by lia.
Qed.

Lemma pipe_consume_of_take : forall q used n,
  (0 <= n)%Z ->
  pipe_consume (q, used) (length (pipe_take q n))
  = pipe_consume (q, used) (Z.to_nat n).
Proof.
  intros q used n Hn. unfold pipe_consume, pipe_take. cbn.
  rewrite length_firstn, Z2Nat.inj_min, Nat2Z.id.
  assert (E : Nat.min (Nat.min (Z.to_nat n) (length q)) (length q)
              = Nat.min (Z.to_nat n) (length q)) by lia.
  rewrite E. now rewrite !skipn_min_length.
Qed.

(** The id a new pipe gets: the number of pipes created so far.

    Entries are NEVER REMOVED from [fdst_pipes] — closing both ends of a
    pipe drops its two fds but leaves the table entry behind — so this
    counts creations, and an id is never reused for a second pipe.  That
    is the point: were an id recycled, a fresh pipe could inherit the
    bytes of a dead one.  The dead entry is unreachable (no fd names it)
    and costs only its bytes, which the model keeps rather than inventing
    a reclamation rule; Linux frees the pipe inode, and nothing a program
    can do observes the difference.

    [Pipe.pipe2_spec] still CHECKS that the id it computes is free (as
    [Open.openat_spec] checks [lowest_fd]'s answer), so a run long enough
    to wrap the 64-bit counter declines rather than aliasing. *)
Definition pipe_new_id (ps : list (word * PipeBuf)) : word :=
  Z_to_bv 64 (Z.of_nat (length ps)).

(** Is some fd in the table an end of pipe [id] of the given direction?
    [writer = true] asks "does this pipe still have a WRITER", the test
    that separates a pipe read at end-of-data into end-of-file (return 0)
    from a block; [writer = false] asks "does it still have a READER",
    which is what stands between a write and SIGPIPE.

    DERIVED, not counted.  Linux keeps [pipe->readers] / [pipe->writers]
    and [pipe_release] decrements them by the file's [f_mode]
    (fs/pipe.c:730-733, v6.18.46); the model
    reads the same fact off the fd table instead, so there is no counter
    to keep in step with [close] — and no way for one to drift.  The two
    agree because [Pipe.pipe2_spec] is the ONLY thing in this model that
    constructs an [FdPipe], so a pipe end exists exactly where this table
    shows one — whatever paths the image happens to contain.  Stated that
    way on purpose: an enumeration of the syscalls that
    could alias an end and are absent would be
    falsified by anything added below it.  [openat] resolves against
    [m_fs] and yields an [FdFile]/[FdFileW]/[FdFileA]/[FdFileRW] — or,
    for the device paths it answers, an [FdDevNull] or an [FdUrandom] — never
    an [FdPipe], so a path
    merely NAMED like a procfs one cannot hand out a second reference.

    A syscall that DUPLICATES a descriptor would keep the two
    constructions in step for a reason worth writing down, because a
    per-fd counter would not: Linux's counters are per [struct file], and
    a duplication creates no new one — [f_dupfd] (fs/file.c:1472,
    v6.18.46) and [do_dup2] (:1265) each just [get_file] the existing one
    (:1480, :1303) — so [pipe->writers] does not move and [pipe_release]
    runs only at the last [fput], while a copy here is a second TABLE
    ENTRY and this scan answers [true] while EITHER entry survives and
    [false] once both are gone, the same moment.

    THAT IS AN ARGUMENT ABOUT A CASE NOTHING REACHES, and what keeps it
    unreached is an arm rather than an absence: [dup] (23) and [dup3]
    (24) ARE modeled, and both consult [Fs.File.dup_modeled_entry], whose
    [| FdPipe _ _ => false] declines a pipe end instead of copying its
    entry.  So no second [FdPipe] naming one pipe is ever built, and
    [Pipe.pipe2_spec] remains the only constructor.  The paragraph above
    is recorded because a later change lifting that decline needs it, not
    because nothing in the model duplicates a descriptor.

    THE OTHER WAY A [struct file] OUTLIVES ITS FD is fd-passing, and it
    matters here for a reason this scan cannot see: Linux counts
    [pipe->writers] per [struct file], so a pipe end in flight over a
    socket — sent, its sender's fd closed, not yet received — still holds
    the pipe open and still blocks a reader, while this table shows no
    end and would answer end-of-file.  That is the one shape where
    reading the fd table is not merely a different spelling of the
    kernel's counter but a WRONG one.

    What closes it is an arm in a different file, and the coupling is
    worth stating because nobody would look for it here:
    [Net.Socket.socket_spec] answers [unmodeled] for every family but
    AF_INET, and at v6.18.46 fd-passing is AF_UNIX only —
    [unix_attach_fds] (net/unix/af_unix.c:1958) is the sole path from an
    SCM_RIGHTS control message to an installed descriptor, and SCM_RIGHTS
    appears nowhere in net/ipv4: [ip_cmsg_send] (net/ipv4/ip_sockglue.c)
    understands IP_RETOPTS, IP_PKTINFO, IP_TTL, IP_TOS and IP_PROTOCOL,
    none of which carries an fd.  So no modeled socket can transport one.

    THE CONDITION THAT FALSIFIES THIS: modelling AF_UNIX.  A change that
    admits that family reopens the case above, and it must either decline
    a pipe end at [sendmsg]'s control data or give this model a notion of
    a pipe end held by nothing in the fd table.  The decline in
    [socket_spec] is load-bearing for pipe end-of-file, not only for
    sockets.

    THE GENERAL CLAIM, since the paragraphs above each argue one route and
    the scan depends on all of them at once: NO REFERENCE TO A PIPE EXISTS
    OUTSIDE THIS TABLE.  That is strictly stronger than "no second fd
    names a pipe end", which is what the arms in [Fs.File] and
    [Checks.Cases.Fs.Pipe] establish, and it is the one the scan needs —
    Linux counts [struct file]s, so a reference with no fd is exactly the
    gap between the two claims.  It holds today because every way to make
    one is declined, each by a named arm rather than by absence:

    - a second PROCESS is what the dup paragraph above does not cover:
      [Kernel.Fork.clone_no_shared_file_b] answers [false] for [FdPipe],
      so a clone with either end open is [unmodeled], and
      [clone_fork_flags_b] admits only the bare SIGCHLD word, so
      CLONE_FILES and CLONE_THREAD never share a table and no second
      instruction stream exists to race a close;
    - [F_DUPFD] does NOT go through [Fs.File.dup_modeled_entry] the way
      [dup] and [dup3] do.  It is declined by [Fcntl.fcntl_spec]'s
      closing [unmodeled], which refuses every command that spec does
      not model — a decline that is not pipe-specific and would
      evaporate the moment [F_DUPFD] is modeled for any reason at all.
      Of the three duplication routes this is the weak one, and it is
      the only one that holds by nothing having been added rather than
      by an arm.  [Fcntl.fcntl_spec] carries the obligation in its own
      prose too, beside its [F_DUPFD] bullet, because this file is not
      where someone widening fcntl's command set will look;
    - a reference IN FLIGHT is closed by two gates, the AF_INET one
      argued above and [Net.Socket.sendmsg_spec]'s
      [if negb (w_is0 ctllen) then unmodeled], which the paragraph above
      names only as something a future AF_UNIX change would need.

    ONLY THE WRITER DIRECTION IS A SOUNDNESS EXPOSURE, which is what
    decides how much any future widening costs.  Under-reporting a WRITER
    makes a read at end-of-data answer 0 where Linux blocks: a modeled
    answer Linux would not give, and the one shape here that costs
    priority 1.  Under-reporting a READER makes the write arm's
    [negb (pipe_end_live … false)] guard fire, which is [unmodeled] — a
    coverage loss, not an unsound answer. *)
Fixpoint pipe_end_live (fds : list (word * FdEntry)) (id : word)
    (writer : bool) : bool :=
  match fds with
  | [] => false
  | (_, FdPipe id' w) :: r =>
      (bv_eqb id' id && Bool.eqb w writer) || pipe_end_live r id writer
  (* The non-pipe kinds are named rather than wildcarded, so that a
     later [FdEntry] constructor able to name a pipe end stops the build
     here instead of being skipped silently.  The paragraph above argues
     from what CONSTRUCTS an [FdPipe]; this match is what would have to
     re-read that argument, and a [_ ::] arm is exactly the shape that
     would not.  A missed end costs differently in the two directions,
     per the asymmetry above: on [writer = true] it fails OPEN, answering
     a modeled 0 where Linux blocks, which is a wrong answer rather than
     an [unmodeled] — that is what makes the silent arm expensive.  On
     [writer = false] it fails CLOSED instead, since the write arm
     declines on [negb (pipe_end_live … false)] and a missed reader only
     makes that guard fire more often. *)
  | (_, FdChannel _) :: r => pipe_end_live r id writer
  | (_, FdFile _ _) :: r => pipe_end_live r id writer
  | (_, FdFileW _ _) :: r => pipe_end_live r id writer
  | (_, FdFileA _ _) :: r => pipe_end_live r id writer
  | (_, FdFileRW _ _) :: r => pipe_end_live r id writer
  | (_, FdDir) :: r => pipe_end_live r id writer
  | (_, FdSocket _) :: r => pipe_end_live r id writer
  | (_, FdDevNull _ _) :: r => pipe_end_live r id writer
  | (_, FdUrandom) :: r => pipe_end_live r id writer
  end.

(** A 32-bit value as the four little-endian bytes the kernel's
    [copy_to_user] of an [int] lays down. *)
Definition le32_bytes (v : word) : list byte :=
  let z := bv_unsigned v in
  [ Z_to_bv 8 z;
    Z_to_bv 8 (Z.shiftr z 8);
    Z_to_bv 8 (Z.shiftr z 16);
    Z_to_bv 8 (Z.shiftr z 24) ].

(** The eight bytes [pipe2] copies out: the read end then the write end,
    as one [int fildes[2]] — a SINGLE contiguous range, which is how
    [do_pipe2]'s one [copy_to_user] writes it (fs/pipe.c:1040, with
    [fd[0] = fdr] and [fd[1] = fdw] set at :1005-1006, v6.18.46). *)
Definition pipe_fd_bytes (fdr fdw : word) : list byte :=
  le32_bytes fdr ++ le32_bytes fdw.

(* =========================================================================
   VmMaps helpers — interval arithmetic in Z over unsigned values
   ========================================================================= *)

(** Do [lo1,lo1+n1) and [lo2,lo2+n2) overlap?  Computed in [Z]: the sums
    cannot wrap. *)
Definition iv_overlap (a1 n1 a2 n2 : word) : bool :=
  Z.ltb (bv_unsigned a1) (bv_unsigned a2 + bv_unsigned n2)
  && Z.ltb (bv_unsigned a2) (bv_unsigned a1 + bv_unsigned n1).

(** Is [lo, lo+n) disjoint from every live mapping? *)
Fixpoint region_free (maps : list (word * word)) (lo n : word) : bool :=
  match maps with
  | [] => true
  | (a, sz) :: r => negb (iv_overlap lo n a sz) && region_free r lo n
  end.

(** [region_free] read entry by entry: a free region misses EVERY entry
    of the ledger it was checked against, wherever that entry sits in the
    list. *)
Lemma region_free_In : forall maps lo n a sz,
  region_free maps lo n = true ->
  In (a, sz) maps ->
  iv_overlap lo n a sz = false.
Proof.
  induction maps as [|[b s] r IH]; intros lo n a sz Hfree Hin;
    [contradiction|].
  cbn in Hfree. apply andb_true_iff in Hfree as [Hhd Htl].
  destruct Hin as [Heq|Hin].
  - inversion Heq; subst.
    destruct (iv_overlap lo n a sz); [discriminate|reflexivity].
  - apply (IH lo n a sz Htl Hin).
Qed.

(** …and the converse, which is how a freeness claim is DISCHARGED from a
    per-entry argument. *)
Lemma region_free_intro : forall maps lo n,
  (forall a sz, In (a, sz) maps -> iv_overlap lo n a sz = false) ->
  region_free maps lo n = true.
Proof.
  induction maps as [|[b s] r IH]; intros lo n H; [reflexivity|].
  cbn. rewrite (H b s ltac:(now left)). cbn.
  apply IH. intros a sz Hin. apply H. now right.
Qed.

(** …and the same fold read the OTHER way: a region the ledger refuses
    is refused by a NAMED entry.  [region_free_In] says what freeness
    gives you; this says what its failure gives you, which is what a
    caller needs in order to ask whether the entry that refused is a
    real one.  [vm_noaccess] is where that question has an answer worth
    writing down — see [entries_nonzero] below. *)
Lemma region_free_false : forall maps lo n,
  region_free maps lo n = false ->
  exists a sz, In (a, sz) maps /\ iv_overlap lo n a sz = true.
Proof.
  induction maps as [|[b s] r IH]; intros lo n H; [discriminate|].
  cbn in H. destruct (iv_overlap lo n b s) eqn:E; cbn in H.
  - exists b, s. split; [now left | exact E].
  - destruct (IH lo n H) as [a [sz [Hin Hov]]].
    exists a, sz. split; [now right | exact Hov].
Qed.

(** Drop any mapping based at [lo] (munmap of a whole anonymous mapping). *)
Definition map_remove (maps : list (word * word)) (lo : word)
    : list (word * word) :=
  List.filter (fun p => negb (bv_eqb (fst p) lo)) maps.

(** Top of the reserved image: the least address at or above every reserved
    (page-rounded LOAD) segment [a, a+sz).  On Linux the initial program
    break [mm->start_brk] sits just above the end of BSS, i.e. above the
    loaded image; a [brk] request BELOW it is invalid and returns the break
    unchanged (see [Mmap.min_brk] / [Mmap.brk_spec]).  Empty image => 0.
    Computed in [Z] over unsigned values (sums cannot wrap, matching the
    old unbounded-[N] semantics). *)
Fixpoint reserved_top (maps : list (word * word)) : Z :=
  match maps with
  | [] => 0%Z
  | (a, sz) :: r => Z.max (bv_unsigned a + bv_unsigned sz) (reserved_top r)
  end.

(** Subtract the half-open interval [lo, hi) from every mapping, keeping the
    parts that fall OUTSIDE it (each mapping may split into a left and/or a
    right remnant, or vanish).  A [brk] SHRINK uses it in two deliberately
    different ways (see [Mmap.brk_model_next]): [vm_maps] drops the logical,
    byte-granular heap tail [new_break, old_break), preserving exact live-byte
    budget accounting, while [vm_noaccess] drops only the page-rounded range
    named by [Mmap.brk_unmaps].  The latter is the kernel's actual
    [do_vmi_align_munmap] interval and is also what the running program sees
    in [eff_unmaps].  Higher anonymous mmaps and lower mappings survive, and
    one straddling record is truncated.
    Arithmetic in [Z] over unsigned values (no wrapping); the remnant
    bases/sizes fit in 64 bits by construction, so the [Z_to_bv]
    round-trips are lossless.  The interval ENDPOINTS are taken in [Z]
    too, for the same reason: an end of exactly 2^64 is a legitimate
    half-open bound, so a caller that reconstructed it as a [word] sum
    could wrap it to 0 and subtract the wrong range.  In [Z] that is
    unrepresentable — callers pass [bv_unsigned lo + bv_unsigned len]
    directly. *)
Definition iv_subtract (a sz : word) (loZ hiZ : Z) : list (word * word) :=
  let aZ  := bv_unsigned a  in let szZ := bv_unsigned sz in
  let left  := if (aZ <? loZ)%Z
               then [(a, Z_to_bv 64 (Z.min szZ (loZ - aZ)))] else [] in
  let right := if (hiZ <? aZ + szZ)%Z
               then [(Z_to_bv 64 (Z.max aZ hiZ),
                      Z_to_bv 64 (aZ + szZ - Z.max aZ hiZ))] else [] in
  left ++ right.

Fixpoint maps_subtract (maps : list (word * word)) (lo hi : Z)
    : list (word * word) :=
  match maps with
  | [] => []
  | (a, sz) :: r => iv_subtract a sz lo hi ++ maps_subtract r lo hi
  end.

(** Remove every inaccessible interval from [maps].  The result is the
    model's BACKED view: anonymous bytes that are presently readable and
    writable.  This is intentionally a conservative commit-time backing
    guarantee, not first-touch accounting, physical frames, RSS, swap, or a
    page-table model. *)
Fixpoint maps_subtract_all (maps cuts : list (word * word))
    : list (word * word) :=
  match cuts with
  | [] => maps
  | (a, n) :: rest =>
      maps_subtract_all
        (maps_subtract maps (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
        rest
  end.

(** A ledger list whose every entry names at least one BYTE.

    Why a ledger would want to say so: [iv_overlap] reports an overlap
    against a ZERO-SIZE interval strictly inside the queried range —
    [iv_overlap lo n a 0] is [lo < a && a < lo + n], which is true for
    any [a] strictly between — so a vacuous entry makes [region_free]
    false over a region it names no byte of.  Every consumer of
    [region_free] is therefore reading a gate that a vacuous entry can
    close for no reason, and a reader who wants to know whether that
    can happen has to go and inspect every writer of the list.  This
    property, and the three closure lemmas under it, are where that
    inspection is done once.

    The list-building operations are the whole of what has to be
    checked, because no writer in this tree builds a ledger list any
    other way: the lists start empty at [init_model] and grow by
    [cons], shrink by [maps_subtract], and (for [brk]) shrink by
    [Mmap.maps_subtract_ranges], which is a fold of [maps_subtract].

    [maps_subtract] is the interesting one.  It is not obvious from
    [iv_subtract] that a cut cannot leave an empty remnant, since both
    remnants are built with a [Z.min] and a subtraction; what makes it
    true is that each remnant is EMITTED only under the guard that
    makes it nonempty ([aZ < loZ] for the left, [hiZ < aZ + szZ] for
    the right).  A cut of a nonempty entry is therefore nonempty or
    absent, never present and vacuous. *)
Definition entries_nonzero (maps : list (word * word)) : Prop :=
  forall a n, In (a, n) maps -> (0 < bv_unsigned n)%Z.

Lemma entries_nonzero_nil : entries_nonzero [].
Proof. intros a n []. Qed.

(** The computational way in, for a fixture whose list is a literal: a
    [vm_compute] on the [forallb] discharges the property without the
    call site taking the list apart by hand. *)
Lemma entries_nonzero_forallb : forall maps,
  forallb (fun p => Z.ltb 0 (bv_unsigned (snd p))) maps = true ->
  entries_nonzero maps.
Proof.
  induction maps as [|[a n] r IH]; intros H b s Hin; [contradiction |].
  cbn [forallb] in H. apply andb_true_iff in H as [Hh Ht].
  destruct Hin as [Heq | Hin].
  - inversion Heq; subst. cbn [snd] in Hh. now apply Z.ltb_lt in Hh.
  - exact (IH Ht b s Hin).
Qed.

Lemma entries_nonzero_cons : forall (a n : word) r,
  (0 < bv_unsigned n)%Z ->
  entries_nonzero r ->
  entries_nonzero ((a, n) :: r).
Proof.
  intros a n r Hn Hr b s [Heq | Hin].
  - inversion Heq; subst. exact Hn.
  - exact (Hr b s Hin).
Qed.

(** The two small round-trip facts the remnant arithmetic needs.
    [Mm/Mremap.v] carries its own copies under its own names; these are
    the ones the lemmas in this file use. *)
Lemma bv_unsigned_range_u64 : forall w : word,
  (0 <= bv_unsigned w < two_pow_64)%Z.
Proof.
  intro w. pose proof (bv_unsigned_in_range 64 w) as H.
  change (bv_modulus 64) with two_pow_64 in H. exact H.
Qed.

Lemma bv_unsigned_Z_to_bv_u64 : forall z,
  (0 <= z < two_pow_64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. apply Z_to_bv_small.
  change (bv_modulus 64) with two_pow_64. exact Hz.
Qed.

(** Cutting a NONEMPTY entry leaves nonempty remnants: each of the two
    is emitted under exactly the guard that makes its size positive. *)
Lemma iv_subtract_nonzero : forall (a sz : word) loZ hiZ,
  (0 < bv_unsigned sz)%Z ->
  entries_nonzero (iv_subtract a sz loZ hiZ).
Proof.
  intros a sz loZ hiZ Hsz b s Hin.
  unfold iv_subtract in Hin. cbv zeta in Hin.
  pose proof (bv_unsigned_range_u64 a) as Ha.
  pose proof (bv_unsigned_range_u64 sz) as Hs.
  apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - destruct (bv_unsigned a <? loZ)%Z eqn:E1; cbn in Hin; [| contradiction].
    apply Z.ltb_lt in E1. destruct Hin as [Heq | []].
    inversion Heq; subst b s.
    pose proof (Z.min_spec (bv_unsigned sz) (loZ - bv_unsigned a)).
    rewrite bv_unsigned_Z_to_bv_u64 by lia. lia.
  - destruct (hiZ <? bv_unsigned a + bv_unsigned sz)%Z eqn:E2;
      cbn in Hin; [| contradiction].
    apply Z.ltb_lt in E2. destruct Hin as [Heq | []].
    inversion Heq; subst b s.
    pose proof (Z.max_spec (bv_unsigned a) hiZ).
    rewrite bv_unsigned_Z_to_bv_u64 by lia. lia.
Qed.

Lemma maps_subtract_nonzero : forall maps loZ hiZ,
  entries_nonzero maps ->
  entries_nonzero (maps_subtract maps loZ hiZ).
Proof.
  induction maps as [|[a sz] r IH]; intros loZ hiZ H b s Hin;
    [contradiction |].
  cbn [maps_subtract] in Hin. apply in_app_or in Hin.
  destruct Hin as [Hin | Hin].
  - exact (iv_subtract_nonzero a sz loZ hiZ
             (H a sz (or_introl eq_refl)) b s Hin).
  - exact (IH loZ hiZ (fun x y Hx => H x y (or_intror Hx)) b s Hin).
Qed.

Lemma maps_subtract_all_nonzero : forall cuts maps,
  entries_nonzero maps ->
  entries_nonzero (maps_subtract_all maps cuts).
Proof.
  induction cuts as [|[a n] rest IH]; intros maps H; [exact H |].
  cbn [maps_subtract_all]. apply IH. now apply maps_subtract_nonzero.
Qed.

Definition vm_backed_maps (h : VmMaps) : list (word * word) :=
  maps_subtract_all (vm_maps h) (vm_noaccess h).

(** ** Atomic first-access accounting

    The instruction interpreter reports successful data-memory accesses as
    [(address, byte_count)] pairs.  These helpers turn the complete report for
    one instruction into the pages that a lazy anonymous mapping would need
    to materialize.  They are deliberately pure: [materialize_accesses]
    returns the complete new ledger or [None], so a cross-page access cannot
    spend one page and then fail on the next.

    [lazy] contains page-aligned MAP_NORESERVE ranges — enforced by
    [vm_add_lazy], which records only a reservation's aligned interior, so
    the bytes [vm_backing_used] subtracts are exactly the bytes a first
    touch can charge back.  A reported page is
    charged only when one lazy range contains the whole page; ordinary mapped
    memory remains part of [used] already.  [materialized] stores page bases,
    and insertion is idempotent, so repeated reads or writes do not charge
    twice.  This is an abstract backing guarantee, not physical frames, RSS,
    swap, or page-table state. *)
Definition page_base_of (z : Z) : word :=
  Z_to_bv 64 ((z / page_size) * page_size).

Definition page_base (a : word) : word := page_base_of (bv_unsigned a).

Definition page_mem (p : word) (pages : list word) : bool :=
  existsb (bv_eqb p) pages.

Definition page_insert (p : word) (pages : list word) : list word :=
  if page_mem p pages then pages else p :: pages.

(** The byte cursor advances in [Z], not by bitvector [+].  BvBase's
    second rule is that range arithmetic is done in [Z] over [bv_unsigned]
    so it cannot wrap; stepping a [word] here would fold the top of the
    address space back onto page 0 and charge a page the access never
    touched.  That direction is an over-charge, and no reported access can
    reach it while [alloc_top] sits far below 2^64 (a stack's width under
    2^47 for any [Run.valid_sp]) — but the rule is
    the rule, and the cursor is the one place this file broke it. *)
Fixpoint access_pages_acc (base : Z) (n : nat) (pages : list word)
    : list word :=
  match n with
  | O => pages
  | S n' =>
      access_pages_acc (base + 1)%Z n' (page_insert (page_base_of base) pages)
  end.

Definition access_pages (a : word) (n : nat) : list word :=
  access_pages_acc (bv_unsigned a) n [].

Fixpoint accesses_pages (accesses : list (word * nat))
    (pages : list word) : list word :=
  match accesses with
  | [] => pages
  | (a, n) :: rest =>
      accesses_pages rest (access_pages_acc (bv_unsigned a) n pages)
  end.

Definition page_in_ranges (p : word) (ranges : list (word * word)) : bool :=
  existsb
    (fun r =>
       let lo := bv_unsigned (fst r) in
       let hi := (lo + bv_unsigned (snd r))%Z in
       (lo <=? bv_unsigned p)%Z
       && (bv_unsigned p + page_size <=? hi)%Z)
    ranges.

Definition newly_materialized_pages (lazy : list (word * word))
    (materialized : list word) (accesses : list (word * nat)) : list word :=
  List.filter
    (fun p => page_in_ranges p lazy && negb (page_mem p materialized))
    (accesses_pages accesses []).

Definition materialize_accesses (lazy : list (word * word))
    (materialized : list word) (used limit : Z)
    (accesses : list (word * nat)) : option (list word) :=
  let new := newly_materialized_pages lazy materialized accesses in
  match new with
  | [] => Some materialized
  | _ =>
      if (used + Z.of_nat (List.length new) * page_size <=? limit)%Z
      then Some (new ++ materialized)
      else None
  end.

(** Accessible anonymous bytes in a VM ledger: everything mapped, less
    every inaccessible interval.  This measures a [VmMaps] alone and knows
    nothing of sparse provenance, so it is NOT a live process's backing
    charge -- [vm_backing_used] just below is, and the two differ by the
    lazy ranges it cuts out and the materialized pages it adds back.

    BOTH ARE LIVE, and which one is right depends on the question.  Ask
    this one how much of a ledger is accessible: the
    [vm_live_bytes]/[vm_backed_bytes] pairs in [Checks/Cases/Mm/Mmap.v]
    state a fixed commit's two accounts side by side, virtual occupancy
    against exposed capacity, and there is no [Model] at those sites to
    have a lazy ledger.  [Common/AllocSim.v]'s pure allocator algebra also
    asks it, and may: its [vm_model] packages a ledger with EMPTY sparse
    state, so [vm_backing_used (vm_model h) = vm_backed_bytes h] holds for
    every [h] by construction, not by accident of the corpus.  The live
    brk budget is a different predicate on a real [Model]
    ([Sys/Mm/Mmap.brk_grow_ok]) and asks [vm_backing_used].

    It lives here, beside the measure it is contrasted with, because
    separated from that
    contrast it reads as a duplicate of [vm_backing_used] with no callers. *)
Definition vm_backed_bytes (h : VmMaps) : Z :=
  live_bytes (vm_backed_maps h).

(** Backing already consumed by a process: eagerly backed readable mappings
    with every lazy reservation cut out, plus the lazy pages charged so far.
    The ledgers are maintained together by the VM syscall helpers below.

    INVARIANT, load-bearing: EVERY LAZY RANGE IS PAGE-ALIGNED.  The
    subtraction here is by whole byte extent, while [page_in_ranges]
    charges a page back only when ONE lazy range contains that whole page.
    Those two agree only on page-aligned ranges; on an unaligned one the
    bytes between them leave the budget and no access can restore them,
    which is an under-charge -- the direction that grants an allocation
    the kernel refuses.

    The invariant holds by construction rather than by argument.  Exactly
    two operations put a range INTO [m_vm_lazy], and both clip to
    [lazy_interior]: [vm_add_lazy], for a fresh MAP_NORESERVE mapping, and
    [vm_resize_backing], for the destination of an mremap that carries
    lazy provenance.  [vm_forget_range] and the [maps_subtract] inside
    [vm_resize_backing] only remove bytes, and removing from an aligned
    range by aligned bounds leaves an aligned range.

    A THIRD way to add one would have to clip the same way; the invariant
    is not re-derivable from the call sites, because neither constructor
    checks its caller.  Every write to either ledger goes through
    [with_vm_backing], so that is where to find the current set of writers,
    and where a new one has to appear.  The alternative, making this
    subtraction page-granular so no precondition is needed at all, is
    deliberately not taken: it would move a definition ~30 sites across
    Common/ and the examples depend on, to close a state nothing can
    build.  [Checks/Cases/Mm/Mmap.v]'s
    [lazy_unaligned_reservation_frees_no_backing] pins the constructor's
    half at the model level, where such a range CAN be built. *)
Definition vm_backing_used (m : Model) : Z :=
  (live_bytes
     (maps_subtract_all (vm_backed_maps (m_vmmaps m)) (m_vm_lazy m))
   + Z.of_nat (List.length (m_vm_materialized m)) * page_size)%Z.

(** The one backed-memory gate used by VM operations.  It is stated over
    [Model], not [VmMaps], because sparse-mapping provenance and first-touch
    charges live in [VmState].  Testing a reconstructed [vm_backed_bytes]
    total here would charge every MAP_NORESERVE reservation eagerly. *)
Definition vm_backing_within_limit (m : Model) : bool :=
  (vm_backing_used m <=? vm_limit (m_vmmaps m))%Z.

Definition materialize_model_accesses (m : Model)
    (accesses : list (word * nat)) : option Model :=
  match materialize_accesses (m_vm_lazy m) (m_vm_materialized m)
          (vm_backing_used m) (vm_limit (m_vmmaps m)) accesses with
  | Some pages => Some (with_vm_backing (m_vm_lazy m) pages m)
  | None => None
  end.

Definition page_outside_range (lo hi : Z) (p : word) : bool :=
  negb ((lo <=? bv_unsigned p)%Z && (bv_unsigned p <? hi)%Z).

(** Forget sparse-backing metadata for an unmapped or replaced interval.
    Range subtraction handles partial lazy reservations; materialized pages
    are page aligned, and every caller supplies page-aligned bounds. *)
Definition vm_forget_range (lo hi : Z) (m : Model) : Model :=
  with_vm_backing
    (maps_subtract (m_vm_lazy m) lo hi)
    (List.filter (page_outside_range lo hi) (m_vm_materialized m)) m.

Lemma materialize_model_accesses_no_lazy : forall m accesses,
  m_vm_lazy m = [] -> materialize_model_accesses m accesses = Some m.
Proof.
  intros [fd [maps lazy materialized] io fs proc lim] accesses Hlazy.
  cbn in Hlazy. subst lazy.
  unfold materialize_model_accesses. cbn.
  unfold materialize_accesses, newly_materialized_pages. cbn.
  induction (accesses_pages accesses []) as [|p pages IH]; cbn; [reflexivity|].
  exact IH.
Qed.

(** User-memory ranges named by a successful syscall effect.  Copy-from-user
    ranges were recorded while selecting the outcome; ordinary byte writes
    are copy-to-user destinations.  Zero-fill and symbolic-copy ranges are
    deliberately absent: creating or moving a lazy anonymous mapping must not
    materialize every untouched page. *)
Fixpoint write_accesses (writes : list (word * list byte))
    : list (word * nat) :=
  match writes with
  | [] => []
  | (a, bs) :: rest => (a, List.length bs) :: write_accesses rest
  end.

Definition syscall_effect_accesses (eff : SyscallEffect)
    : list (word * nat) :=
  eff_copyins eff ++ write_accesses (eff_writes eff).

Lemma materialize_model_accesses_frame : forall m accesses m',
  materialize_model_accesses m accesses = Some m' ->
  m_fd m' = m_fd m /\
  m_vmmaps m' = m_vmmaps m /\
  m_vm_lazy m' = m_vm_lazy m /\
  m_io m' = m_io m /\
  m_fsys m' = m_fsys m /\
  m_proc m' = m_proc m /\
  m_lim m' = m_lim m.
Proof.
  intros m accesses m' Haccount.
  unfold materialize_model_accesses in Haccount.
  destruct (materialize_accesses (m_vm_lazy m) (m_vm_materialized m)
              (vm_backing_used m) (vm_limit (m_vmmaps m)) accesses)
    as [pages|] eqn:Hpages; [|discriminate].
  inversion Haccount; subst.
  destruct m as [fd [maps lazy materialized] io fs proc lim].
  repeat split; reflexivity.
Qed.

(** The page-aligned interior of a reservation: exactly the pages a first
    touch can charge back.

    [vm_backing_used] subtracts a lazy range by its whole byte extent,
    while [page_in_ranges] charges a page back only when ONE range
    contains that whole page.  Those two agree only on page-aligned
    ranges.  On an unaligned one — or on a page split across two adjacent
    ranges — the bytes come off the budget and no access can ever put them
    back, which makes the memory FREE: an under-charge, the direction that
    lets the model grant an allocation the kernel refuses.

    Recording the interior rather than the request keeps both sides over
    the same bytes, so that state cannot be built.  Every caller is
    page-aligned already ([mmap] places on a page boundary and rounds the
    length up), so this is the identity on the reachable domain; it is
    here so the bad state is unconstructible rather than merely unreached.
    An unaligned caller would record LESS than it asked for, which
    over-charges — the safe direction. *)
Definition lazy_interior (a n : word) : list (word * word) :=
  let lo := bv_unsigned a in
  let hi := (lo + bv_unsigned n)%Z in
  let lo' := (((lo + page_size - 1) / page_size) * page_size)%Z in
  let hi' := ((hi / page_size) * page_size)%Z in
  if (lo' <? hi')%Z
  then [(Z_to_bv 64 lo', Z_to_bv 64 (hi' - lo'))]
  else [].

Definition vm_add_lazy (a n : word) (m : Model) : Model :=
  with_vm_backing (lazy_interior a n ++ m_vm_lazy m) (m_vm_materialized m) m.

(** Move or resize the sparse-backing metadata belonging to one whole
    anonymous mapping.  [source_lazy] says the source is uniformly
    MAP_NORESERVE; callers reject mixed lazy/eager sources.  Materialized
    pages retain their source-relative offset, pages cut by a shrink are
    released, and a grown lazy tail starts unmaterialized.  Destination
    metadata is removed first so even a hand-built stale ledger cannot
    manufacture backing by colliding with the move. *)
Definition page_in_half_open (lo hi : Z) (p : word) : bool :=
  (lo <=? bv_unsigned p)%Z && (bv_unsigned p <? hi)%Z.

Definition move_page_base (old dst p : word) : word :=
  Z_to_bv 64 (bv_unsigned dst + (bv_unsigned p - bv_unsigned old)).

Definition vm_resize_backing (source_lazy : bool)
    (old old_n dst new_n : word) (m : Model) : Model :=
  let old_lo := bv_unsigned old in
  let old_hi := (old_lo + bv_unsigned old_n)%Z in
  let dst_lo := bv_unsigned dst in
  let dst_hi := (dst_lo + bv_unsigned new_n)%Z in
  let kept_lazy :=
    maps_subtract
      (maps_subtract (m_vm_lazy m) old_lo old_hi) dst_lo dst_hi in
  let kept_pages :=
    List.filter (page_outside_range dst_lo dst_hi)
      (List.filter (page_outside_range old_lo old_hi)
        (m_vm_materialized m)) in
  let moved_pages :=
    if source_lazy then
      List.map (move_page_base old dst)
        (List.filter
          (fun p => page_in_half_open old_lo old_hi p
                    && (bv_unsigned p - old_lo <? bv_unsigned new_n)%Z)
          (m_vm_materialized m))
    else [] in
  with_vm_backing
    (if source_lazy then lazy_interior dst new_n ++ kept_lazy else kept_lazy)
    (moved_pages ++ kept_pages) m.

(** Does ONE ledger interval contain the whole half-open range
    [lo,lo+n)?

    The predicate is NARROWER than the kernel's question, and
    deliberately so: the model never merges adjacent entries, so a range
    one kernel VMA covers can be spread across two model entries and
    answer "no" here.  That is the safe direction for every caller —
    it declines or re-cuts where Linux would not, never the reverse.

    A "no" does not mean the same thing at every call site, so read the
    site rather than this comment: some decline on it and some only
    select a different arm.  Which are which is not restated here,
    because nothing would fail when the list went stale. *)
Definition map_contains (maps : list (word * word)) (lo n : word) : bool :=
  existsb
    (fun p =>
       let aZ := bv_unsigned (fst p) in
       let hiZ := (aZ + bv_unsigned (snd p))%Z in
       Z.leb aZ (bv_unsigned lo)
       && Z.leb (bv_unsigned lo + bv_unsigned n) hiZ)
    maps.

(** Is [(lo, n)] exactly one of the live-mapping entries?  munmap's
    modeled case: the requested range coincides with a whole recorded
    mapping (see [Mmap.munmap_spec]). *)
Definition map_has (maps : list (word * word)) (lo n : word) : bool :=
  existsb (fun p => bv_eqb (fst p) lo && bv_eqb (snd p) n) maps.

(** The ledger invariant that keeps allocator placement off protected
    memory WITHOUT [vm_noaccess] ever being consulted.

    [vm_noaccess] is NOT a subset of [vm_maps], deliberately: purpose (c)
    above documents the one exception, a brk shrink inside its final page,
    which drops the byte-granular tail [[vm_brk, PAGE_ALIGN vm_brk)] from
    [vm_maps] while the page-rounded protected range stays whole.  The
    weaker property below survives that exception and is still enough for
    every placement decision, because placement is PAGE granular:

      every protected byte lies on a page that some live [vm_maps] entry
      still touches.

    In the orphan state the truncated entry [[e0, vm_brk)] is that
    witness — the shrink TRUNCATES the owning entry rather than removing
    it, so a nonempty orphan forces the entry to reach into the orphan's
    page.  [Checks/Examples.v]'s [noaccess_pages_owned_brk_orphan] and
    [noaccess_pages_owned_fails_without_residual] check that this holds on
    the real shrunken state and fails on the counterfactual one where the
    residual entry is taken away.

    The nonemptiness conjunct is not decoration: [iv_overlap] reports an
    overlap against a ZERO-size interval strictly inside the queried
    range, so without it a vacuous (empty) protected entry could block a
    request that touches no protected byte.  Every writer of
    [vm_noaccess] adds page-rounded, nonempty ranges and [iv_subtract]
    keeps remnants nonempty, so this costs nothing.

    [Mremap.mremap_fresh_avoids_noaccess] is the consumer: assuming this,
    a destination [mremap_fresh_b] accepts is disjoint from
    [vm_noaccess], which is the property the predicate's comment argues
    informally.  [Checks/NoaccessOwned.v] proves it of every reachable
    state: a stronger invariant [sys_inv] holds of [init_model]
    ([init_model_sys_inv]), every step of a run keeps it
    ([star_preserves_sys_inv]), and it gives this one
    ([sys_inv_noaccess_pages_owned]). *)
Definition noaccess_pages_owned (h : VmMaps) : Prop :=
  forall a n,
    In (a, n) (vm_noaccess h) ->
    (0 < bv_unsigned n)%Z
    /\ forall x,
         (bv_unsigned a <= x < bv_unsigned a + bv_unsigned n)%Z ->
         exists b s,
           In (b, s) (vm_maps h)
           /\ (bv_unsigned b < page_round_down_Z x + page_size
               /\ page_round_down_Z x < bv_unsigned b + bv_unsigned s)%Z.

(** The nonemptiness conjunct of that invariant, on its own.

    The two conjuncts are not equally hard.  The page-ownership half is
    kept only through the stronger [Checks.NoaccessOwned.sys_inv], and
    [Mremap.mremap_fresh_avoids_noaccess] takes the whole invariant as
    a hypothesis.  The NONEMPTINESS half is preserved by construction,
    and it is what every [region_free] reader of [vm_noaccess] actually
    leans on — [Madvise.madvise_dontneed_ok]'s third conjunct and
    [Mremap.mremap_ok]'s — because a vacuous entry closes a
    [region_free] gate over a range it names no byte of (see
    [entries_nonzero] above, and
    [Madvise.madvise_noaccess_decline_names_a_protected_byte] for the
    consumer).

    Separating it is what lets a consumer cite a fact the writers are
    shown to keep instead of assuming an invariant nothing establishes.
    [init_model] starts the list empty, and every writer builds the next
    one with [cons], [maps_subtract] or [Mmap.maps_subtract_ranges], so
    the closure lemmas above are the whole of what a writer needs.
    [Mm/Mmap.v]'s section "the protected ledger names real bytes" lists
    every writer, says which of the three things each does to the list,
    and carries a preservation lemma for each; [Mm/Mprotect.v] has the
    one writer outside that file.  The writers that are named post-state
    functions get a lemma about the definition; the ones [mmap_spec] and
    [munmap_spec] write inline get a lemma that RESTATES the record,
    with the cost of that restatement stated where the lemmas are.

    THE COMPOSITION is [Checks/NoaccessOwned.v]'s: [init_model_sys_inv]
    holds at the start, [star_preserves_sys_inv] (and
    [star_cfg_preserves_sys_inv]) carries [sys_inv] along every
    execution, and [sys_inv] gives [noaccess_pages_owned] and so this. *)
Definition vm_noaccess_entries_nonzero (h : VmMaps) : Prop :=
  entries_nonzero (vm_noaccess h).

(** The stronger invariant implies the weaker one, so a caller already
    carrying [noaccess_pages_owned] need not carry both. *)
Lemma noaccess_pages_owned_nonzero : forall h,
  noaccess_pages_owned h -> vm_noaccess_entries_nonzero h.
Proof. intros h H a n Hin. exact (proj1 (H a n Hin)). Qed.

(* =========================================================================
   The run's private /tmp, as keys of the flat file system
   ========================================================================= *)

(** "/tmp/" — the prefix under which the run's declared PRIVATE
    temporary directory is carried in the flat map ([Fs.Fs]).

    WHY THE KEY IS ABSOLUTE.  The model has no directory structure and
    no working directory, so "the file [out.gif] inside /tmp" has to be
    a key like any other.  Spelling it exactly as the program spells it
    — "/tmp/out.gif" — is what lets the three modeled operations reach
    the EXISTING arms: the descriptor a create hands out is an ordinary
    [FdFileW] on that key, and read, write, lseek, fstat and close on it
    are the same arms every file uses.  A relative key can
    never collide with one of these, because no key of a relative name
    begins with "/".

    The prefix is five bytes: '/', 't', 'm', 'p', '/'.  Only
    [Fs.Namei.tmp_name] takes it apart again, and only for a path that
    has exactly ONE further component. *)
Definition tmp_prefix : Fs.path :=
  [Z_to_bv 8 47; Z_to_bv 8 116; Z_to_bv 8 109; Z_to_bv 8 112; Z_to_bv 8 47].

(** The flat-map key of the /tmp entry named [name]. *)
Definition tmp_key (name : Fs.path) : Fs.path := tmp_prefix ++ name.

(** A name with a NUL byte in it is not a name: [read_cstr] stops at the
    first NUL, so no pathname a program can pass names such an entry,
    and Linux's directory entries cannot hold one either.  A declaration
    that mentions one describes nothing, and [fs_seed_tmp] drops it.
    Dropping it is also what keeps the seeded image inside
    [Fs.valid_fs], whose second clause is exactly this test — see
    [fs_seed_tmp_valid]. *)
Definition tmp_nul_free (name : Fs.path) : bool :=
  negb (existsb (fun b => bv_eqb b (Z_to_bv 8 0)) name).

(** Seed a declared private /tmp into a file-system image: insert each
    declared entry under its absolute key, ONE AT A TIME, through the
    file system's own [Fs.fs_set].

    INSERTION RATHER THAN CONCATENATION IS THE WHOLE POINT.  [Fs.fs_set]
    puts a key in its sorted place and replaces a duplicate, so the
    result is in the canonical form for EVERY list the declaration
    happens to be — unsorted, with repeats, in any order — and the
    declaration therefore needs no validity clause of its own.  That is
    what makes [State.in_tmp] a true input: every value is one a launch
    could present, and
    [Run.valid_input] excludes none of them ([fs_seed_tmp_valid] is the
    proof).  A later entry wins over an earlier one with the same name,
    which is the only reading a fold can give and costs nothing: the two
    describe the same directory entry. *)
Definition fs_seed_tmp (fs : Fs.Fs) (t : Fs.Fs) : Fs.Fs :=
  fold_left
    (fun acc e =>
       if tmp_nul_free (fst e) then fs_set acc (tmp_key (fst e)) (snd e)
       else acc)
    t fs.

Lemma fs_seed_tmp_nil : forall fs, fs_seed_tmp fs [] = fs.
Proof. reflexivity. Qed.

Lemma tmp_prefix_nul_free : ~ In (Z_to_bv 8 0) tmp_prefix.
Proof.
  unfold tmp_prefix. cbn [In].
  intros [H|[H|[H|[H|[H|H]]]]]; try exact H;
    apply (proj2 (bv_eqb_eq _ _)) in H; vm_compute in H; discriminate.
Qed.

Lemma tmp_key_nul_free : forall name,
  tmp_nul_free name = true -> ~ In (Z_to_bv 8 0) (tmp_key name).
Proof.
  intros name Hn Hin. unfold tmp_key in Hin.
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - exact (tmp_prefix_nul_free Hin).
  - unfold tmp_nul_free in Hn. apply Bool.negb_true_iff in Hn.
    assert (existsb (fun b => bv_eqb b (Z_to_bv 8 0)) name = true) as Hc.
    { apply existsb_exists. exists (Z_to_bv 8 0). split; [exact Hin|].
      apply bv_eqb_eq. reflexivity. }
    rewrite Hc in Hn. discriminate.
Qed.

(** THE CLAUSE ON THE IMAGE EXCLUDES NO /tmp.  Seeding a canonical image
    with ANY declared /tmp leaves it canonical, so [Run.valid_input]'s
    [Fs.valid_fs] clause — which reads the SEEDED image, through
    [in_fs] — is satisfied for every value of [in_tmp] whenever it was
    satisfied by the image alone.  That is the precise sense in which
    the declaration is unconstrained: no /tmp table a launch could
    present is ruled out. *)
Lemma fs_seed_tmp_valid : forall t fs,
  Fs.valid_fs fs -> Fs.valid_fs (fs_seed_tmp fs t).
Proof.
  induction t as [|[name data] t IH]; intros fs Hv; [exact Hv|].
  cbn [fs_seed_tmp fold_left fst snd].
  destruct (tmp_nul_free name) eqn:Hn; [|now apply IH].
  apply IH. destruct Hv as [Hs Hf]. split.
  - now apply fs_set_sorted.
  - apply (fs_set_keys (fun q => ~ In (Z_to_bv 8 0) q));
      [exact Hf | now apply tmp_key_nul_free].
Qed.

(** The seeding's insertion-closure, the shape [Fs.fs_set_keys] has for
    ONE insertion: a property that holds of every key of the image and
    of every /tmp key holds of every key of the seeded image.  The
    NUL-free clause of [fs_seed_tmp_valid] just above is one instance
    (left as it stands, so that proof keeps reading in one piece);
    [seeded_absolute_key_is_tmp] below is the other. *)
Lemma fs_seed_tmp_keys : forall (P : Fs.path -> Prop) t fs,
  Forall (fun pf => P (fst pf)) fs ->
  (forall n, P (tmp_key n)) ->
  Forall (fun pf => P (fst pf)) (fs_seed_tmp fs t).
Proof.
  intros P t. induction t as [|[name data] t IH]; intros fs Hfs Hk; [exact Hfs|].
  cbn [fs_seed_tmp fold_left fst snd].
  destruct (tmp_nul_free name); [|now apply IH].
  apply IH; [|exact Hk]. apply Fs.fs_set_keys; [exact Hfs | apply Hk].
Qed.

(** WHERE AN ABSOLUTE KEY IN A RUN'S FILE SYSTEM CAN COME FROM: the
    seeding, and nothing else.

    Under [Fs.fs_keys_relative] on the image, every key of the seeded
    image is either RELATIVE — it came from the image, and the image's
    keys begin with no "/" — or it is a key the seeding minted, and
    every one of those is [tmp_key n] for the declared name [n], which
    begins with "/tmp/".  The two halves are one disjunction rather than
    two lemmas because that is how the consumers read it: a spec holding
    an absolute path asks "could this be a key?", and the answer is "only
    if it is under /tmp".

    This is the lemma [Run.device_paths_never_seeded] turns into the
    statement that the device arms' image guards cannot fire on a valid
    input. *)
Lemma seeded_absolute_key_is_tmp : forall t fs,
  Fs.fs_keys_relative fs ->
  Forall (fun pf => Fs.key_is_relative (fst pf) \/ exists n, fst pf = tmp_key n)
         (fs_seed_tmp fs t).
Proof.
  intros t fs Hrel.
  apply (fs_seed_tmp_keys (fun q => Fs.key_is_relative q \/ exists n, q = tmp_key n)).
  - eapply Forall_impl; [|exact Hrel]. intros a Ha. now left.
  - intros n. right. now exists n.
Qed.

(** What the CALLER supplies to a run: the argv and envp strings, the
    initial file-system image, the standard-input stream, the user and
    group the process runs as, and the network the program faces.
    [in_stdin] and [in_net] are inputs of the run exactly like the other
    five — colists fixed up front, see [InputStream] and [NetQueue].
    One record rather than an argument each, so that a new process input
    is a new field here and no consumer's arity moves.

    THE ADVERSARIAL PEER IS AN INPUT, not an internal choice, and that
    is forced rather than stylistic.  [Checks.ExecutableSpecs] proves
    [check_syscall_err_iff] against a TOTAL checker, which makes an arm
    that both succeeds and declines at the same [(i, m)] impossible: one
    [Unmodeled] there forbids every [Ok] there.  Environment choice
    therefore has to arrive quantified, and quantifying it universally
    is also the anti-vacuous direction — [Equivalence.strong_equiv]
    ranges over all inputs, so a new field adds a [forall], never an
    [exists].  [Run.valid_input] is the record's validity predicate.

    [in_net] carries no validity clause, and that is a property of the
    REPRESENTATION rather than an omission: [NetStream]'s payload is a
    [byte] and its terminals are nullary, so every value of the type is
    a network a process could really face.

    [in_uid], [in_gid], [in_groups] and [in_nofile] are the ENVIRONMENT's
    choice in the same sense the ASLR'd stack pointer and program break are
    ([Run.valid_sp], [Run.valid_brk]): the model does not know which
    user launched the process, so it quantifies over every user it could
    have been rather than picking one.  A process launched by uid 1001 and the same
    process launched by root are both runs of this model, and a program
    whose observable behavior depends on which is which can only be
    proved equivalent to a target that depends on it the same way.
    Unlike the sp and the break, which are quantified INDEPENDENTLY per
    binary, the process input is SHARED between source and target
    ([Equivalence.strong_universal_T]), so the two binaries always agree
    on who they are.

    The effective and saved ids are NOT separate inputs: [init_model]
    derives them, because [execve] of an ordinary binary leaves the real
    ids alone and sets the saved ids from the effective ones.  Deriving
    rather than carrying is what confines the model to launches whose
    effective ids equal their real ones — such a launch cannot be
    EXPRESSED, there being no field to express it in.  This is not
    [Run.valid_creds]'s doing; that predicate only bounds the two ids to
    32 bits and excludes [(uid_t)-1].  What is excluded is a secure-exec
    (a set-user-id binary, or one carrying file capabilities), which
    sends libc down its secure-exec path, whose syscalls are outside
    [Specs.modeled_sysnos].  See [StackLayout.auxv_entries], which
    relies on the same restriction.

    [in_uid] REACHES THE PROCESS TWICE, and that is the point: [init_model]
    below copies it into [Creds], which the id readers project, and
    [Run.init_machine_state] hands it to [StackLayout.auxv_entries],
    which writes it into AT_UID and AT_EUID on the initial stack.  One
    field, so the two answers cannot disagree — as they cannot on Linux,
    where [create_elf_tables] and [SYSCALL_DEFINE0(getuid)] both munge
    [current_cred()->uid].  [in_gid] reaches only the credentials: this
    auxv carries no AT_GID or AT_EGID entry at all, so there is no
    second group answer for it to contradict.

    [in_groups] is an input for the same reason, and it is an input
    rather than a constant because the kernel never resets it: [execve]
    builds the new credentials with [prepare_exec_creds], which adjusts
    the keyrings and the saved/fs ids and leaves [group_info] alone, and
    the [prepare_creds] underneath it carries the SAME [struct
    group_info] over by [memcpy] plus [get_group_info] (kernel/cred.c,
    reached from fs/exec.c's [bprm] credential setup; v6.10..v6.18).  So
    the list a process starts with is whatever its parent had, and no
    syscall this model admits can change it — [setgroups] (159) is
    -EPERM unprivileged and declined privileged.  It is therefore
    CONSTANT over a modeled run, which is why [Creds] can hold it and
    nothing has to write it back.

    [in_nofile] is an input for the same reason, and CONSTANT for a
    reason worth stating precisely, because an exec really can change
    this limit: the LSM [bprm_committing_creds] hooks clamp every
    resource including NOFILE (security/selinux/hooks.c,
    [selinux_bprm_committing_creds]; security/apparmor/resource.c; Linux
    v6.18.46, commit 1f99e9ab748f).  What makes the field constant is
    not that nothing writes it but WHEN the writers run — at exec, at
    boot, on a core dump — and this model begins AT execve and reaches
    none of them afterwards.  So the limit a run starts with is the one
    it ends with, and where it came from is the environment's business.
    [limst_nofile] carries the rest of the argument, over the syscalls
    this model does admit.  Unlike [in_groups] it DOES carry a [Run.valid_input]
    clause, and the difference is which end bounds it: an over-long group
    list is refused where it is read, while the descriptor limit is
    ANSWERED from, so an unreachable value would be answered rather than
    declined.  [Run.valid_nofile] carries that bound and its kernel
    argument.

    The consumers — [init_model] here, [Run.init_config] and [Run.run] —
    take the record whole and read the fields with the record
    PROJECTIONS rather than by matching on it.  A projection reduces
    whatever the record is, so [m_fs (init_model _ _ _ _ inp) = in_fs inp]
    holds by [reflexivity] for a variable [inp], where a match would be
    stuck, and a literal [mkProcInput] still iota-reduces through the
    projections to its fields. *)
Record ProcInput := mkProcInput_full {
  in_argv  : list (list byte);
  in_envp  : list (list byte);
  in_image_fs : Fs.Fs
    (* the file-system image the run is launched over, WITHOUT the
       run's private /tmp.  Read it through [in_fs] below, which is
       what every consumer means by "the file system the run starts
       with"; this projection exists so that the image and the
       declared /tmp can be supplied separately *);
  in_stdin : InputStream;
  in_uid   : word;   (* the real user id the process is launched with *)
  in_gid   : word;   (* the real group id the process is launched with *)
  in_groups : list word
    (* the supplementary group list the process is launched with, in the
       kernel's stored order — see [Creds]'s [cr_groups], which
       [init_model] copies this into *);
  in_net   : NetQueue
    (* the connections the environment offers, and what each peer says
       once accepted — see [NetQueue] and [NetStream] *);
  in_nofile : word
    (* the SOFT RLIMIT_NOFILE the process is launched with, an
       [unsigned long] — see [LimState]'s [limst_nofile], which
       [init_model] copies this into, and [Sys.Fs.File.dup3_spec], its
       one reader.  [Run.valid_nofile] bounds it *);
  in_sigmask : word
    (* the signals BLOCKED at the moment the process starts, as riscv64's
       one-word [sigset_t].  An input for the same reason [in_uid] is:
       execve does not reset [task_struct.blocked] — [fs/exec.c] never
       names the field and [begin_new_exec] resets DISPOSITIONS only,
       via [flush_signal_handlers] (Linux v6.18.46, commit
       1f99e9ab748f) — so the starting mask is whatever launched the
       process, and the model cannot derive it.  [Run.valid_input]
       constrains it; see [valid_sigmask] there for what and why *);
  in_hwcap : word
    (* the AT_HWCAP word the auxv publishes: which single-letter ISA
       extensions the HART this process runs on implements.  An input
       rather than a constant because the model has no term for the
       machine — the same reason [riscv_hwprobe] stays outside
       [Specs.modeled_sysnos].  [Run.valid_hwcap] narrows it to the two
       masks a hart that can run this model's instructions may publish;
       [StackLayout.auxv_entries] is its one reader, and the AT_HWCAP
       bullet there carries the kernel argument for the pair *)
;
  in_abort_terminal : bool
    (* THE TASK'S DECLARATION, and the one field of this record that is
       not a fact about the environment: whether the model covers the
       abort path -- [tkill] (130), [tgkill] (131) and the fatal SIGABRT
       they can leave pending -- or declines it.
       [Run.valid_input] pins it to [false]; a task that
       wants the other stance quantifies over [Run.valid_input_abort]
       instead, and a statement that pins neither asserts both.

       IT IS HERE RATHER THAN BESIDE [Run.SpuriousCfg] because it decides
       what a SPEC admits rather than which of a spec's outcomes survive,
       and a spec's only channel to the run's parameters is the model
       ([procst_abort_terminal], which [init_model] copies this into and
       nothing else writes).  What it buys by being a field of the input
       is that it lands in the statement's quantifier for free, which is
       where a reader has to be able to see it *);
  in_va_size : VaSize
    (* THE TASK'S DECLARATION of the kernel's user address-space size --
       which page-table depth the machine this process runs on booted
       with -- and, like the credentials, a fact about the environment
       the model cannot derive: nothing a trace reveals says whether the
       kernel was Sv39, Sv48 or Sv57, and the answer changes where the
       stack is and which addresses [access_ok] admits.  [Run.valid_input]
       pins it to [Sv48], the size every statement in this tree is
       written against; the per-size variants beside it pin the others,
       and [Run.valid_entry] reads it to choose the window.  The
       paragraph above [VaSize] says what the declaration decides today
       and what it does not.

       It is NOT copied into the model: no spec arm reads it (they read
       [TASK_SIZE]), and [Equivalence.strong_equiv_va] is where a
       statement under a size the arms do not implement is refused.
       The day an arm reads the declared size, this field is seeded into
       the model the way [in_nofile] is, and that note is the one to
       update *);
  in_urandom : InputStream
    (* THE ENVIRONMENT'S DECLARATION of the bytes the random device
       hands out, in order: what every read of /dev/urandom
       ([Fs.Open.openat_urandom_spec], [State.FdUrandom]) delivers,
       front first, across every descriptor the run opens on it.  Like
       [in_va_size] it is a fact about the environment the model cannot
       derive -- nothing a trace reveals says which bytes the kernel's
       generator produced -- and like [in_stdin] it is an INPUT of the
       run rather than an internal choice: the stream is ARBITRARY BUT
       FIXED, a parameter of the execution exactly as argv and envp
       are, so a program's behaviour is a function of it and every
       equivalence is proved for every stream, with the SAME stream
       seen by the source and the target of a pair.  It is not
       nondeterministic in the model, and it is not [getrandom]'s
       source: [Drivers.Char.Random.getrandom_spec] keeps its own
       [choose].  [Run.valid_urandom] is the ONE clause on it, and it
       says only that the declared stream never ends: a short read from
       this device is not a thing Linux does, so a finite declaration
       describes no device at all.  It is not the clause [in_stdin]
       does without -- a pipe that ends is a real pipe -- and it says
       nothing whatever about WHICH bytes come out.  [init_model] seeds
       [iost_urandom] from it, and the read arm consumes that copy the
       way stdin's arm consumes [iost_stdin]. *);
  in_tmp   : Fs.Fs
    (* THE ENVIRONMENT'S DECLARATION of the run's PRIVATE /tmp at
       launch: the files it already contains, keyed by the ONE
       component of their name (no "/tmp/" prefix in the key).  Like
       [in_urandom] it is a fact about the environment the model cannot
       derive, and like it the value is ARBITRARY BUT FIXED -- a
       parameter of the execution exactly as argv and envp are, the
       SAME directory seen by the source and the target of a pair, so
       every equivalence is proved for every declared /tmp.  It is not
       nondeterministic in the model.

       THE PREMISE IT CARRIES is that /tmp is a distinct, writable
       directory PRIVATE to this run, which is what makes this table
       the whole truth about it: what the run holds there is this
       declaration, plus what [Fs.Open.create_wronly] created, minus
       what [Fs.Namei.unlinkat_spec] removed, and nothing else can put
       a file there or take one away.

       [Run.valid_input] has NO clause naming it: [fs_seed_tmp] seeds
       any list into the canonical form, so every value is one a launch
       could present ([fs_seed_tmp_valid]). *)
}.

(** THE POSITIONAL-LITERAL FORM: every field except the two ENVIRONMENT
    fields at the end of the record ([in_urandom], [in_tmp]).

    The record's own constructor is [mkProcInput_full] and takes every
    field.  This takes the first thirteen, in that order,
    and fills the last two with THE DEFAULT RANDOM STREAM and
    THE EMPTY /tmp: [default_urandom], which is zero bytes forever, and
    a private /tmp that starts empty.  So a literal written through this
    name denotes an input in an environment
    that holds no file of its own.

    THE RANDOM DEFAULT IS NOT [IEof]: under
    [Run.valid_urandom] every valid input declares an endless stream, so
    a fixture built here with [IEof] would fail its own validity pin.

    WHY IT EXISTS: consumers of this specification hold positional
    [mkProcInput] literals in numbers, and a field added to the middle
    of the record silently changes what such a literal means while a
    field added to the end merely breaks it.  Keeping the thirteen-place
    form under this name, and putting every new environment field at
    the END, is what makes an added field a compile error there rather
    than a re-spelling of every literal.  A NEW literal that wants to
    set either field uses [mkProcInput_full] or the record-brace form;
    this one cannot express them, which is the point.

    It is a plain (transparent) [Definition], so it reduces wherever the
    constructor would — but a [cbn] or [simpl] with an explicit
    constant list has to name it to see through it. *)
Definition mkProcInput
    (argv envp : list (list byte)) (image_fs : Fs.Fs) (stdin : InputStream)
    (uid gid : word) (groups : list word) (net : NetQueue)
    (nofile sigmask hwcap : word) (abort_terminal : bool)
    (va_size : VaSize) : ProcInput :=
  mkProcInput_full argv envp image_fs stdin uid gid groups net
    nofile sigmask hwcap abort_terminal va_size default_urandom [].

(** THE FILE SYSTEM THE RUN STARTS WITH: the image, with the run's
    declared private /tmp seeded into it under absolute keys.

    This is what every consumer means by [in_fs], and it is
    what [init_model] installs, so [m_fs (init_model _ _ _ _ _
    inp) = in_fs inp] holds by [reflexivity].  The record carries the
    image and the
    declared /tmp as two fields, and this function is the one place
    that puts them together.

    IT IS A FUNCTION RATHER THAN A PROJECTION, which the record's header
    note above asks about: a function of two projections reduces exactly
    as a projection does for a variable [inp], so the reflexivity
    property the note is written for is unaffected.  An input whose
    [in_tmp] is the empty declaration gives back the image itself
    ([fs_seed_tmp_nil]), by computation, which is why every literal
    built with [mkProcInput] reduces to its image. *)
Definition in_fs (inp : ProcInput) : Fs.Fs :=
  fs_seed_tmp (in_image_fs inp) (in_tmp inp).

(* =========================================================================
   Initial model: fds 0/1/2 bound to the three standard channels;
   [reserved] is the address space the kernel used at [execve] (the
   page-rounded LOAD segments, built by [Run.segments_reserved]), which
   the allocator may never grant; [brk0] is the ASLR-placed initial
   program break ([Run.valid_brk] — quantified per binary like the
   initial SP, see [Run.mi_init_brk]); [mbase] is the layout-placed
   [mm->mmap_base] ([Run.valid_mmap_base] — quantified the same way,
   see [Run.mi_mmap_base] and the [vm_mmap_base] field note); [sp] is
   the initial stack pointer ([Run.valid_sp], see [Run.mi_init_sp] and
   the [vm_init_sp] field note), which [alloc_top] bounds every grant
   by; the file
   system, standard
   input and the random device's stream start as the [in_fs], [in_stdin]
   and [in_urandom] of the caller-supplied
   [inp], read through the record projections (see [ProcInput]); [lim]
   is the run's backed anonymous-memory budget in bytes ([vm_limit] — see the
   field's note and its companion constants
   [source_alloc_limit]/[target_alloc_limit]).

   The six CREDENTIAL ids are built from the two the input carries.
   [execve] of an ordinary binary — one that is neither set-user-id nor
   set-group-id and carries no file capabilities — leaves the real ids
   untouched, keeps the effective ids of the calling process, and then
   sets the saved set-ids and the filesystem ids from the effective ones
   (Linux v6.18.46, commit 1f99e9ab748f, security/commoncap.c,
   [cap_bprm_creds_from_file], whose
   [new->suid = new->fsuid = new->euid;] and
   [new->sgid = new->fsgid = new->egid;] run on every exec, setuid or
   not.  Those two lines are byte-identical from v6.10 through v6.18;
   the function around them is not, because v6.17 rewrote the test that
   marks an exec privilege-elevated, but every term it added compares an
   effective id with a real one, and a launch whose two differ is not an
   input [ProcInput] can express.  kernel/cred.c, [prepare_exec_creds],
   does the same earlier).
   Because [ProcInput] carries no effective id, all three collapse to
   the one value the input supplies, and a secure-exec — whose
   effective id differs — is not an input this model can state.
   ========================================================================= *)

Definition init_model (reserved : list (word * word)) (brk0 mbase sp : word)
    (lim : Z) (inp : ProcInput) : Model :=
  with_abort_terminal (in_abort_terminal inp)
  (with_sigmask (in_sigmask inp)
  (with_nofile (in_nofile inp)
   (with_net (in_net inp)
   (with_urandom (in_urandom inp)
   (with_creds
    (mkCreds (in_uid inp) (in_uid inp) (in_uid inp)
             (in_gid inp) (in_gid inp) (in_gid inp) (in_groups inp))
    (mkModel
       [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
         (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
         (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ]
       (mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp)
       (in_stdin inp)
       (in_fs inp)
       None
       None
       None)))))).

(** The base case of the nonemptiness invariant: a run starts with NO
    protected range at all.  Every reachable [vm_noaccess] is therefore
    reached from [[]] by the writers in [Mm/Mmap.v] and
    [Mm/Mprotect.v], each of which is shown there to preserve
    [vm_noaccess_entries_nonzero]. *)
Lemma init_model_noaccess_nonzero :
  forall reserved brk0 mbase sp lim inp,
    vm_noaccess_entries_nonzero
      (m_vmmaps (init_model reserved brk0 mbase sp lim inp)).
Proof. intros. apply entries_nonzero_nil. Qed.

(** * The setter/accessor interactions, as REWRITES rather than reductions.

    Reducing through these with explicit constant lists
    ([cbn [with_fds m_fds ...]]) does not work on the nested [Model]:
    such a list has to name every
    constant on the way from [m_fds (with_fds x m)] down to [x], and
    naming them ALSO unfolds a bare [m_fs model] --
    which later steps match on literally, and then cannot find.

    So the accessors and setters are opaque to reduction (below) and these
    lemmas are how a proof gets through them.  Every one is [reflexivity]:
    the nesting is definitional, and this only decides which shapes a proof
    is allowed to see.  Registered in the [model] database, so a caller
    writes [autorewrite with model] and names no field. *)

Lemma m_fds_with_fds : forall (v : list (word * FdEntry)) (m : Model),
  m_fds (with_fds v m) = v.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fds_with_fds : model.

Lemma m_fds_with_vmmaps : forall (v : VmMaps) (m : Model),
  m_fds (with_vmmaps v m) = m_fds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fds_with_vmmaps : model.

Lemma m_fds_with_stdin : forall (v : InputStream) (m : Model),
  m_fds (with_stdin v m) = m_fds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fds_with_stdin : model.

Lemma m_fds_with_urandom : forall (v : InputStream) (m : Model),
  m_fds (with_urandom v m) = m_fds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fds_with_urandom : model.

Lemma m_fds_with_fs : forall (v : Fs.Fs) (m : Model),
  m_fds (with_fs v m) = m_fds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fds_with_fs : model.

Lemma m_fds_with_halted : forall (v : word) (m : Model),
  m_fds (with_halted v m) = m_fds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fds_with_halted : model.

Lemma m_fds_with_tid : forall (v : word) (m : Model),
  m_fds (with_tid v m) = m_fds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fds_with_tid : model.

Lemma m_fds_with_rlimit_core : forall (v : list byte) (m : Model),
  m_fds (with_rlimit_core v m) = m_fds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fds_with_rlimit_core : model.

Lemma m_fds_with_clock : forall (v : word) (m : Model),
  m_fds (with_clock v m) = m_fds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fds_with_clock : model.

Lemma m_fds_with_setsid_succeeded : forall (m : Model),
  m_fds (with_setsid_succeeded m) = m_fds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fds_with_setsid_succeeded : model.

Lemma m_fds_with_pipes : forall (v : list (word * PipeBuf)) (m : Model),
  m_fds (with_pipes v m) = m_fds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fds_with_pipes : model.

Lemma m_vmmaps_with_fds : forall (v : list (word * FdEntry)) (m : Model),
  m_vmmaps (with_fds v m) = m_vmmaps m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vmmaps_with_fds : model.

Lemma m_vmmaps_with_vmmaps : forall (v : VmMaps) (m : Model),
  m_vmmaps (with_vmmaps v m) = v.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vmmaps_with_vmmaps : model.

Lemma m_vmmaps_with_stdin : forall (v : InputStream) (m : Model),
  m_vmmaps (with_stdin v m) = m_vmmaps m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vmmaps_with_stdin : model.

Lemma m_vmmaps_with_urandom : forall (v : InputStream) (m : Model),
  m_vmmaps (with_urandom v m) = m_vmmaps m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vmmaps_with_urandom : model.

Lemma m_vmmaps_with_fs : forall (v : Fs.Fs) (m : Model),
  m_vmmaps (with_fs v m) = m_vmmaps m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vmmaps_with_fs : model.

Lemma m_vmmaps_with_halted : forall (v : word) (m : Model),
  m_vmmaps (with_halted v m) = m_vmmaps m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vmmaps_with_halted : model.

Lemma m_vmmaps_with_tid : forall (v : word) (m : Model),
  m_vmmaps (with_tid v m) = m_vmmaps m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vmmaps_with_tid : model.

Lemma m_vmmaps_with_rlimit_core : forall (v : list byte) (m : Model),
  m_vmmaps (with_rlimit_core v m) = m_vmmaps m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vmmaps_with_rlimit_core : model.

Lemma m_vmmaps_with_clock : forall (v : word) (m : Model),
  m_vmmaps (with_clock v m) = m_vmmaps m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vmmaps_with_clock : model.

Lemma m_vmmaps_with_setsid_succeeded : forall (m : Model),
  m_vmmaps (with_setsid_succeeded m) = m_vmmaps m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vmmaps_with_setsid_succeeded : model.

Lemma m_vmmaps_with_pipes : forall (v : list (word * PipeBuf)) (m : Model),
  m_vmmaps (with_pipes v m) = m_vmmaps m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vmmaps_with_pipes : model.

Lemma m_stdin_with_fds : forall (v : list (word * FdEntry)) (m : Model),
  m_stdin (with_fds v m) = m_stdin m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_stdin_with_fds : model.

Lemma m_urandom_with_fds : forall (v : list (word * FdEntry)) (m : Model),
  m_urandom (with_fds v m) = m_urandom m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_urandom_with_fds : model.

Lemma m_stdin_with_vmmaps : forall (v : VmMaps) (m : Model),
  m_stdin (with_vmmaps v m) = m_stdin m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_stdin_with_vmmaps : model.

Lemma m_urandom_with_vmmaps : forall (v : VmMaps) (m : Model),
  m_urandom (with_vmmaps v m) = m_urandom m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_urandom_with_vmmaps : model.

Lemma m_stdin_with_stdin : forall (v : InputStream) (m : Model),
  m_stdin (with_stdin v m) = v.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_stdin_with_stdin : model.

Lemma m_urandom_with_stdin : forall (v : InputStream) (m : Model),
  m_urandom (with_stdin v m) = m_urandom m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_urandom_with_stdin : model.

Lemma m_stdin_with_urandom : forall (v : InputStream) (m : Model),
  m_stdin (with_urandom v m) = m_stdin m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_stdin_with_urandom : model.

Lemma m_urandom_with_urandom : forall (v : InputStream) (m : Model),
  m_urandom (with_urandom v m) = v.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_urandom_with_urandom : model.

Lemma m_stdin_with_fs : forall (v : Fs.Fs) (m : Model),
  m_stdin (with_fs v m) = m_stdin m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_stdin_with_fs : model.

Lemma m_urandom_with_fs : forall (v : Fs.Fs) (m : Model),
  m_urandom (with_fs v m) = m_urandom m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_urandom_with_fs : model.

Lemma m_stdin_with_halted : forall (v : word) (m : Model),
  m_stdin (with_halted v m) = m_stdin m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_stdin_with_halted : model.

Lemma m_urandom_with_halted : forall (v : word) (m : Model),
  m_urandom (with_halted v m) = m_urandom m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_urandom_with_halted : model.

Lemma m_stdin_with_tid : forall (v : word) (m : Model),
  m_stdin (with_tid v m) = m_stdin m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_stdin_with_tid : model.

Lemma m_urandom_with_tid : forall (v : word) (m : Model),
  m_urandom (with_tid v m) = m_urandom m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_urandom_with_tid : model.

Lemma m_stdin_with_rlimit_core : forall (v : list byte) (m : Model),
  m_stdin (with_rlimit_core v m) = m_stdin m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_stdin_with_rlimit_core : model.

Lemma m_urandom_with_rlimit_core : forall (v : list byte) (m : Model),
  m_urandom (with_rlimit_core v m) = m_urandom m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_urandom_with_rlimit_core : model.

Lemma m_stdin_with_clock : forall (v : word) (m : Model),
  m_stdin (with_clock v m) = m_stdin m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_stdin_with_clock : model.

Lemma m_urandom_with_clock : forall (v : word) (m : Model),
  m_urandom (with_clock v m) = m_urandom m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_urandom_with_clock : model.

Lemma m_stdin_with_setsid_succeeded : forall (m : Model),
  m_stdin (with_setsid_succeeded m) = m_stdin m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_stdin_with_setsid_succeeded : model.

Lemma m_urandom_with_setsid_succeeded : forall (m : Model),
  m_urandom (with_setsid_succeeded m) = m_urandom m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_urandom_with_setsid_succeeded : model.

Lemma m_stdin_with_pipes : forall (v : list (word * PipeBuf)) (m : Model),
  m_stdin (with_pipes v m) = m_stdin m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_stdin_with_pipes : model.

Lemma m_urandom_with_pipes : forall (v : list (word * PipeBuf)) (m : Model),
  m_urandom (with_pipes v m) = m_urandom m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_urandom_with_pipes : model.

Lemma m_fs_with_fds : forall (v : list (word * FdEntry)) (m : Model),
  m_fs (with_fds v m) = m_fs m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fs_with_fds : model.

Lemma m_fs_with_vmmaps : forall (v : VmMaps) (m : Model),
  m_fs (with_vmmaps v m) = m_fs m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fs_with_vmmaps : model.

Lemma m_fs_with_stdin : forall (v : InputStream) (m : Model),
  m_fs (with_stdin v m) = m_fs m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fs_with_stdin : model.

Lemma m_fs_with_urandom : forall (v : InputStream) (m : Model),
  m_fs (with_urandom v m) = m_fs m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fs_with_urandom : model.

Lemma m_fs_with_fs : forall (v : Fs.Fs) (m : Model),
  m_fs (with_fs v m) = v.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fs_with_fs : model.

Lemma m_fs_with_halted : forall (v : word) (m : Model),
  m_fs (with_halted v m) = m_fs m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fs_with_halted : model.

Lemma m_fs_with_tid : forall (v : word) (m : Model),
  m_fs (with_tid v m) = m_fs m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fs_with_tid : model.

Lemma m_fs_with_rlimit_core : forall (v : list byte) (m : Model),
  m_fs (with_rlimit_core v m) = m_fs m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fs_with_rlimit_core : model.

Lemma m_fs_with_clock : forall (v : word) (m : Model),
  m_fs (with_clock v m) = m_fs m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fs_with_clock : model.

Lemma m_fs_with_setsid_succeeded : forall (m : Model),
  m_fs (with_setsid_succeeded m) = m_fs m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fs_with_setsid_succeeded : model.

Lemma m_fs_with_pipes : forall (v : list (word * PipeBuf)) (m : Model),
  m_fs (with_pipes v m) = m_fs m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fs_with_pipes : model.

Lemma m_halted_with_fds : forall (v : list (word * FdEntry)) (m : Model),
  m_halted (with_fds v m) = m_halted m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_halted_with_fds : model.

Lemma m_halted_with_vmmaps : forall (v : VmMaps) (m : Model),
  m_halted (with_vmmaps v m) = m_halted m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_halted_with_vmmaps : model.

Lemma m_halted_with_stdin : forall (v : InputStream) (m : Model),
  m_halted (with_stdin v m) = m_halted m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_halted_with_stdin : model.

Lemma m_halted_with_urandom : forall (v : InputStream) (m : Model),
  m_halted (with_urandom v m) = m_halted m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_halted_with_urandom : model.

Lemma m_halted_with_fs : forall (v : Fs.Fs) (m : Model),
  m_halted (with_fs v m) = m_halted m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_halted_with_fs : model.

Lemma m_halted_with_halted : forall (v : word) (m : Model),
  m_halted (with_halted v m) = Some v.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_halted_with_halted : model.

Lemma m_halted_with_tid : forall (v : word) (m : Model),
  m_halted (with_tid v m) = m_halted m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_halted_with_tid : model.

Lemma m_halted_with_rlimit_core : forall (v : list byte) (m : Model),
  m_halted (with_rlimit_core v m) = m_halted m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_halted_with_rlimit_core : model.

Lemma m_halted_with_clock : forall (v : word) (m : Model),
  m_halted (with_clock v m) = m_halted m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_halted_with_clock : model.

Lemma m_halted_with_setsid_succeeded : forall (m : Model),
  m_halted (with_setsid_succeeded m) = m_halted m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_halted_with_setsid_succeeded : model.

Lemma m_halted_with_pipes : forall (v : list (word * PipeBuf)) (m : Model),
  m_halted (with_pipes v m) = m_halted m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_halted_with_pipes : model.

Lemma m_tid_with_fds : forall (v : list (word * FdEntry)) (m : Model),
  m_tid (with_fds v m) = m_tid m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_tid_with_fds : model.

Lemma m_tid_with_vmmaps : forall (v : VmMaps) (m : Model),
  m_tid (with_vmmaps v m) = m_tid m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_tid_with_vmmaps : model.

Lemma m_tid_with_stdin : forall (v : InputStream) (m : Model),
  m_tid (with_stdin v m) = m_tid m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_tid_with_stdin : model.

Lemma m_tid_with_urandom : forall (v : InputStream) (m : Model),
  m_tid (with_urandom v m) = m_tid m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_tid_with_urandom : model.

Lemma m_tid_with_fs : forall (v : Fs.Fs) (m : Model),
  m_tid (with_fs v m) = m_tid m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_tid_with_fs : model.

Lemma m_tid_with_halted : forall (v : word) (m : Model),
  m_tid (with_halted v m) = m_tid m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_tid_with_halted : model.

Lemma m_tid_with_tid : forall (v : word) (m : Model),
  m_tid (with_tid v m) = Some v.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_tid_with_tid : model.

Lemma m_tid_with_rlimit_core : forall (v : list byte) (m : Model),
  m_tid (with_rlimit_core v m) = m_tid m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_tid_with_rlimit_core : model.

Lemma m_tid_with_clock : forall (v : word) (m : Model),
  m_tid (with_clock v m) = m_tid m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_tid_with_clock : model.

Lemma m_tid_with_setsid_succeeded : forall (m : Model),
  m_tid (with_setsid_succeeded m) = m_tid m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_tid_with_setsid_succeeded : model.

Lemma m_tid_with_pipes : forall (v : list (word * PipeBuf)) (m : Model),
  m_tid (with_pipes v m) = m_tid m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_tid_with_pipes : model.

Lemma m_rlimit_core_with_fds : forall (v : list (word * FdEntry)) (m : Model),
  m_rlimit_core (with_fds v m) = m_rlimit_core m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_rlimit_core_with_fds : model.

Lemma m_rlimit_core_with_vmmaps : forall (v : VmMaps) (m : Model),
  m_rlimit_core (with_vmmaps v m) = m_rlimit_core m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_rlimit_core_with_vmmaps : model.

Lemma m_rlimit_core_with_stdin : forall (v : InputStream) (m : Model),
  m_rlimit_core (with_stdin v m) = m_rlimit_core m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_rlimit_core_with_stdin : model.

Lemma m_rlimit_core_with_urandom : forall (v : InputStream) (m : Model),
  m_rlimit_core (with_urandom v m) = m_rlimit_core m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_rlimit_core_with_urandom : model.

Lemma m_rlimit_core_with_fs : forall (v : Fs.Fs) (m : Model),
  m_rlimit_core (with_fs v m) = m_rlimit_core m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_rlimit_core_with_fs : model.

Lemma m_rlimit_core_with_halted : forall (v : word) (m : Model),
  m_rlimit_core (with_halted v m) = m_rlimit_core m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_rlimit_core_with_halted : model.

Lemma m_rlimit_core_with_tid : forall (v : word) (m : Model),
  m_rlimit_core (with_tid v m) = m_rlimit_core m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_rlimit_core_with_tid : model.

Lemma m_rlimit_core_with_rlimit_core : forall (v : list byte) (m : Model),
  m_rlimit_core (with_rlimit_core v m) = Some v.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_rlimit_core_with_rlimit_core : model.

Lemma m_rlimit_core_with_clock : forall (v : word) (m : Model),
  m_rlimit_core (with_clock v m) = m_rlimit_core m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_rlimit_core_with_clock : model.

Lemma m_clock_with_fds : forall (v : list (word * FdEntry)) (m : Model),
  m_clock (with_fds v m) = m_clock m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_clock_with_fds : model.

Lemma m_clock_with_vmmaps : forall (v : VmMaps) (m : Model),
  m_clock (with_vmmaps v m) = m_clock m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_clock_with_vmmaps : model.

Lemma m_clock_with_stdin : forall (v : InputStream) (m : Model),
  m_clock (with_stdin v m) = m_clock m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_clock_with_stdin : model.

Lemma m_clock_with_urandom : forall (v : InputStream) (m : Model),
  m_clock (with_urandom v m) = m_clock m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_clock_with_urandom : model.

Lemma m_clock_with_fs : forall (v : Fs.Fs) (m : Model),
  m_clock (with_fs v m) = m_clock m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_clock_with_fs : model.

Lemma m_clock_with_halted : forall (v : word) (m : Model),
  m_clock (with_halted v m) = m_clock m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_clock_with_halted : model.

Lemma m_clock_with_tid : forall (v : word) (m : Model),
  m_clock (with_tid v m) = m_clock m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_clock_with_tid : model.

Lemma m_clock_with_rlimit_core : forall (v : list byte) (m : Model),
  m_clock (with_rlimit_core v m) = m_clock m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_clock_with_rlimit_core : model.

Lemma m_clock_with_setsid_succeeded : forall (m : Model),
  m_clock (with_setsid_succeeded m) = m_clock m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_clock_with_setsid_succeeded : model.

Lemma m_clock_with_clock : forall (v : word) (m : Model),
  m_clock (with_clock v m) = v.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_clock_with_clock : model.

Lemma m_creds_with_fds : forall (v : list (word * FdEntry)) (m : Model),
  m_creds (with_fds v m) = m_creds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_creds_with_fds : model.

Lemma m_creds_with_vmmaps : forall (v : VmMaps) (m : Model),
  m_creds (with_vmmaps v m) = m_creds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_creds_with_vmmaps : model.

Lemma m_creds_with_stdin : forall (v : InputStream) (m : Model),
  m_creds (with_stdin v m) = m_creds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_creds_with_stdin : model.

Lemma m_creds_with_urandom : forall (v : InputStream) (m : Model),
  m_creds (with_urandom v m) = m_creds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_creds_with_urandom : model.

Lemma m_creds_with_fs : forall (v : Fs.Fs) (m : Model),
  m_creds (with_fs v m) = m_creds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_creds_with_fs : model.

Lemma m_creds_with_halted : forall (v : word) (m : Model),
  m_creds (with_halted v m) = m_creds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_creds_with_halted : model.

Lemma m_creds_with_tid : forall (v : word) (m : Model),
  m_creds (with_tid v m) = m_creds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_creds_with_tid : model.

Lemma m_creds_with_rlimit_core : forall (v : list byte) (m : Model),
  m_creds (with_rlimit_core v m) = m_creds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_creds_with_rlimit_core : model.

Lemma m_creds_with_clock : forall (v : word) (m : Model),
  m_creds (with_clock v m) = m_creds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_creds_with_clock : model.

Lemma m_creds_with_creds : forall (v : Creds) (m : Model),
  m_creds (with_creds v m) = v.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_creds_with_creds : model.

Lemma m_fds_with_creds : forall (v : Creds) (m : Model),
  m_fds (with_creds v m) = m_fds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fds_with_creds : model.

Lemma m_vmmaps_with_creds : forall (v : Creds) (m : Model),
  m_vmmaps (with_creds v m) = m_vmmaps m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vmmaps_with_creds : model.

Lemma m_stdin_with_creds : forall (v : Creds) (m : Model),
  m_stdin (with_creds v m) = m_stdin m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_stdin_with_creds : model.

Lemma m_urandom_with_creds : forall (v : Creds) (m : Model),
  m_urandom (with_creds v m) = m_urandom m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_urandom_with_creds : model.

Lemma m_fs_with_creds : forall (v : Creds) (m : Model),
  m_fs (with_creds v m) = m_fs m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fs_with_creds : model.

Lemma m_halted_with_creds : forall (v : Creds) (m : Model),
  m_halted (with_creds v m) = m_halted m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_halted_with_creds : model.

Lemma m_tid_with_creds : forall (v : Creds) (m : Model),
  m_tid (with_creds v m) = m_tid m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_tid_with_creds : model.

Lemma m_rlimit_core_with_creds : forall (v : Creds) (m : Model),
  m_rlimit_core (with_creds v m) = m_rlimit_core m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_rlimit_core_with_creds : model.

Lemma m_clock_with_creds : forall (v : Creds) (m : Model),
  m_clock (with_creds v m) = m_clock m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_clock_with_creds : model.

Lemma m_net_with_fds : forall (v : list (word * FdEntry)) (m : Model),
  m_net (with_fds v m) = m_net m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_net_with_fds : model.

Lemma m_net_with_vmmaps : forall (v : VmMaps) (m : Model),
  m_net (with_vmmaps v m) = m_net m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_net_with_vmmaps : model.

Lemma m_net_with_stdin : forall (v : InputStream) (m : Model),
  m_net (with_stdin v m) = m_net m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_net_with_stdin : model.

Lemma m_net_with_urandom : forall (v : InputStream) (m : Model),
  m_net (with_urandom v m) = m_net m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_net_with_urandom : model.

Lemma m_net_with_fs : forall (v : Fs.Fs) (m : Model),
  m_net (with_fs v m) = m_net m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_net_with_fs : model.

Lemma m_net_with_halted : forall (v : word) (m : Model),
  m_net (with_halted v m) = m_net m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_net_with_halted : model.

Lemma m_net_with_tid : forall (v : word) (m : Model),
  m_net (with_tid v m) = m_net m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_net_with_tid : model.

Lemma m_net_with_rlimit_core : forall (v : list byte) (m : Model),
  m_net (with_rlimit_core v m) = m_net m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_net_with_rlimit_core : model.

Lemma m_net_with_clock : forall (v : word) (m : Model),
  m_net (with_clock v m) = m_net m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_net_with_clock : model.

Lemma m_net_with_creds : forall (v : Creds) (m : Model),
  m_net (with_creds v m) = m_net m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_net_with_creds : model.

Lemma m_net_with_net : forall (v : NetQueue) (m : Model),
  m_net (with_net v m) = v.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_net_with_net : model.

Lemma m_conn_ix_with_fds : forall (v : list (word * FdEntry)) (m : Model),
  m_conn_ix (with_fds v m) = m_conn_ix m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_conn_ix_with_fds : model.

Lemma m_conn_ix_with_vmmaps : forall (v : VmMaps) (m : Model),
  m_conn_ix (with_vmmaps v m) = m_conn_ix m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_conn_ix_with_vmmaps : model.

Lemma m_conn_ix_with_stdin : forall (v : InputStream) (m : Model),
  m_conn_ix (with_stdin v m) = m_conn_ix m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_conn_ix_with_stdin : model.

Lemma m_conn_ix_with_urandom : forall (v : InputStream) (m : Model),
  m_conn_ix (with_urandom v m) = m_conn_ix m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_conn_ix_with_urandom : model.

Lemma m_conn_ix_with_fs : forall (v : Fs.Fs) (m : Model),
  m_conn_ix (with_fs v m) = m_conn_ix m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_conn_ix_with_fs : model.

Lemma m_conn_ix_with_halted : forall (v : word) (m : Model),
  m_conn_ix (with_halted v m) = m_conn_ix m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_conn_ix_with_halted : model.

Lemma m_conn_ix_with_tid : forall (v : word) (m : Model),
  m_conn_ix (with_tid v m) = m_conn_ix m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_conn_ix_with_tid : model.

Lemma m_conn_ix_with_rlimit_core : forall (v : list byte) (m : Model),
  m_conn_ix (with_rlimit_core v m) = m_conn_ix m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_conn_ix_with_rlimit_core : model.

Lemma m_conn_ix_with_clock : forall (v : word) (m : Model),
  m_conn_ix (with_clock v m) = m_conn_ix m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_conn_ix_with_clock : model.

Lemma m_conn_ix_with_creds : forall (v : Creds) (m : Model),
  m_conn_ix (with_creds v m) = m_conn_ix m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_conn_ix_with_creds : model.

Lemma m_conn_ix_with_net : forall (v : NetQueue) (m : Model),
  m_conn_ix (with_net v m) = m_conn_ix m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_conn_ix_with_net : model.

Lemma m_fds_with_net : forall (v : NetQueue) (m : Model),
  m_fds (with_net v m) = m_fds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fds_with_net : model.

Lemma m_vmmaps_with_net : forall (v : NetQueue) (m : Model),
  m_vmmaps (with_net v m) = m_vmmaps m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vmmaps_with_net : model.

Lemma m_stdin_with_net : forall (v : NetQueue) (m : Model),
  m_stdin (with_net v m) = m_stdin m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_stdin_with_net : model.

Lemma m_urandom_with_net : forall (v : NetQueue) (m : Model),
  m_urandom (with_net v m) = m_urandom m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_urandom_with_net : model.

Lemma m_fs_with_net : forall (v : NetQueue) (m : Model),
  m_fs (with_net v m) = m_fs m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fs_with_net : model.

Lemma m_halted_with_net : forall (v : NetQueue) (m : Model),
  m_halted (with_net v m) = m_halted m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_halted_with_net : model.

Lemma m_tid_with_net : forall (v : NetQueue) (m : Model),
  m_tid (with_net v m) = m_tid m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_tid_with_net : model.

Lemma m_rlimit_core_with_net : forall (v : NetQueue) (m : Model),
  m_rlimit_core (with_net v m) = m_rlimit_core m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_rlimit_core_with_net : model.

Lemma m_clock_with_net : forall (v : NetQueue) (m : Model),
  m_clock (with_net v m) = m_clock m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_clock_with_net : model.

Lemma m_creds_with_net : forall (v : NetQueue) (m : Model),
  m_creds (with_net v m) = m_creds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_creds_with_net : model.

Lemma m_rlimit_core_with_setsid_succeeded : forall (m : Model),
  m_rlimit_core (with_setsid_succeeded m) = m_rlimit_core m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_rlimit_core_with_setsid_succeeded : model.

Lemma m_setsid_succeeded_with_fds : forall (v : list (word * FdEntry)) (m : Model),
  m_setsid_succeeded (with_fds v m) = m_setsid_succeeded m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_setsid_succeeded_with_fds : model.

Lemma m_setsid_succeeded_with_vmmaps : forall (v : VmMaps) (m : Model),
  m_setsid_succeeded (with_vmmaps v m) = m_setsid_succeeded m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_setsid_succeeded_with_vmmaps : model.

Lemma m_setsid_succeeded_with_stdin : forall (v : InputStream) (m : Model),
  m_setsid_succeeded (with_stdin v m) = m_setsid_succeeded m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_setsid_succeeded_with_stdin : model.

Lemma m_setsid_succeeded_with_urandom : forall (v : InputStream) (m : Model),
  m_setsid_succeeded (with_urandom v m) = m_setsid_succeeded m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_setsid_succeeded_with_urandom : model.

Lemma m_setsid_succeeded_with_fs : forall (v : Fs.Fs) (m : Model),
  m_setsid_succeeded (with_fs v m) = m_setsid_succeeded m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_setsid_succeeded_with_fs : model.

Lemma m_setsid_succeeded_with_halted : forall (v : word) (m : Model),
  m_setsid_succeeded (with_halted v m) = m_setsid_succeeded m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_setsid_succeeded_with_halted : model.

Lemma m_setsid_succeeded_with_tid : forall (v : word) (m : Model),
  m_setsid_succeeded (with_tid v m) = m_setsid_succeeded m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_setsid_succeeded_with_tid : model.

Lemma m_setsid_succeeded_with_rlimit_core : forall (v : list byte) (m : Model),
  m_setsid_succeeded (with_rlimit_core v m) = m_setsid_succeeded m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_setsid_succeeded_with_rlimit_core : model.

Lemma m_setsid_succeeded_with_setsid_succeeded : forall (m : Model),
  m_setsid_succeeded (with_setsid_succeeded m) = true.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_setsid_succeeded_with_setsid_succeeded : model.

Lemma m_setsid_succeeded_with_clock : forall (v : word) (m : Model),
  m_setsid_succeeded (with_clock v m) = m_setsid_succeeded m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_setsid_succeeded_with_clock : model.

Lemma m_creds_with_setsid_succeeded : forall (m : Model),
  m_creds (with_setsid_succeeded m) = m_creds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_creds_with_setsid_succeeded : model.

Lemma m_setsid_succeeded_with_creds : forall (v : Creds) (m : Model),
  m_setsid_succeeded (with_creds v m) = m_setsid_succeeded m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_setsid_succeeded_with_creds : model.

Lemma m_setsid_succeeded_with_net : forall (v : NetQueue) (m : Model),
  m_setsid_succeeded (with_net v m) = m_setsid_succeeded m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_setsid_succeeded_with_net : model.

Lemma m_net_with_setsid_succeeded : forall (m : Model),
  m_net (with_setsid_succeeded m) = m_net m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_net_with_setsid_succeeded : model.

Lemma m_conn_ix_with_setsid_succeeded : forall (m : Model),
  m_conn_ix (with_setsid_succeeded m) = m_conn_ix m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_conn_ix_with_setsid_succeeded : model.

Lemma m_clock_with_pipes : forall (v : list (word * PipeBuf)) (m : Model),
  m_clock (with_pipes v m) = m_clock m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_clock_with_pipes : model.

Lemma m_pipes_with_fds : forall (v : list (word * FdEntry)) (m : Model),
  m_pipes (with_fds v m) = m_pipes m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_pipes_with_fds : model.

Lemma m_pipes_with_vmmaps : forall (v : VmMaps) (m : Model),
  m_pipes (with_vmmaps v m) = m_pipes m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_pipes_with_vmmaps : model.

Lemma m_pipes_with_stdin : forall (v : InputStream) (m : Model),
  m_pipes (with_stdin v m) = m_pipes m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_pipes_with_stdin : model.

Lemma m_pipes_with_urandom : forall (v : InputStream) (m : Model),
  m_pipes (with_urandom v m) = m_pipes m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_pipes_with_urandom : model.

Lemma m_pipes_with_fs : forall (v : Fs.Fs) (m : Model),
  m_pipes (with_fs v m) = m_pipes m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_pipes_with_fs : model.

Lemma m_pipes_with_halted : forall (v : word) (m : Model),
  m_pipes (with_halted v m) = m_pipes m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_pipes_with_halted : model.

Lemma m_pipes_with_tid : forall (v : word) (m : Model),
  m_pipes (with_tid v m) = m_pipes m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_pipes_with_tid : model.

Lemma m_pipes_with_rlimit_core : forall (v : list byte) (m : Model),
  m_pipes (with_rlimit_core v m) = m_pipes m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_pipes_with_rlimit_core : model.

Lemma m_pipes_with_clock : forall (v : word) (m : Model),
  m_pipes (with_clock v m) = m_pipes m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_pipes_with_clock : model.

Lemma m_pipes_with_pipes : forall (v : list (word * PipeBuf)) (m : Model),
  m_pipes (with_pipes v m) = v.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_pipes_with_pipes : model.

Lemma m_rlimit_core_with_pipes : forall (v : list (word * PipeBuf)) (m : Model),
  m_rlimit_core (with_pipes v m) = m_rlimit_core m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_rlimit_core_with_pipes : model.

(** The pipe table's half of the square against the other
    fields — the socket queue and its connection counter, the
    credentials, and the session bit.  [with_pipes] lives in [FdState] and
    every one of these lives elsewhere, so both directions are
    [reflexivity]; they are here because [autorewrite with model] needs
    the pair, not because either direction is in doubt. *)

Lemma m_pipes_with_net : forall (v : NetQueue) (m : Model),
  m_pipes (with_net v m) = m_pipes m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_pipes_with_net : model.

Lemma m_pipes_with_creds : forall (v : Creds) (m : Model),
  m_pipes (with_creds v m) = m_pipes m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_pipes_with_creds : model.

Lemma m_pipes_with_setsid_succeeded : forall (m : Model),
  m_pipes (with_setsid_succeeded m) = m_pipes m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_pipes_with_setsid_succeeded : model.

Lemma m_net_with_pipes : forall (v : list (word * PipeBuf)) (m : Model),
  m_net (with_pipes v m) = m_net m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_net_with_pipes : model.

Lemma m_conn_ix_with_pipes : forall (v : list (word * PipeBuf)) (m : Model),
  m_conn_ix (with_pipes v m) = m_conn_ix m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_conn_ix_with_pipes : model.

Lemma m_creds_with_pipes : forall (v : list (word * PipeBuf)) (m : Model),
  m_creds (with_pipes v m) = m_creds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_creds_with_pipes : model.

Lemma m_setsid_succeeded_with_pipes : forall (v : list (word * PipeBuf)) (m : Model),
  m_setsid_succeeded (with_pipes v m) = m_setsid_succeeded m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_setsid_succeeded_with_pipes : model.
(** The blocked mask against the other setters and accessors.  Every one
    is [reflexivity]: [with_sigmask] rebuilds [ProcState] alone, and every
    other setter either passes [m_proc m] through or carries
    [m_sigmask m] across explicitly. *)

Lemma m_sigmask_with_fds : forall (v : list (word * FdEntry)) (m : Model),
  m_sigmask (with_fds v m) = m_sigmask m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigmask_with_fds : model.

Lemma m_sigmask_with_vmmaps : forall (v : VmMaps) (m : Model),
  m_sigmask (with_vmmaps v m) = m_sigmask m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigmask_with_vmmaps : model.

Lemma m_sigmask_with_vm_backing : forall (l : list (word * word)) (mt : list word) (m : Model),
  m_sigmask (with_vm_backing l mt m) = m_sigmask m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigmask_with_vm_backing : model.

Lemma m_sigmask_with_stdin : forall (v : InputStream) (m : Model),
  m_sigmask (with_stdin v m) = m_sigmask m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigmask_with_stdin : model.

Lemma m_sigmask_with_urandom : forall (v : InputStream) (m : Model),
  m_sigmask (with_urandom v m) = m_sigmask m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigmask_with_urandom : model.

Lemma m_sigmask_with_net : forall (v : NetQueue) (m : Model),
  m_sigmask (with_net v m) = m_sigmask m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigmask_with_net : model.

Lemma m_sigmask_with_fs : forall (v : Fs.Fs) (m : Model),
  m_sigmask (with_fs v m) = m_sigmask m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigmask_with_fs : model.

Lemma m_sigmask_with_halted : forall (v : word) (m : Model),
  m_sigmask (with_halted v m) = m_sigmask m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigmask_with_halted : model.

Lemma m_sigmask_with_tid : forall (v : word) (m : Model),
  m_sigmask (with_tid v m) = m_sigmask m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigmask_with_tid : model.

Lemma m_sigmask_with_rlimit_core : forall (v : list byte) (m : Model),
  m_sigmask (with_rlimit_core v m) = m_sigmask m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigmask_with_rlimit_core : model.

Lemma m_sigmask_with_creds : forall (v : Creds) (m : Model),
  m_sigmask (with_creds v m) = m_sigmask m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigmask_with_creds : model.

Lemma m_sigmask_with_setsid_succeeded : forall (m : Model),
  m_sigmask (with_setsid_succeeded m) = m_sigmask m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigmask_with_setsid_succeeded : model.

Lemma m_sigmask_with_children : forall (m : Model),
  m_sigmask (with_children m) = m_sigmask m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigmask_with_children : model.

Lemma m_sigmask_with_clock : forall (v : word) (m : Model),
  m_sigmask (with_clock v m) = m_sigmask m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigmask_with_clock : model.

Lemma m_sigmask_with_accepted : forall (v : list (word * FdEntry)) (m : Model),
  m_sigmask (with_accepted v m) = m_sigmask m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigmask_with_accepted : model.

Lemma m_sigmask_with_sigmask : forall (v : word) (m : Model),
  m_sigmask (with_sigmask v m) = v.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigmask_with_sigmask : model.

Lemma m_fds_with_sigmask : forall (v : word) (m : Model),
  m_fds (with_sigmask v m) = m_fds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fds_with_sigmask : model.

Lemma m_vmmaps_with_sigmask : forall (v : word) (m : Model),
  m_vmmaps (with_sigmask v m) = m_vmmaps m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vmmaps_with_sigmask : model.

Lemma m_vm_lazy_with_sigmask : forall (v : word) (m : Model),
  m_vm_lazy (with_sigmask v m) = m_vm_lazy m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vm_lazy_with_sigmask : model.

Lemma m_vm_materialized_with_sigmask : forall (v : word) (m : Model),
  m_vm_materialized (with_sigmask v m) = m_vm_materialized m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vm_materialized_with_sigmask : model.

Lemma m_stdin_with_sigmask : forall (v : word) (m : Model),
  m_stdin (with_sigmask v m) = m_stdin m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_stdin_with_sigmask : model.

Lemma m_urandom_with_sigmask : forall (v : word) (m : Model),
  m_urandom (with_sigmask v m) = m_urandom m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_urandom_with_sigmask : model.

Lemma m_net_with_sigmask : forall (v : word) (m : Model),
  m_net (with_sigmask v m) = m_net m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_net_with_sigmask : model.

Lemma m_conn_ix_with_sigmask : forall (v : word) (m : Model),
  m_conn_ix (with_sigmask v m) = m_conn_ix m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_conn_ix_with_sigmask : model.

Lemma m_fs_with_sigmask : forall (v : word) (m : Model),
  m_fs (with_sigmask v m) = m_fs m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fs_with_sigmask : model.

Lemma m_halted_with_sigmask : forall (v : word) (m : Model),
  m_halted (with_sigmask v m) = m_halted m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_halted_with_sigmask : model.

Lemma m_tid_with_sigmask : forall (v : word) (m : Model),
  m_tid (with_sigmask v m) = m_tid m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_tid_with_sigmask : model.

Lemma m_setsid_succeeded_with_sigmask : forall (v : word) (m : Model),
  m_setsid_succeeded (with_sigmask v m) = m_setsid_succeeded m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_setsid_succeeded_with_sigmask : model.

Lemma m_has_children_with_sigmask : forall (v : word) (m : Model),
  m_has_children (with_sigmask v m) = m_has_children m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_has_children_with_sigmask : model.

Lemma m_rlimit_core_with_sigmask : forall (v : word) (m : Model),
  m_rlimit_core (with_sigmask v m) = m_rlimit_core m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_rlimit_core_with_sigmask : model.

Lemma m_clock_with_sigmask : forall (v : word) (m : Model),
  m_clock (with_sigmask v m) = m_clock m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_clock_with_sigmask : model.

Lemma m_creds_with_sigmask : forall (v : word) (m : Model),
  m_creds (with_sigmask v m) = m_creds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_creds_with_sigmask : model.

(** The alternate-signal-stack bit's row and column of the table above.
    The row says every other setter carries it across, which is the
    property [with_sigaltstack_installed]'s own note calls load-bearing; the
    column says installing it moves nothing else. *)

Lemma m_sigaltstack_installed_with_fds : forall (v : list (word * FdEntry)) (m : Model),
  m_sigaltstack_installed (with_fds v m) = m_sigaltstack_installed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigaltstack_installed_with_fds : model.

Lemma m_sigaltstack_installed_with_pipes : forall (v : list (word * PipeBuf)) (m : Model),
  m_sigaltstack_installed (with_pipes v m) = m_sigaltstack_installed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigaltstack_installed_with_pipes : model.

Lemma m_sigaltstack_installed_with_vmmaps : forall (v : VmMaps) (m : Model),
  m_sigaltstack_installed (with_vmmaps v m) = m_sigaltstack_installed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigaltstack_installed_with_vmmaps : model.

Lemma m_sigaltstack_installed_with_vm_backing : forall (l : list (word * word)) (mt : list word) (m : Model),
  m_sigaltstack_installed (with_vm_backing l mt m) = m_sigaltstack_installed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigaltstack_installed_with_vm_backing : model.

Lemma m_sigaltstack_installed_with_stdin : forall (v : InputStream) (m : Model),
  m_sigaltstack_installed (with_stdin v m) = m_sigaltstack_installed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigaltstack_installed_with_stdin : model.

Lemma m_sigaltstack_installed_with_urandom : forall (v : InputStream) (m : Model),
  m_sigaltstack_installed (with_urandom v m) = m_sigaltstack_installed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigaltstack_installed_with_urandom : model.

Lemma m_sigaltstack_installed_with_net : forall (v : NetQueue) (m : Model),
  m_sigaltstack_installed (with_net v m) = m_sigaltstack_installed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigaltstack_installed_with_net : model.

Lemma m_sigaltstack_installed_with_fs : forall (v : Fs.Fs) (m : Model),
  m_sigaltstack_installed (with_fs v m) = m_sigaltstack_installed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigaltstack_installed_with_fs : model.

Lemma m_sigaltstack_installed_with_halted : forall (v : word) (m : Model),
  m_sigaltstack_installed (with_halted v m) = m_sigaltstack_installed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigaltstack_installed_with_halted : model.

Lemma m_sigaltstack_installed_with_tid : forall (v : word) (m : Model),
  m_sigaltstack_installed (with_tid v m) = m_sigaltstack_installed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigaltstack_installed_with_tid : model.

Lemma m_sigaltstack_installed_with_rlimit_core : forall (v : list byte) (m : Model),
  m_sigaltstack_installed (with_rlimit_core v m) = m_sigaltstack_installed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigaltstack_installed_with_rlimit_core : model.

Lemma m_sigaltstack_installed_with_nofile : forall (v : word) (m : Model),
  m_sigaltstack_installed (with_nofile v m) = m_sigaltstack_installed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigaltstack_installed_with_nofile : model.

Lemma m_sigaltstack_installed_with_creds : forall (v : Creds) (m : Model),
  m_sigaltstack_installed (with_creds v m) = m_sigaltstack_installed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigaltstack_installed_with_creds : model.

Lemma m_sigaltstack_installed_with_setsid_succeeded : forall (m : Model),
  m_sigaltstack_installed (with_setsid_succeeded m) = m_sigaltstack_installed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigaltstack_installed_with_setsid_succeeded : model.

Lemma m_sigaltstack_installed_with_children : forall (m : Model),
  m_sigaltstack_installed (with_children m) = m_sigaltstack_installed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigaltstack_installed_with_children : model.

Lemma m_sigaltstack_installed_with_sigmask : forall (v : word) (m : Model),
  m_sigaltstack_installed (with_sigmask v m) = m_sigaltstack_installed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigaltstack_installed_with_sigmask : model.

Lemma m_sigaltstack_installed_with_clock : forall (v : word) (m : Model),
  m_sigaltstack_installed (with_clock v m) = m_sigaltstack_installed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigaltstack_installed_with_clock : model.

Lemma m_sigaltstack_installed_with_accepted : forall (v : list (word * FdEntry)) (m : Model),
  m_sigaltstack_installed (with_accepted v m) = m_sigaltstack_installed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigaltstack_installed_with_accepted : model.

Lemma m_sigaltstack_installed_with_utsname : forall (v : list byte) (m : Model),
  m_sigaltstack_installed (with_utsname v m) = m_sigaltstack_installed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigaltstack_installed_with_utsname : model.

Lemma m_sigaltstack_installed_with_sigaltstack_installed : forall (m : Model),
  m_sigaltstack_installed (with_sigaltstack_installed m) = true.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigaltstack_installed_with_sigaltstack_installed : model.

Lemma m_fds_with_sigaltstack_installed : forall (m : Model),
  m_fds (with_sigaltstack_installed m) = m_fds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fds_with_sigaltstack_installed : model.

Lemma m_pipes_with_sigaltstack_installed : forall (m : Model),
  m_pipes (with_sigaltstack_installed m) = m_pipes m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_pipes_with_sigaltstack_installed : model.

Lemma m_vmmaps_with_sigaltstack_installed : forall (m : Model),
  m_vmmaps (with_sigaltstack_installed m) = m_vmmaps m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vmmaps_with_sigaltstack_installed : model.

Lemma m_vm_lazy_with_sigaltstack_installed : forall (m : Model),
  m_vm_lazy (with_sigaltstack_installed m) = m_vm_lazy m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vm_lazy_with_sigaltstack_installed : model.

Lemma m_vm_materialized_with_sigaltstack_installed : forall (m : Model),
  m_vm_materialized (with_sigaltstack_installed m) = m_vm_materialized m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vm_materialized_with_sigaltstack_installed : model.

Lemma m_stdin_with_sigaltstack_installed : forall (m : Model),
  m_stdin (with_sigaltstack_installed m) = m_stdin m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_stdin_with_sigaltstack_installed : model.

Lemma m_urandom_with_sigaltstack_installed : forall (m : Model),
  m_urandom (with_sigaltstack_installed m) = m_urandom m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_urandom_with_sigaltstack_installed : model.

Lemma m_net_with_sigaltstack_installed : forall (m : Model),
  m_net (with_sigaltstack_installed m) = m_net m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_net_with_sigaltstack_installed : model.

Lemma m_conn_ix_with_sigaltstack_installed : forall (m : Model),
  m_conn_ix (with_sigaltstack_installed m) = m_conn_ix m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_conn_ix_with_sigaltstack_installed : model.

Lemma m_fs_with_sigaltstack_installed : forall (m : Model),
  m_fs (with_sigaltstack_installed m) = m_fs m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fs_with_sigaltstack_installed : model.

Lemma m_halted_with_sigaltstack_installed : forall (m : Model),
  m_halted (with_sigaltstack_installed m) = m_halted m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_halted_with_sigaltstack_installed : model.

Lemma m_tid_with_sigaltstack_installed : forall (m : Model),
  m_tid (with_sigaltstack_installed m) = m_tid m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_tid_with_sigaltstack_installed : model.

Lemma m_setsid_succeeded_with_sigaltstack_installed : forall (m : Model),
  m_setsid_succeeded (with_sigaltstack_installed m) = m_setsid_succeeded m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_setsid_succeeded_with_sigaltstack_installed : model.

Lemma m_has_children_with_sigaltstack_installed : forall (m : Model),
  m_has_children (with_sigaltstack_installed m) = m_has_children m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_has_children_with_sigaltstack_installed : model.

Lemma m_sigmask_with_sigaltstack_installed : forall (m : Model),
  m_sigmask (with_sigaltstack_installed m) = m_sigmask m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigmask_with_sigaltstack_installed : model.

Lemma m_rlimit_core_with_sigaltstack_installed : forall (m : Model),
  m_rlimit_core (with_sigaltstack_installed m) = m_rlimit_core m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_rlimit_core_with_sigaltstack_installed : model.

Lemma m_nofile_with_sigaltstack_installed : forall (m : Model),
  m_nofile (with_sigaltstack_installed m) = m_nofile m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_nofile_with_sigaltstack_installed : model.

Lemma m_clock_with_sigaltstack_installed : forall (m : Model),
  m_clock (with_sigaltstack_installed m) = m_clock m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_clock_with_sigaltstack_installed : model.

Lemma m_creds_with_sigaltstack_installed : forall (m : Model),
  m_creds (with_sigaltstack_installed m) = m_creds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_creds_with_sigaltstack_installed : model.

(** And the accessors of a freshly built model. *)

(** The soft descriptor limit's row and column of the table above.
    [with_nofile] runs once, in [init_model], so the column exists for the
    accessors that read a model built by it; the row is what a proof about
    [Sys.Fs.File.dup3_spec] needs, since installing a descriptor rewrites
    the fd table and the limit has to survive that. *)

Lemma m_nofile_with_fds : forall (v : list (word * FdEntry)) (m : Model),
  m_nofile (with_fds v m) = m_nofile m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_nofile_with_fds : model.

Lemma m_nofile_with_vmmaps : forall (v : VmMaps) (m : Model),
  m_nofile (with_vmmaps v m) = m_nofile m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_nofile_with_vmmaps : model.

Lemma m_nofile_with_stdin : forall (v : InputStream) (m : Model),
  m_nofile (with_stdin v m) = m_nofile m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_nofile_with_stdin : model.

Lemma m_nofile_with_urandom : forall (v : InputStream) (m : Model),
  m_nofile (with_urandom v m) = m_nofile m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_nofile_with_urandom : model.

Lemma m_nofile_with_fs : forall (v : Fs.Fs) (m : Model),
  m_nofile (with_fs v m) = m_nofile m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_nofile_with_fs : model.

Lemma m_nofile_with_halted : forall (v : word) (m : Model),
  m_nofile (with_halted v m) = m_nofile m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_nofile_with_halted : model.

Lemma m_nofile_with_tid : forall (v : word) (m : Model),
  m_nofile (with_tid v m) = m_nofile m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_nofile_with_tid : model.

Lemma m_nofile_with_rlimit_core : forall (v : list byte) (m : Model),
  m_nofile (with_rlimit_core v m) = m_nofile m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_nofile_with_rlimit_core : model.

Lemma m_nofile_with_clock : forall (v : word) (m : Model),
  m_nofile (with_clock v m) = m_nofile m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_nofile_with_clock : model.

Lemma m_nofile_with_creds : forall (v : Creds) (m : Model),
  m_nofile (with_creds v m) = m_nofile m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_nofile_with_creds : model.

Lemma m_nofile_with_net : forall (v : NetQueue) (m : Model),
  m_nofile (with_net v m) = m_nofile m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_nofile_with_net : model.

Lemma m_nofile_with_setsid_succeeded : forall (m : Model),
  m_nofile (with_setsid_succeeded m) = m_nofile m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_nofile_with_setsid_succeeded : model.

Lemma m_nofile_with_nofile : forall (v : word) (m : Model),
  m_nofile (with_nofile v m) = v.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_nofile_with_nofile : model.

Lemma m_fds_with_nofile : forall (v : word) (m : Model),
  m_fds (with_nofile v m) = m_fds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fds_with_nofile : model.

Lemma m_vmmaps_with_nofile : forall (v : word) (m : Model),
  m_vmmaps (with_nofile v m) = m_vmmaps m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vmmaps_with_nofile : model.

Lemma m_stdin_with_nofile : forall (v : word) (m : Model),
  m_stdin (with_nofile v m) = m_stdin m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_stdin_with_nofile : model.

Lemma m_urandom_with_nofile : forall (v : word) (m : Model),
  m_urandom (with_nofile v m) = m_urandom m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_urandom_with_nofile : model.

Lemma m_fs_with_nofile : forall (v : word) (m : Model),
  m_fs (with_nofile v m) = m_fs m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fs_with_nofile : model.

Lemma m_halted_with_nofile : forall (v : word) (m : Model),
  m_halted (with_nofile v m) = m_halted m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_halted_with_nofile : model.

Lemma m_tid_with_nofile : forall (v : word) (m : Model),
  m_tid (with_nofile v m) = m_tid m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_tid_with_nofile : model.

Lemma m_rlimit_core_with_nofile : forall (v : word) (m : Model),
  m_rlimit_core (with_nofile v m) = m_rlimit_core m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_rlimit_core_with_nofile : model.

Lemma m_clock_with_nofile : forall (v : word) (m : Model),
  m_clock (with_nofile v m) = m_clock m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_clock_with_nofile : model.

Lemma m_creds_with_nofile : forall (v : word) (m : Model),
  m_creds (with_nofile v m) = m_creds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_creds_with_nofile : model.

Lemma m_net_with_nofile : forall (v : word) (m : Model),
  m_net (with_nofile v m) = m_net m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_net_with_nofile : model.

Lemma m_conn_ix_with_nofile : forall (v : word) (m : Model),
  m_conn_ix (with_nofile v m) = m_conn_ix m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_conn_ix_with_nofile : model.

Lemma m_setsid_succeeded_with_nofile : forall (v : word) (m : Model),
  m_setsid_succeeded (with_nofile v m) = m_setsid_succeeded m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_setsid_succeeded_with_nofile : model.

Lemma m_fds_mkModel : forall fds vm stdin fs halted tid rlim,
  m_fds (mkModel fds vm stdin fs halted tid rlim) = fds.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fds_mkModel : model.

Lemma m_vmmaps_mkModel : forall fds vm stdin fs halted tid rlim,
  m_vmmaps (mkModel fds vm stdin fs halted tid rlim) = vm.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vmmaps_mkModel : model.

Lemma m_stdin_mkModel : forall fds vm stdin fs halted tid rlim,
  m_stdin (mkModel fds vm stdin fs halted tid rlim) = stdin.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_stdin_mkModel : model.

Lemma m_fs_mkModel : forall fds vm stdin fs halted tid rlim,
  m_fs (mkModel fds vm stdin fs halted tid rlim) = fs.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fs_mkModel : model.

Lemma m_halted_mkModel : forall fds vm stdin fs halted tid rlim,
  m_halted (mkModel fds vm stdin fs halted tid rlim) = halted.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_halted_mkModel : model.

Lemma m_tid_mkModel : forall fds vm stdin fs halted tid rlim,
  m_tid (mkModel fds vm stdin fs halted tid rlim) = tid.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_tid_mkModel : model.

Lemma m_rlimit_core_mkModel : forall fds vm stdin fs halted tid rlim,
  m_rlimit_core (mkModel fds vm stdin fs halted tid rlim) = rlim.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_rlimit_core_mkModel : model.

Lemma m_nofile_mkModel : forall fds vm stdin fs halted tid rlim,
  m_nofile (mkModel fds vm stdin fs halted tid rlim) = default_nofile.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_nofile_mkModel : model.

Lemma m_clock_mkModel : forall fds vm stdin fs halted tid rlim,
  m_clock (mkModel fds vm stdin fs halted tid rlim) = Z_to_bv 64 0.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_clock_mkModel : model.

(** A model built without a [ProcInput] runs as nobody; see [overflow_id]. *)
Lemma m_net_mkModel : forall fds vm stdin fs halted tid rlim,
  m_net (mkModel fds vm stdin fs halted tid rlim) = net_silent.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_net_mkModel : model.

Lemma m_conn_ix_mkModel : forall fds vm stdin fs halted tid rlim,
  m_conn_ix (mkModel fds vm stdin fs halted tid rlim) = Z_to_bv 64 0.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_conn_ix_mkModel : model.

Lemma m_creds_mkModel : forall fds vm stdin fs halted tid rlim,
  m_creds (mkModel fds vm stdin fs halted tid rlim) =
  mkCreds overflow_id overflow_id overflow_id overflow_id overflow_id
          overflow_id [].
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_creds_mkModel : model.

(** A freshly built model has led no session: [mkModel] defaults the bit, as
    it defaults the sparse VM ledgers, so no call site passes it. *)
Lemma m_sigmask_mkModel : forall fds vm stdin fs halted tid rlim,
  m_sigmask (mkModel fds vm stdin fs halted tid rlim) = Z_to_bv 64 0.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigmask_mkModel : model.

Lemma m_setsid_succeeded_mkModel : forall fds vm stdin fs halted tid rlim,
  m_setsid_succeeded (mkModel fds vm stdin fs halted tid rlim) = false.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_setsid_succeeded_mkModel : model.

Lemma m_pipes_mkModel : forall fds vm stdin fs halted tid rlim,
  m_pipes (mkModel fds vm stdin fs halted tid rlim) = [].
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_pipes_mkModel : model.

(** The UTS-name pin against every other move of the model.  One row and
    one column of the matrix above: nothing else reads or writes it, so
    every entry but the diagonal one is [m_utsname m]. *)

Lemma m_utsname_with_fds : forall (v : list (word * FdEntry)) (m : Model),
  m_utsname (with_fds v m) = m_utsname m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_utsname_with_fds : model.

Lemma m_utsname_with_pipes : forall (v : list (word * PipeBuf)) (m : Model),
  m_utsname (with_pipes v m) = m_utsname m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_utsname_with_pipes : model.

Lemma m_utsname_with_vmmaps : forall (v : VmMaps) (m : Model),
  m_utsname (with_vmmaps v m) = m_utsname m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_utsname_with_vmmaps : model.

Lemma m_utsname_with_vm_backing : forall (lz : list (word * word)) (mz : list word) (m : Model),
  m_utsname (with_vm_backing lz mz m) = m_utsname m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_utsname_with_vm_backing : model.

Lemma m_utsname_with_stdin : forall (v : InputStream) (m : Model),
  m_utsname (with_stdin v m) = m_utsname m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_utsname_with_stdin : model.

Lemma m_utsname_with_urandom : forall (v : InputStream) (m : Model),
  m_utsname (with_urandom v m) = m_utsname m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_utsname_with_urandom : model.

Lemma m_utsname_with_net : forall (v : NetQueue) (m : Model),
  m_utsname (with_net v m) = m_utsname m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_utsname_with_net : model.

Lemma m_utsname_with_accepted : forall (v : list (word * FdEntry)) (m : Model),
  m_utsname (with_accepted v m) = m_utsname m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_utsname_with_accepted : model.

Lemma m_utsname_with_fs : forall (v : Fs.Fs) (m : Model),
  m_utsname (with_fs v m) = m_utsname m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_utsname_with_fs : model.

Lemma m_utsname_with_halted : forall (v : word) (m : Model),
  m_utsname (with_halted v m) = m_utsname m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_utsname_with_halted : model.

Lemma m_utsname_with_tid : forall (v : word) (m : Model),
  m_utsname (with_tid v m) = m_utsname m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_utsname_with_tid : model.

Lemma m_utsname_with_rlimit_core : forall (v : list byte) (m : Model),
  m_utsname (with_rlimit_core v m) = m_utsname m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_utsname_with_rlimit_core : model.

Lemma m_utsname_with_nofile : forall (v : word) (m : Model),
  m_utsname (with_nofile v m) = m_utsname m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_utsname_with_nofile : model.

Lemma m_utsname_with_creds : forall (v : Creds) (m : Model),
  m_utsname (with_creds v m) = m_utsname m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_utsname_with_creds : model.

Lemma m_utsname_with_setsid_succeeded : forall (m : Model),
  m_utsname (with_setsid_succeeded m) = m_utsname m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_utsname_with_setsid_succeeded : model.

Lemma m_utsname_with_children : forall (m : Model),
  m_utsname (with_children m) = m_utsname m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_utsname_with_children : model.

Lemma m_utsname_with_sigmask : forall (v : word) (m : Model),
  m_utsname (with_sigmask v m) = m_utsname m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_utsname_with_sigmask : model.

Lemma m_utsname_with_clock : forall (v : word) (m : Model),
  m_utsname (with_clock v m) = m_utsname m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_utsname_with_clock : model.

Lemma m_utsname_with_sigaltstack_installed : forall (m : Model),
  m_utsname (with_sigaltstack_installed m) = m_utsname m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_utsname_with_sigaltstack_installed : model.

Lemma m_utsname_with_utsname : forall (v : list byte) (m : Model),
  m_utsname (with_utsname v m) = Some v.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_utsname_with_utsname : model.

Lemma m_fds_with_utsname : forall (v : list byte) (m : Model),
  m_fds (with_utsname v m) = m_fds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fds_with_utsname : model.

Lemma m_pipes_with_utsname : forall (v : list byte) (m : Model),
  m_pipes (with_utsname v m) = m_pipes m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_pipes_with_utsname : model.

Lemma m_vmmaps_with_utsname : forall (v : list byte) (m : Model),
  m_vmmaps (with_utsname v m) = m_vmmaps m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vmmaps_with_utsname : model.

Lemma m_vm_lazy_with_utsname : forall (v : list byte) (m : Model),
  m_vm_lazy (with_utsname v m) = m_vm_lazy m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vm_lazy_with_utsname : model.

Lemma m_vm_materialized_with_utsname : forall (v : list byte) (m : Model),
  m_vm_materialized (with_utsname v m) = m_vm_materialized m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vm_materialized_with_utsname : model.

Lemma m_stdin_with_utsname : forall (v : list byte) (m : Model),
  m_stdin (with_utsname v m) = m_stdin m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_stdin_with_utsname : model.

Lemma m_urandom_with_utsname : forall (v : list byte) (m : Model),
  m_urandom (with_utsname v m) = m_urandom m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_urandom_with_utsname : model.

Lemma m_net_with_utsname : forall (v : list byte) (m : Model),
  m_net (with_utsname v m) = m_net m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_net_with_utsname : model.

Lemma m_conn_ix_with_utsname : forall (v : list byte) (m : Model),
  m_conn_ix (with_utsname v m) = m_conn_ix m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_conn_ix_with_utsname : model.

Lemma m_fs_with_utsname : forall (v : list byte) (m : Model),
  m_fs (with_utsname v m) = m_fs m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fs_with_utsname : model.

Lemma m_halted_with_utsname : forall (v : list byte) (m : Model),
  m_halted (with_utsname v m) = m_halted m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_halted_with_utsname : model.

Lemma m_tid_with_utsname : forall (v : list byte) (m : Model),
  m_tid (with_utsname v m) = m_tid m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_tid_with_utsname : model.

Lemma m_setsid_succeeded_with_utsname : forall (v : list byte) (m : Model),
  m_setsid_succeeded (with_utsname v m) = m_setsid_succeeded m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_setsid_succeeded_with_utsname : model.

Lemma m_has_children_with_utsname : forall (v : list byte) (m : Model),
  m_has_children (with_utsname v m) = m_has_children m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_has_children_with_utsname : model.

Lemma m_sigmask_with_utsname : forall (v : list byte) (m : Model),
  m_sigmask (with_utsname v m) = m_sigmask m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigmask_with_utsname : model.

Lemma m_rlimit_core_with_utsname : forall (v : list byte) (m : Model),
  m_rlimit_core (with_utsname v m) = m_rlimit_core m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_rlimit_core_with_utsname : model.

Lemma m_nofile_with_utsname : forall (v : list byte) (m : Model),
  m_nofile (with_utsname v m) = m_nofile m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_nofile_with_utsname : model.

Lemma m_clock_with_utsname : forall (v : list byte) (m : Model),
  m_clock (with_utsname v m) = m_clock m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_clock_with_utsname : model.

Lemma m_creds_with_utsname : forall (v : list byte) (m : Model),
  m_creds (with_utsname v m) = m_creds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_creds_with_utsname : model.

Lemma m_utsname_mkModel : forall fds vm stdin fs halted tid rlim,
  m_utsname (mkModel fds vm stdin fs halted tid rlim) = None.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_utsname_mkModel : model.


(** The per-file stat pins against every other move of the model.  One
    row and one column of the matrix above: [Fs.Stat.fstat_spec] is the
    only reader and [with_statpin] the only writer, so every entry but
    the diagonal one is [m_statpins m].

    The column is what the framing obligations need.  A [fstat] that
    creates a pin changes the model on a
    SUCCESS that also writes user memory, so
    [Checks.VmMapsDisjoint]'s per-arm frame lemma for 80 has to see
    through [with_statpin] to the untouched [m_vmmaps]. *)
Lemma m_statpins_with_fds : forall (v : list (word * FdEntry)) (m : Model),
  m_statpins (with_fds v m) = m_statpins m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_statpins_with_fds : model.

Lemma m_statpins_with_pipes : forall (v : list (word * PipeBuf)) (m : Model),
  m_statpins (with_pipes v m) = m_statpins m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_statpins_with_pipes : model.

Lemma m_statpins_with_vmmaps : forall (v : VmMaps) (m : Model),
  m_statpins (with_vmmaps v m) = m_statpins m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_statpins_with_vmmaps : model.

Lemma m_statpins_with_vm_backing : forall (lz : list (word * word)) (mz : list word) (m : Model),
  m_statpins (with_vm_backing lz mz m) = m_statpins m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_statpins_with_vm_backing : model.

Lemma m_statpins_with_stdin : forall (v : InputStream) (m : Model),
  m_statpins (with_stdin v m) = m_statpins m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_statpins_with_stdin : model.

Lemma m_statpins_with_urandom : forall (v : InputStream) (m : Model),
  m_statpins (with_urandom v m) = m_statpins m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_statpins_with_urandom : model.

Lemma m_statpins_with_net : forall (v : NetQueue) (m : Model),
  m_statpins (with_net v m) = m_statpins m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_statpins_with_net : model.

Lemma m_statpins_with_accepted : forall (v : list (word * FdEntry)) (m : Model),
  m_statpins (with_accepted v m) = m_statpins m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_statpins_with_accepted : model.

Lemma m_statpins_with_fs : forall (v : Fs.Fs) (m : Model),
  m_statpins (with_fs v m) = statpins_restrict v (m_statpins m).
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_statpins_with_fs : model.

Lemma m_statpins_with_halted : forall (v : word) (m : Model),
  m_statpins (with_halted v m) = m_statpins m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_statpins_with_halted : model.

Lemma m_statpins_with_tid : forall (v : word) (m : Model),
  m_statpins (with_tid v m) = m_statpins m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_statpins_with_tid : model.

Lemma m_statpins_with_rlimit_core : forall (v : list byte) (m : Model),
  m_statpins (with_rlimit_core v m) = m_statpins m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_statpins_with_rlimit_core : model.

Lemma m_statpins_with_nofile : forall (v : word) (m : Model),
  m_statpins (with_nofile v m) = m_statpins m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_statpins_with_nofile : model.

Lemma m_statpins_with_creds : forall (v : Creds) (m : Model),
  m_statpins (with_creds v m) = m_statpins m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_statpins_with_creds : model.

Lemma m_statpins_with_setsid_succeeded : forall (m : Model),
  m_statpins (with_setsid_succeeded m) = m_statpins m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_statpins_with_setsid_succeeded : model.

Lemma m_statpins_with_children : forall (m : Model),
  m_statpins (with_children m) = m_statpins m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_statpins_with_children : model.

Lemma m_statpins_with_sigmask : forall (v : word) (m : Model),
  m_statpins (with_sigmask v m) = m_statpins m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_statpins_with_sigmask : model.

Lemma m_statpins_with_clock : forall (v : word) (m : Model),
  m_statpins (with_clock v m) = m_statpins m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_statpins_with_clock : model.

Lemma m_statpins_with_utsname : forall (v : list byte) (m : Model),
  m_statpins (with_utsname v m) = m_statpins m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_statpins_with_utsname : model.

Lemma m_fds_with_statpin : forall (p : Fs.path) (bs : list byte) (m : Model),
  m_fds (with_statpin p bs m) = m_fds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fds_with_statpin : model.

Lemma m_pipes_with_statpin : forall (p : Fs.path) (bs : list byte) (m : Model),
  m_pipes (with_statpin p bs m) = m_pipes m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_pipes_with_statpin : model.

Lemma m_vmmaps_with_statpin : forall (p : Fs.path) (bs : list byte) (m : Model),
  m_vmmaps (with_statpin p bs m) = m_vmmaps m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vmmaps_with_statpin : model.

Lemma m_vm_lazy_with_statpin : forall (p : Fs.path) (bs : list byte) (m : Model),
  m_vm_lazy (with_statpin p bs m) = m_vm_lazy m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vm_lazy_with_statpin : model.

Lemma m_vm_materialized_with_statpin : forall (p : Fs.path) (bs : list byte) (m : Model),
  m_vm_materialized (with_statpin p bs m) = m_vm_materialized m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vm_materialized_with_statpin : model.

Lemma m_stdin_with_statpin : forall (p : Fs.path) (bs : list byte) (m : Model),
  m_stdin (with_statpin p bs m) = m_stdin m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_stdin_with_statpin : model.

Lemma m_net_with_statpin : forall (p : Fs.path) (bs : list byte) (m : Model),
  m_net (with_statpin p bs m) = m_net m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_net_with_statpin : model.

Lemma m_conn_ix_with_statpin : forall (p : Fs.path) (bs : list byte) (m : Model),
  m_conn_ix (with_statpin p bs m) = m_conn_ix m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_conn_ix_with_statpin : model.

Lemma m_fs_with_statpin : forall (p : Fs.path) (bs : list byte) (m : Model),
  m_fs (with_statpin p bs m) = m_fs m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fs_with_statpin : model.

Lemma m_halted_with_statpin : forall (p : Fs.path) (bs : list byte) (m : Model),
  m_halted (with_statpin p bs m) = m_halted m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_halted_with_statpin : model.

Lemma m_tid_with_statpin : forall (p : Fs.path) (bs : list byte) (m : Model),
  m_tid (with_statpin p bs m) = m_tid m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_tid_with_statpin : model.

Lemma m_setsid_succeeded_with_statpin : forall (p : Fs.path) (bs : list byte) (m : Model),
  m_setsid_succeeded (with_statpin p bs m) = m_setsid_succeeded m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_setsid_succeeded_with_statpin : model.

Lemma m_has_children_with_statpin : forall (p : Fs.path) (bs : list byte) (m : Model),
  m_has_children (with_statpin p bs m) = m_has_children m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_has_children_with_statpin : model.

Lemma m_sigmask_with_statpin : forall (p : Fs.path) (bs : list byte) (m : Model),
  m_sigmask (with_statpin p bs m) = m_sigmask m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigmask_with_statpin : model.

Lemma m_utsname_with_statpin : forall (p : Fs.path) (bs : list byte) (m : Model),
  m_utsname (with_statpin p bs m) = m_utsname m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_utsname_with_statpin : model.

Lemma m_rlimit_core_with_statpin : forall (p : Fs.path) (bs : list byte) (m : Model),
  m_rlimit_core (with_statpin p bs m) = m_rlimit_core m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_rlimit_core_with_statpin : model.

Lemma m_nofile_with_statpin : forall (p : Fs.path) (bs : list byte) (m : Model),
  m_nofile (with_statpin p bs m) = m_nofile m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_nofile_with_statpin : model.

Lemma m_clock_with_statpin : forall (p : Fs.path) (bs : list byte) (m : Model),
  m_clock (with_statpin p bs m) = m_clock m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_clock_with_statpin : model.

Lemma m_creds_with_statpin : forall (p : Fs.path) (bs : list byte) (m : Model),
  m_creds (with_statpin p bs m) = m_creds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_creds_with_statpin : model.

Lemma m_statpins_with_statpin : forall (p : Fs.path) (bs : list byte) (m : Model),
  m_statpins (with_statpin p bs m) = (p, bs) :: m_statpins m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_statpins_with_statpin : model.

Lemma m_statpins_mkModel : forall fds vm stdin fs halted tid rlim,
  m_statpins (mkModel fds vm stdin fs halted tid rlim) = [].
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_statpins_mkModel : model.

(** Opaque to reduction, on purpose.  [cbn]/[simpl] must not walk into the
    nesting: a proof that wants past an accessor uses the rewrites above,
    which keeps [m_fs model] looking like [m_fs model] wherever it is not
    applied to a setter. *)

Arguments m_fds : simpl never.
Arguments with_fds : simpl never.

Arguments m_vmmaps : simpl never.
Arguments with_vmmaps : simpl never.

Arguments m_stdin : simpl never.
Arguments with_stdin : simpl never.
Arguments m_urandom : simpl never.
Arguments with_urandom : simpl never.

Arguments m_fs : simpl never.
Arguments with_fs : simpl never.

Arguments m_halted : simpl never.
Arguments with_halted : simpl never.

Arguments m_tid : simpl never.
Arguments with_tid : simpl never.

Arguments m_rlimit_core : simpl never.
Arguments with_rlimit_core : simpl never.

Arguments m_nofile : simpl never.
Arguments with_nofile : simpl never.

Arguments m_clock : simpl never.
Arguments with_clock : simpl never.

Arguments m_creds : simpl never.
Arguments with_creds : simpl never.

Arguments m_net : simpl never.
Arguments m_conn_ix : simpl never.
Arguments with_accepted : simpl never.

Arguments m_setsid_succeeded : simpl never.
Arguments with_setsid_succeeded : simpl never.

Arguments m_pipes : simpl never.
Arguments with_pipes : simpl never.
Arguments m_sigmask : simpl never.
Arguments with_sigmask : simpl never.

Arguments m_utsname : simpl never.
Arguments with_utsname : simpl never.

(** And of the model a run starts from.  [init_model] builds one with
    [mkModel], so these are [reflexivity] too -- but a proof cannot see that
    through an opaque accessor, and [cbn] with a delta list will not unfold
    [init_model] to show it.

    DELIBERATELY NOT in the [model] database.  Rewriting these everywhere
    normalises [m_vmmaps (init_model ...)] in proofs that match on it
    unreduced, and breaks more than it fixes -- the same trap as widening a
    [cbn] constant list.  A site that wants one names it. *)

(** The three fields the abort path added, against every setter, and
    every other field against the three setters that write them.  Same
    shape and same [reflexivity] as the block above, and the same reason
    for existing -- but these carry a second job.  [procst_killed],
    [procst_sigabrt_pending] and [procst_abort_terminal] are the fields a
    run with the declaration OFF must never see move, and the lemmas
    below are what says no setter moves them: the only writers are
    [with_killed], [with_sigabrt_pending] and [with_abort_terminal], and
    every other setter carries all three across.  See
    [Kernel.Signal.tkill_spec] for the callers. *)

Lemma m_fds_with_abort_terminal : forall (v : bool) (m : Model),
  m_fds (with_abort_terminal v m) = m_fds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fds_with_abort_terminal : model.

Lemma m_fds_with_sigabrt_pending : forall (m : Model),
  m_fds (with_sigabrt_pending m) = m_fds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fds_with_sigabrt_pending : model.

Lemma m_fds_with_killed : forall (v : word) (m : Model),
  m_fds (with_killed v m) = m_fds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fds_with_killed : model.

Lemma m_pipes_with_abort_terminal : forall (v : bool) (m : Model),
  m_pipes (with_abort_terminal v m) = m_pipes m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_pipes_with_abort_terminal : model.

Lemma m_pipes_with_sigabrt_pending : forall (m : Model),
  m_pipes (with_sigabrt_pending m) = m_pipes m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_pipes_with_sigabrt_pending : model.

Lemma m_pipes_with_killed : forall (v : word) (m : Model),
  m_pipes (with_killed v m) = m_pipes m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_pipes_with_killed : model.

Lemma m_vmmaps_with_abort_terminal : forall (v : bool) (m : Model),
  m_vmmaps (with_abort_terminal v m) = m_vmmaps m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vmmaps_with_abort_terminal : model.

Lemma m_vmmaps_with_sigabrt_pending : forall (m : Model),
  m_vmmaps (with_sigabrt_pending m) = m_vmmaps m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vmmaps_with_sigabrt_pending : model.

Lemma m_vmmaps_with_killed : forall (v : word) (m : Model),
  m_vmmaps (with_killed v m) = m_vmmaps m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vmmaps_with_killed : model.

Lemma m_vm_lazy_with_abort_terminal : forall (v : bool) (m : Model),
  m_vm_lazy (with_abort_terminal v m) = m_vm_lazy m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vm_lazy_with_abort_terminal : model.

Lemma m_vm_lazy_with_sigabrt_pending : forall (m : Model),
  m_vm_lazy (with_sigabrt_pending m) = m_vm_lazy m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vm_lazy_with_sigabrt_pending : model.

Lemma m_vm_lazy_with_killed : forall (v : word) (m : Model),
  m_vm_lazy (with_killed v m) = m_vm_lazy m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vm_lazy_with_killed : model.

Lemma m_vm_materialized_with_abort_terminal : forall (v : bool) (m : Model),
  m_vm_materialized (with_abort_terminal v m) = m_vm_materialized m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vm_materialized_with_abort_terminal : model.

Lemma m_vm_materialized_with_sigabrt_pending : forall (m : Model),
  m_vm_materialized (with_sigabrt_pending m) = m_vm_materialized m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vm_materialized_with_sigabrt_pending : model.

Lemma m_vm_materialized_with_killed : forall (v : word) (m : Model),
  m_vm_materialized (with_killed v m) = m_vm_materialized m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_vm_materialized_with_killed : model.

Lemma m_stdin_with_abort_terminal : forall (v : bool) (m : Model),
  m_stdin (with_abort_terminal v m) = m_stdin m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_stdin_with_abort_terminal : model.

Lemma m_urandom_with_abort_terminal : forall (v : bool) (m : Model),
  m_urandom (with_abort_terminal v m) = m_urandom m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_urandom_with_abort_terminal : model.

Lemma m_stdin_with_sigabrt_pending : forall (m : Model),
  m_stdin (with_sigabrt_pending m) = m_stdin m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_stdin_with_sigabrt_pending : model.

Lemma m_urandom_with_sigabrt_pending : forall (m : Model),
  m_urandom (with_sigabrt_pending m) = m_urandom m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_urandom_with_sigabrt_pending : model.

Lemma m_stdin_with_killed : forall (v : word) (m : Model),
  m_stdin (with_killed v m) = m_stdin m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_stdin_with_killed : model.

Lemma m_urandom_with_killed : forall (v : word) (m : Model),
  m_urandom (with_killed v m) = m_urandom m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_urandom_with_killed : model.

Lemma m_net_with_abort_terminal : forall (v : bool) (m : Model),
  m_net (with_abort_terminal v m) = m_net m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_net_with_abort_terminal : model.

Lemma m_net_with_sigabrt_pending : forall (m : Model),
  m_net (with_sigabrt_pending m) = m_net m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_net_with_sigabrt_pending : model.

Lemma m_net_with_killed : forall (v : word) (m : Model),
  m_net (with_killed v m) = m_net m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_net_with_killed : model.

Lemma m_conn_ix_with_abort_terminal : forall (v : bool) (m : Model),
  m_conn_ix (with_abort_terminal v m) = m_conn_ix m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_conn_ix_with_abort_terminal : model.

Lemma m_conn_ix_with_sigabrt_pending : forall (m : Model),
  m_conn_ix (with_sigabrt_pending m) = m_conn_ix m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_conn_ix_with_sigabrt_pending : model.

Lemma m_conn_ix_with_killed : forall (v : word) (m : Model),
  m_conn_ix (with_killed v m) = m_conn_ix m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_conn_ix_with_killed : model.

Lemma m_fs_with_abort_terminal : forall (v : bool) (m : Model),
  m_fs (with_abort_terminal v m) = m_fs m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fs_with_abort_terminal : model.

Lemma m_fs_with_sigabrt_pending : forall (m : Model),
  m_fs (with_sigabrt_pending m) = m_fs m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fs_with_sigabrt_pending : model.

Lemma m_fs_with_killed : forall (v : word) (m : Model),
  m_fs (with_killed v m) = m_fs m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fs_with_killed : model.

Lemma m_halted_with_abort_terminal : forall (v : bool) (m : Model),
  m_halted (with_abort_terminal v m) = m_halted m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_halted_with_abort_terminal : model.

Lemma m_halted_with_sigabrt_pending : forall (m : Model),
  m_halted (with_sigabrt_pending m) = m_halted m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_halted_with_sigabrt_pending : model.

Lemma m_halted_with_killed : forall (v : word) (m : Model),
  m_halted (with_killed v m) = Some v.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_halted_with_killed : model.

Lemma m_tid_with_abort_terminal : forall (v : bool) (m : Model),
  m_tid (with_abort_terminal v m) = m_tid m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_tid_with_abort_terminal : model.

Lemma m_tid_with_sigabrt_pending : forall (m : Model),
  m_tid (with_sigabrt_pending m) = m_tid m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_tid_with_sigabrt_pending : model.

Lemma m_tid_with_killed : forall (v : word) (m : Model),
  m_tid (with_killed v m) = m_tid m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_tid_with_killed : model.

Lemma m_setsid_succeeded_with_abort_terminal : forall (v : bool) (m : Model),
  m_setsid_succeeded (with_abort_terminal v m) = m_setsid_succeeded m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_setsid_succeeded_with_abort_terminal : model.

Lemma m_setsid_succeeded_with_sigabrt_pending : forall (m : Model),
  m_setsid_succeeded (with_sigabrt_pending m) = m_setsid_succeeded m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_setsid_succeeded_with_sigabrt_pending : model.

Lemma m_setsid_succeeded_with_killed : forall (v : word) (m : Model),
  m_setsid_succeeded (with_killed v m) = m_setsid_succeeded m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_setsid_succeeded_with_killed : model.

Lemma m_has_children_with_abort_terminal : forall (v : bool) (m : Model),
  m_has_children (with_abort_terminal v m) = m_has_children m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_has_children_with_abort_terminal : model.

Lemma m_has_children_with_sigabrt_pending : forall (m : Model),
  m_has_children (with_sigabrt_pending m) = m_has_children m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_has_children_with_sigabrt_pending : model.

Lemma m_has_children_with_killed : forall (v : word) (m : Model),
  m_has_children (with_killed v m) = m_has_children m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_has_children_with_killed : model.

Lemma m_sigmask_with_abort_terminal : forall (v : bool) (m : Model),
  m_sigmask (with_abort_terminal v m) = m_sigmask m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigmask_with_abort_terminal : model.

Lemma m_sigmask_with_sigabrt_pending : forall (m : Model),
  m_sigmask (with_sigabrt_pending m) = m_sigmask m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigmask_with_sigabrt_pending : model.

Lemma m_sigmask_with_killed : forall (v : word) (m : Model),
  m_sigmask (with_killed v m) = m_sigmask m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigmask_with_killed : model.

Lemma m_utsname_with_abort_terminal : forall (v : bool) (m : Model),
  m_utsname (with_abort_terminal v m) = m_utsname m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_utsname_with_abort_terminal : model.

Lemma m_utsname_with_sigabrt_pending : forall (m : Model),
  m_utsname (with_sigabrt_pending m) = m_utsname m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_utsname_with_sigabrt_pending : model.

Lemma m_utsname_with_killed : forall (v : word) (m : Model),
  m_utsname (with_killed v m) = m_utsname m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_utsname_with_killed : model.

Lemma m_rlimit_core_with_abort_terminal : forall (v : bool) (m : Model),
  m_rlimit_core (with_abort_terminal v m) = m_rlimit_core m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_rlimit_core_with_abort_terminal : model.

Lemma m_rlimit_core_with_sigabrt_pending : forall (m : Model),
  m_rlimit_core (with_sigabrt_pending m) = m_rlimit_core m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_rlimit_core_with_sigabrt_pending : model.

Lemma m_rlimit_core_with_killed : forall (v : word) (m : Model),
  m_rlimit_core (with_killed v m) = m_rlimit_core m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_rlimit_core_with_killed : model.

Lemma m_nofile_with_abort_terminal : forall (v : bool) (m : Model),
  m_nofile (with_abort_terminal v m) = m_nofile m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_nofile_with_abort_terminal : model.

Lemma m_nofile_with_sigabrt_pending : forall (m : Model),
  m_nofile (with_sigabrt_pending m) = m_nofile m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_nofile_with_sigabrt_pending : model.

Lemma m_nofile_with_killed : forall (v : word) (m : Model),
  m_nofile (with_killed v m) = m_nofile m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_nofile_with_killed : model.

Lemma m_clock_with_abort_terminal : forall (v : bool) (m : Model),
  m_clock (with_abort_terminal v m) = m_clock m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_clock_with_abort_terminal : model.

Lemma m_clock_with_sigabrt_pending : forall (m : Model),
  m_clock (with_sigabrt_pending m) = m_clock m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_clock_with_sigabrt_pending : model.

Lemma m_clock_with_killed : forall (v : word) (m : Model),
  m_clock (with_killed v m) = m_clock m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_clock_with_killed : model.

Lemma m_creds_with_abort_terminal : forall (v : bool) (m : Model),
  m_creds (with_abort_terminal v m) = m_creds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_creds_with_abort_terminal : model.

Lemma m_creds_with_sigabrt_pending : forall (m : Model),
  m_creds (with_sigabrt_pending m) = m_creds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_creds_with_sigabrt_pending : model.

Lemma m_creds_with_killed : forall (v : word) (m : Model),
  m_creds (with_killed v m) = m_creds m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_creds_with_killed : model.

Lemma m_killed_with_fds : forall (v : list (word * FdEntry)) (m : Model),
  m_killed (with_fds v m) = m_killed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_killed_with_fds : model.

Lemma m_killed_with_pipes : forall (v : list (word * PipeBuf)) (m : Model),
  m_killed (with_pipes v m) = m_killed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_killed_with_pipes : model.

Lemma m_killed_with_vmmaps : forall (v : VmMaps) (m : Model),
  m_killed (with_vmmaps v m) = m_killed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_killed_with_vmmaps : model.

Lemma m_killed_with_vm_backing : forall (lz : list (word * word)) (mt : list word) (m : Model),
  m_killed (with_vm_backing lz mt m) = m_killed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_killed_with_vm_backing : model.

Lemma m_killed_with_stdin : forall (v : InputStream) (m : Model),
  m_killed (with_stdin v m) = m_killed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_killed_with_stdin : model.

Lemma m_killed_with_urandom : forall (v : InputStream) (m : Model),
  m_killed (with_urandom v m) = m_killed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_killed_with_urandom : model.

Lemma m_killed_with_net : forall (v : NetQueue) (m : Model),
  m_killed (with_net v m) = m_killed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_killed_with_net : model.

Lemma m_killed_with_fs : forall (v : Fs.Fs) (m : Model),
  m_killed (with_fs v m) = m_killed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_killed_with_fs : model.

Lemma m_killed_with_halted : forall (v : word) (m : Model),
  m_killed (with_halted v m) = None.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_killed_with_halted : model.

Lemma m_killed_with_tid : forall (v : word) (m : Model),
  m_killed (with_tid v m) = m_killed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_killed_with_tid : model.

Lemma m_killed_with_rlimit_core : forall (v : list byte) (m : Model),
  m_killed (with_rlimit_core v m) = m_killed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_killed_with_rlimit_core : model.

Lemma m_killed_with_utsname : forall (v : list byte) (m : Model),
  m_killed (with_utsname v m) = m_killed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_killed_with_utsname : model.

Lemma m_killed_with_nofile : forall (v : word) (m : Model),
  m_killed (with_nofile v m) = m_killed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_killed_with_nofile : model.

Lemma m_killed_with_creds : forall (v : Creds) (m : Model),
  m_killed (with_creds v m) = m_killed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_killed_with_creds : model.

Lemma m_killed_with_setsid_succeeded : forall (m : Model),
  m_killed (with_setsid_succeeded m) = m_killed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_killed_with_setsid_succeeded : model.

Lemma m_killed_with_children : forall (m : Model),
  m_killed (with_children m) = m_killed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_killed_with_children : model.

Lemma m_killed_with_sigmask : forall (v : word) (m : Model),
  m_killed (with_sigmask v m) = m_killed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_killed_with_sigmask : model.

Lemma m_killed_with_clock : forall (v : word) (m : Model),
  m_killed (with_clock v m) = m_killed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_killed_with_clock : model.

Lemma m_killed_with_accepted : forall (v : list (word * FdEntry)) (m : Model),
  m_killed (with_accepted v m) = m_killed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_killed_with_accepted : model.

Lemma m_killed_with_abort_terminal : forall (v : bool) (m : Model),
  m_killed (with_abort_terminal v m) = m_killed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_killed_with_abort_terminal : model.

Lemma m_killed_with_sigabrt_pending : forall (m : Model),
  m_killed (with_sigabrt_pending m) = m_killed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_killed_with_sigabrt_pending : model.

Lemma m_killed_with_killed : forall (v : word) (m : Model),
  m_killed (with_killed v m) = Some v.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_killed_with_killed : model.

Lemma m_sigabrt_pending_with_fds : forall (v : list (word * FdEntry)) (m : Model),
  m_sigabrt_pending (with_fds v m) = m_sigabrt_pending m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigabrt_pending_with_fds : model.

Lemma m_sigabrt_pending_with_pipes : forall (v : list (word * PipeBuf)) (m : Model),
  m_sigabrt_pending (with_pipes v m) = m_sigabrt_pending m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigabrt_pending_with_pipes : model.

Lemma m_sigabrt_pending_with_vmmaps : forall (v : VmMaps) (m : Model),
  m_sigabrt_pending (with_vmmaps v m) = m_sigabrt_pending m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigabrt_pending_with_vmmaps : model.

Lemma m_sigabrt_pending_with_vm_backing : forall (lz : list (word * word)) (mt : list word) (m : Model),
  m_sigabrt_pending (with_vm_backing lz mt m) = m_sigabrt_pending m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigabrt_pending_with_vm_backing : model.

Lemma m_sigabrt_pending_with_stdin : forall (v : InputStream) (m : Model),
  m_sigabrt_pending (with_stdin v m) = m_sigabrt_pending m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigabrt_pending_with_stdin : model.

Lemma m_sigabrt_pending_with_urandom : forall (v : InputStream) (m : Model),
  m_sigabrt_pending (with_urandom v m) = m_sigabrt_pending m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigabrt_pending_with_urandom : model.

Lemma m_sigabrt_pending_with_net : forall (v : NetQueue) (m : Model),
  m_sigabrt_pending (with_net v m) = m_sigabrt_pending m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigabrt_pending_with_net : model.

Lemma m_sigabrt_pending_with_fs : forall (v : Fs.Fs) (m : Model),
  m_sigabrt_pending (with_fs v m) = m_sigabrt_pending m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigabrt_pending_with_fs : model.

Lemma m_sigabrt_pending_with_halted : forall (v : word) (m : Model),
  m_sigabrt_pending (with_halted v m) = m_sigabrt_pending m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigabrt_pending_with_halted : model.

Lemma m_sigabrt_pending_with_tid : forall (v : word) (m : Model),
  m_sigabrt_pending (with_tid v m) = m_sigabrt_pending m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigabrt_pending_with_tid : model.

Lemma m_sigabrt_pending_with_rlimit_core : forall (v : list byte) (m : Model),
  m_sigabrt_pending (with_rlimit_core v m) = m_sigabrt_pending m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigabrt_pending_with_rlimit_core : model.

Lemma m_sigabrt_pending_with_utsname : forall (v : list byte) (m : Model),
  m_sigabrt_pending (with_utsname v m) = m_sigabrt_pending m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigabrt_pending_with_utsname : model.

Lemma m_sigabrt_pending_with_nofile : forall (v : word) (m : Model),
  m_sigabrt_pending (with_nofile v m) = m_sigabrt_pending m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigabrt_pending_with_nofile : model.

Lemma m_sigabrt_pending_with_creds : forall (v : Creds) (m : Model),
  m_sigabrt_pending (with_creds v m) = m_sigabrt_pending m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigabrt_pending_with_creds : model.

Lemma m_sigabrt_pending_with_setsid_succeeded : forall (m : Model),
  m_sigabrt_pending (with_setsid_succeeded m) = m_sigabrt_pending m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigabrt_pending_with_setsid_succeeded : model.

Lemma m_sigabrt_pending_with_children : forall (m : Model),
  m_sigabrt_pending (with_children m) = m_sigabrt_pending m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigabrt_pending_with_children : model.

Lemma m_sigabrt_pending_with_sigmask : forall (v : word) (m : Model),
  m_sigabrt_pending (with_sigmask v m) = m_sigabrt_pending m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigabrt_pending_with_sigmask : model.

Lemma m_sigabrt_pending_with_clock : forall (v : word) (m : Model),
  m_sigabrt_pending (with_clock v m) = m_sigabrt_pending m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigabrt_pending_with_clock : model.

Lemma m_sigabrt_pending_with_accepted : forall (v : list (word * FdEntry)) (m : Model),
  m_sigabrt_pending (with_accepted v m) = m_sigabrt_pending m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigabrt_pending_with_accepted : model.

Lemma m_sigabrt_pending_with_abort_terminal : forall (v : bool) (m : Model),
  m_sigabrt_pending (with_abort_terminal v m) = m_sigabrt_pending m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigabrt_pending_with_abort_terminal : model.

Lemma m_sigabrt_pending_with_sigabrt_pending : forall (m : Model),
  m_sigabrt_pending (with_sigabrt_pending m) = true.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigabrt_pending_with_sigabrt_pending : model.

Lemma m_sigabrt_pending_with_killed : forall (v : word) (m : Model),
  m_sigabrt_pending (with_killed v m) = m_sigabrt_pending m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigabrt_pending_with_killed : model.

Lemma m_abort_terminal_with_fds : forall (v : list (word * FdEntry)) (m : Model),
  m_abort_terminal (with_fds v m) = m_abort_terminal m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_abort_terminal_with_fds : model.

Lemma m_abort_terminal_with_pipes : forall (v : list (word * PipeBuf)) (m : Model),
  m_abort_terminal (with_pipes v m) = m_abort_terminal m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_abort_terminal_with_pipes : model.

Lemma m_abort_terminal_with_vmmaps : forall (v : VmMaps) (m : Model),
  m_abort_terminal (with_vmmaps v m) = m_abort_terminal m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_abort_terminal_with_vmmaps : model.

Lemma m_abort_terminal_with_vm_backing : forall (lz : list (word * word)) (mt : list word) (m : Model),
  m_abort_terminal (with_vm_backing lz mt m) = m_abort_terminal m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_abort_terminal_with_vm_backing : model.

Lemma m_abort_terminal_with_stdin : forall (v : InputStream) (m : Model),
  m_abort_terminal (with_stdin v m) = m_abort_terminal m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_abort_terminal_with_stdin : model.

Lemma m_abort_terminal_with_urandom : forall (v : InputStream) (m : Model),
  m_abort_terminal (with_urandom v m) = m_abort_terminal m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_abort_terminal_with_urandom : model.

Lemma m_abort_terminal_with_net : forall (v : NetQueue) (m : Model),
  m_abort_terminal (with_net v m) = m_abort_terminal m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_abort_terminal_with_net : model.

Lemma m_abort_terminal_with_fs : forall (v : Fs.Fs) (m : Model),
  m_abort_terminal (with_fs v m) = m_abort_terminal m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_abort_terminal_with_fs : model.

Lemma m_abort_terminal_with_halted : forall (v : word) (m : Model),
  m_abort_terminal (with_halted v m) = m_abort_terminal m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_abort_terminal_with_halted : model.

Lemma m_abort_terminal_with_tid : forall (v : word) (m : Model),
  m_abort_terminal (with_tid v m) = m_abort_terminal m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_abort_terminal_with_tid : model.

Lemma m_abort_terminal_with_rlimit_core : forall (v : list byte) (m : Model),
  m_abort_terminal (with_rlimit_core v m) = m_abort_terminal m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_abort_terminal_with_rlimit_core : model.

Lemma m_abort_terminal_with_utsname : forall (v : list byte) (m : Model),
  m_abort_terminal (with_utsname v m) = m_abort_terminal m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_abort_terminal_with_utsname : model.

Lemma m_abort_terminal_with_nofile : forall (v : word) (m : Model),
  m_abort_terminal (with_nofile v m) = m_abort_terminal m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_abort_terminal_with_nofile : model.

Lemma m_abort_terminal_with_creds : forall (v : Creds) (m : Model),
  m_abort_terminal (with_creds v m) = m_abort_terminal m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_abort_terminal_with_creds : model.

Lemma m_abort_terminal_with_setsid_succeeded : forall (m : Model),
  m_abort_terminal (with_setsid_succeeded m) = m_abort_terminal m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_abort_terminal_with_setsid_succeeded : model.

Lemma m_abort_terminal_with_children : forall (m : Model),
  m_abort_terminal (with_children m) = m_abort_terminal m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_abort_terminal_with_children : model.

Lemma m_abort_terminal_with_sigmask : forall (v : word) (m : Model),
  m_abort_terminal (with_sigmask v m) = m_abort_terminal m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_abort_terminal_with_sigmask : model.

Lemma m_abort_terminal_with_clock : forall (v : word) (m : Model),
  m_abort_terminal (with_clock v m) = m_abort_terminal m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_abort_terminal_with_clock : model.

Lemma m_abort_terminal_with_accepted : forall (v : list (word * FdEntry)) (m : Model),
  m_abort_terminal (with_accepted v m) = m_abort_terminal m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_abort_terminal_with_accepted : model.

Lemma m_abort_terminal_with_abort_terminal : forall (v : bool) (m : Model),
  m_abort_terminal (with_abort_terminal v m) = v.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_abort_terminal_with_abort_terminal : model.

Lemma m_abort_terminal_with_sigabrt_pending : forall (m : Model),
  m_abort_terminal (with_sigabrt_pending m) = m_abort_terminal m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_abort_terminal_with_sigabrt_pending : model.

Lemma m_abort_terminal_with_killed : forall (v : word) (m : Model),
  m_abort_terminal (with_killed v m) = m_abort_terminal m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_abort_terminal_with_killed : model.

(** The cross pairs the two changes that added fields to [ProcState]
    owe each other: the alternate-stack bit against the three abort
    fields' setters, and each of those against its setter.  Same
    [reflexivity], same reason -- every setter rebuilds [ProcState] and
    carries what it does not write. *)
Lemma m_killed_with_sigaltstack_installed : forall (m : Model),
  m_killed (with_sigaltstack_installed m) = m_killed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_killed_with_sigaltstack_installed : model.

Lemma m_sigabrt_pending_with_sigaltstack_installed : forall (m : Model),
  m_sigabrt_pending (with_sigaltstack_installed m) = m_sigabrt_pending m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigabrt_pending_with_sigaltstack_installed : model.

Lemma m_abort_terminal_with_sigaltstack_installed : forall (m : Model),
  m_abort_terminal (with_sigaltstack_installed m) = m_abort_terminal m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_abort_terminal_with_sigaltstack_installed : model.

Lemma m_sigaltstack_installed_with_killed : forall (v : word) (m : Model),
  m_sigaltstack_installed (with_killed v m) = m_sigaltstack_installed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigaltstack_installed_with_killed : model.

Lemma m_sigaltstack_installed_with_sigabrt_pending : forall (m : Model),
  m_sigaltstack_installed (with_sigabrt_pending m) = m_sigaltstack_installed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigaltstack_installed_with_sigabrt_pending : model.

Lemma m_sigaltstack_installed_with_abort_terminal : forall (v : bool) (m : Model),
  m_sigaltstack_installed (with_abort_terminal v m) = m_sigaltstack_installed m.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigaltstack_installed_with_abort_terminal : model.

Lemma m_sigaltstack_installed_init_model : forall reserved brk0 mbase sp lim inp,
  m_sigaltstack_installed (init_model reserved brk0 mbase sp lim inp) = false.
Proof. reflexivity. Qed.

Lemma m_fds_init_model : forall reserved brk0 mbase sp lim inp,
  m_fds (init_model reserved brk0 mbase sp lim inp) =
  [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
     (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
     (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ].
Proof. reflexivity. Qed.


Lemma m_vmmaps_init_model : forall reserved brk0 mbase sp lim inp,
  m_vmmaps (init_model reserved brk0 mbase sp lim inp) =
  mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp.
Proof. reflexivity. Qed.

(** The grant bound of the model a run starts from, in the form the
    examples reason in: [sp] is the section's quantified stack pointer,
    so [lia] closes every bound from [Hsp_lo]/[Hsp_hi].  In the [model]
    rewrite base, unlike its neighbours, because nothing matches on an
    unreduced [alloc_top]. *)
Lemma alloc_top_init : forall reserved brk0 mbase sp lim inp,
  alloc_top (m_vmmaps (init_model reserved brk0 mbase sp lim inp))
  = (bv_unsigned sp - stack_max_size)%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite alloc_top_init : model.

(** A run starts with nothing mapped, no lazy reservation and no page
    materialized, so no backing is charged yet.  Stated over the whole
    [Model] because [vm_backing_used] reads the sparse ledgers in
    [VmState] as well as [vm_maps]; a site that needs the budget conjunct
    of a grant check at the initial model names this rather than trying to
    reduce [vm_backing_used] through the opaque accessors. *)
Lemma vm_backing_used_init_model : forall reserved brk0 mbase sp lim inp,
  vm_backing_used (init_model reserved brk0 mbase sp lim inp) = 0%Z.
Proof. reflexivity. Qed.


Lemma m_stdin_init_model : forall reserved brk0 mbase sp lim inp,
  m_stdin (init_model reserved brk0 mbase sp lim inp) =
  in_stdin inp.
Proof. reflexivity. Qed.

Lemma m_urandom_init_model : forall reserved brk0 mbase sp lim inp,
  m_urandom (init_model reserved brk0 mbase sp lim inp) =
  in_urandom inp.
Proof. reflexivity. Qed.


Lemma m_fs_init_model : forall reserved brk0 mbase sp lim inp,
  m_fs (init_model reserved brk0 mbase sp lim inp) =
  in_fs inp.
Proof. reflexivity. Qed.


Lemma m_halted_init_model : forall reserved brk0 mbase sp lim inp,
  m_halted (init_model reserved brk0 mbase sp lim inp) =
  None.
Proof. reflexivity. Qed.


Lemma m_tid_init_model : forall reserved brk0 mbase sp lim inp,
  m_tid (init_model reserved brk0 mbase sp lim inp) =
  None.
Proof. reflexivity. Qed.


Lemma m_rlimit_core_init_model : forall reserved brk0 mbase sp lim inp,
  m_rlimit_core (init_model reserved brk0 mbase sp lim inp) =
  None.
Proof. reflexivity. Qed.

Lemma m_nofile_init_model : forall reserved brk0 mbase sp lim inp,
  m_nofile (init_model reserved brk0 mbase sp lim inp) = in_nofile inp.
Proof. reflexivity. Qed.

Lemma m_clock_init_model : forall reserved brk0 mbase sp lim inp,
  m_clock (init_model reserved brk0 mbase sp lim inp) =
  Z_to_bv 64 0.
Proof. reflexivity. Qed.

Lemma m_net_init_model : forall reserved brk0 mbase sp lim inp,
  m_net (init_model reserved brk0 mbase sp lim inp) = in_net inp.
Proof. reflexivity. Qed.


Lemma m_conn_ix_init_model : forall reserved brk0 mbase sp lim inp,
  m_conn_ix (init_model reserved brk0 mbase sp lim inp) = Z_to_bv 64 0.
Proof. reflexivity. Qed.


Lemma m_creds_init_model : forall reserved brk0 mbase sp lim inp,
  m_creds (init_model reserved brk0 mbase sp lim inp) =
  mkCreds (in_uid inp) (in_uid inp) (in_uid inp)
          (in_gid inp) (in_gid inp) (in_gid inp) (in_groups inp).
Proof. reflexivity. Qed.

Lemma m_sigmask_init_model : forall reserved brk0 mbase sp lim inp,
  m_sigmask (init_model reserved brk0 mbase sp lim inp) = in_sigmask inp.
Proof. reflexivity. Qed.

Lemma m_setsid_succeeded_init_model : forall reserved brk0 mbase sp lim inp,
  m_setsid_succeeded (init_model reserved brk0 mbase sp lim inp) =
  false.
Proof. reflexivity. Qed.

Lemma m_killed_init_model : forall reserved brk0 mbase sp lim inp,
  m_killed (init_model reserved brk0 mbase sp lim inp) = None.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_killed_init_model : model.

Lemma m_sigabrt_pending_init_model : forall reserved brk0 mbase sp lim inp,
  m_sigabrt_pending (init_model reserved brk0 mbase sp lim inp) = false.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_sigabrt_pending_init_model : model.

(** The declaration arrives from the input and is the only one of the
    three that a run can start with either value of. *)
Lemma m_abort_terminal_init_model : forall reserved brk0 mbase sp lim inp,
  m_abort_terminal (init_model reserved brk0 mbase sp lim inp)
    = in_abort_terminal inp.
Proof. reflexivity. Qed.
#[export] Hint Rewrite m_abort_terminal_init_model : model.

Lemma m_pipes_init_model : forall reserved brk0 mbase sp lim inp,
  m_pipes (init_model reserved brk0 mbase sp lim inp) =
  [].
Proof. reflexivity. Qed.
