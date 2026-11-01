(** * StackLayout — Linux process initial stack builder

    TRUST BOUNDARY: this file is part of the trusted specification.

    Addresses are [word = bv 64], stack bytes are [byte = bv 8].  Auxv
    types/values are word constants, serialized via [BvBase.word_le8].

    Builds the byte sequence Linux v6.18.46 (commit 1f99e9ab748f) places
    on the stack at process startup, from the stack VMA's top DOWN to
    the entry stack pointer: the eight-byte slot
    [create_init_stack_vma] skips (mm/vma_exec.c), the exec file name
    and the envp and argv strings [do_execveat_common] copies
    (fs/exec.c), the pad [arch_align_stack] leaves
    (arch/riscv/kernel/process.c), the sixteen AT_RANDOM bytes, the
    auxiliary vector, and the argv and envp pointer arrays with argc
    ([create_elf_tables], fs/binfmt_elf.c).

    WHERE THE SHAPE COMES FROM, in the kernel's own order.  The model is
    an exact transcription of these four steps; [Run.entry_launch_ok_va]
    states the arithmetic they leave free and this file lays the bytes.

    1. [create_init_stack_vma] (mm/vma_exec.c) sets
       [bprm->p] to [vma->vm_end] less the size of a pointer, so the top eight bytes
       of the stack VMA are never written.
    2. [do_execveat_common] (fs/exec.c) copies [bprm->filename] first
       ([copy_string_kernel]), records [bprm->exec = bprm->p] — the
       value AT_EXECFN carries — then the envp strings, then the argv
       strings, each with [copy_strings] working DOWN.  So from the top:
       the eight-byte slot, the file name and its NUL, the envp strings,
       the argv strings; [argv[0]] is the lowest string byte.
    3. [create_elf_tables] (fs/binfmt_elf.c) takes the sixteen
       [get_random_bytes] bytes off the bottom of the string area with
       [STACK_ALLOC], applies [arch_align_stack] (it subtracts 0 to
       4095 bytes and then masks the low four bits, so the pad it
       leaves is up to 4110), lays [ei_index] auxv words below
       that with [STACK_ADD], and rounds down with
       [STACK_ROUND(sp, items)], [items = (argc + 1) + (envc + 1) + 1].
    4. The vector itself is [ARCH_DLINFO]
       (arch/riscv/include/asm/elf.h) followed by [create_elf_tables]'s
       own unconditional entries, in the order [auxv_entries] lists. *)

From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType Vdso.
Import ListNotations.
Open Scope bv_scope.

Fixpoint string_addrs (base : word) (strs : list (list byte))
    : list word * word :=
  match strs with
  | [] => ([], base)
  | s :: rest =>
    let next := base + len_word s + 1 in
    let '(ptrs, final) := string_addrs next rest in
    (base :: ptrs, final)
  end.

Definition flatten_strings (strs : list (list byte)) : list byte :=
  flat_map (fun s => s ++ [Z_to_bv 8 0]) strs.

(** ** The auxv types this launch publishes

    Values from include/uapi/linux/auxvec.h and
    arch/riscv/include/uapi/asm/auxvec.h, Linux v6.18.46 (commit
    1f99e9ab748f). *)
Definition AT_NULL    : word := Z_to_bv 64 0.
Definition AT_PHDR    : word := Z_to_bv 64 3.
Definition AT_PHENT   : word := Z_to_bv 64 4.
Definition AT_PHNUM   : word := Z_to_bv 64 5.
Definition AT_PAGESZ  : word := Z_to_bv 64 6.
Definition AT_BASE    : word := Z_to_bv 64 7.
Definition AT_FLAGS   : word := Z_to_bv 64 8.
Definition AT_ENTRY   : word := Z_to_bv 64 9.
Definition AT_UID     : word := Z_to_bv 64 11.
Definition AT_EUID    : word := Z_to_bv 64 12.
Definition AT_GID     : word := Z_to_bv 64 13.
Definition AT_EGID    : word := Z_to_bv 64 14.
Definition AT_HWCAP   : word := Z_to_bv 64 16.
Definition AT_CLKTCK  : word := Z_to_bv 64 17.
Definition AT_SECURE  : word := Z_to_bv 64 23.
Definition AT_RANDOM  : word := Z_to_bv 64 25.
Definition AT_RSEQ_FEATURE_SIZE : word := Z_to_bv 64 27.
Definition AT_RSEQ_ALIGN        : word := Z_to_bv 64 28.
Definition AT_EXECFN  : word := Z_to_bv 64 31.
Definition AT_SYSINFO_EHDR      : word := Z_to_bv 64 33.
Definition AT_L1I_CACHESIZE     : word := Z_to_bv 64 40.
Definition AT_L1I_CACHEGEOMETRY : word := Z_to_bv 64 41.
Definition AT_L1D_CACHESIZE     : word := Z_to_bv 64 42.
Definition AT_L1D_CACHEGEOMETRY : word := Z_to_bv 64 43.
Definition AT_L2_CACHESIZE      : word := Z_to_bv 64 44.
Definition AT_L2_CACHEGEOMETRY  : word := Z_to_bv 64 45.
Definition AT_L3_CACHESIZE      : word := Z_to_bv 64 46.
Definition AT_L3_CACHEGEOMETRY  : word := Z_to_bv 64 47.
Definition AT_MINSIGSTKSZ       : word := Z_to_bv 64 51.

(** ** The two AT_HWCAP masks this model admits

    [hwcap_rv64gc] is the bit for each of the six single-letter
    extensions the model's own decoder implements — A, C, D, F, I and M
    — and [hwcap_rv64gcv] is that mask with V added.  The bit for a
    letter X is [1 << (X - 'A')] (arch/riscv/include/uapi/asm/hwcap.h,
    the [COMPAT_HWCAP_ISA_*] macros, Linux v6.18.46, commit
    1f99e9ab748f), so A=0x1, C=0x4, D=0x8, F=0x20, I=0x100, M=0x1000 and
    V=0x200000. *)
Definition hwcap_rv64gc  : word := Z_to_bv 64 0x112D.
Definition hwcap_rv64gcv : word := Z_to_bv 64 0x20112D.

(** ** The eight cache words

    [ARCH_DLINFO] (arch/riscv/include/asm/elf.h) emits a size and a
    geometry word for each of four leaves — L1 instruction, L1 data, L2
    unified, L3 unified — from [get_cache_size] and
    [get_cache_geometry] (arch/riscv/kernel/cacheinfo.c).  A leaf the
    machine does not report gives two zero words.

    The words are carried as a record rather than a list so that the
    vector's LENGTH is fixed by the type: every address in the block
    below is a function of (sp, the stack top, argv, envp, the exec
    name, CONFIG_RSEQ), and nothing a machine reports can move one.
    [State.cache_words_of] derives the record from the launch's four
    [State.CacheLeaf] facts with the kernel's own formulas. *)
Record CacheWords := mkCacheWords {
  cw_l1i_size : word;
  cw_l1i_geom : word;
  cw_l1d_size : word;
  cw_l1d_geom : word;
  cw_l2_size  : word;
  cw_l2_geom  : word;
  cw_l3_size  : word;
  cw_l3_geom  : word
}.

Definition cache_words_zero : CacheWords :=
  let z := Z_to_bv 64 0 in mkCacheWords z z z z z z z z.

(** ** What the LAUNCH, rather than the image or the caller, puts in the
       vector

    Four facts of the machine and of the kernel build that reach the
    auxv and nothing else in this file.  [Run.launch_auxv] derives them
    from [State.KernelBuild] and the entry's mmap base; they are
    arguments here so that this file stays free of [State].

    - [la_sysinfo_ehdr]: AT_SYSINFO_EHDR, the address of the vDSO text.
      [__setup_additional_pages] (arch/riscv/kernel/vdso.c) maps the
      vvar pages and the text directly below the mmap base, and
      [ARCH_DLINFO] publishes [mm->context.vdso], the text's start.
    - [la_cache]: the eight words above.
    - [la_minsigstksz]: AT_MINSIGSTKSZ, [get_min_sigframe_size()]
      (arch/riscv/kernel/signal.c) — [round_up(F + V, 16)] with F the
      size of [struct rt_sigframe] and V the vector context
      ([init_rt_signal_env], [get_rt_frame_size]).
    - [la_rseq]: the kernel has CONFIG_RSEQ (init/Kconfig; riscv64
      selects HAVE_RSEQ in arch/riscv/Kconfig and the option defaults to
      y), so [create_elf_tables] emits AT_RSEQ_FEATURE_SIZE and
      AT_RSEQ_ALIGN.  It is the ONE fact that moves the vector's length,
      which is why [auxv_count] and every address below take it. *)
Record LaunchAuxv := mkLaunchAuxv {
  la_sysinfo_ehdr : word;
  la_cache        : CacheWords;
  la_minsigstksz  : word;
  la_rseq         : bool
}.

(** The auxiliary vector, in the order [create_elf_tables] writes it.

    [ARCH_DLINFO] comes FIRST — fs/binfmt_elf.c expands it before its
    own entries, with the comment "ARCH_DLINFO must come first so PPC
    can do its special alignment of AUXV" — and on riscv64 it is ten
    entries: AT_SYSINFO_EHDR, the eight cache words, AT_MINSIGSTKSZ.
    Then [create_elf_tables]'s unconditional sixteen, then the
    CONFIG_RSEQ pair, then AT_NULL.  Twenty-seven entries, or
    twenty-nine with CONFIG_RSEQ.

    Entries this launch does NOT carry, and why each is absent rather
    than wrong:

    - AT_HWCAP2, AT_HWCAP3, AT_HWCAP4: riscv64 defines no [ELF_HWCAP2],
      [ELF_HWCAP3] or [ELF_HWCAP4], so the [#ifdef]s around those three
      [NEW_AUX_ENT] lines are false.
    - AT_PLATFORM and AT_BASE_PLATFORM: emitted only when
      [ELF_PLATFORM] / [ELF_BASE_PLATFORM] are defined, which riscv64
      does not define.
    - AT_EXECFD: emitted only for [bprm->have_execfd], which
      [binfmt_misc] and the script loader set.  SCOPE.md's assumption
      that [execve] loads the file directly excludes both.
    - AT_NOTELF, AT_IGNORE: never emitted by this loader.

    The VALUES that are constants here, each with its source:

    - AT_PAGESZ is [ELF_EXEC_PAGESIZE] = [PAGE_SIZE] = 4096
      (arch/riscv/include/asm/page.h, with CONFIG_RISCV_4K_PAGES).
    - AT_CLKTCK is [USER_HZ] = 100 (include/asm-generic/param.h; riscv
      has no asm/param.h of its own).
    - AT_PHENT is [sizeof(struct elf_phdr)] = 56 for ELF64, and
      [load_elf_phdrs] (fs/binfmt_elf.c) refuses an image whose
      [e_phentsize] is anything else, so the model's [PhdrInfo] carries
      the same number.
    - AT_BASE is [interp_load_addr], which is 0 for an image with no
      PT_INTERP — SCOPE.md's static [ET_EXEC] assumption.
    - AT_FLAGS is 0: [create_elf_tables] writes the literal.
    - AT_SECURE is [bprm->secureexec], 0 here.  [State.ProcInput] has no
      effective-id field, so [State.init_model] derives the effective
      and saved ids from the real ones and a set-id launch cannot be
      stated; SCOPE.md records the matching assumption that no file
      capability and no LSM transition asks for secure mode
      (security/commoncap.c [cap_bprm_creds_from_file],
      security/selinux/hooks.c).
    - AT_RSEQ_FEATURE_SIZE is [offsetof(struct rseq, end)] = 28 and
      AT_RSEQ_ALIGN is [__alignof__(struct rseq)] = 32
      (include/uapi/linux/rseq.h).

    AT_UID and AT_EUID both carry [uid], AT_GID and AT_EGID both carry
    [gid], for the reason AT_SECURE is 0: the model cannot express a
    launch whose effective id differs from its real one, so musl's
    [__init_libc] reads [libc.secure = 0] and its secure-exec path —
    which probes and sanitizes fds 0-2 with syscalls outside
    [Specs.modeled_sysnos] — stays dead code.  [Kernel.Sys.getid_spec]
    reads the same [State.in_uid] and [State.in_gid], so a program that
    compares its auxv with [getuid] gets the agreement every kernel
    gives.

    AT_RANDOM's sixteen bytes are the run's own draw, not a constant:
    [create_elf_tables] calls
    [get_random_bytes(k_rand_bytes, sizeof(k_rand_bytes))] on every
    [execve].  The model quantifies over them through [ed_random], a
    [bv 128] with no validity clause, independently per binary in
    [Equivalence.strong_universal_T], so a binary that echoes them is a
    binary no equivalence proof can close. *)
Definition auxv_entries (la : LaunchAuxv) (ph : PhdrInfo) (entry : word)
    (uid gid hwcap at_random at_execfn : word) : list (word * word) :=
  let c := la_cache la in
  [ (AT_SYSINFO_EHDR,      la_sysinfo_ehdr la);
    (AT_L1I_CACHESIZE,     cw_l1i_size c);
    (AT_L1I_CACHEGEOMETRY, cw_l1i_geom c);
    (AT_L1D_CACHESIZE,     cw_l1d_size c);
    (AT_L1D_CACHEGEOMETRY, cw_l1d_geom c);
    (AT_L2_CACHESIZE,      cw_l2_size c);
    (AT_L2_CACHEGEOMETRY,  cw_l2_geom c);
    (AT_L3_CACHESIZE,      cw_l3_size c);
    (AT_L3_CACHEGEOMETRY,  cw_l3_geom c);
    (AT_MINSIGSTKSZ,       la_minsigstksz la);
    (AT_HWCAP,  hwcap);
    (AT_PAGESZ, Z_to_bv 64 4096);
    (AT_CLKTCK, Z_to_bv 64 100);
    (AT_PHDR,   Z_to_bv 64 (Z.of_N (ph_addr ph)));
    (AT_PHENT,  Z_to_bv 64 (Z.of_N (ph_ent ph)));
    (AT_PHNUM,  Z_to_bv 64 (Z.of_N (ph_num ph)));
    (AT_BASE,   Z_to_bv 64 0);
    (AT_FLAGS,  Z_to_bv 64 0);
    (AT_ENTRY,  entry);
    (AT_UID,    uid);
    (AT_EUID,   uid);
    (AT_GID,    gid);
    (AT_EGID,   gid);
    (AT_SECURE, Z_to_bv 64 0);
    (AT_RANDOM, at_random);
    (AT_EXECFN, at_execfn) ]
  ++ (if la_rseq la
      then [ (AT_RSEQ_FEATURE_SIZE, Z_to_bv 64 28);
             (AT_RSEQ_ALIGN,        Z_to_bv 64 32) ]
      else [])
  ++ [ (AT_NULL, Z_to_bv 64 0) ].

(** Serialize an auxv: each entry is two little-endian 64-bit words. *)
Definition build_auxv (entries : list (word * word)) : list byte :=
  flat_map (fun e => word_le8 (fst e) ++ word_le8 (snd e)) entries.

Definition auxv_bytes (la : LaunchAuxv) (ph : PhdrInfo) (entry : word)
    (uid gid hwcap at_random at_execfn : word) : list byte :=
  build_auxv (auxv_entries la ph entry uid gid hwcap at_random at_execfn).

(** The vector's entry count and byte size.  CONFIG_RSEQ is the only
    thing that moves either: [PhdrInfo] fills three values, the
    credentials four, [hwcap] one, the launch ten, and no argument but
    [la_rseq] adds or removes an entry. *)
Definition auxv_count (rseq : bool) : nat := if rseq then 29%nat else 27%nat.
Definition auxv_size (rseq : bool) : nat := (16 * auxv_count rseq)%nat.

Lemma length_auxv_bytes : forall la ph entry uid gid hwcap ar ae,
  length (auxv_bytes la ph entry uid gid hwcap ar ae)
  = auxv_size (la_rseq la).
Proof.
  intros [ehdr c msz [|]] ph entry uid gid hwcap ar ae; reflexivity.
Qed.

(** …and the size does not move with the hart, with the machine's
    caches, or with the vDSO's address: the arguments other than
    [la_rseq] change the CONTENTS of value slots and nothing else.
    Stated separately from [length_auxv_bytes] because it is the
    property the addressing argument rests on. *)
Lemma length_auxv_bytes_value_invariant :
  forall la la' ph ph' e e' u u' g g' h h' ar ar' ae ae',
  la_rseq la = la_rseq la' ->
  length (auxv_bytes la ph e u g h ar ae)
  = length (auxv_bytes la' ph' e' u' g' h' ar' ae').
Proof.
  intros [ehdr c msz r] [ehdr' c' msz' r'] ph ph' e e' u u' g g' h h' ar ar' ae ae' Hr.
  cbn in Hr; subst r'. destruct r; reflexivity.
Qed.

(** ** What [execve] drew for this process's entry, and where it put the
       stack

    [Run.ExecEntry]'s [en_draw], beside the three placement draws
    [en_sp], [en_brk] and [en_mmap_base].

    - [ed_random]: the sixteen bytes AT_RANDOM points at
      ([get_random_bytes] in [create_elf_tables], fs/binfmt_elf.c).  No
      validity clause: every 128-bit value is a draw the kernel can
      make and every draw is a 128-bit value.

    - [ed_top]: the stack VMA's [vm_end].  [setup_arg_pages]
      (fs/exec.c) fixes it with
      [stack_top = arch_align_stack(randomize_stack_top(STACK_TOP));
       stack_top = PAGE_ALIGN(stack_top);], so it is a page-aligned
      address at most 2^30 below STACK_TOP
      ([Run.valid_stack_top_va] states the exact set).  It is the
      block's upper end: every byte from [en_sp] to [ed_top] is laid
      here, and there is no slack.

    - [ed_vdso]: what a vDSO call leaves behind.  LPS applies the
      exported function's syscall specification in ONE step rather than
      running the image's instructions, so the caller-saved registers
      other than a0, and the bytes of [sp - F, sp) the call's frame
      used, are the environment's choice.  The arguments are the index
      of the call in the run, the register values before it, the frame
      bytes before it, and the call's result, so a choice that keeps an
      unwritten value gives a run Linux also gives.  Quantified per
      binary, as [ed_random] is.

    [ed_slack] is GONE.  It carried the bytes of the entry stack's last
    page above the model's own shorter block; the block now runs to
    [ed_top], so there is nothing above it to choose. *)
Record EntryDraw := mkDraw {
  ed_random : bv 128;
  ed_top    : word;
  ed_vdso   : VdsoDraw
    (* WHAT A vDSO CALL LEAVES BEHIND: from the index of the call in
       the run, the caller-saved registers before it, the bytes of
       [[sp - F, sp)] before it and the call's result, to the
       caller-saved registers and those bytes after it.  F is the
       chosen image's largest frame ([Vdso.vi_frame]).

       It is part of the DRAW, beside [ed_random], for the same reason
       that one is: Linux's answer is what the vDSO's compiled code
       left, a function of the same inputs and of time values this
       model lets the environment choose, and the model has no term for
       that code.  Drawing it once per launch — rather than afresh at
       each call — is what makes two calls with the same inputs leave
       the same bytes, as they do on a real run; the call's INDEX is an
       argument so that two calls that are not the same call still may
       differ.  [Run.init_config] copies it into the model, where
       [Run.sstep]'s vDSO arm reads it.

       Its result is [Vdso.VdsoLeftovers] rather than a bare pair, so
       that the registers and the frame bytes are named where they are
       read; [Vdso.vdso_draw_keep] is the draw that gives back what the
       call started with, which is one Linux also gives. *)
}.

(** The sixteen bytes AT_RANDOM points at, serialized little-endian.
    The draw is a [bv 128] rather than a list so the LENGTH is fixed by
    the type and no statement that quantifies over an entry grows a side
    condition. *)
Definition at_random_bytes (rnd : bv 128) : list byte :=
  [ bv_extract 0 8 rnd;    bv_extract 8 8 rnd;
    bv_extract 16 8 rnd;   bv_extract 24 8 rnd;
    bv_extract 32 8 rnd;   bv_extract 40 8 rnd;
    bv_extract 48 8 rnd;   bv_extract 56 8 rnd;
    bv_extract 64 8 rnd;   bv_extract 72 8 rnd;
    bv_extract 80 8 rnd;   bv_extract 88 8 rnd;
    bv_extract 96 8 rnd;   bv_extract 104 8 rnd;
    bv_extract 112 8 rnd;  bv_extract 120 8 rnd ].

Lemma length_at_random_bytes : forall rnd, length (at_random_bytes rnd) = 16%nat.
Proof. reflexivity. Qed.

(* =========================================================================
   The block's measurements
   ========================================================================= *)

(** [items] in [create_elf_tables]: [(argc + 1) + (envc + 1) + 1], the
    pointer-sized slots below the auxv — argc, the argv pointers and
    their NULL, the envp pointers and their NULL. *)
Definition block_items (argv envp : list (list byte)) : nat :=
  (length argv + length envp + 3)%nat.

(** C, the distance from the entry stack pointer to the TOP of the
    sixteen AT_RANDOM bytes.

    [create_elf_tables] lays the block downwards from the random bytes:
    [sp = STACK_ADD(p, ei_index)] subtracts [16 * n_aux] from their
    address, [STACK_ROUND(sp, items)] subtracts [8 * items] and then
    clears the low four bits.  The random bytes sit at a 16-aligned
    address ([arch_align_stack] returns one) and [16 * n_aux] is a
    multiple of 16, so the mask removes exactly
    [8 * (items mod 2)] further bytes — which is the zero gap between
    the end of the vector and the random bytes. *)
Definition block_head_size (rseq : bool) (argv envp : list (list byte)) : nat :=
  let items := block_items argv envp in
  (8 * items + auxv_size rseq + 8 * (items mod 2) + 16)%nat.

(** L, the string bytes with their NULs: the argv strings, the envp
    strings and the exec file name, each NUL-terminated
    ([copy_strings] and [copy_string_kernel], fs/exec.c). *)
Definition launch_string_bytes (argv envp : list (list byte))
    (execfn : list byte) : nat :=
  (length (flatten_strings argv) + length (flatten_strings envp)
   + length execfn + 1)%nat.

(** The lowest string byte — [argv[0]], which [create_elf_tables]
    publishes as [mm->arg_start] and the first argv pointer.  The eight
    bytes below [top] are the slot [create_init_stack_vma] skipped. *)
Definition string_base_addr (top : word) (argv envp : list (list byte))
    (execfn : list byte) : word :=
  top - nat_to_word (8 + launch_string_bytes argv envp execfn).

(** AT_EXECFN: [bprm->exec], the address [do_execveat_common] records
    right after [copy_string_kernel] has put the file name at the top of
    the string area. *)
Definition at_execfn_ptr (top : word) (execfn : list byte) : word :=
  top - nat_to_word (8 + length execfn + 1).

(** AT_RANDOM: the bottom of the sixteen bytes, [C - 16] above sp. *)
Definition at_random_ptr (sp : word) (rseq : bool)
    (argv envp : list (list byte)) : word :=
  sp + nat_to_word (block_head_size rseq argv envp - 16).

(** The pad [arch_align_stack] left between the sixteen AT_RANDOM
    bytes and the lowest string byte: whatever is left of
    [top - sp] once the head [C], the strings [L] and the eight-byte
    slot are taken out.

    Clamped at 0 by [Z.to_nat], so the block is defined for every [sp]
    and [top].  Under [Run.entry_launch_ok_va] it is between 0 and
    4095, which is the range [arch_align_stack]
    (arch/riscv/kernel/process.c, Linux v6.18.46, commit 1f99e9ab748f)
    can leave. *)
Definition block_pad_len (rseq : bool) (sp top : word)
    (argv envp : list (list byte)) (execfn : list byte) : nat :=
  Z.to_nat (bv_unsigned top - 8
            - Z.of_nat (launch_string_bytes argv envp execfn)
            - bv_unsigned sp
            - Z.of_nat (block_head_size rseq argv envp)).

(* =========================================================================
   The block
   ========================================================================= *)

(** The initial stack image, from the entry stack pointer [sp] to the
    stack VMA's end [top].  Linux's layout, bottom to top:

      argc, the argv pointers, NULL, the envp pointers, NULL   8*items
      the auxiliary vector                                     16*n_aux
      zero gap, so the random bytes land 16-aligned            0 or 8
      the sixteen AT_RANDOM bytes                              16
      the pad [arch_align_stack] left                          0..4110
      the argv strings, the envp strings, the exec name + NUL  L
      the slot [create_init_stack_vma] skipped                 8

    The pads are ZERO because Linux never writes them: the stack's pages
    are fresh anonymous pages ([get_arg_page], fs/exec.c).

    The pad's length is whatever is left, clamped at 0 by [Z.to_nat], so
    the definition is total for every [sp] and [top].  Under
    [Run.entry_launch_ok_va] it is between 0 and 4110 and the image's
    length is exactly [top - sp]
    ([Run.length_entry_stack_image_launch]).

    WHY 4110 AND NOT 4095.  [arch_align_stack]
    (arch/riscv/kernel/process.c, Linux v6.18.46, commit 1f99e9ab748f)
    subtracts [r] in [0, 4095] AND THEN masks the low four bits, so the
    distance from the lowest string byte down to the top of the
    AT_RANDOM block is [r + ((top - 8 - L - r) mod 16)], at most
    [4095 + 15].  The 4095 is the kernel's draw; the pad is the draw
    plus the alignment remainder.  [Run.launch_sp_lo] and
    [Run.launch_sp_hi] are stated with [align_down16] and so carry the
    true range without naming either number.

    [rnd] is read by NOTHING but the sixteen-byte block
    ([build_stack_bytes_split_random]): every address here is a function
    of (sp, top, argv, envp, the exec name, [la_rseq]) alone. *)
Definition build_stack_bytes (la : LaunchAuxv) (ph : PhdrInfo) (entry : word)
    (sp top : word) (argv envp : list (list byte)) (execfn : list byte)
    (uid gid hwcap : word) (draw : EntryDraw) : list byte :=
  let items := block_items argv envp in
  let sbase := string_base_addr top argv envp execfn in
  let '(argv_ptrs, env_str_base) := string_addrs sbase argv in
  let '(envp_ptrs, _) := string_addrs env_str_base envp in
  let auxv :=
    auxv_bytes la ph entry uid gid hwcap
      (at_random_ptr sp (la_rseq la) argv envp)
      (at_execfn_ptr top execfn) in
  let head :=
    word_le8 (len_word argv)
    ++ flat_map word_le8 argv_ptrs
    ++ word_le8 (Z_to_bv 64 0)
    ++ flat_map word_le8 envp_ptrs
    ++ word_le8 (Z_to_bv 64 0)
    ++ auxv
    ++ repeat (Z_to_bv 8 0) (8 * (items mod 2))
    ++ at_random_bytes (ed_random draw) in
  let strs :=
    flatten_strings argv ++ flatten_strings envp ++ execfn ++ [Z_to_bv 8 0] in
  let pad := block_pad_len (la_rseq la) sp top argv envp execfn in
  head ++ repeat (Z_to_bv 8 0) pad ++ strs ++ repeat (Z_to_bv 8 0) 8.

(** The pointer list [string_addrs] returns has one entry per string:
    the addresses are a function of the base and the lengths, not of
    the bytes. *)
Lemma length_fst_string_addrs : forall strs base,
  length (fst (string_addrs base strs)) = length strs.
Proof.
  induction strs as [|s rest IH]; intro base; [reflexivity|].
  cbn [string_addrs].
  rewrite (surjective_pairing (string_addrs (base + len_word s + 1) rest)).
  cbn [fst length]. rewrite IH. reflexivity.
Qed.

Lemma length_flat_map_word_le8 : forall (l : list word),
  length (flat_map word_le8 l) = (8 * length l)%nat.
Proof.
  induction l as [|w rest IH]; [reflexivity|].
  cbn [flat_map length]. rewrite length_app, IH. cbn [length word_le8]. lia.
Qed.

(** The block runs from [sp] to [top]: its head is [C], its tail is the
    strings and the eight-byte slot, and the pad is whatever lies
    between.  Clamped at 0 by [Z.to_nat], so this holds for every [sp]
    and [top]; [Run.length_entry_stack_image_launch] reads it under the
    launch conjunct, where the pad is between 0 and 4110 and the sum
    collapses to [top - sp]. *)
Lemma length_build_stack_bytes :
  forall la ph entry sp top argv envp execfn uid gid hwcap draw,
  length (build_stack_bytes la ph entry sp top argv envp execfn uid gid hwcap draw)
  = (block_head_size (la_rseq la) argv envp
     + block_pad_len (la_rseq la) sp top argv envp execfn
     + launch_string_bytes argv envp execfn + 8)%nat.
Proof.
  intros la ph entry sp top argv envp execfn uid gid hwcap draw.
  unfold build_stack_bytes. cbv zeta.
  match goal with
  | |- context [string_addrs ?b argv] =>
      rewrite (surjective_pairing (string_addrs b argv))
  end.
  cbv beta iota.
  match goal with
  | |- context [string_addrs ?b envp] =>
      rewrite (surjective_pairing (string_addrs b envp))
  end.
  cbv beta iota.
  rewrite !length_app, !repeat_length, !length_flat_map_word_le8,
          !length_fst_string_addrs, length_auxv_bytes,
          length_at_random_bytes.
  unfold block_head_size, launch_string_bytes, block_items.
  cbn [length word_le8]. lia.
Qed.

(** ** The block's three pieces

    The part BELOW the sixteen AT_RANDOM bytes — argc, the pointer
    arrays, the auxv and the alignment gap — and the part ABOVE them —
    the [arch_align_stack] pad, the strings and the eight-byte slot.
    Named so that a proof can read one byte of the block by its offset
    without unfolding the whole layout, and so that the draw's
    independence below is a computation rather than a search. *)
Definition block_below_random (la : LaunchAuxv) (ph : PhdrInfo)
    (entry : word) (sp top : word) (argv envp : list (list byte))
    (execfn : list byte) (uid gid hwcap : word) : list byte :=
  let sbase := string_base_addr top argv envp execfn in
  let '(argv_ptrs, env_str_base) := string_addrs sbase argv in
  let '(envp_ptrs, _) := string_addrs env_str_base envp in
  word_le8 (len_word argv)
  ++ flat_map word_le8 argv_ptrs
  ++ word_le8 (Z_to_bv 64 0)
  ++ flat_map word_le8 envp_ptrs
  ++ word_le8 (Z_to_bv 64 0)
  ++ auxv_bytes la ph entry uid gid hwcap
       (at_random_ptr sp (la_rseq la) argv envp)
       (at_execfn_ptr top execfn)
  ++ repeat (Z_to_bv 8 0) (8 * (block_items argv envp mod 2)).

Definition block_above_random (rseq : bool) (sp top : word)
    (argv envp : list (list byte)) (execfn : list byte) : list byte :=
  repeat (Z_to_bv 8 0) (block_pad_len rseq sp top argv envp execfn)
  ++ flatten_strings argv ++ flatten_strings envp ++ execfn
  ++ [Z_to_bv 8 0]
  ++ repeat (Z_to_bv 8 0) 8.

(** THE DRAW IS READ BY NOTHING BUT THE SIXTEEN BYTES.  Two entries
    that differ only in [ed_random] give blocks that agree everywhere
    else, and every address in the layout is a function of (sp, top,
    argv, envp, the exec name, [la_rseq]) alone.  The lemma stops
    holding the day someone routes the draw into an address, a length
    or a pad. *)
Lemma build_stack_bytes_split_random :
  forall la ph entry sp top argv envp execfn uid gid hwcap draw,
  build_stack_bytes la ph entry sp top argv envp execfn uid gid hwcap draw
  = block_below_random la ph entry sp top argv envp execfn uid gid hwcap
    ++ at_random_bytes (ed_random draw)
    ++ block_above_random (la_rseq la) sp top argv envp execfn.
Proof.
  intros la ph entry sp top argv envp execfn uid gid hwcap draw.
  unfold build_stack_bytes, block_below_random, block_above_random.
  cbv zeta.
  destruct (string_addrs (string_base_addr top argv envp execfn) argv)
    as [ap eb] eqn:E1.
  destruct (string_addrs eb envp) as [ep fin] eqn:E2.
  rewrite <- !app_assoc. reflexivity.
Qed.

(** The stack image as a partial byte map based at [base].  The
    inside-the-image test is done in [Z] over unsigned values (the image
    never wraps the address space). *)
Definition stack_to_mem (base : word) (bytes : list byte)
    : word -> option byte :=
  fun addr =>
    if Z.leb (bv_unsigned base) (bv_unsigned addr) then
      let off := (bv_unsigned addr - bv_unsigned base)%Z in
      if Z.ltb off (Z.of_nat (length bytes)) then
        nth_error bytes (Z.to_nat off)
      else None
    else None.
