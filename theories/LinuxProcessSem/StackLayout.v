(** * StackLayout — Linux process initial stack builder

    TRUST BOUNDARY: this file is part of the trusted specification.

    Addresses are [word = bv 64], stack bytes are [byte = bv 8].  Auxv
    types/values are word constants, serialized via [BvBase.word_le8].

    Builds the byte sequence that the kernel places on the stack at
    process startup: argc, argv pointers, envp pointers, auxiliary
    vector, and null-terminated string data. *)

From Stdlib Require Import ZArith NArith List.
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

Definition AT_NULL    : word := Z_to_bv 64 0.
Definition AT_PHDR    : word := Z_to_bv 64 3.
Definition AT_PHENT   : word := Z_to_bv 64 4.
Definition AT_PHNUM   : word := Z_to_bv 64 5.
Definition AT_PAGESZ  : word := Z_to_bv 64 6.
Definition AT_HWCAP   : word := Z_to_bv 64 16.
Definition AT_UID     : word := Z_to_bv 64 11.
Definition AT_EUID    : word := Z_to_bv 64 12.
Definition AT_SECURE  : word := Z_to_bv 64 23.
Definition AT_RANDOM  : word := Z_to_bv 64 25.

(** ** The two AT_HWCAP masks this model admits

    [hwcap_rv64gc] is the bit for each of the six single-letter
    extensions the model's own decoder implements — A, C, D, F, I and M
    — and [hwcap_rv64gcv] is that mask with V added.  The bit for a
    letter X is [1 << (X - 'A')] (arch/riscv/include/uapi/asm/hwcap.h,
    the [COMPAT_HWCAP_ISA_*] macros, Linux v6.18.46, commit
    1f99e9ab748f), so A=0x1, C=0x4, D=0x8, F=0x20, I=0x100, M=0x1000 and
    V=0x200000.  [Run.valid_hwcap] admits exactly these two words; the
    argument for the pair is in the [AT_HWCAP] bullet below. *)
Definition hwcap_rv64gc  : word := Z_to_bv 64 0x112D.
Definition hwcap_rv64gcv : word := Z_to_bv 64 0x20112D.

(** The auxiliary vector the model's kernel provides, as (type, value)
    pairs, terminated by AT_NULL (AT_PAGESZ for musl, no secure-exec).
    Notable entries:

    - [AT_PHDR / AT_PHENT / AT_PHNUM]: the binary's own program header
      table, taken from the image's [MemImageType.PhdrInfo] (see there
      for how the loader derives it and why the model needs it).  This
      is what lets a static libc find the segments the kernel describes
      nowhere else — above all PT_TLS, which musl's [__init_tls] locates
      by walking exactly this table before it lays out THREAD-LOCAL
      STORAGE and sets [tp].  The table's BYTES are already in the
      image; the auxv only says where they are.
    - [AT_HWCAP = hwcap]: which single-letter ISA extensions the HART
      running this process implements.  This is a QUANTIFIED value, not
      a constant: [Run.valid_hwcap] names the two masks it may take and
      [State.ProcInput]'s [in_hwcap] carries the choice, so
      [Equivalence.strong_universal_T] ranges over both — the same way
      [Run.valid_sp] ranges over the stack ASLR window instead of
      picking one stack address.

      Linux emits the entry UNCONDITIONALLY, and first:
      [create_elf_tables] opens the vector with
      [NEW_AUX_ENT(AT_HWCAP, ELF_HWCAP)] immediately before the
      [AT_PAGESZ] line (fs/binfmt_elf.c:249, Linux v6.18.46, commit
      1f99e9ab748f), which is why the entry sits where it does below.
      On riscv64 [ELF_HWCAP] is [riscv_get_elf_hwcap()]
      (arch/riscv/include/asm/elf.h:66), and that function masks
      [elf_hwcap] down to bits 0..25 — [RISCV_ISA_EXT_BASE] is 26
      (arch/riscv/include/asm/hwcap.h:33) — so nothing but
      SINGLE-LETTER extensions can appear
      (arch/riscv/kernel/cpufeature.c:1108).  [elf_hwcap] is only ever
      assigned [this_hwcap] or [elf_hwcap & this_hwcap] — the
      intersection over the harts, at arch/riscv/kernel/cpufeature.c
      lines 860-863 and 1011-1014 — and [this_hwcap] is accumulated out
      of [isa2hwcap], which [riscv_fill_hwcap]
      (arch/riscv/kernel/cpufeature.c:1053) seeds at exactly seven
      indices, i m a f d c v (lines 1059-1065), leaving the other
      nineteen zero.  The WHOLE range of AT_HWCAP on this architecture
      is therefore the subsets of {A,C,D,F,I,M,V}, with F implying D
      (the same function masks F off a hart that lacks D, at line 1082).

      Of that range the model fixes six bits and leaves one free.  The
      six are fixed by the ISA the model EXECUTES: [Riscv.Decode] is an
      RV64IMAFD decoder and [Riscv.DecodeC] adds C, so a hart without
      one of those six would not run the instructions this semantics
      interprets, and a statement about this process on such a hart
      would be a statement about a machine the model does not describe.
      The free bit is V.  The model cannot decode a vector instruction —
      but [RiscvSemantics.decode_exec_accesses] answers an undecodable
      word with [MachineUnmodeled] rather than a trap, precisely because
      such a word "may be a genuinely illegal encoding, but it may
      equally be a hole in THIS decoder".  The model therefore does not
      claim the hart lacks V, and must not publish an AT_HWCAP that says
      so.  Nor is the bit a property of the silicon alone: [ELF_HWCAP]
      clears it whenever [riscv_v_vstate_ctrl_user_allowed()] is false
      (arch/riscv/kernel/cpufeature.c:1114-1115), which a process
      controls through [PR_RISCV_V_SET_CONTROL], so the kernel
      produces both masks on one machine.

      WHAT THE FREE BIT COSTS, and why it is worth it.  A runtime that
      dispatches on [AT_HWCAP & COMPAT_HWCAP_ISA_V] selects its vector
      path under [hwcap_rv64gcv], and the first vector instruction it
      executes is a word [DecodeC.decode_any] returns [None] for, so
      that run is [MachineUnmodeled] and no [error_free] statement about
      the binary survives.  That is the honest answer and it is the
      point of the entry.  Without the entry, every such runtime would
      read the zero its lookup defaults to, take its scalar path, and the
      model would prove that path AS CERTAIN for a process a real kernel
      sends down the other one.  The cost is the mirror image: a program
      that ECHOES its AT_HWCAP word has no single modeled answer, so it is
      not provable here — a residual of the same kind as AT_RANDOM's
      below, but on the side that declines rather than the side that
      guesses.

    - [AT_UID = AT_EUID = uid] and [AT_SECURE = 0]: both entries carry
      the [uid] argument, which [Run.init_machine_state] fills from the
      run's [State.in_uid] — the SAME field [State.init_model] copies
      into the credentials [Kernel.Sys.getid_spec] reads.  One source,
      so a program that reads AT_UID off its own initial stack and
      compares it with [getuid] gets the agreement every kernel gives.
      Linux ties the two together the same way: [create_elf_tables]
      (fs/binfmt_elf.c) emits
      [NEW_AUX_ENT(AT_UID, from_kuid_munged(cred->user_ns, cred->uid))]
      and the [AT_EUID] line beside it off [cred = current_cred()], and
      [SYSCALL_DEFINE0(getuid)] (kernel/sys.c) returns
      [from_kuid_munged(current_user_ns(), current_uid())] — the same
      munge of the same field of the same [struct cred], since
      [current_uid()] is [current_cred()->uid].  The creds are already
      the post-exec ones at that point: [load_elf_binary] calls
      [begin_new_exec], which [commit_creds(bprm->cred)], BEFORE it
      calls [create_elf_tables], so a set-user-id exec publishes the
      new ids rather than the caller's.  Both texts are read off Linux
      v6.18.46 (commit 1f99e9ab748f) and are byte-identical there and at
      every mainline release tag from v4.4 through v6.18, and both are
      unconditional — no config guards the four id entries.
      The EQUALITY of the two entries is what keeps libc's secure-exec
      path (which would probe and sanitize fds 0-2) dead code: its
      syscalls are never issued, so the model does not cover them.  The
      equality holds by CONSTRUCTION: [State.ProcInput] carries only the
      REAL ids, and [State.init_model] builds the effective and saved
      ones from them, so a launch whose effective id differs cannot be
      expressed — which is why one [uid] argument serves both entries
      rather than two.  musl's [__init_libc] computes [libc.secure] from
      the INEQUALITY [AT_UID != AT_EUID] (and [AT_GID != AT_EGID], and
      [AT_SECURE]), so the equality is the whole of what libc reads here.
      Residual infidelity, of the same kind as the
      absent entries below: a real kernel also emits AT_GID and AT_EGID,
      which this vector does not carry at all, so it reports no group id
      rather than a wrong one.  [State.in_gid] therefore has nothing to
      fill here; adding the pair is an entry-SET change (it moves
      [auxv_size]) and belongs with the other absentees.
    - [AT_RANDOM = at_random_ptr …]: the address of 16 bytes of startup
      entropy that [build_stack_bytes] materializes at the very end of
      the initial stack image, as the kernel does.  A libc that seeds
      its stack canary from AT_RANDOM (musl's [__init_ssp]) dereferences
      this pointer, so it must be a valid address.  The BYTES are the
      run's own draw, not a constant: [create_elf_tables]
      (fs/binfmt_elf.c, Linux v6.18.46, commit 1f99e9ab748f) calls
      [get_random_bytes(k_rand_bytes, sizeof(k_rand_bytes))], copies the
      16 bytes to the new stack, and emits
      [NEW_AUX_ENT(AT_RANDOM, (elf_addr_t)(unsigned long)u_rand_bytes)]
      pointing at the copy, so every [execve] gets fresh ones.  The
      model quantifies over them exactly as it quantifies over the stack
      pointer and the program break: [at_random_bytes] is a function of
      the [ed_random] half of [Run.ExecEntry]'s [en_draw], a [bv 128]
      carrying no validity clause (every 128-bit value is a draw the kernel can make and every
      draw is a 128-bit value), quantified INDEPENDENTLY per binary in
      [Equivalence.strong_universal_T].  The LAYOUT is untouched:
      [at_random_ptr] and every other address here stay functions of
      (sp, argv, envp) alone, so only the 16 bytes themselves move with
      the draw.  A binary that echoes its AT_RANDOM bytes is therefore
      not modeled as echoing zeros — it is a binary no equivalence proof
      can close, since the two runs may draw differently, which is the
      same stance this file's [Run] neighbours take on a program that
      leaks its stack address.
      Residual infidelity, and it is about WHERE the block sits rather
      than what is in it: this layout puts the 16 bytes ABOVE the argv
      and envp strings, at the top of the image, while Linux puts them
      BELOW the strings — [copy_strings] (fs/exec.c) has already placed
      the strings at the high end when [create_elf_tables] runs, and
      [STACK_ALLOC] takes the block off the bottom of that area.  Both
      put it above [sp], which is the only relation anything in this tree
      checks, so a program comparing the AT_RANDOM pointer with a string
      address is modeled with that comparison inverted.

    Entries a real kernel also supplies and this one does not (AT_BASE,
    AT_ENTRY, AT_FLAGS, AT_CLKTCK, AT_PLATFORM, AT_EXECFN, …)
    are absent rather than zeroed, which reads to libc as "not
    provided"; musl treats every one of them as optional.  Every libc
    reads the auxv as a lookup table (musl's [__init_libc] switches on
    the type of each pair), so to STARTUP CODE the order of the entries
    is not observable — only which types are present, and their values.
    Residual infidelity, of the same kind as the absent AT_GID/AT_EGID
    pair above: a program that walks its own auxv and echoes the raw
    (type, value) words produces a trace that depends on the order and on
    the exact entry set, so such a program's modeled trace differs from
    its real one. *)
Definition auxv_entries (ph : PhdrInfo) (at_random : word) (uid : word)
    (hwcap : word) : list (word * word) :=
  [ (AT_PHDR,   Z_to_bv 64 (Z.of_N (ph_addr ph)));
    (AT_PHENT,  Z_to_bv 64 (Z.of_N (ph_ent ph)));
    (AT_PHNUM,  Z_to_bv 64 (Z.of_N (ph_num ph)));
    (AT_HWCAP,  hwcap);
    (AT_PAGESZ, Z_to_bv 64 4096);
    (AT_UID,    uid);
    (AT_EUID,   uid);
    (AT_SECURE, Z_to_bv 64 0);
    (AT_RANDOM, at_random);
    (AT_NULL,   Z_to_bv 64 0) ].

(** Serialize an auxv: each entry is two little-endian 64-bit words. *)
Definition build_auxv (entries : list (word * word)) : list byte :=
  flat_map (fun e => word_le8 (fst e) ++ word_le8 (snd e)) entries.

Definition auxv_bytes (ph : PhdrInfo) (at_random : word) (uid : word)
    (hwcap : word) : list byte :=
  build_auxv (auxv_entries ph at_random uid hwcap).

(** The serialized auxv's SIZE — 10 entries of two 64-bit words.  It
    depends on neither the image, nor the launching user, nor the hart
    ([PhdrInfo] fills in three of the VALUES, [uid] two more and
    [hwcap] one, and no argument adds or removes an entry), so every
    ADDRESS in the layout below — where the strings start, where
    AT_RANDOM points — stays a function of (sp, argv, envp) alone.
    Only the bytes stored in those
    six slots move.  This is what keeps AT_HWCAP's two admissible masks
    from being an addressing question: the quantifier
    [Equivalence.strong_universal_T] ranges over changes the CONTENTS of
    one 8-byte slot and nothing else. *)
Definition auxv_size : nat := 160%nat.

Lemma length_auxv_bytes : forall ph at_random uid hwcap,
  length (auxv_bytes ph at_random uid hwcap) = auxv_size.
Proof. reflexivity. Qed.

(** …and the size does not move with the hart: the two masks
    [Run.valid_hwcap] admits give byte-identical LAYOUTS, differing only
    in the eight bytes of AT_HWCAP's value slot.  Stated separately from
    [length_auxv_bytes] because it is the property the addressing
    argument above actually rests on. *)
Lemma length_auxv_bytes_hwcap_invariant : forall ph at_random uid h h',
  length (auxv_bytes ph at_random uid h)
  = length (auxv_bytes ph at_random uid h').
Proof. reflexivity. Qed.

(** ** What [execve] drew for this process's entry stack

    The two byte-level choices in the entry stack image that the model
    does NOT determine, carried together in [Run.ExecEntry]'s [en_draw]
    beside the three placement draws [en_sp], [en_brk] and
    [en_mmap_base].  Neither has a validity predicate, because every
    value of either is one a kernel can produce, and both are quantified
    INDEPENDENTLY for the two binaries in
    [Equivalence.strong_universal_T] — which is what makes a program
    whose output depends on either unprovable against anything, the same
    treatment, for the same reason, as a program that leaks its stack
    address.

    - [ed_random]: the 16 bytes AT_RANDOM points at.  [create_elf_tables]
      (fs/binfmt_elf.c, Linux v6.18.46, commit 1f99e9ab748f) calls
      [get_random_bytes(k_rand_bytes, sizeof(k_rand_bytes))] and copies
      the result onto the new stack for AT_RANDOM to point at.  Read by
      exactly one thing, the last 16 bytes of [build_stack_bytes]
      ([build_stack_bytes_split_random]).

    - [ed_slack]: the bytes of the entry stack's LAST PAGE that lie above
      that block.  Linux's stack is a VMA and a VMA covers whole pages —
      [setup_arg_pages] (fs/exec.c) fixes its top with
      [stack_top = arch_align_stack(stack_top); stack_top = PAGE_ALIGN(stack_top);]
      — so those addresses are mapped, and what they hold is the tail of
      the string area, the exec filename [AT_EXECFN] points at
      ([do_execveat_common] copies [bprm->filename] first, so it sits
      highest), and the pointer-sized run of bytes below the VMA's top
      that [create_init_stack_vma] (mm/vma_exec.c) skipped — it hands
      [exec] the first string address as [vm_end] minus the size of a
      pointer — and nothing wrote.
      This model lays out none of that — it publishes no AT_EXECFN and
      builds no filename string — so no address up there has a fixed
      counterpart in the kernel's image, and WHICH of them hold filename
      and which hold untouched zeros depends on how the program was
      invoked.

      The mismatch starts lower than the strings, which is why a
      zero-part plus choice-part SPLIT is impossible rather than merely
      inconvenient: the kernel's own auxv is far longer than this one.
      [create_elf_tables] writes 16 unconditional [NEW_AUX_ENT]s and
      expands riscv's [ARCH_DLINFO] on top of them, which adds
      [AT_SYSINFO_EHDR] and eight cache-descriptor entries
      (arch/riscv/include/asm/elf.h), against this vector's ten.  So for
      a short argv the model's block ends INSIDE the kernel's auxv and
      the first bytes above it in a real process are auxv words — not
      string bytes, and not the filename the paragraph above starts
      from.  Read by [Run.entry_slack].

    Indexed by ADDRESS rather than by offset because the region's
    position and length are functions of [sp] and of the caller's
    argv/envp, and the draw is meant to be independent of both.  A choice
    rather than zeros for the same reason as [ed_random]: a
    model that committed the bytes to a value would prove a program that
    reads one equivalent to a program that really writes that value.  A
    choice rather than a fresh value per read for the opposite reason:
    the bytes are stored memory in Linux, and a model that redrew them
    would call two programs that each echo their own byte equivalent
    when they are not. *)
Record EntryDraw := mkDraw_full {
  ed_random : bv 128;
  ed_slack  : word -> byte;
  ed_vdso   : VdsoDraw
    (* WHAT A vDSO CALL LEAVES BEHIND: from the index of the call in
       the run, the caller-saved registers before it, the bytes of
       [[sp - F, sp)] before it and the call's result, to the
       caller-saved registers and those bytes after it.  F is the
       chosen image's largest frame ([Vdso.vi_frame]).

       It is part of the DRAW, beside [ed_random] and [ed_slack], for
       the same reason they are: Linux's answer is what the vDSO's
       compiled code left, a function of the same inputs and of time
       values this model lets the environment choose, and the model
       has no term for that code.  Drawing it once per launch — rather
       than afresh at each call — is what makes two calls with the same
       inputs leave the same bytes, as they do on a real run; the
       call's INDEX is an argument so that two calls that are not the
       same call still may differ.  [Run.init_config] copies it into
       the model, where [Run.sstep]'s vDSO arm reads it. *)
}.

(** THE TWO-PLACE FORM: the entropy draw and the slack bytes, with the
    vDSO draw filled by [Vdso.vdso_draw_keep] — the draw that gives
    back the registers and frame bytes a call started with, which is
    one Linux also gives (a vDSO function that touched neither a
    scratch register nor its frame).

    It exists for the reason [State.mkProcInput] does: the development
    holds positional [mkDraw] literals, and a fixture that is not about
    the leftovers should not have to name them.  A fixture that IS
    about them writes [mkDraw_full]. *)
Definition mkDraw (random : bv 128) (slack : word -> byte) : EntryDraw :=
  mkDraw_full random slack vdso_draw_keep.

(** The 16 bytes AT_RANDOM points at: this run's entropy draw
    (the [ed_random] half of [Run.ExecEntry]'s [en_draw]; see the auxv comment above for the
    kernel side), serialized little-endian.

    The draw is a [bv 128] rather than a 16-element [list byte] because
    the LENGTH is then fixed by the type.  Every layout lemma below needs
    that length and gets it by computation
    ([length_at_random_bytes]), so the entry carries NO validity clause
    and no statement that quantifies over an entry grows a side
    condition — the same reason [State.in_stdin] has no predicate.  Byte
    [k] of the block is [bv_extract (8 * k) 8 rnd] by definition, so a
    proof that reads one byte back out of the image gets a bare extract
    of the draw rather than a value it can compute with.

    Their address: the stack image ends with
    [raw ++ pad ++ at_random_bytes rnd], so the block sits at
    [sp + struct size + string bytes + pad], the HIGHEST address in the
    image — above the strings, where Linux puts it below them — the same arithmetic
    [build_stack_bytes] below performs on the built lists ([auxv_size] =
    length of the auxv).  The offset is computed in [nat]/[Z] and re-wrapped
    with [nat_to_word] (the image never wraps the address space), and it
    does not mention the draw: the layout is a function of
    (sp, argv, envp) alone ([build_stack_bytes_split_random] states
    this). *)
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

Definition at_random_ptr (sp : word) (argv envp : list (list byte)) : word :=
  let struct_size :=
    (8 + (length argv + 1) * 8 + (length envp + 1) * 8 + auxv_size)%nat in
  let len := (struct_size + length (flatten_strings argv)
                          + length (flatten_strings envp))%nat in
  let pad := Z.to_nat ((8 - Z.of_nat len mod 8) mod 8)%Z in
  sp + nat_to_word (len + pad).

(** The initial stack image.  [rnd] is the run's AT_RANDOM draw and is
    read by NOTHING but the final [at_random_bytes] block: the argc/argv/
    envp/auxv struct, the strings and the alignment pad are all functions
    of the other arguments, which is what
    [build_stack_bytes_split_random] below says and what keeps every
    concrete-layout proof in the tree computing as it did. *)
Definition build_stack_bytes (ph : PhdrInfo) (sp : word) (argv : list (list byte))
    (envp : list (list byte)) (uid : word) (hwcap : word)
    (draw : EntryDraw) : list byte :=
  let argc := len_word argv in
  let envc := length envp in
  let n_argv_slots := (length argv + 1)%nat in
  let n_envp_slots := (envc + 1)%nat in
  let auxv := auxv_bytes ph (at_random_ptr sp argv envp) uid hwcap in
  let struct_size :=
    (8 + n_argv_slots * 8 + n_envp_slots * 8 + length auxv)%nat in
  let string_base := sp + nat_to_word struct_size in
  let '(argv_ptrs, env_str_base) := string_addrs string_base argv in
  let '(envp_ptrs, _) := string_addrs env_str_base envp in
  let raw :=
    word_le8 argc
    ++ flat_map word_le8 argv_ptrs
    ++ word_le8 (Z_to_bv 64 0)
    ++ flat_map word_le8 envp_ptrs
    ++ word_le8 (Z_to_bv 64 0)
    ++ auxv
    ++ flatten_strings argv
    ++ flatten_strings envp in
  let len := Z.of_nat (length raw) in
  let pad := Z.to_nat ((8 - len mod 8) mod 8)%Z in
  raw ++ repeat (Z_to_bv 8 0) pad ++ at_random_bytes (ed_random draw).

(** The image is a draw-INDEPENDENT prefix followed by the 16 bytes of
    the draw.  The proof is where the claim bites: the existential
    witness is introduced BEFORE [rnd] is, so a prefix that mentioned the
    draw could not close it — put another way, this lemma stops holding
    the day someone routes [rnd] into an address, a length or a pad.
    Two consequences a reader should take from it: two entries differing
    only in [ed_random] give images that agree everywhere but the last
    16 bytes, and every existing concrete-layout computation is
    unaffected, because it lives in the prefix. *)
Lemma build_stack_bytes_split_random :
  forall ph (sp : word) (argv envp : list (list byte)) (uid hwcap : word),
  exists pre, forall draw,
    build_stack_bytes ph sp argv envp uid hwcap draw
    = pre ++ at_random_bytes (ed_random draw).
Proof.
  intros ph sp argv envp uid hwcap. eexists. intro draw.
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
  rewrite !app_assoc. reflexivity.
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
