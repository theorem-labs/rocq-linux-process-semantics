(** * MemImageType — shared types for memory image snapshots

    TRUST BOUNDARY: this file is part of the trusted specification.

    Defines the [Segment] record used by all generated MemImage files
    and by [RiscvSemantics.v] for memory reads.  Factored out so that
    multiple MemImage instantiations (source binary + target binary)
    can share the same type without circular dependencies. *)

From Stdlib Require Import NArith List String Ascii.
From Stdlib Require PrimString.

Import ListNotations.
Local Open Scope string_scope.

(** WHAT PUT A SEGMENT IN THE LIST.

    [execve] maps two kinds of thing: the binary's own LOAD segments,
    which the loader reads out of the ELF file, and the kernel's own
    pages, which the binary never asked for — the vDSO text, whose base
    the auxiliary vector publishes as [AT_SYSINFO_EHDR], and the vvar
    data pages directly below it ([__setup_additional_pages],
    arch/riscv/kernel/vdso.c, and [vdso_install_vvar_mapping],
    lib/vdso/datastore.c, Linux v6.18.46, commit 1f99e9ab748f).

    [Run.run] puts all of them into ONE list, because that is the list
    every load, store and fetch is read against, and a second list
    would be a second answer to the same question.  This field is what
    tells them apart.

    IT IS A FIELD AND NOT A LETTER IN [seg_perms].  A tag inside the
    permission string would be safe only if no emitter could ever write
    such a letter, and nothing holds that property: [elf_snapshot.py]'s
    pattern check runs only over files that tool itself wrote, and
    [theorem-labs/linux-process-semantics] has two more emitters,
    [tools/gen_lean_image.py] and [tools/gen_lean_example_image.py],
    that write the permission string verbatim.  A binary segment whose
    permissions happened to carry the letter would be dropped from
    [Run.segments_reserved], and the allocator could then grant over
    the binary's own text while a universal statement still held,
    having said nothing about either binary.  With a field, no string
    can mean a kernel mapping and every emitter must say which kind it
    is writing. *)
Inductive SegKind :=
| SegLoader    (** a LOAD segment of the binary *)
| SegVdsoText  (** the vDSO text the kernel mapped *)
| SegVdsoVvar  (** the vvar data pages below it *).

Record Segment := {
  seg_base  : N;
  seg_size  : N;
  seg_perms : String.string;
  seg_bytes : list PrimString.string;  (* hex chunks, lowercase, no spaces *)
  seg_kind  : SegKind
}.

(** ** [PhdrInfo] — where the binary's PROGRAM HEADER TABLE lands in memory

    The kernel does not only map the LOAD segments at [execve]: it also
    tells the new process where its own program header table is, through
    the auxiliary vector ([StackLayout.auxv_entries]) —

    - AT_PHDR  ([ph_addr]): the RUN-TIME address of the phdr table.  The
      kernel reports the address the table got by virtue of lying inside
      a mapped LOAD segment: for the segment whose file extent covers
      [e_phoff], [p_vaddr + (e_phoff - p_offset)] (fs/binfmt_elf.c, the
      [phdr_addr] computation in [load_elf_binary]).  Static
      non-PIE riscv64 binaries put the table in the first LOAD segment,
      which starts at file offset 0, so this is just [e_phoff] above the
      image base.
    - AT_PHENT ([ph_ent]): [e_phentsize], 56 for every ELF64 file.
    - AT_PHNUM ([ph_num]): [e_phnum].

    WHY THE MODEL NEEDS IT.  A statically linked libc reads its own
    program headers to find the segments the kernel does not describe
    any other way — above all PT_TLS, the initialization image for
    THREAD-LOCAL STORAGE.  musl's [__init_tls] walks
    [AT_PHDR..AT_PHDR + AT_PHNUM * AT_PHENT) looking for it, sizes the
    thread block from its [p_memsz]/[p_align], copies [p_filesz] bytes
    of initialized TLS data out of it, and only then sets the thread
    pointer [tp].  With no AT_PHDR (or AT_PHNUM = 0) that walk finds
    nothing, and every [_Thread_local] access in the program reads and
    writes a block that was never laid out for it.  The phdr table is
    therefore process-startup data exactly like [init_pc], and belongs
    to the image for the same reason.

    Note this is DERIVED data: the bytes of the table are already in the
    image (they lie inside the first LOAD segment, which the loader
    snapshots from file offset 0).  [PhdrInfo] only records where they
    ended up, which the model cannot recompute without an ELF parser.
    [elf-snapshot] emits it, and checks the recorded range
    really is covered by a snapshotted readable segment; because that
    check is Python, and outside the trust boundary, the same
    containment is re-checked inside Rocq for both images of every
    example by [Equivalence.image_phdrs_readable] in [Checker.v].
    Nothing else in the model relates [phdrs] to [loaded_segments]:
    [Run.init_machine_state] publishes [ph_addr] whatever it says. *)
Record PhdrInfo := mkPhdrInfo {
  ph_addr : N;   (** AT_PHDR  — run-time address of the phdr table *)
  ph_ent  : N;   (** AT_PHENT — e_phentsize (56 on ELF64) *)
  ph_num  : N    (** AT_PHNUM — e_phnum *)
}.

(** Does the permission string carry the flag character [c]?  [seg_perms]
    comes from the ELF program-header flags rendered as "rwx" (with '-'
    for an unset bit): 'r' at index 0, 'w' at index 1, 'x' at index 2.
    The three flag letters are distinct and appear nowhere else in the
    string, so scanning the whole string for [c] identifies the flag
    regardless of the exact rendering, staying robust to formatting. *)
Fixpoint string_has (c : Ascii.ascii) (s : String.string) : bool :=
  match s with
  | String.EmptyString => false
  | String.String c' r => if Ascii.eqb c' c then true else string_has c r
  end.

(** The three page permissions the model enforces, each derived from the
    ELF segment's [seg_perms].  Together they make the loaded image obey
    the same protections a real kernel installs at [execve]:

    - [seg_readable]: reads (machine loads, and syscall SOURCE buffers)
      may only touch readable pages.  A PROT_NONE / write-only region is
      not readable — reading it is the SIGSEGV analogue.
    - [seg_writable]: drives two trusted checks — machine stores into a
      non-writable segment are illegal (RiscvSemantics.v), and syscall
      OUTPUT buffers must be writable-mapped (LinuxProcessSem).
    - [seg_executable]: instruction fetch may only read executable pages
      (the NX / W^X guarantee).  Jumping into a non-executable segment
      (.rodata, .data) faults rather than executing its bytes as code. *)
Definition seg_readable   (seg : Segment) : bool := string_has "r"%char (seg_perms seg).
Definition seg_writable   (seg : Segment) : bool := string_has "w"%char (seg_perms seg).
Definition seg_executable (seg : Segment) : bool := string_has "x"%char (seg_perms seg).

(** ** The kernel's own mappings, told apart by [seg_kind]

    WHAT EACH KIND MEANS for the machine, beyond telling the pair apart
    from the binary:

    - [SegVdsoText]: [RiscvSemantics.fetch_failure] answers
      [MachineUnmodeled] for a pc inside it, and [Run.sstep]'s vDSO arm
      takes the one step a call to an exported entry is.  The segment
      is READABLE, so a libc's lookup reads the image's bytes with
      ordinary loads, and carries no 'x', although Linux maps it
      PROT_READ|PROT_EXEC: the model's 'x' flag says "the model fetches
      and executes these bytes", and of the vDSO's bytes it does not.
      Without 'x' no fetch path can reach the decoder there, so the
      [MachineUnmodeled] arm is the only answer rather than one of
      two, and no lemma about a successful [fetch_word] has to exclude
      the vDSO.
    - [SegVdsoVvar]: a load from it is [MachineUnmodeled] rather than
      the fault an unmapped address gives.  The pages exist and are
      readable on Linux; what the model has no term for is their
      CONTENTS, which the kernel rewrites while the process runs.  The
      segment is readable and carries no bytes, which is exactly that
      statement.

    Neither is writable, so a store into either is the SIGSEGV a real
    MMU delivers, through [RiscvSemantics.store_ok], with no arm of its
    own. *)
Definition seg_vdso_text (seg : Segment) : bool :=
  match seg_kind seg with SegVdsoText => true | _ => false end.
Definition seg_vdso_vvar (seg : Segment) : bool :=
  match seg_kind seg with SegVdsoVvar => true | _ => false end.

(** A segment the KERNEL installed rather than the loader.  [Run.run]
    builds these; [Run.segments_reserved] leaves them out, because the
    pair's reservation is the memory ledger's own, and counting it
    twice would move [Run.valid_brk]'s [reserved_top] to the top of the
    address space. *)
Definition seg_kernel_map (seg : Segment) : bool :=
  match seg_kind seg with SegLoader => false | _ => true end.

(** ** [MemImage] — the data a single compiled binary contributes to the model.

    A memory image is exactly the ELF-derived data [Run.run] consumes: the
    loaded code/data segments, the initial program counter, and the
    program-header-table location the kernel publishes in the auxv
    ([PhdrInfo]).  Nothing
    else in the image comes from the binary — the initial register file is
    fixed by the process model ([Run.init_machine_state]): the stack pointer
    is quantified over the launches [execve] can give ([Run.valid_sp] for
    the ASLR window, and [Run.entry_launch_ok_va] for the stack VMA's end
    and the pad below it), and every other
    register, [a0] included, starts at 0 on Linux entry (argc/argv live on
    the stack, not in registers).  Both the source binary and the target
    binary are packaged as [MemImage] modules, and the [Equivalence] functor
    in [Equivalence.v] is parameterized over two of them.

    Generated per-binary by [elf-snapshot --module-name]. *)
Module Type MemImage.
  Parameter loaded_segments : list Segment.
  Parameter init_pc : N.
  Parameter phdrs : PhdrInfo.
End MemImage.

(** The same three data as a RECORD, so that [Run.run] and the theorem
    statements in [Equivalence.v] take one image argument rather than
    three parallel ones.  A [MemImage] module is packaged into it by
    [Equivalence.SPEC]; the module type stays the interface the
    generated snapshot files implement. *)
Record Image := mkImage {
  img_segments : list Segment;
  img_init_pc  : N;
  img_phdrs    : PhdrInfo
}.
