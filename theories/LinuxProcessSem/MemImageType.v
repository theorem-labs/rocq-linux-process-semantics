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

Record Segment := {
  seg_base  : N;
  seg_size  : N;
  seg_perms : String.string;
  seg_bytes : list PrimString.string  (* hex chunks, lowercase, no spaces *)
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
