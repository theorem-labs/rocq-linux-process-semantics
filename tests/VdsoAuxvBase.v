(** * VdsoAuxvBase — AT_SYSINFO_EHDR names the vDSO text the launch maps.

    The launch maps the vDSO pair with [Run.vdso_segments], below the
    lower of the mmap base and [sp - State.stack_max_size], each rounded
    down to a page.  The C library finds the vDSO through
    AT_SYSINFO_EHDR, the first pair of the auxiliary vector: musl's
    [__vdsosym] reads the ELF header at that address on the first
    [clock_gettime] or [time] call.  So the address the entry block
    carries must be the base of the text segment the run maps, or the
    lookup reads memory that is not the vDSO's.

    This file reads AT_SYSINFO_EHDR out of the entry block
    [Run.entry_stack_image] lays, and compares it with the base of the
    [SegVdsoText] segment [Run.vdso_segments] places, on two launches:

    - launch A, [sp - stack_max_size >= mbase]: the pair sits directly
      below the mmap base, as Linux puts it.  The [sp] and the base are
      the recorded norandmaps launch of [tests/placement].
    - launch B, [sp - stack_max_size < mbase]: the pair sits below
      [sp - stack_max_size] instead.  Before AT_SYSINFO_EHDR was read
      from the pair, it named [mbase - 2 pages] here, 0x82000 bytes above
      the placed text, and [launch_b_auxv_names_the_placed_text] was
      false.

    Both values depend on the kernel build, [sp] and [mbase] only, so
    each launch lays its block with no argv and no envp, from [sp] to a
    top just above it: the block stays small, and the auxiliary vector
    starts 24 bytes above [sp], after argc and the two empty pointer
    arrays.  [launch_a_first_auxv_pair_is_sysinfo_ehdr] and its twin
    check that the word read there is AT_SYSINFO_EHDR's (tag 33). *)

From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Vdso Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel Require Vdso.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(** The input of [Checks.Cases.Kernel.Vdso]'s fixture: no argv, no envp,
    and [State.default_kernel], whose vDSO text is two pages. *)
Module KV := LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Vdso.

(** This file is about the pair, so it reduces it, as
    [Checks.Cases.Kernel.Vdso] does; [Run.vdso_segments] says why it is
    opaque elsewhere. *)
Local Transparent vdso_segments.

Definition va_inp : ProcInput := KV.fx_inp.
Definition va_kb : KernelBuild := in_kernel va_inp.

Example va_text_is_two_pages : vdso_text_pages va_kb = 2.
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   The two readings
   ========================================================================= *)

(** The base of the text segment the launch maps, if it maps one. *)
Definition placed_text (sp mbase : word) : option Z :=
  match find seg_vdso_text (vdso_segments va_kb sp mbase) with
  | Some s => Some (Z.of_N (seg_base s))
  | None => None
  end.

Fixpoint le_z (bs : list byte) : Z :=
  match bs with
  | [] => 0
  | b :: rest => bv_unsigned b + 256 * le_z rest
  end.

(** The little-endian word at byte [off] of [bs]. *)
Definition word_at (bs : list byte) (off : nat) : Z :=
  le_z (firstn 8 (skipn off bs)).

(** The first pair of the auxiliary vector in the entry block, as
    (tag, value): argc, the NULL that ends the empty argv and the NULL
    that ends the empty envp take the first 24 bytes. *)
Definition first_auxv_pair (sp mbase top : word) : Z * Z :=
  let bs := entry_stack_image va_inp mbase (mkPhdrInfo 0x10040%N 56%N 4%N)
              (Z_to_bv 64 0x10000) sp
              (mkDraw (Z_to_bv 128 0) top vdso_keeps_all) in
  (word_at bs 24, word_at bs 32).

(* =========================================================================
   Launch A: the stack far above the base
   ========================================================================= *)

Definition sp_a : word := Z_to_bv 64 0x7ffffffffdf0.
Definition mbase_a : word := Z_to_bv 64 0x7ffff8000000.
Definition top_a : word := Z_to_bv 64 0x800000000000.

Example launch_a_stack_is_far_above_the_base :
  (bv_unsigned mbase_a <=? bv_unsigned sp_a - stack_max_size) = true.
Proof. vm_compute. reflexivity. Qed.

(** The text is the two pages directly below the mmap base. *)
Example launch_a_places_the_text_below_the_base :
  placed_text sp_a mbase_a = Some 0x7ffff7ffe000.
Proof. vm_compute. reflexivity. Qed.

Example launch_a_first_auxv_pair_is_sysinfo_ehdr :
  fst (first_auxv_pair sp_a mbase_a top_a) = 33.
Proof. vm_compute. reflexivity. Qed.

Example launch_a_auxv_names_the_placed_text :
  placed_text sp_a mbase_a = Some (snd (first_auxv_pair sp_a mbase_a top_a)).
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   Launch B: the stack close above the base
   ========================================================================= *)

(** The shape of launch the launch rules admit with randomization on
    ([State.default_kernel] has [kb_aslr] and a 256-page guard gap): the
    stack's top at its lowest, [0x7fffc0000000]; the mmap base at mmap
    draw 0, [Run.mmap_base_of Sv48 kb 0]; and [sp] 0x180400 bytes below
    that top, which about 1.5 MiB of argv and envp strings give
    ([Run.launch_sp_hi]).  Then [sp - stack_max_size] is 0x81400 bytes
    below the base. *)
Definition sp_b : word := Z_to_bv 64 0x7fffbfe7fc00.
Definition mbase_b : word := Z_to_bv 64 0x7fffbf701000.
Definition top_b : word := Z_to_bv 64 0x7fffbfe80000.

Example launch_b_lowest_stack_top :
  va_stack_top Sv48 - (stack_rnd_max + page_size) = 0x7fffc0000000.
Proof. vm_compute. reflexivity. Qed.

Example launch_b_base_is_the_launch_base_at_draw_0 :
  bv_unsigned mbase_b = mmap_base_of Sv48 va_kb 0.
Proof. vm_compute. reflexivity. Qed.

Example launch_b_stack_is_close_above_the_base :
  (bv_unsigned sp_b - stack_max_size <? bv_unsigned mbase_b) = true.
Proof. vm_compute. reflexivity. Qed.

(** The text is placed below [page_round_down (sp - stack_max_size)],
    0x84000 bytes below the base. *)
Example launch_b_places_the_text_below_the_stack_bound :
  placed_text sp_b mbase_b = Some 0x7fffbf67d000.
Proof. vm_compute. reflexivity. Qed.

Example launch_b_first_auxv_pair_is_sysinfo_ehdr :
  fst (first_auxv_pair sp_b mbase_b top_b) = 33.
Proof. vm_compute. reflexivity. Qed.

(** THE CASE.  AT_SYSINFO_EHDR is the text the launch placed. *)
Example launch_b_auxv_names_the_placed_text :
  placed_text sp_b mbase_b = Some (snd (first_auxv_pair sp_b mbase_b top_b)).
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   For every launch
   ========================================================================= *)

(** The two Examples above are two launches.  [VdsoSegs] states the
    equality for every input, [sp] and mbase
    ([launch_auxv_sysinfo_ehdr_is_the_text]); this prints what that
    proof rests on, so the build log shows it closed. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import VdsoSegs.
Print Assumptions launch_auxv_sysinfo_ehdr_is_the_text.
