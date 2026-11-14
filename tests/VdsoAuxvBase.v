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
    launches A and B lay their blocks with no argv and no envp, from [sp]
    to a top just above it: the block stays small, and the auxiliary
    vector starts 24 bytes above [sp], after argc and the two empty
    pointer arrays.  [launch_a_first_auxv_pair_is_sysinfo_ehdr] and its
    twin check that the word read there is AT_SYSINFO_EHDR's (tag 33).

    - launch C is a launch the launch rules admit ([launch_c_admitted]:
      [Run.entry_launch_ok_va]) on which [sp - stack_max_size] is below
      the mmap base, with argv strings long enough to get there; it reads
      AT_SYSINFO_EHDR from [Run.launch_auxv]. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Vdso Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel Require Vdso.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require EntryLaunch.
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

(** A launch where [sp - stack_max_size] is below the mmap base, with
    randomization on ([State.default_kernel] has [kb_aslr] and a 256-page
    guard gap).  Two of its numbers are checked below: the stack's top at
    its lowest, [0x7fffc0000000] ([launch_b_lowest_stack_top], from
    [Run.valid_stack_top_va]'s bound), and the mmap base at mmap draw 0
    ([launch_b_base_is_the_launch_base_at_draw_0]).  The third, [sp]
    0x180400 bytes below that top, is NOT derived here: it is the offset
    that about 1.5 MiB of argv and envp strings give through
    [Run.launch_sp_hi], and this file lays no strings (see "Both values
    depend ..." above).  The test needs only a launch on which
    [sp - stack_max_size] is below the base
    ([launch_b_stack_is_close_above_the_base]); that the launch rules
    admit such launches is SCOPE.md's R-a.  Then [sp - stack_max_size] is
    0x81400 bytes below the base. *)
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
   Launch C: an admitted launch on which the two used to differ
   ========================================================================= *)

(** Launch B's block is laid from [sp] to a top just above it, so it is
    not a launch the launch rules admit.  Launch C is one:
    [launch_c_admitted] proves [Run.entry_launch_ok_va] for it, the
    fifth conjunct of [Run.valid_entry_va].  It is
    [Checks.Cases.EntryLaunch]'s randomized fixture at the far end of
    every draw ([a1_aslr_admitted_base_hi]: the stack's top at its
    lowest, [0x7fffc0000000]; the mmap base at draw 0, [0x7fffbf701000])
    with nine argv strings of 131071 bytes each, the longest a string
    may be with its NUL ([MAX_ARG_STRLEN], include/uapi/linux/binfmts.h).
    Their 1179650 bytes put the highest [sp] the launch rules admit at
    [0x7fffbfedfdb0] ([Run.launch_sp_hi]), and [sp - stack_max_size] then
    lies 0x21250 bytes below the base.

    The pair sits below [page_round_down (sp - stack_max_size)], its text
    at [0x7fffbf6dd000].  AT_SYSINFO_EHDR names that text; before it was
    read from the pair it named [mbase - 2 pages], [0x7fffbf6ff000],
    above the pair's top.  This launch's block is 1.2 MB of strings, so
    the Examples read AT_SYSINFO_EHDR from [Run.launch_auxv], not from
    the block; [launch_auxv] is what [Run.entry_stack_image] lays. *)
Module EL := LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EntryLaunch.

Definition long_arg : list byte := repeat (Z_to_bv 8 97) 131071.
Definition argv_c : list (list byte) := repeat long_arg 9.
Definition inp_c : ProcInput :=
  EL.a1_input_argv argv_c EL.a1_execfn (EL.a1_kernel true).

Local Lemma bvu : forall z,
  0 <= z < 18446744073709551616 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z H. apply bv_unsigned_Z_to_bv_u64.
  unfold two_pow_64. change (2 ^ 64) with 18446744073709551616. exact H.
Qed.

Example launch_c_string_bytes :
  launch_string_bytes (in_argv inp_c) (in_envp inp_c) (in_execfn inp_c)
  = 1179650%nat.
Proof. vm_compute. reflexivity. Qed.

Example launch_c_sp_is_the_highest :
  launch_sp_hi (Z_to_bv 64 0x7fffc0000000) inp_c = 0x7fffbfedfdb0.
Proof. vm_compute. reflexivity. Qed.

(** THE LAUNCH IS ADMITTED. *)
Example launch_c_admitted :
  entry_launch_ok_va Sv48
    (EL.a1_entry 0x7fffbfedfdb0 0x7fffbf701000 0x7fffc0000000) inp_c.
Proof.
  cbn [entry_launch_ok_va EL.a1_entry EL.a1_draw en_draw ed_top].
  split; [|split].
  - unfold valid_stack_top_va. rewrite (bvu 0x7fffc0000000 ltac:(lia)).
    repeat split; vm_compute; congruence.
  - unfold valid_launch_sp. rewrite (bvu 0x7fffbfedfdb0 ltac:(lia)).
    repeat split; vm_compute; congruence.
  - exists 0. split; [lia|]. split; [intros _; vm_compute; congruence|].
    split; [intros Hc; discriminate Hc|].
    rewrite (bvu 0x7fffbf701000 ltac:(lia)). vm_compute. reflexivity.
Qed.

Example launch_c_stack_is_close_above_the_base :
  (0x7fffbfedfdb0 - stack_max_size <? 0x7fffbf701000) = true.
Proof. vm_compute. reflexivity. Qed.

Definition sp_c : word := Z_to_bv 64 0x7fffbfedfdb0.
Definition mbase_c : word := Z_to_bv 64 0x7fffbf701000.

(** The text this launch maps, from its own kernel build. *)
Example launch_c_places_the_text_below_the_stack_bound :
  option_map (fun s => Z.of_N (seg_base s))
    (find seg_vdso_text (vdso_segments (in_kernel inp_c) sp_c mbase_c))
  = Some 0x7fffbf6dd000.
Proof. vm_compute. reflexivity. Qed.

(** AT_SYSINFO_EHDR names it. *)
Example launch_c_auxv_names_the_placed_text :
  bv_unsigned (la_sysinfo_ehdr (launch_auxv inp_c sp_c mbase_c))
  = 0x7fffbf6dd000.
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   For every launch
   ========================================================================= *)

(** The Examples above are three launches.  [VdsoSegs] states the
    equality for every input, [sp] and mbase
    ([launch_auxv_sysinfo_ehdr_is_the_text]); this prints what that
    proof rests on.  The build log shows one axiom, [PrimString.string],
    the type of the segments' byte chunks ([MemImageType.Segment]), which
    the repository's assumption audit permits. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import VdsoSegs.
Print Assumptions launch_auxv_sysinfo_ehdr_is_the_text.
