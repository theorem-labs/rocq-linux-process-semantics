(** * LinuxProcessSem.Checks.EntryStackFits — what the entry-stack ceiling buys

    Not part of the trusted specification: QA on the definitions, in the
    style of [Checks/Examples.v] and [Checks/VmMapsDisjoint.v].

    [Run.valid_entry] has a conjunct, [Run.entry_stack_fits], saying
    the initial stack image ends at or below [State.sp_window_hi] — the
    top of the user address space the declared VA environment provides
    (riscv64's [STACK_TOP], derived on [State.sp_window_hi]).  A premise
    that excluded nothing would be no premise, and a premise that
    excluded a real kernel placement would be a soundness hole in
    [Equivalence.strong_universal_T] rather than a fix, so both
    directions are pinned here:

    - PART 1, the conjunct BITES: placements [Run.valid_sp] admits and
      no kernel can produce are refused — at the window's top
      endpoint, and in its interior for an argv near the [valid_argv]
      limit.
    - PART 2, the conjunct EXCLUDES NOTHING REAL: [near_top_sp], a
      stack pointer just below the top of the address space, is still
      admitted.  Its offset is stated once, at that definition, and so
      is what it does and does not claim: it is the model's SPAN
      rounded up, not the block a launch writes and not a placement a
      kernel produces.  The kernel placement is stated beside it, read
      off [Run.launch_sp_hi] — 528 bytes below the top for the minimal
      input — and it is inside the same band.  This is the direction an
      alternative — subtracting the worst-case image from
      [sp_window_hi] once and for all — would get wrong, and Part 2
      says so with the arithmetic rather than in prose.
    - PART 3, the SPAN is a FLOOR the real block clears:
      [Run.entry_stack_span] is the bound [entry_stack_fits] is stated
      against, and the launch now writes a 27-entry auxv — 29 with
      CONFIG_RSEQ — and the exec file name on top of the vectors, so
      the real head plus strings is LARGER than the span at every
      input.  The ceiling therefore never pretends the block is
      smaller than the launch writes it, and it still leaves Part 2's
      band open.
    - PART 4, what the conjunct does to the statements ABOVE it: an
      entry-inhabitation hypothesis may only be asked at the VALID
      inputs.  Over all inputs it is unsatisfiable — an argv nothing
      bounds outruns the whole sp window — so a lemma taking the
      unrestricted form would be dead rather than strong.  Part 4 is
      the negative that keeps
      [EquivalenceDefinition.Classifier.decides_accepts_iff] and its two
      siblings from taking that form.

    Which of the four reasons at the top of [Checks/Examples.v]: the
    FIRST — every lemma here is a [forall] over admissible entries and
    inputs — and the THIRD, since the sp window is a model constant. *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  Equivalence FinInput Classifier.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   PART 1 — the conjunct bites
   ========================================================================= *)

(** The span is positive whatever the input: the argc word, the two NULL
    terminators, the auxv and the AT_RANDOM block are there even for an
    empty argv and envp.  Everything in Part 1 rests on this, so it is
    stated once rather than re-derived. *)
Lemma entry_stack_span_pos : forall argv envp,
  (191 <= entry_stack_span argv envp)%Z.
Proof.
  intros argv envp.
  pose proof (total_arg_bytes_nonneg argv).
  pose proof (total_arg_bytes_nonneg envp).
  pose proof (Nat2Z.is_nonneg (length argv)).
  pose proof (Nat2Z.is_nonneg (length envp)).
  unfold entry_stack_span. lia.
Qed.

(** The top of the sp window is a 16-byte-aligned address inside it, so
    [valid_sp] admits it — the premise without the conjunct. *)
Lemma valid_sp_admits_window_top : valid_sp (Z_to_bv 64 sp_window_hi).
Proof.
  unfold valid_sp, sp_window_lo, sp_window_hi.
  rewrite Z_to_bv_unsigned, bv_wrap_small
    by (unfold bv_modulus; cbn; lia).
  lia.
Qed.

(** ...and [entry_stack_fits] refuses it, for EVERY input.  An [sp] at
    [STACK_TOP] puts argc itself at the first address above the user
    address space; there is no argv or envp small enough to rescue it.
    This is the endpoint case, and the one that makes the pair above a
    proof that the conjunct removes something rather than a restatement
    of [valid_sp]. *)
Lemma entry_stack_fits_refuses_window_top : forall argv envp,
  ~ entry_stack_fits (Z_to_bv 64 sp_window_hi) argv envp.
Proof.
  intros argv envp H. unfold entry_stack_fits in H.
  pose proof (entry_stack_span_pos argv envp).
  revert H.
  rewrite Z_to_bv_unsigned, bv_wrap_small
    by (unfold bv_modulus, sp_window_hi; cbn; lia).
  lia.
Qed.

(** And the same refusal read through [Run.valid_entry] itself, which is
    the predicate [Equivalence.strong_universal_T] quantifies over.  The
    lemma above is about [entry_stack_fits] in isolation, so it survives
    the conjunct being dropped from [valid_entry] — this one does not,
    and it is what makes the file a test of the change rather than of a
    definition beside it. *)
Lemma valid_entry_refuses_window_top : forall img brk mb rnd inp,
  ~ valid_entry img (mkEntry (Z_to_bv 64 sp_window_hi) brk mb rnd) inp.
Proof.
  intros [segs pc ph] brk mb rnd inp H.
  unfold valid_entry in H. cbn [valid_entry_va] in H.
  destruct (in_va_size inp).
  - (* Sv39: the top of the Sv48 window is 254 GiB above the Sv39 one,
       so the window itself refuses it before the ceiling is asked *)
    destruct H as [(_ & Hhi & _) _].
    unfold va_sp_window_hi, va_stack_top, sv39_task_size in Hhi.
    rewrite Z_to_bv_unsigned, bv_wrap_small in Hhi
      by (unfold bv_modulus, sp_window_hi; cbn; lia).
    unfold sp_window_hi in Hhi. lia.
  - destruct H as [_ [_ [_ [Hfits _]]]].
    apply entry_stack_fits_va_sv48 in Hfits.
    exact (entry_stack_fits_refuses_window_top _ _ Hfits).
  - (* Sv57 shares the Sv48 ceiling *)
    destruct H as [_ [_ [_ [Hfits _]]]].
    unfold entry_stack_fits_va, va_sp_window_hi, va_stack_top in Hfits.
    exact (entry_stack_fits_refuses_window_top _ _ Hfits).
Qed.

(** The conjunct bites in the INTERIOR of the window too, not only at its
    endpoint: a megabyte below the top is a placement a kernel really can
    choose, but not while carrying an argv near the [valid_argv] limit of
    2097152 bytes — those strings would run past the last user address.
    Stated over all such [sp] and argv rather than at a witness, because
    the claim is about the band and not about one address. *)
Lemma entry_stack_fits_refuses_interior : forall sp argv envp,
  (sp_window_hi - 1048576 <= bv_unsigned sp)%Z ->
  (1048576 <= total_arg_bytes argv)%Z ->
  ~ entry_stack_fits sp argv envp.
Proof.
  intros sp argv envp Hsp Hargv H. unfold entry_stack_fits in H.
  pose proof (total_arg_bytes_nonneg envp).
  pose proof (Nat2Z.is_nonneg (length argv)).
  pose proof (Nat2Z.is_nonneg (length envp)).
  unfold entry_stack_span in H. lia.
Qed.

(* =========================================================================
   PART 2 — the conjunct excludes nothing a kernel can produce
   ========================================================================= *)

(** The minimal input Linux delivers: argc = 1 with an empty argv[0] (the
    kernel rewrites an empty [execve] argv to exactly this, commit
    dcd46d897adb — see [valid_argv]) and no environment.  Its SPAN is
    216 bytes; the block the launch really writes at it is larger, and
    [minimal_head_and_strings] in Part 3 measures both. *)
Definition minimal_argv : list (list byte) := [[]].
Definition minimal_envp : list (list byte) := [].

Lemma minimal_span : entry_stack_span minimal_argv minimal_envp = 216%Z.
Proof. reflexivity. Qed.

(** 224 bytes below the top of the address space: 16-byte aligned, inside
    the sp window, and enough room for that 216-byte span.  224 is the
    SPAN rounded up to a multiple of 16 — not a block, and not a kernel
    measurement.  The launch's own minimal block is larger and its
    entry [sp] is 528 bytes below the top ([minimal_launch_sp_hi]),
    because [StackLayout]'s auxv carries all 27 entries
    [create_elf_tables] and riscv's [ARCH_DLINFO] emit — 16
    unconditional [NEW_AUX_ENT]s, [AT_SYSINFO_EHDR], eight
    cache-descriptor entries and [AT_MINSIGSTKSZ], 29 of them with
    CONFIG_RSEQ — and the launch pushes the [AT_EXECFN] pathname
    string below them.  What this witness is for is the COMPARISON in
    [worst_case_ceiling_would_refuse_a_real_placement] below: with
    [PF_RANDOMIZE] clear, [randomize_stack_top] returns
    [PAGE_ALIGN(STACK_TOP)] unchanged (mm/util.c, Linux v6.18.46, commit
    1f99e9ab748f), and [setup_arg_pages] page-aligns back over
    [arch_align_stack]'s subtraction (fs/exec.c, same tree), so the entry
    [sp] a kernel really produces for a small argv and envp is within a
    few hundred bytes of [sp_window_hi] — far above
    [sp_window_hi - entry_stack_span_max], which is the line the
    absolute alternative would draw.  That real placement is no longer
    argued in prose alone: the fifth conjunct of [Run.valid_entry_va]
    pins it, and [worst_case_ceiling_would_refuse_the_real_launch]
    states the comparison at it. *)
Definition near_top_sp : word := Z_to_bv 64 (sp_window_hi - 224).

Lemma near_top_sp_unsigned : bv_unsigned near_top_sp = (sp_window_hi - 224)%Z.
Proof.
  unfold near_top_sp.
  rewrite Z_to_bv_unsigned, bv_wrap_small
    by (unfold bv_modulus, sp_window_hi; cbn; lia).
  reflexivity.
Qed.

Lemma valid_sp_near_top : valid_sp near_top_sp.
Proof.
  unfold valid_sp. rewrite near_top_sp_unsigned.
  unfold sp_window_lo, sp_window_hi. lia.
Qed.

Lemma entry_stack_fits_admits_near_top :
  entry_stack_fits near_top_sp minimal_argv minimal_envp.
Proof.
  unfold entry_stack_fits. rewrite near_top_sp_unsigned, minimal_span. lia.
Qed.

(** What Part 2 is really about.  The alternative to a per-run premise is
    an absolute one: keep [valid_entry] blind to the input and subtract
    the worst-case image ([entry_stack_span_max], the
    [valid_argv]/[valid_envp] limits) from [sp_window_hi] instead.  That
    is a smaller change and needs no new argument — and it refuses
    [near_top_sp], and with it the whole 2238671-byte band beneath
    [sp_window_hi] that a kernel with randomization off and a small argv
    and envp places [sp] inside.  Refusing
    it would not cost provability, it would cost COVERAGE: the excluded
    runs are real, and [strong_universal_T] would stop saying anything
    about them.  That asymmetry is why the premise is stated per run. *)
Lemma worst_case_ceiling_would_refuse_a_real_placement :
  (bv_unsigned near_top_sp > sp_window_hi - entry_stack_span_max)%Z
  /\ (bv_unsigned near_top_sp + entry_stack_span minimal_argv minimal_envp
      <= sp_window_hi)%Z.
Proof.
  rewrite near_top_sp_unsigned, minimal_span.
  unfold entry_stack_span_max, sp_window_hi. lia.
Qed.

(** The same comparison at the placement the fifth conjunct of
    [Run.valid_entry_va] really admits, rather than at a model-side
    rounding of the span.  [Run.launch_sp_hi] reads the exec file name,
    argv, envp and the [State.KernelBuild] of the input it is given and
    nothing else, so the credentials, file system and input stream of
    this record are filler — it exists to carry the minimal argv and
    envp into [launch_sp_hi], not to be a valid input. *)
Definition minimal_input : ProcInput :=
  mkProcInput minimal_argv minimal_envp [] IEof (Z_to_bv 64 0) (Z_to_bv 64 0)
              [] net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc false
              Sv48.

(** With no draw at all — the stack VMA ending exactly at [STACK_TOP]
    and [arch_align_stack] subtracting nothing — Linux puts the entry
    stack pointer 528 bytes below the top of the address space: a
    512-byte head ([StackLayout.block_head_size] with CONFIG_RSEQ: four
    vector items and a 29-entry auxv), three bytes of strings, and the
    eight-byte slot [create_init_stack_vma] (mm/vma_exec.c, Linux
    v6.18.46, commit 1f99e9ab748f) leaves at the top, with
    [create_elf_tables]'s 16-alignment mask taking the remainder. *)
Lemma minimal_launch_sp_hi :
  launch_sp_hi (Z_to_bv 64 sp_window_hi) minimal_input
  = (sp_window_hi - 528)%Z.
Proof. vm_compute. reflexivity. Qed.

(** ...and 528 bytes is INSIDE the band the absolute alternative
    refuses, by more than two megabytes.  This is Part 2's claim at a
    kernel placement, not at a witness chosen here. *)
Lemma worst_case_ceiling_would_refuse_the_real_launch :
  (sp_window_hi - entry_stack_span_max
   < launch_sp_hi (Z_to_bv 64 sp_window_hi) minimal_input)%Z.
Proof.
  rewrite minimal_launch_sp_hi.
  unfold entry_stack_span_max, sp_window_hi. lia.
Qed.

(* =========================================================================
   PART 3 — the span is a floor the real block clears, not a ceiling on it
   ========================================================================= *)

(** [entry_stack_fits] is stated against [entry_stack_span] rather than
    against [build_stack_bytes] itself, so that [Run] can reason about
    it without [StackLayout]'s layout arithmetic.  The span counts a
    160-byte auxv and no exec file name — the sizes the model's own
    launch had while its auxv was ten entries — so it is now a FLOOR on
    the real head plus strings and not a ceiling on them.  What keeps
    the real image inside the address space is the fifth conjunct,
    [Run.entry_launch_ok_va], which pins the stack VMA's end, the entry
    stack pointer and the mmap base to the kernel's own three rules;
    [Run.entry_launch_ok_va_fits] derives this ceiling from it, so the
    two cannot drift apart.

    Keeping the ceiling BELOW the block is what makes it safe: a
    premise that over-estimated the block would refuse address space a
    real image can use, which is Part 2's exclusion creeping back in a
    smaller size.  The floor below holds at every input and for either
    CONFIG_RSEQ setting, and the measurement after it shows the gap at
    the minimal input is 307 bytes — nothing beside the 2238671-byte
    band Part 2 is about. *)
Lemma entry_stack_span_is_a_floor_on_the_block :
  forall rseq argv envp execfn,
  (entry_stack_span argv envp
   <= Z.of_nat (block_head_size rseq argv envp
                + launch_string_bytes argv envp execfn + 8))%Z.
Proof.
  intros rseq argv envp execfn.
  pose proof (block_head_size_bounds rseq argv envp) as [HCl _].
  pose proof (launch_string_bytes_ge argv envp execfn) as HL.
  pose proof (total_arg_bytes_nonneg argv).
  pose proof (total_arg_bytes_nonneg envp).
  rewrite !Nat2Z.inj_add.
  unfold entry_stack_span. lia.
Qed.

(** The three measurements at the minimal input, under
    [State.default_kernel] (CONFIG_RSEQ on, so a 29-entry auxv) and the
    one-byte [State.default_execfn]: a 512-byte head and three bytes of
    strings, against a 216-byte span. *)
Lemma minimal_head_and_strings :
  (Z.of_nat (block_head_size (kb_rseq default_kernel) minimal_argv minimal_envp),
   Z.of_nat (launch_string_bytes minimal_argv minimal_envp default_execfn),
   entry_stack_span minimal_argv minimal_envp)
  = (512%Z, 3%Z, 216%Z).
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   PART 4 — the conjunct bounds where an inhabitation hypothesis may be asked
   ========================================================================= *)

(** [Run.valid_entry] takes the input because [entry_stack_fits] reads
    argv and envp, and that has a consequence for every statement built
    on top of it: "this image has a valid entry" is a claim about an
    IMAGE AND AN INPUT TOGETHER, never about an image alone.  A
    hypothesis quantifying it over all inputs is therefore not a strong
    assumption but an unsatisfiable one, and a lemma carrying it proves
    nothing about anything.

    That is the shape
    [forall g, exists en, valid_entry C en
    (to_proc_input g)], over every [FinInput.FinProcInput] whether valid
    or not.  This part is the negative test for that mistake — it
    exhibits the input no image can serve — together with the positive
    pin that the per-valid-input form that
    [EquivalenceDefinition.Classifier.decides_accepts_iff],
    [decides_rejects_iff] and [decides_accepts_or_rejects] take is the one
    [Equivalence.image_brk_satisfiable_entry] actually produces.

    Which of the four reasons at the top of [Checks/Examples.v]: the
    FIRST, a [forall] over images and entries, and the THIRD — the
    argument turns on [State.sp_window_lo] and [State.sp_window_hi],
    model constants no run reveals. *)

(** The witness: an argv of 268435457 empty strings.  Its argv POINTER
    ARRAY alone is 8 * 268435457 = 2147483656 bytes, eight more than the
    2147483648-byte sp window ([State.sp_window_hi] - [State.sp_window_lo]),
    so no stack pointer [valid_sp] admits leaves room for it — the
    strings themselves, and the rest of the block, are not even needed
    for the contradiction.  Empty strings rather than long ones keeps
    the arithmetic in the pointer array, where it can be read off the
    length; [Nat.pow] rather than a numeral keeps the [nat] out of
    unary. *)
Definition oversized_argv : list (list byte) :=
  repeat (@nil byte) (Nat.pow 2 28 + 1).

Lemma oversized_argv_length : Z.of_nat (length oversized_argv) = 268435457%Z.
Proof.
  unfold oversized_argv.
  rewrite repeat_length, Nat2Z.inj_add, Nat2Z.inj_pow.
  reflexivity.
Qed.

(** [hwcap_rv64gc] rather than a zero word, and the choice is not
    cosmetic: this witness exists to be REFUSED, and it has to be refused
    for its argv.  A zero hwcap is not a word [Run.valid_hwcap] admits, so
    an input carrying one would be rejected whatever its argv did, and the
    lemma below would hold for a reason it does not state. *)
Definition oversized_input : FinProcInput :=
  mkFinProcInput oversized_argv [] [] [] (Z_to_bv 64 0) (Z_to_bv 64 0) []
                 net_silent (Z_to_bv 64 0) (Z_to_bv 64 0) hwcap_rv64gc false Sv48
                 [] [] default_kernel default_execfn true true false.

(** The band the POINTER ARRAY alone excludes, stated over every [sp],
    argv and envp rather than at the witness: 268435457 argv entries need
    2147483656 bytes of [char *] before a single string is written, eight
    more than the sp window is wide, so no [Run.valid_sp] stack pointer
    can carry them.  Abstract arguments also keep [lia] away from the
    witness list below, which is a closed term nothing should reduce. *)
Lemma entry_stack_fits_refuses_oversized_argc : forall sp argv envp,
  (sp_window_lo <= bv_unsigned sp)%Z ->
  (268435457 <= Z.of_nat (length argv))%Z ->
  ~ entry_stack_fits sp argv envp.
Proof.
  intros sp argv envp Hlo Hargc H.
  unfold entry_stack_fits, entry_stack_span in H.
  pose proof (total_arg_bytes_nonneg argv).
  pose proof (total_arg_bytes_nonneg envp).
  pose proof (Nat2Z.is_nonneg (length envp)).
  unfold sp_window_lo in Hlo. unfold sp_window_hi in H.
  lia.
Qed.

(** THE NEGATIVE TEST.  No image whatever has a valid entry at every
    finite input, so the unrestricted inhabitation hypothesis is false
    for every [C] and a lemma taking it can be applied to nothing.
    Stated over [C] rather than at a witness image: the failure is in the
    input, and no image can repair it. *)
Lemma no_image_has_an_entry_for_every_input : forall C : Image,
  ~ (forall g, exists en, valid_entry C en (to_proc_input g)).
Proof.
  intros [segs pc ph] H.
  destruct (H oversized_input) as [[sp brk mb rnd] Hen].
  unfold valid_entry in Hen. cbn [valid_entry_va in_va_size to_proc_input fin_va_size oversized_input] in Hen.
  destruct Hen as [[Hlo _] [_ [_ [Hfits _]]]].
  apply entry_stack_fits_va_sv48 in Hfits.
  unfold va_sp_window_lo, va_stack_top in Hlo.
  change (sp_window_hi - 2 * 1024 * 1024 * 1024)%Z with sp_window_lo in Hlo.
  revert Hfits.
  apply entry_stack_fits_refuses_oversized_argc; [exact Hlo |].
  cbn [in_argv to_proc_input fin_argv oversized_input].
  rewrite oversized_argv_length. apply Z.le_refl.
Qed.

(** ...and the input that kills it is one the per-valid-input form never
    asks about, which is what makes the restriction a fix rather than a
    dodge: [Run.valid_argv] caps argc at 1024. *)
Lemma oversized_input_is_not_valid : ~ valid_fin_input oversized_input.
Proof.
  intros [[[_ Hlen] _] _].
  (* [reflexivity] here is a weak-head unfolding of the record projection
     through [to_proc_input]; it never looks inside [oversized_argv].  A
     [cbn] here would leave the kernel a conversion it settles at [Qed]
     by computing the witness list's [length] in unary. *)
  assert (Hargv : in_argv (to_proc_input oversized_input) = oversized_argv)
    by reflexivity.
  rewrite Hargv, oversized_argv_length in Hlen. lia.
Qed.

(** THE POSITIVE PIN, in two steps.  First: the well-formedness
    assertion a checker makes about the classifier image really does
    yield the per-valid-input hypothesis — [image_brk_satisfiable_entry]
    needs [Run.valid_input] for the input, and [FinInput.valid_fin_input]
    is exactly that of [FinInput.to_proc_input], so nothing is bridged
    here. *)
Lemma image_brk_satisfiable_gives_the_per_valid_input_hypothesis :
  forall C : Image,
    image_brk_satisfiable (img_segments C) = true ->
    forall g, valid_fin_input g -> exists en, valid_entry C en (to_proc_input g).
Proof.
  intros C H g Hg.
  exact (image_brk_satisfiable_entry C (to_proc_input g) Hg H).
Qed.

(** Second: that is the hypothesis
    [EquivalenceDefinition.Classifier.decides_accepts_iff] consumes.  The
    lemma is stated so that it typechecks only while the classifier
    lemma takes the per-valid-input form — restore the unrestricted one
    and this file stops building, which is the point of pinning it here
    rather than describing it in a comment. *)
Lemma decides_accepts_iff_takes_the_per_valid_input_hypothesis :
  forall (C : Image) (spec : ProcInput -> Prop),
    decides C spec ->
    image_brk_satisfiable (img_segments C) = true ->
    forall f, valid_fin_input f -> (accepts C f <-> spec (to_proc_input f)).
Proof.
  intros C spec Hdec Hwf.
  exact (decides_accepts_iff C spec Hdec
           (image_brk_satisfiable_gives_the_per_valid_input_hypothesis C Hwf)).
Qed.
