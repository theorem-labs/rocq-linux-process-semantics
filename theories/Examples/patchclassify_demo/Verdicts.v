(** * Examples.patchclassify_demo.Verdicts — what each image does, at
      EVERY valid entry and on EVERY input

    DEMO FILE (not part of the trusted specification).  [Images] defines
    the demo's six images; this file proves the one fact about each that
    every obligation downstream is built from: it terminates, without
    erroring, with a known exit status — whatever [execve] chose for the
    stack, the break and the mmap base, whatever the process was handed
    as argv, envp, file system, standard input and credentials, and at
    whatever allocation budget the role it is playing runs at.

    ** The gap this file closes

    [MustExit.must_exit_with] is a statement about ONE run: one image,
    one budget, one [Run.ExecEntry], one [State.ProcInput].  Every
    obligation the demo owes quantifies over the last two:
    [Classifier.decides] asks for a verdict at EVERY valid entry on
    EVERY valid finite input, and [Equivalence.strong_universal_T]
    quantifies the two images' entries independently.

    [Checks.Examples.exit0_image_must_exit_zero] is the development's
    only prior run-level [must_exit_with], and it is proved at ONE
    concrete entry on ONE concrete input, by [vm_compute] on the
    fuel-bounded evaluator [Checks.Examples.exits_c].  That technique
    does not survive the quantifier: with the entry and the input as
    variables there is nothing closed left to compute.

    ** Why these programs cannot tell the difference, and how that is
       checked rather than claimed

    The demo's programs are [addi a7, x0, 93; addi a0, x0, c; ecall].
    They perform no load and no store, they fetch only from their own
    executable segment, and they read no register they did not just
    write.  So the claim is that the entry and the input reach nothing
    the execution looks at.  Three facts make that precise, and none of
    them is asserted:

    - [init_machine_state_abstracts]: the entry — its stack pointer,
      its mmap base and its launch draw, the three fields
      [Run.init_machine_state] reads — and the whole [State.ProcInput]
      reach the initial MACHINE state only
      through three components — the sp register, the writable memory
      and the read-only backing.  Everything else in
      [Run.init_machine_state] is fixed by the process model
      ([MemImageType.MemImage]'s header: every register but sp starts at
      0) or comes from the image.

    - [State.m_halted_init_model] and [init_model_no_lazy]: the two
      premises [Checks.Examples.exits_c_must_exit_at] puts on the MODEL
      hold for every break, mmap base, budget and input.  (The first is
      the library's; only the second is stated here.)  This
      is the half that makes the statements below independent of [lim],
      and it is why they can be handed to obligations stated at
      [State.source_alloc_limit], at [State.target_alloc_limit] and at
      [Classifier.classifier_alloc_limit] alike, with no per-budget
      proof.

    - the per-program premise of [must_exit_everywhere_of_exits_c]:
      [exits_c] returns [true] with the sp, the memory and the backing
      left as VARIABLES.  A program that consulted any of the three
      would leave the reduction stuck on a variable and the
      [vm_compute] would not reach [true] — so this premise is a
      machine-made check that the program is blind to them, not a
      restatement of the claim.  It is the whole indifference argument,
      and it is one tactic per program.

    ** The generic form, and what it does not cover

    [must_exit_everywhere_of_exits_c] is stated once, over an arbitrary
    image and an arbitrary code, and instantiated six times.  Its
    premise is exactly the class of programs the argument works for:
    those that reach their exit within the fuel without reading data
    memory and without a fetch that falls back into the writable
    overlay.  A program that READ ITS INPUT — the refinement the demo's
    README names as the follow-up — is outside it, and would need a
    simulation argument rather than a computation.

    ** What each theorem below is, and what it is not

    Each is [forall lim en inp, must_exit_with c X lim en inp]: no
    [Run.valid_entry] and no [Run.valid_input] hypothesis, because the
    programs do not need them.  That is STRONGER than the obligations
    consume, which is the useful direction — a consumer applies it and
    discards the validity facts it holds.  It is not stronger than is
    true: [MustExit.must_exit_with_realizes] turns each of these into an
    observable trace ending in [State.ExitEv], so none of them is a
    claim about nothing.

    The predicate pins the code and does not merely assert termination,
    and this file exercises that: [O1_does_not_exit_zero] refutes
    [must_exit_with verdict_accept] of the image that exits 1, through
    [MustExit.must_exit_with_exclusive] and
    [Classifier.verdict_accept_neq_reject]. *)

From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Examples.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  Equivalence MustExit Classifier.
From LinuxProcessSemantics.Examples.patchclassify_demo Require Import Images.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   The initial machine state, with everything the entry and the input
   touch left abstract
   ========================================================================= *)

(** [Run.init_machine_state] with its three input-dependent components
    as parameters: the stack pointer register, the writable memory and
    the read-only backing.  The other five fields are the ones the
    process model fixes — a zeroed FP file, a zeroed fcsr, no pending
    syscall, no reservation, and a pc taken from the image. *)
Definition demo_init_state (pc : N) (sp : word)
    (mem rom : word -> option byte) : machine_state :=
  {| ms_regs := bvmap_set 2 sp (bvmap_set 10 (Z_to_bv 64 0) bvmap_empty);
     ms_fregs := bvmap_empty;
     ms_pc_val := Z_to_bv 64 (Z.of_N pc);
     ms_svc_pending := None;
     ms_resv := None;
     ms_fcsr := Z_to_bv 32 0;
     ms_mem := mem;
     ms_rom := rom |}.

(** ... and it really is [Run.init_machine_state]: whatever the mmap
    base, the launch draw and the [State.ProcInput] — and the input is
    now passed WHOLE, since [Run.init_machine_state] reads the argv,
    the envp, the credentials, the kernel build and the exec file name
    off it through projections — the initial machine state is the shape
    above at SOME memory and SOME backing.  This is the first of the
    three facts in this file's header — the one that says the input
    reaches the machine through no other field, so every field the
    input grows has to be quantified here or the claim narrows without
    saying so.  Taking the input whole is what keeps that true as
    [State.ProcInput] grows: [State.in_kernel] and [State.in_execfn]
    joined it for Linux's exact entry block and neither needed a new
    parameter here. *)
Lemma init_machine_state_abstracts : forall segs pc ph sp mbase rnd inp,
  exists mem rom,
    init_machine_state segs pc ph sp mbase rnd inp
    = demo_init_state pc sp mem rom.
Proof.
  intros segs pc ph sp mbase rnd inp.
  unfold init_machine_state, demo_init_state.
  eexists. eexists. reflexivity.
Qed.

(* =========================================================================
   The model half: neither premise of [exits_c_must_exit_at] can see the
   entry, the budget or the input
   ========================================================================= *)

(** The first of the two is already in the library:
    [State.m_halted_init_model] says a freshly launched process is not
    halted, for every reserved list, break, mmap base, budget and input.
    That is [Checks.Examples.exits_c_must_exit_at]'s first premise —
    needed because a model already carrying a status would satisfy
    [MustExit.must_exit_at] by its base case, with whatever code it
    happened to hold — and it is used below rather than restated here.

    The second has no library counterpart, and is the more interesting
    of the two: the initial model holds no lazy anonymous mapping, which
    is what keeps the accounting step from taking the fault transition
    and what keeps the model FIXED across an instruction step. *)
Lemma init_model_no_lazy : forall reserved brk0 mbase sp lim inp,
  m_vm_lazy (init_model reserved brk0 mbase sp lim inp) = [].
Proof. reflexivity. Qed.

(* =========================================================================
   The indifference lemma
   ========================================================================= *)

(** THE lemma this file exists for.  A program whose fuel-bounded
    execution reaches [exit(code)] with the stack pointer, the writable
    memory and the read-only backing left abstract must exit with that
    code at EVERY entry, on EVERY input, at EVERY budget.

    The proof is the three facts from this file's header, in order: the
    two model premises, each of which holds under variable [brk0],
    [mbase], [lim] and [inp]; then [init_machine_state_abstracts] to put the
    initial machine state into the shape the premise speaks about; then
    the premise.  Nothing here is specific to these six images — the
    hypothesis is the class of programs it applies to. *)
Lemma must_exit_everywhere_of_exits_c :
  forall (segs : list Segment) (pc : N) (ph : PhdrInfo)
         (code : word) (fuel : nat),
    (forall sp mem rom,
        exits_c segs code fuel (demo_init_state pc sp mem rom) = true) ->
    forall lim en inp, must_exit_with code (mkImage segs pc ph) lim en inp.
Proof.
  intros segs pc ph code fuel Hc lim [sp brk0 mbase rnd] inp.
  cbn [must_exit_with]. unfold init_config.
  apply (exits_c_must_exit_at _ _ fuel);
    [apply m_halted_init_model | apply init_model_no_lazy |].
  destruct (init_machine_state_abstracts segs pc ph sp mbase rnd inp)
    as (mem & rom & Hshape).
  rewrite Hshape. apply Hc.
Qed.

(* =========================================================================
   The six programs pass the check
   ========================================================================= *)

(** Four steps of fuel would do — two [addi]s, the [ecall], and the look
    at the pending syscall number — and eight is used, as
    [Checks.Examples.exit0_image_must_exit_zero] uses it, so that the
    evaluator is not run at exactly its budget.  [exits_c] stops as soon
    as a syscall is pending, so the surplus costs nothing.

    Each of these six is where the indifference is actually established:
    the [sp], the [mem] and the [rom] are universally quantified, and
    the computation reaches [true] without them. *)

Lemma O1_exits_c : forall sp mem rom,
  exits_c O1m.loaded_segments verdict_reject 8
    (demo_init_state O1m.init_pc sp mem rom) = true.
Proof. intros. vm_compute. reflexivity. Qed.

Lemma O2_exits_c : forall sp mem rom,
  exits_c O2m.loaded_segments verdict_accept 8
    (demo_init_state O2m.init_pc sp mem rom) = true.
Proof. intros. vm_compute. reflexivity. Qed.

Lemma P1_exits_c : forall sp mem rom,
  exits_c P1m.loaded_segments verdict_accept 8
    (demo_init_state P1m.init_pc sp mem rom) = true.
Proof. intros. vm_compute. reflexivity. Qed.

Lemma P2_exits_c : forall sp mem rom,
  exits_c P2m.loaded_segments verdict_accept 8
    (demo_init_state P2m.init_pc sp mem rom) = true.
Proof. intros. vm_compute. reflexivity. Qed.

Lemma C1_exits_c : forall sp mem rom,
  exits_c C1m.loaded_segments verdict_reject 8
    (demo_init_state C1m.init_pc sp mem rom) = true.
Proof. intros. vm_compute. reflexivity. Qed.

Lemma C2_exits_c : forall sp mem rom,
  exits_c C2m.loaded_segments verdict_reject 8
    (demo_init_state C2m.init_pc sp mem rom) = true.
Proof. intros. vm_compute. reflexivity. Qed.

(* =========================================================================
   The six verdicts
   ========================================================================= *)

(** These are what the obligations consume.  [lim] is universally
    quantified, so the same theorem serves the patch obligation at
    [State.source_alloc_limit] and at [State.target_alloc_limit], the
    classifier obligations at [Classifier.classifier_alloc_limit], and
    the [Classifier.agree] comparisons at either role's budget. *)

(** [O1] reports failure — on every input, from every entry.  This is
    the defect: the status is wrong everywhere, not on some inputs. *)
Theorem O1_must_exit_one : forall lim en inp,
  must_exit_with verdict_reject O1_image lim en inp.
Proof.
  unfold O1_image.
  exact (must_exit_everywhere_of_exits_c _ _ _ _ 8 O1_exits_c).
Qed.

Theorem O2_must_exit_zero : forall lim en inp,
  must_exit_with verdict_accept O2_image lim en inp.
Proof.
  unfold O2_image.
  exact (must_exit_everywhere_of_exits_c _ _ _ _ 8 O2_exits_c).
Qed.

(** [P1] is [O1] repaired: same everywhere-ness, right status. *)
Theorem P1_must_exit_zero : forall lim en inp,
  must_exit_with verdict_accept P1_image lim en inp.
Proof.
  unfold P1_image.
  exact (must_exit_everywhere_of_exits_c _ _ _ _ 8 P1_exits_c).
Qed.

Theorem P2_must_exit_zero : forall lim en inp,
  must_exit_with verdict_accept P2_image lim en inp.
Proof.
  unfold P2_image.
  exact (must_exit_everywhere_of_exits_c _ _ _ _ 8 P2_exits_c).
Qed.

(** The two classifiers fire everywhere.  For [Classifier.decides] this
    is half the obligation — the totality disjunct — and the [iff] is
    then a claim about the spec side, which is where the demo's real
    content is. *)
Theorem C1_must_exit_one : forall lim en inp,
  must_exit_with verdict_reject C1_image lim en inp.
Proof.
  unfold C1_image.
  exact (must_exit_everywhere_of_exits_c _ _ _ _ 8 C1_exits_c).
Qed.

Theorem C2_must_exit_one : forall lim en inp,
  must_exit_with verdict_reject C2_image lim en inp.
Proof.
  unfold C2_image.
  exact (must_exit_everywhere_of_exits_c _ _ _ _ 8 C2_exits_c).
Qed.

(* =========================================================================
   The verdicts bite
   ========================================================================= *)

(** The wrong-code refutation, without which the six theorems above
    would be shaped like verdicts without being verdicts: [O1] does NOT
    must-exit 0, anywhere.  [MustExit.must_exit_with_exclusive] turns
    the two claims into [verdict_accept = verdict_reject], which
    [Classifier.verdict_accept_neq_reject] refutes.

    This is the run-level counterpart of
    [MustExit.must_exit_at_wrong_code], which states the same thing of
    an abstract halted configuration.  Without it, "exits 0" and "exits
    1" would be two claims that might both hold of [O1], and the
    classifier obligations — which read a verdict OFF the pair — would
    be reading nothing. *)
Theorem O1_does_not_exit_zero : forall lim en inp,
  ~ must_exit_with verdict_accept O1_image lim en inp.
Proof.
  intros lim en inp H.
  apply verdict_accept_neq_reject.
  exact (must_exit_with_exclusive _ _ _ _ _ _ H (O1_must_exit_one lim en inp)).
Qed.

(** ... and symmetrically for a patch, so that the refutation is not an
    artifact of which code the defective image reports. *)
Theorem P1_does_not_exit_one : forall lim en inp,
  ~ must_exit_with verdict_reject P1_image lim en inp.
Proof.
  intros lim en inp H.
  apply verdict_accept_neq_reject.
  exact (must_exit_with_exclusive _ _ _ _ _ _ (P1_must_exit_zero lim en inp) H).
Qed.

(** The positive guard: each verdict is realized by an observable trace
    ending in the [State.ExitEv] it names, so none of the six theorems
    is satisfied by a run that says nothing.  Stated for [O1] and [P1],
    the pair whose disagreement the patch-difference classifier is asked
    about. *)
Theorem O1_realizes_exit_one : forall lim en inp,
  exists tr fs,
    bh_traces (run O1_image lim en inp) (tr ++ [ExitEv verdict_reject fs]).
Proof.
  intros lim en inp.
  exact (must_exit_with_realizes _ _ _ _ _ (O1_must_exit_one lim en inp)).
Qed.

Theorem P1_realizes_exit_zero : forall lim en inp,
  exists tr fs,
    bh_traces (run P1_image lim en inp) (tr ++ [ExitEv verdict_accept fs]).
Proof.
  intros lim en inp.
  exact (must_exit_with_realizes _ _ _ _ _ (P1_must_exit_zero lim en inp)).
Qed.

(** No execution of any of the six errors or leaves the modeled surface,
    at any entry on any input — [MustExit.must_exit_with_no_error] and
    [MustExit.must_exit_with_modeled] applied to the verdicts.  The
    error-free obligations downstream need exactly this, and the
    [Equivalence.modeled] clause of [Equivalence.strong_equiv] needs the
    second half. *)
Theorem P1_error_free : forall lim en inp,
  ~ bh_errors (run P1_image lim en inp).
Proof.
  intros lim en inp.
  exact (must_exit_with_no_error _ _ _ _ _ (P1_must_exit_zero lim en inp)).
Qed.

Theorem P2_error_free : forall lim en inp,
  ~ bh_errors (run P2_image lim en inp).
Proof.
  intros lim en inp.
  exact (must_exit_with_no_error _ _ _ _ _ (P2_must_exit_zero lim en inp)).
Qed.

Theorem O1_error_free : forall lim en inp,
  ~ bh_errors (run O1_image lim en inp).
Proof.
  intros lim en inp.
  exact (must_exit_with_no_error _ _ _ _ _ (O1_must_exit_one lim en inp)).
Qed.

Theorem O2_error_free : forall lim en inp,
  ~ bh_errors (run O2_image lim en inp).
Proof.
  intros lim en inp.
  exact (must_exit_with_no_error _ _ _ _ _ (O2_must_exit_zero lim en inp)).
Qed.

Theorem P1_modeled : forall lim en inp,
  ~ bh_unmodeled (run P1_image lim en inp).
Proof.
  intros lim en inp.
  exact (must_exit_with_modeled _ _ _ _ _ (P1_must_exit_zero lim en inp)).
Qed.

Theorem P2_modeled : forall lim en inp,
  ~ bh_unmodeled (run P2_image lim en inp).
Proof.
  intros lim en inp.
  exact (must_exit_with_modeled _ _ _ _ _ (P2_must_exit_zero lim en inp)).
Qed.

Theorem O1_modeled : forall lim en inp,
  ~ bh_unmodeled (run O1_image lim en inp).
Proof.
  intros lim en inp.
  exact (must_exit_with_modeled _ _ _ _ _ (O1_must_exit_one lim en inp)).
Qed.

Theorem O2_modeled : forall lim en inp,
  ~ bh_unmodeled (run O2_image lim en inp).
Proof.
  intros lim en inp.
  exact (must_exit_with_modeled _ _ _ _ _ (O2_must_exit_zero lim en inp)).
Qed.
