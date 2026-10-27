(** * Equivalence — trusted theorem shape for equivalence proofs

    TRUST BOUNDARY: this file is part of the trusted specification.
    Proof files never edit it.  The top-level check depends on the
    definitions here remaining fixed.

    The theorem is observable equivalence between a "source memory
    image" and an "target memory image" — both compiled binaries imported
    with the ELF loader.  Observable behavior is [LinuxProcessSem.Run.run]: the
    prefix-closed set of finite event traces (byte-level channel I/O plus
    exit-with-file-system) a binary admits under the non-deterministic
    syscall model, together with may-error and all-executions-error
    facts.  [equiv] (defined here) compares two behaviors, with the
    escape that a source whose every execution errors frees the target.

    That escape is the theorem's vacuity risk, so [strong_equiv] carries
    a SECOND clause, [modeled]: on every input, the source must never
    reach a configuration the semantics declines to interpret.  A source
    is allowed to CRASH (the model faithfully models crashes); it is not
    allowed to run off the edge of the model.  Without this clause a
    binary using an unmodeled syscall would satisfy the theorem trivially
    — every execution would error, the escape would fire, and the target
    would never be looked at.  See [modeled] below.

    The run is a function of the inputs grouped into the
    [State.ProcInput] record — universally quantified (over the
    validity predicates defined with the process model —
    [Run.valid_argv], [Run.valid_envp], [Fs.valid_fs],
    [Fs.fs_keys_relative], [Run.valid_creds] — where there is one): the
    argv strings, the envp strings, the initial file-system image (whose
    keys are cwd-relative, the premise the device arms rest on — see
    [Run.valid_input]), the LAUNCHING USER AND GROUP
    ([State.in_uid] / [State.in_gid], which the credential syscalls
    report — the model does not know which user started the process, so
    it quantifies over every user it could have been rather than
    inventing one), the SUPPLEMENTARY GROUP LIST ([State.in_groups],
    which [getgroups] counts, quantified for the same reason), the
    STANDARD INPUT STREAM, and the NETWORK the environment offers.  The stream is a colist of bytes
    ([State.InputStream]: coinductive, so an input may be infinite, with
    an [IEof] constructor marking a finite one's end); the network is
    [State.in_net], a [State.NetQueue] naming the connections [accept]
    will hand over, in order, and what each peer sends once accepted.
    Both are supplied up front, so a program's observable behavior is a
    FUNCTION of its input rather than of an internal nondeterministic
    choice, and source and target are compared on the SAME input.
    Quantifying the peer this way, rather than drawing it
    nondeterministically inside the semantics, is also what keeps the
    socket arms falsifiable — a spec that both succeeds and declines at
    one [(i, m)] is impossible against a total checker.

    Neither carries a validity predicate, but not for the same reason.
    The stream needs none and loses nothing: its elements are [byte], so
    every colist of bytes is a real input AND every real input is a
    colist of bytes.  [State.NetQueue] needs none either — every one of
    them is a network some environment could present — but the converse
    fails, because [State.NetQueue] has no nil: an environment that
    simply never connects cannot be written down, so the quantifier
    ranges over strictly fewer networks than exist.  That is a
    deliberate under-approximation, and it narrows the theorem
    rather than weakening it.
    What remains nondeterministic about a read is only how many of the
    available bytes it delivers (short reads); end-of-file is where the
    stream says it is, and is sticky by construction ([IEof] has no
    successor).

    The baseline proof obligation is [strong_universal].  [SPEC] is the
    module type each per-problem proof must satisfy, and
    [strong_universal] is the theorem the Checker pins.

    Some tasks are the other way round: erroring is itself the defect
    being ruled out — a sandbox that must not fault, or an instrumented
    build proved equivalent to the plain one — and "the source crashes
    too" is not an acceptable answer.
    [strong_universal_error_free_T], with its sealing surface
    [SPEC_ERROR_FREE], is the theorem shape for those.  It is a
    SEPARATE, strictly stronger obligation rather than a change to the
    baseline: nothing about [strong_universal] moves,
    existing proofs and checkers see no change, and
    [strong_universal_error_free_implies] records the one-way
    relationship — whatever is proved in the stronger shape discharges
    the baseline statement, never the reverse.  A task must therefore OPT
    IN, which is as it should be, since the stronger shape is unprovable
    for any source that can crash however faithful the target.

    Representation: this is the bitvector development — the quantified
    stack pointers and break bases are [word = bv 64], argv/envp are
    byte ([bv 8]) string lists, and the fixed a0 seed
    ([Run.init_machine_state]'s x10) is the zero word.  [MemImage]
    snapshot modules are unchanged ([N]-based; see MemImageType.v). *)

From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   Equivalence of two behaviors
   ========================================================================= *)

(** Equality of the finite-prefix sets. *)
Definition trace_equiv (T1 T2 : list event -> Prop) : Prop :=
  forall tr, T1 tr <-> T2 tr.

(** Observable equivalence of two binaries:

    - ESCAPE: if EVERY execution of the SOURCE reaches the error
      transition, the task is vacuous and any target behavior is
      accepted.  This is [bh_all_errors], not the existential
      [bh_errors]: one erroring nondeterministic resolution does not free
      the target when another source resolution avoids error.
    - Otherwise the target must match the source's finite-prefix set
      exactly AND must not be able to error on ANY execution.  A target
      that can take the error transition could otherwise hide arbitrary
      unmodeled behavior — including unmodeled syscalls — behind
      trace-set equality of the modeled part.

    Note that refinement (target prefixes ⊆ source prefixes) would be
    too weak on its own: the empty-forever target — silent divergence —
    satisfies it vacuously.  Set EQUALITY forces the target to be exactly
    as productive as the source: every source prefix, including
    those ending in [ExitEv], must also be a target prefix. *)
Definition equiv (source target : behavior) : Prop :=
  bh_all_errors source \/
  (trace_equiv (bh_traces source) (bh_traces target) /\ ~ bh_errors target).

(** The two policy consequences, stated directly for downstream users. *)
Lemma all_source_traces_error_equiv_any : forall source target,
  bh_all_errors source -> equiv source target.
Proof. intros source target Hall. left. exact Hall. Qed.

Lemma source_not_all_errors_target_never_errors : forall source target,
  equiv source target -> ~ bh_all_errors source -> ~ bh_errors target.
Proof.
  intros source target [Hall | [_ Htarget]] Hsurvives;
    [contradiction | exact Htarget].
Qed.

(* =========================================================================
   Coverage of the source by the model
   ========================================================================= *)

(** The model COVERS this run: it never reaches a configuration where the
    semantics declines to say what happens.

    This is a statement about the SEMANTICS, not about the program, and
    it is the anti-vacuity clause of the theorem.  [equiv] alone can be
    satisfied cheaply by an insufficient model: a source binary that
    issues a syscall this development does not model, or executes an
    instruction it does not decode, hits the fail-closed error transition
    on every execution, [bh_all_errors] holds, the ESCAPE fires, and the
    target is freed without ever being analyzed.  The resulting theorem
    is true and says nothing.  [modeled] closes that hole: the proof must
    exhibit a source whose every reachable configuration is one the model
    has an answer for.

    Crucially this is NOT "the source never errors".  Erroring and being
    unmodeled are different things, and only the second is forbidden:

    - the source may FAULT — a wild jump, a load from an unmapped
      address, a store into a read-only segment, an [ebreak], an
      instruction the ARCHITECTURE defines illegal (the all-zero parcel,
      or the write to a read-only CSR that GNU as's [unimp] is, so a
      fired -fsanitize-trap check lands here).  A real
      Linux process dies there too, so the model has modeled it, and the
      equivalence task is about a program that crashes.  That is a
      legitimate task (see the deliberate-bug examples), and it still
      gets the [bh_all_errors] escape.
    - the source may not run off the edge of the MODEL — an undecodable
      word the architecture does not itself define illegal, an
      instruction the ISA semantics declines ([EIllegal] — an
      unknown CSR address it does not define illegal either, or a
      reserved FP rounding mode), a syscall outside
      [Specs.modeled_sysnos], unmodeled flags, or an IMAGE this
      development declines to fetch from (snapshot hex the
      decoder cannot read: see [RiscvSemantics.fetch_failure],
      which is why such a fetch is [MachineUnmodeled] and not a fault —
      real hardware executes those pages, so calling them a crash would
      hand exactly this escape to a binary that works).  There the escape
      would be an artifact of this development's incompleteness rather
      than a fact about the binary, so it is ruled out.

    What the clause does NOT reach: an approximation that answers
    CONFIDENTLY but wrongly is invisible to it, because the model never
    declines.  Keeping specs fail-closed (`unmodeled`, not an invented errno)
    is therefore what makes this clause bite.

    See [Run.unmodeled_at] for the exact split,
    [Run.reaches_unmodeled_reaches_error] for the containment, and
    [Run.reaches_unmodeled_intro] plus
    [Checks.Examples.run_of_undecodable_image_refutes_modeled] for the
    non-vacuity witness (a clause no binary could violate would be no
    clause at all). *)
Definition modeled (b : behavior) : Prop := ~ bh_unmodeled b.

(* =========================================================================
   Error-freedom of one behavior
   ========================================================================= *)

(** The run can NEVER reach the error transition.  This is the
    EXISTENTIAL error proposition negated — [~ bh_errors], not
    [~ bh_all_errors]: one erroring nondeterministic resolution already
    refutes it, exactly the reading target safety in [equiv] uses.

    Error-freedom is strictly stronger than [modeled] on the behaviors
    this development builds: [bh_unmodeled] is a sub-case of [bh_errors]
    (everything the model declines to interpret takes the error
    transition — see [Run.reaches_unmodeled_reaches_error] and
    [run_unmodeled_errors] below), so a behavior with no reachable error
    a fortiori never runs off the edge of the model.  A clause demanding
    [error_free] of the source therefore needs no separate [modeled]
    conjunct — but it also forbids honest CRASHES, which [modeled]
    deliberately allows.  That asymmetry is the whole reason the
    error-free shape below is a separate theorem statement rather than a
    strengthening of [strong_equiv]. *)
Definition error_free (b : behavior) : Prop := ~ bh_errors b.

(* =========================================================================
   Death by a signal, and the error-free shape that has to see it
   ========================================================================= *)

(** The run can end by being KILLED, rather than by exiting: some
    admissible trace carries a [State.KillEv].  Under the declaration
    [Run.valid_input] pins there are none, because the only arm that can
    produce one declines
    ([Kernel.Signal.tkill_spec_off_unmodeled]); under
    [Run.valid_input_abort] a program that calls [abort] has one.

    IT IS READ OFF [bh_traces] rather than carried as a new field of
    [Run.behavior], and that is the point of the event being an event: a
    death by SIGABRT is an OBSERVATION, on the same footing as the exit
    it replaces, so everything that already compares runs by their trace
    sets compares this too without being told about it. *)
Definition dies_by_signal (b : behavior) : Prop :=
  exists tr sig fs, bh_traces b tr /\ List.In (KillEv sig fs) tr.

(** WHAT [equiv] THEREFORE SAYS ABOUT AN ABORT, which is worth stating
    because [equiv] has no clause of its own for it.

    [equiv] compares finite-prefix SETS.  A [State.KillEv] is in those
    sets, so under the abort declaration two binaries are equivalent only
    if they abort on the SAME inputs, with the same output before the
    abort — and a target that aborts where the source exits, or exits
    where the source aborts, is refuted by trace equality rather than by
    a clause about signals.  A target that dies of the same signal after
    the same output is accepted, which is the whole reason a task would
    turn the declaration on.

    It is NOT an error.  [bh_errors] is where the model says the run left
    what it can describe or the process took a fault it did not model;
    an abort the model has followed step by step is neither.  So under
    the declaration an aborting binary satisfies [modeled], where without
    it the arm declines and the run does not — a change that must not be
    made by default, which is why the declaration exists.

    THE ERROR-FREE SHAPE MUST NOT INHERIT THAT, and this is the one place
    the two readings would otherwise diverge in the dangerous direction.
    [error_free] is [~ bh_errors], so with the declaration on it would be
    SATISFIED by a program that aborts on every input: the abort is a
    clean modeled ending and no error transition is ever taken.  Every
    error-free statement in the tree would silently weaken the moment a
    task flipped the declaration.  [error_free_unkilled] is [error_free]
    plus the missing conjunct, and the abort-declared statement family
    below is stated with it. *)
Definition error_free_unkilled (b : behavior) : Prop :=
  error_free b /\ ~ dies_by_signal b.

Lemma error_free_unkilled_error_free : forall b,
  error_free_unkilled b -> error_free b.
Proof. intros b (H & _). exact H. Qed.

(** ... and it is STRICTLY stronger, which is what makes the abort-declared
    error-free statement safe to offer beside the plain one: turning the
    declaration on cannot turn an unprovable error-free obligation into a
    provable one by making the abort stop counting.

    THE WITNESS HERE IS A HAND-WRITTEN [behavior], NOT A [Run.run], and
    that is worth saying because it is the weaker of the two bites this
    predicate has.  What it shows is that the two PREDICATES differ on
    something of the right type; what it does not show is that any IMAGE
    separates them, and a [behavior] is a record of bare [Prop]s, so
    nothing stops one being written that no [Run.run] returns.

    THE IMAGE-LEVEL BITE IS [Checks.AbortWitness], and it is the one to
    read.  [Checks.AbortWitness.abrt_dies_by_signal] exhibits a concrete
    six-instruction image whose run really reaches [State.KillEv] — a
    [set_tid_address] to pin the tid, then [tkill] to it with SIGABRT —
    and so discharges the [dies_by_signal (run ...)] hypothesis that
    [strong_universal_error_free_T_abort_refuted_by_abort] below takes.
    [Checks.AbortWitness.abrt_refutes_error_free_abort] is that
    refutation fired rather than merely stated, and it is fired at an
    image against ITSELF: the two sides are identical, so the only thing
    that fails is the conjunct this definition adds.  That is the
    strongest form the claim has — [error_free] alone would ACCEPT that
    run, since a followed abort takes no error transition. *)
Lemma error_free_unkilled_bites :
  exists b, error_free b /\ ~ error_free_unkilled b.
Proof.
  exists {| bh_traces := fun tr => tr = [] \/ tr = [KillEv (Z_to_bv 64 6) (@nil (Fs.path * list byte))];
            bh_errors := False;
            bh_all_errors := False;
            bh_unmodeled := False |}.
  split.
  - intros H. exact H.
  - intros (_ & Hno). apply Hno.
    exists [KillEv (Z_to_bv 64 6) (@nil (Fs.path * list byte))], (Z_to_bv 64 6), (@nil (Fs.path * list byte)).
    split; [now right | now left].
Qed.

(** The behavior-level image of [Run.reaches_unmodeled_reaches_error]:
    for the behaviors this development actually builds — the ones
    [Run.run] returns — being uncovered by the model is a special case
    of erroring.  ([Run.behavior] is a record of bare [Prop]s, so this
    containment cannot be stated for an arbitrary behavior; it is a fact
    about [Run.run]'s construction.)  This is the bridge that lets
    [error_free] of a run subsume [modeled] of that run, which
    [strong_universal_error_free_implies] below consumes. *)
Lemma run_unmodeled_errors : forall img lim en inp,
  bh_unmodeled (run img lim en inp) -> bh_errors (run img lim en inp).
Proof.
  intros [segs pc ph] lim [sp brk0 mbase rnd] inp Hun.
  cbn [run bh_unmodeled bh_errors] in *.
  eapply reaches_unmodeled_reaches_error; exact Hun.
Qed.

(** The behavior-level image of [Run.all_traces_error_reaches_error],
    the other containment [Run.run] realises: a run whose every
    execution errors can, in particular, error.  This is what makes the
    vacuity escape of [equiv] and [error_free] mutually exclusive rather
    than merely different — see
    [strong_equiv_error_free_no_all_errors_escape]. *)
Lemma run_all_errors_errors : forall img lim en inp,
  bh_all_errors (run img lim en inp) -> bh_errors (run img lim en inp).
Proof.
  intros [segs pc ph] lim [sp brk0 mbase rnd] inp Hall.
  cbn [run bh_all_errors bh_errors] in *.
  eapply all_traces_error_reaches_error; exact Hall.
Qed.

(** Error-freedom of a run implies model coverage of that run: the
    containment above, contraposed.  This is the lemma that justifies
    leaving [modeled] out of [strong_equiv_error_free] — the
    anti-vacuity role that conjunct plays in [strong_equiv] is
    inherited, strengthened, rather than dropped. *)
Lemma run_error_free_modeled : forall img lim en inp,
  error_free (run img lim en inp) -> modeled (run img lim en inp).
Proof.
  intros img lim en inp Hef Hun.
  apply Hef, run_unmodeled_errors, Hun.
Qed.

(* =========================================================================
   Non-vacuity of [error_free] itself
   ========================================================================= *)

(** Two synthetic behaviors, used only to pin what the DEFINITIONS say.
    [Run.behavior] is a record of bare [Prop]s with no coherence
    condition between the fields, so a record built here need not be one
    any binary produces — which is the point: these witness facts about
    [error_free] and [modeled] as predicates, independently of
    [Run.run].  Run-level witnesses are a different (and harder)
    obligation; the one for the baseline shape is
    [Checks.Examples.run_of_undecodable_image_refutes_modeled], and the
    one for the error-free shape is
    [Checks.Examples.undecodable_image_refutes_error_free_equivalence]. *)
Definition quiet_behavior : behavior :=
  {| bh_traces := fun tr => tr = [];
     bh_errors := False;
     bh_all_errors := False;
     bh_unmodeled := False |}.

(** A behavior that crashes but stays inside the model: it can error,
    and nothing about it is unmodeled.  This is exactly the situation
    the baseline shape tolerates and the error-free shape forbids. *)
Definition crashing_behavior : behavior :=
  {| bh_traces := fun tr => tr = [];
     bh_errors := True;
     bh_all_errors := True;
     bh_unmodeled := False |}.

(** [error_free] bites: it is neither empty nor universal. *)
Lemma error_free_bites : error_free quiet_behavior /\ ~ error_free crashing_behavior.
Proof.
  split.
  - intros [].
  - intros Hef. apply Hef. exact I.
Qed.

(** ... and it is STRICTLY stronger than [modeled]: the implication
    proved by [run_error_free_modeled] does not reverse, because a crash
    is modeled.  [crashing_behavior] is the witness.  So the two clauses
    are not interchangeable, and replacing [modeled] by [error_free] in
    a theorem statement is a real strengthening rather than a
    restatement. *)
Lemma modeled_not_error_free_bites : ~ (forall b, modeled b -> error_free b).
Proof.
  intros H.
  assert (Hmodeled : modeled crashing_behavior) by (intros []).
  exact (H crashing_behavior Hmodeled I).
Qed.

(** The "basic" argv used by the basic tiers: a single empty-string
    argument (argc=1, argv[0]=""). *)
Definition basic_argv : list (list byte) := [[]].

(* =========================================================================
   Image well-formedness: a fetchable entry point
   ========================================================================= *)

(** The image's entry point is fetchable: the FIRST instruction fetch at
    [init_pc] succeeds.  Written as [RiscvSemantics.step] gates it — the
    [fetch_word] fast path, then the w+x overlay fetch (here in its
    static projection [fetch_word_wx]: the initial overlay is the stack
    image, which lives in the [Run.valid_sp] window far above every
    loaded segment, so the image bytes are what the first fetch reads),
    falling back to the length-correct combined [fetch_tail_any] over
    the empty overlay — at the same [pc] word [Run.init_machine_state]
    installs ([Z_to_bv 64 (Z.of_N init_pc)]).

    This is the anti-vacuity condition on the images: an image with NO
    loaded segment — or one whose [init_pc] falls outside every segment,
    in a non-executable one, or on an odd address — faults on its first
    instruction, so [Run.all_traces_error] holds of the initial
    configuration and [equiv]'s [bh_all_errors] escape admits ANY
    target, [strong_universal] becoming provable by [left] with nothing
    said about either binary.  (A w+x text segment does not open this
    hole: fetch reads such a segment through the writable overlay —
    [RiscvSemantics.code_read_ov] — so an RWX-linked image simply
    executes.)

    Asserted for BOTH images in each example's [Checker.v].  It is the
    SOURCE side that closes the hole — the source's universal error is
    what frees the target — but an image whose entry does not fetch is
    not a program either way, and the symmetric check costs one
    [vm_compute].  It is a condition on the IMAGE alone: it says nothing
    about the rest of the run. *)
Definition image_entry_fetchable (segs : list Segment) (pc : N) : bool :=
  let addr := Z_to_bv 64 (Z.of_N pc) in
  match fetch_word segs addr with
  | Some _ => true
  | None =>
    match fetch_word_wx segs addr with
    | Some _ => true
    | None =>
      match fetch_tail_any segs (fun _ => None) addr with
      | Some _ => true
      | None => false
      end
    end
  end.

(** The check bites: nothing is fetchable in an image with no segments,
    at any entry point — the Checkers assert
    [image_entry_fetchable = true], so a predicate that held of
    everything would be worthless. *)
Lemma image_entry_fetchable_nil : forall pc,
  image_entry_fetchable [] pc = false.
Proof.
  intros pc. unfold image_entry_fetchable, fetch_word, fetch_word_wx,
    fetch_tail_any, fetch_half_any, fetch_half, fetch_half_ov,
    code_read, code_read_wx, code_read_ov.
  cbn [find_segment]. destruct (negb _); reflexivity.
Qed.

(* =========================================================================
   Image well-formedness: the published program header table is readable
   ========================================================================= *)

(** The program header table the auxv advertises is really THERE: the whole
    range [ph_addr, ph_addr + ph_num * ph_ent) that
    [StackLayout.auxv_entries] publishes as AT_PHDR/AT_PHENT/AT_PHNUM lies
    inside one readable loaded segment, so [RiscvSemantics.memory_read]
    succeeds on it — which is exactly the read a libc's phdr walk performs.

    [MemImageType.PhdrInfo] is the one image datum with no other tie to
    [loaded_segments]: [Run.init_machine_state] splices [ph_addr] into the
    initial stack unconditionally, and [SPEC] accepts whatever the image
    module declares.  [elf-snapshot] checks the containment
    when it emits a [PhdrInfo], but that is Python, outside the trust
    boundary.
    So a stale or hand-edited [phdrs] — e.g. one left behind after a relink
    that changed [e_phnum] — would not break any proof: the current examples
    are [-nostartfiles] and never read their auxv.  A future TLS-using
    source WOULD read it, and a wrong [ph_addr] makes its libc dereference
    unmapped memory at startup, so every source execution errors,
    [bh_all_errors] holds, and [equiv]'s escape frees the target — the same
    vacuity shape as an entry that does not fetch.  Asserted per example in
    [Checker.v], inside the trust boundary, alongside
    [image_entry_fetchable].

    A zero [ph_num] or [ph_ent] is rejected rather than accepted
    vacuously: [memory_read] of a zero-length range says nothing, and
    AT_PHNUM = 0 is precisely the "libc finds no PT_TLS" state this
    datum exists to rule out.  Every ELF the loader accepts has at least
    one program header (it needs one covering [e_phoff] to publish
    AT_PHDR at all) and [e_phentsize] = 56. *)
Definition image_phdrs_readable (segs : list Segment) (ph : PhdrInfo) : bool :=
  (0 <? ph_num ph)%N && (0 <? ph_ent ph)%N &&
  match memory_read segs (Z_to_bv 64 (Z.of_N (ph_addr ph)))
                    (ph_num ph * ph_ent ph)%N with
  | Some _ => true
  | None => false
  end.

(** The check bites, on both of its halves: nothing is readable in an image
    with no loaded segment, and an image claiming no program headers is
    rejected however its segments look.  Same role as
    [image_entry_fetchable_nil] — the Checkers
    assert [image_phdrs_readable = true], so a predicate that held of
    everything would be worthless. *)
Lemma image_phdrs_readable_nil : forall ph,
  image_phdrs_readable [] ph = false.
Proof.
  intros ph. unfold image_phdrs_readable, memory_read.
  cbn [find_segment]. now rewrite Bool.andb_false_r.
Qed.

Lemma image_phdrs_readable_zero_num : forall segs ph,
  ph_num ph = 0%N -> image_phdrs_readable segs ph = false.
Proof.
  intros segs ph Hnum. unfold image_phdrs_readable. rewrite Hnum.
  reflexivity.
Qed.

(* =========================================================================
   Image well-formedness: the brk ASLR window is inhabited
   ========================================================================= *)

(** [strong_universal_T] quantifies its entries under [Run.valid_entry],
    so it is vacuously true of a pair of images for which NO valid entry
    exists — every clause sits under an unsatisfiable premise.
    [Run.valid_sp] and [Run.valid_mmap_base] are over absolute windows
    and always inhabited, and [Run.entry_stack_fits] is satisfied at the
    bottom of the sp window by every valid input
    ([Run.entry_stack_span_bound]), so the one image-dependent premise is
    [Run.valid_brk]: it asks for a 64-bit break word at or above
    [State.reserved_top] of the image's page-rounded LOAD reservations —
    and [reserved_top] is computed in [Z], so an image whose reservations
    reach 2^64 (a LOAD segment ending exactly at the top of the address
    space suffices; no [N] overflow needed) empties the window: no
    [bv 64] unsigned value reaches it, [valid_entry] is unsatisfiable,
    and [strong_universal] is provable with the images never looked at.
    Same shape as the other two checks — a theorem that holds having said
    nothing — reached through the QUANTIFIER rather than through the
    error escape.

    The checked witness is the page-rounded-up [reserved_top] — the
    bottom of the window [Run.valid_brk] admits.  If it fits in 64 bits the
    window is inhabited ([image_brk_satisfiable_sound] below turns the
    boolean into the [exists]); it sits at most a page above
    [reserved_top], within [brk_aslr_max] of it. *)
Definition image_brk_witness (segs : list Segment) : Z :=
  page_size *
  ((reserved_top (segments_reserved segs) + (page_size - 1)) / page_size).

Definition image_brk_satisfiable (segs : list Segment) : bool :=
  (image_brk_witness segs <? 2 ^ 64)%Z.

Lemma reserved_top_nonneg : forall maps,
  (0 <= reserved_top maps)%Z.
Proof.
  induction maps as [| [a sz] r IH]; cbn [reserved_top]; [lia |].
  pose proof (bv_unsigned_in_range 64 a).
  pose proof (bv_unsigned_in_range 64 sz).
  lia.
Qed.

(** The witness really sits in the window: at or above [reserved_top],
    less than a page above it, and page-aligned. *)
Lemma image_brk_witness_bounds : forall segs,
  (reserved_top (segments_reserved segs)
     <= image_brk_witness segs
     < reserved_top (segments_reserved segs) + page_size)%Z
  /\ (image_brk_witness segs mod page_size = 0)%Z.
Proof.
  intros segs. unfold image_brk_witness, page_size.
  set (rt := reserved_top (segments_reserved segs)).
  split; [| rewrite Z.mul_comm; apply Z.mod_mul; lia].
  pose proof (Z.div_mod (rt + (4096 - 1)) 4096 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (rt + (4096 - 1)) 4096 ltac:(lia)) as Hmb.
  lia.
Qed.

(** What the Checkers actually buy with the boolean: a [true] verdict
    yields a valid break.  That is the image-only half; a valid
    [ExecEntry] needs the input too, since [Run.valid_entry] also asks
    that the entry stack image fit below the top of the address space.
    [image_brk_satisfiable_entry] below is the statement that closes
    over both, and it is the one that says [strong_universal_T]'s
    premises are satisfiable. *)
Lemma image_brk_satisfiable_sound : forall segs,
  image_brk_satisfiable segs = true ->
  exists brk, valid_brk segs brk.
Proof.
  intros segs H. apply Z.ltb_lt in H.
  destruct (image_brk_witness_bounds segs) as [Hwin Hmod].
  pose proof (reserved_top_nonneg (segments_reserved segs)).
  exists (Z_to_bv 64 (image_brk_witness segs)).
  unfold valid_brk.
  rewrite Z_to_bv_unsigned, bv_wrap_small
    by (unfold bv_modulus; cbn; lia).
  unfold brk_aslr_max, page_size in *. lia.
Qed.

(** The entry is satisfiable FOR A GIVEN VALID INPUT, since
    [Run.valid_entry]'s stack-image conjunct reads argv and envp: the
    witness stack pointer is the bottom of the sp window, which leaves
    two gigabytes of room below [sp_window_hi] for a block the
    [valid_argv]/[valid_envp] limits cap at [entry_stack_span_max]
    (2238671 bytes).  So adding that conjunct did not open a second way
    to empty the entry quantifier, which is the exact failure this
    boolean exists to rule out. *)
Lemma image_brk_satisfiable_entry : forall img inp,
  valid_input inp ->
  image_brk_satisfiable (img_segments img) = true ->
  exists en, valid_entry img en inp.
Proof.
  intros [segs pc ph] inp Hv H.
  pose proof (valid_input_va_size _ Hv) as Hsize.
  destruct Hv as (Hargv & Henvp & _ & _).
  destruct (image_brk_satisfiable_sound segs H) as [brk Hbrk].
  pose proof (entry_stack_span_bound _ _ Hargv Henvp) as Hspan.
  exists (mkEntry (Z_to_bv 64 sp_window_lo) brk
            (Z_to_bv 64 mmap_base_max)
            (mkDraw (Z_to_bv 128 0) (fun _ => Z_to_bv 8 0))).
  rewrite (valid_entry_sv48 _ _ _ Hsize).
  cbn. split; [| split; [exact Hbrk | split]].
  - unfold valid_sp, sp_window_lo, sp_window_hi.
    rewrite Z_to_bv_unsigned, bv_wrap_small
      by (unfold bv_modulus; cbn; lia).
    lia.
  - unfold valid_mmap_base, mmap_base_min, mmap_base_max, sp_window_hi,
      page_size.
    rewrite Z_to_bv_unsigned, bv_wrap_small
      by (unfold bv_modulus; cbn; lia).
    lia.
  - unfold entry_stack_fits.
    rewrite Z_to_bv_unsigned, bv_wrap_small
      by (unfold bv_modulus, sp_window_lo; cbn; lia).
    unfold entry_stack_span_max in Hspan.
    unfold sp_window_lo, sp_window_hi. lia.
Qed.

(** The check bites: an image whose reservations reach the top of the
    address space fails it.  Same role as [image_entry_fetchable_nil]
    and [image_phdrs_readable_nil] — the Checkers assert
    [image_brk_satisfiable = true], so a predicate that held of
    everything would be worthless.  (Reachable with honest snapshot
    data: a LOAD segment with [seg_base + seg_size] page-rounding up to
    2^64 — no arithmetic wraps anywhere on the way to [reserved_top].) *)
Lemma image_brk_satisfiable_bites : forall segs,
  (2 ^ 64 <= reserved_top (segments_reserved segs))%Z ->
  image_brk_satisfiable segs = false.
Proof.
  intros segs Htop.
  destruct (image_brk_witness_bounds segs) as [Hwin _].
  apply Z.ltb_ge. lia.
Qed.

(* =========================================================================
   Theorem statements (parameterised over the two memory images)
   ========================================================================= *)

Section Spec.

Variable source_image : Image.
Variable target_image : Image.

(** Equivalence for a single (source entry, target entry, process
    input) triple: the two binaries' behaviors — finite trace-prefix
    sets plus error reachability — must match per [equiv], AND the model
    must cover the source on that input per [modeled].  The second
    conjunct is what keeps the first from being satisfiable by an
    insufficient semantics; it is stated per input, like [equiv] itself,
    so a source that leaves the modeled surface on ONE input fails the
    theorem even if it is well covered on every other.

    The two [Run.ExecEntry] records — each carrying the initial stack
    pointer, the initial program break, the mmap base and the 16
    AT_RANDOM bytes — are
    QUANTIFIED INDEPENDENTLY: execve picks all four
    non-deterministically (ASLR, [Run.valid_sp]/[Run.valid_brk]/
    [Run.valid_mmap_base]; the AT_RANDOM draw has no predicate at all,
    since every 128-bit value is one the kernel can make), so
    the target must match the source even when the two processes were
    launched at different (valid) SPs and break bases, and with different
    startup entropy — a program whose
    observable behavior leaks its stack address, its heap base or its
    AT_RANDOM bytes cannot be
    proved equivalent to anything, which is intended.  The
    [State.ProcInput] record — argv, envp, initial file system,
    launching user and group, standard input, the network the
    environment offers, and the soft descriptor limit — is SHARED, so
    the two binaries are compared on the same input.  The difference matters for
    the credentials in particular: because the uid is shared and not
    quantified per binary, a program that BRANCHES on [getuid] can be
    proved equivalent to a target that branches on it the same way,
    which is exactly what modeling the credential syscalls buys.  What
    it does not buy is freedom: the target must depend on the uid the
    same way the source does, on every uid.

    Each run is seeded with its role's ALLOCATION BUDGET
    ([State.source_alloc_limit] / [State.target_alloc_limit] into
    [Run.run]'s [lim] argument): a fixed capacity in bytes on the live
    allocator grants, which forces an out-of-memory point on a source
    with unbounded allocation — so the target can (and, by trace
    equality, must) reproduce the source's OOM behavior exactly.
    Forced is not deterministic: overlapping [State.vm_maps]
    entries make the byte total depend on placement, so the source may
    reach the point at more than one byte count and trace equality
    obliges the target to match each (the argument is on
    [State.source_alloc_limit]).  The target's budget is the larger of the
    two: headroom to trade memory for simplicity, never an excuse to
    keep succeeding where the source's budget forces failure. *)
Definition strong_equiv (en_source en_target : ExecEntry)
    (inp : ProcInput) : Prop :=
  modeled (run source_image source_alloc_limit en_source inp)
  /\
  equiv (run source_image source_alloc_limit en_source inp)
        (run target_image target_alloc_limit en_target inp).

(** The sole proof obligation: equivalence for every valid pair of entry
    records (each break base validated against ITS binary's image — the
    window is image-relative) and every valid process input.  The input
    record is quantified ONCE and shared: source and target must agree
    on every input, each compared against the other on the same one.
    This composes with the error semantics without special-casing,
    because [equiv] — including [bh_errors] and [bh_all_errors] — is
    applied per-input: "every source execution errors" is read at a
    FIXED input, which is the strictly more honest reading (a source
    that errors on some inputs and behaves observably on others does
    not get the vacuity escape by pointing at the erroring
    input). *)
Definition strong_universal_T : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input inp ->
    strong_equiv en_source en_target inp.

(** Error-free equivalence for a single (source entry, target entry,
    process input) triple: BOTH runs are [error_free], and the two
    finite trace-prefix sets are equal.

    Two clauses of [strong_equiv] are deliberately ABSENT:

    - NO [bh_all_errors] escape.  In [equiv] a source whose every
      execution errors frees the target, because the equivalence task is
      then vacuous.  Here that is precisely the outcome being forbidden:
      a source that errors on even ONE path of ONE valid input fails
      this theorem outright
      ([strong_equiv_error_free_no_all_errors_escape] states the extreme
      case).  The consequence is a real restriction on applicability — a
      task whose reference binary crashes cannot use this variant and
      keeps [strong_universal_T] with its escape.
    - NO separate [modeled] conjunct.  Error-freedom subsumes it:
      everything unmodeled errors ([run_unmodeled_errors]), so a source
      run with no reachable error never reaches a configuration the
      model declines either ([run_error_free_modeled]).  The
      anti-vacuity role that conjunct plays in [strong_equiv] is
      inherited and strengthened — not only does the model cover the
      source, the source never even faults.

    Trace-set EQUALITY still matters with both sides error-free, for the
    same reason as in [equiv]: errors are not the only way to say
    nothing.  A silently DIVERGING target — no error transition, no
    further events, forever — is error-free, and refinement (target
    prefixes contained in source prefixes) would accept it vacuously.
    Equality forces the target to be exactly as productive as the
    source: every source prefix, including those ending in [ExitEv],
    must also be a target prefix, and conversely.

    Entries and budgets are treated exactly as in [strong_equiv]: the
    two [Run.ExecEntry] records are quantified independently, the
    [State.ProcInput] is shared, and each run is seeded with its role's
    allocation budget. *)
Definition strong_equiv_error_free (en_source en_target : ExecEntry)
    (inp : ProcInput) : Prop :=
  error_free (run source_image source_alloc_limit en_source inp)
  /\ error_free (run target_image target_alloc_limit en_target inp)
  /\ trace_equiv
       (bh_traces (run source_image source_alloc_limit en_source inp))
       (bh_traces (run target_image target_alloc_limit en_target inp)).

(** The error-free universal statement: [strong_equiv_error_free] for
    every valid pair of entry records and every valid process input —
    the same quantifier shell as [strong_universal_T]
    ([Run.valid_entry] per image, [Run.valid_input] on the shared
    input), so the two statements differ only in the per-triple
    obligation.  On any input family it asserts that ALL executions of
    BOTH binaries are modeled and error-free, and that the binaries are
    observably equivalent.

    Inheriting the shell also inherits its VACUITY ROUTE, and the
    strengthening does not close it.  Error-freedom closes the routes
    that run through the error escape: an image whose entry point cannot
    be fetched, or whose program-header table cannot be read, reaches the
    error transition and so now REFUTES this statement, where under
    [equiv] it would have satisfied the obligation vacuously.  It says
    nothing about a premise that is simply unsatisfiable — an image for
    which no [Run.valid_entry] exists at all still satisfies this
    statement with nothing said about either binary, because
    strengthening what sits UNDER a quantifier cannot repair an empty
    range.  A consuming checker must therefore still ascribe [IMAGE_WF]
    for BOTH images alongside this obligation, exactly as it does for
    the baseline; [image_brk_satisfiable] is the check in that group
    that inhabits the entry space. *)
Definition strong_universal_error_free_T : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input inp ->
    strong_equiv_error_free en_source en_target inp.

(** Per triple, the error-free obligation discharges the baseline one.
    Source error-freedom gives [modeled] via [run_error_free_modeled],
    and [equiv] holds by its RIGHT disjunct — trace equality plus target
    error-freedom — so the escape is never taken. *)
Lemma strong_equiv_error_free_implies : forall en_source en_target inp,
  strong_equiv_error_free en_source en_target inp ->
  strong_equiv en_source en_target inp.
Proof.
  intros en_source en_target inp Hef.
  destruct Hef as (Hsef & Htef & Htr).
  split.
  - apply run_error_free_modeled, Hsef.
  - right. split; [exact Htr | exact Htef].
Qed.

(** The error-free statement is genuinely STRONGER: a proof of it
    mechanically discharges [strong_universal_T] on the same two images.
    This is what makes the variant safe to offer as an alternative
    obligation — anything proved against [SPEC_ERROR_FREE] below implies
    the [SPEC] statement, so the stronger check never accepts a pair of
    binaries the baseline check would reject. *)
Lemma strong_universal_error_free_implies :
  strong_universal_error_free_T -> strong_universal_T.
Proof.
  intros H en_source en_target inp Hsrc Htgt Hinp.
  apply strong_equiv_error_free_implies, H; assumption.
Qed.

(** Where the two shapes diverge, stated as a refutation.  A source
    whose every execution errors satisfies [equiv] against ANY target —
    that is [all_source_traces_error_equiv_any] — and here the same
    hypothesis REFUTES the per-triple obligation outright, via
    [run_all_errors_errors].  So the escape is not merely unused in this
    shape; it is inconsistent with it, and a task cannot slip a vacuous
    instance past the stronger obligation the way the baseline permits.

    This is the definition-level bite.  The run-level witness — a
    concrete image on which the error-free statement fails — is
    example-side:
    [Checks.Examples.undecodable_image_refutes_error_free_equivalence]
    runs the undecodable image against itself at a valid entry and a
    valid input, where the fetch leaves the modeled surface. *)
Lemma strong_equiv_error_free_no_all_errors_escape :
  forall en_source en_target inp,
    bh_all_errors (run source_image source_alloc_limit en_source inp) ->
    ~ strong_equiv_error_free en_source en_target inp.
Proof.
  intros en_source en_target inp Hall Hef.
  destruct Hef as (Hsef & _ & _).
  apply Hsef, run_all_errors_errors, Hall.
Qed.

(** The same bite at the TOP level: one valid triple on which the source
    can error refutes the whole universal statement.  A single erroring
    nondeterministic resolution, on a single valid entry pair and a
    single valid input, is enough — which is what makes this obligation
    unavailable to a task whose reference binary crashes, and what stops
    it from being a predicate nothing could fail.

    Only the refutation direction is proved here.  The positive
    direction — a concrete image pair on which the statement HOLDS — is
    deliberately example-side: it cannot be had reflexively, because the
    two roles run at different budgets
    ([State.source_alloc_limit] versus [State.target_alloc_limit]), so
    even an image compared against itself is a real proof obligation. *)
Lemma strong_universal_error_free_refuted_by_source_error :
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input inp ->
    bh_errors (run source_image source_alloc_limit en_source inp) ->
    ~ strong_universal_error_free_T.
Proof.
  intros en_source en_target inp Hsrc Htgt Hinp Herr H.
  destruct (H en_source en_target inp Hsrc Htgt Hinp) as (Hsef & _ & _).
  exact (Hsef Herr).
Qed.

(* =========================================================================
   The abort-declared statements: the same obligations, quantified over
   the inputs that declare the abort path
   ========================================================================= *)

(** THE QUANTIFIER IS THE WHOLE DIFFERENCE for the baseline shape.
    [strong_equiv] per triple is unchanged — [modeled] and [equiv] read
    the same two runs — and what changes is which inputs the triple
    ranges over: [Run.valid_input_abort] pins
    [State.in_abort_terminal] to [true], so every run this statement
    speaks about is one in which [tkill] to the caller's own tid with
    SIGABRT ends the process instead of leaving the modeled surface.

    WHAT A PROOF OF THIS BUYS, AND WHAT IT COSTS.  It buys [modeled] for
    a source that can abort, which [strong_universal_T] cannot have: with
    the declaration off that source reaches [Run.reaches_unmodeled] and
    the conjunct is false.  It costs the abort becoming an OBSERVATION
    the target has to reproduce — [equiv] is trace-set equality and the
    [State.KillEv] is in the set — so the target must abort on exactly
    the inputs the source aborts on.  Neither statement implies the
    other, and that is why both exist. *)
Definition strong_universal_T_abort : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort inp ->
    strong_equiv en_source en_target inp.

(** Neither stance pinned: the obligation over every input the shared
    clauses accept.  It is exactly the conjunction of the two
    stances ([strong_universal_T_either_splits]), so a task that says
    nothing about the abort path is held to both readings rather than to
    whichever one happens to be the default. *)
Definition strong_universal_T_either : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_either inp ->
    strong_equiv en_source en_target inp.

Lemma strong_universal_T_either_splits :
  strong_universal_T_either
  <-> (strong_universal_T /\ strong_universal_T_abort).
Proof.
  split.
  - intros H. split; intros en_s en_t inp Hs Ht Hv; apply H;
      try assumption;
      [ exact (valid_input_either_of_valid_input _ Hv)
      | exact (valid_input_either_of_valid_input_abort _ Hv) ].
  - intros (Hoff & Hon) en_s en_t inp Hs Ht Hv.
    destruct (valid_input_either_splits _ Hv) as [Hv' | Hv'];
      [ exact (Hoff _ _ _ Hs Ht Hv') | exact (Hon _ _ _ Hs Ht Hv') ].
Qed.

(** The projections, named rather than left to the caller.  The
    error-free either shapes have them because they are conjunctions and
    the projection IS the proof; the T shapes are quantifier shells, so
    theirs go through the split -- but a task author meets both families
    and should not have to notice which is which. *)
Lemma strong_universal_T_either_implies :
  strong_universal_T_either -> strong_universal_T.
Proof. intros H. exact (proj1 (proj1 strong_universal_T_either_splits H)). Qed.

Lemma strong_universal_T_either_implies_abort :
  strong_universal_T_either -> strong_universal_T_abort.
Proof. intros H. exact (proj2 (proj1 strong_universal_T_either_splits H)). Qed.

(** The error-free triple under the abort declaration.  IT IS NOT
    [strong_equiv_error_free] WITH A DIFFERENT QUANTIFIER: both runs are
    asked for [error_free_unkilled] rather than [error_free], because
    with the declaration on an abort is not an error and the plain
    predicate would stop seeing it.  A binary that aborts fails this
    obligation, exactly as it fails [strong_universal_error_free_T] with
    the declaration off — there because the abort is unmodeled, here
    because it is a death.  Same verdict, honest reason. *)
Definition strong_equiv_error_free_abort (en_source en_target : ExecEntry)
    (inp : ProcInput) : Prop :=
  error_free_unkilled (run source_image source_alloc_limit en_source inp)
  /\ error_free_unkilled (run target_image target_alloc_limit en_target inp)
  /\ trace_equiv
       (bh_traces (run source_image source_alloc_limit en_source inp))
       (bh_traces (run target_image target_alloc_limit en_target inp)).

Definition strong_universal_error_free_T_abort : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort inp ->
    strong_equiv_error_free_abort en_source en_target inp.

(** The error-free shape still discharges the baseline shape, under the
    declaration as without it, and for the same reason: everything
    unmodeled errors. *)
Lemma strong_equiv_error_free_abort_implies : forall en_source en_target inp,
  strong_equiv_error_free_abort en_source en_target inp ->
  strong_equiv en_source en_target inp.
Proof.
  intros en_source en_target inp (Hsef & Htef & Htr).
  split.
  - apply run_error_free_modeled, (error_free_unkilled_error_free _ Hsef).
  - right. split;
      [exact Htr | exact (error_free_unkilled_error_free _ Htef)].
Qed.

Lemma strong_universal_error_free_T_abort_implies :
  strong_universal_error_free_T_abort -> strong_universal_T_abort.
Proof.
  intros H en_s en_t inp Hs Ht Hv.
  apply strong_equiv_error_free_abort_implies, H; assumption.
Qed.

(** THE EITHER SHAPE OF THE ERROR-FREE FAMILY IS THE CONJUNCTION of the
    two stances, written as one rather than as a quantifier shell.

    "Either" means the task declined to choose and is held to both
    readings, and the conjunction IS that meaning.  A single shell over
    [Run.valid_input_either] would have to pick one per-triple
    obligation — the two stances do not share one, since the
    declaration-off statement asks for [error_free] and the
    declaration-on statement asks for [error_free_unkilled] — and
    picking the stronger would ask a task to prove more than declining
    to choose promises.  The T family needs no such decision because its
    stances DO share a per-triple obligation, which is why
    [strong_universal_T_either] is a shell and this is not; both split
    the same way. *)
Definition strong_universal_error_free_T_either : Prop :=
  strong_universal_error_free_T /\ strong_universal_error_free_T_abort.

Lemma strong_universal_error_free_T_either_splits :
  strong_universal_error_free_T_either
  <-> (strong_universal_error_free_T /\ strong_universal_error_free_T_abort).
Proof. reflexivity. Qed.

Lemma strong_universal_error_free_T_either_implies :
  strong_universal_error_free_T_either -> strong_universal_error_free_T.
Proof. intros (H & _). exact H. Qed.

Lemma strong_universal_error_free_T_either_implies_abort :
  strong_universal_error_free_T_either -> strong_universal_error_free_T_abort.
Proof. intros (_ & H). exact H. Qed.

(** And it bites on an abort: a source that can be killed on one valid
    triple refutes it.  This is the clause that keeps "the reference can
    abort" a proof obligation under the declaration, rather than only
    without it.

    THE HYPOTHESIS IS DISCHARGED, at
    [Checks.AbortWitness.abrt_dies_by_signal], so this is a refutation
    that has been fired and not only stated —
    [Checks.AbortWitness.abrt_refutes_error_free_abort] is the firing.
    A conditional refutation nothing instantiates is indistinguishable,
    from inside the development, from one whose condition is
    unsatisfiable; that is what the witness is for. *)
Lemma strong_universal_error_free_T_abort_refuted_by_abort :
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort inp ->
    dies_by_signal (run source_image source_alloc_limit en_source inp) ->
    ~ strong_universal_error_free_T_abort.
Proof.
  intros en_s en_t inp Hs Ht Hv Hdies H.
  destruct (H en_s en_t inp Hs Ht Hv) as ((_ & Hno) & _ & _).
  exact (Hno Hdies).
Qed.

End Spec.

(* =========================================================================
   SPEC — module type the per-problem proof must satisfy
   ========================================================================= *)

Module Type SPEC (Source : MemImage) (Target : MemImage).
  Parameter strong_universal :
    strong_universal_T
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC.

(* =========================================================================
   SPEC_ERROR_FREE — module type for the error-free variant
   ========================================================================= *)

(** The sealing surface for tasks stated with
    [strong_universal_error_free_T] instead of [strong_universal_T]:
    same two image modules, same instantiation shape, and a checker
    ascribes against it exactly as it ascribes against [SPEC] —
    including the [IMAGE_WF] ascription for each of the two images,
    which error-freedom does NOT make redundant: it rules out the
    vacuity that runs through the error escape, not the vacuity of an
    image with no valid entry at all (see
    [strong_universal_error_free_T]).  It is a SEPARATE module type
    rather than an extension of [SPEC] so that the baseline obligation
    is untouched — existing proofs and checkers see no change — and
    because a task must opt in to the error-free reading, which is
    unprovable for any source that can crash however faithful the target
    ([strong_universal_error_free_implies] records that whatever is
    proved in the stronger shape implies the [SPEC] statement, never the
    reverse). *)
Module Type SPEC_ERROR_FREE (Source : MemImage) (Target : MemImage).
  Parameter strong_universal_error_free :
    strong_universal_error_free_T
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_ERROR_FREE.

(* =========================================================================
   The declared address-space size: one statement per size, and the one
   that pins none
   ========================================================================= *)

(** [strong_universal_T] quantifies over [Run.valid_input], which pins
    the task's address-space declaration ([State.in_va_size]) to
    [Sv48]; that is the kernel every statement in this tree was written
    against, and the pin is what keeps them saying what they said.  The
    statements below are the same obligation under the other two
    declarations and under none.  THE QUANTIFIER AND ONE CONJUNCT ARE
    THE WHOLE DIFFERENCE: [valid_entry] reads the size off the input,
    so an Sv39 statement ranges over entries placed inside the Sv39
    kernel's window, and [strong_equiv_va] is [strong_equiv] behind the
    one fact the arms establish, that the declared size is the one they
    implement.

    WHY THE CONJUNCT, AND WHAT IT REFUSES.  The spec arms compare
    against the Sv48 [State.TASK_SIZE] at every [access_ok] and every
    range test; [Run.run] is therefore the Sv48 run whatever the input
    declares, and a statement that consulted it under an Sv39 input
    would be judged against a limit that kernel does not have.  So the
    sealed families do not consult it: [strong_equiv_va] requires the
    declaration to be [Sv48] first, which makes
    [strong_universal_T_sv39] and [strong_universal_T_sv57] FALSE for
    every pair of images whose entry predicates are inhabited --
    [image_brk_satisfiable_entry_va] gives that for every image the
    Sv48 check accepts, and the two [_refuted] lemmas below are the
    theorems.  A checker sealed against [SPEC_SV39] or [SPEC_SV57] cannot
    be proved until the arms read the declared size, and the surfaces
    exist so that a task on such a kernel is refused by name rather than
    judged against the Sv48 window.  What this does NOT do is gate
    [Run.run]: an obligation written over it directly, outside these
    families, is a statement about the Sv48 run whatever its input
    declares. *)

(** The entry predicates are inhabited under every declaration, by the
    same witness [image_brk_satisfiable_entry] uses moved to the declared
    size's window.  Stated over [valid_input_va_any] and the size read off
    the input, so that one lemma serves the three pinned predicates. *)
Lemma image_brk_satisfiable_entry_va : forall img inp,
  valid_input_va_any inp ->
  image_brk_satisfiable (img_segments img) = true ->
  exists en, valid_entry img en inp.
Proof.
  intros [segs pc ph] inp (Hargv & Henvp & _ & _) H.
  destruct (image_brk_satisfiable_sound segs H) as [brk Hbrk].
  pose proof (entry_stack_span_bound _ _ Hargv Henvp) as Hspan.
  unfold entry_stack_span_max in Hspan.
  exists (mkEntry (Z_to_bv 64 (va_sp_window_lo (in_va_size inp))) brk
            (Z_to_bv 64 (va_mmap_base_max (in_va_size inp)))
            (mkDraw (Z_to_bv 128 0) (fun _ => Z_to_bv 8 0))).
  unfold valid_entry. cbn [valid_entry_va].
  unfold valid_sp_va, valid_mmap_base_va, entry_stack_fits_va,
    va_sp_window_lo, va_sp_window_hi, va_mmap_base_min, va_mmap_base_max,
    va_stack_top.
  destruct (in_va_size inp);
    unfold sp_window_hi, sv39_task_size, mmap_base_min, page_size;
    (split; [| split; [exact Hbrk | split]]);
    rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia);
    lia.
Qed.

Section SpecVa.

Variable source_image : Image.
Variable target_image : Image.

(** [strong_equiv] behind the declaration the arms implement.  Under
    [Run.valid_input] the first conjunct is the pinned field and the
    predicate is [strong_equiv] ([strong_equiv_va_sv48]); under any other
    declaration it is false, which is the refusal. *)
Definition strong_equiv_va (en_source en_target : ExecEntry)
    (inp : ProcInput) : Prop :=
  in_va_size inp = Sv48
  /\ strong_equiv source_image target_image en_source en_target inp.

Lemma strong_equiv_va_sv48 : forall en_source en_target inp,
  in_va_size inp = Sv48 ->
  (strong_equiv_va en_source en_target inp
   <-> strong_equiv source_image target_image en_source en_target inp).
Proof. intros en_s en_t inp Hv. unfold strong_equiv_va. tauto. Qed.

Definition strong_universal_T_sv39 : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_sv39 inp ->
    strong_equiv_va en_source en_target inp.

Definition strong_universal_T_sv57 : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_sv57 inp ->
    strong_equiv_va en_source en_target inp.

(** No size pinned: the obligation over every input the shared clauses
    accept.  It is exactly the conjunction of the three pinned
    statements ([strong_universal_T_va_any_splits]), so a task that says
    nothing about its kernel is held to all three readings. *)
Definition strong_universal_T_va_any : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_va_any inp ->
    strong_equiv_va en_source en_target inp.

Lemma strong_universal_T_va_any_splits :
  strong_universal_T_va_any
  <-> (strong_universal_T source_image target_image
       /\ strong_universal_T_sv39 /\ strong_universal_T_sv57).
Proof.
  split.
  - intros H. split; [| split]; intros en_s en_t inp Hs Ht Hv.
    + apply (strong_equiv_va_sv48 _ _ _ (valid_input_va_size _ Hv)).
      apply H; try assumption. exact (valid_input_va_any_of_valid_input _ Hv).
    + apply H; try assumption. exact (valid_input_va_any_of_valid_input_sv39 _ Hv).
    + apply H; try assumption. exact (valid_input_va_any_of_valid_input_sv57 _ Hv).
  - intros (H48 & H39 & H57) en_s en_t inp Hs Ht Hv.
    destruct (valid_input_va_any_splits _ Hv) as [Hv' | [Hv' | Hv']].
    + apply (strong_equiv_va_sv48 _ _ _ (valid_input_va_size _ Hv')).
      exact (H48 _ _ _ Hs Ht Hv').
    + exact (H39 _ _ _ Hs Ht Hv').
    + exact (H57 _ _ _ Hs Ht Hv').
Qed.

(** The bite: one Sv39 triple the predicates admit refutes the Sv39
    statement, because the declaration is not the one the arms
    implement.  [Checks.Cases.VaSize] fires it on a concrete image. *)
Lemma strong_universal_T_sv39_refuted :
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_sv39 inp ->
    ~ strong_universal_T_sv39.
Proof.
  intros en_s en_t inp Hs Ht Hv H.
  destruct (H en_s en_t inp Hs Ht Hv) as (H48 & _).
  destruct Hv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hv & _). rewrite Hv in H48. discriminate.
Qed.

Lemma strong_universal_T_sv57_refuted :
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_sv57 inp ->
    ~ strong_universal_T_sv57.
Proof.
  intros en_s en_t inp Hs Ht Hv H.
  destruct (H en_s en_t inp Hs Ht Hv) as (H48 & _).
  destruct Hv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hv & _). rewrite Hv in H48. discriminate.
Qed.

End SpecVa.

(** The sealing surfaces per declaration, beside [SPEC].  A generated
    Checker ascribes ONE of them, and which one is the task's
    declaration: a proof made under [Run.valid_input] does not type-check
    against [SPEC_SV39], and a task on an Sv39 kernel that ascribes
    [SPEC] has claimed a window its kernel does not use.  Today only
    [SPEC] can be inhabited (see the refutations above). *)
Module Type SPEC_SV39 (Source : MemImage) (Target : MemImage).
  Parameter strong_universal :
    strong_universal_T_sv39
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_SV39.

Module Type SPEC_SV57 (Source : MemImage) (Target : MemImage).
  Parameter strong_universal :
    strong_universal_T_sv57
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_SV57.

Module Type SPEC_VA_ANY (Source : MemImage) (Target : MemImage).
  Parameter strong_universal :
    strong_universal_T_va_any
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_VA_ANY.

(* =========================================================================
   The declared HARDWARE-CAPABILITY word: one statement per word, and the
   permissive default that is their conjunction
   ========================================================================= *)

(** [strong_universal_T] quantifies over [Run.valid_input], whose
    [Run.valid_hwcap] clause admits BOTH AT_HWCAP masks -- the RV64GC
    word and the same word with V added.  THE DEFAULT IS DELIBERATELY
    PERMISSIVE and stays so: the model cannot decode a vector
    instruction and answers an undecodable word with
    [Run.MachineUnmodeled] rather than a trap, so it does not claim the
    hart lacks V and must not publish a word that says so.  A statement
    issued under the default is therefore a statement about a process on
    EITHER hart.

    WHAT THE TASK DECLARES, AND WHY IT IS THE TASK'S.  Which word the
    kernel publishes is a fact about the environment the binary is
    launched in, not about the binary and not about the model: [ELF_HWCAP]
    clears the V bit whenever [riscv_v_vstate_ctrl_user_allowed()] is
    false (arch/riscv/kernel/cpufeature.c), which a process controls
    through [PR_RISCV_V_SET_CONTROL], so one machine publishes both.  The
    statements below let a task say which one it is, in the shape
    [strong_universal_T_sv39] gives the address-space declaration.

    WHAT A DECLARED-V PROOF MEANS, AND WHY THE OTHER ONE IS USUALLY THE
    ONE TO WANT.  A runtime that dispatches on the V bit takes its vector
    path under [StackLayout.hwcap_rv64gcv], and the first vector
    instruction it executes is a word [DecodeC.decode_any] returns [None]
    for -- so that run is [Run.MachineUnmodeled],
    [strong_universal_T_hwcap_rv64gcv] is FALSE for it, and so is the
    permissive default, which is their conjunction
    ([strong_universal_T_hwcap_splits]).  The same is true of a binary
    whose only vector-side code is a PROBE, a [vlenb] read behind an
    advertised V: that word DECODES, as an ordinary Zicsr access, and is
    declined one level in -- the model resolves no such CSR, so the ISA
    semantics answers [Sem.EIllegal] and the run is [MachineUnmodeled]
    too, even though the binary never vectorises anything
    ([Checks.Cases.Hwcap] pins both routes and a modeled control).  Such a task's provable statement is
    [strong_universal_T_hwcap_rv64gc], and issuing it is the task
    declaring that its kernel publishes the word without V.

    UNLIKE THE ADDRESS-SIZE FAMILY, NOTHING IS REFUSED HERE.  The
    per-size statements stand behind [strong_equiv_va], a conjunct that
    is false under every declaration but [Sv48], because the spec arms
    implement the Sv48 window and a statement under another size would be
    judged against a limit that kernel does not have.  The AT_HWCAP word
    has no such gap: the arms carry it verbatim into the auxv
    ([StackLayout.auxv_entries]) and read it nowhere else, and both words
    are words the arms handle.  So these statements are over the UNGATED
    [strong_equiv], and the declaration narrows the input family and
    nothing else.

    THE OTHER DECLARED CELL is the configured, budget-abstracted,
    abort-declared one, and it is in [SpecScfgBudgets] beside its
    undeclared statements
    ([strong_universal_T_scfg_budgets_abort_hwcap_rv64gc] and the statements
    beside it).  NOT ADDED, here or there: the declaration crossed with
    another address-space size, with the stance left open, with a
    configuration alone, or with a budget alone.  Those cells can be
    written the same way when a task needs them; the predicates behind
    the two here ([Run.valid_input_hwcap_rv64gc] and its twin) pin the
    abort stance off and the size at [Sv48]. *)

Section SpecHwcap.

Variable source_image : Image.
Variable target_image : Image.

Definition strong_universal_T_hwcap_rv64gc : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_hwcap_rv64gc inp ->
    strong_equiv source_image target_image en_source en_target inp.

Definition strong_universal_T_hwcap_rv64gcv : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_hwcap_rv64gcv inp ->
    strong_equiv source_image target_image en_source en_target inp.

(** The error-free twins: the shape of [strong_universal_error_free_T]
    over the declared input family, so a task that opts into the
    error-free reading can also declare its word. *)
Definition strong_universal_error_free_T_hwcap_rv64gc : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_hwcap_rv64gc inp ->
    strong_equiv_error_free source_image target_image en_source en_target inp.

Definition strong_universal_error_free_T_hwcap_rv64gcv : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_hwcap_rv64gcv inp ->
    strong_equiv_error_free source_image target_image en_source en_target inp.

(** The default is EXACTLY the two, in both directions.  Left to right
    is the narrowing: each declared family is a subfamily of
    [Run.valid_input].  Right to left is what makes the permissive
    default a real obligation rather than a slogan: an input the default
    admits satisfies one of the two declarations
    ([Run.valid_input_hwcap_splits]), so proving both declared statements
    proves the undeclared one.  A task that says nothing about its hart
    is held to both readings. *)
Lemma strong_universal_T_hwcap_splits :
  strong_universal_T source_image target_image
  <-> (strong_universal_T_hwcap_rv64gc /\ strong_universal_T_hwcap_rv64gcv).
Proof.
  split.
  - intros H. split; intros en_s en_t inp Hs Ht Hv; apply H; try assumption.
    + exact (valid_input_of_valid_input_hwcap_rv64gc _ Hv).
    + exact (valid_input_of_valid_input_hwcap_rv64gcv _ Hv).
  - intros (Hgc & Hgcv) en_s en_t inp Hs Ht Hv.
    destruct (valid_input_hwcap_splits _ Hv) as [Hv' | Hv'].
    + exact (Hgc _ _ _ Hs Ht Hv').
    + exact (Hgcv _ _ _ Hs Ht Hv').
Qed.

Lemma strong_universal_error_free_T_hwcap_splits :
  strong_universal_error_free_T source_image target_image
  <-> (strong_universal_error_free_T_hwcap_rv64gc
       /\ strong_universal_error_free_T_hwcap_rv64gcv).
Proof.
  split.
  - intros H. split; intros en_s en_t inp Hs Ht Hv; apply H; try assumption.
    + exact (valid_input_of_valid_input_hwcap_rv64gc _ Hv).
    + exact (valid_input_of_valid_input_hwcap_rv64gcv _ Hv).
  - intros (Hgc & Hgcv) en_s en_t inp Hs Ht Hv.
    destruct (valid_input_hwcap_splits _ Hv) as [Hv' | Hv'].
    + exact (Hgc _ _ _ Hs Ht Hv').
    + exact (Hgcv _ _ _ Hs Ht Hv').
Qed.

End SpecHwcap.

(** The sealing surfaces per declared word, beside [SPEC_VA_ANY].  A
    generated Checker ascribes ONE of them, and which one is the task's
    declaration: a proof made under [Run.valid_input_hwcap_rv64gc] does
    not type-check against [SPEC], because [SPEC]'s statement ranges over
    inputs carrying the other word too.  Unlike [SPEC_SV39] and
    [SPEC_SV57], every one of these is inhabitable today -- nothing in
    the arms refuses either word -- and [SPEC] itself remains the
    conjunction of the first two. *)
Module Type SPEC_HWCAP_RV64GC (Source : MemImage) (Target : MemImage).
  Parameter strong_universal :
    strong_universal_T_hwcap_rv64gc
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_HWCAP_RV64GC.

Module Type SPEC_HWCAP_RV64GCV (Source : MemImage) (Target : MemImage).
  Parameter strong_universal :
    strong_universal_T_hwcap_rv64gcv
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_HWCAP_RV64GCV.

Module Type SPEC_ERROR_FREE_HWCAP_RV64GC (Source : MemImage) (Target : MemImage).
  Parameter strong_universal_error_free :
    strong_universal_error_free_T_hwcap_rv64gc
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_ERROR_FREE_HWCAP_RV64GC.

Module Type SPEC_ERROR_FREE_HWCAP_RV64GCV (Source : MemImage) (Target : MemImage).
  Parameter strong_universal_error_free :
    strong_universal_error_free_T_hwcap_rv64gcv
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_ERROR_FREE_HWCAP_RV64GCV.

(* =========================================================================
   The same statements under a SPURIOUS-FAILURE CONFIGURATION
   ([Run.SpuriousCfg], [Run.run_scfg])
   =========================================================================

   [Run.may_fail_cfg] is the reading every statement above has: the
   environment may refuse any injected syscall — an [openat] of a file
   that exists, an [mmap] while budget remains, a [getrandom] — so a
   program whose failure path faults is not error-free, and no
   classifier that reads its input decides anything.  A configuration
   sets each of the six families of [Run.injected_table] to that reading
   or to "fails only if forced", under which a refusal is admitted only
   where the state leaves no other answer.  Which configuration a task
   is stated under is a PROPERTY OF THE TASK, fixed by the sealed module
   type the per-problem Checker ascribes ([SPEC_SCFG] /
   [SPEC_ERROR_FREE_SCFG]), so a proof made under one configuration
   cannot be graded under another.

   Nothing above this section moves.  At [Run.may_fail_cfg] every
   [_scfg] statement IS the unparameterized one
   ([strong_universal_T_scfg_may_fail],
   [strong_universal_error_free_T_scfg_may_fail]); the bridge is an
   [<->] rather than a conversion because [Run.run_scfg] walks
   [Run.sstep_cfg] where [Run.run] walks [Run.sstep], and the two are
   the same relation by [Run.sstep_cfg_may_fail], not by definition.

   Turning a family off only REMOVES executions ([Run.run_scfg_sub_traces]
   and its siblings), which cuts both ways and a reader should hold both
   in mind.  Error-freedom and coverage of a run are inherited downward
   ([error_free_scfg_of_error_free], [modeled_scfg_of_modeled]): a
   program proved error-free under may-fail is error-free under every
   configuration.  Equivalence is NOT — [equiv] compares trace SETS and
   its escape reads [Run.bh_all_errors], a universal over successors —
   so [strong_universal_T_scfg] at one configuration says nothing about
   another, and that is the reason the configuration is sealed. *)

(** The three behavior-level predicates respect [Run.behavior_equiv],
    which is what carries [Run.run_scfg_may_fail] up to statements. *)
Lemma trace_equiv_behavior_equiv : forall s s' t t',
  behavior_equiv s s' -> behavior_equiv t t' ->
  (trace_equiv (bh_traces s) (bh_traces t) <-> trace_equiv (bh_traces s') (bh_traces t')).
Proof.
  intros s s' t t' (Hs & _) (Ht & _).
  split; intros H tr; specialize (H tr); specialize (Hs tr); specialize (Ht tr); tauto.
Qed.

Lemma equiv_behavior_equiv : forall s s' t t',
  behavior_equiv s s' -> behavior_equiv t t' -> (equiv s t <-> equiv s' t').
Proof.
  intros s s' t t' Hs Ht.
  pose proof (trace_equiv_behavior_equiv _ _ _ _ Hs Ht) as Htr.
  destruct Hs as (_ & _ & Hsa & _). destruct Ht as (_ & Hte & _ & _).
  unfold equiv. tauto.
Qed.

Lemma modeled_behavior_equiv : forall b b',
  behavior_equiv b b' -> (modeled b <-> modeled b').
Proof. intros b b' (_ & _ & _ & Hu). unfold modeled. tauto. Qed.

Lemma error_free_behavior_equiv : forall b b',
  behavior_equiv b b' -> (error_free b <-> error_free b').
Proof. intros b b' (_ & He & _ & _). unfold error_free. tauto. Qed.

(** The same transport for the two predicates the abort declaration
    added.  [dies_by_signal] is read off [Run.bh_traces], which is
    [Run.behavior_equiv]'s first conjunct, so it transports for the same
    reason [trace_equiv] does. *)
Lemma dies_by_signal_behavior_equiv : forall b b',
  behavior_equiv b b' -> (dies_by_signal b <-> dies_by_signal b').
Proof.
  intros b b' (Htr & _ & _ & _). unfold dies_by_signal.
  split; intros (tr & sig & fs & Hin & Hkill);
    exists tr, sig, fs; split; try (apply Htr; exact Hin); exact Hkill.
Qed.

Lemma error_free_unkilled_behavior_equiv : forall b b',
  behavior_equiv b b' -> (error_free_unkilled b <-> error_free_unkilled b').
Proof.
  intros b b' Hb. unfold error_free_unkilled.
  pose proof (error_free_behavior_equiv _ _ Hb).
  pose proof (dies_by_signal_behavior_equiv _ _ Hb).
  tauto.
Qed.

Section SpecScfg.

Variable cfg : SpuriousCfg.
Variable source_image : Image.
Variable target_image : Image.

(** [strong_equiv] with both runs under [cfg]: the same two clauses,
    the same budgets, the same entries. *)
Definition strong_equiv_scfg (en_source en_target : ExecEntry)
    (inp : ProcInput) : Prop :=
  modeled (run_scfg cfg source_image source_alloc_limit en_source inp)
  /\
  equiv (run_scfg cfg source_image source_alloc_limit en_source inp)
        (run_scfg cfg target_image target_alloc_limit en_target inp).

Definition strong_universal_T_scfg : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input inp ->
    strong_equiv_scfg en_source en_target inp.

Definition strong_equiv_error_free_scfg (en_source en_target : ExecEntry)
    (inp : ProcInput) : Prop :=
  error_free (run_scfg cfg source_image source_alloc_limit en_source inp)
  /\ error_free (run_scfg cfg target_image target_alloc_limit en_target inp)
  /\ trace_equiv
       (bh_traces (run_scfg cfg source_image source_alloc_limit en_source inp))
       (bh_traces (run_scfg cfg target_image target_alloc_limit en_target inp)).

Definition strong_universal_error_free_T_scfg : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input inp ->
    strong_equiv_error_free_scfg en_source en_target inp.

(** The error-free shape still discharges the baseline shape under every
    configuration, for the reason it does under none: everything
    unmodeled errors ([Run.run_scfg_unmodeled_errors]). *)
Lemma strong_equiv_error_free_scfg_implies : forall en_source en_target inp,
  strong_equiv_error_free_scfg en_source en_target inp ->
  strong_equiv_scfg en_source en_target inp.
Proof.
  intros en_source en_target inp (Hsef & Htef & Htr).
  split.
  - intros Hun. apply Hsef, run_scfg_unmodeled_errors, Hun.
  - right. split; [exact Htr | exact Htef].
Qed.

Lemma strong_universal_error_free_T_scfg_implies :
  strong_universal_error_free_T_scfg -> strong_universal_T_scfg.
Proof.
  intros H en_source en_target inp Hsrc Htgt Hinp.
  apply strong_equiv_error_free_scfg_implies, H; assumption.
Qed.

(* -------------------------------------------------------------------------
   The abort stances, for the classifier shape
   ------------------------------------------------------------------------- *)

(** WHY THESE EXIST AT ALL, given that the abort declaration already has
    a statement family.

    [strong_universal_T_abort] and its error-free twin are stated over
    [Run.run], the baseline shape.  A classifier task is stated over
    [Run.run_scfg] instead — it has to be, because a classifier that
    reads its input file cannot decide anything under a reading where
    the open may be refused without cause, which is the whole reason the
    configuration exists.  So a C++ task whose reference ends a rejected
    allocation in [abort] had the declaration available in one shape and
    not in the other: the two knobs were independent everywhere except
    in the statements a task can actually be given.

    These four close that.  They are the [_scfg] statements with the
    quantifier the abort family uses, and nothing else changes: the
    per-triple obligations are the [_scfg] ones, the configuration is
    threaded the same way, and the two knobs stay orthogonal —
    a task picks a [Run.SpuriousCfg] and a stance, and every combination
    is stateable.

    WHAT IS NOT HERE, deliberately: no new per-triple obligation for the
    baseline [strong_equiv_scfg] shape, because the abort declaration
    changes what the RUN admits and not what the comparison asks.  Only
    the error-free family needs a triple of its own, for the reason
    [strong_equiv_error_free_abort] gives: with the declaration on an
    abort is not an error, so [error_free] alone would stop seeing it. *)
Definition strong_universal_T_scfg_abort : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort inp ->
    strong_equiv_scfg en_source en_target inp.

Definition strong_universal_T_scfg_either : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_either inp ->
    strong_equiv_scfg en_source en_target inp.

(** The split, exactly as the baseline family has it: a task that says
    nothing about the abort path is held to both readings, and to
    nothing more.  The left conjunct is [strong_universal_T_scfg]
    UNCHANGED — this change adds statements and alters none, so every
    proof already made under the classifier shape still says what it
    said. *)
Lemma strong_universal_T_scfg_either_splits :
  strong_universal_T_scfg_either
  <-> (strong_universal_T_scfg /\ strong_universal_T_scfg_abort).
Proof.
  split.
  - intros H. split; intros en_s en_t inp Hs Ht Hv; apply H;
      try assumption;
      [ exact (valid_input_either_of_valid_input _ Hv)
      | exact (valid_input_either_of_valid_input_abort _ Hv) ].
  - intros (Hoff & Hon) en_s en_t inp Hs Ht Hv.
    destruct (valid_input_either_splits _ Hv) as [Hv' | Hv'];
      [ exact (Hoff _ _ _ Hs Ht Hv') | exact (Hon _ _ _ Hs Ht Hv') ].
Qed.

(** The projections, for [strong_universal_T_either_implies]' reason. *)
Lemma strong_universal_T_scfg_either_implies :
  strong_universal_T_scfg_either -> strong_universal_T_scfg.
Proof.
  intros H. exact (proj1 (proj1 strong_universal_T_scfg_either_splits H)).
Qed.

Lemma strong_universal_T_scfg_either_implies_abort :
  strong_universal_T_scfg_either -> strong_universal_T_scfg_abort.
Proof.
  intros H. exact (proj2 (proj1 strong_universal_T_scfg_either_splits H)).
Qed.

(** The error-free triple under the declaration, in the classifier
    shape.  [error_free_unkilled] rather than [error_free], for
    [strong_equiv_error_free_abort]'s reason: with the declaration on an
    abort takes no error transition, so the plain predicate would be
    satisfied by a program that aborts on every input and turning the
    declaration on would silently weaken every error-free obligation. *)
Definition strong_equiv_error_free_scfg_abort (en_source en_target : ExecEntry)
    (inp : ProcInput) : Prop :=
  error_free_unkilled (run_scfg cfg source_image source_alloc_limit en_source inp)
  /\ error_free_unkilled (run_scfg cfg target_image target_alloc_limit en_target inp)
  /\ trace_equiv
       (bh_traces (run_scfg cfg source_image source_alloc_limit en_source inp))
       (bh_traces (run_scfg cfg target_image target_alloc_limit en_target inp)).

Definition strong_universal_error_free_T_scfg_abort : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort inp ->
    strong_equiv_error_free_scfg_abort en_source en_target inp.

(** The either shape, as the conjunction of the two stances — the same
    shape [strong_universal_error_free_T_either] takes in the baseline
    family, and for the same reason: the two stances do not share a
    per-triple obligation, so a single quantifier shell would have to
    pick one and would ask a task that declined to choose for more than
    declining promises. *)
Definition strong_universal_error_free_T_scfg_either : Prop :=
  strong_universal_error_free_T_scfg /\ strong_universal_error_free_T_scfg_abort.

(** The error-free shape discharges the baseline shape under the
    declaration, for the reason it does without one: everything
    unmodeled errors, and a killed run is not a counterexample to
    [equiv] but to the conjunct [error_free_unkilled] adds. *)
Lemma strong_equiv_error_free_scfg_abort_implies : forall en_source en_target inp,
  strong_equiv_error_free_scfg_abort en_source en_target inp ->
  strong_equiv_scfg en_source en_target inp.
Proof.
  intros en_source en_target inp (Hsef & Htef & Htr).
  split.
  - intros Hun.
    apply (error_free_unkilled_error_free _ Hsef), run_scfg_unmodeled_errors, Hun.
  - right. split;
      [exact Htr | exact (error_free_unkilled_error_free _ Htef)].
Qed.

Lemma strong_universal_error_free_T_scfg_abort_implies :
  strong_universal_error_free_T_scfg_abort -> strong_universal_T_scfg_abort.
Proof.
  intros H en_s en_t inp Hs Ht Hv.
  apply strong_equiv_error_free_scfg_abort_implies, H; assumption.
Qed.

(** Held to both, in both directions: the either shape IS the pair, so
    the split is an [iff] and each stance is a projection. *)
Lemma strong_universal_error_free_T_scfg_either_splits :
  strong_universal_error_free_T_scfg_either
  <-> (strong_universal_error_free_T_scfg
       /\ strong_universal_error_free_T_scfg_abort).
Proof. reflexivity. Qed.

Lemma strong_universal_error_free_T_scfg_either_implies :
  strong_universal_error_free_T_scfg_either ->
  strong_universal_error_free_T_scfg.
Proof. intros (H & _). exact H. Qed.

Lemma strong_universal_error_free_T_scfg_either_implies_abort :
  strong_universal_error_free_T_scfg_either ->
  strong_universal_error_free_T_scfg_abort.
Proof. intros (_ & H). exact H. Qed.

(** ... and it bites on an abort under the classifier shape too: a
    source that can be killed on one valid triple refutes it.  Same
    clause as the baseline family's, over [Run.run_scfg]. *)
Lemma strong_universal_error_free_T_scfg_abort_refuted_by_abort :
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort inp ->
    dies_by_signal (run_scfg cfg source_image source_alloc_limit en_source inp) ->
    ~ strong_universal_error_free_T_scfg_abort.
Proof.
  intros en_s en_t inp Hs Ht Hv Hdies H.
  destruct (H en_s en_t inp Hs Ht Hv) as ((_ & Hno) & _ & _).
  exact (Hno Hdies).
Qed.

(** ... and it bites the same way: one valid triple on which the source
    can error under [cfg] refutes it. *)
Lemma strong_universal_error_free_scfg_refuted_by_source_error :
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input inp ->
    bh_errors (run_scfg cfg source_image source_alloc_limit en_source inp) ->
    ~ strong_universal_error_free_T_scfg.
Proof.
  intros en_source en_target inp Hsrc Htgt Hinp Herr H.
  destruct (H en_source en_target inp Hsrc Htgt Hinp) as (Hsef & _ & _).
  exact (Hsef Herr).
Qed.

End SpecScfg.

(** MEANING PRESERVED: at [Run.may_fail_cfg] each statement is the one
    every existing proof already carries. *)
Lemma strong_equiv_scfg_may_fail : forall s t en_s en_t inp,
  strong_equiv_scfg may_fail_cfg s t en_s en_t inp <-> strong_equiv s t en_s en_t inp.
Proof.
  intros s t en_s en_t inp. unfold strong_equiv_scfg, strong_equiv.
  pose proof (run_scfg_may_fail s source_alloc_limit en_s inp) as Hs.
  pose proof (run_scfg_may_fail t target_alloc_limit en_t inp) as Ht.
  pose proof (modeled_behavior_equiv _ _ Hs).
  pose proof (equiv_behavior_equiv _ _ _ _ Hs Ht).
  tauto.
Qed.

Lemma strong_universal_T_scfg_may_fail : forall s t,
  strong_universal_T_scfg may_fail_cfg s t <-> strong_universal_T s t.
Proof.
  intros s t. unfold strong_universal_T_scfg, strong_universal_T.
  split; intros H en_s en_t inp H1 H2 H3; specialize (H en_s en_t inp H1 H2 H3);
    apply strong_equiv_scfg_may_fail; exact H.
Qed.

Lemma strong_equiv_error_free_scfg_may_fail : forall s t en_s en_t inp,
  strong_equiv_error_free_scfg may_fail_cfg s t en_s en_t inp
  <-> strong_equiv_error_free s t en_s en_t inp.
Proof.
  intros s t en_s en_t inp. unfold strong_equiv_error_free_scfg, strong_equiv_error_free.
  pose proof (run_scfg_may_fail s source_alloc_limit en_s inp) as Hs.
  pose proof (run_scfg_may_fail t target_alloc_limit en_t inp) as Ht.
  pose proof (error_free_behavior_equiv _ _ Hs).
  pose proof (error_free_behavior_equiv _ _ Ht).
  pose proof (trace_equiv_behavior_equiv _ _ _ _ Hs Ht).
  tauto.
Qed.

Lemma strong_universal_error_free_T_scfg_may_fail : forall s t,
  strong_universal_error_free_T_scfg may_fail_cfg s t <-> strong_universal_error_free_T s t.
Proof.
  intros s t. unfold strong_universal_error_free_T_scfg, strong_universal_error_free_T.
  split; intros H en_s en_t inp H1 H2 H3; specialize (H en_s en_t inp H1 H2 H3);
    apply strong_equiv_error_free_scfg_may_fail; exact H.
Qed.

(** MEANING PRESERVED FOR THE ABORT STANCES TOO: at [Run.may_fail_cfg]
    each of the new classifier-shape statements is the baseline
    statement the abort declaration already had.  So the two knobs
    really are orthogonal — turning the configuration off and turning
    the declaration on are independent moves, and setting one back
    recovers the other's family exactly. *)
Lemma strong_universal_T_scfg_abort_may_fail : forall s t,
  strong_universal_T_scfg_abort may_fail_cfg s t <-> strong_universal_T_abort s t.
Proof.
  intros s t. unfold strong_universal_T_scfg_abort, strong_universal_T_abort.
  split; intros H en_s en_t inp H1 H2 H3; specialize (H en_s en_t inp H1 H2 H3);
    apply strong_equiv_scfg_may_fail; exact H.
Qed.

Lemma strong_universal_T_scfg_either_may_fail : forall s t,
  strong_universal_T_scfg_either may_fail_cfg s t <-> strong_universal_T_either s t.
Proof.
  intros s t. unfold strong_universal_T_scfg_either, strong_universal_T_either.
  split; intros H en_s en_t inp H1 H2 H3; specialize (H en_s en_t inp H1 H2 H3);
    apply strong_equiv_scfg_may_fail; exact H.
Qed.

Lemma strong_equiv_error_free_scfg_abort_may_fail : forall s t en_s en_t inp,
  strong_equiv_error_free_scfg_abort may_fail_cfg s t en_s en_t inp
  <-> strong_equiv_error_free_abort s t en_s en_t inp.
Proof.
  intros s t en_s en_t inp.
  unfold strong_equiv_error_free_scfg_abort, strong_equiv_error_free_abort.
  pose proof (run_scfg_may_fail s source_alloc_limit en_s inp) as Hs.
  pose proof (run_scfg_may_fail t target_alloc_limit en_t inp) as Ht.
  pose proof (error_free_unkilled_behavior_equiv _ _ Hs).
  pose proof (error_free_unkilled_behavior_equiv _ _ Ht).
  pose proof (trace_equiv_behavior_equiv _ _ _ _ Hs Ht).
  tauto.
Qed.

Lemma strong_universal_error_free_T_scfg_abort_may_fail : forall s t,
  strong_universal_error_free_T_scfg_abort may_fail_cfg s t
  <-> strong_universal_error_free_T_abort s t.
Proof.
  intros s t.
  unfold strong_universal_error_free_T_scfg_abort, strong_universal_error_free_T_abort.
  split; intros H en_s en_t inp H1 H2 H3; specialize (H en_s en_t inp H1 H2 H3);
    apply strong_equiv_error_free_scfg_abort_may_fail; exact H.
Qed.

(** The either shapes too, each being the pair its two stances make: the
    pin follows from the two component pins and needs nothing new. *)
Lemma strong_universal_error_free_T_scfg_either_may_fail : forall s t,
  strong_universal_error_free_T_scfg_either may_fail_cfg s t
  <-> strong_universal_error_free_T_either s t.
Proof.
  intros s t.
  unfold strong_universal_error_free_T_scfg_either,
    strong_universal_error_free_T_either.
  pose proof (strong_universal_error_free_T_scfg_may_fail s t).
  pose proof (strong_universal_error_free_T_scfg_abort_may_fail s t).
  tauto.
Qed.

(** Error-freedom and coverage are inherited DOWNWARD: fewer executions
    cannot add an error or an uncovered point.  This is the half of
    "removes executions and adds none" a task author can lean on; the
    other half — that equivalence is not inherited in either direction —
    is this section's header. *)
Lemma error_free_scfg_of_error_free : forall cfg img lim en inp,
  error_free (run img lim en inp) -> error_free (run_scfg cfg img lim en inp).
Proof. intros cfg img lim en inp Hef Herr. apply Hef, (run_scfg_sub_errors cfg), Herr. Qed.

Lemma modeled_scfg_of_modeled : forall cfg img lim en inp,
  modeled (run img lim en inp) -> modeled (run_scfg cfg img lim en inp).
Proof. intros cfg img lim en inp Hm Hun. apply Hm, (run_scfg_sub_unmodeled cfg), Hun. Qed.

(** The one-switch form, as a thin instance: the allocation
    family alone.  At [true] it is the unparameterized statement,
    [Run.alloc_only_cfg true] being [Run.may_fail_cfg] by definition. *)
Definition strong_universal_T_cfg (alloc_may_fail : bool) (s t : Image) : Prop :=
  strong_universal_T_scfg (alloc_only_cfg alloc_may_fail) s t.

Definition strong_universal_error_free_T_cfg (alloc_may_fail : bool) (s t : Image) : Prop :=
  strong_universal_error_free_T_scfg (alloc_only_cfg alloc_may_fail) s t.

Lemma strong_universal_T_cfg_true : forall s t,
  strong_universal_T_cfg true s t <-> strong_universal_T s t.
Proof. intros s t. exact (strong_universal_T_scfg_may_fail s t). Qed.

Lemma strong_universal_error_free_T_cfg_true : forall s t,
  strong_universal_error_free_T_cfg true s t <-> strong_universal_error_free_T s t.
Proof. intros s t. exact (strong_universal_error_free_T_scfg_may_fail s t). Qed.

(* =========================================================================
   SPURIOUS_CFG / SPEC_SCFG / SPEC_ERROR_FREE_SCFG — the configuration,
   sealed
   ========================================================================= *)

(** The configuration a task is stated under, as a module so that it is
    a functor ARGUMENT of the sealing surface: the generated Checker
    instantiates it beside the two images
    ([Definition cfg := Run.mkSpuriousCfg true false true true true true.])
    and the ascription fails on a proof made at any other value.  The
    default a task gets by saying nothing is [Run.may_fail_cfg], under
    which [SPEC_SCFG] states exactly what [SPEC] states. *)
Module Type SPURIOUS_CFG.
  Parameter cfg : SpuriousCfg.
End SPURIOUS_CFG.

Module Type SPEC_SCFG (Cfg : SPURIOUS_CFG) (Source : MemImage) (Target : MemImage).
  Parameter strong_universal :
    strong_universal_T_scfg Cfg.cfg
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_SCFG.

Module Type SPEC_ERROR_FREE_SCFG (Cfg : SPURIOUS_CFG) (Source : MemImage) (Target : MemImage).
  Parameter strong_universal_error_free :
    strong_universal_error_free_T_scfg Cfg.cfg
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_ERROR_FREE_SCFG.

(** The abort-declared sealing surfaces, beside [SPEC] and
    [SPEC_ERROR_FREE].  A generated Checker ascribes ONE of the pair, and
    which one it ascribed is the task's declaration: a proof made under
    [Run.valid_input] does not type-check against [SPEC_ABORT] and the
    other way round, so the stance cannot be assumed silently.
    [SPEC_EITHER] is for a task that declines to choose and is held to
    both. *)
Module Type SPEC_ABORT (Source : MemImage) (Target : MemImage).
  Parameter strong_universal :
    strong_universal_T_abort
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_ABORT.

Module Type SPEC_EITHER (Source : MemImage) (Target : MemImage).
  Parameter strong_universal :
    strong_universal_T_either
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_EITHER.

Module Type SPEC_ERROR_FREE_ABORT (Source : MemImage) (Target : MemImage).
  Parameter strong_universal_error_free :
    strong_universal_error_free_T_abort
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_ERROR_FREE_ABORT.

Module Type SPEC_ERROR_FREE_EITHER (Source : MemImage) (Target : MemImage).
  Parameter strong_universal_error_free :
    strong_universal_error_free_T_either
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_ERROR_FREE_EITHER.

(** The same four, for the classifier shape.  A generated Checker that
    ascribes one of these has declared BOTH knobs: the [SPURIOUS_CFG]
    functor argument fixes the configuration and the module type fixes
    the stance, and a proof made at any other combination fails the
    ascription rather than passing quietly.  At [Run.may_fail_cfg] each
    states what the baseline abort surface states
    ([strong_universal_T_scfg_abort_may_fail] and its siblings). *)
Module Type SPEC_SCFG_ABORT (Cfg : SPURIOUS_CFG) (Source : MemImage) (Target : MemImage).
  Parameter strong_universal :
    strong_universal_T_scfg_abort Cfg.cfg
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_SCFG_ABORT.

Module Type SPEC_SCFG_EITHER (Cfg : SPURIOUS_CFG) (Source : MemImage) (Target : MemImage).
  Parameter strong_universal :
    strong_universal_T_scfg_either Cfg.cfg
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_SCFG_EITHER.

Module Type SPEC_ERROR_FREE_SCFG_ABORT (Cfg : SPURIOUS_CFG) (Source : MemImage) (Target : MemImage).
  Parameter strong_universal_error_free :
    strong_universal_error_free_T_scfg_abort Cfg.cfg
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_ERROR_FREE_SCFG_ABORT.

Module Type SPEC_ERROR_FREE_SCFG_EITHER (Cfg : SPURIOUS_CFG) (Source : MemImage) (Target : MemImage).
  Parameter strong_universal_error_free :
    strong_universal_error_free_T_scfg_either Cfg.cfg
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_ERROR_FREE_SCFG_EITHER.

(** The one-switch sealing surface, a thin instance of the
    record form: [SPEC_CFG] at [true] states what [SPEC] states. *)
Module Type ALLOC_CFG.
  Parameter alloc_may_fail : bool.
End ALLOC_CFG.

Module Type SPEC_CFG (Cfg : ALLOC_CFG) (Source : MemImage) (Target : MemImage).
  Parameter strong_universal :
    strong_universal_T_cfg Cfg.alloc_may_fail
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_CFG.

Module Type SPEC_ERROR_FREE_CFG (Cfg : ALLOC_CFG) (Source : MemImage) (Target : MemImage).
  Parameter strong_universal_error_free :
    strong_universal_error_free_T_cfg Cfg.alloc_may_fail
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_ERROR_FREE_CFG.

(* =========================================================================
   The BUDGET-PARAMETERISED statements, under the source-within-budget
   premise
   =========================================================================

   ** What is being stated

   Every statement above pins the two budgets to
   [State.source_alloc_limit] and [State.target_alloc_limit], 16 GiB and
   512 GiB.  For a FLAVOUR PAIR — the same program built plain (the
   source) and with a sanitizer (the target) — that leaves a window: on
   an input where the plain build needs more than 16 GiB, the source is
   refused by its budget where the target, with 32 times the budget, is
   not, and the two are observably different for a reason that has
   nothing to do with the program.  The statements below close that
   window with a PREMISE rather than by changing the budgets:

     for every valid input on which the SOURCE run, under the source
     budget, never takes a budget-refused allocation, the source and
     target trace sets are equal and the target run is error-free.

   [source_within_budget] is that premise: [Run.run_budget_refused]
   negated, on the source run alone.  THE PREMISE SAYS NOTHING ABOUT
   THE TARGET RUN: that the target is not budget-refused either is what
   the side condition below buys, by measurement of the sanitizer
   runtime and not by proof.  Inputs the plain build cannot
   serve within its budget are outside the claim — the statement says
   nothing about them, true or false.  The premise sits in the
   quantifier shell beside [Run.valid_input], and like it is a fact
   about ONE run that a proof discharges per input ([Run.v]'s budget
   section says how; for a source with no MAP_NORESERVE mapping it is
   the grant clause at each ecall, decided by computation).

   The budgets are PARAMETERS of these statements, [lim_source] and
   [lim_target], the way [Run.SpuriousCfg] is a parameter of the
   [_scfg] family: [Run.run] already takes the budget, only the
   statement pins it, and a task pins it through the sealed surface
   [SPEC_BUDGETS] below by instantiating [BUDGETS].  They are NOT a
   [Run.SpuriousCfg] switch — that record is the failure-family
   switches, whose only effect is to remove executions.

   ** Why the budgets stay unequal

   Equalising them does not close the window; it moves it to the other
   side.  A sanitizer runtime's shadow is MAP_NORESERVE, and the model
   charges every first touch of a lazy page against the run's budget
   ([State.materialize_model_accesses]), so a sanitizer build with N
   bytes of live touched heap is charged about 9N/8 plus a fixed
   amount — start-up mappings, per-size-class metadata, the quarantine
   — measured at up to 261 MiB, where the plain build is charged about
   N.  Under any EQUAL budget B the sanitizer side runs out first on
   every input whose live heap falls in (8(B - b)/9, B], and it runs
   out as a materialization fault on the first shadow page that does
   not fit ([Run.sstep_instr_fault]), refuting [error_free] outright
   rather than answering -ENOMEM.  Those figures are MEASUREMENTS OF
   THE SANITIZER RUNTIME, outside this model, cited here as such; they
   are the reason for the shape and no lemma below depends on them.

   ** The side condition

   The premise is sufficient for the target when the target's budget
   covers the sanitizer's overhead on everything the source could
   allocate:

     lim_target >= 9/8 * lim_source + 261 MiB

   ([budget_headroom_ok], in integers).  If the source never takes a
   budget refusal then its live heap never exceeds [lim_source], so the
   target's charge is at most 9/8 * lim_source + 261 MiB, which fits.
   16 GiB and 512 GiB clear it by a wide margin
   ([shipped_budgets_headroom]); equal budgets do not
   ([equal_budgets_fail_headroom]).  It is an OBLIGATION of the sealed
   instance ([BUDGETS.headroom], closed by computation) rather than a
   hypothesis of the universal statement: as a hypothesis, a task with
   bad budgets would be vacuously true; as an obligation, it fails to
   type-check.

   The same obligation bounds the SOURCE budget from below, at one page
   ([State.page_size]), and that floor guards the other vacuity: at a
   zero source budget every grant is refused, the premise excludes every
   input on which the plain build allocates at all, and the statement
   holds of any allocating program by saying nothing.  One page is the
   smallest budget on which a program that allocates can satisfy the
   premise — every grant is page-rounded — so it is the floor below
   which the premise cannot hold of anything, not a claim that a
   one-page task is sensible; which budgets a task may declare is the
   task's decision.  There are two shipped instances: [ShippedBudgets]
   (16 GiB / 512 GiB, for the plain and UBSan-only flavours) and
   [SanitizerBudgets] (2 GiB / 512 GiB, for the sanitizer-instrumented
   flavours, whose allocator caps each size class well below the
   shipped source budget).  Pinned both ways:
   [zero_source_budget_fails_headroom], [shipped_budgets_headroom],
   [sanitizer_budgets_headroom].

   What is and is not proved.  The sufficiency argument cannot be
   proved in the model: the target is a DIFFERENT program, and the
   model has no relation between the two programs' allocations — the
   9/8 and the 261 MiB are properties of the sanitizer runtime in its
   large-chunk regime (for requests of a few tens of bytes the redzone
   factor is larger, and that regime is outside the measured formula;
   the shipped factor of 32 covers it by a wide margin).  What IS
   proved: the arithmetic; that at the shipped constants each
   per-triple predicate below is DEFINITIONALLY its constant-pinned
   twin ([strong_equiv_budgets_pinned] and siblings); that the
   constant-pinned universal statements imply these at the shipped
   constants ([strong_universal_T_budgets_of_pinned] and siblings —
   the premise is dropped, and the converse fails, which is the whole
   point); that error-freedom still discharges the baseline shape; and
   that a source which can error on a triple satisfying the premise
   refutes the error-free statement
   ([strong_universal_error_free_T_budgets_refuted_by_source_error]),
   so the premise does not make the statement unfalsifiable.  That the
   premise BITES — a run can reach the mark, so the family is not the
   constant-pinned one under another name — is run-level and lives in
   [Checks/BudgetPremise.v].

   A FINER PREMISE sits beside it: [source_within_budget_only] excludes
   only the inputs on which the source reaches a first-touch or a
   cumulative refusal, not those on which one request alone is larger
   than the whole budget, and the [_budgets_only] statements require
   the source to be error-free on every input it admits, keeping
   [source_within_budget] for the agreement with the target
   ([Checks/OversizeReachable.v] shows both premises on runs).

   Both stances of the abort declaration are offered, because the
   flavour-pair tasks declare it per task; the per-triple predicates
   are [strong_equiv] / [strong_equiv_error_free] /
   [strong_equiv_error_free_abort] with the budgets abstracted, and
   nothing else. *)

Section SpecBudgets.

Variable lim_source lim_target : Z.
Variable source_image : Image.
Variable target_image : Image.

(** THE PREMISE: the source run, under the source budget, never reaches
    a configuration where it is refused for exceeding that budget
    ([Run.budget_refused_at]). *)
Definition source_within_budget (en_source : ExecEntry) (inp : ProcInput) : Prop :=
  ~ run_budget_refused source_image lim_source en_source inp.

(** [strong_equiv] with the budgets abstracted. *)
Definition strong_equiv_budgets (en_source en_target : ExecEntry)
    (inp : ProcInput) : Prop :=
  modeled (run source_image lim_source en_source inp)
  /\
  equiv (run source_image lim_source en_source inp)
        (run target_image lim_target en_target inp).

(** [strong_equiv_error_free] with the budgets abstracted: the
    flavour-pair obligation. *)
Definition strong_equiv_error_free_budgets (en_source en_target : ExecEntry)
    (inp : ProcInput) : Prop :=
  error_free (run source_image lim_source en_source inp)
  /\ error_free (run target_image lim_target en_target inp)
  /\ trace_equiv
       (bh_traces (run source_image lim_source en_source inp))
       (bh_traces (run target_image lim_target en_target inp)).

(** [strong_equiv_error_free_abort] with the budgets abstracted. *)
Definition strong_equiv_error_free_budgets_abort (en_source en_target : ExecEntry)
    (inp : ProcInput) : Prop :=
  error_free_unkilled (run source_image lim_source en_source inp)
  /\ error_free_unkilled (run target_image lim_target en_target inp)
  /\ trace_equiv
       (bh_traces (run source_image lim_source en_source inp))
       (bh_traces (run target_image lim_target en_target inp)).

(** The universal statements: the shell of [strong_universal_T] (or of
    its abort-declared twin) with the premise beside the validity
    hypotheses. *)
Definition strong_universal_T_budgets : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input inp ->
    source_within_budget en_source inp ->
    strong_equiv_budgets en_source en_target inp.

Definition strong_universal_T_budgets_abort : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort inp ->
    source_within_budget en_source inp ->
    strong_equiv_budgets en_source en_target inp.

Definition strong_universal_error_free_T_budgets : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input inp ->
    source_within_budget en_source inp ->
    strong_equiv_error_free_budgets en_source en_target inp.

Definition strong_universal_error_free_T_budgets_abort : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort inp ->
    source_within_budget en_source inp ->
    strong_equiv_error_free_budgets_abort en_source en_target inp.

(** Error-freedom discharges the baseline shape, budget for budget, by
    the argument of [strong_equiv_error_free_implies]. *)
Lemma strong_equiv_error_free_budgets_implies : forall en_source en_target inp,
  strong_equiv_error_free_budgets en_source en_target inp ->
  strong_equiv_budgets en_source en_target inp.
Proof.
  intros en_source en_target inp (Hsef & Htef & Htr).
  split.
  - apply run_error_free_modeled, Hsef.
  - right. split; [exact Htr | exact Htef].
Qed.

Lemma strong_equiv_error_free_budgets_abort_implies : forall en_source en_target inp,
  strong_equiv_error_free_budgets_abort en_source en_target inp ->
  strong_equiv_budgets en_source en_target inp.
Proof.
  intros en_source en_target inp (Hsef & Htef & Htr).
  split.
  - apply run_error_free_modeled, (error_free_unkilled_error_free _ Hsef).
  - right. split;
      [exact Htr | exact (error_free_unkilled_error_free _ Htef)].
Qed.

Lemma strong_universal_error_free_T_budgets_implies :
  strong_universal_error_free_T_budgets -> strong_universal_T_budgets.
Proof.
  intros H en_s en_t inp Hs Ht Hv Hb.
  apply strong_equiv_error_free_budgets_implies, H; assumption.
Qed.

Lemma strong_universal_error_free_T_budgets_abort_implies :
  strong_universal_error_free_T_budgets_abort -> strong_universal_T_budgets_abort.
Proof.
  intros H en_s en_t inp Hs Ht Hv Hb.
  apply strong_equiv_error_free_budgets_abort_implies, H; assumption.
Qed.

(** The premise does not make the statement unfalsifiable: a source
    that can error on ONE valid triple that satisfies the premise
    refutes it, exactly as
    [strong_universal_error_free_refuted_by_source_error] refutes the
    constant-pinned statement. *)
Lemma strong_universal_error_free_T_budgets_refuted_by_source_error :
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input inp ->
    source_within_budget en_source inp ->
    bh_errors (run source_image lim_source en_source inp) ->
    ~ strong_universal_error_free_T_budgets.
Proof.
  intros en_source en_target inp Hsrc Htgt Hinp Hb Herr H.
  destruct (H en_source en_target inp Hsrc Htgt Hinp Hb) as (Hsef & _ & _).
  exact (Hsef Herr).
Qed.

(** ** The declared capability word, in the two UNCONFIGURED budget cells

    The budget-abstracted statements with the input predicate replaced
    by the pinned declarations, both stances, plain and error-free.
    THESE ARE CELLS DECLARING TASKS ARE ACTUALLY IN, which is the
    correction this block carries: the census that shipped with
    [SpecHwcap] read the may-fail task as standing on the configured
    shells, and it does not -- it is stated on these, the unconfigured
    budget shells, over [Run.valid_input] with the abort stance OFF.
    The stance-on pair beside it is here for the task that does declare
    the stance and still runs unconfigured.

    Why the declaration is wanted here and not only in the default cell
    is [SpecHwcap]'s reason unchanged: a binary that probes for a vector
    unit executes a word the modeled surface does not answer -- a
    [vlenb] read decodes as an ordinary Zicsr access and
    [Sem.csr_slice] resolves no such CSR, so the run is
    [Run.MachineUnmodeled] -- and under [Run.valid_hwcap]'s permissive
    default every statement about such a binary ranges over the
    advertised-V hart too and is false as issued.  Abstracting the
    budget does not change that: the premise
    ([source_within_budget]) is about the source run reaching the
    budget mark and reads no field of the input, so it neither rescues
    the advertised-V run nor interferes with the split.

    Each statement is its undeclared original with ONLY the input
    predicate swapped; the budget premise and both validity hypotheses
    are kept verbatim, so nothing about what the budget means changes
    with the declaration.  The BRIDGES after this section
    ([strong_universal_T_budgets_of_pinned] and the pinning
    equivalences) are deliberately not twinned: a task that wants the
    premise-dropped or constant-pinned form goes through the undeclared
    statement, which the split lemmas below hand it from the two
    declared ones. *)

(** *** The stance-off pair: the may-fail task's cell *)
Definition strong_universal_T_budgets_hwcap_rv64gc : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_hwcap_rv64gc inp ->
    source_within_budget en_source inp ->
    strong_equiv_budgets en_source en_target inp.

Definition strong_universal_T_budgets_hwcap_rv64gcv : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_hwcap_rv64gcv inp ->
    source_within_budget en_source inp ->
    strong_equiv_budgets en_source en_target inp.

Definition strong_universal_error_free_T_budgets_hwcap_rv64gc : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_hwcap_rv64gc inp ->
    source_within_budget en_source inp ->
    strong_equiv_error_free_budgets en_source en_target inp.

Definition strong_universal_error_free_T_budgets_hwcap_rv64gcv : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_hwcap_rv64gcv inp ->
    source_within_budget en_source inp ->
    strong_equiv_error_free_budgets en_source en_target inp.

(** *** The stance-on pair: the same cell with the abort path declared *)
Definition strong_universal_T_budgets_abort_hwcap_rv64gc : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort_hwcap_rv64gc inp ->
    source_within_budget en_source inp ->
    strong_equiv_budgets en_source en_target inp.

Definition strong_universal_T_budgets_abort_hwcap_rv64gcv : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort_hwcap_rv64gcv inp ->
    source_within_budget en_source inp ->
    strong_equiv_budgets en_source en_target inp.

Definition strong_universal_error_free_T_budgets_abort_hwcap_rv64gc : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort_hwcap_rv64gc inp ->
    source_within_budget en_source inp ->
    strong_equiv_error_free_budgets_abort en_source en_target inp.

Definition strong_universal_error_free_T_budgets_abort_hwcap_rv64gcv : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort_hwcap_rv64gcv inp ->
    source_within_budget en_source inp ->
    strong_equiv_error_free_budgets_abort en_source en_target inp.

(** Each undeclared statement in these cells is EXACTLY its two
    declared ones, for the reason it is in the default cell: the
    capability clause of the input predicate is a two-word disjunction
    ([Run.valid_hwcap]), and neither the budget premise nor the
    per-triple predicate reads the field.  Left to right is the
    narrowing; right to left is what makes the permissive reading a
    real obligation -- a task that says nothing about its hart is held
    to both readings. *)
Lemma strong_universal_T_budgets_hwcap_splits :
  strong_universal_T_budgets
  <-> (strong_universal_T_budgets_hwcap_rv64gc
       /\ strong_universal_T_budgets_hwcap_rv64gcv).
Proof.
  split.
  - intros H. split; intros en_s en_t inp Hs Ht Hv Hb; apply H; try assumption.
    + exact (valid_input_of_valid_input_hwcap_rv64gc _ Hv).
    + exact (valid_input_of_valid_input_hwcap_rv64gcv _ Hv).
  - intros (Hgc & Hgcv) en_s en_t inp Hs Ht Hv Hb.
    destruct (valid_input_hwcap_splits _ Hv) as [Hv' | Hv'].
    + exact (Hgc _ _ _ Hs Ht Hv' Hb).
    + exact (Hgcv _ _ _ Hs Ht Hv' Hb).
Qed.

Lemma strong_universal_error_free_T_budgets_hwcap_splits :
  strong_universal_error_free_T_budgets
  <-> (strong_universal_error_free_T_budgets_hwcap_rv64gc
       /\ strong_universal_error_free_T_budgets_hwcap_rv64gcv).
Proof.
  split.
  - intros H. split; intros en_s en_t inp Hs Ht Hv Hb; apply H; try assumption.
    + exact (valid_input_of_valid_input_hwcap_rv64gc _ Hv).
    + exact (valid_input_of_valid_input_hwcap_rv64gcv _ Hv).
  - intros (Hgc & Hgcv) en_s en_t inp Hs Ht Hv Hb.
    destruct (valid_input_hwcap_splits _ Hv) as [Hv' | Hv'].
    + exact (Hgc _ _ _ Hs Ht Hv' Hb).
    + exact (Hgcv _ _ _ Hs Ht Hv' Hb).
Qed.

Lemma strong_universal_T_budgets_abort_hwcap_splits :
  strong_universal_T_budgets_abort
  <-> (strong_universal_T_budgets_abort_hwcap_rv64gc
       /\ strong_universal_T_budgets_abort_hwcap_rv64gcv).
Proof.
  split.
  - intros H. split; intros en_s en_t inp Hs Ht Hv Hb; apply H; try assumption.
    + exact (valid_input_abort_of_valid_input_abort_hwcap_rv64gc _ Hv).
    + exact (valid_input_abort_of_valid_input_abort_hwcap_rv64gcv _ Hv).
  - intros (Hgc & Hgcv) en_s en_t inp Hs Ht Hv Hb.
    destruct (valid_input_abort_hwcap_splits _ Hv) as [Hv' | Hv'].
    + exact (Hgc _ _ _ Hs Ht Hv' Hb).
    + exact (Hgcv _ _ _ Hs Ht Hv' Hb).
Qed.

Lemma strong_universal_error_free_T_budgets_abort_hwcap_splits :
  strong_universal_error_free_T_budgets_abort
  <-> (strong_universal_error_free_T_budgets_abort_hwcap_rv64gc
       /\ strong_universal_error_free_T_budgets_abort_hwcap_rv64gcv).
Proof.
  split.
  - intros H. split; intros en_s en_t inp Hs Ht Hv Hb; apply H; try assumption.
    + exact (valid_input_abort_of_valid_input_abort_hwcap_rv64gc _ Hv).
    + exact (valid_input_abort_of_valid_input_abort_hwcap_rv64gcv _ Hv).
  - intros (Hgc & Hgcv) en_s en_t inp Hs Ht Hv Hb.
    destruct (valid_input_abort_hwcap_splits _ Hv) as [Hv' | Hv'].
    + exact (Hgc _ _ _ Hs Ht Hv' Hb).
    + exact (Hgcv _ _ _ Hs Ht Hv' Hb).
Qed.

(** The error-free reading still discharges the baseline one under each
    declaration, exactly as it does undeclared
    ([strong_universal_error_free_T_budgets_implies] and its abort
    twin): the per-triple implication does not read the input. *)
Lemma strong_universal_error_free_T_budgets_hwcap_rv64gc_implies :
  strong_universal_error_free_T_budgets_hwcap_rv64gc ->
  strong_universal_T_budgets_hwcap_rv64gc.
Proof.
  intros H en_s en_t inp Hs Ht Hv Hb.
  apply strong_equiv_error_free_budgets_implies, H; assumption.
Qed.

Lemma strong_universal_error_free_T_budgets_hwcap_rv64gcv_implies :
  strong_universal_error_free_T_budgets_hwcap_rv64gcv ->
  strong_universal_T_budgets_hwcap_rv64gcv.
Proof.
  intros H en_s en_t inp Hs Ht Hv Hb.
  apply strong_equiv_error_free_budgets_implies, H; assumption.
Qed.

Lemma strong_universal_error_free_T_budgets_abort_hwcap_rv64gc_implies :
  strong_universal_error_free_T_budgets_abort_hwcap_rv64gc ->
  strong_universal_T_budgets_abort_hwcap_rv64gc.
Proof.
  intros H en_s en_t inp Hs Ht Hv Hb.
  apply strong_equiv_error_free_budgets_abort_implies, H; assumption.
Qed.

Lemma strong_universal_error_free_T_budgets_abort_hwcap_rv64gcv_implies :
  strong_universal_error_free_T_budgets_abort_hwcap_rv64gcv ->
  strong_universal_T_budgets_abort_hwcap_rv64gcv.
Proof.
  intros H en_s en_t inp Hs Ht Hv Hb.
  apply strong_equiv_error_free_budgets_abort_implies, H; assumption.
Qed.

(** ** The finer premise: oversize refusals not excluded

    [source_within_budget] also excludes inputs on which one request's
    charge alone exceeds the budget ([Run.RefuseOversize]), so a source
    that aborts when such a request is refused can satisfy the released
    statements.  [source_within_budget_only] negates
    [Run.run_budget_only_refused], which does not count those refusals.

    The finer premise guards only the source's error-freedom.  The
    agreement with the target keeps [source_within_budget]: with unequal
    budgets the target may be granted a request the source is refused,
    and the traces then differ for no defect of the program.  Each
    statement implies its released twin ([_subsumes]). *)
Definition source_within_budget_only (en_source : ExecEntry) (inp : ProcInput) : Prop :=
  ~ run_budget_only_refused source_image lim_source en_source inp.

Lemma source_within_budget_only_of_source_within_budget : forall en_source inp,
  source_within_budget en_source inp -> source_within_budget_only en_source inp.
Proof.
  intros en_source inp H Hc. apply H. exact (run_budget_only_refused_implies _ _ _ _ Hc).
Qed.

Definition strong_universal_error_free_T_budgets_only : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input inp ->
    source_within_budget_only en_source inp ->
    error_free (run source_image lim_source en_source inp)
    /\ (source_within_budget en_source inp ->
        strong_equiv_error_free_budgets en_source en_target inp).

Lemma strong_universal_error_free_T_budgets_only_subsumes :
  strong_universal_error_free_T_budgets_only ->
  strong_universal_error_free_T_budgets.
Proof.
  intros H en_source en_target inp Hs Ht Hv Hb.
  exact (proj2 (H en_source en_target inp Hs Ht Hv
                  (source_within_budget_only_of_source_within_budget _ _ Hb)) Hb).
Qed.

Lemma strong_universal_error_free_T_budgets_only_refuted_by_source_error :
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input inp ->
    source_within_budget_only en_source inp ->
    bh_errors (run source_image lim_source en_source inp) ->
    ~ strong_universal_error_free_T_budgets_only.
Proof.
  intros en_source en_target inp Hsrc Htgt Hinp Hb Herr H.
  destruct (H en_source en_target inp Hsrc Htgt Hinp Hb) as (Hsef & _).
  exact (Hsef Herr).
Qed.

(** The abort-declared twin.  The source part asks [error_free_unkilled],
    as [strong_equiv_error_free_budgets_abort] does, so a source killed
    after a refused oversize request refutes it. *)
Definition strong_universal_error_free_T_budgets_only_abort : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort inp ->
    source_within_budget_only en_source inp ->
    error_free_unkilled (run source_image lim_source en_source inp)
    /\ (source_within_budget en_source inp ->
        strong_equiv_error_free_budgets_abort en_source en_target inp).

Lemma strong_universal_error_free_T_budgets_only_abort_subsumes :
  strong_universal_error_free_T_budgets_only_abort ->
  strong_universal_error_free_T_budgets_abort.
Proof.
  intros H en_source en_target inp Hs Ht Hv Hb.
  exact (proj2 (H en_source en_target inp Hs Ht Hv
                  (source_within_budget_only_of_source_within_budget _ _ Hb)) Hb).
Qed.

Lemma strong_universal_error_free_T_budgets_only_abort_refuted_by_source_error :
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort inp ->
    source_within_budget_only en_source inp ->
    bh_errors (run source_image lim_source en_source inp) ->
    ~ strong_universal_error_free_T_budgets_only_abort.
Proof.
  intros en_source en_target inp Hsrc Htgt Hinp Hb Herr H.
  destruct (H en_source en_target inp Hsrc Htgt Hinp Hb) as ((Hsef & _) & _).
  exact (Hsef Herr).
Qed.

Lemma strong_universal_error_free_T_budgets_only_abort_refuted_by_abort :
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort inp ->
    source_within_budget_only en_source inp ->
    dies_by_signal (run source_image lim_source en_source inp) ->
    ~ strong_universal_error_free_T_budgets_only_abort.
Proof.
  intros en_source en_target inp Hsrc Htgt Hinp Hb Hdies H.
  destruct (H en_source en_target inp Hsrc Htgt Hinp Hb) as ((_ & Hno) & _).
  exact (Hno Hdies).
Qed.

End SpecBudgets.

(** At the shipped constants each per-triple predicate IS its
    constant-pinned twin: the [<->] is by unfolding alone. *)
Lemma strong_equiv_budgets_pinned : forall s t en_s en_t inp,
  strong_equiv_budgets source_alloc_limit target_alloc_limit s t en_s en_t inp
  <-> strong_equiv s t en_s en_t inp.
Proof. intros; split; exact (fun H => H). Qed.

Lemma strong_equiv_error_free_budgets_pinned : forall s t en_s en_t inp,
  strong_equiv_error_free_budgets source_alloc_limit target_alloc_limit s t en_s en_t inp
  <-> strong_equiv_error_free s t en_s en_t inp.
Proof. intros; split; exact (fun H => H). Qed.

Lemma strong_equiv_error_free_budgets_abort_pinned : forall s t en_s en_t inp,
  strong_equiv_error_free_budgets_abort source_alloc_limit target_alloc_limit s t en_s en_t inp
  <-> strong_equiv_error_free_abort s t en_s en_t inp.
Proof. intros; split; exact (fun H => H). Qed.

(** ... and the constant-pinned universal statements imply the budget
    ones at the shipped constants: the premise is dropped.  Never the
    converse — a budget statement says nothing on the inputs the
    premise excludes, and that is its purpose. *)
Lemma strong_universal_T_budgets_of_pinned : forall s t,
  strong_universal_T s t ->
  strong_universal_T_budgets source_alloc_limit target_alloc_limit s t.
Proof. intros s t H en_s en_t inp Hs Ht Hv _. exact (H en_s en_t inp Hs Ht Hv). Qed.

Lemma strong_universal_T_budgets_abort_of_pinned : forall s t,
  strong_universal_T_abort s t ->
  strong_universal_T_budgets_abort source_alloc_limit target_alloc_limit s t.
Proof. intros s t H en_s en_t inp Hs Ht Hv _. exact (H en_s en_t inp Hs Ht Hv). Qed.

Lemma strong_universal_error_free_T_budgets_of_pinned : forall s t,
  strong_universal_error_free_T s t ->
  strong_universal_error_free_T_budgets source_alloc_limit target_alloc_limit s t.
Proof. intros s t H en_s en_t inp Hs Ht Hv _. exact (H en_s en_t inp Hs Ht Hv). Qed.

Lemma strong_universal_error_free_T_budgets_abort_of_pinned : forall s t,
  strong_universal_error_free_T_abort s t ->
  strong_universal_error_free_T_budgets_abort source_alloc_limit target_alloc_limit s t.
Proof. intros s t H en_s en_t inp Hs Ht Hv _. exact (H en_s en_t inp Hs Ht Hv). Qed.

(* =========================================================================
   The budget premise under a SPURIOUS-FAILURE CONFIGURATION: the family
   the premise is for
   =========================================================================

   The flavour-pair tasks are stated in the classifier shape — the
   [_scfg] statements over [Run.run_scfg], pinned to a configuration
   by [SPEC_SCFG] / [SPEC_ERROR_FREE_SCFG] — and [SpecBudgets] above
   states the premise over [Run.run] alone.  This section carries it
   to the configured run, so that a task stated under a configuration
   can take the premise.

   THE PREMISE UNDER A CONFIGURATION reads the configured run:
   [source_within_budget_scfg] negates [Run.run_scfg_budget_refused],
   reachability of the same mark over the configured step relation.
   The mark itself does not depend on the configuration (it reads the
   request and the state); what a configuration changes is which
   configurations the run reaches, and it only removes some.  So the
   premise over the unfiltered run discharges the premise over any
   configured run ([source_within_budget_scfg_of_source_within_budget]),
   which is how a proof made with the unfiltered machinery — the
   reflective evaluator, the invariant principle — is reused here; and
   at [Run.may_fail_cfg] the premises are the same
   ([source_within_budget_scfg_may_fail]).  The configured reading is
   the statement's, rather than the unfiltered one, because it is the
   weaker premise: an input on which the source is budget-refused only
   along an execution the configuration removes is an input the
   configured statement covers, and the unfiltered premise would
   exclude it for nothing.

   Everything else is the [_scfg] shape with the budgets abstracted, and
   the same bridges as [SpecBudgets]: at [Run.may_fail_cfg] each
   statement is its [SpecBudgets] twin ([strong_universal_T_scfg_budgets_may_fail]
   and siblings), and at the shipped constants the constant-pinned
   [_scfg] statement implies the budget one with the premise dropped
   ([strong_universal_T_scfg_budgets_of_scfg] and siblings), never the
   converse.  Both stances of the abort declaration are stated: the
   cell with the declaration off, and the cell
   under the declaration, which bridges to [SpecScfg]'s
   [strong_universal_T_scfg_abort] and
   [strong_universal_error_free_T_scfg_abort] the same way
   ([strong_universal_T_scfg_budgets_abort_of_scfg] and its error-free
   sibling).  What the composition of the stances with the configured
   and the budget-parameterised families should look like beyond those
   cells is the matrix question the section after the sealed surfaces
   records rather than decides. *)

Section SpecScfgBudgets.

Variable cfg : SpuriousCfg.
Variable lim_source lim_target : Z.
Variable source_image : Image.
Variable target_image : Image.

(** THE PREMISE, over the configured source run. *)
Definition source_within_budget_scfg (en_source : ExecEntry) (inp : ProcInput) : Prop :=
  ~ run_scfg_budget_refused cfg source_image lim_source en_source inp.

(** The unfiltered premise discharges it: a configuration removes
    executions and adds none. *)
Lemma source_within_budget_scfg_of_source_within_budget : forall en_source inp,
  source_within_budget lim_source source_image en_source inp ->
  source_within_budget_scfg en_source inp.
Proof.
  intros en_source inp H Hc. apply H. exact (run_scfg_budget_refused_sub cfg _ _ _ _ Hc).
Qed.

(** [strong_equiv_scfg] with the budgets abstracted. *)
Definition strong_equiv_budgets_scfg (en_source en_target : ExecEntry)
    (inp : ProcInput) : Prop :=
  modeled (run_scfg cfg source_image lim_source en_source inp)
  /\
  equiv (run_scfg cfg source_image lim_source en_source inp)
        (run_scfg cfg target_image lim_target en_target inp).

(** [strong_equiv_error_free_scfg] with the budgets abstracted. *)
Definition strong_equiv_error_free_budgets_scfg (en_source en_target : ExecEntry)
    (inp : ProcInput) : Prop :=
  error_free (run_scfg cfg source_image lim_source en_source inp)
  /\ error_free (run_scfg cfg target_image lim_target en_target inp)
  /\ trace_equiv
       (bh_traces (run_scfg cfg source_image lim_source en_source inp))
       (bh_traces (run_scfg cfg target_image lim_target en_target inp)).

Definition strong_universal_T_scfg_budgets : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input inp ->
    source_within_budget_scfg en_source inp ->
    strong_equiv_budgets_scfg en_source en_target inp.

Definition strong_universal_error_free_T_scfg_budgets : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input inp ->
    source_within_budget_scfg en_source inp ->
    strong_equiv_error_free_budgets_scfg en_source en_target inp.

Lemma strong_equiv_error_free_budgets_scfg_implies : forall en_source en_target inp,
  strong_equiv_error_free_budgets_scfg en_source en_target inp ->
  strong_equiv_budgets_scfg en_source en_target inp.
Proof.
  intros en_source en_target inp (Hsef & Htef & Htr).
  split.
  - intros Hun. apply Hsef, run_scfg_unmodeled_errors, Hun.
  - right. split; [exact Htr | exact Htef].
Qed.

Lemma strong_universal_error_free_T_scfg_budgets_implies :
  strong_universal_error_free_T_scfg_budgets -> strong_universal_T_scfg_budgets.
Proof.
  intros H en_s en_t inp Hs Ht Hv Hb.
  apply strong_equiv_error_free_budgets_scfg_implies, H; assumption.
Qed.

(** A source that can error under the configuration, on a valid triple
    that satisfies the configured premise, refutes the statement. *)
Lemma strong_universal_error_free_T_scfg_budgets_refuted_by_source_error :
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input inp ->
    source_within_budget_scfg en_source inp ->
    bh_errors (run_scfg cfg source_image lim_source en_source inp) ->
    ~ strong_universal_error_free_T_scfg_budgets.
Proof.
  intros en_source en_target inp Hsrc Htgt Hinp Hb Herr H.
  destruct (H en_source en_target inp Hsrc Htgt Hinp Hb) as (Hsef & _ & _).
  exact (Hsef Herr).
Qed.



(** ** The declared capability word, in this cell

    The configured, budget-abstracted statements with
    [Run.valid_input] replaced by the pinned declarations, plain and
    error-free.  THE STANCE IS OFF HERE, and that is the correction
    this block carries: the census that shipped with [SpecHwcap] put
    the forced-only configured task in the abort-declared cell below,
    and it is in this one -- it runs under a spurious-failure
    configuration with an abstracted budget and the abort path NOT
    declared, so an abort is an error to it and not a death.

    The reason for the declaration is the one [SpecHwcap] gives and a
    configuration does not touch: a binary that probes for a vector
    unit executes a word the modeled surface does not answer, so under
    [Run.valid_hwcap]'s permissive default a statement about it ranges
    over the advertised-V hart and is false as issued.  A configuration
    removes executions and adds none
    ([source_within_budget_scfg_of_source_within_budget]), so it cannot
    put the probe back inside the modeled surface either.

    Each statement is its undeclared original with ONLY the input
    predicate swapped; the configured budget premise
    ([source_within_budget_scfg]) and both validity hypotheses are kept
    verbatim.  The BRIDGES after this section are not twinned, for the
    reason the abort cell's are not: a task wanting the premise-dropped
    or constant-pinned form goes through the undeclared statement, which
    [strong_universal_T_scfg_budgets_hwcap_splits] hands it from the two
    declared ones. *)
Definition strong_universal_T_scfg_budgets_hwcap_rv64gc : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_hwcap_rv64gc inp ->
    source_within_budget_scfg en_source inp ->
    strong_equiv_budgets_scfg en_source en_target inp.

Definition strong_universal_T_scfg_budgets_hwcap_rv64gcv : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_hwcap_rv64gcv inp ->
    source_within_budget_scfg en_source inp ->
    strong_equiv_budgets_scfg en_source en_target inp.

Definition strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_hwcap_rv64gc inp ->
    source_within_budget_scfg en_source inp ->
    strong_equiv_error_free_budgets_scfg en_source en_target inp.

Definition strong_universal_error_free_T_scfg_budgets_hwcap_rv64gcv : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_hwcap_rv64gcv inp ->
    source_within_budget_scfg en_source inp ->
    strong_equiv_error_free_budgets_scfg en_source en_target inp.

(** The undeclared statement in this cell is EXACTLY the two declared
    ones: [Run.valid_hwcap] is a two-word disjunction and neither the
    configured premise nor the configured runs read the field. *)
Lemma strong_universal_T_scfg_budgets_hwcap_splits :
  strong_universal_T_scfg_budgets
  <-> (strong_universal_T_scfg_budgets_hwcap_rv64gc
       /\ strong_universal_T_scfg_budgets_hwcap_rv64gcv).
Proof.
  split.
  - intros H. split; intros en_s en_t inp Hs Ht Hv Hb; apply H; try assumption.
    + exact (valid_input_of_valid_input_hwcap_rv64gc _ Hv).
    + exact (valid_input_of_valid_input_hwcap_rv64gcv _ Hv).
  - intros (Hgc & Hgcv) en_s en_t inp Hs Ht Hv Hb.
    destruct (valid_input_hwcap_splits _ Hv) as [Hv' | Hv'].
    + exact (Hgc _ _ _ Hs Ht Hv' Hb).
    + exact (Hgcv _ _ _ Hs Ht Hv' Hb).
Qed.

Lemma strong_universal_error_free_T_scfg_budgets_hwcap_splits :
  strong_universal_error_free_T_scfg_budgets
  <-> (strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc
       /\ strong_universal_error_free_T_scfg_budgets_hwcap_rv64gcv).
Proof.
  split.
  - intros H. split; intros en_s en_t inp Hs Ht Hv Hb; apply H; try assumption.
    + exact (valid_input_of_valid_input_hwcap_rv64gc _ Hv).
    + exact (valid_input_of_valid_input_hwcap_rv64gcv _ Hv).
  - intros (Hgc & Hgcv) en_s en_t inp Hs Ht Hv Hb.
    destruct (valid_input_hwcap_splits _ Hv) as [Hv' | Hv'].
    + exact (Hgc _ _ _ Hs Ht Hv' Hb).
    + exact (Hgcv _ _ _ Hs Ht Hv' Hb).
Qed.

(** The error-free reading still discharges the baseline one under each
    declaration, exactly as it does undeclared
    ([strong_universal_error_free_T_scfg_budgets_implies]): the
    per-triple implication does not read the input. *)
Lemma strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc_implies :
  strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc ->
  strong_universal_T_scfg_budgets_hwcap_rv64gc.
Proof.
  intros H en_s en_t inp Hs Ht Hv Hb.
  apply strong_equiv_error_free_budgets_scfg_implies, H; assumption.
Qed.

Lemma strong_universal_error_free_T_scfg_budgets_hwcap_rv64gcv_implies :
  strong_universal_error_free_T_scfg_budgets_hwcap_rv64gcv ->
  strong_universal_T_scfg_budgets_hwcap_rv64gcv.
Proof.
  intros H en_s en_t inp Hs Ht Hv Hb.
  apply strong_equiv_error_free_budgets_scfg_implies, H; assumption.
Qed.

(* -------------------------------------------------------------------------
   The abort-declared cell: configured, budget-parameterised, under the
   abort declaration
   ------------------------------------------------------------------------- *)

(** The same premise and the same configured runs, quantified over
    [Run.valid_input_abort] instead of [Run.valid_input]; the error-free
    triple asks [error_free_unkilled], as [strong_equiv_error_free_abort]
    and [strong_equiv_error_free_budgets_abort] do, because under the
    declaration an abort is a death and not an error.  The premise
    itself does not see the stance: [source_within_budget_scfg] is
    stated per entry and input, and its discharge from the unfiltered
    premise ([source_within_budget_scfg_of_source_within_budget]) holds
    whatever the input declares.  The constant-pinned configured
    statements under the declaration are [SpecScfg]'s
    [strong_universal_T_scfg_abort] and
    [strong_universal_error_free_T_scfg_abort]; the premise-dropped
    implications from them are
    [strong_universal_T_scfg_budgets_abort_of_scfg] and
    [strong_universal_error_free_T_scfg_budgets_abort_of_scfg], beside
    the other bridges after this section. *)
Definition strong_equiv_error_free_budgets_scfg_abort (en_source en_target : ExecEntry)
    (inp : ProcInput) : Prop :=
  error_free_unkilled (run_scfg cfg source_image lim_source en_source inp)
  /\ error_free_unkilled (run_scfg cfg target_image lim_target en_target inp)
  /\ trace_equiv
       (bh_traces (run_scfg cfg source_image lim_source en_source inp))
       (bh_traces (run_scfg cfg target_image lim_target en_target inp)).

Definition strong_universal_T_scfg_budgets_abort : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort inp ->
    source_within_budget_scfg en_source inp ->
    strong_equiv_budgets_scfg en_source en_target inp.

Definition strong_universal_error_free_T_scfg_budgets_abort : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort inp ->
    source_within_budget_scfg en_source inp ->
    strong_equiv_error_free_budgets_scfg_abort en_source en_target inp.

Lemma strong_equiv_error_free_budgets_scfg_abort_implies : forall en_source en_target inp,
  strong_equiv_error_free_budgets_scfg_abort en_source en_target inp ->
  strong_equiv_budgets_scfg en_source en_target inp.
Proof.
  intros en_source en_target inp (Hsef & Htef & Htr).
  split.
  - intros Hun. apply (error_free_unkilled_error_free _ Hsef), run_scfg_unmodeled_errors, Hun.
  - right. split; [exact Htr | exact (error_free_unkilled_error_free _ Htef)].
Qed.

Lemma strong_universal_error_free_T_scfg_budgets_abort_implies :
  strong_universal_error_free_T_scfg_budgets_abort -> strong_universal_T_scfg_budgets_abort.
Proof.
  intros H en_s en_t inp Hs Ht Hv Hb.
  apply strong_equiv_error_free_budgets_scfg_abort_implies, H; assumption.
Qed.

(** Refuted by a source that can error under the configuration on a
    valid abort-declared triple satisfying the premise ... *)
Lemma strong_universal_error_free_T_scfg_budgets_abort_refuted_by_source_error :
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort inp ->
    source_within_budget_scfg en_source inp ->
    bh_errors (run_scfg cfg source_image lim_source en_source inp) ->
    ~ strong_universal_error_free_T_scfg_budgets_abort.
Proof.
  intros en_source en_target inp Hsrc Htgt Hinp Hb Herr H.
  destruct (H en_source en_target inp Hsrc Htgt Hinp Hb) as ((Hsef & _) & _ & _).
  exact (Hsef Herr).
Qed.

(** ... and by a source that can be killed there, the death being an
    observation the error-free shape refuses under the declaration. *)
Lemma strong_universal_error_free_T_scfg_budgets_abort_refuted_by_abort :
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort inp ->
    source_within_budget_scfg en_source inp ->
    dies_by_signal (run_scfg cfg source_image lim_source en_source inp) ->
    ~ strong_universal_error_free_T_scfg_budgets_abort.
Proof.
  intros en_source en_target inp Hsrc Htgt Hinp Hb Hdies H.
  destruct (H en_source en_target inp Hsrc Htgt Hinp Hb) as ((_ & Hno) & _ & _).
  exact (Hno Hdies).
Qed.

(** ** The declared capability word, in this cell

    The configured, budget-abstracted, abort-declared statements with
    [Run.valid_input_abort] replaced by the pinned predicates.  THIS
    CELL AND THE DEFAULT ONE are the two such a task needs: a classifier
    task whose binaries probe for a vector unit runs under a
    spurious-failure configuration with an abstracted budget and the
    abort path modeled, and under the permissive default every statement
    about such a binary is false as issued (see [SpecHwcap]'s header for
    why -- the probe word leaves the modeled surface under an advertised
    V).  No other scfg or budgets cell gets a hwcap variant: not the
    non-abort ones, not the [either] ones, and not the
    [_of_scfg] / [_may_fail] bridges, which relate cells rather than
    state obligations.  Those can be written the same way when a task
    needs one.

    The BRIDGES above are unaffected and deliberately not twinned: a
    task that has a declared-word statement in this cell and wants the
    premise-dropped or constant-pinned form goes through the undeclared
    statement, which [strong_universal_T_scfg_budgets_abort_hwcap_splits]
    gives it from the two declared ones. *)
Definition strong_universal_T_scfg_budgets_abort_hwcap_rv64gc : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort_hwcap_rv64gc inp ->
    source_within_budget_scfg en_source inp ->
    strong_equiv_budgets_scfg en_source en_target inp.

Definition strong_universal_T_scfg_budgets_abort_hwcap_rv64gcv : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort_hwcap_rv64gcv inp ->
    source_within_budget_scfg en_source inp ->
    strong_equiv_budgets_scfg en_source en_target inp.

Definition strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gc : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort_hwcap_rv64gc inp ->
    source_within_budget_scfg en_source inp ->
    strong_equiv_error_free_budgets_scfg_abort en_source en_target inp.

Definition strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gcv : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort_hwcap_rv64gcv inp ->
    source_within_budget_scfg en_source inp ->
    strong_equiv_error_free_budgets_scfg_abort en_source en_target inp.

(** The undeclared statement in this cell is EXACTLY the two declared
    ones, for the reason it is in the default cell: [Run.valid_hwcap] is
    a two-word disjunction and the premise
    ([source_within_budget_scfg]) does not read the field. *)
Lemma strong_universal_T_scfg_budgets_abort_hwcap_splits :
  strong_universal_T_scfg_budgets_abort
  <-> (strong_universal_T_scfg_budgets_abort_hwcap_rv64gc
       /\ strong_universal_T_scfg_budgets_abort_hwcap_rv64gcv).
Proof.
  split.
  - intros H. split; intros en_s en_t inp Hs Ht Hv Hb; apply H; try assumption.
    + exact (valid_input_abort_of_valid_input_abort_hwcap_rv64gc _ Hv).
    + exact (valid_input_abort_of_valid_input_abort_hwcap_rv64gcv _ Hv).
  - intros (Hgc & Hgcv) en_s en_t inp Hs Ht Hv Hb.
    destruct (valid_input_abort_hwcap_splits _ Hv) as [Hv' | Hv'].
    + exact (Hgc _ _ _ Hs Ht Hv' Hb).
    + exact (Hgcv _ _ _ Hs Ht Hv' Hb).
Qed.

Lemma strong_universal_error_free_T_scfg_budgets_abort_hwcap_splits :
  strong_universal_error_free_T_scfg_budgets_abort
  <-> (strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gc
       /\ strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gcv).
Proof.
  split.
  - intros H. split; intros en_s en_t inp Hs Ht Hv Hb; apply H; try assumption.
    + exact (valid_input_abort_of_valid_input_abort_hwcap_rv64gc _ Hv).
    + exact (valid_input_abort_of_valid_input_abort_hwcap_rv64gcv _ Hv).
  - intros (Hgc & Hgcv) en_s en_t inp Hs Ht Hv Hb.
    destruct (valid_input_abort_hwcap_splits _ Hv) as [Hv' | Hv'].
    + exact (Hgc _ _ _ Hs Ht Hv' Hb).
    + exact (Hgcv _ _ _ Hs Ht Hv' Hb).
Qed.

(** The error-free reading still discharges the baseline one under each
    declaration, exactly as it does undeclared
    ([strong_universal_error_free_T_scfg_budgets_abort_implies]): the
    per-triple implication does not read the input. *)
Lemma strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gc_implies :
  strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gc ->
  strong_universal_T_scfg_budgets_abort_hwcap_rv64gc.
Proof.
  intros H en_s en_t inp Hs Ht Hv Hb.
  apply strong_equiv_error_free_budgets_scfg_abort_implies, H; assumption.
Qed.

Lemma strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gcv_implies :
  strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gcv ->
  strong_universal_T_scfg_budgets_abort_hwcap_rv64gcv.
Proof.
  intros H en_s en_t inp Hs Ht Hv Hb.
  apply strong_equiv_error_free_budgets_scfg_abort_implies, H; assumption.
Qed.

(* -------------------------------------------------------------------------
   The finer premise, under a configuration
   ------------------------------------------------------------------------- *)

(** [SpecBudgets]' finer premise over the configured run:
    [source_within_budget_scfg_only] negates
    [Run.run_scfg_budget_only_refused], which counts the first-touch and
    the cumulative grant refusals ([Run.RefuseBudget]) the configured run
    reaches and not the oversize ones.  It is implied by the configured
    released premise and by the unfiltered finer one.  The statements
    have [SpecBudgets]' two-part shape: the finer premise guards the
    source's own error-freedom (and unkilledness, under the abort
    declaration), and the agreement with the target keeps
    [source_within_budget_scfg]. *)
Definition source_within_budget_scfg_only (en_source : ExecEntry) (inp : ProcInput) : Prop :=
  ~ run_scfg_budget_only_refused cfg source_image lim_source en_source inp.

Lemma source_within_budget_scfg_only_of_source_within_budget_scfg : forall en_source inp,
  source_within_budget_scfg en_source inp -> source_within_budget_scfg_only en_source inp.
Proof.
  intros en_source inp H Hc. apply H.
  exact (run_scfg_budget_only_refused_implies cfg _ _ _ _ Hc).
Qed.

Lemma source_within_budget_scfg_only_of_source_within_budget_only : forall en_source inp,
  source_within_budget_only lim_source source_image en_source inp ->
  source_within_budget_scfg_only en_source inp.
Proof.
  intros en_source inp H Hc. apply H.
  exact (run_scfg_budget_only_refused_sub cfg _ _ _ _ Hc).
Qed.

Definition strong_universal_error_free_T_scfg_budgets_only : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input inp ->
    source_within_budget_scfg_only en_source inp ->
    error_free (run_scfg cfg source_image lim_source en_source inp)
    /\ (source_within_budget_scfg en_source inp ->
        strong_equiv_error_free_budgets_scfg en_source en_target inp).

Lemma strong_universal_error_free_T_scfg_budgets_only_subsumes :
  strong_universal_error_free_T_scfg_budgets_only ->
  strong_universal_error_free_T_scfg_budgets.
Proof.
  intros H en_source en_target inp Hs Ht Hv Hb.
  exact (proj2 (H en_source en_target inp Hs Ht Hv
                  (source_within_budget_scfg_only_of_source_within_budget_scfg _ _ Hb)) Hb).
Qed.

Lemma strong_universal_error_free_T_scfg_budgets_only_refuted_by_source_error :
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input inp ->
    source_within_budget_scfg_only en_source inp ->
    bh_errors (run_scfg cfg source_image lim_source en_source inp) ->
    ~ strong_universal_error_free_T_scfg_budgets_only.
Proof.
  intros en_source en_target inp Hsrc Htgt Hinp Hb Herr H.
  destruct (H en_source en_target inp Hsrc Htgt Hinp Hb) as (Hsef & _).
  exact (Hsef Herr).
Qed.

Definition strong_universal_error_free_T_scfg_budgets_only_abort : Prop :=
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort inp ->
    source_within_budget_scfg_only en_source inp ->
    error_free_unkilled (run_scfg cfg source_image lim_source en_source inp)
    /\ (source_within_budget_scfg en_source inp ->
        strong_equiv_error_free_budgets_scfg_abort en_source en_target inp).

Lemma strong_universal_error_free_T_scfg_budgets_only_abort_subsumes :
  strong_universal_error_free_T_scfg_budgets_only_abort ->
  strong_universal_error_free_T_scfg_budgets_abort.
Proof.
  intros H en_source en_target inp Hs Ht Hv Hb.
  exact (proj2 (H en_source en_target inp Hs Ht Hv
                  (source_within_budget_scfg_only_of_source_within_budget_scfg _ _ Hb)) Hb).
Qed.

Lemma strong_universal_error_free_T_scfg_budgets_only_abort_refuted_by_source_error :
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort inp ->
    source_within_budget_scfg_only en_source inp ->
    bh_errors (run_scfg cfg source_image lim_source en_source inp) ->
    ~ strong_universal_error_free_T_scfg_budgets_only_abort.
Proof.
  intros en_source en_target inp Hsrc Htgt Hinp Hb Herr H.
  destruct (H en_source en_target inp Hsrc Htgt Hinp Hb) as ((Hsef & _) & _).
  exact (Hsef Herr).
Qed.

Lemma strong_universal_error_free_T_scfg_budgets_only_abort_refuted_by_abort :
  forall en_source en_target inp,
    valid_entry source_image en_source inp ->
    valid_entry target_image en_target inp ->
    valid_input_abort inp ->
    source_within_budget_scfg_only en_source inp ->
    dies_by_signal (run_scfg cfg source_image lim_source en_source inp) ->
    ~ strong_universal_error_free_T_scfg_budgets_only_abort.
Proof.
  intros en_source en_target inp Hsrc Htgt Hinp Hb Hdies H.
  destruct (H en_source en_target inp Hsrc Htgt Hinp Hb) as ((_ & Hno) & _).
  exact (Hno Hdies).
Qed.

End SpecScfgBudgets.

(** MEANING PRESERVED at [Run.may_fail_cfg]: premise and statements are
    their [SpecBudgets] twins. *)
Lemma source_within_budget_scfg_may_fail : forall ls s en inp,
  source_within_budget_scfg may_fail_cfg ls s en inp <-> source_within_budget ls s en inp.
Proof.
  intros ls s en inp. unfold source_within_budget_scfg, source_within_budget.
  rewrite (run_scfg_budget_refused_may_fail s ls en inp). reflexivity.
Qed.

Lemma strong_equiv_budgets_scfg_may_fail : forall ls lt s t en_s en_t inp,
  strong_equiv_budgets_scfg may_fail_cfg ls lt s t en_s en_t inp
  <-> strong_equiv_budgets ls lt s t en_s en_t inp.
Proof.
  intros ls lt s t en_s en_t inp. unfold strong_equiv_budgets_scfg, strong_equiv_budgets.
  pose proof (run_scfg_may_fail s ls en_s inp) as Hs.
  pose proof (run_scfg_may_fail t lt en_t inp) as Ht.
  pose proof (modeled_behavior_equiv _ _ Hs).
  pose proof (equiv_behavior_equiv _ _ _ _ Hs Ht).
  tauto.
Qed.

Lemma strong_universal_T_scfg_budgets_may_fail : forall ls lt s t,
  strong_universal_T_scfg_budgets may_fail_cfg ls lt s t
  <-> strong_universal_T_budgets ls lt s t.
Proof.
  intros ls lt s t. unfold strong_universal_T_scfg_budgets, strong_universal_T_budgets.
  split; intros H en_s en_t inp H1 H2 H3 H4.
  - apply strong_equiv_budgets_scfg_may_fail, H; try assumption.
    apply source_within_budget_scfg_may_fail; exact H4.
  - apply strong_equiv_budgets_scfg_may_fail, H; try assumption.
    apply source_within_budget_scfg_may_fail; exact H4.
Qed.

Lemma strong_equiv_error_free_budgets_scfg_may_fail : forall ls lt s t en_s en_t inp,
  strong_equiv_error_free_budgets_scfg may_fail_cfg ls lt s t en_s en_t inp
  <-> strong_equiv_error_free_budgets ls lt s t en_s en_t inp.
Proof.
  intros ls lt s t en_s en_t inp.
  unfold strong_equiv_error_free_budgets_scfg, strong_equiv_error_free_budgets.
  pose proof (run_scfg_may_fail s ls en_s inp) as Hs.
  pose proof (run_scfg_may_fail t lt en_t inp) as Ht.
  pose proof (error_free_behavior_equiv _ _ Hs).
  pose proof (error_free_behavior_equiv _ _ Ht).
  pose proof (trace_equiv_behavior_equiv _ _ _ _ Hs Ht).
  tauto.
Qed.

Lemma strong_universal_error_free_T_scfg_budgets_may_fail : forall ls lt s t,
  strong_universal_error_free_T_scfg_budgets may_fail_cfg ls lt s t
  <-> strong_universal_error_free_T_budgets ls lt s t.
Proof.
  intros ls lt s t.
  unfold strong_universal_error_free_T_scfg_budgets, strong_universal_error_free_T_budgets.
  split; intros H en_s en_t inp H1 H2 H3 H4.
  - apply strong_equiv_error_free_budgets_scfg_may_fail, H; try assumption.
    apply source_within_budget_scfg_may_fail; exact H4.
  - apply strong_equiv_error_free_budgets_scfg_may_fail, H; try assumption.
    apply source_within_budget_scfg_may_fail; exact H4.
Qed.

(** At the shipped constants each per-triple predicate IS its
    constant-pinned [_scfg] twin, and the constant-pinned configured
    statements imply the budget ones with the premise dropped. *)
Lemma strong_equiv_budgets_scfg_pinned : forall cfg s t en_s en_t inp,
  strong_equiv_budgets_scfg cfg source_alloc_limit target_alloc_limit s t en_s en_t inp
  <-> strong_equiv_scfg cfg s t en_s en_t inp.
Proof. intros; split; exact (fun H => H). Qed.

Lemma strong_equiv_error_free_budgets_scfg_pinned : forall cfg s t en_s en_t inp,
  strong_equiv_error_free_budgets_scfg cfg source_alloc_limit target_alloc_limit s t en_s en_t inp
  <-> strong_equiv_error_free_scfg cfg s t en_s en_t inp.
Proof. intros; split; exact (fun H => H). Qed.

Lemma strong_equiv_error_free_budgets_scfg_abort_pinned : forall cfg s t en_s en_t inp,
  strong_equiv_error_free_budgets_scfg_abort cfg source_alloc_limit target_alloc_limit s t en_s en_t inp
  <-> strong_equiv_error_free_scfg_abort cfg s t en_s en_t inp.
Proof. intros; split; exact (fun H => H). Qed.

Lemma strong_universal_T_scfg_budgets_of_scfg : forall cfg s t,
  strong_universal_T_scfg cfg s t ->
  strong_universal_T_scfg_budgets cfg source_alloc_limit target_alloc_limit s t.
Proof. intros cfg s t H en_s en_t inp Hs Ht Hv _. exact (H en_s en_t inp Hs Ht Hv). Qed.

Lemma strong_universal_error_free_T_scfg_budgets_of_scfg : forall cfg s t,
  strong_universal_error_free_T_scfg cfg s t ->
  strong_universal_error_free_T_scfg_budgets cfg source_alloc_limit target_alloc_limit s t.
Proof. intros cfg s t H en_s en_t inp Hs Ht Hv _. exact (H en_s en_t inp Hs Ht Hv). Qed.

(** The same bridge for the abort-declared cell: [SpecScfg]'s
    constant-pinned statements under the declaration imply the budget
    ones at the shipped constants with the premise dropped.  The
    per-triple predicates agree definitionally once the constants are
    written in ([strong_equiv_budgets_scfg_pinned] for the baseline
    triple, [strong_equiv_error_free_budgets_scfg_abort_pinned] for the
    error-free abort triple), so the proof is the one the bridges above
    use.  Never the converse, for the reason given above. *)
Lemma strong_universal_T_scfg_budgets_abort_of_scfg : forall cfg s t,
  strong_universal_T_scfg_abort cfg s t ->
  strong_universal_T_scfg_budgets_abort cfg source_alloc_limit target_alloc_limit s t.
Proof. intros cfg s t H en_s en_t inp Hs Ht Hv _. exact (H en_s en_t inp Hs Ht Hv). Qed.

Lemma strong_universal_error_free_T_scfg_budgets_abort_of_scfg : forall cfg s t,
  strong_universal_error_free_T_scfg_abort cfg s t ->
  strong_universal_error_free_T_scfg_budgets_abort cfg source_alloc_limit target_alloc_limit s t.
Proof. intros cfg s t H en_s en_t inp Hs Ht Hv _. exact (H en_s en_t inp Hs Ht Hv). Qed.


(** MEANING PRESERVED at [Run.may_fail_cfg] for the abort-declared cell:
    each statement is its [SpecBudgets] twin.  Death by a signal is read
    off the trace set, which the two runs share at may-fail. *)
Lemma dies_by_signal_scfg_may_fail : forall img lim en inp,
  dies_by_signal (run_scfg may_fail_cfg img lim en inp) <-> dies_by_signal (run img lim en inp).
Proof.
  intros img lim en inp. unfold dies_by_signal.
  destruct (run_scfg_may_fail img lim en inp) as (Ht & _).
  split; intros (tr & sig & fs & Htr & Hin); exists tr, sig, fs; split; try exact Hin;
    apply Ht; exact Htr.
Qed.

Lemma error_free_unkilled_scfg_may_fail : forall img lim en inp,
  error_free_unkilled (run_scfg may_fail_cfg img lim en inp)
  <-> error_free_unkilled (run img lim en inp).
Proof.
  intros img lim en inp. unfold error_free_unkilled.
  rewrite (error_free_behavior_equiv _ _ (run_scfg_may_fail img lim en inp)).
  rewrite (dies_by_signal_scfg_may_fail img lim en inp). reflexivity.
Qed.

Lemma strong_equiv_error_free_budgets_scfg_abort_may_fail : forall ls lt s t en_s en_t inp,
  strong_equiv_error_free_budgets_scfg_abort may_fail_cfg ls lt s t en_s en_t inp
  <-> strong_equiv_error_free_budgets_abort ls lt s t en_s en_t inp.
Proof.
  intros ls lt s t en_s en_t inp.
  unfold strong_equiv_error_free_budgets_scfg_abort, strong_equiv_error_free_budgets_abort.
  pose proof (run_scfg_may_fail s ls en_s inp) as Hs.
  pose proof (run_scfg_may_fail t lt en_t inp) as Ht.
  pose proof (error_free_unkilled_scfg_may_fail s ls en_s inp).
  pose proof (error_free_unkilled_scfg_may_fail t lt en_t inp).
  pose proof (trace_equiv_behavior_equiv _ _ _ _ Hs Ht).
  tauto.
Qed.

Lemma strong_universal_T_scfg_budgets_abort_may_fail : forall ls lt s t,
  strong_universal_T_scfg_budgets_abort may_fail_cfg ls lt s t
  <-> strong_universal_T_budgets_abort ls lt s t.
Proof.
  intros ls lt s t.
  unfold strong_universal_T_scfg_budgets_abort, strong_universal_T_budgets_abort.
  split; intros H en_s en_t inp H1 H2 H3 H4.
  - apply strong_equiv_budgets_scfg_may_fail, H; try assumption.
    apply source_within_budget_scfg_may_fail; exact H4.
  - apply strong_equiv_budgets_scfg_may_fail, H; try assumption.
    apply source_within_budget_scfg_may_fail; exact H4.
Qed.

Lemma strong_universal_error_free_T_scfg_budgets_abort_may_fail : forall ls lt s t,
  strong_universal_error_free_T_scfg_budgets_abort may_fail_cfg ls lt s t
  <-> strong_universal_error_free_T_budgets_abort ls lt s t.
Proof.
  intros ls lt s t.
  unfold strong_universal_error_free_T_scfg_budgets_abort,
    strong_universal_error_free_T_budgets_abort.
  split; intros H en_s en_t inp H1 H2 H3 H4.
  - apply strong_equiv_error_free_budgets_scfg_abort_may_fail, H; try assumption.
    apply source_within_budget_scfg_may_fail; exact H4.
  - apply strong_equiv_error_free_budgets_scfg_abort_may_fail, H; try assumption.
    apply source_within_budget_scfg_may_fail; exact H4.
Qed.

(** At the shipped constants the per-triple predicate is
    [strong_equiv_error_free_budgets_scfg_abort] with the constants
    written in, which is [SpecScfg]'s
    [strong_equiv_error_free_scfg_abort] by unfolding alone
    ([strong_equiv_error_free_budgets_scfg_abort_pinned]); the
    premise-dropped implication from its universal statement is
    [strong_universal_error_free_T_scfg_budgets_abort_of_scfg] above,
    and the identity against the unfiltered abort twin is the may-fail
    one, above. *)

(* -------------------------------------------------------------------------
   Neither stance pinned, with the budgets as parameters
   ------------------------------------------------------------------------- *)

(** The budget statements held to BOTH stances of the abort
    declaration, as the literal conjunction of both stances — which is what
    [strong_universal_T_either] is by [strong_universal_T_either_splits],
    stated here as the conjunction outright so that the projections are
    [proj1]/[proj2] and nothing has to be re-derived.  The baseline pair
    has a quantified reading over [Run.valid_input_either]
    ([strong_universal_T_budgets_either_splits]); the error-free pair
    has none, because its per-triple conclusion differs by stance
    ([error_free] against [error_free_unkilled]), so
    [strong_universal_error_free_T_budgets_either_is_conj] records only
    that it is the conjunction it is defined as. *)
Definition strong_universal_T_budgets_either (ls lt : Z) (s t : Image) : Prop :=
  strong_universal_T_budgets ls lt s t /\ strong_universal_T_budgets_abort ls lt s t.

Definition strong_universal_error_free_T_budgets_either (ls lt : Z) (s t : Image) : Prop :=
  strong_universal_error_free_T_budgets ls lt s t
  /\ strong_universal_error_free_T_budgets_abort ls lt s t.

Lemma strong_universal_T_budgets_either_splits : forall ls lt s t,
  strong_universal_T_budgets_either ls lt s t
  <-> (forall en_source en_target inp,
        valid_entry s en_source inp ->
        valid_entry t en_target inp ->
        valid_input_either inp ->
        source_within_budget ls s en_source inp ->
        strong_equiv_budgets ls lt s t en_source en_target inp).
Proof.
  intros ls lt s t. split.
  - intros (Hoff & Hon) en_s en_t inp Hs Ht Hv Hb.
    destruct (valid_input_either_splits _ Hv) as [Hv' | Hv'];
      [ exact (Hoff _ _ _ Hs Ht Hv' Hb) | exact (Hon _ _ _ Hs Ht Hv' Hb) ].
  - intros H. split; intros en_s en_t inp Hs Ht Hv Hb; apply H; try assumption;
      [ exact (valid_input_either_of_valid_input _ Hv)
      | exact (valid_input_either_of_valid_input_abort _ Hv) ].
Qed.

Lemma strong_universal_error_free_T_budgets_either_is_conj : forall ls lt s t,
  strong_universal_error_free_T_budgets_either ls lt s t
  <-> (strong_universal_error_free_T_budgets ls lt s t
       /\ strong_universal_error_free_T_budgets_abort ls lt s t).
Proof. intros; split; exact (fun H => H). Qed.

Lemma strong_universal_T_budgets_either_off : forall ls lt s t,
  strong_universal_T_budgets_either ls lt s t -> strong_universal_T_budgets ls lt s t.
Proof. intros ls lt s t H. exact (proj1 H). Qed.

Lemma strong_universal_T_budgets_either_abort : forall ls lt s t,
  strong_universal_T_budgets_either ls lt s t -> strong_universal_T_budgets_abort ls lt s t.
Proof. intros ls lt s t H. exact (proj2 H). Qed.

Lemma strong_universal_error_free_T_budgets_either_off : forall ls lt s t,
  strong_universal_error_free_T_budgets_either ls lt s t
  -> strong_universal_error_free_T_budgets ls lt s t.
Proof. intros ls lt s t H. exact (proj1 H). Qed.

Lemma strong_universal_error_free_T_budgets_either_abort : forall ls lt s t,
  strong_universal_error_free_T_budgets_either ls lt s t
  -> strong_universal_error_free_T_budgets_abort ls lt s t.
Proof. intros ls lt s t H. exact (proj2 H). Qed.

(** Error-freedom discharges the baseline shape here too, stance by
    stance. *)
Lemma strong_universal_error_free_T_budgets_either_implies : forall ls lt s t,
  strong_universal_error_free_T_budgets_either ls lt s t
  -> strong_universal_T_budgets_either ls lt s t.
Proof.
  intros ls lt s t (Hoff & Hon). split.
  - exact (strong_universal_error_free_T_budgets_implies _ _ _ _ Hoff).
  - exact (strong_universal_error_free_T_budgets_abort_implies _ _ _ _ Hon).
Qed.

(* -------------------------------------------------------------------------
   The side condition, and the sealed surface
   ------------------------------------------------------------------------- *)

(** The sanitizer runtime's fixed charge over and above 9/8 of the live
    heap, in bytes: 261 MiB, the upper end of what was measured
    (start-up mappings, per-size-class metadata, a full 256 MiB
    quarantine).  A measurement outside the model; see the section
    header. *)
Definition asan_fixed_overhead : Z := (261 * 1048576)%Z.

(** The SOURCE budget the sanitizer-instrumented flavours are stated
    under: 2 GiB, not the shipped 16 GiB.  A sealed
    ASan allocator caps each size class at 3.5 GiB, so a source over 2
    GiB is unreachable by premise anyway; OSS-Fuzz's own roughly 2.5
    GiB RSS limit is the external anchor for the number.  The plain and
    UBSan-only flavours are unaffected and stay at the shipped 16 GiB;
    the TARGET budget does not move (512 GiB, [target_alloc_limit]). *)
Definition sanitizer_source_limit : Z := 0x80000000%Z.  (* 2 GiB *)

(** [lim_target >= 9/8 * lim_source + asan_fixed_overhead], in
    integers, with the source budget at least one page (the floor the
    section header argues). *)
Definition budget_headroom_ok (lim_source lim_target : Z) : bool :=
  ((page_size <=? lim_source)
   && (9 * lim_source + 8 * asan_fixed_overhead <=? 8 * lim_target))%Z.

Lemma budget_headroom_ok_spec : forall lim_source lim_target,
  budget_headroom_ok lim_source lim_target = true
  <-> (page_size <= lim_source
       /\ 9 * lim_source + 8 * asan_fixed_overhead <= 8 * lim_target)%Z.
Proof.
  intros ls lt. unfold budget_headroom_ok.
  rewrite Bool.andb_true_iff, !Z.leb_le. reflexivity.
Qed.

(** The shipped constants clear the side condition ... *)
Lemma shipped_budgets_headroom :
  budget_headroom_ok source_alloc_limit target_alloc_limit = true.
Proof. vm_compute. reflexivity. Qed.

(** The sanitizer source budget clears the side condition against the
    unchanged (shipped) target budget. *)
Lemma sanitizer_budgets_headroom :
  budget_headroom_ok sanitizer_source_limit target_alloc_limit = true.
Proof. vm_compute. reflexivity. Qed.

(** ... and EQUAL budgets at the source's size do not: the "why not
    equal budgets" of the section header, pinned. *)
Lemma equal_budgets_fail_headroom :
  budget_headroom_ok source_alloc_limit source_alloc_limit = false.
Proof. vm_compute. reflexivity. Qed.

(** ... and neither does a ZERO source budget, however large the
    target's: the floor of the section header, pinned.  Without it a
    task could declare a source budget of 0, under which the premise is
    false on every allocating input and the statement vacuous. *)
Lemma zero_source_budget_fails_headroom :
  budget_headroom_ok 0 target_alloc_limit = false.
Proof. vm_compute. reflexivity. Qed.

(** The floor is exactly one page: a one-page source budget with the
    shipped target budget is admitted. *)
Lemma one_page_source_budget_passes_headroom :
  budget_headroom_ok page_size target_alloc_limit = true.
Proof. vm_compute. reflexivity. Qed.

(** The budgets a task is stated under, as a module so that they are a
    functor ARGUMENT of the sealing surface, the way [SPURIOUS_CFG] and
    [ALLOC_CFG] are: the generated Checker instantiates it beside the
    two images, and the ascription fails on a proof made at any other
    pair.  [headroom] is the side condition as a proof obligation of
    the instance — [vm_compute] closes it for concrete budgets, and no
    instance exists for a pair that violates it. *)
Module Type BUDGETS.
  Parameter lim_source : Z.
  Parameter lim_target : Z.
  Parameter headroom : budget_headroom_ok lim_source lim_target = true.
End BUDGETS.

(** The shipped pair, as an instance. *)
Module ShippedBudgets <: BUDGETS.
  Definition lim_source : Z := source_alloc_limit.
  Definition lim_target : Z := target_alloc_limit.
  Definition headroom : budget_headroom_ok lim_source lim_target = true :=
    shipped_budgets_headroom.
End ShippedBudgets.

(** The sanitizer pair, as an instance: the ASan/UBSan-instrumented
    flavours' claim is stated under this pair instead of
    [ShippedBudgets], differing from it in [lim_source] only (the
    target budget is unchanged).  A statement proved under
    [SanitizerBudgets] is NOT implied by the corresponding
    constant-pinned ([_of_pinned]) statement at [ShippedBudgets]'s
    constants: the smaller source budget removes MORE inputs from the
    premise, and a proof under the larger budget says nothing about
    the inputs the smaller one excludes.  The direction is one-sided —
    narrowing the premise is always sound, widening it is the thing a
    proof has to earn — which is the point of stating the
    sanitizer-flavour claim under its own, smaller, budget rather than
    reusing the shipped one. *)
Module SanitizerBudgets <: BUDGETS.
  Definition lim_source : Z := sanitizer_source_limit.
  Definition lim_target : Z := target_alloc_limit.
  Definition headroom : budget_headroom_ok lim_source lim_target = true :=
    sanitizer_budgets_headroom.
End SanitizerBudgets.

(** Pinned: the two instances share the same target budget ... *)
Lemma sanitizer_budgets_target_is_shipped :
  SanitizerBudgets.lim_target = ShippedBudgets.lim_target.
Proof. reflexivity. Qed.

(** ... and differ in the source budget, strictly downward. *)
Lemma sanitizer_source_budget_is_below_shipped :
  (SanitizerBudgets.lim_source < ShippedBudgets.lim_source)%Z.
Proof. vm_compute. reflexivity. Qed.

Module Type SPEC_BUDGETS (B : BUDGETS) (Source : MemImage) (Target : MemImage).
  Parameter strong_universal :
    strong_universal_T_budgets B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_BUDGETS.

Module Type SPEC_BUDGETS_ABORT (B : BUDGETS) (Source : MemImage) (Target : MemImage).
  Parameter strong_universal :
    strong_universal_T_budgets_abort B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_BUDGETS_ABORT.

Module Type SPEC_ERROR_FREE_BUDGETS (B : BUDGETS) (Source : MemImage) (Target : MemImage).
  Parameter strong_universal_error_free :
    strong_universal_error_free_T_budgets B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_ERROR_FREE_BUDGETS.

Module Type SPEC_ERROR_FREE_BUDGETS_ABORT (B : BUDGETS) (Source : MemImage) (Target : MemImage).
  Parameter strong_universal_error_free :
    strong_universal_error_free_T_budgets_abort B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_ERROR_FREE_BUDGETS_ABORT.

(** The unconfigured budget surfaces with the capability word declared,
    both stances.  A generated Checker in one of these cells ascribes
    ONE of a pair, and which one is the task's claim about the kernel
    its binaries are launched under;
    [strong_universal_T_budgets_hwcap_splits] and its three siblings say
    each undeclared surface above is the conjunction of its two declared
    ones.  These exist because the declaring tasks turned out to be
    here: the may-fail one on the stance-off shells, and the stance-on
    pair beside it for the task that declares the stance and runs
    unconfigured. *)
Module Type SPEC_BUDGETS_HWCAP_RV64GC (B : BUDGETS) (Source : MemImage) (Target : MemImage).
  Parameter strong_universal :
    strong_universal_T_budgets_hwcap_rv64gc B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_BUDGETS_HWCAP_RV64GC.

Module Type SPEC_BUDGETS_HWCAP_RV64GCV (B : BUDGETS) (Source : MemImage) (Target : MemImage).
  Parameter strong_universal :
    strong_universal_T_budgets_hwcap_rv64gcv B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_BUDGETS_HWCAP_RV64GCV.

Module Type SPEC_ERROR_FREE_BUDGETS_HWCAP_RV64GC (B : BUDGETS) (Source : MemImage) (Target : MemImage).
  Parameter strong_universal_error_free :
    strong_universal_error_free_T_budgets_hwcap_rv64gc B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_ERROR_FREE_BUDGETS_HWCAP_RV64GC.

Module Type SPEC_ERROR_FREE_BUDGETS_HWCAP_RV64GCV (B : BUDGETS) (Source : MemImage) (Target : MemImage).
  Parameter strong_universal_error_free :
    strong_universal_error_free_T_budgets_hwcap_rv64gcv B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_ERROR_FREE_BUDGETS_HWCAP_RV64GCV.

Module Type SPEC_BUDGETS_ABORT_HWCAP_RV64GC (B : BUDGETS) (Source : MemImage) (Target : MemImage).
  Parameter strong_universal :
    strong_universal_T_budgets_abort_hwcap_rv64gc B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_BUDGETS_ABORT_HWCAP_RV64GC.

Module Type SPEC_BUDGETS_ABORT_HWCAP_RV64GCV (B : BUDGETS) (Source : MemImage) (Target : MemImage).
  Parameter strong_universal :
    strong_universal_T_budgets_abort_hwcap_rv64gcv B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_BUDGETS_ABORT_HWCAP_RV64GCV.

Module Type SPEC_ERROR_FREE_BUDGETS_ABORT_HWCAP_RV64GC (B : BUDGETS) (Source : MemImage) (Target : MemImage).
  Parameter strong_universal_error_free :
    strong_universal_error_free_T_budgets_abort_hwcap_rv64gc B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_ERROR_FREE_BUDGETS_ABORT_HWCAP_RV64GC.

Module Type SPEC_ERROR_FREE_BUDGETS_ABORT_HWCAP_RV64GCV (B : BUDGETS) (Source : MemImage) (Target : MemImage).
  Parameter strong_universal_error_free :
    strong_universal_error_free_T_budgets_abort_hwcap_rv64gcv B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_ERROR_FREE_BUDGETS_ABORT_HWCAP_RV64GCV.

(** The configured budget surfaces: [SPEC_SCFG]'s field names, a
    configuration and a budget pair beside the images. *)
Module Type SPEC_SCFG_BUDGETS (Cfg : SPURIOUS_CFG) (B : BUDGETS)
    (Source : MemImage) (Target : MemImage).
  Parameter strong_universal :
    strong_universal_T_scfg_budgets Cfg.cfg B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_SCFG_BUDGETS.

Module Type SPEC_ERROR_FREE_SCFG_BUDGETS (Cfg : SPURIOUS_CFG) (B : BUDGETS)
    (Source : MemImage) (Target : MemImage).
  Parameter strong_universal_error_free :
    strong_universal_error_free_T_scfg_budgets Cfg.cfg B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_ERROR_FREE_SCFG_BUDGETS.

(** The configured budget surfaces with the capability word declared,
    the stance left off -- the cell the forced-only configured task is
    actually in.  [strong_universal_T_scfg_budgets_hwcap_splits] says
    the undeclared surface above is the conjunction of the two. *)
Module Type SPEC_SCFG_BUDGETS_HWCAP_RV64GC (Cfg : SPURIOUS_CFG) (B : BUDGETS)
    (Source : MemImage) (Target : MemImage).
  Parameter strong_universal :
    strong_universal_T_scfg_budgets_hwcap_rv64gc Cfg.cfg B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_SCFG_BUDGETS_HWCAP_RV64GC.

Module Type SPEC_SCFG_BUDGETS_HWCAP_RV64GCV (Cfg : SPURIOUS_CFG) (B : BUDGETS)
    (Source : MemImage) (Target : MemImage).
  Parameter strong_universal :
    strong_universal_T_scfg_budgets_hwcap_rv64gcv Cfg.cfg B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_SCFG_BUDGETS_HWCAP_RV64GCV.

Module Type SPEC_ERROR_FREE_SCFG_BUDGETS_HWCAP_RV64GC (Cfg : SPURIOUS_CFG) (B : BUDGETS)
    (Source : MemImage) (Target : MemImage).
  Parameter strong_universal_error_free :
    strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc Cfg.cfg B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_ERROR_FREE_SCFG_BUDGETS_HWCAP_RV64GC.

Module Type SPEC_ERROR_FREE_SCFG_BUDGETS_HWCAP_RV64GCV (Cfg : SPURIOUS_CFG) (B : BUDGETS)
    (Source : MemImage) (Target : MemImage).
  Parameter strong_universal_error_free :
    strong_universal_error_free_T_scfg_budgets_hwcap_rv64gcv Cfg.cfg B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_ERROR_FREE_SCFG_BUDGETS_HWCAP_RV64GCV.

(** The abort-declared configured budget surfaces,
    [SPEC_SCFG]'s field names, a configuration and a budget pair beside
    the images. *)
Module Type SPEC_SCFG_BUDGETS_ABORT (Cfg : SPURIOUS_CFG) (B : BUDGETS)
    (Source : MemImage) (Target : MemImage).
  Parameter strong_universal :
    strong_universal_T_scfg_budgets_abort Cfg.cfg B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_SCFG_BUDGETS_ABORT.

Module Type SPEC_ERROR_FREE_SCFG_BUDGETS_ABORT (Cfg : SPURIOUS_CFG) (B : BUDGETS)
    (Source : MemImage) (Target : MemImage).
  Parameter strong_universal_error_free :
    strong_universal_error_free_T_scfg_budgets_abort Cfg.cfg B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_ERROR_FREE_SCFG_BUDGETS_ABORT.

(** The same surfaces with the capability word declared.  A generated
    Checker in this cell ascribes ONE of the pair, and which one is the
    task's claim about the kernel its binaries are launched under;
    [strong_universal_T_scfg_budgets_abort_hwcap_splits] says the
    undeclared surface above is the conjunction of the two.  These four
    exist for classifier tasks whose binaries probe for a vector unit;
    no other configured or budgeted cell has a declared-word surface. *)
Module Type SPEC_SCFG_BUDGETS_ABORT_HWCAP_RV64GC (Cfg : SPURIOUS_CFG) (B : BUDGETS)
    (Source : MemImage) (Target : MemImage).
  Parameter strong_universal :
    strong_universal_T_scfg_budgets_abort_hwcap_rv64gc Cfg.cfg B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_SCFG_BUDGETS_ABORT_HWCAP_RV64GC.

Module Type SPEC_SCFG_BUDGETS_ABORT_HWCAP_RV64GCV (Cfg : SPURIOUS_CFG) (B : BUDGETS)
    (Source : MemImage) (Target : MemImage).
  Parameter strong_universal :
    strong_universal_T_scfg_budgets_abort_hwcap_rv64gcv Cfg.cfg B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_SCFG_BUDGETS_ABORT_HWCAP_RV64GCV.

Module Type SPEC_ERROR_FREE_SCFG_BUDGETS_ABORT_HWCAP_RV64GC (Cfg : SPURIOUS_CFG) (B : BUDGETS)
    (Source : MemImage) (Target : MemImage).
  Parameter strong_universal_error_free :
    strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gc Cfg.cfg B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_ERROR_FREE_SCFG_BUDGETS_ABORT_HWCAP_RV64GC.

Module Type SPEC_ERROR_FREE_SCFG_BUDGETS_ABORT_HWCAP_RV64GCV (Cfg : SPURIOUS_CFG) (B : BUDGETS)
    (Source : MemImage) (Target : MemImage).
  Parameter strong_universal_error_free :
    strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gcv Cfg.cfg B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_ERROR_FREE_SCFG_BUDGETS_ABORT_HWCAP_RV64GCV.

(** Neither stance pinned, with the budgets: a task that declines to
    choose is held to both readings. *)
Module Type SPEC_BUDGETS_EITHER (B : BUDGETS) (Source : MemImage) (Target : MemImage).
  Parameter strong_universal :
    strong_universal_T_budgets_either B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_BUDGETS_EITHER.

Module Type SPEC_ERROR_FREE_BUDGETS_EITHER (B : BUDGETS) (Source : MemImage) (Target : MemImage).
  Parameter strong_universal_error_free :
    strong_universal_error_free_T_budgets_either B.lim_source B.lim_target
      (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
      (mkImage Target.loaded_segments Target.init_pc Target.phdrs).
End SPEC_ERROR_FREE_BUDGETS_EITHER.

(* =========================================================================
   The matrix: budgets, stances and configurations
   =========================================================================

   Independent choices shape a statement: the STANCE on the
   abort declaration (off, on, or either), the CONFIGURATION of
   injected failures (the [_scfg] family, or the unfiltered run), and
   the BUDGETS (the shipped constants, or a declared pair under the
   premise).  This file states them as separate families of cells, each
   a definition with its sealed module type, and not every cell exists:
   the budget family under a configuration has no [_either] cell, while
   the unconfigured families and the configured family without budgets
   each have one.  The cells stated are the configured
   family under each stance of the abort declaration, with the shipped
   constants and with declared budgets, for the classifier and the
   error-free shapes, beside the flavour-pair base cells — and each is
   an INSTANCE.  The configured budget cell under the abort declaration
   ([strong_universal_T_scfg_budgets_abort] and its error-free form) has
   as its constant-pinned configured twin
   [strong_universal_T_scfg_abort] (with
   [strong_universal_error_free_T_scfg_abort]), and the premise-dropped
   implication between them is
   [strong_universal_T_scfg_budgets_abort_of_scfg] (with its
   error-free sibling).

   The alternative to cells is one statement parameterised by the
   choices, with today's names as its instances proved definitionally
   equal, and one sealed surface taking a stance module, a configuration
   module and a budget module beside the images.  That is the cheaper
   shape as axes are added (each new axis multiplies the cells), and it
   is what a checker generator would consume; its cost is a refactor
   that touches every sealed type in this file while keeping every
   existing name ascribable. *)

(* =========================================================================
   IMAGE_WF — module type grouping the image well-formedness checks
   ========================================================================= *)

(** The anti-vacuity checks on ONE image, as a module type: each example's
    [Checker.v] ascribes a module to [IMAGE_WF Img] for each of its two
    image modules, exactly as it ascribes the proof to [SPEC].  The
    ascription is what pins the checked statements — the generated file
    contributes only [vm_compute] proofs, and a Checker that proved the
    wrong statement (a different image, a weakened predicate) would fail
    the ascription rather than silently pass.

    The rationale for each check lives on its definition above
    ([image_entry_fetchable], [image_phdrs_readable],
    [image_brk_satisfiable]); the common shape is: an image defect that
    lets [strong_universal] hold having said nothing about either binary
    — through [equiv]'s [bh_all_errors] escape (every source execution
    errors) or through an unsatisfiable [valid_entry] premise — and that
    no test catches because the binary runs fine on real hardware.
    The proofs cannot live here as a
    functor — a functor body is type-checked once with the image abstract,
    and these checks hold by [vm_compute] on each concrete image — so the
    per-example Checker carries the (one-tactic) proofs and this module
    type carries the statements. *)
Module Type IMAGE_WF (Img : MemImage).
  Parameter entry_fetchable :
    image_entry_fetchable Img.loaded_segments Img.init_pc = true.
  Parameter phdrs_readable :
    image_phdrs_readable Img.loaded_segments Img.phdrs = true.
  Parameter brk_satisfiable :
    image_brk_satisfiable Img.loaded_segments = true.
End IMAGE_WF.
