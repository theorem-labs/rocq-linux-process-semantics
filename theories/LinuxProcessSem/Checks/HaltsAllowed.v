(** * LinuxProcessSem.Checks.HaltsAllowed — the allowed-exit statement, fired

    Not part of the trusted specification: this file is QA on the
    definitions, in the sense [Checks/Examples.v] describes.  It exists
    so that [EquivalenceDefinition.HaltsAllowed]'s statement family is
    not a family of claims nobody has met or refused.

    WHY IT IS HERE AND NOT UNDER [Checks/Cases/].  The [Cases/] tree is
    the per-arm certificate tree and [Checks.Examples] `Require Export`s
    all of it, so a [Cases/] file cannot import [Checks.Examples] — the
    dependency runs the other way.  The fixtures this file needs are
    exactly [Checks.Examples]'s images and [Checks.AbortWitness]'s
    killed run, so it sits beside [Checks.AbortWitness] and
    [Checks.SpuriousCfg], which hold the other statement-level
    witnesses for the same reason.

    ** What is pinned, and why each one

    THE POSITIVE HALF is what separates a demanding statement from an
    empty one.  [halts_allowed_T] is a [forall] over entries and inputs
    with four things to rule out at once, and nothing here would have
    noticed if no image met it.  [exit0_halts_allowed_zero] is a
    concrete image that does, at every valid entry and on every valid
    input rather than at one fixture pair — which matters, because the
    quantifier is the statement and a witness at one entry would leave
    the statement's own shape untested.

    THE NEGATIVE HALVES are the two routes out.  The error route fires
    at statement level: the undecodable image leaves the modeled surface
    on its first fetch, at a VALID entry and on a VALID input, so
    [halts_allowed_T] is refused for it at every allowed set.

    THE SIGNAL ROUTE IS TWO ROUTES, AND ONLY ONE OF THEM IS FIRED ONE
    LEVEL DOWN.

    SIGABRT.  [Run.valid_input] pins [State.in_abort_terminal] to
    [false], and with the declaration off [Kernel.Signal.tkill_spec]
    declines every call, so no run this statement quantifies over can
    reach a [State.KillEv] CARRYING SIGABRT ([Run.sstep_off_no_kill],
    which says that and no longer says "no kill").  So that refutation
    is fired where it can be — against [MustExit.must_exit_in] on
    [Checks.AbortWitness]'s killed run — and [abrt_input_not_valid_input]
    pins the reason it stops there, so a reader does not take the
    missing statement-level refutation for an oversight.

    SIGPIPE.  The same shape, through its own declaration.
    [Fs.ReadWrite.write_spec] raises signal 13 from ordinary modeled
    state — a pipe whose read end the program closed, a socket with no
    connection, a channel [State.in_channel_reader] says is unread —
    but [Fs.ReadWrite.sigpipe_write] DECLINES such a write at SIG_DFL
    unless the launch declares the death ([State.in_sigpipe_terminal]),
    and [Run.valid_input] pins that declaration [false].  So under the
    ordinary predicate no run ends in [KillEv 13]: the write is an
    error, which [must_exit_in] refutes through its error conjunct.  The
    death is reached by name, under [Run.valid_input_sigpipe_kills] for
    a pipe or a socket and [Run.valid_input_channel_closed] for a
    reader-less channel, and there a run that dies by signal 13 does not
    satisfy [must_exit_in]: that predicate's halted constructor requires
    [State.m_killed] to be [None], so it asks the program to end BY
    EXIT and not merely to end. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs Examples Omni SpuriousCfg AbortWitness GatedSize.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  Equivalence MustExit Classifier HaltsAllowed.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   The exit-0 image, at every valid entry and on every valid input
   ========================================================================= *)

(** The unfiltered twin of [Checks.BudgetPremise.exit0_must_exit_at_cfg]:
    the image exits 0 from EVERY [execve] placement, on EVERY input and
    at EVERY budget.  [Checks.Omni.exit0_exits_c] is what makes that a
    [vm_compute] over the segment image alone — the program makes no
    memory access beyond its own fetches, so the stack the entry
    describes is never looked at. *)
Lemma exit0_must_exit_at_anywhere : forall sp brk0 mbase rnd lim inp,
  must_exit_at exit0_segments verdict_accept
    (init_config exit0_segments 0x100 demo_phdrs sp brk0 mbase rnd lim inp).
Proof.
  intros. unfold init_config.
  apply (exits_c_must_exit_at _ _ 8); [reflexivity | reflexivity | apply exit0_exits_c].
Qed.

(** UNIVERSALLY QUANTIFIED (admission reason 1), and over the whole
    quantifier the statement carries: every valid entry, every valid
    input, every resolution of the nondeterminism.  The validity
    hypotheses are not used — the image exits from every placement, not
    only the valid ones — and they are still the right premises to
    discharge, because a witness that needed a narrower entry would not
    be a witness for this statement. *)
Theorem exit0_halts_allowed_zero :
  halts_allowed_T [verdict_accept] exit0_image.
Proof.
  intros [sp brk0 mbase rnd] inp _ _.
  cbn [must_exit_in exit0_image].
  apply (must_exit_at_in _ _ verdict_accept).
  - exact (exit0_must_exit_at_anywhere _ _ _ _ _ _).
  - cbn [In]. left; reflexivity.
Qed.

(** ... and therefore at the widest set too, through
    [HaltsAllowed.halts_allowed_T_mono].  This is the monotonicity
    lemma FIRED rather than stated: the singleton claim above is carried
    to [AnyExit] by nothing but the subset side condition. *)
Theorem exit0_halts_allowed_any_exit :
  halts_allowed_T AnyExit.codes exit0_image.
Proof.
  apply (halts_allowed_T_mono [verdict_accept]); [| exact exit0_halts_allowed_zero].
  intros code Hin. cbn [In] in Hin. destruct Hin as [Heq | []]. subst code.
  apply status_allowed_In. vm_compute. reflexivity.
Qed.

(** The configured reading, under the configuration the classifier layer
    pins its verdicts to.  [Checks.SpuriousCfg.exits_c_must_exit_at_cfg]
    supplies the filtered walk; nothing else changes. *)
Theorem exit0_halts_allowed_forced_only :
  halts_allowed_T_scfg forced_only_cfg [verdict_accept] exit0_image.
Proof.
  intros [sp brk0 mbase rnd] inp _ _.
  cbn [must_exit_in_scfg exit0_image].
  apply (must_exit_in_at_cfg_singleton _ _ verdict_accept).
  unfold init_config.
  apply (exits_c_must_exit_at_cfg _ _ _ 8);
    [reflexivity | reflexivity | apply exit0_exits_c].
Qed.

(** The budget reading, at the shipped source budget.  The premise is
    taken and discarded: this image allocates nothing, so no execution
    of it can be budget-refused, and the statement holds whether or not
    the premise is met. *)
Theorem exit0_halts_allowed_budgets :
  halts_allowed_T_scfg_budgets forced_only_cfg source_alloc_limit
    [verdict_accept] exit0_image.
Proof.
  intros [sp brk0 mbase rnd] inp _ _ _.
  cbn [must_exit_in_scfg exit0_image].
  apply (must_exit_in_at_cfg_singleton _ _ verdict_accept).
  unfold init_config.
  apply (exits_c_must_exit_at_cfg _ _ _ 8);
    [reflexivity | reflexivity | apply exit0_exits_c].
Qed.

(** The constant-pinned bridge fired on this image: the configured
    statement hands over the budget one with the premise dropped. *)
Example exit0_budgets_from_scfg :
  halts_allowed_T_scfg_budgets forced_only_cfg source_alloc_limit
    [verdict_accept] exit0_image.
Proof. exact (halts_allowed_T_scfg_budgets_of_scfg _ _ _ exit0_halts_allowed_forced_only). Qed.

(** The singleton bridge fired in the other direction: the set form at a
    one-element set really is the single-code form, on a concrete run. *)
Example exit0_singleton_is_must_exit_with : forall inp,
  must_exit_in [verdict_accept] exit0_image source_alloc_limit demo_entry inp
  <-> must_exit_with verdict_accept exit0_image source_alloc_limit demo_entry inp.
Proof. intros inp. apply must_exit_in_singleton. Qed.

(* =========================================================================
   [AnyExit] really covers every status the model can record
   ========================================================================= *)

(** The pin by computation, on the shape
    [Sys.Kernel.Exit.exit_spec] writes: a status whose low byte is [255]
    and whose high bytes are not zero lands in [AnyExit] under the mask.
    The general claim is
    [HaltsAllowed.any_exit_covers_masked_status]; this is the instance
    that says the general claim's [vm_compute]-decidable reading agrees
    with it on a case a reader can check by eye. *)
Example truncated_status_in_any_exit :
  In (bv_and (Z_to_bv 64 0x1ff) (Z_to_bv 64 255)) AnyExit.codes.
Proof. apply status_allowed_In. vm_compute. reflexivity. Qed.

(** The two verdict words a classifier uses are in it, which is what
    makes [AnyExit] a set a classifier task could also be stated under. *)
Example verdicts_in_any_exit :
  In verdict_accept AnyExit.codes /\ In verdict_reject AnyExit.codes.
Proof.
  split; apply status_allowed_In; vm_compute; reflexivity.
Qed.

(** ... and a word that is NOT a byte is not in it, which is what says
    the set is a real bound rather than everything.  Without this the
    coverage lemma above would be compatible with [AnyExit] holding
    every word. *)
Example non_byte_not_in_any_exit :
  status_allowed AnyExit.codes (Z_to_bv 64 256) = false.
Proof. vm_compute. reflexivity. Qed.

(* =========================================================================
   The error route: the undecodable image is refused
   ========================================================================= *)

(** UNIVERSALLY QUANTIFIED (reason 1) as the negation of one, and at
    EVERY allowed set: the image leaves the modeled surface on its first
    fetch, and [halts_allowed_T] forbids an error anywhere in the tree,
    so no set of statuses can rescue it.  The entry is
    [Checks.Examples.demo_entry] and the input the valid one, so the
    refutation really reaches inside the statement's quantifier. *)
Theorem undecodable_image_refutes_halts_allowed : forall S,
  ~ halts_allowed_T S undecodable_image.
Proof.
  intros S.
  apply (halts_allowed_T_refuted_by_error S undecodable_image demo_entry
           demo_proc_input).
  - exact (demo_entry_valid_undecodable demo_proc_input demo_input_valid).
  - exact demo_input_valid.
  - apply run_unmodeled_errors,
      run_of_undecodable_image_is_unmodeled_at_demo_entry.
Qed.

(** The same image is refused under the configured reading too: the
    fetch that leaves the surface is an instruction step, and the filter
    touches no instruction step. *)
Theorem undecodable_image_refutes_halts_allowed_forced_only : forall S,
  ~ halts_allowed_T_scfg forced_only_cfg S undecodable_image.
Proof.
  intros S H.
  apply (must_exit_in_scfg_refuted_by_error forced_only_cfg S undecodable_image
           source_alloc_limit demo_entry demo_proc_input).
  - apply run_scfg_unmodeled_errors.
    rewrite demo_entry_fields.
    cbn [run_scfg bh_unmodeled undecodable_image]. unfold init_config.
    match goal with
    | |- reaches_unmodeled_cfg _ _ ?c => exists [], c
    end.
    split; [apply star_cfg_refl |].
    split; [reflexivity |]. left. split; [reflexivity |].
    cbn [cfg_ms cfg_model].
    match goal with
    | |- mi_account_step ?segs ?ms ?model = _ =>
        rewrite (mi_account_step_no_lazy segs ms model ltac:(reflexivity))
    end.
    rewrite undecodable_step_unmodeled_at_demo_entry. reflexivity.
  - apply H; [exact (demo_entry_valid_undecodable demo_proc_input
                       demo_input_valid)
            | exact demo_input_valid].
Qed.

(* =========================================================================
   The signal route, and where it stops
   ========================================================================= *)

(** The killed run of [Checks.AbortWitness], in the shape
    [MustExit.must_exit_in_refuted_by_kill] takes.

    The entry is [Checks.AbortWitness.abrt_entry], not
    [Checks.Examples.demo_entry]: an entry is a function of its input
    now ([Run.entry_launch_ok_va] ties the stack pointer to the
    lengths of THAT input's strings, [create_elf_tables],
    fs/binfmt_elf.c, Linux v6.18.46, commit 1f99e9ab748f), and this
    run is on [abrt_input], whose argv differs from
    [demo_proc_input]'s. *)
Lemma abrt_run_reaches_killed : forall lim,
  run_reaches_killed abrt_image lim abrt_entry abrt_input.
Proof.
  intros lim. rewrite abrt_entry_fields.
  cbn [run_reaches_killed abrt_image]. rewrite abrt_config.
  exists (abrt_trace lim), (mkCfg (abrt_t 3) (abrt_killed_model lim)),
    (Z_to_bv 64 6).
  split; [exact (abrt_star lim) |].
  cbn [cfg_model]. unfold abrt_killed_model.
  exact (proj2 (killed_is_halted _ _)).
Qed.

(** THE SIGNAL REFUTATION, FIRED.  A run that dies by a signal satisfies
    [MustExit.must_exit_in] at NO allowed set — not even one containing
    the signal number, which is the point: the halted case's
    [State.m_killed] conjunct refuses a killed leaf whatever
    [State.m_halted] holds, and [State.with_killed] sets both fields to
    the signal.  So "halts with an allowed status" really does mean
    [exit_group] and not "stops running". *)
Theorem abrt_refutes_must_exit_in : forall S lim,
  ~ must_exit_in S abrt_image lim abrt_entry abrt_input.
Proof.
  intros S lim.
  exact (must_exit_in_refuted_by_kill S abrt_image lim abrt_entry abrt_input
           (abrt_run_reaches_killed lim)).
Qed.

(** ... and here is where it stops, pinned rather than left to a reader.
    [Run.valid_input] pins the abort declaration OFF, and this input
    declares it on, so the run above is not one [halts_allowed_T]
    quantifies over.  That is why the theorem above is about
    [MustExit.must_exit_in] and not about [halts_allowed_T]: the
    statement-level signal refutation is unavailable over this input
    class because the input class has no killed runs in it, not because
    the refutation was not written. *)
Example abrt_input_not_valid_input : ~ valid_input abrt_input.
Proof.
  intros Hv.
  (* Through [Run.valid_input_abort_terminal], the accessor, rather than
     by position: [Run.valid_input] grows a conjunct whenever the input
     class learns to say something new, and a positional pattern then
     names a different clause rather than failing — the witness goes on
     compiling and stops being about the abort declaration.  What this
     proof depends on is that [Run.valid_input] pins
     [State.in_abort_terminal] to [false] SOMEWHERE, which is the fact
     the prose above claims. *)
  pose proof (valid_input_abort_terminal _ Hv) as Hoff.
  rewrite abrt_input_declares_abort in Hoff. discriminate.
Qed.

(** The control, and it is what says the refutation above is about the
    DEATH rather than about the image: the same program on the
    undeclared input is refused too, but by the ERROR route — with the
    declaration clear [Kernel.Signal.tkill_spec] declines, the run
    leaves the modeled surface, and there is no [State.KillEv] to refute
    it by.  The two stances therefore differ on this image for
    [halts_allowed_T] exactly as [Checks.AbortWitness] shows they differ
    for the error-free family. *)
Example abrt_declined_undeclared_is_unmodeled :
  check_syscall (sys_input abrt_segments (abrt_t 3) (Z_to_bv 64 130))
    (mkEffect (Z_to_bv 64 0) [] [])
    (with_tid abort_tid
       (init_model (segments_reserved abrt_segments) (Z_to_bv 64 0x1000)
          (Z_to_bv 64 mmap_base_max) (Z_to_bv 64 0x7fff80000000)
          source_alloc_limit abrt_input_undeclared))
  = CheckUnmodeled.
Proof. exact abrt_tkill_declined_undeclared. Qed.

(* =========================================================================
   The set form is not the single-code form in disguise
   ========================================================================= *)

(** The statement this whole family exists for, at the level of the
    predicate: [MustExit.must_exit_in] over a two-element set is WEAKER
    than the disjunction of the two single-code claims, because a run
    may exit 0 on one resolution and 1 on another.  Stated here as the
    implication that DOES hold, in both directions of the disjunction,
    so that a reader can see the converse is not offered. *)
Example must_exit_in_pair_from_either : forall img lim en inp,
  must_exit_with verdict_accept img lim en inp
  \/ must_exit_with verdict_reject img lim en inp ->
  must_exit_in [verdict_accept; verdict_reject] img lim en inp.
Proof.
  intros img lim en inp [H | H].
  - apply (must_exit_with_in _ verdict_accept); [exact H |]. cbn [In]. left; reflexivity.
  - apply (must_exit_with_in _ verdict_reject); [exact H |].
    cbn [In]. right; left; reflexivity.
Qed.

(** The monotonicity lemma fired at the predicate level: a two-element
    allowance is implied by either singleton. *)
Example must_exit_in_mono_fired : forall img lim en inp,
  must_exit_in [verdict_accept] img lim en inp ->
  must_exit_in [verdict_accept; verdict_reject] img lim en inp.
Proof.
  intros img lim en inp H.
  apply (must_exit_in_mono [verdict_accept]); [| exact H].
  intros code Hin. cbn [In] in *. destruct Hin as [Heq | []].
  left; exact Heq.
Qed.

(* =========================================================================
   The wrong-status route, fired on an image that really exits elsewhere
   ========================================================================= *)

(** [Checks.GatedSize.exit1_image] is the exit-zero image with one
    immediate changed, so the two are interchangeable everywhere
    [Run.valid_entry] is concerned and the only difference between them
    is the status.  That is what makes it the right refutation: what
    fails is the STATUS and nothing else about the program. *)
Lemma exit1_must_exit_reject : forall lim,
  must_exit_with verdict_reject exit1_image lim demo_entry demo_proc_input.
Proof.
  intros lim. rewrite demo_entry_fields.
  cbn [must_exit_with exit1_image]. unfold init_config.
  apply (exits_c_must_exit_at _ _ 8); [reflexivity | reflexivity |].
  vm_compute. reflexivity.
Qed.

(** THE WRONG-STATUS REFUTATION, FIRED.  A program that halts cleanly,
    errors nowhere, is never killed and terminates on every execution
    still fails [halts_allowed_T] when the status it halts with is
    outside the allowed set.  Without this the statement would be
    indistinguishable, on every image in the tree, from "terminates
    cleanly" with the set along for the ride — every other refutation
    here fires on a program that fails for some OTHER reason.

    The [Run.star] comes from [MustExit.must_exit_at_realizes], which is
    the file's own non-vacuity guard used as a tool: the guard says the
    predicate really produces an exit, and that exit is what the
    refutation needs a witness of.  Its halted-field premise is proved
    in place rather than asserted at a written-out configuration:
    [Checks.Examples.demo_entry] is built by [Run.launch_entry_va] now,
    so its four fields are that file's to move and nothing here repeats
    them. *)
Theorem exit1_refutes_halts_allowed_zero :
  ~ halts_allowed_T [verdict_accept] exit1_image.
Proof.
  pose proof (exit1_must_exit_reject source_alloc_limit) as Hme.
  rewrite demo_entry_fields in Hme.
  cbn [must_exit_with exit1_image] in Hme.
  destruct (must_exit_at_realizes _ _ _ Hme
              ltac:(cbn [init_config cfg_model]; reflexivity))
    as (tr & fs & c' & Hstar & Hh).
  apply (halts_allowed_T_refuted_by_wrong_status _ exit1_image demo_entry
           demo_proc_input (tr ++ [ExitEv verdict_reject fs]) c' verdict_reject).
  - exact (demo_entry_valid_exit1 demo_proc_input demo_input_valid).
  - exact demo_input_valid.
  - rewrite demo_entry_fields. cbn [exit1_image]. exact Hstar.
  - exact Hh.
  - intros Hin. apply In_status_allowed in Hin. vm_compute in Hin. discriminate.
Qed.

(** ... and the same image PASSES at a set that admits its status, which
    is what says the refutation above is about the set and not about the
    program. *)
Example exit1_halts_allowed_at_reject :
  must_exit_in [verdict_reject] exit1_image source_alloc_limit demo_entry demo_proc_input.
Proof.
  apply must_exit_in_singleton. exact (exit1_must_exit_reject _).
Qed.

(* =========================================================================
   The sealed surfaces are inhabitable
   =========================================================================

   A module type nothing ascribes against is a module type nobody has
   shown can be met, and the three surfaces this file's statements are
   issued through need that shown.  Each is sealed here over the
   halting fixture at [HaltsAllowed.AnyExit], reusing the
   [MemImageType.MemImage] and [Equivalence.SPURIOUS_CFG] instances
   [Checks.Omni] already packages for the equivalence surfaces, so the
   image a reader sees sealed here is the image sealed there.

   [Equivalence.ShippedBudgets] is the budget pair for the third.  Its
   [headroom] obligation is about the PAIR and this statement has one
   image, so nothing here consumes it; the surface takes the whole
   module anyway, which is what keeps a one-image statement pinned to
   the same constant as the two-image statement beside it. *)

Module Exit0HaltsAllowedChecked <: SPEC_HALTS_ALLOWED AnyExit Exit0Image.
  Definition halts_allowed :
    halts_allowed_T AnyExit.codes
      (mkImage Exit0Image.loaded_segments Exit0Image.init_pc Exit0Image.phdrs)
    := exit0_halts_allowed_any_exit.
End Exit0HaltsAllowedChecked.

Module Exit0HaltsAllowedScfgChecked
  <: SPEC_HALTS_ALLOWED_SCFG MayFailCfg AnyExit Exit0Image.
  Definition halts_allowed :
    halts_allowed_T_scfg MayFailCfg.cfg AnyExit.codes
      (mkImage Exit0Image.loaded_segments Exit0Image.init_pc Exit0Image.phdrs)
    := proj2 (halts_allowed_T_scfg_may_fail _ _) exit0_halts_allowed_any_exit.
End Exit0HaltsAllowedScfgChecked.

Module Exit0HaltsAllowedBudgetsChecked
  <: SPEC_HALTS_ALLOWED_SCFG_BUDGETS MayFailCfg ShippedBudgets AnyExit Exit0Image.
  Definition halts_allowed :
    halts_allowed_T_scfg_budgets MayFailCfg.cfg ShippedBudgets.lim_source
      AnyExit.codes
      (mkImage Exit0Image.loaded_segments Exit0Image.init_pc Exit0Image.phdrs)
    := halts_allowed_T_scfg_budgets_of_scfg _ _ _
         (proj2 (halts_allowed_T_scfg_may_fail _ _) exit0_halts_allowed_any_exit).
End Exit0HaltsAllowedBudgetsChecked.
