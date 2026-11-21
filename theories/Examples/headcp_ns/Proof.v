(** * Equivalence proof for headcp-ns — top-level glue

    PROOF-SIDE FILE (not part of the trusted specification).  Discharges
    [strong_universal_operands_inside]: observable equivalence between
    the source image (Source) and the target image (Target) for all
    valid entries and every valid process input whose operands' opens
    stay inside the model ([operands_inside_model] below).

    Both binaries implement headcp: copy the first up-to-128 bytes of
    argv[1] into argv[2] with a single read and a single write.  Both
    issue every syscall through a raw ecall, so error returns are
    errno-free.  File I/O emits no trace events, so the only observables
    are the exit code and the final image.  The shared outcome set is
    [hc_outcomes fs0 cwd ur src dst] (see headcp_ns_defs), stated over
    the walk of each operand from the working folder.

    Case split (only on the INPUT):
    - [argc < 3]  -> exit 2, no file I/O  (CatSim: [cat_omni_strong_equiv_te]);
    - [argc >= 3] -> both binaries derive the same outcome set
      ([source_ge3], [target_ge3]), on what each open answers
      ([FileSimWalk.open_arm]): an errno of the first open -> 3; of the
      second -> 4; with both descriptors, a folder source -> 5, and a
      regular file, /dev/null or /dev/urandom source -> 0 with the
      bytes read written whole to a regular file, /dev/null or
      /dev/urandom destination.

    C exits 6 on a write result other than the count read and Zig on a
    negative one; the two agree because the model answers every write
    these binaries make with the whole count (a regular file, /dev/null
    and /dev/urandom alike, for a readable buffer of at most 128 bytes).

    Ported in part from theorem-labs/linux-process-semantics
    r22/namespace-core at 6ff3d045 (issue #1011). *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StreamExec StreamSim FileSim ErrEscape FileSimWalk.
From LinuxProcessSemantics.Examples.headcp_ns Require Import headcp_ns_code headcp_ns_defs headcp_ns_source headcp_ns_target.
From LinuxProcessSemantics.Examples.headcp_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.headcp_ns Require Import TargetMemImage.
From LinuxProcessSemantics.EquivalenceDefinition Require FinInput.

Import ListNotations.
Open Scope bv_scope.

(* ================================================================= *)
(* The input hypothesis.                                              *)
(* ================================================================= *)

(** EVERY OPERAND'S OPEN STAYS INSIDE THE MODEL.

    Both binaries open argv[1] with O_RDONLY (the walk
    [Fs.WalkFull true false]) and then argv[2] with
    O_WRONLY|O_CREAT|O_TRUNC (the walk [Fs.WalkCreate true]), each from
    the working folder.  The model declines such an open on exactly one
    walk end: [Fs.ROutside] -- the name proc or sys looked up at the
    root, by any spelling or link, because /proc and /sys are outside
    the model.  A device entry is answered at any key.
    [Run.valid_input] admits such an input: the root as working folder
    beside an operand proc, or a link whose body leads there.  On such
    an input the source run is declined and no equivalence can be
    stated of it.

    The hypothesis excludes those inputs and nothing else: an operand
    that is empty or does not fit in PATH_MAX is answered before any
    walk, so it is not constrained, and [operands_inside_model_iff]
    proves the hypothesis EQUIVALENT to the model answering the open of
    each operand.  Its text is pinned by tools/gen_checker.py, and the
    generated Checker.v prints it. *)
Definition operands_inside_model (inp : ProcInput) : Prop :=
  (3 <= length (in_argv inp))%nat ->
  forall (i : nat) (md : Fs.WalkMode),
    (i = 1%nat /\ md = Fs.WalkFull true false
     \/ i = 2%nat /\ md = Fs.WalkCreate true) ->
    nth i (in_argv inp) [] <> [] ->
    (length (nth i (in_argv inp) []) < State.path_max)%nat ->
    match fst (fst (Fs.resolve md (in_fs inp) (in_cwd inp) (nth i (in_argv inp) []))) with
    | Fs.ROutside => False
    | _ => True
    end.

(** The hypothesis admits a valid input, so the statement below is not
    vacuous: [EquivalenceDefinition.FinInput.inhabited_fin_input]'s
    launch, whose argv is argv[0] alone, so neither binary opens
    anything. *)
Lemma operands_inside_model_witness :
  exists inp, valid_input inp /\ operands_inside_model inp.
Proof.
  exists (FinInput.to_proc_input FinInput.inhabited_fin_input).
  split; [exact FinInput.inhabited_fin_input_valid|].
  intros H3. change (3 <= 1)%nat in H3. lia.
Qed.

(** THE HYPOTHESIS IS EXACTLY THE MODEL'S ANSWER.  At any model whose
    image and working folder are the input's -- the model each open of
    the run is made in, since no step before the second open changes
    either -- the hypothesis holds if and only if the open of each
    operand the binaries make, with the flag word they pass (O_RDONLY
    is 0, O_WRONLY|O_CREAT|O_TRUNC is 577), has no [Unmodeled] outcome
    once the pathname reaches the walk ([openat_resolved_spec]). *)
Lemma operands_inside_model_iff : forall inp m si,
  valid_argv (in_argv inp) -> m_fs m = in_fs inp -> m_cwd m = in_cwd inp ->
  operands_inside_model inp <->
  ((3 <= length (in_argv inp))%nat ->
   forall (i : nat) (fl : word),
     (i = 1%nat /\ fl = Z_to_bv 64 0 \/ i = 2%nat /\ fl = Z_to_bv 64 577) ->
     nth i (in_argv inp) [] <> [] ->
     (length (nth i (in_argv inp) []) < State.path_max)%nat ->
     ~ openat_resolved_spec (nth i (in_argv inp) []) fl m si m Unmodeled).
Proof.
  intros inp m si Hva Hfs Hcwd. unfold operands_inside_model. split.
  - intros H H3 i fl Hi Hne Hlen.
    destruct Hi as [[-> ->] | [-> ->]].
    + apply (proj2 (openat_operand_answers_iff _ _ (Fs.WalkFull true false) m si
               (valid_argv_no_slash _ 0%nat Hva ltac:(lia))
               (or_introl (conj eq_refl eq_refl)))).
      rewrite Hfs, Hcwd.
      exact (H H3 1%nat _ (or_introl (conj eq_refl eq_refl)) Hne Hlen).
    + apply (proj2 (openat_operand_answers_iff _ _ (Fs.WalkCreate true) m si
               (valid_argv_no_slash _ 1%nat Hva ltac:(lia))
               (or_intror (conj eq_refl eq_refl)))).
      rewrite Hfs, Hcwd.
      exact (H H3 2%nat _ (or_intror (conj eq_refl eq_refl)) Hne Hlen).
  - intros H H3 i md Hi Hne Hlen.
    destruct Hi as [[-> ->] | [-> ->]].
    + pose proof (proj1 (openat_operand_answers_iff _ _ (Fs.WalkFull true false) m si
                    (valid_argv_no_slash _ 0%nat Hva ltac:(lia))
                    (or_introl (conj eq_refl eq_refl)))
                  (H H3 1%nat _ (or_introl (conj eq_refl eq_refl)) Hne Hlen)) as Ha.
      rewrite Hfs, Hcwd in Ha. exact Ha.
    + pose proof (proj1 (openat_operand_answers_iff _ _ (Fs.WalkCreate true) m si
                    (valid_argv_no_slash _ 1%nat Hva ltac:(lia))
                    (or_intror (conj eq_refl eq_refl)))
                  (H H3 2%nat _ (or_intror (conj eq_refl eq_refl)) Hne Hlen)) as Ha.
      rewrite Hfs, Hcwd in Ha. exact Ha.
Qed.

Theorem omni_strong_universal_operands_inside : forall en_source en_target inp,
  valid_entry (mkImage SourceMemImage.Source.loaded_segments
                 SourceMemImage.Source.init_pc SourceMemImage.Source.phdrs) en_source inp ->
  valid_entry (mkImage TargetMemImage.Target.loaded_segments
                 TargetMemImage.Target.init_pc TargetMemImage.Target.phdrs) en_target inp ->
  valid_input inp ->
  operands_inside_model inp ->
  omni_strong_equiv
    (mkImage SourceMemImage.Source.loaded_segments
             SourceMemImage.Source.init_pc SourceMemImage.Source.phdrs)
    (mkImage TargetMemImage.Target.loaded_segments
             TargetMemImage.Target.init_pc TargetMemImage.Target.phdrs)
    en_source en_target inp.
Proof.
  intros [sp_source brk_source mb_source rnd_source] [sp_target brk_target mb_target rnd_target]
    inp Hens Hent Hvalid Hinside.
  (* the input declares Sv48 ([Run.valid_input] pins it), so the entry
     predicate is the literal Sv48 one ([Run.valid_entry_sv48]) *)
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  (* The FIFTH conjunct of each entry predicate is [Run.entry_launch_ok_va]
     ([create_elf_tables] and [setup_arg_pages], fs/binfmt_elf.c and
     fs/exec.c, Linux v6.18.46, commit 1f99e9ab748f). *)
  destruct Hens as (Hspr & _ & _ & _ & Hlau_source).
  destruct Hent as (Hspa & _ & _ & _ & Hlau_target).
  pose proof (valid_input_argv _ Hvalid) as Hva.
  pose proof (valid_input_launch _ Hvalid) as Hvl.
  (* [Run.valid_urandom]: the declared random stream is endless *)
  assert (Hur : stream_infinite (in_urandom inp)).
  { destruct Hvalid as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hu & _). exact Hu. }
  destruct Hspr as (Hr_lo & Hr_hi & _).
  destruct Hspa as (Ha_lo & Ha_hi & _).
  (* the vDSO pair each run appends ([Run.run_segments]) *)
  set (vS := vdso_segments (in_kernel inp) sp_source mb_source).
  set (vT := vdso_segments (in_kernel inp) sp_target mb_target).
  unfold SourceMemImage.Source.init_pc, TargetMemImage.Target.init_pc.
  rewrite source_init_pc_val, target_init_pc_val.
  destruct (le_lt_dec 3 (length (in_argv inp))) as [Hge3 | Hlt3].
  - (* argc >= 3 : the hypothesis makes each operand's open one the
       model answers *)
    assert (Hans : forall (rd : bool) (i : nat),
               (i = 1%nat /\ rd = true \/ i = 2%nat /\ rd = false) ->
               op_walked (nth i (in_argv inp) []) = true ->
               open_answered rd (in_fs inp) (in_cwd inp) (nth i (in_argv inp) [])).
    { intros rd i Hi Hw. apply open_answered_of_inside.
      destruct (op_walked_true _ Hw) as [Hne Hlen].
      destruct Hi as [[-> ->] | [-> ->]].
      - exact (Hinside Hge3 1%nat _ (or_introl (conj eq_refl eq_refl)) Hne Hlen).
      - exact (Hinside Hge3 2%nat _ (or_intror (conj eq_refl eq_refl)) Hne Hlen). }
    eapply fout_omni_strong_equiv.
    + apply (source_ge3 vS inp Hva Hvl sp_source brk_source mb_source rnd_source
               Hr_lo Hr_hi Hlau_source Hge3).
      all: first [ reflexivity | exact Hur
                 | exact (Hans true 1%nat (or_introl (conj eq_refl eq_refl)))
                 | exact (Hans false 2%nat (or_intror (conj eq_refl eq_refl))) ].
    + apply (target_ge3 vT inp Hva Hvl sp_target brk_target mb_target rnd_target
               Ha_lo Ha_hi Hlau_target Hge3).
      all: first [ reflexivity | exact Hur
                 | exact (Hans true 1%nat (or_introl (conj eq_refl eq_refl)))
                 | exact (Hans false 2%nat (or_intror (conj eq_refl eq_refl))) ].
  - (* argc < 3 : exit 2, no file I/O *)
    eapply cat_omni_strong_equiv_te.
    + apply (source_wexit_lt3 vS inp Hva Hvl sp_source brk_source mb_source rnd_source
               Hr_lo Hr_hi Hlau_source Hlt3).
    + apply (target_wexit_lt3 vT inp Hva Hvl sp_target brk_target mb_target rnd_target
               Ha_lo Ha_hi Hlau_target Hlt3).
    + unfold bufs_modeled. apply Forall_nil.
    + (* no write, so the run is the same whatever the reader *)
      left. left. reflexivity.
Qed.

(** The statement [Checker.v] pins to [Equivalence.SPEC_ON] under
    [operands_inside_model], through the compat [iff]. *)
Theorem strong_universal_operands_inside :
  strong_universal_T_on operands_inside_model
    (mkImage SourceMemImage.Source.loaded_segments
             SourceMemImage.Source.init_pc SourceMemImage.Source.phdrs)
    (mkImage TargetMemImage.Target.loaded_segments
             TargetMemImage.Target.init_pc TargetMemImage.Target.phdrs).
Proof.
  intros en_source en_target inp Hs Ht Hv Hh.
  apply (proj2 (strong_equiv_iff _ _ en_source en_target inp)).
  exact (omni_strong_universal_operands_inside en_source en_target inp Hs Ht Hv Hh).
Qed.

