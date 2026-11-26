(** * Equivalence proof for arena-tee-ns — top-level glue

    PROOF-SIDE FILE (not part of the trusted specification).  Discharges
    [strong_universal]: observable trace equivalence between the source
    image (Source) and the target image (Target) for all valid stack
    pointers and every valid process input (one [State.ProcInput]
    record: argv, envp, file system, stdin).

    Both binaries drain stdin into a 4088-byte anonymous [mmap] arena
    and then write, ON CHANNEL 2, eight lowercase hex digits holding the
    drained byte count followed by the drained bytes; a failed [mmap]
    exits 1 with no output.  There is exactly ONE shape — the two-element
    outcome set [arena_tee_ns_defs.arena_outcomes], whose success branch
    is [DrainAlg.t_drain] — and both binaries are shown to realize it,
    so the single master theorem [ShapeAlg.shape_strong_equiv] closes the
    goal.

    The two binaries chunk stdin completely differently (the source asks
    the kernel for [cap - n] through musl's [read] wrapper, the target
    through a raw [ecall], and neither proof constrains the kernel's
    answer), and the chunking is nevertheless invisible: a [read] emits
    one [ReadEv] per byte, so [DrainAlg.t_drain_collapse] — packaged for
    this example as [arena_tee_ns_defs.arena_outcomes_spec] — turns the
    whole nondeterministic loop into ONE deterministic block of read
    events followed by a tail that is a function of the input stream.

    The initial stack pointers are QUANTIFIED (ASLR): [strong_universal_T]
    supplies independent [sp_source]/[sp_target] anywhere in the valid
    window, and the per-binary lemmas are generic over any
    window-bounded sp.  The initial break is quantified too and never
    used: neither binary calls [brk]. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec MmapSim ShapeAlg DrainAlg.
From LinuxProcessSemantics.Examples.arena_tee_ns Require Import arena_tee_ns_defs arena_tee_ns_code arena_tee_ns_source arena_tee_ns_target.
From LinuxProcessSemantics.Examples.arena_tee_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.arena_tee_ns Require Import TargetMemImage.

Import ListNotations.
Open Scope bv_scope.

Theorem omni_strong_universal :
  omni_strong_universal_T
    (mkImage SourceMemImage.Source.loaded_segments
             SourceMemImage.Source.init_pc SourceMemImage.Source.phdrs)
    (mkImage TargetMemImage.Target.loaded_segments
             TargetMemImage.Target.init_pc TargetMemImage.Target.phdrs).
Proof.
  intros [sp_source brk_source mb_source rnd_source] [sp_target brk_target mb_target rnd_target] inp Hens Hent Hvalid.
  (* the input declares Sv48 ([Run.valid_input] pins it), so the entry
     predicate is the literal Sv48 one ([Run.valid_entry_sv48]) *)
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  (* The FIFTH conjunct of each entry predicate is [Run.entry_launch_ok_va]
     ([create_elf_tables] and [setup_arg_pages], fs/binfmt_elf.c and
     fs/exec.c, Linux v6.18.46, commit 1f99e9ab748f). *)
  destruct Hens as (Hspr & _ & Hmbr & _ & Hlau_source).
  destruct Hent as (Hspa & _ & Hmba & _ & Hlau_target).
  pose proof (valid_input_argv _ Hvalid) as Hva.
  pose proof (valid_input_envp _ Hvalid) as Hve.
  pose proof (valid_input_launch _ Hvalid) as Hvl.
  pose proof (valid_input_channel_reader _ Hvalid) as Hrd.
  destruct Hspr as (Hr_lo & Hr_hi & _).
  destruct Hspa as (Ha_lo & Ha_hi & _).
  destruct Hmbr as (Hmb_s & _). destruct Hmba as (Hmb_t & _).
  apply (shape_omni_strong_equiv
           source_segs SourceMemImage_init_pc SourceMemImage_phdrs
           sp_source brk_source mb_source rnd_source
           target_segs TargetMemImage_init_pc TargetMemImage_phdrs
           sp_target brk_target mb_target rnd_target
           (arena_outcomes (in_fs inp) (in_stdin inp)) inp).
  - eapply source_realizes; eassumption.
  - eapply target_realizes; eassumption.
Qed.

(** The legacy statement, through the compat [iff]; this is the theorem
    [Checker.v] pins to [Equivalence.SPEC]. *)
Theorem strong_universal :
  strong_universal_T
    (mkImage SourceMemImage.Source.loaded_segments
             SourceMemImage.Source.init_pc SourceMemImage.Source.phdrs)
    (mkImage TargetMemImage.Target.loaded_segments
             TargetMemImage.Target.init_pc TargetMemImage.Target.phdrs).
Proof. apply strong_universal_iff. exact omni_strong_universal. Qed.

