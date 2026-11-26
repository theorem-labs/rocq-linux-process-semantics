(** * Equivalence proof for oob-read-bug-ns — top-level glue

    PROOF-SIDE FILE (not part of the trusted specification).  Discharges
    [strong_universal]: observable trace equivalence between the source
    image (Source) and the target image (Target) for all valid stack
    pointers, break bases and every valid process input (one
    [State.ProcInput] record: argv, envp, file system, stdin).

    With [s = argv[1]], [n = strlen(s)] the shared observable behavior:

      - argc < 2               : no output, exit 2      (deterministic)
      - argc >= 2, n > 65536   : no output, exit 3      (deterministic)
      - argc >= 2, n <= 65536   : the brk outcome SET
          { ([], 4) } ∪ { (outbufs s, 0) }
        (brk nondeterminism on the two brk calls).  The chunk loop may
        read through the end of the logical byte allocation, but the
        page-rounded brk grant supplies zero padding, so every length
        has the same byte sum and observable outcomes.

    Exit codes are [Z_to_bv 64 c] words; the length-cap
    case split is in [Z] over [length (nth 1 argv [])]. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec AllocSim RunSegmentsLift.
From LinuxProcessSemantics.Examples.oob_read_bug_ns Require Import oob_read_bug_ns_defs oob_read_bug_ns_code oob_read_bug_ns_source oob_read_bug_ns_target oob_read_bug_ns_target_outcomes.
From LinuxProcessSemantics.Examples.oob_read_bug_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.oob_read_bug_ns Require Import TargetMemImage.

Import ListNotations.
Open Scope bv_scope.

Theorem omni_strong_universal :
  omni_strong_universal_T
    (mkImage SourceMemImage.Source.loaded_segments
             SourceMemImage.Source.init_pc SourceMemImage.Source.phdrs)
    (mkImage TargetMemImage.Target.loaded_segments
             TargetMemImage.Target.init_pc TargetMemImage.Target.phdrs).
Proof.
  intros [sp_source brk_source mb_source rnd_source] [sp_target brk_target mb_target rnd_target]
    inp Hens Hent Hvalid.
  (* the input declares Sv48 ([Run.valid_input] pins it), so the entry
     predicate is the literal Sv48 one ([Run.valid_entry_sv48]) *)
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  (* The FIFTH conjunct of each entry predicate is [Run.entry_launch_ok_va]
     ([create_elf_tables] and [setup_arg_pages], fs/binfmt_elf.c and
     fs/exec.c, Linux v6.18.46, commit 1f99e9ab748f). *)
  destruct Hens as (Hspr & Hbr & Hmbr & _ & Hlau_source).
  destruct Hent as (Hspa & Hba & Hmba & _ & Hlau_target).
  pose proof (valid_input_argv _ Hvalid) as Hva.
  pose proof (valid_input_envp _ Hvalid) as Hve.
  pose proof (valid_input_launch _ Hvalid) as Hvl.
  pose proof (valid_input_channel_reader _ Hvalid) as Hrd.
  set (argv := in_argv inp) in *.
  destruct Hspr as (Hr_lo & Hr_hi & _).
  destruct Hspa as (Ha_lo & Ha_hi & _).
  destruct Hbr as (Hbr_lo & Hbr_hi & Hbr_mod).
  destruct Hba as (Hba_lo & Hba_hi & Hba_mod).
  destruct Hmbr as (Hmb_s & _). destruct Hmba as (Hmb_t & _).
  unfold SourceMemImage.Source.init_pc, TargetMemImage.Target.init_pc.
  rewrite source_init_pc_val, target_init_pc_val.
  destruct (le_lt_dec 2 (length argv)) as [Hge2 | Hlt2].
  - (* 2 <= argc : split on the length cap *)
    destruct (Z.leb_spec (Z.of_nat (length (nth 1 argv []))) 65536) as [Hle | Hgt].
    + (* n <= 65536 : the shared brk outcome set *)
      apply (alloc_omni_strong_equiv
               source_segs 0x111c8 source_phdrs sp_source brk_source mb_source rnd_source
               target_segs 0x100115c target_phdrs sp_target brk_target mb_target rnd_target
               (oobU (nat_to_word (length (nth 1 argv [])))
                     (outbufs (nth 1 argv []))) inp).
      * eapply source_outcomes; eassumption.
      * eapply target_outcomes; eassumption.
    + (* n > 65536 : no output, exit 3 *)
      apply (cat_omni_strong_equiv_te
               source_segs 0x111c8 source_phdrs sp_source brk_source mb_source rnd_source
               target_segs 0x100115c target_phdrs sp_target brk_target mb_target rnd_target
               [] (Z_to_bv 64 3) inp).
      * apply to_wexit_run. eapply source_wexit_cap; eassumption.
      * apply to_wexit_run. eapply target_wexit_cap; eassumption.
      * apply Forall_nil.
      * (* no output: the reader is never asked *)
        left. left. reflexivity.
  - (* argc < 2 : no output, exit 2 *)
    apply (cat_omni_strong_equiv_te
             source_segs 0x111c8 source_phdrs sp_source brk_source mb_source rnd_source
             target_segs 0x100115c target_phdrs sp_target brk_target mb_target rnd_target
             [] (Z_to_bv 64 2) inp).
    + apply to_wexit_run. eapply source_wexit_lt2; eassumption.
    + apply to_wexit_run. eapply target_wexit_lt2; eassumption.
    + apply Forall_nil.
    + (* no output: the reader is never asked *)
      left. left. reflexivity.
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

