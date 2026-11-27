(** * Equivalence proof for brk-rev — top-level glue

    PROOF-SIDE FILE (not part of the trusted specification).  Discharges
    [strong_universal]: observable trace equivalence between the source
    image (Source) and the target image (Target) for all valid stack
    pointers and every valid process input (one [State.ProcInput]
    record: argv, envp, file system, stdin, the credentials, the kernel
    build and the exec file name).

    With [s = argv[1]], [n = strlen(s)] the shared observable behavior:

      - argc < 2               : no output, exit 2      (deterministic)
      - argc >= 2, n > 65536   : no output, exit 3      (deterministic)
      - argc >= 2, n <= 65536  : the outcome SET
          { ([], 4) } ∪ { ([rev s ++ '\n'], 0) }
        (brk nondeterminism: any failing resolution of the two brk
        calls exits 4 silently; any succeeding resolution writes the
        reversed string plus newline and exits 0).

    The glue goes through Common.ShapeAlg: each branch names ONE shape
    (a prefix-closed trace set), exhibits a [realizes] derivation for the
    source and for the target at that same shape, and closes the goal
    with the single master theorem [shape_strong_equiv].  The per-binary
    witnesses are unchanged; the library bridges [wall_realizes] and
    [outcomes_realizes] carry them into [realizes].

    Both binaries allocate with brk, so the interesting branch is TWO
    [AllocSim.to_outcomes] derivations over the same outcome set
    [brkU (rev_buf argv[1])] — and [t_outcomes_two_alt2] identifies that
    set's trace denotation with the very same

      [t_alt2 (t_writes [] (t_exit 4 fs0))
              (t_writes [rev_buf argv[1]] (t_exit 0 fs0))]

    an mmap-allocating target would land on, so no allocator-pair-specific
    glue lemma (the old [AllocSim.alloc_strong_equiv]) is involved.

    Exit codes are [Z_to_bv 64 c] words, and the strlen cap
    case split is in [Z] over [Z.of_nat (length argv[1])].

    Each run reads [Run.run_segments] and starts from the model
    [Run.init_config] builds (the vDSO counter, and the vDSO pair in the
    brk ledger).  The derivations take the entry predicate's launch
    conjunct [Run.entry_launch_ok_va] and [Run.valid_launch]; the outcome
    derivations also take [Run.valid_mmap_base]'s floor (it keeps the
    vDSO pair far above the heap), and every leaf takes [Run.valid_input]'s
    reader on fd 1. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec AllocSim AllocSim2 ShapeAlg.
From LinuxProcessSemantics.Common Require WallSim.
From LinuxProcessSemantics.Examples.brk_rev_ns Require Import brk_rev_ns_defs brk_rev_ns_code brk_rev_ns_source brk_rev_ns_target.
From LinuxProcessSemantics.Examples.brk_rev_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.brk_rev_ns Require Import TargetMemImage.

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
  pose proof (valid_input_launch _ Hvalid) as Hvl.
  pose proof (valid_input_channel_reader _ Hvalid) as Hrd.
  set (argv := in_argv inp) in *; set (fs0 := in_fs inp) in *.
  destruct Hspr as (Hr_lo & Hr_hi & _).
  destruct Hspa as (Ha_lo & Ha_hi & _).
  destruct Hbr as (Hbr_lo & Hbr_hi & Hbr_mod).
  destruct Hba as (Hba_lo & Hba_hi & Hba_mod).
  destruct Hmbr as (Hmb_s & _). destruct Hmba as (Hmb_t & _).
  (* fd 1 is the stdout channel and has a reader in each run's initial
     model ([State.with_vdso] keeps the descriptor table) *)
  assert (HfdS : fd1chan (with_vdso (Vdso.vdso_run_init (ed_vdso rnd_source))
                   (init_model (segments_reserved (run_segments source_segs inp sp_source mb_source))
                      brk_source mb_source sp_source source_alloc_limit inp)))
    by (split; [reflexivity | exact Hrd]).
  assert (HfdT : fd1chan (with_vdso (Vdso.vdso_run_init (ed_vdso rnd_target))
                   (init_model (segments_reserved (run_segments target_segs inp sp_target mb_target))
                      brk_target mb_target sp_target target_alloc_limit inp)))
    by (split; [reflexivity | exact Hrd]).
  destruct (le_lt_dec 2 (length argv)) as [Hge2 | Hlt2].
  - (* 2 <= argc : split on the length cap *)
    destruct (Z.leb_spec (Z.of_nat (length (nth 1 argv []))) 65536)
      as [Hle | Hgt].
    + (* n <= 65536 : the shared two-element outcome set *)
      apply (shape_omni_strong_equiv
               source_segs SourceMemImage_init_pc SourceMemImage_phdrs sp_source brk_source mb_source rnd_source
               target_segs TargetMemImage_init_pc TargetMemImage_phdrs sp_target brk_target mb_target rnd_target
               (t_alt2 (t_writes [] (t_exit (Z_to_bv 64 4) fs0))
                       (t_writes [rev_buf (nth 1 argv [])] (t_exit (Z_to_bv 64 0) fs0)))
               inp).
      * unfold init_config.
        eapply rz_conseq; [apply outcomes_realizes; [| reflexivity | reflexivity] |
                           apply t_outcomes_two_alt2].
        rewrite source_init_pc_val.
        eapply source_outcomes; eassumption.
      * unfold init_config.
        eapply rz_conseq; [apply outcomes_realizes; [| reflexivity | reflexivity] |
                           apply t_outcomes_two_alt2].
        rewrite target_init_pc_val.
        eapply target_outcomes; eassumption.
    + (* n > 65536 : no output, exit 3 *)
      apply (shape_omni_strong_equiv
               source_segs SourceMemImage_init_pc SourceMemImage_phdrs sp_source brk_source mb_source rnd_source
               target_segs TargetMemImage_init_pc TargetMemImage_phdrs sp_target brk_target mb_target rnd_target
               (t_writes [] (t_exit (Z_to_bv 64 3) fs0)) inp).
      * unfold init_config. apply wall_realizes;
          [reflexivity | reflexivity | exact HfdS | | apply Forall_nil].
        rewrite source_init_pc_val. cbn [WallSim.to_wallexit].
        eapply source_wexit_cap; eassumption.
      * unfold init_config. apply wall_realizes;
          [reflexivity | reflexivity | exact HfdT | | apply Forall_nil].
        rewrite target_init_pc_val. cbn [WallSim.to_wallexit].
        eapply target_wexit_cap; eassumption.
  - (* argc < 2 : no output, exit 2 *)
    apply (shape_omni_strong_equiv
             source_segs SourceMemImage_init_pc SourceMemImage_phdrs sp_source brk_source mb_source rnd_source
             target_segs TargetMemImage_init_pc TargetMemImage_phdrs sp_target brk_target mb_target rnd_target
             (t_writes [] (t_exit (Z_to_bv 64 2) fs0)) inp).
    + unfold init_config. apply wall_realizes;
        [reflexivity | reflexivity | exact HfdS | | apply Forall_nil].
      rewrite source_init_pc_val. cbn [WallSim.to_wallexit].
      eapply source_wexit_lt2; eassumption.
    + unfold init_config. apply wall_realizes;
        [reflexivity | reflexivity | exact HfdT | | apply Forall_nil].
      rewrite target_init_pc_val. cbn [WallSim.to_wallexit].
      eapply target_wexit_lt2; eassumption.
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

