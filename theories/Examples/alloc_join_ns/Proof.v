(** * Equivalence proof for alloc-join — top-level glue

    PROOF-SIDE FILE (not part of the trusted specification).  Discharges
    [strong_universal]: observable trace equivalence between the source
    image (Source, brk allocator) and the target image (Target, mmap
    allocator) for all valid stack pointers and every valid process
    input (one [State.ProcInput] record: argv, envp, file system,
    stdin).

    With [tot = |join1(argv[1..])| + 1] the shared observable behavior:

      - argc < 2               : no output, exit 2      (deterministic)
      - argc >= 2, tot > 65536 : no output, exit 3      (deterministic)
      - argc >= 2, tot <= 65536: the outcome SET
          { ([], 4) } ∪ { ([join1(argv[1..]) ++ '\n'], 0) }
        — the source reaches it through the two brk resolutions, the
        target through the two mmap resolution families; allocation
        emits no events, so the sets coincide.

    The glue goes through Common.ShapeAlg: each branch names ONE shape
    (a prefix-closed trace set), exhibits a [realizes] derivation for the
    source and for the target at that same shape, and closes the goal with
    the single master theorem [shape_strong_equiv].  The per-binary
    witnesses are unchanged; the library bridges [wall_realizes],
    [outcomes_realizes] and [tmw_realizes] carry them into [realizes].

    The allocation branch is where this earns its keep: the source is a
    brk-branching [AllocSim.to_outcomes] set and the target a
    [MmapSim.tmw] derivation, but both land on the SAME shape

      [t_alt2 (t_writes [] (t_exit 4 fs0)) (t_writes [jout argv] (t_exit 0 fs0))]

    ([t_outcomes_two_alt2] is the one rewrite that identifies them), so
    no allocator-pair-specific glue lemma is involved.

    Exit codes are [Z_to_bv 64 c] words; the total-size cap case split
    is in [Z] over [bv_unsigned (tot inp)]. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec AllocSim MmapSim AllocSim2 ShapeAlg RunSegmentsLift.
From LinuxProcessSemantics.Examples.alloc_join_ns Require Import alloc_join_ns_defs alloc_join_ns_code alloc_join_ns_source alloc_join_ns_target.
From LinuxProcessSemantics.Examples.alloc_join_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.alloc_join_ns Require Import TargetMemImage.

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
  destruct Hent as (Hspa & _ & Hmba & _ & Hlau_target).
  pose proof (valid_input_argv _ Hvalid) as Hva.
  pose proof (valid_input_envp _ Hvalid) as Hve.
  pose proof (valid_input_launch _ Hvalid) as Hvl.
  pose proof (valid_input_channel_reader _ Hvalid) as Hrd.
  set (argv := in_argv inp) in *; set (fs0 := in_fs inp) in *.
  destruct Hspr as (Hr_lo & Hr_hi & _).
  destruct Hspa as (Ha_lo & Ha_hi & _).
  destruct Hbr as (Hbr_lo & Hbr_hi & Hbr_mod).
  destruct Hmbr as (Hmb_s & _). destruct Hmba as (Hmb_t & _).
  (* the target run's reservations are the image's: the vDSO pair
     reserves nothing ([RunSegmentsLift.segments_reserved_vdso]); the
     image's list is concrete, so the split is by computation *)
  assert (HresT : segments_reserved (run_segments target_segs inp sp_target mb_target)
                  = segments_reserved target_segs).
  { replace (segments_reserved (run_segments target_segs inp sp_target mb_target))
      with (segments_reserved target_segs
            ++ segments_reserved (vdso_segments (in_kernel inp) sp_target mb_target))
      by reflexivity.
    rewrite segments_reserved_vdso, app_nil_r. reflexivity. }
  (* fd 1 is the stdout channel and has a reader in each run's initial
     model ([State.with_vdso] keeps the descriptor table) *)
  assert (Hfd : forall v reserved brk0 mb sp lim,
             fd1chan (with_vdso v (init_model reserved brk0 mb sp lim inp)))
    by (intros; split; [reflexivity | exact Hrd]).
  destruct (le_lt_dec 2 (length argv)) as [Hge2 | Hlt2].
  - (* 2 <= argc : split on the total-size cap *)
    destruct (Z.leb_spec (bv_unsigned (tot inp)) 65536) as [Hle | Hgt].
    + (* tot <= 65536 : the shared two-element outcome set *)
      apply (shape_omni_strong_equiv
               source_segs SourceMemImage_init_pc SourceMemImage_phdrs sp_source brk_source mb_source rnd_source
               target_segs TargetMemImage_init_pc TargetMemImage_phdrs sp_target brk_target mb_target rnd_target
               (t_alt2 (t_writes [] (t_exit (Z_to_bv 64 4) fs0))
                       (t_writes [jout argv] (t_exit (Z_to_bv 64 0) fs0)))
               inp).
      * unfold init_config.
        eapply rz_conseq; [apply outcomes_realizes; [| reflexivity | reflexivity] |
                           apply t_outcomes_two_alt2].
        rewrite source_init_pc_val.
        eapply source_outcomes; eassumption.
      * unfold init_config. rewrite HresT. apply tmw_realizes;
          [reflexivity | reflexivity | apply Hfd | | apply Forall_nil
           | apply jout_modeled; assumption].
        rewrite target_init_pc_val.
        apply (tmw_app target_segs _ (vdso_segments_no_exec _ _ _)).
        eapply target_tmw; eassumption.
    + (* tot > 65536 : no output, exit 3 *)
      apply (shape_omni_strong_equiv
               source_segs SourceMemImage_init_pc SourceMemImage_phdrs sp_source brk_source mb_source rnd_source
               target_segs TargetMemImage_init_pc TargetMemImage_phdrs sp_target brk_target mb_target rnd_target
               (t_writes [] (t_exit (Z_to_bv 64 3) fs0)) inp).
      * unfold init_config. apply wall_realizes;
          [reflexivity | reflexivity | apply Hfd | | apply Forall_nil].
        rewrite source_init_pc_val. cbn [WallSim.to_wallexit].
        apply to_wexit_run. eapply source_wexit_cap; eassumption.
      * unfold init_config. apply wall_realizes;
          [reflexivity | reflexivity | apply Hfd | | apply Forall_nil].
        rewrite target_init_pc_val. cbn [WallSim.to_wallexit].
        apply to_wexit_run. eapply target_wexit_cap; eassumption.
  - (* argc < 2 : no output, exit 2 *)
    apply (shape_omni_strong_equiv
             source_segs SourceMemImage_init_pc SourceMemImage_phdrs sp_source brk_source mb_source rnd_source
             target_segs TargetMemImage_init_pc TargetMemImage_phdrs sp_target brk_target mb_target rnd_target
             (t_writes [] (t_exit (Z_to_bv 64 2) fs0)) inp).
    + unfold init_config. apply wall_realizes;
        [reflexivity | reflexivity | apply Hfd | | apply Forall_nil].
      rewrite source_init_pc_val. cbn [WallSim.to_wallexit].
      apply to_wexit_run. eapply source_wexit_lt2; eassumption.
    + unfold init_config. apply wall_realizes;
        [reflexivity | reflexivity | apply Hfd | | apply Forall_nil].
      rewrite target_init_pc_val. cbn [WallSim.to_wallexit].
      apply to_wexit_run. eapply target_wexit_lt2; eassumption.
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

