(** * Equivalence proof for mmap-upper — top-level glue

    PROOF-SIDE FILE (not part of the trusted specification).  Discharges
    [strong_universal]: observable trace equivalence between the source
    image (Source) and the target image (Target) for all valid stack
    pointers and every valid process input (one [State.ProcInput]
    record: argv, envp, file system, stdin).

    Both binaries implement mmap-upper.  With [s = argv[1]], [n = |s|]
    the shared observable behavior splits four ways:

      - [length argv < 2] : no output, exit 2
      - [n > 4095]        : no output, exit 3
      - mmap resolutions  : {no output, exit 4}  (any-errno failure)
                          ∪ {ONE write of [out_buf s = upper s ++ '\n'],
                             munmap, exit 0}     (any admissible grant)

    The glue goes through Common.ShapeAlg: each branch names ONE shape
    (a prefix-closed trace set), exhibits a [realizes] derivation for the
    source and for the target at that same shape, and closes the goal with
    the single master theorem [shape_strong_equiv].  The per-binary
    witnesses are unchanged — the [to_wexit] / [tmw] lemmas of
    mmap_upper_ns_source.v and _target.v are carried into [realizes] by the
    library bridges [wall_realizes] / [tmw_realizes] (a [bufs = []]
    [to_wallexit] IS a [to_wexit], so the exit-path lemmas apply as they
    stand).

    The shapes are

      - [length argv < 2] : [t_writes [] (t_exit 2 fs0)]
      - [n > 4095]        : [t_writes [] (t_exit 3 fs0)]
      - otherwise         : [t_alt2 (t_writes [] (t_exit 4 fs0))
                                    (t_writes [out_buf s] (t_exit 0 fs0))]

    the last one being the mmap branch point: both binaries carry the SAME
    failure summand and the SAME success summand, so their trace sets
    coincide resolution by resolution.

    The initial stack pointers are QUANTIFIED (ASLR): [strong_universal_T]
    supplies independent [sp_source]/[sp_target] anywhere in the valid
    window, and the per-binary lemmas are generic over any
    window-bounded sp.

    sp windows are [Z] bounds over [bv_unsigned]; the x0 seed and exit
    codes are [Z_to_bv 64] values; argv strings are [list byte]. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec MmapSim ShapeAlg RunSegmentsLift.
From LinuxProcessSemantics.Examples.mmap_upper_ns Require Import mmap_upper_ns_defs mmap_upper_ns_code mmap_upper_ns_source mmap_upper_ns_target.
From LinuxProcessSemantics.Examples.mmap_upper_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.mmap_upper_ns Require Import TargetMemImage.

Import ListNotations.
Open Scope bv_scope.

(* ######################################################################### *)
(* Every buffer this example writes is modeled                              *)
(* ######################################################################### *)

(** The failure summand and the two short-exit branches write nothing. *)
Lemma no_writes_modeled : bufs_modeled [].
Proof. apply Forall_nil. Qed.

(** The success summand writes exactly one buffer, [out_buf s].  The
    reference program exits 3 without writing when [|s| > 4095], so on the
    branch that writes, [|out_buf s| = |s| + 1 <= 4096], comfortably below
    [rw_bytes_max = 131072]. *)
Lemma out_buf_modeled : forall s : list byte,
  (length s <= 4095)%nat -> bufs_modeled [out_buf s].
Proof.
  intros s Hs. apply bufs_modeled_single.
  unfold buf_modeled. rewrite length_out_buf. unfold rw_bytes_max. lia.
Qed.

(* ######################################################################### *)
(* Glue: identical branch behavior on both sides -> strong equiv.           *)
(* ######################################################################### *)

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
  destruct Hens as (Hspr & _ & Hmbr & _ & Hlau_source).
  destruct Hent as (Hspa & _ & Hmba & _ & Hlau_target).
  pose proof (valid_input_argv _ Hvalid) as Hva.
  pose proof (valid_input_envp _ Hvalid) as Hve.
  pose proof (valid_input_launch _ Hvalid) as Hvl.
  pose proof (valid_input_channel_reader _ Hvalid) as Hrd.
  set (argv := in_argv inp) in *; set (fs0 := in_fs inp) in *.
  destruct Hspr as (Hr_lo & Hr_hi & _).
  destruct Hspa as (Ha_lo & Ha_hi & _).
  destruct Hmbr as (Hmb_s & _). destruct Hmba as (Hmb_t & _).
  (* the run's reservations are the image's: the vDSO pair reserves
     nothing ([RunSegmentsLift.segments_reserved_vdso]); the image's list
     is concrete, so the split is by computation *)
  assert (HresS : segments_reserved (run_segments source_segs inp sp_source mb_source)
                  = segments_reserved source_segs).
  { replace (segments_reserved (run_segments source_segs inp sp_source mb_source))
      with (segments_reserved source_segs
            ++ segments_reserved (vdso_segments (in_kernel inp) sp_source mb_source))
      by reflexivity.
    rewrite segments_reserved_vdso, app_nil_r. reflexivity. }
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
  (* Every branch closes with the SAME master theorem; the branch only
     chooses which shape both sides are shown to realize. *)
  destruct (le_lt_dec 2 (length argv)) as [Hge2 | Hlt2].
  - (* 2 <= length argv : split on the 4095 length cap *)
    destruct (le_lt_dec (length (nth 1 argv (@nil byte))) 4095) as [Hle | Hgt].
    + (* n <= 4095 : the mmap branch point *)
      apply (shape_omni_strong_equiv
               source_segs SourceMemImage_init_pc SourceMemImage_phdrs sp_source brk_source mb_source rnd_source
               target_segs TargetMemImage_init_pc TargetMemImage_phdrs sp_target brk_target mb_target rnd_target
               (t_alt2 (t_writes [] (t_exit (Z_to_bv 64 4) fs0))
                       (t_writes [out_buf (nth 1 argv (@nil byte))] (t_exit (Z_to_bv 64 0) fs0)))
               inp).
      * unfold init_config. rewrite HresS. apply tmw_realizes;
          [ reflexivity | reflexivity | apply Hfd
          | | apply no_writes_modeled
          | apply out_buf_modeled; exact Hle ].
        rewrite source_init_pc_val.
        apply (tmw_app source_segs _ (vdso_segments_no_exec _ _ _)).
        eapply source_tmw; eassumption.
      * unfold init_config. rewrite HresT. apply tmw_realizes;
          [ reflexivity | reflexivity | apply Hfd
          | | apply no_writes_modeled
          | apply out_buf_modeled; exact Hle ].
        rewrite target_init_pc_val.
        apply (tmw_app target_segs _ (vdso_segments_no_exec _ _ _)).
        eapply target_tmw; eassumption.
    + (* n > 4095 : no output, exit 3 *)
      apply (shape_omni_strong_equiv
               source_segs SourceMemImage_init_pc SourceMemImage_phdrs sp_source brk_source mb_source rnd_source
               target_segs TargetMemImage_init_pc TargetMemImage_phdrs sp_target brk_target mb_target rnd_target
               (t_writes [] (t_exit (Z_to_bv 64 3) fs0))
               inp).
      * unfold init_config. apply wall_realizes;
          [ reflexivity | reflexivity | apply Hfd | | apply no_writes_modeled ].
        rewrite source_init_pc_val. cbn [WallSim.to_wallexit].
        apply to_wexit_run. eapply source_wexit_len3; eassumption.
      * unfold init_config. apply wall_realizes;
          [ reflexivity | reflexivity | apply Hfd | | apply no_writes_modeled ].
        rewrite target_init_pc_val. cbn [WallSim.to_wallexit].
        apply to_wexit_run. eapply target_wexit_len3; eassumption.
  - (* length argv < 2 : no output, exit 2 *)
    apply (shape_omni_strong_equiv
             source_segs SourceMemImage_init_pc SourceMemImage_phdrs sp_source brk_source mb_source rnd_source
             target_segs TargetMemImage_init_pc TargetMemImage_phdrs sp_target brk_target mb_target rnd_target
             (t_writes [] (t_exit (Z_to_bv 64 2) fs0))
             inp).
    + unfold init_config. apply wall_realizes;
        [ reflexivity | reflexivity | apply Hfd | | apply no_writes_modeled ].
      rewrite source_init_pc_val. cbn [WallSim.to_wallexit].
      apply to_wexit_run. eapply source_wexit_lt2; eassumption.
    + unfold init_config. apply wall_realizes;
        [ reflexivity | reflexivity | apply Hfd | | apply no_writes_modeled ].
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

