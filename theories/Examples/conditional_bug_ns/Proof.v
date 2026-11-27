(** * Equivalence proof for conditional-bug-ns — top-level glue.

    PROOF-SIDE FILE (not part of the trusted specification).  Discharges
    [strong_universal_T]: observable trace equivalence between the source
    image (Source) and the target image (Target) for all valid stack
    pointers and every valid process input (one [State.ProcInput]
    record: argv, envp, file system, stdin, the credentials, the kernel
    build and the exec file name).

    Both binaries dispatch on the FIRST byte of argv[1]:

      - argc < 2                    : no output,   exit 2
      - first byte 'n' (110)        : no output,   exit 0
      - first byte 'h' (104)        : "hello\n",   exit 0
      - first byte 'o' (111)        : INTENTIONAL BUG — a volatile load
        from unmapped address 64.  The SOURCE reaches the explicit error
        transition on every execution, so [Equivalence.equiv]'s universal
        SOURCE-ERROR ESCAPE applies:
        the target's behavior on these inputs is irrelevant and is not
        analyzed ([Common.ErrEscape.err_escape_strong_equiv], which also
        discharges [Equivalence.modeled]: the load faults, and a fault is
        modeled).
      - any other first byte        : no output,   exit 3

    On the four defined arms the per-binary derivations agree on the
    exact [(bufs, code)] pair and are glued with [cat_strong_equiv_te]
    (no-output arms) and [WallSim.wall_strong_equiv] (the 'h' arm: both
    binaries realize the write through a put-style retry loop, so the
    trace set is the full-delivery form).  The initial stack pointers are QUANTIFIED
    (ASLR): [strong_universal_T] supplies independent
    [sp_source]/[sp_target] anywhere in the valid window.

    Every derivation runs over the run's segment list
    ([Run.run_segments]) and takes the entry predicate's launch conjunct
    [Run.entry_launch_ok_va] and [Run.valid_launch]; the no-output arms
    are covered whatever the reader on fd 1 ([CatSim.cat_launch]'s first
    case), and the 'h' arm takes [Run.valid_input]'s reader. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec WallSim ErrEscape.
From LinuxProcessSemantics.Examples.conditional_bug_ns Require Import conditional_bug_ns_defs conditional_bug_ns_code conditional_bug_ns_source conditional_bug_ns_target.
From LinuxProcessSemantics.Examples.conditional_bug_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.conditional_bug_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

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
  destruct Hens as (Hspr & _ & _ & _ & Hls).
  destruct Hent as (Hspa & _ & _ & _ & Hlt).
  pose proof (valid_input_argv _ Hvalid) as Hva.
  pose proof (valid_input_launch _ Hvalid) as Hvl.
  pose proof (valid_input_channel_reader _ Hvalid) as Hrdr.
  set (argv := in_argv inp) in *.
  destruct Hspr as (Hr_lo & Hr_hi & _).
  destruct Hspa as (Ha_lo & Ha_hi & _).
  destruct (le_lt_dec 2 (length argv)) as [Hge2 | Hlt2].
  - (* 2 <= argc: dispatch on the first byte of argv[1] *)
    destruct (decide (byte_at (nth 1 argv []) 0 = Z_to_bv 8 111)) as [Ho | Hn111].
    + (* 'o': every source execution faults -> the target is freed *)
      destruct (source_err_o inp Hva Hvl sp_source brk_source mb_source rnd_source
                  Hr_lo Hr_hi Hls Hge2 Ho)
        as (ms' & Hm & Hsvc & Hill).
      apply (err_escape_omni_strong_equiv source_segs SourceMemImage_init_pc SourceMemImage_phdrs sp_source brk_source mb_source rnd_source
               inp _ _ ms');
        [ rewrite source_init_pc_val; exact Hm | exact Hsvc | exact Hill ].
    + destruct (decide (byte_at (nth 1 argv []) 0 = Z_to_bv 8 110)) as [Hn | Hn110].
      * (* 'n': no output, exit 0 *)
        apply (cat_omni_strong_equiv_te
                 source_segs SourceMemImage_init_pc SourceMemImage_phdrs sp_source brk_source mb_source rnd_source
                 target_segs TargetMemImage_init_pc TargetMemImage_phdrs sp_target brk_target mb_target rnd_target
                 [] (Z_to_bv 64 0) inp).
        -- rewrite source_init_pc_val.
           apply (source_wexit_n inp Hva Hvl sp_source brk_source mb_source rnd_source);
             assumption.
        -- rewrite target_init_pc_val.
           apply (target_wexit_n inp Hva Hvl sp_target brk_target mb_target rnd_target);
             assumption.
        -- exact nil_bufs_modeled.
        -- (* no write, so the run is the same whatever the reader *)
           left. left. reflexivity.
      * destruct (decide (byte_at (nth 1 argv []) 0 = Z_to_bv 8 104)) as [Hh | Hn104].
        -- (* 'h': "hello\n", exit 0 *)
           apply (wall_omni_strong_equiv
                    source_segs SourceMemImage_init_pc SourceMemImage_phdrs sp_source brk_source mb_source rnd_source
                    target_segs TargetMemImage_init_pc TargetMemImage_phdrs sp_target brk_target mb_target rnd_target
                    [hello] (Z_to_bv 64 0) inp).
           ++ rewrite source_init_pc_val.
              apply (source_wexit_h inp Hva Hvl sp_source brk_source mb_source rnd_source);
                assumption.
           ++ rewrite target_init_pc_val.
              apply (target_wexit_h inp Hva Hvl sp_target brk_target mb_target rnd_target);
                assumption.
           ++ exact hello_bufs_modeled.
           ++ (* [Run.valid_input] pins a reader on fd 1 *)
              exact Hrdr.
        -- (* anything else: no output, exit 3 *)
           apply (cat_omni_strong_equiv_te
                    source_segs SourceMemImage_init_pc SourceMemImage_phdrs sp_source brk_source mb_source rnd_source
                    target_segs TargetMemImage_init_pc TargetMemImage_phdrs sp_target brk_target mb_target rnd_target
                    [] (Z_to_bv 64 3) inp).
           ++ rewrite source_init_pc_val.
              apply (source_wexit_other inp Hva Hvl sp_source brk_source mb_source rnd_source);
                assumption.
           ++ rewrite target_init_pc_val.
              apply (target_wexit_other inp Hva Hvl sp_target brk_target mb_target rnd_target);
                assumption.
           ++ exact nil_bufs_modeled.
           ++ left. left. reflexivity.
  - (* argc < 2: no output, exit 2 *)
    apply (cat_omni_strong_equiv_te
             source_segs SourceMemImage_init_pc SourceMemImage_phdrs sp_source brk_source mb_source rnd_source
             target_segs TargetMemImage_init_pc TargetMemImage_phdrs sp_target brk_target mb_target rnd_target
             [] (Z_to_bv 64 2) inp).
    + rewrite source_init_pc_val.
      apply (source_wexit_lt2 inp Hva Hvl sp_source brk_source mb_source rnd_source);
        assumption.
    + rewrite target_init_pc_val.
      apply (target_wexit_lt2 inp Hva Hvl sp_target brk_target mb_target rnd_target);
        assumption.
    + exact nil_bufs_modeled.
    + left. left. reflexivity.
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

