(** * Equivalence proof for tail1-ns — top-level glue

    PROOF-SIDE FILE (not part of the trusted specification).  Discharges
    [strong_universal]: observable trace equivalence between the source
    image (Source) and the target image (Target) for all valid stack
    pointers and every valid process input (one [State.ProcInput]
    record: argv, envp, file system, stdin, the credentials, the kernel
    build and the exec file name).

    Both binaries implement tail-1: read all of stdin to EOF in
    1024-byte chunks, tracking the current unterminated line [cur] and
    the last completed line [done]; at EOF write the last line (cur if
    nonempty, else done, else nothing) in one write and exit 0.  A line
    exceeding 4096 bytes aborts with exit 3.  Arguments are ignored (no
    argc split).  In-model stdin reads never fail and stdout writes
    always complete, so both binaries' read/write error paths (exit 1 /
    exit 4) are dead, and the shared observable trace set is
    [drain_from (Z_to_bv 64 1024) f out ec ([], [])].

    The per-binary derivations are [src_LH_to_rd]/[src_init_to_rd]
    (tail1_ns_source) and [tgt_LH_to_rd]/[tgt_init_to_rd]
    (tail1_ns_target), glued with [DrainSim.drain_omni_strong_equiv].

    Bytes are [byte = bv 8], machine values [word = bv 64]; the exit code
    [ec] is a word with the Z-level bound [ec_lt256].

    Each binary's run reads [Run.run_segments]: the per-binary sections
    take the vDSO pair as their [vt], instantiated here; the derivations
    take the entry predicate's launch conjunct [Run.entry_launch_ok_va]
    and [Run.valid_launch]; and [drain_omni_strong_equiv] takes
    [Run.valid_input]'s reader on fd 1. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim StreamSim DrainSim.
From LinuxProcessSemantics.Examples.tail1_ns Require Import tail1_ns_code tail1_ns_defs tail1_ns_source tail1_ns_target.
From LinuxProcessSemantics.Examples.tail1_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.tail1_ns Require Import TargetMemImage.

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
  destruct Hens as (Hspr & _ & _ & _ & Hlau_source).
  destruct Hent as (Hspa & _ & _ & _ & Hlau_target).
  pose proof (valid_input_argv _ Hvalid) as Hva.
  pose proof (valid_input_launch _ Hvalid) as Hvl.
  pose proof (valid_input_channel_reader _ Hvalid) as Hrdr.
  destruct Hspr as (Hr_lo & Hr_hi & _).
  destruct Hspa as (Ha_lo & Ha_hi & _).
  (* the vDSO pair each run appends ([Run.run_segments]) *)
  set (vS := vdso_segments (in_kernel inp) sp_source mb_source).
  set (vT := vdso_segments (in_kernel inp) sp_target mb_target).
  apply (drain_omni_strong_equiv A (Z_to_bv 64 1024) f out ec a0
           source_segs (src_LH vS inp sp_source mb_source rnd_source)
           SourceMemImage_init_pc SourceMemImage_phdrs sp_source brk_source mb_source rnd_source
           target_segs (tgt_LH vT inp sp_target mb_target rnd_target)
           TargetMemImage_init_pc TargetMemImage_phdrs sp_target brk_target mb_target rnd_target
           inp).
  - exact ec_lt256.
  - unfold rw_bytes_max. vm_compute. split; [reflexivity | discriminate].
  - intros a ms H. eapply src_LH_to_rd; eassumption.
  - intros a ms H. eapply tgt_LH_to_rd; eassumption.
  - rewrite source_init_pc_val. eapply src_init_to_rd; eassumption.
  - rewrite target_init_pc_val. eapply tgt_init_to_rd; eassumption.
  - (* [Run.valid_input] pins a reader on fd 1 *)
    exact Hrdr.
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

