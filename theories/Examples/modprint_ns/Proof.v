(** * Equivalence proof for modprint-ns — top-level glue.

    PROOF-SIDE FILE (not part of the trusted specification).  Discharges
    [strong_universal_T]: observable trace equivalence between the source
    image (Source) and the target image (Target) for all valid stack
    pointers and every valid process input (one [State.ProcInput]
    record: argv, envp, file system, stdin, the credentials, the kernel
    build and the exec file name).

    Both binaries make the SAME single syscall sequence for every input:

      - write(1, udec (argc mod 7) ++ "\n", 2), then exit 0.

    The MACHINE side is deterministic, but the ENVIRONMENT is not: a
    channel write delivers a nonempty prefix of its own choosing, and
    this is the one example whose binaries do not retry, so the choice
    is observable.  With a 2-byte buffer the behavior is therefore a
    two-element family — deliver the digit alone, or the digit and the
    newline — and both binaries admit exactly the same family.

    There is no input-dependent control flow in either binary, so this
    proof has no case split at all: one application of the shape
    algebra's [cat_strong_equiv_alg] to the two per-binary
    [to_wexit] derivations, both concluding at the same
    [(mod_bufs argc, 0)].  The initial stack pointers are QUANTIFIED
    (ASLR): [strong_universal_T] supplies independent
    [sp_source]/[sp_target] anywhere in the valid window.

    This is the SHAPE end of the combined infrastructure stack.  Both
    binaries realize the trace set [t_writes_pick (mod_bufs argc)
    (t_exit 0 (in_fs inp))] — the delivered-prefix family, NOT the
    full-delivery [t_writes], which is what a retrying binary realizes;
    [ShapeAlg.realizes_obs_iff] is a plain [iff], so the two are not
    interchangeable.  [Common/ShapeAlg.v] carries the two [to_wexit]
    derivations into
    [realizes] and closes [strong_equiv] with its single master theorem,
    so nothing in [Common/CatSim.v] is on the critical path any more.
    Underneath, the source's [to_wexit] derivation is itself produced by
    the other two layers: a [Common/MuslCall.v] summary for musl's [write]
    blob and [Common/SymTac.v]'s [sym_block] for every straight line
    between the syscalls (see [modprint_ns_source.v]).

    Each derivation runs over the run's segment list ([Run.run_segments])
    and takes the entry predicate's launch conjunct
    [Run.entry_launch_ok_va] and [Run.valid_launch]; the glue takes
    [Run.valid_input]'s reader on fd 1 ([Run.valid_input_channel_reader]),
    since a write into a reader-gone channel is a different run. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec NumPrint ShapeAlg.
From LinuxProcessSemantics.Examples.modprint_ns Require Import modprint_ns_defs modprint_ns_code modprint_ns_source modprint_ns_target.
From LinuxProcessSemantics.Examples.modprint_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.modprint_ns Require Import TargetMemImage.
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
  (* The FIFTH conjunct of each entry predicate is [Run.entry_launch_ok_va]:
     the stack top, stack pointer and mmap base a Linux launch can give
     ([create_elf_tables] and [setup_arg_pages], fs/binfmt_elf.c and
     fs/exec.c, Linux v6.18.46, commit 1f99e9ab748f).  Both derivations
     read argc off the initial stack and store into it, so both need it,
     with [Run.valid_launch]. *)
  destruct Hens as (Hspr & _ & _ & _ & Hlau_source).
  destruct Hent as (Hspa & _ & _ & _ & Hlau_target).
  pose proof (valid_input_argv _ Hvalid) as Hva.
  pose proof (valid_input_launch _ Hvalid) as Hvl.
  pose proof (valid_input_channel_reader _ Hvalid) as Hrdr.
  set (argv := in_argv inp) in *.
  destruct Hspr as (Hr_lo & Hr_hi & _).
  destruct Hspa as (Ha_lo & Ha_hi & _).
  apply (cat_omni_strong_equiv_alg
           source_segs SourceMemImage_init_pc source_phdrs sp_source brk_source mb_source rnd_source
           target_segs TargetMemImage_init_pc target_phdrs sp_target brk_target mb_target rnd_target
           (mod_bufs (Z.of_nat (length argv))) (Z_to_bv 64 0) inp).
  - rewrite source_init_pc_val.
    apply (source_wexit inp Hva Hvl sp_source brk_source mb_source rnd_source);
      assumption.
  - rewrite target_init_pc_val.
    apply (target_wexit inp Hva Hvl sp_target brk_target mb_target rnd_target);
      assumption.
  - (* The single buffer is the two bytes [digit; '\n'], well under the
       model's read/write transfer bound. *)
    unfold bufs_modeled, mod_bufs.
    repeat constructor.
    unfold buf_modeled. rewrite mod_buf_bytes by lia.
    cbn [length]. unfold rw_bytes_max. lia.
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

