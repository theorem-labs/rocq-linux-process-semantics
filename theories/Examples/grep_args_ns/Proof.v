(** * Equivalence proof for grep-args-ns

    PROOF-SIDE FILE (not part of the trusted specification).  Discharges [strong_universal_T]: observable trace
    equivalence between the source image (Source) and the target image (Target)
    for every valid process input (one [State.ProcInput] record: argv,
    envp, file system, stdin), under the star-based
    [LinuxProcessSem.Run] trace semantics.

    Both binaries implement grep-args: with [pat = argv[1]], for each
    [argv[i]] (i >= 2) containing [pat] as a substring they write that
    argument then a newline to stdout, and exit 0; [argc < 2] exits 2 with
    no output.  In-model a write to the stdout channel with a readable
    buffer delivers a nondeterministic NONEMPTY prefix; both binaries
    push the remainder out through a put-style retry loop, so the whole
    buffer still reaches the trace in one piece ([WallSim.to_wall]) and
    the write-error paths (exit 3) stay dead.  The shared observable
    behavior is

      bufs = grep_bufs pat (skipn 2 argv)      (see [grep_bufs] below)
      code = 0                                  (or 2 when argc < 2)

    where a matching empty argument contributes only its newline (both
    binaries skip zero-length writes).

    The source is musl-gcc -Os output (a real stack frame, saved
    registers, an environ-store in _start, calls to musl's [strlen] --
    gcc recognizes the C [slen] loops as strlen -- and calls into musl's
    write() wrapper: arg-shuffling __syscall plumbing plus
    __syscall_ret, whose scratch store below the frame the proof threads
    through a [mem_ok] memory abstraction); the target is Zig
    ReleaseSmall output (its own frame plus leaf slen/put functions).
    Neither difference is observable.

    musl's [strlen] scans 8 bytes at a time with the classic
    [(x - ONES) & ~x & HIGHS] has-zero test; module [HZ] below proves
    that test exact, and [read_word_m] shows the (NUL-straddling) word
    load always lands inside the initial stack image.

    Proof shape, per binary: symbolic execution over the argv layout
    builds the inductive [to_wallexit] (Common.WallSim) — straight lines run
    reflectively by [Common/SymTac.v]'s [sym_block] and re-attached
    through [msteps], loops carried by per-iteration induction, write/exit
    tails attached with [tw_write_ret]/[tw_exit_coden].  The per-binary
    derivations live in [grep_args_ns_source.v] and
    [grep_args_ns_target.v]; the shared observable-behavior spec and the
    binary-independent lemmas live in [grep_args_ns_defs.v].  The two
    derivations are glued here with [WallSim.wall_strong_equiv] (the
    shape algebra's [wall_realizes]), once per input branch.

    Conventions: bytes are [byte = bv 8],
    machine values [word = bv 64]; unbounded address bookkeeping is in [Z]
    over [bv_unsigned]; computed stack addresses use the canonical
    [Z_to_bv 64 (...)] form, pc values the numeral-literal form (the two
    are only PROPOSITIONALLY interchangeable — see StepTac's [wlit]). *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac MuslStrlen StreamSim StoreOk WallSim ShapeAlg.
From LinuxProcessSemantics.Examples.grep_args_ns Require Import grep_args_ns_code.
From LinuxProcessSemantics.Examples.grep_args_ns Require Import grep_args_ns_defs.
From LinuxProcessSemantics.Examples.grep_args_ns Require Import grep_args_ns_source.
From LinuxProcessSemantics.Examples.grep_args_ns Require Import grep_args_ns_target.
From LinuxProcessSemantics.Examples.grep_args_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.grep_args_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(* ######################################################################### *)
(* Glue: identical buffers and exit code on both sides -> strong equiv.     *)
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
  (* The FIFTH conjunct of each entry predicate is [Run.entry_launch_ok_va]:
     the stack top, stack pointer and mmap base a Linux launch can give
     ([create_elf_tables] and [setup_arg_pages], fs/binfmt_elf.c and
     fs/exec.c, Linux v6.18.46, commit 1f99e9ab748f).  Both derivations
     read the argv strings off the initial stack and store into it, so
     both need it, with [Run.valid_launch]. *)
  destruct Hens as (Hspr & _ & _ & _ & Hlau_source).
  destruct Hent as (Hspa & _ & _ & _ & Hlau_target).
  pose proof (valid_input_argv _ Hvalid) as Hva.
  pose proof (valid_input_envp _ Hvalid) as Hve.
  pose proof (valid_input_launch _ Hvalid) as Hvl.
  pose proof (valid_input_channel_reader _ Hvalid) as Hrdr.
  set (argv := in_argv inp) in *.
  destruct Hspr as (Hr_lo & Hr_hi & _).
  destruct Hspa as (Ha_lo & Ha_hi & _).
  destruct (le_lt_dec 2 (length argv)) as [Hge2 | Hlt2].
  - apply (wall_omni_strong_equiv
             source_segs SourceMemImage_init_pc SourceMemImage_phdrs sp_source brk_source mb_source rnd_source
             target_segs TargetMemImage_init_pc TargetMemImage_phdrs sp_target brk_target mb_target rnd_target
             (grep_bufs (nth 1 argv []) (skipn 2 argv)) (Z_to_bv 64 0) inp).
    + rewrite source_init_pc_val.
      eapply (source_wexit_ge2 inp); eassumption.
    + rewrite target_init_pc_val.
      eapply (target_wexit_ge2 inp); eassumption.
    + (* every written buffer fits the model's single-transfer bound:
         a matching argv string (<= 131071 bytes by [valid_argv]) or a
         one-byte newline. *)
      apply grep_bufs_modeled, Forall_skipn_argv.
      destruct Hva as (_ & _ & Hlen & _). exact Hlen.
    + (* [Run.valid_input] pins a reader on fd 1 *)
      exact Hrdr.
  - apply (wall_omni_strong_equiv
             source_segs SourceMemImage_init_pc SourceMemImage_phdrs sp_source brk_source mb_source rnd_source
             target_segs TargetMemImage_init_pc TargetMemImage_phdrs sp_target brk_target mb_target rnd_target
             [] (Z_to_bv 64 2) inp).
    + rewrite source_init_pc_val.
      eapply (source_wexit_lt2 inp); eassumption.
    + rewrite target_init_pc_val.
      eapply (target_wexit_lt2 inp); eassumption.
    + apply Forall_nil.
    + exact Hrdr.
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

