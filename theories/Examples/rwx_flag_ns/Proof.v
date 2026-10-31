(** * Equivalence proof for rwx-flag-ns — top-level glue.

    PROOF-SIDE FILE (not part of the trusted specification).  Discharges
    [strong_universal_T]: observable trace equivalence between the source
    image (Source) and the target image (Target) for all valid stack
    pointers and every valid process input (one [State.ProcInput]
    record: argv, envp, file system, stdin, the credentials, the kernel
    build and the exec file name).

    Both binaries store 5 into a writable global byte, load it back and
    exit with it — no output, exit 5, on every input — so the two
    [to_wexit] derivations agree on [([], 5)] and are glued with
    [cat_strong_equiv_te].

    The point of the example is the SOURCE's layout: a single RWX LOAD
    segment (linked without [-z separate-code]; see source/rwx.lds), so
    every source fetch goes through the overlay-aware w+x fetch and the
    source derivation is carried by [Common.WxExec]'s frame invariant —
    see rwx_flag_ns_source.v.  The target is an ordinary lld-linked
    binary, proved with the standard static-fetch machinery. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec.
From LinuxProcessSemantics.Examples.rwx_flag_ns Require Import rwx_flag_ns_defs rwx_flag_ns_source rwx_flag_ns_target.
From LinuxProcessSemantics.Examples.rwx_flag_ns Require Import rwx_flag_ns_code.
From LinuxProcessSemantics.Examples.rwx_flag_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.rwx_flag_ns Require Import TargetMemImage.

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
     this stack top, stack pointer and mmap base are ones a Linux
     launch can give ([create_elf_tables] and [setup_arg_pages],
     fs/binfmt_elf.c and fs/exec.c, Linux v6.18.46, commit
     1f99e9ab748f).  The source derivation reads argc off the initial
     stack and fetches through the overlay, so it needs that conjunct
     and the LAST conjunct of [Run.valid_input], [Run.valid_launch]:
     together they bound the entry block and put [sp] at or below the
     stack VMA's end.  The target reads nothing off the stack and needs
     neither. *)
  destruct Hens as (Hspr & _ & _ & _ & Hlaunch_source).
  destruct Hent as (Hspa & _).
  (* Guarded rather than positional: [Run.valid_input] grows a conjunct
     whenever the input class learns to say something new, and this
     proof names none of them by place -- the peel below leaves every
     clause in the context, where [assumption] finds it.  The
     [lazymatch] is the guard, and it is what stops the peel at
     [Run.valid_launch]: that conjunct stays FOLDED, so it is not
     syntactically a conjunction and arrives whole, which is what
     [source_wexit] asks for.  Scoped to [Hvalid] rather than run over
     every conjunction in the context, because [Hlaunch_source] must
     stay whole too. *)
  red in Hvalid.
  repeat (lazymatch type of Hvalid with
          | _ /\ _ => let Hc := fresh "Hc" in destruct Hvalid as [Hc Hvalid]
          end).
  destruct Hspr as (Hr_lo & Hr_hi & _).
  destruct Hspa as (Ha_lo & Ha_hi & _).
  apply (cat_omni_strong_equiv_te
           source_segs SourceMemImage_init_pc SourceMemImage_phdrs sp_source brk_source mb_source rnd_source
           target_segs TargetMemImage_init_pc TargetMemImage_phdrs sp_target brk_target mb_target rnd_target
           [] (Z_to_bv 64 5) inp).
  - rewrite source_init_pc_val.
    apply source_wexit with (rbrk := brk_source); assumption.
  - rewrite target_init_pc_val.
    apply target_wexit; assumption.
  - (* Neither binary writes anything, so there is no buffer to bound. *)
    unfold bufs_modeled. constructor.
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

