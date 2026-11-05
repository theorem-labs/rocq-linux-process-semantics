(** * Riscv.Extraction — extract the RV64GC ISA model to OCaml

    Produces [riscv_model.ml] (+ [.mli]), for a differential tester
    that checks this model against independent reference
    implementations of the ISA (a disassembler for the decoder; the
    Sail RISC-V model for execution).

    Not part of the batch build, because compiling it writes a .ml file
    as a side effect: theories/dune names it explicitly in
    [(modules :standard \ Riscv.Extraction LinuxProcessSem.Checks.Extraction)],
    so that list is what must be updated if this file is moved or
    renamed.

    Representation notes for the OCaml side:

    - [N]/[Z]/[positive] are realized with zarith's [Big_int_Z], so the
      OCaml caller can build operands from parsed integers cheaply.
    - [bv n] is a record whose only computational field is the unsigned
      [Z] (the [BvWf] proof is erased), so a bitvector extracts to a
      bare [Big_int_Z.big_int] and the WIDTH IS ERASED.
    - [eff]'s [ELoad] continuation extracts to an OCaml closure, so the
      OCaml caller answers loads on demand out of its own memory.

    THE ROOTS ARE THE CHECKED ONES, and the second note above is why.
    This file used to tell the caller that it "must therefore mask
    values itself when constructing inputs, and must recover each
    immediate's width from the [instr] constructor rather than from the
    runtime value".  A sentence telling the caller to mask is not a
    boundary; it is a contract nobody checks, and it is the same failure
    that let a system call return of 2^64 reach a verdict through the
    other extracted artifact.  [Riscv.CheckedIsa] is the boundary: every
    entry point takes the outside world's values as [Z] and refuses,
    before the model runs, any integer that is not in the type it would
    have to inhabit.  A refusal ([CkRefused], [LsRefused], and [None]
    from [core_of_raw]) is a third answer, kept apart from the model's
    own: a word that does not decode is [CkAnswer None], and a word that
    is not a word at all is [CkRefused].  Read that file for what it
    checks, what it builds, and what it cannot enforce.

    A caller gives an ENCODING and a [RawCore] of plain integers; the
    instruction AST, the compressed AST and the core state are built out
    of [bv]s and so are not arguments of this surface, which is also why
    no caller has to recover an immediate's width any more.
    [eff_feed_load] is how the interpreter answers the [ELoad] its own
    memory serves, and it refuses a value the pending width does not
    hold. *)

From Stdlib Require Import extraction.ExtrOcamlBasic.
From Stdlib Require Import extraction.ExtrOcamlZBigInt.
From LinuxProcessSemantics.Riscv Require Import
  Prelude CheckedBv Instr Decode DecodeC Sem CheckedIsa.

Require Extraction.

(* Roots: the checked decoders and the compressed expander, the checked
   execution of one encoding and of one step, the raw core a caller
   fills in and the way back from a retired one, the checked answer to a
   pending load with the reader of what that load is waiting for, and
   [msize_bytes], which takes no bitvector.

   [decode], [decode16], [expand_c], [decode_any], [is_defined_illegal],
   [exec] and [step] are NOT roots any more: each is reached through its
   checked form, and naming one here would publish a way into the model
   that no boundary guards.  (The generated .mli publishes everything the
   roots reach, these included, so no choice of roots can hide them; the
   roots are what this tree supports, and what a reader must use.) *)
Extraction "riscv_model.ml"
  decode_checked
  decode16_checked
  expand_c_checked
  decode_any_checked
  is_defined_illegal_checked
  exec_encoded_checked
  step_checked
  mkRawCore
  core_of_raw
  raw_of_core
  eff_pending_load
  eff_feed_load
  msize_bytes.
