import LinuxProcessSemantics.Examples.grep_args_ns.grep_args_ns_source
import LinuxProcessSemantics.Examples.grep_args_ns.grep_args_ns_target

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! Mirrors `theories/Examples/grep_args_ns/Proof.v` at the baseline above;
this proof-side file discharges observable trace equivalence between the
source and target images for every valid process input (argv, envp, file
system and stdin). `omni_strong_universal` glues the per-binary derivations
with `Common.WallSim.wall_omni_strong_equiv`, once per input branch, and
`strong_universal` follows through `strong_universal_iff`.

Both binaries implement grep-args: with `pat = argv[1]`, each argument
starting at index 2 that contains `pat` is written to stdout, followed by
a newline, and the program exits 0; `argc < 2` exits 2 without output.
The modeled stdout write of a readable nonempty buffer delivers a
nondeterministic nonempty prefix. The put-style retry loops push the
remainder out, so `WallSim.to_wall` accounts for the whole buffer and
the write-error paths (exit 3) stay dead. The shared buffers are
`grep_bufs pat (argv.drop 2)`; a matching empty argument contributes only
its newline, since both binaries skip zero-length writes.

The source is musl-gcc -Os output: a stack frame, saved registers, an
environ store in _start, and the musl write wrapper's
argument shuffling and __syscall_ret scratch store below the frame. The
source proof threads that store through its `mem_ok` abstraction. The target
is Zig ReleaseSmall output with its own frame and leaf slen/put functions.
Rocq `Proof.v`'s header says the source calls musl's strlen; it does not
(the comment above `source_slen_hay` in
`theories/Examples/grep_args_ns/grep_args_ns_source.v` says the three scans
are inline), and neither Rocq derivation uses the `tw_write_ret` it names.

The per-binary proofs build `to_wallexit` over the argv layout, with
per-iteration induction for the loops; their Lean ports replace Rocq's
reflective `sym_block` straight lines with StepTac instruction steps. The
buffer specification and binary-independent lemmas live in `grep_args_ns_defs`; this file combines
the matching buffers and exit codes through WallSim's shape algebra.

Lean spellings: Rocq's `Z` is `Int`, `nat` is `Nat`, `firstn`/`skipn` are
`List.take`/`List.drop`, and `nth` is `List.getD`. Section variables become
explicit arguments or `variable`s. Bytes and words are `BitVec 8` and
`BitVec 64`; address bookkeeping uses `Int` over `bv_unsigned`, and computed
stack addresses use `Z_to_bv 64`. `Source.image` and `Target.image` abbreviate the
Rocq statements' `mkImage` applications.

Which dispatcher arms the theorem rests on: WallSim's write/exit derivations
use `Common/CatSim.lean`'s `syscall_spec_write` and
`Common/ExitSim.lean`'s `syscall_spec_exit`. The grep_args_ns entry in
`testing/syscall-check/traces/examples.json` records the arms write and exit,
syscall numbers 64 and 93 for both binaries, and both ending with exit code 0
for `conform -- ell hello bell nope`. That recorded run exercises the
matching-argument branch; the theorem also covers the `argc < 2` branch.
-/

namespace LinuxProcessSemantics.Examples.grep_args_ns.Proof

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.OmniRun
open LinuxProcessSemantics.Common.WallSim
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence
open LinuxProcessSemantics.Examples.grep_args_ns.SourceMemImage
open LinuxProcessSemantics.Examples.grep_args_ns.TargetMemImage
open LinuxProcessSemantics.Examples.grep_args_ns.grep_args_ns_code
open LinuxProcessSemantics.Examples.grep_args_ns.grep_args_ns_defs
open LinuxProcessSemantics.Examples.grep_args_ns.grep_args_ns_source
open LinuxProcessSemantics.Examples.grep_args_ns.grep_args_ns_target

-- Glue: identical buffers and exit code on both sides give strong equivalence.
theorem omni_strong_universal : omni_strong_universal_T Source.image Target.image := by
  intro es et inp Hens Hent Hvalid
  cases es with
  | mkEntry sp_source brk_source mb_source rnd_source =>
  cases et with
  | mkEntry sp_target brk_target mb_target rnd_target =>
  -- The input declares Sv48 (`Run.valid_input` pins it), so the entry
  -- predicate is the literal Sv48 one (`Run.valid_entry_sv48`).
  have Hsv48 := valid_input_va_size inp Hvalid
  have Hens' := (valid_entry_sv48 _ _ _ Hsv48).1 Hens
  have Hent' := (valid_entry_sv48 _ _ _ Hsv48).1 Hent
  obtain ⟨Hspr, _⟩ := Hens'
  obtain ⟨Hspa, _⟩ := Hent'
  obtain ⟨Hva, Hve, _⟩ := Hvalid
  obtain ⟨Hr_lo, Hr_hi, _⟩ := Hspr
  obtain ⟨Ha_lo, Ha_hi, _⟩ := Hspa
  by_cases Hge2 : 2 ≤ inp.in_argv.length
  · apply wall_omni_strong_equiv
      source_segs SourceMemImage_init_pc SourceMemImage_phdrs
      sp_source brk_source mb_source rnd_source
      target_segs TargetMemImage_init_pc TargetMemImage_phdrs
      sp_target brk_target mb_target rnd_target
      (grep_bufs (inp.in_argv.getD 1 []) (inp.in_argv.drop 2)) (Z_to_bv 64 0) inp
    · rw [source_init_pc_val]
      apply source_wexit_ge2 <;> assumption
    · rw [target_init_pc_val]
      apply target_wexit_ge2 <;> assumption
    · -- Every written buffer fits the model's single-transfer bound:
      -- a matching argv string (≤ 131071 bytes by `valid_argv`) or
      -- a one-byte newline.
      apply grep_bufs_modeled
      apply Forall_skipn_argv
      exact Hva.2.2.1
  · have Hlt2 : inp.in_argv.length < 2 := Nat.lt_of_not_ge Hge2
    apply wall_omni_strong_equiv
      source_segs SourceMemImage_init_pc SourceMemImage_phdrs
      sp_source brk_source mb_source rnd_source
      target_segs TargetMemImage_init_pc TargetMemImage_phdrs
      sp_target brk_target mb_target rnd_target
      [] (Z_to_bv 64 2) inp
    · rw [source_init_pc_val]
      apply source_wexit_lt2 <;> assumption
    · rw [target_init_pc_val]
      apply target_wexit_lt2 <;> assumption
    · intro b hb
      exact False.elim (List.not_mem_nil hb)

/-- The legacy statement, through the compatibility iff; this is the theorem
`Checker.v` pins to `Equivalence.SPEC`. -/
theorem strong_universal : strong_universal_T Source.image Target.image :=
  (strong_universal_iff Source.image Target.image).2 omni_strong_universal

end LinuxProcessSemantics.Examples.grep_args_ns.Proof
