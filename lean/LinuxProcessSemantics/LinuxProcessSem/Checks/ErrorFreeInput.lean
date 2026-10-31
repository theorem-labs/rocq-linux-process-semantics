-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/ErrorFreeInput.v
import LinuxProcessSemantics.LinuxProcessSem.Checks.Examples
import LinuxProcessSemantics.LinuxProcessSem.Checks.Omni
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.Equivalence
import LinuxProcessSemantics.EquivalenceDefinition.Classifier
import LinuxProcessSemantics.EquivalenceDefinition.FinInput
import LinuxProcessSemantics.EquivalenceDefinition.MustExit
import LinuxProcessSemantics.Common.PropExec

/-! # LinuxProcessSem.Checks.ErrorFreeInput — the buggy / not-buggy gate, witnessed

Mirrors `theories/LinuxProcessSem/Checks/ErrorFreeInput.v`.  Not part of
the trusted specification: QA on `EquivalenceDefinition.Classifier`'s
`error_free_input` and `classifies_error_free_inputs_T`, in the style of
`Checks/Examples.lean`.

`EquivalenceDefinition/Classifier.lean` states what the gate of a
two-region submission decides — whether the ORIGINAL program is
error-free on the input — and proves that of ABSTRACT images.  Nothing
there exhibits an original.  A predicate that no concrete binary is ever
shown to satisfy, and none to refute, would leave both its bite and its
vacuity lemma free, so this file runs the definition on the two concrete
riscv64 images `Checks/Examples.lean` already built and one concrete
input, and pins both answers:

- PART 1 — the two regions, inhabited.  `Checks.Examples.exit0_image` is
  error-free on this input at EVERY entry `execve` could have chosen,
  which is what `Classifier.error_free_input` quantifies over;
  `Checks.Examples.undecodable_image` is not, refuted from ONE valid
  entry, which is all a refutation needs.
- PART 2 — what those answers oblige a gate to do.  A gate meeting
  `Classifier.classifies_error_free_inputs_T` for the undecodable
  original must exit 1 on this input, and one meeting it for the exit-0
  original must exit 0 — at every valid entry of its own, in both cases,
  and whatever else the gate does.
- PART 3 — the vacuity route the trusted file names, biting the ORIGINAL
  rather than the gate: an original that does not load is not-buggy
  everywhere, so a gate that decides correctly about it accepts the whole
  input space and the second program of the split is never asked about
  anything.
- PART 4 — the same two answers under the configuration layer.

Which of the four reasons at the top of `Checks/Examples.lean` admits
this file: the FIRST.  `Classifier.error_free_input` is a `∀` over every
valid `Run.ExecEntry` ending in `Equivalence.error_free`, itself the
negation of a reachability claim about a whole run tree, and
`Classifier.decides` adds a `MustExit.must_exit_with` over that same
tree.  A real run shows one execution of one of these binaries; it cannot
show all of them, and it has no notion of a region at all.

WHAT THIS FILE BORROWS RATHER THAN REBUILDS.  The Rocq file reuses three
`Checks/Examples.v` facts — `demo_input_valid`,
`demo_entry_valid_undecodable` and
`run_of_undecodable_image_is_unmodeled_at_demo_entry` — and
`Checks/Examples.lean` carries none of them.  The Lean tree has the same
three facts elsewhere and they are used from there rather than written
again: `Checks.Omni.demo_input_valid` (which `Checks/Omni.lean` says
belongs in `Checks/Examples.lean` when that file ports it),
`Checks.Cases.EquivalenceDefinition.Equivalence.undecodable_entry_valid`
and `…Equivalence.undecodable_run_unmodeled`, the last two generalised
over the input and the budget, so the Rocq lemmas' `source_alloc_limit`
instance is an application.  The one fact no file has is the CONFIGURED
reading of the third, which Part 4 needs; it is proved below under the
Rocq name `undecodable_unmodeled_scfg`, which is a declaration of the
Rocq file itself.

SPELLINGS.  Rocq's `Example`/`Lemma` is a Lean `theorem`; `Z` is `Int`;
Rocq's `vm_compute; reflexivity` on a closed computation is
`decide +kernel`, the kernel-evaluated form `Checks/Examples.lean` uses,
and `rfl` where the two sides are already one term.  Rocq's
`destruct en as [sp brk0 mbase rnd]` before `vm_compute` is `obtain`, but
not for Rocq's reason: Rocq's `vm_compute` reduces past the four entry
fields, and a Lean `decide` refuses any goal that still carries a free
variable, so the entry is taken apart to NAME its stack pointer and its
draw for the quantified lemma that closes the fuel run,
`Checks.Omni.exit0_exits_c`. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.ErrorFreeInput

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.MustExit
open LinuxProcessSemantics.EquivalenceDefinition.FinInput
open LinuxProcessSemantics.EquivalenceDefinition.Classifier
open LinuxProcessSemantics.Common.PropExec
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Examples

/-! ## The input everything below runs on -/

/-- One empty argument, no environment, an empty file system, no standard
input — the input `Checks/Examples.lean`'s own witnesses use (it is the
same term as `Checks.Examples.demo_proc_input`), named here so the
statements below read as claims about a fixed input rather than about a
literal repeated eleven times.  Rocq:
`ErrorFreeInput.efi_demo_input`. -/
def efi_demo_input : ProcInput :=
  ProcInput.mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
    default_nofile (Z_to_bv 64 0) demo_hwcap false .Sv48

/-- Rocq: `ErrorFreeInput.efi_demo_input_valid`.  Rocq closes it by
`Checks.Examples.demo_input_valid`; the Lean twin of that fact is
`Checks.Omni.demo_input_valid`, which `Checks/Omni.lean` states beside
its one reader and records as belonging to `Checks/Examples.lean`. -/
theorem efi_demo_input_valid : valid_input efi_demo_input :=
  Checks.Omni.demo_input_valid

/-- The same input as a `FinInput.FinProcInput`, which is what
`Classifier.decides` quantifies over: the gate obligations are stated on
finite inputs, for the reason `EquivalenceDefinition/Classifier.lean`'s
header gives — a verdict is an observable event, so accept sets are open
in the prefix topology and the properties worth classifying are not.
`efi_demo_to_proc_input` pins that the two records agree by computation
rather than by the reader's eye.  Rocq: `ErrorFreeInput.efi_demo_fin`. -/
def efi_demo_fin : FinProcInput :=
  FinProcInput.mkFinProcInput [[]] [] [] [] demo_uid demo_gid demo_groups net_silent
    default_nofile (Z_to_bv 64 0) demo_hwcap false .Sv48 [] []

/-- Rocq: `ErrorFreeInput.efi_demo_to_proc_input`. -/
theorem efi_demo_to_proc_input : to_proc_input efi_demo_fin = efi_demo_input := rfl

/-- It is a VALID finite input, which every gate statement below needs: an
obligation quantified over valid inputs is refuted by nothing else, and a
region containing only invalid inputs is a region no program is ever asked
about.  Rocq: `ErrorFreeInput.efi_demo_fin_valid`. -/
theorem efi_demo_fin_valid : valid_fin_input efi_demo_fin := by
  unfold valid_fin_input
  rw [efi_demo_to_proc_input]
  exact efi_demo_input_valid

/-- `Run.valid_entry` of the undecodable image at `Checks.Examples.demo_entry`
on this input.  NO ROCQ TWIN in this file: Rocq writes
`apply demo_entry_valid_undecodable; exact efi_demo_input_valid` at each
of the five places that need it, and
`Checks.Cases.EquivalenceDefinition.Equivalence.undecodable_entry_valid`
is the Lean twin of that `Checks/Examples.v` lemma, generalised over the
input.  Named once here so the five uses below read as Rocq's do. -/
theorem efi_undecodable_entry : valid_entry undecodable_image demo_entry efi_demo_input :=
  Checks.Cases.EquivalenceDefinition.Equivalence.undecodable_entry_valid _
    (valid_input_va_size _ efi_demo_input_valid)
    (by unfold valid_argv; decide) (by unfold valid_envp; decide)

/-! ## PART 1 — the two regions, inhabited -/

/-- The exit-0 image must exit 0 AT EVERY ENTRY, at the SOURCE role's
budget.  Both halves of that sentence are the point.

Every entry, because `Classifier.error_free_input` is a `∀` over them and
one entry would not do it: the original has to behave however `execve`
placed its stack, break and mmap base, and whatever 16 AT_RANDOM bytes it
drew.  It is provable here for the reason `Checks/Examples.lean`'s header
gives for this program — it makes no memory access at all beyond its own
instruction fetches — so all four entry fields are left as VARIABLES.  A
closed `decide` cannot state that: `decide` refuses a goal carrying a free
variable, and reverting `sp` and the `StackLayout.EntryDraw` would ask for
a decision procedure over both types.  The fuel run is therefore closed by
`Checks.Omni.exit0_exits_c`, which is Rocq's `Omni.exit0_exits_c` and is
already quantified over the stack pointer, the draw, the argument and
environment lists, the user identifier and the capability word; an original
that consulted its stack pointer, or read the bytes AT_RANDOM points at,
could not have that lemma.

`State.source_alloc_limit`, because that is the budget
`Classifier.error_free_input` names, and it is not
`Classifier.classifier_alloc_limit` (which is what the GATE would run at)
and not `Checks.Cases.Prelude.demo_limit` (which
`Checks.Examples.exit0_image_must_exit_zero` uses).  Rocq:
`ErrorFreeInput.exit0_must_exit_zero_at_source_budget`. -/
theorem exit0_must_exit_zero_at_source_budget (en : ExecEntry) :
    must_exit_with verdict_accept exit0_image source_alloc_limit en efi_demo_input := by
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  unfold must_exit_with init_config
  apply exits_c_must_exit_at _ _ 8
  · rfl
  · rfl
  · exact Checks.Omni.exit0_exits_c sp rnd _ _ _ _

/-- THE NOT-BUGGY REGION IS INHABITED: this input is in it, for the exit-0
original.  The step from "must exit 0" to "never errors" is
`MustExit.must_exit_with_no_error`, which is what lets a
`MustExit.must_exit_with` obligation stand in for an error-freedom one — a
binary that decides by exiting cannot also be allowed to fault.  The entry
hypothesis is discarded rather than used: the exit-0 image behaves at
EVERY entry, valid or not, which is stronger than the definition asks for.
Rocq: `ErrorFreeInput.exit0_error_free_input`. -/
theorem exit0_error_free_input : error_free_input exit0_image efi_demo_input := by
  intro en _
  exact must_exit_with_no_error _ _ _ _ _ (exit0_must_exit_zero_at_source_budget en)

/-- THE BUGGY REGION IS INHABITED TOO, at the same input for a different
original: the undecodable image errors on its first fetch, so it is not
error-free there.  One valid entry is enough, which is the asymmetry
`Classifier.error_free_input`'s `∀` creates and
`Classifier.error_free_input_refuted_by_error` is the elimination rule
for.

The error is reached through `Equivalence.run_unmodeled_errors`: leaving
the modeled surface is a special case of erroring, and the Lean twin of
`Checks.Examples.run_of_undecodable_image_is_unmodeled_at_demo_entry` is
`Checks.Cases.EquivalenceDefinition.Equivalence.undecodable_run_unmodeled`,
which is stated at EVERY budget, so `State.source_alloc_limit` — the
budget this predicate names — is one of its instances rather than a
separate lemma.  Rocq:
`ErrorFreeInput.undecodable_not_error_free_input`. -/
theorem undecodable_not_error_free_input :
    ¬ error_free_input undecodable_image efi_demo_input :=
  error_free_input_refuted_by_error _ _ demo_entry efi_undecodable_entry
    (run_unmodeled_errors _ _ _ _
      (Checks.Cases.EquivalenceDefinition.Equivalence.undecodable_run_unmodeled _ _))

/-- The two answers really are different answers, which is the fact a
region boundary is made of.  Asserted as a pair rather than left to a
reader who has both lemmas in hand, because a predicate constant on the
images anyone tries it on would carve no boundary at all and every
disjointness fact about the two regions would be free.  Rocq:
`ErrorFreeInput.error_free_input_separates_the_two_images`. -/
theorem error_free_input_separates_the_two_images :
    error_free_input exit0_image efi_demo_input
    ∧ ¬ error_free_input undecodable_image efi_demo_input :=
  ⟨exit0_error_free_input, undecodable_not_error_free_input⟩

/-! ## PART 2 — what those answers oblige a gate to do -/

/-- A gate that decides this predicate about the UNDECODABLE original must
exit 1 on this input, at every valid entry of its own.  The gate is
quantified, not exhibited, because the claim is about what the obligation
FORCES rather than about a binary.  Exhibiting one is a different and much
larger piece of work — the shape of it is
`Examples.patchclassify_demo.Obligations`, which builds a concrete
classifier for each of the other two properties in this family and proves
`Classifier.decides` of it — and no image has been built for THIS
property.

Note the budget the conclusion is at: `Classifier.classifier_alloc_limit`,
the one the gate RUNS at, while the hypothesis feeding it was about the
original's run at `State.source_alloc_limit`.  The two budgets appear in
one statement and never in one run.  Rocq:
`ErrorFreeInput.gate_for_undecodable_original_must_exit_one`. -/
theorem gate_for_undecodable_original_must_exit_one (C : Image) (enC : ExecEntry)
    (hdec : classifies_error_free_inputs_T undecodable_image C)
    (henC : valid_entry C enC (to_proc_input efi_demo_fin)) :
    must_exit_with verdict_reject C classifier_alloc_limit enC
      (to_proc_input efi_demo_fin) := by
  refine classifies_error_free_inputs_T_rejects_error undecodable_image C efi_demo_fin
    demo_entry enC hdec efi_demo_fin_valid ?_ ?_ henC
  · rw [efi_demo_to_proc_input]; exact efi_undecodable_entry
  · rw [efi_demo_to_proc_input]
    exact run_unmodeled_errors _ _ _ _
      (Checks.Cases.EquivalenceDefinition.Equivalence.undecodable_run_unmodeled _ _)

/-- ... and the same input read as a member of the gate's REJECT SET, which
is the reading the measure layer sums over (`Classifier.rejects` is
`FinInput.valid_fin_input` together with the negation of
`Classifier.accepts`).  Stated as well as the exit code because the two
are the same fact only for a gate with an inhabited entry space, and that
hypothesis is where the difference lives.  Rocq:
`ErrorFreeInput.gate_for_undecodable_original_rejects`. -/
theorem gate_for_undecodable_original_rejects (C : Image) (enC : ExecEntry)
    (hdec : classifies_error_free_inputs_T undecodable_image C)
    (henC : valid_entry C enC (to_proc_input efi_demo_fin)) :
    rejects C efi_demo_fin := by
  refine classifies_error_free_inputs_T_refutes_acceptance undecodable_image C efi_demo_fin
    demo_entry enC hdec efi_demo_fin_valid ?_ ?_ henC
  · rw [efi_demo_to_proc_input]; exact efi_undecodable_entry
  · rw [efi_demo_to_proc_input]
    exact run_unmodeled_errors _ _ _ _
      (Checks.Cases.EquivalenceDefinition.Equivalence.undecodable_run_unmodeled _ _)

/-- ... and the other direction, for the exit-0 original: the gate must
ACCEPT, at every valid entry, which is `Classifier.accepts` itself.  Both
directions are pinned because the obligation is an iff and either half
alone would be met by a gate with one fixed answer.  Rocq:
`ErrorFreeInput.gate_for_exit0_original_accepts`. -/
theorem gate_for_exit0_original_accepts (C : Image)
    (hdec : classifies_error_free_inputs_T exit0_image C) :
    accepts C efi_demo_fin := by
  refine classifies_error_free_inputs_T_accepts_error_free exit0_image C efi_demo_fin hdec
    efi_demo_fin_valid ?_
  rw [efi_demo_to_proc_input]
  exact exit0_error_free_input

/-- The two verdicts a gate is forced into at this one input are
incompatible, so no single image is a correct gate for both originals.
That is the sharpest form of "the boundary is not the submission's to
choose": the gate's answer is determined by which original it is asked
about.

The contradiction runs through `MustExit.must_exit_with_exclusive` against
`Classifier.verdict_accept_neq_reject`, and it needs one valid entry of
the gate to have anything to contradict — with none,
`Classifier.decides_vacuous_no_entries` hands both hypotheses to the same
image for free, so the statement stripped of that entry would be false.
It is the `Equivalence.IMAGE_WF` obligation showing up in the smallest
possible statement.  Rocq:
`ErrorFreeInput.no_gate_serves_both_originals`. -/
theorem no_gate_serves_both_originals (C : Image) (enC : ExecEntry)
    (henC : valid_entry C enC (to_proc_input efi_demo_fin))
    (hbad : classifies_error_free_inputs_T undecodable_image C)
    (hgood : classifies_error_free_inputs_T exit0_image C) : False :=
  verdict_accept_neq_reject
    (must_exit_with_exclusive _ _ _ _ _ _
      (gate_for_exit0_original_accepts C hgood enC henC)
      (gate_for_undecodable_original_must_exit_one C enC hbad henC))

/-! ## PART 3 — the vacuity route, biting the ORIGINAL -/

/-- An original that does not load is NOT-BUGGY EVERYWHERE, so a gate that
decides correctly about it accepts the whole input space: the not-buggy
region is everything, the second program of the split is never asked about
any input, and its own slice obligation holds with nothing established
about its binary.

`Obad` is quantified rather than exhibited, because the tree carries no
concrete image for which `Run.valid_entry` is empty at a valid input —
`Run.valid_sp` and `Run.valid_mmap_base` do not depend on the image, and
`Equivalence.image_brk_satisfiable_entry` inhabits the rest for a
well-formed one.  The hypothesis is exactly
`Classifier.error_free_input_vacuous_no_entries`'s.

WHICH IMAGE THE HOLE IS IN is the point of stating this here at all.
`Classifier.accepts_vacuous_no_entries` and
`Classifier.decides_vacuous_no_entries` are about the GATE failing to
load; this survives a gate that is perfectly well-formed and doing its job
correctly.  A checker that ascribed `Equivalence.IMAGE_WF` to its gate
images and forgot the original would be pinning exactly this.  Rocq:
`ErrorFreeInput.unloadable_original_makes_the_gate_accept_everything`. -/
theorem unloadable_original_makes_the_gate_accept_everything (Obad C : Image)
    (hdec : classifies_error_free_inputs_T Obad C)
    (hno : ∀ f en, ¬ valid_entry Obad en (to_proc_input f)) :
    ∀ f, valid_fin_input f → accepts C f :=
  classifies_error_free_inputs_T_vacuous_accepts_everything Obad C hdec hno

/-- ... including at the one input this file computes on, which is where
the route costs something.  A checker looking at two submitted originals
that both fail to do anything — one that traps on its first instruction,
one that does not load — would call those the same failure.  The gate is
forced to REFUSE this input for the first
(`gate_for_undecodable_original_rejects`) and forced to ACCEPT it for the
second, so the two get OPPOSITE verdicts and the second is the one that
costs the checker the whole partition.  Rocq:
`ErrorFreeInput.unloadable_original_flips_the_refusal`. -/
theorem unloadable_original_flips_the_refusal (Obad C : Image)
    (hdec : classifies_error_free_inputs_T Obad C)
    (hno : ∀ f en, ¬ valid_entry Obad en (to_proc_input f)) :
    accepts C efi_demo_fin :=
  unloadable_original_makes_the_gate_accept_everything Obad C hdec hno efi_demo_fin
    efi_demo_fin_valid

/-! ## PART 4 — the same two answers, under the configuration layer -/

/-- The undecodable image is uncovered under EVERY configuration, not just
under may-fail.  Turning a spurious-failure family off removes executions
(`Run.run_scfg_sub_unmodeled` runs the other way), so nothing carries an
uncovered point down from the may-fail run for free — but nothing has to
here, because this image is unmodeled at its FIRST FETCH, before any
syscall and so before any family can fire.  The witness is the empty
`Run.star_cfg`, which exists at every `cfg` by `Run.star_cfg_refl`.

This is the one fact Part 1 does not already give under a configuration;
the accepting side is inherited, below.  Rocq:
`ErrorFreeInput.undecodable_unmodeled_scfg`.  Its unconfigured companion
is `Checks.Cases.EquivalenceDefinition.Equivalence.undecodable_run_unmodeled`,
and this proof is that one with `Run.star_cfg_refl` in place of
`Run.star_refl`: `Run.unmodeled_at` is the same predicate in both. -/
theorem undecodable_unmodeled_scfg (cfg : SpuriousCfg) :
    (run_scfg cfg undecodable_image source_alloc_limit demo_entry
      efi_demo_input).bh_unmodeled := by
  have hun : unmodeled_at undecodable_image.img_segments
      (init_config undecodable_image.img_segments undecodable_image.img_init_pc
        undecodable_image.img_phdrs demo_entry.en_sp demo_entry.en_brk
        demo_entry.en_mmap_base demo_entry.en_draw source_alloc_limit efi_demo_input) := by
    refine ⟨rfl, Or.inl ⟨rfl, ?_⟩⟩
    rw [mi_account_step_no_lazy _ _ _ rfl]
    rw [step_of_fetch _ _ 0xffffffff (by
      change RiscvSemantics.fetch_word undecodable_segments 0x100 = some 0xffffffff
      decide +kernel)]
    rfl
  exact ⟨[], _, star_cfg.star_cfg_refl .., hun⟩

/-- THE BUGGY REGION, under every configuration.  Leaving the modeled
surface is a special case of erroring at each `cfg` too
(`Run.run_scfg_unmodeled_errors`), so the undecodable original is outside
the not-buggy region however the task configured its families.  Rocq:
`ErrorFreeInput.undecodable_not_error_free_input_s`. -/
theorem undecodable_not_error_free_input_s (cfg : SpuriousCfg) :
    ¬ error_free_input_s cfg undecodable_image efi_demo_input :=
  error_free_input_s_refuted_by_error cfg _ _ demo_entry efi_undecodable_entry
    (run_scfg_unmodeled_errors _ _ _ _ _ (undecodable_unmodeled_scfg cfg))

/-- THE NOT-BUGGY REGION, under every configuration, and this half is
inherited rather than recomputed: fewer executions cannot add an error,
which is `Classifier.error_free_input_s_of_error_free_input`.  So the
exit-0 original stays not-buggy at every `cfg`, and the two images are
separated under every configuration, not only under may-fail.  Rocq:
`ErrorFreeInput.exit0_error_free_input_s`. -/
theorem exit0_error_free_input_s (cfg : SpuriousCfg) :
    error_free_input_s cfg exit0_image efi_demo_input :=
  error_free_input_s_of_error_free_input cfg exit0_image efi_demo_input
    exit0_error_free_input

/-- Rocq: `ErrorFreeInput.error_free_input_s_separates_the_two_images`. -/
theorem error_free_input_s_separates_the_two_images (cfg : SpuriousCfg) :
    error_free_input_s cfg exit0_image efi_demo_input
    ∧ ¬ error_free_input_s cfg undecodable_image efi_demo_input :=
  ⟨exit0_error_free_input_s cfg, undecodable_not_error_free_input_s cfg⟩

/-- What that obliges a CONFIGURED gate to do, at every configuration: exit
1 on this input for the undecodable original, at every valid entry of its
own, with the gate's own run pinned to `Run.forced_only_cfg` the way
`Classifier.classifies_error_free_inputs_T_s` pins it.  The gate is
quantified, as in Part 2 and for the same reason.  Rocq:
`ErrorFreeInput.gate_s_for_undecodable_original_must_exit_one`. -/
theorem gate_s_for_undecodable_original_must_exit_one (cfg : SpuriousCfg) (C : Image)
    (enC : ExecEntry)
    (hdec : classifies_error_free_inputs_T_s cfg undecodable_image C)
    (henC : valid_entry C enC (to_proc_input efi_demo_fin)) :
    must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit enC
      (to_proc_input efi_demo_fin) := by
  refine classifies_error_free_inputs_T_s_rejects_error cfg undecodable_image C efi_demo_fin
    demo_entry enC hdec efi_demo_fin_valid ?_ ?_ henC
  · rw [efi_demo_to_proc_input]; exact efi_undecodable_entry
  · rw [efi_demo_to_proc_input]
    exact run_scfg_unmodeled_errors _ _ _ _ _ (undecodable_unmodeled_scfg cfg)

/-- ... and the accepting half, for the exit-0 original.  Rocq:
`ErrorFreeInput.gate_s_for_exit0_original_accepts`. -/
theorem gate_s_for_exit0_original_accepts (cfg : SpuriousCfg) (C : Image)
    (hdec : classifies_error_free_inputs_T_s cfg exit0_image C) :
    accepts_fo C efi_demo_fin := by
  refine classifies_error_free_inputs_T_s_accepts_error_free cfg exit0_image C efi_demo_fin
    hdec efi_demo_fin_valid ?_
  rw [efi_demo_to_proc_input]
  exact exit0_error_free_input_s cfg

/-- ... and the separation survives: no image is a correct configured gate
for both originals, at any configuration.  Part 2's statement with the
whole configuration layer underneath it, and the same valid-entry
hypothesis for the same reason — `Classifier.decides_fo_vacuous_no_entries`
hands both hypotheses to an unloadable gate for free.  Rocq:
`ErrorFreeInput.no_gate_s_serves_both_originals`. -/
theorem no_gate_s_serves_both_originals (cfg : SpuriousCfg) (C : Image) (enC : ExecEntry)
    (henC : valid_entry C enC (to_proc_input efi_demo_fin))
    (hbad : classifies_error_free_inputs_T_s cfg undecodable_image C)
    (hgood : classifies_error_free_inputs_T_s cfg exit0_image C) : False :=
  verdict_accept_neq_reject
    (must_exit_with_scfg_exclusive _ _ _ _ _ _ _
      (gate_s_for_exit0_original_accepts cfg C hgood enC henC)
      (gate_s_for_undecodable_original_must_exit_one cfg C enC hbad henC))

/-- The `_fo` name carries the same three facts, and they are the
`Run.may_fail_cfg` instances of the three above through
`Classifier.classifies_error_free_inputs_T_fo_iff_s_may_fail`.  Stated
under that name because the `_fo` form is one a checker emits, so a reader
checking what it obliges should not have to find the rewrite.  Rocq:
`ErrorFreeInput.gate_fo_for_undecodable_original_must_exit_one`. -/
theorem gate_fo_for_undecodable_original_must_exit_one (C : Image) (enC : ExecEntry)
    (hdec : classifies_error_free_inputs_T_fo undecodable_image C)
    (henC : valid_entry C enC (to_proc_input efi_demo_fin)) :
    must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit enC
      (to_proc_input efi_demo_fin) :=
  gate_s_for_undecodable_original_must_exit_one may_fail_cfg C enC
    ((classifies_error_free_inputs_T_fo_iff_s_may_fail _ C).mp hdec) henC

/-- Rocq: `ErrorFreeInput.gate_fo_for_exit0_original_accepts`. -/
theorem gate_fo_for_exit0_original_accepts (C : Image)
    (hdec : classifies_error_free_inputs_T_fo exit0_image C) :
    accepts_fo C efi_demo_fin :=
  gate_s_for_exit0_original_accepts may_fail_cfg C
    ((classifies_error_free_inputs_T_fo_iff_s_may_fail _ C).mp hdec)

/-- Rocq: `ErrorFreeInput.no_gate_fo_serves_both_originals`. -/
theorem no_gate_fo_serves_both_originals (C : Image) (enC : ExecEntry)
    (henC : valid_entry C enC (to_proc_input efi_demo_fin))
    (hbad : classifies_error_free_inputs_T_fo undecodable_image C)
    (hgood : classifies_error_free_inputs_T_fo exit0_image C) : False :=
  no_gate_s_serves_both_originals may_fail_cfg C enC henC
    ((classifies_error_free_inputs_T_fo_iff_s_may_fail _ C).mp hbad)
    ((classifies_error_free_inputs_T_fo_iff_s_may_fail _ C).mp hgood)

#print axioms exit0_error_free_input
#print axioms undecodable_not_error_free_input
#print axioms no_gate_serves_both_originals
#print axioms no_gate_fo_serves_both_originals

end LinuxProcessSemantics.LinuxProcessSem.Checks.ErrorFreeInput
