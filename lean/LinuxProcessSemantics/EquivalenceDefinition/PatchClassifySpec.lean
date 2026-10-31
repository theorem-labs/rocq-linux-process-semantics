-- Ports rocq-linux-process-semantics f1006fe8:theories/EquivalenceDefinition/PatchClassifySpec.v
import LinuxProcessSemantics.EquivalenceDefinition.Measure

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058 -/

/-! # EquivalenceDefinition.PatchClassifySpec — the sealed surface of a patch-plus-classifier submission

Mirrors `theories/EquivalenceDefinition/PatchClassifySpec.v`.

TRUST BOUNDARY: this file is part of the trusted specification.  A check
that ascribes one of the surfaces below depends on the definitions here,
and on everything they name, staying fixed, exactly as a baseline check
depends on `Equivalence`.

`Equivalence.SPEC` seals a submission that answers ONE question about TWO
binaries: are they observably equivalent.  This file seals a submission
that answers three questions about SIX, and it is the packaging alone: it
defines nothing of its own, and every obligation it states is a definition
of `Equivalence`, `Classifier` or `Measure` applied to the submission's
images.  A sealed surface is the right shape for the job for the reason
`Equivalence.SPEC` gives: the submission's proofs are ascribed to it, so a
proof of a DIFFERENT statement — another image, a weakened predicate, a
bound about some other classifier — fails the ascription instead of
passing unnoticed.

## The six images and what each is asked

Two originals, `O1` and `O2`, are given to the submission; the submission
produces the other four.

* `P1` and `P2` are the patched builds of the two originals, and the
  equivalence obligation is BETWEEN THE TWO PATCHES, not between a patch
  and its own original.  That is the point of the exercise: the originals
  are not equivalent to each other, which is the defect, and the
  submission must repair both so that the pair becomes equivalent, each
  role at its own allocation budget (`State.source_alloc_limit` for the
  first and `State.target_alloc_limit` for the second, as
  `Equivalence.strong_equiv` pins them).
* `C1` is the PATCH-DIFFERENCE classifier: on a finite input it exits 0
  exactly when both patches preserved their original's behaviour, and 1
  when either changed it.  The conjunction inside
  `Classifier.classifies_patch_diff_T` is a union scope, so the classifier
  fires if EITHER pair differs.
* `C2` is the GOOD-INPUT classifier: on a finite input it exits 0 exactly
  when the two ORIGINALS were already error-free equivalent there, which
  is what `Classifier.good_input` says at all entry pairs.

Both classifier obligations are TOTAL DECISION statements, not acceptance
statements: `Classifier.decides` asks for a verdict — all executions exit
0, or all exit 1 — at every valid entry of every valid finite input.
`Classifier`'s header argues each of the three restrictions in that
sentence (finite inputs, per entry, total); none of them is weakened here.

## `b1` and `b2` are chosen by the submission and READ, never compared

The two bounds come from the submission together with their proofs;
nothing here or below dictates a value.  A check that wants to show a
reader what was proved PRINTS a bound rather than comparing it against an
expected one, for the reason `Measure`'s header gives.
`Measure.weight_bound_mono` says a proof at `b` is a proof at every larger
`b'`, so a printed bound is an UPPER BOUND claim rather than a
measurement, and `Measure.weight_bound_qeq` transports the claim between
equal values of `M` and of `b`, so a reader may compare a bound with a
threshold of their own in whichever representation they like.

## `Equivalence.IMAGE_WF` for ALL SIX images is the check's job

Every obligation below quantifies over valid execution entries, so an
image for which no `Run.valid_entry` exists satisfies all of them with
nothing established about anything.  A consuming check ascribes
`Equivalence.IMAGE_WF` per image for that reason; here the same ascription
is needed SIX times, and the two for the classifiers are the ones easiest
to forget and worst to omit.  Two lemmas say why.
`Classifier.decides_vacuous_no_entries`: an image with no valid entry
DECIDES EVERY property, contradictory ones included, so `classifies_diff`
and `classifies_good` would both hold of a classifier that is not a
program.  `Classifier.accepts_vacuous_no_entries`: the same image ACCEPTS
EVERY INPUT, which empties `Classifier.rejects` and makes
`Measure.weight_bound_T` hold at `b = 0`, and so, by
`Measure.weight_bound_mono`, at every `b`, for any weight function and any
declared total.  A check that pinned the classifier statements and the
bounds but skipped the classifier images' well-formedness would have
pinned two theorems and two numbers, all four free.

Nothing in the structures below requires those proofs, so the guard is a
convention of the consuming check.  The Rocq file names the alternative
and leaves it unbuilt: take the six well-formedness proofs as further
arguments, so that nothing can be ascribed without supplying them.  What
that costs is that the six proofs have to exist before anything can be
ascribed at all — an obligation on a task author, not only on a
submission — and that every ascription has to follow the changed arity.

## `W` is trusted metadata, not an obligation

`Measure.Distribution` carries the weight function and the declared total.
Both are per-problem metadata supplied with the task, never proved by the
submission, and the structure's own proof obligations are about them
rather than about any submission: the weight and the total are
nonnegative, and `w_core_blind` says the weight does not depend on the
launch environment, which is what makes the per-core charge in
`Measure.weight_bound_T` well defined.  The bounds below are claims about
the submission's classifiers RELATIVE to that declared pair; they say
nothing about whether `W.M` is really the total mass of anything, and no
obligation ties it to 1.

## What "fire set" denotes here

A set of CORES, not of records.  `Measure.weight_bound_T` is indexed by
`FinInput.fin_core` — argv, envp, the file system and standard input — so
a core counts once however many launch environments
(`FinInput.fin_uid`, `fin_gid`, `fin_groups`, `fin_net`) it is offered
under, and it counts as soon as ANY of them is rejected.  A task author
sizing a distribution therefore weighs cores, and
`Measure.Distribution.w_core_blind` is the obligation that keeps a weight
from disagreeing with that reading.

## The Lean shape of the sealed surface

Rocq states each surface as a module type over functor arguments
(`MemImage`, `SPURIOUS_CFG`, `DISTRIBUTION`).  Lean has no module types,
so each `SPEC_PATCH_CLASSIFY*` below is a structure over the same data
passed explicitly, the way `Equivalence/Base.lean`'s `SPEC` takes its two
images: six `MemImageType.Image`s, a `Run.SpuriousCfg` where Rocq takes
`Cfg`, and a `Measure.Distribution` where Rocq takes `W`.  Rocq's `Q` is
`Rat`, as in `Measure`.

These structures are NOT `Prop`-valued, unlike `Equivalence.SPEC` and the
other sealed surfaces of this tree, because `b1` and `b2` carry data.
Lean refuses to project a non-proof field of a `Prop`-valued structure
("failed to generate projection `S.b1` for the 'Prop'-valued type `S`,
field must be a proof, but it has type Rat", Lean 4.34.0), and the two
bounds have to be projectable: they are what a check reads off the
submission.  The alternative — the bounds as further arguments of a
`Prop`-valued structure — moves them out of the submission's record and
into the statement the check writes down, which reverses who picks them,
so it is not taken.  Every other field is a proposition, and each one is
its Rocq `Parameter` unchanged. -/

namespace LinuxProcessSemantics.EquivalenceDefinition.PatchClassifySpec

open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.Classifier
open LinuxProcessSemantics.EquivalenceDefinition.Measure

/-! ## The baseline surface -/

/-- The whole submission surface, in six obligations: the patched pair is
observably equivalent, each classifier decides its question on finite
inputs, and each classifier's fire set weighs at most its stated multiple
of the declared total.  `strong_universal` is quantified over ALL valid
inputs, infinite ones included; only the two classifier obligations
restrict to finite inputs. -/
structure SPEC_PATCH_CLASSIFY (O1 P1 O2 P2 C1 C2 : Image) (W : Distribution) where
  /-- The two patched binaries are observably equivalent, at every valid
  entry pair and on every valid input. -/
  strong_universal : strong_universal_T P1 P2
  /-- `C1` decides, on finite inputs, whether BOTH patches preserved
  their original's behaviour. -/
  classifies_diff : classifies_patch_diff_T O1 P1 O2 P2 C1
  /-- `C2` decides, on finite inputs, whether the two ORIGINALS were
  already error-free equivalent. -/
  classifies_good : classifies_good_inputs_T O1 O2 C2
  /-- The bound claimed for the patch-difference classifier, chosen by
  the submission and read by printing — see this file's header. -/
  b1 : Rat
  /-- The bound claimed for the good-input classifier, the same way. -/
  b2 : Rat
  /-- `C1`'s fire set weighs no more than `b1` times the declared total,
  measured by `W` — the fire set being a set of CORES, charged once each,
  per this file's header and `Measure.weight_bound_T`. -/
  bound_diff : weight_bound_T C1 W.w W.M b1
  /-- `C2`'s fire set weighs no more than `b2` times the declared total,
  the same way. -/
  bound_good : weight_bound_T C2 W.w W.M b2

/-- The same surface with the patch obligation replaced by
`Equivalence.strong_universal_error_free_T`: the two patched binaries must
also never reach the error transition, on any input, at any valid entry.

A SEPARATE surface rather than an extension, for the reason
`Equivalence.SPEC_ERROR_FREE` gives: the stronger reading is unprovable
for a binary that may legitimately crash, so a task OPTS IN to it.  What a
task gets by opting in is the stronger patch statement and a sharper
classifier question as well — with both patches error-free, an input on
which `Classifier.agree` fails can no longer fail because both sides
crashed the same way.  Nothing is lost by the substitution:
`Equivalence.strong_universal_error_free_implies` discharges the baseline
obligation from this one, so a submission sealed here also satisfies
`SPEC_PATCH_CLASSIFY` on the same six images.

The other five obligations are unchanged, deliberately.  The classifiers
are asked the same questions — `Classifier.good_input` is already the
error-free comparison of the two originals, whichever flavour the patch
obligation takes — and the measure layer never sees the difference. -/
structure SPEC_PATCH_CLASSIFY_ERROR_FREE (O1 P1 O2 P2 C1 C2 : Image) (W : Distribution) where
  /-- The two patched binaries are error-free AND observably equivalent. -/
  strong_universal_error_free : strong_universal_error_free_T P1 P2
  /-- `C1` decides, on finite inputs, whether both patches preserved
  their original's behaviour. -/
  classifies_diff : classifies_patch_diff_T O1 P1 O2 P2 C1
  /-- `C2` decides, on finite inputs, whether the two originals were
  already error-free equivalent. -/
  classifies_good : classifies_good_inputs_T O1 O2 C2
  /-- The bound claimed for the patch-difference classifier. -/
  b1 : Rat
  /-- The bound claimed for the good-input classifier. -/
  b2 : Rat
  /-- `C1`'s fire set weighs no more than `b1` times the declared total. -/
  bound_diff : weight_bound_T C1 W.w W.M b1
  /-- `C2`'s fire set weighs no more than `b2` times the declared total. -/
  bound_good : weight_bound_T C2 W.w W.M b2

/-! ## The same surfaces under a spurious-failure configuration -/

/-- The six-image surface with the task's configuration `cfg` passed
explicitly, the way `Equivalence.strong_universal_T_scfg` and
`HaltsAllowed.SPEC_HALTS_ALLOWED_SCFG` take it, and with the two
readings the classifier layer keeps apart:

* the patch obligation and the classified properties are under the TASK'S
  configuration (`Equivalence.strong_universal_T_scfg`,
  `Classifier.classifies_patch_diff_T_s`,
  `Classifier.classifies_good_inputs_T_s`);
* the two classifiers' OWN runs are pinned to forced-only, for every
  family, whatever `cfg` says — the `_fo` inside those two definitions,
  and `Measure.weight_bound_T_fo` for the bounds.

At `Run.may_fail_cfg` the patch obligation and the classified properties
are the ones `SPEC_PATCH_CLASSIFY` states
(`Equivalence.strong_universal_T_scfg_may_fail`,
`Classifier.agree_s_may_fail`, `Classifier.good_input_s_may_fail`); what
differs is the classifier pin, which is a weakening of the verdict
obligation (`Classifier.decides_fo_of_decides`).  Everything this file's
header says applies unchanged. -/
structure SPEC_PATCH_CLASSIFY_SCFG (cfg : SpuriousCfg) (O1 P1 O2 P2 C1 C2 : Image)
    (W : Distribution) where
  /-- The two patched binaries are observably equivalent under the task's
  configuration. -/
  strong_universal : strong_universal_T_scfg cfg P1 P2
  /-- `C1`, run forced-only, decides the configured agreement of both
  original/patched pairs. -/
  classifies_diff : classifies_patch_diff_T_s cfg O1 P1 O2 P2 C1
  /-- `C2`, run forced-only, decides configured goodness of the two
  originals. -/
  classifies_good : classifies_good_inputs_T_s cfg O1 O2 C2
  /-- The bound claimed for the patch-difference classifier. -/
  b1 : Rat
  /-- The bound claimed for the good-input classifier. -/
  b2 : Rat
  /-- `C1`'s forced-only fire set weighs no more than `b1` times the
  declared total. -/
  bound_diff : weight_bound_T_fo C1 W.w W.M b1
  /-- `C2`'s forced-only fire set weighs no more than `b2` times the
  declared total. -/
  bound_good : weight_bound_T_fo C2 W.w W.M b2

/-- The error-free flavour, with the substitution
`SPEC_PATCH_CLASSIFY_ERROR_FREE` makes and the same classifier pin. -/
structure SPEC_PATCH_CLASSIFY_SCFG_ERROR_FREE (cfg : SpuriousCfg) (O1 P1 O2 P2 C1 C2 : Image)
    (W : Distribution) where
  /-- The two patched binaries are error-free AND observably equivalent
  under the task's configuration. -/
  strong_universal_error_free : strong_universal_error_free_T_scfg cfg P1 P2
  /-- `C1`, run forced-only, decides the configured agreement of both
  original/patched pairs. -/
  classifies_diff : classifies_patch_diff_T_s cfg O1 P1 O2 P2 C1
  /-- `C2`, run forced-only, decides configured goodness of the two
  originals. -/
  classifies_good : classifies_good_inputs_T_s cfg O1 O2 C2
  /-- The bound claimed for the patch-difference classifier. -/
  b1 : Rat
  /-- The bound claimed for the good-input classifier. -/
  b2 : Rat
  /-- `C1`'s forced-only fire set weighs no more than `b1` times the
  declared total. -/
  bound_diff : weight_bound_T_fo C1 W.w W.M b1
  /-- `C2`'s forced-only fire set weighs no more than `b2` times the
  declared total. -/
  bound_good : weight_bound_T_fo C2 W.w W.M b2

/-! ## The same two surfaces with the CLASSIFIERS' AT_HWCAP word declared

The classifier binaries take the same vector probe as the binaries they
classify.  A classifier that reads `vlenb` to learn whether it has a
vector unit executes, under an advertised V, a word the model declines, so
its run is `Run.MachineUnmodeled`, no `MustExit.must_exit_with_scfg` holds
of it, and `Classifier.decides_fo` is FALSE for it — on every input,
whatever the classifier would otherwise answer.  The four surfaces below
are how a task with such a classifier states what it can prove: the
verdict obligations are the declared ones, and
`Classifier.classifies_patch_diff_T_s_hwcap_splits` says the undeclared
surfaces above are the conjunction of each pair.

WHAT IS NOT DECLARED HERE, deliberately.  The PATCH obligation
(`Equivalence.strong_universal_T_scfg`) and the weight bounds stay the
undeclared ones: what these surfaces declare is about the CLASSIFIER'S
hart, which is the binary whose probe is at issue.  A task whose PATCH
pair also probes states that separately, through the equivalence layer's
own declared surfaces (`Equivalence.SPEC_HWCAP_RV64GC` and its three
siblings), and the day a surface needs both halves declared at once
it is written the way these are. -/

/-- The configured surface with the classifiers' obligations declared at
RV64GC. -/
structure SPEC_PATCH_CLASSIFY_SCFG_HWCAP_RV64GC (cfg : SpuriousCfg) (O1 P1 O2 P2 C1 C2 : Image)
    (W : Distribution) where
  /-- The undeclared patch obligation, under the task's configuration. -/
  strong_universal : strong_universal_T_scfg cfg P1 P2
  /-- `C1`, run forced-only, decides the configured agreement of both
  pairs on inputs declaring RV64GC. -/
  classifies_diff : classifies_patch_diff_T_s_hwcap_rv64gc cfg O1 P1 O2 P2 C1
  /-- `C2`, run forced-only, decides configured goodness on inputs
  declaring RV64GC. -/
  classifies_good : classifies_good_inputs_T_s_hwcap_rv64gc cfg O1 O2 C2
  /-- The bound claimed for the patch-difference classifier. -/
  b1 : Rat
  /-- The bound claimed for the good-input classifier. -/
  b2 : Rat
  /-- `C1`'s forced-only fire set weighs no more than `b1` times the
  declared total; the bound is the undeclared one. -/
  bound_diff : weight_bound_T_fo C1 W.w W.M b1
  /-- `C2`'s forced-only fire set weighs no more than `b2` times the
  declared total; the bound is the undeclared one. -/
  bound_good : weight_bound_T_fo C2 W.w W.M b2

/-- The configured surface with the classifiers' obligations declared at
RV64GCV. -/
structure SPEC_PATCH_CLASSIFY_SCFG_HWCAP_RV64GCV (cfg : SpuriousCfg) (O1 P1 O2 P2 C1 C2 : Image)
    (W : Distribution) where
  /-- The undeclared patch obligation, under the task's configuration. -/
  strong_universal : strong_universal_T_scfg cfg P1 P2
  /-- `C1`, run forced-only, decides the configured agreement of both
  pairs on inputs declaring RV64GCV. -/
  classifies_diff : classifies_patch_diff_T_s_hwcap_rv64gcv cfg O1 P1 O2 P2 C1
  /-- `C2`, run forced-only, decides configured goodness on inputs
  declaring RV64GCV. -/
  classifies_good : classifies_good_inputs_T_s_hwcap_rv64gcv cfg O1 O2 C2
  /-- The bound claimed for the patch-difference classifier. -/
  b1 : Rat
  /-- The bound claimed for the good-input classifier. -/
  b2 : Rat
  /-- `C1`'s forced-only fire set weighs no more than `b1` times the
  declared total; the bound is the undeclared one. -/
  bound_diff : weight_bound_T_fo C1 W.w W.M b1
  /-- `C2`'s forced-only fire set weighs no more than `b2` times the
  declared total; the bound is the undeclared one. -/
  bound_good : weight_bound_T_fo C2 W.w W.M b2

/-- The error-free flavour at RV64GC, the same substitution again. -/
structure SPEC_PATCH_CLASSIFY_SCFG_ERROR_FREE_HWCAP_RV64GC (cfg : SpuriousCfg)
    (O1 P1 O2 P2 C1 C2 : Image) (W : Distribution) where
  /-- The undeclared error-free patch obligation, under the task's
  configuration. -/
  strong_universal_error_free : strong_universal_error_free_T_scfg cfg P1 P2
  /-- `C1`, run forced-only, decides the configured agreement of both
  pairs on inputs declaring RV64GC. -/
  classifies_diff : classifies_patch_diff_T_s_hwcap_rv64gc cfg O1 P1 O2 P2 C1
  /-- `C2`, run forced-only, decides configured goodness on inputs
  declaring RV64GC. -/
  classifies_good : classifies_good_inputs_T_s_hwcap_rv64gc cfg O1 O2 C2
  /-- The bound claimed for the patch-difference classifier. -/
  b1 : Rat
  /-- The bound claimed for the good-input classifier. -/
  b2 : Rat
  /-- `C1`'s forced-only fire set weighs no more than `b1` times the
  declared total; the bound is the undeclared one. -/
  bound_diff : weight_bound_T_fo C1 W.w W.M b1
  /-- `C2`'s forced-only fire set weighs no more than `b2` times the
  declared total; the bound is the undeclared one. -/
  bound_good : weight_bound_T_fo C2 W.w W.M b2

/-- The error-free flavour at RV64GCV, the same substitution again. -/
structure SPEC_PATCH_CLASSIFY_SCFG_ERROR_FREE_HWCAP_RV64GCV (cfg : SpuriousCfg)
    (O1 P1 O2 P2 C1 C2 : Image) (W : Distribution) where
  /-- The undeclared error-free patch obligation, under the task's
  configuration. -/
  strong_universal_error_free : strong_universal_error_free_T_scfg cfg P1 P2
  /-- `C1`, run forced-only, decides the configured agreement of both
  pairs on inputs declaring RV64GCV. -/
  classifies_diff : classifies_patch_diff_T_s_hwcap_rv64gcv cfg O1 P1 O2 P2 C1
  /-- `C2`, run forced-only, decides configured goodness on inputs
  declaring RV64GCV. -/
  classifies_good : classifies_good_inputs_T_s_hwcap_rv64gcv cfg O1 O2 C2
  /-- The bound claimed for the patch-difference classifier. -/
  b1 : Rat
  /-- The bound claimed for the good-input classifier. -/
  b2 : Rat
  /-- `C1`'s forced-only fire set weighs no more than `b1` times the
  declared total; the bound is the undeclared one. -/
  bound_diff : weight_bound_T_fo C1 W.w W.M b1
  /-- `C2`'s forced-only fire set weighs no more than `b2` times the
  declared total; the bound is the undeclared one. -/
  bound_good : weight_bound_T_fo C2 W.w W.M b2

end LinuxProcessSemantics.EquivalenceDefinition.PatchClassifySpec
