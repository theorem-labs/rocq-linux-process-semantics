-- Ports oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:theories/Shapes.v
-- over rocq-linux-process-semantics f1006fe8's Lean twin.
import LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed
import OssFuzzTheorems.Core.Images

/-! # OssFuzzTheorems.Core.Shapes: what every statement in this collection says

The Lean twin of `theories/Shapes.v` of theorem-labs/oss-verify-proofs-internal
(`origin/ossv/recipes` `9b0ac6f0e6780f75e0353041e71b055f15384ff0`), stated over
the Lean twin of the Rocq model the released statements pin
(rocq-linux-process-semantics `f1006fe8`).

Every statement in oss-fuzz-theorems is one of the definitions below, applied to
the memory images of specific binaries. Each is written out in full. Each
agreement and halting shape is proved EQUAL, by `rfl`, to the definition in
linux-process-semantics it corresponds to, so what you read here is exactly what
the model means and the model's documentation applies unchanged.

Vocabulary (all from the model):
- IMAGE (`MemImageType.Image`): what the Linux loader maps from a static riscv64
  ELF file: its loadable segments, entry point and program-header location.
- ENTRY (`Run.ExecEntry`): what the kernel chooses at execve and the program does
  not control: stack top, program break, mmap base, the AT_RANDOM bytes.
  Statements quantify over every valid entry, independently for each build.
- INPUT (`State.ProcInput`): everything the environment supplies: argv, envp, the
  starting file system (so the input file, its contents or its absence), stdin,
  user and group ids, network peers, limits, the advertised machine
  capabilities. `Run.valid_input` is the model's set of realistic inputs for a
  riscv64 Linux process with a 48-bit address space.
- RUN (`Run.run img lim en inp`): the process's behaviour with `lim` bytes of
  memory it may allocate.
- ERROR: a step the model does not take, or a fault it treats as one.
- ENVIRONMENT FAILURES (`Run.SpuriousCfg`): which system calls may fail even
  though the process's state does not force them to. See `Env`.

Nothing in this file is assumed: it declares no axiom and leaves no proof
unfinished.

## What this file does NOT port, and why

- `theories/Shapes.v`'s shapes 3 and 4 — `disagrees_at_most`, `classifies`,
  `classifier_rejects_at_most`, `agreement_decidable` and their `_rv64gc`
  variants. They rest on `EquivalenceDefinition.Classifier.good_input_s` and
  `weight_bound_T_fo`, which the Lean model does not carry at
  `ff0313ba4f2e9baffcf5b5f50bc9d31628ae8556`, and no statement of
  `libreac/fuzz_knock` has those shapes (its nine are four `_halts`, two
  `_halts_may_fail` and three `_agrees`). OSSV-265 gaps row K1-1.
- `Budgets.Standard` and `Budgets.Asan` are Rocq's `Equivalence.ShippedBudgets`
  and `SanitizerBudgets`, two instance modules of the `BUDGETS` module type.
  Lean has no module types and the port registers all three as `unported`
  (`EquivalenceDefinition/Equivalence/Budgets.lean:6-8,14-16`), so each member
  is spelled as the constant Rocq's module defines, with a theorem pinning it to
  the model's own constant where one exists. The values are the Rocq ones.
  OSSV-265 gaps row K1-2. -/

namespace OssFuzzTheorems.Core.Shapes

open LinuxProcessSemantics.Riscv.Prelude (word)
open LinuxProcessSemantics.LinuxProcessSem.MemImageType (Image)
open LinuxProcessSemantics.LinuxProcessSem.State
  (ProcInput source_alloc_limit target_alloc_limit)
open LinuxProcessSemantics.LinuxProcessSem.Run
  (SpuriousCfg ExecEntry valid_entry valid_input valid_input_abort
   valid_input_hwcap_rv64gc valid_input_abort_hwcap_rv64gc
   may_fail_cfg forced_only_cfg alloc_only_cfg
   run run_scfg run_budget_refused run_scfg_budget_refused)
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.MustExit (must_exit_in_scfg must_exit_in_scfg_mono_set)
open LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed
  (halts_allowed_T_scfg halts_allowed_T_scfg_budgets halts_allowed_T_scfg_mono_set)
open LinuxProcessSemantics.Riscv.Prelude (Z_to_bv)

/-! ## Parameters -/

/-! Memory budgets in bytes, for the plain build and the sanitizer build
(`theories/Shapes.v:54-66`). -/
namespace Budgets

/-! Rocq's `Equivalence.ShippedBudgets`: 16 GiB for the plain build, 512 GiB for
the sanitizer build. -/
namespace Standard
def lim_source : Int := 0x400000000
def lim_target : Int := 0x8000000000

/-- The members are the model's own constants, which is what Rocq's instance
module defines them as. -/
theorem lim_source_eq : lim_source = source_alloc_limit := rfl
theorem lim_target_eq : lim_target = target_alloc_limit := rfl
end Standard

/-! Rocq's `Equivalence.SanitizerBudgets`: 2 GiB for the plain build, 512 GiB
for the sanitizer build, used when the sanitizer build includes
AddressSanitizer, whose allocator caps each size class well below 16 GiB. -/
namespace Asan
def lim_source : Int := 0x80000000
def lim_target : Int := 0x8000000000

theorem lim_target_eq : lim_target = target_alloc_limit := rfl
end Asan

end Budgets

/-- `theories/Shapes.v:68-71`. -/
theorem standard_budgets :
    Budgets.Standard.lim_source = 0x400000000 ∧ Budgets.Standard.lim_target = 0x8000000000 :=
  ⟨rfl, rfl⟩

/-- `theories/Shapes.v:73-76`. -/
theorem asan_budgets :
    Budgets.Asan.lim_source = 0x80000000 ∧ Budgets.Asan.lim_target = 0x8000000000 :=
  ⟨rfl, rfl⟩

/-! How much the environment may refuse (`theories/Shapes.v:79-89`). -/
namespace Env
/-- Any system call the model lets fail may fail, at any time: memory, file
system, descriptors, network, credentials, interruption. -/
def may_fail : SpuriousCfg := may_fail_cfg
/-- As `may_fail`, except that a memory request fails only when the budget is
spent or no address range is free. -/
def alloc_forced_only : SpuriousCfg := alloc_only_cfg false
/-- A call fails only where the process's own state forces it to. -/
def forced_only : SpuriousCfg := forced_only_cfg
end Env

/-! The three readings, spelled as the model's six per-family switches (memory
first; `true` means "may fail without cause") (`theories/Shapes.v:91-100`). -/

theorem may_fail_is : Env.may_fail = SpuriousCfg.mkSpuriousCfg true true true true true true := rfl

theorem alloc_forced_only_is :
    Env.alloc_forced_only = SpuriousCfg.mkSpuriousCfg false true true true true true := rfl

theorem forced_only_is :
    Env.forced_only = SpuriousCfg.mkSpuriousCfg false false false false false false := rfl

/-! Sets of allowed exit statuses (`theories/Shapes.v:102-123`). -/
namespace Exits
/-- 0..255: the statement says only that the process exits. Rocq takes it from
`HaltsAllowed.AnyExit.codes`, whose one member is `byte_codes`. -/
def any : List word := LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.byte_codes
/-- 0 (every harness call returned 0 or -1) or 2 (the driver refused the input
file, or ran out of memory, before or instead of calling the harness; in a Rust
fuzz target, also an allocation that failed at any point, which the OSS Verify
port's allocation-error hook ends with one line on standard error).
`docs/running.md` lists the others: 77 (the harness called `exit()`), 78 (a
harness call returned a value other than 0 or -1), 79 (a Rust fuzz target
panicked); an abort, including a failed `assert()` and a sanitizer report, is
not an exit at all. In the driver's counting mode (bit 15 of the config-length
word) a harness binary exits 0 whatever the harness returned. -/
def ok_or_refused : List word := [Z_to_bv 64 0, Z_to_bv 64 2]
end Exits

/-! ## Shape 1: agreement of a sanitizer build with the plain build

`agrees lim_plain lim_san plain san`: for every valid input and every valid pair
of entries, IF the plain build's run is never refused memory for exceeding
`lim_plain`, THEN no execution of either build reaches an error, and the two
builds have exactly the same finite traces. The environment may refuse any call,
in either build (`Env.may_fail`). The budget premise is on the plain build only.
(`theories/Shapes.v:126-145`) -/
def agrees (lim_plain lim_san : Int) (plain san : Image) : Prop :=
  ∀ (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry plain en_plain inp →
    valid_entry san en_san inp →
    valid_input inp →
    ¬ run_budget_refused plain lim_plain en_plain inp →
    error_free (run plain lim_plain en_plain inp)
    ∧ error_free (run san lim_san en_san inp)
    ∧ trace_equiv (run plain lim_plain en_plain inp).bh_traces
                  (run san lim_san en_san inp).bh_traces

theorem agrees_is_lps (lp ls : Int) (p s : Image) :
    agrees lp ls p s = strong_universal_error_free_T_budgets lp ls p s := rfl

/-- `agrees_in env ...`: the same claim when the environment refuses only what
`env` allows (`theories/Shapes.v:147-166`). -/
def agrees_in (env : SpuriousCfg) (lim_plain lim_san : Int) (plain san : Image) : Prop :=
  ∀ (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry plain en_plain inp →
    valid_entry san en_san inp →
    valid_input inp →
    ¬ run_scfg_budget_refused env plain lim_plain en_plain inp →
    error_free (run_scfg env plain lim_plain en_plain inp)
    ∧ error_free (run_scfg env san lim_san en_san inp)
    ∧ trace_equiv (run_scfg env plain lim_plain en_plain inp).bh_traces
                  (run_scfg env san lim_san en_san inp).bh_traces

theorem agrees_in_is_lps (env : SpuriousCfg) (lp ls : Int) (p s : Image) :
    agrees_in env lp ls p s = strong_universal_error_free_T_scfg_budgets env lp ls p s := rfl

/-- `agrees` is `agrees_in Env.may_fail`. They are different terms (one is
stated over `run`, the other over `run_scfg`), so this is an equivalence
(`theories/Shapes.v:168-177`). -/
theorem agrees_iff_agrees_in_may_fail (lp ls : Int) (p s : Image) :
    agrees lp ls p s ↔ agrees_in Env.may_fail lp ls p s :=
  (strong_universal_error_free_T_scfg_budgets_may_fail lp ls p s).symm

/-- `theories/Shapes.v:179-193`: the same claim under the model's other reading
of abort(), in which abort is death by SIGABRT rather than an unmodelled step.
The claim still forbids it: both runs must be error-free AND never killed by a
signal. -/
def agrees_abort_modelled (lim_plain lim_san : Int) (plain san : Image) : Prop :=
  ∀ (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry plain en_plain inp →
    valid_entry san en_san inp →
    valid_input_abort inp →
    ¬ run_budget_refused plain lim_plain en_plain inp →
    error_free_unkilled (run plain lim_plain en_plain inp)
    ∧ error_free_unkilled (run san lim_san en_san inp)
    ∧ trace_equiv (run plain lim_plain en_plain inp).bh_traces
                  (run san lim_san en_san inp).bh_traces

theorem agrees_abort_modelled_is_lps (lp ls : Int) (p s : Image) :
    agrees_abort_modelled lp ls p s = strong_universal_error_free_T_budgets_abort lp ls p s := rfl

/-- `theories/Shapes.v:195-207`. -/
def agrees_in_abort_modelled (env : SpuriousCfg) (lim_plain lim_san : Int)
    (plain san : Image) : Prop :=
  ∀ (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry plain en_plain inp →
    valid_entry san en_san inp →
    valid_input_abort inp →
    ¬ run_scfg_budget_refused env plain lim_plain en_plain inp →
    error_free_unkilled (run_scfg env plain lim_plain en_plain inp)
    ∧ error_free_unkilled (run_scfg env san lim_san en_san inp)
    ∧ trace_equiv (run_scfg env plain lim_plain en_plain inp).bh_traces
                  (run_scfg env san lim_san en_san inp).bh_traces

theorem agrees_in_abort_modelled_is_lps (env : SpuriousCfg) (lp ls : Int) (p s : Image) :
    agrees_in_abort_modelled env lp ls p s
      = strong_universal_error_free_T_scfg_budgets_abort env lp ls p s := rfl

/-! The `_rv64gc` variants, on the inputs whose advertised machine (AT_HWCAP) is
RV64GC, with no vector unit (`theories/Shapes.v:209-253`). -/

def agrees_rv64gc (lim_plain lim_san : Int) (plain san : Image) : Prop :=
  ∀ (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry plain en_plain inp →
    valid_entry san en_san inp →
    valid_input_hwcap_rv64gc inp →
    ¬ run_budget_refused plain lim_plain en_plain inp →
    error_free (run plain lim_plain en_plain inp)
    ∧ error_free (run san lim_san en_san inp)
    ∧ trace_equiv (run plain lim_plain en_plain inp).bh_traces
                  (run san lim_san en_san inp).bh_traces

theorem agrees_rv64gc_is_lps (lp ls : Int) (p s : Image) :
    agrees_rv64gc lp ls p s = strong_universal_error_free_T_budgets_hwcap_rv64gc lp ls p s := rfl

def agrees_abort_modelled_rv64gc (lim_plain lim_san : Int) (plain san : Image) : Prop :=
  ∀ (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry plain en_plain inp →
    valid_entry san en_san inp →
    valid_input_abort_hwcap_rv64gc inp →
    ¬ run_budget_refused plain lim_plain en_plain inp →
    error_free_unkilled (run plain lim_plain en_plain inp)
    ∧ error_free_unkilled (run san lim_san en_san inp)
    ∧ trace_equiv (run plain lim_plain en_plain inp).bh_traces
                  (run san lim_san en_san inp).bh_traces

theorem agrees_abort_modelled_rv64gc_is_lps (lp ls : Int) (p s : Image) :
    agrees_abort_modelled_rv64gc lp ls p s
      = strong_universal_error_free_T_budgets_abort_hwcap_rv64gc lp ls p s := rfl

def agrees_in_rv64gc (env : SpuriousCfg) (lim_plain lim_san : Int) (plain san : Image) : Prop :=
  ∀ (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry plain en_plain inp →
    valid_entry san en_san inp →
    valid_input_hwcap_rv64gc inp →
    ¬ run_scfg_budget_refused env plain lim_plain en_plain inp →
    error_free (run_scfg env plain lim_plain en_plain inp)
    ∧ error_free (run_scfg env san lim_san en_san inp)
    ∧ trace_equiv (run_scfg env plain lim_plain en_plain inp).bh_traces
                  (run_scfg env san lim_san en_san inp).bh_traces

theorem agrees_in_rv64gc_is_lps (env : SpuriousCfg) (lp ls : Int) (p s : Image) :
    agrees_in_rv64gc env lp ls p s
      = strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc env lp ls p s := rfl

/-! ## Shape 2: halting

`halts_within_budget lim allowed img`: on every valid input and entry on which
the run is never refused memory for exceeding `lim`, and when the environment
refuses nothing it is not forced to (`Env.forced_only`), EVERY execution of
`img` ends by calling exit_group with a status in `allowed`. So no execution
runs forever (the predicate is inductive), gets stuck, reaches an error, or dies
by a signal. Nothing is said about output. Under `Env.forced_only` a memory
request is refused only when the budget is spent or no address range is free,
and address-space reservations that are never touched (PROT_NONE, MAP_NORESERVE)
are not charged to the budget. (`theories/Shapes.v:255-287`) -/
def halts_within_budget (lim : Int) (allowed : List word) (img : Image) : Prop :=
  ∀ (en : ExecEntry) (inp : ProcInput),
    valid_entry img en inp →
    valid_input inp →
    ¬ run_scfg_budget_refused forced_only_cfg img lim en inp →
    must_exit_in_scfg forced_only_cfg allowed img lim en inp

theorem halts_within_budget_is_lps (lim : Int) (allowed : List word) (img : Image) :
    halts_within_budget lim allowed img
      = halts_allowed_T_scfg_budgets forced_only_cfg lim allowed img := rfl

/-- `halts_may_fail allowed img`: as above, with no budget premise, whatever the
environment refuses (`Env.may_fail`), at the model's single-binary budget
(16 GiB). Stronger, and false for any build whose start-up waits forever when a
reservation is refused, which is why no AddressSanitizer build has a statement
of this shape. (`theories/Shapes.v:289-299`) -/
def halts_may_fail (allowed : List word) (img : Image) : Prop :=
  ∀ (en : ExecEntry) (inp : ProcInput),
    valid_entry img en inp →
    valid_input inp →
    must_exit_in_scfg may_fail_cfg allowed img source_alloc_limit en inp

theorem halts_may_fail_is_lps (allowed : List word) (img : Image) :
    halts_may_fail allowed img = halts_allowed_T_scfg may_fail_cfg allowed img := rfl

/-! Widening the allowed set weakens both readings (`theories/Shapes.v:309-325`). -/

theorem halts_within_budget_mono (lim : Int) (S1 S2 : List word) (img : Image)
    (hsub : ∀ code, code ∈ S1 → code ∈ S2) :
    halts_within_budget lim S1 img → halts_within_budget lim S2 img :=
  fun h en inp hen hinp hlim =>
    must_exit_in_scfg_mono_set _ _ _ _ _ _ _ hsub (h en inp hen hinp hlim)

theorem halts_may_fail_mono (S1 S2 : List word) (img : Image)
    (hsub : ∀ code, code ∈ S1 → code ∈ S2) :
    halts_may_fail S1 img → halts_may_fail S2 img :=
  fun h => halts_allowed_T_scfg_mono_set _ _ _ _ hsub h

end OssFuzzTheorems.Core.Shapes
