-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/EntryStackFits.v
import LinuxProcessSemantics.LinuxProcessSem.Run
import LinuxProcessSemantics.LinuxProcessSem.StackLayout
import LinuxProcessSemantics.EquivalenceDefinition.FinInput
import LinuxProcessSemantics.EquivalenceDefinition.Classifier

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058 -/

/-! # LinuxProcessSem.Checks.EntryStackFits — what the entry-stack ceiling buys

Mirrors `theories/LinuxProcessSem/Checks/EntryStackFits.v`, declaration for
declaration.  Not part of the trusted specification: QA on the definitions,
in the style of `Checks/Examples.lean` and `Checks/VmMapsDisjoint.lean`.

`Run.valid_entry` has a conjunct, `Run.entry_stack_fits`, saying the initial
stack image ends at or below `State.sp_window_hi` — the top of the user
address space the declared VA environment provides.  A premise that excluded
nothing would be no premise, and a premise that excluded a real kernel
placement would be a soundness hole rather than a fix, so both directions are
pinned here.  The four parts, their witnesses, the kernel sources they rest on
(`randomize_stack_top`, `setup_arg_pages`, `create_elf_tables`) and the
argument for each choice are on the Rocq file and are not repeated: this file
carries the statements and the Lean proofs.

- PART 1, the conjunct BITES: placements `Run.valid_sp` admits and no kernel
  can produce are refused — at the window's top endpoint, and in its interior
  for an argv near the `valid_argv` limit.
- PART 2, the conjunct EXCLUDES NOTHING REAL: `near_top_sp` is still admitted.
- PART 3, the SPAN is not slack: it is attained exactly at the minimal input.
- PART 4, what the conjunct does to the statements ABOVE it: an
  entry-inhabitation hypothesis may only be asked at the VALID inputs.

WHERE THE LEAN TWIN DIFFERS FROM THE ROCQ ONE, and what is true here instead:

- `Run.entry_stack_fits_va_sv48` is an `↔` in Lean and an implication in Rocq,
  so the Sv48 arms below rewrite with it instead of applying it.
- Rocq's `Equivalence.image_brk_satisfiable_entry` has NO Lean twin.  Its
  Lean counterpart is `Equivalence.image_brk_satisfiable_entry_va`, stated
  over `Run.valid_input_va_any` and the size read off the input, which serves
  all three declared address-space sizes at once.  The two lemmas of PART 4
  that Rocq states through `image_brk_satisfiable_entry` are stated here
  unchanged and proved through the `_va` lemma composed with
  `Run.valid_input_va_any_of_valid_input`; nothing is weakened, since
  `FinInput.valid_fin_input` is `Run.valid_input` of `to_proc_input`.
- Rocq's proofs rewrite with stdpp's `Z_to_bv_unsigned` and `bv_wrap_small`.
  Lean has `BvBase.bv_unsigned_Z_to_bv_small` for that round trip, and
  `window_top_unsigned` below names its instance at `State.sp_window_hi` once
  rather than three times; it is the file's one declaration with no Rocq twin.
- Rocq's `lia` is `omega`, `Z` is `Int`, `repeat x n` is `List.replicate n x`,
  and a Rocq `Lemma`/`Example` is a Lean `theorem`.

The bound `191` of `entry_stack_span_pos` is Rocq's and is loose: the Lean
`Run.entry_stack_span` of the empty argv and envp is `207`.  The statement is
carried over unchanged, since everything in PART 1 is stated against it. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.EntryStackFits

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.EquivalenceDefinition.FinInput
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.EquivalenceDefinition.Classifier

/-! ## PART 1 — the conjunct bites -/

/-- The span is positive whatever the input: the argc word, the two NULL
terminators, the auxv and the AT_RANDOM block are there even for an empty
argv and envp.  Everything in PART 1 rests on this, so it is stated once
rather than re-derived.  Rocq: `EntryStackFits.entry_stack_span_pos`. -/
theorem entry_stack_span_pos (argv envp : List (List byte)) :
    191 ≤ entry_stack_span argv envp := by
  have h1 := total_arg_bytes_nonneg argv
  have h2 := total_arg_bytes_nonneg envp
  unfold entry_stack_span auxv_size
  omega

/-- The round trip of `State.sp_window_hi` through a 64-bit word.  NO ROCQ
TWIN: Rocq rewrites with stdpp's `Z_to_bv_unsigned` and `bv_wrap_small` at
each of the three uses below, and Lean's counterpart,
`BvBase.bv_unsigned_Z_to_bv_small`, is an equation worth naming once. -/
theorem window_top_unsigned : bv_unsigned (Z_to_bv 64 sp_window_hi) = sp_window_hi :=
  bv_unsigned_Z_to_bv_small _ (by decide) (by decide)

/-- The top of the sp window is a 16-byte-aligned address inside it, so
`Run.valid_sp` admits it — the premise without the conjunct.  Rocq:
`EntryStackFits.valid_sp_admits_window_top`. -/
theorem valid_sp_admits_window_top : valid_sp (Z_to_bv 64 sp_window_hi) := by
  unfold valid_sp
  rw [window_top_unsigned]
  simp only [sp_window_lo, sp_window_hi]
  omega

/-- …and `Run.entry_stack_fits` refuses it, for EVERY input.  An `sp` at
`STACK_TOP` puts argc itself at the first address above the user address
space; there is no argv or envp small enough to rescue it.  Rocq:
`EntryStackFits.entry_stack_fits_refuses_window_top`. -/
theorem entry_stack_fits_refuses_window_top (argv envp : List (List byte)) :
    ¬ entry_stack_fits (Z_to_bv 64 sp_window_hi) argv envp := by
  intro h
  have hspan := entry_stack_span_pos argv envp
  unfold entry_stack_fits at h
  rw [window_top_unsigned] at h
  omega

/-- And the same refusal read through `Run.valid_entry` itself, which is the
predicate `Equivalence.strong_universal_T` quantifies over.  The lemma above
is about `Run.entry_stack_fits` in isolation, so it survives the conjunct
being dropped from `Run.valid_entry` — this one does not.

The Lean proof splits on the declared size for one fact only,
`va_stack_top v ≤ sp_window_hi` — the Sv39 window is 254 GiB below the Sv48
one and the Sv57 ceiling IS the Sv48 one — and the three arms then close
together, where Rocq argues each arm in full.  Rocq:
`EntryStackFits.valid_entry_refuses_window_top`. -/
theorem valid_entry_refuses_window_top (img : Image) (brk mb : word) (rnd : EntryDraw)
    (inp : ProcInput) :
    ¬ valid_entry img (ExecEntry.mkEntry (Z_to_bv 64 sp_window_hi) brk mb rnd) inp := by
  intro h
  have hspan := entry_stack_span_pos inp.in_argv inp.in_envp
  have hT : va_stack_top inp.in_va_size ≤ sp_window_hi := by
    cases inp.in_va_size <;>
      simp only [va_stack_top, sv39_task_size, sp_window_hi] <;> omega
  unfold valid_entry valid_entry_va at h
  obtain ⟨hsp, -, -, hfits⟩ := h
  simp only [valid_sp_va, entry_stack_fits_va, va_sp_window_hi, va_sp_window_lo,
    window_top_unsigned] at hsp hfits
  omega

/-- The conjunct bites in the INTERIOR of the window too, not only at its
endpoint: a megabyte below the top is a placement a kernel really can choose,
but not while carrying an argv near the `Run.valid_argv` limit of 2097152
bytes.  Stated over all such `sp` and argv rather than at a witness, because
the claim is about the band and not about one address.  Rocq:
`EntryStackFits.entry_stack_fits_refuses_interior`. -/
theorem entry_stack_fits_refuses_interior (sp : word) (argv envp : List (List byte))
    (hsp : sp_window_hi - 1048576 ≤ bv_unsigned sp)
    (hargv : 1048576 ≤ total_arg_bytes argv) :
    ¬ entry_stack_fits sp argv envp := by
  intro h
  have h2 := total_arg_bytes_nonneg envp
  unfold entry_stack_fits entry_stack_span auxv_size at h
  omega

/-! ## PART 2 — the conjunct excludes nothing a kernel can produce -/

/-- The minimal input Linux delivers: argc = 1 with an empty argv[0], and no
environment.  Its stack image is 216 bytes.  Rocq:
`EntryStackFits.minimal_argv`. -/
def minimal_argv : List (List byte) := [[]]

/-- Rocq: `EntryStackFits.minimal_envp`. -/
def minimal_envp : List (List byte) := []

/-- Rocq: `EntryStackFits.minimal_span`. -/
theorem minimal_span : entry_stack_span minimal_argv minimal_envp = 216 := by decide

/-- 224 bytes below the top of the address space: 16-byte aligned, inside the
sp window, and enough room for that 216-byte image.  224 is the MODEL's
minimal image rounded up, not a kernel measurement; what the witness is for,
and which real placements it stands in for, are argued on the Rocq
definition.  Rocq: `EntryStackFits.near_top_sp`. -/
def near_top_sp : word := Z_to_bv 64 (sp_window_hi - 224)

/-- Rocq: `EntryStackFits.near_top_sp_unsigned`. -/
theorem near_top_sp_unsigned : bv_unsigned near_top_sp = sp_window_hi - 224 := by
  unfold near_top_sp
  exact bv_unsigned_Z_to_bv_small _ (by decide) (by decide)

/-- Rocq: `EntryStackFits.valid_sp_near_top`. -/
theorem valid_sp_near_top : valid_sp near_top_sp := by
  unfold valid_sp
  rw [near_top_sp_unsigned]
  simp only [sp_window_lo, sp_window_hi]
  omega

/-- Rocq: `EntryStackFits.entry_stack_fits_admits_near_top`. -/
theorem entry_stack_fits_admits_near_top :
    entry_stack_fits near_top_sp minimal_argv minimal_envp := by
  unfold entry_stack_fits
  rw [near_top_sp_unsigned, minimal_span]
  omega

/-- What PART 2 is really about.  The alternative to a per-run premise is an
absolute one: subtract the worst-case image (`Run.entry_stack_span_max`) from
`State.sp_window_hi` and keep `Run.valid_entry` blind to the input.  That
refuses `near_top_sp`, and with it the whole band beneath `sp_window_hi` a
kernel with randomization off and a small argv and envp places `sp` inside.
Refusing it would not cost provability, it would cost COVERAGE.  Rocq:
`EntryStackFits.worst_case_ceiling_would_refuse_a_real_placement`. -/
theorem worst_case_ceiling_would_refuse_a_real_placement :
    bv_unsigned near_top_sp > sp_window_hi - entry_stack_span_max
    ∧ bv_unsigned near_top_sp + entry_stack_span minimal_argv minimal_envp
      ≤ sp_window_hi := by
  rw [near_top_sp_unsigned, minimal_span]
  unfold entry_stack_span_max
  omega

/-! ## PART 3 — the span is the image's size, not a comfortable over-estimate

`Run.entry_stack_fits` is stated against `Run.entry_stack_span` rather than
against `StackLayout.build_stack_bytes` itself.  That is only safe while the
span stays an upper bound that is not slack: every byte of slack is a byte of
the address space the premise refuses to let a real image use.  At the
minimal input the bound is ATTAINED. -/

/-- Rocq: `EntryStackFits.entry_stack_span_attained_at_the_minimum`.

The conversion is bounded and small — `minimal_argv` is `[[]]`,
`minimal_envp` is `[]`, and the whole image is 216 bytes — but it runs
`build_stack_bytes` to a byte list and counts it, which is past both
default budgets.  Raised here rather than made into a `simp` computation:
`rfl` is the Rocq proof, and the two options say what the cost is. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem entry_stack_span_attained_at_the_minimum (ph : PhdrInfo) (sp : word)
    (uid hw : word) (rnd : EntryDraw) :
    ((build_stack_bytes ph sp minimal_argv minimal_envp uid hw rnd).length : Int)
    = entry_stack_span minimal_argv minimal_envp := by
  with_unfolding_all rfl

/-! ## PART 4 — the conjunct bounds where an inhabitation hypothesis may be asked

`Run.valid_entry` takes the input because `Run.entry_stack_fits` reads argv
and envp: "this image has a valid entry" is a claim about an IMAGE AND AN
INPUT TOGETHER, never about an image alone.  A hypothesis quantifying it over
all inputs is therefore not a strong assumption but an unsatisfiable one.
This part is the negative test for that mistake, together with the positive
pin that the per-valid-input form
`Classifier.decides_accepts_iff` takes is the one
`Equivalence.image_brk_satisfiable_entry_va` actually produces. -/

/-- The witness: an argv of 268435457 empty strings.  Its argv POINTER ARRAY
alone is 2147483656 bytes, eight more than the 2147483648-byte sp window, so
no stack pointer `Run.valid_sp` admits leaves room for it.  Rocq:
`EntryStackFits.oversized_argv`. -/
def oversized_argv : List (List byte) := List.replicate (2 ^ 28 + 1) []

/-- NO `simp`, AND NO `simp only`, ON A GOAL HOLDING THIS LIST.  Lean core's
builtin `[simp]` dsimproc `List.reduceReplicate` rewrites
`List.replicate <literal> x` to the LIST LITERAL, which for this witness is
268435457 elements; `simp only` runs the builtin simprocs too, so the guard is
to keep the term away from the simplifier entirely.  `List.length_replicate`
applied as a term unfolds `oversized_argv` once, reads the count off
`List.replicate`'s first argument and never builds the list — the Lean twin of
what the Rocq proof's `repeat_length` and `Nat.pow` buy there, and of the
warning on the Rocq `oversized_input_is_not_valid` against letting the kernel
compute this length.  Rocq: `EntryStackFits.oversized_argv_length`. -/
theorem oversized_argv_length : (oversized_argv.length : Int) = 268435457 := by
  have h : oversized_argv.length = 268435457 := List.length_replicate
  omega

/-- `StackLayout.hwcap_rv64gc` rather than a zero word, and the choice is not
cosmetic: this witness exists to be REFUSED, and it has to be refused for its
argv.  Rocq: `EntryStackFits.oversized_input`. -/
def oversized_input : FinProcInput :=
  FinProcInput.mkFinProcInput oversized_argv [] [] [] (Z_to_bv 64 0) (Z_to_bv 64 0) []
    net_silent (Z_to_bv 64 0) (Z_to_bv 64 0) hwcap_rv64gc false .Sv48 [] []

/-- The band the POINTER ARRAY alone excludes, stated over every `sp`, argv
and envp rather than at the witness.  Rocq:
`EntryStackFits.entry_stack_fits_refuses_oversized_argc`. -/
theorem entry_stack_fits_refuses_oversized_argc (sp : word) (argv envp : List (List byte))
    (hlo : sp_window_lo ≤ bv_unsigned sp)
    (hargc : 268435457 ≤ (argv.length : Int)) :
    ¬ entry_stack_fits sp argv envp := by
  intro h
  have h1 := total_arg_bytes_nonneg argv
  have h2 := total_arg_bytes_nonneg envp
  unfold entry_stack_fits entry_stack_span auxv_size sp_window_hi at h
  unfold sp_window_lo at hlo
  omega

/-- THE NEGATIVE TEST.  No image whatever has a valid entry at every finite
input, so the unrestricted inhabitation hypothesis is false for every `C` and
a lemma taking it can be applied to nothing.  Stated over `C` rather than at a
witness image: the failure is in the input, and no image can repair it.  Rocq:
`EntryStackFits.no_image_has_an_entry_for_every_input`. -/
theorem no_image_has_an_entry_for_every_input (C : Image) :
    ¬ (∀ g, ∃ en, valid_entry C en (to_proc_input g)) := by
  intro h
  obtain ⟨en, hen⟩ := h oversized_input
  have hva : (to_proc_input oversized_input).in_va_size = .Sv48 := rfl
  unfold valid_entry valid_entry_va at hen
  obtain ⟨hsp, -, -, hfits⟩ := hen
  rw [hva] at hsp hfits
  rw [entry_stack_fits_va_sv48] at hfits
  have hlo : sp_window_lo ≤ bv_unsigned en.en_sp := by
    simp only [valid_sp_va, va_sp_window_lo, va_sp_window_hi, va_stack_top,
      sp_window_lo, sp_window_hi] at hsp ⊢
    omega
  have hargv : (to_proc_input oversized_input).in_argv = oversized_argv := rfl
  rw [hargv] at hfits
  exact entry_stack_fits_refuses_oversized_argc en.en_sp _ _ hlo
    (by have := oversized_argv_length; omega) hfits

/-- …and the input that kills it is one the per-valid-input form never asks
about, which is what makes the restriction a fix rather than a dodge:
`Run.valid_argv` caps argc at 1024.  Rocq:
`EntryStackFits.oversized_input_is_not_valid`. -/
theorem oversized_input_is_not_valid : ¬ valid_fin_input oversized_input := by
  intro h
  have hlen : ((to_proc_input oversized_input).in_argv.length : Int) ≤ 1024 := h.1.1.2
  have hargv : (to_proc_input oversized_input).in_argv = oversized_argv := rfl
  rw [hargv, oversized_argv_length] at hlen
  omega

/-- THE POSITIVE PIN, in two steps.  First: the well-formedness assertion a
checker makes about the classifier image really does yield the
per-valid-input hypothesis.  Rocq states this through
`Equivalence.image_brk_satisfiable_entry`, which has no Lean twin; here it is
`Equivalence.image_brk_satisfiable_entry_va` at the size read off the input,
whose premise `Run.valid_input_va_any` is implied by the `Run.valid_input`
that `FinInput.valid_fin_input` IS.  The statement is Rocq's unchanged.  Rocq:
`EntryStackFits.image_brk_satisfiable_gives_the_per_valid_input_hypothesis`. -/
theorem image_brk_satisfiable_gives_the_per_valid_input_hypothesis (C : Image)
    (h : image_brk_satisfiable C.img_segments = true) :
    ∀ g, valid_fin_input g → ∃ en, valid_entry C en (to_proc_input g) :=
  fun g hg =>
    image_brk_satisfiable_entry_va C (to_proc_input g)
      (valid_input_va_any_of_valid_input _ hg) h

/-- Second: that is the hypothesis `Classifier.decides_accepts_iff` consumes.
The lemma is stated so that it typechecks only while the classifier lemma
takes the per-valid-input form — restore the unrestricted one and this file
stops building, which is the point of pinning it here rather than describing
it in a comment.  Rocq:
`EntryStackFits.decides_accepts_iff_takes_the_per_valid_input_hypothesis`. -/
theorem decides_accepts_iff_takes_the_per_valid_input_hypothesis (C : Image)
    (spec : ProcInput → Prop) (hdec : decides C spec)
    (hwf : image_brk_satisfiable C.img_segments = true) (f : FinProcInput) :
    valid_fin_input f → (accepts C f ↔ spec (to_proc_input f)) :=
  decides_accepts_iff C spec hdec
    (image_brk_satisfiable_gives_the_per_valid_input_hypothesis C hwf) f

end LinuxProcessSemantics.LinuxProcessSem.Checks.EntryStackFits
