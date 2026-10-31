import LinuxProcessSemantics.LinuxProcessSem.State
import LinuxProcessSemantics.EquivalenceDefinition.Equivalence
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.PreludeCore
import LinuxProcessSemantics.LinuxProcessSem.Checks.Omni
import LinuxProcessSemantics.Examples.rwx_flag_ns.Proof

/-! # Checks.Cases.EquivalenceDefinition.Equivalence

Not part of the trusted specification. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.Equivalence

open LinuxProcessSemantics.LinuxProcessSem.State

/-- inherited-divergence: bugs/accept-queue-cannot-run-out.md -- The environment never runs out of peers.
Linux v6.18.46 `inet_csk_accept` in net/ipv4/inet_connection_sock.c answers
-EAGAIN for an O_NONBLOCK listener whose accept queue is empty (lines 667-673).
Otherwise it waits in `inet_csk_wait_for_connect` (call at line 675; function
at lines 601-644 in the same file).
The model's environment `NetQueue` in State/Streams.lean has no empty queue.
The divergence belongs to State.v and State.lean. State.lean's entry on
`DIVERGENCE_UNDECLARED_ALLOWED` keeps the debt. Equivalence.v cites it because
the universal theorem quantifies over this environment.
kernel: net/ipv4/inet_connection_sock.c:inet_csk_accept@v6.18.46
-/
theorem accept_queue_never_runs_out (q : NetQueue) (n : Nat) :
    nq_peer (Nat.repeat nq_rest n q) = (q.conn_at n).1 := by
  have observations (k : Nat) :
      ∀ i, (Nat.repeat nq_rest k q).conn_at i = q.conn_at (i + k) := by
    induction k with
    | zero => intro i; rfl
    | succ k ih =>
      intro i
      change (Nat.repeat nq_rest k q).conn_at (i + 1) = q.conn_at (i + (k + 1))
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using ih (i + 1)
  simpa only [nq_peer, Nat.zero_add] using congrArg Prod.fst (observations n 0)

/-! ## A-Equiv-va: the address-space-size statements at concrete inputs -/

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence

/-- Restates Rocq `Checks.Cases.VaSize.sv57_window_is_sv48s`.
model: the declared geometry and `valid_sp_va`, evaluated independently of equivalence.
-/
theorem sv57_window_is_sv48s :
    va_sp_window_lo .Sv57 = va_sp_window_lo .Sv48 ∧
    va_sp_window_hi .Sv57 = va_sp_window_hi .Sv48 ∧
    va_mmap_base_min .Sv57 = va_mmap_base_min .Sv48 ∧
    va_mmap_base_max .Sv57 = va_mmap_base_max .Sv48 := by decide

/-- Restates Rocq `Checks.Cases.VaSize.sv57_task_size_is_2_56`.
model: the declared geometry and `valid_sp_va`, evaluated independently of equivalence.
-/
theorem sv57_task_size_is_2_56 :
    va_task_size .Sv57 = 2 ^ 56 := by decide

/-- Restates Rocq `Checks.Cases.VaSize.sv57_limit_is_not_sv48s`.
model: the declared geometry and `valid_sp_va`, evaluated independently of equivalence.
-/
theorem sv57_limit_is_not_sv48s :
    va_task_size .Sv57 ≠ va_task_size .Sv48 := by decide

/-- Restates Rocq `Checks.Cases.VaSize.sv39_top_is_the_whole_space`.
model: the declared geometry and `valid_sp_va`, evaluated independently of equivalence.
-/
theorem sv39_top_is_the_whole_space :
    va_task_size .Sv39 = 2 ^ 38 ∧ va_stack_top .Sv39 = 2 ^ 38 := by decide

/-- Restates Rocq `Checks.Cases.VaSize.sv39_window`.
model: the declared geometry and `valid_sp_va`, evaluated independently of equivalence.
-/
theorem sv39_window :
    va_sp_window_lo .Sv39 = 0x3f80000000 ∧ va_sp_window_hi .Sv39 = 0x4000000000 := by decide

/-- Restates Rocq `Checks.Cases.VaSize.sv48_window_bottom_valid_under_sv48`.
model: the declared geometry and `valid_sp_va`, evaluated independently of equivalence.
-/
theorem sv48_window_bottom_valid_under_sv48 :
    valid_sp_va .Sv48 (Z_to_bv 64 sp_window_lo) := by unfold valid_sp_va; decide

/-- Restates Rocq `Checks.Cases.VaSize.sv48_window_bottom_refused_under_sv39`.
model: the declared geometry and `valid_sp_va`, evaluated independently of equivalence.
-/
theorem sv48_window_bottom_refused_under_sv39 :
    ¬ valid_sp_va .Sv39 (Z_to_bv 64 sp_window_lo) := by unfold valid_sp_va; decide

/-- Restates Rocq `Checks.Cases.VaSize.sv48_window_bottom_valid_under_sv57`.
model: the declared geometry and `valid_sp_va`, evaluated independently of equivalence.
-/
theorem sv48_window_bottom_valid_under_sv57 :
    valid_sp_va .Sv57 (Z_to_bv 64 sp_window_lo) := by unfold valid_sp_va; decide

/-- The three fixtures differ only in their address-space declaration and carry one empty argument.
Restates Rocq `Checks.Cases.VaSize.sized_input`.
model: `ProcInput.mkProcInput` fixes the fixture fields, including `ProcInput.in_va_size`.
-/
def sized_input (v : VaSize) : ProcInput :=
  ProcInput.mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
    default_nofile (Z_to_bv 64 0) demo_hwcap false v

/-- The shared input clauses accept every declaration of the fixture.
Restates Rocq `Checks.Cases.VaSize.sized_input_va_any`.
model: `Run.valid_input_va_any` checks the shared clauses of `sized_input`.
-/
theorem sized_input_va_any : ∀ v, valid_input_va_any (sized_input v) := by
  intro v
  unfold valid_input_va_any
  repeat' with_reducible apply And.intro
  all_goals first
    | (simp only [sized_input, ProcInput.mkProcInput, ProcInput.in_fs,
        valid_argv, valid_envp, Fs.valid_fs, valid_creds, valid_id,
        valid_nofile, valid_sigmask, valid_hwcap]
       set_option maxRecDepth 32768 in decide)
    | rfl
    | exact default_urandom_infinite
    | fail "valid_input_va_any: a clause matched none of the shapes"

/-- The Sv48 fixture belongs to the Sv48 input class.
Restates Rocq `Checks.Cases.VaSize.sized_sv48_valid`.
model: `Run.valid_input` checks the shared clauses and the Sv48 declaration of `sized_input`.
-/
theorem sized_sv48_valid : valid_input (sized_input .Sv48) := by
  rcases valid_input_va_any_splits _ (sized_input_va_any .Sv48) with h | h | h
  · exact h
  · cases valid_input_sv39_va_size _ h
  · cases valid_input_sv57_va_size _ h

/-- The Sv39 fixture belongs to the Sv39 input class.
Restates Rocq `Checks.Cases.VaSize.sized_sv39_valid`.
model: `Run.valid_input_sv39` checks the shared clauses and the Sv39 declaration of `sized_input`.
-/
theorem sized_sv39_valid : valid_input_sv39 (sized_input .Sv39) := by
  rcases valid_input_va_any_splits _ (sized_input_va_any .Sv39) with h | h | h
  · cases valid_input_va_size _ h
  · exact h
  · cases valid_input_sv57_va_size _ h

/-- The Sv57 fixture belongs to the Sv57 input class.
Restates Rocq `Checks.Cases.VaSize.sized_sv57_valid`.
model: `Run.valid_input_sv57` checks the shared clauses and the Sv57 declaration of `sized_input`.
-/
theorem sized_sv57_valid : valid_input_sv57 (sized_input .Sv57) := by
  rcases valid_input_va_any_splits _ (sized_input_va_any .Sv57) with h | h | h
  · cases valid_input_va_size _ h
  · cases valid_input_sv39_va_size _ h
  · exact h

/-- Each pinned input class rejects both fixtures bearing a different declaration.
Restates Rocq `Checks.Cases.VaSize.each_instance_refuses_the_others`.
model: `Run.valid_input`, `Run.valid_input_sv39`, and `Run.valid_input_sv57` require their respective `ProcInput.in_va_size` values.
-/
theorem each_instance_refuses_the_others :
    ¬ valid_input (sized_input .Sv39) ∧ ¬ valid_input (sized_input .Sv57) ∧
    ¬ valid_input_sv39 (sized_input .Sv48) ∧ ¬ valid_input_sv39 (sized_input .Sv57) ∧
    ¬ valid_input_sv57 (sized_input .Sv48) ∧ ¬ valid_input_sv57 (sized_input .Sv39) := by
  repeat' apply And.intro
  all_goals intro h
  all_goals first
    | cases valid_input_va_size _ h
    | cases valid_input_sv39_va_size _ h
    | cases valid_input_sv57_va_size _ h

/-- Splitting the unpinned input predicate covers all three concrete declarations.
Restates Rocq `Checks.Cases.VaSize.va_any_splits_each_to_its_own`.
model: `Run.valid_input_va_any`, `Run.valid_input`, `Run.valid_input_sv39`, and `Run.valid_input_sv57` differ only in the address-space declaration clause.
-/
theorem va_any_splits_each_to_its_own :
    (valid_input (sized_input .Sv48) ∨ valid_input_sv39 (sized_input .Sv48) ∨
      valid_input_sv57 (sized_input .Sv48)) ∧
    (valid_input (sized_input .Sv39) ∨ valid_input_sv39 (sized_input .Sv39) ∨
      valid_input_sv57 (sized_input .Sv39)) ∧
    (valid_input (sized_input .Sv57) ∨ valid_input_sv39 (sized_input .Sv57) ∨
      valid_input_sv57 (sized_input .Sv57)) := by
  repeat' apply And.intro
  all_goals exact valid_input_va_any_splits _ (sized_input_va_any _)

/-- inherited-divergence: bugs/va-size-declines-every-non-sv48-run.md -- Linux v6.18.46
runs riscv64 tasks under Sv39 and Sv57. In arch/riscv/mm/init.c, `satp_mode`
starts at Sv57 for non-XIP kernels (line 49); `set_satp_mode` selects Sv39
when requested (lines 885-900) and falls back when hardware rejects a mode
(lines 926-940), using `disable_pgtable_l4` (lines 829-834).
In arch/riscv/include/asm/pgtable.h, `TASK_SIZE_64` depends on the paging
mode through `PGDIR_SIZE`; the Sv39/Sv48/Sv57 task sizes and `TASK_SIZE`
definitions are at lines 1068-1088.
The model refuses the sealed statement under Sv39 because `strong_equiv_va`
requires Sv48.
Restates Rocq `Checks.Cases.VaSize.sv39_statement_refused`.
kernel: arch/riscv/mm/init.c:set_satp_mode@v6.18.46
-/
theorem sv39_statement_refused :
    ∀ s t es et, ¬ strong_equiv_va s t es et (sized_input .Sv39) := by
  intro s t es et h
  cases h.1

/-- The Sv57 declaration alone refutes the sealed equivalence predicate.
Restates Rocq `Checks.Cases.VaSize.sv57_statement_refused`.
model: `strong_equiv_va` requires `ProcInput.in_va_size` to be Sv48.
-/
theorem sv57_statement_refused :
    ∀ s t es et, ¬ strong_equiv_va s t es et (sized_input .Sv57) := by
  intro s t es et h
  cases h.1

/-- Under Sv48 the sealed predicate leaves exactly the original equivalence question.
Restates Rocq `Checks.Cases.VaSize.sv48_statement_is_strong_equiv`.
model: `strong_equiv_va` conjoins the Sv48 declaration with `strong_equiv`.
-/
theorem sv48_statement_is_strong_equiv : ∀ s t es et,
    strong_equiv_va s t es et (sized_input .Sv48) ↔
      strong_equiv s t es et (sized_input .Sv48) := by
  intro s t es et
  exact strong_equiv_va_sv48 _ _ _ _ _ rfl

/-- The empty image isolates the statement's declaration gate from segment reservations.
Restates Rocq `Checks.Cases.VaSize.empty_image`.
model: `Image.mkImage` fixes the empty segment list, entry point, and program headers.
-/
def empty_image : Image := Image.mkImage [] 0 demo_phdrs

/-- The empty image supplies the satisfiable-brk premise used to construct entries.
Restates Rocq `Checks.Cases.VaSize.empty_image_brk_satisfiable`.
model: `image_brk_satisfiable`, `Run.segments_reserved`, and `State.reserved_top` compute the empty image's brk bound.
-/
theorem empty_image_brk_satisfiable : image_brk_satisfiable empty_image.img_segments = true := by
  decide

/-- An inhabited entry makes the Sv39 universal statement concretely false.
Restates Rocq `Checks.Cases.VaSize.sv39_statement_refuted_on_the_empty_image`.
model: `strong_universal_T_sv39` quantifies over `Run.valid_entry` and `Run.valid_input_sv39`, while `strong_equiv_va` requires Sv48.
-/
theorem sv39_statement_refuted_on_the_empty_image :
    ¬ strong_universal_T_sv39 empty_image empty_image := by
  obtain ⟨en, hen⟩ := image_brk_satisfiable_entry_va empty_image (sized_input .Sv39)
    (sized_input_va_any .Sv39) empty_image_brk_satisfiable
  exact strong_universal_T_sv39_refuted _ _ en en _ hen hen sized_sv39_valid

/-- An inhabited entry makes the Sv57 universal statement concretely false.
Restates Rocq `Checks.Cases.VaSize.sv57_statement_refuted_on_the_empty_image`.
model: `strong_universal_T_sv57` quantifies over `Run.valid_entry` and `Run.valid_input_sv57`, while `strong_equiv_va` requires Sv48.
-/
theorem sv57_statement_refuted_on_the_empty_image :
    ¬ strong_universal_T_sv57 empty_image empty_image := by
  obtain ⟨en, hen⟩ := image_brk_satisfiable_entry_va empty_image (sized_input .Sv57)
    (sized_input_va_any .Sv57) empty_image_brk_satisfiable
  exact strong_universal_T_sv57_refuted _ _ en en _ hen hen sized_sv57_valid

/-- The unpinned universal statement inherits the empty image's Sv39 refutation.
Restates Rocq `Checks.Cases.VaSize.va_any_statement_refuted_on_the_empty_image`.
model: `strong_universal_T_va_any` quantifies over `Run.valid_entry` and `Run.valid_input_va_any`, admitting the Sv39 fixture that `strong_equiv_va` refuses.
-/
theorem va_any_statement_refuted_on_the_empty_image :
    ¬ strong_universal_T_va_any empty_image empty_image := by
  intro h
  exact sv39_statement_refuted_on_the_empty_image
    ((strong_universal_T_va_any_splits _ _).1 h).2.1

/-- The same empty image under Sv48 retains the ordinary equivalence obligation.
Restates Rocq `Checks.Cases.VaSize.empty_image_sv48_is_the_equivalence_question`.
model: `strong_equiv_va` conjoins the Sv48 declaration with `strong_equiv`, including for `empty_image`.
-/
theorem empty_image_sv48_is_the_equivalence_question : ∀ es et,
    strong_equiv_va empty_image empty_image es et (sized_input .Sv48) ↔
      strong_equiv empty_image empty_image es et (sized_input .Sv48) := by
  intro es et
  exact sv48_statement_is_strong_equiv _ _ _ _

/-- This synthetic image makes the reserved top exceed every representable brk word.
model: `Run.segments_reserved`, `State.reserved_top`, and `Run.valid_brk` decide the entry obstruction.
-/
def brk_unplaceable_image : Image :=
  Image.mkImage [⟨2 ^ 64 - 4096, 8192, "", []⟩] 0 demo_phdrs

/-- Equality at an aligned reservation top is a valid break, not a strict lower bound.
model: `valid_brk` at the empty image's zero reservation top.
-/
theorem brk_at_reserved_top_accept : valid_brk [] (Z_to_bv 64 0) := by unfold valid_brk; decide

/-- A break below a nonzero reservation top is invalid.
model: `valid_brk` at a single page reservation and the zero break.
-/
theorem brk_below_reserved_top_refute :
    ¬ valid_brk [⟨0, 4096, "", []⟩] (Z_to_bv 64 0) := by unfold valid_brk; decide

/-- No entry can satisfy the image's brk lower bound, regardless of the input declaration.
model: `Run.valid_entry`, `Run.valid_brk`, and `Riscv.Prelude.bv_unsigned` bound the unsigned brk word.
-/
theorem brk_unplaceable_image_has_no_entry :
    ∀ en inp, ¬ valid_entry brk_unplaceable_image en inp := by
  intro en inp h
  have htop : reserved_top (segments_reserved brk_unplaceable_image.img_segments) =
      2 ^ 64 + 4096 := by decide
  have hlo := h.2.1.1
  rw [htop] at hlo
  have hbound := en.en_brk.isLt
  unfold bv_unsigned at hlo
  omega

/-- Without a valid entry the Sv39 universal statement holds, pinning the refutation's entry premise.
model: `strong_universal_T_sv39` quantifies over `Run.valid_entry`, which `brk_unplaceable_image_has_no_entry` refutes.
-/
theorem sv39_statement_holds_when_no_entry_exists :
    strong_universal_T_sv39 brk_unplaceable_image brk_unplaceable_image := by
  intro es et inp hs _ _
  exact False.elim (brk_unplaceable_image_has_no_entry es inp hs)

/-- Without a valid entry the Sv57 universal statement holds, pinning the refutation's entry premise.
model: `strong_universal_T_sv57` quantifies over `Run.valid_entry`, which `brk_unplaceable_image_has_no_entry` refutes.
-/
theorem sv57_statement_holds_when_no_entry_exists :
    strong_universal_T_sv57 brk_unplaceable_image brk_unplaceable_image := by
  intro es et inp hs _ _
  exact False.elim (brk_unplaceable_image_has_no_entry es inp hs)

/-- The unpinned universal statement also holds when no declaration can supply a valid entry.
model: `strong_universal_T_va_any` quantifies over `Run.valid_entry`, which `brk_unplaceable_image_has_no_entry` refutes.
-/
theorem va_any_statement_holds_when_no_entry_exists :
    strong_universal_T_va_any brk_unplaceable_image brk_unplaceable_image := by
  intro es et inp hs _ _
  exact False.elim (brk_unplaceable_image_has_no_entry es inp hs)

/-- An entry-less source suffices even when the other image admits entries.
model: `strong_universal_T_sv39` retains its independent source entry premise.
-/
theorem sv39_no_source_entry_accept :
    strong_universal_T_sv39 brk_unplaceable_image empty_image := by
  intro es et inp hs ht _
  exact False.elim (brk_unplaceable_image_has_no_entry es inp hs)

/-- An entry-less target suffices even when the other image admits entries.
model: `strong_universal_T_sv39` retains its independent target entry premise.
-/
theorem sv39_no_target_entry_accept :
    strong_universal_T_sv39 empty_image brk_unplaceable_image := by
  intro es et inp hs ht _
  exact False.elim (brk_unplaceable_image_has_no_entry et inp ht)

/-- An entry-less source suffices even when the other image admits entries.
model: `strong_universal_T_sv57` retains its independent source entry premise.
-/
theorem sv57_no_source_entry_accept :
    strong_universal_T_sv57 brk_unplaceable_image empty_image := by
  intro es et inp hs ht _
  exact False.elim (brk_unplaceable_image_has_no_entry es inp hs)

/-- An entry-less target suffices even when the other image admits entries.
model: `strong_universal_T_sv57` retains its independent target entry premise.
-/
theorem sv57_no_target_entry_accept :
    strong_universal_T_sv57 empty_image brk_unplaceable_image := by
  intro es et inp hs ht _
  exact False.elim (brk_unplaceable_image_has_no_entry et inp ht)

/-- An entry-less source suffices even when the other image admits entries.
model: `strong_universal_T_va_any` retains its independent source entry premise.
-/
theorem va_any_no_source_entry_accept :
    strong_universal_T_va_any brk_unplaceable_image empty_image := by
  intro es et inp hs ht _
  exact False.elim (brk_unplaceable_image_has_no_entry es inp hs)

/-- An entry-less target suffices even when the other image admits entries.
model: `strong_universal_T_va_any` retains its independent target entry premise.
-/
theorem va_any_no_target_entry_accept :
    strong_universal_T_va_any empty_image brk_unplaceable_image := by
  intro es et inp hs ht _
  exact False.elim (brk_unplaceable_image_has_no_entry et inp ht)

/-! ## A-Equiv-error-free: the error-free, abort, either and hwcap statements -/

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.StackLayout
open LinuxProcessSemantics.Common.PropExec (step_of_fetch)
open LinuxProcessSemantics.LinuxProcessSem.MemImageType
open LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics
open LinuxProcessSemantics.LinuxProcessSem.Run
open LinuxProcessSemantics.LinuxProcessSem.OmniRun
open LinuxProcessSemantics.EquivalenceDefinition.Equivalence
open LinuxProcessSemantics.Common.ExitSim
open LinuxProcessSemantics.LinuxProcessSem.Checks.Examples
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude
open LinuxProcessSemantics.Examples.rwx_flag_ns.SourceMemImage
open LinuxProcessSemantics.Examples.rwx_flag_ns.TargetMemImage

/-- A synthetic signal-ending trace distinguishes no errors from no death.
model: a behavior record with a singleton `KillEv` trace and false error fields. -/
def killed_behavior : behavior :=
  { bh_traces := fun tr => tr = [] ∨ tr = [KillEv (Z_to_bv 64 6) []]
    bh_errors := False, bh_all_errors := False, bh_unmodeled := False }

/-- Signal death requires an actual member of an observable trace.
model: raw trace membership, with the event equality stated independently. -/
theorem dies_by_signal_iff (b : behavior) :
    dies_by_signal b ↔ ∃ tr, b.bh_traces tr ∧ ∃ e ∈ tr, ∃ sig fs, e = KillEv sig fs := by
  constructor
  · rintro ⟨tr, sig, fs, ht, hk⟩
    exact ⟨tr, ht, KillEv sig fs, hk, sig, fs, rfl⟩
  · rintro ⟨tr, ht, e, he, sig, fs, rfl⟩
    exact ⟨tr, sig, fs, ht, he⟩

/-- The explicit signal trace witnesses death without inventing a run.
model: `killed_behavior` contains the singleton signal trace. -/
theorem dies_by_signal_accept : dies_by_signal killed_behavior :=
  ⟨[KillEv (Z_to_bv 64 6) []], Z_to_bv 64 6, [], Or.inr rfl, List.mem_cons_self⟩

/-- Empty traces cannot carry a signal event.
model: `quiet_behavior` has only the empty trace. -/
theorem dies_by_signal_refute : ¬ dies_by_signal quiet_behavior := by
  rintro ⟨tr, sig, fs, ht, hk⟩
  cases ht
  exact List.not_mem_nil hk

/-- Safety negates possible error, rather than just universal error.
model: the raw existential-error field is false. -/
theorem error_free_raw_iff (b : behavior) : error_free b ↔ ¬ b.bh_errors := Iff.rfl

/-- The quiet record has no possible error, as in Rocq `error_free_bites`.
model: the concrete quiet record has a false possible-error field. -/
theorem error_free_accept : error_free quiet_behavior := error_free_bites.1

/-- A modeled crash still fails safety, as in Rocq `error_free_bites`.
model: the concrete crashing record has a true possible-error field. -/
theorem error_free_refute : ¬ error_free crashing_behavior := error_free_bites.2

/-- Every observed event must differ from every signal-death event.
model: error-freedom plus a universal exclusion over the raw trace field. -/
theorem error_free_unkilled_iff (b : behavior) :
    error_free_unkilled b ↔
      (¬ b.bh_errors ∧ ∀ tr, b.bh_traces tr → ∀ e ∈ tr, ∀ sig fs, e ≠ KillEv sig fs) := by
  constructor
  · rintro ⟨he, hn⟩
    refine ⟨he, ?_⟩
    rintro tr ht e hm sig fs rfl
    exact hn ⟨tr, sig, fs, ht, hm⟩
  · rintro ⟨he, hn⟩
    refine ⟨he, ?_⟩
    rintro ⟨tr, sig, fs, ht, hk⟩
    exact hn tr ht (KillEv sig fs) hk sig fs rfl

/-- Quiet behavior has neither error nor signal death.
model: the false error field and the empty trace jointly establish safety. -/
theorem error_free_unkilled_accept : error_free_unkilled quiet_behavior :=
  ⟨error_free_accept, dies_by_signal_refute⟩

/-- The extra conjunct rejects a signal death even with no error, as in
Rocq `error_free_unkilled_bites`.
model: the concrete killed record has no error but contains a signal event. -/
theorem error_free_unkilled_refute :
    error_free killed_behavior ∧ ¬ error_free_unkilled killed_behavior :=
  ⟨fun h => h, fun h => h.2 dies_by_signal_accept⟩

/-- The abort launch changes only the declared stance of the valid demo.
model: the concrete process-input record keeps the same shared validity clauses. -/
def abort_input : ProcInput := { demo_proc_input with in_abort_terminal := true }

/-- The vector-capable launch changes only the published capability word.
model: the concrete process-input record chooses `hwcap_rv64gcv`. -/
def vector_input : ProcInput := { demo_proc_input with in_hwcap := hwcap_rv64gcv }

/-- Changing the stance preserves every shared input clause.
model: `Run.valid_input_abort` at the demo record with its stance on. -/
theorem abort_input_valid : valid_input_abort abort_input := by
  obtain ⟨ha, he, hf, him, hc, hn, hs, hw, _, hv, hu⟩ := Checks.Omni.demo_input_valid
  exact ⟨ha, he, hf, him, hc, hn, hs, hw, rfl, hv, hu⟩

/-- The original demo word is the RV64GC declaration.
model: `Run.valid_input_hwcap_rv64gc` at the concrete demo input. -/
theorem scalar_input_valid : valid_input_hwcap_rv64gc demo_proc_input := by
  obtain ⟨ha, he, hf, him, hc, hn, hs, _, hab, hv, hu⟩ := Checks.Omni.demo_input_valid
  exact ⟨ha, he, hf, him, hc, hn, hs, rfl, hab, hv, hu⟩

/-- The alternate word preserves the other clauses.
model: `Run.valid_input_hwcap_rv64gcv` at `vector_input`. -/
theorem vector_input_valid : valid_input_hwcap_rv64gcv vector_input := by
  obtain ⟨ha, he, hf, him, hc, hn, hs, _, hab, hv, hu⟩ := Checks.Omni.demo_input_valid
  exact ⟨ha, he, hf, him, hc, hn, hs, rfl, hab, hv, hu⟩

/-- The undecodable segment fits below the demo break, and the stack has
room for any valid argument and environment lists.
model: `Run.valid_entry_sv48` and `entry_stack_span_bound` at the demo entry. -/
theorem undecodable_entry_valid (inp : ProcInput) (hv : inp.in_va_size = .Sv48)
    (ha : valid_argv inp.in_argv) (he : valid_envp inp.in_envp) :
    valid_entry undecodable_image demo_entry inp := by
  rw [valid_entry_sv48 _ _ _ hv]
  refine ⟨by unfold valid_sp; decide +kernel,
    by unfold valid_brk; decide +kernel,
    by unfold valid_mmap_base; decide +kernel, ?_⟩
  have hspan := (entry_stack_span_bound _ _ ha he).2
  change sp_window_lo + entry_stack_span inp.in_argv inp.in_envp ≤ sp_window_hi
  have hroom : sp_window_lo + entry_stack_span_max ≤ sp_window_hi := by decide +kernel
  omega

/-- The first fetch decodes no instruction, independently of the input.
model: `reaches_unmodeled_intro` at the four-byte 0xffffffff segment and the valid demo entry. -/
theorem undecodable_run_unmodeled (lim : Int) (inp : ProcInput) :
    (run undecodable_image lim demo_entry inp).bh_unmodeled := by
  apply reaches_unmodeled_intro
  · rfl
  · rfl
  · rw [mi_account_step_no_lazy _ _ _ rfl]
    rw [step_of_fetch _ _ 0xffffffff (by
      change fetch_word undecodable_segments 0x100 = some 0xffffffff
      decide +kernel)]
    rfl

/-- A modeled all-errors source still frees an undecodable target in baseline equivalence.
model: `Checks.Omni.ebreak_frees_undecodable_target` transported to `strong_equiv`.
-/
theorem all_errors_escape_accept :
    strong_equiv Checks.Omni.ebreak_image undecodable_image demo_entry demo_entry demo_proc_input :=
  (LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.strong_equiv_iff _ _ _ _ _).2
    Checks.Omni.ebreak_frees_undecodable_target

/-- The same real all-errors run cannot use that escape in the error-free contract.
model: `strong_equiv_error_free_no_all_errors_escape` fired with `Checks.Omni.ebreak_omni_errors`.
-/
theorem all_errors_escape_refute :
    ¬ strong_equiv_error_free Checks.Omni.ebreak_image undecodable_image demo_entry demo_entry demo_proc_input :=
  strong_equiv_error_free_no_all_errors_escape _ _ _ _ _
    ((bh_all_errors_iff _ _ _ _).2 (Checks.Omni.ebreak_omni_errors _))

/-- The same source execution proof uses only the Sv48 entry bounds, so it
also establishes termination with the abort stance on.
model: the pilot's `SourceExec.source_exit` derivation at `valid_entry_sv48`. -/
theorem pilot_source_abort_terminates (en : ExecEntry) (inp : ProcInput)
    (hi : valid_input_abort inp) (he : valid_entry Source.image en inp) :
    omni_run Source.image source_alloc_limit en inp (exit_post 5 inp.in_fs) :=
  Examples.rwx_flag_ns.Proof.source_abort_terminates en inp hi he

/-- An execution terminating with the sole exit event is safe and cannot
have a signal event in any observed prefix.
model: `exit_no_error_te` and `exit_obs_iff_te` exclude errors and signal events. -/
theorem exit_run_unkilled (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (h : omni_run img lim en inp (exit_post 5 inp.in_fs)) :
    error_free_unkilled (run img lim en inp) := by
  refine ⟨exit_no_error_te _ _ _ _ _ h, ?_⟩
  rintro ⟨tr, sig, fs, ht, hk⟩
  have hp := (exit_obs_iff_te _ _ _ _ _ h tr).1 ht
  cases tr with
  | nil => exact List.not_mem_nil hk
  | cons e tail =>
    obtain ⟨rfl, hp⟩ := hp
    cases tail with
    | nil => simp only [List.mem_singleton] at hk; cases hk
    | cons e tail => exact hp

/-- The pilot terminates on both sides with exit 5 at every valid triple;
this accept does not use an empty entry range or the all-error escape.
model: the pilot's two termination proofs and the exit trace characterization. -/
theorem strong_universal_error_free_T_accept :
    strong_universal_error_free_T Source.image Target.image :=
  Examples.rwx_flag_ns.Proof.strong_universal_error_free

/-- The pilot still exits 5 when abort is enabled; no signal death is hidden
by error-freedom. This is a termination-based accept.
model: `pilot_source_abort_terminates`, the target termination proof and `exit_run_unkilled`. -/
theorem strong_universal_error_free_T_abort_accept :
    strong_universal_error_free_T_abort Source.image Target.image := by
  intro es et inp hs _ hi
  have hsrun := pilot_source_abort_terminates es inp hi hs
  have htrun := Examples.rwx_flag_ns.Proof.target_terminates et inp
  exact ⟨exit_run_unkilled _ _ _ _ hsrun, exit_run_unkilled _ _ _ _ htrun,
    fun tr => (exit_obs_iff_te _ _ _ _ _ hsrun tr).trans (exit_obs_iff_te _ _ _ _ _ htrun tr).symm⟩

/-- The off refutation uses a valid entry, not a false quantifier premise.
model: the concrete demo entry satisfies the image break and stack bounds. -/
theorem undecodable_off_entry :
    valid_entry undecodable_image demo_entry demo_proc_input := undecodable_entry_valid _ (valid_input_va_size _ Checks.Omni.demo_input_valid) (by unfold valid_argv; decide)
      (by unfold valid_envp; decide)

/-- The abort refutation uses a valid entry, not a false quantifier premise.
model: the concrete demo entry satisfies the image break and stack bounds. -/
theorem undecodable_abort_entry :
    valid_entry undecodable_image demo_entry abort_input := undecodable_entry_valid _ (valid_input_abort_va_size _ abort_input_valid) (by unfold valid_argv; decide)
      (by unfold valid_envp; decide)

/-- The vector refutation uses a valid entry, not a false quantifier premise.
model: the concrete demo entry satisfies the image break and stack bounds. -/
theorem undecodable_vector_entry :
    valid_entry undecodable_image demo_entry vector_input := undecodable_entry_valid _ (valid_input_va_size _ (valid_input_of_valid_input_hwcap_rv64gcv _ vector_input_valid)) (by unfold valid_argv; decide)
      (by unfold valid_envp; decide)

/-- The triple requires safety on both budgets and equality of all observed prefixes.
model: raw run fields; the abort reading additionally excludes every signal event. -/
theorem strong_equiv_error_free_iff (source target : Image) (es et : ExecEntry) (inp : ProcInput) :
    strong_equiv_error_free source target es et inp ↔
      ¬ (run source source_alloc_limit es inp).bh_errors ∧ ¬ (run target target_alloc_limit et inp).bh_errors ∧
      (∀ tr, (run source source_alloc_limit es inp).bh_traces tr ↔ (run target target_alloc_limit et inp).bh_traces tr) := by
  simp only [strong_equiv_error_free, error_free, trace_equiv]

/-- The triple requires safety on both budgets and equality of all observed prefixes.
model: raw run fields; the abort reading additionally excludes every signal event. -/
theorem strong_equiv_error_free_abort_iff (source target : Image) (es et : ExecEntry) (inp : ProcInput) :
    strong_equiv_error_free_abort source target es et inp ↔
      (¬ (run source source_alloc_limit es inp).bh_errors ∧
        ∀ tr, (run source source_alloc_limit es inp).bh_traces tr → ∀ e ∈ tr, ∀ sig fs, e ≠ KillEv sig fs) ∧ (¬ (run target target_alloc_limit et inp).bh_errors ∧
        ∀ tr, (run target target_alloc_limit et inp).bh_traces tr → ∀ e ∈ tr, ∀ sig fs, e ≠ KillEv sig fs) ∧
      (∀ tr, (run source source_alloc_limit es inp).bh_traces tr ↔ (run target target_alloc_limit et inp).bh_traces tr) := by
  simp only [strong_equiv_error_free_abort, error_free_unkilled_iff, trace_equiv]

/-- Valid entries are quantified independently and share one process input;
the conclusion fixes the raw run fields for the declared input family.
model: explicit quantifiers over entries and inputs, with no predicate substituted for the run fields. -/
theorem strong_universal_error_free_T_iff (source target : Image) :
    strong_universal_error_free_T source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input inp →
      ¬ (run source source_alloc_limit es inp).bh_errors ∧ ¬ (run target target_alloc_limit et inp).bh_errors ∧
      (∀ tr, (run source source_alloc_limit es inp).bh_traces tr ↔ (run target target_alloc_limit et inp).bh_traces tr)) := by
  simp only [strong_universal_error_free_T, strong_equiv_error_free, error_free, trace_equiv]

/-- Valid entries are quantified independently and share one process input;
the conclusion fixes the raw run fields for the declared input family.
model: explicit quantifiers over entries and inputs, with no predicate substituted for the run fields. -/
theorem strong_universal_T_abort_iff (source target : Image) :
    strong_universal_T_abort source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input_abort inp →
      ¬ (run source source_alloc_limit es inp).bh_unmodeled ∧
      ((run source source_alloc_limit es inp).bh_all_errors ∨ ((∀ tr, (run source source_alloc_limit es inp).bh_traces tr ↔ (run target target_alloc_limit et inp).bh_traces tr) ∧ ¬ (run target target_alloc_limit et inp).bh_errors))) := by
  simp only [strong_universal_T_abort, strong_equiv, modeled, equiv, trace_equiv]

/-- Valid entries are quantified independently and share one process input;
the conclusion fixes the raw run fields for the declared input family.
model: explicit quantifiers over entries and inputs, with no predicate substituted for the run fields. -/
theorem strong_universal_T_either_iff (source target : Image) :
    strong_universal_T_either source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input_either inp →
      ¬ (run source source_alloc_limit es inp).bh_unmodeled ∧
      ((run source source_alloc_limit es inp).bh_all_errors ∨ ((∀ tr, (run source source_alloc_limit es inp).bh_traces tr ↔ (run target target_alloc_limit et inp).bh_traces tr) ∧ ¬ (run target target_alloc_limit et inp).bh_errors))) := by
  simp only [strong_universal_T_either, strong_equiv, modeled, equiv, trace_equiv]

/-- Valid entries are quantified independently and share one process input;
the conclusion fixes the raw run fields for the declared input family.
model: explicit quantifiers over entries and inputs, with no predicate substituted for the run fields. -/
theorem strong_universal_error_free_T_abort_iff (source target : Image) :
    strong_universal_error_free_T_abort source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input_abort inp →
      (¬ (run source source_alloc_limit es inp).bh_errors ∧
        ∀ tr, (run source source_alloc_limit es inp).bh_traces tr → ∀ e ∈ tr, ∀ sig fs, e ≠ KillEv sig fs) ∧ (¬ (run target target_alloc_limit et inp).bh_errors ∧
        ∀ tr, (run target target_alloc_limit et inp).bh_traces tr → ∀ e ∈ tr, ∀ sig fs, e ≠ KillEv sig fs) ∧
      (∀ tr, (run source source_alloc_limit es inp).bh_traces tr ↔ (run target target_alloc_limit et inp).bh_traces tr)) := by
  simp only [strong_universal_error_free_T_abort, strong_equiv_error_free_abort, error_free_unkilled_iff, trace_equiv]

/-- Valid entries are quantified independently and share one process input;
the conclusion fixes the raw run fields for the declared input family.
model: explicit quantifiers over entries and inputs, with no predicate substituted for the run fields. -/
theorem strong_universal_error_free_T_either_iff (source target : Image) :
    strong_universal_error_free_T_either source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input inp →
      ¬ (run source source_alloc_limit es inp).bh_errors ∧ ¬ (run target target_alloc_limit et inp).bh_errors ∧
      (∀ tr, (run source source_alloc_limit es inp).bh_traces tr ↔ (run target target_alloc_limit et inp).bh_traces tr)) ∧
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input_abort inp →
      (¬ (run source source_alloc_limit es inp).bh_errors ∧
        ∀ tr, (run source source_alloc_limit es inp).bh_traces tr → ∀ e ∈ tr, ∀ sig fs, e ≠ KillEv sig fs) ∧ (¬ (run target target_alloc_limit et inp).bh_errors ∧
        ∀ tr, (run target target_alloc_limit et inp).bh_traces tr → ∀ e ∈ tr, ∀ sig fs, e ≠ KillEv sig fs) ∧
      (∀ tr, (run source source_alloc_limit es inp).bh_traces tr ↔ (run target target_alloc_limit et inp).bh_traces tr)) := by
  simp only [strong_universal_error_free_T_either, strong_universal_error_free_T, strong_universal_error_free_T_abort, strong_equiv_error_free_abort, strong_equiv_error_free, error_free_unkilled_iff, error_free, trace_equiv]

/-- Valid entries are quantified independently and share one process input;
the conclusion fixes the raw run fields for the declared input family.
model: explicit quantifiers over entries and inputs, with no predicate substituted for the run fields. -/
theorem strong_universal_T_hwcap_rv64gc_iff (source target : Image) :
    strong_universal_T_hwcap_rv64gc source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input_hwcap_rv64gc inp →
      ¬ (run source source_alloc_limit es inp).bh_unmodeled ∧
      ((run source source_alloc_limit es inp).bh_all_errors ∨ ((∀ tr, (run source source_alloc_limit es inp).bh_traces tr ↔ (run target target_alloc_limit et inp).bh_traces tr) ∧ ¬ (run target target_alloc_limit et inp).bh_errors))) := by
  simp only [strong_universal_T_hwcap_rv64gc, strong_equiv, modeled, equiv, trace_equiv]

/-- Valid entries are quantified independently and share one process input;
the conclusion fixes the raw run fields for the declared input family.
model: explicit quantifiers over entries and inputs, with no predicate substituted for the run fields. -/
theorem strong_universal_T_hwcap_rv64gcv_iff (source target : Image) :
    strong_universal_T_hwcap_rv64gcv source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input_hwcap_rv64gcv inp →
      ¬ (run source source_alloc_limit es inp).bh_unmodeled ∧
      ((run source source_alloc_limit es inp).bh_all_errors ∨ ((∀ tr, (run source source_alloc_limit es inp).bh_traces tr ↔ (run target target_alloc_limit et inp).bh_traces tr) ∧ ¬ (run target target_alloc_limit et inp).bh_errors))) := by
  simp only [strong_universal_T_hwcap_rv64gcv, strong_equiv, modeled, equiv, trace_equiv]

/-- Valid entries are quantified independently and share one process input;
the conclusion fixes the raw run fields for the declared input family.
model: explicit quantifiers over entries and inputs, with no predicate substituted for the run fields. -/
theorem strong_universal_error_free_T_hwcap_rv64gc_iff (source target : Image) :
    strong_universal_error_free_T_hwcap_rv64gc source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input_hwcap_rv64gc inp →
      ¬ (run source source_alloc_limit es inp).bh_errors ∧ ¬ (run target target_alloc_limit et inp).bh_errors ∧
      (∀ tr, (run source source_alloc_limit es inp).bh_traces tr ↔ (run target target_alloc_limit et inp).bh_traces tr)) := by
  simp only [strong_universal_error_free_T_hwcap_rv64gc, strong_equiv_error_free, error_free, trace_equiv]

/-- Valid entries are quantified independently and share one process input;
the conclusion fixes the raw run fields for the declared input family.
model: explicit quantifiers over entries and inputs, with no predicate substituted for the run fields. -/
theorem strong_universal_error_free_T_hwcap_rv64gcv_iff (source target : Image) :
    strong_universal_error_free_T_hwcap_rv64gcv source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input_hwcap_rv64gcv inp →
      ¬ (run source source_alloc_limit es inp).bh_errors ∧ ¬ (run target target_alloc_limit et inp).bh_errors ∧
      (∀ tr, (run source source_alloc_limit es inp).bh_traces tr ↔ (run target target_alloc_limit et inp).bh_traces tr)) := by
  simp only [strong_universal_error_free_T_hwcap_rv64gcv, strong_equiv_error_free, error_free, trace_equiv]

/-- The terminating pilot satisfies baseline equivalence with abort enabled.
model: the pilot’s abort equivalence theorem combines its two termination proofs. -/
theorem strong_universal_T_abort_accept :
    strong_universal_T_abort Source.image Target.image :=
  Examples.rwx_flag_ns.Proof.strong_universal_abort

/-- The pilot satisfies both stances by termination, so leaving the stance open is safe.
model: the two pilot contracts discharge both halves of the stance split. -/
theorem strong_universal_T_either_accept :
    strong_universal_T_either Source.image Target.image := (strong_universal_T_either_splits _ _).2
      ⟨Examples.rwx_flag_ns.Proof.strong_universal, strong_universal_T_abort_accept⟩

/-- Both safety readings hold for the terminating pilot.
model: the pilot terminates with exit 5 under both input stances. -/
theorem strong_universal_error_free_T_either_accept :
    strong_universal_error_free_T_either Source.image Target.image := ⟨strong_universal_error_free_T_accept, strong_universal_error_free_T_abort_accept⟩

/-- The pilot terminates under the RV64GC declaration; this narrows an inhabited input family.
model: the pilot universal proof projects through the hardware-capability split. -/
theorem strong_universal_T_hwcap_rv64gc_accept :
    strong_universal_T_hwcap_rv64gc Source.image Target.image := ((strong_universal_T_hwcap_splits _ _).1 Examples.rwx_flag_ns.Proof.strong_universal).1

/-- The pilot terminates under the RV64GCV declaration; this narrows an inhabited input family.
model: the pilot universal proof projects through the hardware-capability split. -/
theorem strong_universal_T_hwcap_rv64gcv_accept :
    strong_universal_T_hwcap_rv64gcv Source.image Target.image := ((strong_universal_T_hwcap_splits _ _).1 Examples.rwx_flag_ns.Proof.strong_universal).2

/-- The pilot terminates under the RV64GC declaration; this narrows an inhabited input family.
model: the pilot universal proof projects through the hardware-capability split. -/
theorem strong_universal_error_free_T_hwcap_rv64gc_accept :
    strong_universal_error_free_T_hwcap_rv64gc Source.image Target.image := ((strong_universal_error_free_T_hwcap_splits _ _).1 strong_universal_error_free_T_accept).1

/-- The pilot terminates under the RV64GCV declaration; this narrows an inhabited input family.
model: the pilot universal proof projects through the hardware-capability split. -/
theorem strong_universal_error_free_T_hwcap_rv64gcv_accept :
    strong_universal_error_free_T_hwcap_rv64gcv Source.image Target.image := ((strong_universal_error_free_T_hwcap_splits _ _).1 strong_universal_error_free_T_accept).2

/-- The undecodable image errors on its first fetch at a valid triple, even against itself
(Rocq: `Checks.Examples.undecodable_image_refutes_error_free_equivalence`).
model: `strong_universal_error_free_refuted_by_source_error` fired at the undecodable run, which is unmodeled and so errors. -/
theorem undecodable_image_refutes_error_free_equivalence :
    ¬ strong_universal_error_free_T undecodable_image undecodable_image := strong_universal_error_free_refuted_by_source_error _ _ demo_entry demo_entry demo_proc_input
      undecodable_off_entry undecodable_off_entry Checks.Omni.demo_input_valid
      (run_unmodeled_errors _ _ _ _ (undecodable_run_unmodeled _ _))

/-- The first undecodable fetch fails coverage at a valid entry and an input in this declaration.
model: the concrete undecodable run reaches the error transition before any observation. -/
theorem strong_universal_T_abort_refute :
    ¬ strong_universal_T_abort undecodable_image undecodable_image := by
  intro h
  exact unmodeled_source_refutes_strong_equiv _ _ _ _ _ (undecodable_run_unmodeled _ _)
    (h demo_entry demo_entry abort_input undecodable_abort_entry undecodable_abort_entry
      abort_input_valid)

/-- The first undecodable fetch fails coverage at a valid entry and an input in this declaration.
model: the concrete undecodable run reaches the error transition before any observation. -/
theorem strong_universal_T_either_refute :
    ¬ strong_universal_T_either undecodable_image undecodable_image := by
  intro h
  exact unmodeled_source_refutes_strong_equiv _ _ _ _ _ (undecodable_run_unmodeled _ _)
    (h demo_entry demo_entry demo_proc_input undecodable_off_entry undecodable_off_entry
      (valid_input_either_of_valid_input _ Checks.Omni.demo_input_valid))

/-- The first undecodable fetch fails coverage at a valid entry and an input in this declaration.
model: the concrete undecodable run reaches the error transition before any observation. -/
theorem strong_universal_error_free_T_abort_refute :
    ¬ strong_universal_error_free_T_abort undecodable_image undecodable_image := by
  intro h
  exact (h demo_entry demo_entry abort_input undecodable_abort_entry undecodable_abort_entry
    abort_input_valid).1.1 (run_unmodeled_errors _ _ _ _ (undecodable_run_unmodeled _ _))

/-- The first undecodable fetch fails coverage at a valid entry and an input in this declaration.
model: the concrete undecodable run reaches the error transition before any observation. -/
theorem strong_universal_error_free_T_either_refute :
    ¬ strong_universal_error_free_T_either undecodable_image undecodable_image := fun h => undecodable_image_refutes_error_free_equivalence h.1

/-- The first undecodable fetch fails coverage at a valid entry and an input in this declaration.
model: the concrete undecodable run reaches the error transition before any observation. -/
theorem strong_universal_T_hwcap_rv64gc_refute :
    ¬ strong_universal_T_hwcap_rv64gc undecodable_image undecodable_image := by
  intro h
  exact unmodeled_source_refutes_strong_equiv _ _ _ _ _ (undecodable_run_unmodeled _ _)
    (h demo_entry demo_entry demo_proc_input undecodable_off_entry undecodable_off_entry
      scalar_input_valid)

/-- The first undecodable fetch fails coverage at a valid entry and an input in this declaration.
model: the concrete undecodable run reaches the error transition before any observation. -/
theorem strong_universal_T_hwcap_rv64gcv_refute :
    ¬ strong_universal_T_hwcap_rv64gcv undecodable_image undecodable_image := by
  intro h
  exact unmodeled_source_refutes_strong_equiv _ _ _ _ _ (undecodable_run_unmodeled _ _)
    (h demo_entry demo_entry vector_input undecodable_vector_entry undecodable_vector_entry
      vector_input_valid)

/-- The first undecodable fetch fails coverage at a valid entry and an input in this declaration.
model: the concrete undecodable run reaches the error transition before any observation. -/
theorem strong_universal_error_free_T_hwcap_rv64gc_refute :
    ¬ strong_universal_error_free_T_hwcap_rv64gc undecodable_image undecodable_image := by
  intro h
  exact (h demo_entry demo_entry demo_proc_input undecodable_off_entry undecodable_off_entry
    scalar_input_valid).1 (run_unmodeled_errors _ _ _ _ (undecodable_run_unmodeled _ _))

/-- The first undecodable fetch fails coverage at a valid entry and an input in this declaration.
model: the concrete undecodable run reaches the error transition before any observation. -/
theorem strong_universal_error_free_T_hwcap_rv64gcv_refute :
    ¬ strong_universal_error_free_T_hwcap_rv64gcv undecodable_image undecodable_image := by
  intro h
  exact (h demo_entry demo_entry vector_input undecodable_vector_entry undecodable_vector_entry
    vector_input_valid).1 (run_unmodeled_errors _ _ _ _ (undecodable_run_unmodeled _ _))

/-- The quiet record's four fields characterize a behavior independently.
model: only the empty trace exists and all three exceptional fields are absent. -/
theorem quiet_behavior_iff (b : behavior) :
    behavior_equiv b quiet_behavior ↔
      (∀ tr, b.bh_traces tr ↔ tr = []) ∧
      ¬ b.bh_errors ∧ ¬ b.bh_all_errors ∧ ¬ b.bh_unmodeled := by
  simp only [behavior_equiv, quiet_behavior, iff_false]

/-- The quiet record satisfies its complete field characterization.
model: reflexivity of behavior equivalence on the concrete quiet record. -/
theorem quiet_behavior_accept : behavior_equiv quiet_behavior quiet_behavior :=
  behavior_equiv_refl _

/-- A possible crash distinguishes the quiet record from the crashing one.
model: behavior equivalence must preserve the possible-error field. -/
theorem quiet_behavior_refute : ¬ behavior_equiv crashing_behavior quiet_behavior :=
  fun h => h.2.1.mp True.intro

/-- The crashing record keeps empty traces but both error fields hold.
model: raw trace and exception fields, with no claim that this record is a run. -/
theorem crashing_behavior_iff (b : behavior) :
    behavior_equiv b crashing_behavior ↔
      (∀ tr, b.bh_traces tr ↔ tr = []) ∧
      b.bh_errors ∧ b.bh_all_errors ∧ ¬ b.bh_unmodeled := by
  simp only [behavior_equiv, crashing_behavior, iff_true, iff_false]

/-- A crash record satisfies its field characterization despite being modeled.
model: reflexivity of behavior equivalence on the concrete crashing record. -/
theorem crashing_behavior_accept : behavior_equiv crashing_behavior crashing_behavior :=
  behavior_equiv_refl _

/-- The quiet record has no error and cannot be the crashing behavior.
model: the possible-error fields disagree. -/
theorem crashing_behavior_refute : ¬ behavior_equiv quiet_behavior crashing_behavior :=
  fun h => h.2.1.mpr True.intro

/-- Basic argv has exactly one argument and that argument is empty.
model: length and membership characterize the concrete argument vector. -/
theorem basic_argv_iff (argv : List (List byte)) :
    argv = basic_argv ↔ argv.length = 1 ∧ ∀ arg ∈ argv, arg = [] := by
  constructor
  · rintro rfl
    refine ⟨rfl, ?_⟩
    intro arg h
    exact List.mem_singleton.mp h
  · rintro ⟨hlen, hall⟩
    obtain ⟨arg, rfl⟩ := List.length_eq_one_iff.mp hlen
    have h := hall arg List.mem_cons_self
    cases h
    rfl

/-- argc = 1 with an empty first argument is the basic vector.
model: the concrete singleton empty argument matches both clauses. -/
theorem basic_argv_accept : ([[]] : List (List byte)) = basic_argv := rfl

/-- argc = 0 is different from an empty first argument.
model: the basic vector has one list cell, not zero. -/
theorem basic_argv_refute : ([] : List (List byte)) ≠ basic_argv := by
  intro h
  cases h

/-- The pilot's independently valid entries instantiate the safety theorem.
model: the pilot domain witnesses make this a concrete non-vacuous triple. -/
theorem strong_equiv_error_free_accept :
    strong_equiv_error_free Source.image Target.image
      Examples.rwx_flag_ns.Domain.source_entry Examples.rwx_flag_ns.Domain.target_entry
      demo_proc_input :=
  strong_universal_error_free_T_accept _ _ _
    (Examples.rwx_flag_ns.Domain.source_entry_valid demo_proc_input Checks.Omni.demo_input_valid)
    (Examples.rwx_flag_ns.Domain.target_entry_valid demo_proc_input Checks.Omni.demo_input_valid)
    Checks.Omni.demo_input_valid

/-- The abort input leaves the entry geometry and stack payload unchanged.
model: `valid_entry` depends on the same address size, argv and envp in both records. -/
theorem pilot_abort_entries_valid :
    valid_entry Source.image Examples.rwx_flag_ns.Domain.source_entry abort_input ∧
    valid_entry Target.image Examples.rwx_flag_ns.Domain.target_entry abort_input :=
  ⟨Examples.rwx_flag_ns.Domain.source_entry_valid demo_proc_input Checks.Omni.demo_input_valid,
    Examples.rwx_flag_ns.Domain.target_entry_valid demo_proc_input Checks.Omni.demo_input_valid⟩

/-- The same pilot at valid entries also establishes no signal death.
model: instantiate the abort safety theorem at the concrete abort input. -/
theorem strong_equiv_error_free_abort_accept :
    strong_equiv_error_free_abort Source.image Target.image
      Examples.rwx_flag_ns.Domain.source_entry Examples.rwx_flag_ns.Domain.target_entry
      abort_input :=
  strong_universal_error_free_T_abort_accept _ _ _
    pilot_abort_entries_valid.1 pilot_abort_entries_valid.2 abort_input_valid

/-- Even identical images fail the safety triple when their first fetch errors.
model: the undecodable demo-entry run has a reachable error. -/
theorem strong_equiv_error_free_refute :
    ¬ strong_equiv_error_free undecodable_image undecodable_image demo_entry demo_entry demo_proc_input :=
  fun h => h.1 (run_unmodeled_errors _ _ _ _ (undecodable_run_unmodeled _ _))

/-- Turning on abort does not make an undecodable instruction safe.
model: the first-fetch error also refutes the error-free conjunct under abort. -/
theorem strong_equiv_error_free_abort_refute :
    ¬ strong_equiv_error_free_abort undecodable_image undecodable_image demo_entry demo_entry abort_input :=
  fun h => h.1.1 (run_unmodeled_errors _ _ _ _ (undecodable_run_unmodeled _ _))

/-- Sealing preserves the entire quantified obligation, including its input declaration.
model: the structure's sole field is characterized by explicit raw-run quantifiers. -/
theorem SPEC_ERROR_FREE_iff (source target : Image) :
    SPEC_ERROR_FREE source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input inp →
      ¬ (run source source_alloc_limit es inp).bh_errors ∧ ¬ (run target target_alloc_limit et inp).bh_errors ∧
      (∀ tr, (run source source_alloc_limit es inp).bh_traces tr ↔ (run target target_alloc_limit et inp).bh_traces tr)) := by
  constructor
  · intro h
    exact (strong_universal_error_free_T_iff _ _).1 h.strong_universal_error_free
  · intro h
    exact ⟨(strong_universal_error_free_T_iff _ _).2 h⟩

/-- The terminating pilot supplies the sealed obligation without vacuity.
model: the concrete pilot contract inhabits this declaration's sealing structure. -/
theorem SPEC_ERROR_FREE_accept : SPEC_ERROR_FREE Source.image Target.image :=
  ⟨strong_universal_error_free_T_accept⟩

/-- Sealing cannot hide the undecodable source's failure at a valid triple.
model: extracting the sealed field exposes the concrete undecodable-run refutation. -/
theorem SPEC_ERROR_FREE_refute : ¬ SPEC_ERROR_FREE undecodable_image undecodable_image :=
  fun h => undecodable_image_refutes_error_free_equivalence h.strong_universal_error_free

/-- Sealing preserves the entire quantified obligation, including its input declaration.
model: the structure's sole field is characterized by explicit raw-run quantifiers. -/
theorem SPEC_ABORT_iff (source target : Image) :
    SPEC_ABORT source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input_abort inp →
      ¬ (run source source_alloc_limit es inp).bh_unmodeled ∧
      ((run source source_alloc_limit es inp).bh_all_errors ∨ ((∀ tr, (run source source_alloc_limit es inp).bh_traces tr ↔ (run target target_alloc_limit et inp).bh_traces tr) ∧ ¬ (run target target_alloc_limit et inp).bh_errors))) := by
  constructor
  · intro h
    exact (strong_universal_T_abort_iff _ _).1 h.strong_universal
  · intro h
    exact ⟨(strong_universal_T_abort_iff _ _).2 h⟩

/-- The terminating pilot supplies the sealed obligation without vacuity.
model: the concrete pilot contract inhabits this declaration's sealing structure. -/
theorem SPEC_ABORT_accept : SPEC_ABORT Source.image Target.image :=
  ⟨strong_universal_T_abort_accept⟩

/-- Sealing cannot hide the undecodable source's failure at a valid triple.
model: extracting the sealed field exposes the concrete undecodable-run refutation. -/
theorem SPEC_ABORT_refute : ¬ SPEC_ABORT undecodable_image undecodable_image :=
  fun h => strong_universal_T_abort_refute h.strong_universal

/-- Sealing preserves the entire quantified obligation, including its input declaration.
model: the structure's sole field is characterized by explicit raw-run quantifiers. -/
theorem SPEC_EITHER_iff (source target : Image) :
    SPEC_EITHER source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input_either inp →
      ¬ (run source source_alloc_limit es inp).bh_unmodeled ∧
      ((run source source_alloc_limit es inp).bh_all_errors ∨ ((∀ tr, (run source source_alloc_limit es inp).bh_traces tr ↔ (run target target_alloc_limit et inp).bh_traces tr) ∧ ¬ (run target target_alloc_limit et inp).bh_errors))) := by
  constructor
  · intro h
    exact (strong_universal_T_either_iff _ _).1 h.strong_universal
  · intro h
    exact ⟨(strong_universal_T_either_iff _ _).2 h⟩

/-- The terminating pilot supplies the sealed obligation without vacuity.
model: the concrete pilot contract inhabits this declaration's sealing structure. -/
theorem SPEC_EITHER_accept : SPEC_EITHER Source.image Target.image :=
  ⟨strong_universal_T_either_accept⟩

/-- Sealing cannot hide the undecodable source's failure at a valid triple.
model: extracting the sealed field exposes the concrete undecodable-run refutation. -/
theorem SPEC_EITHER_refute : ¬ SPEC_EITHER undecodable_image undecodable_image :=
  fun h => strong_universal_T_either_refute h.strong_universal

/-- Sealing preserves the entire quantified obligation, including its input declaration.
model: the structure's sole field is characterized by explicit raw-run quantifiers. -/
theorem SPEC_ERROR_FREE_ABORT_iff (source target : Image) :
    SPEC_ERROR_FREE_ABORT source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input_abort inp →
      (¬ (run source source_alloc_limit es inp).bh_errors ∧
        ∀ tr, (run source source_alloc_limit es inp).bh_traces tr → ∀ e ∈ tr, ∀ sig fs, e ≠ KillEv sig fs) ∧ (¬ (run target target_alloc_limit et inp).bh_errors ∧
        ∀ tr, (run target target_alloc_limit et inp).bh_traces tr → ∀ e ∈ tr, ∀ sig fs, e ≠ KillEv sig fs) ∧
      (∀ tr, (run source source_alloc_limit es inp).bh_traces tr ↔ (run target target_alloc_limit et inp).bh_traces tr)) := by
  constructor
  · intro h
    exact (strong_universal_error_free_T_abort_iff _ _).1 h.strong_universal_error_free
  · intro h
    exact ⟨(strong_universal_error_free_T_abort_iff _ _).2 h⟩

/-- The terminating pilot supplies the sealed obligation without vacuity.
model: the concrete pilot contract inhabits this declaration's sealing structure. -/
theorem SPEC_ERROR_FREE_ABORT_accept : SPEC_ERROR_FREE_ABORT Source.image Target.image :=
  ⟨strong_universal_error_free_T_abort_accept⟩

/-- Sealing cannot hide the undecodable source's failure at a valid triple.
model: extracting the sealed field exposes the concrete undecodable-run refutation. -/
theorem SPEC_ERROR_FREE_ABORT_refute : ¬ SPEC_ERROR_FREE_ABORT undecodable_image undecodable_image :=
  fun h => strong_universal_error_free_T_abort_refute h.strong_universal_error_free

/-- Sealing preserves the entire quantified obligation, including its input declaration.
model: the structure's sole field is characterized by explicit raw-run quantifiers. -/
theorem SPEC_ERROR_FREE_EITHER_iff (source target : Image) :
    SPEC_ERROR_FREE_EITHER source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input inp →
      ¬ (run source source_alloc_limit es inp).bh_errors ∧ ¬ (run target target_alloc_limit et inp).bh_errors ∧
      (∀ tr, (run source source_alloc_limit es inp).bh_traces tr ↔ (run target target_alloc_limit et inp).bh_traces tr)) ∧
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input_abort inp →
      (¬ (run source source_alloc_limit es inp).bh_errors ∧
        ∀ tr, (run source source_alloc_limit es inp).bh_traces tr → ∀ e ∈ tr, ∀ sig fs, e ≠ KillEv sig fs) ∧ (¬ (run target target_alloc_limit et inp).bh_errors ∧
        ∀ tr, (run target target_alloc_limit et inp).bh_traces tr → ∀ e ∈ tr, ∀ sig fs, e ≠ KillEv sig fs) ∧
      (∀ tr, (run source source_alloc_limit es inp).bh_traces tr ↔ (run target target_alloc_limit et inp).bh_traces tr)) := by
  constructor
  · intro h
    exact (strong_universal_error_free_T_either_iff _ _).1 h.strong_universal_error_free
  · intro h
    exact ⟨(strong_universal_error_free_T_either_iff _ _).2 h⟩

/-- The terminating pilot supplies the sealed obligation without vacuity.
model: the concrete pilot contract inhabits this declaration's sealing structure. -/
theorem SPEC_ERROR_FREE_EITHER_accept : SPEC_ERROR_FREE_EITHER Source.image Target.image :=
  ⟨strong_universal_error_free_T_either_accept⟩

/-- Sealing cannot hide the undecodable source's failure at a valid triple.
model: extracting the sealed field exposes the concrete undecodable-run refutation. -/
theorem SPEC_ERROR_FREE_EITHER_refute : ¬ SPEC_ERROR_FREE_EITHER undecodable_image undecodable_image :=
  fun h => strong_universal_error_free_T_either_refute h.strong_universal_error_free

/-- Sealing preserves the entire quantified obligation, including its input declaration.
model: the structure's sole field is characterized by explicit raw-run quantifiers. -/
theorem SPEC_HWCAP_RV64GC_iff (source target : Image) :
    SPEC_HWCAP_RV64GC source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input_hwcap_rv64gc inp →
      ¬ (run source source_alloc_limit es inp).bh_unmodeled ∧
      ((run source source_alloc_limit es inp).bh_all_errors ∨ ((∀ tr, (run source source_alloc_limit es inp).bh_traces tr ↔ (run target target_alloc_limit et inp).bh_traces tr) ∧ ¬ (run target target_alloc_limit et inp).bh_errors))) := by
  constructor
  · intro h
    exact (strong_universal_T_hwcap_rv64gc_iff _ _).1 h.strong_universal
  · intro h
    exact ⟨(strong_universal_T_hwcap_rv64gc_iff _ _).2 h⟩

/-- The terminating pilot supplies the sealed obligation without vacuity.
model: the concrete pilot contract inhabits this declaration's sealing structure. -/
theorem SPEC_HWCAP_RV64GC_accept : SPEC_HWCAP_RV64GC Source.image Target.image :=
  ⟨strong_universal_T_hwcap_rv64gc_accept⟩

/-- Sealing cannot hide the undecodable source's failure at a valid triple.
model: extracting the sealed field exposes the concrete undecodable-run refutation. -/
theorem SPEC_HWCAP_RV64GC_refute : ¬ SPEC_HWCAP_RV64GC undecodable_image undecodable_image :=
  fun h => strong_universal_T_hwcap_rv64gc_refute h.strong_universal

/-- Sealing preserves the entire quantified obligation, including its input declaration.
model: the structure's sole field is characterized by explicit raw-run quantifiers. -/
theorem SPEC_HWCAP_RV64GCV_iff (source target : Image) :
    SPEC_HWCAP_RV64GCV source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input_hwcap_rv64gcv inp →
      ¬ (run source source_alloc_limit es inp).bh_unmodeled ∧
      ((run source source_alloc_limit es inp).bh_all_errors ∨ ((∀ tr, (run source source_alloc_limit es inp).bh_traces tr ↔ (run target target_alloc_limit et inp).bh_traces tr) ∧ ¬ (run target target_alloc_limit et inp).bh_errors))) := by
  constructor
  · intro h
    exact (strong_universal_T_hwcap_rv64gcv_iff _ _).1 h.strong_universal
  · intro h
    exact ⟨(strong_universal_T_hwcap_rv64gcv_iff _ _).2 h⟩

/-- The terminating pilot supplies the sealed obligation without vacuity.
model: the concrete pilot contract inhabits this declaration's sealing structure. -/
theorem SPEC_HWCAP_RV64GCV_accept : SPEC_HWCAP_RV64GCV Source.image Target.image :=
  ⟨strong_universal_T_hwcap_rv64gcv_accept⟩

/-- Sealing cannot hide the undecodable source's failure at a valid triple.
model: extracting the sealed field exposes the concrete undecodable-run refutation. -/
theorem SPEC_HWCAP_RV64GCV_refute : ¬ SPEC_HWCAP_RV64GCV undecodable_image undecodable_image :=
  fun h => strong_universal_T_hwcap_rv64gcv_refute h.strong_universal

/-- Sealing preserves the entire quantified obligation, including its input declaration.
model: the structure's sole field is characterized by explicit raw-run quantifiers. -/
theorem SPEC_ERROR_FREE_HWCAP_RV64GC_iff (source target : Image) :
    SPEC_ERROR_FREE_HWCAP_RV64GC source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input_hwcap_rv64gc inp →
      ¬ (run source source_alloc_limit es inp).bh_errors ∧ ¬ (run target target_alloc_limit et inp).bh_errors ∧
      (∀ tr, (run source source_alloc_limit es inp).bh_traces tr ↔ (run target target_alloc_limit et inp).bh_traces tr)) := by
  constructor
  · intro h
    exact (strong_universal_error_free_T_hwcap_rv64gc_iff _ _).1 h.strong_universal_error_free
  · intro h
    exact ⟨(strong_universal_error_free_T_hwcap_rv64gc_iff _ _).2 h⟩

/-- The terminating pilot supplies the sealed obligation without vacuity.
model: the concrete pilot contract inhabits this declaration's sealing structure. -/
theorem SPEC_ERROR_FREE_HWCAP_RV64GC_accept : SPEC_ERROR_FREE_HWCAP_RV64GC Source.image Target.image :=
  ⟨strong_universal_error_free_T_hwcap_rv64gc_accept⟩

/-- Sealing cannot hide the undecodable source's failure at a valid triple.
model: extracting the sealed field exposes the concrete undecodable-run refutation. -/
theorem SPEC_ERROR_FREE_HWCAP_RV64GC_refute : ¬ SPEC_ERROR_FREE_HWCAP_RV64GC undecodable_image undecodable_image :=
  fun h => strong_universal_error_free_T_hwcap_rv64gc_refute h.strong_universal_error_free

/-- Sealing preserves the entire quantified obligation, including its input declaration.
model: the structure's sole field is characterized by explicit raw-run quantifiers. -/
theorem SPEC_ERROR_FREE_HWCAP_RV64GCV_iff (source target : Image) :
    SPEC_ERROR_FREE_HWCAP_RV64GCV source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input_hwcap_rv64gcv inp →
      ¬ (run source source_alloc_limit es inp).bh_errors ∧ ¬ (run target target_alloc_limit et inp).bh_errors ∧
      (∀ tr, (run source source_alloc_limit es inp).bh_traces tr ↔ (run target target_alloc_limit et inp).bh_traces tr)) := by
  constructor
  · intro h
    exact (strong_universal_error_free_T_hwcap_rv64gcv_iff _ _).1 h.strong_universal_error_free
  · intro h
    exact ⟨(strong_universal_error_free_T_hwcap_rv64gcv_iff _ _).2 h⟩

/-- The terminating pilot supplies the sealed obligation without vacuity.
model: the concrete pilot contract inhabits this declaration's sealing structure. -/
theorem SPEC_ERROR_FREE_HWCAP_RV64GCV_accept : SPEC_ERROR_FREE_HWCAP_RV64GCV Source.image Target.image :=
  ⟨strong_universal_error_free_T_hwcap_rv64gcv_accept⟩

/-- Sealing cannot hide the undecodable source's failure at a valid triple.
model: extracting the sealed field exposes the concrete undecodable-run refutation. -/
theorem SPEC_ERROR_FREE_HWCAP_RV64GCV_refute : ¬ SPEC_ERROR_FREE_HWCAP_RV64GCV undecodable_image undecodable_image :=
  fun h => strong_universal_error_free_T_hwcap_rv64gcv_refute h.strong_universal_error_free

/-! ## A-Equiv-scfg: the configured (_scfg and _cfg) statements -/

/--
model: the initial configuration itself witnesses `reaches_unmodeled_cfg`. -/
theorem undecodable_run_scfg_unmodeled (cfg : SpuriousCfg) (lim : Int) (inp : ProcInput) :
    (run_scfg cfg undecodable_image lim demo_entry inp).bh_unmodeled := by
  refine ⟨[], _, star_cfg.star_cfg_refl _, rfl, Or.inl ⟨rfl, ?_⟩⟩
  rw [mi_account_step_no_lazy _ _ _ rfl]
  rw [step_of_fetch _ _ 0xffffffff (by
    change fetch_word undecodable_segments 0x100 = some 0xffffffff
    decide +kernel)]
  rfl

/-- The triple compares the two configured runs, each on its role's budget.
model: raw configured-run fields, with no predicate substituted for them.
-/
theorem strong_equiv_scfg_iff (cfg : SpuriousCfg) (source target : Image) (es et : ExecEntry) (inp : ProcInput) :
    strong_equiv_scfg cfg source target es et inp ↔
    ¬ (run_scfg cfg source source_alloc_limit es inp).bh_unmodeled ∧
      ((run_scfg cfg source source_alloc_limit es inp).bh_all_errors ∨
        ((∀ tr, (run_scfg cfg source source_alloc_limit es inp).bh_traces tr ↔
        (run_scfg cfg target target_alloc_limit et inp).bh_traces tr) ∧ ¬ (run_scfg cfg target target_alloc_limit et inp).bh_errors)) := Iff.rfl

/-- Valid entries are quantified independently and share one process input;
the conclusion fixes the raw configured-run fields for the declared input family.
model: explicit quantifiers over entries and inputs, with no predicate substituted for the run fields.
-/
theorem strong_universal_T_scfg_iff (cfg : SpuriousCfg) (source target : Image) :
    strong_universal_T_scfg cfg source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input inp →
      ¬ (run_scfg cfg source source_alloc_limit es inp).bh_unmodeled ∧
      ((run_scfg cfg source source_alloc_limit es inp).bh_all_errors ∨
        ((∀ tr, (run_scfg cfg source source_alloc_limit es inp).bh_traces tr ↔
        (run_scfg cfg target target_alloc_limit et inp).bh_traces tr) ∧ ¬ (run_scfg cfg target target_alloc_limit et inp).bh_errors))) := Iff.rfl

/-- The triple compares the two configured runs, each on its role's budget.
model: raw configured-run fields, with no predicate substituted for them.
-/
theorem strong_equiv_error_free_scfg_iff (cfg : SpuriousCfg) (source target : Image) (es et : ExecEntry) (inp : ProcInput) :
    strong_equiv_error_free_scfg cfg source target es et inp ↔
    ¬ (run_scfg cfg source source_alloc_limit es inp).bh_errors ∧
      ¬ (run_scfg cfg target target_alloc_limit et inp).bh_errors ∧
      (∀ tr, (run_scfg cfg source source_alloc_limit es inp).bh_traces tr ↔
        (run_scfg cfg target target_alloc_limit et inp).bh_traces tr) := Iff.rfl

/-- Valid entries are quantified independently and share one process input;
the conclusion fixes the raw configured-run fields for the declared input family.
model: explicit quantifiers over entries and inputs, with no predicate substituted for the run fields.
-/
theorem strong_universal_error_free_T_scfg_iff (cfg : SpuriousCfg) (source target : Image) :
    strong_universal_error_free_T_scfg cfg source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input inp →
      ¬ (run_scfg cfg source source_alloc_limit es inp).bh_errors ∧
      ¬ (run_scfg cfg target target_alloc_limit et inp).bh_errors ∧
      (∀ tr, (run_scfg cfg source source_alloc_limit es inp).bh_traces tr ↔
        (run_scfg cfg target target_alloc_limit et inp).bh_traces tr)) := Iff.rfl

/-- Valid entries are quantified independently and share one process input;
the conclusion fixes the raw configured-run fields for the declared input family.
model: explicit quantifiers over entries and inputs, with no predicate substituted for the run fields.
-/
theorem strong_universal_T_scfg_abort_iff (cfg : SpuriousCfg) (source target : Image) :
    strong_universal_T_scfg_abort cfg source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input_abort inp →
      ¬ (run_scfg cfg source source_alloc_limit es inp).bh_unmodeled ∧
      ((run_scfg cfg source source_alloc_limit es inp).bh_all_errors ∨
        ((∀ tr, (run_scfg cfg source source_alloc_limit es inp).bh_traces tr ↔
        (run_scfg cfg target target_alloc_limit et inp).bh_traces tr) ∧ ¬ (run_scfg cfg target target_alloc_limit et inp).bh_errors))) := Iff.rfl

/-- Valid entries are quantified independently and share one process input;
the conclusion fixes the raw configured-run fields for the declared input family.
model: explicit quantifiers over entries and inputs, with no predicate substituted for the run fields.
-/
theorem strong_universal_T_scfg_either_iff (cfg : SpuriousCfg) (source target : Image) :
    strong_universal_T_scfg_either cfg source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input_either inp →
      ¬ (run_scfg cfg source source_alloc_limit es inp).bh_unmodeled ∧
      ((run_scfg cfg source source_alloc_limit es inp).bh_all_errors ∨
        ((∀ tr, (run_scfg cfg source source_alloc_limit es inp).bh_traces tr ↔
        (run_scfg cfg target target_alloc_limit et inp).bh_traces tr) ∧ ¬ (run_scfg cfg target target_alloc_limit et inp).bh_errors))) := Iff.rfl

/-- The triple compares the two configured runs, each on its role's budget.
model: raw configured-run fields, with no predicate substituted for them.
-/
theorem strong_equiv_error_free_scfg_abort_iff (cfg : SpuriousCfg) (source target : Image) (es et : ExecEntry) (inp : ProcInput) :
    strong_equiv_error_free_scfg_abort cfg source target es et inp ↔
    (¬ (run_scfg cfg source source_alloc_limit es inp).bh_errors ∧
        ∀ tr, (run_scfg cfg source source_alloc_limit es inp).bh_traces tr →
          ∀ e ∈ tr, ∀ sig fs, e ≠ KillEv sig fs) ∧
      (¬ (run_scfg cfg target target_alloc_limit et inp).bh_errors ∧
        ∀ tr, (run_scfg cfg target target_alloc_limit et inp).bh_traces tr →
          ∀ e ∈ tr, ∀ sig fs, e ≠ KillEv sig fs) ∧
      (∀ tr, (run_scfg cfg source source_alloc_limit es inp).bh_traces tr ↔
        (run_scfg cfg target target_alloc_limit et inp).bh_traces tr) :=
  and_congr (error_free_unkilled_iff _) (and_congr (error_free_unkilled_iff _) Iff.rfl)

/-- Valid entries are quantified independently and share one process input;
the conclusion fixes the raw configured-run fields for the declared input family.
model: explicit quantifiers over entries and inputs, with no predicate substituted for the run fields.
-/
theorem strong_universal_error_free_T_scfg_abort_iff (cfg : SpuriousCfg) (source target : Image) :
    strong_universal_error_free_T_scfg_abort cfg source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input_abort inp →
      (¬ (run_scfg cfg source source_alloc_limit es inp).bh_errors ∧
        ∀ tr, (run_scfg cfg source source_alloc_limit es inp).bh_traces tr →
          ∀ e ∈ tr, ∀ sig fs, e ≠ KillEv sig fs) ∧
      (¬ (run_scfg cfg target target_alloc_limit et inp).bh_errors ∧
        ∀ tr, (run_scfg cfg target target_alloc_limit et inp).bh_traces tr →
          ∀ e ∈ tr, ∀ sig fs, e ≠ KillEv sig fs) ∧
      (∀ tr, (run_scfg cfg source source_alloc_limit es inp).bh_traces tr ↔
        (run_scfg cfg target target_alloc_limit et inp).bh_traces tr)) := by
  constructor
  · intro h es et inp hs ht hi
    exact (strong_equiv_error_free_scfg_abort_iff cfg source target es et inp).1
      (h es et inp hs ht hi)
  · intro h es et inp hs ht hi
    exact (strong_equiv_error_free_scfg_abort_iff cfg source target es et inp).2
      (h es et inp hs ht hi)

/-- Valid entries are quantified independently and share one process input;
the conclusion fixes the raw configured-run fields for the declared input family.
model: explicit quantifiers over entries and inputs, with no predicate substituted for the run fields.
-/
theorem strong_universal_error_free_T_scfg_either_iff (cfg : SpuriousCfg) (source target : Image) :
    strong_universal_error_free_T_scfg_either cfg source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input inp →
      ¬ (run_scfg cfg source source_alloc_limit es inp).bh_errors ∧
      ¬ (run_scfg cfg target target_alloc_limit et inp).bh_errors ∧
      (∀ tr, (run_scfg cfg source source_alloc_limit es inp).bh_traces tr ↔
        (run_scfg cfg target target_alloc_limit et inp).bh_traces tr)) ∧
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input_abort inp →
      (¬ (run_scfg cfg source source_alloc_limit es inp).bh_errors ∧
        ∀ tr, (run_scfg cfg source source_alloc_limit es inp).bh_traces tr →
          ∀ e ∈ tr, ∀ sig fs, e ≠ KillEv sig fs) ∧
      (¬ (run_scfg cfg target target_alloc_limit et inp).bh_errors ∧
        ∀ tr, (run_scfg cfg target target_alloc_limit et inp).bh_traces tr →
          ∀ e ∈ tr, ∀ sig fs, e ≠ KillEv sig fs) ∧
      (∀ tr, (run_scfg cfg source source_alloc_limit es inp).bh_traces tr ↔
        (run_scfg cfg target target_alloc_limit et inp).bh_traces tr)) :=
  and_congr (strong_universal_error_free_T_scfg_iff cfg source target)
    (strong_universal_error_free_T_scfg_abort_iff cfg source target)

/-- Valid entries are quantified independently and share one process input;
the conclusion fixes the raw configured-run fields for the declared input family.
model: explicit quantifiers over entries and inputs, with no predicate substituted for the run fields.
-/
theorem strong_universal_T_cfg_iff (alloc_may_fail : Bool) (source target : Image) :
    strong_universal_T_cfg alloc_may_fail source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input inp →
      ¬ (run_scfg (alloc_only_cfg alloc_may_fail) source source_alloc_limit es inp).bh_unmodeled ∧
      ((run_scfg (alloc_only_cfg alloc_may_fail) source source_alloc_limit es inp).bh_all_errors ∨
        ((∀ tr, (run_scfg (alloc_only_cfg alloc_may_fail) source source_alloc_limit es inp).bh_traces tr ↔
        (run_scfg (alloc_only_cfg alloc_may_fail) target target_alloc_limit et inp).bh_traces tr) ∧ ¬ (run_scfg (alloc_only_cfg alloc_may_fail) target target_alloc_limit et inp).bh_errors))) := Iff.rfl

/-- Valid entries are quantified independently and share one process input;
the conclusion fixes the raw configured-run fields for the declared input family.
model: explicit quantifiers over entries and inputs, with no predicate substituted for the run fields.
-/
theorem strong_universal_error_free_T_cfg_iff (alloc_may_fail : Bool) (source target : Image) :
    strong_universal_error_free_T_cfg alloc_may_fail source target ↔
    (∀ es et inp, valid_entry source es inp → valid_entry target et inp →
      valid_input inp →
      ¬ (run_scfg (alloc_only_cfg alloc_may_fail) source source_alloc_limit es inp).bh_errors ∧
      ¬ (run_scfg (alloc_only_cfg alloc_may_fail) target target_alloc_limit et inp).bh_errors ∧
      (∀ tr, (run_scfg (alloc_only_cfg alloc_may_fail) source source_alloc_limit es inp).bh_traces tr ↔
        (run_scfg (alloc_only_cfg alloc_may_fail) target target_alloc_limit et inp).bh_traces tr)) := Iff.rfl

/-- The terminating pilot provides an inhabited accept through the baseline bridge.
model: the pilot's exit-5 proof at the concrete permissive refusal configuration.
-/
theorem strong_equiv_scfg_accept :
    strong_equiv_scfg may_fail_cfg Source.image Target.image
      Examples.rwx_flag_ns.Domain.source_entry Examples.rwx_flag_ns.Domain.target_entry
      demo_proc_input :=
  (strong_equiv_scfg_may_fail _ _ _ _ _).2 (strong_equiv_error_free_implies _ _ _ _ _ strong_equiv_error_free_accept)

/-- The terminating pilot provides an inhabited accept through the baseline bridge.
model: the pilot's exit-5 proof at the concrete permissive refusal configuration.
-/
theorem strong_universal_T_scfg_accept :
    strong_universal_T_scfg may_fail_cfg Source.image Target.image :=
  (strong_universal_T_scfg_may_fail _ _).2 Examples.rwx_flag_ns.Proof.strong_universal

/-- The terminating pilot provides an inhabited accept through the baseline bridge.
model: the pilot's exit-5 proof at the concrete permissive refusal configuration.
-/
theorem strong_equiv_error_free_scfg_accept :
    strong_equiv_error_free_scfg may_fail_cfg Source.image Target.image
      Examples.rwx_flag_ns.Domain.source_entry Examples.rwx_flag_ns.Domain.target_entry
      demo_proc_input :=
  (strong_equiv_error_free_scfg_may_fail _ _ _ _ _).2 strong_equiv_error_free_accept

/-- The terminating pilot provides an inhabited accept through the baseline bridge.
model: the pilot's exit-5 proof at the concrete permissive refusal configuration.
-/
theorem strong_universal_error_free_T_scfg_accept :
    strong_universal_error_free_T_scfg may_fail_cfg Source.image Target.image :=
  (strong_universal_error_free_T_scfg_may_fail _ _).2 strong_universal_error_free_T_accept

/-- The terminating pilot provides an inhabited accept through the baseline bridge.
model: the pilot's exit-5 proof at the concrete permissive refusal configuration.
-/
theorem strong_universal_T_scfg_abort_accept :
    strong_universal_T_scfg_abort may_fail_cfg Source.image Target.image :=
  (strong_universal_T_scfg_abort_may_fail _ _).2 strong_universal_T_abort_accept

/-- The terminating pilot provides an inhabited accept through the baseline bridge.
model: the pilot's exit-5 proof at the concrete permissive refusal configuration.
-/
theorem strong_universal_T_scfg_either_accept :
    strong_universal_T_scfg_either may_fail_cfg Source.image Target.image :=
  (strong_universal_T_scfg_either_may_fail _ _).2 strong_universal_T_either_accept

/-- The terminating pilot provides an inhabited accept through the baseline bridge.
model: the pilot's exit-5 proof at the concrete permissive refusal configuration.
-/
theorem strong_equiv_error_free_scfg_abort_accept :
    strong_equiv_error_free_scfg_abort may_fail_cfg Source.image Target.image
      Examples.rwx_flag_ns.Domain.source_entry Examples.rwx_flag_ns.Domain.target_entry
      abort_input :=
  (strong_equiv_error_free_scfg_abort_may_fail _ _ _ _ _).2 strong_equiv_error_free_abort_accept

/-- The terminating pilot provides an inhabited accept through the baseline bridge.
model: the pilot's exit-5 proof at the concrete permissive refusal configuration.
-/
theorem strong_universal_error_free_T_scfg_abort_accept :
    strong_universal_error_free_T_scfg_abort may_fail_cfg Source.image Target.image :=
  (strong_universal_error_free_T_scfg_abort_may_fail _ _).2 strong_universal_error_free_T_abort_accept

/-- The terminating pilot provides an inhabited accept through the baseline bridge.
model: the pilot's exit-5 proof at the concrete permissive refusal configuration.
-/
theorem strong_universal_error_free_T_scfg_either_accept :
    strong_universal_error_free_T_scfg_either may_fail_cfg Source.image Target.image :=
  (strong_universal_error_free_T_scfg_either_may_fail _ _).2 strong_universal_error_free_T_either_accept

/-- The terminating pilot provides an inhabited accept through the baseline bridge.
model: the pilot's exit-5 proof at the concrete permissive refusal configuration.
-/
theorem strong_universal_T_cfg_accept :
    strong_universal_T_cfg true Source.image Target.image :=
  (strong_universal_T_cfg_true _ _).2 Examples.rwx_flag_ns.Proof.strong_universal

/-- The terminating pilot provides an inhabited accept through the baseline bridge.
model: the pilot's exit-5 proof at the concrete permissive refusal configuration.
-/
theorem strong_universal_error_free_T_cfg_accept :
    strong_universal_error_free_T_cfg true Source.image Target.image :=
  (strong_universal_error_free_T_cfg_true _ _).2 strong_universal_error_free_T_accept

/-- The initial undecodable fetch makes the claimed coverage or safety fail.
model: a concrete unmodeled source run, with valid demo witnesses for quantified contracts.
-/
theorem strong_equiv_scfg_refute (cfg : SpuriousCfg) :
    ¬ strong_equiv_scfg cfg undecodable_image undecodable_image demo_entry demo_entry demo_proc_input :=
  fun h => h.1 (undecodable_run_scfg_unmodeled cfg _ _)

/-- The initial undecodable fetch makes the claimed coverage or safety fail.
model: a concrete unmodeled source run, with valid demo witnesses for quantified contracts.
-/
theorem strong_universal_T_scfg_refute (cfg : SpuriousCfg) :
    ¬ strong_universal_T_scfg cfg undecodable_image undecodable_image :=
  fun h => (h demo_entry demo_entry demo_proc_input undecodable_off_entry undecodable_off_entry
    Checks.Omni.demo_input_valid).1 (undecodable_run_scfg_unmodeled cfg _ _)

/-- The initial undecodable fetch makes the claimed coverage or safety fail.
model: a concrete unmodeled source run, with valid demo witnesses for quantified contracts.
-/
theorem strong_equiv_error_free_scfg_refute (cfg : SpuriousCfg) :
    ¬ strong_equiv_error_free_scfg cfg undecodable_image undecodable_image demo_entry demo_entry demo_proc_input :=
  fun h => h.1
    (run_scfg_unmodeled_errors cfg _ _ _ _ (undecodable_run_scfg_unmodeled cfg _ _))

/-- The initial undecodable fetch makes the claimed coverage or safety fail.
model: a concrete unmodeled source run, with valid demo witnesses for quantified contracts.
-/
theorem strong_universal_error_free_T_scfg_refute (cfg : SpuriousCfg) :
    ¬ strong_universal_error_free_T_scfg cfg undecodable_image undecodable_image :=
  fun h => (h demo_entry demo_entry demo_proc_input undecodable_off_entry undecodable_off_entry
    Checks.Omni.demo_input_valid).1
    (run_scfg_unmodeled_errors cfg _ _ _ _ (undecodable_run_scfg_unmodeled cfg _ _))

/-- The initial undecodable fetch makes the claimed coverage or safety fail.
model: a concrete unmodeled source run, with valid demo witnesses for quantified contracts.
-/
theorem strong_universal_T_scfg_abort_refute (cfg : SpuriousCfg) :
    ¬ strong_universal_T_scfg_abort cfg undecodable_image undecodable_image :=
  fun h => (h demo_entry demo_entry abort_input undecodable_abort_entry undecodable_abort_entry
    abort_input_valid).1 (undecodable_run_scfg_unmodeled cfg _ _)

/-- The initial undecodable fetch makes the claimed coverage or safety fail.
model: a concrete unmodeled source run, with valid demo witnesses for quantified contracts.
-/
theorem strong_universal_T_scfg_either_refute (cfg : SpuriousCfg) :
    ¬ strong_universal_T_scfg_either cfg undecodable_image undecodable_image :=
  fun h => (h demo_entry demo_entry demo_proc_input undecodable_off_entry undecodable_off_entry
    (valid_input_either_of_valid_input _ Checks.Omni.demo_input_valid)).1 (undecodable_run_scfg_unmodeled cfg _ _)

/-- The initial undecodable fetch makes the claimed coverage or safety fail.
model: a concrete unmodeled source run, with valid demo witnesses for quantified contracts.
-/
theorem strong_equiv_error_free_scfg_abort_refute (cfg : SpuriousCfg) :
    ¬ strong_equiv_error_free_scfg_abort cfg undecodable_image undecodable_image demo_entry demo_entry abort_input :=
  fun h => h.1.1
    (run_scfg_unmodeled_errors cfg _ _ _ _ (undecodable_run_scfg_unmodeled cfg _ _))

/-- The initial undecodable fetch makes the claimed coverage or safety fail.
model: a concrete unmodeled source run, with valid demo witnesses for quantified contracts.
-/
theorem strong_universal_error_free_T_scfg_abort_refute (cfg : SpuriousCfg) :
    ¬ strong_universal_error_free_T_scfg_abort cfg undecodable_image undecodable_image :=
  fun h => (h demo_entry demo_entry abort_input undecodable_abort_entry undecodable_abort_entry
    abort_input_valid).1.1
    (run_scfg_unmodeled_errors cfg _ _ _ _ (undecodable_run_scfg_unmodeled cfg _ _))

/-- The initial undecodable fetch makes the claimed coverage or safety fail.
model: a concrete unmodeled source run, with valid demo witnesses for quantified contracts.
-/
theorem strong_universal_error_free_T_scfg_either_refute (cfg : SpuriousCfg) :
    ¬ strong_universal_error_free_T_scfg_either cfg undecodable_image undecodable_image :=
  fun h => strong_universal_error_free_T_scfg_refute cfg h.1

/-- The initial undecodable fetch makes the claimed coverage or safety fail.
model: a concrete unmodeled source run, with valid demo witnesses for quantified contracts.
-/
theorem strong_universal_T_cfg_refute (alloc_may_fail : Bool) :
    ¬ strong_universal_T_cfg alloc_may_fail undecodable_image undecodable_image :=
  strong_universal_T_scfg_refute (alloc_only_cfg alloc_may_fail)

/-- The initial undecodable fetch makes the claimed coverage or safety fail.
model: a concrete unmodeled source run, with valid demo witnesses for quantified contracts.
-/
theorem strong_universal_error_free_T_cfg_refute (alloc_may_fail : Bool) :
    ¬ strong_universal_error_free_T_cfg alloc_may_fail undecodable_image undecodable_image :=
  strong_universal_error_free_T_scfg_refute (alloc_only_cfg alloc_may_fail)

/-! ## A-Equiv-budgets: the budget-parameterised statements -/

/-- Reachability is negated on the source alone.
model: the budget-refusal predicate at the source entry and limit.
-/
theorem source_within_budget_iff (ls : Int) (s : Image) (es : ExecEntry) (inp : ProcInput) :
    source_within_budget ls s es inp ↔ ¬ run_budget_refused s ls es inp := Iff.rfl

/-- Raw fields keep coverage, safety and trace comparison separate.
model: the two run records with independently named source and target limits.
-/
theorem strong_equiv_budgets_iff (ls lt : Int) (s t : Image) (es et : ExecEntry) (inp : ProcInput) :
    strong_equiv_budgets ls lt s t es et inp ↔
      ¬ (run s ls es inp).bh_unmodeled ∧
      ((run s ls es inp).bh_all_errors ∨ ((∀ tr, (run s ls es inp).bh_traces tr ↔ (run t lt et inp).bh_traces tr) ∧ ¬ (run t lt et inp).bh_errors)) := Iff.rfl

/-- Raw fields keep coverage, safety and trace comparison separate.
model: the two run records with independently named source and target limits.
-/
theorem strong_equiv_error_free_budgets_iff (ls lt : Int) (s t : Image) (es et : ExecEntry) (inp : ProcInput) :
    strong_equiv_error_free_budgets ls lt s t es et inp ↔
      ¬ (run s ls es inp).bh_errors ∧
      ¬ (run t lt et inp).bh_errors ∧
      (∀ tr, (run s ls es inp).bh_traces tr ↔ (run t lt et inp).bh_traces tr) := Iff.rfl

/-- Raw fields keep coverage, safety and trace comparison separate.
model: the two run records with independently named source and target limits.
-/
theorem strong_equiv_error_free_budgets_abort_iff (ls lt : Int) (s t : Image) (es et : ExecEntry) (inp : ProcInput) :
    strong_equiv_error_free_budgets_abort ls lt s t es et inp ↔
      (¬ (run s ls es inp).bh_errors ∧ ¬ (∃ tr sig fs, (run s ls es inp).bh_traces tr ∧ KillEv sig fs ∈ tr)) ∧
      (¬ (run t lt et inp).bh_errors ∧ ¬ (∃ tr sig fs, (run t lt et inp).bh_traces tr ∧ KillEv sig fs ∈ tr)) ∧
      (∀ tr, (run s ls es inp).bh_traces tr ↔ (run t lt et inp).bh_traces tr) := Iff.rfl

/-- The budget premise stays beside validity in the quantifier shell.
model: explicit entries, input declaration and raw run fields.
-/
theorem strong_universal_T_budgets_iff (ls lt : Int) (s t : Image) :
    strong_universal_T_budgets ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input inp → ¬ run_budget_refused s ls es inp →
      ¬ (run s ls es inp).bh_unmodeled ∧
      ((run s ls es inp).bh_all_errors ∨ ((∀ tr, (run s ls es inp).bh_traces tr ↔ (run t lt et inp).bh_traces tr) ∧ ¬ (run t lt et inp).bh_errors))) := Iff.rfl

/-- The budget premise stays beside validity in the quantifier shell.
model: explicit entries, input declaration and raw run fields.
-/
theorem strong_universal_error_free_T_budgets_iff (ls lt : Int) (s t : Image) :
    strong_universal_error_free_T_budgets ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input inp → ¬ run_budget_refused s ls es inp →
      ¬ (run s ls es inp).bh_errors ∧
      ¬ (run t lt et inp).bh_errors ∧
      (∀ tr, (run s ls es inp).bh_traces tr ↔ (run t lt et inp).bh_traces tr)) := Iff.rfl

/-- The budget premise stays beside validity in the quantifier shell.
model: explicit entries, input declaration and raw run fields.
-/
theorem strong_universal_T_budgets_hwcap_rv64gc_iff (ls lt : Int) (s t : Image) :
    strong_universal_T_budgets_hwcap_rv64gc ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input_hwcap_rv64gc inp → ¬ run_budget_refused s ls es inp →
      ¬ (run s ls es inp).bh_unmodeled ∧
      ((run s ls es inp).bh_all_errors ∨ ((∀ tr, (run s ls es inp).bh_traces tr ↔ (run t lt et inp).bh_traces tr) ∧ ¬ (run t lt et inp).bh_errors))) := Iff.rfl

/-- The budget premise stays beside validity in the quantifier shell.
model: explicit entries, input declaration and raw run fields.
-/
theorem strong_universal_error_free_T_budgets_hwcap_rv64gc_iff (ls lt : Int) (s t : Image) :
    strong_universal_error_free_T_budgets_hwcap_rv64gc ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input_hwcap_rv64gc inp → ¬ run_budget_refused s ls es inp →
      ¬ (run s ls es inp).bh_errors ∧
      ¬ (run t lt et inp).bh_errors ∧
      (∀ tr, (run s ls es inp).bh_traces tr ↔ (run t lt et inp).bh_traces tr)) := Iff.rfl

/-- The budget premise stays beside validity in the quantifier shell.
model: explicit entries, input declaration and raw run fields.
-/
theorem strong_universal_T_budgets_hwcap_rv64gcv_iff (ls lt : Int) (s t : Image) :
    strong_universal_T_budgets_hwcap_rv64gcv ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input_hwcap_rv64gcv inp → ¬ run_budget_refused s ls es inp →
      ¬ (run s ls es inp).bh_unmodeled ∧
      ((run s ls es inp).bh_all_errors ∨ ((∀ tr, (run s ls es inp).bh_traces tr ↔ (run t lt et inp).bh_traces tr) ∧ ¬ (run t lt et inp).bh_errors))) := Iff.rfl

/-- The budget premise stays beside validity in the quantifier shell.
model: explicit entries, input declaration and raw run fields.
-/
theorem strong_universal_error_free_T_budgets_hwcap_rv64gcv_iff (ls lt : Int) (s t : Image) :
    strong_universal_error_free_T_budgets_hwcap_rv64gcv ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input_hwcap_rv64gcv inp → ¬ run_budget_refused s ls es inp →
      ¬ (run s ls es inp).bh_errors ∧
      ¬ (run t lt et inp).bh_errors ∧
      (∀ tr, (run s ls es inp).bh_traces tr ↔ (run t lt et inp).bh_traces tr)) := Iff.rfl

/-- The budget premise stays beside validity in the quantifier shell.
model: explicit entries, input declaration and raw run fields.
-/
theorem strong_universal_T_budgets_abort_iff (ls lt : Int) (s t : Image) :
    strong_universal_T_budgets_abort ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input_abort inp → ¬ run_budget_refused s ls es inp →
      ¬ (run s ls es inp).bh_unmodeled ∧
      ((run s ls es inp).bh_all_errors ∨ ((∀ tr, (run s ls es inp).bh_traces tr ↔ (run t lt et inp).bh_traces tr) ∧ ¬ (run t lt et inp).bh_errors))) := Iff.rfl

/-- The budget premise stays beside validity in the quantifier shell.
model: explicit entries, input declaration and raw run fields.
-/
theorem strong_universal_error_free_T_budgets_abort_iff (ls lt : Int) (s t : Image) :
    strong_universal_error_free_T_budgets_abort ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input_abort inp → ¬ run_budget_refused s ls es inp →
      (¬ (run s ls es inp).bh_errors ∧ ¬ (∃ tr sig fs, (run s ls es inp).bh_traces tr ∧ KillEv sig fs ∈ tr)) ∧
      (¬ (run t lt et inp).bh_errors ∧ ¬ (∃ tr sig fs, (run t lt et inp).bh_traces tr ∧ KillEv sig fs ∈ tr)) ∧
      (∀ tr, (run s ls es inp).bh_traces tr ↔ (run t lt et inp).bh_traces tr)) := Iff.rfl

/-- The budget premise stays beside validity in the quantifier shell.
model: explicit entries, input declaration and raw run fields.
-/
theorem strong_universal_T_budgets_abort_hwcap_rv64gc_iff (ls lt : Int) (s t : Image) :
    strong_universal_T_budgets_abort_hwcap_rv64gc ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input_abort_hwcap_rv64gc inp → ¬ run_budget_refused s ls es inp →
      ¬ (run s ls es inp).bh_unmodeled ∧
      ((run s ls es inp).bh_all_errors ∨ ((∀ tr, (run s ls es inp).bh_traces tr ↔ (run t lt et inp).bh_traces tr) ∧ ¬ (run t lt et inp).bh_errors))) := Iff.rfl

/-- The budget premise stays beside validity in the quantifier shell.
model: explicit entries, input declaration and raw run fields.
-/
theorem strong_universal_error_free_T_budgets_abort_hwcap_rv64gc_iff (ls lt : Int) (s t : Image) :
    strong_universal_error_free_T_budgets_abort_hwcap_rv64gc ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input_abort_hwcap_rv64gc inp → ¬ run_budget_refused s ls es inp →
      (¬ (run s ls es inp).bh_errors ∧ ¬ (∃ tr sig fs, (run s ls es inp).bh_traces tr ∧ KillEv sig fs ∈ tr)) ∧
      (¬ (run t lt et inp).bh_errors ∧ ¬ (∃ tr sig fs, (run t lt et inp).bh_traces tr ∧ KillEv sig fs ∈ tr)) ∧
      (∀ tr, (run s ls es inp).bh_traces tr ↔ (run t lt et inp).bh_traces tr)) := Iff.rfl

/-- The budget premise stays beside validity in the quantifier shell.
model: explicit entries, input declaration and raw run fields.
-/
theorem strong_universal_T_budgets_abort_hwcap_rv64gcv_iff (ls lt : Int) (s t : Image) :
    strong_universal_T_budgets_abort_hwcap_rv64gcv ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input_abort_hwcap_rv64gcv inp → ¬ run_budget_refused s ls es inp →
      ¬ (run s ls es inp).bh_unmodeled ∧
      ((run s ls es inp).bh_all_errors ∨ ((∀ tr, (run s ls es inp).bh_traces tr ↔ (run t lt et inp).bh_traces tr) ∧ ¬ (run t lt et inp).bh_errors))) := Iff.rfl

/-- The budget premise stays beside validity in the quantifier shell.
model: explicit entries, input declaration and raw run fields.
-/
theorem strong_universal_error_free_T_budgets_abort_hwcap_rv64gcv_iff (ls lt : Int) (s t : Image) :
    strong_universal_error_free_T_budgets_abort_hwcap_rv64gcv ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input_abort_hwcap_rv64gcv inp → ¬ run_budget_refused s ls es inp →
      (¬ (run s ls es inp).bh_errors ∧ ¬ (∃ tr sig fs, (run s ls es inp).bh_traces tr ∧ KillEv sig fs ∈ tr)) ∧
      (¬ (run t lt et inp).bh_errors ∧ ¬ (∃ tr sig fs, (run t lt et inp).bh_traces tr ∧ KillEv sig fs ∈ tr)) ∧
      (∀ tr, (run s ls es inp).bh_traces tr ↔ (run t lt et inp).bh_traces tr)) := Iff.rfl

/-- Reachability is negated on the source alone.
model: the budget-refusal predicate at the source entry and limit.
-/
theorem source_within_budget_scfg_iff (cfg : SpuriousCfg) (ls : Int) (s : Image) (es : ExecEntry) (inp : ProcInput) :
    source_within_budget_scfg cfg ls s es inp ↔ ¬ run_scfg_budget_refused cfg s ls es inp := Iff.rfl

/-- Raw fields keep coverage, safety and trace comparison separate.
model: the two run records with independently named source and target limits.
-/
theorem strong_equiv_budgets_scfg_iff (cfg : SpuriousCfg) (ls lt : Int) (s t : Image) (es et : ExecEntry) (inp : ProcInput) :
    strong_equiv_budgets_scfg cfg ls lt s t es et inp ↔
      ¬ (run_scfg cfg s ls es inp).bh_unmodeled ∧
      ((run_scfg cfg s ls es inp).bh_all_errors ∨ ((∀ tr, (run_scfg cfg s ls es inp).bh_traces tr ↔ (run_scfg cfg t lt et inp).bh_traces tr) ∧ ¬ (run_scfg cfg t lt et inp).bh_errors)) := Iff.rfl

/-- Raw fields keep coverage, safety and trace comparison separate.
model: the two run records with independently named source and target limits.
-/
theorem strong_equiv_error_free_budgets_scfg_iff (cfg : SpuriousCfg) (ls lt : Int) (s t : Image) (es et : ExecEntry) (inp : ProcInput) :
    strong_equiv_error_free_budgets_scfg cfg ls lt s t es et inp ↔
      ¬ (run_scfg cfg s ls es inp).bh_errors ∧
      ¬ (run_scfg cfg t lt et inp).bh_errors ∧
      (∀ tr, (run_scfg cfg s ls es inp).bh_traces tr ↔ (run_scfg cfg t lt et inp).bh_traces tr) := Iff.rfl

/-- Raw fields keep coverage, safety and trace comparison separate.
model: the two run records with independently named source and target limits.
-/
theorem strong_equiv_error_free_budgets_scfg_abort_iff (cfg : SpuriousCfg) (ls lt : Int) (s t : Image) (es et : ExecEntry) (inp : ProcInput) :
    strong_equiv_error_free_budgets_scfg_abort cfg ls lt s t es et inp ↔
      (¬ (run_scfg cfg s ls es inp).bh_errors ∧ ¬ (∃ tr sig fs, (run_scfg cfg s ls es inp).bh_traces tr ∧ KillEv sig fs ∈ tr)) ∧
      (¬ (run_scfg cfg t lt et inp).bh_errors ∧ ¬ (∃ tr sig fs, (run_scfg cfg t lt et inp).bh_traces tr ∧ KillEv sig fs ∈ tr)) ∧
      (∀ tr, (run_scfg cfg s ls es inp).bh_traces tr ↔ (run_scfg cfg t lt et inp).bh_traces tr) := Iff.rfl

/-- The budget premise stays beside validity in the quantifier shell.
model: explicit entries, input declaration and raw run fields.
-/
theorem strong_universal_T_scfg_budgets_iff (cfg : SpuriousCfg) (ls lt : Int) (s t : Image) :
    strong_universal_T_scfg_budgets cfg ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input inp → ¬ run_scfg_budget_refused cfg s ls es inp →
      ¬ (run_scfg cfg s ls es inp).bh_unmodeled ∧
      ((run_scfg cfg s ls es inp).bh_all_errors ∨ ((∀ tr, (run_scfg cfg s ls es inp).bh_traces tr ↔ (run_scfg cfg t lt et inp).bh_traces tr) ∧ ¬ (run_scfg cfg t lt et inp).bh_errors))) := Iff.rfl

/-- The budget premise stays beside validity in the quantifier shell.
model: explicit entries, input declaration and raw run fields.
-/
theorem strong_universal_error_free_T_scfg_budgets_iff (cfg : SpuriousCfg) (ls lt : Int) (s t : Image) :
    strong_universal_error_free_T_scfg_budgets cfg ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input inp → ¬ run_scfg_budget_refused cfg s ls es inp →
      ¬ (run_scfg cfg s ls es inp).bh_errors ∧
      ¬ (run_scfg cfg t lt et inp).bh_errors ∧
      (∀ tr, (run_scfg cfg s ls es inp).bh_traces tr ↔ (run_scfg cfg t lt et inp).bh_traces tr)) := Iff.rfl

/-- The budget premise stays beside validity in the quantifier shell.
model: explicit entries, input declaration and raw run fields.
-/
theorem strong_universal_T_scfg_budgets_hwcap_rv64gc_iff (cfg : SpuriousCfg) (ls lt : Int) (s t : Image) :
    strong_universal_T_scfg_budgets_hwcap_rv64gc cfg ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input_hwcap_rv64gc inp → ¬ run_scfg_budget_refused cfg s ls es inp →
      ¬ (run_scfg cfg s ls es inp).bh_unmodeled ∧
      ((run_scfg cfg s ls es inp).bh_all_errors ∨ ((∀ tr, (run_scfg cfg s ls es inp).bh_traces tr ↔ (run_scfg cfg t lt et inp).bh_traces tr) ∧ ¬ (run_scfg cfg t lt et inp).bh_errors))) := Iff.rfl

/-- The budget premise stays beside validity in the quantifier shell.
model: explicit entries, input declaration and raw run fields.
-/
theorem strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc_iff (cfg : SpuriousCfg) (ls lt : Int) (s t : Image) :
    strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc cfg ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input_hwcap_rv64gc inp → ¬ run_scfg_budget_refused cfg s ls es inp →
      ¬ (run_scfg cfg s ls es inp).bh_errors ∧
      ¬ (run_scfg cfg t lt et inp).bh_errors ∧
      (∀ tr, (run_scfg cfg s ls es inp).bh_traces tr ↔ (run_scfg cfg t lt et inp).bh_traces tr)) := Iff.rfl

/-- The budget premise stays beside validity in the quantifier shell.
model: explicit entries, input declaration and raw run fields.
-/
theorem strong_universal_T_scfg_budgets_hwcap_rv64gcv_iff (cfg : SpuriousCfg) (ls lt : Int) (s t : Image) :
    strong_universal_T_scfg_budgets_hwcap_rv64gcv cfg ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input_hwcap_rv64gcv inp → ¬ run_scfg_budget_refused cfg s ls es inp →
      ¬ (run_scfg cfg s ls es inp).bh_unmodeled ∧
      ((run_scfg cfg s ls es inp).bh_all_errors ∨ ((∀ tr, (run_scfg cfg s ls es inp).bh_traces tr ↔ (run_scfg cfg t lt et inp).bh_traces tr) ∧ ¬ (run_scfg cfg t lt et inp).bh_errors))) := Iff.rfl

/-- The budget premise stays beside validity in the quantifier shell.
model: explicit entries, input declaration and raw run fields.
-/
theorem strong_universal_error_free_T_scfg_budgets_hwcap_rv64gcv_iff (cfg : SpuriousCfg) (ls lt : Int) (s t : Image) :
    strong_universal_error_free_T_scfg_budgets_hwcap_rv64gcv cfg ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input_hwcap_rv64gcv inp → ¬ run_scfg_budget_refused cfg s ls es inp →
      ¬ (run_scfg cfg s ls es inp).bh_errors ∧
      ¬ (run_scfg cfg t lt et inp).bh_errors ∧
      (∀ tr, (run_scfg cfg s ls es inp).bh_traces tr ↔ (run_scfg cfg t lt et inp).bh_traces tr)) := Iff.rfl

/-- The budget premise stays beside validity in the quantifier shell.
model: explicit entries, input declaration and raw run fields.
-/
theorem strong_universal_T_scfg_budgets_abort_iff (cfg : SpuriousCfg) (ls lt : Int) (s t : Image) :
    strong_universal_T_scfg_budgets_abort cfg ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input_abort inp → ¬ run_scfg_budget_refused cfg s ls es inp →
      ¬ (run_scfg cfg s ls es inp).bh_unmodeled ∧
      ((run_scfg cfg s ls es inp).bh_all_errors ∨ ((∀ tr, (run_scfg cfg s ls es inp).bh_traces tr ↔ (run_scfg cfg t lt et inp).bh_traces tr) ∧ ¬ (run_scfg cfg t lt et inp).bh_errors))) := Iff.rfl

/-- The budget premise stays beside validity in the quantifier shell.
model: explicit entries, input declaration and raw run fields.
-/
theorem strong_universal_error_free_T_scfg_budgets_abort_iff (cfg : SpuriousCfg) (ls lt : Int) (s t : Image) :
    strong_universal_error_free_T_scfg_budgets_abort cfg ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input_abort inp → ¬ run_scfg_budget_refused cfg s ls es inp →
      (¬ (run_scfg cfg s ls es inp).bh_errors ∧ ¬ (∃ tr sig fs, (run_scfg cfg s ls es inp).bh_traces tr ∧ KillEv sig fs ∈ tr)) ∧
      (¬ (run_scfg cfg t lt et inp).bh_errors ∧ ¬ (∃ tr sig fs, (run_scfg cfg t lt et inp).bh_traces tr ∧ KillEv sig fs ∈ tr)) ∧
      (∀ tr, (run_scfg cfg s ls es inp).bh_traces tr ↔ (run_scfg cfg t lt et inp).bh_traces tr)) := Iff.rfl

/-- The budget premise stays beside validity in the quantifier shell.
model: explicit entries, input declaration and raw run fields.
-/
theorem strong_universal_T_scfg_budgets_abort_hwcap_rv64gc_iff (cfg : SpuriousCfg) (ls lt : Int) (s t : Image) :
    strong_universal_T_scfg_budgets_abort_hwcap_rv64gc cfg ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input_abort_hwcap_rv64gc inp → ¬ run_scfg_budget_refused cfg s ls es inp →
      ¬ (run_scfg cfg s ls es inp).bh_unmodeled ∧
      ((run_scfg cfg s ls es inp).bh_all_errors ∨ ((∀ tr, (run_scfg cfg s ls es inp).bh_traces tr ↔ (run_scfg cfg t lt et inp).bh_traces tr) ∧ ¬ (run_scfg cfg t lt et inp).bh_errors))) := Iff.rfl

/-- The budget premise stays beside validity in the quantifier shell.
model: explicit entries, input declaration and raw run fields.
-/
theorem strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gc_iff (cfg : SpuriousCfg) (ls lt : Int) (s t : Image) :
    strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gc cfg ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input_abort_hwcap_rv64gc inp → ¬ run_scfg_budget_refused cfg s ls es inp →
      (¬ (run_scfg cfg s ls es inp).bh_errors ∧ ¬ (∃ tr sig fs, (run_scfg cfg s ls es inp).bh_traces tr ∧ KillEv sig fs ∈ tr)) ∧
      (¬ (run_scfg cfg t lt et inp).bh_errors ∧ ¬ (∃ tr sig fs, (run_scfg cfg t lt et inp).bh_traces tr ∧ KillEv sig fs ∈ tr)) ∧
      (∀ tr, (run_scfg cfg s ls es inp).bh_traces tr ↔ (run_scfg cfg t lt et inp).bh_traces tr)) := Iff.rfl

/-- The budget premise stays beside validity in the quantifier shell.
model: explicit entries, input declaration and raw run fields.
-/
theorem strong_universal_T_scfg_budgets_abort_hwcap_rv64gcv_iff (cfg : SpuriousCfg) (ls lt : Int) (s t : Image) :
    strong_universal_T_scfg_budgets_abort_hwcap_rv64gcv cfg ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input_abort_hwcap_rv64gcv inp → ¬ run_scfg_budget_refused cfg s ls es inp →
      ¬ (run_scfg cfg s ls es inp).bh_unmodeled ∧
      ((run_scfg cfg s ls es inp).bh_all_errors ∨ ((∀ tr, (run_scfg cfg s ls es inp).bh_traces tr ↔ (run_scfg cfg t lt et inp).bh_traces tr) ∧ ¬ (run_scfg cfg t lt et inp).bh_errors))) := Iff.rfl

/-- The budget premise stays beside validity in the quantifier shell.
model: explicit entries, input declaration and raw run fields.
-/
theorem strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gcv_iff (cfg : SpuriousCfg) (ls lt : Int) (s t : Image) :
    strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gcv cfg ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input_abort_hwcap_rv64gcv inp → ¬ run_scfg_budget_refused cfg s ls es inp →
      (¬ (run_scfg cfg s ls es inp).bh_errors ∧ ¬ (∃ tr sig fs, (run_scfg cfg s ls es inp).bh_traces tr ∧ KillEv sig fs ∈ tr)) ∧
      (¬ (run_scfg cfg t lt et inp).bh_errors ∧ ¬ (∃ tr sig fs, (run_scfg cfg t lt et inp).bh_traces tr ∧ KillEv sig fs ∈ tr)) ∧
      (∀ tr, (run_scfg cfg s ls es inp).bh_traces tr ↔ (run_scfg cfg t lt et inp).bh_traces tr)) := Iff.rfl

/-- The two stances retain their respective conclusions.
model: the two independently expanded quantified statements.
-/
theorem strong_universal_T_budgets_either_iff (ls lt : Int) (s t : Image) :
    strong_universal_T_budgets_either ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input inp → ¬ run_budget_refused s ls es inp →
      ¬ (run s ls es inp).bh_unmodeled ∧
      ((run s ls es inp).bh_all_errors ∨ ((∀ tr, (run s ls es inp).bh_traces tr ↔ (run t lt et inp).bh_traces tr) ∧ ¬ (run t lt et inp).bh_errors))) ∧
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input_abort inp → ¬ run_budget_refused s ls es inp →
      ¬ (run s ls es inp).bh_unmodeled ∧
      ((run s ls es inp).bh_all_errors ∨ ((∀ tr, (run s ls es inp).bh_traces tr ↔ (run t lt et inp).bh_traces tr) ∧ ¬ (run t lt et inp).bh_errors))) := Iff.rfl

/-- The two stances retain their respective conclusions.
model: the two independently expanded quantified statements.
-/
theorem strong_universal_error_free_T_budgets_either_iff (ls lt : Int) (s t : Image) :
    strong_universal_error_free_T_budgets_either ls lt s t ↔
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input inp → ¬ run_budget_refused s ls es inp →
      ¬ (run s ls es inp).bh_errors ∧
      ¬ (run t lt et inp).bh_errors ∧
      (∀ tr, (run s ls es inp).bh_traces tr ↔ (run t lt et inp).bh_traces tr)) ∧
    (∀ es et inp, valid_entry s es inp → valid_entry t et inp →
      valid_input_abort inp → ¬ run_budget_refused s ls es inp →
      (¬ (run s ls es inp).bh_errors ∧ ¬ (∃ tr sig fs, (run s ls es inp).bh_traces tr ∧ KillEv sig fs ∈ tr)) ∧
      (¬ (run t lt et inp).bh_errors ∧ ¬ (∃ tr sig fs, (run t lt et inp).bh_traces tr ∧ KillEv sig fs ∈ tr)) ∧
      (∀ tr, (run s ls es inp).bh_traces tr ↔ (run t lt et inp).bh_traces tr)) := Iff.rfl

/-- The error transition has no successor configuration to reach a later refusal.
model: the initial undecodable fetch and empty lazy ledger exclude budget reachability.
-/
theorem undecodable_within_budget (lim : Int) (inp : ProcInput) :
    source_within_budget lim undecodable_image demo_entry inp := by
  let c0 := init_config undecodable_image.img_segments undecodable_image.img_init_pc
    undecodable_image.img_phdrs demo_entry.en_sp demo_entry.en_brk
    demo_entry.en_mmap_base demo_entry.en_draw lim inp
  have hu : mi_account_step undecodable_image.img_segments c0.cfg_ms c0.cfg_model = MachineUnmodeled := by
    rw [mi_account_step_no_lazy _ _ _ rfl]
    rw [step_of_fetch _ _ 0xffffffff (by
      change fetch_word undecodable_segments 0x100 = some 0xffffffff
      decide)]
    rfl
  apply never_budget_refused_ind _ (fun c => c = c0) c0 rfl
  · intro c evs c' hc hs
    subst c
    unfold c0 init_config at hs
    cases hs with
    | sstep_instr _ _ _ _ _ _ h =>
      change mi_account_step undecodable_image.img_segments c0.cfg_ms c0.cfg_model = _ at h
      rw [hu] at h
      cases h
    | sstep_syscall _ _ _ _ _ _ _ _ h => cases h
    | sstep_exit _ _ _ _ _ _ _ _ h => cases h
    | sstep_killed _ _ _ _ _ _ _ _ h => cases h
  · intro c hc
    subst c
    exact budget_refused_at_no_lazy_instr _ _ _ rfl rfl

/-- Filtering preserves this absence of budget reachability.
model: the unconfigured undecodable fixture transported by the budget-subset bridge.
-/
theorem undecodable_within_budget_scfg (cfg : SpuriousCfg) (lim : Int) (inp : ProcInput) :
    source_within_budget_scfg cfg lim undecodable_image demo_entry inp :=
  source_within_budget_scfg_of_source_within_budget cfg _ _ _ _ (undecodable_within_budget lim inp)

/-- A two-page brk grow under a one-page limit makes the premise bite.
model: three instruction words setting a0 = 0x3000 and a7 = 214 before ecall.
-/
def budget_probe_image : Image :=
  ⟨[{ seg_base := 0x100, seg_size := 12, seg_perms := "r-x",
      seg_bytes := ["373500009308600d73000000"] }], 0x100, demo_phdrs⟩

/-- The fixture uses the same launch as the undecodable control.
model: the probe's initial configuration with one page of allocation budget.
-/
def budget_probe_c0 : config :=
  init_config budget_probe_image.img_segments 0x100 demo_phdrs demo_entry.en_sp
    demo_entry.en_brk demo_entry.en_mmap_base demo_entry.en_draw page_size demo_proc_input

/-- The first instruction sets the requested break without touching memory.
model: the machine record after the probe's lui a0,3.
-/
def budget_probe_ms1 : machine_state :=
  { budget_probe_c0.cfg_ms with
    ms_regs := bvmap_set 10 0x3000 budget_probe_c0.cfg_ms.ms_regs, ms_pc_val := 0x104 }

/-- The second instruction selects brk.
model: the machine record after the probe's addi a7,zero,214.
-/
def budget_probe_ms2 : machine_state :=
  { budget_probe_ms1 with ms_regs := bvmap_set 17 214 budget_probe_ms1.ms_regs, ms_pc_val := 0x108 }

/-- The syscall is pending before its answer is chosen.
model: the machine record after the probe's ecall.
-/
def budget_probe_ms3 : machine_state :=
  { budget_probe_ms2 with ms_svc_pending := some 214 }

/-- Each instruction preserves the model and reaches the next machine state.
model: the concrete instruction fetches at 0x100, 0x104 and 0x108.
-/
theorem budget_probe_steps :
    sstep budget_probe_image.img_segments budget_probe_c0 []
      (SNext ⟨budget_probe_ms1, budget_probe_c0.cfg_model⟩) ∧
    sstep budget_probe_image.img_segments ⟨budget_probe_ms1, budget_probe_c0.cfg_model⟩ []
      (SNext ⟨budget_probe_ms2, budget_probe_c0.cfg_model⟩) ∧
    sstep budget_probe_image.img_segments ⟨budget_probe_ms2, budget_probe_c0.cfg_model⟩ []
      (SNext ⟨budget_probe_ms3, budget_probe_c0.cfg_model⟩) := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    apply sstep.sstep_instr _ _ _ _ rfl rfl
    rw [mi_account_step_no_lazy _ _ _ rfl]
  · rw [step_of_fetch _ _ 0x00003537 (by decide)]
    rfl
  · rw [step_of_fetch _ _ 0x0d600893 (by decide)]
    rfl
  · rw [step_of_fetch _ _ 0x00000073 (by decide)]
    have hr : ms_reg budget_probe_ms2 17 = (214 : word) := by decide +kernel
    change MachineOk ({ budget_probe_ms2 with ms_svc_pending := some (ms_reg budget_probe_ms2 17) },
      budget_probe_c0.cfg_model) = _
    rw [hr]
    rfl

/-- The request exceeds the limit before a syscall outcome is selected.
model: the brk grant mark at a two-page grow and a one-page budget.
-/
theorem budget_probe_refused :
    run_budget_refused budget_probe_image page_size demo_entry demo_proc_input := by
  refine ⟨[], ⟨budget_probe_ms3, budget_probe_c0.cfg_model⟩, ?_, ?_⟩
  · exact star.star_step _ [] _ [] _ budget_probe_steps.1
      (star.star_step _ [] _ [] _ budget_probe_steps.2.1
        (star.star_step _ [] _ [] _ budget_probe_steps.2.2 (star.star_refl _)))
  · exact ⟨rfl, Or.inr ⟨214, rfl, Or.inl (by decide +kernel)⟩⟩

/-- An allocating source can reach the mark, so the premise excludes a real run.
model: the three-instruction brk probe exceeds its one-page limit.
-/
theorem source_within_budget_refute :
    ¬ source_within_budget page_size budget_probe_image demo_entry demo_proc_input :=
  fun h => h budget_probe_refused

/-- The permissive configuration preserves the reached mark.
model: the concrete brk refusal transported by the may-fail reachability equivalence.
-/
theorem source_within_budget_scfg_refute :
    ¬ source_within_budget_scfg may_fail_cfg page_size budget_probe_image demo_entry demo_proc_input :=
  fun h => source_within_budget_refute ((source_within_budget_scfg_may_fail _ _ _ _).1 h)

/-- A straight-line exit path reaches no allocation request or lazy-page charge.
model: the exit-path invariant excludes each arm of the budget mark.
-/
theorem exit_path_within_budget (segs : List Segment) (code : word)
    (c : config) (hp : on_path segs code c) : ¬ reaches_budget_refused segs c := by
  apply never_budget_refused_ind segs (on_path segs code) c hp (on_path_step segs code)
  intro c hc hb
  obtain ⟨ms, model⟩ := c
  rcases hc with ⟨_, hlazy, hte⟩ | hh
  · cases hte with
    | te_step ms ms' hsvc _ _ =>
      exact budget_refused_at_no_lazy_instr segs _ model hlazy hsvc hb
    | te_here ms x8 hsvc hno _ =>
      rcases hb.2 with ⟨hnone, _⟩ | ⟨y8, hy8, hm | ⟨eff, m', evs, hspec, hh', _⟩⟩
      · exact nomatch (hnone.symm.trans hsvc)
      · have heq : y8 = x8 := Option.some.inj (hy8.symm.trans hsvc)
        subst y8
        rcases hno with hno | hno
        all_goals simp only [alloc_budget_refused_b, sys_input, hno] at hm; cases hm
      · have heq : y8 = x8 := Option.some.inj (hy8.symm.trans hsvc)
        subst y8
        obtain ⟨_, rfl, _⟩ := exit_dispatch_ok_inv _ _ _ _ _ hno hspec
        rw [m_halted_with_halted] at hh'
        cases hh'
  · exact hh hb.1

/-- The pilot's execution proof reaches an exit without an allocating syscall.
model: the source to_exit derivation supplies the initial exit-path invariant.
-/
theorem pilot_source_within_budget (lim : Int) :
    source_within_budget lim Source.image Examples.rwx_flag_ns.Domain.source_entry demo_proc_input := by
  apply exit_path_within_budget _ 5
  refine Or.inl ⟨rfl, rfl, ?_⟩
  exact Examples.rwx_flag_ns.SourceExec.source_exit _ _ _ _ _ _ (by decide) (by decide)

/-- The pilot stays within its source limit.
model: the source exit derivation excludes budget reachability.
-/
theorem source_within_budget_accept :
    source_within_budget source_alloc_limit Source.image Examples.rwx_flag_ns.Domain.source_entry demo_proc_input :=
  pilot_source_within_budget _

/-- The pilot stays within its source limit.
model: the source exit derivation excludes budget reachability.
-/
theorem source_within_budget_scfg_accept :
    source_within_budget_scfg may_fail_cfg source_alloc_limit Source.image Examples.rwx_flag_ns.Domain.source_entry demo_proc_input :=
  (source_within_budget_scfg_may_fail _ _ _ _).2 source_within_budget_accept

/-- The declared vector word and abort stance vary independent input fields.
model: the demo input with the vector word and abort enabled.
-/
def budget_abort_vector_input : ProcInput := { abort_input with in_hwcap := hwcap_rv64gcv }

/-- The shared input clauses survive the two declarations.
model: the demo validity proof with the declared word and stance substituted.
-/
theorem budget_abort_rv64gc_valid : valid_input_abort_hwcap_rv64gc abort_input := by
  obtain ⟨ha, he, hf, him, hc, hn, hs, _, _, hv, hu⟩ := Checks.Omni.demo_input_valid
  exact ⟨ha, he, hf, him, hc, hn, hs, rfl, rfl, hv, hu⟩

/-- The shared input clauses survive the two declarations.
model: the demo validity proof with the declared word and stance substituted.
-/
theorem budget_abort_rv64gcv_valid : valid_input_abort_hwcap_rv64gcv budget_abort_vector_input := by
  obtain ⟨ha, he, hf, him, hc, hn, hs, _, _, hv, hu⟩ := Checks.Omni.demo_input_valid
  exact ⟨ha, he, hf, him, hc, hn, hs, rfl, rfl, hv, hu⟩

/-- The vector word does not affect stack sizing.
model: the undecodable image fits the demo entry under the abort-vector input.
-/
theorem budget_undecodable_abort_vector_entry :
    valid_entry undecodable_image demo_entry budget_abort_vector_input :=
  undecodable_entry_valid _ rfl (by unfold valid_argv; decide) (by unfold valid_envp; decide)

/-- The terminating pilot supplies a concrete triple at the shipped limits.
model: the pinned bridge applied to the pilot accept.
-/
theorem strong_equiv_budgets_accept :
    strong_equiv_budgets source_alloc_limit target_alloc_limit Source.image Target.image
      Examples.rwx_flag_ns.Domain.source_entry Examples.rwx_flag_ns.Domain.target_entry demo_proc_input :=
  (strong_equiv_budgets_pinned _ _ _ _ _).2 (strong_equiv_error_free_implies _ _ _ _ _ strong_equiv_error_free_accept)

/-- The terminating pilot supplies a concrete triple at the shipped limits.
model: the pinned bridge applied to the pilot accept.
-/
theorem strong_equiv_error_free_budgets_accept :
    strong_equiv_error_free_budgets source_alloc_limit target_alloc_limit Source.image Target.image
      Examples.rwx_flag_ns.Domain.source_entry Examples.rwx_flag_ns.Domain.target_entry demo_proc_input :=
  (strong_equiv_error_free_budgets_pinned _ _ _ _ _).2 strong_equiv_error_free_accept

/-- The terminating pilot supplies a concrete triple at the shipped limits.
model: the pinned bridge applied to the pilot accept.
-/
theorem strong_equiv_error_free_budgets_abort_accept :
    strong_equiv_error_free_budgets_abort source_alloc_limit target_alloc_limit Source.image Target.image
      Examples.rwx_flag_ns.Domain.source_entry Examples.rwx_flag_ns.Domain.target_entry abort_input :=
  (strong_equiv_error_free_budgets_abort_pinned _ _ _ _ _).2 strong_equiv_error_free_abort_accept

/-- The pilot supplies an inhabited task through the budget bridges.
model: the shipped-limit bridge and, for a declared word, the capability split.
-/
theorem strong_universal_T_budgets_accept :
    strong_universal_T_budgets source_alloc_limit target_alloc_limit Source.image Target.image :=
  strong_universal_T_budgets_of_pinned _ _ Examples.rwx_flag_ns.Proof.strong_universal

/-- The pilot supplies an inhabited task through the budget bridges.
model: the shipped-limit bridge and, for a declared word, the capability split.
-/
theorem strong_universal_error_free_T_budgets_accept :
    strong_universal_error_free_T_budgets source_alloc_limit target_alloc_limit Source.image Target.image :=
  strong_universal_error_free_T_budgets_of_pinned _ _ strong_universal_error_free_T_accept

/-- The pilot supplies an inhabited task through the budget bridges.
model: the shipped-limit bridge and, for a declared word, the capability split.
-/
theorem strong_universal_T_budgets_hwcap_rv64gc_accept :
    strong_universal_T_budgets_hwcap_rv64gc source_alloc_limit target_alloc_limit Source.image Target.image :=
  ((strong_universal_T_budgets_hwcap_splits _ _ _ _).1 strong_universal_T_budgets_accept).1

/-- The pilot supplies an inhabited task through the budget bridges.
model: the shipped-limit bridge and, for a declared word, the capability split.
-/
theorem strong_universal_error_free_T_budgets_hwcap_rv64gc_accept :
    strong_universal_error_free_T_budgets_hwcap_rv64gc source_alloc_limit target_alloc_limit Source.image Target.image :=
  ((strong_universal_error_free_T_budgets_hwcap_splits _ _ _ _).1 strong_universal_error_free_T_budgets_accept).1

/-- The pilot supplies an inhabited task through the budget bridges.
model: the shipped-limit bridge and, for a declared word, the capability split.
-/
theorem strong_universal_T_budgets_hwcap_rv64gcv_accept :
    strong_universal_T_budgets_hwcap_rv64gcv source_alloc_limit target_alloc_limit Source.image Target.image :=
  ((strong_universal_T_budgets_hwcap_splits _ _ _ _).1 strong_universal_T_budgets_accept).2

/-- The pilot supplies an inhabited task through the budget bridges.
model: the shipped-limit bridge and, for a declared word, the capability split.
-/
theorem strong_universal_error_free_T_budgets_hwcap_rv64gcv_accept :
    strong_universal_error_free_T_budgets_hwcap_rv64gcv source_alloc_limit target_alloc_limit Source.image Target.image :=
  ((strong_universal_error_free_T_budgets_hwcap_splits _ _ _ _).1 strong_universal_error_free_T_budgets_accept).2

/-- The pilot supplies an inhabited task through the budget bridges.
model: the shipped-limit bridge and, for a declared word, the capability split.
-/
theorem strong_universal_T_budgets_abort_accept :
    strong_universal_T_budgets_abort source_alloc_limit target_alloc_limit Source.image Target.image :=
  strong_universal_T_budgets_abort_of_pinned _ _ strong_universal_T_abort_accept

/-- The pilot supplies an inhabited task through the budget bridges.
model: the shipped-limit bridge and, for a declared word, the capability split.
-/
theorem strong_universal_error_free_T_budgets_abort_accept :
    strong_universal_error_free_T_budgets_abort source_alloc_limit target_alloc_limit Source.image Target.image :=
  strong_universal_error_free_T_budgets_abort_of_pinned _ _ strong_universal_error_free_T_abort_accept

/-- The pilot supplies an inhabited task through the budget bridges.
model: the shipped-limit bridge and, for a declared word, the capability split.
-/
theorem strong_universal_T_budgets_abort_hwcap_rv64gc_accept :
    strong_universal_T_budgets_abort_hwcap_rv64gc source_alloc_limit target_alloc_limit Source.image Target.image :=
  ((strong_universal_T_budgets_abort_hwcap_splits _ _ _ _).1 strong_universal_T_budgets_abort_accept).1

/-- The pilot supplies an inhabited task through the budget bridges.
model: the shipped-limit bridge and, for a declared word, the capability split.
-/
theorem strong_universal_error_free_T_budgets_abort_hwcap_rv64gc_accept :
    strong_universal_error_free_T_budgets_abort_hwcap_rv64gc source_alloc_limit target_alloc_limit Source.image Target.image :=
  ((strong_universal_error_free_T_budgets_abort_hwcap_splits _ _ _ _).1 strong_universal_error_free_T_budgets_abort_accept).1

/-- The pilot supplies an inhabited task through the budget bridges.
model: the shipped-limit bridge and, for a declared word, the capability split.
-/
theorem strong_universal_T_budgets_abort_hwcap_rv64gcv_accept :
    strong_universal_T_budgets_abort_hwcap_rv64gcv source_alloc_limit target_alloc_limit Source.image Target.image :=
  ((strong_universal_T_budgets_abort_hwcap_splits _ _ _ _).1 strong_universal_T_budgets_abort_accept).2

/-- The pilot supplies an inhabited task through the budget bridges.
model: the shipped-limit bridge and, for a declared word, the capability split.
-/
theorem strong_universal_error_free_T_budgets_abort_hwcap_rv64gcv_accept :
    strong_universal_error_free_T_budgets_abort_hwcap_rv64gcv source_alloc_limit target_alloc_limit Source.image Target.image :=
  ((strong_universal_error_free_T_budgets_abort_hwcap_splits _ _ _ _).1 strong_universal_error_free_T_budgets_abort_accept).2

/-- The terminating pilot supplies a concrete triple at the shipped limits.
model: the pinned bridge applied to the pilot accept.
-/
theorem strong_equiv_budgets_scfg_accept :
    strong_equiv_budgets_scfg may_fail_cfg source_alloc_limit target_alloc_limit Source.image Target.image
      Examples.rwx_flag_ns.Domain.source_entry Examples.rwx_flag_ns.Domain.target_entry demo_proc_input :=
  (strong_equiv_budgets_scfg_pinned may_fail_cfg _ _ _ _ _).2 strong_equiv_scfg_accept

/-- The terminating pilot supplies a concrete triple at the shipped limits.
model: the pinned bridge applied to the pilot accept.
-/
theorem strong_equiv_error_free_budgets_scfg_accept :
    strong_equiv_error_free_budgets_scfg may_fail_cfg source_alloc_limit target_alloc_limit Source.image Target.image
      Examples.rwx_flag_ns.Domain.source_entry Examples.rwx_flag_ns.Domain.target_entry demo_proc_input :=
  (strong_equiv_error_free_budgets_scfg_pinned may_fail_cfg _ _ _ _ _).2 strong_equiv_error_free_scfg_accept

/-- The terminating pilot supplies a concrete triple at the shipped limits.
model: the pinned bridge applied to the pilot accept.
-/
theorem strong_equiv_error_free_budgets_scfg_abort_accept :
    strong_equiv_error_free_budgets_scfg_abort may_fail_cfg source_alloc_limit target_alloc_limit Source.image Target.image
      Examples.rwx_flag_ns.Domain.source_entry Examples.rwx_flag_ns.Domain.target_entry abort_input :=
  (strong_equiv_error_free_budgets_scfg_abort_pinned may_fail_cfg _ _ _ _ _).2 strong_equiv_error_free_scfg_abort_accept

/-- The pilot supplies an inhabited task through the budget bridges.
model: the shipped-limit bridge and, for a declared word, the capability split.
-/
theorem strong_universal_T_scfg_budgets_accept :
    strong_universal_T_scfg_budgets may_fail_cfg source_alloc_limit target_alloc_limit Source.image Target.image :=
  strong_universal_T_scfg_budgets_of_scfg may_fail_cfg _ _ strong_universal_T_scfg_accept

/-- The pilot supplies an inhabited task through the budget bridges.
model: the shipped-limit bridge and, for a declared word, the capability split.
-/
theorem strong_universal_error_free_T_scfg_budgets_accept :
    strong_universal_error_free_T_scfg_budgets may_fail_cfg source_alloc_limit target_alloc_limit Source.image Target.image :=
  strong_universal_error_free_T_scfg_budgets_of_scfg may_fail_cfg _ _ strong_universal_error_free_T_scfg_accept

/-- The pilot supplies an inhabited task through the budget bridges.
model: the shipped-limit bridge and, for a declared word, the capability split.
-/
theorem strong_universal_T_scfg_budgets_hwcap_rv64gc_accept :
    strong_universal_T_scfg_budgets_hwcap_rv64gc may_fail_cfg source_alloc_limit target_alloc_limit Source.image Target.image :=
  ((strong_universal_T_scfg_budgets_hwcap_splits may_fail_cfg _ _ _ _).1 strong_universal_T_scfg_budgets_accept).1

/-- The pilot supplies an inhabited task through the budget bridges.
model: the shipped-limit bridge and, for a declared word, the capability split.
-/
theorem strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc_accept :
    strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc may_fail_cfg source_alloc_limit target_alloc_limit Source.image Target.image :=
  ((strong_universal_error_free_T_scfg_budgets_hwcap_splits may_fail_cfg _ _ _ _).1 strong_universal_error_free_T_scfg_budgets_accept).1

/-- The pilot supplies an inhabited task through the budget bridges.
model: the shipped-limit bridge and, for a declared word, the capability split.
-/
theorem strong_universal_T_scfg_budgets_hwcap_rv64gcv_accept :
    strong_universal_T_scfg_budgets_hwcap_rv64gcv may_fail_cfg source_alloc_limit target_alloc_limit Source.image Target.image :=
  ((strong_universal_T_scfg_budgets_hwcap_splits may_fail_cfg _ _ _ _).1 strong_universal_T_scfg_budgets_accept).2

/-- The pilot supplies an inhabited task through the budget bridges.
model: the shipped-limit bridge and, for a declared word, the capability split.
-/
theorem strong_universal_error_free_T_scfg_budgets_hwcap_rv64gcv_accept :
    strong_universal_error_free_T_scfg_budgets_hwcap_rv64gcv may_fail_cfg source_alloc_limit target_alloc_limit Source.image Target.image :=
  ((strong_universal_error_free_T_scfg_budgets_hwcap_splits may_fail_cfg _ _ _ _).1 strong_universal_error_free_T_scfg_budgets_accept).2

/-- The pilot supplies an inhabited task through the budget bridges.
model: the shipped-limit bridge and, for a declared word, the capability split.
-/
theorem strong_universal_T_scfg_budgets_abort_accept :
    strong_universal_T_scfg_budgets_abort may_fail_cfg source_alloc_limit target_alloc_limit Source.image Target.image :=
  strong_universal_T_scfg_budgets_abort_of_scfg may_fail_cfg _ _ strong_universal_T_scfg_abort_accept

/-- The pilot supplies an inhabited task through the budget bridges.
model: the shipped-limit bridge and, for a declared word, the capability split.
-/
theorem strong_universal_error_free_T_scfg_budgets_abort_accept :
    strong_universal_error_free_T_scfg_budgets_abort may_fail_cfg source_alloc_limit target_alloc_limit Source.image Target.image :=
  strong_universal_error_free_T_scfg_budgets_abort_of_scfg may_fail_cfg _ _ strong_universal_error_free_T_scfg_abort_accept

/-- The pilot supplies an inhabited task through the budget bridges.
model: the shipped-limit bridge and, for a declared word, the capability split.
-/
theorem strong_universal_T_scfg_budgets_abort_hwcap_rv64gc_accept :
    strong_universal_T_scfg_budgets_abort_hwcap_rv64gc may_fail_cfg source_alloc_limit target_alloc_limit Source.image Target.image :=
  ((strong_universal_T_scfg_budgets_abort_hwcap_splits may_fail_cfg _ _ _ _).1 strong_universal_T_scfg_budgets_abort_accept).1

/-- The pilot supplies an inhabited task through the budget bridges.
model: the shipped-limit bridge and, for a declared word, the capability split.
-/
theorem strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gc_accept :
    strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gc may_fail_cfg source_alloc_limit target_alloc_limit Source.image Target.image :=
  ((strong_universal_error_free_T_scfg_budgets_abort_hwcap_splits may_fail_cfg _ _ _ _).1 strong_universal_error_free_T_scfg_budgets_abort_accept).1

/-- The pilot supplies an inhabited task through the budget bridges.
model: the shipped-limit bridge and, for a declared word, the capability split.
-/
theorem strong_universal_T_scfg_budgets_abort_hwcap_rv64gcv_accept :
    strong_universal_T_scfg_budgets_abort_hwcap_rv64gcv may_fail_cfg source_alloc_limit target_alloc_limit Source.image Target.image :=
  ((strong_universal_T_scfg_budgets_abort_hwcap_splits may_fail_cfg _ _ _ _).1 strong_universal_T_scfg_budgets_abort_accept).2

/-- The pilot supplies an inhabited task through the budget bridges.
model: the shipped-limit bridge and, for a declared word, the capability split.
-/
theorem strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gcv_accept :
    strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gcv may_fail_cfg source_alloc_limit target_alloc_limit Source.image Target.image :=
  ((strong_universal_error_free_T_scfg_budgets_abort_hwcap_splits may_fail_cfg _ _ _ _).1 strong_universal_error_free_T_scfg_budgets_abort_accept).2

/-- The pilot satisfies both stance obligations.
model: the two concrete shipped-limit accepts.
-/
theorem strong_universal_T_budgets_either_accept :
    strong_universal_T_budgets_either source_alloc_limit target_alloc_limit Source.image Target.image :=
  ⟨strong_universal_T_budgets_accept, strong_universal_T_budgets_abort_accept⟩

/-- The pilot satisfies both stance obligations.
model: the two concrete shipped-limit accepts.
-/
theorem strong_universal_error_free_T_budgets_either_accept :
    strong_universal_error_free_T_budgets_either source_alloc_limit target_alloc_limit Source.image Target.image :=
  ⟨strong_universal_error_free_T_budgets_accept, strong_universal_error_free_T_budgets_abort_accept⟩

/-- The initial undecodable fetch refutes coverage or safety.
model: a concrete source run reaches the unmodeled error.
-/
theorem strong_equiv_budgets_refute (ls lt : Int) (inp : ProcInput) :
    ¬ strong_equiv_budgets ls lt undecodable_image undecodable_image demo_entry demo_entry inp :=
  fun h => h.1 (undecodable_run_unmodeled _ _)

/-- The initial undecodable fetch refutes coverage or safety.
model: a concrete source run reaches the unmodeled error.
-/
theorem strong_equiv_error_free_budgets_refute (ls lt : Int) (inp : ProcInput) :
    ¬ strong_equiv_error_free_budgets ls lt undecodable_image undecodable_image demo_entry demo_entry inp :=
  fun h => h.1 (run_unmodeled_errors _ _ _ _ (undecodable_run_unmodeled _ _))

/-- The initial undecodable fetch refutes coverage or safety.
model: a concrete source run reaches the unmodeled error.
-/
theorem strong_equiv_error_free_budgets_abort_refute (ls lt : Int) (inp : ProcInput) :
    ¬ strong_equiv_error_free_budgets_abort ls lt undecodable_image undecodable_image demo_entry demo_entry inp :=
  fun h => h.1.1 (run_unmodeled_errors _ _ _ _ (undecodable_run_unmodeled _ _))

/-- The counterexample satisfies the budget premise as well as validity.
model: the undecodable run at the concrete declared input, with budget reachability excluded.
-/
theorem strong_universal_T_budgets_refute (ls lt : Int) :
    ¬ strong_universal_T_budgets ls lt undecodable_image undecodable_image :=
  fun h => strong_equiv_budgets_refute ls lt _
    (h demo_entry demo_entry demo_proc_input undecodable_off_entry undecodable_off_entry
      Checks.Omni.demo_input_valid (undecodable_within_budget ls _))

/-- The counterexample satisfies the budget premise as well as validity.
model: the undecodable run at the concrete declared input, with budget reachability excluded.
-/
theorem strong_universal_error_free_T_budgets_refute (ls lt : Int) :
    ¬ strong_universal_error_free_T_budgets ls lt undecodable_image undecodable_image :=
  fun h => strong_equiv_error_free_budgets_refute ls lt _
    (h demo_entry demo_entry demo_proc_input undecodable_off_entry undecodable_off_entry
      Checks.Omni.demo_input_valid (undecodable_within_budget ls _))

/-- The counterexample satisfies the budget premise as well as validity.
model: the undecodable run at the concrete declared input, with budget reachability excluded.
-/
theorem strong_universal_T_budgets_hwcap_rv64gc_refute (ls lt : Int) :
    ¬ strong_universal_T_budgets_hwcap_rv64gc ls lt undecodable_image undecodable_image :=
  fun h => strong_equiv_budgets_refute ls lt _
    (h demo_entry demo_entry demo_proc_input undecodable_off_entry undecodable_off_entry
      scalar_input_valid (undecodable_within_budget ls _))

/-- The counterexample satisfies the budget premise as well as validity.
model: the undecodable run at the concrete declared input, with budget reachability excluded.
-/
theorem strong_universal_error_free_T_budgets_hwcap_rv64gc_refute (ls lt : Int) :
    ¬ strong_universal_error_free_T_budgets_hwcap_rv64gc ls lt undecodable_image undecodable_image :=
  fun h => strong_equiv_error_free_budgets_refute ls lt _
    (h demo_entry demo_entry demo_proc_input undecodable_off_entry undecodable_off_entry
      scalar_input_valid (undecodable_within_budget ls _))

/-- The counterexample satisfies the budget premise as well as validity.
model: the undecodable run at the concrete declared input, with budget reachability excluded.
-/
theorem strong_universal_T_budgets_hwcap_rv64gcv_refute (ls lt : Int) :
    ¬ strong_universal_T_budgets_hwcap_rv64gcv ls lt undecodable_image undecodable_image :=
  fun h => strong_equiv_budgets_refute ls lt _
    (h demo_entry demo_entry vector_input undecodable_vector_entry undecodable_vector_entry
      vector_input_valid (undecodable_within_budget ls _))

/-- The counterexample satisfies the budget premise as well as validity.
model: the undecodable run at the concrete declared input, with budget reachability excluded.
-/
theorem strong_universal_error_free_T_budgets_hwcap_rv64gcv_refute (ls lt : Int) :
    ¬ strong_universal_error_free_T_budgets_hwcap_rv64gcv ls lt undecodable_image undecodable_image :=
  fun h => strong_equiv_error_free_budgets_refute ls lt _
    (h demo_entry demo_entry vector_input undecodable_vector_entry undecodable_vector_entry
      vector_input_valid (undecodable_within_budget ls _))

/-- The counterexample satisfies the budget premise as well as validity.
model: the undecodable run at the concrete declared input, with budget reachability excluded.
-/
theorem strong_universal_T_budgets_abort_refute (ls lt : Int) :
    ¬ strong_universal_T_budgets_abort ls lt undecodable_image undecodable_image :=
  fun h => strong_equiv_budgets_refute ls lt _
    (h demo_entry demo_entry abort_input undecodable_abort_entry undecodable_abort_entry
      abort_input_valid (undecodable_within_budget ls _))

/-- The counterexample satisfies the budget premise as well as validity.
model: the undecodable run at the concrete declared input, with budget reachability excluded.
-/
theorem strong_universal_error_free_T_budgets_abort_refute (ls lt : Int) :
    ¬ strong_universal_error_free_T_budgets_abort ls lt undecodable_image undecodable_image :=
  fun h => strong_equiv_error_free_budgets_abort_refute ls lt _
    (h demo_entry demo_entry abort_input undecodable_abort_entry undecodable_abort_entry
      abort_input_valid (undecodable_within_budget ls _))

/-- The counterexample satisfies the budget premise as well as validity.
model: the undecodable run at the concrete declared input, with budget reachability excluded.
-/
theorem strong_universal_T_budgets_abort_hwcap_rv64gc_refute (ls lt : Int) :
    ¬ strong_universal_T_budgets_abort_hwcap_rv64gc ls lt undecodable_image undecodable_image :=
  fun h => strong_equiv_budgets_refute ls lt _
    (h demo_entry demo_entry abort_input undecodable_abort_entry undecodable_abort_entry
      budget_abort_rv64gc_valid (undecodable_within_budget ls _))

/-- The counterexample satisfies the budget premise as well as validity.
model: the undecodable run at the concrete declared input, with budget reachability excluded.
-/
theorem strong_universal_error_free_T_budgets_abort_hwcap_rv64gc_refute (ls lt : Int) :
    ¬ strong_universal_error_free_T_budgets_abort_hwcap_rv64gc ls lt undecodable_image undecodable_image :=
  fun h => strong_equiv_error_free_budgets_abort_refute ls lt _
    (h demo_entry demo_entry abort_input undecodable_abort_entry undecodable_abort_entry
      budget_abort_rv64gc_valid (undecodable_within_budget ls _))

/-- The counterexample satisfies the budget premise as well as validity.
model: the undecodable run at the concrete declared input, with budget reachability excluded.
-/
theorem strong_universal_T_budgets_abort_hwcap_rv64gcv_refute (ls lt : Int) :
    ¬ strong_universal_T_budgets_abort_hwcap_rv64gcv ls lt undecodable_image undecodable_image :=
  fun h => strong_equiv_budgets_refute ls lt _
    (h demo_entry demo_entry budget_abort_vector_input budget_undecodable_abort_vector_entry budget_undecodable_abort_vector_entry
      budget_abort_rv64gcv_valid (undecodable_within_budget ls _))

/-- The counterexample satisfies the budget premise as well as validity.
model: the undecodable run at the concrete declared input, with budget reachability excluded.
-/
theorem strong_universal_error_free_T_budgets_abort_hwcap_rv64gcv_refute (ls lt : Int) :
    ¬ strong_universal_error_free_T_budgets_abort_hwcap_rv64gcv ls lt undecodable_image undecodable_image :=
  fun h => strong_equiv_error_free_budgets_abort_refute ls lt _
    (h demo_entry demo_entry budget_abort_vector_input budget_undecodable_abort_vector_entry budget_undecodable_abort_vector_entry
      budget_abort_rv64gcv_valid (undecodable_within_budget ls _))

/-- The initial undecodable fetch refutes coverage or safety.
model: a concrete source run reaches the unmodeled error.
-/
theorem strong_equiv_budgets_scfg_refute (cfg : SpuriousCfg) (ls lt : Int) (inp : ProcInput) :
    ¬ strong_equiv_budgets_scfg cfg ls lt undecodable_image undecodable_image demo_entry demo_entry inp :=
  fun h => h.1 (undecodable_run_scfg_unmodeled cfg _ _)

/-- The initial undecodable fetch refutes coverage or safety.
model: a concrete source run reaches the unmodeled error.
-/
theorem strong_equiv_error_free_budgets_scfg_refute (cfg : SpuriousCfg) (ls lt : Int) (inp : ProcInput) :
    ¬ strong_equiv_error_free_budgets_scfg cfg ls lt undecodable_image undecodable_image demo_entry demo_entry inp :=
  fun h => h.1 (run_scfg_unmodeled_errors cfg _ _ _ _ (undecodable_run_scfg_unmodeled cfg _ _))

/-- The initial undecodable fetch refutes coverage or safety.
model: a concrete source run reaches the unmodeled error.
-/
theorem strong_equiv_error_free_budgets_scfg_abort_refute (cfg : SpuriousCfg) (ls lt : Int) (inp : ProcInput) :
    ¬ strong_equiv_error_free_budgets_scfg_abort cfg ls lt undecodable_image undecodable_image demo_entry demo_entry inp :=
  fun h => h.1.1 (run_scfg_unmodeled_errors cfg _ _ _ _ (undecodable_run_scfg_unmodeled cfg _ _))

/-- The counterexample satisfies the budget premise as well as validity.
model: the undecodable run at the concrete declared input, with budget reachability excluded.
-/
theorem strong_universal_T_scfg_budgets_refute (cfg : SpuriousCfg) (ls lt : Int) :
    ¬ strong_universal_T_scfg_budgets cfg ls lt undecodable_image undecodable_image :=
  fun h => strong_equiv_budgets_scfg_refute cfg ls lt _
    (h demo_entry demo_entry demo_proc_input undecodable_off_entry undecodable_off_entry
      Checks.Omni.demo_input_valid (undecodable_within_budget_scfg cfg ls _))

/-- The counterexample satisfies the budget premise as well as validity.
model: the undecodable run at the concrete declared input, with budget reachability excluded.
-/
theorem strong_universal_error_free_T_scfg_budgets_refute (cfg : SpuriousCfg) (ls lt : Int) :
    ¬ strong_universal_error_free_T_scfg_budgets cfg ls lt undecodable_image undecodable_image :=
  fun h => strong_equiv_error_free_budgets_scfg_refute cfg ls lt _
    (h demo_entry demo_entry demo_proc_input undecodable_off_entry undecodable_off_entry
      Checks.Omni.demo_input_valid (undecodable_within_budget_scfg cfg ls _))

/-- The counterexample satisfies the budget premise as well as validity.
model: the undecodable run at the concrete declared input, with budget reachability excluded.
-/
theorem strong_universal_T_scfg_budgets_hwcap_rv64gc_refute (cfg : SpuriousCfg) (ls lt : Int) :
    ¬ strong_universal_T_scfg_budgets_hwcap_rv64gc cfg ls lt undecodable_image undecodable_image :=
  fun h => strong_equiv_budgets_scfg_refute cfg ls lt _
    (h demo_entry demo_entry demo_proc_input undecodable_off_entry undecodable_off_entry
      scalar_input_valid (undecodable_within_budget_scfg cfg ls _))

/-- The counterexample satisfies the budget premise as well as validity.
model: the undecodable run at the concrete declared input, with budget reachability excluded.
-/
theorem strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc_refute (cfg : SpuriousCfg) (ls lt : Int) :
    ¬ strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc cfg ls lt undecodable_image undecodable_image :=
  fun h => strong_equiv_error_free_budgets_scfg_refute cfg ls lt _
    (h demo_entry demo_entry demo_proc_input undecodable_off_entry undecodable_off_entry
      scalar_input_valid (undecodable_within_budget_scfg cfg ls _))

/-- The counterexample satisfies the budget premise as well as validity.
model: the undecodable run at the concrete declared input, with budget reachability excluded.
-/
theorem strong_universal_T_scfg_budgets_hwcap_rv64gcv_refute (cfg : SpuriousCfg) (ls lt : Int) :
    ¬ strong_universal_T_scfg_budgets_hwcap_rv64gcv cfg ls lt undecodable_image undecodable_image :=
  fun h => strong_equiv_budgets_scfg_refute cfg ls lt _
    (h demo_entry demo_entry vector_input undecodable_vector_entry undecodable_vector_entry
      vector_input_valid (undecodable_within_budget_scfg cfg ls _))

/-- The counterexample satisfies the budget premise as well as validity.
model: the undecodable run at the concrete declared input, with budget reachability excluded.
-/
theorem strong_universal_error_free_T_scfg_budgets_hwcap_rv64gcv_refute (cfg : SpuriousCfg) (ls lt : Int) :
    ¬ strong_universal_error_free_T_scfg_budgets_hwcap_rv64gcv cfg ls lt undecodable_image undecodable_image :=
  fun h => strong_equiv_error_free_budgets_scfg_refute cfg ls lt _
    (h demo_entry demo_entry vector_input undecodable_vector_entry undecodable_vector_entry
      vector_input_valid (undecodable_within_budget_scfg cfg ls _))

/-- The counterexample satisfies the budget premise as well as validity.
model: the undecodable run at the concrete declared input, with budget reachability excluded.
-/
theorem strong_universal_T_scfg_budgets_abort_refute (cfg : SpuriousCfg) (ls lt : Int) :
    ¬ strong_universal_T_scfg_budgets_abort cfg ls lt undecodable_image undecodable_image :=
  fun h => strong_equiv_budgets_scfg_refute cfg ls lt _
    (h demo_entry demo_entry abort_input undecodable_abort_entry undecodable_abort_entry
      abort_input_valid (undecodable_within_budget_scfg cfg ls _))

/-- The counterexample satisfies the budget premise as well as validity.
model: the undecodable run at the concrete declared input, with budget reachability excluded.
-/
theorem strong_universal_error_free_T_scfg_budgets_abort_refute (cfg : SpuriousCfg) (ls lt : Int) :
    ¬ strong_universal_error_free_T_scfg_budgets_abort cfg ls lt undecodable_image undecodable_image :=
  fun h => strong_equiv_error_free_budgets_scfg_abort_refute cfg ls lt _
    (h demo_entry demo_entry abort_input undecodable_abort_entry undecodable_abort_entry
      abort_input_valid (undecodable_within_budget_scfg cfg ls _))

/-- The counterexample satisfies the budget premise as well as validity.
model: the undecodable run at the concrete declared input, with budget reachability excluded.
-/
theorem strong_universal_T_scfg_budgets_abort_hwcap_rv64gc_refute (cfg : SpuriousCfg) (ls lt : Int) :
    ¬ strong_universal_T_scfg_budgets_abort_hwcap_rv64gc cfg ls lt undecodable_image undecodable_image :=
  fun h => strong_equiv_budgets_scfg_refute cfg ls lt _
    (h demo_entry demo_entry abort_input undecodable_abort_entry undecodable_abort_entry
      budget_abort_rv64gc_valid (undecodable_within_budget_scfg cfg ls _))

/-- The counterexample satisfies the budget premise as well as validity.
model: the undecodable run at the concrete declared input, with budget reachability excluded.
-/
theorem strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gc_refute (cfg : SpuriousCfg) (ls lt : Int) :
    ¬ strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gc cfg ls lt undecodable_image undecodable_image :=
  fun h => strong_equiv_error_free_budgets_scfg_abort_refute cfg ls lt _
    (h demo_entry demo_entry abort_input undecodable_abort_entry undecodable_abort_entry
      budget_abort_rv64gc_valid (undecodable_within_budget_scfg cfg ls _))

/-- The counterexample satisfies the budget premise as well as validity.
model: the undecodable run at the concrete declared input, with budget reachability excluded.
-/
theorem strong_universal_T_scfg_budgets_abort_hwcap_rv64gcv_refute (cfg : SpuriousCfg) (ls lt : Int) :
    ¬ strong_universal_T_scfg_budgets_abort_hwcap_rv64gcv cfg ls lt undecodable_image undecodable_image :=
  fun h => strong_equiv_budgets_scfg_refute cfg ls lt _
    (h demo_entry demo_entry budget_abort_vector_input budget_undecodable_abort_vector_entry budget_undecodable_abort_vector_entry
      budget_abort_rv64gcv_valid (undecodable_within_budget_scfg cfg ls _))

/-- The counterexample satisfies the budget premise as well as validity.
model: the undecodable run at the concrete declared input, with budget reachability excluded.
-/
theorem strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gcv_refute (cfg : SpuriousCfg) (ls lt : Int) :
    ¬ strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gcv cfg ls lt undecodable_image undecodable_image :=
  fun h => strong_equiv_error_free_budgets_scfg_abort_refute cfg ls lt _
    (h demo_entry demo_entry budget_abort_vector_input budget_undecodable_abort_vector_entry budget_undecodable_abort_vector_entry
      budget_abort_rv64gcv_valid (undecodable_within_budget_scfg cfg ls _))

/-- One failed stance suffices to refute the conjunction.
model: the concrete off-stance counterexample with its budget premise discharged.
-/
theorem strong_universal_T_budgets_either_refute (ls lt : Int) :
    ¬ strong_universal_T_budgets_either ls lt undecodable_image undecodable_image :=
  fun h => strong_universal_T_budgets_refute ls lt h.1

/-- One failed stance suffices to refute the conjunction.
model: the concrete off-stance counterexample with its budget premise discharged.
-/
theorem strong_universal_error_free_T_budgets_either_refute (ls lt : Int) :
    ¬ strong_universal_error_free_T_budgets_either ls lt undecodable_image undecodable_image :=
  fun h => strong_universal_error_free_T_budgets_refute ls lt h.1

/-- The Boolean gate retains the floor and overhead comparisons separately.
model: the two integer comparisons expanded with the measured literal charge.
-/
theorem budget_headroom_ok_iff (ls lt : Int) :
    budget_headroom_ok ls lt = true ↔
      (decide ((4096 : Int) ≤ ls) && decide (9 * ls + 8 * (261 * 1048576) ≤ 8 * lt)) = true := Iff.rfl

/-- The shipped and sanitizer limits clear both arithmetic obligations.
model: literal byte-count inequalities, independently checked by the kernel.
-/
theorem budget_headroom_ok_accept :
    ((4096 : Int) ≤ 0x400000000 ∧ 9 * (0x400000000 : Int) + 8 * (261 * 1048576) ≤ 8 * 0x8000000000) ∧
    ((4096 : Int) ≤ 0x80000000 ∧ 9 * (0x80000000 : Int) + 8 * (261 * 1048576) ≤ 8 * 0x8000000000) := by decide

/-- Equal limits fail the overhead inequality, while zero fails the floor.
model: independent negations of the literal equal-budget and zero-budget obligations.
-/
theorem budget_headroom_ok_refute :
    ¬ ((4096 : Int) ≤ 0x400000000 ∧ 9 * (0x400000000 : Int) + 8 * (261 * 1048576) ≤ 8 * 0x400000000) ∧
    ¬ ((4096 : Int) ≤ 0 ∧ 9 * (0 : Int) + 8 * (261 * 1048576) ≤ 8 * 0x8000000000) := by decide

/-- The shipped and sanitizer limits clear the actual Boolean gate.
model: `budget_headroom_ok` evaluated at independently stated byte counts.
-/
theorem budget_headroom_gate_accept :
    budget_headroom_ok 0x400000000 0x8000000000 = true ∧
    budget_headroom_ok 0x80000000 0x8000000000 = true := by decide

/-- Equal limits fail the overhead inequality, while zero fails the floor.
model: `budget_headroom_ok` evaluated on equal and zero source budgets.
-/
theorem budget_headroom_gate_refute :
    budget_headroom_ok 0x400000000 0x400000000 = false ∧
    budget_headroom_ok 0 0x8000000000 = false := by decide

/-- One page needs exactly 273682944 target bytes, including the fixed charge.
model: `budget_headroom_ok` at the independently calculated overhead boundary.
-/
theorem budget_headroom_boundary_accept :
    budget_headroom_ok 4096 273682944 = true := by decide

/-- One byte less than the required headroom is insufficient.
model: `budget_headroom_ok` just below the overhead boundary.
-/
theorem budget_headroom_boundary_refute :
    budget_headroom_ok 4096 273682943 = false := by decide

/-- The sanitizer's source limit is two GiB.
model: `sanitizer_source_limit` checked against its literal byte count.
-/
theorem sanitizer_source_limit_value : sanitizer_source_limit = 0x80000000 := by decide

/-- The sanitizer limit must not silently grow to the ordinary source budget.
model: `sanitizer_source_limit` compared with `source_alloc_limit`.
-/
theorem sanitizer_source_limit_below_source : sanitizer_source_limit < source_alloc_limit := by decide

/-- The auxiliary-vector list publishes exactly the supplied capability word.
model: `auxv_entries` filtered by the `AT_HWCAP` key; this does not assert serialization.
-/
theorem auxv_hwcap_is_exactly_the_launch_word (ph : PhdrInfo) (at_random uid hw : word) :
    (auxv_entries ph at_random uid hw).filter (fun e => bv_eqb e.1 AT_HWCAP) =
      [(AT_HWCAP, hw)] := by rfl

/-- The scalar declaration publishes its own word.
model: `auxv_hwcap_is_exactly_the_launch_word` and `valid_input_hwcap_rv64gc_word`.
-/
theorem the_rv64gc_declaration_publishes_the_v_less_word (inp : ProcInput) (ph : PhdrInfo)
    (at_random : word) (h : valid_input_hwcap_rv64gc inp) :
    (auxv_entries ph at_random inp.in_uid inp.in_hwcap).filter (fun e => bv_eqb e.1 AT_HWCAP) =
      [(AT_HWCAP, hwcap_rv64gc)] := by
  rw [auxv_hwcap_is_exactly_the_launch_word, valid_input_hwcap_rv64gc_word _ h]

/-- The vector declaration publishes its distinct word.
model: `auxv_hwcap_is_exactly_the_launch_word` and `valid_input_hwcap_rv64gcv_word`.
-/
theorem the_rv64gcv_declaration_publishes_the_v_word (inp : ProcInput) (ph : PhdrInfo)
    (at_random : word) (h : valid_input_hwcap_rv64gcv inp) :
    (auxv_entries ph at_random inp.in_uid inp.in_hwcap).filter (fun e => bv_eqb e.1 AT_HWCAP) =
      [(AT_HWCAP, hwcap_rv64gcv)] := by
  rw [auxv_hwcap_is_exactly_the_launch_word, valid_input_hwcap_rv64gcv_word _ h]

/-- Publishing the scalar word for a vector launch is rejected.
model: the independently unequal capability words in the filtered `auxv_entries` list.
-/
theorem auxv_hwcap_wrong_word_refute :
    (auxv_entries demo_phdrs 0 0 hwcap_rv64gcv).filter (fun e => bv_eqb e.1 AT_HWCAP) ≠
      [(AT_HWCAP, hwcap_rv64gc)] := by decide

/-- The two independently named declarations pin both directions of the split.
model: Rocq Checks/Cases/Hwcap.v part (vi), restated outside its mirror path.
-/
theorem the_budgets_cell_is_exactly_its_two_declarations (ls lt : Int) (s t : Image) :
    (strong_universal_T_budgets ls lt s t →
      strong_universal_T_budgets_hwcap_rv64gc ls lt s t ∧ strong_universal_T_budgets_hwcap_rv64gcv ls lt s t) ∧
    (strong_universal_T_budgets_hwcap_rv64gc ls lt s t → strong_universal_T_budgets_hwcap_rv64gcv ls lt s t →
      strong_universal_T_budgets ls lt s t) :=
  ⟨(strong_universal_T_budgets_hwcap_splits ls lt s t).1,
    fun hgc hgcv => (strong_universal_T_budgets_hwcap_splits ls lt s t).2 ⟨hgc, hgcv⟩⟩

/-- The two independently named declarations pin both directions of the split.
model: Rocq Checks/Cases/Hwcap.v part (vi), restated outside its mirror path.
-/
theorem the_error_free_budgets_cell_is_exactly_its_two_declarations (ls lt : Int) (s t : Image) :
    (strong_universal_error_free_T_budgets ls lt s t →
      strong_universal_error_free_T_budgets_hwcap_rv64gc ls lt s t ∧ strong_universal_error_free_T_budgets_hwcap_rv64gcv ls lt s t) ∧
    (strong_universal_error_free_T_budgets_hwcap_rv64gc ls lt s t → strong_universal_error_free_T_budgets_hwcap_rv64gcv ls lt s t →
      strong_universal_error_free_T_budgets ls lt s t) :=
  ⟨(strong_universal_error_free_T_budgets_hwcap_splits ls lt s t).1,
    fun hgc hgcv => (strong_universal_error_free_T_budgets_hwcap_splits ls lt s t).2 ⟨hgc, hgcv⟩⟩

/-- The two independently named declarations pin both directions of the split.
model: Rocq Checks/Cases/Hwcap.v part (vi), restated outside its mirror path.
-/
theorem the_abort_budgets_cell_is_exactly_its_two_declarations (ls lt : Int) (s t : Image) :
    (strong_universal_T_budgets_abort ls lt s t →
      strong_universal_T_budgets_abort_hwcap_rv64gc ls lt s t ∧ strong_universal_T_budgets_abort_hwcap_rv64gcv ls lt s t) ∧
    (strong_universal_T_budgets_abort_hwcap_rv64gc ls lt s t → strong_universal_T_budgets_abort_hwcap_rv64gcv ls lt s t →
      strong_universal_T_budgets_abort ls lt s t) :=
  ⟨(strong_universal_T_budgets_abort_hwcap_splits ls lt s t).1,
    fun hgc hgcv => (strong_universal_T_budgets_abort_hwcap_splits ls lt s t).2 ⟨hgc, hgcv⟩⟩

/-- The two independently named declarations pin both directions of the split.
model: Rocq Checks/Cases/Hwcap.v part (vi), restated outside its mirror path.
-/
theorem the_error_free_abort_budgets_cell_is_exactly_its_two_declarations (ls lt : Int) (s t : Image) :
    (strong_universal_error_free_T_budgets_abort ls lt s t →
      strong_universal_error_free_T_budgets_abort_hwcap_rv64gc ls lt s t ∧ strong_universal_error_free_T_budgets_abort_hwcap_rv64gcv ls lt s t) ∧
    (strong_universal_error_free_T_budgets_abort_hwcap_rv64gc ls lt s t → strong_universal_error_free_T_budgets_abort_hwcap_rv64gcv ls lt s t →
      strong_universal_error_free_T_budgets_abort ls lt s t) :=
  ⟨(strong_universal_error_free_T_budgets_abort_hwcap_splits ls lt s t).1,
    fun hgc hgcv => (strong_universal_error_free_T_budgets_abort_hwcap_splits ls lt s t).2 ⟨hgc, hgcv⟩⟩

/-- The two independently named declarations pin both directions of the split.
model: Rocq Checks/Cases/Hwcap.v part (vi), restated outside its mirror path.
-/
theorem the_scfg_budgets_cell_is_exactly_its_two_declarations (cfg : SpuriousCfg) (ls lt : Int) (s t : Image) :
    (strong_universal_T_scfg_budgets cfg ls lt s t →
      strong_universal_T_scfg_budgets_hwcap_rv64gc cfg ls lt s t ∧ strong_universal_T_scfg_budgets_hwcap_rv64gcv cfg ls lt s t) ∧
    (strong_universal_T_scfg_budgets_hwcap_rv64gc cfg ls lt s t → strong_universal_T_scfg_budgets_hwcap_rv64gcv cfg ls lt s t →
      strong_universal_T_scfg_budgets cfg ls lt s t) :=
  ⟨(strong_universal_T_scfg_budgets_hwcap_splits cfg ls lt s t).1,
    fun hgc hgcv => (strong_universal_T_scfg_budgets_hwcap_splits cfg ls lt s t).2 ⟨hgc, hgcv⟩⟩

/-- The two independently named declarations pin both directions of the split.
model: Rocq Checks/Cases/Hwcap.v part (vi), restated outside its mirror path.
-/
theorem the_error_free_scfg_budgets_cell_is_exactly_its_two_declarations (cfg : SpuriousCfg) (ls lt : Int) (s t : Image) :
    (strong_universal_error_free_T_scfg_budgets cfg ls lt s t →
      strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc cfg ls lt s t ∧ strong_universal_error_free_T_scfg_budgets_hwcap_rv64gcv cfg ls lt s t) ∧
    (strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc cfg ls lt s t → strong_universal_error_free_T_scfg_budgets_hwcap_rv64gcv cfg ls lt s t →
      strong_universal_error_free_T_scfg_budgets cfg ls lt s t) :=
  ⟨(strong_universal_error_free_T_scfg_budgets_hwcap_splits cfg ls lt s t).1,
    fun hgc hgcv => (strong_universal_error_free_T_scfg_budgets_hwcap_splits cfg ls lt s t).2 ⟨hgc, hgcv⟩⟩

/-- Exit-only instruction paths survive every refusal configuration.
model: `sstep_cfg_instr` and `sstep_cfg_exit` have no refusal filter.
-/
theorem to_exit_star_cfg (segs : List Segment) (cfg : SpuriousCfg) (code : word)
    (ms : machine_state) (m : Model) (hh : m_halted m = none) (hl : m_vm_lazy m = [])
    (h : to_exit segs code ms) :
    ∃ c, star_cfg segs cfg (config.mkCfg ms m)
      [ExitEv (bv_and code (Z_to_bv 64 255)) (m_fs m)] c := by
  induction h with
  | te_here ms x8 hs hn hc =>
    refine ⟨config.mkCfg ms (with_halted (bv_and code (Z_to_bv 64 255)) m), ?_⟩
    have step := sstep_cfg.sstep_cfg_exit (segs := segs) (cfg := cfg) ms m x8 _ _ [] _
      hh hs (exit_dispatch_ok _ m hn) rfl rfl
    rw [in_arg0_sys_input, hc] at step
    exact star_cfg.star_cfg_step _ _ _ _ _ step (star_cfg.star_cfg_refl _)
  | te_step ms ms' hs hstep _ ih =>
    obtain ⟨c, hstar⟩ := ih
    refine ⟨c, star_cfg.star_cfg_step _ [] _ _ _ ?_ hstar⟩
    apply sstep_cfg.sstep_cfg_instr _ _ _ _ hh hs
    rw [mi_account_step_no_lazy _ _ _ hl, hstep]

/-- The exit-zero fixture has an instruction path independent of the entry draws.
model: `Checks.Omni.exit0_step_100`, `exit0_step_104`, and `exit0_step_108`.
-/
theorem exit0_to_exit (en : ExecEntry) (inp : ProcInput) :
    to_exit exit0_segments (Z_to_bv 64 0)
      (init_machine_state exit0_segments 0x100 demo_phdrs en.en_sp en.en_draw
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) := by
  rw [LinuxProcessSemantics.Common.PropExec.init_mkst, Checks.Omni.entry_pc_0x100]
  apply to_exit.te_step _ _ rfl (Checks.Omni.exit0_step_100 _ _ _)
  apply to_exit.te_step _ _ rfl (Checks.Omni.exit0_step_104 _ _ _)
  apply to_exit.te_step _ _ rfl (Checks.Omni.exit0_step_108 _ _ _)
  refine to_exit.te_here _ (Z_to_bv 64 93) ?_ (Or.inl (by decide)) ?_
  · change some (Riscv.Sem.reg_get (bvmap_set (10 : BitVec 5) 0 (bvmap_set 17 93 _)) 17) = _
    simp only [Riscv.Sem.reg_get]
    rw [bvmap_get_set_other _ _ _ _ (by decide), bvmap_get_set_same]
    rfl
  · change Riscv.Sem.reg_get (bvmap_set (10 : BitVec 5) 0 _) 10 = _
    simp only [Riscv.Sem.reg_get, bvmap_get_set_same]
    rfl


/-- The complete exit trace remains available under filtering, and every trace is its prefix.
model: `run_scfg_sub_traces` supplies one direction; `to_exit_star_cfg` supplies the other.
-/
theorem exit0_scfg_traces (cfg : SpuriousCfg) (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (tr : List event) :
    (run_scfg cfg exit0_image lim en inp).bh_traces tr ↔
      is_prefix tr [ExitEv (Z_to_bv 64 0) inp.in_fs] := by
  constructor
  · intro h
    exact (Checks.Omni.exit0_obs _ _ _ _ _ _ tr).1
      (run_scfg_sub_traces cfg _ _ _ _ tr h)
  · intro h
    obtain ⟨c, hc⟩ := to_exit_star_cfg exit0_segments cfg (Z_to_bv 64 0) _
      (init_model (segments_reserved exit0_segments) en.en_brk en.en_mmap_base en.en_sp lim inp)
      rfl rfl (exit0_to_exit en inp)
    exact ⟨_, c, hc, h⟩

/-- Exit zero stays safe and trace-equivalent at all filtered configurations.
model: `exit0_scfg_traces` and `run_scfg_sub_errors` applied to the exit fixture.
-/
theorem exit0_error_free_scfg (cfg : SpuriousCfg) :
    strong_universal_error_free_T_scfg cfg exit0_image exit0_image := by
  intro es et inp _ _ _
  refine ⟨?_, ?_, fun tr => (exit0_scfg_traces cfg _ es inp tr).trans
    (exit0_scfg_traces cfg _ et inp tr).symm⟩
  · exact fun h => Checks.Omni.exit0_error_free_run _ _ _ (run_scfg_sub_errors cfg _ _ _ _ h)
  · exact fun h => Checks.Omni.exit0_error_free_run _ _ _ (run_scfg_sub_errors cfg _ _ _ _ h)

/-- Both refusal-filtering choices retain the inhabited exit-zero accept.
model: `exit0_error_free_scfg` at `forced_only_cfg` and `alloc_only_cfg false`.
-/
theorem filtered_exit_accept :
    strong_universal_error_free_T_scfg forced_only_cfg exit0_image exit0_image ∧
    strong_universal_error_free_T_scfg (alloc_only_cfg false) exit0_image exit0_image :=
  ⟨exit0_error_free_scfg _, exit0_error_free_scfg _⟩

/-- Filtering cannot invent an exit-one observation for the exit-zero image.
model: `exit0_scfg_traces` characterizes the actual filtered trace set.
-/
theorem filtered_exit_refute :
    ¬ (run_scfg forced_only_cfg exit0_image source_alloc_limit demo_entry demo_proc_input).bh_traces
      [ExitEv (Z_to_bv 64 1) demo_proc_input.in_fs] := by
  intro h
  have hp := (exit0_scfg_traces _ _ _ _ _).1 h
  have : (Z_to_bv 64 1 : word) = Z_to_bv 64 0 := by injection hp.1
  contradiction

/-! A concrete signal-death witness, shared by the plain and configured contracts. -/

/-- The program learns its tid and then sends itself SIGABRT.
model: `Checks.AbortWitness`'s six-instruction fixture, with two syscall transitions.
-/
def abrt_image : Image := Image.mkImage
  [⟨0x100, 24, "r-x", ["930800061305000073000000930820089305600073000000"]⟩]
  0x100 demo_phdrs

private def abrt_ms : machine_state :=
  init_machine_state abrt_image.img_segments 0x100 demo_phdrs demo_entry.en_sp
    demo_entry.en_draw abort_input.in_argv abort_input.in_envp abort_input.in_uid abort_input.in_hwcap

private def advance_instruction (ms : machine_state) : machine_state :=
  match step abrt_image.img_segments ms with
  | MachineOk ms' => ms'
  | _ => ms

private def abrt_s (k : Nat) : machine_state := Nat.repeat advance_instruction k abrt_ms
private def abrt_effect : SyscallEffect := mkEffect (Z_to_bv 64 4242) [] []
private def abrt_t (k : Nat) : machine_state :=
  Nat.repeat advance_instruction k (advance_past_svc (apply_effect (abrt_s 3) abrt_effect))
private def abrt_model (lim : Int) : Model :=
  init_model (segments_reserved abrt_image.img_segments) demo_entry.en_brk
    demo_entry.en_mmap_base demo_entry.en_sp lim abort_input

/-- The abort image fits the same entry reservations as the undecodable fixture.
model: `valid_entry` at `abrt_image`, `demo_entry`, and `abort_input`.
-/
theorem abrt_entry_valid : valid_entry abrt_image demo_entry abort_input := by
  rw [valid_entry_sv48 _ _ _ (valid_input_abort_va_size _ abort_input_valid)]
  refine ⟨by unfold valid_sp; decide, by unfold valid_brk; decide,
    by unfold valid_mmap_base; decide, ?_⟩
  exact undecodable_abort_entry.2.2.2

set_option maxRecDepth 32768 in
/-- Every configuration admits the concrete path to the signal event.
model: `sstep_cfg` executes the image; `check_syscall_sound_ok` validates both answers.
-/
theorem abrt_dies_by_signal_scfg (cfg : SpuriousCfg) (lim : Int) :
    dies_by_signal (run_scfg cfg abrt_image lim demo_entry abort_input) := by
  let m := abrt_model lim
  let mt := with_tid (Z_to_bv 64 4242) m
  let mk := with_killed (Z_to_bv 64 6) mt
  have first (k : Nat) (hk : k < 3) :
      sstep_cfg abrt_image.img_segments cfg (config.mkCfg (abrt_s k) m) []
        (SNext (config.mkCfg (abrt_s (k + 1)) m)) := by
    apply sstep_cfg.sstep_cfg_instr _ _ _ _ rfl
    · obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      all_goals rfl
    · rw [mi_account_step_no_lazy _ _ _ rfl]
      obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      all_goals rfl
  have second (k : Nat) (hk : k < 3) :
      sstep_cfg abrt_image.img_segments cfg (config.mkCfg (abrt_t k) mt) []
        (SNext (config.mkCfg (abrt_t (k + 1)) mt)) := by
    apply sstep_cfg.sstep_cfg_instr _ _ _ _ rfl
    · obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      all_goals rfl
    · rw [mi_account_step_no_lazy _ _ _ rfl]
      obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      all_goals rfl
  have tid : sstep_cfg abrt_image.img_segments cfg (config.mkCfg (abrt_s 3) m) []
      (SNext (config.mkCfg (abrt_t 0) mt)) := by
    apply sstep_cfg.sstep_cfg_syscall _ _ (Z_to_bv 64 96) abrt_effect mt mt [] rfl (by decide +kernel)
    · apply Checks.ExecutableSpecs.check_syscall_sound_ok
      rfl
    · exact spurious_refusal_not_refusal cfg _ _ _ (by rfl)
    · rfl
    · exact materialize_model_accesses_no_lazy _ _ rfl
  have kill : sstep_cfg abrt_image.img_segments cfg (config.mkCfg (abrt_t 3) mt)
      [KillEv (Z_to_bv 64 6) (m_fs mk)] (SNext (config.mkCfg (abrt_t 3) mk)) := by
    apply sstep_cfg.sstep_cfg_killed _ _ (Z_to_bv 64 130) (mkEffect (Z_to_bv 64 0) [] []) mk [] _ rfl (by decide +kernel)
    · apply Checks.ExecutableSpecs.check_syscall_sound_ok
      change Checks.Sys.Table.check_tkill_a0_a1 _ _ _ = _
      rw [Checks.Sys.Table.check_tkill_a0_a1_eq]
      have hp : Sys.Syscall.pid32 (in_arg (sys_input abrt_image.img_segments (abrt_t 3) (Z_to_bv 64 130)) 0) =
          Z_to_bv 64 4242 := by decide +kernel
      have hs : Sys.Kernel.Signal.sig32 (in_arg (sys_input abrt_image.img_segments (abrt_t 3) (Z_to_bv 64 130)) 1) =
          Z_to_bv 64 6 := by decide +kernel
      rw [hp, hs]
      have ha : m_abort_terminal mt = true := rfl
      have ht : m_tid mt = some (Z_to_bv 64 4242) := rfl
      have hm : m_sigmask mt = Z_to_bv 64 0 := rfl
      simp [Checks.Sys.Kernel.Signal.check_tkill, Checks.Sys.Kernel.Signal.check_tkill_self,
        Checks.Sys.Kernel.Signal.check_send_sigabrt, ha, ht, hm,
        Sys.Kernel.Signal.pid_positive, Sys.Kernel.Signal.tkill_sig_valid,
        Sys.Kernel.Signal.sigabrt_blocked, bv_eqb, bv_unsigned, Z_to_bv, bv_and,
        Sys.Uapi.SIGABRT, Sys.Uapi.sigabrt_mask, Sys.Syscall.w_is0, mk]
    · rfl
  refine ⟨[KillEv (Z_to_bv 64 6) (m_fs mk)], Z_to_bv 64 6, m_fs mk, ?_, List.mem_cons_self⟩
  refine ⟨_, config.mkCfg (abrt_t 3) mk, ?_, is_prefix_refl _⟩
  exact star_cfg.star_cfg_step _ _ _ _ _ (first 0 (by decide))
    (star_cfg.star_cfg_step _ _ _ _ _ (first 1 (by decide))
    (star_cfg.star_cfg_step _ _ _ _ _ (first 2 (by decide))
    (star_cfg.star_cfg_step _ _ _ _ _ tid
    (star_cfg.star_cfg_step _ _ _ _ _ (second 0 (by decide))
    (star_cfg.star_cfg_step _ _ _ _ _ (second 1 (by decide))
    (star_cfg.star_cfg_step _ _ _ _ _ (second 2 (by decide))
    (star_cfg.star_cfg_step _ _ _ _ _ kill (star_cfg.star_cfg_refl _))))))))

/-- The plain run also reaches an actual signal event.
model: `run_scfg_may_fail` transports `abrt_dies_by_signal_scfg` to `run`.
-/
theorem abrt_dies_by_signal (lim : Int) :
    dies_by_signal (run abrt_image lim demo_entry abort_input) :=
  (dies_by_signal_behavior_equiv _ _ (run_scfg_may_fail _ _ _ _)).1
    (abrt_dies_by_signal_scfg may_fail_cfg lim)

/-- Signal death fires the plain abort-family refutation at valid entries.
model: `strong_universal_error_free_T_abort_refuted_by_abort` with a real run witness.
-/
theorem abrt_refutes_error_free_abort :
    ¬ strong_universal_error_free_T_abort abrt_image abrt_image :=
  strong_universal_error_free_T_abort_refuted_by_abort _ _ _ _ _
    abrt_entry_valid abrt_entry_valid abort_input_valid (abrt_dies_by_signal _)

/-- Signal death also fires the configured abort-family refutation.
model: `strong_universal_error_free_T_scfg_abort_refuted_by_abort` with the same real image.
-/
theorem abrt_refutes_error_free_scfg_abort (cfg : SpuriousCfg) :
    ¬ strong_universal_error_free_T_scfg_abort cfg abrt_image abrt_image :=
  strong_universal_error_free_T_scfg_abort_refuted_by_abort cfg _ _ _ _ _
    abrt_entry_valid abrt_entry_valid abort_input_valid (abrt_dies_by_signal_scfg cfg _)

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.EquivalenceDefinition.Equivalence
