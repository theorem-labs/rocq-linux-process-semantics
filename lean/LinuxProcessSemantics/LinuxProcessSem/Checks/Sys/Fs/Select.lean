import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Select
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Fs.Select — pselect6 (72) and ppoll (73): checker, witness, frame

Mirrors `theories/LinuxProcessSem/Checks/Sys/Fs/Select.v` — the two
checkers and their eight soundness and completeness lemmas — and, in the
same file, `theories/LinuxProcessSem/Checks/Witness/Fs/Select.v` (the two
witnesses and their `*_witness_ok` lemmas) and the two per-checker frame
lemmas that `theories/LinuxProcessSem/Checks/VmMapsDisjoint.v` states for
`check_pselect6` and `check_ppoll`.  Not part of the trusted specification:
nothing here claims anything about Linux that `Sys/Fs/Select.lean` does not
already claim.  The definitions are the executable side of that spec and
the lemmas say the two sides agree, in both directions.  Its pins are
`Checks/Cases/Checks/Sys/Fs/Select.lean`.

WHY THREE ROCQ FILES MEET IN ONE LEAN FILE.  The port plan gives this
ticket one file and lists the witnesses among what it provides
(`tools/lean_port_brief.py C-Fs-Select`), and neither of the two tickets
that consume them claims a file for them: the VmMapsDisjoint twin
(ticket K4) takes each arm's `*_frame` lemma, from wherever the arm's
ticket put it, as one alternative of its `first` alternation, and the
witness prelude (ticket K5)
reaches each witness through the checked-arm table's arm block.  So the
witness twin and the frame twin are here, under the names their Rocq
originals carry.  This stops being the layout the day the Lean tree
gains a witness file of its own for this syscall, under a `Witness`
directory as Rocq's is: then the witness moves there.

WHAT THE CHECKER RESTS ON.  `pselect6_outcome` and `ppoll_outcome` are
total functions, and each spec is `input`, `get_model` and a match on the
outcome function, so the modeled band is deterministic: a given input and
model allow exactly one effect, or none.  That is why the checker can be
the spec's own computation and one comparison, with no decision of its
own, and why a `none` from the outcome function is `CheckUnmodeled`
before `eff` is looked at — the order the `*_sound_unmodeled` lemmas
state.  Which kernel steps make the band deterministic and which are
declined is argued in the header of `Sys/Fs/Select.lean`, not here.  The two kernel entry points the equality
is measured against, read at commit 1f99e9ab748f, are `pselect6`
(fs/select.c:793-803, Linux v6.18.46), which reads the {sigset, size}
pack through `get_sigset_argpack` (fs/select.c:774-791, Linux v6.18.46)
and hands it to `do_pselect` (fs/select.c:728-761, Linux v6.18.46) —
timeout, then mask, then `core_sys_select` (fs/select.c:621-698, Linux
v6.18.46), then `poll_select_finish` (fs/select.c:295-365, Linux
v6.18.46) — and `ppoll` (fs/select.c:1095-1117, Linux v6.18.46), which
does the same with `do_sys_poll` (fs/select.c:967-1039, Linux v6.18.46)
in the middle.  Both hand the mask to `set_user_sigmask`
(kernel/signal.c:3281-3297, Linux v6.18.46), which is where a
`sigsetsize` other than eight is refused before the set is read.  Which of those steps the spec answers and which
it declines is the spec's business and is pinned beside it; the checker
adds no decision of its own.

WHY THE INNER MATCH ON `eff` KEEPS ITS WILDCARD.  `Sys/Fs/Select.lean`'s
header explains that a definition whose body is a bare `match` with an
overlapping arm gets a conditional equation lemma per arm, which the
ground evaluator cannot apply.  `check_pselect6`'s body is a match on the
outcome function — no parameter of the definition — so Lean states one
unfolding equation for the whole body, and the nested match on `eff` is
then reduced by its matcher on a concrete effect, where overlap is
harmless.  `check_ppoll` is written the same way.  Rocq's checkers have the
same two-level shape and the same wildcard.

WHAT THE TABLE ROW WILL LOOK LIKE.  This file provides the five proof
fields and the witness a `CheckedArm` needs; the arm itself, its
`arm_unfold` lemmas and its `checked_table` row belong in the
checked-arm table (ticket K2), once it is in the tree.  Rocq has no
per-arm preservation lemma: `checked_table_preserves_vm` in
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v` proves
`Forall arm_preserves_vm checked_table` by rewriting each arm's `ca_check`
with `arm_unfold` and then taking, from a `first` alternation, the one
`*_frame` or `*_preserves` lemma that applies — for these two arms
`erewrite check_pselect6_frame by eassumption; exact Hwf` and its ppoll
twin.  The VmMapsDisjoint twin (ticket K4) owes the same alternation, and
the frame lemmas below are stated over the checker's own arguments, as
Rocq's are, so that the rewritten hypothesis matches them directly.  This
paragraph stops being true if K4 lands a per-arm lemma instead; then the
arm block owes it and this file does not.
-/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Select

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Select
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude

/-! ## pselect6 (72) -/

/-- pselect6 is deterministic throughout its modeled band — the header of
`Sys/Fs/Select.lean` says which kernel steps make it so and which are
declined — so the acceptor is the spec's own computation followed by one
comparison with the effect it is shown.  Mirrors `check_pselect6` in
`theories/LinuxProcessSem/Checks/Sys/Fs/Select.v`. -/
def check_pselect6 (i : SyscallInput) (n32 inp outp exp tsp sig : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match pselect6_outcome i m n32 inp outp exp tsp sig with
  | none => CheckUnmodeled
  | some (r, ws) =>
      match eff with
      | SyscallEffect.mkEffectU r' ws' [] [] [] [] =>
          if bv_eqb r' r && writes_eqb ws' ws then CheckOk m [] else CheckReject
      | _ => CheckReject

/-- Every `CheckOk` the checker returns is a run the spec admits: the
accepted effect is the spec's `mkEffect r ws []`, the model is unchanged
and no event is emitted. -/
theorem check_pselect6_sound_ok (i : SyscallInput) (n32 inp outp exp tsp sig : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_pselect6 i n32 inp outp exp tsp sig eff m = CheckOk m' evs) :
    pselect6_spec n32 inp outp exp tsp sig i m (Ok eff m' evs) := by
  unfold check_pselect6 at h
  unfold pselect6_spec
  apply bind_ok0 _ _ i m i m _ _ _ (input_ok i m)
  apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
  cases ho : pselect6_outcome i m n32 inp outp exp tsp sig with
  | none => rw [ho] at h; cases h
  | some p =>
    obtain ⟨r, ws⟩ := p
    rw [ho] at h
    dsimp only at h ⊢
    split at h
    · split at h
      · rename_i hg
        cases h
        rw [Bool.and_eq_true] at hg
        obtain ⟨hr, hw⟩ := hg
        rw [bv_eqb_eq] at hr
        rw [writes_eqb_eq] at hw
        subst hr
        subst hw
        exact pure_ok _ i m
      · cases h
    · cases h

/-- Every `CheckUnmodeled` the checker returns is a run the spec leaves
unmodeled: the checker declines only where `pselect6_outcome` is `none`,
and there the spec's third step is `unmodeled`. -/
theorem check_pselect6_sound_unmodeled (i : SyscallInput) (n32 inp outp exp tsp sig : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_pselect6 i n32 inp outp exp tsp sig eff m = CheckUnmodeled) :
    pselect6_spec n32 inp outp exp tsp sig i m Unmodeled := by
  unfold check_pselect6 at h
  unfold pselect6_spec
  apply bind_unmodeled2 _ _ i m i m [] (input_ok i m)
  apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
  cases ho : pselect6_outcome i m n32 inp outp exp tsp sig with
  | none =>
    dsimp only
    exact unmodeled_intro i m
  | some p =>
    obtain ⟨r, ws⟩ := p
    rw [ho] at h
    dsimp only at h
    split at h
    · split at h <;> cases h
    · cases h

/-- Every run the spec admits is one the checker accepts, with the same
model and the same (empty) event list. -/
theorem check_pselect6_complete_ok (i : SyscallInput) (n32 inp outp exp tsp sig : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : pselect6_spec n32 inp outp exp tsp sig i m (Ok eff m' evs)) :
    check_pselect6 i n32 inp outp exp tsp sig eff m = CheckOk m' evs := by
  unfold pselect6_spec at h
  have h := bind_input_model_inv _ i m _ h
  unfold check_pselect6
  cases ho : pselect6_outcome i m n32 inp outp exp tsp sig with
  | none =>
    rw [ho] at h
    dsimp only at h
    simp only [Monad.unmodeled] at h
    cases h
  | some p =>
    obtain ⟨r, ws⟩ := p
    rw [ho] at h
    dsimp only at h
    simp only [Monad.pure, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    dsimp only
    rw [bv_eqb_refl, (writes_eqb_eq ws ws).mpr rfl]
    rfl

/-- Every run the spec leaves unmodeled is one the checker declines,
whatever effect it is shown. -/
theorem check_pselect6_complete_unmodeled (i : SyscallInput) (n32 inp outp exp tsp sig : word)
    (eff : SyscallEffect) (m : Model)
    (h : pselect6_spec n32 inp outp exp tsp sig i m Unmodeled) :
    check_pselect6 i n32 inp outp exp tsp sig eff m = CheckUnmodeled := by
  unfold pselect6_spec at h
  have h := bind_input_model_inv _ i m _ h
  unfold check_pselect6
  cases ho : pselect6_outcome i m n32 inp outp exp tsp sig with
  | none => rfl
  | some p =>
    obtain ⟨r, ws⟩ := p
    rw [ho] at h
    dsimp only at h
    simp only [Monad.pure] at h
    cases h

/-- The one effect the spec admits for pselect6 on this input and model, or
`Unmodeled` where it admits none.  Mirrors `pselect6_witness` in
`theories/LinuxProcessSem/Checks/Witness/Fs/Select.v`; the argument order
— input and model first — is the dispatcher's, so a table row can apply
it to `i m` and then to the narrowed arguments. -/
def pselect6_witness (i : SyscallInput) (m : Model) (n32 inp outp exp tsp sig : word) :
    outcome SyscallEffect :=
  match pselect6_outcome i m n32 inp outp exp tsp sig with
  | none => Unmodeled
  | some (r, ws) => Ok (mkEffect r ws []) m []

/-- The witness is a run of the spec: the spec is receptive on every
input and model. -/
theorem pselect6_witness_ok (n32 inp outp exp tsp sig : word) (i : SyscallInput) (m : Model) :
    pselect6_spec n32 inp outp exp tsp sig i m (pselect6_witness i m n32 inp outp exp tsp sig) := by
  unfold pselect6_spec pselect6_witness
  cases ho : pselect6_outcome i m n32 inp outp exp tsp sig with
  | none =>
    apply bind_unmodeled2 _ _ i m i m [] (input_ok i m)
    apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
    rw [ho]
    exact unmodeled_intro i m
  | some p =>
    obtain ⟨r, ws⟩ := p
    apply bind_ok0 _ _ i m i m _ m [] (input_ok i m)
    apply bind_ok0 _ _ i m m m _ m [] (get_model_ok i m)
    rw [ho]
    exact pure_ok _ i m

/-- pselect6 accepts only with the model it was given, so the mapping
ledger is untouched.  Mirrors `check_pselect6_frame` in
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`, whose proof is the
`vm_frame2` loop; the steps are written out here because the Lean tree has
no `vm_frame2` yet — the VmMapsDisjoint twin (ticket K4) is where one
would live, and this file could not import it. -/
theorem check_pselect6_frame (i : SyscallInput) (n32 inp outp exp tsp sig : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_pselect6 i n32 inp outp exp tsp sig eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_pselect6 at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h; rfl
      · cases h
    · cases h

/-! ## ppoll (73) -/

/-- ppoll is deterministic throughout its modeled band as pselect6 is, and
the acceptor has the same shape over `ppoll_outcome`.  Mirrors
`check_ppoll` in `theories/LinuxProcessSem/Checks/Sys/Fs/Select.v`. -/
def check_ppoll (i : SyscallInput) (ufds nfds tsp sig sigsetsize : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match ppoll_outcome i m ufds nfds tsp sig sigsetsize with
  | none => CheckUnmodeled
  | some (r, ws) =>
      match eff with
      | SyscallEffect.mkEffectU r' ws' [] [] [] [] =>
          if bv_eqb r' r && writes_eqb ws' ws then CheckOk m [] else CheckReject
      | _ => CheckReject

/-- Every `CheckOk` the checker returns is a run the spec admits. -/
theorem check_ppoll_sound_ok (i : SyscallInput) (ufds nfds tsp sig sigsetsize : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckOk m' evs) :
    ppoll_spec ufds nfds tsp sig sigsetsize i m (Ok eff m' evs) := by
  unfold check_ppoll at h
  unfold ppoll_spec
  apply bind_ok0 _ _ i m i m _ _ _ (input_ok i m)
  apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
  cases ho : ppoll_outcome i m ufds nfds tsp sig sigsetsize with
  | none => rw [ho] at h; cases h
  | some p =>
    obtain ⟨r, ws⟩ := p
    rw [ho] at h
    dsimp only at h ⊢
    split at h
    · split at h
      · rename_i hg
        cases h
        rw [Bool.and_eq_true] at hg
        obtain ⟨hr, hw⟩ := hg
        rw [bv_eqb_eq] at hr
        rw [writes_eqb_eq] at hw
        subst hr
        subst hw
        exact pure_ok _ i m
      · cases h
    · cases h

/-- Every `CheckUnmodeled` the checker returns is a run the spec leaves
unmodeled. -/
theorem check_ppoll_sound_unmodeled (i : SyscallInput) (ufds nfds tsp sig sigsetsize : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckUnmodeled) :
    ppoll_spec ufds nfds tsp sig sigsetsize i m Unmodeled := by
  unfold check_ppoll at h
  unfold ppoll_spec
  apply bind_unmodeled2 _ _ i m i m [] (input_ok i m)
  apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
  cases ho : ppoll_outcome i m ufds nfds tsp sig sigsetsize with
  | none =>
    dsimp only
    exact unmodeled_intro i m
  | some p =>
    obtain ⟨r, ws⟩ := p
    rw [ho] at h
    dsimp only at h
    split at h
    · split at h <;> cases h
    · cases h

/-- Every run the spec admits is one the checker accepts. -/
theorem check_ppoll_complete_ok (i : SyscallInput) (ufds nfds tsp sig sigsetsize : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : ppoll_spec ufds nfds tsp sig sigsetsize i m (Ok eff m' evs)) :
    check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckOk m' evs := by
  unfold ppoll_spec at h
  have h := bind_input_model_inv _ i m _ h
  unfold check_ppoll
  cases ho : ppoll_outcome i m ufds nfds tsp sig sigsetsize with
  | none =>
    rw [ho] at h
    dsimp only at h
    simp only [Monad.unmodeled] at h
    cases h
  | some p =>
    obtain ⟨r, ws⟩ := p
    rw [ho] at h
    dsimp only at h
    simp only [Monad.pure, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    dsimp only
    rw [bv_eqb_refl, (writes_eqb_eq ws ws).mpr rfl]
    rfl

/-- Every run the spec leaves unmodeled is one the checker declines,
whatever effect it is shown. -/
theorem check_ppoll_complete_unmodeled (i : SyscallInput) (ufds nfds tsp sig sigsetsize : word)
    (eff : SyscallEffect) (m : Model)
    (h : ppoll_spec ufds nfds tsp sig sigsetsize i m Unmodeled) :
    check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckUnmodeled := by
  unfold ppoll_spec at h
  have h := bind_input_model_inv _ i m _ h
  unfold check_ppoll
  cases ho : ppoll_outcome i m ufds nfds tsp sig sigsetsize with
  | none => rfl
  | some p =>
    obtain ⟨r, ws⟩ := p
    rw [ho] at h
    dsimp only at h
    simp only [Monad.pure] at h
    cases h

/-- The one effect the spec admits for ppoll on this input and model, or
`Unmodeled` where it admits none.  Mirrors `ppoll_witness` in
`theories/LinuxProcessSem/Checks/Witness/Fs/Select.v`. -/
def ppoll_witness (i : SyscallInput) (m : Model) (ufds nfds tsp sig sigsetsize : word) :
    outcome SyscallEffect :=
  match ppoll_outcome i m ufds nfds tsp sig sigsetsize with
  | none => Unmodeled
  | some (r, ws) => Ok (mkEffect r ws []) m []

/-- The witness is a run of the spec. -/
theorem ppoll_witness_ok (ufds nfds tsp sig sigsetsize : word) (i : SyscallInput) (m : Model) :
    ppoll_spec ufds nfds tsp sig sigsetsize i m (ppoll_witness i m ufds nfds tsp sig sigsetsize) := by
  unfold ppoll_spec ppoll_witness
  cases ho : ppoll_outcome i m ufds nfds tsp sig sigsetsize with
  | none =>
    apply bind_unmodeled2 _ _ i m i m [] (input_ok i m)
    apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
    rw [ho]
    exact unmodeled_intro i m
  | some p =>
    obtain ⟨r, ws⟩ := p
    apply bind_ok0 _ _ i m i m _ m [] (input_ok i m)
    apply bind_ok0 _ _ i m m m _ m [] (get_model_ok i m)
    rw [ho]
    exact pure_ok _ i m

/-- ppoll accepts only with the model it was given.  Mirrors
`check_ppoll_frame` in `theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`. -/
theorem check_ppoll_frame (i : SyscallInput) (ufds nfds tsp sig sigsetsize : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_ppoll i ufds nfds tsp sig sigsetsize eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_ppoll at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h; rfl
      · cases h
    · cases h

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Select
