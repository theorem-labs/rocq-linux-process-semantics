import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! The baseline is the squash of the 2026-09-11 work, where the two Rocq
Mprotect files under `Checks/` are byte-identical to `f44244ad6b80`, the
commit the ticket names and this port was read at; a twin's baseline has to
be an ancestor of its branch, which `f44244ad` stopped being when that
day's work was rebase-merged.  `Checks/Sys/Dispatch.lean`'s header carries
the argument. -/

/-! # LinuxProcessSem.Checks.Sys.Mm.Mprotect — mprotect (226): checker and witness

Mirrors `theories/LinuxProcessSem/Checks/Sys/Mm/Mprotect.v` — `check_mprotect`
and its four soundness and completeness lemmas — and, in the same file,
`theories/LinuxProcessSem/Checks/Witness/Mm/Mprotect.v` (`mprotect_witness`
and `mprotect_witness_ok`).  Not part of the trusted specification: `Sys/Mm/Mprotect.lean` is the model,
and every theorem here relates an executable function to it.

WHY TWO ROCQ FILES MEET IN ONE LEAN FILE.  Rocq splits by role: the
checker in a file `Checks/ExecutableSpecs.v` re-exports, the witness in one
`Checks/Progress.v` re-exports.  The Lean tree keeps one file per syscall
because the `CheckedArm` a registration builds wants both at once — the
checker, the witness and the proofs below are the fields of one record —
and because the witness half is a few lines that would otherwise sit
alone in a file whose header is longer than its content.  The pins over
this file are in `Checks/Cases/Checks/Sys/Mm/Mprotect.lean`, where every
pin in this tree lives.

WHAT IS NOT HERE, AND WHOSE IT IS.  Rocq builds `arm_mprotect` and lists it
in `checked_table` (`Checks/Sys/Dispatch.v`), registers the `arm_unfold`
equations, and proves `check_mprotect_preserves` in
`Checks/VmMapsDisjoint.v`.  In the Lean port those are the registration
step of the conformance ticket for this arm, not this file's (BRIEF.md
section 5, the CHECK and VERIFY blocks): the checker lands on the
preludes and the spec alone, and the checked table's row and the ledger's
per-arm alternative are written when the arm is registered.

The frame lemma is the one piece of that step this file CAN carry, and
does, in the shape it can be stated in.  Rocq's `check_mprotect_preserves`
is `vm_wf (m_vmmaps m) → vm_wf (m_vmmaps m')`, and `vm_wf` is the K4
ledger module's — the twin of `Checks/VmMapsDisjoint.v`, landed in #1054,
which this branch's base predates — so the Rocq-shaped lemma is not
statable on it, and the ledger frame every sibling checker states
(`m_vmmaps m' = m_vmmaps m` on every `CheckOk`, the shape K4's
`arm_preserves_of_frame` consumes) is false on the exposure arm, whose
accepted model moves a range out of `vm_noaccess`, a field of that
ledger.  What Rocq's proof turns on is one projection: an accepting run
leaves `vm_maps` as it was (`rewrite vmm_mprotect_next; cbn [vm_maps]`).
That is `check_mprotect_vm_maps` below, and the registration's
`_preserves` is one
rewrite of it where the two meet: K4's per-arm file takes a
`check_<name>_preserves` directly, which is this lemma under `vm_wf`'s
unfolding.

THE ORDER OF THE GATES IS THE KERNEL'S.  `do_mprotect_pkey` (`mm/mprotect.c`,
Linux v6.18.46) refuses a `prot` carrying both `PROT_GROWSDOWN` and
`PROT_GROWSUP` with -EINVAL, then an unaligned `start` with -EINVAL, then
returns 0 for a zero `len` before anything else is looked at, then
page-aligns `len` and refuses a wrapped end with -ENOMEM — all before it
takes the mmap lock or looks at a VMA.  The checker asks the same four
questions in the same order, each closed by `check_ret_only`, and only then
asks whether `prot` is in the band the model covers.  Which arm a call then
lands in is a property of the ledger — `vm_noaccess` and `vm_maps` — and is
decided before the effect is inspected, so a call the model does not cover
is `CheckUnmodeled` whatever effect it was shown. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mprotect

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! ## Splitting the wrap gate

The wrap gate compares `two_pow_64` with `bv_unsigned addr + page_round_up_Z
(bv_unsigned len)`, and a tactic that has to reduce a term whose HEAD is
that `if` — the spec applied to its arguments once the three gates before
it are gone — evaluates the gate's `Decidable` instance with the
elaborator's `whnf`.  On a symbolic `len` that reduction does not stop at
the `Int` operations: it appears to run through `Nat`'s unary recursion,
and dies of `maxRecDepth` before it is done.  What is measured is the
failure, not that mechanism: `by_cases`, `split`, `refine` and `apply` on such a goal all
fail the same way, generalizing `two_pow_64` alone does not help, and
generalizing the sum to a variable does.  A term whose head is `Eq` is
never reduced that way, which is why the completeness lemmas, whose goal
is an equation on the checker, split the gate with `by_cases` as it
stands.  The soundness lemmas and the witness lemma,
whose goal is the spec, `generalize` the sum first, and the gate then
splits like any other. -/

/-! ## mprotect (226) -/

/-- The executable acceptor for `mprotect_spec`.  Mirrors `check_mprotect` in
`theories/LinuxProcessSem/Checks/Sys/Mm/Mprotect.v`.

Why the exposure arm reads the effect the way it does: a kernel that
answered an errno touched no page, so an errno beside a zero-fill is a
lie; a kernel that answered 0 exposed exactly the rounded range, so the
zero-fill has to be that range and no other, and has to fit the backing
budget the spec's `choose` asks for (`mprotect_budget_ok`). -/
def check_mprotect (addr len prot : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if mprotect_grows_conflict_b prot then check_ret_only eff (errno_ret EINVAL) m []
  else if !(bv_unsigned addr % page_size == 0) then check_ret_only eff (errno_ret EINVAL) m []
  else if w_is0 len then check_ret_only eff (Z_to_bv 64 0) m []
  else if two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len) then
    check_ret_only eff (errno_ret ENOMEM) m []
  else if !(mprotect_modeled_b prot) then CheckUnmodeled
  else
    let h := m_vmmaps m
    let nZ := page_round_up_Z (bv_unsigned len)
    let n := Z_to_bv 64 nZ
    if map_contains h.vm_noaccess addr n && map_contains h.vm_maps addr n then
      match eff with
      | SyscallEffect.mkEffectU r [] zs [] [] [] =>
          if errno_ret_in mprotect_errnos r then
            (match zs with
             | [] => CheckOk m []
             | _ => CheckReject)
          else if mprotect_budget_ok m addr n && w_is0 r && listNN_eqb zs [(addr, n)] then
            CheckOk (mprotect_model_next m addr n) []
          else CheckReject
      | _ => CheckReject
    else if map_contains h.vm_maps addr n && region_free h.vm_noaccess addr n then
      match eff with
      | SyscallEffect.mkEffectU r [] [] [] [] [] =>
          if w_is0 r then CheckOk m [] else CheckReject
      | _ => CheckReject
    else CheckUnmodeled

/-- Every `CheckOk` the checker returns is a run the spec admits.  Rocq:
`check_mprotect_sound_ok`. -/
theorem check_mprotect_sound_ok (addr len prot : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_mprotect addr len prot eff m = CheckOk m' evs) :
    mprotect_spec addr len prot i m (Ok eff m' evs) := by
  unfold check_mprotect at h
  unfold mprotect_spec
  generalize bv_unsigned addr + page_round_up_Z (bv_unsigned len) = X at h ⊢
  split at h
  · rename_i hg
    rw [ite_eq_left hg]
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  rename_i hg1
  rw [ite_eq_right hg1]
  split at h
  · rename_i hg
    rw [ite_eq_left hg]
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  rename_i hg2
  rw [ite_eq_right hg2]
  split at h
  · rename_i hg
    rw [ite_eq_left hg]
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  rename_i hg3
  rw [ite_eq_right hg3]
  by_cases hg4 : two_pow_64 ≤ X
  · rw [ite_eq_left hg4] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  rw [ite_eq_right hg4] at h ⊢
  cases hp : mprotect_modeled_b prot
  · rw [hp] at h
    rw [Bool.not_false, ite_eq_left rfl] at h
    cases h
  · rw [hp] at h
    rw [Bool.not_true, ite_eq_right Bool.false_ne_true] at h
    rw [ite_eq_left rfl]
    apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
    dsimp only at h ⊢
    split at h
    · rename_i hc
      rw [ite_eq_left hc]
      split at h
      · rename_i r zs
        split at h
        · rename_i he
          split at h
          · obtain ⟨e, hin, rfl⟩ := (errno_ret_in_true _ _).mp he
            cases h
            apply alt_l
            apply bind_ok0 _ _ i _ e _ _ _ _ (choose_ok _ e i _ hin)
            exact pure_ok _ i _
          · cases h
        · split at h
          · rename_i hC
            rw [Bool.and_eq_true, Bool.and_eq_true] at hC
            obtain ⟨⟨hbud, hr⟩, hz⟩ := hC
            rw [w_is0, bv_eqb_eq] at hr
            rw [listNN_eqb_eq] at hz
            subst hr hz
            cases h
            apply alt_r
            apply bind_ok0 _ _ i _ () _ _ _ _
            · exact choose_ok _ () i _ hbud
            apply bind_ok0 _ _ i _ () _ _ _ _ (modify_ok _ i _)
            exact pure_ok _ i _
          · cases h
      · cases h
    · rename_i hc
      rw [ite_eq_right hc]
      split at h
      · rename_i hr
        rw [ite_eq_left hr]
        split at h
        · rename_i r
          split at h
          · rename_i h0
            rw [w_is0, bv_eqb_eq] at h0
            subst h0
            cases h
            exact pure_ok _ i _
          · cases h
        · cases h
      · cases h

/-- Every `CheckUnmodeled` the checker returns is a run the spec leaves
unmodeled.  Rocq: `check_mprotect_sound_unmodeled`. -/
theorem check_mprotect_sound_unmodeled (addr len prot : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_mprotect addr len prot eff m = CheckUnmodeled) :
    mprotect_spec addr len prot i m Unmodeled := by
  unfold check_mprotect at h
  unfold mprotect_spec
  generalize bv_unsigned addr + page_round_up_Z (bv_unsigned len) = X at h ⊢
  split at h
  · exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  rename_i hg1
  rw [ite_eq_right hg1]
  split at h
  · exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  rename_i hg2
  rw [ite_eq_right hg2]
  split at h
  · exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  rename_i hg3
  rw [ite_eq_right hg3]
  by_cases hg4 : two_pow_64 ≤ X
  · rw [ite_eq_left hg4] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  rw [ite_eq_right hg4] at h ⊢
  cases hp : mprotect_modeled_b prot
  · rw [hp] at h
    rw [ite_eq_right Bool.false_ne_true]
    exact unmodeled_intro i m
  · rw [hp] at h
    rw [Bool.not_true, ite_eq_right Bool.false_ne_true] at h
    rw [ite_eq_left rfl]
    apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
    dsimp only at h ⊢
    split at h
    · exfalso
      split at h
      · split at h
        · split at h <;> cases h
        · split at h <;> cases h
      · cases h
    · rename_i hc
      rw [ite_eq_right hc]
      split at h
      · exfalso
        split at h
        · split at h <;> cases h
        · cases h
      · rename_i hr
        rw [ite_eq_right hr]
        exact unmodeled_intro i m

/-- Every run the spec admits is one the checker accepts, with the same
model and the same (empty) event list.  Rocq: `check_mprotect_complete_ok`. -/
theorem check_mprotect_complete_ok (addr len prot : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : mprotect_spec addr len prot i m (Ok eff m' evs)) :
    check_mprotect addr len prot eff m = CheckOk m' evs := by
  unfold mprotect_spec at h
  unfold check_mprotect
  split at h
  · rename_i hg
    rw [ite_eq_left hg]
    have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  rename_i hg1
  rw [ite_eq_right hg1]
  split at h
  · rename_i hg
    rw [ite_eq_left hg]
    have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  rename_i hg2
  rw [ite_eq_right hg2]
  split at h
  · rename_i hg
    rw [ite_eq_left hg]
    have h' : Ok eff m' evs = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := h
    cases h'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  rename_i hg3
  rw [ite_eq_right hg3]
  by_cases hg4 : two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)
  · rw [ite_eq_left hg4] at h ⊢
    have h' : Ok eff m' evs = Ok (mkEffect (errno_ret ENOMEM) [] []) m [] := h
    cases h'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  rw [ite_eq_right hg4] at h ⊢
  cases hp : mprotect_modeled_b prot
  · rw [hp] at h
    rw [ite_eq_right Bool.false_ne_true] at h
    have h' : Ok eff m' evs = Unmodeled := h
    cases h'
  · rw [hp] at h
    rw [ite_eq_left rfl] at h
    rw [Bool.not_true, ite_eq_right Bool.false_ne_true]
    have h := (bind_get_model_iff _ i m _).mp h
    dsimp only at h ⊢
    split at h
    · rename_i hc
      rw [ite_eq_left hc]
      rcases (alt_iff _ _ i m _).mp h with h | h
      · obtain ⟨e, hin, he⟩ := (bind_choose_iff _ _ i m _).mp h
        have he' : Ok eff m' evs
            = Ok (SyscallEffect.mkEffectU (errno_ret e) [] [] [] [] []) m [] := he
        cases he'
        dsimp only
        rw [ite_eq_left (errno_ret_in_intro _ _ hin)]
      · obtain ⟨_, hbud, h⟩ := (bind_choose_iff _ _ i m _).mp h
        have h := (bind_modify_iff _ _ i m _).mp h
        have h' : Ok eff m' evs
            = Ok (SyscallEffect.mkEffectU (Z_to_bv 64 0) [] [(addr, _)] [] [] []) _ [] := h
        cases h'
        dsimp only
        have he0 : errno_ret_in mprotect_errnos (Z_to_bv 64 0) = false := by decide
        rw [he0, ite_eq_right Bool.false_ne_true, ite_eq_left]
        rw [Bool.and_eq_true, Bool.and_eq_true]
        exact ⟨⟨hbud, bv_eqb_refl _⟩, (listNN_eqb_eq _ _).mpr rfl⟩
    · rename_i hc
      rw [ite_eq_right hc]
      split at h
      · rename_i hr
        rw [ite_eq_left hr]
        have h' : Ok eff m' evs
            = Ok (SyscallEffect.mkEffectU (Z_to_bv 64 0) [] [] [] [] []) m [] := h
        cases h'
        dsimp only
        have h0 : w_is0 (Z_to_bv 64 0) = true := bv_eqb_refl _
        rw [ite_eq_left h0]
      · have h' : Ok eff m' evs = Unmodeled := h
        cases h'

/-- Every run the spec leaves unmodeled is one the checker declines,
whatever effect it is shown.  Rocq: `check_mprotect_complete_unmodeled`. -/
theorem check_mprotect_complete_unmodeled (addr len prot : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect) (h : mprotect_spec addr len prot i m Unmodeled) :
    check_mprotect addr len prot eff m = CheckUnmodeled := by
  unfold mprotect_spec at h
  unfold check_mprotect
  split at h
  · have h' : (Unmodeled : outcome SyscallEffect)
        = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'
  rename_i hg1
  rw [ite_eq_right hg1]
  split at h
  · have h' : (Unmodeled : outcome SyscallEffect)
        = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'
  rename_i hg2
  rw [ite_eq_right hg2]
  split at h
  · have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := h
    cases h'
  rename_i hg3
  rw [ite_eq_right hg3]
  by_cases hg4 : two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len)
  · rw [ite_eq_left hg4] at h
    have h' : (Unmodeled : outcome SyscallEffect)
        = Ok (mkEffect (errno_ret ENOMEM) [] []) m [] := h
    cases h'
  rw [ite_eq_right hg4] at h ⊢
  cases hp : mprotect_modeled_b prot
  · rw [hp] at h
    rw [Bool.not_false, ite_eq_left rfl]
  · rw [hp] at h
    rw [ite_eq_left rfl] at h
    rw [Bool.not_true, ite_eq_right Bool.false_ne_true]
    have h := (bind_get_model_iff _ i m _).mp h
    dsimp only at h ⊢
    split at h
    · exfalso
      rcases (alt_iff _ _ i m _).mp h with h | h
      · obtain ⟨e, _, he⟩ := (bind_choose_iff _ _ i m _).mp h
        have he' : (Unmodeled : outcome SyscallEffect)
            = Ok (mkEffect (errno_ret e) [] []) m [] := he
        cases he'
      · obtain ⟨_, _, h⟩ := (bind_choose_iff _ _ i m _).mp h
        have h := (bind_modify_iff _ _ i m _).mp h
        have h' : (Unmodeled : outcome SyscallEffect) = Ok _ _ [] := h
        cases h'
    · rename_i hc
      rw [ite_eq_right hc]
      split at h
      · have h' : (Unmodeled : outcome SyscallEffect)
            = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := h
        cases h'
      · rename_i hr
        rw [ite_eq_right hr]

/-- Every `CheckOk` the checker returns keeps `vm_maps`: the exposure arm's
`mprotect_model_next` rebuilds the ledger with `vm_maps` unchanged and a
range moved out of `vm_noaccess`, and every other accepting arm returns
the model it was given.  The projection Rocq's `check_mprotect_preserves`
(`Checks/VmMapsDisjoint.v`) rests on, stated here because `vm_wf` is not;
see the header. -/
theorem check_mprotect_vm_maps (addr len prot : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : check_mprotect addr len prot eff m = CheckOk m' evs) :
    (m_vmmaps m').vm_maps = (m_vmmaps m).vm_maps := by
  unfold check_mprotect at h
  generalize bv_unsigned addr + page_round_up_Z (bv_unsigned len) = X at h
  split at h
  · obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl
  split at h
  · obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl
  split at h
  · obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl
  by_cases hg4 : two_pow_64 ≤ X
  · rw [ite_eq_left hg4] at h
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl
  rw [ite_eq_right hg4] at h
  cases hp : mprotect_modeled_b prot
  · rw [hp] at h
    rw [Bool.not_false, ite_eq_left rfl] at h
    cases h
  · rw [hp] at h
    rw [Bool.not_true, ite_eq_right Bool.false_ne_true] at h
    dsimp only at h
    split at h
    · split at h
      · split at h
        · split at h
          · cases h
            rfl
          · cases h
        · split at h
          · cases h
            rfl
          · cases h
      · cases h
    · split at h
      · split at h
        · split at h
          · cases h
            rfl
          · cases h
        · cases h
      · cases h

/-! ## The witness -/

/-- One outcome `mprotect_spec` admits on every input and model, or
`Unmodeled` where it admits none.  Mirrors `mprotect_witness` in
`theories/LinuxProcessSem/Checks/Witness/Mm/Mprotect.v`: the exposure arm
fails with `witness_errno`, the head of `mprotect_errnos`, which is what
lets `errno_head_witness` discharge the `choose`. -/
def mprotect_witness (addr len prot : word) (m : Model) : outcome SyscallEffect :=
  if mprotect_grows_conflict_b prot then ret_outcome (errno_ret EINVAL) m
  else if !(bv_unsigned addr % page_size == 0) then ret_outcome (errno_ret EINVAL) m
  else if w_is0 len then ret_outcome (Z_to_bv 64 0) m
  else if two_pow_64 ≤ bv_unsigned addr + page_round_up_Z (bv_unsigned len) then
    ret_outcome (errno_ret ENOMEM) m
  else if mprotect_modeled_b prot then
    let h := m_vmmaps m
    let nZ := page_round_up_Z (bv_unsigned len)
    let n := Z_to_bv 64 nZ
    if map_contains h.vm_noaccess addr n && map_contains h.vm_maps addr n then
      ret_outcome (errno_ret witness_errno) m
    else if map_contains h.vm_maps addr n && region_free h.vm_noaccess addr n then
      ret_outcome (Z_to_bv 64 0) m
    else Unmodeled
  else Unmodeled

/-- The witness is a run of the spec: `mprotect_spec` is receptive on every
input and model.  Rocq: `mprotect_witness_ok`. -/
theorem mprotect_witness_ok (addr len prot : word) (i : SyscallInput) (m : Model) :
    mprotect_spec addr len prot i m (mprotect_witness addr len prot m) := by
  unfold mprotect_spec mprotect_witness
  generalize bv_unsigned addr + page_round_up_Z (bv_unsigned len) = X
  split
  · exact pure_ok _ i m
  split
  · exact pure_ok _ i m
  split
  · exact pure_ok _ i m
  by_cases hg4 : two_pow_64 ≤ X
  · rw [ite_eq_left hg4, ite_eq_left hg4]
    exact pure_ok _ i m
  rw [ite_eq_right hg4, ite_eq_right hg4]
  split
  · apply bind_step _ _ i m m m _ (get_model_ok i m)
    dsimp only
    split
    · apply alt_l
      apply bind_step _ _ i m ENOMEM m _ (errno_head_witness _ _ i m)
      exact pure_ok _ i m
    split
    · exact pure_ok _ i m
    · exact unmodeled_intro i m
  · exact unmodeled_intro i m

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mprotect
