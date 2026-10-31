import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Groups

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Kernel.Groups — the getgroups (158) and setgroups (159) checkers and witnesses, and their proofs

Mirrors `theories/LinuxProcessSem/Checks/Sys/Kernel/Groups.v` (the two
executable checkers and their soundness and completeness proofs) and
`theories/LinuxProcessSem/Checks/Witness/Kernel/Groups.v` (the two
receptiveness witnesses and their proofs), in that order, as two sections
of one module.  Both answer to Linux `kernel/groups.c`: this file holds
the checkers and witnesses for the syscalls defined there, and no others.
The ticket that ports both, C-Kernel-Groups, names this one file, so the
witnesses live here rather than under a `Checks/Witness/` mirror path.
Not part of the trusted specification: the specs are
`Sys/Kernel/Groups.lean`'s, and every theorem here relates an executable
checker, or a witness, to one of them.

The Rocq checker file is split out of `Checks/ExecutableSpecs.v`, which
keeps the dispatcher and the four top-level theorems and re-exports it;
the Rocq witness file is split out of `Checks/Progress.v` the same way.

WHAT IS NOT HERE, AND WHOSE IT IS.  The arm each checker becomes — the
`CheckedArm` built from its four lemmas and its witness's `_ok`, the row
that carries its number in the checked table, the `arm_unfold` lemmas
that open it, and the alternative the VM-ledger invariant's alternation
takes for it — is the conformance ticket's registration step, not this
file's (BRIEF.md section 5, CHECK).  That split is what lets this file
build on the checkers' prelude and the spec alone, and a `lean: checks:`
PR carries none of those hunks.

The header's baseline is a71fd38a, the squash that landed the 2026-09-11
work on main; both Rocq files are byte-identical there to the port's
common baseline f44244ad, from which the brief quotes them, and to
24e9aa5d3, the `nightly/09-14-2026` tip this twin was written against on
2026-09-19.

WHAT A CHECKER HERE DECIDES.  `check_getgroups` is the spec's branch
structure, branch for branch, with the relational `ret_only r` replaced
by `check_ret_only eff r m []` — the executable test that the recorded
effect is exactly a return of `r` with no writes, no zero-fills and no
model change — and the spec's `unmodeled` replaced by `CheckUnmodeled`.
Nothing is decided here that the spec does not decide, and the
lemmas below say so in both directions: what the checker accepts the
spec admits (`*_sound_ok`), what the checker declines the spec declines
(`*_sound_unmodeled`), and conversely (`*_complete_ok`,
`*_complete_unmodeled`).  Read `Sys/Kernel/Groups.lean` for the kernel
order the branches are in and for why the `grouplist` pointer is not an
argument of either checker: on every branch a checker answers, the kernel
never dereferences it.

WHAT ELSE IS HERE.  The frame lemmas, Rocq's
`VmMapsDisjoint.check_getgroups_frame` and `check_setgroups_frame`: neither
checker moves `m_vmmaps`.  Rocq states them in
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`, beside the alternation
that consumes them, and the C ticket's acceptance text assigns them to the
registration step; this file states them anyway, because each depends on
nothing but its checker and one prelude lemma, and a lemma provable where
its subject is defined should not wait on a file that cannot import it
(in Rocq the alternation's file imports the table, which imports the
checkers; no Lean table or alternation exists at this head, and the V
ticket's registration, BRIEF.md section 5, is to import this file the
same way).  The
arm-level facts the alternation consumes are DERIVED from them at
registration, not re-proved.  They are the section before the witnesses.

THE WITNESSES spell their outcome out as `Ok (mkEffect r [] []) m []`,
which is what `ret_outcome r m` of `Checks/Witness/Prelude.v` unfolds to.
That prelude's twin is ticket K5's and is not in the tree, and this file
does not port its name (BRIEF.md section 12, NEEDS); folding the shorthand
in once it lands is a rewrite inside two definitions that moves no
statement, and that landing is the condition under which this paragraph
goes stale. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Groups

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Groups
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude

/-! ## getgroups (158) -/

/-- `getgroups` (158): the count, or one of the two -EINVALs, and
`CheckUnmodeled` on the writing path.  Mirrors
`Kernel.Groups.getgroups_spec` branch for branch — read that spec for the
kernel order the branches are in and why the `grouplist` pointer is not
an argument here either.  Rocq: `Checks.Sys.Kernel.Groups.check_getgroups`. -/
def check_getgroups (gidsetsize : word) (eff : SyscallEffect) (m : Model) : check_result :=
  let n := sint32 gidsetsize
  if n < 0 then check_ret_only eff (errno_ret EINVAL) m []
  else
    let ng : Int := ((m_creds m).cr_groups).length
    if NGROUPS_MAX < ng then CheckUnmodeled
    else if n = 0 then check_ret_only eff (Z_to_bv 64 ng) m []
    else if n < ng then check_ret_only eff (errno_ret EINVAL) m []
    else if ng = 0 then check_ret_only eff (Z_to_bv 64 0) m []
    else CheckUnmodeled

/-! ### The proofs, and why they start with `generalize`

Rocq's proofs case on `Z.ltb (sint32 gidsetsize) 0` directly.  The Lean
proofs first `generalize` the `sint32 gidsetsize` they all turn on into an
opaque `n : Int`, and case on `n`.  The reason is a limit of the
elaborator, not of the argument: `sint32 w` is `if u < 2^31 then u else
u - 2^32` over `u`, the low 32 bits of `w` read unsigned, and for a
SYMBOLIC `w` a `whnf` that has to decide `u < 2^31` — `by_cases` on
`sint32 w < 0`, `rcases` on `Decidable.em` of it, and the
`constructorNameAsVariable` linter's look at every hypothesis whose head
is such a decision — reduces `Int.decLt` on the literal `2147483648` one
unit at a time and hits the recursion limit; the same statement with a
small literal, or over `Nat`, is instant.  With
`n` opaque nothing has a decision on `sint32` left to reduce.  The two
`*_complete_*` lemmas below still STATE a hypothesis of that shape — the
spec applied, whose head is that decision — so that linter is switched off
for exactly those two declarations; the tactic-level `generalize` cannot
reach a binder of the statement. -/

/-- Rocq: `Checks.Sys.Kernel.Groups.check_getgroups_sound_ok`. -/
theorem check_getgroups_sound_ok (gidsetsize : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_getgroups gidsetsize eff m = CheckOk m' evs) :
    getgroups_spec gidsetsize i m (Ok eff m' evs) := by
  unfold check_getgroups at h
  unfold getgroups_spec
  dsimp only at h ⊢
  generalize sint32 gidsetsize = n at h ⊢
  by_cases hneg : n < 0
  · simp only [hneg, ↓reduceIte] at h ⊢
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact pure_ok _ i _
  · simp only [hneg, ↓reduceIte] at h ⊢
    rw [bind_get_model_iff]
    by_cases hmax : NGROUPS_MAX < (((m_creds m).cr_groups).length : Int)
    · exact absurd h (by simp only [hmax, ↓reduceIte, reduceCtorEq, not_false_eq_true])
    · simp only [hmax, ↓reduceIte] at h ⊢
      by_cases hzero : n = 0
      · simp only [hzero, ↓reduceIte] at h ⊢
        rw [check_ret_only_ok_iff] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact pure_ok _ i _
      · simp only [hzero, ↓reduceIte] at h ⊢
        by_cases hsmall : n < (((m_creds m).cr_groups).length : Int)
        · simp only [hsmall, ↓reduceIte] at h ⊢
          rw [check_ret_only_ok_iff] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact pure_ok _ i _
        · simp only [hsmall, ↓reduceIte] at h ⊢
          by_cases hempty : (((m_creds m).cr_groups).length : Int) = 0
          · simp only [hempty, ↓reduceIte] at h ⊢
            rw [check_ret_only_ok_iff] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact pure_ok _ i _
          · exact absurd h (by simp only [hempty, ↓reduceIte, reduceCtorEq, not_false_eq_true])

/-- Rocq: `Checks.Sys.Kernel.Groups.check_getgroups_sound_unmodeled`. -/
theorem check_getgroups_sound_unmodeled (gidsetsize : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_getgroups gidsetsize eff m = CheckUnmodeled) :
    getgroups_spec gidsetsize i m Unmodeled := by
  unfold check_getgroups at h
  unfold getgroups_spec
  dsimp only at h ⊢
  generalize sint32 gidsetsize = n at h ⊢
  by_cases hneg : n < 0
  · simp only [hneg, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  · simp only [hneg, ↓reduceIte] at h ⊢
    rw [bind_get_model_iff]
    by_cases hmax : NGROUPS_MAX < (((m_creds m).cr_groups).length : Int)
    · simp only [hmax, ↓reduceIte]
      exact unmodeled_intro i m
    · simp only [hmax, ↓reduceIte] at h ⊢
      by_cases hzero : n = 0
      · simp only [hzero, ↓reduceIte] at h
        exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
      · simp only [hzero, ↓reduceIte] at h ⊢
        by_cases hsmall : n < (((m_creds m).cr_groups).length : Int)
        · simp only [hsmall, ↓reduceIte] at h
          exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
        · simp only [hsmall, ↓reduceIte] at h ⊢
          by_cases hempty : (((m_creds m).cr_groups).length : Int) = 0
          · simp only [hempty, ↓reduceIte] at h
            exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
          · simp only [hempty, ↓reduceIte]
            exact unmodeled_intro i m

set_option linter.constructorNameAsVariable false in
/-- Rocq: `Checks.Sys.Kernel.Groups.check_getgroups_complete_ok`.  The
linter is off for the reason the section header gives: the hypothesis is
the spec applied, and the linter's `whnf` of it does not terminate. -/
theorem check_getgroups_complete_ok (gidsetsize : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : getgroups_spec gidsetsize i m (Ok eff m' evs)) :
    check_getgroups gidsetsize eff m = CheckOk m' evs := by
  unfold getgroups_spec at h
  unfold check_getgroups
  dsimp only at h ⊢
  generalize sint32 gidsetsize = n at h ⊢
  by_cases hneg : n < 0
  · simp only [hneg, ↓reduceIte] at h ⊢
    have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  · simp only [hneg, ↓reduceIte] at h ⊢
    rw [bind_get_model_iff] at h
    by_cases hmax : NGROUPS_MAX < (((m_creds m).cr_groups).length : Int)
    · simp only [hmax, ↓reduceIte] at h
      have h' : Ok eff m' evs = Unmodeled := h
      cases h'
    · simp only [hmax, ↓reduceIte] at h ⊢
      by_cases hzero : n = 0
      · simp only [hzero, ↓reduceIte] at h ⊢
        have h' : Ok eff m' evs
            = Ok (mkEffect (Z_to_bv 64 (((m_creds m).cr_groups).length : Int)) [] []) m [] := h
        cases h'
        exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
      · simp only [hzero, ↓reduceIte] at h ⊢
        by_cases hsmall : n < (((m_creds m).cr_groups).length : Int)
        · simp only [hsmall, ↓reduceIte] at h ⊢
          have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
          cases h'
          exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
        · simp only [hsmall, ↓reduceIte] at h ⊢
          by_cases hempty : (((m_creds m).cr_groups).length : Int) = 0
          · simp only [hempty, ↓reduceIte] at h ⊢
            have h' : Ok eff m' evs = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := h
            cases h'
            exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
          · simp only [hempty, ↓reduceIte] at h
            have h' : Ok eff m' evs = Unmodeled := h
            cases h'

set_option linter.constructorNameAsVariable false in
/-- Rocq: `Checks.Sys.Kernel.Groups.check_getgroups_complete_unmodeled`.
The linter is off for the reason the section header gives. -/
theorem check_getgroups_complete_unmodeled (gidsetsize : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (h : getgroups_spec gidsetsize i m Unmodeled) :
    check_getgroups gidsetsize eff m = CheckUnmodeled := by
  unfold getgroups_spec at h
  unfold check_getgroups
  dsimp only at h ⊢
  generalize sint32 gidsetsize = n at h ⊢
  by_cases hneg : n < 0
  · simp only [hneg, ↓reduceIte] at h
    have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'
  · simp only [hneg, ↓reduceIte] at h ⊢
    rw [bind_get_model_iff] at h
    by_cases hmax : NGROUPS_MAX < (((m_creds m).cr_groups).length : Int)
    · simp only [hmax, ↓reduceIte]
    · simp only [hmax, ↓reduceIte] at h ⊢
      by_cases hzero : n = 0
      · simp only [hzero, ↓reduceIte] at h
        have h' : (Unmodeled : outcome SyscallEffect)
            = Ok (mkEffect (Z_to_bv 64 (((m_creds m).cr_groups).length : Int)) [] []) m [] := h
        cases h'
      · simp only [hzero, ↓reduceIte] at h ⊢
        by_cases hsmall : n < (((m_creds m).cr_groups).length : Int)
        · simp only [hsmall, ↓reduceIte] at h
          have h' : (Unmodeled : outcome SyscallEffect)
              = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
          cases h'
        · simp only [hsmall, ↓reduceIte] at h ⊢
          by_cases hempty : (((m_creds m).cr_groups).length : Int) = 0
          · simp only [hempty, ↓reduceIte] at h
            have h' : (Unmodeled : outcome SyscallEffect)
                = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := h
            cases h'
          · simp only [hempty, ↓reduceIte]

/-! ## setgroups (159) -/

/-- `setgroups` (159): -EPERM for an unprivileged caller, `CheckUnmodeled`
for a privileged one.  `may_setgroups()` is the first test
`SYSCALL_DEFINE2(setgroups)` makes (kernel/groups.c, Linux v6.18.46), so an
unprivileged caller is answered -EPERM whatever its `gidsetsize` — the
`NGROUPS_MAX` test and the `groups_from_user` copy come after it and are
never reached; a privileged caller reaches them and the checker declines,
since the spec does.  Mirrors `Kernel.Groups.setgroups_spec`.  Rocq:
`Checks.Sys.Kernel.Groups.check_setgroups`. -/
def check_setgroups (eff : SyscallEffect) (m : Model) : check_result :=
  if creds_privileged (m_creds m) then CheckUnmodeled
  else check_ret_only eff (errno_ret EPERM) m []

/-- Rocq: `Checks.Sys.Kernel.Groups.check_setgroups_sound_ok`. -/
theorem check_setgroups_sound_ok (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (h : check_setgroups eff m = CheckOk m' evs) :
    setgroups_spec i m (Ok eff m' evs) := by
  unfold check_setgroups at h
  unfold setgroups_spec
  rw [bind_get_model_iff]
  cases hp : creds_privileged (m_creds m)
  · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h ⊢
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact pure_ok _ i _
  · exact absurd h (by simp only [hp, ↓reduceIte, reduceCtorEq, not_false_eq_true])

/-- Rocq: `Checks.Sys.Kernel.Groups.check_setgroups_sound_unmodeled`. -/
theorem check_setgroups_sound_unmodeled (eff : SyscallEffect) (m : Model) (i : SyscallInput)
    (h : check_setgroups eff m = CheckUnmodeled) :
    setgroups_spec i m Unmodeled := by
  unfold check_setgroups at h
  unfold setgroups_spec
  rw [bind_get_model_iff]
  cases hp : creds_privileged (m_creds m)
  · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  · simp only [↓reduceIte]
    exact unmodeled_intro i m

/-- Rocq: `Checks.Sys.Kernel.Groups.check_setgroups_complete_ok`. -/
theorem check_setgroups_complete_ok (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (h : setgroups_spec i m (Ok eff m' evs)) :
    check_setgroups eff m = CheckOk m' evs := by
  unfold setgroups_spec at h
  unfold check_setgroups
  rw [bind_get_model_iff] at h
  cases hp : creds_privileged (m_creds m)
  · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h ⊢
    have h' : Ok eff m' evs = Ok (mkEffect (errno_ret EPERM) [] []) m [] := h
    cases h'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  · simp only [hp, ↓reduceIte] at h
    have h' : Ok eff m' evs = Unmodeled := h
    cases h'

/-- Rocq: `Checks.Sys.Kernel.Groups.check_setgroups_complete_unmodeled`. -/
theorem check_setgroups_complete_unmodeled (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (h : setgroups_spec i m Unmodeled) :
    check_setgroups eff m = CheckUnmodeled := by
  unfold setgroups_spec at h
  unfold check_setgroups
  rw [bind_get_model_iff] at h
  cases hp : creds_privileged (m_creds m)
  · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
    have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (errno_ret EPERM) [] []) m [] := h
    cases h'
  · simp only [↓reduceIte]

/-! ## The frame lemmas

Rocq keeps every arm's frame lemma inside
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`, next to the alternation
that uses it; the header says why these two are here instead, and what
the registration step derives from them.

The argument is the trivial one: neither checker builds a model.  On every
accepting branch the result is `check_ret_only eff r m []`, which accepts
only with the model it was given (the middle conjunct of
`check_ret_only_ok_iff`), so `m_vmmaps m'` is `m_vmmaps m` by
substitution.  The `CheckUnmodeled` branches never reach a `CheckOk` and
are closed by the constructor mismatch. -/

/-- Rocq: `VmMapsDisjoint.check_getgroups_frame`. -/
theorem check_getgroups_frame (gidsetsize : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_getgroups gidsetsize eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_getgroups at h
  -- `generalize` first, for the reason the section above gives: a case
  -- split on the `sint32` decision of a symbolic word does not terminate,
  -- and one on an opaque `n` does.
  dsimp only at h
  generalize sint32 gidsetsize = n at h
  by_cases hneg : n < 0
  · simp only [hneg, ↓reduceIte] at h
    rw [check_ret_only_ok_iff] at h
    obtain ⟨-, rfl, -⟩ := h
    rfl
  · simp only [hneg, ↓reduceIte] at h
    by_cases hmax : NGROUPS_MAX < (((m_creds m).cr_groups).length : Int)
    · exact absurd h (by simp only [hmax, ↓reduceIte, reduceCtorEq, not_false_eq_true])
    · simp only [hmax, ↓reduceIte] at h
      by_cases hzero : n = 0
      · simp only [hzero, ↓reduceIte] at h
        rw [check_ret_only_ok_iff] at h
        obtain ⟨-, rfl, -⟩ := h
        rfl
      · simp only [hzero, ↓reduceIte] at h
        by_cases hsmall : n < (((m_creds m).cr_groups).length : Int)
        · simp only [hsmall, ↓reduceIte] at h
          rw [check_ret_only_ok_iff] at h
          obtain ⟨-, rfl, -⟩ := h
          rfl
        · simp only [hsmall, ↓reduceIte] at h
          by_cases hempty : (((m_creds m).cr_groups).length : Int) = 0
          · simp only [hempty, ↓reduceIte] at h
            rw [check_ret_only_ok_iff] at h
            obtain ⟨-, rfl, -⟩ := h
            rfl
          · exact absurd h (by simp only [hempty, ↓reduceIte, reduceCtorEq, not_false_eq_true])

/-- Rocq: `VmMapsDisjoint.check_setgroups_frame`. -/
theorem check_setgroups_frame (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_setgroups eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_setgroups at h
  cases hp : creds_privileged (m_creds m)
  · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
    rw [check_ret_only_ok_iff] at h
    obtain ⟨-, rfl, -⟩ := h
    rfl
  · exact absurd h (by simp only [hp, ↓reduceIte, reduceCtorEq, not_false_eq_true])

/-! ## The witnesses — `Checks/Witness/Kernel/Groups.v`

Mirrors `theories/LinuxProcessSem/Checks/Witness/Kernel/Groups.v`.  A
witness exhibits one admissible outcome for a spec in the matching `Sys`
module, which is what progress is proved from: the receptiveness field of
the arm the registration step builds is the `*_witness_ok` lemma below,
applied to the register the arm reads.

Both specs are deterministic on every branch — each branch is a `ret_only`
or an `unmodeled` — so each witness is the branch itself, and the
`*_witness_ok` proof is the spec's own case split.  Failing closed is an
admissible outcome, which is what makes progress hold on the branches that
decline: a witness of `Unmodeled` is a witness.  An answering branch's
outcome is written out, `Ok (mkEffect r [] []) m []`, for the reason the
header gives.

The `getgroups` proof opens with `generalize sint32 gidsetsize = n`, for
the reason the checker's section gives at length: a case split on a
decision over `sint32` of a symbolic word sends the elaborator's `whnf`
into an unbounded reduction, and an opaque `n` does not. -/

/-- `getgroups` (158) is deterministic on every branch, so the witness is
the branch itself: the count, an -EINVAL, or the `Unmodeled` the writing
path and the over-long-list guard both answer.  Rocq:
`Checks.Witness.Kernel.Groups.getgroups_witness`. -/
def getgroups_witness (gidsetsize : word) (m : Model) : outcome SyscallEffect :=
  let n := sint32 gidsetsize
  if n < 0 then Ok (mkEffect (errno_ret EINVAL) [] []) m []
  else
    let ng : Int := ((m_creds m).cr_groups).length
    if NGROUPS_MAX < ng then Unmodeled
    else if n = 0 then Ok (mkEffect (Z_to_bv 64 ng) [] []) m []
    else if n < ng then Ok (mkEffect (errno_ret EINVAL) [] []) m []
    else if ng = 0 then Ok (mkEffect (Z_to_bv 64 0) [] []) m []
    else Unmodeled

/-- Rocq: `Checks.Witness.Kernel.Groups.getgroups_witness_ok`. -/
theorem getgroups_witness_ok (gidsetsize : word) (i : SyscallInput) (m : Model) :
    getgroups_spec gidsetsize i m (getgroups_witness gidsetsize m) := by
  unfold getgroups_spec getgroups_witness
  dsimp only
  generalize sint32 gidsetsize = n
  by_cases hneg : n < 0
  · simp only [hneg, ↓reduceIte]
    exact pure_ok _ i _
  · simp only [hneg, ↓reduceIte]
    rw [bind_get_model_iff]
    by_cases hmax : NGROUPS_MAX < (((m_creds m).cr_groups).length : Int)
    · simp only [hmax, ↓reduceIte]
      exact unmodeled_intro i m
    · simp only [hmax, ↓reduceIte]
      by_cases hzero : n = 0
      · simp only [hzero, ↓reduceIte]
        exact pure_ok _ i _
      · simp only [hzero, ↓reduceIte]
        by_cases hsmall : n < (((m_creds m).cr_groups).length : Int)
        · simp only [hsmall, ↓reduceIte]
          exact pure_ok _ i _
        · simp only [hsmall, ↓reduceIte]
          by_cases hempty : (((m_creds m).cr_groups).length : Int) = 0
          · simp only [hempty, ↓reduceIte]
            exact pure_ok _ i _
          · simp only [hempty, ↓reduceIte]
            exact unmodeled_intro i m

/-- `setgroups` (159): -EPERM for the unprivileged caller, `Unmodeled`
for the privileged one the spec declines.  Rocq:
`Checks.Witness.Kernel.Groups.setgroups_witness`. -/
def setgroups_witness (m : Model) : outcome SyscallEffect :=
  if creds_privileged (m_creds m) then Unmodeled
  else Ok (mkEffect (errno_ret EPERM) [] []) m []

/-- Rocq: `Checks.Witness.Kernel.Groups.setgroups_witness_ok`. -/
theorem setgroups_witness_ok (i : SyscallInput) (m : Model) :
    setgroups_spec i m (setgroups_witness m) := by
  unfold setgroups_spec setgroups_witness
  rw [bind_get_model_iff]
  cases hp : creds_privileged (m_creds m)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact pure_ok _ i _
  · simp only [↓reduceIte]
    exact unmodeled_intro i m

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Groups
