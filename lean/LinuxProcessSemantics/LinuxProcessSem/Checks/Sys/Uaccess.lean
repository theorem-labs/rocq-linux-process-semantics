import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Uaccess — the checkers' user-access gates

Mirrors `theories/LinuxProcessSem/Checks/Sys/Uaccess.v`, the checker side
of the boundary whose spec side is `Sys/Uaccess.lean`: the executable
form of `access_ok_zero`, and an acceptor for an arm whose only two
answers are -EFAULT and one fallback return.  The kernel it decides is
the range check every transfer faces before it dispatches, `access_ok`
(`arch/riscv/include/asm/uaccess.h`, v6.18.46, which is
`include/asm-generic/access_ok.h`'s `__access_ok` on the untagged
address: `size <= limit && addr <= limit - size`), where `vfs_read` and
`vfs_write` return -EFAULT (fs/read_write.c, v6.18.46); the arguments for
the spec side are on `Sys/Uaccess.lean` and are not repeated here.  Not
part of the trusted specification: the soundness and completeness lemmas
below relate each acceptor to the `Sys` combinator it decides, and a
checker that uses one inherits the relation through them.

Every top-level Rocq definition and lemma is here under its own name.
Rocq's three `Ltac`s are the three macros; each one's docstring says how
its Lean arms correspond to Rocq's, and `check_access_ok_zero_split` is
the split the macros perform, as a lemma a proof can `rcases` when it
wants both sides of the gate in one hypothesis rather than two goals. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Uaccess

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude

/-- The executable `access_ok_zero`: the range verdict decides between the
arm's own checker `k` and the bare -EFAULT.  Why a transfer that moved no
bytes still faces the range check, and why the range is the whole of
what it faces, is on Rocq's `Uaccess.access_ok_zero` and `Sys/Uaccess.lean`. -/
def check_access_ok_zero (buf count : word) (eff : SyscallEffect) (m : Model)
    (k : check_result) : check_result :=
  if access_okb buf (bv_unsigned count) then k
  else check_ret_only eff (errno_ret EFAULT) m []

/-- Accept either the bare -EFAULT or the bare `fallback` return: the
executable form of `alt (err_ret EFAULT) (ret_only fallback)`, for an arm
the model cannot decide between the two — a destination whose
writability the model does not track. -/
def check_efault_or (fallback : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if eff_is_errno EFAULT eff then CheckOk m [] else check_ret_only eff fallback m []

/-! ## The split

Rocq's `ok_zero_cases`, `ok_zero_split` and `ok_zero_complete` open
`check_access_ok_zero` and `access_ok_zero` together and case on the
range verdict they share, so that a soundness or completeness proof meets
the same side of the gate in its hypothesis and its goal.  The lemma
states that split once; the macros perform it. -/

/-- Both gates, on both sides of the range verdict at once: in range,
both are their continuation; out of range, the checker is the bare
-EFAULT acceptor and the spec is `err_ret EFAULT`. -/
theorem check_access_ok_zero_split (buf count : word) (eff : SyscallEffect) (m : Model)
    (k : check_result) (ks : Sys SyscallEffect) :
    (access_okb buf (bv_unsigned count) = true
      ∧ check_access_ok_zero buf count eff m k = k
      ∧ access_ok_zero buf count ks = ks)
    ∨ (access_okb buf (bv_unsigned count) = false
      ∧ check_access_ok_zero buf count eff m k = check_ret_only eff (errno_ret EFAULT) m []
      ∧ access_ok_zero buf count ks = err_ret EFAULT) := by
  cases hok : access_okb buf (bv_unsigned count) with
  | true =>
    exact Or.inl ⟨rfl, by simp only [check_access_ok_zero, hok, ↓reduceIte],
      by simp only [access_ok_zero, hok, ↓reduceIte]⟩
  | false =>
    exact Or.inr ⟨rfl, by simp only [check_access_ok_zero, hok, Bool.false_eq_true, ↓reduceIte],
      by simp only [access_ok_zero, hok, Bool.false_eq_true, ↓reduceIte]⟩

/-- Rocq's `ok_zero_cases H b c`: open `check_access_ok_zero` in `H` and
`access_ok_zero` in the goal, case on the range verdict, and reduce the
`if` on both.  The verdict equation is `Hok`, as in Rocq's `eqn:Hok`.
The `unfold`s are each under `try` because Lean's `unfold … at h` fails
when the name occurs nowhere, where Rocq's `unfold … in H` merely does
nothing.  The arms arrive in the OPPOSITE order to Rocq's: Lean's `Bool`
lists `false` before `true`, so the first goal is the out-of-range one,
where `H` is the bare -EFAULT acceptor, and the second is the in-range
one, where `H` is the arm's own checker. -/
syntax "ok_zero_cases " ident term:max term:max : tactic
macro_rules
  | `(tactic| ok_zero_cases $h $b $c) =>
    `(tactic| ((try unfold check_access_ok_zero at $h:ident)
               (try unfold access_ok_zero)
               generalize $(Lean.mkIdent `Hok):ident : access_okb $b (bv_unsigned $c) = ok
                 at $h:ident ⊢
               cases ok <;> simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte] at $h:ident ⊢))

/-- Rocq's `ok_zero_split b c`: the same split over the whole context,
followed by `sys_unfold` and `inv_ok` on each arm, for a completeness
proof whose hypothesis is the spec and whose goal is the checker.  The
`unfold`s are under `try` for the reason above.  Rocq's `destruct` here
names no equation, and Lean's `generalize` could be nameless too; the
verdict is kept as `Hok` on purpose, so a consumer can read which arm it
is on as under `ok_zero_cases` — one hypothesis more than Rocq's tactic
leaves.  The arms arrive `false` first, as above. -/
syntax "ok_zero_split " term:max term:max : tactic
macro_rules
  | `(tactic| ok_zero_split $b $c) =>
    `(tactic| ((try unfold access_ok_zero at *)
               (try unfold check_access_ok_zero at *)
               generalize $(Lean.mkIdent `Hok):ident : access_okb $b (bv_unsigned $c) = ok at *
               cases ok <;> (simp -failIfUnchanged only [Bool.false_eq_true, ↓reduceIte] at *
                             sys_unfold
                             inv_ok)))

/-- Rocq's `ok_zero_complete b c`: `ok_zero_split` and then `rfl` on
every arm, for the completeness proof whose arms both close by
computation. -/
syntax "ok_zero_complete " term:max term:max : tactic
macro_rules
  | `(tactic| ok_zero_complete $b $c) =>
    `(tactic| (ok_zero_split $b $c <;> rfl))

/-! ## `check_efault_or` against `alt (err_ret EFAULT) (ret_only fallback)` -/

theorem check_efault_or_sound_ok (fallback : word) (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_efault_or fallback eff m = CheckOk m' evs) :
    alt (err_ret EFAULT) (ret_only fallback) i m (Ok eff m' evs) := by
  unfold check_efault_or at h
  cases hE : eff_is_errno EFAULT eff with
  | true =>
    simp only [hE, ↓reduceIte, check_result.CheckOk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have heff := eff_is_errno_true EFAULT eff hE
    subst heff
    exact alt_l _ _ i _ _ (pure_ok _ i _)
  | false =>
    simp only [hE, Bool.false_eq_true, ↓reduceIte] at h
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact alt_r _ _ i _ _ (pure_ok _ i _)

theorem check_efault_or_no_unmodeled (fallback : word) (eff : SyscallEffect) (m : Model) :
    check_efault_or fallback eff m ≠ CheckUnmodeled := by
  unfold check_efault_or
  cases eff_is_errno EFAULT eff with
  | true =>
    simp only [↓reduceIte]
    intro h
    cases h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact check_ret_only_no_unmodeled eff fallback m []

/-- Completeness: a `fallback` that itself reads as -EFAULT is accepted by
the first arm, which is why the second arm's `check_ret_only` is never
consulted on it. -/
theorem check_efault_or_complete_ok (fallback : word) (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : alt (err_ret EFAULT) (ret_only fallback) i m (Ok eff m' evs)) :
    check_efault_or fallback eff m = CheckOk m' evs := by
  unfold check_efault_or
  rcases h with h | h
  · unfold err_ret ret_only at h
    rw [pure_iff] at h
    injection h with h1 h2 h3
    subst h1 h2 h3
    have hE : eff_is_errno EFAULT (mkEffect (errno_ret EFAULT) [] []) = true := by
      simp only [eff_is_errno, bv_eqb_refl]
    simp only [hE, ↓reduceIte]
  · unfold ret_only at h
    rw [pure_iff] at h
    injection h with h1 h2 h3
    subst h1 h2 h3
    cases hE : eff_is_errno EFAULT (mkEffect fallback [] []) with
    | true => simp only [↓reduceIte]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

theorem efault_or_no_unmodeled (fallback : word) (i : SyscallInput) (m : Model) :
    ¬ alt (err_ret EFAULT) (ret_only fallback) i m Unmodeled := by
  intro h
  rcases h with h | h
  · unfold err_ret ret_only at h
    rw [pure_iff] at h
    cases h
  · unfold ret_only at h
    rw [pure_iff] at h
    cases h

/-- The acceptor is as narrow as its two arms: an -EINVAL that is not the
`fallback` is refused, the shape a consumer's negative case takes. -/
theorem check_efault_or_not_einval (fallback : word) (m m' : Model) (evs : List event)
    (hne : bv_eqb (errno_ret EINVAL) fallback = false)
    (h : check_efault_or fallback (mkEffect (errno_ret EINVAL) [] []) m = CheckOk m' evs) :
    False := by
  unfold check_efault_or at h
  have hE : eff_is_errno EFAULT (mkEffect (errno_ret EINVAL) [] []) = false := by decide
  simp only [hE, Bool.false_eq_true, ↓reduceIte] at h
  rw [check_ret_only_ok_iff] at h
  obtain ⟨h1, -, -⟩ := h
  injection h1 with hr
  rw [hr, bv_eqb_refl] at hne
  cases hne

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Uaccess
