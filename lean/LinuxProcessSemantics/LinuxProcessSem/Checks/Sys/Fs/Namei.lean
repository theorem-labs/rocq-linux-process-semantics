-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Sys/Fs/Namei.v
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058
unported: unlinkat_open -- the Witness file's Ltac prologue; its two steps are the two `bind_step` refines written out in `unlinkat_witness_ok` -/

/-! # LinuxProcessSem.Checks.Sys.Fs.Namei — the unlinkat (35) checker, its witness, and their proofs

Mirrors `theories/LinuxProcessSem/Checks/Sys/Fs/Namei.v` and
`theories/LinuxProcessSem/Checks/Witness/Fs/Namei.v` together, name for
name: the executable acceptor for `Sys.Fs.Namei.unlinkat_spec`, the
progress witness for it, and the soundness, completeness and
receptiveness proofs that tie the two to the spec.  The `CheckedArm` those
five build, Rocq's `Dispatch.arm_unlinkat`, is the conformance ticket's
registration step in `Checks/Sys/Table.lean`; WHAT THIS FILE DOES NOT
HOLD, below, says what is left to it.  Both Rocq
files answer to Linux `fs/namei.c`; the kernel argument for every arm is
on the spec (`Sys/Fs/Namei.lean`) and is not repeated
here.  Not part of the trusted specification: the checker is what a
trace is graded by, and the proofs are what make that grade a statement
about the spec.

WHY ONE FILE.  Rocq keeps the witness in `Checks/Witness/`, because its
`Progress.v` re-exports every witness module and its `ExecutableSpecs.v`
every checker module.  Here the two go into one `CheckedArm`, whose
`ca_receptive` field needs the witness beside the checker, and the Lean
`Checks/Progress.lean` and `Checks/ExecutableSpecs.lean` take the table
rather than the modules, so nothing needs the split.

THE HEADER'S BASELINE is the commit both Rocq files were read at, the
one `Sys/Fs/Namei.lean` records: there `unlinkat_body_spec`'s
implied-directory arm is a DECLINE, and the spec, checker, witness and
lemmas of the implied-directory removal are gone with it, while
`unlinkat_tmp_spec`'s own implied-directory arm answers `may_delete`'s
-EISDIR; `check_unlinkat_body`, `check_unlinkat_tmp`,
`unlinkat_body_witness` and `unlinkat_tmp_witness` below follow that.
This stops being the right baseline the day either Rocq file
moves again: `tools/check_lean_spec_parity.py` reads the spec twin's
header, and the proofs below, against the spec twin, are what would
stop closing.

TWO ORDERS THE CHECKER KEEPS, both the kernel's.  The flag word is
decided before the pathname is fetched: `SYSCALL_DEFINE3(unlinkat)`
(fs/namei.c, Linux v6.18.46, commit 1f99e9ab748f) returns -EINVAL on a
flag other than AT_REMOVEDIR before the `getname(pathname)` in either of
its two return expressions (fs/namei.c:4777-4782), so that arm is OUTSIDE
the copy-in wrapper and an honest
-EINVAL there carries an empty ledger — `unlinkat_bad_flags_records_no_copyin`
in `Checks/Cases/Checks/Sys/Fs/Namei.lean` is the pin.  And a removal
is accepted only through the six-field match of `check_unlink_result`: a bare
return with every ledger empty, so a forged write, zero, unmap, copy or
copy-in on a syscall that performs none reaches `CheckReject` and not
the model.

THE WITNESS takes the injectable-failure branch of the `alt` wherever
the removal could succeed, exactly as the openat witness does: it
exhibits -ENOMEM with the model unchanged and never has to build the
removed file system.  The removal's own outcome is still admissible — the
checker accepts it, `check_unlinkat_sound_ok` says the spec does too —
so the choice costs nothing but the proof's size.

WHAT THIS FILE DOES NOT HOLD.  The arm, `arm_unlinkat`, is not declared
here and not by this ticket: it is the conformance ticket's registration
step, a block for 35 in `Checks/Sys/Table.lean` built out of the five
proofs below, with the `checked_table` row, the `arm_unfold` lemmas and
the arm-level fact `arm_unlinkat_preserves_vm` that
`Checks/VmMapsDisjoint/Arms.lean`'s alternation consumes — the C ticket's
brief names no registration point, so that the checker can land on the
preludes and the spec alone, ahead of the checked-table chain.  What
this file holds of that argument, ahead of the registration that consumes
them as `Checks/Sys/Fs/Sync.lean` holds `check_fsync_frame`, is
`check_unlinkat_frame`, Rocq's `VmMapsDisjoint.check_unlinkat_frame`,
proved with this file's own means (Rocq closes it with `vm_frame2`; the
lemma says why that does not carry over), and
`check_unlinkat_fd_state_frame` beside it.

LEAN-ONLY LEMMAS, none with a Rocq twin: `check_unlink_result_ok_inv`,
`check_unlink_found_ok_inv`, `check_unlinkat_tmp_ok_inv` and
`check_unlinkat_body_ok_inv`, each `eff.eff_copyins = [] ∧ m_vmmaps m' =
m_vmmaps m ∧ m'.m_fd = m.m_fd` for one layer's `CheckOk`, and
`check_unlinkat_fd_state_frame`, the last conjunct at the top.  Rocq proves
the vm frame in one shot, `repeat' … split at h` over the unfolded checker;
in Lean that `split` exceeds `simp`'s step budget on the whole term, so the
frame is carried up layer by layer instead, and the descriptor conjunct
rides the same case analysis because `Checks/Invariants.lean` holds every
arm of `checked_table` to two invariants over `m_fd`.  Their consumers are
`check_unlinkat_frame` (the vm conjunct), `check_unlinkat_fd_state_frame`
(the descriptor conjunct) and the `*_ok_copyins_nil` twins, which are
their first projections and feed `check_unlinkat_complete_ok` as Rocq's do.

SPELLINGS, said once: Rocq's `negb` is `!`, `Nat.ltb NAME_MAX (length n)`
is the decidable `NAME_MAX < n.length`, `in_mem i` is `i.in_mem`, and
the `Ltac` prologues `ul_open`/`ul_open_u` are the two macros below.
The guard proofs are written out where Rocq's are `destruct …; hall …;
inv_ok`: each guard is a `cases hg : g` and a `simp only [hg, …,
↓reduceIte]` on both sides, so that the checker's `if` and the spec's
applied `if` are reduced by the same fact. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Namei

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! ## The checker -/

/-- The acceptor for the arm of `unlinkat_spec` that can succeed: an
injectable errno with no state change, or the removal itself returning 0.
Both take a bare return and FIVE EMPTY ledgers, so only a forged ledger
reaches the other half of the claim.  Rocq: `Namei.check_unlink_result`. -/
def check_unlink_result (p : path) (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | SyscallEffect.mkEffectU ret [] [] [] [] [] =>
      if errno_ret_in unlinkat_errnos ret then CheckOk m []
      else if bv_eqb ret (Z_to_bv 64 0) then CheckOk (with_fs (fs_remove (m_fs m) p) m) []
      else CheckReject
  | _ => CheckReject

/-- Mirrors `unlink_found_spec`, the tail both arms share.  Rocq:
`Namei.check_unlink_found`. -/
def check_unlink_found (p c : path) (flags : word) (eff : SyscallEffect) (m : Model) :
    check_result :=
  if unlink_rmdir flags then check_ret_only eff (errno_ret ENOTDIR) m []
  else if path_trailing_slash p then check_ret_only eff (errno_ret ENOTDIR) m []
  else if fd_names_path (m_fds m) c then CheckUnmodeled
  else check_unlink_result c eff m

/-- Mirrors `unlinkat_tmp_spec`; that definition carries the premise, says
what the absent key's -ENOENT and the implied directory's -EISDIR rest on
(`may_delete`, fs/namei.c:3289-3290, Linux v6.18.46, tested BEFORE the
lookup, since an implied directory is not a key the run holds), and says
what each decline is for.  Rocq: `Namei.check_unlinkat_tmp`. -/
def check_unlinkat_tmp (n p c : path) (flags : word) (eff : SyscallEffect) (m : Model) :
    check_result :=
  if unlink_rmdir flags then CheckUnmodeled
  else if NAME_MAX < n.length then CheckUnmodeled
  else if fs_under (m_fs m) c then check_ret_only eff (errno_ret EISDIR) m []
  else
    match fs_lookup (m_fs m) c with
    | none => check_ret_only eff (errno_ret ENOENT) m []
    | some _ => check_unlink_found p c flags eff m

/-- Mirrors `unlinkat_body_spec`, guard for guard.  Rocq:
`Namei.check_unlinkat_body`. -/
def check_unlinkat_body (i : SyscallInput) (dirfd pathp flags : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match read_cstr i.in_mem pathp with
  | CstrTooLong => check_ret_only eff (errno_ret ENAMETOOLONG) m []
  | CstrFault => check_ret_only eff (errno_ret EFAULT) m []
  | CstrOk p =>
    if path_eqb p [] then check_ret_only eff (errno_ret ENOENT) m []
    else if !(bv_eqb dirfd AT_FDCWD32) then CheckUnmodeled
    else
      let c := path_strip_trailing_slashes p
      if path_eqb c [] then
        (if unlink_rmdir flags then check_ret_only eff (errno_ret EBUSY) m []
         else check_ret_only eff (errno_ret EISDIR) m [])
      else if path_has_slash c then
        (match tmp_name c with
         | some n => check_unlinkat_tmp n p c flags eff m
         | none => CheckUnmodeled)
      else if path_eqb c dot_path then
        (if unlink_rmdir flags then check_ret_only eff (errno_ret EINVAL) m []
         else check_ret_only eff (errno_ret EISDIR) m [])
      else if path_eqb c dotdot_path then
        (if unlink_rmdir flags then check_ret_only eff (errno_ret ENOTEMPTY) m []
         else check_ret_only eff (errno_ret EISDIR) m [])
      else if NAME_MAX < c.length then CheckUnmodeled
      else if fs_under (m_fs m) c then CheckUnmodeled
      else
        match fs_lookup (m_fs m) c with
        | none => check_ret_only eff (errno_ret ENOENT) m []
        | some _ => check_unlink_found p c flags eff m

/-- The pathname copy-in, as the openat checker checks it: decide the body
against the effect with the ledger cleared, then require the claimed
ledger to be exactly that one range.  The flag arm is outside the wrapper
because the kernel decides it before `getname` (the header says where),
so an honest -EINVAL there carries no copy-in at all.  Rocq:
`Namei.check_unlinkat`. -/
def check_unlinkat (i : SyscallInput) (dirfd pathp flags : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if !(modeled_unlink_flags flags) then check_ret_only eff (errno_ret EINVAL) m []
  else
    let reads := [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
    check_copyins_after reads eff (check_unlinkat_body i dirfd pathp flags (clear_copyins eff) m)

/-! ## The witness -/

/-- Mirrors `unlink_found_spec`: the removal is witnessed by the `alt`'s
LEFT branch, so the witness never builds the removed file system.  Rocq:
`Witness.Fs.Namei.unlink_found_witness`. -/
def unlink_found_witness (p c : path) (flags : word) (m : Model) : outcome SyscallEffect :=
  if unlink_rmdir flags then ret_outcome (errno_ret ENOTDIR) m
  else if path_trailing_slash p then ret_outcome (errno_ret ENOTDIR) m
  else if fd_names_path (m_fds m) c then Unmodeled
  else ret_outcome (errno_ret witness_errno) m

/-- Mirrors `unlinkat_tmp_spec`.  Rocq: `Witness.Fs.Namei.unlinkat_tmp_witness`. -/
def unlinkat_tmp_witness (n p c : path) (flags : word) (m : Model) : outcome SyscallEffect :=
  if unlink_rmdir flags then Unmodeled
  else if NAME_MAX < n.length then Unmodeled
  else if fs_under (m_fs m) c then ret_outcome (errno_ret EISDIR) m
  else
    match fs_lookup (m_fs m) c with
    | none => ret_outcome (errno_ret ENOENT) m
    | some _ => unlink_found_witness p c flags m

/-- Mirrors `unlinkat_body_spec`.  Rocq: `Witness.Fs.Namei.unlinkat_body_witness`. -/
def unlinkat_body_witness (dirfd pathp flags : word) (i : SyscallInput) (m : Model) :
    outcome SyscallEffect :=
  match read_cstr i.in_mem pathp with
  | CstrTooLong => ret_outcome (errno_ret ENAMETOOLONG) m
  | CstrFault => ret_outcome (errno_ret EFAULT) m
  | CstrOk p =>
    if path_eqb p [] then ret_outcome (errno_ret ENOENT) m
    else if !(bv_eqb dirfd AT_FDCWD32) then Unmodeled
    else
      let c := path_strip_trailing_slashes p
      if path_eqb c [] then
        (if unlink_rmdir flags then ret_outcome (errno_ret EBUSY) m
         else ret_outcome (errno_ret EISDIR) m)
      else if path_has_slash c then
        (match tmp_name c with
         | some n => unlinkat_tmp_witness n p c flags m
         | none => Unmodeled)
      else if path_eqb c dot_path then
        (if unlink_rmdir flags then ret_outcome (errno_ret EINVAL) m
         else ret_outcome (errno_ret EISDIR) m)
      else if path_eqb c dotdot_path then
        (if unlink_rmdir flags then ret_outcome (errno_ret ENOTEMPTY) m
         else ret_outcome (errno_ret EISDIR) m)
      else if NAME_MAX < c.length then Unmodeled
      else if fs_under (m_fs m) c then Unmodeled
      else
        match fs_lookup (m_fs m) c with
        | none => ret_outcome (errno_ret ENOENT) m
        | some _ => unlink_found_witness p c flags m

/-- The flag arm carries no copy-in — the kernel decides it before
`getname` — and every other arm carries the one pathname range
`unlinkat_spec` records.  Rocq: `Witness.Fs.Namei.unlinkat_witness`. -/
def unlinkat_witness (dirfd pathp flags : word) (i : SyscallInput) (m : Model) :
    outcome SyscallEffect :=
  if !(modeled_unlink_flags flags) then ret_outcome (errno_ret EINVAL) m
  else
    outcome_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
      (unlinkat_body_witness dirfd pathp flags i m)

/-! ## Soundness: what the checker accepts, the spec admits -/

/-- Read the input and the model, the two steps `unlinkat_spec` takes
before the flag test.  Rocq: `Namei.ul_open`. -/
macro "ul_open" : tactic =>
  `(tactic| (refine bind_ok0 _ _ _ _ _ _ _ _ _ (input_ok _ _) ?_
             refine bind_ok0 _ _ _ _ _ _ _ _ _ (get_model_ok _ _) ?_))

/-- The same two steps when the outcome being justified is `Unmodeled`.
Rocq: `Namei.ul_open_u`. -/
macro "ul_open_u" : tactic =>
  `(tactic| (refine bind_unmodeled2 _ _ _ _ _ _ _ (input_ok _ _) ?_
             refine bind_unmodeled2 _ _ _ _ _ _ _ (get_model_ok _ _) ?_))

/-- Rocq: `Namei.check_unlink_found_sound_ok`. -/
theorem check_unlink_found_sound_ok (i : SyscallInput) (p c : path) (flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_unlink_found p c flags eff m = CheckOk m' evs) :
    unlink_found_spec p c flags m i m (Ok eff m' evs) := by
  unfold check_unlink_found at h
  unfold unlink_found_spec
  cases hrm : unlink_rmdir flags
  · simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hts : path_trailing_slash p
    · simp only [hts, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hfd : fd_names_path (m_fds m) c
      · simp only [hfd, Bool.false_eq_true, ↓reduceIte] at h ⊢
        unfold check_unlink_result at h
        obtain ⟨ret, ws, zs, us, cs, cis⟩ := eff
        cases ws <;> cases zs <;> cases us <;> cases cs <;> cases cis <;> dsimp only at h <;>
          try (cases h)
        cases he : errno_ret_in unlinkat_errnos ret
        · simp only [he, Bool.false_eq_true, ↓reduceIte] at h
          cases heq : bv_eqb ret (Z_to_bv 64 0)
          · simp only [heq, Bool.false_eq_true, ↓reduceIte] at h
            cases h
          · simp only [heq, ↓reduceIte] at h
            cases h
            obtain rfl : ret = Z_to_bv 64 0 := (bv_eqb_eq _ _).mp heq
            exact alt_r _ _ i _ _
              (bind_ok0 _ _ i _ () _ _ _ _ (modify_ok _ i _) (pure_ok _ i _))
        · simp only [he, ↓reduceIte] at h
          cases h
          obtain ⟨e, hin, rfl⟩ := (errno_ret_in_true _ _).mp he
          exact alt_l _ _ i _ _
            (bind_ok0 _ _ i _ e _ _ _ _ (choose_ok _ e i _ hin) (pure_ok _ i _))
      · simp only [hfd, ↓reduceIte] at h
        cases h
    · simp only [hts, ↓reduceIte] at h ⊢
      rw [check_ret_only_ok_iff] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact pure_ok _ i _
  · simp only [hrm, ↓reduceIte] at h ⊢
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact pure_ok _ i _

/-- Rocq: `Namei.check_unlink_found_sound_unmodeled`. -/
theorem check_unlink_found_sound_unmodeled (i : SyscallInput) (p c : path) (flags : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_unlink_found p c flags eff m = CheckUnmodeled) :
    unlink_found_spec p c flags m i m Unmodeled := by
  unfold check_unlink_found at h
  unfold unlink_found_spec
  cases hrm : unlink_rmdir flags
  · simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hts : path_trailing_slash p
    · simp only [hts, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hfd : fd_names_path (m_fds m) c
      · simp only [hfd, Bool.false_eq_true, ↓reduceIte] at h
        exfalso
        unfold check_unlink_result at h
        obtain ⟨ret, ws, zs, us, cs, cis⟩ := eff
        cases ws <;> cases zs <;> cases us <;> cases cs <;> cases cis <;> dsimp only at h <;>
          try (cases h)
        split at h <;> (try split at h) <;> cases h
      · simp only [↓reduceIte]
        exact unmodeled_intro i m
    · simp only [hts, ↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  · simp only [hrm, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

/-- What an accepted effect and model look like below the guards: the
effect's copy-in ledger is empty, and the VM ledger and the descriptor
subsystem are the input's.  The three conjuncts are consumed by different
callers — `check_unlinkat_complete_ok` needs the first,
`check_unlinkat_frame` the second, `check_unlinkat_fd_state_frame` the
third — so all three ride one case analysis rather than three copies of
it.  No Rocq twin: Rocq gets the first from
`check_unlink_found_ok_copyins_nil` and the second from
`VmMapsDisjoint.vm_frame2`, whose `split` this checker's unfolded body
exhausts (simp's step budget); the third is owed to the Lean registry
alone (`Checks/Invariants.lean`). -/
theorem check_unlink_result_ok_inv (p : path) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_unlink_result p eff m = CheckOk m' evs) :
    eff.eff_copyins = [] ∧ m_vmmaps m' = m_vmmaps m ∧ m'.m_fd = m.m_fd := by
  unfold check_unlink_result at h
  obtain ⟨ret, ws, zs, us, cs, cis⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases cis <;> dsimp only at h <;>
    try (cases h)
  split at h
  · cases h
    exact ⟨rfl, rfl, rfl⟩
  · split at h
    · cases h
      exact ⟨rfl, rfl, rfl⟩
    · cases h

/-- The `check_unlink_result_ok_inv` shape one level up.  No Rocq twin. -/
theorem check_unlink_found_ok_inv (p c : path) (flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_unlink_found p c flags eff m = CheckOk m' evs) :
    eff.eff_copyins = [] ∧ m_vmmaps m' = m_vmmaps m ∧ m'.m_fd = m.m_fd := by
  unfold check_unlink_found at h
  cases hrm : unlink_rmdir flags
  · simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h
    cases hts : path_trailing_slash p
    · simp only [hts, Bool.false_eq_true, ↓reduceIte] at h
      cases hfd : fd_names_path (m_fds m) c
      · simp only [hfd, Bool.false_eq_true, ↓reduceIte] at h
        exact check_unlink_result_ok_inv c eff m m' evs h
      · simp only [hfd, ↓reduceIte] at h
        cases h
    · simp only [hts, ↓reduceIte] at h
      rw [check_ret_only_ok_iff] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact ⟨rfl, rfl, rfl⟩
  · simp only [hrm, ↓reduceIte] at h
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨rfl, rfl, rfl⟩

/-- Rocq: `Namei.check_unlink_found_ok_copyins_nil`. -/
theorem check_unlink_found_ok_copyins_nil (p c : path) (flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_unlink_found p c flags eff m = CheckOk m' evs) :
    eff.eff_copyins = [] :=
  (check_unlink_found_ok_inv p c flags eff m m' evs h).1

/-- Rocq: `Namei.check_unlinkat_tmp_sound_ok`. -/
theorem check_unlinkat_tmp_sound_ok (i : SyscallInput) (n p c : path) (flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_unlinkat_tmp n p c flags eff m = CheckOk m' evs) :
    unlinkat_tmp_spec n p c flags m i m (Ok eff m' evs) := by
  unfold check_unlinkat_tmp at h
  unfold unlinkat_tmp_spec
  cases hrm : unlink_rmdir flags
  · simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hnm : NAME_MAX < n.length
    · simp only [hnm, ↓reduceIte] at h
      cases h
    · simp only [hnm, ↓reduceIte] at h ⊢
      cases hun : fs_under (m_fs m) c
      · simp only [hun, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hfs : fs_lookup (m_fs m) c with
        | none =>
          simp only [hfs] at h
          rw [check_ret_only_ok_iff] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact pure_ok _ i _
        | some data =>
          simp only [hfs] at h
          exact check_unlink_found_sound_ok i p c flags eff m m' evs h
      · simp only [hun, ↓reduceIte] at h ⊢
        rw [check_ret_only_ok_iff] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact pure_ok _ i _
  · simp only [hrm, ↓reduceIte] at h
    cases h

/-- Rocq: `Namei.check_unlinkat_tmp_sound_unmodeled`. -/
theorem check_unlinkat_tmp_sound_unmodeled (i : SyscallInput) (n p c : path) (flags : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_unlinkat_tmp n p c flags eff m = CheckUnmodeled) :
    unlinkat_tmp_spec n p c flags m i m Unmodeled := by
  unfold check_unlinkat_tmp at h
  unfold unlinkat_tmp_spec
  cases hrm : unlink_rmdir flags
  · simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hnm : NAME_MAX < n.length
    · simp only [hnm, ↓reduceIte]
      exact unmodeled_intro i m
    · simp only [hnm, ↓reduceIte] at h ⊢
      cases hun : fs_under (m_fs m) c
      · simp only [hun, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hfs : fs_lookup (m_fs m) c with
        | none =>
          simp only [hfs] at h
          exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
        | some data =>
          simp only [hfs] at h
          exact check_unlink_found_sound_unmodeled i p c flags eff m h
      · simp only [hun, ↓reduceIte] at h
        exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  · simp only [↓reduceIte]
    exact unmodeled_intro i m

/-- The `check_unlink_result_ok_inv` shape for the /tmp arm.  No Rocq twin. -/
theorem check_unlinkat_tmp_ok_inv (n p c : path) (flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_unlinkat_tmp n p c flags eff m = CheckOk m' evs) :
    eff.eff_copyins = [] ∧ m_vmmaps m' = m_vmmaps m ∧ m'.m_fd = m.m_fd := by
  unfold check_unlinkat_tmp at h
  cases hrm : unlink_rmdir flags
  · simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hnm : NAME_MAX < n.length
    · simp only [hnm, ↓reduceIte] at h
      cases h
    · simp only [hnm, ↓reduceIte] at h
      cases hun : fs_under (m_fs m) c
      · simp only [hun, Bool.false_eq_true, ↓reduceIte] at h
        cases hfs : fs_lookup (m_fs m) c with
        | none =>
          simp only [hfs] at h
          rw [check_ret_only_ok_iff] at h
          obtain ⟨rfl, rfl, -⟩ := h
          exact ⟨rfl, rfl, rfl⟩
        | some data =>
          simp only [hfs] at h
          exact check_unlink_found_ok_inv p c flags eff m m' evs h
      · simp only [hun, ↓reduceIte] at h
        rw [check_ret_only_ok_iff] at h
        obtain ⟨rfl, rfl, -⟩ := h
        exact ⟨rfl, rfl, rfl⟩
  · simp only [hrm, ↓reduceIte] at h
    cases h

/-- Rocq: `Namei.check_unlinkat_tmp_ok_copyins_nil`. -/
theorem check_unlinkat_tmp_ok_copyins_nil (n p c : path) (flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_unlinkat_tmp n p c flags eff m = CheckOk m' evs) :
    eff.eff_copyins = [] :=
  (check_unlinkat_tmp_ok_inv n p c flags eff m m' evs h).1

/-- Rocq: `Namei.check_unlinkat_body_sound_ok`. -/
theorem check_unlinkat_body_sound_ok (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_unlinkat_body i dirfd pathp flags eff m = CheckOk m' evs) :
    unlinkat_body_spec dirfd pathp flags i m i m (Ok eff m' evs) := by
  unfold check_unlinkat_body at h
  unfold unlinkat_body_spec
  cases hp : read_cstr i.in_mem pathp with
  | CstrTooLong =>
    simp only [hp] at h
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact pure_ok _ i _
  | CstrFault =>
    simp only [hp] at h
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact pure_ok _ i _
  | CstrOk p =>
    simp only [hp] at h
    dsimp only
    cases hpe : path_eqb p []
    · simp only [hpe, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hd : bv_eqb dirfd AT_FDCWD32
      · simp only [hd, Bool.not_false, ↓reduceIte] at h
        cases h
      · simp only [hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hroot : path_eqb (path_strip_trailing_slashes p) []
        · simp only [hroot, Bool.false_eq_true, ↓reduceIte] at h ⊢
          cases hsl : path_has_slash (path_strip_trailing_slashes p)
          · simp only [hsl, Bool.false_eq_true, ↓reduceIte] at h ⊢
            cases hdot : path_eqb (path_strip_trailing_slashes p) dot_path
            · simp only [hdot, Bool.false_eq_true, ↓reduceIte] at h ⊢
              cases hdd : path_eqb (path_strip_trailing_slashes p) dotdot_path
              · simp only [hdd, Bool.false_eq_true, ↓reduceIte] at h ⊢
                by_cases hnm : NAME_MAX < (path_strip_trailing_slashes p).length
                · simp only [hnm, ↓reduceIte] at h
                  cases h
                · simp only [hnm, ↓reduceIte] at h ⊢
                  cases hun : fs_under (m_fs m) (path_strip_trailing_slashes p)
                  · simp only [hun, Bool.false_eq_true, ↓reduceIte] at h ⊢
                    cases hfs : fs_lookup (m_fs m) (path_strip_trailing_slashes p) with
                    | none =>
                      simp only [hfs] at h
                      rw [check_ret_only_ok_iff] at h
                      obtain ⟨rfl, rfl, rfl⟩ := h
                      exact pure_ok _ i _
                    | some data =>
                      simp only [hfs] at h
                      exact check_unlink_found_sound_ok i p _ flags eff m m' evs h
                  · simp only [hun, ↓reduceIte] at h
                    cases h
              · simp only [hdd, ↓reduceIte] at h ⊢
                cases hrm : unlink_rmdir flags
                · simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h ⊢
                  rw [check_ret_only_ok_iff] at h
                  obtain ⟨rfl, rfl, rfl⟩ := h
                  exact pure_ok _ i _
                · simp only [hrm, ↓reduceIte] at h ⊢
                  rw [check_ret_only_ok_iff] at h
                  obtain ⟨rfl, rfl, rfl⟩ := h
                  exact pure_ok _ i _
            · simp only [hdot, ↓reduceIte] at h ⊢
              cases hrm : unlink_rmdir flags
              · simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h ⊢
                rw [check_ret_only_ok_iff] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                exact pure_ok _ i _
              · simp only [hrm, ↓reduceIte] at h ⊢
                rw [check_ret_only_ok_iff] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                exact pure_ok _ i _
          · simp only [hsl, ↓reduceIte] at h ⊢
            cases htn : tmp_name (path_strip_trailing_slashes p) with
            | none =>
              simp only [htn] at h
              cases h
            | some n =>
              simp only [htn] at h
              exact check_unlinkat_tmp_sound_ok i n p _ flags eff m m' evs h
        · simp only [hroot, ↓reduceIte] at h ⊢
          cases hrm : unlink_rmdir flags
          · simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h ⊢
            rw [check_ret_only_ok_iff] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact pure_ok _ i _
          · simp only [hrm, ↓reduceIte] at h ⊢
            rw [check_ret_only_ok_iff] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact pure_ok _ i _
    · simp only [hpe, ↓reduceIte] at h ⊢
      rw [check_ret_only_ok_iff] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact pure_ok _ i _

/-- Rocq: `Namei.check_unlinkat_body_sound_unmodeled`. -/
theorem check_unlinkat_body_sound_unmodeled (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_unlinkat_body i dirfd pathp flags eff m = CheckUnmodeled) :
    unlinkat_body_spec dirfd pathp flags i m i m Unmodeled := by
  unfold check_unlinkat_body at h
  unfold unlinkat_body_spec
  cases hp : read_cstr i.in_mem pathp with
  | CstrTooLong =>
    simp only [hp] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | CstrFault =>
    simp only [hp] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | CstrOk p =>
    simp only [hp] at h
    dsimp only
    cases hpe : path_eqb p []
    · simp only [hpe, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hd : bv_eqb dirfd AT_FDCWD32
      · simp only [Bool.not_false, ↓reduceIte]
        exact unmodeled_intro i m
      · simp only [hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hroot : path_eqb (path_strip_trailing_slashes p) []
        · simp only [hroot, Bool.false_eq_true, ↓reduceIte] at h ⊢
          cases hsl : path_has_slash (path_strip_trailing_slashes p)
          · simp only [hsl, Bool.false_eq_true, ↓reduceIte] at h ⊢
            cases hdot : path_eqb (path_strip_trailing_slashes p) dot_path
            · simp only [hdot, Bool.false_eq_true, ↓reduceIte] at h ⊢
              cases hdd : path_eqb (path_strip_trailing_slashes p) dotdot_path
              · simp only [hdd, Bool.false_eq_true, ↓reduceIte] at h ⊢
                by_cases hnm : NAME_MAX < (path_strip_trailing_slashes p).length
                · simp only [hnm, ↓reduceIte]
                  exact unmodeled_intro i m
                · simp only [hnm, ↓reduceIte] at h ⊢
                  cases hun : fs_under (m_fs m) (path_strip_trailing_slashes p)
                  · simp only [hun, Bool.false_eq_true, ↓reduceIte] at h ⊢
                    cases hfs : fs_lookup (m_fs m) (path_strip_trailing_slashes p) with
                    | none =>
                      simp only [hfs] at h
                      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
                    | some data =>
                      simp only [hfs] at h
                      exact check_unlink_found_sound_unmodeled i p _ flags eff m h
                  · simp only [hun, ↓reduceIte] at h ⊢
                    exact unmodeled_intro i m
              · simp only [hdd, ↓reduceIte] at h
                cases hrm : unlink_rmdir flags
                · simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h
                  exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
                · simp only [hrm, ↓reduceIte] at h
                  exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
            · simp only [hdot, ↓reduceIte] at h
              cases hrm : unlink_rmdir flags
              · simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h
                exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
              · simp only [hrm, ↓reduceIte] at h
                exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
          · simp only [hsl, ↓reduceIte] at h ⊢
            cases htn : tmp_name (path_strip_trailing_slashes p) with
            | none => exact unmodeled_intro i m
            | some n =>
              simp only [htn] at h
              exact check_unlinkat_tmp_sound_unmodeled i n p _ flags eff m h
        · simp only [hroot, ↓reduceIte] at h
          cases hrm : unlink_rmdir flags
          · simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h
            exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
          · simp only [hrm, ↓reduceIte] at h
            exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    · simp only [hpe, ↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

/-- The `check_unlink_result_ok_inv` shape for the whole body.  No Rocq
twin; `check_unlinkat_body_ok_copyins_nil`, `check_unlinkat_frame` and
`check_unlinkat_fd_state_frame` are its three conjuncts, lifted through
the flag gate. -/
theorem check_unlinkat_body_ok_inv (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_unlinkat_body i dirfd pathp flags eff m = CheckOk m' evs) :
    eff.eff_copyins = [] ∧ m_vmmaps m' = m_vmmaps m ∧ m'.m_fd = m.m_fd := by
  unfold check_unlinkat_body at h
  cases hp : read_cstr i.in_mem pathp with
  | CstrTooLong =>
    simp only [hp] at h
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨rfl, rfl, rfl⟩
  | CstrFault =>
    simp only [hp] at h
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨rfl, rfl, rfl⟩
  | CstrOk p =>
    simp only [hp] at h
    cases hpe : path_eqb p []
    · simp only [hpe, Bool.false_eq_true, ↓reduceIte] at h
      cases hd : bv_eqb dirfd AT_FDCWD32
      · simp only [hd, Bool.not_false, ↓reduceIte] at h
        cases h
      · simp only [hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        cases hroot : path_eqb (path_strip_trailing_slashes p) []
        · simp only [hroot, Bool.false_eq_true, ↓reduceIte] at h
          cases hsl : path_has_slash (path_strip_trailing_slashes p)
          · simp only [hsl, Bool.false_eq_true, ↓reduceIte] at h
            cases hdot : path_eqb (path_strip_trailing_slashes p) dot_path
            · simp only [hdot, Bool.false_eq_true, ↓reduceIte] at h
              cases hdd : path_eqb (path_strip_trailing_slashes p) dotdot_path
              · simp only [hdd, Bool.false_eq_true, ↓reduceIte] at h
                by_cases hnm : NAME_MAX < (path_strip_trailing_slashes p).length
                · simp only [hnm, ↓reduceIte] at h
                  cases h
                · simp only [hnm, ↓reduceIte] at h
                  cases hun : fs_under (m_fs m) (path_strip_trailing_slashes p)
                  · simp only [hun, Bool.false_eq_true, ↓reduceIte] at h
                    cases hfs : fs_lookup (m_fs m) (path_strip_trailing_slashes p) with
                    | none =>
                      simp only [hfs] at h
                      rw [check_ret_only_ok_iff] at h
                      obtain ⟨rfl, rfl, -⟩ := h
                      exact ⟨rfl, rfl, rfl⟩
                    | some data =>
                      simp only [hfs] at h
                      exact check_unlink_found_ok_inv p _ flags eff m m' evs h
                  · simp only [hun, ↓reduceIte] at h
                    cases h
              · simp only [hdd, ↓reduceIte] at h
                cases hrm : unlink_rmdir flags
                · simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h
                  rw [check_ret_only_ok_iff] at h
                  obtain ⟨rfl, rfl, -⟩ := h
                  exact ⟨rfl, rfl, rfl⟩
                · simp only [hrm, ↓reduceIte] at h
                  rw [check_ret_only_ok_iff] at h
                  obtain ⟨rfl, rfl, -⟩ := h
                  exact ⟨rfl, rfl, rfl⟩
            · simp only [hdot, ↓reduceIte] at h
              cases hrm : unlink_rmdir flags
              · simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h
                rw [check_ret_only_ok_iff] at h
                obtain ⟨rfl, rfl, -⟩ := h
                exact ⟨rfl, rfl, rfl⟩
              · simp only [hrm, ↓reduceIte] at h
                rw [check_ret_only_ok_iff] at h
                obtain ⟨rfl, rfl, -⟩ := h
                exact ⟨rfl, rfl, rfl⟩
          · simp only [hsl, ↓reduceIte] at h
            cases htn : tmp_name (path_strip_trailing_slashes p) with
            | none =>
              simp only [htn] at h
              cases h
            | some n =>
              simp only [htn] at h
              exact check_unlinkat_tmp_ok_inv n p _ flags eff m m' evs h
        · simp only [hroot, ↓reduceIte] at h
          cases hrm : unlink_rmdir flags
          · simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h
            rw [check_ret_only_ok_iff] at h
            obtain ⟨rfl, rfl, -⟩ := h
            exact ⟨rfl, rfl, rfl⟩
          · simp only [hrm, ↓reduceIte] at h
            rw [check_ret_only_ok_iff] at h
            obtain ⟨rfl, rfl, -⟩ := h
            exact ⟨rfl, rfl, rfl⟩
    · simp only [hpe, ↓reduceIte] at h
      rw [check_ret_only_ok_iff] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact ⟨rfl, rfl, rfl⟩

/-- No arm of the body claims a copy-in of its own: each returns either
through `check_ret_only`, which forces every ledger empty, or through
`check_unlink_result`, which matches six empty lists.  That is what lets
`check_unlinkat_complete_ok` equate the WHOLE claimed ledger with the one
pathname range rather than with a prefix of it.  Rocq:
`Namei.check_unlinkat_body_ok_copyins_nil`. -/
theorem check_unlinkat_body_ok_copyins_nil (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_unlinkat_body i dirfd pathp flags eff m = CheckOk m' evs) :
    eff.eff_copyins = [] :=
  (check_unlinkat_body_ok_inv i dirfd pathp flags eff m m' evs h).1

/-! ## Completeness: what the spec admits, the checker accepts -/

/-- 0 is not an injectable errno, so the removal and the failure
alternative never both accept the same return.  Rocq:
`Namei.errno_ret_in_unlinkat_zero`. -/
theorem errno_ret_in_unlinkat_zero : errno_ret_in unlinkat_errnos (Z_to_bv 64 0) = false := by
  decide

/-- Rocq: `Namei.check_unlink_found_complete_ok`. -/
theorem check_unlink_found_complete_ok (i : SyscallInput) (p c : path) (flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : unlink_found_spec p c flags m i m (Ok eff m' evs)) :
    check_unlink_found p c flags eff m = CheckOk m' evs := by
  unfold unlink_found_spec at h
  unfold check_unlink_found
  cases hrm : unlink_rmdir flags
  · simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hts : path_trailing_slash p
    · simp only [hts, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hfd : fd_names_path (m_fds m) c
      · simp only [hfd, Bool.false_eq_true, ↓reduceIte] at h ⊢
        rcases h with h | h
        · -- the injectable failure: no state change
          obtain ⟨e, hin, hk⟩ := (bind_choose_iff _ _ i m _).mp h
          cases (pure_iff _ i _ _).mp hk
          simp only [check_unlink_result, errno_ret_in_intro _ _ hin, ↓reduceIte]
        · -- the removal itself
          have h' := (bind_modify_iff (with_fs (fs_remove (m_fs m) c))
            (fun _ => ret_only (Z_to_bv 64 0)) i m _).mp h
          cases (pure_iff _ i _ _).mp h'
          simp only [check_unlink_result, errno_ret_in_unlinkat_zero, bv_eqb_refl,
            Bool.false_eq_true, ↓reduceIte]
      · simp only [hfd, ↓reduceIte] at h
        cases (unmodeled_iff _ _ _).mp h
    · simp only [hts, ↓reduceIte] at h ⊢
      cases (pure_iff _ i _ _).mp h
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  · simp only [hrm, ↓reduceIte] at h ⊢
    cases (pure_iff _ i _ _).mp h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- Rocq: `Namei.check_unlink_found_complete_unmodeled`. -/
theorem check_unlink_found_complete_unmodeled (i : SyscallInput) (p c : path) (flags : word)
    (m : Model) (eff : SyscallEffect) (h : unlink_found_spec p c flags m i m Unmodeled) :
    check_unlink_found p c flags eff m = CheckUnmodeled := by
  unfold unlink_found_spec at h
  unfold check_unlink_found
  cases hrm : unlink_rmdir flags
  · simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hts : path_trailing_slash p
    · simp only [hts, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hfd : fd_names_path (m_fds m) c
      · simp only [hfd, Bool.false_eq_true, ↓reduceIte] at h
        rcases h with h | h
        · obtain ⟨e, -, hk⟩ := (bind_choose_iff _ _ i m _).mp h
          cases (pure_iff _ i _ _).mp hk
        · have h' := (bind_modify_iff (with_fs (fs_remove (m_fs m) c))
            (fun _ => ret_only (Z_to_bv 64 0)) i m _).mp h
          cases (pure_iff _ i _ _).mp h'
      · simp only [↓reduceIte]
    · simp only [hts, ↓reduceIte] at h
      cases (pure_iff _ i _ _).mp h
  · simp only [hrm, ↓reduceIte] at h
    cases (pure_iff _ i _ _).mp h

/-- Rocq: `Namei.check_unlinkat_tmp_complete_ok`. -/
theorem check_unlinkat_tmp_complete_ok (i : SyscallInput) (n p c : path) (flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : unlinkat_tmp_spec n p c flags m i m (Ok eff m' evs)) :
    check_unlinkat_tmp n p c flags eff m = CheckOk m' evs := by
  unfold unlinkat_tmp_spec at h
  unfold check_unlinkat_tmp
  cases hrm : unlink_rmdir flags
  · simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hnm : NAME_MAX < n.length
    · simp only [hnm, ↓reduceIte] at h
      cases (unmodeled_iff _ _ _).mp h
    · simp only [hnm, ↓reduceIte] at h ⊢
      cases hun : fs_under (m_fs m) c
      · simp only [hun, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hfs : fs_lookup (m_fs m) c with
        | none =>
          simp only [hfs] at h ⊢
          cases (pure_iff _ i _ _).mp h
          exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
        | some data =>
          simp only [hfs] at h
          exact check_unlink_found_complete_ok i p c flags eff m m' evs h
      · simp only [hun, ↓reduceIte] at h ⊢
        cases (pure_iff _ i _ _).mp h
        exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  · simp only [hrm, ↓reduceIte] at h
    cases (unmodeled_iff _ _ _).mp h

/-- Rocq: `Namei.check_unlinkat_tmp_complete_unmodeled`. -/
theorem check_unlinkat_tmp_complete_unmodeled (i : SyscallInput) (n p c : path) (flags : word)
    (m : Model) (eff : SyscallEffect) (h : unlinkat_tmp_spec n p c flags m i m Unmodeled) :
    check_unlinkat_tmp n p c flags eff m = CheckUnmodeled := by
  unfold unlinkat_tmp_spec at h
  unfold check_unlinkat_tmp
  cases hrm : unlink_rmdir flags
  · simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hnm : NAME_MAX < n.length
    · simp only [hnm, ↓reduceIte]
    · simp only [hnm, ↓reduceIte] at h ⊢
      cases hun : fs_under (m_fs m) c
      · simp only [hun, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hfs : fs_lookup (m_fs m) c with
        | none =>
          simp only [hfs] at h
          cases (pure_iff _ i _ _).mp h
        | some data =>
          simp only [hfs] at h
          exact check_unlink_found_complete_unmodeled i p c flags m eff h
      · simp only [hun, ↓reduceIte] at h
        cases (pure_iff _ i _ _).mp h
  · simp only [↓reduceIte]

/-- Rocq: `Namei.check_unlinkat_body_complete_ok`. -/
theorem check_unlinkat_body_complete_ok (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : unlinkat_body_spec dirfd pathp flags i m i m (Ok eff m' evs)) :
    check_unlinkat_body i dirfd pathp flags eff m = CheckOk m' evs := by
  unfold unlinkat_body_spec at h
  unfold check_unlinkat_body
  cases hp : read_cstr i.in_mem pathp with
  | CstrTooLong =>
    simp only [hp] at h
    cases (pure_iff _ i _ _).mp h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | CstrFault =>
    simp only [hp] at h
    cases (pure_iff _ i _ _).mp h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | CstrOk p =>
    simp only [hp] at h
    dsimp only
    cases hpe : path_eqb p []
    · simp only [hpe, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hd : bv_eqb dirfd AT_FDCWD32
      · simp only [hd, Bool.not_false, ↓reduceIte] at h
        cases (unmodeled_iff _ _ _).mp h
      · simp only [hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hroot : path_eqb (path_strip_trailing_slashes p) []
        · simp only [hroot, Bool.false_eq_true, ↓reduceIte] at h ⊢
          cases hsl : path_has_slash (path_strip_trailing_slashes p)
          · simp only [hsl, Bool.false_eq_true, ↓reduceIte] at h ⊢
            cases hdot : path_eqb (path_strip_trailing_slashes p) dot_path
            · simp only [hdot, Bool.false_eq_true, ↓reduceIte] at h ⊢
              cases hdd : path_eqb (path_strip_trailing_slashes p) dotdot_path
              · simp only [hdd, Bool.false_eq_true, ↓reduceIte] at h ⊢
                by_cases hnm : NAME_MAX < (path_strip_trailing_slashes p).length
                · simp only [hnm, ↓reduceIte] at h
                  cases (unmodeled_iff _ _ _).mp h
                · simp only [hnm, ↓reduceIte] at h ⊢
                  cases hun : fs_under (m_fs m) (path_strip_trailing_slashes p)
                  · simp only [hun, Bool.false_eq_true, ↓reduceIte] at h ⊢
                    cases hfs : fs_lookup (m_fs m) (path_strip_trailing_slashes p) with
                    | none =>
                      simp only [hfs] at h
                      cases (pure_iff _ i _ _).mp h
                      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
                    | some data =>
                      simp only [hfs] at h
                      exact check_unlink_found_complete_ok i p _ flags eff m m' evs h
                  · simp only [hun, ↓reduceIte] at h
                    cases (unmodeled_iff _ _ _).mp h
              · simp only [hdd, ↓reduceIte] at h ⊢
                cases hrm : unlink_rmdir flags
                · simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h ⊢
                  cases (pure_iff _ i _ _).mp h
                  exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
                · simp only [hrm, ↓reduceIte] at h ⊢
                  cases (pure_iff _ i _ _).mp h
                  exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
            · simp only [hdot, ↓reduceIte] at h ⊢
              cases hrm : unlink_rmdir flags
              · simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h ⊢
                cases (pure_iff _ i _ _).mp h
                exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
              · simp only [hrm, ↓reduceIte] at h ⊢
                cases (pure_iff _ i _ _).mp h
                exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
          · simp only [hsl, ↓reduceIte] at h ⊢
            cases htn : tmp_name (path_strip_trailing_slashes p) with
            | none =>
              simp only [htn] at h
              cases (unmodeled_iff _ _ _).mp h
            | some n =>
              simp only [htn] at h
              exact check_unlinkat_tmp_complete_ok i n p _ flags eff m m' evs h
        · simp only [hroot, ↓reduceIte] at h ⊢
          cases hrm : unlink_rmdir flags
          · simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h ⊢
            cases (pure_iff _ i _ _).mp h
            exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
          · simp only [hrm, ↓reduceIte] at h ⊢
            cases (pure_iff _ i _ _).mp h
            exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    · simp only [hpe, ↓reduceIte] at h ⊢
      cases (pure_iff _ i _ _).mp h
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- Rocq: `Namei.check_unlinkat_body_complete_unmodeled`. -/
theorem check_unlinkat_body_complete_unmodeled (i : SyscallInput) (dirfd pathp flags : word)
    (m : Model) (eff : SyscallEffect) (h : unlinkat_body_spec dirfd pathp flags i m i m Unmodeled) :
    check_unlinkat_body i dirfd pathp flags eff m = CheckUnmodeled := by
  unfold unlinkat_body_spec at h
  unfold check_unlinkat_body
  cases hp : read_cstr i.in_mem pathp with
  | CstrTooLong =>
    simp only [hp] at h
    cases (pure_iff _ i _ _).mp h
  | CstrFault =>
    simp only [hp] at h
    cases (pure_iff _ i _ _).mp h
  | CstrOk p =>
    simp only [hp] at h
    dsimp only
    cases hpe : path_eqb p []
    · simp only [hpe, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hd : bv_eqb dirfd AT_FDCWD32
      · simp only [Bool.not_false, ↓reduceIte]
      · simp only [hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hroot : path_eqb (path_strip_trailing_slashes p) []
        · simp only [hroot, Bool.false_eq_true, ↓reduceIte] at h ⊢
          cases hsl : path_has_slash (path_strip_trailing_slashes p)
          · simp only [hsl, Bool.false_eq_true, ↓reduceIte] at h ⊢
            cases hdot : path_eqb (path_strip_trailing_slashes p) dot_path
            · simp only [hdot, Bool.false_eq_true, ↓reduceIte] at h ⊢
              cases hdd : path_eqb (path_strip_trailing_slashes p) dotdot_path
              · simp only [hdd, Bool.false_eq_true, ↓reduceIte] at h ⊢
                by_cases hnm : NAME_MAX < (path_strip_trailing_slashes p).length
                · simp only [hnm, ↓reduceIte]
                · simp only [hnm, ↓reduceIte] at h ⊢
                  cases hun : fs_under (m_fs m) (path_strip_trailing_slashes p)
                  · simp only [hun, Bool.false_eq_true, ↓reduceIte] at h ⊢
                    cases hfs : fs_lookup (m_fs m) (path_strip_trailing_slashes p) with
                    | none =>
                      simp only [hfs] at h
                      cases (pure_iff _ i _ _).mp h
                    | some data =>
                      simp only [hfs] at h
                      exact check_unlink_found_complete_unmodeled i p _ flags m eff h
                  · simp only [hun, ↓reduceIte]
              · simp only [hdd, ↓reduceIte] at h
                cases hrm : unlink_rmdir flags
                · simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h
                  cases (pure_iff _ i _ _).mp h
                · simp only [hrm, ↓reduceIte] at h
                  cases (pure_iff _ i _ _).mp h
            · simp only [hdot, ↓reduceIte] at h
              cases hrm : unlink_rmdir flags
              · simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h
                cases (pure_iff _ i _ _).mp h
              · simp only [hrm, ↓reduceIte] at h
                cases (pure_iff _ i _ _).mp h
          · simp only [hsl, ↓reduceIte] at h ⊢
            cases htn : tmp_name (path_strip_trailing_slashes p) with
            | none => rfl
            | some n =>
              simp only [htn] at h
              exact check_unlinkat_tmp_complete_unmodeled i n p _ flags m eff h
        · simp only [hroot, ↓reduceIte] at h
          cases hrm : unlink_rmdir flags
          · simp only [hrm, Bool.false_eq_true, ↓reduceIte] at h
            cases (pure_iff _ i _ _).mp h
          · simp only [hrm, ↓reduceIte] at h
            cases (pure_iff _ i _ _).mp h
    · simp only [hpe, ↓reduceIte] at h
      cases (pure_iff _ i _ _).mp h

/-! ## The four exports

Each is the body lemma above with the flag arm in front and the pathname
copy-in threaded, exactly as the openat checker's four are.  The flag arm
carries no copy-in: the kernel decides it before `getname`. -/

/-- Rocq: `Namei.check_unlinkat_sound_ok`. -/
theorem check_unlinkat_sound_ok (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_unlinkat i dirfd pathp flags eff m = CheckOk m' evs) :
    unlinkat_spec dirfd pathp flags i m (Ok eff m' evs) := by
  unfold check_unlinkat at h
  unfold unlinkat_spec
  cases hfl : modeled_unlink_flags flags
  · simp only [hfl, Bool.not_false, ↓reduceIte] at h ⊢
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    ul_open
    exact pure_ok _ i _
  · simp only [hfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    rw [check_copyins_after_ok_iff] at h
    obtain ⟨hreads, hbody⟩ := h
    ul_open
    exact record_copyins_clear_ok _ _ _ _ _ _ _ hreads
      (check_unlinkat_body_sound_ok i dirfd pathp flags _ m m' evs hbody)

/-- Rocq: `Namei.check_unlinkat_sound_unmodeled`. -/
theorem check_unlinkat_sound_unmodeled (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m : Model) (h : check_unlinkat i dirfd pathp flags eff m = CheckUnmodeled) :
    unlinkat_spec dirfd pathp flags i m Unmodeled := by
  unfold check_unlinkat at h
  unfold unlinkat_spec
  cases hfl : modeled_unlink_flags flags
  · simp only [hfl, Bool.not_false, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  · simp only [hfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    ul_open_u
    exact record_copyins_unmodeled _ _ _ _
      (check_unlinkat_body_sound_unmodeled i dirfd pathp flags _ m
        (check_copyins_after_unmodeled _ _ _ h))

/-- Rocq: `Namei.check_unlinkat_complete_ok`. -/
theorem check_unlinkat_complete_ok (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : unlinkat_spec dirfd pathp flags i m (Ok eff m' evs)) :
    check_unlinkat i dirfd pathp flags eff m = CheckOk m' evs := by
  unfold unlinkat_spec at h
  have h2 := get_model_bind_ok_inv _ i m eff m' evs (input_bind_ok_inv _ i m eff m' evs h)
  unfold check_unlinkat
  cases hfl : modeled_unlink_flags flags
  · simp only [hfl, Bool.not_false, ↓reduceIte] at h2 ⊢
    cases (pure_iff _ i _ _).mp h2
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  · simp only [hfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h2 ⊢
    obtain ⟨core, hcore, heff⟩ := record_copyins_ok_inv _ _ i m eff m' evs h2
    have hbody := check_unlinkat_body_complete_ok i dirfd pathp flags core m m' evs hcore
    have hnil := check_unlinkat_body_ok_copyins_nil i dirfd pathp flags core m m' evs hbody
    obtain ⟨ret, ws, zs, us, cs, cis⟩ := core
    dsimp only at hnil
    subst hnil
    subst heff
    exact (check_copyins_after_ok_iff _ _ _ _ _).mpr ⟨rfl, hbody⟩

/-- Rocq: `Namei.check_unlinkat_complete_unmodeled`. -/
theorem check_unlinkat_complete_unmodeled (i : SyscallInput) (dirfd pathp flags : word)
    (m : Model) (eff : SyscallEffect) (h : unlinkat_spec dirfd pathp flags i m Unmodeled) :
    check_unlinkat i dirfd pathp flags eff m = CheckUnmodeled := by
  unfold unlinkat_spec at h
  have h2 := get_model_bind_unmodeled_inv _ i m (input_bind_unmodeled_inv _ i m h)
  unfold check_unlinkat
  cases hfl : modeled_unlink_flags flags
  · simp only [hfl, Bool.not_false, ↓reduceIte] at h2
    cases (pure_iff _ i _ _).mp h2
  · simp only [hfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h2 ⊢
    simp only [check_copyins_after,
      check_unlinkat_body_complete_unmodeled i dirfd pathp flags m (clear_copyins eff)
        (record_copyins_unmodeled_inv _ _ i m h2)]

/-! ## Receptiveness: the witness is an outcome the spec admits -/

/-- Rocq: `Witness.Fs.Namei.unlink_found_witness_ok`. -/
theorem unlink_found_witness_ok (p c : path) (flags : word) (i : SyscallInput) (m : Model) :
    unlink_found_spec p c flags m i m (unlink_found_witness p c flags m) := by
  unfold unlink_found_spec unlink_found_witness
  cases unlink_rmdir flags
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases path_trailing_slash p
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases fd_names_path (m_fds m) c
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact alt_l _ _ i m _
          (bind_step _ _ i m _ _ _ (errno_head_witness _ _ i m) (pure_ok _ i _))
      · simp only [↓reduceIte]
        exact unmodeled_intro i m
    · simp only [↓reduceIte]
      exact pure_ok _ i _
  · simp only [↓reduceIte]
    exact pure_ok _ i _

/-- Rocq: `Witness.Fs.Namei.unlinkat_tmp_witness_ok`. -/
theorem unlinkat_tmp_witness_ok (n p c : path) (flags : word) (i : SyscallInput) (m : Model) :
    unlinkat_tmp_spec n p c flags m i m (unlinkat_tmp_witness n p c flags m) := by
  unfold unlinkat_tmp_spec unlinkat_tmp_witness
  cases unlink_rmdir flags
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hnm : NAME_MAX < n.length
    · simp only [hnm, ↓reduceIte]
      exact unmodeled_intro i m
    · simp only [hnm, ↓reduceIte]
      cases fs_under (m_fs m) c
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases fs_lookup (m_fs m) c
        · exact pure_ok _ i _
        · exact unlink_found_witness_ok p c flags i m
      · simp only [↓reduceIte]
        exact pure_ok _ i _
  · simp only [↓reduceIte]
    exact unmodeled_intro i m

/-- Rocq: `Witness.Fs.Namei.unlinkat_body_witness_ok`.  Both sides read the
same guards in the same order, so one `cases` settles each; the body
opens no binds, which is what `unlinkat_witness_ok` peels instead. -/
theorem unlinkat_body_witness_ok (dirfd pathp flags : word) (i : SyscallInput) (m : Model) :
    unlinkat_body_spec dirfd pathp flags i m i m (unlinkat_body_witness dirfd pathp flags i m) := by
  unfold unlinkat_body_spec unlinkat_body_witness
  cases read_cstr i.in_mem pathp with
  | CstrTooLong => exact pure_ok _ i _
  | CstrFault => exact pure_ok _ i _
  | CstrOk p =>
    dsimp only
    cases path_eqb p []
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases bv_eqb dirfd AT_FDCWD32
      · simp only [Bool.not_false, ↓reduceIte]
        exact unmodeled_intro i m
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases path_eqb (path_strip_trailing_slashes p) []
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases path_has_slash (path_strip_trailing_slashes p)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            cases path_eqb (path_strip_trailing_slashes p) dot_path
            · simp only [Bool.false_eq_true, ↓reduceIte]
              cases path_eqb (path_strip_trailing_slashes p) dotdot_path
              · simp only [Bool.false_eq_true, ↓reduceIte]
                by_cases hnm : NAME_MAX < (path_strip_trailing_slashes p).length
                · simp only [hnm, ↓reduceIte]
                  exact unmodeled_intro i m
                · simp only [hnm, ↓reduceIte]
                  cases fs_under (m_fs m) (path_strip_trailing_slashes p)
                  · simp only [Bool.false_eq_true, ↓reduceIte]
                    cases fs_lookup (m_fs m) (path_strip_trailing_slashes p)
                    · exact pure_ok _ i _
                    · exact unlink_found_witness_ok p _ flags i m
                  · simp only [↓reduceIte]
                    exact unmodeled_intro i m
              · simp only [↓reduceIte]
                cases unlink_rmdir flags
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  exact pure_ok _ i _
                · simp only [↓reduceIte]
                  exact pure_ok _ i _
            · simp only [↓reduceIte]
              cases unlink_rmdir flags
              · simp only [Bool.false_eq_true, ↓reduceIte]
                exact pure_ok _ i _
              · simp only [↓reduceIte]
                exact pure_ok _ i _
          · simp only [↓reduceIte]
            cases tmp_name (path_strip_trailing_slashes p)
            · exact unmodeled_intro i m
            · exact unlinkat_tmp_witness_ok _ p _ flags i m
        · simp only [↓reduceIte]
          cases unlink_rmdir flags
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact pure_ok _ i _
          · simp only [↓reduceIte]
            exact pure_ok _ i _
    · simp only [↓reduceIte]
      exact pure_ok _ i _

/-- Rocq: `Witness.Fs.Namei.unlinkat_witness_ok`. -/
theorem unlinkat_witness_ok (dirfd pathp flags : word) (i : SyscallInput) (m : Model) :
    unlinkat_spec dirfd pathp flags i m (unlinkat_witness dirfd pathp flags i m) := by
  unfold unlinkat_spec unlinkat_witness
  refine bind_step _ _ i m _ _ _ (input_ok i m) ?_
  refine bind_step _ _ i m _ _ _ (get_model_ok i m) ?_
  cases modeled_unlink_flags flags
  · simp only [Bool.not_false, ↓reduceIte]
    exact pure_ok _ i _
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact record_copyins_outcome _ _ _ _ _ (unlinkat_body_witness_ok dirfd pathp flags i m)

/-! ## The frames -/

/-- The checker never moves the VM ledger: every accepting arm is a
`check_ret_only`, which hands the model straight back, or
`check_unlink_result`, whose one change
is `with_fs`.  Rocq:
`VmMapsDisjoint.check_unlinkat_frame`, closed there by `vm_frame2`; here
the body's half comes from `check_unlinkat_body_ok_inv`, since `split` on
the unfolded checker exhausts simp's step budget.  Lifted to the arm as
`arm_unlinkat_preserves_vm` in `Checks/VmMapsDisjoint/Arms.lean` by the
registration step. -/
theorem check_unlinkat_frame (i : SyscallInput) (dirfd pathp flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_unlinkat i dirfd pathp flags eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_unlinkat at h
  cases hfl : modeled_unlink_flags flags
  · simp only [hfl, Bool.not_false, ↓reduceIte] at h
    rw [check_ret_only_ok_iff] at h
    obtain ⟨-, rfl, -⟩ := h
    rfl
  · simp only [hfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    rw [check_copyins_after_ok_iff] at h
    exact (check_unlinkat_body_ok_inv i dirfd pathp flags _ m m' evs h.2).2.1

/-- Nor does it move the descriptor subsystem: the one change an accepting
arm makes is `with_fs`, which rebuilds the model around a new file table
and hands `m_fd` back as it was.  Lean-only, the third conjunct of the
`*_ok_inv` lemmas lifted through the flag gate exactly as
`check_unlinkat_frame` lifts the second.  Once the arm is registered,
`Checks/Invariants.lean` draws `fd_table_unique_arm_unlinkat` and
`pipes_within_capacity_arm_unlinkat` from it through
`arm_preserves_of_view_frame`, as it draws the `exit` and
`mmap` pairs from `check_exit_fd_state_frame` and
`check_mmap_fd_state_frame`; the registry's header says a checker's
descriptor frame belongs beside the checker, which is why this one is
here and not there. -/
theorem check_unlinkat_fd_state_frame (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_unlinkat i dirfd pathp flags eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  unfold check_unlinkat at h
  cases hfl : modeled_unlink_flags flags
  · simp only [hfl, Bool.not_false, ↓reduceIte] at h
    rw [check_ret_only_ok_iff] at h
    obtain ⟨-, rfl, -⟩ := h
    rfl
  · simp only [hfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    rw [check_copyins_after_ok_iff] at h
    exact (check_unlinkat_body_ok_inv i dirfd pathp flags _ m m' evs h.2).2.2

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Namei
