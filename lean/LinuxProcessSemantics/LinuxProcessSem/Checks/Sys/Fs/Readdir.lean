-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Sys/Fs/Readdir.v
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Readdir
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058 -/

/-! # LinuxProcessSem.Checks.Sys.Fs.Readdir — the getdents64 (61) checker, its witness, and their proofs

Mirrors `theories/LinuxProcessSem/Checks/Sys/Fs/Readdir.v` — the checker
and the four lemmas relating it to `Sys/Fs/Readdir.lean`'s
`getdents64_spec` — AND `theories/LinuxProcessSem/Checks/Witness/Fs/Readdir.v`,
the witness and its `*_ok` lemma.  Rocq keeps the two in separate files
because `Checks/ExecutableSpecs.v` re-exports the one and
`Checks/Progress.v` the other; here the `CheckedArm` the registration
builds over this file wants both at once — the checker, the witness and
the proofs below are the fields of one record — so they are one module.
A reader looking for the Rocq
`Checks/Witness/Fs/Readdir.v` twin finds it in the last section of this
file.  Not part of the trusted specification: the spec is
`Sys/Fs/Readdir.lean`, and everything here is judged against it.

WHAT IS NOT HERE, AND WHOSE IT IS.  Rocq builds `arm_getdents64` and lists
it in `checked_table` (`Checks/Sys/Dispatch.v`), registers the `arm_unfold`
equations (`ca_check_arm_getdents64`, `ca_witness_arm_getdents64`,
`sa_spec_arm_getdents64` and `ca_no_arm_getdents64`), and names
`check_getdents64_frame` in the alternation of `Checks/VmMapsDisjoint.v`.  In the Lean port those are the registration
step of the conformance ticket for this arm, not this file's: the checker
lands on the preludes
and the spec alone, and the checked table's row, its `arm_unfold` lemmas
and the ledger's per-arm alternative are written when the arm is
registered.  The frame lemma itself IS here, in the last section, as
`Sync`, `Pipe`, `Select` and most checker files of this tree state theirs
— `Open`, `Stat` and `Timerfd` leave it to the registration, and say so:
it is about the checker alone, and the registration's `arm_preserves_vm`
is `arm_preserves_of_frame` applied to it.

Every definition keeps the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function, and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f) throughout; of the Rocq
files, the spec `Sys/Fs/Readdir.v` cites the same functions at the same
version and no line numbers, and the three this file mirrors name the
functions and no version.

EVERY REGULAR FILE IS -ENOTDIR here, `FdFileA` and `FdFileRW` with
`FdFile` and `FdFileW` (`Sys/Fs/Readdir.lean`, module header), so the
only decline is the directory arm's roomy half.

THE PROOFS take the same route as Rocq's but spell the steps Rocq's
`inv_ok` and `sys_unfold` take in one word: `bind_get_model_iff` for the
`get_model` bind, a case split on `fd_lookup`, and on the directory arm a
case split on `getdents64_no_room count` and on the effect's five ledgers.
Five small lemmas — `err_ret_of_check_ret_only`, `err_ret_ok_inv`,
`check_ret_only_of_err_ret`, `err_ret_no_unmodeled` and
`ret_outcome_ok_inv` — carry the plain-return arms in both directions;
Rocq spells the same steps once, under `try`, over every plain-return
goal at a time (`try (apply check_ret_only_ok_iff in H; destruct H as
(-> & -> & ->); apply pure_ok)` in its soundness lemma).  They are stated
here rather than in `Checks/Sys/Prelude.lean` because that file is frozen
(the brief's list).  They are not the tree's first copies: `err_ret e` is
`ret_only (errno_ret e)` by definition, and
`Checks/Sys/Kernel/Futex/Syscalls.lean` states the first, third and fourth
on `ret_only` (`ret_only_of_check_ret_only`, `check_ret_only_of_ret_only`,
`ret_only_not_unmodeled`); `check_ret_only_frame` in the last section is
`Checks/VmMapsDisjoint.lean`'s `check_ret_only_model` read through
`m_vmmaps`.  They are restated under the `err_ret` spelling this file's
proofs read them by, and the next checker with a plain-return arm can
import either copy.

ONE REDUCTION IS AVOIDED ON PURPOSE in every proof here.  Reducing
`getdents64_no_room count` with `count` symbolic exhausts `maxRecDepth`
(Lean v4.34.0; still under `set_option maxRecDepth 20000`): the gate
reads `count` through `sint32` and `Int.decLt`, whose `Int.subNatNat`
subtracts the literal 2147483648, and `Nat.sub` recurses on that second
argument once the first is stuck on the free variable.  A CLOSED `count`
wedges the unifier the same way, for the reason
`Checks/Cases/Checks/Sys/Kernel/Time/PosixTimers.lean`'s header states
and pins: `isDefEq` reduces each side with `whnfCore` under the
projection setting `.yesWithDeltaI`, under which `BitVec.toNat` of a
word built by an ordinary definition is a stuck projection, so the
literal never folds and `getdents64_no_room 23 = true := rfl` fails like
the symbolic case.  `Meta.whnf` under the default setting folds it:
`decide` proves `getdents64_no_room 23 = true` at once, `conv => lhs;
whnf` closes the same goal, and under `set_option
backward.isDefEq.lazyWhnfCore false`, the option that selects the
projection setting, the plain `rfl` closes too — pinned at the end of
`Checks/Cases/Checks/Sys/Fs/Readdir.lean`.  Two earlier drafts here
blamed a transparency drop in `Lean.Meta.whnfMatcher` and then
`Meta.whnf` itself; scratch compiles refuted both, and nothing below
rests on the reason.  So no step here may hand that term to the unifier,
or a symbolic one to `whnf`:

- once the fd lookup is known, no hypothesis is re-introduced as a
  binder: `revert` then `intro h` met the limit in
  `Lean.Linter.constructorNameAsVariable`, which runs `whnf` on every
  binder's type, where the theorems' own `(h : getdents64_spec …)`
  binders, their lookup still symbolic, do not.  So the completeness
  proofs split with `cases hfd : fd_lookup (m_fds m) fd` and `rw [hfd] at
  h`, which rewrite in place, and read a plain-return outcome through
  `err_ret_ok_inv` rather than `injection`, which met the limit in that
  context; the witness-acceptance proof in
  `Checks/Cases/Checks/Sys/Fs/Readdir.lean` reads the witness's
  `ret_outcome` through `ret_outcome_ok_inv` for the same reason — that
  lemma's docstring says what is pinned about it;
- the gate is only ever case-split, `cases hroom : getdents64_no_room
  count`, never unified against;
- the frame lemma at the end of this file takes the directory arm apart
  with `split at h`, which generalises a condition without reducing it,
  and uses `cases h` only on constructor-headed equations; `vm_step`, the
  macro of `Checks/VmMapsDisjoint.lean` that `vm_frame` repeats, opens
  with `cases h`, which unifies the `ite` — and a `maxRecDepth` failure
  is a runtime exception
  that `first` and `try` do not catch — so the registration derives its
  `arm_preserves_vm` from the lemma here rather than re-proving it with
  the macro;
- the closed pins in `Checks/Cases/Checks/Sys/Fs/Readdir.lean` rewrite the
  gate with a `decide`-proved equation before `rfl`.

A hypothesis whose type is an `Eq` — the soundness direction's
`check_getdents64 … = CheckOk …` — is safe to revert and intro: the
linter's whnf stops at `Eq`. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Readdir

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Readdir
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! ## The plain-return arms, in both directions

`err_ret e` admits exactly one outcome, `Ok (mkEffect (errno_ret e) [] []) m []`,
and `check_ret_only eff (errno_ret e) m []` accepts exactly that effect on
exactly that model with no events (`Checks/Sys/Prelude.lean`'s
`check_ret_only_ok_iff`).  The three lemmas below are that fact read as
soundness, as completeness, and as "never declines"; beside them,
`err_ret_ok_inv` and `ret_outcome_ok_inv` read one `Ok` off, on the spec's
side and on the witness's. -/

/-- Soundness of a plain-return arm: what `check_ret_only` accepts for
`-e`, `err_ret e` admits.  Rocq inlines this as
`apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->); apply pure_ok`. -/
theorem err_ret_of_check_ret_only (e : Int) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_ret_only eff (errno_ret e) m [] = CheckOk m' evs) :
    err_ret e i m (Ok eff m' evs) := by
  rw [check_ret_only_ok_iff] at h
  obtain ⟨heff, hm', hevs⟩ := h
  subst heff hm' hevs
  exact pure_ok _ i _

/-- What `err_ret e` admits, read off: the effect is the bare return, the
model is unchanged, no event.  Rocq's `inv_ok` does this in place; here it
is a lemma because it is used where `injection` cannot be — see
`check_getdents64_complete_ok`.  The `have h' : … := h` restates
`err_ret`'s outcome as the constructor equation `pure` unfolds to, so the
`injection` after it sees two constructor applications and nothing of
`err_ret`. -/
theorem err_ret_ok_inv (e : Int) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (h : err_ret e i m (Ok eff m' evs)) :
    eff = mkEffect (errno_ret e) [] [] ∧ m' = m ∧ evs = [] := by
  have h' : Ok eff m' evs = Ok (mkEffect (errno_ret e) [] []) m [] := h
  injection h' with heff hm' hevs
  exact ⟨heff, hm', hevs⟩

/-- What `ret_outcome r m` is, read off: the bare return `r`, the model
unchanged, no event — `err_ret_ok_inv` for the witness's side of the same
outcome.  It is a lemma for the same reason.  The witness-acceptance proof
in `Checks/Cases/Checks/Sys/Fs/Readdir.lean` needs this inversion on the
directory arm, and there an in-place `injection` on the equation exhausts
`maxRecDepth` while `hroom : getdents64_no_room count = true` is in the
context — `set_option diagnostics true` counts 114 `Nat.rec` unfoldings
before the limit — and goes through once that hypothesis is cleared
(scratch compiles, Lean 4.34.0).
Why the context matters to `injection` is not pinned; a standalone lemma
sidesteps the question. -/
theorem ret_outcome_ok_inv (r : word) (m : Model) (eff : SyscallEffect) (m' : Model)
    (evs : List event) (h : ret_outcome r m = Ok eff m' evs) :
    eff = mkEffect r [] [] ∧ m' = m ∧ evs = [] := by
  unfold ret_outcome at h
  injection h with heff hm' hevs
  exact ⟨heff.symm, hm'.symm, hevs.symm⟩

/-- Completeness of a plain-return arm: what `err_ret e` admits,
`check_ret_only` accepts for `-e`.  Rocq inlines this as `inv_ok;
cbn [check_ret_only]; rewrite bv_eqb_refl; reflexivity`. -/
theorem check_ret_only_of_err_ret (e : Int) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput) (h : err_ret e i m (Ok eff m' evs)) :
    check_ret_only eff (errno_ret e) m [] = CheckOk m' evs := by
  obtain ⟨heff, hm', hevs⟩ := err_ret_ok_inv e eff m m' evs i h
  subst heff hm' hevs
  exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- A plain-return arm never declines: `err_ret e` is a `pure`, and a
`pure` admits only `Ok`.  Rocq closes the same goal with `inv_ok`. -/
theorem err_ret_no_unmodeled (e : Int) (i : SyscallInput) (m : Model)
    (h : err_ret e i m Unmodeled) : False := by
  have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (errno_ret e) [] []) m [] := h
  cases h'

/-! ## The checker -/

/-- `getdents64` (61): -EBADF on a closed fd, -ENOTDIR on every fd that is
not a directory, and on a directory fd either -EINVAL or the one
injectable errno when the buffer cannot hold the smallest possible entry.
Every larger buffer on a directory fd is `CheckUnmodeled`.  Mirrors
`Sys.Fs.Readdir.getdents64_spec` arm for arm — read that spec for why the
listing itself is declined, and why the `dirent` pointer is not an
argument here either.

The three answers, where the kernel decides each (fs/readdir.c, Linux
v6.18.46):

- -EBADF: `getdents64` (fs/readdir.c:409-410) returns it when
  `fd_empty(f)` holds of the `CLASS(fd_pos, f)(fd)` lookup (fs/readdir.c:400),
  before `iterate_dir` is called (fs/readdir.c:412) — so before any
  property of the file is read;
- -ENOTDIR: `iterate_dir` (fs/readdir.c:88-91, Linux v6.18.46) starts from
  `res = -ENOTDIR` and jumps to `out` when `file->f_op->iterate_shared` is
  NULL, which it is for every file kind the model holds other than a
  directory (the spec's per-arm comments name the ops tables);
- -EINVAL or the injected -ENOENT: `iterate_dir` (fs/readdir.c:105-106,
  Linux v6.18.46) answers -ENOENT for a removed directory before calling `.iterate_shared`
  (fs/readdir.c:108); otherwise the filesystem's first emission —
  `dir_emit_dot`'s `.` (include/linux/fs.h:4016-4020, Linux v6.18.46) on
  the filesystems the spec twin names — reaches
  `filldir64` (fs/readdir.c:349-368, Linux v6.18.46), which sets
  `buf->error = -EINVAL`
  and returns `false` when `reclen > ctx->count` — `reclen` at its floor
  being `dirent64_min_reclen`, and `ctx->count` the `int` the spec reads
  through `getdents64_ctx_count`.  `getdents64` then hands `buf.error` back
  (fs/readdir.c:413-414, Linux v6.18.46).  The two permission tests between
  the -ENOTDIR and the -ENOENT — `security_file_permission`
  (security/security.c:2944, Linux v6.18.46) and `fsnotify_file_perm`
  (include/linux/fsnotify.h:204, Linux v6.18.46), called at fs/readdir.c:93
  and 97 — are the spec twin's declared narrowing
  (linux-process-semantics@ff0313ba4f:bugs/getdents64-lsm-and-fanotify-denials-not-admitted.md),
  which this checker inherits: their -EACCES and -EPERM are refused, not
  admitted.

All the admitted answers are a bare return with FIVE EMPTY LEDGERS: the
kernel reaches `user_write_access_begin` (the `user_access_begin` alias of
include/linux/uaccess.h:568-569, Linux v6.18.46; the call is
fs/readdir.c:374) only once the `reclen > ctx->count` test
(fs/readdir.c:367-368, Linux v6.18.46) has let the entry through, and
every answer this spec admits failed the call at or before that test,
so none of them writes, zeroes, unmaps or copies a byte.  A
kernel that claimed a write alongside one of these returns is rejected on
the ledger rather than on the return value.  Rocq:
`Checks.Sys.Fs.Readdir.check_getdents64`. -/
def check_getdents64 (fd count : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdChannel _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | some (.FdFile _ _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | some (.FdFileW _ _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | some (.FdFileA _ _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | some (.FdFileRW _ _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | some (.FdPipe _ _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | some (.FdSocket _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | some (.FdDevNull _ _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | some .FdUrandom => check_ret_only eff (errno_ret ENOTDIR) m []
  | some .FdDir =>
      if getdents64_no_room count then
        match eff with
        | SyscallEffect.mkEffectU ret [] [] [] [] [] =>
            if errno_ret_in getdents64_errnos ret then CheckOk m []
            else if bv_eqb ret (errno_ret EINVAL) then CheckOk m []
            else CheckReject
        | _ => CheckReject
      else CheckUnmodeled

/-! ## Soundness and completeness against `getdents64_spec` -/

/-- Rocq: `Checks.Sys.Fs.Readdir.check_getdents64_sound_ok`. -/
theorem check_getdents64_sound_ok (fd count : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_getdents64 fd count eff m = CheckOk m' evs) :
    getdents64_spec fd count i m (Ok eff m' evs) := by
  unfold check_getdents64 at h
  unfold getdents64_spec
  rw [bind_get_model_iff]
  revert h
  cases fd_lookup (m_fds m) fd with
  | none =>
    intro h
    exact err_ret_of_check_ret_only EBADF eff m m' evs i h
  | some e =>
    cases e <;> intro h
    case FdDir =>
      cases hroom : getdents64_no_room count with
      | false =>
        -- the roomy half declines, so it accepts nothing
        simp only [hroom, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
      | true =>
        simp only [hroom, ↓reduceIte] at h ⊢
        -- the five ledgers must be empty: every other shape is rejected
        obtain ⟨ret, ws, zs, us, cs, cis⟩ := eff
        rcases ws with _ | ⟨_, _⟩ <;> rcases zs with _ | ⟨_, _⟩ <;>
          rcases us with _ | ⟨_, _⟩ <;> rcases cs with _ | ⟨_, _⟩ <;>
          rcases cis with _ | ⟨_, _⟩ <;>
          try (simp only [reduceCtorEq] at h; done)
        dsimp only at h
        cases he : errno_ret_in getdents64_errnos ret with
        | true =>
          -- the injected errno: the left arm of the `alt`
          simp only [he, ↓reduceIte, check_result.CheckOk.injEq] at h
          obtain ⟨hm', hevs⟩ := h
          subst hm' hevs
          rw [errno_ret_in_true] at he
          obtain ⟨e, hin, hret⟩ := he
          subst hret
          apply alt_l
          exact bind_ok0 (errno_from getdents64_errnos) (fun e => err_ret e) i m e m
            (mkEffect (errno_ret e) [] []) m []
            (choose_ok (fun e => e ∈ getdents64_errnos) e i m hin) (pure_ok _ i m)
        | false =>
          simp only [he, Bool.false_eq_true, ↓reduceIte] at h
          cases hq : bv_eqb ret (errno_ret EINVAL) with
          | true =>
            -- `filldir64`'s own -EINVAL: the right arm of the `alt`
            simp only [hq, ↓reduceIte, check_result.CheckOk.injEq] at h
            obtain ⟨hm', hevs⟩ := h
            subst hm' hevs
            rw [bv_eqb_eq] at hq
            subst hq
            apply alt_r
            exact pure_ok _ i m
          | false =>
            simp only [hq, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
    -- the nine non-directory kinds: each is a plain -ENOTDIR
    all_goals exact err_ret_of_check_ret_only ENOTDIR eff m m' evs i h

/-- The one decline is the directory arm's roomy half — the listing the
model cannot produce.  Inside the small-buffer half every effect shape is
either accepted or rejected, never declined, and so is every
non-directory fd, the append-mode and read-write files with the rest.
Rocq: `Checks.Sys.Fs.Readdir.check_getdents64_sound_unmodeled`. -/
theorem check_getdents64_sound_unmodeled (fd count : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_getdents64 fd count eff m = CheckUnmodeled) :
    getdents64_spec fd count i m Unmodeled := by
  unfold check_getdents64 at h
  unfold getdents64_spec
  rw [bind_get_model_iff]
  revert h
  cases fd_lookup (m_fds m) fd with
  | none =>
    intro h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | some e =>
    cases e <;> intro h
    case FdDir =>
      cases hroom : getdents64_no_room count with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact unmodeled_intro i m
      | true =>
        exfalso
        simp only [hroom, ↓reduceIte] at h
        obtain ⟨ret, ws, zs, us, cs, cis⟩ := eff
        rcases ws with _ | ⟨_, _⟩ <;> rcases zs with _ | ⟨_, _⟩ <;>
          rcases us with _ | ⟨_, _⟩ <;> rcases cs with _ | ⟨_, _⟩ <;>
          rcases cis with _ | ⟨_, _⟩ <;>
          try (simp only [reduceCtorEq] at h; done)
        dsimp only at h
        cases he : errno_ret_in getdents64_errnos ret with
        | true => simp only [he, ↓reduceIte, reduceCtorEq] at h
        | false =>
          simp only [he, Bool.false_eq_true, ↓reduceIte] at h
          cases hq : bv_eqb ret (errno_ret EINVAL) with
          | true => simp only [hq, ↓reduceIte, reduceCtorEq] at h
          | false => simp only [hq, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
    all_goals exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

/-- Rocq: `Checks.Sys.Fs.Readdir.check_getdents64_complete_ok`.  Rocq's
proof selects the directory arm by its INDEX among `FdEntry`'s
constructors and warns that the index moves with the type; here the arm
is selected by name (`case FdDir`), so a constructor added ahead of it
changes nothing in this proof. -/
theorem check_getdents64_complete_ok (fd count : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : getdents64_spec fd count i m (Ok eff m' evs)) :
    check_getdents64 fd count eff m = CheckOk m' evs := by
  unfold getdents64_spec at h
  rw [bind_get_model_iff] at h
  unfold check_getdents64
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    rw [hfd] at h
    exact check_ret_only_of_err_ret EBADF eff m m' evs i h
  | some e =>
    rw [hfd] at h
    cases e
    case FdDir =>
      cases hroom : getdents64_no_room count with
      | false =>
        -- the roomy half admits only `Unmodeled`, never an `Ok`
        simp only [hroom, Bool.false_eq_true, ↓reduceIte] at h
        rw [unmodeled_iff] at h
        cases h
      | true =>
        simp only [hroom, ↓reduceIte] at h ⊢
        rw [alt_iff] at h
        rcases h with h | h
        · -- the injected errno: `errno_from`'s `choose` names it
          unfold errno_from at h
          rw [bind_choose_iff] at h
          obtain ⟨e, hin, hk⟩ := h
          obtain ⟨heff, hm', hevs⟩ := err_ret_ok_inv e eff m m' evs i hk
          subst heff hm' hevs
          simp only [errno_ret_in_intro getdents64_errnos e hin, ↓reduceIte]
        · -- `filldir64`'s -EINVAL, which is not in the injectable set
          obtain ⟨heff, hm', hevs⟩ := err_ret_ok_inv EINVAL eff m m' evs i h
          subst heff hm' hevs
          have hne : errno_ret_in getdents64_errnos (errno_ret EINVAL) = false := by decide
          simp only [hne, Bool.false_eq_true, ↓reduceIte, bv_eqb_refl]
    all_goals exact check_ret_only_of_err_ret ENOTDIR eff m m' evs i h

/-- Rocq: `Checks.Sys.Fs.Readdir.check_getdents64_complete_unmodeled`.
Neither arm of the directory arm's `alt` can be `Unmodeled`: a `choose`
bound to a `pure` admits only `Ok`. -/
theorem check_getdents64_complete_unmodeled (fd count : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (h : getdents64_spec fd count i m Unmodeled) :
    check_getdents64 fd count eff m = CheckUnmodeled := by
  unfold getdents64_spec at h
  rw [bind_get_model_iff] at h
  unfold check_getdents64
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    rw [hfd] at h
    exact (err_ret_no_unmodeled EBADF i m h).elim
  | some e =>
    rw [hfd] at h
    cases e
    case FdDir =>
      cases hroom : getdents64_no_room count with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]
      | true =>
        exfalso
        simp only [hroom, ↓reduceIte] at h
        rw [alt_iff] at h
        rcases h with h | h
        · unfold errno_from at h
          rw [bind_choose_iff] at h
          obtain ⟨e, _, hk⟩ := h
          exact err_ret_no_unmodeled e i m hk
        · exact err_ret_no_unmodeled EINVAL i m h
    all_goals exact (err_ret_no_unmodeled ENOTDIR i m h).elim

/-! ## The witness — the `Checks/Witness/Fs/Readdir.v` twin

On the directory arm the witness takes -EINVAL rather than the injected
-ENOENT: it is the answer the model actually derives from `count`
(`filldir64`, fs/readdir.c:366-368, Linux v6.18.46), while a directory
removed out from under the fd (`iterate_dir`, fs/readdir.c:105-106) is a
condition no modeled state decides.  Above the small-buffer band, failing
closed is itself the admissible outcome. -/

/-- Rocq: `Checks.Witness.Fs.Readdir.getdents64_witness`. -/
def getdents64_witness (fd count : word) (m : Model) : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some (.FdChannel _) => ret_outcome (errno_ret ENOTDIR) m
  | some (.FdFile _ _) => ret_outcome (errno_ret ENOTDIR) m
  | some (.FdFileW _ _) => ret_outcome (errno_ret ENOTDIR) m
  | some (.FdFileA _ _) => ret_outcome (errno_ret ENOTDIR) m
  | some (.FdFileRW _ _) => ret_outcome (errno_ret ENOTDIR) m
  | some (.FdPipe _ _) => ret_outcome (errno_ret ENOTDIR) m
  | some (.FdSocket _) => ret_outcome (errno_ret ENOTDIR) m
  | some (.FdDevNull _ _) => ret_outcome (errno_ret ENOTDIR) m
  | some .FdUrandom => ret_outcome (errno_ret ENOTDIR) m
  | some .FdDir =>
      if getdents64_no_room count then ret_outcome (errno_ret EINVAL) m
      else Unmodeled

/-- Rocq: `Checks.Witness.Fs.Readdir.getdents64_witness_ok`. -/
theorem getdents64_witness_ok (fd count : word) (i : SyscallInput) (m : Model) :
    getdents64_spec fd count i m (getdents64_witness fd count m) := by
  unfold getdents64_spec getdents64_witness
  rw [bind_get_model_iff]
  cases fd_lookup (m_fds m) fd with
  | none => exact pure_ok _ i m
  | some e =>
    cases e
    case FdDir =>
      cases getdents64_no_room count with
      | true =>
        simp only [↓reduceIte]
        exact alt_r _ _ i m _ (pure_ok _ i m)
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact unmodeled_intro i m
    all_goals exact pure_ok _ i m

/-! ## The frame lemma

Rocq states `check_getdents64_frame` in `Checks/VmMapsDisjoint.v`, beside
the other arms' frame lemmas, where `check_syscall_preserves_vm_wf`
consumes it; here it sits with the checker it is about, as `Sync`, `Pipe`,
`Select` and most checker files of this tree place theirs, and the
registration's `arm_preserves_vm` is
`arm_preserves_of_frame` applied to it.  Every accepting answer of this
checker hands back the model it was given — the plain-return arms through
`check_ret_only`, the directory arm's two accepted returns as `CheckOk m []`
outright — and the kernel side of that is the checker's own note: nothing
an admitted `getdents64` answer does reaches the `user_write_access_begin`
of include/linux/uaccess.h:568-569 (called at fs/readdir.c:374, Linux
v6.18.46), let alone `mm`.

The directory arm is taken apart with `split at h`, which generalises a
condition without reducing it, and `cases h` is used only on
constructor-headed equations, for the reason the file header gives:
`vm_frame`'s first alternative would hand the gate to `whnf`. -/

/-- What `check_ret_only` accepts hands back the model it was given, read
on the VM ledger alone. -/
theorem check_ret_only_frame (eff : SyscallEffect) (r : word) (m m' : Model)
    (evs evs' : List event) (h : check_ret_only eff r m evs = CheckOk m' evs') :
    m_vmmaps m' = m_vmmaps m := by
  rw [check_ret_only_ok_iff] at h
  obtain ⟨-, rfl, -⟩ := h
  rfl

/-- An accepted `getdents64` leaves the VM ledger where it was.  Rocq:
`VmMapsDisjoint.check_getdents64_frame`. -/
theorem check_getdents64_frame (fd count : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_getdents64 fd count eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_getdents64 at h
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    rw [hfd] at h
    exact check_ret_only_frame _ _ _ _ _ _ h
  | some e =>
    rw [hfd] at h
    cases e
    case FdDir =>
      dsimp only at h
      split at h
      · split at h
        · split at h
          · cases h; rfl
          · split at h
            · cases h; rfl
            · cases h
        · cases h
      · cases h
    all_goals exact check_ret_only_frame _ _ _ _ _ _ h

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Readdir
