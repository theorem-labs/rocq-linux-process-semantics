import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Sync

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Fs.Sync — the fsync (82), fdatasync (83) checker, witness, and their proofs

Mirrors two Rocq files at once: `theories/LinuxProcessSem/Checks/Sys/Fs/Sync.v`,
which holds the checker for the syscalls `Sys/Fs/Sync.v` defines, and no
others — the executable acceptor `check_fsync`, and the four lemmas relating
it to the relational `fsync_spec` of `Sys/Fs/Sync.lean` — and
`theories/LinuxProcessSem/Checks/Witness/Fs/Sync.v`, the progress witness
`fsync_witness` with `fsync_witness_ok`, one outcome the spec admits at
every fd and model.  The checker is the computable side of the spec and is
NOT part of the trusted specification; what a run may trust is the spec,
and these lemmas are what lets a verdict of the checker stand for an answer
of the spec.  Its pins are `Checks/Cases/Checks/Sys/Fs/Sync.lean`.

THE BASELINE NAMED ABOVE is the commit all three Rocq files — the two
mirrored here and the spec's — were read at and the last one to touch
them, and it is the commit the spec twin `Sys/Fs/Sync.lean` names.  The
port plan's baseline, `f44244ad`, is not an ancestor of this history and
predates the `FdUrandom` arm the Rocq files gained with the /dev/urandom
descriptor; the checker and the witness below carry that arm, so the
header names the commit they were actually read at rather than one that
lacks it.

The FdFileRW and FdFileA declines follow the spec twin's declared narrowing
(`Sys/Fs/Sync.lean`, module header).

WHAT THIS FILE HOLDS, AND WHAT WAITS.  The checker, its four lemmas, the
witness with its proof and the frame lemma need only the two preludes and
the spec, and are here.  The rest of the Rocq surface for this syscall is
the registration step of the ticket that adds the arms, and cannot be here:

- the arms `arm_fsync` and `arm_fdatasync`, their `checked_table` rows and
  their `arm_unfold` lemmas are `CheckedArm` values (`Checks/Sys/Dispatch.v`;
  the Lean record is `Checks/Sys/Dispatch.lean`'s) and go in
  `Checks/Sys/Table.lean` when the V ticket registers them; that file
  imports each checker it registers, so a checker's file cannot see its
  own arm;
- the ledger facts the VM invariant's alternation consumes are, in the
  Lean shape, one `arm_<name>_preserves_vm` theorem per arm and one
  alternative per theorem, beside the alternation in
  `Checks/VmMapsDisjoint/Arms.lean` (Rocq's alternation names
  `check_fsync_frame` directly, `Checks/VmMapsDisjoint.v`).  That file
  imports the table, which imports this file, so importing it back is a
  cycle.  They are DERIVED from `check_fsync_frame` below, not re-proved.

The frame lemma is stated here, ahead of the registration that consumes
it, because it depends on nothing but `check_fsync`, and a lemma provable
where its subject is defined should not wait on a file that cannot import
it.  The C ticket's acceptance text assigns it to the registration step;
this file states it where `Checks/Sys/Kernel/Exit.lean` and
`Checks/Sys/Mm/Madvise.lean` state theirs.

THE PROOFS keep Rocq's shape.  Every arm but the read-write and append-mode
files' is a `check_ret_only`, so each direction is the lookup split —
`none`, then one case per constructor — and one prelude lemma per arm:
`check_ret_only_ok_iff` for the two `Ok` directions,
`check_ret_only_no_unmodeled` where the checker is supposed to have
declined, and a constructor mismatch where the spec is; the `FdFileRW` and
`FdFileA` cases are the declines on both sides.  The lookup is generalised
out of both the checker and the spec before the split, because Lean's
`cases` on a `match` discriminant otherwise leaves the hypothesis and the
goal on different copies of it.  The witness proof is the same split under
one `bind_step` over the `get_model`, and `pure_ok` closes every arm but
those two: the witness is the checker's accepting answer written out,
`ret_outcome r m` wherever the checker has `check_ret_only eff r m []`. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Sync

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Sync
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude (ret_outcome bind_step)

/-- Accept an observed `fsync`/`fdatasync` effect exactly when `fsync_spec`
admits it.  Every arm of the spec but the read-write and append-mode files'
is return-only, so every such arm here is `check_ret_only` against the one
return the spec names for the fd's kind, with the model handed back
unchanged and no event: `-EBADF` for a number with no open file, which
`do_fsync` (fs/sync.c:209-210, Linux v6.18.46) answers before any file is
examined; `-EINVAL` for a descriptor whose `file_operations` table has no
`.fsync`, the test `vfs_fsync_range` (fs/sync.c:183-184, Linux v6.18.46)
makes before it reads `datasync`; and 0 for a regular file or a directory.
Which table stands behind each fd kind, and why the two syscalls share one
checker, is on the spec's docstring.

Any other return, any write, any zeroing and any event is rejected — the
lies the checker exists to refuse, and
`Checks/Cases/Checks/Sys/Fs/Sync.lean` pins them.  The two declines are the
read-write and append-mode files', the spec twin's declared narrowing. -/
def check_fsync (fd : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | none                  => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdChannel _)   => check_ret_only eff (errno_ret EINVAL) m []
  | some (.FdSocket _)    => check_ret_only eff (errno_ret EINVAL) m []
  | some (.FdPipe _ _)    => check_ret_only eff (errno_ret EINVAL) m []
  | some (.FdDevNull _ _) => check_ret_only eff (errno_ret EINVAL) m []
  | some .FdUrandom       => check_ret_only eff (errno_ret EINVAL) m []
  | some (.FdFile _ _)    => check_ret_only eff (Z_to_bv 64 0) m []
  | some (.FdFileW _ _)   => check_ret_only eff (Z_to_bv 64 0) m []
  | some (.FdFileA _ _) => CheckUnmodeled
  | some (.FdFileRW _ _) => CheckUnmodeled
  | some .FdDir           => check_ret_only eff (Z_to_bv 64 0) m []

/-- Accepting is sound: an accepted effect is one the spec admits, with the
spec's own post-model and events.  Rocq: `Sync.check_fsync_sound_ok`. -/
theorem check_fsync_sound_ok (fd : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (h : check_fsync fd eff m = CheckOk m' evs) :
    fsync_spec fd i m (Ok eff m' evs) := by
  unfold check_fsync at h
  unfold fsync_spec
  rw [bind_get_model_iff]
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none =>
    dsimp only at h ⊢
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact pure_ok _ i _
  | some e =>
    cases e
    case FdFileA _ _ => cases h
    case FdFileRW _ _ => cases h
    all_goals
      (dsimp only at h ⊢
       rw [check_ret_only_ok_iff] at h
       obtain ⟨rfl, rfl, rfl⟩ := h
       exact pure_ok _ i _)

/-- Declining is sound: the two `CheckUnmodeled` arms are the read-write and
append-mode files', where the spec declines too.  Rocq:
`Sync.check_fsync_sound_unmodeled`. -/
theorem check_fsync_sound_unmodeled (fd : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_fsync fd eff m = CheckUnmodeled) :
    fsync_spec fd i m Unmodeled := by
  unfold check_fsync at h
  unfold fsync_spec
  rw [bind_get_model_iff]
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none =>
    exfalso
    dsimp only at h
    exact check_ret_only_no_unmodeled _ _ _ _ h
  | some e =>
    cases e
    case FdFileA _ _ => exact unmodeled_intro i m
    case FdFileRW _ _ => exact unmodeled_intro i m
    all_goals
      (exfalso
       dsimp only at h
       exact check_ret_only_no_unmodeled _ _ _ _ h)

/-- Accepting is complete: every effect the spec admits is accepted, with
the spec's post-model and events.  Rocq: `Sync.check_fsync_complete_ok`. -/
theorem check_fsync_complete_ok (fd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput) (h : fsync_spec fd i m (Ok eff m' evs)) :
    check_fsync fd eff m = CheckOk m' evs := by
  unfold fsync_spec at h
  rw [bind_get_model_iff] at h
  unfold check_fsync
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none =>
    dsimp only at h ⊢
    rw [err_ret, ret_only, pure_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | some e =>
    cases e
    case FdFileA _ _ => simp only [unmodeled_iff, reduceCtorEq] at h
    case FdFileRW _ _ => simp only [unmodeled_iff, reduceCtorEq] at h
    all_goals
      (dsimp only at h ⊢
       simp only [err_ret, ret_only, pure_iff] at h
       obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
       exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩)

/-- Declining is complete: the spec's two `unmodeled` arms are the
read-write and append-mode files', where the checker declines too.  Rocq:
`Sync.check_fsync_complete_unmodeled`. -/
theorem check_fsync_complete_unmodeled (fd : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (h : fsync_spec fd i m Unmodeled) :
    check_fsync fd eff m = CheckUnmodeled := by
  unfold fsync_spec at h
  rw [bind_get_model_iff] at h
  unfold check_fsync
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none =>
    dsimp only at h
    rw [err_ret, ret_only, pure_iff] at h
    cases h
  | some e =>
    cases e
    case FdFileA _ _ => rfl
    case FdFileRW _ _ => rfl
    all_goals
      (dsimp only at h
       simp only [err_ret, ret_only, pure_iff] at h
       cases h)

/-! ## The witness

One outcome the spec admits at every fd and model, as a value, and the proof
that it does: the receptive half of the arm the registration step builds
over this checker, which is what stops a checker from being vacuously
complete over a spec that admits nothing.  It is the checker's accepting
answer written out — `ret_outcome r m`, the "return `r`, change nothing,
emit nothing" triple, wherever `check_fsync` has `check_ret_only eff r m []`
— so an arm the witness answered differently from the checker is caught by
`Checks/Cases/Checks/Sys/Fs/Sync.lean`, which feeds the witness back to the
checker.  The two `Unmodeled` arms here are the read-write and append-mode
files', the spec twin's declared declines; every other arm is `pure`, and
exhibiting it is exhibiting the spec's own answer. -/

/-- Rocq: `Checks.Witness.Fs.Sync.fsync_witness`.  Which return each kind
of fd gets, and which kernel line makes it so, is on `check_fsync` above
and on the spec's docstring; the witness adds no claim of its own. -/
def fsync_witness (fd : word) (m : Model) : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | none                  => ret_outcome (errno_ret EBADF) m
  | some (.FdChannel _)   => ret_outcome (errno_ret EINVAL) m
  | some (.FdSocket _)    => ret_outcome (errno_ret EINVAL) m
  | some (.FdPipe _ _)    => ret_outcome (errno_ret EINVAL) m
  | some (.FdDevNull _ _) => ret_outcome (errno_ret EINVAL) m
  | some .FdUrandom       => ret_outcome (errno_ret EINVAL) m
  | some (.FdFile _ _)    => ret_outcome (Z_to_bv 64 0) m
  | some (.FdFileW _ _)   => ret_outcome (Z_to_bv 64 0) m
  | some (.FdFileA _ _) => Unmodeled
  | some (.FdFileRW _ _) => Unmodeled
  | some .FdDir           => ret_outcome (Z_to_bv 64 0) m

/-- The spec admits the witness at every fd, input and model.  Rocq:
`Checks.Witness.Fs.Sync.fsync_witness_ok`; the proof keeps its shape — one
`bind_step` over the `get_model`, the lookup split, and `pure_ok` on every
arm but the read-write and append-mode files', which are `unmodeled_intro`. -/
theorem fsync_witness_ok (fd : word) (i : SyscallInput) (m : Model) :
    fsync_spec fd i m (fsync_witness fd m) := by
  unfold fsync_spec fsync_witness
  refine bind_step _ _ i m m m _ (get_model_ok i m) ?_
  generalize fd_lookup (m_fds m) fd = r
  cases r with
  | none => exact pure_ok _ i _
  | some e =>
    cases e
    case FdFileA _ _ => exact unmodeled_intro i m
    case FdFileRW _ _ => exact unmodeled_intro i m
    all_goals exact pure_ok _ i _

/-! ## The frame lemma -/

/-- An accepted `fsync` leaves the VM ledger where it was: every arm hands
back the model it was given.  This is the fact the ledger invariant's
alternation consumes for this arm, stated here so that it does not wait on
the alternation's file; Rocq keeps it in `VmMapsDisjoint.v` under the same
name.  Rocq: `VmMapsDisjoint.check_fsync_frame`. -/
theorem check_fsync_frame (fd : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_fsync fd eff m = CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  unfold check_fsync at h
  generalize fd_lookup (m_fds m) fd = r at h
  cases r with
  | none =>
    dsimp only at h
    rw [check_ret_only_ok_iff] at h
    obtain ⟨-, rfl, -⟩ := h
    rfl
  | some e =>
    cases e
    case FdFileA _ _ => cases h
    case FdFileRW _ _ => cases h
    all_goals
      (dsimp only at h
       rw [check_ret_only_ok_iff] at h
       obtain ⟨-, rfl, -⟩ := h
       rfl)

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Sync
