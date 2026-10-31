import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Ioctl
import LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Fs.Ioctl — the ioctl (29) checker, witness and frame, and their proofs

Mirrors `theories/LinuxProcessSem/Checks/Sys/Fs/Ioctl.v`, which holds the
checker for the one syscall `Sys/Fs/Ioctl.v` defines: the executable
acceptor `check_ioctl` and the four lemmas relating it to the relational
`ioctl_spec` of `Sys/Fs/Ioctl.lean`; and, in the same file,
`theories/LinuxProcessSem/Checks/Witness/Fs/Ioctl.v`, the witness
`ioctl_witness` and its `ioctl_witness_ok`.  The checker is the computable
side of the spec and is NOT part of the trusted specification; what a run
may trust is the spec, and these lemmas are what lets a verdict of the
checker stand for an answer of the spec.  Its pins are
`Checks/Cases/Checks/Sys/Fs/Ioctl.lean`.

THE BASELINE NAMED ABOVE is the commit both Rocq files were read at and the
last one to touch them; they read the same at the tip this port was cut
from.  The port plan's baseline, `f44244ad`, is not an ancestor of this
history and predates the `FdUrandom` arm both Rocq files gained with the
/dev/urandom descriptor; the checker below carries that arm, so the header
names the commit it was actually read at rather than one that lacks it.
The spec twin `Sys/Fs/Ioctl.lean` names the day tip of its own port
instead, for the reason its header gives; the Rocq spec reads the same at
both.

The FdFileRW and FdFileA declines follow the spec twin's declared narrowing
(`Sys/Fs/Ioctl.lean`, module header).

WHERE THE WITNESS LIVES.  The Lean tree has no `Checks/Witness/Fs/`
directory; the witness prelude (`Checks/Witness/Prelude.lean`, ticket K5)
is in the tree, and the checker of pselect6 and ppoll
(`Checks/Sys/Fs/Select.lean`) already keeps its witnesses beside its
checkers.  This file does the same: `ioctl_witness` is one `ret_outcome`
per answering arm and `Unmodeled` per declining one, under the name its
Rocq original carries.  This stops being the layout the day the Lean tree
gains a witness file of its own for this syscall.

THE FRAME LEMMA is Rocq's `VmMapsDisjoint.check_ioctl_frame`.  The Lean
twin of that file (`Checks/VmMapsDisjoint.lean`, ticket K4) says where the
per-arm frame lemmas live and how they close: each arrives with its C
ticket, in the checker's own file, which imports the twin so that the
lemma is closed by the twin's `vm_frame2` — Rocq's proof is `unfold
check_ioctl in H. vm_frame2 H.`, and the proof below is the same two
steps.  The registration step (ticket V-Fs-Ioctl) derives the arm-level
fact `arm_ioctl_preserves_vm` from it through `arm_preserves_of_frame`
and appends the fact to `Checks/VmMapsDisjoint/Arms.lean`, which imports
the table and so cannot be imported here.  Importing the twin closes no
cycle: it imports `Checks/Sys/Dispatch.lean` and never
`Checks/Sys/Table.lean`, the one file that imports the checkers.
`Checks/Sys/Fs/Sync.lean` and `Checks/Sys/Fs/Select.lean` state theirs in
the checker's file too but write the steps out by hand, because the twin
did not exist when they landed (Select's frame lemma says so in place, and
Sync's header records that the twins it needed were not in the tree yet);
this is the first checker to land on the twin, so it takes the discipline
the twin's header asks for.  The port plan's C-ticket text still assigns
the frame lemma to the registration step; the twin's header is the newer
word and this file follows it.

THE PROOFS first split the fd-first request gate, closing a declined
request with `unmodeled_iff`. After that they keep Rocq's lookup split —
`none`, then one case per constructor — and, on the six kinds that share
the terminal-only arm, a second split on `tty_only_request req`: where it
holds the arm is a `check_ret_only`, closed by `check_ret_only_ok_iff` in
both `Ok` directions and refuted by `check_ret_only_no_unmodeled` where
the checker is supposed to have declined; where it fails, and on the two
character devices, the checker's answer is the constructor `CheckUnmodeled`
and the spec's is `unmodeled`, so a mismatch is a constructor mismatch and
a match is `unmodeled_intro`.  The lookup is generalised out of both the
checker and the spec before the split, because Lean's `cases` on a `match`
discriminant otherwise leaves the hypothesis and the goal on different
copies of it; the Bool is split with `cases hr : …`, which substitutes in
the goal only, so the hypothesis is rewritten with `hr` by hand. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Ioctl

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Ioctl
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-- Accept an observed effect exactly when `ioctl_spec` admits it.
The prefix gate mirrors `Ioctl.ioctl_fd_first_request`: QEMU v11.1.1
linux-user/syscall.c `do_ioctl` can answer unknown requests or fail to copy
IOC_W arguments before `safe_ioctl` checks the fd. See the spec's source
argument. Only after this gate does the unchanged fd match run.
Linux v6.18.46 fs/ioctl.c `ioctl` returns EBADF from `fd_empty`, and
`vfs_ioctl` supplies ENOTTY on the modeled nonterminal kinds; the spec
explains the handler behind each kind. Every answering arm is return-only,
so `check_ret_only` refuses any other return or nonempty effect ledger.
Rocq: `Ioctl.check_ioctl`. -/
def check_ioctl (fd req : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if !ioctl_fd_first_request req then CheckUnmodeled else
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdChannel _) | some (.FdFile _ _) | some (.FdFileW _ _) | some .FdDir
  | some (.FdSocket _) | some (.FdPipe _ _) =>
      if tty_only_request req then check_ret_only eff (errno_ret ENOTTY) m [] else CheckUnmodeled
  | some (.FdFileA _ _) => CheckUnmodeled
  | some (.FdFileRW _ _) => CheckUnmodeled
  | some (.FdDevNull _ _) => CheckUnmodeled
  | some .FdUrandom => CheckUnmodeled

/-- Accepting is sound: an accepted effect is one the spec admits, with the
spec's own post-model and events.  Rocq: `Ioctl.check_ioctl_sound_ok`. -/
theorem check_ioctl_sound_ok (fd req : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput) (h : check_ioctl fd req eff m = CheckOk m' evs) :
    ioctl_spec fd req i m (Ok eff m' evs) := by
  unfold check_ioctl at h
  unfold ioctl_spec
  cases hg : ioctl_fd_first_request req with
  | false => simp only [hg, Bool.not_false, ↓reduceIte, reduceCtorEq] at h ⊢
  | true =>
    simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    rw [bind_get_model_iff]
    generalize fd_lookup (m_fds m) fd = r at h ⊢
    cases r with
    | none =>
      dsimp only at h ⊢
      rw [check_ret_only_ok_iff] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact pure_ok _ i _
    | some e =>
      cases e <;> dsimp only at h ⊢ <;>
        first
        | cases h
        | (cases hr : tty_only_request req
           · simp only [hr, Bool.false_eq_true, ↓reduceIte] at h
             cases h
           · simp only [hr, ↓reduceIte] at h ⊢
             rw [check_ret_only_ok_iff] at h
             obtain ⟨rfl, rfl, rfl⟩ := h
             exact pure_ok _ i _)

/-- Declining is sound: where the checker declines, the spec has an
`Unmodeled` run.  Rocq:
`Ioctl.check_ioctl_sound_unmodeled`. -/
theorem check_ioctl_sound_unmodeled (fd req : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_ioctl fd req eff m = CheckUnmodeled) :
    ioctl_spec fd req i m Unmodeled := by
  unfold check_ioctl at h
  unfold ioctl_spec
  cases hg : ioctl_fd_first_request req with
  | false => simp only [hg, Bool.not_false, ↓reduceIte, unmodeled_iff] at h ⊢
  | true =>
    simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    rw [bind_get_model_iff]
    generalize fd_lookup (m_fds m) fd = r at h ⊢
    cases r with
    | none =>
      dsimp only at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | some e =>
      cases e <;> dsimp only at h ⊢ <;>
        first
        | exact unmodeled_intro i m
        | (cases hr : tty_only_request req
           · simp only [Bool.false_eq_true, ↓reduceIte]
             exact unmodeled_intro i m
           · simp only [hr, ↓reduceIte] at h
             exact absurd h (check_ret_only_no_unmodeled _ _ _ _))

/-- Accepting is complete: every effect the spec admits is accepted, with
the spec's post-model and events.  Rocq:
`Ioctl.check_ioctl_complete_ok`. -/
theorem check_ioctl_complete_ok (fd req : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput) (h : ioctl_spec fd req i m (Ok eff m' evs)) :
    check_ioctl fd req eff m = CheckOk m' evs := by
  unfold ioctl_spec at h
  unfold check_ioctl
  cases hg : ioctl_fd_first_request req with
  | false => simp only [hg, Bool.not_false, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h ⊢
  | true =>
    simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    rw [bind_get_model_iff] at h
    generalize fd_lookup (m_fds m) fd = r at h ⊢
    cases r with
    | none =>
      dsimp only at h ⊢
      rw [err_ret, ret_only, pure_iff] at h
      obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    | some e =>
      cases e <;> dsimp only at h ⊢ <;>
        first
        | (rw [unmodeled_iff] at h
           cases h)
        | (cases hr : tty_only_request req
           · simp only [hr, Bool.false_eq_true, ↓reduceIte] at h
             rw [unmodeled_iff] at h
             cases h
           · simp only [hr, ↓reduceIte] at h ⊢
             rw [err_ret, ret_only, pure_iff] at h
             obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
             exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩)

/-- Declining is complete: where the spec has an `Unmodeled` run, the
checker declines — by `rfl` on the two character devices and on an open fd
whose request is not terminal-only; after the fd-first gate, on a closed fd or an answering terminal-only
request the spec's run is a `pure` outcome equal to `Unmodeled`, a
constructor mismatch.  Rocq: `Ioctl.check_ioctl_complete_unmodeled`. -/
theorem check_ioctl_complete_unmodeled (fd req : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (h : ioctl_spec fd req i m Unmodeled) :
    check_ioctl fd req eff m = CheckUnmodeled := by
  unfold ioctl_spec at h
  unfold check_ioctl
  cases hg : ioctl_fd_first_request req with
  | false => simp only [hg, Bool.not_false, ↓reduceIte, unmodeled_iff] at h ⊢
  | true =>
    simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    rw [bind_get_model_iff] at h
    generalize fd_lookup (m_fds m) fd = r at h ⊢
    cases r with
    | none =>
      dsimp only at h
      rw [err_ret, ret_only, pure_iff] at h
      cases h
    | some e =>
      cases e <;> dsimp only at h ⊢ <;>
        first
        | rfl
        | (cases hr : tty_only_request req
           · simp only [Bool.false_eq_true, ↓reduceIte]
           · simp only [hr, ↓reduceIte] at h
             rw [err_ret, ret_only, pure_iff] at h
             cases h)

/-- The one outcome the spec admits for `ioctl` on this fd, request and
model, or `Unmodeled` where it admits none: the same match as the checker,
with `ret_outcome` where the checker has `check_ret_only`.  Mirrors
`ioctl_witness` in `theories/LinuxProcessSem/Checks/Witness/Fs/Ioctl.v`. -/
def ioctl_witness (fd req : word) (m : Model) : outcome SyscallEffect :=
  if !ioctl_fd_first_request req then Unmodeled else
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some (.FdChannel _) | some (.FdFile _ _) | some (.FdFileW _ _) | some .FdDir
  | some (.FdSocket _) | some (.FdPipe _ _) =>
      if tty_only_request req then ret_outcome (errno_ret ENOTTY) m else Unmodeled
  | some (.FdFileA _ _) => Unmodeled
  | some (.FdFileRW _ _) => Unmodeled
  | some (.FdDevNull _ _) => Unmodeled
  | some .FdUrandom => Unmodeled

/-- The witness is a run of the spec: the spec is receptive on every fd,
request and model.  Rocq: `Ioctl.ioctl_witness_ok`. -/
theorem ioctl_witness_ok (fd req : word) (i : SyscallInput) (m : Model) :
    ioctl_spec fd req i m (ioctl_witness fd req m) := by
  unfold ioctl_spec ioctl_witness
  cases hg : ioctl_fd_first_request req with
  | false => simp only [Bool.not_false, ↓reduceIte, unmodeled_iff]
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [bind_get_model_iff]
    generalize fd_lookup (m_fds m) fd = r
    cases r with
    | none => exact pure_ok _ i m
    | some e =>
      cases e <;> dsimp only <;>
        first
        | exact unmodeled_intro i m
        | (cases hr : tty_only_request req
           · simp only [Bool.false_eq_true, ↓reduceIte]
             exact unmodeled_intro i m
           · simp only [↓reduceIte]
             exact pure_ok _ i m)

open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint in
/-- An accepted `ioctl` leaves the VM ledger where it was: every accepting
arm hands back the model it was given, and the declining arms accept
nothing.  This is the fact the ledger invariant's alternation consumes for
this arm, stated here so that it does not wait on the alternation's file;
Rocq keeps it in `VmMapsDisjoint.v` under the same name and closes it with
`vm_frame2`, as this does.  Rocq: `VmMapsDisjoint.check_ioctl_frame`. -/
theorem check_ioctl_frame (fd req : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_ioctl fd req eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_ioctl at h
  vm_frame2 h

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Ioctl
