import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.File

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Fs.File — the dup (23) and dup3 (24) checkers, witnesses, and their proofs

Mirrors `theories/LinuxProcessSem/Checks/Sys/Fs/File.v` — the executable
checkers `check_dup` and `check_dup3`, their shared allocating acceptor
`check_dup_result`, and the eight proofs — and, in the same file,
`theories/LinuxProcessSem/Checks/Witness/Fs/File.v` — the progress
witnesses `dup_witness` and `dup3_witness` with `dup_witness_ok` and
`dup3_witness_ok`.  All answer to the relational specs in
`Sys/Fs/File.lean`, which answer to Linux `fs/file.c`.  Not part of the
trusted specification: the checkers' proofs relate them to the specs, and
the proofs are what carry the trust.  This file stops at those theorems.
The `CheckedArm`s built from them, their `checked_table` rows, their
`arm_unfold` lemmas and their `*_frame` lemmas are V-Fs-File's: a checker
ticket owes none of them since #904 re-cut the C tickets' edges, so that
it depends on K1, K5 and its spec alone rather than on the checked-table
chain (BRIEF.md section 5, the CHECK and VERIFY blocks).  Rocq states
`check_dup_frame` and `check_dup3_frame` in
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`, beside the
alternation that consumes them; the Lean tree states each arm's frame
lemma in the checker's own file once the arm is registered, and what
these two will rest on is already visible below: every accepting leaf
hands back either the model it was given (`check_ret_only`) or
`with_fds fds m`, and `State.with_fds` rebuilds the model from `m.m_vm`
unchanged, so `m_vmmaps` is the pre-model's on every `CheckOk`.  This
stops being true the day a leaf moves the model by anything but
`with_fds`, and the frame lemma written at registration is the check that
fails then.  The pins over what this file computes are
`Checks/Cases/Checks/Sys/Fs/File.lean`.

Every kernel claim below is read at Linux v6.18.46 (commit
1f99e9ab748f); the definition-level arguments — `dup`'s order, `ksys_dup3`'s
five gates, why a free `newfd` at or above `NR_OPEN_DEFAULT` is declined
and why the limit is read from the run — are on `Sys/Fs/File.lean` and on
Rocq's `File.dup_spec` and `File.dup3_spec`, and are not repeated here.
What this file adds is the ACCEPTOR reading of each arm: which `(effect,
model, events)` triple the checker admits, which it rejects, and where it
declines.

THIS FILE IMPORTS `Checks/Sys/Fs/Open.lean` rather than the preludes alone,
as Rocq's imports the `Fs.Open` mirror: `Open.errno_ret_in_alloc_fd` — an
allocated descriptor never matches an injectable errno — is proved there,
beside the `openat` acceptor that first needed it, and `check_dup_result`
IS that acceptor over `dup_errnos` — `Open.check_new_fd_result dup_errnos`,
the way `Open.check_open_result` is it over `openat_errnos`.  Rocq keeps
the two acceptors one definition apart, for the reason its
`check_dup_result` docstring gives — a shared acceptor costs a second
`unfold` in every consumer, in `Common/FileSim.v` and `Examples/cp_ns`
among them — and that reason has no Lean counterpart: the Lean tree has no
`Common/`, and nothing outside this file and its pins names the acceptor.
So the Lean definition is the instance, kept under Rocq's name for the
port's name-for-name mapping and unfolding to the shared acceptor by
`rfl`, and its two lemmas `check_dup_result_no_unmodeled` and
`check_dup_result_ok_inv` are `Open`'s general ones applied to
`dup_errnos`.  Neither lemma has a Rocq name — Rocq's `check_dup_sound_ok`
destructs the effect's five ledgers inline — and both are about the
acceptor's shape alone.

Spellings that differ from Rocq without changing a value: `negb` is `!`,
written `!(dup_modeled_entry e)` exactly as the spec writes it, so the
checker's `if` and the spec's are the same term; `Z.ltb (bv_unsigned newfd)
NR_OPEN_DEFAULT` is the decidable `bv_unsigned newfd < NR_OPEN_DEFAULT`
the spec's `if` tests; `None`/`Some` are `none`/`some`.  The proofs do not
mirror Rocq's scripts tactic for tactic: Rocq's `destruct … eqn:` is
`cases h : …`, which substitutes in the goal only (a hypothesis still
holds the term and is rewritten by name), Rocq's `cbv beta iota` after a
rewrite is the `↓reduceIte` simproc, and Rocq's `sys_unfold; inv_ok`
completeness walk is `bind_model_inv` followed by the monad's `*_iff`
readings, as `Checks/Sys/Fs/Locks.lean` and `Checks/Sys/Fs/Open.lean` do
it. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.File

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.File
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open (errno_ret_in_alloc_fd
  check_new_fd_result check_new_fd_result_no_unmodeled check_new_fd_result_ok_inv)

/-! ## The checker — `Checks/Sys/Fs/File.v` -/

/-! ### The allocating acceptor

`dup_spec`'s second arm admits two outcomes: an errno drawn from
`dup_errnos`, or the lowest free descriptor with `oldfd`'s entry installed
at it.  The kernel's side is `SYSCALL_DEFINE1(dup, unsigned int, fildes)`
(fs/file.c:1457-1470, Linux v6.18.46, commit 1f99e9ab748f): `fget_raw`
takes a second reference to the `struct file` the descriptor names,
`get_unused_fd_flags` (fs/file.c:620-623, Linux v6.18.46) allocates the
slot through `alloc_fd` (fs/file.c:570-613, Linux v6.18.46), and
`fd_install` (fs/file.c:652, Linux v6.18.46) stores the same pointer there.
That the slot is the LOWEST free descriptor, and that no descriptor the
scan can produce lands in the error band, is `Checks/Sys/Fs/Open.lean`'s
argument (`alloc_fd`, `find_next_fd`, `__put_unused_fd`, and
`errno_ret_in_alloc_fd` from `State.alloc_fd_le`), not repeated here.

What separates this acceptor from `openat`'s is the errno set.  `dup`
allocates no `struct file` — the reference it installs is the one
`fget_raw` took — so the -ENFILE from `alloc_empty_file` (fs/file_table.c,
Linux v6.18.46, the system-wide open-file limit) is not on its path, and
nothing on the path is interruptible.  What is on it is the descriptor
table: `alloc_fd` answers -EMFILE at `fd >= end` (fs/file.c:591-593, Linux
v6.18.46) with `end` the soft RLIMIT_NOFILE; when the table must grow,
`expand_files` (fs/file.c:310-311, Linux v6.18.46) answers -EMFILE at the
`sysctl_nr_open` ceiling, and `alloc_fdtable` (fs/file.c, Linux v6.18.46)
below it answers -ENOMEM when the allocation fails (:242) or -EMFILE when
a ceiling lowered under it, or the `INT_MAX` bound, leaves too few slots
(:194-197, :212-213).  Those two errnos are `dup_errnos`; a kernel handing
back any other errno, or -EBADF on a descriptor the model holds, is lying,
and the acceptor refuses it.  Whether either can be reached on a given
table is not the acceptor's question: the set is the spec's
(`Sys/Fs/File.lean`, `dup_errnos`), offered on every allocating call
whatever the table, and the acceptor admits exactly the outcomes the spec
does.  That the offer outruns Linux — -EMFILE where the soft limit is not
reached, -ENOMEM where `max_fds`, never below `NR_OPEN_DEFAULT`, is not
reached — is the priority-2 admission
bugs/fd-allocation-ignores-rlimit-nofile.md records for the limit; the
pins over this file state it at the acceptor
(`dup_above_the_soft_limit_admits_the_slot_at_the_acceptor`). -/

/-- Accept the effect of `dup`'s allocating arm: the return alone, no
ledgers, and either an errno of `dup_errnos` with the model unchanged, or
the lowest free descriptor with the model `mk` builds for it.  A held
descriptor, a free one that is not the lowest, and any ledger entry are
refused.  Rocq: `File.check_dup_result`, which spells the match inline;
here it is `Open.check_new_fd_result` over `dup_errnos` (the header says
why the two trees differ). -/
def check_dup_result : SyscallEffect → Model → (word → Model) → check_result :=
  check_new_fd_result dup_errnos

/-- `check_dup_result` never declines: the arm it serves has no
`unmodeled` branch of its own — `dup_spec`'s decline is the fd-kind test
before it, which `check_dup` answers itself.  Lean-only;
`Open.check_new_fd_result_no_unmodeled` at `dup_errnos`. -/
theorem check_dup_result_no_unmodeled (eff : SyscallEffect) (m : Model) (mk : word → Model) :
    check_dup_result eff m mk ≠ CheckUnmodeled :=
  check_new_fd_result_no_unmodeled dup_errnos eff m mk

/-- What an accepting `check_dup_result` verdict says about its inputs:
the effect is a bare return, no event is emitted, and the return is
either an errno of `dup_errnos` with the model kept, or the free lowest
descriptor with the model `mk` builds.  `check_dup_sound_ok` reads its
two cases off this.  Lean-only; `Open.check_new_fd_result_ok_inv` at
`dup_errnos`. -/
theorem check_dup_result_ok_inv (eff : SyscallEffect) (m : Model) (mk : word → Model)
    (m' : Model) (evs : List event) (h : check_dup_result eff m mk = CheckOk m' evs) :
    evs = [] ∧ ∃ ret, eff = mkEffect ret [] []
      ∧ ((errno_ret_in dup_errnos ret = true ∧ m' = m)
         ∨ (fd_lookup (m_fds m) ret = none ∧ ret = alloc_fd (m_fds m) ∧ m' = mk ret)) :=
  check_new_fd_result_ok_inv dup_errnos eff m mk m' evs h

/-- The two errnos of `dup_errnos` are in `[1, 4095]`, which is what
`errno_ret_in_alloc_fd` asks of the set.  Rocq closes the same fact `by
reflexivity` at each use. -/
theorem dup_errnos_ok : errnos_ok dup_errnos = true := by decide

/-! ### The two checkers -/

/-- The dup acceptor.  Rocq: `File.check_dup`.

`SYSCALL_DEFINE1(dup, unsigned int, fildes)` (fs/file.c:1457-1470, Linux
v6.18.46, commit 1f99e9ab748f) resolves the descriptor first — `fget_raw`
returning NULL is -EBADF before `get_unused_fd_flags` runs — so a closed
`oldfd` is `check_ret_only` at -EBADF whatever table the kernel claims to
have failed to grow.  An open one whose kind `dup_modeled_entry` refuses
(a file, whose copy would share the original's offset through the
`struct file` both descriptors name; a socket; a pipe end) declines before
any return is read: `CheckUnmodeled`, the fail-closed answer, not a
verdict on the kernel's.  A modeled kind goes to the allocating acceptor
with `mk` installing the SAME entry at the returned descriptor — the copy
is the entry, as `fd_install` (fs/file.c:652, Linux v6.18.46) stores the
same pointer. -/
def check_dup (oldfd : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) oldfd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some e =>
      if !(dup_modeled_entry e) then CheckUnmodeled
      else check_dup_result eff m (fun fd => with_fds (fd_insert (m_fds m) fd e) m)

/-- The dup3 acceptor.  Rocq: `File.check_dup3`.

The gates are `ksys_dup3`'s (fs/file.c:1399-1431, Linux v6.18.46, commit
1f99e9ab748f) in its order, each a `check_ret_only` at the errno the
kernel returns there: a flag bit outside O_CLOEXEC is -EINVAL (:1405-1406),
`oldfd == newfd` is -EINVAL (:1408-1409), `newfd >= rlimit(RLIMIT_NOFILE)`
is -EBADF (:1411-1412) — read from `State.m_nofile`, the limit the run was
launched with — and a closed `oldfd` is -EBADF (:1417-1418, through the
`Ebadf` label at :1426-1427, reached before `expand_files`' result is read
at :1419).  Every accepting answer is deterministic, so the return the
checker admits is the one word the spec computes and no other; no errno is
injectable here, since a free `newfd` under `NR_OPEN_DEFAULT` needs no
table growth and an open one is replaced by `do_dup2` (fs/file.c, Linux
v6.18.46), whose -EBUSY needs a second thread the model does not
have.  Two arms decline: an `oldfd` whose kind `dup_modeled_entry` refuses,
after the three gates before it have answered (so `dup3(3, 3, 0)` is
-EINVAL, not a decline), and a FREE `newfd` at or above `NR_OPEN_DEFAULT`,
where the kernel's answer turns on the table's current `max_fds` and the
`nr_open` sysctl, neither of which the model carries. -/
def check_dup3 (oldfd newfd flags : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if !(dup3_flags_ok flags) then check_ret_only eff (errno_ret EINVAL) m []
  else if bv_eqb oldfd newfd then check_ret_only eff (errno_ret EINVAL) m []
  else if !(dup3_newfd_under_limit newfd m) then check_ret_only eff (errno_ret EBADF) m []
  else
    match fd_lookup (m_fds m) oldfd with
    | none => check_ret_only eff (errno_ret EBADF) m []
    | some e =>
        if !(dup_modeled_entry e) then CheckUnmodeled
        else
          match fd_lookup (m_fds m) newfd with
          | none =>
              if bv_unsigned newfd < NR_OPEN_DEFAULT
              then check_ret_only eff newfd (with_fds (fd_insert (m_fds m) newfd e) m) []
              else CheckUnmodeled
          | some _ => check_ret_only eff newfd (with_fds (fd_insert (m_fds m) newfd e) m) []

/-! ## The proofs — dup

Each is the spec's own case split.  `bind_ok0` and `bind_unmodeled2` step
through `get_model`; `check_ret_only_ok_iff` reads an accepting
`check_ret_only` back into its three equalities and
`check_ret_only_no_unmodeled` refuses a declining one; the allocating
arm's two outcomes are `check_dup_result_ok_inv`'s two cases, taken
through `alt_l`/`alt_r` and `choose_ok` as `Open.check_open_result_sound_ok`
takes them. -/

/-- Rocq: `File.check_dup_sound_ok`. -/
theorem check_dup_sound_ok (oldfd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput) (h : check_dup oldfd eff m = CheckOk m' evs) :
    dup_spec oldfd i m (Ok eff m' evs) := by
  unfold check_dup at h
  unfold dup_spec
  refine bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m) ?_
  cases hfd : fd_lookup (m_fds m) oldfd with
  | none =>
    simp only [hfd] at h
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact pure_ok _ i _
  | some e =>
    simp only [hfd] at h ⊢
    cases hk : dup_modeled_entry e with
    | false =>
      simp only [hk, Bool.not_false, ↓reduceIte, reduceCtorEq] at h
    | true =>
      simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨rfl, ret, rfl, hcase⟩ := check_dup_result_ok_inv eff m _ m' evs h
      unfold errno_from lowest_fd set_fds
      rcases hcase with ⟨he, hm⟩ | ⟨hnone, hfd', hm⟩ <;> subst m'
      · obtain ⟨er, hmem, rfl⟩ := (errno_ret_in_true dup_errnos ret).mp he
        apply alt_l
        refine bind_ok0 _ _ i m er m _ _ _ (choose_ok _ er i m hmem) ?_
        exact pure_ok _ i m
      · apply alt_r
        refine bind_ok0 _ _ i m ret m _ _ _ (choose_ok _ ret i m (And.intro hnone hfd')) ?_
        refine bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m) ?_
        exact pure_ok _ i _

/-- Rocq: `File.check_dup_sound_unmodeled`. -/
theorem check_dup_sound_unmodeled (oldfd : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_dup oldfd eff m = CheckUnmodeled) :
    dup_spec oldfd i m Unmodeled := by
  unfold check_dup at h
  unfold dup_spec
  refine bind_unmodeled2 _ _ i m m m [] (get_model_ok i m) ?_
  cases hfd : fd_lookup (m_fds m) oldfd with
  | none =>
    simp only [hfd] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | some e =>
    simp only [hfd] at h ⊢
    cases hk : dup_modeled_entry e with
    | false =>
      simp only [Bool.not_false, ↓reduceIte]
      exact unmodeled_intro i m
    | true =>
      simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      exact absurd h (check_dup_result_no_unmodeled _ _ _)

/-- Rocq: `File.check_dup_complete_ok`. -/
theorem check_dup_complete_ok (oldfd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput) (h : dup_spec oldfd i m (Ok eff m' evs)) :
    check_dup oldfd eff m = CheckOk m' evs := by
  unfold dup_spec at h
  have h := bind_model_inv _ i m _ h
  unfold check_dup
  cases hfd : fd_lookup (m_fds m) oldfd with
  | none =>
    simp only [hfd, err_ret, ret_only, pure_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | some e =>
    simp only [hfd] at h ⊢
    cases hk : dup_modeled_entry e with
    | false =>
      simp only [hk, Bool.not_false, ↓reduceIte] at h
      exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])
    | true =>
      simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
      unfold errno_from lowest_fd set_fds at h
      rw [alt_iff] at h
      rcases h with h | h
      · rw [bind_choose_iff] at h
        obtain ⟨er, hmem, h⟩ := h
        simp only [err_ret, ret_only, pure_iff] at h
        obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
        simp only [check_dup_result, check_new_fd_result, errno_ret_in_intro dup_errnos er hmem,
          ↓reduceIte]
      · rw [bind_choose_iff] at h
        obtain ⟨fd, ⟨hnone, hfd'⟩, h⟩ := h
        simp only [bind_modify_iff, ret_only, pure_iff] at h
        obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
        subst hfd'
        simp only [check_dup_result, check_new_fd_result, errno_ret_in_alloc_fd _ _ dup_errnos_ok,
          Bool.false_eq_true, ↓reduceIte, hnone, bv_eqb_refl]

/-- Rocq: `File.check_dup_complete_unmodeled`. -/
theorem check_dup_complete_unmodeled (oldfd : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (h : dup_spec oldfd i m Unmodeled) :
    check_dup oldfd eff m = CheckUnmodeled := by
  unfold dup_spec at h
  have h := bind_model_inv _ i m _ h
  unfold check_dup
  cases hfd : fd_lookup (m_fds m) oldfd with
  | none =>
    simp only [hfd, err_ret, ret_only, pure_iff, reduceCtorEq] at h
  | some e =>
    simp only [hfd] at h ⊢
    cases hk : dup_modeled_entry e with
    | false =>
      simp only [Bool.not_false, ↓reduceIte]
    | true =>
      simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      unfold errno_from lowest_fd set_fds at h
      rw [alt_iff] at h
      rcases h with h | h
      · rw [bind_choose_iff] at h
        obtain ⟨er, -, h⟩ := h
        simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
      · rw [bind_choose_iff] at h
        obtain ⟨fd, -, h⟩ := h
        simp only [bind_modify_iff, ret_only, pure_iff, reduceCtorEq] at h

/-! ## The proofs — dup3

The same walk down `ksys_dup3`'s gates on both sides; every accepting leaf
is a `check_ret_only`, and the two installing leaves step through
`set_fds`'s `modify` with `modify_ok` (soundness) or `bind_modify_iff`
(completeness).  The free-`newfd` bound is a decidable proposition rather
than a `Bool`, so it is split by `by_cases` where the others are `cases`
on the boolean. -/

/-- Rocq: `File.check_dup3_sound_ok`. -/
theorem check_dup3_sound_ok (oldfd newfd flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_dup3 oldfd newfd flags eff m = CheckOk m' evs) :
    dup3_spec oldfd newfd flags i m (Ok eff m' evs) := by
  unfold check_dup3 at h
  unfold dup3_spec
  refine bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m) ?_
  cases hf : dup3_flags_ok flags with
  | false =>
    simp only [hf, Bool.not_false, ↓reduceIte] at h ⊢
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact pure_ok _ i _
  | true =>
  simp only [hf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hne : bv_eqb oldfd newfd with
  | true =>
    simp only [hne, ↓reduceIte] at h ⊢
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact pure_ok _ i _
  | false =>
  simp only [hne, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hl : dup3_newfd_under_limit newfd m with
  | false =>
    simp only [hl, Bool.not_false, ↓reduceIte] at h ⊢
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact pure_ok _ i _
  | true =>
  simp only [hl, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hfd : fd_lookup (m_fds m) oldfd with
  | none =>
    simp only [hfd] at h ⊢
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact pure_ok _ i _
  | some e =>
  simp only [hfd] at h ⊢
  cases hk : dup_modeled_entry e with
  | false =>
    simp only [hk, Bool.not_false, ↓reduceIte, reduceCtorEq] at h
  | true =>
  simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hnf : fd_lookup (m_fds m) newfd with
  | some e2 =>
    simp only [hnf] at h ⊢
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    unfold set_fds
    refine bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m) ?_
    exact pure_ok _ i _
  | none =>
    simp only [hnf] at h ⊢
    by_cases hb : bv_unsigned newfd < NR_OPEN_DEFAULT
    · simp only [hb, ↓reduceIte] at h ⊢
      rw [check_ret_only_ok_iff] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      unfold set_fds
      refine bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m) ?_
      exact pure_ok _ i _
    · simp only [hb, ↓reduceIte, reduceCtorEq] at h

/-- Rocq: `File.check_dup3_sound_unmodeled`. -/
theorem check_dup3_sound_unmodeled (oldfd newfd flags : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_dup3 oldfd newfd flags eff m = CheckUnmodeled) :
    dup3_spec oldfd newfd flags i m Unmodeled := by
  unfold check_dup3 at h
  unfold dup3_spec
  refine bind_unmodeled2 _ _ i m m m [] (get_model_ok i m) ?_
  cases hf : dup3_flags_ok flags with
  | false =>
    simp only [hf, Bool.not_false, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | true =>
  simp only [hf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hne : bv_eqb oldfd newfd with
  | true =>
    simp only [hne, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | false =>
  simp only [hne, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hl : dup3_newfd_under_limit newfd m with
  | false =>
    simp only [hl, Bool.not_false, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | true =>
  simp only [hl, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hfd : fd_lookup (m_fds m) oldfd with
  | none =>
    simp only [hfd] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | some e =>
  simp only [hfd] at h ⊢
  cases hk : dup_modeled_entry e with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
  simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hnf : fd_lookup (m_fds m) newfd with
  | some e2 =>
    simp only [hnf] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | none =>
    simp only [hnf] at h ⊢
    by_cases hb : bv_unsigned newfd < NR_OPEN_DEFAULT
    · simp only [hb, ↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    · simp only [hb, ↓reduceIte]
      exact unmodeled_intro i m

/-- Rocq: `File.check_dup3_complete_ok`. -/
theorem check_dup3_complete_ok (oldfd newfd flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput) (h : dup3_spec oldfd newfd flags i m (Ok eff m' evs)) :
    check_dup3 oldfd newfd flags eff m = CheckOk m' evs := by
  unfold dup3_spec at h
  have h := bind_model_inv _ i m _ h
  unfold check_dup3
  cases hf : dup3_flags_ok flags with
  | false =>
    simp only [hf, Bool.not_false, ↓reduceIte, err_ret, ret_only, pure_iff] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | true =>
  simp only [hf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hne : bv_eqb oldfd newfd with
  | true =>
    simp only [hne, ↓reduceIte, err_ret, ret_only, pure_iff] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | false =>
  simp only [hne, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hl : dup3_newfd_under_limit newfd m with
  | false =>
    simp only [hl, Bool.not_false, ↓reduceIte, err_ret, ret_only, pure_iff] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | true =>
  simp only [hl, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hfd : fd_lookup (m_fds m) oldfd with
  | none =>
    simp only [hfd, err_ret, ret_only, pure_iff] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | some e =>
  simp only [hfd] at h ⊢
  cases hk : dup_modeled_entry e with
  | false =>
    simp only [hk, Bool.not_false, ↓reduceIte] at h
    exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])
  | true =>
  simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hnf : fd_lookup (m_fds m) newfd with
  | some e2 =>
    simp only [hnf, set_fds, bind_modify_iff, ret_only, pure_iff] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | none =>
    simp only [hnf] at h ⊢
    by_cases hb : bv_unsigned newfd < NR_OPEN_DEFAULT
    · simp only [hb, ↓reduceIte, set_fds, bind_modify_iff, ret_only, pure_iff] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    · simp only [hb, ↓reduceIte] at h
      exact absurd ((unmodeled_iff i m _).mp h) (by simp only [reduceCtorEq, not_false_eq_true])

/-- Rocq: `File.check_dup3_complete_unmodeled`. -/
theorem check_dup3_complete_unmodeled (oldfd newfd flags : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (h : dup3_spec oldfd newfd flags i m Unmodeled) :
    check_dup3 oldfd newfd flags eff m = CheckUnmodeled := by
  unfold dup3_spec at h
  have h := bind_model_inv _ i m _ h
  unfold check_dup3
  cases hf : dup3_flags_ok flags with
  | false =>
    simp only [hf, Bool.not_false, ↓reduceIte, err_ret, ret_only, pure_iff, reduceCtorEq] at h
  | true =>
  simp only [hf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hne : bv_eqb oldfd newfd with
  | true =>
    simp only [hne, ↓reduceIte, err_ret, ret_only, pure_iff, reduceCtorEq] at h
  | false =>
  simp only [hne, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hl : dup3_newfd_under_limit newfd m with
  | false =>
    simp only [hl, Bool.not_false, ↓reduceIte, err_ret, ret_only, pure_iff, reduceCtorEq] at h
  | true =>
  simp only [hl, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hfd : fd_lookup (m_fds m) oldfd with
  | none =>
    simp only [hfd, err_ret, ret_only, pure_iff, reduceCtorEq] at h
  | some e =>
  simp only [hfd] at h ⊢
  cases hk : dup_modeled_entry e with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
  | true =>
  simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hnf : fd_lookup (m_fds m) newfd with
  | some e2 =>
    simp only [hnf, set_fds, bind_modify_iff, ret_only, pure_iff, reduceCtorEq] at h
  | none =>
    simp only [hnf] at h ⊢
    by_cases hb : bv_unsigned newfd < NR_OPEN_DEFAULT
    · simp only [hb, ↓reduceIte, set_fds, bind_modify_iff, ret_only, pure_iff, reduceCtorEq] at h
    · simp only [hb, ↓reduceIte]

/-! ## The witnesses — `Checks/Witness/Fs/File.v`

dup allocates, so its witness takes the environment-failure branch, as
openat's does: `alt_l` into `errno_from dup_errnos`, whose head is
`witness_errno` (-ENOMEM, from `alloc_fdtable` (fs/file.c, Linux v6.18.46)
failing).  dup3 is deterministic on every arm it answers and has
none to take; its witness is the spec's own case tree as data. -/

/-- Rocq: `Witness.Fs.File.dup_witness`. -/
def dup_witness (oldfd : word) (m : Model) : outcome SyscallEffect :=
  match fd_lookup (m_fds m) oldfd with
  | none => ret_outcome (errno_ret EBADF) m
  | some e =>
      if !(dup_modeled_entry e) then Unmodeled
      else ret_outcome (errno_ret witness_errno) m

/-- Rocq: `Witness.Fs.File.dup_witness_ok`. -/
theorem dup_witness_ok (oldfd : word) (i : SyscallInput) (m : Model) :
    dup_spec oldfd i m (dup_witness oldfd m) := by
  unfold dup_spec dup_witness
  refine bind_step _ _ i m m m _ (get_model_ok i m) ?_
  cases hfd : fd_lookup (m_fds m) oldfd with
  | none => exact pure_ok _ i _
  | some e =>
    dsimp only
    cases hk : dup_modeled_entry e with
    | false =>
      simp only [Bool.not_false, ↓reduceIte]
      exact unmodeled_intro i m
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      apply alt_l
      refine bind_step _ _ i m witness_errno m _ (errno_head_witness _ _ i m) ?_
      exact pure_ok _ i m

/-- Rocq: `Witness.Fs.File.dup3_witness`. -/
def dup3_witness (oldfd newfd flags : word) (m : Model) : outcome SyscallEffect :=
  if !(dup3_flags_ok flags) then ret_outcome (errno_ret EINVAL) m
  else if bv_eqb oldfd newfd then ret_outcome (errno_ret EINVAL) m
  else if !(dup3_newfd_under_limit newfd m) then ret_outcome (errno_ret EBADF) m
  else
    match fd_lookup (m_fds m) oldfd with
    | none => ret_outcome (errno_ret EBADF) m
    | some e =>
        if !(dup_modeled_entry e) then Unmodeled
        else
          match fd_lookup (m_fds m) newfd with
          | none =>
              if bv_unsigned newfd < NR_OPEN_DEFAULT
              then ret_outcome newfd (with_fds (fd_insert (m_fds m) newfd e) m)
              else Unmodeled
          | some _ => ret_outcome newfd (with_fds (fd_insert (m_fds m) newfd e) m)

/-- Rocq: `Witness.Fs.File.dup3_witness_ok`. -/
theorem dup3_witness_ok (oldfd newfd flags : word) (i : SyscallInput) (m : Model) :
    dup3_spec oldfd newfd flags i m (dup3_witness oldfd newfd flags m) := by
  unfold dup3_spec dup3_witness
  refine bind_step _ _ i m m m _ (get_model_ok i m) ?_
  cases hf : dup3_flags_ok flags with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact pure_ok _ i _
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hne : bv_eqb oldfd newfd with
  | true =>
    simp only [↓reduceIte]
    exact pure_ok _ i _
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases hl : dup3_newfd_under_limit newfd m with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact pure_ok _ i _
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hfd : fd_lookup (m_fds m) oldfd with
  | none => exact pure_ok _ i _
  | some e =>
  dsimp only
  cases hk : dup_modeled_entry e with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hnf : fd_lookup (m_fds m) newfd with
  | some e2 =>
    dsimp only
    unfold set_fds
    refine bind_step _ _ i m () _ _ (modify_ok _ i m) ?_
    exact pure_ok _ i _
  | none =>
    dsimp only
    by_cases hb : bv_unsigned newfd < NR_OPEN_DEFAULT
    · simp only [hb, ↓reduceIte]
      unfold set_fds
      refine bind_step _ _ i m () _ _ (modify_ok _ i m) ?_
      exact pure_ok _ i _
    · simp only [hb, ↓reduceIte]
      exact unmodeled_intro i m

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.File
