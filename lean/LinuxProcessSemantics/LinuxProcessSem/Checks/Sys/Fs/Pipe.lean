import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Pipe
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Fs.Pipe — the pipe2 (59) checker, its frame lemma and its witness, with their proofs

Mirrors two Rocq files: `theories/LinuxProcessSem/Checks/Sys/Fs/Pipe.v`,
the checker `check_pipe2` with the model helpers `pipe2_fdr`,
`pipe2_fds1`, `pipe2_fdw`, `pipe2_model` and the four lemmas relating the
checker to the spec, and `theories/LinuxProcessSem/Checks/Witness/Fs/Pipe.v`,
the witness `pipe2_witness` with `pipe2_witness_ok`.  Both answer to
`Sys/Fs/Pipe.lean`, the twin of the spec they are judged against, and
through it to Linux `fs/pipe.c` and `fs/file.c`.  Not part of the trusted
specification: the checker is executable and the witness is a value, and
the lemmas are what tie either to `pipe2_spec`.  Its pins are
`Checks/Cases/Checks/Sys/Fs/Pipe.lean`, the checker's verdict on each
fixture of `Checks/Cases/Fs/Pipe.lean`.

The baseline named above is the 09-11 integration commit, an ancestor of
the branch this file lands on.  Both Rocq files, and the spec they read,
are byte-identical there to what the ticket's `f44244ad6b80` holds, so
the header names the commit the branch can retrace.

ONE FILE FOR TWO, and why.  Rocq keeps the checker under `Checks/Sys/`
and the witness under `Checks/Witness/` so that `ExecutableSpecs.v` and
`Progress.v` each import only the half it dispatches.  The Lean tree's
dispatcher takes a record instead — `CheckedArm`, in
`Checks/Sys/Dispatch.lean` — carrying the checker and the witness in one
value with the five proofs between them, and the arm's registration in
`Checks/Arms/Fs/Pipe.lean` — the conformance ticket's, not this file's —
builds one such arm from the five theorems below.  So the two halves are
written where that arm reads them.  Every definition keeps
its Rocq name.

THE FRAME LEMMA IS HERE, and the rest of the ledger argument is not.
Rocq states `check_pipe2_frame` in
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`, beside the alternation
that consumes it; the Lean tree states each arm's frame lemma in the
checker's own file — the header of `Checks/VmMapsDisjoint.lean` says so,
and `Checks/Sys/Fs/Select.lean` and `Checks/Sys/Fs/Sync.lean` are the
precedent — so `check_pipe2_frame` is below, after the four lemmas.  Its
proof is written out step by step rather than closed by that file's
`vm_frame`, because no checker file in the tree imports
`Checks/VmMapsDisjoint.lean` yet — that file's own header states the
opposite discipline, a checker importing it and closing the lemma by
`vm_frame`, and every merged checker departs from it the same way; the
`lean: base:` PR that first takes the import is where the two meet — and
its import chain would pull `Run`
and `Sys/Mm/*` into a file that needs the spec, the checker prelude and
the witness prelude — the last is the one piece of the checked-table chain
the witness proof cannot do without — and nothing else.  Nothing of
`Checks/Sys/Table.lean` is imported, which is what let it land before
the arm did.  The arm-level fact `arm_pipe2_preserves_vm`, the `CheckedArm`
value and the `arm_unfold` lemmas are in `Checks/Arms/Fs/Pipe.lean`, and
`tools/gen_lean_checked.py` renders the `checked_table` row and the
invariant alternatives from it.  The dispatcher applies the checker as `check_pipe2 i (in_arg i 0) (pipe_flags32 (in_arg i
1)) eff m`, as Rocq's `arm_pipe2` in `Checks/Sys/Dispatch.v` does and as
the spec's own row in `Sys/SyscallTable.v` narrows the same word: the
low-32 narrowing of the flag word is the arm's, not the checker's, and
the checker below sees the narrowed word.

SPELLINGS, said once.  Rocq tests the flag word as
`Z.eqb (Z.ldiff (bv_unsigned flags) pipe2_flags_mask) 0`; here it is
`bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 pipe2_flags_mask))) == 0`, on
the word, which is how `Sys/Fs/Pipe.lean` spells its own gate — the mask
is below `2^64`, so the two agree on every word.  `Z.eqb` is `==` on
`Int`, `negb`/`andb` are `!`/`&&`, `in_wmem i` is `i.in_wmem`, and
`Some`/`None` are `some`/`none`.  Each test below is spelled exactly as
the spec spells it, so that one `cases` on the shared term drives both
sides of every proof. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Pipe

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.File
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Pipe
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! ## The model a successful pipe2 leaves

The four helpers name the two descriptors and the post-model the spec's
success branch builds through `lowest_fd`, `set_fds` and `set_pipes`, so
that the checker can compare an offered copy-out against ONE computed
value: the spec chooses `fdr` and `fdw` by `choose`, and the completeness
proof is what shows the choice is forced — `lowest_fd`'s predicate pins
the fd to `alloc_fd`, so there is exactly one pair the spec admits, and it
is this one. -/

/-- The read end: the lowest free descriptor of the table as it stands.
Linux: `alloc_fd` (fs/file.c:570-613, Linux v6.18.46, commit
1f99e9ab748f) scans from `files->next_fd` with `find_next_fd` (:585) and
returns the first clear bit, which `__do_pipe_flags` (fs/pipe.c:982-1015)
takes first, through `get_unused_fd_flags` at :994.  Rocq:
`Checks.Sys.Fs.Pipe.pipe2_fdr`. -/
def pipe2_fdr (m : Model) : word := alloc_fd (m_fds m)

/-- The table with the read end installed, which is the table the write
end is allocated against: `__do_pipe_flags` asks for `fdw` at fs/pipe.c:999
only after `fdr` has been reserved at :994 (Linux v6.18.46), so the
second answer is the lowest free fd of a table in which the first is no
longer free.  Rocq: `Checks.Sys.Fs.Pipe.pipe2_fds1`. -/
def pipe2_fds1 (m : Model) (id : word) : List (word × FdEntry) :=
  fd_insert (m_fds m) (pipe2_fdr m) (.FdPipe id false)

/-- The write end: the lowest free descriptor once the read end is taken.
Rocq: `Checks.Sys.Fs.Pipe.pipe2_fdw`. -/
def pipe2_fdw (m : Model) (id : word) : word := alloc_fd (pipe2_fds1 m id)

/-- The model after a successful `pipe2`: both ends installed, the pipe's
buffer registered empty under the fresh id.  `pipe_new_id` is the model's
choice of id; the checker declines when it is already taken rather than
picking another, which is the `pipe_lookup … = some` arm of `check_pipe2`.
`Checks/Cases/Fs/Pipe.lean` carries a copy of these four builders, written
before this file existed so that its literals could be stated; the pins
file's `pipe2_model_agrees` holds the copy to this one by `rfl`, and the
copy retires when that file imports this one instead.
Rocq: `Checks.Sys.Fs.Pipe.pipe2_model`. -/
def pipe2_model (m : Model) (id : word) : Model :=
  with_pipes (pipe_insert (m_pipes m) id ([], 0))
    (with_fds (fd_insert (pipe2_fds1 m id) (pipe2_fdw m id) (.FdPipe id true)) m)

/-! ## The checker -/

/-- The executable form of `pipe2_spec`, arm for arm and in the spec's
order, which is Linux's: the flag word is tested before anything else
(`__do_pipe_flags`, fs/pipe.c:987-988, Linux v6.18.46, commit
1f99e9ab748f: `flags & ~(O_CLOEXEC | O_NONBLOCK | O_DIRECT |
O_NOTIFICATION_PIPE)` is `return -EINVAL`, and `O_NOTIFICATION_PIPE` is
`O_EXCL` by include/uapi/linux/watch_queue.h:9); the descriptor pair is
built next, in `__do_pipe_flags` :990-1006; and the copy-out to `fildes`
is last, in `do_pipe2` (fs/pipe.c:1032-1052, Linux v6.18.46), whose `copy_to_user` at
:1040 fails to `error = -EFAULT` at :1045 after both files and both fds
have been given back (:1041-1044), so the -EFAULT installs nothing.

What the arms cannot say for themselves:

* -EINVAL goes through `check_ret_only` because :988 precedes every
  allocation, so the return touches nothing;
* the non-zero accepted flag words are declined rather than modeled
  because each changes what follows — the descriptor modes
  `create_pipe_files` gives the two files (fs/pipe.c:945 and :956, Linux
  v6.18.46), close-on-exec through `get_unused_fd_flags(flags)` (:994,
  :999), the watch queue at :935-942 — and the spec states none of it;
* `pipe2_errnos` is admitted ahead of the copy-out on every arm that
  admits anything, because the environment may refuse the pair before
  `copy_to_user` is reached, and each of the three has more than one
  source, all inside `__do_pipe_flags` and so ahead of :1040: -EMFILE is
  `alloc_fd`'s `if (fd >= end)` against the soft `RLIMIT_NOFILE`
  (fs/file.c:591-593, `end` from `get_unused_fd_flags` at :617-622,
  Linux v6.18.46) and `expand_files`' `sysctl_nr_open` test (:310-311);
  -ENFILE is `alloc_empty_file`'s `files_stat.max_files` test
  (fs/file_table.c:248-255, returned at :278, Linux v6.18.46), reached
  from `create_pipe_files`' calls at fs/pipe.c:944-950 and :956-961 into
  `alloc_file_pseudo` (fs/file_table.c:408) and `alloc_file_clone`
  (fs/file_table.c:464), and `create_pipe_files`' own answer when
  `get_pipe_inode` (fs/pipe.c:886-924) hands it no inode (:932-933);
  -ENOMEM is those same file allocations failing for memory
  (`alloc_empty_file`, fs/file_table.c:258-260, Linux v6.18.46;
  `alloc_path_pseudo`, :400-402) and, only on a table that must grow past
  `max_fds` (fs/file.c:595, Linux v6.18.46), `alloc_fdtable`'s
  `ERR_PTR(-ENOMEM)` (:242) through `expand_files` (:596).
  -EFAULT joins them only where `access_ok` (`__access_ok`,
  include/asm-generic/access_ok.h:31-41, Linux v6.18.46: `size <= limit`
  and `addr <= limit - size`, which `access_okb` spells) or the probe of
  the first byte fails, since a copy that never started has written no
  prefix;
* the pair's bytes are `pipe_fd_bytes fdr fdw` because `fd[0] = fdr;
  fd[1] = fdw` (fs/pipe.c:1005-1006, Linux v6.18.46) is copied whole at
  :1040, and `fdr` is the lower because `__do_pipe_flags` reserves it
  first (:994 before :999);
* the two `fd_lookup … = some` arms are what refuse a table in which the
  computed fd is not actually free: the spec's `lowest_fd` demands
  `fd_lookup fds fd = none` as well as `fd = alloc_fd fds`, and
  `alloc_fd`'s scan is fuel-bounded, so the checker must test the first
  half rather than take it from the second;
* a `fildes` with some but not all of its eight bytes writable is
  declined because `copy_to_user` may have written a prefix before it
  failed, and the spec does not model the partial write.

Why `CheckUnmodeled` and never `CheckReject` on the declined arms: the
spec declines there, and `check_pipe2_complete_unmodeled` is the direction
that forbids grading a run the model cannot hold.  Rocq:
`Checks.Sys.Fs.Pipe.check_pipe2`. -/
def check_pipe2 (i : SyscallInput) (fildes flags : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if !(bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 pipe2_flags_mask))) == 0)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if !(w_is0 flags) then CheckUnmodeled
  else
    let id := pipe_new_id (m_pipes m)
    match pipe_lookup (m_pipes m) id with
    | some _ => CheckUnmodeled
    | none =>
        if !(access_okb fildes 8) then
          match eff with
          | SyscallEffect.mkEffectU ret [] [] [] [] [] =>
              if errno_ret_in (EFAULT :: pipe2_errnos) ret then CheckOk m [] else CheckReject
          | _ => CheckReject
        else
          match read_bytes_map i.in_wmem fildes (Z_to_bv 64 8) with
          | some _ =>
              match eff with
              | SyscallEffect.mkEffectU ret [] [] [] [] [] =>
                  if errno_ret_in pipe2_errnos ret then CheckOk m [] else CheckReject
              | SyscallEffect.mkEffectU ret [(a, bs)] [] [] [] [] =>
                  match fd_lookup (m_fds m) (pipe2_fdr m) with
                  | some _ => CheckReject
                  | none =>
                      match fd_lookup (pipe2_fds1 m id) (pipe2_fdw m id) with
                      | some _ => CheckReject
                      | none =>
                          if bv_eqb ret (Z_to_bv 64 0) && bv_eqb a fildes
                             && listN_eqb bs (pipe_fd_bytes (pipe2_fdr m) (pipe2_fdw m id))
                          then CheckOk (pipe2_model m id) [] else CheckReject
              | _ => CheckReject
          | none =>
              match read_bytes_map i.in_wmem fildes (Z_to_bv 64 1) with
              | none =>
                  match eff with
                  | SyscallEffect.mkEffectU ret [] [] [] [] [] =>
                      if errno_ret_in (EFAULT :: pipe2_errnos) ret then CheckOk m [] else CheckReject
                  | _ => CheckReject
              | some _ => CheckUnmodeled

/-- `listN_eqb` on equal lists, the shape the complete direction of the
pair arm reaches once `lowest_fd` has fixed both descriptors: written as a
rewrite rule because the `if` it sits in carries a `Decidable` instance
that `rw` cannot abstract through, so the condition has to be folded by
`simp only`, which re-derives the instance.  No Rocq twin — Rocq closes
the same step by `reflexivity` at the use site.  Its home is
`Checks/Sys/Prelude.lean`, beside `bv_eqb_refl`, the same lemma for
words; that file is frozen, so it waits here until a `lean: base:` PR
moves it, and the day the prelude gains the name, the `simp only [...,
listN_eqb_refl, ...]` in `check_pipe2_complete_ok` becomes ambiguous:
that is the condition under which this one leaves. -/
theorem listN_eqb_refl (l : List byte) : listN_eqb l l = true :=
  (listN_eqb_eq l l).mpr rfl

/-! ## The four lemmas

Each proof walks the same five tests in the same order on both sides —
the flag mask, the zero test, the id lookup, `access_ok`, the two
readability probes — with one `cases` or `generalize` per test, so that
the checker's arm and the spec's arm are reduced by the same equation
and what is left is one acceptor against one monadic program.  The
errno-only arms then come down to `errno_ret_in_true` one way and
`errno_ret_in_intro` the other; the pair arm to `lowest_fd`'s predicate,
which `choose_ok` discharges with the checker's `fd_lookup … = none`
hypotheses in the sound direction and which fixes both descriptors to
`alloc_fd` in the complete one. -/

/-- Accepting is sound: an accepted effect is one the spec admits, over
the spec's post-model, with no event.  Rocq:
`Checks.Sys.Fs.Pipe.check_pipe2_sound_ok`. -/
theorem check_pipe2_sound_ok (i : SyscallInput) (fildes flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_pipe2 i fildes flags eff m = CheckOk m' evs) :
    pipe2_spec fildes flags i m (Ok eff m' evs) := by
  unfold check_pipe2 at h
  unfold pipe2_spec
  apply bind_ok0 _ _ i m i m _ _ _ (input_ok i m)
  apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
  dsimp only at h ⊢
  cases hmask : (bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 pipe2_flags_mask))) == 0)
  · simp only [hmask, Bool.not_false, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  · simp only [hmask, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hz : w_is0 flags
    · simp only [hz, Bool.not_false, ↓reduceIte] at h
      cases h
    · simp only [hz, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize pipe_new_id (m_pipes m) = pid at h ⊢
      rcases hl : pipe_lookup (m_pipes m) pid with _ | st
      · simp only [hl] at h ⊢
        cases hacc : access_okb fildes 8
        · simp only [hacc, Bool.not_false, ↓reduceIte] at h ⊢
          split at h
          next ret =>
            cases hin : errno_ret_in (EFAULT :: pipe2_errnos) ret
            · simp only [hin, Bool.false_eq_true, ↓reduceIte] at h
              cases h
            · simp only [hin, ↓reduceIte] at h
              cases h
              obtain ⟨e, he, rfl⟩ := (errno_ret_in_true _ _).mp hin
              rcases List.mem_cons.mp he with rfl | ht
              · exact alt_r _ _ i m _ (pure_ok _ i m)
              · exact alt_l _ _ i m _
                  (bind_ok0 _ _ i m e m _ _ _ (errno_from_witness pipe2_errnos e i m ht)
                    (pure_ok _ i m))
          next => cases h
        · simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
          rcases hr8 : read_bytes_map i.in_wmem fildes (Z_to_bv 64 8) with _ | w8
          · simp only [hr8] at h ⊢
            rcases hr1 : read_bytes_map i.in_wmem fildes (Z_to_bv 64 1) with _ | w1
            · simp only [hr1] at h ⊢
              split at h
              next ret =>
                cases hin : errno_ret_in (EFAULT :: pipe2_errnos) ret
                · simp only [hin, Bool.false_eq_true, ↓reduceIte] at h
                  cases h
                · simp only [hin, ↓reduceIte] at h
                  cases h
                  obtain ⟨e, he, rfl⟩ := (errno_ret_in_true _ _).mp hin
                  rcases List.mem_cons.mp he with rfl | ht
                  · exact alt_r _ _ i m _ (pure_ok _ i m)
                  · exact alt_l _ _ i m _
                      (bind_ok0 _ _ i m e m _ _ _
                        (errno_from_witness pipe2_errnos e i m ht) (pure_ok _ i m))
              next => cases h
            · simp only [hr1] at h
              cases h
          · simp only [hr8] at h ⊢
            split at h
            next ret =>
              cases hin : errno_ret_in pipe2_errnos ret
              · simp only [hin, Bool.false_eq_true, ↓reduceIte] at h
                cases h
              · simp only [hin, ↓reduceIte] at h
                cases h
                obtain ⟨e, he, rfl⟩ := (errno_ret_in_true _ _).mp hin
                exact alt_l _ _ i m _
                  (bind_ok0 _ _ i m e m _ _ _ (errno_from_witness pipe2_errnos e i m he)
                    (pure_ok _ i m))
            next ret a bs =>
              rcases hfr : fd_lookup (m_fds m) (pipe2_fdr m) with _ | x
              · simp only [hfr] at h
                rcases hfw : fd_lookup (pipe2_fds1 m pid) (pipe2_fdw m pid) with _ | y
                · simp only [hfw] at h
                  cases hg : (bv_eqb ret (Z_to_bv 64 0) && bv_eqb a fildes
                      && listN_eqb bs (pipe_fd_bytes (pipe2_fdr m) (pipe2_fdw m pid)))
                  · simp only [hg, Bool.false_eq_true, ↓reduceIte] at h
                    cases h
                  · simp only [hg, ↓reduceIte] at h
                    cases h
                    simp only [Bool.and_eq_true, bv_eqb_eq, listN_eqb_eq] at hg
                    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hg
                    exact alt_r _ _ i m _
                      (bind_ok0 _ _ i m (pipe2_fdr m) m _ _ _
                        (choose_ok (fun fd => fd_lookup (m_fds m) fd = none ∧ fd = alloc_fd (m_fds m))
                          (pipe2_fdr m) i m ⟨hfr, rfl⟩)
                        (bind_ok0 _ _ i m (pipe2_fdw m pid) m _ _ _
                          (choose_ok (fun fd => fd_lookup (pipe2_fds1 m pid) fd = none
                                        ∧ fd = alloc_fd (pipe2_fds1 m pid))
                            (pipe2_fdw m pid) i m ⟨hfw, rfl⟩)
                          (bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m)
                            (bind_ok0 _ _ i _ () _ _ _ _ (modify_ok _ i _) (pure_ok _ i _)))))
                · simp only [hfw] at h
                  cases h
              · simp only [hfr] at h
                cases h
            next => cases h
      · simp only [hl] at h
        cases h

/-- Declining is sound: the checker declines exactly where the spec has an
`unmodeled` arm, and every other arm is an acceptor that never declines.  Rocq: `Checks.Sys.Fs.Pipe.check_pipe2_sound_unmodeled`. -/
theorem check_pipe2_sound_unmodeled (i : SyscallInput) (fildes flags : word) (eff : SyscallEffect)
    (m : Model) (h : check_pipe2 i fildes flags eff m = CheckUnmodeled) :
    pipe2_spec fildes flags i m Unmodeled := by
  unfold check_pipe2 at h
  unfold pipe2_spec
  apply bind_unmodeled2 _ _ i m i m [] (input_ok i m)
  apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
  dsimp only at h ⊢
  cases hmask : (bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 pipe2_flags_mask))) == 0)
  · simp only [hmask, Bool.not_false, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  · simp only [hmask, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hz : w_is0 flags
    · simp only [Bool.not_false, ↓reduceIte]
      exact unmodeled_intro i m
    · simp only [hz, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize pipe_new_id (m_pipes m) = pid at h ⊢
      rcases hl : pipe_lookup (m_pipes m) pid with _ | st
      · simp only [hl] at h ⊢
        cases hacc : access_okb fildes 8
        · simp only [hacc, Bool.not_false, ↓reduceIte] at h
          split at h
          next => split at h <;> cases h
          next => cases h
        · simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
          rcases hr8 : read_bytes_map i.in_wmem fildes (Z_to_bv 64 8) with _ | w8
          · simp only [hr8] at h ⊢
            rcases hr1 : read_bytes_map i.in_wmem fildes (Z_to_bv 64 1) with _ | w1
            · simp only [hr1] at h
              split at h
              next => split at h <;> cases h
              next => cases h
            · dsimp only
              exact unmodeled_intro i m
          · simp only [hr8] at h
            split at h
            next => split at h <;> cases h
            next =>
              split at h
              next => cases h
              next =>
                split at h
                next => cases h
                next => split at h <;> cases h
            next => cases h
      · dsimp only
        exact unmodeled_intro i m

/-- Accepting is complete: every outcome the spec admits is accepted,
with the spec's own post-model and events.  The monadic hypothesis is
unfolded to its existentials and `Ok` equations and taken apart by
`rcases`; on the pair arm this is where `lowest_fd` forces both
descriptors to `alloc_fd`, so that the spec's write is the checker's
computed one.  Rocq: `Checks.Sys.Fs.Pipe.check_pipe2_complete_ok`. -/
theorem check_pipe2_complete_ok (i : SyscallInput) (fildes flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : pipe2_spec fildes flags i m (Ok eff m' evs)) :
    check_pipe2 i fildes flags eff m = CheckOk m' evs := by
  unfold pipe2_spec at h
  have h := bind_input_model_inv _ i m _ h
  unfold check_pipe2
  dsimp only at h ⊢
  cases hmask : (bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 pipe2_flags_mask))) == 0)
  · simp only [hmask, Bool.not_false, ↓reduceIte] at h ⊢
    have h' : (Ok eff m' evs : outcome SyscallEffect)
        = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    injection h' with heff hm hevs
    subst heff hm hevs
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  · simp only [hmask, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hz : w_is0 flags
    · simp only [hz, Bool.not_false, ↓reduceIte] at h
      have h' : (Ok eff m' evs : outcome SyscallEffect) = Unmodeled := h
      cases h'
    · simp only [hz, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize pipe_new_id (m_pipes m) = pid at h ⊢
      rcases hl : pipe_lookup (m_pipes m) pid with _ | st
      · simp only [hl] at h ⊢
        cases hacc : access_okb fildes 8
        · simp only [hacc, Bool.not_false, ↓reduceIte] at h ⊢
          simp only [Monad.alt, Monad.bind, errno_from, Monad.choose, err_ret, ret_only,
            Monad.pure, outcome.Ok.injEq] at h
          rcases h with ⟨e, m1, evs1, evs2, ⟨x, hx, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl⟩
            | ⟨rfl, rfl, rfl⟩
          · dsimp only
            rw [errno_ret_in_intro _ _ (List.mem_cons_of_mem _ hx)]
            rfl
          · dsimp only
            rw [errno_ret_in_intro _ _ (List.mem_cons_self ..)]
            rfl
        · simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
          rcases hr8 : read_bytes_map i.in_wmem fildes (Z_to_bv 64 8) with _ | w8
          · simp only [hr8] at h ⊢
            rcases hr1 : read_bytes_map i.in_wmem fildes (Z_to_bv 64 1) with _ | w1
            · simp only [hr1] at h ⊢
              simp only [Monad.alt, Monad.bind, errno_from, Monad.choose, err_ret, ret_only,
                Monad.pure, outcome.Ok.injEq] at h
              rcases h with ⟨e, m1, evs1, evs2, ⟨x, hx, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl⟩
                | ⟨rfl, rfl, rfl⟩
              · dsimp only
                rw [errno_ret_in_intro _ _ (List.mem_cons_of_mem _ hx)]
                rfl
              · dsimp only
                rw [errno_ret_in_intro _ _ (List.mem_cons_self ..)]
                rfl
            · simp only [hr1] at h
              have h' : (Ok eff m' evs : outcome SyscallEffect) = Unmodeled := h
              cases h'
          · simp only [hr8] at h ⊢
            simp only [Monad.alt, Monad.bind, errno_from, Sys.Fs.File.lowest_fd, Monad.choose,
              err_ret, ret_only, set_fds, set_pipes, Monad.modify, Monad.pure,
              outcome.Ok.injEq] at h
            rcases h with ⟨e, m1, evs1, evs2, ⟨x, hx, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl⟩
              | ⟨fdr, m1, evs1, evs2, ⟨x, ⟨hx1, rfl⟩, rfl, rfl, rfl⟩,
                 ⟨fdw, m2, evs3, evs4, ⟨y, ⟨hy1, rfl⟩, rfl, rfl, rfl⟩,
                  ⟨u, m3, evs5, evs6, ⟨-, rfl, rfl⟩,
                   ⟨u', m4, evs7, evs8, ⟨-, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
            · dsimp only
              rw [errno_ret_in_intro _ _ hx]
              rfl
            · simp only [pipe2_fdr, pipe2_fds1, pipe2_fdw, pipe2_model, hx1, hy1, bv_eqb_refl,
                listN_eqb_refl, Bool.and_self, ↓reduceIte, List.nil_append]
      · simp only [hl] at h
        have h' : (Ok eff m' evs : outcome SyscallEffect) = Unmodeled := h
        cases h'

/-- Declining is complete: where the spec declines, the checker declines
whatever effect it is offered — the fail-closed direction.  On the arms
where the spec never declines, the hypothesis is an `Unmodeled` outcome
of a program built from `pure`, `choose` and `modify`, none of which
admits one, so it reduces to `False`.  Rocq:
`Checks.Sys.Fs.Pipe.check_pipe2_complete_unmodeled`. -/
theorem check_pipe2_complete_unmodeled (i : SyscallInput) (fildes flags : word) (m : Model)
    (eff : SyscallEffect) (h : pipe2_spec fildes flags i m Unmodeled) :
    check_pipe2 i fildes flags eff m = CheckUnmodeled := by
  unfold pipe2_spec at h
  have h := bind_input_model_inv _ i m _ h
  unfold check_pipe2
  dsimp only at h ⊢
  cases hmask : (bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 pipe2_flags_mask))) == 0)
  · simp only [hmask, Bool.not_false, ↓reduceIte] at h
    have h' : (Unmodeled : outcome SyscallEffect) = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := h
    cases h'
  · simp only [hmask, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hz : w_is0 flags
    · simp only [Bool.not_false, ↓reduceIte]
    · simp only [hz, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize pipe_new_id (m_pipes m) = pid at h ⊢
      rcases hl : pipe_lookup (m_pipes m) pid with _ | st
      · simp only [hl] at h ⊢
        cases hacc : access_okb fildes 8
        · simp only [hacc, Bool.not_false, ↓reduceIte] at h
          simp only [Monad.alt, Monad.bind, errno_from, Monad.choose, err_ret, ret_only,
            Monad.pure, reduceCtorEq, and_false, exists_false, or_self] at h
        · simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
          rcases hr8 : read_bytes_map i.in_wmem fildes (Z_to_bv 64 8) with _ | w8
          · simp only [hr8] at h ⊢
            rcases hr1 : read_bytes_map i.in_wmem fildes (Z_to_bv 64 1) with _ | w1
            · simp only [hr1] at h
              simp only [Monad.alt, Monad.bind, errno_from, Monad.choose, err_ret, ret_only,
                Monad.pure, reduceCtorEq, and_false, exists_false, or_self] at h
            · dsimp only
          · simp only [hr8] at h
            simp only [Monad.alt, Monad.bind, errno_from, Sys.Fs.File.lowest_fd, Monad.choose,
              err_ret, ret_only, set_fds, set_pipes, Monad.modify, Monad.pure, reduceCtorEq,
              and_false, exists_false, or_self] at h
      · dsimp only

/-! ## The frame lemma -/

/-- An accepted `pipe2` leaves the VM ledger where it was: every acceptor
hands back either the model it was given or `pipe2_model` of it, and
`pipe2_model` rebuilds the fd and pipe tables around an unchanged `m_vm`,
so the pair arm closes by `rfl` once its equation is opened.  This is the
fact the ledger invariant's alternation consumes for this arm, stated here
so that it does not wait on the arm; the header says why the steps are
written out rather than left to `vm_frame`.  The walk is the four lemmas'
— one `cases` or `generalize` per test, in the checker's order — and on
each acceptor the `CheckOk` equation is opened by `cases`, which fixes the
post-model.  Rocq: `VmMapsDisjoint.check_pipe2_frame`. -/
theorem check_pipe2_frame (i : SyscallInput) (fildes flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_pipe2 i fildes flags eff m = CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  unfold check_pipe2 at h
  dsimp only at h
  cases hmask : (bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 pipe2_flags_mask))) == 0)
  · simp only [hmask, Bool.not_false, ↓reduceIte] at h
    obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl
  · simp only [hmask, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    cases hz : w_is0 flags
    · simp only [hz, Bool.not_false, ↓reduceIte] at h
      cases h
    · simp only [hz, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      generalize pipe_new_id (m_pipes m) = pid at h
      rcases hl : pipe_lookup (m_pipes m) pid with _ | st
      · simp only [hl] at h
        cases hacc : access_okb fildes 8
        · simp only [hacc, Bool.not_false, ↓reduceIte] at h
          split at h
          next => split at h <;> cases h <;> rfl
          next => cases h
        · simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          rcases hr8 : read_bytes_map i.in_wmem fildes (Z_to_bv 64 8) with _ | w8
          · simp only [hr8] at h
            rcases hr1 : read_bytes_map i.in_wmem fildes (Z_to_bv 64 1) with _ | w1
            · simp only [hr1] at h
              split at h
              next => split at h <;> cases h <;> rfl
              next => cases h
            · simp only [hr1] at h
              cases h
          · simp only [hr8] at h
            split at h
            next => split at h <;> cases h <;> rfl
            next =>
              split at h
              next => cases h
              next =>
                split at h
                next => cases h
                next => split at h <;> cases h <;> rfl
            next => cases h
      · simp only [hl] at h
        cases h

/-! ## The witness — `Checks/Witness/Fs/Pipe.v` -/

/-- One admitted outcome at every input, which is what the progress
argument consumes.  The tests are the checker's, in the checker's order.
Where the spec admits an answer the witness returns -EMFILE, the head of
`pipe2_errnos`: the environment may always refuse the pair for want of a
descriptor (`alloc_fd`, fs/file.c:591-593, Linux v6.18.46, commit
1f99e9ab748f), before any copy-out, so this is admitted on every arm that
admits anything — including the `access_ok` failure and the unreadable
`fildes`, where -EFAULT would do too but is not the head of the
injected set.  `Unmodeled` IS an admissible outcome, so the declined
arms need no invented answer: the spec's own arm is
`unmodeled`, and exhibiting it is what makes this total.  `ret_outcome`
is `Checks/Witness/Prelude.lean`'s: the bare return over the model, no
event.  Rocq: `Checks.Witness.Fs.Pipe.pipe2_witness`. -/
def pipe2_witness (fildes flags : word) (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  if !(bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 pipe2_flags_mask))) == 0)
  then ret_outcome (errno_ret EINVAL) m
  else if !(w_is0 flags) then Unmodeled
  else
    match pipe_lookup (m_pipes m) (pipe_new_id (m_pipes m)) with
    | some _ => Unmodeled
    | none =>
        if !(access_okb fildes 8) then ret_outcome (errno_ret EMFILE) m
        else
          match read_bytes_map i.in_wmem fildes (Z_to_bv 64 8) with
          | some _ => ret_outcome (errno_ret EMFILE) m
          | none =>
              match read_bytes_map i.in_wmem fildes (Z_to_bv 64 1) with
              | none => ret_outcome (errno_ret EMFILE) m
              | some _ => Unmodeled

/-- The witness is admitted at every input.  -EMFILE is the head of
`pipe2_errnos`, which is what lets `errno_head_witness` pick it on each
arm that draws from the set.  Rocq:
`Checks.Witness.Fs.Pipe.pipe2_witness_ok`. -/
theorem pipe2_witness_ok (fildes flags : word) (i : SyscallInput) (m : Model) :
    pipe2_spec fildes flags i m (pipe2_witness fildes flags i m) := by
  unfold pipe2_spec pipe2_witness
  apply bind_step _ _ i m i m _ (input_ok i m)
  apply bind_step _ _ i m m m _ (get_model_ok i m)
  dsimp only
  cases (bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 pipe2_flags_mask))) == 0)
  · simp only [Bool.not_false, ↓reduceIte]
    exact pure_ok _ i m
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases w_is0 flags
    · simp only [Bool.not_false, ↓reduceIte]
      exact unmodeled_intro i m
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      generalize pipe_new_id (m_pipes m) = pid
      rcases pipe_lookup (m_pipes m) pid with _ | st
      · dsimp only
        cases access_okb fildes 8
        · simp only [Bool.not_false, ↓reduceIte]
          exact alt_l _ _ i m _
            (bind_step _ _ i m EMFILE m _ (errno_head_witness EMFILE [ENFILE, ENOMEM] i m)
              (pure_ok _ i m))
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rcases read_bytes_map i.in_wmem fildes (Z_to_bv 64 8) with _ | w8
          · dsimp only
            rcases read_bytes_map i.in_wmem fildes (Z_to_bv 64 1) with _ | w1
            · dsimp only
              exact alt_l _ _ i m _
                (bind_step _ _ i m EMFILE m _ (errno_head_witness EMFILE [ENFILE, ENOMEM] i m)
                  (pure_ok _ i m))
            · dsimp only
              exact unmodeled_intro i m
          · dsimp only
            exact alt_l _ _ i m _
              (bind_step _ _ i m EMFILE m _ (errno_head_witness EMFILE [ENFILE, ENOMEM] i m)
                (pure_ok _ i m))
      · dsimp only
        exact unmodeled_intro i m

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Pipe
