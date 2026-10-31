-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Sys/Fs/Stat.v
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Time.PosixTimers
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Stat

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058 -/

/-! # LinuxProcessSem.Checks.Sys.Fs.Stat — the readlinkat (78), newfstatat (79) and fstat (80) checkers, and their witnesses

Twin of `theories/LinuxProcessSem/Checks/Sys/Fs/Stat.v` (the checkers) and
`theories/LinuxProcessSem/Checks/Witness/Fs/Stat.v` (the witnesses), both
read at the f1006fe8 named above, which is the commit
`Sys/Fs/Stat.lean` names too.  The checkers are the computable side of
`Sys/Fs/Stat.lean`'s
specs and are NOT part of the trusted specification: what a run may trust
is the spec, and the lemmas here are what lets a verdict of a checker stand
for an answer of the spec.

The two Rocq files are one Lean module because the witnesses close
`ca_receptive` for the same `CheckedArm` the checkers close `ca_sound_*`
and `ca_complete_*` for, and the Lean tree has no `Checks/Witness/Fs/`
directory to mirror yet.  Which Rocq names have a twin here is a question
for the parity guards (which do not reach `Checks/` yet:
`check_lean_spec_parity.py` sweeps `Sys/`, and
`check_lean_cases_parity.py` reports the pins file `unmirrored`), not for
this header; three things about the names are not derivable from them.
The eight `check_fstat_devnull_*` and `check_fstat_urandom_*`
instantiations of the `check_fstat_chrdev_*` lemmas are here under Rocq's
names, beside the lemmas they instantiate.  The `Local` helpers of `Checks/Sys/Fs/Stat.v`
are shadowing copies of lemmas `Checks/Sys/Prelude.v` already declares,
whatever the comment beside them says about a deferred extraction, so
their content is in `Checks/Sys/Prelude.lean` under the Prelude's names —
`get_model_bind_ok_inv` and `get_model_bind_unmodeled_inv` for what
`Stat.v` spells `bind_get_model_ok_inv` and
`bind_get_model_unmodeled_inv`, the other four under the same names — and
only those two `Stat.v`-local spellings are absent here, the proofs going
through `bind_step get_model` and `bind_unmodeled2 get_model` instead.
Rocq's `Local Lemma newfstatat_core_witness_ok`
(`Checks/Witness/Fs/Stat.v`) is `newfstatat_core_spec_iff` read at the
witness and has no name of its own here, as that lemma's docstring says.

WHAT IS NOT HERE, AND WHOSE IT IS.  Rocq builds `arm_readlinkat`,
`arm_newfstatat` and `arm_fstat`, lists them in `checked_table`
(`Checks/Sys/Dispatch.v`), registers their `arm_unfold` equations, and
proves `check_readlinkat_frame`, `check_newfstatat_frame` and
`check_fstat_frame` in `Checks/VmMapsDisjoint.v`.  In the Lean port those
are the registration step of the conformance ticket for these arms, not
this file's: the
checkers land on the two preludes and the spec alone, and the checked
table's rows, the frame lemmas and the per-arm alternatives of the
`vm_maps` preservation proof are written when the arms are registered.
The frame lemmas need nothing this file does not already export: every
accepting leaf below is a `check_ret_only`, a `check_ret_only_copyins` or
a delivery, and `check_fstat_deliver_by_ok` is the fact a delivery's frame
follows from, with `State`'s `m_vmmaps_with_statpin` for the pinning
case.  This stops being true the day a leaf moves the model by anything
but `with_statpin`, and the frame lemma written at registration is the
check that fails then.

One lemma is stated here that Rocq keeps in `Uapi`: `stat_set_size_size_ok`,
which `Sys/Uapi/Fs.lean` declines to port for want of the little-endian
round trip, and which `fstat_file_witness_ok` alone uses.  The round trip
is not restated here: `Checks/Sys/Kernel/Time/PosixTimers.lean` already
carries it — `bytes_le_to_nat_of_le_bytes` and Rocq's
`bytes_le_to_Z_of_le_bytes` (`BvBase.v`) — for the same reason, its witness
needing them while `BvBase.lean` is frozen, and this file imports that
module for the one lemma rather than proving a second copy (the ticket's
ground rule: no helper copied when one exists).  THE DEBT: `Sys/Uapi/Fs.lean`'s
NOT PORTED note names a round trip the tree has carried since that checker
merged, and `stat_set_size_size_ok` lives here, out of its home, until the
`lean: base:` change `PosixTimers.lean`'s header asks for moves the round
trip to `BvBase.lean`; the same change moves this lemma to `Sys/Uapi/Fs.lean`,
deletes it here and repoints the import above.  A `lean: base:` port that
adds `stat_set_size_size_ok` to `Sys/Uapi/Fs.lean` before this file's copy
is deleted collides on the name. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Stat

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Stat
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! ## One leaf every arm below ends in

`err_ret e` is `Monad.pure` of the bare errno return, so it holds of exactly
one outcome.  Stated once here because all three cascades below —
`readlinkat`'s included — reach it on every answering leaf, in both
directions. -/

/-- Rocq has no twin: it unfolds `err_ret` in place (`sys_unfold`). -/
theorem err_ret_iff (e : Int) (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    err_ret e i m o ↔ o = Ok (mkEffect (errno_ret e) [] []) m [] := by
  unfold err_ret ret_only
  exact pure_iff _ i m o

/-! ## readlinkat (78)

`readlinkat_spec` answers before it reads: under `AT_FDCWD` it is -EINVAL for
every pathname and every buffer, and every other dirfd is declined.
`do_readlinkat` (fs/stat.c:563-602, Linux v6.18.46, commit 1f99e9ab748f)
answers -EINVAL at two sites.  The first is its `bufsiz <= 0` gate
(fs/stat.c:571-572), taken before `getname_flags` (:575) reads a byte: for
that half of the calls the spec's errno and its empty ledger are the
kernel's own, whatever the name (the spec never reads `bufsiz`, so it
cannot tell the halves apart; linux-process-semantics@ff0313ba4f:bugs/readlinkat-path-not-interpreted.md
names the gate).  The second is the `else` arm (fs/stat.c:592-594,
v6.18.46; the errno is the ternary at :593), which a call with a positive `bufsiz`
reaches only for a name that RESOLVES to something other than a symlink —
the only kind of node the modeled image holds.  The rest of this paragraph
is about that half.  A name that resolves to nothing is -ENOENT from
`filename_lookup` (fs/namei.c:2697-2705, Linux v6.18.46), which
`do_readlinkat` reaches before its `else` arm (fs/stat.c:576-579, Linux
v6.18.46), and the spec answers -EINVAL there too: one of the class of false
rejections linux-process-semantics@ff0313ba4f:bugs/readlinkat-path-not-interpreted.md records.  The class has a
member that entry does not list yet: `lookup_flags` is `LOOKUP_EMPTY` from the
start (fs/stat.c:569, Linux v6.18.46), so an empty name passes
`getname_flags`, which refuses it only without that flag (fs/namei.c:167-171,
Linux v6.18.46); `link_path_walk` returns for it before its first component
(fs/namei.c:2455-2458) with `last_type` still `LAST_ROOT` (fs/namei.c:2446),
`path_lookupat`'s loop (fs/namei.c:2675-2677) then calls `lookup_last`
(fs/namei.c:2647-2653, Linux v6.18.46), which hands the type to
`walk_component` (fs/namei.c:2142-2145) and it to `handle_dots`
(fs/namei.c:2096-2132, Linux v6.18.46), which returns `NULL` for anything but
`LAST_DOTDOT` and so moves nowhere, and the lookup ends where `path_init`
began — under `AT_FDCWD` the cwd (fs/namei.c:2590-2604, Linux v6.18.46) —
which is no symlink, so the `else` arm's ternary at fs/stat.c:593 (v6.18.46)
answers -ENOENT for the empty name under a positive `bufsiz` where the spec
commits to -EINVAL.  The checker takes the spec as it is; the entry names
three shapes and not this one, and adding it is a follow-up outside this
file. -/

/-- Rocq: `Stat.check_readlinkat`.  Declines every dirfd but `AT_FDCWD`, and
otherwise accepts one effect: the bare -EINVAL return with no writes and no
copy-in ledger, since `readlinkat_spec` records none. -/
def check_readlinkat (dirfd : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if !(bv_eqb dirfd AT_FDCWD32) then CheckUnmodeled
  else check_ret_only eff (errno_ret EINVAL) m []

/-- Rocq: `Stat.readlinkat_witness` (Checks/Witness/Fs/Stat.v). -/
def readlinkat_witness (dirfd : word) (m : Model) : outcome SyscallEffect :=
  if !(bv_eqb dirfd AT_FDCWD32) then Unmodeled
  else ret_outcome (errno_ret EINVAL) m

/-- Rocq: `Stat.check_readlinkat_sound_ok`. -/
theorem check_readlinkat_sound_ok (dirfd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_readlinkat dirfd eff m = CheckOk m' evs) :
    readlinkat_spec dirfd i m (Ok eff m' evs) := by
  unfold check_readlinkat at h
  unfold readlinkat_spec
  obtain ⟨c, hd⟩ : ∃ c, bv_eqb dirfd AT_FDCWD32 = c := ⟨_, rfl⟩
  cases c
  · simp only [hd, Bool.not_false, ↓reduceIte, reduceCtorEq] at h
  · simp only [hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨heff, hm, hevs⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    subst heff hevs m'
    exact pure_ok _ i m

/-- Rocq: `Stat.check_readlinkat_sound_unmodeled`. -/
theorem check_readlinkat_sound_unmodeled (dirfd : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_readlinkat dirfd eff m = CheckUnmodeled) :
    readlinkat_spec dirfd i m Unmodeled := by
  unfold check_readlinkat at h
  unfold readlinkat_spec
  obtain ⟨c, hd⟩ : ∃ c, bv_eqb dirfd AT_FDCWD32 = c := ⟨_, rfl⟩
  cases c
  · simp only [hd, Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  · simp only [hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

/-- Rocq: `Stat.check_readlinkat_complete_ok`. -/
theorem check_readlinkat_complete_ok (dirfd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput) (h : readlinkat_spec dirfd i m (Ok eff m' evs)) :
    check_readlinkat dirfd eff m = CheckOk m' evs := by
  unfold readlinkat_spec at h
  unfold check_readlinkat
  obtain ⟨c, hd⟩ : ∃ c, bv_eqb dirfd AT_FDCWD32 = c := ⟨_, rfl⟩
  cases c
  · simp only [hd, Bool.not_false, ↓reduceIte] at h
    rw [unmodeled_iff] at h
    cases h
  · simp only [hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    rw [err_ret_iff] at h
    injection h with heff hm hevs
    subst heff hevs m'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- Rocq: `Stat.check_readlinkat_complete_unmodeled`. -/
theorem check_readlinkat_complete_unmodeled (dirfd : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (h : readlinkat_spec dirfd i m Unmodeled) :
    check_readlinkat dirfd eff m = CheckUnmodeled := by
  unfold readlinkat_spec at h
  unfold check_readlinkat
  obtain ⟨c, hd⟩ : ∃ c, bv_eqb dirfd AT_FDCWD32 = c := ⟨_, rfl⟩
  cases c
  · simp only [hd, Bool.not_false, ↓reduceIte]
  · simp only [hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    rw [err_ret_iff] at h
    cases h

/-- Rocq: `Stat.readlinkat_witness_ok`. -/
theorem readlinkat_witness_ok (dirfd : word) (i : SyscallInput) (m : Model) :
    readlinkat_spec dirfd i m (readlinkat_witness dirfd m) := by
  unfold readlinkat_spec readlinkat_witness
  obtain ⟨c, hd⟩ : ∃ c, bv_eqb dirfd AT_FDCWD32 = c := ⟨_, rfl⟩
  cases c
  · simp only [hd, Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  · simp only [hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact pure_ok _ i m

/-! ## newfstatat (79)

Writing nothing is not reading nothing.  Every arm `newfstatat_core_spec`
answers is downstream of the strncpy_from_user call in `getname_flags`
(fs/namei.c:136-216, Linux v6.18.46, commit 1f99e9ab748f, the copy at :157;
its -EFAULT is returned as it is at :161-165, the empty name is -ENOENT at
:168-171 and a PATH_MAX-long one -ENAMETOOLONG at :207-211), which
`vfs_fstatat` (fs/stat.c:365-379, v6.18.46) reaches through
`getname_maybe_null` in the initializer of its `name` local (:370) before
anything else — `getname_flags (name, 0)` for every flag word without
`AT_EMPTY_PATH` (include/linux/fs.h:2944-2957), which every modeled flag
word is — and `SYSCALL_DEFINE4(newfstatat)`
(fs/stat.c:536-547, v6.18.46) reaches `cp_new_stat` (:546) on success alone.
So every answering arm carries the pathname's copy-in range, and the
acceptor is `check_ret_only_copyins`: the ledger must be exactly the range
`newfstatat_spec` records, the same range `Open.check_openat` demands, and
a kernel reporting no read, a longer one, or a shifted one is refused.  The
declining arms are the spec's own; where the checker declines, the spec
does. -/

/-- Rocq: `Stat.check_newfstatat`.  The flag word's errno first, then the
pathname's, then the dirfd's, then the file's: the kernel's errno PRIORITY,
which is not its chronology — `vfs_fstatat` fetches the name (fs/stat.c:370,
v6.18.46) before `vfs_statx` tests the flag mask (:348-350), and the fetch's
errno surfaces only in `filename_lookup` (fs/namei.c:2702-2703) after that
test — argued on `newfstatat_core_spec`, whose header derives it. -/
def check_newfstatat (i : SyscallInput) (dirfd pathp flag : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  let reads := [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
  if !(modeled_statat_flags flag) then CheckUnmodeled
  else
    match read_cstr i.in_mem pathp with
    | CstrTooLong => check_ret_only_copyins reads eff (errno_ret ENAMETOOLONG) m []
    | CstrFault => check_ret_only_copyins reads eff (errno_ret EFAULT) m []
    | CstrOk p =>
        if path_eqb p [] then check_ret_only_copyins reads eff (errno_ret ENOENT) m []
        else if !(bv_eqb dirfd AT_FDCWD32) then CheckUnmodeled
        else if path_eqb p dot_path then CheckUnmodeled
        else
          match fs_lookup (m_fs m) p with
          | none => check_ret_only_copyins reads eff (errno_ret ENOENT) m []
          | some _ => CheckUnmodeled

/-- Rocq: `Stat.newfstatat_core_witness` (Checks/Witness/Fs/Stat.v).  The
core spec is deterministic — every leaf is `unmodeled` or one `err_ret` —
so this is not merely a witness but the spec's whole extension
(`newfstatat_core_spec_iff`). -/
def newfstatat_core_witness (dirfd pathp flag : word) (i : SyscallInput) (m : Model) :
    outcome SyscallEffect :=
  if !(modeled_statat_flags flag) then Unmodeled
  else
    match read_cstr i.in_mem pathp with
    | CstrTooLong => ret_outcome (errno_ret ENAMETOOLONG) m
    | CstrFault => ret_outcome (errno_ret EFAULT) m
    | CstrOk p =>
        if path_eqb p [] then ret_outcome (errno_ret ENOENT) m
        else if !(bv_eqb dirfd AT_FDCWD32) then Unmodeled
        else if path_eqb p dot_path then Unmodeled
        else
          match fs_lookup (m_fs m) p with
          | none => ret_outcome (errno_ret ENOENT) m
          | some _ => Unmodeled

/-- Rocq: `Stat.newfstatat_witness` (Checks/Witness/Fs/Stat.v). -/
def newfstatat_witness (dirfd pathp flag : word) (i : SyscallInput) (m : Model) :
    outcome SyscallEffect :=
  outcome_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
    (newfstatat_core_witness dirfd pathp flag i m)

/-- The branch analysis every `newfstatat` lemma runs: the flag word, the
three answers of `read_cstr`, the empty name, the dirfd, `"."`, and the
lookup, in the order the spec, the checker and the witness all share.  Each
branch's hypothesis is rewritten at `loc` (a hypothesis, the goal, or both)
and the leaf is closed by the `unmodeled` tactic where the spec declines
and by the `answers` tactic where it returns an errno.  The discriminant is
generalised through an existential rather than `cases h : e`, so the
rewrite happens by `simp only` at every location alike and no location is
left untouched. -/
syntax "statat_cases " term:max term:max term:max term:max term:max
  (Lean.Parser.Tactic.location)? &" unmodeled " tactic &" answers " tactic : tactic

macro_rules
  | `(tactic| statat_cases $flag $i $pathp $dirfd $m $[$loc]? unmodeled $unm answers $ans) =>
    `(tactic| (
      obtain ⟨c, hfl⟩ : ∃ c, modeled_statat_flags $flag = c := ⟨_, rfl⟩
      cases c
      · simp only [hfl, Bool.not_false, ↓reduceIte] $[$loc]?
        $unm
      · simp only [hfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte] $[$loc]?
        obtain ⟨r, hr⟩ : ∃ r, read_cstr ($i).in_mem $pathp = r := ⟨_, rfl⟩
        cases r with
        | CstrTooLong =>
          simp only [hr] $[$loc]?
          $ans
        | CstrFault =>
          simp only [hr] $[$loc]?
          $ans
        | CstrOk p =>
          simp only [hr] $[$loc]?
          obtain ⟨c, hpe⟩ : ∃ c, path_eqb p [] = c := ⟨_, rfl⟩
          cases c
          · simp only [hpe, Bool.false_eq_true, ↓reduceIte] $[$loc]?
            obtain ⟨c, hd⟩ : ∃ c, bv_eqb $dirfd AT_FDCWD32 = c := ⟨_, rfl⟩
            cases c
            · simp only [hd, Bool.not_false, ↓reduceIte] $[$loc]?
              $unm
            · simp only [hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] $[$loc]?
              obtain ⟨c, hdot⟩ : ∃ c, path_eqb p dot_path = c := ⟨_, rfl⟩
              cases c
              · simp only [hdot, Bool.false_eq_true, ↓reduceIte] $[$loc]?
                obtain ⟨r, hfs⟩ : ∃ r, fs_lookup (m_fs $m) p = r := ⟨_, rfl⟩
                cases r with
                | none =>
                  simp only [hfs] $[$loc]?
                  $ans
                | some _ =>
                  simp only [hfs] $[$loc]?
                  $unm
              · simp only [hdot, ↓reduceIte] $[$loc]?
                $unm
          · simp only [hpe, ↓reduceIte] $[$loc]?
            $ans))

/-- The core spec holds of exactly its witness.  Rocq proves the four
checker lemmas and `newfstatat_witness_ok` by running the cascade in each;
here it runs twice — once for each direction of this equivalence — and the
lemmas below are its corollaries.  Rocq's `Local Lemma
newfstatat_core_witness_ok` (Checks/Witness/Fs/Stat.v) is this equivalence
read at `newfstatat_core_witness`, and has no separately named twin. -/
theorem newfstatat_core_spec_iff (dirfd pathp flag : word) (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    newfstatat_core_spec dirfd pathp flag i m o
      ↔ o = newfstatat_core_witness dirfd pathp flag i m := by
  unfold newfstatat_core_spec newfstatat_core_witness
  constructor
  · intro h
    have hb := bind_input_model_inv _ i m o h
    statat_cases flag i pathp dirfd m at hb ⊢
      unmodeled (rw [unmodeled_iff] at hb; exact hb)
      answers (rw [err_ret_iff] at hb; exact hb)
  · intro h
    subst h
    refine bind_step input _ i m i m _ (input_ok i m) ?_
    refine bind_step get_model _ i m m m _ (get_model_ok i m) ?_
    statat_cases flag i pathp dirfd m
      unmodeled (exact unmodeled_intro i m)
      answers (exact pure_ok _ i m)

/-- `newfstatat_spec` is `newfstatat_core_spec` under the pathname's copy-in
ledger, and so holds of exactly its witness too. -/
theorem newfstatat_spec_iff (dirfd pathp flag : word) (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    newfstatat_spec dirfd pathp flag i m o ↔ o = newfstatat_witness dirfd pathp flag i m := by
  unfold newfstatat_spec newfstatat_witness
  constructor
  · intro h
    cases o with
    | Unmodeled =>
      have h1 := input_bind_unmodeled_inv _ i m h
      have h2 := record_copyins_unmodeled_inv _ _ i m h1
      rw [newfstatat_core_spec_iff] at h2
      rw [← h2]
      rfl
    | Ok eff m' evs =>
      have h1 := input_bind_ok_inv _ i m _ m' evs h
      obtain ⟨core, hcore, heff⟩ := record_copyins_ok_inv _ _ i m eff m' evs h1
      rw [newfstatat_core_spec_iff] at hcore
      rw [← hcore, heff]
      rfl
  · intro h
    subst h
    refine bind_step input _ i m i m _ (input_ok i m) ?_
    exact record_copyins_outcome _ _ i m _
      ((newfstatat_core_spec_iff dirfd pathp flag i m _).mpr rfl)

/-- Rocq: `Stat.check_newfstatat_sound_ok`. -/
theorem check_newfstatat_sound_ok (i : SyscallInput) (dirfd pathp flag : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_newfstatat i dirfd pathp flag eff m = CheckOk m' evs) :
    newfstatat_spec dirfd pathp flag i m (Ok eff m' evs) := by
  unfold check_newfstatat at h
  rw [newfstatat_spec_iff]
  unfold newfstatat_witness newfstatat_core_witness
  statat_cases flag i pathp dirfd m at h ⊢
    unmodeled (cases h)
    answers (obtain ⟨heff, hm, hevs⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
             subst heff hevs m'
             rfl)

/-- Rocq: `Stat.check_newfstatat_sound_unmodeled`. -/
theorem check_newfstatat_sound_unmodeled (i : SyscallInput) (dirfd pathp flag : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_newfstatat i dirfd pathp flag eff m = CheckUnmodeled) :
    newfstatat_spec dirfd pathp flag i m Unmodeled := by
  unfold check_newfstatat at h
  rw [newfstatat_spec_iff]
  unfold newfstatat_witness newfstatat_core_witness
  statat_cases flag i pathp dirfd m at h ⊢
    unmodeled rfl
    answers (exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _))

/-- Rocq: `Stat.check_newfstatat_complete_ok`. -/
theorem check_newfstatat_complete_ok (i : SyscallInput) (dirfd pathp flag : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : newfstatat_spec dirfd pathp flag i m (Ok eff m' evs)) :
    check_newfstatat i dirfd pathp flag eff m = CheckOk m' evs := by
  rw [newfstatat_spec_iff] at h
  unfold newfstatat_witness newfstatat_core_witness at h
  unfold check_newfstatat
  statat_cases flag i pathp dirfd m at h ⊢
    unmodeled (simp only [outcome_copyins, reduceCtorEq] at h)
    answers (simp only [outcome_copyins, ret_outcome, List.append_nil] at h
             injection h with heff hm hevs
             subst heff hevs m'
             exact check_ret_only_copyins_refl _ _ _ _)

/-- Rocq: `Stat.check_newfstatat_complete_unmodeled`. -/
theorem check_newfstatat_complete_unmodeled (i : SyscallInput) (dirfd pathp flag : word)
    (m : Model) (eff : SyscallEffect) (h : newfstatat_spec dirfd pathp flag i m Unmodeled) :
    check_newfstatat i dirfd pathp flag eff m = CheckUnmodeled := by
  rw [newfstatat_spec_iff] at h
  unfold newfstatat_witness newfstatat_core_witness at h
  unfold check_newfstatat
  statat_cases flag i pathp dirfd m at h ⊢
    unmodeled (try rfl)
    answers (simp only [outcome_copyins, ret_outcome, reduceCtorEq] at h)

/-- Rocq: `Stat.newfstatat_witness_ok`. -/
theorem newfstatat_witness_ok (dirfd pathp flag : word) (i : SyscallInput) (m : Model) :
    newfstatat_spec dirfd pathp flag i m (newfstatat_witness dirfd pathp flag i m) :=
  (newfstatat_spec_iff dirfd pathp flag i m _).mpr rfl

/-! ## fstat (80): delivering a `struct stat`

`cp_new_stat` (fs/stat.c:470-507, Linux v6.18.46, commit 1f99e9ab748f) hands
all `sizeof(tmp)` = 128 bytes to ONE copy_to_user (:506) and returns 0,
so the accepted effect is exactly one write of `Uapi.STAT_SIZE` bytes at
`statbuf`, a zero return, and an empty copy-in ledger: `fstat` takes its
descriptor in a register and reads no user memory.  What the 128 bytes may
say is the spec's business (`Uapi.stat_buf_wf`, the arm's own predicate,
`Uapi.stat_stable_eqb` against the pin); what the checker adds is the pin
bookkeeping — installed on the branch that had none, held on the branch
that had one — the way `check_uname_copy` installs its choice. -/

/-- Rocq: `Stat.check_fstat_deliver_by`.  `ok` is the arm's own predicate on
the buffer: `stat_size_ok n` for a file, `stat_devnull_ok`/`stat_urandom_ok`
for a device; `pin` is the buffer already recorded for `p`, if any. -/
def check_fstat_deliver_by (ok : List byte → Bool) (statbuf : word) (p : path)
    (pin : Option (List byte)) (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | SyscallEffect.mkEffectU r [(a, bs)] [] [] [] [] =>
      if !(bv_eqb r (Z_to_bv 64 0) && bv_eqb a statbuf) then CheckReject
      else if !(stat_buf_wf bs && ok bs) then CheckReject
      else
        match pin with
        | some b0 => if stat_stable_eqb bs b0 then CheckOk m [] else CheckReject
        | none => CheckOk (with_statpin p bs m) []
  | _ => CheckReject

/-- Rocq: `Stat.check_fstat_deliver`: the file arm's instance, `n` the
length of the contents `Fs` holds for `p`. -/
def check_fstat_deliver (statbuf : word) (n : Nat) (p : path) (pin : Option (List byte))
    (eff : SyscallEffect) (m : Model) : check_result :=
  check_fstat_deliver_by (stat_size_ok n) statbuf p pin eff m

/-- Rocq: `Stat.check_fstat_deliver_by_no_unmodeled`. -/
theorem check_fstat_deliver_by_no_unmodeled (ok : List byte → Bool) (statbuf : word)
    (p : path) (pin : Option (List byte)) (eff : SyscallEffect) (m : Model) :
    check_fstat_deliver_by ok statbuf p pin eff m ≠ CheckUnmodeled := by
  intro h
  unfold check_fstat_deliver_by at h
  repeat' first | cases h | split at h

/-- Rocq: `Stat.check_fstat_deliver_no_unmodeled`. -/
theorem check_fstat_deliver_no_unmodeled (statbuf : word) (n : Nat) (p : path)
    (pin : Option (List byte)) (eff : SyscallEffect) (m : Model) :
    check_fstat_deliver statbuf n p pin eff m ≠ CheckUnmodeled :=
  check_fstat_deliver_by_no_unmodeled _ _ _ _ _ _

/-- What an accepted delivery is.  Rocq: `Stat.check_fstat_deliver_by_ok`. -/
theorem check_fstat_deliver_by_ok (ok : List byte → Bool) (statbuf : word) (p : path)
    (pin : Option (List byte)) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_fstat_deliver_by ok statbuf p pin eff m = CheckOk m' evs) :
    ∃ bs, eff = mkEffect (Z_to_bv 64 0) [(statbuf, bs)] [] ∧ evs = []
      ∧ stat_buf_wf bs = true ∧ ok bs = true
      ∧ ((∃ b0, pin = some b0 ∧ stat_stable_eqb bs b0 = true ∧ m' = m)
         ∨ (pin = none ∧ m' = with_statpin p bs m)) := by
  unfold check_fstat_deliver_by at h
  split at h
  · rename_i r a bs
    obtain ⟨c, hra⟩ : ∃ c, (bv_eqb r (Z_to_bv 64 0) && bv_eqb a statbuf) = c := ⟨_, rfl⟩
    cases c
    · simp only [hra, Bool.not_false, ↓reduceIte, reduceCtorEq] at h
    · simp only [hra, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨hr, ha⟩ := Bool.and_eq_true_iff.mp hra
      rw [bv_eqb_eq] at hr ha
      subst hr ha
      obtain ⟨c, hwo⟩ : ∃ c, (stat_buf_wf bs && ok bs) = c := ⟨_, rfl⟩
      cases c
      · simp only [hwo, Bool.not_false, ↓reduceIte, reduceCtorEq] at h
      · simp only [hwo, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨hwf, hok⟩ := Bool.and_eq_true_iff.mp hwo
        cases pin with
        | some b0 =>
          dsimp only at h
          obtain ⟨c, hst⟩ : ∃ c, stat_stable_eqb bs b0 = c := ⟨_, rfl⟩
          cases c
          · simp only [hst, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
          · simp only [hst, ↓reduceIte] at h
            injection h with hm hevs
            exact ⟨bs, rfl, hevs.symm, hwf, hok, Or.inl ⟨b0, rfl, hst, hm.symm⟩⟩
        | none =>
          dsimp only at h
          injection h with hm hevs
          exact ⟨bs, rfl, hevs.symm, hwf, hok, Or.inr ⟨rfl, hm.symm⟩⟩
  · cases h

/-- Rocq: `Stat.check_fstat_deliver_ok`. -/
theorem check_fstat_deliver_ok (statbuf : word) (n : Nat) (p : path) (pin : Option (List byte))
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_fstat_deliver statbuf n p pin eff m = CheckOk m' evs) :
    ∃ bs, eff = mkEffect (Z_to_bv 64 0) [(statbuf, bs)] [] ∧ evs = []
      ∧ stat_buf_wf bs = true ∧ stat_size_ok n bs = true
      ∧ ((∃ b0, pin = some b0 ∧ stat_stable_eqb bs b0 = true ∧ m' = m)
         ∨ (pin = none ∧ m' = with_statpin p bs m)) :=
  check_fstat_deliver_by_ok _ _ _ _ _ _ _ _ h

/-- The converse of `check_fstat_deliver_by_ok` on a pinned path: a
well-formed buffer the arm's predicate accepts and the pin holds stable is
accepted with the model unchanged.  Rocq closes the completeness proofs by
`rewrite`; this is that rewrite, stated once. -/
theorem check_fstat_deliver_by_pinned (ok : List byte → Bool) (statbuf : word) (p : path)
    (b0 bs : List byte) (m : Model) (hwf : stat_buf_wf bs = true) (hok : ok bs = true)
    (hst : stat_stable_eqb bs b0 = true) :
    check_fstat_deliver_by ok statbuf p (some b0) (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] []) m
      = CheckOk m [] := by
  unfold check_fstat_deliver_by
  simp only [bv_eqb_refl, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hwf, hok,
    hst]

/-- The converse on an unpinned path: accepted, and the buffer becomes the
pin. -/
theorem check_fstat_deliver_by_unpinned (ok : List byte → Bool) (statbuf : word) (p : path)
    (bs : List byte) (m : Model) (hwf : stat_buf_wf bs = true) (hok : ok bs = true) :
    check_fstat_deliver_by ok statbuf p none (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] []) m
      = CheckOk (with_statpin p bs m) [] := by
  unfold check_fstat_deliver_by
  simp only [bv_eqb_refl, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hwf, hok]

/-! ## fstat (80): the witness buffers

A regular file's first answer, before any pin: zeroes everywhere but
`st_mode`, which is `S_IFREG`, with `st_size` set by `Uapi.stat_set_size`
to the length `Fs` holds (`fstat_witness_buf`).  A device's: `S_IFCHR` in
`st_mode`, the device number in `st_rdev`
(include/uapi/asm-generic/stat.h:24-45, v6.18.46: `st_mode` at byte 16,
`st_rdev` at byte 32), zeroes elsewhere.  The facts about these constant
buffers are computed, as Rocq computes them by `vm_compute`. -/

/-- Rocq: `Stat.stat_witness_base` (Checks/Witness/Fs/Stat.v). -/
def stat_witness_base : List byte :=
  Z_to_le_bytes 16 0 ++ Z_to_le_bytes 4 S_IFREG ++ Z_to_le_bytes 108 0

/-- Rocq: `Stat.stat_witness_base_wf`. -/
theorem stat_witness_base_wf : stat_buf_wf stat_witness_base = true := by decide +kernel

/-- Rocq: `Stat.stat_witness_base_length`. -/
theorem stat_witness_base_length : stat_witness_base.length = 128 := by decide +kernel

/-- Rocq: `Stat.fstat_witness_buf` (Checks/Witness/Fs/Stat.v). -/
def fstat_witness_buf (n : Nat) (pin : Option (List byte)) : List byte :=
  match pin with
  | some b0 => stat_set_size n b0
  | none => stat_set_size n stat_witness_base

/-- Rocq: `Stat.stat_chrdev_witness_base` (Checks/Witness/Fs/Stat.v). -/
def stat_chrdev_witness_base (rdev : Int) : List byte :=
  Z_to_le_bytes 16 0 ++ Z_to_le_bytes 4 S_IFCHR ++ Z_to_le_bytes 12 0
  ++ Z_to_le_bytes 8 rdev ++ Z_to_le_bytes 88 0

/-- Rocq: `Stat.stat_devnull_witness_base`. -/
def stat_devnull_witness_base : List byte := stat_chrdev_witness_base DEVNULL_RDEV

/-- Rocq: `Stat.stat_urandom_witness_base`. -/
def stat_urandom_witness_base : List byte := stat_chrdev_witness_base URANDOM_RDEV

/-- Rocq: `Stat.stat_devnull_witness_base_wf`. -/
theorem stat_devnull_witness_base_wf : stat_buf_wf stat_devnull_witness_base = true := by
  decide +kernel

/-- Rocq: `Stat.stat_devnull_witness_base_ok`. -/
theorem stat_devnull_witness_base_ok : stat_devnull_ok stat_devnull_witness_base = true := by
  decide +kernel

/-- Rocq: `Stat.stat_urandom_witness_base_wf`. -/
theorem stat_urandom_witness_base_wf : stat_buf_wf stat_urandom_witness_base = true := by
  decide +kernel

/-- Rocq: `Stat.stat_urandom_witness_base_ok`. -/
theorem stat_urandom_witness_base_ok : stat_urandom_ok stat_urandom_witness_base = true := by
  decide +kernel

/-! ### `stat_set_size_size_ok`, out of its home

Rocq keeps this lemma in `Sys/Uapi.v`; `Sys/Uapi/Fs.lean` ports every
other `stat_set_size_*` lemma and declines this one for want of the
little-endian round trip.  The round trip is
`PosixTimers.bytes_le_to_nat_of_le_bytes` (see the header), read here at
eight bytes: `Z_to_le_bytes` then `bytes_le_to_Z` is reduction modulo
`2 ^ 64`, which is what `bv_unsigned (Z_to_bv 64 _)` computes. -/

/-- Rocq: `Uapi.stat_set_size_size_ok`, stated here for the reason the
section header gives. -/
theorem stat_set_size_size_ok (n : Nat) (bs : List byte) (hlen : bs.length = 128) :
    stat_size_ok n (stat_set_size n bs) = true := by
  have hfield : stat_field_le ST_SIZE_OFF 8 (stat_set_size n bs)
      = bv_unsigned (Z_to_bv 64 (n : Int)) := by
    unfold stat_field_le ST_SIZE_OFF
    rw [stat_set_size_field n bs (by omega)]
    unfold bytes_le_to_Z bv_unsigned Z_to_bv
    rw [Checks.Sys.Kernel.Time.PosixTimers.bytes_le_to_nat_of_le_bytes, BitVec.ofInt_natCast,
      BitVec.toNat_ofNat]
  unfold stat_size_ok
  rw [hfield, beq_self_eq_true, Bool.or_true]

/-! ## fstat (80): a regular file

`fstat_file_spec`'s order is `newfstat`'s (fs/stat.c:550-560, Linux
v6.18.46, commit 1f99e9ab748f): the descriptor's inode is read at :555 and
the struct is copied out at :559, in `vfs_fstat` (fs/stat.c:276-282) and
`cp_new_stat` (fs/stat.c:470-507) respectively.  So a path `Fs` no longer
holds is declined, then access_ok over the whole 128 bytes is -EFAULT
(the copy's own gate, fs/stat.c:506, v6.18.46), then a range only partly writable is
declined, then the pin decides which delivery the checker runs. -/

/-- Rocq: `Stat.check_fstat_file`. -/
def check_fstat_file (i : SyscallInput) (p : path) (statbuf : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match fs_lookup (m_fs m) p with
  | none => CheckUnmodeled
  | some data =>
      if !(access_okb statbuf STAT_SIZE) then check_ret_only eff (errno_ret EFAULT) m []
      else
        match read_bytes_map i.in_wmem statbuf (Z_to_bv 64 STAT_SIZE) with
        | none => CheckUnmodeled
        | some _ =>
            match statpin_lookup (m_statpins m) p with
            | some b0 =>
                if !(stat_buf_wf b0) then CheckUnmodeled
                else check_fstat_deliver statbuf data.length p (some b0) eff m
            | none => check_fstat_deliver statbuf data.length p none eff m

/-- Rocq: `Stat.fstat_file_witness` (Checks/Witness/Fs/Stat.v). -/
def fstat_file_witness (p : path) (statbuf : word) (i : SyscallInput) (m : Model) :
    outcome SyscallEffect :=
  match fs_lookup (m_fs m) p with
  | none => Unmodeled
  | some data =>
      if !(access_okb statbuf STAT_SIZE) then ret_outcome (errno_ret EFAULT) m
      else
        match read_bytes_map i.in_wmem statbuf (Z_to_bv 64 STAT_SIZE) with
        | none => Unmodeled
        | some _ =>
            match statpin_lookup (m_statpins m) p with
            | some b0 =>
                if !(stat_buf_wf b0) then Unmodeled
                else Ok (mkEffect (Z_to_bv 64 0)
                          [(statbuf, fstat_witness_buf data.length (some b0))] []) m []
            | none =>
                let bs := fstat_witness_buf data.length none
                Ok (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] []) (with_statpin p bs m) []

/-- The branch analysis every file-arm lemma runs: the lookup, `access_ok`,
the writable range, the pin and its well-formedness, in the order the spec,
the checker and the witness share.  Four leaves: `unmodeled` where the spec
declines, `efault` on the failed `access_ok`, `pinned` and `unpinned` for
the two deliveries.  Generalisation through an existential, as in
`statat_cases`, so every location is rewritten alike. -/
syntax "fstat_file_cases " term:max term:max term:max term:max
  (Lean.Parser.Tactic.location)? &" unmodeled " tactic &" efault " tactic
  &" pinned " tactic &" unpinned " tactic : tactic

macro_rules
  | `(tactic| fstat_file_cases $i $p $statbuf $m $[$loc]?
        unmodeled $unm efault $ef pinned $pn unpinned $un) =>
    `(tactic| (
      obtain ⟨r, hfs⟩ : ∃ r, fs_lookup (m_fs $m) $p = r := ⟨_, rfl⟩
      cases r with
      | none =>
        simp only [hfs] $[$loc]?
        $unm
      | some _ =>
        simp only [hfs] $[$loc]?
        obtain ⟨c, hacc⟩ : ∃ c, access_okb $statbuf STAT_SIZE = c := ⟨_, rfl⟩
        cases c
        · simp only [hacc, Bool.not_false, ↓reduceIte] $[$loc]?
          $ef
        · simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] $[$loc]?
          obtain ⟨r, hrd⟩ :
              ∃ r, read_bytes_map ($i).in_wmem $statbuf (Z_to_bv 64 STAT_SIZE) = r := ⟨_, rfl⟩
          cases r with
          | none =>
            simp only [hrd] $[$loc]?
            $unm
          | some _ =>
            simp only [hrd] $[$loc]?
            obtain ⟨r, hpin⟩ : ∃ r, statpin_lookup (m_statpins $m) $p = r := ⟨_, rfl⟩
            cases r with
            | none =>
              simp only [hpin] $[$loc]?
              $un
            | some _ =>
              simp only [hpin] $[$loc]?
              obtain ⟨c, hwf0⟩ : ∃ c, stat_buf_wf ‹List byte› = c := ⟨_, rfl⟩
              cases c
              · simp only [hwf0, Bool.not_false, ↓reduceIte] $[$loc]?
                $unm
              · simp only [hwf0, Bool.not_true, Bool.false_eq_true, ↓reduceIte] $[$loc]?
                $pn))

/-- Rocq: `Stat.check_fstat_file_sound_ok`. -/
theorem check_fstat_file_sound_ok (i : SyscallInput) (p : path) (statbuf : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_fstat_file i p statbuf eff m = CheckOk m' evs) :
    fstat_file_spec p statbuf i m (Ok eff m' evs) := by
  unfold check_fstat_file at h
  unfold fstat_file_spec
  refine bind_step input _ i m i m _ (input_ok i m) ?_
  refine bind_step get_model _ i m m m _ (get_model_ok i m) ?_
  fstat_file_cases i p statbuf m at h ⊢
    unmodeled (cases h)
    efault (obtain ⟨heff, hm, hevs⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
            subst heff hevs m'
            exact pure_ok _ i m)
    pinned (obtain ⟨bs, heff, hevs, hwf, hsz, hpin⟩ := check_fstat_deliver_ok _ _ _ _ _ _ _ _ h
            subst heff hevs
            rcases hpin with ⟨b1, hb1, hst, hm⟩ | ⟨hno, _⟩
            · injection hb1 with hb1
              subst hb1 m'
              rw [bind_choose_iff]
              exact ⟨bs, ⟨hwf, hsz, hst⟩, pure_ok _ i m⟩
            · cases hno)
    unpinned (obtain ⟨bs, heff, hevs, hwf, hsz, hpin⟩ := check_fstat_deliver_ok _ _ _ _ _ _ _ _ h
              subst heff hevs
              rcases hpin with ⟨_, hb1, _, _⟩ | ⟨_, hm⟩
              · cases hb1
              · subst hm
                rw [bind_choose_iff]
                exact ⟨bs, ⟨hwf, hsz⟩,
                  bind_ok0 _ _ i m () _ _ _ [] (modify_ok _ i m) (pure_ok _ i _)⟩)

/-- Rocq: `Stat.check_fstat_file_sound_unmodeled`. -/
theorem check_fstat_file_sound_unmodeled (i : SyscallInput) (p : path) (statbuf : word)
    (eff : SyscallEffect) (m : Model) (h : check_fstat_file i p statbuf eff m = CheckUnmodeled) :
    fstat_file_spec p statbuf i m Unmodeled := by
  unfold check_fstat_file at h
  unfold fstat_file_spec
  refine bind_unmodeled2 input _ i m i m [] (input_ok i m) ?_
  refine bind_unmodeled2 get_model _ i m m m [] (get_model_ok i m) ?_
  fstat_file_cases i p statbuf m at h ⊢
    unmodeled (exact unmodeled_intro i m)
    efault (exact absurd h (check_ret_only_no_unmodeled _ _ _ _))
    pinned (exact absurd h (check_fstat_deliver_no_unmodeled _ _ _ _ _ _))
    unpinned (exact absurd h (check_fstat_deliver_no_unmodeled _ _ _ _ _ _))

/-- Rocq: `Stat.check_fstat_file_complete_ok`. -/
theorem check_fstat_file_complete_ok (i : SyscallInput) (p : path) (statbuf : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : fstat_file_spec p statbuf i m (Ok eff m' evs)) :
    check_fstat_file i p statbuf eff m = CheckOk m' evs := by
  unfold fstat_file_spec at h
  have hb := bind_input_model_inv _ i m _ h
  unfold check_fstat_file
  fstat_file_cases i p statbuf m at hb ⊢
    unmodeled (rw [unmodeled_iff] at hb
               cases hb)
    efault (rw [err_ret_iff] at hb
            injection hb with heff hm hevs
            subst heff hevs m'
            exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩)
    pinned (simp only [bind_choose_iff, pure_iff] at hb
            obtain ⟨bs, ⟨hwf, hsz, hst⟩, hb⟩ := hb
            injection hb with heff hm hevs
            subst heff hevs m'
            exact check_fstat_deliver_by_pinned _ _ _ _ _ _ hwf hsz hst)
    unpinned (simp only [bind_choose_iff, set_statpin, bind_modify_iff, pure_iff] at hb
              obtain ⟨bs, ⟨hwf, hsz⟩, hb⟩ := hb
              injection hb with heff hm hevs
              subst heff hevs m'
              exact check_fstat_deliver_by_unpinned _ _ _ _ _ hwf hsz)

/-- Rocq: `Stat.check_fstat_file_complete_unmodeled`. -/
theorem check_fstat_file_complete_unmodeled (i : SyscallInput) (p : path) (statbuf : word)
    (m : Model) (eff : SyscallEffect) (h : fstat_file_spec p statbuf i m Unmodeled) :
    check_fstat_file i p statbuf eff m = CheckUnmodeled := by
  unfold fstat_file_spec at h
  have hb := bind_input_model_inv _ i m _ h
  unfold check_fstat_file
  fstat_file_cases i p statbuf m at hb ⊢
    unmodeled (try rfl)
    efault (rw [err_ret_iff] at hb
            cases hb)
    pinned (simp only [bind_choose_iff, pure_iff] at hb
            obtain ⟨_, _, hb⟩ := hb
            cases hb)
    unpinned (simp only [bind_choose_iff, set_statpin, bind_modify_iff, pure_iff] at hb
              obtain ⟨_, _, hb⟩ := hb
              cases hb)

/-- Rocq: `Stat.fstat_file_witness_ok`.  The pinned delivery re-sizes the
pin itself, so it is stable against it by `stat_set_size_stable`; the
unpinned one re-sizes `stat_witness_base`. -/
theorem fstat_file_witness_ok (p : path) (statbuf : word) (i : SyscallInput) (m : Model) :
    fstat_file_spec p statbuf i m (fstat_file_witness p statbuf i m) := by
  unfold fstat_file_spec fstat_file_witness
  refine bind_step input _ i m i m _ (input_ok i m) ?_
  refine bind_step get_model _ i m m m _ (get_model_ok i m) ?_
  fstat_file_cases i p statbuf m
    unmodeled (exact unmodeled_intro i m)
    efault (exact pure_ok _ i m)
    pinned (rw [bind_choose_iff]
            exact ⟨_, ⟨stat_set_size_wf _ _ (by assumption),
                stat_set_size_size_ok _ _ (stat_buf_wf_length _ (by assumption)),
                stat_set_size_stable _ _ (stat_buf_wf_length _ (by assumption))⟩,
              pure_ok _ i m⟩)
    unpinned (rw [bind_choose_iff]
              exact ⟨_, ⟨stat_set_size_wf _ _ stat_witness_base_wf,
                  stat_set_size_size_ok _ _ stat_witness_base_length⟩,
                bind_ok0 _ _ i m () _ _ _ [] (modify_ok _ i m) (pure_ok _ i _)⟩)

/-! ## fstat (80): a character device

`fstat_chrdev_spec` is the file arm without the lookup and with the
device's own predicate `ok` beside `stat_buf_wf`, checked on the pin as
well as on the delivery (the spec's docstring says why the pin is checked
against both). -/

/-- Rocq: `Stat.check_fstat_chrdev`. -/
def check_fstat_chrdev (ok : List byte → Bool) (p : path) (i : SyscallInput) (statbuf : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if !(access_okb statbuf STAT_SIZE) then check_ret_only eff (errno_ret EFAULT) m []
  else
    match read_bytes_map i.in_wmem statbuf (Z_to_bv 64 STAT_SIZE) with
    | none => CheckUnmodeled
    | some _ =>
        match statpin_lookup (m_statpins m) p with
        | some b0 =>
            if !(stat_buf_wf b0 && ok b0) then CheckUnmodeled
            else check_fstat_deliver_by ok statbuf p (some b0) eff m
        | none => check_fstat_deliver_by ok statbuf p none eff m

/-- Rocq: `Stat.check_fstat_devnull`. -/
def check_fstat_devnull (i : SyscallInput) (statbuf : word) (eff : SyscallEffect) (m : Model) :
    check_result :=
  check_fstat_chrdev stat_devnull_ok devnull_path i statbuf eff m

/-- Rocq: `Stat.check_fstat_urandom`. -/
def check_fstat_urandom (i : SyscallInput) (statbuf : word) (eff : SyscallEffect) (m : Model) :
    check_result :=
  check_fstat_chrdev stat_urandom_ok urandom_path i statbuf eff m

/-- Rocq: `Stat.fstat_chrdev_witness` (Checks/Witness/Fs/Stat.v).  On a pinned
path the witness delivers the pin itself, which is stable against itself;
on an unpinned one it delivers `base`, the device's constant buffer. -/
def fstat_chrdev_witness (p : path) (ok : List byte → Bool) (base : List byte) (statbuf : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  if !(access_okb statbuf STAT_SIZE) then ret_outcome (errno_ret EFAULT) m
  else
    match read_bytes_map i.in_wmem statbuf (Z_to_bv 64 STAT_SIZE) with
    | none => Unmodeled
    | some _ =>
        match statpin_lookup (m_statpins m) p with
        | some b0 =>
            if !(stat_buf_wf b0 && ok b0) then Unmodeled
            else Ok (mkEffect (Z_to_bv 64 0) [(statbuf, b0)] []) m []
        | none =>
            Ok (mkEffect (Z_to_bv 64 0) [(statbuf, base)] []) (with_statpin p base m) []

/-- Rocq: `Stat.fstat_devnull_witness`. -/
def fstat_devnull_witness (statbuf : word) (i : SyscallInput) (m : Model) :
    outcome SyscallEffect :=
  fstat_chrdev_witness devnull_path stat_devnull_ok stat_devnull_witness_base statbuf i m

/-- Rocq: `Stat.fstat_urandom_witness`. -/
def fstat_urandom_witness (statbuf : word) (i : SyscallInput) (m : Model) :
    outcome SyscallEffect :=
  fstat_chrdev_witness urandom_path stat_urandom_ok stat_urandom_witness_base statbuf i m

/-- `fstat_file_cases` without the lookup, and with the pin tested against
both predicates. -/
syntax "fstat_chrdev_cases " term:max term:max term:max term:max term:max
  (Lean.Parser.Tactic.location)? &" unmodeled " tactic &" efault " tactic
  &" pinned " tactic &" unpinned " tactic : tactic

macro_rules
  | `(tactic| fstat_chrdev_cases $ok $p $i $statbuf $m $[$loc]?
        unmodeled $unm efault $ef pinned $pn unpinned $un) =>
    `(tactic| (
      obtain ⟨c, hacc⟩ : ∃ c, access_okb $statbuf STAT_SIZE = c := ⟨_, rfl⟩
      cases c
      · simp only [hacc, Bool.not_false, ↓reduceIte] $[$loc]?
        $ef
      · simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] $[$loc]?
        obtain ⟨r, hrd⟩ :
            ∃ r, read_bytes_map ($i).in_wmem $statbuf (Z_to_bv 64 STAT_SIZE) = r := ⟨_, rfl⟩
        cases r with
        | none =>
          simp only [hrd] $[$loc]?
          $unm
        | some _ =>
          simp only [hrd] $[$loc]?
          obtain ⟨r, hpin⟩ : ∃ r, statpin_lookup (m_statpins $m) $p = r := ⟨_, rfl⟩
          cases r with
          | none =>
            simp only [hpin] $[$loc]?
            $un
          | some _ =>
            simp only [hpin] $[$loc]?
            obtain ⟨c, hwo⟩ : ∃ c, (stat_buf_wf ‹List byte› && $ok ‹List byte›) = c := ⟨_, rfl⟩
            cases c
            · simp only [hwo, Bool.not_false, ↓reduceIte] $[$loc]?
              $unm
            · simp only [hwo, Bool.not_true, Bool.false_eq_true, ↓reduceIte] $[$loc]?
              $pn))

/-- Rocq: `Stat.check_fstat_chrdev_sound_ok`. -/
theorem check_fstat_chrdev_sound_ok (ok : List byte → Bool) (p : path) (i : SyscallInput)
    (statbuf : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_fstat_chrdev ok p i statbuf eff m = CheckOk m' evs) :
    fstat_chrdev_spec p ok statbuf i m (Ok eff m' evs) := by
  unfold check_fstat_chrdev at h
  unfold fstat_chrdev_spec
  refine bind_step input _ i m i m _ (input_ok i m) ?_
  refine bind_step get_model _ i m m m _ (get_model_ok i m) ?_
  fstat_chrdev_cases ok p i statbuf m at h ⊢
    unmodeled (cases h)
    efault (obtain ⟨heff, hm, hevs⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
            subst heff hevs m'
            exact pure_ok _ i m)
    pinned (obtain ⟨bs, heff, hevs, hwf, hok, hpin⟩ := check_fstat_deliver_by_ok _ _ _ _ _ _ _ _ h
            subst heff hevs
            rcases hpin with ⟨b1, hb1, hst, hm⟩ | ⟨hno, _⟩
            · injection hb1 with hb1
              subst hb1 m'
              rw [bind_choose_iff]
              exact ⟨bs, ⟨hwf, hok, hst⟩, pure_ok _ i m⟩
            · cases hno)
    unpinned (obtain ⟨bs, heff, hevs, hwf, hok, hpin⟩ :=
                check_fstat_deliver_by_ok _ _ _ _ _ _ _ _ h
              subst heff hevs
              rcases hpin with ⟨_, hb1, _, _⟩ | ⟨_, hm⟩
              · cases hb1
              · subst hm
                rw [bind_choose_iff]
                exact ⟨bs, ⟨hwf, hok⟩,
                  bind_ok0 _ _ i m () _ _ _ [] (modify_ok _ i m) (pure_ok _ i _)⟩)

/-- Rocq: `Stat.check_fstat_chrdev_sound_unmodeled`. -/
theorem check_fstat_chrdev_sound_unmodeled (ok : List byte → Bool) (p : path) (i : SyscallInput)
    (statbuf : word) (eff : SyscallEffect) (m : Model)
    (h : check_fstat_chrdev ok p i statbuf eff m = CheckUnmodeled) :
    fstat_chrdev_spec p ok statbuf i m Unmodeled := by
  unfold check_fstat_chrdev at h
  unfold fstat_chrdev_spec
  refine bind_unmodeled2 input _ i m i m [] (input_ok i m) ?_
  refine bind_unmodeled2 get_model _ i m m m [] (get_model_ok i m) ?_
  fstat_chrdev_cases ok p i statbuf m at h ⊢
    unmodeled (exact unmodeled_intro i m)
    efault (exact absurd h (check_ret_only_no_unmodeled _ _ _ _))
    pinned (exact absurd h (check_fstat_deliver_by_no_unmodeled _ _ _ _ _ _))
    unpinned (exact absurd h (check_fstat_deliver_by_no_unmodeled _ _ _ _ _ _))

/-- Rocq: `Stat.check_fstat_chrdev_complete_ok`. -/
theorem check_fstat_chrdev_complete_ok (ok : List byte → Bool) (p : path) (i : SyscallInput)
    (statbuf : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : fstat_chrdev_spec p ok statbuf i m (Ok eff m' evs)) :
    check_fstat_chrdev ok p i statbuf eff m = CheckOk m' evs := by
  unfold fstat_chrdev_spec at h
  have hb := bind_input_model_inv _ i m _ h
  unfold check_fstat_chrdev
  fstat_chrdev_cases ok p i statbuf m at hb ⊢
    unmodeled (rw [unmodeled_iff] at hb
               cases hb)
    efault (rw [err_ret_iff] at hb
            injection hb with heff hm hevs
            subst heff hevs m'
            exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩)
    pinned (simp only [bind_choose_iff, pure_iff] at hb
            obtain ⟨bs, ⟨hwf, hok, hst⟩, hb⟩ := hb
            injection hb with heff hm hevs
            subst heff hevs m'
            exact check_fstat_deliver_by_pinned _ _ _ _ _ _ hwf hok hst)
    unpinned (simp only [bind_choose_iff, set_statpin, bind_modify_iff, pure_iff] at hb
              obtain ⟨bs, ⟨hwf, hok⟩, hb⟩ := hb
              injection hb with heff hm hevs
              subst heff hevs m'
              exact check_fstat_deliver_by_unpinned _ _ _ _ _ hwf hok)

/-- Rocq: `Stat.check_fstat_chrdev_complete_unmodeled`. -/
theorem check_fstat_chrdev_complete_unmodeled (ok : List byte → Bool) (p : path)
    (i : SyscallInput) (statbuf : word) (m : Model) (eff : SyscallEffect)
    (h : fstat_chrdev_spec p ok statbuf i m Unmodeled) :
    check_fstat_chrdev ok p i statbuf eff m = CheckUnmodeled := by
  unfold fstat_chrdev_spec at h
  have hb := bind_input_model_inv _ i m _ h
  unfold check_fstat_chrdev
  fstat_chrdev_cases ok p i statbuf m at hb ⊢
    unmodeled (try rfl)
    efault (rw [err_ret_iff] at hb
            cases hb)
    pinned (simp only [bind_choose_iff, pure_iff] at hb
            obtain ⟨_, _, hb⟩ := hb
            cases hb)
    unpinned (simp only [bind_choose_iff, set_statpin, bind_modify_iff, pure_iff] at hb
              obtain ⟨_, _, hb⟩ := hb
              cases hb)

/-! ### The two devices' own lemmas

Rocq instantiates the four `check_fstat_chrdev_*` lemmas at each device's
predicate and path under the device's name.  `check_fstat`'s proofs below
apply the chrdev lemmas directly, so nothing depends on these eight; they
are here so that every Rocq name has its twin, and each is the chrdev
lemma with `check_fstat_<device>` and `fstat_<device>_spec` unfolded. -/

/-- Rocq: `Stat.check_fstat_devnull_sound_ok`. -/
theorem check_fstat_devnull_sound_ok (i : SyscallInput) (statbuf : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_fstat_devnull i statbuf eff m = CheckOk m' evs) :
    fstat_devnull_spec statbuf i m (Ok eff m' evs) := by
  unfold check_fstat_devnull at h
  unfold fstat_devnull_spec
  exact check_fstat_chrdev_sound_ok _ _ _ _ _ _ _ _ h

/-- Rocq: `Stat.check_fstat_devnull_sound_unmodeled`. -/
theorem check_fstat_devnull_sound_unmodeled (i : SyscallInput) (statbuf : word)
    (eff : SyscallEffect) (m : Model) (h : check_fstat_devnull i statbuf eff m = CheckUnmodeled) :
    fstat_devnull_spec statbuf i m Unmodeled := by
  unfold check_fstat_devnull at h
  unfold fstat_devnull_spec
  exact check_fstat_chrdev_sound_unmodeled _ _ _ _ _ _ h

/-- Rocq: `Stat.check_fstat_devnull_complete_ok`. -/
theorem check_fstat_devnull_complete_ok (i : SyscallInput) (statbuf : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : fstat_devnull_spec statbuf i m (Ok eff m' evs)) :
    check_fstat_devnull i statbuf eff m = CheckOk m' evs := by
  unfold fstat_devnull_spec at h
  unfold check_fstat_devnull
  exact check_fstat_chrdev_complete_ok _ _ _ _ _ _ _ _ h

/-- Rocq: `Stat.check_fstat_devnull_complete_unmodeled`. -/
theorem check_fstat_devnull_complete_unmodeled (i : SyscallInput) (statbuf : word) (m : Model)
    (eff : SyscallEffect) (h : fstat_devnull_spec statbuf i m Unmodeled) :
    check_fstat_devnull i statbuf eff m = CheckUnmodeled := by
  unfold fstat_devnull_spec at h
  unfold check_fstat_devnull
  exact check_fstat_chrdev_complete_unmodeled _ _ _ _ _ _ h

/-- Rocq: `Stat.check_fstat_urandom_sound_ok`. -/
theorem check_fstat_urandom_sound_ok (i : SyscallInput) (statbuf : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_fstat_urandom i statbuf eff m = CheckOk m' evs) :
    fstat_urandom_spec statbuf i m (Ok eff m' evs) := by
  unfold check_fstat_urandom at h
  unfold fstat_urandom_spec
  exact check_fstat_chrdev_sound_ok _ _ _ _ _ _ _ _ h

/-- Rocq: `Stat.check_fstat_urandom_sound_unmodeled`. -/
theorem check_fstat_urandom_sound_unmodeled (i : SyscallInput) (statbuf : word)
    (eff : SyscallEffect) (m : Model) (h : check_fstat_urandom i statbuf eff m = CheckUnmodeled) :
    fstat_urandom_spec statbuf i m Unmodeled := by
  unfold check_fstat_urandom at h
  unfold fstat_urandom_spec
  exact check_fstat_chrdev_sound_unmodeled _ _ _ _ _ _ h

/-- Rocq: `Stat.check_fstat_urandom_complete_ok`. -/
theorem check_fstat_urandom_complete_ok (i : SyscallInput) (statbuf : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : fstat_urandom_spec statbuf i m (Ok eff m' evs)) :
    check_fstat_urandom i statbuf eff m = CheckOk m' evs := by
  unfold fstat_urandom_spec at h
  unfold check_fstat_urandom
  exact check_fstat_chrdev_complete_ok _ _ _ _ _ _ _ _ h

/-- Rocq: `Stat.check_fstat_urandom_complete_unmodeled`. -/
theorem check_fstat_urandom_complete_unmodeled (i : SyscallInput) (statbuf : word) (m : Model)
    (eff : SyscallEffect) (h : fstat_urandom_spec statbuf i m Unmodeled) :
    check_fstat_urandom i statbuf eff m = CheckUnmodeled := by
  unfold fstat_urandom_spec at h
  unfold check_fstat_urandom
  exact check_fstat_chrdev_complete_unmodeled _ _ _ _ _ _ h

/-! ### The character devices' witnesses

One witness lemma for the parametric arm and one instantiation per device,
as in Rocq's `Checks/Witness/Fs/Stat.v`; the witnesses themselves are
defined with the arm they answer for, above. -/

/-- Rocq: `Stat.fstat_chrdev_witness_ok`: for any `base` that is well formed
and passes the device's predicate. -/
theorem fstat_chrdev_witness_ok (p : path) (ok : List byte → Bool) (base : List byte)
    (hbwf : stat_buf_wf base = true) (hbok : ok base = true) (statbuf : word)
    (i : SyscallInput) (m : Model) :
    fstat_chrdev_spec p ok statbuf i m (fstat_chrdev_witness p ok base statbuf i m) := by
  unfold fstat_chrdev_spec fstat_chrdev_witness
  refine bind_step input _ i m i m _ (input_ok i m) ?_
  refine bind_step get_model _ i m m m _ (get_model_ok i m) ?_
  fstat_chrdev_cases ok p i statbuf m
    unmodeled (exact unmodeled_intro i m)
    efault (exact pure_ok _ i m)
    pinned (rw [bind_choose_iff]
            exact ⟨_, ⟨(Bool.and_eq_true_iff.mp (by assumption)).1,
                (Bool.and_eq_true_iff.mp (by assumption)).2, stat_stable_eqb_refl _⟩,
              pure_ok _ i m⟩)
    unpinned (rw [bind_choose_iff]
              exact ⟨_, ⟨hbwf, hbok⟩,
                bind_ok0 _ _ i m () _ _ _ [] (modify_ok _ i m) (pure_ok _ i _)⟩)

/-- Rocq: `Stat.fstat_devnull_witness_ok`. -/
theorem fstat_devnull_witness_ok (statbuf : word) (i : SyscallInput) (m : Model) :
    fstat_devnull_spec statbuf i m (fstat_devnull_witness statbuf i m) :=
  fstat_chrdev_witness_ok _ _ _ stat_devnull_witness_base_wf stat_devnull_witness_base_ok
    statbuf i m

/-- Rocq: `Stat.fstat_urandom_witness_ok`. -/
theorem fstat_urandom_witness_ok (statbuf : word) (i : SyscallInput) (m : Model) :
    fstat_urandom_spec statbuf i m (fstat_urandom_witness statbuf i m) :=
  fstat_chrdev_witness_ok _ _ _ stat_urandom_witness_base_wf stat_urandom_witness_base_ok
    statbuf i m

/-! ## fstat (80): the descriptor

`vfs_fstat` (fs/stat.c:276-282, Linux v6.18.46, commit 1f99e9ab748f) resolves
the descriptor before anything else and answers -EBADF for an empty one
(:279-280), so that is the one errno this arm asserts itself; every other
answer is the kind's.  The match is total on `FdEntry`, as the spec's is:
a new kind of file is a new decision, not a fall-through. -/

/-- Rocq: `Stat.check_fstat`. -/
def check_fstat (i : SyscallInput) (fd statbuf : word) (eff : SyscallEffect) (m : Model) :
    check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdChannel _) => CheckUnmodeled
  | some (.FdFile p _) => check_fstat_file i p statbuf eff m
  | some (.FdFileW p _) => check_fstat_file i p statbuf eff m
  | some (.FdFileA p _) => check_fstat_file i p statbuf eff m
  | some (.FdFileRW p _) => check_fstat_file i p statbuf eff m
  | some .FdDir => CheckUnmodeled
  | some (.FdSocket _) => CheckUnmodeled
  | some (.FdPipe _ _) => CheckUnmodeled
  | some (.FdDevNull _ _) => check_fstat_devnull i statbuf eff m
  | some .FdUrandom => check_fstat_urandom i statbuf eff m

/-- Rocq: `Stat.fstat_witness` (Checks/Witness/Fs/Stat.v).  Its `FdFileRW`
and `FdFileA` arms go through `fstat_file_witness`, as `check_fstat`'s and
the spec twin's do (`Sys/Fs/Stat.lean`'s header): the four file kinds
share one inode, and `struct stat` has no member the access mode or
`f_flags` decides. -/
def fstat_witness (fd statbuf : word) (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some (.FdChannel _) => Unmodeled
  | some (.FdFile p _) => fstat_file_witness p statbuf i m
  | some (.FdFileW p _) => fstat_file_witness p statbuf i m
  | some (.FdFileA p _) => fstat_file_witness p statbuf i m
  | some (.FdFileRW p _) => fstat_file_witness p statbuf i m
  | some .FdDir => Unmodeled
  | some (.FdSocket _) => Unmodeled
  | some (.FdPipe _ _) => Unmodeled
  | some (.FdDevNull _ _) => fstat_devnull_witness statbuf i m
  | some .FdUrandom => fstat_urandom_witness statbuf i m

/-- Rocq: `Stat.check_fstat_sound_ok`. -/
theorem check_fstat_sound_ok (i : SyscallInput) (fd statbuf : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_fstat i fd statbuf eff m = CheckOk m' evs) :
    fstat_spec fd statbuf i m (Ok eff m' evs) := by
  unfold check_fstat at h
  unfold fstat_spec
  refine bind_step get_model _ i m m m _ (get_model_ok i m) ?_
  obtain ⟨r, hfd⟩ : ∃ r, fd_lookup (m_fds m) fd = r := ⟨_, rfl⟩
  cases r with
  | none =>
    simp only [hfd] at h ⊢
    obtain ⟨heff, hm, hevs⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    subst heff hevs m'
    exact pure_ok _ i m
  | some e =>
    cases e <;> simp only [hfd] at h ⊢
    · cases h                                                     -- FdChannel
    · exact check_fstat_file_sound_ok _ _ _ _ _ _ _ h             -- FdFile
    · exact check_fstat_file_sound_ok _ _ _ _ _ _ _ h             -- FdFileW
    · exact check_fstat_file_sound_ok _ _ _ _ _ _ _ h             -- FdFileA
    · exact check_fstat_file_sound_ok _ _ _ _ _ _ _ h             -- FdFileRW
    · cases h                                                     -- FdDir
    · cases h                                                     -- FdSocket
    · cases h                                                     -- FdPipe
    · exact check_fstat_chrdev_sound_ok _ _ _ _ _ _ _ _ h         -- FdDevNull
    · exact check_fstat_chrdev_sound_ok _ _ _ _ _ _ _ _ h         -- FdUrandom

/-- Rocq: `Stat.check_fstat_sound_unmodeled`. -/
theorem check_fstat_sound_unmodeled (i : SyscallInput) (fd statbuf : word) (eff : SyscallEffect)
    (m : Model) (h : check_fstat i fd statbuf eff m = CheckUnmodeled) :
    fstat_spec fd statbuf i m Unmodeled := by
  unfold check_fstat at h
  unfold fstat_spec
  refine bind_unmodeled2 get_model _ i m m m [] (get_model_ok i m) ?_
  obtain ⟨r, hfd⟩ : ∃ r, fd_lookup (m_fds m) fd = r := ⟨_, rfl⟩
  cases r with
  | none =>
    simp only [hfd] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | some e =>
    cases e <;> simp only [hfd] at h ⊢
    · exact unmodeled_intro i m                                   -- FdChannel
    · exact check_fstat_file_sound_unmodeled _ _ _ _ _ h          -- FdFile
    · exact check_fstat_file_sound_unmodeled _ _ _ _ _ h          -- FdFileW
    · exact check_fstat_file_sound_unmodeled _ _ _ _ _ h          -- FdFileA
    · exact check_fstat_file_sound_unmodeled _ _ _ _ _ h          -- FdFileRW
    · exact unmodeled_intro i m                                   -- FdDir
    · exact unmodeled_intro i m                                   -- FdSocket
    · exact unmodeled_intro i m                                   -- FdPipe
    · exact check_fstat_chrdev_sound_unmodeled _ _ _ _ _ _ h      -- FdDevNull
    · exact check_fstat_chrdev_sound_unmodeled _ _ _ _ _ _ h      -- FdUrandom

/-- Rocq: `Stat.check_fstat_complete_ok`. -/
theorem check_fstat_complete_ok (i : SyscallInput) (fd statbuf : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : fstat_spec fd statbuf i m (Ok eff m' evs)) :
    check_fstat i fd statbuf eff m = CheckOk m' evs := by
  unfold fstat_spec at h
  have hb := bind_model_inv _ i m _ h
  unfold check_fstat
  obtain ⟨r, hfd⟩ : ∃ r, fd_lookup (m_fds m) fd = r := ⟨_, rfl⟩
  cases r with
  | none =>
    simp only [hfd] at hb ⊢
    rw [err_ret_iff] at hb
    injection hb with heff hm hevs
    subst heff hevs m'
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | some e =>
    cases e <;> simp only [hfd] at hb ⊢
    · rw [unmodeled_iff] at hb; cases hb                          -- FdChannel
    · exact check_fstat_file_complete_ok _ _ _ _ _ _ _ hb         -- FdFile
    · exact check_fstat_file_complete_ok _ _ _ _ _ _ _ hb         -- FdFileW
    · exact check_fstat_file_complete_ok _ _ _ _ _ _ _ hb         -- FdFileA
    · exact check_fstat_file_complete_ok _ _ _ _ _ _ _ hb         -- FdFileRW
    · rw [unmodeled_iff] at hb; cases hb                          -- FdDir
    · rw [unmodeled_iff] at hb; cases hb                          -- FdSocket
    · rw [unmodeled_iff] at hb; cases hb                          -- FdPipe
    · exact check_fstat_chrdev_complete_ok _ _ _ _ _ _ _ _ hb     -- FdDevNull
    · exact check_fstat_chrdev_complete_ok _ _ _ _ _ _ _ _ hb     -- FdUrandom

/-- Rocq: `Stat.check_fstat_complete_unmodeled`. -/
theorem check_fstat_complete_unmodeled (i : SyscallInput) (fd statbuf : word) (m : Model)
    (eff : SyscallEffect) (h : fstat_spec fd statbuf i m Unmodeled) :
    check_fstat i fd statbuf eff m = CheckUnmodeled := by
  unfold fstat_spec at h
  have hb := bind_model_inv _ i m _ h
  unfold check_fstat
  obtain ⟨r, hfd⟩ : ∃ r, fd_lookup (m_fds m) fd = r := ⟨_, rfl⟩
  cases r with
  | none =>
    simp only [hfd] at hb
    rw [err_ret_iff] at hb
    cases hb
  | some e =>
    cases e <;> simp only [hfd] at hb ⊢
    · exact check_fstat_file_complete_unmodeled _ _ _ _ _ hb      -- FdFile
    · exact check_fstat_file_complete_unmodeled _ _ _ _ _ hb      -- FdFileW
    · exact check_fstat_file_complete_unmodeled _ _ _ _ _ hb      -- FdFileA
    · exact check_fstat_file_complete_unmodeled _ _ _ _ _ hb      -- FdFileRW
    · exact check_fstat_chrdev_complete_unmodeled _ _ _ _ _ _ hb  -- FdDevNull
    · exact check_fstat_chrdev_complete_unmodeled _ _ _ _ _ _ hb  -- FdUrandom

/-- Rocq: `Stat.fstat_witness_ok`. -/
theorem fstat_witness_ok (fd statbuf : word) (i : SyscallInput) (m : Model) :
    fstat_spec fd statbuf i m (fstat_witness fd statbuf i m) := by
  unfold fstat_spec fstat_witness
  refine bind_step get_model _ i m m m _ (get_model_ok i m) ?_
  obtain ⟨r, hfd⟩ : ∃ r, fd_lookup (m_fds m) fd = r := ⟨_, rfl⟩
  cases r with
  | none =>
    simp only [hfd]
    exact pure_ok _ i m
  | some e =>
    cases e <;> simp only [hfd]
    · exact unmodeled_intro i m                                   -- FdChannel
    · exact fstat_file_witness_ok _ _ i m                         -- FdFile
    · exact fstat_file_witness_ok _ _ i m                         -- FdFileW
    · exact fstat_file_witness_ok _ _ i m                         -- FdFileA
    · exact fstat_file_witness_ok _ _ i m                         -- FdFileRW
    · exact unmodeled_intro i m                                   -- FdDir
    · exact unmodeled_intro i m                                   -- FdSocket
    · exact unmodeled_intro i m                                   -- FdPipe
    · exact fstat_devnull_witness_ok _ i m                        -- FdDevNull
    · exact fstat_urandom_witness_ok _ i m                        -- FdUrandom

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Stat
