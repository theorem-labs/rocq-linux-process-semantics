-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Sys/Fs/Open.v
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open
import LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-! rocq-baseline: f1006fe8178338a499b5e5c41be83006c4edd058 -/

/-! # LinuxProcessSem.Checks.Sys.Fs.Open — the openat (56), faccessat (48), faccessat2 (439), close (57) and ftruncate (46) checkers, their proofs, and their witnesses

Mirrors `theories/LinuxProcessSem/Checks/Sys/Fs/Open.v` (the executable
checkers `check_openat`, `check_faccessat`, `check_faccessat2`,
`check_close` and `check_ftruncate` and the lemmas relating each to its
spec) and
`theories/LinuxProcessSem/Checks/Witness/Fs/Open.v` (the receptiveness
witnesses and their `_ok` lemmas), in that order, as two sections of one
module.  Both Rocq files hold the checkers and witnesses for every
syscall `Sys/Fs/Open.v` defines; this module holds the openat ones, ported
by ticket C-Fs-Open-openat, the faccessat and faccessat2 ones, ported
by ticket C-Fs-Open-faccessat, the close one, ported by ticket
C-Fs-Open-close-ftruncate, and the ftruncate one, ported by ticket
C-Fs-Open-ftruncate once the spec twin had `ftruncate_spec` (#1198),
which landed after the close ticket merged.  The four tickets' entries in
`docs/lean-port/data/plan.json` name this one file, so the witnesses live
here rather than
under a `Checks/Witness/` mirror path, as
`Checks/Sys/Kernel/Groups.lean` did before them.  Not part of the trusted
specification: each checker is the computable side of its spec, and these
lemmas are what lets a verdict of the checker stand for an answer of the
spec.  Its pins are `Checks/Cases/Checks/Sys/Fs/Open.lean`.

THE BASELINE NAMED ABOVE, f1006fe8, is the commit both Rocq files were
read at, and it is the commit the spec twin `Sys/Fs/Open.lean` names.  It
sends `check_openat_tmp`'s create word through `check_openat_create`, so
that a `/tmp` name the image implies is a directory answers -EISDIR, and
moves that arm's `fs_under` decline into its read branch; the checker and
the witness below follow it.

EVERY ARM OF ROCQ'S CHECKER IS HERE.  `check_openat_resolved` answers the
append word (`check_openat_append`), the six read-write words
(`check_openat_rdwr`, with `creat` and `trunc` read off the word) and the
read-write exclusive-create word (`check_openat_rdwr_excl`), on the two
acceptors `check_open_append` and `check_open_rdwr`, which bind a
`State.FdFileA` and a `State.FdFileRW`.  O_WRONLY|O_CREAT|O_EXCL|O_APPEND
is not an arm of either: `modeled_open_flags` does not admit that word, so
the checker declines it before the pathname is read, and the `/dev/null`
and `/dev/urandom` arms answer it nowhere.  `check_ftruncate`
writes the writable body for `FdFileA` and again for `FdFileW | FdFileRW`,
as `ftruncate_spec` does.

THE ORDER OF THE GATES IS THE KERNEL'S, and it is what the top-level
`check_openat` pins first.  `do_sys_openat2` (fs/open.c, Linux v6.18.46)
runs `build_open_flags` before `getname`, so a flag word the model does
not interpret has to be declined before a pathname is read: the checker
answers `CheckUnmodeled` on `modeled_open_flags` first, and only then
compares the copy-in ledger and hands the rest to `check_openat_body`.
Within the body, `getname_flags` (fs/namei.c, Linux v6.18.46) is the
source of the three fetch answers — `-ENAMETOOLONG`, `-EFAULT` and the
`-ENOENT` of an empty string — and they precede every look at the dirfd,
which `path_init` is the first to read.  Which errno wins when two
conditions hold is therefore not a choice this file makes: it is the order
of those calls, transcribed.

WHAT THIS FILE HOLDS, AND WHAT IT LEAVES TO THE REGISTRATIONS.  The
checker, the four lemmas, the witness and its `_ok` need only the two
preludes and the spec, and are here, for openat, for the faccessat pair,
for close and for ftruncate alike.  The arms the checkers become — the
`CheckedArm` built from each one's five, its `arm_unfold` lemmas and the
facts the ledger and the invariant registry take for it — are the
registration step, and none of it is stated here: a registration writes
`Checks/Arms/Fs/Open.lean`, the one file `tools/gen_lean_checked.py`
reads it from.  The frame lemmas those facts are derived from split by
ticket: the openat, faccessat and close tickets left theirs to the
registration too, as their acceptance text assigned it, which departs
from the four checker twins before them, each of which states its
`*_frame` lemma beside its checker; the ftruncate half states its two,
`check_ftruncate_frame` and `check_ftruncate_fd_state_frame`, in its own
section below the four lemmas, as those twins do, and
`Checks/Arms/Fs/Open.lean` derives the arm's ledger and registry facts
from them.  openat's and close's frame lemmas are in
`Checks/Arms/Fs/Open.lean`.  This file also holds the frame fact of the
acceptor openat's lemma closes each acceptor call by,
`check_open_result_frame`, below `check_create_wronly` with its
`vm_done` rule: `Checks/VmMapsDisjoint.lean`'s `vm_done` docstring has
the checker twin register that rule from its own file, and the one
import here beyond the two preludes and the spec,
`Checks.VmMapsDisjoint`, is for it.  Every model openat's checker
changes comes out of that acceptor, which binds a descriptor
(`with_fds`); when the descriptor is `check_create_wronly`'s `FdFileW` —
the create word on a plain or `/tmp` name, an exclusive-create word on a
plain one — it also sets the path to an empty file in the image
(`with_fs`), and the `/dev/null` arm binds its descriptor alone,
whatever the word.  Neither setter reaches `m_vmmaps`.  The faccessat
pair's will rest on `check_access_exists_ok_inv`, since nothing there
changes the model.

THE PROOFS keep Rocq's shape: one lemma per arm and direction, each a
case split on the arm's own decisions, and one prelude lemma per leaf —
`check_ret_only_ok_iff` and `check_ret_only_no_unmodeled` for a
deterministic errno, `check_new_fd_result_ok_inv` and
`check_new_fd_result_no_unmodeled` below for a descriptor-minting arm.
Each decision is generalised out of both the checker and the spec before
the split, because Lean's `cases` on a `match` discriminant otherwise
leaves the hypothesis and the goal on different copies of it; the flag
word is generalised as `fl` first, since the spec binds it with a `let`
that `simp` unfolds on its own.  Where Rocq writes `refine_if` and
`refine_cstr` over `completes_ok`, the Lean proofs split directly; the
two predicates are ported for the statements, which name them. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Fs
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.File
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! ## The checker — `Checks/Sys/Fs/Open.v` -/

/-! ### The descriptor-minting acceptor

`open_result_spec` admits two outcomes: an errno drawn from
`openat_errnos`, or the lowest free descriptor with the model extended
by `mk`.  The kernel's side of the second is `alloc_fd` (fs/file.c:570-613,
Linux v6.18.46): the scan starts at `max(start, files->next_fd)` (:580-585),
with `start` 0 from `__get_unused_fd_flags` (:615-618), and `find_next_fd`
(:544-565) reports the first clear bit of the open-descriptor bitmap at or
above it.  That the result is the LOWEST free descriptor rests on
`__put_unused_fd` (:630-631) lowering `next_fd` on every close, so that
`next_fd` never exceeds the lowest free slot.  A kernel reporting any other
free descriptor — or one already held — is lying, and the acceptor
refuses it; a kernel reporting one of the environmental errnos has
answered where `alloc_fd` (`-EMFILE` at the limit), `get_unused_fd_flags`
or `do_filp_open` may, and is accepted with the model unchanged.  What
separates the two cases mechanically is `errno_ret_in`: a returned word
is an errno iff it is `-e` for some `e` in the set, and no descriptor the
scan can produce lands in that range, which `errno_ret_in_alloc_fd`
below proves from `State.alloc_fd_le`. -/

/-- The scan bound keeps every allocated descriptor out of the error
band: `alloc_fd` answers at most 4096 (`State.alloc_fd_le`), and the band
starts at `2^64 - 4095`.  Rocq: `alloc_fd_not_error_b`. -/
theorem alloc_fd_not_error_b (fds : List (word × FdEntry)) :
    addr_is_error_b (alloc_fd fds) = false := by
  unfold addr_is_error_b
  rw [decide_eq_false_iff_not]
  intro h
  have hle := alloc_fd_le fds
  have hbig : (4096 : Int) < two_pow_64 - 4096 := by decide
  exact Int.lt_irrefl _ (Int.lt_trans hbig (Int.lt_of_lt_of_le h hle))

/-- An allocated descriptor is never one of the set's errno words: the
prelude's `errno_ret_in_fd` needs the descriptor below `2^31`, and the
scan bound puts it at or below 4096.  Rocq: `errno_ret_in_alloc_fd`. -/
theorem errno_ret_in_alloc_fd (es : List Int) (fds : List (word × FdEntry))
    (hok : errnos_ok es = true) : errno_ret_in es (alloc_fd fds) = false :=
  errno_ret_in_fd es (alloc_fd fds) hok (Int.lt_of_le_of_lt (alloc_fd_le fds) (by decide))

/-- The four errnos of `openat_errnos` are all in `[1, 4095]`, which is
what `errno_ret_in_alloc_fd` asks of the set. -/
theorem openat_errnos_ok : errnos_ok openat_errnos = true := by decide

/-- Accept the effect of a descriptor-minting call whose failure modes
are the errnos `es`: the return alone, no ledgers, and either an errno of
`es` with the model unchanged, or the lowest free descriptor with the
model `mk` builds for it.  A held descriptor, a free one that is not the
lowest, and any ledger entry are refused.  Rocq: `check_new_fd_result`,
which `Checks/Sys/Fs/Open.v` shares with the socket checkers. -/
def check_new_fd_result (es : List Int) (eff : SyscallEffect) (m : Model)
    (mk : word → Model) : check_result :=
  match eff with
  | SyscallEffect.mkEffectU ret [] [] [] [] [] =>
      if errno_ret_in es ret then CheckOk m []
      else
        match fd_lookup (m_fds m) ret with
        | some _ => CheckReject
        | none =>
            if bv_eqb ret (alloc_fd (m_fds m)) then CheckOk (mk ret) [] else CheckReject
  | _ => CheckReject

/-- `check_new_fd_result` never declines: the arms it serves have no
`unmodeled` branch of their own.  Rocq: `check_new_fd_result_no_unmodeled`. -/
theorem check_new_fd_result_no_unmodeled (es : List Int) (eff : SyscallEffect) (m : Model)
    (mk : word → Model) : check_new_fd_result es eff m mk ≠ CheckUnmodeled := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws with
  | cons w ws => simp only [check_new_fd_result, ne_eq, reduceCtorEq, not_false_eq_true]
  | nil =>
  cases zs with
  | cons z zs => simp only [check_new_fd_result, ne_eq, reduceCtorEq, not_false_eq_true]
  | nil =>
  cases us with
  | cons u us => simp only [check_new_fd_result, ne_eq, reduceCtorEq, not_false_eq_true]
  | nil =>
  cases cs with
  | cons c cs => simp only [check_new_fd_result, ne_eq, reduceCtorEq, not_false_eq_true]
  | nil =>
  cases copyins with
  | cons c copyins => simp only [check_new_fd_result, ne_eq, reduceCtorEq, not_false_eq_true]
  | nil =>
  simp only [check_new_fd_result]
  cases errno_ret_in es ret with
  | true => simp only [↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases fd_lookup (m_fds m) ret with
    | some _ => simp only [ne_eq, reduceCtorEq, not_false_eq_true]
    | none =>
      cases bv_eqb ret (alloc_fd (m_fds m)) <;>
        simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true]

/-- What an accepting `check_new_fd_result` verdict says about its
inputs: the effect is a bare return, no event is emitted, and the return
is either an errno of the set with the model kept, or the free lowest
descriptor with the model `mk` builds.  The soundness lemmas below read
their cases off this. -/
theorem check_new_fd_result_ok_inv (es : List Int) (eff : SyscallEffect) (m : Model)
    (mk : word → Model) (m' : Model) (evs : List event)
    (h : check_new_fd_result es eff m mk = CheckOk m' evs) :
    evs = [] ∧ ∃ ret, eff = mkEffect ret [] []
      ∧ ((errno_ret_in es ret = true ∧ m' = m)
         ∨ (fd_lookup (m_fds m) ret = none ∧ ret = alloc_fd (m_fds m) ∧ m' = mk ret)) := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws with
  | cons w ws => simp only [check_new_fd_result, reduceCtorEq] at h
  | nil =>
  cases zs with
  | cons z zs => simp only [check_new_fd_result, reduceCtorEq] at h
  | nil =>
  cases us with
  | cons u us => simp only [check_new_fd_result, reduceCtorEq] at h
  | nil =>
  cases cs with
  | cons c cs => simp only [check_new_fd_result, reduceCtorEq] at h
  | nil =>
  cases copyins with
  | cons c copyins => simp only [check_new_fd_result, reduceCtorEq] at h
  | nil =>
  simp only [check_new_fd_result] at h
  cases hE : errno_ret_in es ret with
  | true =>
    simp only [hE, ↓reduceIte, check_result.CheckOk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, ret, rfl, Or.inl ⟨hE, rfl⟩⟩
  | false =>
    simp only [hE, Bool.false_eq_true, ↓reduceIte] at h
    cases hl : fd_lookup (m_fds m) ret with
    | some _ => simp only [hl, reduceCtorEq] at h
    | none =>
      simp only [hl] at h
      cases hF : bv_eqb ret (alloc_fd (m_fds m)) with
      | true =>
        simp only [hF, ↓reduceIte, check_result.CheckOk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [bv_eqb_eq] at hF
        exact ⟨rfl, ret, rfl, Or.inr ⟨hl, hF, rfl⟩⟩
      | false => simp only [hF, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-- `check_new_fd_result` over `openat_errnos`, the acceptor every
descriptor-minting arm of `openat` is.  Rocq: `check_open_result`. -/
def check_open_result : SyscallEffect → Model → (word → Model) → check_result :=
  check_new_fd_result openat_errnos

/-- The create-and-truncate acceptor: the descriptor is a `FdFileW` at
offset 0 and the image holds `p` empty, the two effects
`create_wronly` performs in that order.  Rocq: `check_create_wronly`. -/
def check_create_wronly (p : path) (eff : SyscallEffect) (m : Model) : check_result :=
  check_open_result eff m
    (fun fd => with_fds (fd_insert (m_fds m) fd (.FdFileW p (Z_to_bv 64 0)))
                 (with_fs (fs_set (m_fs m) p []) m))

/-- The append acceptor: the descriptor is a `FdFileA` at offset 0 and
the image holds `p`, created empty only if it was absent — the two
effects `open_append` performs, in that order.  Rocq:
`check_open_append`. -/
def check_open_append (p : path) (eff : SyscallEffect) (m : Model) : check_result :=
  check_open_result eff m
    (fun fd => with_fds (fd_insert (m_fds m) fd (.FdFileA p (Z_to_bv 64 0)))
                 (with_fs (append_open_fs (m_fs m) p) m))

/-- The read-write acceptor: the descriptor is a `FdFileRW` at offset 0
over the image `fs'` its caller computed — `open_rdwr` takes the image as
an argument because the four non-exclusive words differ only in it.
Rocq: `check_open_rdwr`. -/
def check_open_rdwr (p : path) (fs' : Fs.Fs) (eff : SyscallEffect) (m : Model)
    : check_result :=
  check_open_result eff m
    (fun fd => with_fds (fd_insert (m_fds m) fd (.FdFileRW p (Z_to_bv 64 0)))
                 (with_fs fs' m))

/-! ### The acceptor's ledger frame — `VmMapsDisjoint.v`

Rocq states `check_open_result_frame` in `Checks/VmMapsDisjoint.v` and
makes it the third alternative of its `vm_done`.  The Lean `vm_done`
(`Checks/VmMapsDisjoint.lean`) is extended by a `macro_rules` beside each
wrapper's frame lemma, and its docstring leaves this one to the checker
twin's own file, so the lemma and its rule are here, beside the
acceptor. -/

/-- What an accepting `check_open_result` leaves: the model it was handed
(an errno of `openat_errnos`), or `mk` of the descriptor it accepted.  Read
off `check_new_fd_result_ok_inv`.  Lean-only: `check_open_result_frame`
below, and `check_openat_fd_table_unique` and
`check_openat_pipes_within_capacity` in `Checks/Arms/Fs/Open.lean`, each
take their case split from it. -/
theorem check_open_result_cases {eff : SyscallEffect} {m : Model} {mk : word → Model}
    {m' : Model} {evs : List event}
    (h : check_open_result eff m mk = CheckOk m' evs) :
    m' = m ∨ ∃ fd, m' = mk fd := by
  unfold check_open_result at h
  obtain ⟨-, ret, -, ⟨-, hm⟩ | ⟨-, -, hm⟩⟩ :=
    check_new_fd_result_ok_inv _ _ _ _ _ _ h
  · exact Or.inl hm
  · exact Or.inr ⟨ret, hm⟩

/-- Rocq: `VmMapsDisjoint.check_open_result_frame`.  The descriptor-minting
acceptor answers with the model it was handed or with `mk` of a
descriptor, so when no model `mk` builds moves the ledger, neither does
the acceptor.  Rocq's proof walks the unfolded acceptor with `vm_step`;
this one reads the two accepting answers off
`check_open_result_cases`. -/
theorem check_open_result_frame (eff : SyscallEffect) (m : Model) (mk : word → Model)
    (m' : Model) (evs : List event) (hmk : ∀ fd, m_vmmaps (mk fd) = m_vmmaps m)
    (h : check_open_result eff m mk = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  rcases check_open_result_cases h with rfl | ⟨fd, rfl⟩
  · rfl
  · exact hmk fd

/-- The `vm_done` rule for `check_open_result`, Rocq's third `vm_done`
alternative: `eapply check_open_result_frame in H` with the `mk` premise
closed by `intros; reflexivity`.  The premise is a `by` block, elaborated
after the hypothesis has fixed `mk`, and the `.trans rfl` is that of
`check_efault_or_frame`'s rule in `Checks/VmMapsDisjoint.lean`, for the
reason its docstring gives. -/
macro_rules
  | `(tactic| vm_done $h:ident) =>
    `(tactic| exact (check_open_result_frame _ _ _ _ _ (by intros; rfl) $h:ident).trans rfl)

/-! ### The arms, in the order `openat_resolved_spec` tries them

Each is the spec's own decision tree with `check_ret_only` at a
deterministic errno and `check_open_result` at a descriptor.  Which errno
each arm answers, and why, is argued on the spec's twin; nothing here
re-derives it. -/

/-- The read word on a plain name.  Rocq: `check_openat_read`. -/
def check_openat_read (p : path) (eff : SyscallEffect) (m : Model) : check_result :=
  if path_is_dirref p then
    check_open_result eff m (fun fd => with_fds (fd_insert (m_fds m) fd .FdDir) m)
  else
    match fs_lookup (m_fs m) p with
    | none => check_ret_only eff (errno_ret ENOENT) m []
    | some _ =>
        check_open_result eff m
          (fun fd => with_fds (fd_insert (m_fds m) fd (.FdFile p (Z_to_bv 64 0))) m)

/-- The create word on a plain name.  Rocq: `check_openat_create`. -/
def check_openat_create (p : path) (eff : SyscallEffect) (m : Model) : check_result :=
  if path_is_dirref p || fs_under (m_fs m) p then check_ret_only eff (errno_ret EISDIR) m []
  else check_create_wronly p eff m

/-- The append word on a plain name.  Rocq: `check_openat_append`. -/
def check_openat_append (p : path) (eff : SyscallEffect) (m : Model) : check_result :=
  if path_is_dirref p || fs_under (m_fs m) p then check_ret_only eff (errno_ret EISDIR) m []
  else check_open_append p eff m

/-- The six non-exclusive read-write words on a plain name, with `creat`
and `trunc` the two bits that separate them.  Rocq: `check_openat_rdwr`. -/
def check_openat_rdwr (creat trunc : Bool) (p : path) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if path_is_dirref p || fs_under (m_fs m) p then check_ret_only eff (errno_ret EISDIR) m []
  else
    match fs_lookup (m_fs m) p with
    | none =>
        if creat then check_open_rdwr p (fs_set (m_fs m) p []) eff m
        else check_ret_only eff (errno_ret ENOENT) m []
    | some _ =>
        check_open_rdwr p (if trunc then fs_set (m_fs m) p [] else m_fs m) eff m

/-- The read-write exclusive-create word on a plain name.  Rocq:
`check_openat_rdwr_excl`. -/
def check_openat_rdwr_excl (p : path) (eff : SyscallEffect) (m : Model) : check_result :=
  if path_is_dirref p || fs_under (m_fs m) p then check_ret_only eff (errno_ret EEXIST) m []
  else
    match fs_lookup (m_fs m) p with
    | some _ => check_ret_only eff (errno_ret EEXIST) m []
    | none => check_open_rdwr p (fs_set (m_fs m) p []) eff m

/-- The exclusive-create words on a plain name.  Rocq: `check_openat_excl`. -/
def check_openat_excl (p : path) (eff : SyscallEffect) (m : Model) : check_result :=
  if path_is_dirref p || fs_under (m_fs m) p then check_ret_only eff (errno_ret EEXIST) m []
  else
    match fs_lookup (m_fs m) p with
    | some _ => check_ret_only eff (errno_ret EEXIST) m []
    | none => check_create_wronly p eff m

/-- The `O_DIRECTORY` word on a plain name: the one plain-name arm with
declines of its own, over `NAME_MAX` and an implied directory.
Rocq: `check_openat_dir`. -/
def check_openat_dir (p : path) (eff : SyscallEffect) (m : Model) : check_result :=
  if path_is_dirref p then
    check_open_result eff m (fun fd => with_fds (fd_insert (m_fds m) fd .FdDir) m)
  else if NAME_MAX < p.length then CheckUnmodeled
  else if fs_under (m_fs m) p then CheckUnmodeled
  else
    match fs_lookup (m_fs m) p with
    | none => check_ret_only eff (errno_ret ENOENT) m []
    | some _ => check_ret_only eff (errno_ret ENOTDIR) m []

/-- `/etc/localtime`.  Rocq: `check_openat_localtime`. -/
def check_openat_localtime (flags : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match fs_lookup (m_fs m) localtime_path with
  | some _ => CheckUnmodeled
  | none =>
      if fs_under (m_fs m) localtime_path then CheckUnmodeled
      else if flag_set (bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags)))) O_CREAT
      then CheckUnmodeled
      else check_ret_only eff (errno_ret ENOENT) m []

/-- A `/dev/null` descriptor with the given read and write halves.
Rocq: `check_open_devnull`. -/
def check_open_devnull (rd wr : Bool) (eff : SyscallEffect) (m : Model) : check_result :=
  check_open_result eff m (fun fd => with_fds (fd_insert (m_fds m) fd (.FdDevNull rd wr)) m)

/-- `/dev/null`, by flag word.  Rocq: `check_openat_devnull`. -/
def check_openat_devnull (flags : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match fs_lookup (m_fs m) devnull_path with
  | some _ => CheckUnmodeled
  | none =>
      if fs_under (m_fs m) devnull_path then CheckUnmodeled
      else
        let fl := bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags)))
        if fl == 0 then check_open_devnull true false eff m
        else if fl == wr_create_flags then check_open_devnull false true eff m
        else if is_excl_create fl then check_ret_only eff (errno_ret EEXIST) m []
        else if fl == O_DIRECTORY then check_ret_only eff (errno_ret ENOTDIR) m []
        else if fl == append_create_flags then check_open_devnull false true eff m
        else if rdwr_open_word fl then check_open_devnull true true eff m
        else if is_rdwr_excl_create fl then check_ret_only eff (errno_ret EEXIST) m []
        else CheckUnmodeled

/-- A `/dev/urandom` descriptor.  Rocq: `check_open_urandom`. -/
def check_open_urandom (eff : SyscallEffect) (m : Model) : check_result :=
  check_open_result eff m (fun fd => with_fds (fd_insert (m_fds m) fd .FdUrandom) m)

/-- `/dev/urandom`, by flag word.  Rocq: `check_openat_urandom`. -/
def check_openat_urandom (flags : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match fs_lookup (m_fs m) urandom_path with
  | some _ => CheckUnmodeled
  | none =>
      if fs_under (m_fs m) urandom_path then CheckUnmodeled
      else
        let fl := bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags)))
        if fl == 0 then check_open_urandom eff m
        else if is_excl_create fl then check_ret_only eff (errno_ret EEXIST) m []
        else if fl == O_DIRECTORY then check_ret_only eff (errno_ret ENOTDIR) m []
        else if is_rdwr_excl_create fl then check_ret_only eff (errno_ret EEXIST) m []
        else CheckUnmodeled

/-- `/tmp/<n>`, with `p` the whole key.  Rocq: `check_openat_tmp`. -/
def check_openat_tmp (n p : path) (flags : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if NAME_MAX < n.length then CheckUnmodeled
  else
    let fl := bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags)))
    if fl == 0 then
      (if fs_under (m_fs m) p then CheckUnmodeled
       else match fs_lookup (m_fs m) p with
            | none => CheckUnmodeled
            | some _ => check_openat_read p eff m)
    else if fl == wr_create_flags then check_openat_create p eff m
    else CheckUnmodeled

/-- A pathname with a separator: the three device and zone paths, the
`/tmp` family, and a decline for everything else.  Rocq: `check_openat_sep`. -/
def check_openat_sep (p : path) (flags : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if path_eqb p localtime_path then check_openat_localtime flags eff m
  else if path_eqb p devnull_path then check_openat_devnull flags eff m
  else if path_eqb p urandom_path then check_openat_urandom flags eff m
  else
    match tmp_name p with
    | some n => check_openat_tmp n p flags eff m
    | none => CheckUnmodeled

/-- A resolved pathname, by word, in the order `openat_resolved_spec`
tries them.  Rocq: `check_openat_resolved`. -/
def check_openat_resolved (p : path) (flags : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if path_has_slash p then check_openat_sep p flags eff m
  else
    let fl := bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags)))
    if fl == 0 then check_openat_read p eff m
    else if fl == wr_create_flags then check_openat_create p eff m
    else if is_excl_create fl then check_openat_excl p eff m
    else if fl == O_DIRECTORY then check_openat_dir p eff m
    else if fl == append_create_flags then check_openat_append p eff m
    else if rdwr_open_word fl then
      check_openat_rdwr (flag_set fl O_CREAT) (flag_set fl O_TRUNC) p eff m
    else if is_rdwr_excl_create fl then check_openat_rdwr_excl p eff m
    else CheckUnmodeled

/-- The body after the flag gate: the three answers of `getname_flags`
(fs/namei.c, Linux v6.18.46) — `-ENAMETOOLONG` at `PATH_MAX`, the
`-EFAULT` its `strncpy_from_user` passes through, `-ENOENT` on an empty
string — then the dirfd, then the resolved name.  Rocq: `check_openat_body`. -/
def check_openat_body (i : SyscallInput) (dirfd pathp flags : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match read_cstr i.in_mem pathp with
  | CstrTooLong => check_ret_only eff (errno_ret ENAMETOOLONG) m []
  | CstrFault => check_ret_only eff (errno_ret EFAULT) m []
  | CstrOk p =>
      if path_eqb p [] then check_ret_only eff (errno_ret ENOENT) m []
      else if !bv_eqb dirfd AT_FDCWD32 then CheckUnmodeled
      else check_openat_resolved p flags eff m

/-- The `openat` checker.  The flag gate comes first because
`do_sys_openat2` (fs/open.c, Linux v6.18.46) calls `build_open_flags`
before `getname`; then the copy-in ledger is compared against the one
range the pathname fetch reads — the prefix through the first NUL, or to
the fault, or to `PATH_MAX` — before the body sees the effect with that
ledger cleared.  The range is a model of what `getname_flags` reads and
not of how: `strncpy_from_user` reads a word at a time
(`do_strncpy_from_user`, lib/strncpy_from_user.c, Linux v6.18.46), so
the kernel's own accesses can run past the NUL within the last word, and
`linux-process-semantics@ff0313ba4f:bugs/openat-getname-word-at-a-time.md`
records the gap.  Rocq: `check_openat`. -/
def check_openat (i : SyscallInput) (dirfd pathp flags : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if !modeled_open_flags flags then CheckUnmodeled
  else
    let reads := [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
    check_copyins_after reads eff (check_openat_body i dirfd pathp flags (clear_copyins eff) m)

/-- A two-byte memory, "f" then NUL at 0x2000, for the example below.
Rocq: `openat_nul_mem`. -/
def openat_nul_mem (a : word) : Option byte :=
  if bv_eqb a 0x2000 then some 102 else if bv_eqb a 0x2001 then some 0 else none

/-- The copy-in range a one-character pathname produces is 2 bytes: the
terminating NUL is read, as `strncpy_from_user` reads it.  Rocq:
`openat_copyin_includes_the_nul`. -/
theorem openat_copyin_includes_the_nul :
    cstr_access_len_aux openat_nul_mem 0x2000 path_max = 2 := by decide

/-! ### Soundness on `CheckOk` -/

/-- A `check_ret_only` acceptance is a `ret_only` answer.  Rocq:
`check_ret_only_sound_ok`. -/
theorem check_ret_only_sound_ok (i : SyscallInput) (eff : SyscallEffect) (r : word)
    (m m' : Model) (evs : List event) (h : check_ret_only eff r m [] = CheckOk m' evs) :
    ret_only r i m (Ok eff m' evs) := by
  rw [check_ret_only_ok_iff] at h
  obtain ⟨rfl, hm, rfl⟩ := h
  subst m'
  exact pure_ok _ i m

/-- Rocq: `check_open_result_sound_ok`.  `mk` is passed explicitly at
every use: left to unification against `check_open_result eff m (fun fd
=> mk fd m)`, the elaborator abstracts `m` as well and lands on a
function of two arguments the spec does not have. -/
theorem check_open_result_sound_ok (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (mk : word → Model → Model) (m' : Model) (evs : List event)
    (h : check_open_result eff m (fun fd => mk fd m) = CheckOk m' evs) :
    open_result_spec m mk i m (Ok eff m' evs) := by
  unfold check_open_result at h
  obtain ⟨rfl, ret, rfl, hcase⟩ := check_new_fd_result_ok_inv openat_errnos eff m _ m' evs h
  unfold open_result_spec errno_from lowest_fd
  rcases hcase with ⟨he, hm⟩ | ⟨hnone, hfd, hm⟩ <;> subst m'
  · obtain ⟨e, hmem, rfl⟩ := (errno_ret_in_true openat_errnos ret).mp he
    apply alt_l
    refine bind_ok0 _ _ i m e m _ _ _ (choose_ok _ e i m hmem) ?_
    exact pure_ok _ i m
  · apply alt_r
    refine bind_ok0 _ _ i m ret m _ _ _ (choose_ok _ ret i m (And.intro hnone hfd)) ?_
    refine bind_ok0 _ _ i m () (mk ret m) _ _ _ (modify_ok _ i m) ?_
    exact pure_ok _ i _

/-- Rocq: `check_create_wronly_sound_ok`. -/
theorem check_create_wronly_sound_ok (i : SyscallInput) (p : path) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_create_wronly p eff m = CheckOk m' evs) :
    create_wronly p m i m (Ok eff m' evs) := by
  unfold check_create_wronly check_open_result at h
  obtain ⟨rfl, ret, rfl, hcase⟩ := check_new_fd_result_ok_inv openat_errnos eff m _ m' evs h
  unfold create_wronly errno_from lowest_fd set_fs set_fds
  rcases hcase with ⟨he, hm⟩ | ⟨hnone, hfd, hm⟩ <;> subst m'
  · obtain ⟨e, hmem, rfl⟩ := (errno_ret_in_true openat_errnos ret).mp he
    apply alt_l
    refine bind_ok0 _ _ i m e m _ _ _ (choose_ok _ e i m hmem) ?_
    exact pure_ok _ i m
  · apply alt_r
    refine bind_ok0 _ _ i m ret m _ _ _ (choose_ok _ ret i m (And.intro hnone hfd)) ?_
    refine bind_ok0 _ _ i m () (with_fs (fs_set (m_fs m) p []) m) _ _ _ (modify_ok _ i m) ?_
    refine bind_ok0 _ _ i _ () _ _ _ _ (modify_ok _ i _) ?_
    exact pure_ok _ i _

/-- Rocq: `check_open_append_sound_ok`. -/
theorem check_open_append_sound_ok (i : SyscallInput) (p : path) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_open_append p eff m = CheckOk m' evs) :
    open_append p m i m (Ok eff m' evs) := by
  unfold check_open_append check_open_result at h
  obtain ⟨rfl, ret, rfl, hcase⟩ := check_new_fd_result_ok_inv openat_errnos eff m _ m' evs h
  unfold open_append errno_from lowest_fd set_fs set_fds
  rcases hcase with ⟨he, hm⟩ | ⟨hnone, hfd, hm⟩ <;> subst m'
  · obtain ⟨e, hmem, rfl⟩ := (errno_ret_in_true openat_errnos ret).mp he
    apply alt_l
    refine bind_ok0 _ _ i m e m _ _ _ (choose_ok _ e i m hmem) ?_
    exact pure_ok _ i m
  · apply alt_r
    refine bind_ok0 _ _ i m ret m _ _ _ (choose_ok _ ret i m (And.intro hnone hfd)) ?_
    refine bind_ok0 _ _ i m () (with_fs (append_open_fs (m_fs m) p) m) _ _ _ (modify_ok _ i m) ?_
    refine bind_ok0 _ _ i _ () _ _ _ _ (modify_ok _ i _) ?_
    exact pure_ok _ i _

/-- Rocq: `check_open_rdwr_sound_ok`. -/
theorem check_open_rdwr_sound_ok (i : SyscallInput) (p : path) (fs' : Fs.Fs)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_open_rdwr p fs' eff m = CheckOk m' evs) :
    open_rdwr p fs' m i m (Ok eff m' evs) := by
  unfold check_open_rdwr check_open_result at h
  obtain ⟨rfl, ret, rfl, hcase⟩ := check_new_fd_result_ok_inv openat_errnos eff m _ m' evs h
  unfold open_rdwr errno_from lowest_fd set_fs set_fds
  rcases hcase with ⟨he, hm⟩ | ⟨hnone, hfd, hm⟩ <;> subst m'
  · obtain ⟨e, hmem, rfl⟩ := (errno_ret_in_true openat_errnos ret).mp he
    apply alt_l
    refine bind_ok0 _ _ i m e m _ _ _ (choose_ok _ e i m hmem) ?_
    exact pure_ok _ i m
  · apply alt_r
    refine bind_ok0 _ _ i m ret m _ _ _ (choose_ok _ ret i m (And.intro hnone hfd)) ?_
    refine bind_ok0 _ _ i m () (with_fs fs' m) _ _ _ (modify_ok _ i m) ?_
    refine bind_ok0 _ _ i _ () _ _ _ _ (modify_ok _ i _) ?_
    exact pure_ok _ i _

/-- Rocq: `check_openat_read_sound_ok`. -/
theorem check_openat_read_sound_ok (i : SyscallInput) (p : path) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_openat_read p eff m = CheckOk m' evs) :
    openat_read_spec p m i m (Ok eff m' evs) := by
  unfold check_openat_read at h
  unfold openat_read_spec
  generalize path_is_dirref p = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact check_open_result_sound_ok i eff m (fun fd => with_fds (fd_insert (m_fds m) fd .FdDir))
      m' evs h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = r at h ⊢
    cases r with
    | none =>
      dsimp only at h ⊢
      exact check_ret_only_sound_ok i eff (errno_ret ENOENT) m m' evs h
    | some _ =>
      dsimp only at h ⊢
      exact check_open_result_sound_ok i eff m
        (fun fd => with_fds (fd_insert (m_fds m) fd (.FdFile p (Z_to_bv 64 0)))) m' evs h

/-- Rocq: `check_openat_create_sound_ok`. -/
theorem check_openat_create_sound_ok (i : SyscallInput) (p : path) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_openat_create p eff m = CheckOk m' evs) :
    openat_create_spec p m i m (Ok eff m' evs) := by
  unfold check_openat_create at h
  unfold openat_create_spec
  generalize (path_is_dirref p || fs_under (m_fs m) p) = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact check_ret_only_sound_ok i eff (errno_ret EISDIR) m m' evs h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact check_create_wronly_sound_ok i p eff m m' evs h

/-- Rocq: `check_openat_excl_sound_ok`. -/
theorem check_openat_excl_sound_ok (i : SyscallInput) (p : path) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_openat_excl p eff m = CheckOk m' evs) :
    openat_excl_spec p m i m (Ok eff m' evs) := by
  unfold check_openat_excl at h
  unfold openat_excl_spec
  generalize (path_is_dirref p || fs_under (m_fs m) p) = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact check_ret_only_sound_ok i eff (errno_ret EEXIST) m m' evs h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = r at h ⊢
    cases r with
    | some _ =>
      dsimp only at h ⊢
      exact check_ret_only_sound_ok i eff (errno_ret EEXIST) m m' evs h
    | none =>
      dsimp only at h ⊢
      exact check_create_wronly_sound_ok i p eff m m' evs h

/-- Rocq: `check_openat_dir_sound_ok`. -/
theorem check_openat_dir_sound_ok (i : SyscallInput) (p : path) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_openat_dir p eff m = CheckOk m' evs) :
    openat_dir_spec p m i m (Ok eff m' evs) := by
  unfold check_openat_dir at h
  unfold openat_dir_spec
  generalize path_is_dirref p = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact check_open_result_sound_ok i eff m (fun fd => with_fds (fd_insert (m_fds m) fd .FdDir))
      m' evs h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hn : NAME_MAX < p.length
    · simp only [hn, ↓reduceIte, reduceCtorEq] at h
    · simp only [hn, ↓reduceIte] at h ⊢
      generalize fs_under (m_fs m) p = b at h ⊢
      cases b with
      | true => simp only [↓reduceIte, reduceCtorEq] at h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize fs_lookup (m_fs m) p = r at h ⊢
        cases r with
        | none =>
          dsimp only at h ⊢
          exact check_ret_only_sound_ok i eff (errno_ret ENOENT) m m' evs h
        | some _ =>
          dsimp only at h ⊢
          exact check_ret_only_sound_ok i eff (errno_ret ENOTDIR) m m' evs h

/-- Rocq: `check_openat_append_sound_ok`. -/
theorem check_openat_append_sound_ok (i : SyscallInput) (p : path) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_openat_append p eff m = CheckOk m' evs) :
    openat_append_spec p m i m (Ok eff m' evs) := by
  unfold check_openat_append at h
  unfold openat_append_spec
  generalize (path_is_dirref p || fs_under (m_fs m) p) = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact check_ret_only_sound_ok i eff (errno_ret EISDIR) m m' evs h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact check_open_append_sound_ok i p eff m m' evs h

/-- Rocq: `check_openat_rdwr_sound_ok`. -/
theorem check_openat_rdwr_sound_ok (i : SyscallInput) (creat trunc : Bool) (p : path)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_openat_rdwr creat trunc p eff m = CheckOk m' evs) :
    openat_rdwr_spec creat trunc p m i m (Ok eff m' evs) := by
  unfold check_openat_rdwr at h
  unfold openat_rdwr_spec
  generalize (path_is_dirref p || fs_under (m_fs m) p) = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact check_ret_only_sound_ok i eff (errno_ret EISDIR) m m' evs h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = r at h ⊢
    cases r with
    | none =>
      dsimp only at h ⊢
      cases creat with
      | true =>
        simp only [↓reduceIte] at h ⊢
        exact check_open_rdwr_sound_ok i p (fs_set (m_fs m) p []) eff m m' evs h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact check_ret_only_sound_ok i eff (errno_ret ENOENT) m m' evs h
    | some _ =>
      dsimp only at h ⊢
      cases trunc with
      | true =>
        simp only [↓reduceIte] at h ⊢
        exact check_open_rdwr_sound_ok i p (fs_set (m_fs m) p []) eff m m' evs h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact check_open_rdwr_sound_ok i p (m_fs m) eff m m' evs h

/-- Rocq: `check_openat_rdwr_excl_sound_ok`. -/
theorem check_openat_rdwr_excl_sound_ok (i : SyscallInput) (p : path) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_openat_rdwr_excl p eff m = CheckOk m' evs) :
    openat_rdwr_excl_spec p m i m (Ok eff m' evs) := by
  unfold check_openat_rdwr_excl at h
  unfold openat_rdwr_excl_spec
  generalize (path_is_dirref p || fs_under (m_fs m) p) = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact check_ret_only_sound_ok i eff (errno_ret EEXIST) m m' evs h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = r at h ⊢
    cases r with
    | some _ =>
      dsimp only at h ⊢
      exact check_ret_only_sound_ok i eff (errno_ret EEXIST) m m' evs h
    | none =>
      dsimp only at h ⊢
      exact check_open_rdwr_sound_ok i p (fs_set (m_fs m) p []) eff m m' evs h

/-- Rocq: `check_openat_localtime_sound_ok`. -/
theorem check_openat_localtime_sound_ok (i : SyscallInput) (flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_openat_localtime flags eff m = CheckOk m' evs) :
    openat_localtime_spec flags m i m (Ok eff m' evs) := by
  unfold check_openat_localtime at h
  unfold openat_localtime_spec
  generalize fs_lookup (m_fs m) localtime_path = r at h ⊢
  cases r with
  | some _ => simp only [reduceCtorEq] at h
  | none =>
    dsimp only at h ⊢
    generalize fs_under (m_fs m) localtime_path = b at h ⊢
    cases b with
    | true => simp only [↓reduceIte, reduceCtorEq] at h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize flag_set (bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))))
        O_CREAT = b at h ⊢
      cases b with
      | true => simp only [↓reduceIte, reduceCtorEq] at h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact check_ret_only_sound_ok i eff (errno_ret ENOENT) m m' evs h

/-- Rocq: `check_open_devnull_sound_ok`. -/
theorem check_open_devnull_sound_ok (i : SyscallInput) (rd wr : Bool) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_open_devnull rd wr eff m = CheckOk m' evs) :
    open_devnull m rd wr i m (Ok eff m' evs) :=
  check_open_result_sound_ok i eff m
    (fun fd => with_fds (fd_insert (m_fds m) fd (.FdDevNull rd wr))) m' evs h

/-- Rocq: `check_openat_devnull_sound_ok`. -/
theorem check_openat_devnull_sound_ok (i : SyscallInput) (flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_openat_devnull flags eff m = CheckOk m' evs) :
    openat_devnull_spec flags m i m (Ok eff m' evs) := by
  unfold check_openat_devnull at h
  unfold openat_devnull_spec
  generalize fs_lookup (m_fs m) devnull_path = r at h ⊢
  cases r with
  | some _ => simp only [reduceCtorEq] at h
  | none =>
    dsimp only at h ⊢
    generalize fs_under (m_fs m) devnull_path = b at h ⊢
    cases b with
    | true => simp only [↓reduceIte, reduceCtorEq] at h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))) = fl at h ⊢
      generalize (fl == 0) = b at h ⊢
      cases b with
      | true =>
        simp only [↓reduceIte] at h ⊢
        exact check_open_devnull_sound_ok i true false eff m m' evs h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize (fl == wr_create_flags) = b at h ⊢
        cases b with
        | true =>
          simp only [↓reduceIte] at h ⊢
          exact check_open_devnull_sound_ok i false true eff m m' evs h
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          generalize is_excl_create fl = b at h ⊢
          cases b with
          | true =>
            simp only [↓reduceIte] at h ⊢
            exact check_ret_only_sound_ok i eff (errno_ret EEXIST) m m' evs h
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
            generalize (fl == O_DIRECTORY) = b at h ⊢
            cases b with
            | true =>
              simp only [↓reduceIte] at h ⊢
              exact check_ret_only_sound_ok i eff (errno_ret ENOTDIR) m m' evs h
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
              generalize (fl == append_create_flags) = b at h ⊢
              cases b with
              | true =>
                simp only [↓reduceIte] at h ⊢
                exact check_open_devnull_sound_ok i false true eff m m' evs h
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
                generalize rdwr_open_word fl = b at h ⊢
                cases b with
                | true =>
                  simp only [↓reduceIte] at h ⊢
                  exact check_open_devnull_sound_ok i true true eff m m' evs h
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
                  generalize is_rdwr_excl_create fl = b at h ⊢
                  cases b with
                  | true =>
                    simp only [↓reduceIte] at h ⊢
                    exact check_ret_only_sound_ok i eff (errno_ret EEXIST) m m' evs h
                  | false => simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-- Rocq: `check_open_urandom_sound_ok`. -/
theorem check_open_urandom_sound_ok (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_open_urandom eff m = CheckOk m' evs) :
    open_urandom m i m (Ok eff m' evs) :=
  check_open_result_sound_ok i eff m
    (fun fd => with_fds (fd_insert (m_fds m) fd .FdUrandom)) m' evs h

/-- Rocq: `check_openat_urandom_sound_ok`. -/
theorem check_openat_urandom_sound_ok (i : SyscallInput) (flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_openat_urandom flags eff m = CheckOk m' evs) :
    openat_urandom_spec flags m i m (Ok eff m' evs) := by
  unfold check_openat_urandom at h
  unfold openat_urandom_spec
  generalize fs_lookup (m_fs m) urandom_path = r at h ⊢
  cases r with
  | some _ => simp only [reduceCtorEq] at h
  | none =>
    dsimp only at h ⊢
    generalize fs_under (m_fs m) urandom_path = b at h ⊢
    cases b with
    | true => simp only [↓reduceIte, reduceCtorEq] at h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))) = fl at h ⊢
      generalize (fl == 0) = b at h ⊢
      cases b with
      | true =>
        simp only [↓reduceIte] at h ⊢
        exact check_open_urandom_sound_ok i eff m m' evs h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize is_excl_create fl = b at h ⊢
        cases b with
        | true =>
          simp only [↓reduceIte] at h ⊢
          exact check_ret_only_sound_ok i eff (errno_ret EEXIST) m m' evs h
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          generalize (fl == O_DIRECTORY) = b at h ⊢
          cases b with
          | true =>
            simp only [↓reduceIte] at h ⊢
            exact check_ret_only_sound_ok i eff (errno_ret ENOTDIR) m m' evs h
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
            generalize is_rdwr_excl_create fl = b at h ⊢
            cases b with
            | true =>
              simp only [↓reduceIte] at h ⊢
              exact check_ret_only_sound_ok i eff (errno_ret EEXIST) m m' evs h
            | false => simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-- Rocq: `check_openat_tmp_sound_ok`. -/
theorem check_openat_tmp_sound_ok (i : SyscallInput) (n p : path) (flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_openat_tmp n p flags eff m = CheckOk m' evs) :
    openat_tmp_spec n p flags m i m (Ok eff m' evs) := by
  unfold check_openat_tmp at h
  unfold openat_tmp_spec
  by_cases hn : NAME_MAX < n.length
  · simp only [hn, ↓reduceIte, reduceCtorEq] at h
  · simp only [hn, ↓reduceIte] at h ⊢
    generalize bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))) = fl at h ⊢
    generalize (fl == 0) = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte] at h ⊢
      generalize fs_under (m_fs m) p = c at h ⊢
      cases c with
      | true => simp only [↓reduceIte, reduceCtorEq] at h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize fs_lookup (m_fs m) p = r at h ⊢
        cases r with
        | none => simp only [reduceCtorEq] at h
        | some _ =>
          dsimp only at h ⊢
          exact check_openat_read_sound_ok i p eff m m' evs h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize (fl == wr_create_flags) = b at h ⊢
      cases b with
      | true =>
        simp only [↓reduceIte] at h ⊢
        exact check_openat_create_sound_ok i p eff m m' evs h
      | false => simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-- Rocq: `check_openat_sep_sound_ok`. -/
theorem check_openat_sep_sound_ok (i : SyscallInput) (p : path) (flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_openat_sep p flags eff m = CheckOk m' evs) :
    openat_sep_spec p flags m i m (Ok eff m' evs) := by
  unfold check_openat_sep at h
  unfold openat_sep_spec
  generalize path_eqb p localtime_path = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact check_openat_localtime_sound_ok i flags eff m m' evs h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize path_eqb p devnull_path = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact check_openat_devnull_sound_ok i flags eff m m' evs h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize path_eqb p urandom_path = b at h ⊢
      cases b with
      | true =>
        simp only [↓reduceIte] at h ⊢
        exact check_openat_urandom_sound_ok i flags eff m m' evs h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize tmp_name p = r at h ⊢
        cases r with
        | some n =>
          dsimp only at h ⊢
          exact check_openat_tmp_sound_ok i n p flags eff m m' evs h
        | none => simp only [reduceCtorEq] at h

/-- Rocq: `check_openat_resolved_sound_ok`. -/
theorem check_openat_resolved_sound_ok (i : SyscallInput) (p : path) (flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_openat_resolved p flags eff m = CheckOk m' evs) :
    openat_resolved_spec p flags m i m (Ok eff m' evs) := by
  unfold check_openat_resolved at h
  unfold openat_resolved_spec
  generalize path_has_slash p = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact check_openat_sep_sound_ok i p flags eff m m' evs h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))) = fl at h ⊢
    generalize (fl == 0) = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact check_openat_read_sound_ok i p eff m m' evs h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize (fl == wr_create_flags) = b at h ⊢
      cases b with
      | true =>
        simp only [↓reduceIte] at h ⊢
        exact check_openat_create_sound_ok i p eff m m' evs h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize is_excl_create fl = b at h ⊢
        cases b with
        | true =>
          simp only [↓reduceIte] at h ⊢
          exact check_openat_excl_sound_ok i p eff m m' evs h
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          generalize (fl == O_DIRECTORY) = b at h ⊢
          cases b with
          | true =>
            simp only [↓reduceIte] at h ⊢
            exact check_openat_dir_sound_ok i p eff m m' evs h
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
            generalize (fl == append_create_flags) = b at h ⊢
            cases b with
            | true =>
              simp only [↓reduceIte] at h ⊢
              exact check_openat_append_sound_ok i p eff m m' evs h
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
              generalize rdwr_open_word fl = b at h ⊢
              cases b with
              | true =>
                simp only [↓reduceIte] at h ⊢
                exact check_openat_rdwr_sound_ok i _ _ p eff m m' evs h
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
                generalize is_rdwr_excl_create fl = b at h ⊢
                cases b with
                | true =>
                  simp only [↓reduceIte] at h ⊢
                  exact check_openat_rdwr_excl_sound_ok i p eff m m' evs h
                | false => simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-- Rocq: `check_openat_body_spec_sound_ok`. -/
theorem check_openat_body_spec_sound_ok (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_openat_body i dirfd pathp flags eff m = CheckOk m' evs) :
    openat_body_spec i m dirfd pathp flags i m (Ok eff m' evs) := by
  unfold check_openat_body at h
  unfold openat_body_spec
  generalize read_cstr i.in_mem pathp = r at h ⊢
  cases r with
  | CstrTooLong =>
    dsimp only at h ⊢
    exact check_ret_only_sound_ok i eff (errno_ret ENAMETOOLONG) m m' evs h
  | CstrFault =>
    dsimp only at h ⊢
    exact check_ret_only_sound_ok i eff (errno_ret EFAULT) m m' evs h
  | CstrOk p =>
    dsimp only at h ⊢
    generalize path_eqb p [] = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact check_ret_only_sound_ok i eff (errno_ret ENOENT) m m' evs h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize (!bv_eqb dirfd AT_FDCWD32) = b at h ⊢
      cases b with
      | true => simp only [↓reduceIte, reduceCtorEq] at h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact check_openat_resolved_sound_ok i p flags eff m m' evs h

/-- Rocq: `check_openat_body_sound_ok`. -/
theorem check_openat_body_sound_ok (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (hfl : (!modeled_open_flags flags) = false)
    (h : check_openat_body i dirfd pathp flags eff m = CheckOk m' evs) :
    openat_core_spec dirfd pathp flags i m (Ok eff m' evs) := by
  unfold openat_core_spec
  apply bind_ok0 _ _ i m i m _ _ _ (input_ok i m)
  apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
  simp only [hfl, Bool.false_eq_true, ↓reduceIte]
  exact check_openat_body_spec_sound_ok i dirfd pathp flags eff m m' evs h

/-- An accepted `openat` effect is one `openat_spec` admits.  Rocq:
`check_openat_sound_ok`. -/
theorem check_openat_sound_ok (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_openat i dirfd pathp flags eff m = CheckOk m' evs) :
    openat_spec dirfd pathp flags i m (Ok eff m' evs) := by
  unfold check_openat at h
  generalize hf : (!modeled_open_flags flags) = b at h
  cases b with
  | true => simp only [↓reduceIte, reduceCtorEq] at h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    rw [check_copyins_after_ok_iff] at h
    obtain ⟨hreads, hchecked⟩ := h
    unfold openat_spec
    apply bind_ok0 _ _ i m i m _ _ _ (input_ok i m)
    exact record_copyins_clear_ok _ _ i m eff m' evs hreads
      (check_openat_body_sound_ok i dirfd pathp flags (clear_copyins eff) m m' evs hf hchecked)

/-! ### Soundness on `CheckUnmodeled`

The plain-name read, create and exclusive arms never decline, and the
lemmas for them say so; the arms with declines of their own relate each
`CheckUnmodeled` to the spec's `unmodeled` at the same leaf. -/

/-- Rocq: `check_open_result_no_unmodeled`. -/
theorem check_open_result_no_unmodeled (eff : SyscallEffect) (m : Model) (mk : word → Model) :
    check_open_result eff m mk ≠ CheckUnmodeled :=
  check_new_fd_result_no_unmodeled openat_errnos eff m mk

/-- Rocq: `check_openat_read_no_unmodeled`. -/
theorem check_openat_read_no_unmodeled (p : path) (eff : SyscallEffect) (m : Model) :
    check_openat_read p eff m ≠ CheckUnmodeled := by
  intro h
  unfold check_openat_read at h
  generalize path_is_dirref p = b at h
  cases b with
  | true =>
    simp only [↓reduceIte] at h
    exact check_open_result_no_unmodeled _ _ _ h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    generalize fs_lookup (m_fs m) p = r at h
    cases r with
    | none =>
      dsimp only at h
      exact check_ret_only_no_unmodeled _ _ _ _ h
    | some _ =>
      dsimp only at h
      exact check_open_result_no_unmodeled _ _ _ h

/-- Rocq: `check_openat_create_no_unmodeled`. -/
theorem check_openat_create_no_unmodeled (p : path) (eff : SyscallEffect) (m : Model) :
    check_openat_create p eff m ≠ CheckUnmodeled := by
  intro h
  unfold check_openat_create at h
  generalize (path_is_dirref p || fs_under (m_fs m) p) = b at h
  cases b with
  | true =>
    simp only [↓reduceIte] at h
    exact check_ret_only_no_unmodeled _ _ _ _ h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact check_open_result_no_unmodeled _ _ _ h

/-- Rocq: `check_openat_excl_no_unmodeled`. -/
theorem check_openat_excl_no_unmodeled (p : path) (eff : SyscallEffect) (m : Model) :
    check_openat_excl p eff m ≠ CheckUnmodeled := by
  intro h
  unfold check_openat_excl at h
  generalize (path_is_dirref p || fs_under (m_fs m) p) = b at h
  cases b with
  | true =>
    simp only [↓reduceIte] at h
    exact check_ret_only_no_unmodeled _ _ _ _ h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    generalize fs_lookup (m_fs m) p = r at h
    cases r with
    | some _ =>
      dsimp only at h
      exact check_ret_only_no_unmodeled _ _ _ _ h
    | none =>
      dsimp only at h
      exact check_open_result_no_unmodeled _ _ _ h

/-- Rocq: `check_openat_dir_sound_unmodeled`. -/
theorem check_openat_dir_sound_unmodeled (i : SyscallInput) (p : path) (eff : SyscallEffect)
    (m : Model) (h : check_openat_dir p eff m = CheckUnmodeled) :
    openat_dir_spec p m i m Unmodeled := by
  unfold check_openat_dir at h
  unfold openat_dir_spec
  generalize path_is_dirref p = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h
    exact absurd h (check_open_result_no_unmodeled _ _ _)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hn : NAME_MAX < p.length
    · simp only [hn, ↓reduceIte]
      exact unmodeled_intro i m
    · simp only [hn, ↓reduceIte] at h ⊢
      generalize fs_under (m_fs m) p = b at h ⊢
      cases b with
      | true =>
        simp only [↓reduceIte]
        exact unmodeled_intro i m
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        generalize fs_lookup (m_fs m) p = r at h
        cases r with
        | none =>
          dsimp only at h
          exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
        | some _ =>
          dsimp only at h
          exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

/-- Rocq: `check_openat_append_no_unmodeled`. -/
theorem check_openat_append_no_unmodeled (p : path) (eff : SyscallEffect) (m : Model) :
    check_openat_append p eff m ≠ CheckUnmodeled := by
  intro h
  unfold check_openat_append at h
  generalize (path_is_dirref p || fs_under (m_fs m) p) = b at h
  cases b with
  | true =>
    simp only [↓reduceIte] at h
    exact check_ret_only_no_unmodeled _ _ _ _ h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact check_open_result_no_unmodeled _ _ _ h

/-- Rocq: `check_open_rdwr_no_unmodeled`. -/
theorem check_open_rdwr_no_unmodeled (p : path) (fs' : Fs.Fs) (eff : SyscallEffect) (m : Model) :
    check_open_rdwr p fs' eff m ≠ CheckUnmodeled := by
  intro h
  unfold check_open_rdwr at h
  exact check_open_result_no_unmodeled _ _ _ h

/-- Rocq: `check_openat_rdwr_no_unmodeled`. -/
theorem check_openat_rdwr_no_unmodeled (creat trunc : Bool) (p : path) (eff : SyscallEffect)
    (m : Model) : check_openat_rdwr creat trunc p eff m ≠ CheckUnmodeled := by
  intro h
  unfold check_openat_rdwr at h
  generalize (path_is_dirref p || fs_under (m_fs m) p) = b at h
  cases b with
  | true =>
    simp only [↓reduceIte] at h
    exact check_ret_only_no_unmodeled _ _ _ _ h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    generalize fs_lookup (m_fs m) p = r at h
    cases r with
    | none =>
      dsimp only at h
      cases creat with
      | true =>
        simp only [↓reduceIte] at h
        exact check_open_rdwr_no_unmodeled _ _ _ _ h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        exact check_ret_only_no_unmodeled _ _ _ _ h
    | some _ =>
      dsimp only at h
      cases trunc with
      | true =>
        simp only [↓reduceIte] at h
        exact check_open_rdwr_no_unmodeled _ _ _ _ h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        exact check_open_rdwr_no_unmodeled _ _ _ _ h

/-- Rocq: `check_openat_rdwr_excl_no_unmodeled`. -/
theorem check_openat_rdwr_excl_no_unmodeled (p : path) (eff : SyscallEffect) (m : Model) :
    check_openat_rdwr_excl p eff m ≠ CheckUnmodeled := by
  intro h
  unfold check_openat_rdwr_excl at h
  generalize (path_is_dirref p || fs_under (m_fs m) p) = b at h
  cases b with
  | true =>
    simp only [↓reduceIte] at h
    exact check_ret_only_no_unmodeled _ _ _ _ h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    generalize fs_lookup (m_fs m) p = r at h
    cases r with
    | some _ =>
      dsimp only at h
      exact check_ret_only_no_unmodeled _ _ _ _ h
    | none =>
      dsimp only at h
      exact check_open_rdwr_no_unmodeled _ _ _ _ h

/-- Rocq: `check_openat_localtime_sound_unmodeled`. -/
theorem check_openat_localtime_sound_unmodeled (i : SyscallInput) (flags : word)
    (eff : SyscallEffect) (m : Model) (h : check_openat_localtime flags eff m = CheckUnmodeled) :
    openat_localtime_spec flags m i m Unmodeled := by
  unfold check_openat_localtime at h
  unfold openat_localtime_spec
  generalize fs_lookup (m_fs m) localtime_path = r at h ⊢
  cases r with
  | some _ =>
    dsimp only
    exact unmodeled_intro i m
  | none =>
    dsimp only at h ⊢
    generalize fs_under (m_fs m) localtime_path = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize flag_set (bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))))
        O_CREAT = b at h ⊢
      cases b with
      | true =>
        simp only [↓reduceIte]
        exact unmodeled_intro i m
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

/-- Rocq: `check_openat_devnull_sound_unmodeled`. -/
theorem check_openat_devnull_sound_unmodeled (i : SyscallInput) (flags : word)
    (eff : SyscallEffect) (m : Model) (h : check_openat_devnull flags eff m = CheckUnmodeled) :
    openat_devnull_spec flags m i m Unmodeled := by
  unfold check_openat_devnull at h
  unfold openat_devnull_spec
  generalize fs_lookup (m_fs m) devnull_path = r at h ⊢
  cases r with
  | some _ =>
    dsimp only
    exact unmodeled_intro i m
  | none =>
    dsimp only at h ⊢
    generalize fs_under (m_fs m) devnull_path = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))) = fl at h ⊢
      generalize (fl == 0) = b at h ⊢
      cases b with
      | true =>
        simp only [↓reduceIte] at h
        exact absurd h (check_open_result_no_unmodeled _ _ _)
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize (fl == wr_create_flags) = b at h ⊢
        cases b with
        | true =>
          simp only [↓reduceIte] at h
          exact absurd h (check_open_result_no_unmodeled _ _ _)
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          generalize is_excl_create fl = b at h ⊢
          cases b with
          | true =>
            simp only [↓reduceIte] at h
            exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
            generalize (fl == O_DIRECTORY) = b at h ⊢
            cases b with
            | true =>
              simp only [↓reduceIte] at h
              exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
              generalize (fl == append_create_flags) = b at h ⊢
              cases b with
              | true =>
                simp only [↓reduceIte] at h
                exact absurd h (check_open_result_no_unmodeled _ _ _)
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
                generalize rdwr_open_word fl = b at h ⊢
                cases b with
                | true =>
                  simp only [↓reduceIte] at h
                  exact absurd h (check_open_result_no_unmodeled _ _ _)
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
                  generalize is_rdwr_excl_create fl = b at h ⊢
                  cases b with
                  | true =>
                    simp only [↓reduceIte] at h
                    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    exact unmodeled_intro i m

/-- Rocq: `check_openat_urandom_sound_unmodeled`. -/
theorem check_openat_urandom_sound_unmodeled (i : SyscallInput) (flags : word)
    (eff : SyscallEffect) (m : Model) (h : check_openat_urandom flags eff m = CheckUnmodeled) :
    openat_urandom_spec flags m i m Unmodeled := by
  unfold check_openat_urandom at h
  unfold openat_urandom_spec
  generalize fs_lookup (m_fs m) urandom_path = r at h ⊢
  cases r with
  | some _ =>
    dsimp only
    exact unmodeled_intro i m
  | none =>
    dsimp only at h ⊢
    generalize fs_under (m_fs m) urandom_path = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))) = fl at h ⊢
      generalize (fl == 0) = b at h ⊢
      cases b with
      | true =>
        simp only [↓reduceIte] at h
        exact absurd h (check_open_result_no_unmodeled _ _ _)
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize is_excl_create fl = b at h ⊢
        cases b with
        | true =>
          simp only [↓reduceIte] at h
          exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          generalize (fl == O_DIRECTORY) = b at h ⊢
          cases b with
          | true =>
            simp only [↓reduceIte] at h
            exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
            generalize is_rdwr_excl_create fl = b at h ⊢
            cases b with
            | true =>
              simp only [↓reduceIte] at h
              exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact unmodeled_intro i m

/-- Rocq: `check_openat_tmp_sound_unmodeled`. -/
theorem check_openat_tmp_sound_unmodeled (i : SyscallInput) (n p : path) (flags : word)
    (eff : SyscallEffect) (m : Model) (h : check_openat_tmp n p flags eff m = CheckUnmodeled) :
    openat_tmp_spec n p flags m i m Unmodeled := by
  unfold check_openat_tmp at h
  unfold openat_tmp_spec
  by_cases hn : NAME_MAX < n.length
  · simp only [hn, ↓reduceIte]
    exact unmodeled_intro i m
  · simp only [hn, ↓reduceIte] at h ⊢
    generalize bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))) = fl at h ⊢
    generalize (fl == 0) = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte] at h ⊢
      generalize fs_under (m_fs m) p = c at h ⊢
      cases c with
      | true =>
        simp only [↓reduceIte]
        exact unmodeled_intro i m
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize fs_lookup (m_fs m) p = r at h ⊢
        cases r with
        | none =>
          dsimp only
          exact unmodeled_intro i m
        | some _ =>
          dsimp only at h
          exact absurd h (check_openat_read_no_unmodeled _ _ _)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize (fl == wr_create_flags) = b at h ⊢
      cases b with
      | true =>
        simp only [↓reduceIte] at h
        exact absurd h (check_openat_create_no_unmodeled _ _ _)
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact unmodeled_intro i m

/-- Rocq: `check_openat_sep_sound_unmodeled`. -/
theorem check_openat_sep_sound_unmodeled (i : SyscallInput) (p : path) (flags : word)
    (eff : SyscallEffect) (m : Model) (h : check_openat_sep p flags eff m = CheckUnmodeled) :
    openat_sep_spec p flags m i m Unmodeled := by
  unfold check_openat_sep at h
  unfold openat_sep_spec
  generalize path_eqb p localtime_path = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact check_openat_localtime_sound_unmodeled i flags eff m h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize path_eqb p devnull_path = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact check_openat_devnull_sound_unmodeled i flags eff m h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize path_eqb p urandom_path = b at h ⊢
      cases b with
      | true =>
        simp only [↓reduceIte] at h ⊢
        exact check_openat_urandom_sound_unmodeled i flags eff m h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize tmp_name p = r at h ⊢
        cases r with
        | some n =>
          dsimp only at h ⊢
          exact check_openat_tmp_sound_unmodeled i n p flags eff m h
        | none =>
          dsimp only
          exact unmodeled_intro i m

/-- Rocq: `check_openat_resolved_sound_unmodeled`. -/
theorem check_openat_resolved_sound_unmodeled (i : SyscallInput) (p : path) (flags : word)
    (eff : SyscallEffect) (m : Model) (h : check_openat_resolved p flags eff m = CheckUnmodeled) :
    openat_resolved_spec p flags m i m Unmodeled := by
  unfold check_openat_resolved at h
  unfold openat_resolved_spec
  generalize path_has_slash p = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact check_openat_sep_sound_unmodeled i p flags eff m h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))) = fl at h ⊢
    generalize (fl == 0) = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_openat_read_no_unmodeled _ _ _)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize (fl == wr_create_flags) = b at h ⊢
      cases b with
      | true =>
        simp only [↓reduceIte] at h
        exact absurd h (check_openat_create_no_unmodeled _ _ _)
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize is_excl_create fl = b at h ⊢
        cases b with
        | true =>
          simp only [↓reduceIte] at h
          exact absurd h (check_openat_excl_no_unmodeled _ _ _)
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          generalize (fl == O_DIRECTORY) = b at h ⊢
          cases b with
          | true =>
            simp only [↓reduceIte] at h ⊢
            exact check_openat_dir_sound_unmodeled i p eff m h
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
            generalize (fl == append_create_flags) = b at h ⊢
            cases b with
            | true =>
              simp only [↓reduceIte] at h
              exact absurd h (check_openat_append_no_unmodeled _ _ _)
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
              generalize rdwr_open_word fl = b at h ⊢
              cases b with
              | true =>
                simp only [↓reduceIte] at h
                exact absurd h (check_openat_rdwr_no_unmodeled _ _ _ _ _)
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
                generalize is_rdwr_excl_create fl = b at h ⊢
                cases b with
                | true =>
                  simp only [↓reduceIte] at h
                  exact absurd h (check_openat_rdwr_excl_no_unmodeled _ _ _)
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  exact unmodeled_intro i m

/-- Rocq: `check_openat_body_spec_sound_unmodeled`. -/
theorem check_openat_body_spec_sound_unmodeled (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m : Model) (h : check_openat_body i dirfd pathp flags eff m = CheckUnmodeled) :
    openat_body_spec i m dirfd pathp flags i m Unmodeled := by
  unfold check_openat_body at h
  unfold openat_body_spec
  generalize read_cstr i.in_mem pathp = r at h ⊢
  cases r with
  | CstrTooLong =>
    dsimp only at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | CstrFault =>
    dsimp only at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | CstrOk p =>
    dsimp only at h ⊢
    generalize path_eqb p [] = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize (!bv_eqb dirfd AT_FDCWD32) = b at h ⊢
      cases b with
      | true =>
        simp only [↓reduceIte]
        exact unmodeled_intro i m
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact check_openat_resolved_sound_unmodeled i p flags eff m h

/-- Rocq: `check_openat_body_sound_unmodeled`. -/
theorem check_openat_body_sound_unmodeled (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m : Model) (hfl : (!modeled_open_flags flags) = false)
    (h : check_openat_body i dirfd pathp flags eff m = CheckUnmodeled) :
    openat_core_spec dirfd pathp flags i m Unmodeled := by
  unfold openat_core_spec
  apply bind_unmodeled2 _ _ i m i m [] (input_ok i m)
  apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
  simp only [hfl, Bool.false_eq_true, ↓reduceIte]
  exact check_openat_body_spec_sound_unmodeled i dirfd pathp flags eff m h

/-- A declined `openat` is one `openat_spec` declines.  Rocq:
`check_openat_sound_unmodeled`. -/
theorem check_openat_sound_unmodeled (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m : Model) (h : check_openat i dirfd pathp flags eff m = CheckUnmodeled) :
    openat_spec dirfd pathp flags i m Unmodeled := by
  unfold check_openat at h
  generalize hf : (!modeled_open_flags flags) = b at h
  unfold openat_spec
  apply bind_unmodeled2 _ _ i m i m [] (input_ok i m)
  apply record_copyins_unmodeled
  cases b with
  | true =>
    unfold openat_core_spec
    apply bind_unmodeled2 _ _ i m i m [] (input_ok i m)
    apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
    simp only [hf, ↓reduceIte]
    exact unmodeled_intro i m
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact check_openat_body_sound_unmodeled i dirfd pathp flags (clear_copyins eff) m hf
      (check_copyins_after_unmodeled _ _ _ h)

/-! ### Completeness on `Ok`

`completes_ok` is the shape every arm lemma of this section takes: an
admitted `Ok` outcome is accepted, and its effect carries no copy-in of
its own — the second conjunct is what lets `check_openat` compare the one
copy-in the pathname fetch produces against a ledger the body did not
touch.  Rocq: `completes_ok`. -/
def completes_ok (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model)
    (evs : List event) (spec : Sys SyscallEffect) (check : check_result) : Prop :=
  spec i m (Ok eff m' evs) → check = CheckOk m' evs ∧ eff.eff_copyins = []

/-- Rocq: `check_ret_only_complete_ok`. -/
theorem check_ret_only_complete_ok (i : SyscallInput) (eff : SyscallEffect) (r : word)
    (m m' : Model) (evs : List event) (h : ret_only r i m (Ok eff m' evs)) :
    check_ret_only eff r m [] = CheckOk m' evs ∧ eff.eff_copyins = [] := by
  rw [ret_only, pure_iff] at h
  obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
  exact ⟨(check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩, rfl⟩

/-- Rocq: `check_open_result_complete_ok`. -/
theorem check_open_result_complete_ok (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (mk : word → Model → Model) (m' : Model) (evs : List event)
    (h : open_result_spec m mk i m (Ok eff m' evs)) :
    check_open_result eff m (fun fd => mk fd m) = CheckOk m' evs ∧ eff.eff_copyins = [] := by
  unfold open_result_spec errno_from lowest_fd at h
  rw [alt_iff] at h
  rcases h with h | h
  · rw [bind_choose_iff] at h
    obtain ⟨e, he, h⟩ := h
    simp only [err_ret, ret_only, pure_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    refine ⟨?_, rfl⟩
    simp only [check_open_result, check_new_fd_result,
      errno_ret_in_intro openat_errnos e he, ↓reduceIte]
  · rw [bind_choose_iff] at h
    obtain ⟨fd, ⟨hnone, hfd⟩, h⟩ := h
    simp only [bind_modify_iff, ret_only, pure_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    subst hfd
    refine ⟨?_, rfl⟩
    simp only [check_open_result, check_new_fd_result,
      errno_ret_in_alloc_fd _ _ openat_errnos_ok, Bool.false_eq_true, ↓reduceIte, hnone,
      bv_eqb_refl]

/-- Rocq: `check_create_wronly_complete_ok`. -/
theorem check_create_wronly_complete_ok (i : SyscallInput) (p : path) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : create_wronly p m i m (Ok eff m' evs)) :
    check_create_wronly p eff m = CheckOk m' evs ∧ eff.eff_copyins = [] := by
  unfold create_wronly errno_from lowest_fd set_fs set_fds at h
  rw [alt_iff] at h
  rcases h with h | h
  · rw [bind_choose_iff] at h
    obtain ⟨e, he, h⟩ := h
    simp only [err_ret, ret_only, pure_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    refine ⟨?_, rfl⟩
    simp only [check_create_wronly, check_open_result, check_new_fd_result,
      errno_ret_in_intro openat_errnos e he, ↓reduceIte]
  · rw [bind_choose_iff] at h
    obtain ⟨fd, ⟨hnone, hfd⟩, h⟩ := h
    simp only [bind_modify_iff, ret_only, pure_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    subst hfd
    refine ⟨?_, rfl⟩
    simp only [check_create_wronly, check_open_result, check_new_fd_result,
      errno_ret_in_alloc_fd _ _ openat_errnos_ok, Bool.false_eq_true, ↓reduceIte, hnone,
      bv_eqb_refl]

/-- Rocq: `check_open_append_complete_ok`. -/
theorem check_open_append_complete_ok (i : SyscallInput) (p : path) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : open_append p m i m (Ok eff m' evs)) :
    check_open_append p eff m = CheckOk m' evs ∧ eff.eff_copyins = [] := by
  unfold open_append errno_from lowest_fd set_fs set_fds at h
  rw [alt_iff] at h
  rcases h with h | h
  · rw [bind_choose_iff] at h
    obtain ⟨e, he, h⟩ := h
    simp only [err_ret, ret_only, pure_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    refine ⟨?_, rfl⟩
    simp only [check_open_append, check_open_result, check_new_fd_result,
      errno_ret_in_intro openat_errnos e he, ↓reduceIte]
  · rw [bind_choose_iff] at h
    obtain ⟨fd, ⟨hnone, hfd⟩, h⟩ := h
    simp only [bind_modify_iff, ret_only, pure_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    subst hfd
    refine ⟨?_, rfl⟩
    simp only [check_open_append, check_open_result, check_new_fd_result,
      errno_ret_in_alloc_fd _ _ openat_errnos_ok, Bool.false_eq_true, ↓reduceIte, hnone,
      bv_eqb_refl]

/-- Rocq: `check_open_rdwr_complete_ok`. -/
theorem check_open_rdwr_complete_ok (i : SyscallInput) (p : path) (fs' : Fs.Fs)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : open_rdwr p fs' m i m (Ok eff m' evs)) :
    check_open_rdwr p fs' eff m = CheckOk m' evs ∧ eff.eff_copyins = [] := by
  unfold open_rdwr errno_from lowest_fd set_fs set_fds at h
  rw [alt_iff] at h
  rcases h with h | h
  · rw [bind_choose_iff] at h
    obtain ⟨e, he, h⟩ := h
    simp only [err_ret, ret_only, pure_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    refine ⟨?_, rfl⟩
    simp only [check_open_rdwr, check_open_result, check_new_fd_result,
      errno_ret_in_intro openat_errnos e he, ↓reduceIte]
  · rw [bind_choose_iff] at h
    obtain ⟨fd, ⟨hnone, hfd⟩, h⟩ := h
    simp only [bind_modify_iff, ret_only, pure_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    subst hfd
    refine ⟨?_, rfl⟩
    simp only [check_open_rdwr, check_open_result, check_new_fd_result,
      errno_ret_in_alloc_fd _ _ openat_errnos_ok, Bool.false_eq_true, ↓reduceIte, hnone,
      bv_eqb_refl]

/-- Rocq: `check_openat_read_complete_ok`. -/
theorem check_openat_read_complete_ok (i : SyscallInput) (p : path) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) :
    completes_ok i m eff m' evs (openat_read_spec p m) (check_openat_read p eff m) := by
  unfold completes_ok
  intro h
  unfold openat_read_spec at h
  unfold check_openat_read
  generalize path_is_dirref p = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact check_open_result_complete_ok i eff m (fun fd => with_fds (fd_insert (m_fds m) fd .FdDir))
      m' evs h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = r at h ⊢
    cases r with
    | none =>
      dsimp only at h ⊢
      exact check_ret_only_complete_ok i eff (errno_ret ENOENT) m m' evs h
    | some _ =>
      dsimp only at h ⊢
      exact check_open_result_complete_ok i eff m
        (fun fd => with_fds (fd_insert (m_fds m) fd (.FdFile p (Z_to_bv 64 0)))) m' evs h

/-- Rocq: `check_openat_create_complete_ok`. -/
theorem check_openat_create_complete_ok (i : SyscallInput) (p : path) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) :
    completes_ok i m eff m' evs (openat_create_spec p m) (check_openat_create p eff m) := by
  unfold completes_ok
  intro h
  unfold openat_create_spec at h
  unfold check_openat_create
  generalize (path_is_dirref p || fs_under (m_fs m) p) = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact check_ret_only_complete_ok i eff (errno_ret EISDIR) m m' evs h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact check_create_wronly_complete_ok i p eff m m' evs h

/-- Rocq: `check_openat_excl_complete_ok`. -/
theorem check_openat_excl_complete_ok (i : SyscallInput) (p : path) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) :
    completes_ok i m eff m' evs (openat_excl_spec p m) (check_openat_excl p eff m) := by
  unfold completes_ok
  intro h
  unfold openat_excl_spec at h
  unfold check_openat_excl
  generalize (path_is_dirref p || fs_under (m_fs m) p) = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact check_ret_only_complete_ok i eff (errno_ret EEXIST) m m' evs h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = r at h ⊢
    cases r with
    | some _ =>
      dsimp only at h ⊢
      exact check_ret_only_complete_ok i eff (errno_ret EEXIST) m m' evs h
    | none =>
      dsimp only at h ⊢
      exact check_create_wronly_complete_ok i p eff m m' evs h

/-- Rocq: `check_openat_dir_complete_ok`. -/
theorem check_openat_dir_complete_ok (i : SyscallInput) (p : path) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) :
    completes_ok i m eff m' evs (openat_dir_spec p m) (check_openat_dir p eff m) := by
  unfold completes_ok
  intro h
  unfold openat_dir_spec at h
  unfold check_openat_dir
  generalize path_is_dirref p = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact check_open_result_complete_ok i eff m (fun fd => with_fds (fd_insert (m_fds m) fd .FdDir))
      m' evs h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hn : NAME_MAX < p.length
    · simp only [hn, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h
    · simp only [hn, ↓reduceIte] at h ⊢
      generalize fs_under (m_fs m) p = b at h ⊢
      cases b with
      | true => simp only [↓reduceIte, unmodeled_iff, reduceCtorEq] at h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize fs_lookup (m_fs m) p = r at h ⊢
        cases r with
        | none =>
          dsimp only at h ⊢
          exact check_ret_only_complete_ok i eff (errno_ret ENOENT) m m' evs h
        | some _ =>
          dsimp only at h ⊢
          exact check_ret_only_complete_ok i eff (errno_ret ENOTDIR) m m' evs h

/-- Rocq: `check_openat_append_complete_ok`. -/
theorem check_openat_append_complete_ok (i : SyscallInput) (p : path) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) :
    completes_ok i m eff m' evs (openat_append_spec p m) (check_openat_append p eff m) := by
  unfold completes_ok
  intro h
  unfold openat_append_spec at h
  unfold check_openat_append
  generalize (path_is_dirref p || fs_under (m_fs m) p) = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact check_ret_only_complete_ok i eff (errno_ret EISDIR) m m' evs h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact check_open_append_complete_ok i p eff m m' evs h

/-- Rocq: `check_openat_rdwr_complete_ok`. -/
theorem check_openat_rdwr_complete_ok (i : SyscallInput) (creat trunc : Bool) (p : path)
    (eff : SyscallEffect) (m m' : Model) (evs : List event) :
    completes_ok i m eff m' evs (openat_rdwr_spec creat trunc p m)
      (check_openat_rdwr creat trunc p eff m) := by
  unfold completes_ok
  intro h
  unfold openat_rdwr_spec at h
  unfold check_openat_rdwr
  generalize (path_is_dirref p || fs_under (m_fs m) p) = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact check_ret_only_complete_ok i eff (errno_ret EISDIR) m m' evs h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = r at h ⊢
    cases r with
    | none =>
      dsimp only at h ⊢
      cases creat with
      | true =>
        simp only [↓reduceIte] at h ⊢
        exact check_open_rdwr_complete_ok i p (fs_set (m_fs m) p []) eff m m' evs h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact check_ret_only_complete_ok i eff (errno_ret ENOENT) m m' evs h
    | some _ =>
      dsimp only at h ⊢
      cases trunc with
      | true =>
        simp only [↓reduceIte] at h ⊢
        exact check_open_rdwr_complete_ok i p (fs_set (m_fs m) p []) eff m m' evs h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact check_open_rdwr_complete_ok i p (m_fs m) eff m m' evs h

/-- Rocq: `check_openat_rdwr_excl_complete_ok`. -/
theorem check_openat_rdwr_excl_complete_ok (i : SyscallInput) (p : path) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) :
    completes_ok i m eff m' evs (openat_rdwr_excl_spec p m) (check_openat_rdwr_excl p eff m) := by
  unfold completes_ok
  intro h
  unfold openat_rdwr_excl_spec at h
  unfold check_openat_rdwr_excl
  generalize (path_is_dirref p || fs_under (m_fs m) p) = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact check_ret_only_complete_ok i eff (errno_ret EEXIST) m m' evs h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize fs_lookup (m_fs m) p = r at h ⊢
    cases r with
    | some _ =>
      dsimp only at h ⊢
      exact check_ret_only_complete_ok i eff (errno_ret EEXIST) m m' evs h
    | none =>
      dsimp only at h ⊢
      exact check_open_rdwr_complete_ok i p (fs_set (m_fs m) p []) eff m m' evs h

/-- Rocq: `check_openat_localtime_complete_ok`. -/
theorem check_openat_localtime_complete_ok (i : SyscallInput) (flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event) :
    completes_ok i m eff m' evs (openat_localtime_spec flags m)
      (check_openat_localtime flags eff m) := by
  unfold completes_ok
  intro h
  unfold openat_localtime_spec at h
  unfold check_openat_localtime
  generalize fs_lookup (m_fs m) localtime_path = r at h ⊢
  cases r with
  | some _ => simp only [unmodeled_iff, reduceCtorEq] at h
  | none =>
    dsimp only at h ⊢
    generalize fs_under (m_fs m) localtime_path = b at h ⊢
    cases b with
    | true => simp only [↓reduceIte, unmodeled_iff, reduceCtorEq] at h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize flag_set (bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))))
        O_CREAT = b at h ⊢
      cases b with
      | true => simp only [↓reduceIte, unmodeled_iff, reduceCtorEq] at h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact check_ret_only_complete_ok i eff (errno_ret ENOENT) m m' evs h

/-- Rocq: `check_open_devnull_complete_ok`. -/
theorem check_open_devnull_complete_ok (i : SyscallInput) (rd wr : Bool) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : open_devnull m rd wr i m (Ok eff m' evs)) :
    check_open_devnull rd wr eff m = CheckOk m' evs ∧ eff.eff_copyins = [] :=
  check_open_result_complete_ok i eff m
    (fun fd => with_fds (fd_insert (m_fds m) fd (.FdDevNull rd wr))) m' evs h

/-- Rocq: `check_openat_devnull_complete_ok`. -/
theorem check_openat_devnull_complete_ok (i : SyscallInput) (flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) :
    completes_ok i m eff m' evs (openat_devnull_spec flags m) (check_openat_devnull flags eff m) := by
  unfold completes_ok
  intro h
  unfold openat_devnull_spec at h
  unfold check_openat_devnull
  generalize fs_lookup (m_fs m) devnull_path = r at h ⊢
  cases r with
  | some _ => simp only [unmodeled_iff, reduceCtorEq] at h
  | none =>
    dsimp only at h ⊢
    generalize fs_under (m_fs m) devnull_path = b at h ⊢
    cases b with
    | true => simp only [↓reduceIte, unmodeled_iff, reduceCtorEq] at h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))) = fl at h ⊢
      generalize (fl == 0) = b at h ⊢
      cases b with
      | true =>
        simp only [↓reduceIte] at h ⊢
        exact check_open_devnull_complete_ok i true false eff m m' evs h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize (fl == wr_create_flags) = b at h ⊢
        cases b with
        | true =>
          simp only [↓reduceIte] at h ⊢
          exact check_open_devnull_complete_ok i false true eff m m' evs h
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          generalize is_excl_create fl = b at h ⊢
          cases b with
          | true =>
            simp only [↓reduceIte] at h ⊢
            exact check_ret_only_complete_ok i eff (errno_ret EEXIST) m m' evs h
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
            generalize (fl == O_DIRECTORY) = b at h ⊢
            cases b with
            | true =>
              simp only [↓reduceIte] at h ⊢
              exact check_ret_only_complete_ok i eff (errno_ret ENOTDIR) m m' evs h
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
              generalize (fl == append_create_flags) = b at h ⊢
              cases b with
              | true =>
                simp only [↓reduceIte] at h ⊢
                exact check_open_devnull_complete_ok i false true eff m m' evs h
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
                generalize rdwr_open_word fl = b at h ⊢
                cases b with
                | true =>
                  simp only [↓reduceIte] at h ⊢
                  exact check_open_devnull_complete_ok i true true eff m m' evs h
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
                  generalize is_rdwr_excl_create fl = b at h ⊢
                  cases b with
                  | true =>
                    simp only [↓reduceIte] at h ⊢
                    exact check_ret_only_complete_ok i eff (errno_ret EEXIST) m m' evs h
                  | false => simp only [Bool.false_eq_true, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h

/-- Rocq: `check_open_urandom_complete_ok`. -/
theorem check_open_urandom_complete_ok (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : open_urandom m i m (Ok eff m' evs)) :
    check_open_urandom eff m = CheckOk m' evs ∧ eff.eff_copyins = [] :=
  check_open_result_complete_ok i eff m
    (fun fd => with_fds (fd_insert (m_fds m) fd .FdUrandom)) m' evs h

/-- Rocq: `check_openat_urandom_complete_ok`. -/
theorem check_openat_urandom_complete_ok (i : SyscallInput) (flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) :
    completes_ok i m eff m' evs (openat_urandom_spec flags m) (check_openat_urandom flags eff m) := by
  unfold completes_ok
  intro h
  unfold openat_urandom_spec at h
  unfold check_openat_urandom
  generalize fs_lookup (m_fs m) urandom_path = r at h ⊢
  cases r with
  | some _ => simp only [unmodeled_iff, reduceCtorEq] at h
  | none =>
    dsimp only at h ⊢
    generalize fs_under (m_fs m) urandom_path = b at h ⊢
    cases b with
    | true => simp only [↓reduceIte, unmodeled_iff, reduceCtorEq] at h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))) = fl at h ⊢
      generalize (fl == 0) = b at h ⊢
      cases b with
      | true =>
        simp only [↓reduceIte] at h ⊢
        exact check_open_urandom_complete_ok i eff m m' evs h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize is_excl_create fl = b at h ⊢
        cases b with
        | true =>
          simp only [↓reduceIte] at h ⊢
          exact check_ret_only_complete_ok i eff (errno_ret EEXIST) m m' evs h
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          generalize (fl == O_DIRECTORY) = b at h ⊢
          cases b with
          | true =>
            simp only [↓reduceIte] at h ⊢
            exact check_ret_only_complete_ok i eff (errno_ret ENOTDIR) m m' evs h
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
            generalize is_rdwr_excl_create fl = b at h ⊢
            cases b with
            | true =>
              simp only [↓reduceIte] at h ⊢
              exact check_ret_only_complete_ok i eff (errno_ret EEXIST) m m' evs h
            | false => simp only [Bool.false_eq_true, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h

/-- Rocq: `check_openat_tmp_complete_ok`. -/
theorem check_openat_tmp_complete_ok (i : SyscallInput) (n p : path) (flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event) :
    completes_ok i m eff m' evs (openat_tmp_spec n p flags m) (check_openat_tmp n p flags eff m) := by
  unfold completes_ok
  intro h
  unfold openat_tmp_spec at h
  unfold check_openat_tmp
  by_cases hn : NAME_MAX < n.length
  · simp only [hn, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h
  · simp only [hn, ↓reduceIte] at h ⊢
    generalize bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))) = fl at h ⊢
    generalize (fl == 0) = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte] at h ⊢
      generalize fs_under (m_fs m) p = c at h ⊢
      cases c with
      | true => simp only [↓reduceIte, unmodeled_iff, reduceCtorEq] at h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize fs_lookup (m_fs m) p = r at h ⊢
        cases r with
        | none => simp only [unmodeled_iff, reduceCtorEq] at h
        | some _ =>
          dsimp only at h ⊢
          exact check_openat_read_complete_ok i p eff m m' evs h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize (fl == wr_create_flags) = b at h ⊢
      cases b with
      | true =>
        simp only [↓reduceIte] at h ⊢
        exact check_openat_create_complete_ok i p eff m m' evs h
      | false => simp only [Bool.false_eq_true, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h

/-- Rocq: `check_openat_sep_complete_ok`. -/
theorem check_openat_sep_complete_ok (i : SyscallInput) (p : path) (flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event) :
    completes_ok i m eff m' evs (openat_sep_spec p flags m) (check_openat_sep p flags eff m) := by
  unfold completes_ok
  intro h
  unfold openat_sep_spec at h
  unfold check_openat_sep
  generalize path_eqb p localtime_path = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact check_openat_localtime_complete_ok i flags eff m m' evs h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize path_eqb p devnull_path = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact check_openat_devnull_complete_ok i flags eff m m' evs h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize path_eqb p urandom_path = b at h ⊢
      cases b with
      | true =>
        simp only [↓reduceIte] at h ⊢
        exact check_openat_urandom_complete_ok i flags eff m m' evs h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize tmp_name p = r at h ⊢
        cases r with
        | some n =>
          dsimp only at h ⊢
          exact check_openat_tmp_complete_ok i n p flags eff m m' evs h
        | none => simp only [unmodeled_iff, reduceCtorEq] at h

/-- Rocq: `check_openat_resolved_complete_ok`. -/
theorem check_openat_resolved_complete_ok (i : SyscallInput) (p : path) (flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event) :
    completes_ok i m eff m' evs (openat_resolved_spec p flags m)
      (check_openat_resolved p flags eff m) := by
  unfold completes_ok
  intro h
  unfold openat_resolved_spec at h
  unfold check_openat_resolved
  generalize path_has_slash p = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact check_openat_sep_complete_ok i p flags eff m m' evs h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))) = fl at h ⊢
    generalize (fl == 0) = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact check_openat_read_complete_ok i p eff m m' evs h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize (fl == wr_create_flags) = b at h ⊢
      cases b with
      | true =>
        simp only [↓reduceIte] at h ⊢
        exact check_openat_create_complete_ok i p eff m m' evs h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize is_excl_create fl = b at h ⊢
        cases b with
        | true =>
          simp only [↓reduceIte] at h ⊢
          exact check_openat_excl_complete_ok i p eff m m' evs h
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          generalize (fl == O_DIRECTORY) = b at h ⊢
          cases b with
          | true =>
            simp only [↓reduceIte] at h ⊢
            exact check_openat_dir_complete_ok i p eff m m' evs h
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
            generalize (fl == append_create_flags) = b at h ⊢
            cases b with
            | true =>
              simp only [↓reduceIte] at h ⊢
              exact check_openat_append_complete_ok i p eff m m' evs h
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
              generalize rdwr_open_word fl = b at h ⊢
              cases b with
              | true =>
                simp only [↓reduceIte] at h ⊢
                exact check_openat_rdwr_complete_ok i _ _ p eff m m' evs h
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
                generalize is_rdwr_excl_create fl = b at h ⊢
                cases b with
                | true =>
                  simp only [↓reduceIte] at h ⊢
                  exact check_openat_rdwr_excl_complete_ok i p eff m m' evs h
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h

/-- Rocq: `check_openat_body_complete_ok`. -/
theorem check_openat_body_complete_ok (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event) :
    completes_ok i m eff m' evs (openat_body_spec i m dirfd pathp flags)
      (check_openat_body i dirfd pathp flags eff m) := by
  unfold completes_ok
  intro h
  unfold openat_body_spec at h
  unfold check_openat_body
  generalize read_cstr i.in_mem pathp = r at h ⊢
  cases r with
  | CstrTooLong =>
    dsimp only at h ⊢
    exact check_ret_only_complete_ok i eff (errno_ret ENAMETOOLONG) m m' evs h
  | CstrFault =>
    dsimp only at h ⊢
    exact check_ret_only_complete_ok i eff (errno_ret EFAULT) m m' evs h
  | CstrOk p =>
    dsimp only at h ⊢
    generalize path_eqb p [] = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact check_ret_only_complete_ok i eff (errno_ret ENOENT) m m' evs h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize (!bv_eqb dirfd AT_FDCWD32) = b at h ⊢
      cases b with
      | true => simp only [↓reduceIte, unmodeled_iff, reduceCtorEq] at h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact check_openat_resolved_complete_ok i p flags eff m m' evs h

/-- What an `Ok` answer of `openat_core_spec` says: the flag word passed
the gate, and the body admitted the outcome.  Rocq: `openat_core_ok_inv`. -/
theorem openat_core_ok_inv (i : SyscallInput) (dirfd pathp flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : openat_core_spec dirfd pathp flags i m (Ok eff m' evs)) :
    (!modeled_open_flags flags) = false
      ∧ openat_body_spec i m dirfd pathp flags i m (Ok eff m' evs) := by
  unfold openat_core_spec at h
  have h := bind_input_model_inv _ i m _ h
  generalize hf : (!modeled_open_flags flags) = b at h
  cases b with
  | true => simp only [↓reduceIte, unmodeled_iff, reduceCtorEq] at h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact ⟨rfl, h⟩

/-- An effect `openat_spec` admits is accepted, model and events included.
Rocq: `check_openat_complete_ok`. -/
theorem check_openat_complete_ok (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : openat_spec dirfd pathp flags i m (Ok eff m' evs)) :
    check_openat i dirfd pathp flags eff m = CheckOk m' evs := by
  unfold openat_spec at h
  have h := input_bind_ok_inv _ i m _ _ _ h
  obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
  obtain ⟨hflags, hbody⟩ := openat_core_ok_inv i dirfd pathp flags core m m' evs hcore
  obtain ⟨hchecked, hcopyins⟩ :=
    check_openat_body_complete_ok i dirfd pathp flags core m m' evs hbody
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := core
  dsimp only at hcopyins
  subst hcopyins
  unfold check_openat
  simp only [hflags, Bool.false_eq_true, ↓reduceIte]
  rw [check_copyins_after_ok_iff]
  exact ⟨rfl, hchecked⟩

/-! ### Completeness on `Unmodeled`

`completes_unmodeled` is the second shape: a spec that declines is met by
a checker that declines.  The plain-name arms and the acceptors never
decline, so for them the lemma is that the spec does not either.  Rocq:
`completes_unmodeled`. -/
def completes_unmodeled (i : SyscallInput) (m : Model) (spec : Sys SyscallEffect)
    (check : check_result) : Prop :=
  spec i m Unmodeled → check = CheckUnmodeled

/-- Rocq: `ret_only_no_unmodeled`. -/
theorem ret_only_no_unmodeled (r : word) (i : SyscallInput) (m : Model) :
    ¬ ret_only r i m Unmodeled := by
  intro h
  simp only [ret_only, pure_iff, reduceCtorEq] at h

/-- Rocq: `open_result_spec_no_unmodeled`. -/
theorem open_result_spec_no_unmodeled (m : Model) (mk : word → Model → Model) (i : SyscallInput) :
    ¬ open_result_spec m mk i m Unmodeled := by
  intro h
  unfold open_result_spec errno_from lowest_fd at h
  rw [alt_iff] at h
  rcases h with h | h
  · rw [bind_choose_iff] at h
    obtain ⟨e, -, h⟩ := h
    simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
  · rw [bind_choose_iff] at h
    obtain ⟨fd, -, h⟩ := h
    simp only [bind_modify_iff, ret_only, pure_iff, reduceCtorEq] at h

/-- Rocq: `create_wronly_no_unmodeled`. -/
theorem create_wronly_no_unmodeled (p : path) (m : Model) (i : SyscallInput) :
    ¬ create_wronly p m i m Unmodeled := by
  intro h
  unfold create_wronly errno_from lowest_fd set_fs set_fds at h
  rw [alt_iff] at h
  rcases h with h | h
  · rw [bind_choose_iff] at h
    obtain ⟨e, -, h⟩ := h
    simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
  · rw [bind_choose_iff] at h
    obtain ⟨fd, -, h⟩ := h
    simp only [bind_modify_iff, ret_only, pure_iff, reduceCtorEq] at h

/-- Rocq: `openat_read_spec_no_unmodeled`. -/
theorem openat_read_spec_no_unmodeled (p : path) (m : Model) (i : SyscallInput) :
    ¬ openat_read_spec p m i m Unmodeled := by
  intro h
  unfold openat_read_spec at h
  generalize path_is_dirref p = b at h
  cases b with
  | true =>
    simp only [↓reduceIte] at h
    exact open_result_spec_no_unmodeled m _ i h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    generalize fs_lookup (m_fs m) p = r at h
    cases r with
    | none =>
      dsimp only at h
      exact ret_only_no_unmodeled _ i m h
    | some _ =>
      dsimp only at h
      exact open_result_spec_no_unmodeled m _ i h

/-- Rocq: `openat_create_spec_no_unmodeled`. -/
theorem openat_create_spec_no_unmodeled (p : path) (m : Model) (i : SyscallInput) :
    ¬ openat_create_spec p m i m Unmodeled := by
  intro h
  unfold openat_create_spec at h
  generalize (path_is_dirref p || fs_under (m_fs m) p) = b at h
  cases b with
  | true =>
    simp only [↓reduceIte] at h
    exact ret_only_no_unmodeled _ i m h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact create_wronly_no_unmodeled p m i h

/-- Rocq: `openat_excl_spec_no_unmodeled`. -/
theorem openat_excl_spec_no_unmodeled (p : path) (m : Model) (i : SyscallInput) :
    ¬ openat_excl_spec p m i m Unmodeled := by
  intro h
  unfold openat_excl_spec at h
  generalize (path_is_dirref p || fs_under (m_fs m) p) = b at h
  cases b with
  | true =>
    simp only [↓reduceIte] at h
    exact ret_only_no_unmodeled _ i m h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    generalize fs_lookup (m_fs m) p = r at h
    cases r with
    | some _ =>
      dsimp only at h
      exact ret_only_no_unmodeled _ i m h
    | none =>
      dsimp only at h
      exact create_wronly_no_unmodeled p m i h

/-- Rocq: `check_openat_dir_complete_unmodeled`. -/
theorem check_openat_dir_complete_unmodeled (i : SyscallInput) (p : path) (eff : SyscallEffect)
    (m : Model) : completes_unmodeled i m (openat_dir_spec p m) (check_openat_dir p eff m) := by
  unfold completes_unmodeled
  intro h
  unfold openat_dir_spec at h
  unfold check_openat_dir
  generalize path_is_dirref p = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h
    exact absurd h (open_result_spec_no_unmodeled m _ i)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hn : NAME_MAX < p.length
    · simp only [hn, ↓reduceIte]
    · simp only [hn, ↓reduceIte] at h ⊢
      generalize fs_under (m_fs m) p = b at h ⊢
      cases b with
      | true => simp only [↓reduceIte]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        generalize fs_lookup (m_fs m) p = r at h
        cases r with
        | none =>
          dsimp only at h
          exact absurd h (ret_only_no_unmodeled _ i m)
        | some _ =>
          dsimp only at h
          exact absurd h (ret_only_no_unmodeled _ i m)

/-- Rocq: `open_append_no_unmodeled`. -/
theorem open_append_no_unmodeled (p : path) (m : Model) (i : SyscallInput) :
    ¬ open_append p m i m Unmodeled := by
  intro h
  unfold open_append errno_from lowest_fd set_fs set_fds at h
  rw [alt_iff] at h
  rcases h with h | h
  · rw [bind_choose_iff] at h
    obtain ⟨e, -, h⟩ := h
    simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
  · rw [bind_choose_iff] at h
    obtain ⟨fd, -, h⟩ := h
    simp only [bind_modify_iff, ret_only, pure_iff, reduceCtorEq] at h

/-- Rocq: `openat_append_spec_no_unmodeled`. -/
theorem openat_append_spec_no_unmodeled (p : path) (m : Model) (i : SyscallInput) :
    ¬ openat_append_spec p m i m Unmodeled := by
  intro h
  unfold openat_append_spec at h
  generalize (path_is_dirref p || fs_under (m_fs m) p) = b at h
  cases b with
  | true =>
    simp only [↓reduceIte] at h
    exact ret_only_no_unmodeled _ i m h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact open_append_no_unmodeled p m i h

/-- Rocq: `open_rdwr_no_unmodeled`. -/
theorem open_rdwr_no_unmodeled (p : path) (fs' : Fs.Fs) (m : Model) (i : SyscallInput) :
    ¬ open_rdwr p fs' m i m Unmodeled := by
  intro h
  unfold open_rdwr errno_from lowest_fd set_fs set_fds at h
  rw [alt_iff] at h
  rcases h with h | h
  · rw [bind_choose_iff] at h
    obtain ⟨e, -, h⟩ := h
    simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
  · rw [bind_choose_iff] at h
    obtain ⟨fd, -, h⟩ := h
    simp only [bind_modify_iff, ret_only, pure_iff, reduceCtorEq] at h

/-- Rocq: `openat_rdwr_spec_no_unmodeled`. -/
theorem openat_rdwr_spec_no_unmodeled (creat trunc : Bool) (p : path) (m : Model)
    (i : SyscallInput) : ¬ openat_rdwr_spec creat trunc p m i m Unmodeled := by
  intro h
  unfold openat_rdwr_spec at h
  generalize (path_is_dirref p || fs_under (m_fs m) p) = b at h
  cases b with
  | true =>
    simp only [↓reduceIte] at h
    exact ret_only_no_unmodeled _ i m h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    generalize fs_lookup (m_fs m) p = r at h
    cases r with
    | none =>
      dsimp only at h
      cases creat with
      | true =>
        simp only [↓reduceIte] at h
        exact open_rdwr_no_unmodeled p _ m i h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        exact ret_only_no_unmodeled _ i m h
    | some _ =>
      dsimp only at h
      cases trunc with
      | true =>
        simp only [↓reduceIte] at h
        exact open_rdwr_no_unmodeled p _ m i h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        exact open_rdwr_no_unmodeled p _ m i h

/-- Rocq: `openat_rdwr_excl_spec_no_unmodeled`. -/
theorem openat_rdwr_excl_spec_no_unmodeled (p : path) (m : Model) (i : SyscallInput) :
    ¬ openat_rdwr_excl_spec p m i m Unmodeled := by
  intro h
  unfold openat_rdwr_excl_spec at h
  generalize (path_is_dirref p || fs_under (m_fs m) p) = b at h
  cases b with
  | true =>
    simp only [↓reduceIte] at h
    exact ret_only_no_unmodeled _ i m h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    generalize fs_lookup (m_fs m) p = r at h
    cases r with
    | some _ =>
      dsimp only at h
      exact ret_only_no_unmodeled _ i m h
    | none =>
      dsimp only at h
      exact open_rdwr_no_unmodeled p _ m i h

/-- Rocq: `check_openat_localtime_complete_unmodeled`. -/
theorem check_openat_localtime_complete_unmodeled (i : SyscallInput) (flags : word)
    (eff : SyscallEffect) (m : Model) :
    completes_unmodeled i m (openat_localtime_spec flags m) (check_openat_localtime flags eff m) := by
  unfold completes_unmodeled
  intro h
  unfold openat_localtime_spec at h
  unfold check_openat_localtime
  generalize fs_lookup (m_fs m) localtime_path = r at h ⊢
  cases r with
  | some _ => rfl
  | none =>
    dsimp only at h ⊢
    generalize fs_under (m_fs m) localtime_path = b at h ⊢
    cases b with
    | true => simp only [↓reduceIte]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize flag_set (bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))))
        O_CREAT = b at h ⊢
      cases b with
      | true => simp only [↓reduceIte]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        exact absurd h (ret_only_no_unmodeled _ i m)

/-- Rocq: `open_devnull_no_unmodeled`. -/
theorem open_devnull_no_unmodeled (rd wr : Bool) (m : Model) (i : SyscallInput) :
    ¬ open_devnull m rd wr i m Unmodeled :=
  open_result_spec_no_unmodeled m _ i

/-- Rocq: `check_openat_devnull_complete_unmodeled`. -/
theorem check_openat_devnull_complete_unmodeled (i : SyscallInput) (flags : word)
    (eff : SyscallEffect) (m : Model) :
    completes_unmodeled i m (openat_devnull_spec flags m) (check_openat_devnull flags eff m) := by
  unfold completes_unmodeled
  intro h
  unfold openat_devnull_spec at h
  unfold check_openat_devnull
  generalize fs_lookup (m_fs m) devnull_path = r at h ⊢
  cases r with
  | some _ => rfl
  | none =>
    dsimp only at h ⊢
    generalize fs_under (m_fs m) devnull_path = b at h ⊢
    cases b with
    | true => simp only [↓reduceIte]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))) = fl at h ⊢
      generalize (fl == 0) = b at h ⊢
      cases b with
      | true =>
        simp only [↓reduceIte] at h
        exact absurd h (open_devnull_no_unmodeled _ _ m i)
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize (fl == wr_create_flags) = b at h ⊢
        cases b with
        | true =>
          simp only [↓reduceIte] at h
          exact absurd h (open_devnull_no_unmodeled _ _ m i)
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          generalize is_excl_create fl = b at h ⊢
          cases b with
          | true =>
            simp only [↓reduceIte] at h
            exact absurd h (ret_only_no_unmodeled _ i m)
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
            generalize (fl == O_DIRECTORY) = b at h ⊢
            cases b with
            | true =>
              simp only [↓reduceIte] at h
              exact absurd h (ret_only_no_unmodeled _ i m)
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
              generalize (fl == append_create_flags) = b at h ⊢
              cases b with
              | true =>
                simp only [↓reduceIte] at h
                exact absurd h (open_devnull_no_unmodeled _ _ m i)
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
                generalize rdwr_open_word fl = b at h ⊢
                cases b with
                | true =>
                  simp only [↓reduceIte] at h
                  exact absurd h (open_devnull_no_unmodeled _ _ m i)
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
                  generalize is_rdwr_excl_create fl = b at h ⊢
                  cases b with
                  | true =>
                    simp only [↓reduceIte] at h
                    exact absurd h (ret_only_no_unmodeled _ i m)
                  | false => simp only [Bool.false_eq_true, ↓reduceIte]

/-- Rocq: `open_urandom_no_unmodeled`. -/
theorem open_urandom_no_unmodeled (m : Model) (i : SyscallInput) :
    ¬ open_urandom m i m Unmodeled :=
  open_result_spec_no_unmodeled m _ i

/-- Rocq: `check_openat_urandom_complete_unmodeled`. -/
theorem check_openat_urandom_complete_unmodeled (i : SyscallInput) (flags : word)
    (eff : SyscallEffect) (m : Model) :
    completes_unmodeled i m (openat_urandom_spec flags m) (check_openat_urandom flags eff m) := by
  unfold completes_unmodeled
  intro h
  unfold openat_urandom_spec at h
  unfold check_openat_urandom
  generalize fs_lookup (m_fs m) urandom_path = r at h ⊢
  cases r with
  | some _ => rfl
  | none =>
    dsimp only at h ⊢
    generalize fs_under (m_fs m) urandom_path = b at h ⊢
    cases b with
    | true => simp only [↓reduceIte]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))) = fl at h ⊢
      generalize (fl == 0) = b at h ⊢
      cases b with
      | true =>
        simp only [↓reduceIte] at h
        exact absurd h (open_urandom_no_unmodeled m i)
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize is_excl_create fl = b at h ⊢
        cases b with
        | true =>
          simp only [↓reduceIte] at h
          exact absurd h (ret_only_no_unmodeled _ i m)
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          generalize (fl == O_DIRECTORY) = b at h ⊢
          cases b with
          | true =>
            simp only [↓reduceIte] at h
            exact absurd h (ret_only_no_unmodeled _ i m)
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
            generalize is_rdwr_excl_create fl = b at h ⊢
            cases b with
            | true =>
              simp only [↓reduceIte] at h
              exact absurd h (ret_only_no_unmodeled _ i m)
            | false => simp only [Bool.false_eq_true, ↓reduceIte]

/-- Rocq: `check_openat_tmp_complete_unmodeled`. -/
theorem check_openat_tmp_complete_unmodeled (i : SyscallInput) (n p : path) (flags : word)
    (eff : SyscallEffect) (m : Model) :
    completes_unmodeled i m (openat_tmp_spec n p flags m) (check_openat_tmp n p flags eff m) := by
  unfold completes_unmodeled
  intro h
  unfold openat_tmp_spec at h
  unfold check_openat_tmp
  by_cases hn : NAME_MAX < n.length
  · simp only [hn, ↓reduceIte]
  · simp only [hn, ↓reduceIte] at h ⊢
    generalize bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))) = fl at h ⊢
    generalize (fl == 0) = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte] at h ⊢
      generalize fs_under (m_fs m) p = c at h ⊢
      cases c with
      | true => simp only [↓reduceIte]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize fs_lookup (m_fs m) p = r at h ⊢
        cases r with
        | none => rfl
        | some _ =>
          dsimp only at h
          exact absurd h (openat_read_spec_no_unmodeled p m i)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize (fl == wr_create_flags) = b at h ⊢
      cases b with
      | true =>
        simp only [↓reduceIte] at h
        exact absurd h (openat_create_spec_no_unmodeled p m i)
      | false => simp only [Bool.false_eq_true, ↓reduceIte]

/-- Rocq: `check_openat_sep_complete_unmodeled`. -/
theorem check_openat_sep_complete_unmodeled (i : SyscallInput) (p : path) (flags : word)
    (eff : SyscallEffect) (m : Model) :
    completes_unmodeled i m (openat_sep_spec p flags m) (check_openat_sep p flags eff m) := by
  unfold completes_unmodeled
  intro h
  unfold openat_sep_spec at h
  unfold check_openat_sep
  generalize path_eqb p localtime_path = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact check_openat_localtime_complete_unmodeled i flags eff m h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize path_eqb p devnull_path = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact check_openat_devnull_complete_unmodeled i flags eff m h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize path_eqb p urandom_path = b at h ⊢
      cases b with
      | true =>
        simp only [↓reduceIte] at h ⊢
        exact check_openat_urandom_complete_unmodeled i flags eff m h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize tmp_name p = r at h ⊢
        cases r with
        | some n =>
          dsimp only at h ⊢
          exact check_openat_tmp_complete_unmodeled i n p flags eff m h
        | none => rfl

/-- Rocq: `check_openat_resolved_complete_unmodeled`. -/
theorem check_openat_resolved_complete_unmodeled (i : SyscallInput) (p : path) (flags : word)
    (eff : SyscallEffect) (m : Model) :
    completes_unmodeled i m (openat_resolved_spec p flags m) (check_openat_resolved p flags eff m) := by
  unfold completes_unmodeled
  intro h
  unfold openat_resolved_spec at h
  unfold check_openat_resolved
  generalize path_has_slash p = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact check_openat_sep_complete_unmodeled i p flags eff m h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))) = fl at h ⊢
    generalize (fl == 0) = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (openat_read_spec_no_unmodeled p m i)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize (fl == wr_create_flags) = b at h ⊢
      cases b with
      | true =>
        simp only [↓reduceIte] at h
        exact absurd h (openat_create_spec_no_unmodeled p m i)
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize is_excl_create fl = b at h ⊢
        cases b with
        | true =>
          simp only [↓reduceIte] at h
          exact absurd h (openat_excl_spec_no_unmodeled p m i)
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          generalize (fl == O_DIRECTORY) = b at h ⊢
          cases b with
          | true =>
            simp only [↓reduceIte] at h ⊢
            exact check_openat_dir_complete_unmodeled i p eff m h
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
            generalize (fl == append_create_flags) = b at h ⊢
            cases b with
            | true =>
              simp only [↓reduceIte] at h
              exact absurd h (openat_append_spec_no_unmodeled p m i)
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
              generalize rdwr_open_word fl = b at h ⊢
              cases b with
              | true =>
                simp only [↓reduceIte] at h
                exact absurd h (openat_rdwr_spec_no_unmodeled _ _ p m i)
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
                generalize is_rdwr_excl_create fl = b at h ⊢
                cases b with
                | true =>
                  simp only [↓reduceIte] at h
                  exact absurd h (openat_rdwr_excl_spec_no_unmodeled p m i)
                | false => simp only [Bool.false_eq_true, ↓reduceIte]

/-- Rocq: `check_openat_body_spec_complete_unmodeled`. -/
theorem check_openat_body_spec_complete_unmodeled (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m : Model) :
    completes_unmodeled i m (openat_body_spec i m dirfd pathp flags)
      (check_openat_body i dirfd pathp flags eff m) := by
  unfold completes_unmodeled
  intro h
  unfold openat_body_spec at h
  unfold check_openat_body
  generalize read_cstr i.in_mem pathp = r at h ⊢
  cases r with
  | CstrTooLong =>
    dsimp only at h
    exact absurd h (ret_only_no_unmodeled _ i m)
  | CstrFault =>
    dsimp only at h
    exact absurd h (ret_only_no_unmodeled _ i m)
  | CstrOk p =>
    dsimp only at h ⊢
    generalize path_eqb p [] = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (ret_only_no_unmodeled _ i m)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize (!bv_eqb dirfd AT_FDCWD32) = b at h ⊢
      cases b with
      | true => simp only [↓reduceIte]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact check_openat_resolved_complete_unmodeled i p flags eff m h

/-- What a declined `openat_core_spec` says: the flag gate declined, or
it passed and the body declined.  Rocq: `openat_core_unmodeled_inv`. -/
theorem openat_core_unmodeled_inv (i : SyscallInput) (dirfd pathp flags : word) (m : Model)
    (h : openat_core_spec dirfd pathp flags i m Unmodeled) :
    (!modeled_open_flags flags) = true
      ∨ ((!modeled_open_flags flags) = false
         ∧ openat_body_spec i m dirfd pathp flags i m Unmodeled) := by
  unfold openat_core_spec at h
  have h := bind_input_model_inv _ i m _ h
  generalize hf : (!modeled_open_flags flags) = b at h ⊢
  cases b with
  | true => exact Or.inl rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact Or.inr ⟨rfl, h⟩

/-- A call `openat_spec` declines is declined, whatever effect is offered.
Rocq: `check_openat_complete_unmodeled`. -/
theorem check_openat_complete_unmodeled (i : SyscallInput) (dirfd pathp flags : word)
    (m : Model) (eff : SyscallEffect) (h : openat_spec dirfd pathp flags i m Unmodeled) :
    check_openat i dirfd pathp flags eff m = CheckUnmodeled := by
  unfold openat_spec at h
  have h := input_bind_unmodeled_inv _ i m h
  have h := record_copyins_unmodeled_inv _ _ i m h
  unfold check_openat
  rcases openat_core_unmodeled_inv i dirfd pathp flags m h with hf | ⟨hf, hbody⟩
  · simp only [hf, ↓reduceIte]
  · have hb := check_openat_body_spec_complete_unmodeled i dirfd pathp flags (clear_copyins eff) m
      hbody
    simp only [hf, Bool.false_eq_true, ↓reduceIte, hb, check_copyins_after]

/-! ### faccessat (48) and faccessat2 (439) — the checker

`check_faccessat` and `check_faccessat2` are the computable side of
`faccessat_spec` and `faccessat2_spec` (`Sys/Fs/Open.lean`), ported name
for name from the faccessat half of `Checks/Sys/Fs/Open.v` at the
header's baseline; their witnesses close the witness section below.  Not
part of the trusted specification.  Their pins are the faccessat half of
`Checks/Cases/Checks/Sys/Fs/Open.lean`.

THE ORDER OF THE GATES IS `do_faccessat`'s (fs/open.c:467-537, Linux
v6.18.46).  `if (mode & ~S_IRWXO) return -EINVAL;` is its first
statement (:475-476) and `if (flags & ~(AT_EACCESS | AT_SYMLINK_NOFOLLOW
| AT_EMPTY_PATH)) return -EINVAL;` its second (:478-479), both before
`user_path_at` (:493) reads a byte of the pathname.  So both -EINVAL arms
sit OUTSIDE the copy-in comparison, where the spec keeps them outside
`record_copyins`: an honest -EINVAL carries no ledger, and one that
claims the pathname range is refused as a read Linux did not make.  The
two declines, AT_EMPTY_PATH and a permission mode, sit there too and for
the same reason; `faccessat2_spec`'s docstring says why the two -EINVALs
precede the mode decline.  Only past those gates does
`check_copyins_after` require the claimed ledger to be exactly the one
range `getname_flags` (fs/namei.c:136-216, Linux v6.18.46) read, and hand
the effect, ledger cleared, to `check_faccessat_body`.

THE BODY has no flag word to dispatch on and the acceptor no state to
build: faccessat changes nothing, so the two alternatives of
`access_exists_spec` write the same model and differ in the return
alone, and `check_access_exists` accepts their union without a case on
which was taken.

THE PROOFS keep Rocq's shape in this file's tactics.  The body lemmas
generalise each decision out of both sides before the split, as the
openat body lemmas do; the wrapper lemmas open the spec's two reads with
`bind_ok0` and `bind_unmodeled2` (Rocq's `fa_open` and `fa_open_u`) and
settle the ledger through `check_copyins_after_ok_iff` and
`record_copyins_clear_ok`.  Rocq's `fa_det`, `fa_det_u` and `fa_unmod_h`
are the `check_ret_only_complete_ok`, `ret_only_no_unmodeled` and
`unmodeled_iff` steps they abbreviate.  `check_access_exists_ok_inv`
plays the part `check_new_fd_result_ok_inv` plays for the openat
acceptor: one reading of what an accepting verdict says, off which the
soundness lemma and the ledger lemma are read. -/

/-- The acceptor for the arm of `faccessat_spec` that can succeed: 0, or
an errno of `faccessat_errnos`, with NO state change either way and FIVE
EMPTY LEDGERS.  faccessat writes, zeroes, unmaps and copies out nothing,
and the wrapper clears the pathname copy-in before the body sees the
effect, so only a forged ledger reaches the second arm of the match.
Rocq: `check_access_exists`. -/
def check_access_exists (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | SyscallEffect.mkEffectU ret [] [] [] [] [] =>
      if errno_ret_in faccessat_errnos ret || bv_eqb ret (Z_to_bv 64 0) then CheckOk m []
      else CheckReject
  | _ => CheckReject

/-- The pathname half, decided against an effect whose copy-in ledger the
wrapper has cleared: the three fetch answers of `getname_flags`
(fs/namei.c:136-216, Linux v6.18.46), then the dirfd, which `path_init`
(fs/namei.c:2590, Linux v6.18.46) is the first to read and which the
model answers for AT_FDCWD alone, then "." and "..", then the declines
and the map, in `faccessat_body_spec`'s order.  Public where Rocq's is a
`Local Definition`, so the pins can state it by name.  Rocq:
`check_faccessat_body`. -/
def check_faccessat_body (i : SyscallInput) (dirfd pathp : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match read_cstr i.in_mem pathp with
  | CstrTooLong => check_ret_only eff (errno_ret ENAMETOOLONG) m []
  | CstrFault => check_ret_only eff (errno_ret EFAULT) m []
  | CstrOk p =>
      if path_eqb p [] then check_ret_only eff (errno_ret ENOENT) m []
      else if !bv_eqb dirfd AT_FDCWD32 then CheckUnmodeled
      else if path_eqb p dot_path then check_access_exists eff m
      else if path_eqb p dotdot_path then check_access_exists eff m
      else if path_has_slash p then CheckUnmodeled
      else if NAME_MAX < p.length then CheckUnmodeled
      else if fs_under (m_fs m) p then CheckUnmodeled
      else
        match fs_lookup (m_fs m) p with
        | none => check_ret_only eff (errno_ret ENOENT) m []
        | some _ => check_access_exists eff m

/-- `faccessat(dirfd, path, mode)`: the mode -EINVAL of `do_faccessat`
(fs/open.c:475-476, Linux v6.18.46) accepted as a bare return with every
ledger empty, the permission modes declined, and on F_OK the pathname
copy-in checked as `check_openat` checks it: decide the body against the
effect with the ledger cleared, then require the claimed ledger to be
exactly the one range `cstr_access_len_aux` measures.  Both mode arms are
outside that comparison, mirroring the spec: `do_faccessat` decides the
mode (fs/open.c:475-476, Linux v6.18.46) before its call into
`user_path_at` (fs/namei.c:3211-3219, Linux v6.18.46) at fs/open.c:493,
so an honest -EINVAL carries no copy-in at all.  Rocq: `check_faccessat`. -/
def check_faccessat (i : SyscallInput) (dirfd pathp mode : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if !modeled_access_mode mode then check_ret_only eff (errno_ret EINVAL) m []
  else if !access_mode_f_ok mode then CheckUnmodeled
  else
    let reads := [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
    check_copyins_after reads eff (check_faccessat_body i dirfd pathp (clear_copyins eff) m)

/-- `faccessat2(dirfd, path, mode, flags)`: the same body under a wrapper
with one more test.  `do_faccessat` is the shared function, so the
acceptor differs from `check_faccessat` only in the two flag arms: the
kernel's own -EINVAL for a bit outside the three it accepts
(fs/open.c:478-479, Linux v6.18.46), and the decline for AT_EMPTY_PATH.
Both sit outside the copy-in comparison, mirroring the spec: neither
reaches the call into `user_path_at` (fs/namei.c:3211-3219, Linux
v6.18.46) at fs/open.c:493, so neither carries a ledger.  Rocq:
`check_faccessat2`. -/
def check_faccessat2 (i : SyscallInput) (dirfd pathp mode flags : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if !modeled_access_mode mode then check_ret_only eff (errno_ret EINVAL) m []
  else if !valid_access_flags flags then check_ret_only eff (errno_ret EINVAL) m []
  else if !modeled_access_flags flags then CheckUnmodeled
  else if !access_mode_f_ok mode then CheckUnmodeled
  else
    let reads := [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
    check_copyins_after reads eff (check_faccessat_body i dirfd pathp (clear_copyins eff) m)

/-! ### The acceptor, from both sides -/

/-- `faccessat_errnos` lies inside the errno band, which is what lets
`errno_ret_in_fd` separate it from a small return.  Lean-only: Rocq's
`errno_ret_in_faccessat_zero` discharges the same `errnos_ok` premise by
`reflexivity` in place. -/
theorem faccessat_errnos_ok : errnos_ok faccessat_errnos = true := by decide

/-- 0 is not an injectable errno, so the two alternatives of
`access_exists_spec` never both have to be justified by the same return,
though either would do, since both leave the model alone.  Rocq:
`errno_ret_in_faccessat_zero`. -/
theorem errno_ret_in_faccessat_zero : errno_ret_in faccessat_errnos (Z_to_bv 64 0) = false :=
  errno_ret_in_fd faccessat_errnos (Z_to_bv 64 0) faccessat_errnos_ok (by decide)

/-- What an accepting `check_access_exists` verdict says about its
inputs: the model is kept, no event is emitted, the effect is a bare
return with every ledger empty, and the return is an errno of the set or
0.  The soundness lemma and the ledger lemma below read their cases off
this, as the openat acceptor's read theirs off
`check_new_fd_result_ok_inv`.  Lean-only: Rocq's
`check_access_exists_sound_ok` and `check_access_exists_ok_copyins_nil`
destruct the acceptor's match in place; here both read one inversion. -/
theorem check_access_exists_ok_inv (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_access_exists eff m = CheckOk m' evs) :
    m' = m ∧ evs = [] ∧ ∃ ret, eff = mkEffect ret [] []
      ∧ (errno_ret_in faccessat_errnos ret = true ∨ ret = Z_to_bv 64 0) := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws with
  | cons w ws => simp only [check_access_exists, reduceCtorEq] at h
  | nil =>
  cases zs with
  | cons z zs => simp only [check_access_exists, reduceCtorEq] at h
  | nil =>
  cases us with
  | cons u us => simp only [check_access_exists, reduceCtorEq] at h
  | nil =>
  cases cs with
  | cons c cs => simp only [check_access_exists, reduceCtorEq] at h
  | nil =>
  cases copyins with
  | cons c copyins => simp only [check_access_exists, reduceCtorEq] at h
  | nil =>
  simp only [check_access_exists] at h
  cases hE : errno_ret_in faccessat_errnos ret with
  | true =>
    simp only [hE, Bool.true_or, ↓reduceIte, check_result.CheckOk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, ret, rfl, Or.inl hE⟩
  | false =>
    simp only [hE, Bool.false_or] at h
    cases hZ : bv_eqb ret (Z_to_bv 64 0) with
    | true =>
      simp only [hZ, ↓reduceIte, check_result.CheckOk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl, ret, rfl, Or.inr ((bv_eqb_eq _ _).mp hZ)⟩
    | false => simp only [hZ, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-- An accepted effect is one `access_exists_spec` admits: the errno
through `alt_l` and the set, 0 through `alt_r`.  Rocq:
`check_access_exists_sound_ok`. -/
theorem check_access_exists_sound_ok (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_access_exists eff m = CheckOk m' evs) :
    access_exists_spec i m (Ok eff m' evs) := by
  obtain ⟨rfl, rfl, ret, rfl, hcase⟩ := check_access_exists_ok_inv eff m m' evs h
  unfold access_exists_spec errno_from
  rcases hcase with he | rfl
  · obtain ⟨e, hmem, rfl⟩ := (errno_ret_in_true faccessat_errnos ret).mp he
    apply alt_l
    refine bind_ok0 _ _ i _ e _ _ _ _ (choose_ok _ e i _ hmem) ?_
    exact pure_ok _ i _
  · apply alt_r
    exact pure_ok _ i _

/-- `check_access_exists` never declines.  Rocq:
`check_access_exists_no_unmodeled`. -/
theorem check_access_exists_no_unmodeled (eff : SyscallEffect) (m : Model) :
    check_access_exists eff m ≠ CheckUnmodeled := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws with
  | cons w ws => simp only [check_access_exists, ne_eq, reduceCtorEq, not_false_eq_true]
  | nil =>
  cases zs with
  | cons z zs => simp only [check_access_exists, ne_eq, reduceCtorEq, not_false_eq_true]
  | nil =>
  cases us with
  | cons u us => simp only [check_access_exists, ne_eq, reduceCtorEq, not_false_eq_true]
  | nil =>
  cases cs with
  | cons c cs => simp only [check_access_exists, ne_eq, reduceCtorEq, not_false_eq_true]
  | nil =>
  cases copyins with
  | cons c copyins => simp only [check_access_exists, ne_eq, reduceCtorEq, not_false_eq_true]
  | nil =>
  simp only [check_access_exists]
  cases errno_ret_in faccessat_errnos ret || bv_eqb ret (Z_to_bv 64 0) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true]

/-- Every outcome `access_exists_spec` admits is accepted: the errno of
the set by `errno_ret_in_intro`, the 0 by `errno_ret_in_faccessat_zero`
and `bv_eqb_refl`.  Rocq: `check_access_exists_complete_ok`. -/
theorem check_access_exists_complete_ok (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : access_exists_spec i m (Ok eff m' evs)) :
    check_access_exists eff m = CheckOk m' evs := by
  unfold access_exists_spec errno_from at h
  rw [alt_iff] at h
  rcases h with h | h
  · rw [bind_choose_iff] at h
    obtain ⟨e, he, h⟩ := h
    simp only [err_ret, ret_only, pure_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    simp only [check_access_exists, errno_ret_in_intro faccessat_errnos e he, Bool.true_or,
      ↓reduceIte]
  · simp only [ret_only, pure_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    simp only [check_access_exists, errno_ret_in_faccessat_zero, bv_eqb_refl, Bool.false_or,
      ↓reduceIte]

/-- An accepted effect claims no copy-in: the acceptor matches five empty
lists.  Rocq: `check_access_exists_ok_copyins_nil`. -/
theorem check_access_exists_ok_copyins_nil (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_access_exists eff m = CheckOk m' evs) :
    eff.eff_copyins = [] := by
  obtain ⟨-, -, ret, rfl, -⟩ := check_access_exists_ok_inv eff m m' evs h
  rfl

/-- `access_exists_spec` never declines.  Rocq: `access_exists_no_unmodeled`. -/
theorem access_exists_no_unmodeled (i : SyscallInput) (m : Model) :
    ¬ access_exists_spec i m Unmodeled := by
  intro h
  unfold access_exists_spec errno_from at h
  rw [alt_iff] at h
  rcases h with h | h
  · rw [bind_choose_iff] at h
    obtain ⟨e, -, h⟩ := h
    simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
  · simp only [ret_only, pure_iff, reduceCtorEq] at h

/-! ### The body, from both sides -/

/-- Rocq: `check_faccessat_body_sound_ok`. -/
theorem check_faccessat_body_sound_ok (i : SyscallInput) (dirfd pathp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_faccessat_body i dirfd pathp eff m = CheckOk m' evs) :
    faccessat_body_spec dirfd pathp i m i m (Ok eff m' evs) := by
  unfold check_faccessat_body at h
  unfold faccessat_body_spec
  generalize read_cstr i.in_mem pathp = r at h ⊢
  cases r with
  | CstrTooLong =>
    dsimp only at h ⊢
    exact check_ret_only_sound_ok i eff (errno_ret ENAMETOOLONG) m m' evs h
  | CstrFault =>
    dsimp only at h ⊢
    exact check_ret_only_sound_ok i eff (errno_ret EFAULT) m m' evs h
  | CstrOk p =>
    dsimp only at h ⊢
    generalize path_eqb p [] = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact check_ret_only_sound_ok i eff (errno_ret ENOENT) m m' evs h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize (!bv_eqb dirfd AT_FDCWD32) = b at h ⊢
      cases b with
      | true => simp only [↓reduceIte, reduceCtorEq] at h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize path_eqb p dot_path = b at h ⊢
        cases b with
        | true =>
          simp only [↓reduceIte] at h ⊢
          exact check_access_exists_sound_ok i eff m m' evs h
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          generalize path_eqb p dotdot_path = b at h ⊢
          cases b with
          | true =>
            simp only [↓reduceIte] at h ⊢
            exact check_access_exists_sound_ok i eff m m' evs h
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
            generalize path_has_slash p = b at h ⊢
            cases b with
            | true => simp only [↓reduceIte, reduceCtorEq] at h
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
              by_cases hn : NAME_MAX < p.length
              · simp only [hn, ↓reduceIte, reduceCtorEq] at h
              · simp only [hn, ↓reduceIte] at h ⊢
                generalize fs_under (m_fs m) p = b at h ⊢
                cases b with
                | true => simp only [↓reduceIte, reduceCtorEq] at h
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
                  generalize fs_lookup (m_fs m) p = r at h ⊢
                  cases r with
                  | none =>
                    dsimp only at h ⊢
                    exact check_ret_only_sound_ok i eff (errno_ret ENOENT) m m' evs h
                  | some _ =>
                    dsimp only at h ⊢
                    exact check_access_exists_sound_ok i eff m m' evs h

/-- Rocq: `check_faccessat_body_sound_unmodeled`. -/
theorem check_faccessat_body_sound_unmodeled (i : SyscallInput) (dirfd pathp : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_faccessat_body i dirfd pathp eff m = CheckUnmodeled) :
    faccessat_body_spec dirfd pathp i m i m Unmodeled := by
  unfold check_faccessat_body at h
  unfold faccessat_body_spec
  generalize read_cstr i.in_mem pathp = r at h ⊢
  cases r with
  | CstrTooLong =>
    dsimp only at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | CstrFault =>
    dsimp only at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | CstrOk p =>
    dsimp only at h ⊢
    generalize path_eqb p [] = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize (!bv_eqb dirfd AT_FDCWD32) = b at h ⊢
      cases b with
      | true =>
        simp only [↓reduceIte]
        exact unmodeled_intro i m
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize path_eqb p dot_path = b at h ⊢
        cases b with
        | true =>
          simp only [↓reduceIte] at h
          exact absurd h (check_access_exists_no_unmodeled _ _)
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          generalize path_eqb p dotdot_path = b at h ⊢
          cases b with
          | true =>
            simp only [↓reduceIte] at h
            exact absurd h (check_access_exists_no_unmodeled _ _)
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
            generalize path_has_slash p = b at h ⊢
            cases b with
            | true =>
              simp only [↓reduceIte]
              exact unmodeled_intro i m
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
              by_cases hn : NAME_MAX < p.length
              · simp only [hn, ↓reduceIte]
                exact unmodeled_intro i m
              · simp only [hn, ↓reduceIte] at h ⊢
                generalize fs_under (m_fs m) p = b at h ⊢
                cases b with
                | true =>
                  simp only [↓reduceIte]
                  exact unmodeled_intro i m
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte] at h
                  generalize fs_lookup (m_fs m) p = r at h
                  cases r with
                  | none =>
                    dsimp only at h
                    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
                  | some _ =>
                    dsimp only at h
                    exact absurd h (check_access_exists_no_unmodeled _ _)

/-- Rocq: `check_faccessat_body_complete_ok`. -/
theorem check_faccessat_body_complete_ok (i : SyscallInput) (dirfd pathp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : faccessat_body_spec dirfd pathp i m i m (Ok eff m' evs)) :
    check_faccessat_body i dirfd pathp eff m = CheckOk m' evs := by
  unfold faccessat_body_spec at h
  unfold check_faccessat_body
  generalize read_cstr i.in_mem pathp = r at h ⊢
  cases r with
  | CstrTooLong =>
    dsimp only at h ⊢
    exact (check_ret_only_complete_ok i eff (errno_ret ENAMETOOLONG) m m' evs h).1
  | CstrFault =>
    dsimp only at h ⊢
    exact (check_ret_only_complete_ok i eff (errno_ret EFAULT) m m' evs h).1
  | CstrOk p =>
    dsimp only at h ⊢
    generalize path_eqb p [] = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact (check_ret_only_complete_ok i eff (errno_ret ENOENT) m m' evs h).1
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize (!bv_eqb dirfd AT_FDCWD32) = b at h ⊢
      cases b with
      | true => simp only [↓reduceIte, unmodeled_iff, reduceCtorEq] at h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize path_eqb p dot_path = b at h ⊢
        cases b with
        | true =>
          simp only [↓reduceIte] at h ⊢
          exact check_access_exists_complete_ok i eff m m' evs h
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          generalize path_eqb p dotdot_path = b at h ⊢
          cases b with
          | true =>
            simp only [↓reduceIte] at h ⊢
            exact check_access_exists_complete_ok i eff m m' evs h
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
            generalize path_has_slash p = b at h ⊢
            cases b with
            | true => simp only [↓reduceIte, unmodeled_iff, reduceCtorEq] at h
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
              by_cases hn : NAME_MAX < p.length
              · simp only [hn, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h
              · simp only [hn, ↓reduceIte] at h ⊢
                generalize fs_under (m_fs m) p = b at h ⊢
                cases b with
                | true => simp only [↓reduceIte, unmodeled_iff, reduceCtorEq] at h
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
                  generalize fs_lookup (m_fs m) p = r at h ⊢
                  cases r with
                  | none =>
                    dsimp only at h ⊢
                    exact (check_ret_only_complete_ok i eff (errno_ret ENOENT) m m' evs h).1
                  | some _ =>
                    dsimp only at h ⊢
                    exact check_access_exists_complete_ok i eff m m' evs h

/-- Rocq: `check_faccessat_body_complete_unmodeled`. -/
theorem check_faccessat_body_complete_unmodeled (i : SyscallInput) (dirfd pathp : word)
    (m : Model) (eff : SyscallEffect) (h : faccessat_body_spec dirfd pathp i m i m Unmodeled) :
    check_faccessat_body i dirfd pathp eff m = CheckUnmodeled := by
  unfold faccessat_body_spec at h
  unfold check_faccessat_body
  generalize read_cstr i.in_mem pathp = r at h ⊢
  cases r with
  | CstrTooLong =>
    dsimp only at h
    exact absurd h (ret_only_no_unmodeled _ i m)
  | CstrFault =>
    dsimp only at h
    exact absurd h (ret_only_no_unmodeled _ i m)
  | CstrOk p =>
    dsimp only at h ⊢
    generalize path_eqb p [] = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (ret_only_no_unmodeled _ i m)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize (!bv_eqb dirfd AT_FDCWD32) = b at h ⊢
      cases b with
      | true => simp only [↓reduceIte]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize path_eqb p dot_path = b at h ⊢
        cases b with
        | true =>
          simp only [↓reduceIte] at h
          exact absurd h (access_exists_no_unmodeled i m)
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          generalize path_eqb p dotdot_path = b at h ⊢
          cases b with
          | true =>
            simp only [↓reduceIte] at h
            exact absurd h (access_exists_no_unmodeled i m)
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
            generalize path_has_slash p = b at h ⊢
            cases b with
            | true => simp only [↓reduceIte]
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
              by_cases hn : NAME_MAX < p.length
              · simp only [hn, ↓reduceIte]
              · simp only [hn, ↓reduceIte] at h ⊢
                generalize fs_under (m_fs m) p = b at h ⊢
                cases b with
                | true => simp only [↓reduceIte]
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
                  generalize fs_lookup (m_fs m) p = r at h ⊢
                  cases r with
                  | none =>
                    dsimp only at h
                    exact absurd h (ret_only_no_unmodeled _ i m)
                  | some _ =>
                    dsimp only at h
                    exact absurd h (access_exists_no_unmodeled i m)

/-- No arm of the body claims a copy-in of its own: each returns either
through `check_ret_only`, which forces every ledger empty, or through
`check_access_exists`, which matches five empty lists.  That is what lets
the wrapper equate the WHOLE claimed ledger with the one pathname range
rather than with a prefix of it.  Rocq:
`check_faccessat_body_ok_copyins_nil`. -/
theorem check_faccessat_body_ok_copyins_nil (i : SyscallInput) (dirfd pathp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_faccessat_body i dirfd pathp eff m = CheckOk m' evs) : eff.eff_copyins = [] := by
  unfold check_faccessat_body at h
  generalize read_cstr i.in_mem pathp = r at h
  cases r with
  | CstrTooLong =>
    dsimp only at h
    obtain ⟨rfl, -, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl
  | CstrFault =>
    dsimp only at h
    obtain ⟨rfl, -, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl
  | CstrOk p =>
    dsimp only at h
    generalize path_eqb p [] = b at h
    cases b with
    | true =>
      simp only [↓reduceIte] at h
      obtain ⟨rfl, -, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      generalize (!bv_eqb dirfd AT_FDCWD32) = b at h
      cases b with
      | true => simp only [↓reduceIte, reduceCtorEq] at h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        generalize path_eqb p dot_path = b at h
        cases b with
        | true =>
          simp only [↓reduceIte] at h
          exact check_access_exists_ok_copyins_nil eff m m' evs h
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          generalize path_eqb p dotdot_path = b at h
          cases b with
          | true =>
            simp only [↓reduceIte] at h
            exact check_access_exists_ok_copyins_nil eff m m' evs h
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at h
            generalize path_has_slash p = b at h
            cases b with
            | true => simp only [↓reduceIte, reduceCtorEq] at h
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte] at h
              by_cases hn : NAME_MAX < p.length
              · simp only [hn, ↓reduceIte, reduceCtorEq] at h
              · simp only [hn, ↓reduceIte] at h
                generalize fs_under (m_fs m) p = b at h
                cases b with
                | true => simp only [↓reduceIte, reduceCtorEq] at h
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte] at h
                  generalize fs_lookup (m_fs m) p = r at h
                  cases r with
                  | none =>
                    dsimp only at h
                    obtain ⟨rfl, -, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
                    rfl
                  | some _ =>
                    dsimp only at h
                    exact check_access_exists_ok_copyins_nil eff m m' evs h

/-! ### The four exports, for each entry point -/

/-- An accepted `faccessat` effect is one `faccessat_spec` admits.  Rocq:
`check_faccessat_sound_ok`. -/
theorem check_faccessat_sound_ok (i : SyscallInput) (dirfd pathp mode : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_faccessat i dirfd pathp mode eff m = CheckOk m' evs) :
    faccessat_spec dirfd pathp mode i m (Ok eff m' evs) := by
  unfold check_faccessat at h
  unfold faccessat_spec
  apply bind_ok0 _ _ i m i m _ _ _ (input_ok i m)
  apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
  generalize (!modeled_access_mode mode) = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact check_ret_only_sound_ok i eff (errno_ret EINVAL) m m' evs h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!access_mode_f_ok mode) = b at h ⊢
    cases b with
    | true => simp only [↓reduceIte, reduceCtorEq] at h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      rw [check_copyins_after_ok_iff] at h
      obtain ⟨hreads, hchecked⟩ := h
      exact record_copyins_clear_ok _ _ i m eff m' evs hreads
        (check_faccessat_body_sound_ok i dirfd pathp (clear_copyins eff) m m' evs hchecked)

/-- A declined `faccessat` is one `faccessat_spec` declines.  Rocq:
`check_faccessat_sound_unmodeled`. -/
theorem check_faccessat_sound_unmodeled (i : SyscallInput) (dirfd pathp mode : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_faccessat i dirfd pathp mode eff m = CheckUnmodeled) :
    faccessat_spec dirfd pathp mode i m Unmodeled := by
  unfold check_faccessat at h
  unfold faccessat_spec
  apply bind_unmodeled2 _ _ i m i m [] (input_ok i m)
  apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
  generalize (!modeled_access_mode mode) = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!access_mode_f_ok mode) = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      apply record_copyins_unmodeled
      exact check_faccessat_body_sound_unmodeled i dirfd pathp (clear_copyins eff) m
        (check_copyins_after_unmodeled _ _ _ h)

/-- Every effect `faccessat_spec` admits is accepted.  Rocq:
`check_faccessat_complete_ok`. -/
theorem check_faccessat_complete_ok (i : SyscallInput) (dirfd pathp mode : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : faccessat_spec dirfd pathp mode i m (Ok eff m' evs)) :
    check_faccessat i dirfd pathp mode eff m = CheckOk m' evs := by
  unfold faccessat_spec at h
  have h := input_bind_ok_inv _ i m _ _ _ h
  have h := get_model_bind_ok_inv _ i m _ _ _ h
  unfold check_faccessat
  generalize (!modeled_access_mode mode) = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact (check_ret_only_complete_ok i eff (errno_ret EINVAL) m m' evs h).1
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!access_mode_f_ok mode) = b at h ⊢
    cases b with
    | true => simp only [↓reduceIte, unmodeled_iff, reduceCtorEq] at h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
      have hchecked := check_faccessat_body_complete_ok i dirfd pathp core m m' evs hcore
      have hnil := check_faccessat_body_ok_copyins_nil i dirfd pathp core m m' evs hchecked
      obtain ⟨ret, ws, zs, us, cs, copyins⟩ := core
      dsimp only at hnil
      subst hnil
      rw [check_copyins_after_ok_iff]
      exact ⟨rfl, hchecked⟩

/-- A call `faccessat_spec` declines is declined, whatever effect is
offered.  Rocq: `check_faccessat_complete_unmodeled`. -/
theorem check_faccessat_complete_unmodeled (i : SyscallInput) (dirfd pathp mode : word)
    (m : Model) (eff : SyscallEffect) (h : faccessat_spec dirfd pathp mode i m Unmodeled) :
    check_faccessat i dirfd pathp mode eff m = CheckUnmodeled := by
  unfold faccessat_spec at h
  have h := input_bind_unmodeled_inv _ i m h
  have h := get_model_bind_unmodeled_inv _ i m h
  unfold check_faccessat
  generalize (!modeled_access_mode mode) = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h
    exact absurd h (ret_only_no_unmodeled _ i m)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!access_mode_f_ok mode) = b at h ⊢
    cases b with
    | true => simp only [↓reduceIte]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      have h := record_copyins_unmodeled_inv _ _ i m h
      simp only [check_copyins_after,
        check_faccessat_body_complete_unmodeled i dirfd pathp m (clear_copyins eff) h]

/-- An accepted `faccessat2` effect is one `faccessat2_spec` admits.
Rocq: `check_faccessat2_sound_ok`. -/
theorem check_faccessat2_sound_ok (i : SyscallInput) (dirfd pathp mode flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_faccessat2 i dirfd pathp mode flags eff m = CheckOk m' evs) :
    faccessat2_spec dirfd pathp mode flags i m (Ok eff m' evs) := by
  unfold check_faccessat2 at h
  unfold faccessat2_spec
  apply bind_ok0 _ _ i m i m _ _ _ (input_ok i m)
  apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
  generalize (!modeled_access_mode mode) = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact check_ret_only_sound_ok i eff (errno_ret EINVAL) m m' evs h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!valid_access_flags flags) = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact check_ret_only_sound_ok i eff (errno_ret EINVAL) m m' evs h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize (!modeled_access_flags flags) = b at h ⊢
      cases b with
      | true => simp only [↓reduceIte, reduceCtorEq] at h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize (!access_mode_f_ok mode) = b at h ⊢
        cases b with
        | true => simp only [↓reduceIte, reduceCtorEq] at h
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          rw [check_copyins_after_ok_iff] at h
          obtain ⟨hreads, hchecked⟩ := h
          exact record_copyins_clear_ok _ _ i m eff m' evs hreads
            (check_faccessat_body_sound_ok i dirfd pathp (clear_copyins eff) m m' evs hchecked)

/-- A declined `faccessat2` is one `faccessat2_spec` declines.  Rocq:
`check_faccessat2_sound_unmodeled`. -/
theorem check_faccessat2_sound_unmodeled (i : SyscallInput) (dirfd pathp mode flags : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_faccessat2 i dirfd pathp mode flags eff m = CheckUnmodeled) :
    faccessat2_spec dirfd pathp mode flags i m Unmodeled := by
  unfold check_faccessat2 at h
  unfold faccessat2_spec
  apply bind_unmodeled2 _ _ i m i m [] (input_ok i m)
  apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
  generalize (!modeled_access_mode mode) = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!valid_access_flags flags) = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize (!modeled_access_flags flags) = b at h ⊢
      cases b with
      | true =>
        simp only [↓reduceIte]
        exact unmodeled_intro i m
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize (!access_mode_f_ok mode) = b at h ⊢
        cases b with
        | true =>
          simp only [↓reduceIte]
          exact unmodeled_intro i m
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          apply record_copyins_unmodeled
          exact check_faccessat_body_sound_unmodeled i dirfd pathp (clear_copyins eff) m
            (check_copyins_after_unmodeled _ _ _ h)

/-- Every effect `faccessat2_spec` admits is accepted.  Rocq:
`check_faccessat2_complete_ok`. -/
theorem check_faccessat2_complete_ok (i : SyscallInput) (dirfd pathp mode flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : faccessat2_spec dirfd pathp mode flags i m (Ok eff m' evs)) :
    check_faccessat2 i dirfd pathp mode flags eff m = CheckOk m' evs := by
  unfold faccessat2_spec at h
  have h := input_bind_ok_inv _ i m _ _ _ h
  have h := get_model_bind_ok_inv _ i m _ _ _ h
  unfold check_faccessat2
  generalize (!modeled_access_mode mode) = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact (check_ret_only_complete_ok i eff (errno_ret EINVAL) m m' evs h).1
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!valid_access_flags flags) = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact (check_ret_only_complete_ok i eff (errno_ret EINVAL) m m' evs h).1
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize (!modeled_access_flags flags) = b at h ⊢
      cases b with
      | true => simp only [↓reduceIte, unmodeled_iff, reduceCtorEq] at h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize (!access_mode_f_ok mode) = b at h ⊢
        cases b with
        | true => simp only [↓reduceIte, unmodeled_iff, reduceCtorEq] at h
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m _ m' evs h
          have hchecked := check_faccessat_body_complete_ok i dirfd pathp core m m' evs hcore
          have hnil := check_faccessat_body_ok_copyins_nil i dirfd pathp core m m' evs hchecked
          obtain ⟨ret, ws, zs, us, cs, copyins⟩ := core
          dsimp only at hnil
          subst hnil
          rw [check_copyins_after_ok_iff]
          exact ⟨rfl, hchecked⟩

/-- A call `faccessat2_spec` declines is declined, whatever effect is
offered.  Rocq: `check_faccessat2_complete_unmodeled`. -/
theorem check_faccessat2_complete_unmodeled (i : SyscallInput) (dirfd pathp mode flags : word)
    (m : Model) (eff : SyscallEffect) (h : faccessat2_spec dirfd pathp mode flags i m Unmodeled) :
    check_faccessat2 i dirfd pathp mode flags eff m = CheckUnmodeled := by
  unfold faccessat2_spec at h
  have h := input_bind_unmodeled_inv _ i m h
  have h := get_model_bind_unmodeled_inv _ i m h
  unfold check_faccessat2
  generalize (!modeled_access_mode mode) = b at h ⊢
  cases b with
  | true =>
    simp only [↓reduceIte] at h
    exact absurd h (ret_only_no_unmodeled _ i m)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize (!valid_access_flags flags) = b at h ⊢
    cases b with
    | true =>
      simp only [↓reduceIte] at h
      exact absurd h (ret_only_no_unmodeled _ i m)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      generalize (!modeled_access_flags flags) = b at h ⊢
      cases b with
      | true => simp only [↓reduceIte]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        generalize (!access_mode_f_ok mode) = b at h ⊢
        cases b with
        | true => simp only [↓reduceIte]
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
          have h := record_copyins_unmodeled_inv _ _ i m h
          simp only [check_copyins_after,
            check_faccessat_body_complete_unmodeled i dirfd pathp m (clear_copyins eff) h]

/-! ### close (57) — the checker

Mirrors the `close` half of `theories/LinuxProcessSem/Checks/Sys/Fs/Open.v`
at the header's baseline, where it is byte-identical to the port plan's.
The syscall has one decision and the checker is that decision made
computable.  `SYSCALL_DEFINE1(close, …)` (fs/open.c:1574-1602, Linux
v6.18.46) asks `file_close_fd` (fs/file.c:850-860, Linux v6.18.46) for
the descriptor, and a NULL there — a number at or past `max_fds`, or an
empty slot, the two tests `file_close_fd_locked` (fs/file.c:699-704,
Linux v6.18.46) makes — is the `-EBADF` of fs/open.c:1580-1581 with
nothing changed, which is the `none` arm's `check_ret_only` over the
model it was given.  Otherwise `file_close_fd_locked` has cleared the
slot and, at :705-706, handed the number back through `__put_unused_fd`
(fs/file.c:626-632, Linux v6.18.46) before the entry point calls
`filp_flush` (fs/open.c:1538-1556, Linux v6.18.46) at :1583, so the
`some` arm compares the effect against 0
over the model with that one entry removed and nothing else touched;
that the next `alloc_fd` (fs/file.c:570, Linux v6.18.46) refills the
freed number is `fd_remove`'s doing on the spec side, pinned there
(`Checks/Cases/Fs/Open.lean`, `dir_close_frees_the_lowest_slot`).  The
flush's own errno and the `-EINTR` a restart code is rewritten to
(fs/open.c:1594-1599, Linux v6.18.46) are outside `close_spec` for the
reasons its docstring in `Sys/Fs/Open.lean` gives at length; the
checker follows the spec it is proved against, so an effect carrying
either is `CheckReject`, and `Checks/Cases/Checks/Sys/Fs/Open.lean`
offers both rather than arguing them again.  Neither arm declines, so
the two `_unmodeled` lemmas hold by contradiction, exactly as Rocq's do. -/

/-- Rocq: `Checks.Sys.Fs.Open.check_close`.  The table lookup is the one
decision; `check_ret_only` compares the effect against the errno or the
zero, with the model the arm names and no events. -/
def check_close (fd : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | none   => check_ret_only eff (errno_ret EBADF) m []
  | some _ => check_ret_only eff (Z_to_bv 64 0) (with_fds (fd_remove (m_fds m) fd) m) []

/-- Rocq: `Checks.Sys.Fs.Open.check_close_sound_ok`.  A `CheckOk` is an
outcome of the spec: on a closed number the errno with the model
unchanged, on a held one the zero over `set_fds` of the shrunk table. -/
theorem check_close_sound_ok (fd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_close fd eff m = CheckOk m' evs) :
    close_spec fd i m (Ok eff m' evs) := by
  unfold check_close at h
  unfold close_spec
  apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none =>
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | some e =>
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m) (pure_ok _ i _)

/-- Rocq: `Checks.Sys.Fs.Open.check_close_sound_unmodeled`.  The checker
never declines — both arms are `check_ret_only` — so the hypothesis is
absurd. -/
theorem check_close_sound_unmodeled (fd : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_close fd eff m = CheckUnmodeled) :
    close_spec fd i m Unmodeled := by
  exfalso
  unfold check_close at h
  generalize fd_lookup (m_fds m) fd = r at h
  cases r with
  | none => exact check_ret_only_no_unmodeled _ _ _ _ h
  | some e => exact check_ret_only_no_unmodeled _ _ _ _ h

/-- Rocq: `Checks.Sys.Fs.Open.check_close_complete_ok`.  Every outcome the
spec admits is one the checker accepts, with the spec's model and no
events; the held arm's model comes out of `bind_set_fds_iff`. -/
theorem check_close_complete_ok (fd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : close_spec fd i m (Ok eff m' evs)) :
    check_close fd eff m = CheckOk m' evs := by
  unfold close_spec at h
  unfold check_close
  have h := bind_model_inv _ i m _ h
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none =>
    simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | some e =>
    simp only [bind_set_fds_iff, ret_only, pure_iff, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- Rocq: `Checks.Sys.Fs.Open.check_close_complete_unmodeled`.  The spec
never declines either, so the hypothesis is absurd. -/
theorem check_close_complete_unmodeled (fd : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (h : close_spec fd i m Unmodeled) :
    check_close fd eff m = CheckUnmodeled := by
  exfalso
  unfold close_spec at h
  have h := bind_model_inv _ i m _ h
  generalize fd_lookup (m_fds m) fd = r at h
  cases r with
  | none => simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
  | some e => simp only [bind_set_fds_iff, ret_only, pure_iff, reduceCtorEq] at h

/-! ### ftruncate (46) — the checker

Mirrors the `ftruncate` half of `theories/LinuxProcessSem/Checks/Sys/Fs/Open.v`
at the header's baseline, `f1006fe8`, the baseline the spec twin names.
The decisions are the spec's, in the
kernel's order, so which errno wins when two conditions hold is not this
file's choice:
`do_sys_ftruncate` (fs/open.c:202-211, Linux v6.18.46) refuses a negative
length before its `CLASS(fd, f)(fd)` looks the descriptor up, and
`do_ftruncate` (fs/open.c:163-200, Linux v6.18.46) makes its
`S_ISREG`-and-`FMODE_WRITE` test before the size is handed on.  The
model's zero-fill bound, `modeled_truncate_gap`, is consulted after both,
on a writable file alone, so a huge length on any kind that is not
writable is still the kernel's -EINVAL and not a decline
(`check_ftruncate_declines_only_on_a_held_writable_file`).

EVERY WRITABLE REGULAR FILE TAKES THE WRITABLE BODY, as the spec twin's
`ftruncate_spec` does: Rocq writes that body for `FdFileW | FdFileRW` and
again for `FdFileA`, and both are written here.  An O_APPEND or an O_RDWR
description carries FMODE_WRITE on an S_ISREG inode exactly as an
O_WRONLY one does, and `do_ftruncate`'s test reads nothing else.

WHAT THE ACCEPTED MODEL IS.  On the write-only file, the model the checker
hands back is `with_fs` over the resized image and nothing else: the
descriptor table is not rebuilt, because `do_sys_ftruncate` resolves the
descriptor through the class over `fdget` (include/linux/file.h:83, Linux
v6.18.46), not `fd_pos`'s `fdget_pos` (:85), and nothing on the path
reads or writes `f_pos`.  No effect a kernel reports can show where the
offset went, so what fixes it is the model the `CheckOk` names, and the
pins state that model whole: a checker that moved the offset would fail
them (`ftruncate_accepted_keeps_the_table` among them), not merely a lie
offered from outside.  The other arms answer through `check_ret_only`,
over the model they were given.

THE PROOFS keep Rocq's shape — one case split on the length gate, the
descriptor kind, the image lookup and the gap guard, in that order, on
both sides.  The two `if`s are split by `by_cases` and rewritten out of
both the checker and the spec by `ite_eq_left`/`ite_eq_right`, which
needs the two sides to spell each condition identically, as they do; the
two lookups are generalised out of both before the split, for the reason
the module header gives. -/

/-- Rocq: `Checks.Sys.Fs.Open.check_ftruncate`.  The seven kinds that are
not a writable regular file — the channels by the spec's premise that no
channel the model is handed is one — each answer the -EINVAL
`do_ftruncate` returns (fs/open.c:175-176, Linux v6.18.46) on its own
line, in Rocq's order, so that a change to one kind's answer is a
one-line diff against both the Rocq checker and the spec twin. -/
def check_ftruncate (fd len : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if bv_signed len < 0 then check_ret_only eff (errno_ret EINVAL) m []
  else
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdChannel _) => check_ret_only eff (errno_ret EINVAL) m []
  | some (.FdSocket _) => check_ret_only eff (errno_ret EINVAL) m []
  | some (.FdPipe _ _) => check_ret_only eff (errno_ret EINVAL) m []
  | some (.FdDevNull _ _) => check_ret_only eff (errno_ret EINVAL) m []
  | some .FdUrandom => check_ret_only eff (errno_ret EINVAL) m []
  | some (.FdFile _ _) => check_ret_only eff (errno_ret EINVAL) m []
  | some .FdDir => check_ret_only eff (errno_ret EINVAL) m []
  | some (.FdFileA p _) =>
      match fs_lookup (m_fs m) p with
      | none => CheckUnmodeled
      | some data =>
          if (!modeled_truncate_gap data len) then CheckUnmodeled
          else
            check_ret_only eff (Z_to_bv 64 0)
              (with_fs (fs_set (m_fs m) p (file_truncate data len)) m) []
  | some (.FdFileW p _) | some (.FdFileRW p _) =>
      match fs_lookup (m_fs m) p with
      | none => CheckUnmodeled
      | some data =>
          if (!modeled_truncate_gap data len) then CheckUnmodeled
          else
            check_ret_only eff (Z_to_bv 64 0)
              (with_fs (fs_set (m_fs m) p (file_truncate data len)) m) []

/-- Rocq: `Checks.Sys.Fs.Open.check_ftruncate_sound_ok`.  A `CheckOk` is an
outcome of the spec: an errno over the model unchanged, or the 0 over
`set_fs` of the resized image. -/
theorem check_ftruncate_sound_ok (fd len : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_ftruncate fd len eff m = CheckOk m' evs) :
    ftruncate_spec fd len i m (Ok eff m' evs) := by
  unfold check_ftruncate at h
  unfold ftruncate_spec
  by_cases hneg : bv_signed len < 0
  · rw [ite_eq_left hneg] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  rw [ite_eq_right hneg] at h ⊢
  apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none =>
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | some e =>
    cases e
    case FdFileA p _ | FdFileW p _ | FdFileRW p _ =>
      dsimp only at h ⊢
      generalize fs_lookup (m_fs m) p = r at h ⊢
      cases r with
      | none => cases h
      | some data =>
        dsimp only at h ⊢
        by_cases hg : (!modeled_truncate_gap data len) = true
        · rw [ite_eq_left hg] at h
          cases h
        · rw [ite_eq_right hg] at h ⊢
          obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
          exact bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m) (pure_ok _ i _)
    all_goals
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _

/-- Rocq: `Checks.Sys.Fs.Open.check_ftruncate_sound_unmodeled`.  The
checker declines only on the writable file — a path the image does not
hold, or a grow past the gap guard — and the spec declines there too. -/
theorem check_ftruncate_sound_unmodeled (fd len : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_ftruncate fd len eff m = CheckUnmodeled) :
    ftruncate_spec fd len i m Unmodeled := by
  unfold check_ftruncate at h
  unfold ftruncate_spec
  by_cases hneg : bv_signed len < 0
  · rw [ite_eq_left hneg] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  rw [ite_eq_right hneg] at h ⊢
  apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | some e =>
    cases e
    case FdFileA p _ | FdFileW p _ | FdFileRW p _ =>
      dsimp only at h ⊢
      generalize fs_lookup (m_fs m) p = r at h ⊢
      cases r with
      | none => exact unmodeled_intro i m
      | some data =>
        dsimp only at h ⊢
        by_cases hg : (!modeled_truncate_gap data len) = true
        · rw [ite_eq_left hg]
          exact unmodeled_intro i m
        · rw [ite_eq_right hg] at h
          exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
    all_goals exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

/-- Rocq: `Checks.Sys.Fs.Open.check_ftruncate_complete_ok`.  Every outcome
the spec admits is one the checker accepts, with the spec's model and no
events; the writable arm's model comes out of `bind_set_fs_iff`. -/
theorem check_ftruncate_complete_ok (fd len : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : ftruncate_spec fd len i m (Ok eff m' evs)) :
    check_ftruncate fd len eff m = CheckOk m' evs := by
  unfold ftruncate_spec at h
  unfold check_ftruncate
  by_cases hneg : bv_signed len < 0
  · rw [ite_eq_left hneg] at h ⊢
    simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  rw [ite_eq_right hneg] at h ⊢
  have h := bind_model_inv _ i m _ h
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none =>
    simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | some e =>
    cases e
    case FdFileA p _ | FdFileW p _ | FdFileRW p _ =>
      dsimp only at h ⊢
      generalize fs_lookup (m_fs m) p = r at h ⊢
      cases r with
      | none => simp only [unmodeled_iff, reduceCtorEq] at h
      | some data =>
        dsimp only at h ⊢
        by_cases hg : (!modeled_truncate_gap data len) = true
        · rw [ite_eq_left hg] at h
          simp only [unmodeled_iff, reduceCtorEq] at h
        · rw [ite_eq_right hg] at h ⊢
          simp only [bind_set_fs_iff, ret_only, pure_iff, outcome.Ok.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    all_goals
      simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- Rocq: `Checks.Sys.Fs.Open.check_ftruncate_complete_unmodeled`.  Where
the spec declines, the checker declines, whatever effect it is offered;
every errno arm and the writable arm's success are `pure`, which never
yields `Unmodeled`. -/
theorem check_ftruncate_complete_unmodeled (fd len : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (h : ftruncate_spec fd len i m Unmodeled) :
    check_ftruncate fd len eff m = CheckUnmodeled := by
  unfold ftruncate_spec at h
  unfold check_ftruncate
  by_cases hneg : bv_signed len < 0
  · rw [ite_eq_left hneg] at h
    simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
  rw [ite_eq_right hneg] at h ⊢
  have h := bind_model_inv _ i m _ h
  generalize fd_lookup (m_fds m) fd = r at h ⊢
  cases r with
  | none => simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
  | some e =>
    cases e
    case FdFileA p _ | FdFileW p _ | FdFileRW p _ =>
      dsimp only at h ⊢
      generalize fs_lookup (m_fs m) p = r at h ⊢
      cases r with
      | none => rfl
      | some data =>
        dsimp only at h ⊢
        by_cases hg : (!modeled_truncate_gap data len) = true
        · rw [ite_eq_left hg]
        · rw [ite_eq_right hg] at h
          simp only [bind_set_fs_iff, ret_only, pure_iff, reduceCtorEq] at h
    all_goals simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h

/-! #### The frame lemmas

The two facts the registration's arm-level obligations are derived from,
stated beside the checker as `Checks/Sys/Fs/EventFd.lean`,
`Checks/Sys/Fs/Namei.lean` and `Checks/Sys/Fs/Sync.lean` state theirs:
the ledger half is Rocq's `VmMapsDisjoint.check_ftruncate_frame`, and the
descriptor half is Lean-only, the fact the invariant registry's
descriptor-table and pipe-capacity entries read through
`arm_preserves_of_view_frame`.  Both rest on one inversion, that an
accepted model is the model handed in or `with_fs` over it:
`ftruncate_spec`'s success arm writes the resized image and nothing else
— no `set_fds`, and `with_fs` keeps a stat pin exactly when its path
survives (`statpins_restrict`, `State/Model.lean`).
That is the spec's narrowing, not the kernel's: `do_truncate`
(fs/open.c:39-71, Linux v6.18.46) also asks for the times `do_ftruncate`
names (`ATTR_MTIME | ATTR_CTIME`, fs/open.c:195-196), which the pin
stores and `stat_stable_eqb` (`Sys/Uapi/Fs.lean`) leaves free, and, for
some callers, asks for the file's setid bits to be cleared
(fs/open.c:56-61, Linux v6.18.46).  `notify_change` (fs/attr.c:489-503,
Linux v6.18.46) turns that request into a mode change and hands it, with
the times, to the inode's `->setattr` or, where the inode has none
(fs/attr.c:545-548, Linux v6.18.46), to `simple_setattr`
(fs/libfs.c:903-918, Linux v6.18.46).  What is applied is that
function's choice:
- `setattr_copy` (fs/attr.c:332-359, Linux v6.18.46) applies both, and
  `simple_setattr` (fs/libfs.c:915, Linux v6.18.46), `shmem_setattr`
  (mm/shmem.c:1365, Linux v6.18.46) and `ext4_setattr`
  (fs/ext4/inode.c:6079, Linux v6.18.46) call it;
- `nfs_setattr` (fs/nfs/inode.c:726-728, Linux v6.18.46) drops the mode
  change, leaving the bits to the server, and knfsd does not ask for it:
  `__nfsd_setattr` (fs/nfsd/vfs.c:450-458, Linux v6.18.46) passes a size
  change to `notify_change` as `ATTR_SIZE | ATTR_CTIME | ATTR_MTIME`
  alone.  That leaves them to the exported inode's `->setattr`, which
  runs under the credentials knfsd installs for the request, and those
  lack CAP_FSETID when the export does not map the caller to root
  (`nfsd_setuser`, fs/nfsd/auth.c:77-78, drops `CAP_NFSD_SET`,
  include/linux/capability.h:57-69, which holds it; Linux v6.18.46).  So
  an exported FUSE file system whose daemon negotiated
  `FUSE_HANDLE_KILLPRIV_V2` (include/uapi/linux/fuse.h:429-433, Linux
  v6.18.46) asks the daemon to clear S_ISUID and a group-executable
  S_ISGID (`fuse_do_setattr`, fs/fuse/dir.c:2041-2043, Linux v6.18.46);
- SMB drops the mode change and sets the times itself.  After a size
  change that succeeds, `cifs_file_set_size`
  (fs/smb/client/inode.c:3107-3110, Linux v6.18.46) calls
  `cifs_setsize`, which sets the inode's mtime and ctime to the current
  time (fs/smb/client/inode.c:3039, Linux v6.18.46).  `cifs_setattr_unix`
  then clears ATTR_CTIME and ATTR_MTIME from the request, to avoid
  setting timestamps on the server, and drops ATTR_MODE when
  ATTR_KILL_SUID or ATTR_KILL_SGID is set
  (fs/smb/client/inode.c:3178-3188, Linux v6.18.46), and
  `cifs_setattr_nounix` does the same (fs/smb/client/inode.c:3356-3361
  and fs/smb/client/inode.c:3386-3388, Linux v6.18.46);
- `fuse_setattr` (fs/fuse/dir.c:2136-2163, Linux v6.18.46) asks its
  server again for at most S_ISUID and a group-executable S_ISGID, or
  leaves both to the server.

Where the bits are cleared, the pinned `st_mode` still holds them, and
`stat_stable_eqb` compares it — a false rejection in the stat pin's
comparison, which predates this arm.  Which bits `do_truncate` asks
for, at v6.18.46, its `dentry_needs_remove_privs`
(fs/inode.c:2214-2230, Linux v6.18.46) leaves to
`setattr_should_drop_suidgid` (fs/attr.c:63-79, Linux v6.18.46), which
asks for none unless the caller fails `capable(CAP_FSETID)`, the initial
user namespace's test (kernel/capability.c:414-417).  For such a caller
it asks for S_ISUID where it is set, and for S_ISGID where it is set and
the file is group-executable, or where the file's group is not one of
the caller's and the caller lacks CAP_FSETID in its own user namespace
over the inode's ids too (`setattr_should_drop_sgid`, fs/attr.c:33-45,
which calls `in_group_or_capable`, fs/inode.c:2910-2918, which calls
`capable_wrt_inode_uidgid`, kernel/capability.c:473-480, Linux
v6.18.46).  Every mainline release from v4.17 to v6.1 asks for S_ISGID
in fewer cases: at v6.1, `do_truncate` reaches `should_remove_suid`,
which asks for it only on a group-executable file (lines 1957 to 1977 of
that version's fs/inode.c).  Mainline took the rule above at v6.2, and
the 5.10.y, 5.15.y and 6.1.y stable branches took it as a backport, at
5.10.176, 5.15.103 and 6.1.15 (6.1.188's `setattr_should_drop_sgid` is
lines 36 to 49 of its fs/attr.c), while 4.19.325 and 5.4.302 keep
v6.1's rule.

The two lemmas are proved from that inversion rather than by
`Checks/VmMapsDisjoint.lean`'s `vm_frame2`.
The close half of this file states no frame lemma, which the module
header explains; `Checks/Arms/Fs/Open.lean` derives
`arm_ftruncate_preserves_vm` and the registry facts for 46 from these
two. -/

/-- An accepted `ftruncate` answers over the model it was given, or over
that model with the file image replaced.  Lean-only: the common step of
the two frame lemmas below. -/
theorem check_ftruncate_ok_model (fd len : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_ftruncate fd len eff m = CheckOk m' evs) :
    m' = m ∨ ∃ fs, m' = with_fs fs m := by
  unfold check_ftruncate at h
  by_cases hneg : bv_signed len < 0
  · rw [ite_eq_left hneg] at h
    exact Or.inl ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2.1
  rw [ite_eq_right hneg] at h
  generalize fd_lookup (m_fds m) fd = r at h
  cases r with
  | none => exact Or.inl ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2.1
  | some e =>
    cases e
    case FdFileA p _ | FdFileW p _ | FdFileRW p _ =>
      dsimp only at h
      generalize fs_lookup (m_fs m) p = r at h
      cases r with
      | none => cases h
      | some data =>
        dsimp only at h
        by_cases hg : (!modeled_truncate_gap data len) = true
        · rw [ite_eq_left hg] at h
          cases h
        · rw [ite_eq_right hg] at h
          exact Or.inr ⟨_, ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2.1⟩
    all_goals exact Or.inl ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2.1

/-- Rocq: `VmMapsDisjoint.check_ftruncate_frame`.  An accepted `ftruncate`
leaves the VM ledger where it was; a `*_frame` rather than a
`*_preserves`, since nothing in `m_vmmaps` is written for `vm_wf` to be
re-established over. -/
theorem check_ftruncate_frame (fd len : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_ftruncate fd len eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  rcases check_ftruncate_ok_model fd len eff m m' evs h with rfl | ⟨fs, rfl⟩ <;> rfl

/-- Nor does it move the descriptor subsystem: `with_fs` rebuilds the
model around a new image and hands `m_fd` back as it was, so neither the
table — the offset included, as the section header argues — nor the
pipes change.  Lean-only. -/
theorem check_ftruncate_fd_state_frame (fd len : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_ftruncate fd len eff m = CheckOk m' evs) :
    m'.m_fd = m.m_fd := by
  rcases check_ftruncate_ok_model fd len eff m m' evs h with rfl | ⟨fs, rfl⟩ <;> rfl

/-! ## The witness — `Checks/Witness/Fs/Open.v`

Mirrors `theories/LinuxProcessSem/Checks/Witness/Fs/Open.v`.  A witness
exhibits one admissible outcome for a spec in the matching `Sys` module,
which is what progress is proved from: the receptiveness field of the
arm the registration step builds is `openat_witness_ok` below, applied to
the registers the arm reads.

The witness follows the spec's own decision tree.  On every deterministic
branch it is the branch's errno; on every branch that declines it is
`Unmodeled`, which is an admissible outcome and is what makes progress
hold there; and on every branch that mints a descriptor it draws the
environmental errno `witness_errno` (`Checks/Witness/Prelude.lean`), the
head of `openat_errnos`, rather than the descriptor — because the
descriptor branch has to name the lowest free fd and the model it builds,
and the errno branch names neither.  `-ENOMEM` is a real answer of the
kernel here, and the ledger says which one: the witness records the
pathname copy-in beside it, so it is `alloc_empty_file`'s
(fs/file_table.c:258-260, Linux v6.18.46), failing in `path_openat`
(fs/namei.c:4124) after `getname` (fs/open.c:1431) has copied the
pathname in and `get_unused_fd_flags` (:1435) has reserved a slot.
`getname_flags`'s own `-ENOMEM` (fs/namei.c:146-148, Linux v6.18.46), when `__getname`
cannot allocate the buffer, fails before any byte is read and would leave
the ledger empty; the checker refuses THAT effect
(`Checks/Cases/Checks/Sys/Fs/Open.lean`'s ledger pins) and the witness
does not draw it.  That the head of the set is `witness_errno`
is pinned in `Checks/Cases/Checks/Witness/Prelude.lean`, so a reordering
of `openat_errnos` fails there before it fails here. -/

/-- The witness after the input and model reads.  Rocq:
`Checks.Witness.Fs.Open.openat_core_witness`. -/
def openat_core_witness (dirfd pathp flags : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  if !modeled_open_flags flags then Unmodeled
  else
    match read_cstr i.in_mem pathp with
    | CstrTooLong => ret_outcome (errno_ret ENAMETOOLONG) m
    | CstrFault => ret_outcome (errno_ret EFAULT) m
    | CstrOk p =>
        if path_eqb p [] then ret_outcome (errno_ret ENOENT) m
        else if !bv_eqb dirfd AT_FDCWD32 then Unmodeled
        else if path_has_slash p then
          if path_eqb p localtime_path then
            match fs_lookup (m_fs m) localtime_path with
            | some _ => Unmodeled
            | none =>
                if fs_under (m_fs m) localtime_path then Unmodeled
                else if flag_set (bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))))
                          O_CREAT
                then Unmodeled
                else ret_outcome (errno_ret ENOENT) m
          else if path_eqb p devnull_path then
            match fs_lookup (m_fs m) devnull_path with
            | some _ => Unmodeled
            | none =>
                if fs_under (m_fs m) devnull_path then Unmodeled
                else
                  let fl := bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags)))
                  if fl == 0 then ret_outcome (errno_ret witness_errno) m
                  else if fl == wr_create_flags then ret_outcome (errno_ret witness_errno) m
                  else if is_excl_create fl then ret_outcome (errno_ret EEXIST) m
                  else if fl == O_DIRECTORY then ret_outcome (errno_ret ENOTDIR) m
                  else if fl == append_create_flags then ret_outcome (errno_ret witness_errno) m
                  else if rdwr_open_word fl then ret_outcome (errno_ret witness_errno) m
                  else if is_rdwr_excl_create fl then ret_outcome (errno_ret EEXIST) m
                  else Unmodeled
          else if path_eqb p urandom_path then
            match fs_lookup (m_fs m) urandom_path with
            | some _ => Unmodeled
            | none =>
                if fs_under (m_fs m) urandom_path then Unmodeled
                else
                  let fl := bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags)))
                  if fl == 0 then ret_outcome (errno_ret witness_errno) m
                  else if is_excl_create fl then ret_outcome (errno_ret EEXIST) m
                  else if fl == O_DIRECTORY then ret_outcome (errno_ret ENOTDIR) m
                  else if is_rdwr_excl_create fl then ret_outcome (errno_ret EEXIST) m
                  else Unmodeled
          else
            match tmp_name p with
            | some n =>
                if NAME_MAX < n.length then Unmodeled
                else
                  let fl := bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags)))
                  if fl == 0 then
                    (if fs_under (m_fs m) p then Unmodeled
                     else match fs_lookup (m_fs m) p with
                          | none => Unmodeled
                          | some _ => ret_outcome (errno_ret witness_errno) m)
                  else if fl == wr_create_flags then
                    (if path_is_dirref p || fs_under (m_fs m) p
                     then ret_outcome (errno_ret EISDIR) m
                     else ret_outcome (errno_ret witness_errno) m)
                  else Unmodeled
            | none => Unmodeled
        else
          let fl := bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags)))
          if fl == 0 then
            if path_is_dirref p then ret_outcome (errno_ret witness_errno) m
            else
              match fs_lookup (m_fs m) p with
              | none => ret_outcome (errno_ret ENOENT) m
              | some _ => ret_outcome (errno_ret witness_errno) m
          else if fl == wr_create_flags then
            if path_is_dirref p || fs_under (m_fs m) p then ret_outcome (errno_ret EISDIR) m
            else ret_outcome (errno_ret witness_errno) m
          else if is_excl_create fl then
            if path_is_dirref p || fs_under (m_fs m) p then ret_outcome (errno_ret EEXIST) m
            else
              match fs_lookup (m_fs m) p with
              | some _ => ret_outcome (errno_ret EEXIST) m
              | none => ret_outcome (errno_ret witness_errno) m
          else if fl == O_DIRECTORY then
            if path_is_dirref p then ret_outcome (errno_ret witness_errno) m
            else if NAME_MAX < p.length then Unmodeled
            else if fs_under (m_fs m) p then Unmodeled
            else
              match fs_lookup (m_fs m) p with
              | none => ret_outcome (errno_ret ENOENT) m
              | some _ => ret_outcome (errno_ret ENOTDIR) m
          else if fl == append_create_flags then
            if path_is_dirref p || fs_under (m_fs m) p then ret_outcome (errno_ret EISDIR) m
            else ret_outcome (errno_ret witness_errno) m
          else if rdwr_open_word fl then
            if path_is_dirref p || fs_under (m_fs m) p then ret_outcome (errno_ret EISDIR) m
            else
              match fs_lookup (m_fs m) p with
              | none =>
                  if flag_set fl O_CREAT then ret_outcome (errno_ret witness_errno) m
                  else ret_outcome (errno_ret ENOENT) m
              | some _ => ret_outcome (errno_ret witness_errno) m
          else if is_rdwr_excl_create fl then
            if path_is_dirref p || fs_under (m_fs m) p then ret_outcome (errno_ret EEXIST) m
            else
              match fs_lookup (m_fs m) p with
              | some _ => ret_outcome (errno_ret EEXIST) m
              | none => ret_outcome (errno_ret witness_errno) m
          else Unmodeled

/-- The `openat` witness: the core's outcome with the pathname copy-in
recorded, as `openat_spec` records it.  Rocq:
`Checks.Witness.Fs.Open.openat_witness`. -/
def openat_witness (dirfd pathp flags : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  outcome_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
    (openat_core_witness dirfd pathp flags i m)

/-- A descriptor-minting arm admits the environmental errno the witness
draws: `alt_l` into `errno_from`, whose head is `witness_errno`. -/
theorem open_result_spec_witness (m : Model) (mk : word → Model → Model) (i : SyscallInput) :
    open_result_spec m mk i m (ret_outcome (errno_ret witness_errno) m) := by
  unfold open_result_spec
  apply alt_l
  apply bind_step _ _ i m witness_errno m _ (errno_head_witness _ _ i m)
  exact pure_ok _ i m

/-- The same for `create_wronly`. -/
theorem create_wronly_witness (p : path) (m : Model) (i : SyscallInput) :
    create_wronly p m i m (ret_outcome (errno_ret witness_errno) m) := by
  unfold create_wronly
  apply alt_l
  apply bind_step _ _ i m witness_errno m _ (errno_head_witness _ _ i m)
  exact pure_ok _ i m

/-- The same for `open_append`. -/
theorem open_append_witness (p : path) (m : Model) (i : SyscallInput) :
    open_append p m i m (ret_outcome (errno_ret witness_errno) m) := by
  unfold open_append
  apply alt_l
  apply bind_step _ _ i m witness_errno m _ (errno_head_witness _ _ i m)
  exact pure_ok _ i m

/-- The same for `open_rdwr`, whatever image the arm computed. -/
theorem open_rdwr_witness (p : path) (fs' : Fs.Fs) (m : Model) (i : SyscallInput) :
    open_rdwr p fs' m i m (ret_outcome (errno_ret witness_errno) m) := by
  unfold open_rdwr
  apply alt_l
  apply bind_step _ _ i m witness_errno m _ (errno_head_witness _ _ i m)
  exact pure_ok _ i m

/-- Rocq: `Checks.Witness.Fs.Open.openat_core_witness_ok`, the spec's own
case split with one prelude lemma per leaf. -/
theorem openat_core_witness_ok (dirfd pathp flags : word) (i : SyscallInput) (m : Model) :
    openat_core_spec dirfd pathp flags i m (openat_core_witness dirfd pathp flags i m) := by
  unfold openat_core_spec openat_core_witness
  apply bind_step _ _ i m i m _ (input_ok i m)
  apply bind_step _ _ i m m m _ (get_model_ok i m)
  generalize (!modeled_open_flags flags) = b
  cases b with
  | true =>
    simp only [↓reduceIte]
    exact unmodeled_intro i m
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold openat_body_spec
    generalize read_cstr i.in_mem pathp = r
    cases r with
    | CstrTooLong =>
      dsimp only
      exact pure_ok _ i m
    | CstrFault =>
      dsimp only
      exact pure_ok _ i m
    | CstrOk p =>
      dsimp only
      generalize path_eqb p [] = b
      cases b with
      | true =>
        simp only [↓reduceIte]
        exact pure_ok _ i m
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        generalize (!bv_eqb dirfd AT_FDCWD32) = b
        cases b with
        | true =>
          simp only [↓reduceIte]
          exact unmodeled_intro i m
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          unfold openat_resolved_spec
          generalize path_has_slash p = b
          cases b with
          | true =>
            simp only [↓reduceIte]
            unfold openat_sep_spec
            generalize path_eqb p localtime_path = b
            cases b with
            | true =>
              simp only [↓reduceIte]
              unfold openat_localtime_spec
              generalize fs_lookup (m_fs m) localtime_path = r
              cases r with
              | some _ =>
                dsimp only
                exact unmodeled_intro i m
              | none =>
                dsimp only
                generalize fs_under (m_fs m) localtime_path = b
                cases b with
                | true =>
                  simp only [↓reduceIte]
                  exact unmodeled_intro i m
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  generalize flag_set
                    (bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags)))) O_CREAT = b
                  cases b with
                  | true =>
                    simp only [↓reduceIte]
                    exact unmodeled_intro i m
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    exact pure_ok _ i m
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              generalize path_eqb p devnull_path = b
              cases b with
              | true =>
                simp only [↓reduceIte]
                unfold openat_devnull_spec
                generalize fs_lookup (m_fs m) devnull_path = r
                cases r with
                | some _ =>
                  dsimp only
                  exact unmodeled_intro i m
                | none =>
                  dsimp only
                  generalize fs_under (m_fs m) devnull_path = b
                  cases b with
                  | true =>
                    simp only [↓reduceIte]
                    exact unmodeled_intro i m
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    generalize bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))) = fl
                    generalize (fl == 0) = b
                    cases b with
                    | true =>
                      simp only [↓reduceIte]
                      exact open_result_spec_witness m _ i
                    | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      generalize (fl == wr_create_flags) = b
                      cases b with
                      | true =>
                        simp only [↓reduceIte]
                        exact open_result_spec_witness m _ i
                      | false =>
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        generalize is_excl_create fl = b
                        cases b with
                        | true =>
                          simp only [↓reduceIte]
                          exact pure_ok _ i m
                        | false =>
                          simp only [Bool.false_eq_true, ↓reduceIte]
                          generalize (fl == O_DIRECTORY) = b
                          cases b with
                          | true =>
                            simp only [↓reduceIte]
                            exact pure_ok _ i m
                          | false =>
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            generalize (fl == append_create_flags) = b
                            cases b with
                            | true =>
                              simp only [↓reduceIte]
                              exact open_result_spec_witness m _ i
                            | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              generalize rdwr_open_word fl = b
                              cases b with
                              | true =>
                                simp only [↓reduceIte]
                                exact open_result_spec_witness m _ i
                              | false =>
                                simp only [Bool.false_eq_true, ↓reduceIte]
                                generalize is_rdwr_excl_create fl = b
                                cases b with
                                | true =>
                                  simp only [↓reduceIte]
                                  exact pure_ok _ i m
                                | false =>
                                  simp only [Bool.false_eq_true, ↓reduceIte]
                                  exact unmodeled_intro i m
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                generalize path_eqb p urandom_path = b
                cases b with
                | true =>
                  simp only [↓reduceIte]
                  unfold openat_urandom_spec
                  generalize fs_lookup (m_fs m) urandom_path = r
                  cases r with
                  | some _ =>
                    dsimp only
                    exact unmodeled_intro i m
                  | none =>
                    dsimp only
                    generalize fs_under (m_fs m) urandom_path = b
                    cases b with
                    | true =>
                      simp only [↓reduceIte]
                      exact unmodeled_intro i m
                    | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      generalize bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))) = fl
                      generalize (fl == 0) = b
                      cases b with
                      | true =>
                        simp only [↓reduceIte]
                        exact open_result_spec_witness m _ i
                      | false =>
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        generalize is_excl_create fl = b
                        cases b with
                        | true =>
                          simp only [↓reduceIte]
                          exact pure_ok _ i m
                        | false =>
                          simp only [Bool.false_eq_true, ↓reduceIte]
                          generalize (fl == O_DIRECTORY) = b
                          cases b with
                          | true =>
                            simp only [↓reduceIte]
                            exact pure_ok _ i m
                          | false =>
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            generalize is_rdwr_excl_create fl = b
                            cases b with
                            | true =>
                              simp only [↓reduceIte]
                              exact pure_ok _ i m
                            | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              exact unmodeled_intro i m
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  generalize tmp_name p = r
                  cases r with
                  | none =>
                    dsimp only
                    exact unmodeled_intro i m
                  | some n =>
                    dsimp only
                    unfold openat_tmp_spec
                    by_cases hn : NAME_MAX < n.length
                    · simp only [hn, ↓reduceIte]
                      exact unmodeled_intro i m
                    · simp only [hn, ↓reduceIte]
                      generalize bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))) = fl
                      generalize (fl == 0) = b
                      cases b with
                      | true =>
                        simp only [↓reduceIte]
                        generalize fs_under (m_fs m) p = c
                        cases c with
                        | true =>
                          simp only [↓reduceIte]
                          exact unmodeled_intro i m
                        | false =>
                          simp only [Bool.false_eq_true, ↓reduceIte]
                          unfold openat_read_spec
                          generalize fs_lookup (m_fs m) p = r
                          cases r with
                          | none =>
                            dsimp only
                            exact unmodeled_intro i m
                          | some _ =>
                            dsimp only
                            generalize path_is_dirref p = b
                            cases b with
                            | true =>
                              simp only [↓reduceIte]
                              exact open_result_spec_witness m _ i
                            | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              exact open_result_spec_witness m _ i
                      | false =>
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        generalize (fl == wr_create_flags) = b
                        cases b with
                        | true =>
                          simp only [↓reduceIte]
                          unfold openat_create_spec
                          generalize (path_is_dirref p || fs_under (m_fs m) p) = c
                          cases c with
                          | true =>
                            simp only [↓reduceIte]
                            exact pure_ok _ i m
                          | false =>
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            exact create_wronly_witness p m i
                        | false =>
                          simp only [Bool.false_eq_true, ↓reduceIte]
                          exact unmodeled_intro i m
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            unfold openat_read_spec openat_create_spec openat_excl_spec openat_dir_spec
              openat_append_spec openat_rdwr_spec openat_rdwr_excl_spec
            generalize bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 open_ignored_flags))) = fl
            generalize (fl == 0) = b
            cases b with
            | true =>
              simp only [↓reduceIte]
              generalize path_is_dirref p = b
              cases b with
              | true =>
                simp only [↓reduceIte]
                exact open_result_spec_witness m _ i
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                generalize fs_lookup (m_fs m) p = r
                cases r with
                | none =>
                  dsimp only
                  exact pure_ok _ i m
                | some _ =>
                  dsimp only
                  exact open_result_spec_witness m _ i
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              generalize (fl == wr_create_flags) = b
              cases b with
              | true =>
                simp only [↓reduceIte]
                generalize (path_is_dirref p || fs_under (m_fs m) p) = b
                cases b with
                | true =>
                  simp only [↓reduceIte]
                  exact pure_ok _ i m
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  exact create_wronly_witness p m i
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                generalize is_excl_create fl = b
                cases b with
                | true =>
                  simp only [↓reduceIte]
                  generalize (path_is_dirref p || fs_under (m_fs m) p) = b
                  cases b with
                  | true =>
                    simp only [↓reduceIte]
                    exact pure_ok _ i m
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    generalize fs_lookup (m_fs m) p = r
                    cases r with
                    | some _ =>
                      dsimp only
                      exact pure_ok _ i m
                    | none =>
                      dsimp only
                      exact create_wronly_witness p m i
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  generalize (fl == O_DIRECTORY) = b
                  cases b with
                  | true =>
                    simp only [↓reduceIte]
                    generalize path_is_dirref p = b
                    cases b with
                    | true =>
                      simp only [↓reduceIte]
                      exact open_result_spec_witness m _ i
                    | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      by_cases hn : NAME_MAX < p.length
                      · simp only [hn, ↓reduceIte]
                        exact unmodeled_intro i m
                      · simp only [hn, ↓reduceIte]
                        generalize fs_under (m_fs m) p = b
                        cases b with
                        | true =>
                          simp only [↓reduceIte]
                          exact unmodeled_intro i m
                        | false =>
                          simp only [Bool.false_eq_true, ↓reduceIte]
                          generalize fs_lookup (m_fs m) p = r
                          cases r with
                          | none =>
                            dsimp only
                            exact pure_ok _ i m
                          | some _ =>
                            dsimp only
                            exact pure_ok _ i m
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    generalize (fl == append_create_flags) = b
                    cases b with
                    | true =>
                      simp only [↓reduceIte]
                      generalize (path_is_dirref p || fs_under (m_fs m) p) = b
                      cases b with
                      | true =>
                        simp only [↓reduceIte]
                        exact pure_ok _ i m
                      | false =>
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        exact open_append_witness p m i
                    | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      generalize rdwr_open_word fl = b
                      cases b with
                      | true =>
                        simp only [↓reduceIte]
                        generalize (path_is_dirref p || fs_under (m_fs m) p) = b
                        cases b with
                        | true =>
                          simp only [↓reduceIte]
                          exact pure_ok _ i m
                        | false =>
                          simp only [Bool.false_eq_true, ↓reduceIte]
                          generalize fs_lookup (m_fs m) p = r
                          cases r with
                          | none =>
                            dsimp only
                            generalize flag_set fl O_CREAT = c
                            cases c with
                            | true =>
                              simp only [↓reduceIte]
                              exact open_rdwr_witness p _ m i
                            | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              exact pure_ok _ i m
                          | some _ =>
                            dsimp only
                            exact open_rdwr_witness p _ m i
                      | false =>
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        generalize is_rdwr_excl_create fl = b
                        cases b with
                        | true =>
                          simp only [↓reduceIte]
                          generalize (path_is_dirref p || fs_under (m_fs m) p) = b
                          cases b with
                          | true =>
                            simp only [↓reduceIte]
                            exact pure_ok _ i m
                          | false =>
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            generalize fs_lookup (m_fs m) p = r
                            cases r with
                            | some _ =>
                              dsimp only
                              exact pure_ok _ i m
                            | none =>
                              dsimp only
                              exact open_rdwr_witness p _ m i
                        | false =>
                          simp only [Bool.false_eq_true, ↓reduceIte]
                          exact unmodeled_intro i m

/-- Rocq: `Checks.Witness.Fs.Open.openat_witness_ok`. -/
theorem openat_witness_ok (dirfd pathp flags : word) (i : SyscallInput) (m : Model) :
    openat_spec dirfd pathp flags i m (openat_witness dirfd pathp flags i m) := by
  unfold openat_spec openat_witness
  apply bind_step _ _ i m i m _ (input_ok i m)
  exact record_copyins_outcome _ _ i m _ (openat_core_witness_ok dirfd pathp flags i m)

/-! ### faccessat and faccessat2 — the witness

The deterministic errno arms, the fail-closed `Unmodeled`, or, where the
path resolves, plain SUCCESS.  That is the alt's RIGHT branch, unlike
`openat_witness`, which takes the injectable-errno branch to avoid
building a new model state.  Nothing has to be built here: faccessat
changes no state, so both alternatives of `access_exists_spec` return the
same model, and the success one is the outcome a real run produces.
Ported from the faccessat half of `Checks/Witness/Fs/Open.v`. -/

/-- The body's outcome: `faccessat_body_spec`'s deterministic arms, its
declines, and 0 wherever `access_exists_spec` is reached.  Rocq:
`faccessat_body_witness`. -/
def faccessat_body_witness (dirfd pathp : word) (i : SyscallInput) (m : Model) :
    outcome SyscallEffect :=
  match read_cstr i.in_mem pathp with
  | CstrTooLong => ret_outcome (errno_ret ENAMETOOLONG) m
  | CstrFault => ret_outcome (errno_ret EFAULT) m
  | CstrOk p =>
      if path_eqb p [] then ret_outcome (errno_ret ENOENT) m
      else if !bv_eqb dirfd AT_FDCWD32 then Unmodeled
      else if path_eqb p dot_path then ret_outcome (Z_to_bv 64 0) m
      else if path_eqb p dotdot_path then ret_outcome (Z_to_bv 64 0) m
      else if path_has_slash p then Unmodeled
      else if NAME_MAX < p.length then Unmodeled
      else if fs_under (m_fs m) p then Unmodeled
      else
        match fs_lookup (m_fs m) p with
        | none => ret_outcome (errno_ret ENOENT) m
        | some _ => ret_outcome (Z_to_bv 64 0) m

/-- Both mode arms carry no copy-in, since `do_faccessat` decides the mode
(fs/open.c:475-476, Linux v6.18.46) before its call at :493 into
`user_path_at` (fs/namei.c:3211-3219, Linux v6.18.46), and every other
arm carries the one pathname range `faccessat_spec` records.
Rocq: `faccessat_witness`. -/
def faccessat_witness (dirfd pathp mode : word) (i : SyscallInput) (m : Model) :
    outcome SyscallEffect :=
  if !modeled_access_mode mode then ret_outcome (errno_ret EINVAL) m
  else if !access_mode_f_ok mode then Unmodeled
  else
    outcome_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
      (faccessat_body_witness dirfd pathp i m)

/-- `faccessat2`'s witness is `faccessat`'s under one more -EINVAL and one
more decline: `do_faccessat` (fs/open.c:467-537, Linux v6.18.46) is the
shared body, so past the flag word there is nothing new to build.  Rocq:
`faccessat2_witness`. -/
def faccessat2_witness (dirfd pathp mode flags : word) (i : SyscallInput) (m : Model) :
    outcome SyscallEffect :=
  if !modeled_access_mode mode then ret_outcome (errno_ret EINVAL) m
  else if !valid_access_flags flags then ret_outcome (errno_ret EINVAL) m
  else if !modeled_access_flags flags then Unmodeled
  else if !access_mode_f_ok mode then Unmodeled
  else
    outcome_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
      (faccessat_body_witness dirfd pathp i m)

/-- Rocq: `faccessat_body_witness_ok`. -/
theorem faccessat_body_witness_ok (dirfd pathp : word) (i : SyscallInput) (m : Model) :
    faccessat_body_spec dirfd pathp i m i m (faccessat_body_witness dirfd pathp i m) := by
  unfold faccessat_body_spec faccessat_body_witness
  generalize read_cstr i.in_mem pathp = r
  cases r with
  | CstrTooLong =>
    dsimp only
    exact pure_ok _ i m
  | CstrFault =>
    dsimp only
    exact pure_ok _ i m
  | CstrOk p =>
    dsimp only
    generalize path_eqb p [] = b
    cases b with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i m
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      generalize (!bv_eqb dirfd AT_FDCWD32) = b
      cases b with
      | true =>
        simp only [↓reduceIte]
        exact unmodeled_intro i m
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        generalize path_eqb p dot_path = b
        cases b with
        | true =>
          simp only [↓reduceIte]
          unfold access_exists_spec
          apply alt_r
          exact pure_ok _ i m
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          generalize path_eqb p dotdot_path = b
          cases b with
          | true =>
            simp only [↓reduceIte]
            unfold access_exists_spec
            apply alt_r
            exact pure_ok _ i m
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            generalize path_has_slash p = b
            cases b with
            | true =>
              simp only [↓reduceIte]
              exact unmodeled_intro i m
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              by_cases hn : NAME_MAX < p.length
              · simp only [hn, ↓reduceIte]
                exact unmodeled_intro i m
              · simp only [hn, ↓reduceIte]
                generalize fs_under (m_fs m) p = b
                cases b with
                | true =>
                  simp only [↓reduceIte]
                  exact unmodeled_intro i m
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  generalize fs_lookup (m_fs m) p = r
                  cases r with
                  | none =>
                    dsimp only
                    exact pure_ok _ i m
                  | some _ =>
                    dsimp only
                    unfold access_exists_spec
                    apply alt_r
                    exact pure_ok _ i m

/-- Rocq: `faccessat_witness_ok`. -/
theorem faccessat_witness_ok (dirfd pathp mode : word) (i : SyscallInput) (m : Model) :
    faccessat_spec dirfd pathp mode i m (faccessat_witness dirfd pathp mode i m) := by
  unfold faccessat_spec faccessat_witness
  apply bind_step _ _ i m i m _ (input_ok i m)
  apply bind_step _ _ i m m m _ (get_model_ok i m)
  generalize (!modeled_access_mode mode) = b
  cases b with
  | true =>
    simp only [↓reduceIte]
    exact pure_ok _ i m
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize (!access_mode_f_ok mode) = b
    cases b with
    | true =>
      simp only [↓reduceIte]
      exact unmodeled_intro i m
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact record_copyins_outcome _ _ i m _ (faccessat_body_witness_ok dirfd pathp i m)

/-- Rocq: `faccessat2_witness_ok`. -/
theorem faccessat2_witness_ok (dirfd pathp mode flags : word) (i : SyscallInput) (m : Model) :
    faccessat2_spec dirfd pathp mode flags i m (faccessat2_witness dirfd pathp mode flags i m) := by
  unfold faccessat2_spec faccessat2_witness
  apply bind_step _ _ i m i m _ (input_ok i m)
  apply bind_step _ _ i m m m _ (get_model_ok i m)
  generalize (!modeled_access_mode mode) = b
  cases b with
  | true =>
    simp only [↓reduceIte]
    exact pure_ok _ i m
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize (!valid_access_flags flags) = b
    cases b with
    | true =>
      simp only [↓reduceIte]
      exact pure_ok _ i m
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      generalize (!modeled_access_flags flags) = b
      cases b with
      | true =>
        simp only [↓reduceIte]
        exact unmodeled_intro i m
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        generalize (!access_mode_f_ok mode) = b
        cases b with
        | true =>
          simp only [↓reduceIte]
          exact unmodeled_intro i m
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact record_copyins_outcome _ _ i m _ (faccessat_body_witness_ok dirfd pathp i m)

/-! ### close — the witness

Mirrors the `close` half of
`theories/LinuxProcessSem/Checks/Witness/Fs/Open.v`.  Both arms of
`close_spec` are deterministic, so the witness is the spec's own answer on
each and draws nothing; `close_witness_ok` is what the registration
step's receptiveness field for 57 becomes. -/

/-- Rocq: `Checks.Witness.Fs.Open.close_witness`. -/
def close_witness (fd : word) (m : Model) : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | none   => ret_outcome (errno_ret EBADF) m
  | some _ => ret_outcome (Z_to_bv 64 0) (with_fds (fd_remove (m_fds m) fd) m)

/-- Rocq: `Checks.Witness.Fs.Open.close_witness_ok`. -/
theorem close_witness_ok (fd : word) (i : SyscallInput) (m : Model) :
    close_spec fd i m (close_witness fd m) := by
  unfold close_spec close_witness
  apply bind_step _ _ i m m m _ (get_model_ok i m)
  generalize fd_lookup (m_fds m) fd = r
  cases r with
  | none => exact pure_ok _ i _
  | some e => exact bind_step _ _ i m () _ _ (modify_ok _ i m) (pure_ok _ i _)

/-! ### ftruncate — the witness

Mirrors the `ftruncate` half of
`theories/LinuxProcessSem/Checks/Witness/Fs/Open.v` at the commit the
checker section names.  `ftruncate_spec` has no `alt` and no `errno_from`,
so the witness is the spec's own answer on each arm and draws nothing: an
errno over the model unchanged, `Unmodeled` where the spec declines, and on
a writable file — `FdFileA` as much as `FdFileW` and `FdFileRW` — the 0
over the resized image.  `ftruncate_witness_ok` is what the registration
step's receptiveness field for 46 becomes. -/

/-- Rocq: `Checks.Witness.Fs.Open.ftruncate_witness`. -/
def ftruncate_witness (fd len : word) (m : Model) : outcome SyscallEffect :=
  if bv_signed len < 0 then ret_outcome (errno_ret EINVAL) m
  else
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some (.FdChannel _) => ret_outcome (errno_ret EINVAL) m
  | some (.FdSocket _) => ret_outcome (errno_ret EINVAL) m
  | some (.FdPipe _ _) => ret_outcome (errno_ret EINVAL) m
  | some (.FdDevNull _ _) => ret_outcome (errno_ret EINVAL) m
  | some .FdUrandom => ret_outcome (errno_ret EINVAL) m
  | some (.FdFile _ _) => ret_outcome (errno_ret EINVAL) m
  | some .FdDir => ret_outcome (errno_ret EINVAL) m
  | some (.FdFileA p _) =>
      match fs_lookup (m_fs m) p with
      | none => Unmodeled
      | some data =>
          if (!modeled_truncate_gap data len) then Unmodeled
          else ret_outcome (Z_to_bv 64 0) (with_fs (fs_set (m_fs m) p (file_truncate data len)) m)
  | some (.FdFileW p _) | some (.FdFileRW p _) =>
      match fs_lookup (m_fs m) p with
      | none => Unmodeled
      | some data =>
          if (!modeled_truncate_gap data len) then Unmodeled
          else ret_outcome (Z_to_bv 64 0) (with_fs (fs_set (m_fs m) p (file_truncate data len)) m)

/-- Rocq: `Checks.Witness.Fs.Open.ftruncate_witness_ok`; the proof keeps
its shape — the length gate, one `bind_step` over the `get_model`, then the
kind, the image lookup and the gap guard, with `pure_ok`, `unmodeled_intro`
or the `set_fs` step on each leaf. -/
theorem ftruncate_witness_ok (fd len : word) (i : SyscallInput) (m : Model) :
    ftruncate_spec fd len i m (ftruncate_witness fd len m) := by
  unfold ftruncate_spec ftruncate_witness
  by_cases hneg : bv_signed len < 0
  · rw [ite_eq_left hneg, ite_eq_left hneg]
    exact pure_ok _ i _
  rw [ite_eq_right hneg, ite_eq_right hneg]
  apply bind_step _ _ i m m m _ (get_model_ok i m)
  generalize fd_lookup (m_fds m) fd = r
  cases r with
  | none => exact pure_ok _ i _
  | some e =>
    cases e
    case FdFileA p _ | FdFileW p _ | FdFileRW p _ =>
      dsimp only
      generalize fs_lookup (m_fs m) p = r
      cases r with
      | none => exact unmodeled_intro i m
      | some data =>
        dsimp only
        by_cases hg : (!modeled_truncate_gap data len) = true
        · rw [ite_eq_left hg, ite_eq_left hg]
          exact unmodeled_intro i m
        · rw [ite_eq_right hg, ite_eq_right hg]
          exact bind_step _ _ i m () _ _ (modify_ok _ i m) (pure_ok _ i _)
    all_goals exact pure_ok _ i _

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open
