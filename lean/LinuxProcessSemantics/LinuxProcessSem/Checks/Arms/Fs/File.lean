import LinuxProcessSemantics.LinuxProcessSem.Checks.Arms.Fs.ReadWrite
import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.File
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: f44244ad6b8041aa83053d9ca91e090037ed743b -/

/-! # LinuxProcessSem.Checks.Arms.Fs.File — dup and dup3 on the checked surface

The registration of `Checks/Sys/Fs/File.lean`'s two checkers in
`checked_table`, in the one file that registration writes.
`tools/gen_lean_checked.py` renders `checked_table`,
`checked_table_preserves_vm` and `registry_preserves` from the files
under `Checks/Arms/`, one per checker twin, so that registering an arm
creates or edits no hub but this file; its docstring is the shape it reads
and what it refuses. The file holds three sections, each in the
namespace its declarations had when those three hubs were written by
hand, so that no name moved with the file:

- `Checks.Sys.Table`: the `CheckedArm`s (`arm_dup` and `arm_dup3`) and
  their four `arm_unfold` lemmas each;
- `Checks.VmMapsDisjoint.Arms`: each arm's ledger fact,
  `arm_<name>_preserves_vm`, which `checked_table_preserves_vm`'s
  alternation names, and the frame lemmas it is built from;
- `Checks.Invariants`: one `<invariant>_arm_<name>` per entry of
  `Checks/InvariantRegistry.lean`'s `invariant_registry`, which
  `registry_preserves`'s alternation names.

The baseline above is the commit the two rows were read at:
`theories/LinuxProcessSem/Checks/Sys/Dispatch.v`'s `arm_dup` and
`arm_dup3`, with their `ca_check_arm_*`, `ca_witness_arm_*`,
`sa_spec_arm_*` and `ca_no_arm_*` lemmas, and
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`'s `check_dup_frame`
and `check_dup3_frame`, which the ledger facts below are built from.
All of them read the same at a71fd38a, the baseline the sibling arm
files carry.

These two install a descriptor on an accepted answer, so the
`fd_table_unique` facts below are not a view frame: `dup` installs at
the descriptor `alloc_fd` chose and `dup3` at the caller's `newfd`, and
what carries the invariant across is that the model installs through
`State.fd_insert`, which drops every binding of the descriptor before it
conses the new one — the model's spelling of `do_dup2` overwriting the
one array slot `fdt->fd[fd]` (fs/file.c:1304, Linux v6.18.46, commit
1f99e9ab748f) and of `fd_install` storing into a slot it asserts empty
(fs/file.c:674-675, same version). That step is
`fd_table_unique_fd_insert`, which `Checks/Arms/Fs/ReadWrite.lean`
states for `write`'s rebinding and this file imports. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/- ### dup (23) -/

/-- dup (23).  THE DESCRIPTOR IS REGISTER `a0`, CUT TO ITS LOW 32 BITS.
riscv64's `__riscv_sys_dup` hands `orig_a0` over first
(`SC_RISCV_REGS_TO_ARGS`, arch/riscv/include/asm/syscall_wrapper.h:21-24,
Linux v6.18.46), and the wrapper narrows it to the type
`SYSCALL_DEFINE1(dup, unsigned int, fildes)` (fs/file.c:1457, same
version) declares through `__SC_CAST` (include/linux/syscalls.h:132,
applied at arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46),
so `fget_raw` looks up the low 32 bits: `dup(2^32 + 2)` duplicates
descriptor 2.  `Sys.Syscall.fd32 (in_arg i 0)` is that reading, applied
here at the boundary as Rocq's `arm_dup` applies it, so the checker and
the witness receive the narrowed descriptor, as the spec does.  `ca_arm`
is the term `Sys/Registry/Fs/File.lean`'s row builds, which
`checked_table_arms` checks.  The ledger fact this arm owes
`checked_table_preserves_vm` is `check_dup_frame`, stated below in this file. -/
def arm_dup : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 23 (fun i => Sys.Fs.File.dup_spec (Sys.Syscall.fd32 (in_arg i 0)) i)
  ca_check := fun i eff m =>
    Checks.Sys.Fs.File.check_dup (Sys.Syscall.fd32 (in_arg i 0)) eff m
  ca_witness := fun i m =>
    Checks.Sys.Fs.File.dup_witness (Sys.Syscall.fd32 (in_arg i 0)) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.File.check_dup_sound_ok (Sys.Syscall.fd32 (in_arg i 0)) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.File.check_dup_sound_unmodeled (Sys.Syscall.fd32 (in_arg i 0)) eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.File.check_dup_complete_ok (Sys.Syscall.fd32 (in_arg i 0)) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.File.check_dup_complete_unmodeled (Sys.Syscall.fd32 (in_arg i 0)) m i eff h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.File.dup_witness_ok (Sys.Syscall.fd32 (in_arg i 0)) i m

@[arm_unfold] theorem ca_check_arm_dup (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_dup.ca_check i eff m
      = Checks.Sys.Fs.File.check_dup (Sys.Syscall.fd32 (in_arg i 0)) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_dup (i : SyscallInput) (m : Model) :
    arm_dup.ca_witness i m = Checks.Sys.Fs.File.dup_witness (Sys.Syscall.fd32 (in_arg i 0)) m := rfl
@[arm_unfold] theorem sa_spec_arm_dup (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_dup.ca_arm.sa_spec i m o = Sys.Fs.File.dup_spec (Sys.Syscall.fd32 (in_arg i 0)) i m o := rfl
@[arm_unfold] theorem ca_no_arm_dup : ca_no arm_dup = 23 := rfl

/- ### dup3 (24) -/

/-- dup3 (24).  `oldfd` IS `a0` AND `newfd` IS `a1`, EACH CUT TO ITS LOW
32 BITS; THE FLAG WORD IS `a2`, READ WHOLE HERE.
`SYSCALL_DEFINE3(dup3, unsigned int, oldfd, unsigned int, newfd, int,
flags)` (fs/file.c:1433, Linux v6.18.46) takes the three registers in
order (`SC_RISCV_REGS_TO_ARGS`, arch/riscv/include/asm/syscall_wrapper.h:21-24,
same version) and narrows each to its declared type through `__SC_CAST`
(include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46).  The two
descriptors are narrowed here by `Sys.Syscall.fd32`, as Rocq's `arm_dup3`
narrows them, so `ksys_dup3`'s `oldfd == newfd` test (fs/file.c:1408,
same version) compares the narrowed words and `dup3(2^32 + 1, 1, 0)` is
-EINVAL.  The flag word is handed over whole because its `int` cut is
inside the spec: `Sys.Fs.File.dup3_flags_ok` applies `flag32` itself
before it tests `flags & ~O_CLOEXEC` (fs/file.c:1405, Linux v6.18.46), and
nothing else of the arm reads `a2`.  `ca_arm` is the term
`Sys/Registry/Fs/File.lean`'s row builds, which `checked_table_arms`
checks.  The ledger fact this arm owes `checked_table_preserves_vm` is
`check_dup3_frame`, stated below in this file. -/
def arm_dup3 : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 24 (fun i => Sys.Fs.File.dup3_spec (Sys.Syscall.fd32 (in_arg i 0))
    (Sys.Syscall.fd32 (in_arg i 1)) (in_arg i 2) i)
  ca_check := fun i eff m =>
    Checks.Sys.Fs.File.check_dup3 (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.fd32 (in_arg i 1))
      (in_arg i 2) eff m
  ca_witness := fun i m =>
    Checks.Sys.Fs.File.dup3_witness (Sys.Syscall.fd32 (in_arg i 0))
      (Sys.Syscall.fd32 (in_arg i 1)) (in_arg i 2) m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.File.check_dup3_sound_ok (Sys.Syscall.fd32 (in_arg i 0))
      (Sys.Syscall.fd32 (in_arg i 1)) (in_arg i 2) eff m m' evs i h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.File.check_dup3_sound_unmodeled (Sys.Syscall.fd32 (in_arg i 0))
      (Sys.Syscall.fd32 (in_arg i 1)) (in_arg i 2) eff m i h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.File.check_dup3_complete_ok (Sys.Syscall.fd32 (in_arg i 0))
      (Sys.Syscall.fd32 (in_arg i 1)) (in_arg i 2) eff m m' evs i h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.File.check_dup3_complete_unmodeled (Sys.Syscall.fd32 (in_arg i 0))
      (Sys.Syscall.fd32 (in_arg i 1)) (in_arg i 2) m i eff h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.File.dup3_witness_ok (Sys.Syscall.fd32 (in_arg i 0))
      (Sys.Syscall.fd32 (in_arg i 1)) (in_arg i 2) i m

@[arm_unfold] theorem ca_check_arm_dup3 (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    arm_dup3.ca_check i eff m
      = Checks.Sys.Fs.File.check_dup3 (Sys.Syscall.fd32 (in_arg i 0))
          (Sys.Syscall.fd32 (in_arg i 1)) (in_arg i 2) eff m := rfl
@[arm_unfold] theorem ca_witness_arm_dup3 (i : SyscallInput) (m : Model) :
    arm_dup3.ca_witness i m
      = Checks.Sys.Fs.File.dup3_witness (Sys.Syscall.fd32 (in_arg i 0))
          (Sys.Syscall.fd32 (in_arg i 1)) (in_arg i 2) m := rfl
@[arm_unfold] theorem sa_spec_arm_dup3 (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    arm_dup3.ca_arm.sa_spec i m o
      = Sys.Fs.File.dup3_spec (Sys.Syscall.fd32 (in_arg i 0)) (Sys.Syscall.fd32 (in_arg i 1))
          (in_arg i 2) i m o := rfl
@[arm_unfold] theorem ca_no_arm_dup3 : ca_no arm_dup3 = 24 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.File
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.File

/-! ## What an accepted verdict leaves behind — the registration's frame lemmas

The frame lemmas the facts below are built from, stated in the arm file as
`Checks/Arms/Fs/Timerfd.lean` states its own: the checker twin
`Checks/Sys/Fs/File.lean` is not the registration's to edit.  Every model
either checker accepts is one of two: the model it was handed (each `check_ret_only`
leaf, and `check_dup_result`'s errno half), or that model with ONE entry
installed through `State.fd_insert` and nothing else moved (`with_fds`).
`check_dup_ok_post` and `check_dup3_ok_post` state that dichotomy once,
and every frame below reads it off: `with_fds` rebuilds the descriptor
table alone, so the memory ledger and the pipe buffers are the
pre-model's on either branch, and what the table becomes is
`fd_insert`'s answer, which `fd_table_unique_fd_insert` holds to the
registry's descriptor-uniqueness invariant.

That the installed entry is the one Linux installs, at the descriptor
Linux installs it at, is the checkers' soundness against their specs
(`Checks/Sys/Fs/File.lean`) and not these lemmas' claim: `dup` binds the
`struct file` `fget_raw` returned at the descriptor `get_unused_fd_flags`
reserved (`fd_install`,
fs/file.c:1465, Linux v6.18.46, commit 1f99e9ab748f), and `dup3` at the
caller's `newfd` through `do_dup2`, which overwrites that one array slot
(fs/file.c:1304, same version).  What these lemmas add is that nothing
else moves, the fact the registry's invariants consume.  This stops
being true the day a leaf answers with a model built by anything but
`with_fds`, and `check_dup_ok_post` or `check_dup3_ok_post` is then what
fails to build. -/

/-- Every model `check_dup` accepts is the one it was handed, or that one
with one entry installed at one descriptor.  Lean-only: Rocq's frame
proof (`VmMapsDisjoint.check_dup_frame`) runs `vm_frame2` over the
unfolded checker rather than naming the shape, and the Rocq tree
registers no invariant over the descriptor table that would need it. -/
theorem check_dup_ok_post (oldfd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_dup oldfd eff m = CheckOk m' evs) :
    m' = m ∨ ∃ fd e, m' = with_fds (fd_insert (m_fds m) fd e) m := by
  unfold check_dup at h
  cases hfd : fd_lookup (m_fds m) oldfd with
  | none =>
    simp only [hfd] at h
    exact Or.inl ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2.1
  | some e =>
    simp only [hfd] at h
    cases hk : dup_modeled_entry e with
    | false => simp only [hk, Bool.not_false, ↓reduceIte, reduceCtorEq] at h
    | true =>
      simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨-, ret, -, hcase⟩ := check_dup_result_ok_inv eff m _ m' evs h
      rcases hcase with ⟨-, hm⟩ | ⟨-, -, hm⟩
      · exact Or.inl hm
      · exact Or.inr ⟨ret, e, hm⟩

/-- Every model `check_dup3` accepts is the one it was handed, or that
one with one entry installed at `newfd` itself — the descriptor
`do_dup2` writes (fs/file.c:1304, Linux v6.18.46), whether or not it was
free.  Lean-only, for `check_dup_ok_post`'s reason. -/
theorem check_dup3_ok_post (oldfd newfd flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_dup3 oldfd newfd flags eff m = CheckOk m' evs) :
    m' = m ∨ ∃ e, m' = with_fds (fd_insert (m_fds m) newfd e) m := by
  unfold check_dup3 at h
  cases hf : dup3_flags_ok flags with
  | false =>
    simp only [hf, Bool.not_false, ↓reduceIte] at h
    exact Or.inl ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2.1
  | true =>
  simp only [hf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hne : bv_eqb oldfd newfd with
  | true =>
    simp only [hne, ↓reduceIte] at h
    exact Or.inl ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2.1
  | false =>
  simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
  cases hl : dup3_newfd_under_limit newfd m with
  | false =>
    simp only [hl, Bool.not_false, ↓reduceIte] at h
    exact Or.inl ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2.1
  | true =>
  simp only [hl, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hfd : fd_lookup (m_fds m) oldfd with
  | none =>
    simp only [hfd] at h
    exact Or.inl ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2.1
  | some e =>
  simp only [hfd] at h
  cases hk : dup_modeled_entry e with
  | false => simp only [hk, Bool.not_false, ↓reduceIte, reduceCtorEq] at h
  | true =>
  simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  refine Or.inr ⟨e, ?_⟩
  cases hnf : fd_lookup (m_fds m) newfd with
  | some e2 =>
    simp only [hnf] at h
    exact ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2.1
  | none =>
    simp only [hnf] at h
    by_cases hb : bv_unsigned newfd < NR_OPEN_DEFAULT
    · simp only [hb, ↓reduceIte] at h
      exact ((check_ret_only_ok_iff _ _ _ _ _ _).mp h).2.1
    · simp only [hb, ↓reduceIte, reduceCtorEq] at h

/-- Rocq: `VmMapsDisjoint.check_dup_frame`, stated there beside the
alternation that consumes it; `Checks/VmMapsDisjoint.lean` is frozen, so
the Lean twin is here, as `check_timerfd_create_frame` is.
Neither branch of `check_dup_ok_post` touches `m_vm`: `dup` maps and
unmaps nothing (fs/file.c:1457-1470, Linux v6.18.46). -/
theorem check_dup_frame (oldfd : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_dup oldfd eff m = CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  rcases check_dup_ok_post oldfd eff m m' evs h with rfl | ⟨fd, e, rfl⟩ <;> rfl

/-- Rocq: `VmMapsDisjoint.check_dup3_frame`; `check_dup_frame`'s
placement and argument, over `ksys_dup3` (fs/file.c:1399-1431, Linux
v6.18.46), which maps and unmaps nothing either. -/
theorem check_dup3_frame (oldfd newfd flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_dup3 oldfd newfd flags eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  rcases check_dup3_ok_post oldfd newfd flags eff m m' evs h with rfl | ⟨e, rfl⟩ <;> rfl

/-- `dup` (23): the accepted model is the one handed in or that one with
one descriptor bound, and neither touches the memory ledger
(`check_dup_frame`, above). -/
theorem arm_dup_preserves_vm : arm_preserves_vm arm_dup :=
  arm_preserves_of_frame arm_dup (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_dup_frame _ eff m m' evs h)

/-- `dup3` (24): likewise (`check_dup3_frame`). -/
theorem arm_dup3_preserves_vm : arm_preserves_vm arm_dup3 :=
  arm_preserves_of_frame arm_dup3 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_dup3_frame _ _ _ eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- `vm_wf` × `dup`: the ledger fact above. -/
theorem vm_wf_arm_dup : arm_preserves inv_vm_wf arm_dup :=
  Arms.arm_dup_preserves_vm

/-- `vm_wf` × `dup3`: the ledger fact above. -/
theorem vm_wf_arm_dup3 : arm_preserves inv_vm_wf arm_dup3 :=
  Arms.arm_dup3_preserves_vm

/-- `fd_table_unique` × `dup`: the table is the one handed in, or that
one with the copy installed through `fd_insert` at the descriptor the
kernel reported (`check_dup_ok_post`), which keeps every descriptor bound
once (`fd_table_unique_fd_insert`). -/
theorem fd_table_unique_arm_dup : arm_preserves inv_fd_table_unique arm_dup := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  rcases Arms.check_dup_ok_post _ eff m m' evs h with rfl | ⟨fd, e, rfl⟩
  · exact hold
  · exact fd_table_unique_fd_insert (m_fds m) fd e hold

/-- `fd_table_unique` × `dup3`: likewise, the install at `newfd`
replacing whatever `newfd` held (`check_dup3_ok_post`). -/
theorem fd_table_unique_arm_dup3 : arm_preserves inv_fd_table_unique arm_dup3 := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  rcases Arms.check_dup3_ok_post _ _ _ eff m m' evs h with rfl | ⟨e, rfl⟩
  · exact hold
  · exact fd_table_unique_fd_insert (m_fds m) _ e hold

/-- `check_dup` leaves every pipe buffer as it found it: neither branch
of `check_dup_ok_post` writes one, and `with_fds` carries `m_pipes` over.
Lean-only, for `Checks/InvariantRegistry.lean`'s `pipes_within_capacity`,
which the Rocq tree does not register. -/
theorem check_dup_pipes_frame (oldfd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : Checks.Sys.Fs.File.check_dup oldfd eff m = CheckOk m' evs) :
    m_pipes m' = m_pipes m := by
  rcases Arms.check_dup_ok_post oldfd eff m m' evs h with rfl | ⟨fd, e, rfl⟩ <;> rfl

/-- `check_dup3` likewise leaves every pipe buffer as it found it.
Lean-only. -/
theorem check_dup3_pipes_frame (oldfd newfd flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (h : Checks.Sys.Fs.File.check_dup3 oldfd newfd flags eff m = CheckOk m' evs) :
    m_pipes m' = m_pipes m := by
  rcases Arms.check_dup3_ok_post oldfd newfd flags eff m m' evs h with rfl | ⟨e, rfl⟩ <;> rfl

/-- `pipes_within_capacity` × `dup`: no pipe buffer is written
(`check_dup_pipes_frame`). -/
theorem pipes_within_capacity_arm_dup : arm_preserves inv_pipes_within_capacity arm_dup :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_dup (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_dup_pipes_frame _ eff m m' evs h)

/-- `pipes_within_capacity` × `dup3`: likewise (`check_dup3_pipes_frame`). -/
theorem pipes_within_capacity_arm_dup3 : arm_preserves inv_pipes_within_capacity arm_dup3 :=
  arm_preserves_of_view_frame inv_pipes_within_capacity arm_dup3 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact check_dup3_pipes_frame _ _ _ eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
