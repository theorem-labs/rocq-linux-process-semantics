import LinuxProcessSemantics.LinuxProcessSem.Checks.InvariantRegistry
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Pipe
import LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
import LinuxProcessSemantics.LinuxProcessSem.SysSimp

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Arms.Fs.Pipe — pipe2 on the checked surface

The registration of `Checks/Sys/Fs/Pipe.lean`'s checker in
`checked_table`, in the one file that registration writes; the shape is
`Checks/Arms/Fs/EventFd.lean`'s, whose header says what
`tools/gen_lean_checked.py` renders from the three sections below and
why each stands in the namespace it does.

The baseline above is the one `Checks/Sys/Dispatch.lean` explains: the
arm is the row `arm_pipe2` of
`theories/LinuxProcessSem/Checks/Sys/Dispatch.v`'s `checked_table`, read
at that commit; the row is text for text the same at the conformance
ticket's `f44244ad6b80`.

WHY THE DESCRIPTOR-STATE FACTS ARE NOT FRAMES.  On the pair arm `pipe2`
installs two descriptors and registers a pipe (the accepted pair's
post-model is `one_pipe_model`, not the model handed in:
`pipe2_unwrapped_fildes_still_installs_the_pair_over_the_real_table`).
So its two descriptor-state facts below are not frames, as eventfd2's
are; each is an argument over the two models the checker can accept, the
one handed in or `pipe2_model` (`check_pipe2_ok_models`), and the helper
lemmas it is built from stand in the `Checks.Invariants` section, beside
the facts that read them.  Two of those helpers, `fd_insert_keys_nodup`
and `pipe_insert_within_capacity`, state over the same setters what
`Checks/Arms/Fs/ReadWrite.lean`'s `fd_table_unique_fd_insert` and
`pipes_within_capacity_pipe_insert` state.  They are restated rather than
imported so that this registration does not depend on write's; merging
each pair into one lemma in a module both arm files import changes no
statement.  The ledger fact is still a frame: `check_pipe2_frame` states
it beside the checker. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch

/- ### pipe2 (59) -/

/-- pipe2 (59).  `fildes` IS REGISTER `a0`, WHOLE, AND THE FLAG WORD IS
REGISTER `a1`, CUT TO ITS LOW 32 BITS.  riscv64's `__riscv_sys_pipe2`
hands the registers over in order, `orig_a0` then `a1`
(`SC_RISCV_REGS_TO_ARGS`, arch/riscv/include/asm/syscall_wrapper.h:21-24,
Linux v6.18.46), and the wrapper narrows each to the type
`SYSCALL_DEFINE2(pipe2, int __user *, fildes, int, flags)` declares
(fs/pipe.c:1054, same version) through `__SC_CAST`
(include/linux/syscalls.h:132, applied at
arch/riscv/include/asm/syscall_wrapper.h:88, Linux v6.18.46): a pointer
keeps all 64 bits and the `int` keeps 32, which `__do_pipe_flags` then
gates (fs/pipe.c:987-988, Linux v6.18.46).  `Sys.Syscall.pipe_flags32
(in_arg i 1)` is that narrowing, applied here at the boundary as Rocq's
`arm_pipe2` applies it, so the checker and the witness receive the
narrowed word and gate it whole.  Gating the unnarrowed register would
be a wrong answer, not a decline: `pipe2(fds, 1 << 32)` would take the
-EINVAL where Linux sees flags 0 and hands back a pair.  `ca_arm` is the
term `Sys/Registry/Fs/Pipe.lean`'s row builds, which
`checked_table_arms` checks.  The ledger fact this arm owes
`checked_table_preserves_vm` is `check_pipe2_frame`, beside the
checker. -/
def arm_pipe2 : CheckedArm where
  ca_arm := SpecArm.mkSpecArm 59
    (fun i => Sys.Fs.Pipe.pipe2_spec (in_arg i 0) (Sys.Syscall.pipe_flags32 (in_arg i 1)) i)
  ca_check := fun i eff m =>
    Checks.Sys.Fs.Pipe.check_pipe2 i (in_arg i 0) (Sys.Syscall.pipe_flags32 (in_arg i 1)) eff m
  ca_witness := fun i m =>
    Checks.Sys.Fs.Pipe.pipe2_witness (in_arg i 0) (Sys.Syscall.pipe_flags32 (in_arg i 1)) i m
  ca_sound_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Pipe.check_pipe2_sound_ok i (in_arg i 0)
      (Sys.Syscall.pipe_flags32 (in_arg i 1)) eff m m' evs h
  ca_sound_unmodeled := fun i eff m h =>
    Checks.Sys.Fs.Pipe.check_pipe2_sound_unmodeled i (in_arg i 0)
      (Sys.Syscall.pipe_flags32 (in_arg i 1)) eff m h
  ca_complete_ok := fun i eff m m' evs h =>
    Checks.Sys.Fs.Pipe.check_pipe2_complete_ok i (in_arg i 0)
      (Sys.Syscall.pipe_flags32 (in_arg i 1)) eff m m' evs h
  ca_complete_unmodeled := fun i m eff h =>
    Checks.Sys.Fs.Pipe.check_pipe2_complete_unmodeled i (in_arg i 0)
      (Sys.Syscall.pipe_flags32 (in_arg i 1)) m eff h
  ca_receptive := fun i m =>
    Checks.Sys.Fs.Pipe.pipe2_witness_ok (in_arg i 0) (Sys.Syscall.pipe_flags32 (in_arg i 1)) i m

@[arm_unfold] theorem ca_check_arm_pipe2 (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : arm_pipe2.ca_check i eff m
      = Checks.Sys.Fs.Pipe.check_pipe2 i (in_arg i 0) (Sys.Syscall.pipe_flags32 (in_arg i 1))
          eff m := rfl
@[arm_unfold] theorem ca_witness_arm_pipe2 (i : SyscallInput) (m : Model) :
    arm_pipe2.ca_witness i m
      = Checks.Sys.Fs.Pipe.pipe2_witness (in_arg i 0) (Sys.Syscall.pipe_flags32 (in_arg i 1))
          i m := rfl
@[arm_unfold] theorem sa_spec_arm_pipe2 (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : arm_pipe2.ca_arm.sa_spec i m o
      = Sys.Fs.Pipe.pipe2_spec (in_arg i 0) (Sys.Syscall.pipe_flags32 (in_arg i 1)) i m o := rfl
@[arm_unfold] theorem ca_no_arm_pipe2 : ca_no arm_pipe2 = 59 := rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-- `pipe2` (59): no answer the checker accepts maps or unmaps memory —
the pipe's ring is a kernel allocation
(`alloc_pipe_info`, fs/pipe.c:792-839, Linux v6.18.46), never a user
mapping — so the ledger is what it was (`check_pipe2_frame`, stated
beside the checker in `Checks/Sys/Fs/Pipe.lean`). -/
theorem arm_pipe2_preserves_vm : arm_preserves_vm arm_pipe2 :=
  arm_preserves_of_frame arm_pipe2 (fun i eff m m' evs h => by
    simp only [arm_unfold] at h
    exact Checks.Sys.Fs.Pipe.check_pipe2_frame i _ _ eff m m' evs h)

end LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.Arms

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Dispatch
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Table
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Pipe
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Pipe

/-! ### What an accepted pipe2 can leave

The checker accepts two kinds of answer: an errno, over the model handed
in, and the pair, over `pipe2_model m (pipe_new_id (m_pipes m))`.  The
walk is `check_pipe2_frame`'s, one `cases` or `generalize` per test in
the checker's order, with the fresh id's equation kept so that the pair
arm's post-model can be named. -/

/-- An accepted `pipe2` leaves the model it was handed, or the model with
the pair installed under the fresh id — nothing else. -/
theorem check_pipe2_ok_models (i : SyscallInput) (fildes flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_pipe2 i fildes flags eff m = CheckOk m' evs) :
    m' = m ∨ m' = pipe2_model m (pipe_new_id (m_pipes m)) := by
  unfold check_pipe2 at h
  dsimp only at h
  cases hmask : (bv_unsigned (bv_and flags (bv_not (Z_to_bv 64 pipe2_flags_mask))) == 0)
  · simp only [hmask, Bool.not_false, ↓reduceIte] at h
    obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact Or.inl rfl
  · simp only [hmask, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    cases hz : w_is0 flags
    · simp only [hz, Bool.not_false, ↓reduceIte] at h
      cases h
    · simp only [hz, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      generalize hpid : pipe_new_id (m_pipes m) = pid at h
      rcases hl : pipe_lookup (m_pipes m) pid with _ | st
      · simp only [hl] at h
        cases hacc : access_okb fildes 8
        · simp only [hacc, Bool.not_false, ↓reduceIte] at h
          split at h
          next => split at h <;> cases h <;> exact Or.inl rfl
          next => cases h
        · simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          rcases hr8 : read_bytes_map i.in_wmem fildes (Z_to_bv 64 8) with _ | w8
          · simp only [hr8] at h
            rcases hr1 : read_bytes_map i.in_wmem fildes (Z_to_bv 64 1) with _ | w1
            · simp only [hr1] at h
              split at h
              next => split at h <;> cases h <;> exact Or.inl rfl
              next => cases h
            · simp only [hr1] at h
              cases h
          · simp only [hr8] at h
            split at h
            next => split at h <;> cases h <;> exact Or.inl rfl
            next =>
              split at h
              next => cases h
              next =>
                split at h
                next => cases h
                next =>
                  split at h
                  next =>
                    cases h
                    exact Or.inr (hpid ▸ rfl)
                  next => cases h
            next => cases h
      · simp only [hl] at h
        cases h

/-- `fd_insert` keeps the table's descriptors distinct, whatever the
table held at `fd`: it drops every binding of `fd` before it prepends
the new one.  That is the model's spelling of `fd_install` storing into
the one slot `fdt->fd[fd]` (fs/file.c:652-677, Linux v6.18.46, commit
1f99e9ab748f); a table indexed by descriptor cannot bind one twice. -/
theorem fd_insert_keys_nodup (fds : List (word × FdEntry)) (fd : word) (e : FdEntry)
    (h : fd_table_unique fds) : fd_table_unique (fd_insert fds fd e) := by
  unfold fd_table_unique fd_insert at *
  rw [List.map_cons, List.nodup_cons]
  refine ⟨?_, h.sublist (List.filter_sublist.map Prod.fst)⟩
  intro hmem
  obtain ⟨p, hp, hpk⟩ := List.mem_map.mp hmem
  have hkeep := (List.mem_filter.mp hp).2
  rw [hpk, bv_eqb_refl] at hkeep
  exact absurd hkeep (by decide)

/-- `pipe_insert` of a buffer inside its page keeps every pipe inside
its page: the new binding is the one given, and every other binding is
one the table already held.  The model's registry has no kernel step to
mirror: Linux keeps no table of pipes.  A new `pipe_inode_info` comes
from `alloc_pipe_info` (fs/pipe.c:792-839, Linux v6.18.46, commit
1f99e9ab748f), and `get_pipe_inode` (fs/pipe.c:896-900, Linux v6.18.46)
stores it in the new inode's `i_pipe`.  `create_pipe_files`
(fs/pipe.c:953 and :963, Linux v6.18.46) stores it in the `private_data`
of the two files made over that inode, and under `O_NOTIFICATION_PIPE`, a
flag the model declines, `watch_queue_init`
(kernel/watch_queue.c:699, Linux v6.18.46) stores it in the `watch_queue`
it allocates.  None of those steps reads or writes another
`pipe_inode_info`, so no other pipe is touched. -/
theorem pipe_insert_within_capacity (ps : List (word × PipeBuf)) (id : word) (st : PipeBuf)
    (h : pipes_within_capacity ps) (hst : pipe_within_capacity st) :
    pipes_within_capacity (pipe_insert ps id st) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact hst
  · exact h p (List.mem_filter.mp hp).1

/-- The buffer a fresh pipe starts with is inside its page: empty, with
its merge mark at 0.  Linux: `alloc_pipe_info` zeroes the
`pipe_inode_info` (`kzalloc`, fs/pipe.c:800) and its slot array
(`kcalloc`, :817), so `head == tail` and no slot holds a byte
(fs/pipe.c, Linux v6.18.46, commit 1f99e9ab748f). -/
theorem fresh_pipe_within_capacity : pipe_within_capacity (([], 0) : PipeBuf) := by
  show (([] : List byte).length : Int) ≤ 0 ∧ (0 : Int) ≤ PIPE_BUF
  decide

/-- `vm_wf` × `pipe2`: the ledger fact above. -/
theorem vm_wf_arm_pipe2 : arm_preserves inv_vm_wf arm_pipe2 :=
  Arms.arm_pipe2_preserves_vm

/-- `fd_table_unique` × `pipe2`: an accepted answer leaves one of two
models (`check_pipe2_ok_models`, which does not say which answer leaves
which), and the proof needs no more than that.  The model handed in keeps
the table.  The pair is two `fd_insert`s, one per `fd_install` at
fs/pipe.c:1047-1048 (`do_pipe2`, Linux v6.18.46), each of which keeps the
descriptors distinct.  Linux agrees with the checker on the errno answers:
each is returned before `fd_install` runs (`__do_pipe_flags`,
fs/pipe.c:987-1015, and the -EFAULT of `do_pipe2`, :1040-1045, which gives
both reserved descriptors back), so an errno answer installs nothing. -/
theorem fd_table_unique_arm_pipe2 : arm_preserves inv_fd_table_unique arm_pipe2 := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  rcases check_pipe2_ok_models i _ _ eff m m' evs h with rfl | rfl
  · exact hold
  · exact fd_insert_keys_nodup _ _ _ (fd_insert_keys_nodup (m_fds m) _ _ hold)

/-- `pipes_within_capacity` × `pipe2`: an errno answer registers no pipe,
and the pair registers one, empty (`get_pipe_inode`, fs/pipe.c:886-924,
through `alloc_pipe_info`, Linux v6.18.46), which
`fresh_pipe_within_capacity` puts inside its page. -/
theorem pipes_within_capacity_arm_pipe2 :
    arm_preserves inv_pipes_within_capacity arm_pipe2 := by
  intro i eff m m' evs h hold
  simp only [arm_unfold] at h
  rcases check_pipe2_ok_models i _ _ eff m m' evs h with rfl | rfl
  · exact hold
  · exact pipe_insert_within_capacity (m_pipes m) _ _ hold fresh_pipe_within_capacity

end LinuxProcessSemantics.LinuxProcessSem.Checks.Invariants
