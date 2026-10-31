import LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Kernel.Fork — the set_tid_address (96), clone (220) and clone3 (435) checkers and witnesses

Mirrors `theories/LinuxProcessSem/Checks/Sys/Kernel/Fork.v` (the checkers,
and the four obligation proofs of each one that faces a spec — the return
acceptor `check_clone_answer` faces none) together with the whole of
`theories/LinuxProcessSem/Checks/Witness/Kernel/Fork.v` (the witnesses and
their receptivity proofs), and the arms' frame lemmas from
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`.  Rocq keeps the
witness in its own file because each of its files holds every arm's share
of one obligation; the Lean tree keeps no `Checks/Witness/` mirror files,
so a witness lives beside its checker.  What Rocq states about this arm in
`Checks/Sys/Dispatch.v` — its `CheckedArm` and `arm_unfold` lemmas — is
the arm's REGISTRATION, which edits `Checks/Sys/Table.lean` and appends to
`Checks/VmMapsDisjoint/Arms.lean` the arm-level preserves fact that file
derives from the frame lemma below through `arm_preserves_of_frame`; that
is the conformance tickets' step (V-Kernel-Fork-set_tid_address and
V-Kernel-Fork-clone), not this file's: this file imports the two preludes and the spec and nothing of the
checked table, so that it can land before the table has an arm
(`tools/lean_port_graph.py`, `derive_edges` rules 3 and 4).  The two
mirrored Rocq files are byte-identical at a71fd38a and at the port's
common baseline f44244ad, which is an ancestor of no day branch; the
header names the one `Sys/Kernel/Fork.lean` names.  No guard holds a
`Checks/` twin's header to the Rocq tree (`tools/check_lean_spec_parity.py`
sweeps `Sys/`), so the sentence before this one is held by readers, and
stops being true the day either Rocq file changes after a71fd38a.  Not part of the trusted specification: what
is trusted is `Sys/Kernel/Fork.lean`, and everything here is proved
against it.

The file is in two halves: the set_tid_address checker and witness first,
then, under their own heading, the clone and clone3 checkers and witnesses,
which arrived with ticket C-Kernel-Fork-clone once the set_tid_address half
had landed.  The Rocq Lemmas stated over the clone checkers — the
four-obligation lemmas, `clone_pid_not_errno` and the witness receptivity
lemmas — were never `unported:` entries, since a Rocq Lemma is not one
(`docs/lean-port/BRIEF.md`, the header block); they arrived with their
subjects.

WHAT THE CHECKER DECIDES.  `set_tid_address` (kernel/fork.c:1747-1752,
Linux v6.18.46, commit 1f99e9ab748f) stores the argument in
`current->clear_child_tid` and returns `task_pid_vnr(current)`; it has no
error path and dereferences nothing, so the only effect a trace may show
is a bare return.  The spec (`Sys/Kernel/Fork.lean`) draws the tid once,
inside `PID_MAX_ENVELOPE`, and repeats it on every later call.  The
checker reads the same decision executably: an effect with any write,
zero, unmap, copy or copy-in ledger is refused outright; with a recorded
tid the return must be that tid; with none the return must be a tid the
spec could have drawn, and it becomes the recorded one.  `CheckReject` is
the answer to every lie, never `CheckUnmodeled`: this arm is inside the
modeled surface whatever the trace says, which is
`check_set_tid_address_complete_unmodeled`'s content.

THE FIRST CALL'S NEW MODEL IS THE CHECKER'S TO CONSTRUCT.  On the `none`
branch the checker answers `CheckOk (with_tid ret m) []`, the model the
spec's `set_tid` step produces for the draw `ret`.  That is where the
"post-model" half of `ca_complete_ok` bites: a checker answering
`CheckOk m []` there would accept exactly the same traces and fail the
proof, because the spec's post-model records the tid.

THE ENVELOPE TEST IS OVER THE RETURN AS AN UNSIGNED 64-BIT VALUE, as the
spec's `choose` is.  A return of `2^64 - 1`, the bit pattern of `-1`,
reads as `18446744073709551615`, fails the upper bound and is refused; so
is 0.  The bounds are the spec's, and the argument for them is on
`Sys.Kernel.Fork.PID_MAX_ENVELOPE`, not here. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Fork

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! ## The checker -/

/-- Rocq: `Checks.Sys.Kernel.Fork.check_set_tid_address`.  The effect is
matched against the return-only shape first, so a ledger of any kind is
refused before the tid is looked at; then the recorded tid, if any,
decides which of the spec's two arms the return is held to.  The Boolean
`decide (0 < …) && decide (… < PID_MAX_ENVELOPE)` is Rocq's
`(0 <? …)%Z && (… <? PID_MAX_ENVELOPE)%Z`. -/
def check_set_tid_address (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | SyscallEffect.mkEffectU ret [] [] [] [] [] =>
      match m_tid m with
      | some tid => if bv_eqb ret tid then CheckOk m [] else CheckReject
      | none =>
          if decide (0 < bv_unsigned ret) && decide (bv_unsigned ret < PID_MAX_ENVELOPE)
          then CheckOk (with_tid ret m) [] else CheckReject
  | _ => CheckReject

/-- Accepting is sound.  Rocq: `check_set_tid_address_sound_ok`.

The proof takes the effect apart into its return and five ledgers, closes every
non-empty ledger by the constructor mismatch `CheckReject = CheckOk …`,
and then follows the recorded tid: with one, `bv_eqb_eq` turns the
accepted test into `ret = tid` and the spec's `ret_only` arm is `pure_ok`;
with none, the two halves of the accepted envelope test feed the spec's
`choose`, and `set_tid` is `modify_ok`. -/
theorem check_set_tid_address_sound_ok (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_set_tid_address eff m = CheckOk m' evs) :
    set_tid_address_spec i m (Ok eff m' evs) := by
  obtain ⟨ret, ws, zs, us, cs, cis⟩ := eff
  cases ws with
  | cons _ _ => exact absurd h (by simp only [check_set_tid_address, reduceCtorEq, not_false_eq_true])
  | nil =>
  cases zs with
  | cons _ _ => exact absurd h (by simp only [check_set_tid_address, reduceCtorEq, not_false_eq_true])
  | nil =>
  cases us with
  | cons _ _ => exact absurd h (by simp only [check_set_tid_address, reduceCtorEq, not_false_eq_true])
  | nil =>
  cases cs with
  | cons _ _ => exact absurd h (by simp only [check_set_tid_address, reduceCtorEq, not_false_eq_true])
  | nil =>
  cases cis with
  | cons _ _ => exact absurd h (by simp only [check_set_tid_address, reduceCtorEq, not_false_eq_true])
  | nil =>
  unfold set_tid_address_spec
  cases htid : m_tid m with
  | some tid =>
      simp only [check_set_tid_address, htid] at h
      cases hr : bv_eqb ret tid with
      | false => simp only [hr, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
      | true =>
          simp only [hr, ↓reduceIte, check_result.CheckOk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hret : ret = tid := (bv_eqb_eq ret tid).mp hr
          subst hret
          refine bind_ok0 _ _ i m m m _ m [] (get_model_ok i m) ?_
          simp only [htid]
          exact pure_ok _ i m
  | none =>
      simp only [check_set_tid_address, htid] at h
      cases hv : (decide (0 < bv_unsigned ret) && decide (bv_unsigned ret < PID_MAX_ENVELOPE)) with
      | false => simp only [hv, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
      | true =>
          simp only [hv, ↓reduceIte, check_result.CheckOk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hlo : 0 < bv_unsigned ret := by
            have := (Bool.and_eq_true _ _).mp hv
            exact of_decide_eq_true this.1
          have hhi : bv_unsigned ret < PID_MAX_ENVELOPE := by
            have := (Bool.and_eq_true _ _).mp hv
            exact of_decide_eq_true this.2
          refine bind_ok0 _ _ i m m m _ (with_tid ret m) [] (get_model_ok i m) ?_
          simp only [htid]
          refine bind_ok0 _ _ i m ret m _ (with_tid ret m) [] (choose_ok _ ret i m ⟨hlo, hhi⟩) ?_
          refine bind_ok0 _ _ i m () (with_tid ret m) _ (with_tid ret m) [] (modify_ok _ i m) ?_
          exact pure_ok _ i (with_tid ret m)

/-- Declining is sound, vacuously: the checker never declines.  Rocq:
`check_set_tid_address_sound_unmodeled`. -/
theorem check_set_tid_address_sound_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (h : check_set_tid_address eff m = CheckUnmodeled) : set_tid_address_spec i m Unmodeled := by
  exfalso
  obtain ⟨ret, ws, zs, us, cs, cis⟩ := eff
  cases ws with
  | cons _ _ => simp only [check_set_tid_address, reduceCtorEq] at h
  | nil =>
  cases zs with
  | cons _ _ => simp only [check_set_tid_address, reduceCtorEq] at h
  | nil =>
  cases us with
  | cons _ _ => simp only [check_set_tid_address, reduceCtorEq] at h
  | nil =>
  cases cs with
  | cons _ _ => simp only [check_set_tid_address, reduceCtorEq] at h
  | nil =>
  cases cis with
  | cons _ _ => simp only [check_set_tid_address, reduceCtorEq] at h
  | nil =>
  cases htid : m_tid m with
  | some tid =>
      simp only [check_set_tid_address, htid] at h
      cases hr : bv_eqb ret tid <;> simp only [hr, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  | none =>
      simp only [check_set_tid_address, htid] at h
      cases hv : (decide (0 < bv_unsigned ret) && decide (bv_unsigned ret < PID_MAX_ENVELOPE)) <;>
        simp only [hv, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

/-- Accepting is complete: every effect the spec admits is accepted, with
the spec's own post-model.  Rocq: `check_set_tid_address_complete_ok`.

The recorded-tid arm is read the way Rocq reads it: `sys_unfold` and
`inv_ok` (Checks/Sys/Prelude.lean) open the primitives and take the
`Ok = Ok` apart, and the accepted test is `bv_eqb tid tid`.  The draw
arm is read through the monad's own `bind_choose_iff` and
`bind_modify_iff` instead: on this arm's unfolded shape — a `choose`
inside two `bind`s, four existentials deep — `inv_ok`'s `cases` chain
exceeds Lean's default recursion depth, and raising the depth is a
setting where a lemma will do.  The two envelope bounds come out as
hypotheses and `decide_eq_true` reads each Boolean as `true`. -/
theorem check_set_tid_address_complete_ok (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : set_tid_address_spec i m (Ok eff m' evs)) :
    check_set_tid_address eff m = CheckOk m' evs := by
  unfold set_tid_address_spec at h
  replace h := get_model_bind_ok_inv _ i m _ m' evs h
  cases htid : m_tid m with
  | some tid =>
      simp only [htid] at h
      sys_unfold
      inv_ok
      simp only [check_set_tid_address, htid, bv_eqb_refl, ↓reduceIte]
  | none =>
      simp only [htid] at h
      rw [bind_choose_iff] at h
      obtain ⟨tid, ⟨hlo, hhi⟩, h⟩ := h
      rw [set_tid, bind_modify_iff] at h
      unfold ret_only Monad.pure at h
      cases h
      simp only [check_set_tid_address, htid, decide_eq_true hlo, decide_eq_true hhi,
        Bool.true_and, ↓reduceIte]

/-- Declining is complete, vacuously: the spec never declines.  Rocq:
`check_set_tid_address_complete_unmodeled`. -/
theorem check_set_tid_address_complete_unmodeled (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (h : set_tid_address_spec i m Unmodeled) : check_set_tid_address eff m = CheckUnmodeled := by
  exfalso
  unfold set_tid_address_spec at h
  replace h := get_model_bind_unmodeled_inv _ i m h
  cases htid : m_tid m with
  | some tid =>
      simp only [htid] at h
      sys_unfold
      inv_ok
  | none =>
      simp only [htid] at h
      rw [bind_choose_iff] at h
      obtain ⟨tid, -, h⟩ := h
      rw [set_tid, bind_modify_iff] at h
      unfold ret_only Monad.pure at h
      cases h

/-! ## The witness -/

/-- One outcome the spec admits at every model.  Rocq:
`Checks.Witness.Kernel.Fork.set_tid_address_witness`.  With a recorded tid
the answer is forced; with none the witness draws 1, the tid `init` holds
and the lowest the envelope admits, and records it. -/
def set_tid_address_witness (m : Model) : outcome SyscallEffect :=
  match m_tid m with
  | some tid => ret_outcome tid m
  | none => ret_outcome (Z_to_bv 64 1) (with_tid (Z_to_bv 64 1) m)

/-- The witness is admitted.  Rocq: `set_tid_address_witness_ok`. -/
theorem set_tid_address_witness_ok (i : SyscallInput) (m : Model) :
    set_tid_address_spec i m (set_tid_address_witness m) := by
  unfold set_tid_address_spec set_tid_address_witness
  cases htid : m_tid m with
  | some tid =>
      refine bind_step _ _ i m m m _ (get_model_ok i m) ?_
      simp only [htid]
      exact pure_ok _ i m
  | none =>
      refine bind_step _ _ i m m m _ (get_model_ok i m) ?_
      simp only [htid]
      refine bind_step _ _ i m (Z_to_bv 64 1) m _ (choose_ok _ (Z_to_bv 64 1) i m ⟨by decide, by decide⟩) ?_
      refine bind_step _ _ i m () (with_tid (Z_to_bv 64 1) m) _ (modify_ok _ i m) ?_
      exact pure_ok _ i _

/-! ## The frame lemma -/

/-- An accepted call leaves the VM ledger as it found it: with a tid
recorded the model handed back is the one handed in, and with none it is
`with_tid ret` of it, which rebuilds the process state alone
(`State/Model.lean`).  Rocq: `VmMapsDisjoint.check_set_tid_address_frame`,
stated here for the reason the file header gives — it depends on nothing
but the checker — and the arm-level fact `Checks/VmMapsDisjoint/Arms.lean`
derives from it through `arm_preserves_of_frame` is the registration's. -/
theorem check_set_tid_address_frame (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_set_tid_address eff m = CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  obtain ⟨ret, ws, zs, us, cs, cis⟩ := eff
  cases ws with
  | cons _ _ => simp only [check_set_tid_address, reduceCtorEq] at h
  | nil =>
  cases zs with
  | cons _ _ => simp only [check_set_tid_address, reduceCtorEq] at h
  | nil =>
  cases us with
  | cons _ _ => simp only [check_set_tid_address, reduceCtorEq] at h
  | nil =>
  cases cs with
  | cons _ _ => simp only [check_set_tid_address, reduceCtorEq] at h
  | nil =>
  cases cis with
  | cons _ _ => simp only [check_set_tid_address, reduceCtorEq] at h
  | nil =>
  cases htid : m_tid m with
  | some tid =>
      simp only [check_set_tid_address, htid] at h
      cases hr : bv_eqb ret tid with
      | false => simp only [hr, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
      | true =>
          simp only [hr, ↓reduceIte, check_result.CheckOk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          rfl
  | none =>
      simp only [check_set_tid_address, htid] at h
      cases hv : (decide (0 < bv_unsigned ret) && decide (bv_unsigned ret < PID_MAX_ENVELOPE)) with
      | false => simp only [hv, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
      | true =>
          simp only [hv, ↓reduceIte, check_result.CheckOk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          rfl


/-! ## clone (220) and clone3 (435)

The clone half of both mirrored Rocq files, ported by ticket
C-Kernel-Fork-clone.  Two entry points, one resolution: `clone_spec` gates
on the flag word and `clone3_spec` on the size, the readable struct and
the image, and both then run `Sys.Kernel.Fork.clone_resolve`, which
declines while a descriptor whose offset the child would share is open
and otherwise admits one of `clone_errnos` or a pid inside
`clone_pid_ok_b`.  The checkers follow the same shape: `check_clone_answer`
reads the return, `check_clone_resolve` and `check_clone3_resolve` put the
descriptor gate and the ledger shape around it, and `check_clone` and
`check_clone3` put the entry point's own gates around those.

WHAT THE RETURN DECIDES.  `kernel_clone` (kernel/fork.c:2570-2655, Linux
v6.18.46, commit 1f99e9ab748f) returns `PTR_ERR(p)` when `copy_process`
failed (:2615) and `pid_vnr(pid)` of the child's `struct pid` otherwise
(:2624, :2654), so a trace shows either a negative errno or a pid, never
both and never 0 — 0 is the CHILD's register (`childregs->a0 = 0` in
`copy_thread`, arch/riscv/kernel/process.c:255, Linux v6.18.46), which this model, which
describes the parent, never sees returned.  The two arms are disjoint on
the return, which `clone_pid_not_errno` proves for every model: an errno
reads as an unsigned value just under `2^64`, a pid below
`PID_MAX_ENVELOPE`.  A return of 0 falls through both tests to
`CheckReject`, and the pid arm alone moves the model, with
`State.with_children`, because only a `copy_process` that succeeded linked
a child onto `current->children` (kernel/fork.c:2398, Linux v6.18.46).

WHAT THE LEDGER DECIDES.  Legacy `clone` dereferences none of its pointer
arguments for the modeled word — the two flags under which a fork writes
the parent's memory, `CLONE_PIDFD` (`copy_process`'s `put_user` of the new
descriptor, kernel/fork.c:2215-2227, Linux v6.18.46) and
`CLONE_PARENT_SETTID` (`kernel_clone`'s `put_user` of the pid, :2626-2627),
are outside `clone_fork_flags_b`, and legacy `clone` hands `parent_tidptr`
to both pointers (:2744-2746) — so its effect must be a bare return.
`clone3` copied `struct clone_args` out of user memory
(the copy at the end of `copy_struct_from_user`, include/linux/uaccess.h:408-409,
Linux v6.18.46), so its effect must carry exactly `[(uargs,
CLONE_ARGS_SIZE_nat)]` and no other ledger: an empty copy-in ledger there
is a claim that the call read no user memory, which would let the model
accept an allocation the kernel refuses.  The descriptor gate is tested
FIRST in both resolutions, so a model the resolution declines answers
`CheckUnmodeled` whatever ledger the effect carries.

The Lean proofs differ from Rocq's in one habit: where Rocq destructs the
effect's five ledgers inside every lemma, seven helper lemmas do it once
and hand the accepted return back — `check_clone_answer_no_unmodeled` and
`check_clone_answer_frame` for the return, `check_clone_resolve_ok_inv`,
`check_clone_resolve_unmodeled_inv` and their `clone3` companions for the
ledgers, `check_clone3_ok_inv` for the size, read and image gates — so the
four obligations and the frame lemma each read one shape.  They are
helper lemmas, not twins, and say so. -/

/-- Rocq: `Checks.Sys.Kernel.Fork.check_clone_answer`.  The errno arm is
tested first and leaves the model alone; the pid arm records the child.
Order does not matter for the answer — `clone_pid_not_errno` says no
return passes both tests — but it is Rocq's order, kept so the two
checkers read alike. -/
def check_clone_answer (ret : word) (m : Model) : check_result :=
  if errno_ret_in clone_errnos ret then CheckOk m []
  else if clone_pid_ok_b m ret then CheckOk (with_children m) []
  else CheckReject

/-- Rocq: `Checks.Sys.Kernel.Fork.check_clone_resolve`.  The descriptor
gate first, then the bare-return shape, then the return. -/
def check_clone_resolve (eff : SyscallEffect) (m : Model) : check_result :=
  if !(clone_no_shared_file_b (m_fds m)) then CheckUnmodeled
  else match eff with
    | SyscallEffect.mkEffectU ret [] [] [] [] [] => check_clone_answer ret m
    | _ => CheckReject

/-- Rocq: `Checks.Sys.Kernel.Fork.check_clone3_resolve`.  The one ledger
the effect may carry is the struct read, `[(uargs, CLONE_ARGS_SIZE_nat)]`,
compared by address and length; Rocq's `Nat.eqb` is `==` on `Nat`. -/
def check_clone3_resolve (uargs : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if !(clone_no_shared_file_b (m_fds m)) then CheckUnmodeled
  else match eff with
    | SyscallEffect.mkEffectU ret [] [] [] [] [(a, n)] =>
        if bv_eqb a uargs && (n == CLONE_ARGS_SIZE_nat) then check_clone_answer ret m
        else CheckReject
    | _ => CheckReject

/-- Rocq: `Checks.Sys.Kernel.Fork.check_clone`.  The flag gate is the
spec's `clone_fork_flags_b`: any other word declines before the effect is
looked at. -/
def check_clone (flags : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if clone_fork_flags_b flags then check_clone_resolve eff m else CheckUnmodeled

/-- Rocq: `Checks.Sys.Kernel.Fork.check_clone3`.  The three declines of
`clone3_spec` in the spec's order — the size, the readable struct, the
image — and then the ledgered resolution.  The read is the spec's bare
`read_bytes_map` with no `access_okb` ahead of it, mirrored here because
the four obligations require it: a `uargs` within 88 bytes of `2^64` whose
walk wraps onto mapped low addresses would be read where Linux's
`access_ok` refuses the range.
bugs/read-bytes-map-wraps-while-access-ok-over-sums-in-z.md lists
`Kernel/Fork` among the files its class has not been audited in, and the
caller-side repair it describes costs the spec, this checker and
`clone3_witness` together; whether any run can hold the shape is that
register's question, not this file's. -/
def check_clone3 (i : SyscallInput) (uargs size : word) (eff : SyscallEffect) (m : Model) :
    check_result :=
  if !(bv_eqb size (Z_to_bv 64 CLONE_ARGS_SIZE)) then CheckUnmodeled
  else match read_bytes_map i.in_mem uargs (Z_to_bv 64 CLONE_ARGS_SIZE) with
    | none => CheckUnmodeled
    | some bs =>
        if clone3_fork_args_b bs then check_clone3_resolve uargs eff m else CheckUnmodeled

/-- No admissible pid can be mistaken for an admissible errno.  Every
member of `clone_errnos` reads as an unsigned 64-bit value just under
`2^64`, and every pid `clone_pid_ok_b` admits is below
`PID_MAX_ENVELOPE`, so `errno_ret_in_below` separates them whatever the
list holds.  This is what keeps `check_clone_resolve` a function of the
observed return, for every `Model` rather than merely every reachable
one.  Rocq: `Checks.Sys.Kernel.Fork.clone_pid_not_errno`. -/
theorem clone_pid_not_errno (m : Model) (r : word) (hok : clone_pid_ok_b m r = true) :
    errno_ret_in clone_errnos r = false := by
  unfold clone_pid_ok_b at hok
  have hrange := ((Bool.and_eq_true _ _).mp hok).1
  have hhi : bv_unsigned r < PID_MAX_ENVELOPE :=
    of_decide_eq_true ((Bool.and_eq_true _ _).mp hrange).2
  apply errno_ret_in_below clone_errnos r (by decide)
  unfold PID_MAX_ENVELOPE at hhi
  unfold two_pow_64
  omega

/-- `check_clone_answer` never declines: both of its tests answer
`CheckOk` or `CheckReject`.  Helper, not a twin. -/
theorem check_clone_answer_no_unmodeled (ret : word) (m : Model) :
    check_clone_answer ret m ≠ CheckUnmodeled := by
  unfold check_clone_answer
  split <;> (try split) <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]

/-- An accepted `check_clone_answer` leaves the VM ledger alone: the model
handed back is `m` or `with_children m`, which rebuilds the process state
alone (`State/Model.lean`).  Helper for the two frame lemmas, not a
twin. -/
theorem check_clone_answer_frame (ret : word) (m m' : Model) (evs : List event)
    (h : check_clone_answer ret m = CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  unfold check_clone_answer at h
  cases hin : errno_ret_in clone_errnos ret with
  | true =>
      simp only [hin, ↓reduceIte, check_result.CheckOk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rfl
  | false =>
      simp only [hin, Bool.false_eq_true, ↓reduceIte] at h
      cases hv : clone_pid_ok_b m ret with
      | false => simp only [hv, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
      | true =>
          simp only [hv, ↓reduceIte, check_result.CheckOk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          rfl

/-- What an accepted `check_clone_resolve` says of its inputs: the gate
was open, the effect was a bare return, and `check_clone_answer` accepted
it.  Helper, not a twin: Rocq destructs the five ledgers inside each
lemma. -/
theorem check_clone_resolve_ok_inv (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_clone_resolve eff m = CheckOk m' evs) :
    clone_no_shared_file_b (m_fds m) = true ∧
      ∃ ret, eff = mkEffect ret [] [] ∧ check_clone_answer ret m = CheckOk m' evs := by
  obtain ⟨ret, ws, zs, us, cs, cis⟩ := eff
  cases hg : clone_no_shared_file_b (m_fds m) with
  | false => simp only [check_clone_resolve, hg, Bool.not_false, ↓reduceIte, reduceCtorEq] at h
  | true =>
  simp only [check_clone_resolve, hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases ws with
  | cons _ _ => simp only [reduceCtorEq] at h
  | nil =>
  cases zs with
  | cons _ _ => simp only [reduceCtorEq] at h
  | nil =>
  cases us with
  | cons _ _ => simp only [reduceCtorEq] at h
  | nil =>
  cases cs with
  | cons _ _ => simp only [reduceCtorEq] at h
  | nil =>
  cases cis with
  | cons _ _ => simp only [reduceCtorEq] at h
  | nil =>
  exact ⟨rfl, ret, rfl, h⟩

/-- A declining `check_clone_resolve` declined at the gate: nothing past
it answers `CheckUnmodeled`.  Helper, not a twin. -/
theorem check_clone_resolve_unmodeled_inv (eff : SyscallEffect) (m : Model)
    (h : check_clone_resolve eff m = CheckUnmodeled) : clone_no_shared_file_b (m_fds m) = false := by
  obtain ⟨ret, ws, zs, us, cs, cis⟩ := eff
  cases hg : clone_no_shared_file_b (m_fds m) with
  | false => rfl
  | true =>
  exfalso
  simp only [check_clone_resolve, hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases ws with
  | cons _ _ => simp only [reduceCtorEq] at h
  | nil =>
  cases zs with
  | cons _ _ => simp only [reduceCtorEq] at h
  | nil =>
  cases us with
  | cons _ _ => simp only [reduceCtorEq] at h
  | nil =>
  cases cs with
  | cons _ _ => simp only [reduceCtorEq] at h
  | nil =>
  cases cis with
  | cons _ _ => simp only [reduceCtorEq] at h
  | nil =>
  exact check_clone_answer_no_unmodeled ret m h

/-- Accepting is sound.  Rocq: `check_clone_resolve_sound_ok`.  The errno
arm is the spec's left alternative, `errno_from` drawing the member
`errno_ret_in_true` names; the pid arm is the right one, `choose` drawing
the return itself and `modify with_children` producing the checker's
post-model. -/
theorem check_clone_resolve_sound_ok (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_clone_resolve eff m = CheckOk m' evs) :
    clone_resolve i m (Ok eff m' evs) := by
  obtain ⟨hg, ret, rfl, ha⟩ := check_clone_resolve_ok_inv eff m m' evs h
  unfold clone_resolve
  refine bind_ok0 _ _ i m m m _ m' evs (get_model_ok i m) ?_
  simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  unfold check_clone_answer at ha
  cases hin : errno_ret_in clone_errnos ret with
  | true =>
      simp only [hin, ↓reduceIte, check_result.CheckOk.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      obtain ⟨e, he, rfl⟩ := (errno_ret_in_true _ _).mp hin
      exact alt_l _ _ i m _
        (bind_ok0 _ _ i m e m _ _ _ (errno_from_witness clone_errnos e i m he) (pure_ok _ i _))
  | false =>
      simp only [hin, Bool.false_eq_true, ↓reduceIte] at ha
      cases hv : clone_pid_ok_b m ret with
      | false => simp only [hv, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at ha
      | true =>
          simp only [hv, ↓reduceIte, check_result.CheckOk.injEq] at ha
          obtain ⟨rfl, rfl⟩ := ha
          exact alt_r _ _ i m _
            (bind_ok0 _ _ i m ret m _ _ _ (choose_ok _ ret i m hv)
              (bind_ok0 _ _ i m () _ _ _ _ (modify_ok _ i m) (pure_ok _ i _)))

/-- Declining is sound: the checker declines only at the descriptor gate,
where the spec declines too.  Rocq: `check_clone_resolve_sound_unmodeled`. -/
theorem check_clone_resolve_sound_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (h : check_clone_resolve eff m = CheckUnmodeled) : clone_resolve i m Unmodeled := by
  have hg := check_clone_resolve_unmodeled_inv eff m h
  unfold clone_resolve
  refine bind_unmodeled2 _ _ i m m m [] (get_model_ok i m) ?_
  simp only [hg, Bool.not_false, ↓reduceIte]
  exact unmodeled_intro i m

/-- Accepting is complete: every effect the spec admits is accepted, with
the spec's own post-model.  Rocq: `check_clone_resolve_complete_ok`.  The
`alt` is opened to its two existential shapes and each is taken apart by
`rcases`; on the errno arm `errno_ret_in_intro` decides the first test,
on the pid arm `clone_pid_not_errno` fails it and the drawn `clone_pid_ok_b`
passes the second. -/
theorem check_clone_resolve_complete_ok (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : clone_resolve i m (Ok eff m' evs)) :
    check_clone_resolve eff m = CheckOk m' evs := by
  unfold clone_resolve at h
  replace h := get_model_bind_ok_inv _ i m _ m' evs h
  cases hg : clone_no_shared_file_b (m_fds m) with
  | false =>
      simp only [hg, Bool.not_false, ↓reduceIte] at h
      have h' : (Ok eff m' evs : outcome SyscallEffect) = Unmodeled := h
      cases h'
  | true =>
      simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      simp only [Monad.alt, Monad.bind, errno_from, Monad.choose, err_ret, ret_only, Monad.pure,
        Monad.modify, outcome.Ok.injEq] at h
      rcases h with ⟨e, m1, evs1, evs2, ⟨x, hx, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl⟩
        | ⟨pid, m1, evs1, evs2, ⟨x, hx, rfl, rfl, rfl⟩,
            ⟨u, m2, evs3, evs4, ⟨_, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl⟩, rfl⟩
      · simp only [check_clone_resolve, check_clone_answer, hg, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, errno_ret_in_intro _ _ hx, List.append_nil]
      · simp only [check_clone_resolve, check_clone_answer, hg, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, clone_pid_not_errno _ _ hx, hx, List.append_nil]

/-- Declining is complete: the spec declines only at the descriptor gate,
and there the checker declines whatever the effect.  Rocq:
`check_clone_resolve_complete_unmodeled`.  Past the gate the `alt` holds
`errno_from`'s `choose`, the pid's `choose`, a `modify` and two `pure`s,
none of which admits `Unmodeled`. -/
theorem check_clone_resolve_complete_unmodeled (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (h : clone_resolve i m Unmodeled) : check_clone_resolve eff m = CheckUnmodeled := by
  unfold clone_resolve at h
  replace h := get_model_bind_unmodeled_inv _ i m h
  cases hg : clone_no_shared_file_b (m_fds m) with
  | false => simp only [check_clone_resolve, hg, Bool.not_false, ↓reduceIte]
  | true =>
      exfalso
      simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      simp only [Monad.alt, Monad.bind, errno_from, Monad.choose, err_ret, ret_only, Monad.pure,
        Monad.modify, reduceCtorEq, and_false, exists_false, or_self] at h

/-- What an accepted `check_clone3_resolve` says of its inputs: the gate
was open, the effect was a bare return under exactly the struct's
copy-in ledger, and `check_clone_answer` accepted the return.  Helper,
not a twin. -/
theorem check_clone3_resolve_ok_inv (uargs : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_clone3_resolve uargs eff m = CheckOk m' evs) :
    clone_no_shared_file_b (m_fds m) = true ∧
      ∃ ret, eff = with_copyins [(uargs, CLONE_ARGS_SIZE_nat)] (mkEffect ret [] []) ∧
        check_clone_answer ret m = CheckOk m' evs := by
  obtain ⟨ret, ws, zs, us, cs, cis⟩ := eff
  cases hg : clone_no_shared_file_b (m_fds m) with
  | false => simp only [check_clone3_resolve, hg, Bool.not_false, ↓reduceIte, reduceCtorEq] at h
  | true =>
  simp only [check_clone3_resolve, hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases ws with
  | cons _ _ => simp only [reduceCtorEq] at h
  | nil =>
  cases zs with
  | cons _ _ => simp only [reduceCtorEq] at h
  | nil =>
  cases us with
  | cons _ _ => simp only [reduceCtorEq] at h
  | nil =>
  cases cs with
  | cons _ _ => simp only [reduceCtorEq] at h
  | nil =>
  cases cis with
  | nil => simp only [reduceCtorEq] at h
  | cons p rest =>
  cases rest with
  | cons _ _ => simp only [reduceCtorEq] at h
  | nil =>
  obtain ⟨a, n⟩ := p
  cases hl : (bv_eqb a uargs && (n == CLONE_ARGS_SIZE_nat)) with
  | false => simp only [hl, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  | true =>
      simp only [hl, ↓reduceIte] at h
      obtain ⟨ha, hn⟩ := (Bool.and_eq_true _ _).mp hl
      obtain rfl := (bv_eqb_eq _ _).mp ha
      obtain rfl := beq_iff_eq.mp hn
      exact ⟨rfl, ret, rfl, h⟩

/-- A declining `check_clone3_resolve` declined at the gate.  Helper, not
a twin. -/
theorem check_clone3_resolve_unmodeled_inv (uargs : word) (eff : SyscallEffect) (m : Model)
    (h : check_clone3_resolve uargs eff m = CheckUnmodeled) :
    clone_no_shared_file_b (m_fds m) = false := by
  obtain ⟨ret, ws, zs, us, cs, cis⟩ := eff
  cases hg : clone_no_shared_file_b (m_fds m) with
  | false => rfl
  | true =>
  exfalso
  simp only [check_clone3_resolve, hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases ws with
  | cons _ _ => simp only [reduceCtorEq] at h
  | nil =>
  cases zs with
  | cons _ _ => simp only [reduceCtorEq] at h
  | nil =>
  cases us with
  | cons _ _ => simp only [reduceCtorEq] at h
  | nil =>
  cases cs with
  | cons _ _ => simp only [reduceCtorEq] at h
  | nil =>
  cases cis with
  | nil => simp only [reduceCtorEq] at h
  | cons p rest =>
  cases rest with
  | cons _ _ => simp only [reduceCtorEq] at h
  | nil =>
  obtain ⟨a, n⟩ := p
  cases hl : (bv_eqb a uargs && (n == CLONE_ARGS_SIZE_nat)) with
  | false => simp only [hl, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  | true =>
      simp only [hl, ↓reduceIte] at h
      exact check_clone_answer_no_unmodeled ret m h

/-- The same four, for the resolution that carries a ledger.  Each goes
through the plain one on the effect with the ledger stripped, so the
admitted answer is decided in exactly one place.  Rocq:
`check_clone3_resolve_sound_ok`. -/
theorem check_clone3_resolve_sound_ok (i : SyscallInput) (uargs : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_clone3_resolve uargs eff m = CheckOk m' evs) :
    clone3_resolve uargs i m (Ok eff m' evs) := by
  obtain ⟨hg, ret, rfl, ha⟩ := check_clone3_resolve_ok_inv uargs eff m m' evs h
  unfold clone3_resolve
  refine record_copyins_ok_empty _ _ i m (mkEffect ret [] []) m' evs rfl ?_
  refine check_clone_resolve_sound_ok i _ m m' evs ?_
  simp only [check_clone_resolve, hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact ha

/-- Rocq: `check_clone3_resolve_sound_unmodeled`. -/
theorem check_clone3_resolve_sound_unmodeled (i : SyscallInput) (uargs : word) (eff : SyscallEffect)
    (m : Model) (h : check_clone3_resolve uargs eff m = CheckUnmodeled) :
    clone3_resolve uargs i m Unmodeled := by
  have hg := check_clone3_resolve_unmodeled_inv uargs eff m h
  unfold clone3_resolve
  apply record_copyins_unmodeled
  refine check_clone_resolve_sound_unmodeled i eff m ?_
  simp only [check_clone_resolve, hg, Bool.not_false, ↓reduceIte]

/-- Rocq: `check_clone3_resolve_complete_ok`.  `record_copyins_ok_inv`
hands back the bare effect the resolution admitted; the plain checker's
completeness accepts it, and its accepted shape is the one the ledgered
checker matches once the ledger is put back. -/
theorem check_clone3_resolve_complete_ok (i : SyscallInput) (uargs : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : clone3_resolve uargs i m (Ok eff m' evs)) :
    check_clone3_resolve uargs eff m = CheckOk m' evs := by
  unfold clone3_resolve at h
  obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m eff m' evs h
  have hc := check_clone_resolve_complete_ok i core m m' evs hcore
  obtain ⟨hg, ret, rfl, ha⟩ := check_clone_resolve_ok_inv core m m' evs hc
  show check_clone3_resolve uargs (SyscallEffect.mkEffectU ret [] [] [] [] [(uargs, CLONE_ARGS_SIZE_nat)]) m
    = CheckOk m' evs
  simp only [check_clone3_resolve, hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bv_eqb_refl,
    beq_self_eq_true, Bool.and_self]
  exact ha

/-- Rocq: `check_clone3_resolve_complete_unmodeled`. -/
theorem check_clone3_resolve_complete_unmodeled (i : SyscallInput) (uargs : word) (m : Model)
    (eff : SyscallEffect) (h : clone3_resolve uargs i m Unmodeled) :
    check_clone3_resolve uargs eff m = CheckUnmodeled := by
  unfold clone3_resolve at h
  have hc := check_clone_resolve_complete_unmodeled i m eff (record_copyins_unmodeled_inv _ _ i m h)
  have hg := check_clone_resolve_unmodeled_inv eff m hc
  simp only [check_clone3_resolve, hg, Bool.not_false, ↓reduceIte]

/-- Rocq: `check_clone_sound_ok`. -/
theorem check_clone_sound_ok (i : SyscallInput) (flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_clone flags eff m = CheckOk m' evs) :
    clone_spec flags i m (Ok eff m' evs) := by
  unfold clone_spec
  cases hf : clone_fork_flags_b flags with
  | false => simp only [check_clone, hf, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  | true =>
      simp only [check_clone, hf, ↓reduceIte] at h
      simp only [↓reduceIte]
      exact check_clone_resolve_sound_ok i eff m m' evs h

/-- Rocq: `check_clone_sound_unmodeled`. -/
theorem check_clone_sound_unmodeled (i : SyscallInput) (flags : word) (eff : SyscallEffect) (m : Model)
    (h : check_clone flags eff m = CheckUnmodeled) : clone_spec flags i m Unmodeled := by
  unfold clone_spec
  cases hf : clone_fork_flags_b flags with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact unmodeled_intro i m
  | true =>
      simp only [check_clone, hf, ↓reduceIte] at h
      simp only [↓reduceIte]
      exact check_clone_resolve_sound_unmodeled i eff m h

/-- Rocq: `check_clone_complete_ok`. -/
theorem check_clone_complete_ok (i : SyscallInput) (flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : clone_spec flags i m (Ok eff m' evs)) :
    check_clone flags eff m = CheckOk m' evs := by
  unfold clone_spec at h
  cases hf : clone_fork_flags_b flags with
  | false =>
      simp only [hf, Bool.false_eq_true, ↓reduceIte] at h
      have h' : (Ok eff m' evs : outcome SyscallEffect) = Unmodeled := h
      cases h'
  | true =>
      simp only [hf, ↓reduceIte] at h
      simp only [check_clone, hf, ↓reduceIte]
      exact check_clone_resolve_complete_ok i eff m m' evs h

/-- Rocq: `check_clone_complete_unmodeled`. -/
theorem check_clone_complete_unmodeled (i : SyscallInput) (flags : word) (m : Model)
    (eff : SyscallEffect) (h : clone_spec flags i m Unmodeled) :
    check_clone flags eff m = CheckUnmodeled := by
  unfold clone_spec at h
  cases hf : clone_fork_flags_b flags with
  | false => simp only [check_clone, hf, Bool.false_eq_true, ↓reduceIte]
  | true =>
      simp only [hf, ↓reduceIte] at h
      simp only [check_clone, hf, ↓reduceIte]
      exact check_clone_resolve_complete_unmodeled i m eff h

/-- What an accepted `check_clone3` says of its inputs: the size was the
struct's, the struct was readable, its image was the plain fork's, and
the ledgered resolution accepted the effect.  Helper, not a twin. -/
theorem check_clone3_ok_inv (i : SyscallInput) (uargs size : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_clone3 i uargs size eff m = CheckOk m' evs) :
    bv_eqb size (Z_to_bv 64 CLONE_ARGS_SIZE) = true ∧
      ∃ bs, read_bytes_map i.in_mem uargs (Z_to_bv 64 CLONE_ARGS_SIZE) = some bs ∧
        clone3_fork_args_b bs = true ∧ check_clone3_resolve uargs eff m = CheckOk m' evs := by
  unfold check_clone3 at h
  cases hsz : bv_eqb size (Z_to_bv 64 CLONE_ARGS_SIZE) with
  | false => simp only [hsz, Bool.not_false, ↓reduceIte, reduceCtorEq] at h
  | true =>
  simp only [hsz, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hbs : read_bytes_map i.in_mem uargs (Z_to_bv 64 CLONE_ARGS_SIZE) with
  | none => simp only [hbs, reduceCtorEq] at h
  | some bs =>
  simp only [hbs] at h
  cases ha : clone3_fork_args_b bs with
  | false => simp only [ha, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  | true =>
  simp only [ha, ↓reduceIte] at h
  exact ⟨rfl, bs, rfl, ha, h⟩

/-- Rocq: `check_clone3_sound_ok`.  The spec's `input` is read with
`bind_ok0` and the three gates are followed as the checker took them. -/
theorem check_clone3_sound_ok (i : SyscallInput) (uargs size : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_clone3 i uargs size eff m = CheckOk m' evs) :
    clone3_spec uargs size i m (Ok eff m' evs) := by
  obtain ⟨hsz, bs, hbs, ha, h⟩ := check_clone3_ok_inv i uargs size eff m m' evs h
  unfold clone3_spec
  simp only [hsz, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine bind_ok0 _ _ i m i m _ m' evs (input_ok i m) ?_
  simp only [hbs, ha, ↓reduceIte]
  exact check_clone3_resolve_sound_ok i uargs eff m m' evs h

/-- Rocq: `check_clone3_sound_unmodeled`.  Three declines are the spec's
own `unmodeled`; the fourth, past the image gate, is the resolution's. -/
theorem check_clone3_sound_unmodeled (i : SyscallInput) (uargs size : word) (eff : SyscallEffect)
    (m : Model) (h : check_clone3 i uargs size eff m = CheckUnmodeled) :
    clone3_spec uargs size i m Unmodeled := by
  unfold check_clone3 at h
  unfold clone3_spec
  cases hsz : bv_eqb size (Z_to_bv 64 CLONE_ARGS_SIZE) with
  | false =>
      simp only [Bool.not_false, ↓reduceIte]
      exact unmodeled_intro i m
  | true =>
  simp only [hsz, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  refine bind_unmodeled2 _ _ i m i m [] (input_ok i m) ?_
  cases hbs : read_bytes_map i.in_mem uargs (Z_to_bv 64 CLONE_ARGS_SIZE) with
  | none =>
      exact unmodeled_intro i m
  | some bs =>
  simp only [hbs] at h ⊢
  cases ha : clone3_fork_args_b bs with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact unmodeled_intro i m
  | true =>
  simp only [ha, ↓reduceIte] at h ⊢
  exact check_clone3_resolve_sound_unmodeled i uargs eff m h

/-- Rocq: `check_clone3_complete_ok`. -/
theorem check_clone3_complete_ok (i : SyscallInput) (uargs size : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : clone3_spec uargs size i m (Ok eff m' evs)) :
    check_clone3 i uargs size eff m = CheckOk m' evs := by
  unfold clone3_spec at h
  cases hsz : bv_eqb size (Z_to_bv 64 CLONE_ARGS_SIZE) with
  | false =>
      simp only [hsz, Bool.not_false, ↓reduceIte] at h
      have h' : (Ok eff m' evs : outcome SyscallEffect) = Unmodeled := h
      cases h'
  | true =>
  simp only [hsz, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  replace h := input_bind_ok_inv _ i m _ m' evs h
  cases hbs : read_bytes_map i.in_mem uargs (Z_to_bv 64 CLONE_ARGS_SIZE) with
  | none =>
      simp only [hbs] at h
      have h' : (Ok eff m' evs : outcome SyscallEffect) = Unmodeled := h
      cases h'
  | some bs =>
  simp only [hbs] at h
  cases ha : clone3_fork_args_b bs with
  | false =>
      simp only [ha, Bool.false_eq_true, ↓reduceIte] at h
      have h' : (Ok eff m' evs : outcome SyscallEffect) = Unmodeled := h
      cases h'
  | true =>
  simp only [ha, ↓reduceIte] at h
  simp only [check_clone3, hsz, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hbs, ha]
  exact check_clone3_resolve_complete_ok i uargs eff m m' evs h

/-- Rocq: `check_clone3_complete_unmodeled`. -/
theorem check_clone3_complete_unmodeled (i : SyscallInput) (uargs size : word) (m : Model)
    (eff : SyscallEffect) (h : clone3_spec uargs size i m Unmodeled) :
    check_clone3 i uargs size eff m = CheckUnmodeled := by
  unfold clone3_spec at h
  cases hsz : bv_eqb size (Z_to_bv 64 CLONE_ARGS_SIZE) with
  | false => simp only [check_clone3, hsz, Bool.not_false, ↓reduceIte]
  | true =>
  simp only [hsz, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  replace h := input_bind_unmodeled_inv _ i m h
  cases hbs : read_bytes_map i.in_mem uargs (Z_to_bv 64 CLONE_ARGS_SIZE) with
  | none => simp only [check_clone3, hsz, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hbs]
  | some bs =>
  simp only [hbs] at h
  cases ha : clone3_fork_args_b bs with
  | false => simp only [check_clone3, hsz, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hbs, ha]
  | true =>
  simp only [ha, ↓reduceIte] at h
  simp only [check_clone3, hsz, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hbs, ha]
  exact check_clone3_resolve_complete_unmodeled i uargs m eff h

/-! ## The clone witnesses

One outcome each spec admits at every model, for the progress argument.
Both fail with -EAGAIN, the head of `clone_errnos` — the answer
`copy_process` gives when `RLIMIT_NPROC` is reached (kernel/fork.c:2058-2064,
Linux v6.18.46; the thread ceiling's -EAGAIN at :2071-2073 is the other) — because a failure is admitted at every model the gate
lets through, where a pid would have to avoid the recorded tid.  Where the
gate is closed the witness declines, as the spec does. -/

/-- Rocq: `Checks.Witness.Kernel.Fork.clone_resolve_witness`. -/
def clone_resolve_witness (m : Model) : outcome SyscallEffect :=
  if !(clone_no_shared_file_b (m_fds m)) then Unmodeled
  else ret_outcome (errno_ret EAGAIN) m

/-- The witness is admitted.  Rocq: `clone_resolve_witness_ok`. -/
theorem clone_resolve_witness_ok (i : SyscallInput) (m : Model) :
    clone_resolve i m (clone_resolve_witness m) := by
  unfold clone_resolve clone_resolve_witness
  refine bind_step _ _ i m m m _ (get_model_ok i m) ?_
  cases hg : clone_no_shared_file_b (m_fds m) with
  | false =>
      simp only [Bool.not_false, ↓reduceIte]
      exact unmodeled_intro i m
  | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact alt_l _ _ i m _
        (bind_ok0 _ _ i m EAGAIN m _ _ _ (errno_from_witness clone_errnos EAGAIN i m (by decide))
          (pure_ok _ i m))

/-- Rocq: `Checks.Witness.Kernel.Fork.clone_witness`. -/
def clone_witness (flags : word) (m : Model) : outcome SyscallEffect :=
  if clone_fork_flags_b flags then clone_resolve_witness m else Unmodeled

/-- Rocq: `clone_witness_ok`. -/
theorem clone_witness_ok (i : SyscallInput) (flags : word) (m : Model) :
    clone_spec flags i m (clone_witness flags m) := by
  unfold clone_spec clone_witness
  cases hf : clone_fork_flags_b flags with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact unmodeled_intro i m
  | true =>
      simp only [↓reduceIte]
      exact clone_resolve_witness_ok i m

/-- The same witness, carrying the copy-in ledger the `clone3` resolution
records.  `clone_resolve_witness` answers with `mkEffect`, whose
`eff_copyins` is `[]`, so `record_copyins_ok_empty` applies directly.
Rocq: `Checks.Witness.Kernel.Fork.clone3_resolve_witness`. -/
def clone3_resolve_witness (uargs : word) (m : Model) : outcome SyscallEffect :=
  if !(clone_no_shared_file_b (m_fds m)) then Unmodeled
  else Ok (with_copyins [(uargs, CLONE_ARGS_SIZE_nat)] (mkEffect (errno_ret EAGAIN) [] [])) m []

/-- Rocq: `clone3_resolve_witness_ok`. -/
theorem clone3_resolve_witness_ok (i : SyscallInput) (uargs : word) (m : Model) :
    clone3_resolve uargs i m (clone3_resolve_witness uargs m) := by
  unfold clone3_resolve clone3_resolve_witness
  cases hg : clone_no_shared_file_b (m_fds m) with
  | false =>
      simp only [Bool.not_false, ↓reduceIte]
      apply record_copyins_unmodeled
      unfold clone_resolve
      refine bind_unmodeled2 _ _ i m m m [] (get_model_ok i m) ?_
      simp only [hg, Bool.not_false, ↓reduceIte]
      exact unmodeled_intro i m
  | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine record_copyins_ok_empty _ _ i m (mkEffect (errno_ret EAGAIN) [] []) m [] rfl ?_
      have h := clone_resolve_witness_ok i m
      simp only [clone_resolve_witness, hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        ret_outcome] at h
      exact h

/-- Rocq: `Checks.Witness.Kernel.Fork.clone3_witness`. -/
def clone3_witness (i : SyscallInput) (uargs size : word) (m : Model) : outcome SyscallEffect :=
  if !(bv_eqb size (Z_to_bv 64 CLONE_ARGS_SIZE)) then Unmodeled
  else match read_bytes_map i.in_mem uargs (Z_to_bv 64 CLONE_ARGS_SIZE) with
    | none => Unmodeled                     -- unreadable clone_args
    | some bs =>
        if clone3_fork_args_b bs then clone3_resolve_witness uargs m else Unmodeled

/-- Rocq: `clone3_witness_ok`. -/
theorem clone3_witness_ok (i : SyscallInput) (uargs size : word) (m : Model) :
    clone3_spec uargs size i m (clone3_witness i uargs size m) := by
  unfold clone3_spec clone3_witness
  cases hsz : bv_eqb size (Z_to_bv 64 CLONE_ARGS_SIZE) with
  | false =>
      simp only [Bool.not_false, ↓reduceIte]
      exact unmodeled_intro i m
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine bind_step _ _ i m i m _ (input_ok i m) ?_
  cases hbs : read_bytes_map i.in_mem uargs (Z_to_bv 64 CLONE_ARGS_SIZE) with
  | none =>
      dsimp only
      exact unmodeled_intro i m
  | some bs =>
  dsimp only
  cases ha : clone3_fork_args_b bs with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact unmodeled_intro i m
  | true =>
  simp only [↓reduceIte]
  exact clone3_resolve_witness_ok i uargs m

/-! ## The clone frame lemmas -/

/-- An accepted `clone` leaves the VM ledger as it found it: the errno arm
hands back `m`, the pid arm `with_children m`.  Rocq:
`VmMapsDisjoint.check_clone_frame`, stated here for the reason the file
header gives. -/
theorem check_clone_frame (flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_clone flags eff m = CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  cases hf : clone_fork_flags_b flags with
  | false => simp only [check_clone, hf, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  | true =>
      simp only [check_clone, hf, ↓reduceIte] at h
      obtain ⟨-, ret, -, h⟩ := check_clone_resolve_ok_inv eff m m' evs h
      exact check_clone_answer_frame ret m m' evs h

/-- The same for `clone3`.  Rocq: `VmMapsDisjoint.check_clone3_frame`. -/
theorem check_clone3_frame (i : SyscallInput) (uargs size : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_clone3 i uargs size eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨-, bs, -, -, h⟩ := check_clone3_ok_inv i uargs size eff m m' evs h
  obtain ⟨-, ret, -, h⟩ := check_clone3_resolve_ok_inv uargs eff m m' evs h
  exact check_clone_answer_frame ret m m' evs h

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Fork
