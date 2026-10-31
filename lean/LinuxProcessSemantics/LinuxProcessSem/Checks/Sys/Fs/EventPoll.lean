-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Checks/Sys/Fs/EventPoll.v
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.EventPoll
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-! # LinuxProcessSem.Checks.Sys.Fs.EventPoll — epoll_create1 (20), epoll_ctl (21), epoll_pwait (22): checker, witness, frame

Ports `theories/LinuxProcessSem/Checks/Sys/Fs/EventPoll.v` — the three
checkers and their twelve soundness and completeness lemmas — and, in the
same file, `theories/LinuxProcessSem/Checks/Witness/Fs/EventPoll.v` (the
three witnesses and their `*_witness_ok` lemmas) and the three per-checker
frame lemmas that `theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`
states for `check_epoll_create1`, `check_epoll_ctl` and
`check_epoll_pwait`.  Every name below is the Rocq name, and every
executable definition is the Rocq definition: each checker is its
syscall's `*_outcome` read back, `CheckUnmodeled` where that answers
`none` and `check_ret_only` against the one return it names otherwise.
Not part of the trusted specification: nothing here claims anything about
Linux that `Sys/Fs/EventPoll.lean` does not already claim.  The
definitions are the executable side of that spec and the lemmas say the
two sides agree, in both directions.  Its pins are
`Checks/Cases/Checks/Sys/Fs/EventPoll.lean`.

WHY THREE ROCQ FILES MEET IN ONE LEAN FILE is argued in the header of
`Checks/Sys/Fs/Select.lean`; the short form is that the VmMapsDisjoint
twin takes each arm's `*_frame` lemma from wherever the arm's ticket put
it, and the witness prelude reaches each witness through the checked-arm
table's arm block, so both twins sit here under their Rocq names.  One
thing the earlier twins could not do, this one does: their witnesses were
written before the witness prelude landed — Select's spell their outcome
by hand because it carries the fd-set writes, and
`Checks/Sys/Kernel/Groups.lean`'s spell the return-only one by hand and
say so — while the witnesses below are built from
`Checks/Witness/Prelude.lean`'s `ret_outcome`, as Rocq's are.  That is why
this file imports that prelude and why its `*_witness_ok` proofs step with
`bind_step`, the lemma Rocq's tactic of that name applies, rather than the
checker prelude's `bind_ok0` and `bind_unmodeled2` pair.  Each witness
keeps its own Rocq twin's argument order: syscall arguments first and the
input and model last, as `Checks/Witness/Fs/EventPoll.v` has them; the
Select twins put the input and model first because
`Checks/Witness/Fs/Select.v`'s `pselect6_witness` does.  The checked-arm
row that consumes a witness applies it to `i m` either way, so neither
order costs the table anything.

WHAT THE CHECKER RESTS ON.  All three arms are deterministic and write no
user memory, so each acceptor is the spec's own computation plus one
equality on the return value, and `check_ret_only` carries the rest of the
obligation: it rejects any effect with a non-empty write, zero, unmap,
copy or copy-in ledger, which is what pins that a conforming run may not
smuggle a store past an arm that stores nothing.  Everything that makes
epoll hard — readiness, the interest set, the ready list, blocking — is
decided by the spec's outcome function answering `none`, which is
`CheckUnmodeled` here, before the effect is looked at.  Which kernel steps
the spec answers and which it declines is the spec's business and is
argued on `Sys/Fs/EventPoll.lean`; the checker adds no decision of its
own.  The entry points the equality is measured against, read at commit
1f99e9ab748f: `epoll_create1` (fs/eventpoll.c:2473-2476, Linux v6.18.46)
into `do_epoll_create` (fs/eventpoll.c:2430-2471, Linux v6.18.46), whose
one modeled rejection precedes every allocation — the -ENOMEM of
`ep_alloc` (fs/eventpoll.c:1341-1363, Linux v6.18.46) and the -EMFILE of
the descriptor table lie on the well-formed path the spec declines;
`epoll_ctl`
(fs/eventpoll.c:2658-2668, Linux v6.18.46), which copies the event struct
before `do_epoll_ctl` (fs/eventpoll.c:2511-2651, Linux v6.18.46) looks
either descriptor up; and `epoll_pwait` (fs/eventpoll.c:2774-2783, Linux
v6.18.46) into `do_epoll_pwait` (fs/eventpoll.c:2753-2772, Linux
v6.18.46), which installs the mask through `set_user_sigmask`
(kernel/signal.c:3281-3297, Linux v6.18.46) before `do_epoll_wait`
(fs/eventpoll.c:2715-2738, Linux v6.18.46) resolves the epfd and
`ep_check_params` (fs/eventpoll.c:2670-2689, Linux v6.18.46) judges the
count, the range and the file.

ONE BINDER IS RENAMED: Rocq's fourth `epoll_ctl`
argument is `event`, which in this tree is also the type of the event
list every lemma below quantifies over (`evs : List event`), so the word
argument is `ev` here.  The spec twin keeps `event`, because its
statements mention no event list.

THE PROOFS are Rocq's, step for step.  Each direction splits the outcome
function — `none`, then `some r` — and uses `check_ret_only_ok_iff` for
the two `Ok` directions and `check_ret_only_no_unmodeled` to rule out a
checker decline in an answered branch, while the spec proof rules it out
by constructor mismatch.  Rocq's `destruct ... eqn:Ho; cbv iota` is
`cases ho : ... with` followed by `rw [ho] at h` and `dsimp only`, for the
reason `Checks/Sys/Fs/Sync.lean` gives for generalising its lookup:
`cases` on the outcome substitutes the goal but not a hypothesis that
still mentions the scrutinee.  The two-reader arms open with the checker
prelude's `bind_input_model_inv` where Rocq's open with
`sys_unfold; inv_ok`.

THE FRAME LEMMAS are here for the reason `Checks/Sys/Fs/Sync.lean` gives:
each depends on nothing but its checker, and a lemma provable where its
subject is defined should not wait on a file that cannot import it.  The
C ticket's acceptance text assigns them to the registration step; the
four checker twins already in the tree state them early, and this one
does the same.  Each is closed by `vm_frame2`, Rocq's proof name for
name: the tactic landed with `Checks/VmMapsDisjoint.lean` (#1054), whose
header asks a checker's file to import it — that file imports
`Checks/Sys/Dispatch.lean` and never `Checks/Sys/Table.lean`, so the
import runs one way even once the V ticket registers the arm.  The four
earlier twins predate the tactic and write the steps out. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.EventPoll

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.EventPoll
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-! ## epoll_create1 (20) -/

/-- Accept an observed `epoll_create1` effect exactly when
`epoll_create1_spec` admits it: `CheckUnmodeled` where the spec declines
(a well-formed flag word, whose success arm is not modeled), and
otherwise `check_ret_only` against the one return the spec names, with
the model handed back unchanged and no event.  Mirrors
`check_epoll_create1` in
`theories/LinuxProcessSem/Checks/Sys/Fs/EventPoll.v`. -/
def check_epoll_create1 (flags32 : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match epoll_create1_outcome flags32 with
  | none => CheckUnmodeled
  | some r => check_ret_only eff r m []

/-- Every `CheckOk` the checker returns is a run the spec admits: the
accepted effect is the spec's `mkEffect r [] []`, the model is unchanged
and no event is emitted.  Rocq: `check_epoll_create1_sound_ok`. -/
theorem check_epoll_create1_sound_ok (flags32 : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : check_epoll_create1 flags32 eff m = CheckOk m' evs) :
    epoll_create1_spec flags32 i m (Ok eff m' evs) := by
  unfold check_epoll_create1 at h
  unfold epoll_create1_spec
  cases ho : epoll_create1_outcome flags32 with
  | none => rw [ho] at h; cases h
  | some r =>
    rw [ho] at h
    dsimp only at h ⊢
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact pure_ok _ i _

/-- Every `CheckUnmodeled` the checker returns is a run the spec leaves
unmodeled: the checker declines only where the outcome function is
`none`, and there the spec is `unmodeled`; on the other arm
`check_ret_only` never declines.  Rocq:
`check_epoll_create1_sound_unmodeled`. -/
theorem check_epoll_create1_sound_unmodeled (flags32 : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_epoll_create1 flags32 eff m = CheckUnmodeled) :
    epoll_create1_spec flags32 i m Unmodeled := by
  unfold check_epoll_create1 at h
  unfold epoll_create1_spec
  cases ho : epoll_create1_outcome flags32 with
  | none =>
    dsimp only
    exact unmodeled_intro i m
  | some r =>
    rw [ho] at h
    dsimp only at h
    exact (check_ret_only_no_unmodeled _ _ _ _ h).elim

/-- Every run the spec admits is one the checker accepts, with the same
model and the same (empty) event list.  Rocq:
`check_epoll_create1_complete_ok`. -/
theorem check_epoll_create1_complete_ok (flags32 : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (h : epoll_create1_spec flags32 i m (Ok eff m' evs)) :
    check_epoll_create1 flags32 eff m = CheckOk m' evs := by
  unfold epoll_create1_spec at h
  unfold check_epoll_create1
  cases ho : epoll_create1_outcome flags32 with
  | none =>
    rw [ho] at h
    dsimp only at h
    simp only [Monad.unmodeled] at h
    cases h
  | some r =>
    rw [ho] at h
    dsimp only at h ⊢
    simp only [Monad.pure, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- Every run the spec leaves unmodeled is one the checker declines,
whatever effect it is shown.  Rocq:
`check_epoll_create1_complete_unmodeled`. -/
theorem check_epoll_create1_complete_unmodeled (flags32 : word) (m : Model) (eff : SyscallEffect)
    (i : SyscallInput) (h : epoll_create1_spec flags32 i m Unmodeled) :
    check_epoll_create1 flags32 eff m = CheckUnmodeled := by
  unfold epoll_create1_spec at h
  unfold check_epoll_create1
  cases ho : epoll_create1_outcome flags32 with
  | none => rfl
  | some r =>
    rw [ho] at h
    dsimp only at h
    simp only [Monad.pure] at h
    cases h

/-- The one effect the spec admits for `epoll_create1` on this flag word,
or `Unmodeled` where it admits none — which is itself the admissible
outcome on a well-formed create, and is what makes progress hold for a
syscall whose success arm is not modeled at all.  Mirrors
`epoll_create1_witness` in
`theories/LinuxProcessSem/Checks/Witness/Fs/EventPoll.v`. -/
def epoll_create1_witness (flags32 : word) (m : Model) : outcome SyscallEffect :=
  match epoll_create1_outcome flags32 with
  | none => Unmodeled
  | some r => ret_outcome r m

/-- The witness is a run of the spec: the spec is receptive on every
input and model.  Rocq: `epoll_create1_witness_ok`. -/
theorem epoll_create1_witness_ok (flags32 : word) (i : SyscallInput) (m : Model) :
    epoll_create1_spec flags32 i m (epoll_create1_witness flags32 m) := by
  unfold epoll_create1_spec epoll_create1_witness
  cases ho : epoll_create1_outcome flags32 with
  | none => exact unmodeled_intro i m
  | some r => exact pure_ok _ i m

/-- `epoll_create1` accepts only with the model it was given, so the
mapping ledger is untouched.  Mirrors `check_epoll_create1_frame` in
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`. -/
theorem check_epoll_create1_frame (flags32 : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_epoll_create1 flags32 eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_epoll_create1 at h
  vm_frame2 h

/-! ## epoll_ctl (21) -/

/-- Accept an observed `epoll_ctl` effect exactly when `epoll_ctl_spec`
admits it: `CheckUnmodeled` where the spec declines (a channel target,
for which `fd_can_poll` returns `none`, and the /dev/null and
/dev/urandom targets the spec leaves unanswered until each has its own
probe), and otherwise `check_ret_only` against the one return the spec
names — Linux's errno, from the event struct's readability, then the two
lookups, then the target's `->poll`, then -EINVAL, in the kernel's order.
The syscall input is an argument because the arm reads user memory
through it.  Mirrors `check_epoll_ctl` in
`theories/LinuxProcessSem/Checks/Sys/Fs/EventPoll.v`. -/
def check_epoll_ctl (i : SyscallInput) (epfd op32 tfd ev : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match epoll_ctl_outcome i m epfd op32 tfd ev with
  | none => CheckUnmodeled
  | some r => check_ret_only eff r m []

/-- Every `CheckOk` the checker returns is a run the spec admits.  Rocq:
`check_epoll_ctl_sound_ok`. -/
theorem check_epoll_ctl_sound_ok (i : SyscallInput) (epfd op32 tfd ev : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_epoll_ctl i epfd op32 tfd ev eff m = CheckOk m' evs) :
    epoll_ctl_spec epfd op32 tfd ev i m (Ok eff m' evs) := by
  unfold check_epoll_ctl at h
  unfold epoll_ctl_spec
  apply bind_ok0 _ _ i m i m _ _ _ (input_ok i m)
  apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
  cases ho : epoll_ctl_outcome i m epfd op32 tfd ev with
  | none => rw [ho] at h; cases h
  | some r =>
    rw [ho] at h
    dsimp only at h ⊢
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact pure_ok _ i _

/-- Every `CheckUnmodeled` the checker returns is a run the spec leaves
unmodeled.  Rocq: `check_epoll_ctl_sound_unmodeled`. -/
theorem check_epoll_ctl_sound_unmodeled (i : SyscallInput) (epfd op32 tfd ev : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_epoll_ctl i epfd op32 tfd ev eff m = CheckUnmodeled) :
    epoll_ctl_spec epfd op32 tfd ev i m Unmodeled := by
  unfold check_epoll_ctl at h
  unfold epoll_ctl_spec
  apply bind_unmodeled2 _ _ i m i m [] (input_ok i m)
  apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
  cases ho : epoll_ctl_outcome i m epfd op32 tfd ev with
  | none =>
    dsimp only
    exact unmodeled_intro i m
  | some r =>
    rw [ho] at h
    dsimp only at h
    exact (check_ret_only_no_unmodeled _ _ _ _ h).elim

/-- Every run the spec admits is one the checker accepts.  Rocq:
`check_epoll_ctl_complete_ok`. -/
theorem check_epoll_ctl_complete_ok (i : SyscallInput) (epfd op32 tfd ev : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : epoll_ctl_spec epfd op32 tfd ev i m (Ok eff m' evs)) :
    check_epoll_ctl i epfd op32 tfd ev eff m = CheckOk m' evs := by
  unfold epoll_ctl_spec at h
  have h := bind_input_model_inv _ i m _ h
  unfold check_epoll_ctl
  cases ho : epoll_ctl_outcome i m epfd op32 tfd ev with
  | none =>
    rw [ho] at h
    dsimp only at h
    simp only [Monad.unmodeled] at h
    cases h
  | some r =>
    rw [ho] at h
    dsimp only at h ⊢
    simp only [Monad.pure, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- Every run the spec leaves unmodeled is one the checker declines,
whatever effect it is shown.  Rocq: `check_epoll_ctl_complete_unmodeled`. -/
theorem check_epoll_ctl_complete_unmodeled (i : SyscallInput) (epfd op32 tfd ev : word)
    (m : Model) (eff : SyscallEffect)
    (h : epoll_ctl_spec epfd op32 tfd ev i m Unmodeled) :
    check_epoll_ctl i epfd op32 tfd ev eff m = CheckUnmodeled := by
  unfold epoll_ctl_spec at h
  have h := bind_input_model_inv _ i m _ h
  unfold check_epoll_ctl
  cases ho : epoll_ctl_outcome i m epfd op32 tfd ev with
  | none => rfl
  | some r =>
    rw [ho] at h
    dsimp only at h
    simp only [Monad.pure] at h
    cases h

/-- The one effect the spec admits for `epoll_ctl` on this input and
model, or `Unmodeled` where it admits none.  Mirrors
`epoll_ctl_witness`
in `theories/LinuxProcessSem/Checks/Witness/Fs/EventPoll.v`, in Rocq's
argument order (the file header says why). -/
def epoll_ctl_witness (epfd op32 tfd ev : word) (i : SyscallInput) (m : Model) :
    outcome SyscallEffect :=
  match epoll_ctl_outcome i m epfd op32 tfd ev with
  | none => Unmodeled
  | some r => ret_outcome r m

/-- The witness is a run of the spec.  Rocq: `epoll_ctl_witness_ok`. -/
theorem epoll_ctl_witness_ok (epfd op32 tfd ev : word) (i : SyscallInput) (m : Model) :
    epoll_ctl_spec epfd op32 tfd ev i m (epoll_ctl_witness epfd op32 tfd ev i m) := by
  unfold epoll_ctl_spec epoll_ctl_witness
  apply bind_step _ _ i m i m _ (input_ok i m)
  apply bind_step _ _ i m m m _ (get_model_ok i m)
  cases ho : epoll_ctl_outcome i m epfd op32 tfd ev with
  | none => exact unmodeled_intro i m
  | some r => exact pure_ok _ i m

/-- `epoll_ctl` accepts only with the model it was given.  Mirrors
`check_epoll_ctl_frame` in
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`. -/
theorem check_epoll_ctl_frame (i : SyscallInput) (epfd op32 tfd ev : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_epoll_ctl i epfd op32 tfd ev eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_epoll_ctl at h
  vm_frame2 h

/-! ## epoll_pwait (22) -/

/-- Accept an observed `epoll_pwait` effect exactly when
`epoll_pwait_spec` admits it: `CheckUnmodeled` where
`epoll_pwait_outcome` declines — a signal mask that would be installed,
which this model has no signals to install — and otherwise
`check_ret_only` against the one return the outcome names: -EINVAL for a
wrong `sigsetsize`, -EFAULT for an unreadable mask, -EBADF for a closed
epfd, -EINVAL for a count outside `(0, EP_MAX_EVENTS]`, then -EFAULT or
-EINVAL on the `access_ok` of the events array
(fs/eventpoll.c:2670-2689, Linux v6.18.46).  `timeout` is not an
argument, as it is not one of the spec's: no arm reads it.
Mirrors `check_epoll_pwait` in
`theories/LinuxProcessSem/Checks/Sys/Fs/EventPoll.v`. -/
def check_epoll_pwait (i : SyscallInput) (epfd events maxevents32 sigmask sigsetsize : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize with
  | none => CheckUnmodeled
  | some r => check_ret_only eff r m []

/-- Every `CheckOk` the checker returns is a run the spec admits.  Rocq:
`check_epoll_pwait_sound_ok`. -/
theorem check_epoll_pwait_sound_ok (i : SyscallInput)
    (epfd events maxevents32 sigmask sigsetsize : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m = CheckOk m' evs) :
    epoll_pwait_spec epfd events maxevents32 sigmask sigsetsize i m (Ok eff m' evs) := by
  unfold check_epoll_pwait at h
  unfold epoll_pwait_spec
  apply bind_ok0 _ _ i m i m _ _ _ (input_ok i m)
  apply bind_ok0 _ _ i m m m _ _ _ (get_model_ok i m)
  cases ho : epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize with
  | none => rw [ho] at h; cases h
  | some r =>
    rw [ho] at h
    dsimp only at h ⊢
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact pure_ok _ i _

/-- Every `CheckUnmodeled` the checker returns is a run the spec leaves
unmodeled.  Rocq: `check_epoll_pwait_sound_unmodeled`. -/
theorem check_epoll_pwait_sound_unmodeled (i : SyscallInput)
    (epfd events maxevents32 sigmask sigsetsize : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m = CheckUnmodeled) :
    epoll_pwait_spec epfd events maxevents32 sigmask sigsetsize i m Unmodeled := by
  unfold check_epoll_pwait at h
  unfold epoll_pwait_spec
  apply bind_unmodeled2 _ _ i m i m [] (input_ok i m)
  apply bind_unmodeled2 _ _ i m m m [] (get_model_ok i m)
  cases ho : epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize with
  | none =>
    dsimp only
    exact unmodeled_intro i m
  | some r =>
    rw [ho] at h
    dsimp only at h
    exact (check_ret_only_no_unmodeled _ _ _ _ h).elim

/-- Every run the spec admits is one the checker accepts.  Rocq:
`check_epoll_pwait_complete_ok`. -/
theorem check_epoll_pwait_complete_ok (i : SyscallInput)
    (epfd events maxevents32 sigmask sigsetsize : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : epoll_pwait_spec epfd events maxevents32 sigmask sigsetsize i m (Ok eff m' evs)) :
    check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m = CheckOk m' evs := by
  unfold epoll_pwait_spec at h
  have h := bind_input_model_inv _ i m _ h
  unfold check_epoll_pwait
  cases ho : epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize with
  | none =>
    rw [ho] at h
    dsimp only at h
    simp only [Monad.unmodeled] at h
    cases h
  | some r =>
    rw [ho] at h
    dsimp only at h ⊢
    simp only [Monad.pure, outcome.Ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- Every run the spec leaves unmodeled is one the checker declines,
whatever effect it is shown.  Rocq:
`check_epoll_pwait_complete_unmodeled`. -/
theorem check_epoll_pwait_complete_unmodeled (i : SyscallInput)
    (epfd events maxevents32 sigmask sigsetsize : word)
    (m : Model) (eff : SyscallEffect)
    (h : epoll_pwait_spec epfd events maxevents32 sigmask sigsetsize i m Unmodeled) :
    check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m = CheckUnmodeled := by
  unfold epoll_pwait_spec at h
  have h := bind_input_model_inv _ i m _ h
  unfold check_epoll_pwait
  cases ho : epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize with
  | none => rfl
  | some r =>
    rw [ho] at h
    dsimp only at h
    simp only [Monad.pure] at h
    cases h

/-- The one effect the spec admits for `epoll_pwait` on this input and
model, or `Unmodeled` where it admits none.  Mirrors
`epoll_pwait_witness` in
`theories/LinuxProcessSem/Checks/Witness/Fs/EventPoll.v`. -/
def epoll_pwait_witness (epfd events maxevents32 sigmask sigsetsize : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  match epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize with
  | none => Unmodeled
  | some r => ret_outcome r m

/-- The witness is a run of the spec.  Rocq: `epoll_pwait_witness_ok`. -/
theorem epoll_pwait_witness_ok (epfd events maxevents32 sigmask sigsetsize : word)
    (i : SyscallInput) (m : Model) :
    epoll_pwait_spec epfd events maxevents32 sigmask sigsetsize i m
      (epoll_pwait_witness epfd events maxevents32 sigmask sigsetsize i m) := by
  unfold epoll_pwait_spec epoll_pwait_witness
  apply bind_step _ _ i m i m _ (input_ok i m)
  apply bind_step _ _ i m m m _ (get_model_ok i m)
  cases ho : epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize with
  | none => exact unmodeled_intro i m
  | some r => exact pure_ok _ i m

/-- `epoll_pwait` accepts only with the model it was given.  Mirrors
`check_epoll_pwait_frame` in
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`. -/
theorem check_epoll_pwait_frame (i : SyscallInput)
    (epfd events maxevents32 sigmask sigsetsize : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_epoll_pwait at h
  vm_frame2 h

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.EventPoll
