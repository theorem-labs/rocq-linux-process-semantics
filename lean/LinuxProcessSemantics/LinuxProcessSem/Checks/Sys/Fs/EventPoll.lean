import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.EventPoll
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Fs.EventPoll — epoll_create1 (20), epoll_ctl (21), epoll_pwait (22): checker, witness, frame

Starts from `theories/LinuxProcessSem/Checks/Sys/Fs/EventPoll.v` — the three
checkers and their twelve soundness and completeness lemmas — and, in the
same file, `theories/LinuxProcessSem/Checks/Witness/Fs/EventPoll.v` (the
three witnesses and their `*_witness_ok` lemmas) and the three per-checker
frame lemmas that `theories/LinuxProcessSem/Checks/VmMapsDisjoint.v` states
for `check_epoll_create1`, `check_epoll_ctl` and `check_epoll_pwait`.
Those names and obligations are retained, but the executable definitions
follow Lean's additional declines. The answer-set helper and the
`choose` proof steps prepare #1925's representation; `ep_join` currently
permits only the base Linux answer, and only when every QEMU answer agrees.
References to Rocq names below identify these original counterparts,
not a claim that their current bodies match. Not
part of the trusted specification: nothing here claims anything about
Linux that `Sys/Fs/EventPoll.lean` does not already claim.  The
definitions are the executable side of that spec and the lemmas say the
two sides agree, in both directions.  Its pins are
`Checks/Cases/Checks/Sys/Fs/EventPoll.lean`.

THE BASELINE NAMED ABOVE is the commit the spec twin names and an ancestor
of this history; the two `EventPoll.v` files are byte-identical there to
`f44244ad6b80`, the commit the port plan names, which stopped being an
ancestor of any branch when that day's work was rebase-merged, and neither
had been touched at that baseline since `c56338cde` (2026-08-31, #509)
landed them.  So the header names the commit a reader can `git show` rather than one they
cannot reach.  The third Rocq file, `VmMapsDisjoint.v`, moves with every
arm; the three frame lemmas twinned below are the ones at its lines
1727-1748 at that baseline.  No tool reads this header: the parity sweeps
stop at `Sys/` and `Checks/Cases/`, so the claim that the mirrored names below
are the Rocq names is held by review alone.

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

WHAT THE CHECKER RESTS ON.  All three arms write no user memory, so each
acceptor is the spec's own computation plus a membership test of the
return value in the answers it admits (one equality for `epoll_create1`),
and `check_ret_only` and `check_ep_answer` carry the rest of the
obligation: each rejects any effect with a non-empty write, zero, unmap,
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

THE PROOFS retain Rocq's split on the outcome and adapt the answered
branch to the Lean join. Each direction splits the outcome
function — `none`, then `some r` — and uses the corresponding helper:
`check_ret_only_ok_iff` for `epoll_create1`'s two `Ok` directions and
`check_ep_answer_ok_iff` with `bind_choose_iff` for `epoll_ctl`'s and
`epoll_pwait`'s. `check_ret_only_no_unmodeled` and
`check_ep_answer_no_unmodeled` rule out a checker decline in an answered
branch, while the spec proof rules it out by constructor mismatch. Rocq's
`destruct ... eqn:Ho; cbv iota` is `cases ho : ... with` followed by
`rw [ho] at h` and `dsimp only`, for the reason `Checks/Sys/Fs/Sync.lean`
gives for generalising its lookup: `cases` on the outcome substitutes the
goal but not a hypothesis that still mentions the scrutinee.  The two-reader arms open with the
checker prelude's `bind_input_model_inv` where Rocq's open with
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

/-! Proof steps for the imported lock definitions in `Sys/Fs/EventPoll.lean`.
These support the mutation allowlist's decision-tree arguments; they are
not concrete syscall pins. They live on the checker side because the
Rocq spec has no corresponding helper lemmas. -/

/-- The word-length helper preserves the integer overlap traversal within
its unsigned range. The callers supply 16 bytes or a positive event count
bounded by EP_MAX_EVENTS times 16; access_okb alone supplies no lower bound. -/
theorem qemu_lock_load_write_free_eq
    (res : List (word × word)) (wmp : word → Option byte)
    (a : word) (len : Int) (h0 : 0 ≤ len) (h1 : len < 2 ^ 64) :
    LinuxProcessSemantics.LinuxProcessSem.Sys.Net.Socket.load_write_free
        res wmp a (Z_to_bv 64 len) =
      res.all (fun r =>
        let lo := max (bv_unsigned a) (bv_unsigned r.1)
        let hi := min (bv_unsigned a + len)
          (bv_unsigned r.1 + bv_unsigned r.2)
        (List.range (hi - lo).toNat).all (fun k =>
          (wmp (Z_to_bv 64 (lo + Int.ofNat k))).isNone)) := by
  unfold LinuxProcessSemantics.LinuxProcessSem.Sys.Net.Socket.load_write_free
  rw [BvBase.bv_unsigned_Z_to_bv_small len h0 h1]

/-- The sure gate's conjunct justifies commuting the two lock tests.
The sure gate includes the may gate as a conjunct. -/
theorem qemu_lock_sure_implies_may (i : SyscallInput) (m : Model) (write : Bool)
    (a : word) (len : Int) (h : qemu_lock_sure i m write a len = true) :
    qemu_lock_may i write a len = true := by
  simp only [qemu_lock_sure, Bool.and_eq_true] at h
  exact h.1.1.2

/-- The fault-list form preserves the lock's possible outcomes.
These are equivalent decision trees for the conservative lock bounds. -/
theorem qemu_after_lock_eq_fault_form (i : SyscallInput) (m : Model) (write : Bool)
    (a : word) (len : Int) (later : Option (List word)) :
    qemu_after_lock i m write a len later =
      (let fault := if qemu_lock_sure i m write a len then [] else [errno_ret EFAULT]
       if qemu_lock_may i write a len then
         match later with
         | some rs => some (fault ++ rs)
         | none => none
       else some fault) := by
  cases hm : qemu_lock_may i write a len
  · simp [qemu_after_lock, qemu_lock_sure, hm]
  · cases hs : qemu_lock_sure i m write a len <;>
      cases later <;> simp [qemu_after_lock, hm, hs]

theorem ep_answerb_spec (o : word × List word) (r : word) :
    ep_answerb o r = true ↔ ep_answer o r := by
  simp only [ep_answerb, ep_answer, Bool.or_eq_true, bv_eqb_eq, List.any_eq_true]
  constructor
  · rintro (h | ⟨x, hx, heq⟩)
    · exact Or.inl h
    · exact Or.inr (heq ▸ hx)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨r, h, rfl⟩

/-- `check_ret_only` for an answer set: accept a return-only effect whose
return is one of the answers `o` names (`ep_answer`). Lean's `ep_join`
produces a singleton Linux answer only when QEMU agrees; this generic
checker, witness and all four proof directions consume that joined outcome.
The base Rocq checker has no answer-set helper; #1925 adds its counterpart
to `theories/LinuxProcessSem/Checks/Sys/Fs/EventPoll.v`. -/
def check_ep_answer (o : word × List word) (eff : SyscallEffect) (m : Model) : check_result :=
  if ep_answerb o eff.eff_ret then check_ret_only eff eff.eff_ret m [] else CheckReject

theorem check_ep_answer_ok_iff (o : word × List word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) :
    check_ep_answer o eff m = CheckOk m' evs ↔
      ∃ r, ep_answer o r ∧ eff = mkEffect r [] [] ∧ m' = m ∧ evs = [] := by
  constructor
  · intro h
    unfold check_ep_answer at h
    split at h
    · rename_i hr
      obtain ⟨heff, hm, hevs⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact ⟨eff.eff_ret, (ep_answerb_spec o eff.eff_ret).mp hr, heff, hm, hevs⟩
    · cases h
  · rintro ⟨r, hr, rfl, rfl, rfl⟩
    unfold check_ep_answer
    rw [ite_eq_left ((ep_answerb_spec o r).mpr hr)]
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

theorem check_ep_answer_no_unmodeled (o : word × List word) (eff : SyscallEffect) (m : Model) :
    check_ep_answer o eff m ≠ CheckUnmodeled := by
  unfold check_ep_answer
  split
  · exact check_ret_only_no_unmodeled eff eff.eff_ret m []
  · intro h
    cases h

/-! ## epoll_create1 (20) -/

/-- Accept an observed `epoll_create1` effect exactly when
`epoll_create1_spec` admits it: `CheckUnmodeled` where the spec declines
(a well-formed flag word, whose success arm is not modeled, or a word
QEMU's flag translation may accept), and otherwise `check_ret_only`
against the one return the spec names, with the model handed back
unchanged and no event.  Mirrors `check_epoll_create1` in
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
for which `fd_can_poll` returns `none`, the /dev/null and /dev/urandom
targets the spec leaves unanswered until each has its own probe, and an
input where either computation declines or its answers disagree), and otherwise
`check_ep_answer` against the answers the spec names — Linux's errno,
from the event struct's readability, then the two lookups, then the
target's `->poll`, then -EINVAL, in the kernel's order. QEMU must agree
with that answer before the join reaches this checker.
The syscall input is an argument because the arm reads
user memory through it.  Mirrors `check_epoll_ctl` in
`theories/LinuxProcessSem/Checks/Sys/Fs/EventPoll.v`. -/
def check_epoll_ctl (i : SyscallInput) (epfd op32 tfd ev : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match epoll_ctl_outcome i m epfd op32 tfd ev with
  | none => CheckUnmodeled
  | some r => check_ep_answer r eff m

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
    rw [check_ep_answer_ok_iff] at h
    obtain ⟨r0, hr, rfl, rfl, rfl⟩ := h
    exact (bind_choose_iff _ _ _ _ _).mpr ⟨r0, hr, pure_ok _ i _⟩

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
    exact (check_ep_answer_no_unmodeled _ _ _ h).elim

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
    rw [bind_choose_iff] at h
    obtain ⟨r0, hr, hp⟩ := h
    simp only [Monad.pure, outcome.Ok.injEq] at hp
    obtain ⟨rfl, rfl, rfl⟩ := hp
    exact (check_ep_answer_ok_iff _ _ _ _ _).mpr ⟨r0, hr, rfl, rfl, rfl⟩

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
    rw [bind_choose_iff] at h
    obtain ⟨_, _, hp⟩ := h
    cases hp

/-- The effect of the Linux answer the spec admits for `epoll_ctl` on
this input and model, or `Unmodeled` where it admits none.  Mirrors
`epoll_ctl_witness`
in `theories/LinuxProcessSem/Checks/Witness/Fs/EventPoll.v`, in Rocq's
argument order (the file header says why). -/
def epoll_ctl_witness (epfd op32 tfd ev : word) (i : SyscallInput) (m : Model) :
    outcome SyscallEffect :=
  match epoll_ctl_outcome i m epfd op32 tfd ev with
  | none => Unmodeled
  | some r => ret_outcome r.1 m

/-- The witness is a run of the spec.  Rocq: `epoll_ctl_witness_ok`. -/
theorem epoll_ctl_witness_ok (epfd op32 tfd ev : word) (i : SyscallInput) (m : Model) :
    epoll_ctl_spec epfd op32 tfd ev i m (epoll_ctl_witness epfd op32 tfd ev i m) := by
  unfold epoll_ctl_spec epoll_ctl_witness
  apply bind_step _ _ i m i m _ (input_ok i m)
  apply bind_step _ _ i m m m _ (get_model_ok i m)
  cases ho : epoll_ctl_outcome i m epfd op32 tfd ev with
  | none => exact unmodeled_intro i m
  | some r => exact (bind_choose_iff _ _ _ _ _).mpr ⟨r.1, Or.inl rfl, pure_ok _ i m⟩

/-- `epoll_ctl` accepts only with the model it was given.  Mirrors
`check_epoll_ctl_frame` in
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`. -/
theorem check_epoll_ctl_frame (i : SyscallInput) (epfd op32 tfd ev : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_epoll_ctl i epfd op32 tfd ev eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_epoll_ctl check_ep_answer at h
  vm_frame2 h

/-! ## epoll_pwait (22) -/

/-- Accept an observed `epoll_pwait` effect exactly when
`epoll_pwait_spec` admits it: `CheckUnmodeled` where `epoll_pwait_outcome`
declines -- a signal mask that would be installed, a closed epfd beside
an out-of-bounds count or an `access_ok`-refused range, where
fs/eventpoll.c:do_epoll_wait answers -EBADF from v6.15 (read at v6.18.46),
-EINVAL for bad counts at v6.14 and -EFAULT for refused ranges at v6.1
(access_ok against TASK_SIZE), or an open epfd beside a range past
`TASK_SIZE` that `LONG_MAX` admits -- and otherwise `check_ep_answer`
against the answers the outcome names.  `timeout` is not an argument, as
it is not one of the spec's: no arm reads it.
Mirrors `check_epoll_pwait` in
`theories/LinuxProcessSem/Checks/Sys/Fs/EventPoll.v`. -/
def check_epoll_pwait (i : SyscallInput) (epfd events maxevents32 sigmask sigsetsize : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize with
  | none => CheckUnmodeled
  | some r => check_ep_answer r eff m

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
    rw [check_ep_answer_ok_iff] at h
    obtain ⟨r0, hr, rfl, rfl, rfl⟩ := h
    exact (bind_choose_iff _ _ _ _ _).mpr ⟨r0, hr, pure_ok _ i _⟩

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
    exact (check_ep_answer_no_unmodeled _ _ _ h).elim

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
    rw [bind_choose_iff] at h
    obtain ⟨r0, hr, hp⟩ := h
    simp only [Monad.pure, outcome.Ok.injEq] at hp
    obtain ⟨rfl, rfl, rfl⟩ := hp
    exact (check_ep_answer_ok_iff _ _ _ _ _).mpr ⟨r0, hr, rfl, rfl, rfl⟩

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
    rw [bind_choose_iff] at h
    obtain ⟨_, _, hp⟩ := h
    cases hp

/-- The effect of the Linux answer the spec admits for `epoll_pwait` on
this input and model, or `Unmodeled` where it admits none.  Mirrors
`epoll_pwait_witness` in
`theories/LinuxProcessSem/Checks/Witness/Fs/EventPoll.v`. -/
def epoll_pwait_witness (epfd events maxevents32 sigmask sigsetsize : word)
    (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  match epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize with
  | none => Unmodeled
  | some r => ret_outcome r.1 m

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
  | some r => exact (bind_choose_iff _ _ _ _ _).mpr ⟨r.1, Or.inl rfl, pure_ok _ i m⟩

/-- `epoll_pwait` accepts only with the model it was given.  Mirrors
`check_epoll_pwait_frame` in
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`. -/
theorem check_epoll_pwait_frame (i : SyscallInput)
    (epfd events maxevents32 sigmask sigsetsize : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_epoll_pwait check_ep_answer at h
  vm_frame2 h

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.EventPoll
