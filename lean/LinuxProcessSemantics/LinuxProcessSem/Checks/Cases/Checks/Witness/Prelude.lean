import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap
import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open
import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.File

/-! # Checks.Cases.Checks.Witness.Prelude — the witnesses' shared helpers, exercised

Pins over `Checks.Witness.Prelude`, the twin of
`theories/LinuxProcessSem/Checks/Witness/Prelude.v`.  The Rocq tree has no
check file for it — its lemmas are stated in the file itself — so this file
mirrors nothing: these are the Lean tree's tests for what the twin ports,
placed where every pin in this tree lives so that `tools/check_lean_pins.py`
reads them and the twin holds only definitions and their Rocq-twin lemmas.
Not part of the trusted specification.

What the helpers decide is the SHAPE of a witness outcome: which errno the
failure branch takes and from where, that the return-only outcome moves
nothing, and that a program's events are the ones it emitted.  Each pin
states one such decision on a concrete value beside the line of Linux that
makes it the kernel's, or says that it makes no kernel claim; the
refutations are the concrete lies a witness could otherwise tell — an errno
drawn from outside the injectable set, an emitted event dropped.  The last
section elaborates one `srw` with both tactics of that name in scope, which
is the situation `Checks/Progress.lean` and every witness check file are
in. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Witness.Prelude

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap
open LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.File
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

section ErrnoBranch

/-! ## The failure branch: `witness_errno` and the head of the set

A witness that fails does so with the HEAD of its arm's injectable set,
through `errno_head_witness`, and `witness_errno` names the head the sets
in this tree share.  The pins fix the value against the header and
the head against each set, so that renumbering the constant or reordering
a set fails here and not in a witness proof three files away. -/

/-- `witness_errno` is `ENOMEM`, 12.
kernel: include/uapi/asm-generic/errno-base.h:ENOMEM@v6.18.46 -/
theorem witness_errno_is_enomem : witness_errno = 12 := by decide

/-- It heads `mmap`'s injectable set, whose failure branch it is.  The arm
draws it beside every anonymous placement, and -ENOMEM is what `do_mmap`
returns there when `__get_unmapped_area` (mm/mmap.c) finds no room for
`len` below `TASK_SIZE`, or when the commit charge fails in
`__vm_enough_memory` of mm/util.c — the address-space and accounting
refusals the model does not track — so the errno the witness fails with
is one Linux gives.
kernel: mm/mmap.c:do_mmap; mm/mmap.c:__get_unmapped_area@v6.18.46 -/
theorem witness_errno_heads_mmap_errnos : mmap_errnos.head? = some witness_errno := by decide

/-- ...and `mprotect`'s.  The arm draws it only on a MAPPED range being
made accessible — `Sys/Mm/Mprotect.lean` declines an unmapped one, so
`do_mprotect_pkey`'s -ENOMEM at a missing vma is not the branch modeled —
and on the modeled branch the -ENOMEM is `mprotect_fixup`'s
(mm/mprotect.c), refused by `may_expand_vm` (mm/mmap.c) over the limits
or by `security_vm_enough_memory_mm` (security/security.c) over the
commit charge, neither of which the model tracks.
kernel: mm/mprotect.c:mprotect_fixup@v6.18.46 -/
theorem witness_errno_heads_mprotect_errnos :
    mprotect_errnos.head? = some witness_errno := by decide

/-- ...and `openat`'s and `dup`'s, the two other sets in the tree headed by
it, whose Rocq witnesses draw it the same way: a reordering of either set
fails here, before a witness twin lands to fail on it.
model: the head of `openat_errnos`; each member's kernel reading is on `Sys/Fs/Open.lean` -/
theorem witness_errno_heads_openat_errnos : openat_errnos.head? = some witness_errno := by
  decide

/-- The same for `dup`'s set.
model: the head of `dup_errnos`; each member's kernel reading is on `Sys/Fs/File.lean` -/
theorem witness_errno_heads_dup_errnos : dup_errnos.head? = some witness_errno := by decide

/-- The branch is available: the head is a member, so the failure outcome
the mmap witness exhibits is one the arm's `errno_from` draw admits.
kernel: mm/mmap.c:do_mmap@v6.18.46 -/
theorem errno_head_witness_at_mmap (i : SyscallInput) (m : Model) :
    errno_from mmap_errnos i m (Ok witness_errno m []) :=
  errno_head_witness ENOMEM [] i m

/-- The set is not only its head: `errno_from_witness` draws any member,
and -EMFILE is `dup`'s second, the answer `alloc_fd` gives when the table
is full.  A witness that needed it — none in the tree does yet — would
draw it from here.
kernel: fs/file.c:alloc_fd@v6.18.46 -/
theorem errno_from_witness_at_a_later_member (i : SyscallInput) (m : Model) :
    errno_from dup_errnos i m (Ok EMFILE m []) :=
  errno_from_witness dup_errnos EMFILE i m (List.Mem.tail _ (List.Mem.head _))

/-- The lie: -EBADF is an answer `mmap` really gives — `ksys_mmap_pgoff`'s
`fget` failing on a file-backed request — but its one source there is
behind `!(flags & MAP_ANONYMOUS)`, the path `Sys/Mm/Mmap.lean` declines,
so on the anonymous path the arms model it is not the kernel's answer, and
no witness may draw it from a set that does not name it.  The spec-side
refusal, with the probe behind it, is `rw_grant_ebadf_rejected` in
`Checks/Cases/Mm/Mmap.lean`.
kernel: mm/mmap.c:ksys_mmap_pgoff@v6.18.46 -/
theorem errno_from_witness_refuses_an_unlisted_errno (i : SyscallInput) (m : Model) :
    ¬ errno_from mmap_errnos i m (Ok EBADF m []) := by
  rintro ⟨e, he, heq⟩
  injection heq with he' hm hevs
  subst he'
  simp only [mmap_errnos, List.mem_singleton] at he
  exact absurd he (by decide)

end ErrnoBranch

section ReturnOnly

/-! ## `ret_outcome`: the return-only outcome

`SYSCALL_DEFINE1(close, unsigned int, fd)` (fs/open.c, Linux v6.18.46) is
the shape: a return and nothing else, no `copy_to_user` in its body.  The
outcome a witness for such an arm exhibits carries the return, no write,
no zeroed or unmapped range, no copy, an empty ledger, the model it was
given and no event.  `Checks/Sys/Prelude.lean`'s `check_ret_only` is the
same shape as an acceptor, and the two must agree, or an arm's
`ca_receptive` and `ca_complete_ok` fields could not both be discharged. -/

variable (r : word) (m : Model)

/-- The witness's return-only outcome is one the return-only acceptor
admits, and the acceptor's answer is the model the witness was GIVEN and
no event: the right-hand side names `m` and `[]`, not the outcome's own
`m'` and `evs`, which the acceptor would pass through unread — a witness
that halted the model or emitted an event satisfies the pass-through form
and fails this one.
model: `Prelude.check_ret_only_ok_iff` on the effect `ret_outcome`
carries; no kernel behaviour is claimed beyond the section's -/
theorem check_ret_only_admits_ret_outcome (eff : SyscallEffect) (m' : Model) (evs : List event)
    (h : ret_outcome r m = Ok eff m' evs) : check_ret_only eff r m' evs = CheckOk m [] := by
  simp only [ret_outcome, outcome.Ok.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- A return-only witness is never a decline: an arm that answers with
one is on the modeled surface.
model: `ret_outcome` is an `Ok`; no kernel behaviour is claimed -/
theorem ret_outcome_never_declines : ret_outcome r m ≠ Unmodeled := by
  unfold ret_outcome
  exact nofun

end ReturnOnly

section Steps

/-! ## The steps a witness proof takes

`bind_step` carries a continuation's outcome, of either shape, past a
reader that emits nothing; `emit_pure_ok` is the one step that emits.
The pins fix each on the shapes the channel `read` witness produces — a
`ReadEv` for the byte it delivers — and refuse the accounting a witness
could get wrong, the emitted event dropped. -/

variable (i : SyscallInput) (m : Model) (ch : word) (b : byte)

/-- `bind_step` on the `Ok` shape: a reader that emits nothing, then the
continuation's answer, is the continuation's answer with its events.
model: `Monad.bind` read through `bind_step`; no kernel behaviour is
claimed -/
theorem bind_step_carries_an_ok :
    bind get_model (fun m0 => (emit [ReadEv ch b] ;; Monad.pure m0)) i m
      (Ok m m [ReadEv ch b]) :=
  bind_step get_model _ i m m m _ (get_model_ok i m) (emit_pure_ok [ReadEv ch b] m i m)

/-- ...and on the `Unmodeled` shape: a decline behind the same reader is a
decline of the whole program.
model: `Monad.bind` read through `bind_step`; no kernel behaviour is
claimed -/
theorem bind_step_carries_a_decline :
    bind get_model (fun _ => (unmodeled : Sys SyscallEffect)) i m Unmodeled :=
  bind_step get_model _ i m m m Unmodeled (get_model_ok i m) (unmodeled_intro i m)

/-- ...and with a first step that UPDATES the model: `bind_step` carries the
step's post-model into the continuation, which is where the halt a witness
for `exit` sets has to travel.  The two pins above take the step at
`get_model`, whose post-model is the pre-model, and could not tell.
model: `Monad.bind` read through `bind_step` over `Monad.modify`; no kernel behaviour is claimed -/
theorem bind_step_carries_a_model_update :
    bind (modify (with_halted ch)) (fun _ => Monad.pure (mkEffect (Z_to_bv 64 0) [] [])) i m
      (Ok (mkEffect (Z_to_bv 64 0) [] []) (with_halted ch m) []) :=
  bind_step (modify (with_halted ch)) _ i m () (with_halted ch m) _
    (modify_ok (with_halted ch) i m) rfl

/-- One emitted event is the program's one event.
model: `Monad.emit` then `Monad.pure`, read by `bind`; no kernel behaviour
is claimed -/
theorem emit_pure_ok_at_one_event :
    (emit [ReadEv ch b] ;; Monad.pure (mkEffect (Z_to_bv 64 1) [] [])) i m
      (Ok (mkEffect (Z_to_bv 64 1) [] []) m [ReadEv ch b]) :=
  emit_pure_ok [ReadEv ch b] _ i m

/-- The lie: the event dropped.  The program emitted it, so an outcome
with no events is not one `bind` admits.
model: the events `bind` admits are the concatenation of both steps'; no
kernel behaviour is claimed -/
theorem emit_pure_refuses_a_dropped_event :
    ¬ (emit [ReadEv ch b] ;; Monad.pure (mkEffect (Z_to_bv 64 1) [] [])) i m
        (Ok (mkEffect (Z_to_bv 64 1) [] []) m []) := by
  rintro ⟨u, m1, evs1, evs2, hemit, hpure, hevs⟩
  -- `hemit` and `hpure` are the two steps' equations, `Ok u m1 evs1 = Ok () m
  -- [ReadEv ch b]` and `Ok _ m evs2 = Ok _ m1 []`; only their event
  -- components matter, and `[] = [ReadEv ch b] ++ []` is refuted by shape.
  have h1 : evs1 = [ReadEv ch b] := (outcome.Ok.inj hemit).2.2
  have h2 : evs2 = [] := (outcome.Ok.inj hpure).2.2
  rw [h1, h2] at hevs
  simp only [List.append_nil, reduceCtorEq] at hevs

end Steps

section Tactic

/-! ## `srw`, with both tactics of that name in scope

`Checks/Sys/Prelude.lean` defines `srw` for the checkers and
`Checks/Witness/Prelude.lean` defines it for the witnesses, as Rocq does
once per file.  This file imports both, so the text `srw h` parses to a
choice of two alternatives, of which Lean elaborates ONE — the alternative
the parser lists first — and never the other: a failure inside the first
is reported, not a reason to try the second.  So these examples pin that
the text still parses and closes with both in scope, which is the
situation `Checks/Progress.lean` and any witness check file importing the
checker prelude are in; they cannot pin the witnesses' expansion, and
`Checks/Cases/Checks/Witness/Uaccess.lean`, where only that one is in
scope, does.  The example is the goal shape a witness proof hands the
tactic — a scrutinee equation whose rewrite exposes a redex the closing
step needs reduced. -/

/-- `srw`: rewrite, then re-reduce the redex the rewrite exposed.
model: the tactic's own expansion; no kernel behaviour is claimed -/
example (x y z : Nat) (h : x = z) (hy : z + 1 = y) : (fun n => n + 1) x = y := by
  srw h
  rw [hy]

/-- `srw … at h`: the same on a hypothesis.
model: the tactic's own expansion; no kernel behaviour is claimed -/
example (x y : Nat) (h : x = 3) (hx : (fun n => n + 1) x = y) : 3 + 1 = y := by
  srw h at hx
  exact hx

end Tactic

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Witness.Prelude
