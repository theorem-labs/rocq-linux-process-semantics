import LinuxProcessSemantics.LinuxProcessSem.Sys.Drivers.Char.Random
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Drivers.Char.Random — the getrandom (278) checker and its witness

Mirrors `theories/LinuxProcessSem/Checks/Sys/Drivers/Char/Random.v` (the
executable checker `check_getrandom`, its helper `check_getrandom_zero`,
and the four soundness and completeness proofs) and
`theories/LinuxProcessSem/Checks/Witness/Drivers/Char/Random.v` (the
receptiveness witness `getrandom_witness` and its proof), in that order,
as two sections of one module: the ticket that ports both,
C-Drivers-Char-Random, names this one file, so the witness lives here
rather than under a `Checks/Witness/` mirror path, as the clock_gettime
and getgroups ports did before it.  Both Rocq files are byte-identical at
a71fd38a, at the port plan's common baseline f44244ad — which is not an
ancestor of this history — and at the day tip; the header names the one
the `Sys/` twin names.

Not part of the trusted specification.  The trusted definition is
`Sys/Drivers/Char/Random.lean`'s `getrandom_spec`; the proofs here relate
the executable `check_getrandom` and the witness to it, and they are what
let the checker's answer stand in for the relation.  The pins on the
checker and the witness are
`Checks/Cases/Checks/Sys/Drivers/Char/Random.lean`.

THE CHECKER IS THE SPEC, GATE FOR GATE.  Its three leading gates — the
flag word, the transfer bound and the destination walk — are spelled
exactly as `getrandom_spec` spells them, so that one `generalize` splits
the checker and the spec together in every proof below; the nonzero /
zero split and the small-request bound are the spec's own `if`s for the
same reason.  What the checker adds is the executable test of the
effect, which the spec states as a `choose` guard and the checker as a
`Bool` chain: Rocq's `bv_eqb` stays `bv_eqb`, and Rocq's `Z.eqb` and
`Z.leb` on the delivered count are `decide` of the `Int` proposition the
spec's guard states, so that one reflection lemma, `decide_eq_true_eq`,
turns each conjunct back into the guard.  `getrandom_errnos` is tested
through the prelude's `errno_ret_in`, as in Rocq.

THE PROOFS keep Rocq's case structure.  Rocq walks the gates with
`destruct … eqn:` and `srw`; here a gate shared by the checker and the
spec is `generalize`d out of both and split with `cases`, because a
`split` cannot find an `if` that is applied to `i m o`, and the
small-request bound — a decided `Int` proposition on both sides — is a
`by_cases` followed by `simp only [h, ↓reduceIte]`.  The effect is taken
apart by `split at h` on the checker's own `match`, one goal per arm, and
the spec's side is read through the `Monad` `iff` lemmas
(`bind_input_iff`, `bind_choose_iff`, `alt_iff`, `pure_iff`), so no proof
here unfolds `bind` by hand.  The zero-byte arm is factored the way Rocq
factors it: `check_getrandom_zero_sound` and
`check_getrandom_zero_no_unmodeled` are Rocq's helpers under Rocq's
names, and `check_getrandom_zero_complete` and
`zero_arm_never_unmodeled` are the two Lean-only helpers that let the
completeness proofs close both range verdicts by one application each —
Rocq's proofs reach the same facts by `hall`/`inv_ok` at the use site.

THE FRAME LEMMA `check_getrandom_frame` is Rocq's
`VmMapsDisjoint.check_getrandom_frame`.  The CHECK definition of done
assigns it to the registration step; it is stated here anyway, as the
four checker ports before this one did, because it depends on nothing
but `check_getrandom` — every accepting arm hands back the model it was
given — and the alternation that consumes it lives in a file that
imports the table, which imports this file.  Nothing else of the
registration is here: no `CheckedArm`, no table row, no `arm_unfold`
lemma. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Drivers.Char.Random

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess
open LinuxProcessSemantics.LinuxProcessSem.Sys.Drivers.Char.Random
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude

/-! ## The checker — `Checks/Sys/Drivers/Char/Random.v` -/

/-- The zero-byte request's acceptor, parameterised by the range verdict
`r0` the caller has already decided: `0` where the range test of
`import_ubuf` passes, `-EFAULT` where it does not (lib/iov_iter.c:1437-1438,
Linux v6.18.46; the test is `__access_ok`, include/asm-generic/access_ok.h
at the same version).  Accepts a bare return of `r0` or of any
errno in `getrandom_errnos` — the -EINTR `arch_do_signal_or_restart`
(arch/riscv/kernel/signal.c:438-443, v6.18.46) makes of the -ERESTARTSYS
`wait_for_random_bytes` returns (drivers/char/random.c:136-147, v6.18.46)
when the handler lacks SA_RESTART, which the syscall can answer at
:1403-1405 BEFORE it imports the buffer at :1408, whatever the range
verdict — with no write, no zero-fill, no unmap, no copy and no copy-in;
refuses everything else, and never declines
(`check_getrandom_zero_no_unmodeled`).  Rocq: `Random.check_getrandom_zero`. -/
def check_getrandom_zero (r0 : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | .mkEffectU r [] [] [] [] [] =>
      if errno_ret_in getrandom_errnos r || bv_eqb r r0 then CheckOk m [] else CheckReject
  | _ => CheckReject

/-- Accept an observed `getrandom(buf, cap, flags)` effect exactly when
`getrandom_spec buf cap flags` admits it, deciding the gates in the order
`SYSCALL_DEFINE3(getrandom, char __user *, ubuf, size_t, len, unsigned int, flags)`
(drivers/char/random.c:1385-1412, Linux v6.18.46) decides them:

- THE FLAG WORD first (:1390), as the spec: a word other than 0 and
  GRND_NONBLOCK is `CheckUnmodeled`, before any argument is read.
- THE TRANSFER BOUND next: a `cap` above `Uaccess.rw_bytes_max` is
  `CheckUnmodeled`.  The bound is the model's, not Linux's — Linux clamps
  only at MAX_RW_COUNT in `import_ubuf` (lib/iov_iter.c:1435-1436,
  v6.18.46) and delivers everything below it — so the decline costs
  every request between 128 KiB and that clamp; `rw_bytes_max`'s own
  docstring in `Sys/Uaccess.lean` carries that cost and says why the
  gate stands in front of the walk below.
- THE DESTINATION WALK: a `cap`-byte destination the writable view does
  not hold in full is `CheckUnmodeled` — Linux would answer the short
  count or the -EFAULT of `get_random_bytes_user`'s
  `return ret ? ret : -EFAULT` (drivers/char/random.c:481, v6.18.46), and
  the spec declines the program bug rather than choose.  The walk is
  `read_bytes_map`'s, which steps addresses modulo 2^64 and runs no range
  test, so a destination the view holds past `TASK_SIZE` or across the
  top of the word is walked and its delivery accepted where Linux answers
  -EFAULT; that admission is the spec's, inherited from the bare walk and
  recorded in `bugs/wrapping-walks-unbounded-segments.md`.
- A NONZERO REQUEST OF AT MOST `getrandom_small_max` BYTES: exactly one
  write, at `buf`, of exactly `cap` bytes, with the return equal to the
  delivered length; no errno, no short count — the loop of
  `get_random_bytes_user` (drivers/char/random.c:460-476, v6.18.46) tests
  `signal_pending` only after a whole page has landed (:471-473), and a
  request of at most 32 bytes never enters it (:455-458), the argument
  on `getrandom_small_max`.  That any count is answered at all — that
  the wait at :1403 is not entered — is the seeded-pool premise
  `bugs/getrandom-answers-rest-on-a-seeded-pool.md` records; the checker
  tests no flag word on that arm because the spec tests none there.
- A LARGER NONZERO REQUEST: a bare errno from `getrandom_errnos`, or one
  write at `buf` of between 1 and `cap` bytes with the return equal to its
  length (the `signal_pending` break at :471-473 returns the count so
  far, :481).
- A ZERO-BYTE REQUEST: `check_getrandom_zero` with the range verdict
  `access_okb buf 0` decides — 0 or -EFAULT, the range test `import_ubuf`
  runs (lib/iov_iter.c:1437-1438, v6.18.46) through `__access_ok`
  (include/asm-generic/access_ok.h, v6.18.46) on the empty range — beside
  the -EINTR the helper always admits.  riscv's own `access_ok`
  (arch/riscv/include/asm/uaccess.h, v6.18.46) is that same test: under
  CONFIG_RISCV_ISA_SUPM it first strips the pointer-masking tag bits a
  task has asked for, and no task in this model has asked for any — the
  two writers of the task's mask, prctl's PR_SET_TAGGED_ADDR_CTRL and
  ptrace's PTRACE_SETREGSET, are declined, the argument beside
  `access_okb` in `State/Readers.lean` and `State.v` — so
  `__untagged_addr_remote` hands the address back unchanged, and outright
  where the hart lacks Supm; without that option the generic macro
  applies as written.  What `access_okb` sees is the comparison alone:
  that its exactness rests on that closed world, and that `__access_ok`
  has a branch ahead of the comparison the model has no counterpart for,
  are `bugs/access-okb-closed-world.md` and
  `bugs/access-okb-early-return-unmodeled.md`.

Every accepting arm hands back the model unchanged and no event.  Which
kernel lines make each shape the only admissible one, and why the bound
is 256 rather than the page the pinned kernel would allow, is on
`getrandom_spec` and `getrandom_small_max` in `Sys/Drivers/Char/Random.lean`;
the pins are `Checks/Cases/Checks/Sys/Drivers/Char/Random.lean`.  Rocq:
`Random.check_getrandom`. -/
def check_getrandom (i : SyscallInput) (buf cap flags : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if !(bv_unsigned flags == 0 || bv_unsigned flags == GRND_NONBLOCK) then CheckUnmodeled
  else if !(modeled_rw_count cap) then CheckUnmodeled   -- see `Uaccess.rw_bytes_max`
  else
  match read_bytes_map i.in_wmem buf cap with
  | none => CheckUnmodeled   -- unwritable destination buffer
  | some _ =>
    if !(w_is0 cap) then
      if bv_unsigned cap ≤ getrandom_small_max then
        -- the small request: full delivery at `buf`, and nothing else — no
        -- short count, no -EINTR (see `Random.getrandom_small_max`)
        match eff with
        | .mkEffectU r [(a, bs)] [] [] [] [] =>
            if bv_eqb a buf && bv_eqb r (len_word bs)
               && decide ((bs.length : Int) = bv_unsigned cap)
            then CheckOk m [] else CheckReject
        | _ => CheckReject
      else
        match eff with
        | .mkEffectU r [] [] [] [] [] =>
            if errno_ret_in getrandom_errnos r then CheckOk m [] else CheckReject
        | .mkEffectU r [(a, bs)] [] [] [] [] =>
            if bv_eqb a buf && bv_eqb r (len_word bs)
               && decide (1 ≤ (bs.length : Int)) && decide ((bs.length : Int) ≤ bv_unsigned cap)
            then CheckOk m [] else CheckReject
        | _ => CheckReject
    else if access_okb buf (bv_unsigned cap) then check_getrandom_zero (Z_to_bv 64 0) eff m
    else check_getrandom_zero (errno_ret EFAULT) eff m

/-- What an accepted zero-byte effect is: the model and the events are
untouched, and the effect is a bare errno from `getrandom_errnos` or the
bare return `r0` the caller decided.  Rocq: `Random.check_getrandom_zero_sound`. -/
theorem check_getrandom_zero_sound (r0 : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_getrandom_zero r0 eff m = CheckOk m' evs) :
    m' = m ∧ evs = [] ∧
      ((∃ e, e ∈ getrandom_errnos ∧ eff = mkEffect (errno_ret e) [] []) ∨ eff = mkEffect r0 [] []) := by
  unfold check_getrandom_zero at h
  split at h
  · rename_i r
    split at h
    · rename_i hg
      obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj h
      refine ⟨rfl, rfl, ?_⟩
      rw [Bool.or_eq_true, errno_ret_in_true, bv_eqb_eq] at hg
      rcases hg with ⟨e, he, rfl⟩ | rfl
      · exact Or.inl ⟨e, he, rfl⟩
      · exact Or.inr rfl
    · cases h
  · cases h

/-- The zero-byte acceptor never declines: every effect is accepted or
refused.  Rocq: `Random.check_getrandom_zero_no_unmodeled`. -/
theorem check_getrandom_zero_no_unmodeled (r0 : word) (eff : SyscallEffect) (m : Model) :
    check_getrandom_zero r0 eff m ≠ CheckUnmodeled := by
  intro h
  unfold check_getrandom_zero at h
  split at h
  · split at h <;> cases h
  · cases h

/-- The spec's zero-byte arm, with the range verdict `r0` already decided,
is accepted by `check_getrandom_zero r0`: the interrupted alternative
lands on the errno test, the bare `r0` on the `bv_eqb`.  Lean-only: the
completeness proof applies this once per range verdict where Rocq's
`hall`/`inv_ok` chain re-derives it in place. -/
theorem check_getrandom_zero_complete (r0 : word) (eff : SyscallEffect) (i : SyscallInput)
    (m m' : Model) (evs : List event)
    (h : alt (e <- errno_from getrandom_errnos ;; err_ret e) (ret_only r0) i m (Ok eff m' evs)) :
    check_getrandom_zero r0 eff m = CheckOk m' evs := by
  rw [alt_iff] at h
  rcases h with h | h
  · rw [errno_from, bind_choose_iff] at h
    obtain ⟨e, he, hk⟩ := h
    rw [err_ret, ret_only, pure_iff] at hk
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj hk
    simp only [check_getrandom_zero, errno_ret_in_intro _ _ he, Bool.true_or, ↓reduceIte]
  · rw [ret_only, pure_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    simp only [check_getrandom_zero, bv_eqb_refl, Bool.or_true, ↓reduceIte]

/-- The spec's zero-byte arm never runs `Unmodeled`: both alternatives end
in `pure`.  Lean-only, for the same reason as `check_getrandom_zero_complete`. -/
theorem zero_arm_never_unmodeled (r0 : word) (i : SyscallInput) (m : Model)
    (h : alt (e <- errno_from getrandom_errnos ;; err_ret e) (ret_only r0) i m Unmodeled) : False := by
  rw [alt_iff] at h
  rcases h with h | h
  · rw [errno_from, bind_choose_iff] at h
    obtain ⟨e, -, hk⟩ := h
    rw [err_ret, ret_only, pure_iff] at hk
    cases hk
  · rw [ret_only, pure_iff] at h
    cases h

/-- Accepting is sound: an accepted effect is one the spec admits, with the
spec's own post-model and events.  Rocq: `Random.check_getrandom_sound_ok`. -/
theorem check_getrandom_sound_ok (i : SyscallInput) (buf cap flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (h : check_getrandom i buf cap flags eff m = CheckOk m' evs) :
    getrandom_spec buf cap flags i m (Ok eff m' evs) := by
  unfold check_getrandom at h
  unfold getrandom_spec
  generalize (!(bv_unsigned flags == 0 || bv_unsigned flags == GRND_NONBLOCK)) = f at h ⊢
  cases f with
  | true => simp only [↓reduceIte] at h; cases h
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  generalize (!(modeled_rw_count cap)) = n at h ⊢
  cases n with
  | true => simp only [↓reduceIte] at h; cases h
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  rw [bind_input_iff]
  generalize read_bytes_map i.in_wmem buf cap = w at h ⊢
  cases w with
  | none => cases h
  | some _ =>
  dsimp only at h ⊢
  generalize (!(w_is0 cap)) = c at h ⊢
  cases c with
  | true =>
    simp only [↓reduceIte] at h ⊢
    by_cases hsm : bv_unsigned cap ≤ getrandom_small_max
    · -- the small request: the full delivery, and only that
      simp only [hsm, ↓reduceIte] at h ⊢
      split at h
      · rename_i r a bs
        split at h
        · rename_i hg
          obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj h
          simp only [Bool.and_eq_true, bv_eqb_eq, decide_eq_true_eq] at hg
          obtain ⟨⟨rfl, rfl⟩, hlen⟩ := hg
          rw [bind_choose_iff]
          exact ⟨bs, hlen, rfl⟩
        · cases h
      · cases h
    · -- the large request: the interrupted return or a nonempty delivery
      simp only [hsm, ↓reduceIte] at h ⊢
      split at h
      · rename_i r
        split at h
        · rename_i hg
          obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj h
          rw [errno_ret_in_true] at hg
          obtain ⟨e, he, rfl⟩ := hg
          rw [alt_iff]
          left
          rw [errno_from, bind_choose_iff]
          exact ⟨e, he, rfl⟩
        · cases h
      · rename_i r a bs
        split at h
        · rename_i hg
          obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj h
          simp only [Bool.and_eq_true, bv_eqb_eq, decide_eq_true_eq] at hg
          obtain ⟨⟨⟨rfl, rfl⟩, h1⟩, h2⟩ := hg
          rw [alt_iff]
          right
          rw [bind_choose_iff]
          exact ⟨bs, ⟨h1, h2⟩, rfl⟩
        · cases h
      · cases h
  | false =>
    -- the zero-byte request: the range verdict decides what joins -EINTR
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize access_okb buf (bv_unsigned cap) = s at h ⊢
    cases s with
    | true =>
      simp only [↓reduceIte] at h ⊢
      obtain ⟨rfl, rfl, ⟨e, he, rfl⟩ | rfl⟩ := check_getrandom_zero_sound _ _ _ _ _ h
      · rw [alt_iff]; left
        rw [errno_from, bind_choose_iff]
        exact ⟨e, he, rfl⟩
      · rw [alt_iff]; right
        exact rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨rfl, rfl, ⟨e, he, rfl⟩ | rfl⟩ := check_getrandom_zero_sound _ _ _ _ _ h
      · rw [alt_iff]; left
        rw [errno_from, bind_choose_iff]
        exact ⟨e, he, rfl⟩
      · rw [alt_iff]; right
        exact rfl

/-- Declining is sound: where the checker answers `CheckUnmodeled` the spec
runs `Unmodeled` — at the flag gate, at the transfer bound and at an
unwritable destination, and nowhere else, since every effect arm accepts
or refuses and `check_getrandom_zero` never declines.  Rocq:
`Random.check_getrandom_sound_unmodeled`. -/
theorem check_getrandom_sound_unmodeled (i : SyscallInput) (buf cap flags : word)
    (eff : SyscallEffect) (m : Model) (h : check_getrandom i buf cap flags eff m = CheckUnmodeled) :
    getrandom_spec buf cap flags i m Unmodeled := by
  unfold check_getrandom at h
  unfold getrandom_spec
  generalize (!(bv_unsigned flags == 0 || bv_unsigned flags == GRND_NONBLOCK)) = f at h ⊢
  cases f with
  | true => simp only [↓reduceIte]; exact unmodeled_intro i m
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  generalize (!(modeled_rw_count cap)) = n at h ⊢
  cases n with
  | true => simp only [↓reduceIte]; exact unmodeled_intro i m
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  rw [bind_input_iff]
  generalize read_bytes_map i.in_wmem buf cap = w at h ⊢
  cases w with
  | none => exact unmodeled_intro i m
  | some _ =>
  exfalso
  dsimp only at h
  generalize (!(w_is0 cap)) = c at h
  cases c with
  | true =>
    simp only [↓reduceIte] at h
    by_cases hsm : bv_unsigned cap ≤ getrandom_small_max
    · simp only [hsm, ↓reduceIte] at h
      split at h
      · split at h <;> cases h
      · cases h
    · simp only [hsm, ↓reduceIte] at h
      split at h
      · split at h <;> cases h
      · split at h <;> cases h
      · cases h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    generalize access_okb buf (bv_unsigned cap) = s at h
    cases s with
    | true =>
      simp only [↓reduceIte] at h
      exact check_getrandom_zero_no_unmodeled _ _ _ h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact check_getrandom_zero_no_unmodeled _ _ _ h

/-- Accepting is complete: every effect the spec admits is accepted, with
the spec's post-model and events.  Rocq: `Random.check_getrandom_complete_ok`. -/
theorem check_getrandom_complete_ok (i : SyscallInput) (buf cap flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : getrandom_spec buf cap flags i m (Ok eff m' evs)) :
    check_getrandom i buf cap flags eff m = CheckOk m' evs := by
  unfold getrandom_spec at h
  unfold check_getrandom
  generalize (!(bv_unsigned flags == 0 || bv_unsigned flags == GRND_NONBLOCK)) = f at h ⊢
  cases f with
  | true => simp only [↓reduceIte] at h; cases h
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  generalize (!(modeled_rw_count cap)) = n at h ⊢
  cases n with
  | true => simp only [↓reduceIte] at h; cases h
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  rw [bind_input_iff] at h
  generalize read_bytes_map i.in_wmem buf cap = w at h ⊢
  cases w with
  | none => cases h
  | some _ =>
  dsimp only at h ⊢
  generalize (!(w_is0 cap)) = c at h ⊢
  cases c with
  | true =>
    simp only [↓reduceIte] at h ⊢
    by_cases hsm : bv_unsigned cap ≤ getrandom_small_max
    · -- the small request: the chosen list has exactly `cap` bytes
      simp only [hsm, ↓reduceIte] at h ⊢
      rw [bind_choose_iff] at h
      obtain ⟨bs, hlen, hk⟩ := h
      rw [pure_iff] at hk
      obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj hk
      simp only [bv_eqb_refl, decide_eq_true hlen, Bool.true_and, ↓reduceIte]
    · -- the large request: the interrupted return or a nonempty delivery
      simp only [hsm, ↓reduceIte] at h ⊢
      rw [alt_iff] at h
      rcases h with h | h
      · rw [errno_from, bind_choose_iff] at h
        obtain ⟨e, he, hk⟩ := h
        rw [err_ret, ret_only, pure_iff] at hk
        obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj hk
        simp only [errno_ret_in_intro _ _ he, ↓reduceIte]
      · rw [bind_choose_iff] at h
        obtain ⟨bs, ⟨h1, h2⟩, hk⟩ := h
        rw [pure_iff] at hk
        obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj hk
        simp only [bv_eqb_refl, decide_eq_true h1, decide_eq_true h2, Bool.and_self, ↓reduceIte]
  | false =>
    -- the zero-byte request: both range verdicts are one helper application
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    generalize access_okb buf (bv_unsigned cap) = s at h ⊢
    cases s with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact check_getrandom_zero_complete _ _ _ _ _ _ h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact check_getrandom_zero_complete _ _ _ _ _ _ h

/-- Declining is complete: where the spec runs `Unmodeled` the checker
answers `CheckUnmodeled`, whatever effect it is shown.  Rocq:
`Random.check_getrandom_complete_unmodeled`. -/
theorem check_getrandom_complete_unmodeled (i : SyscallInput) (buf cap flags : word)
    (m : Model) (eff : SyscallEffect) (h : getrandom_spec buf cap flags i m Unmodeled) :
    check_getrandom i buf cap flags eff m = CheckUnmodeled := by
  unfold getrandom_spec at h
  unfold check_getrandom
  generalize (!(bv_unsigned flags == 0 || bv_unsigned flags == GRND_NONBLOCK)) = f at h ⊢
  cases f with
  | true => simp only [↓reduceIte]
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  generalize (!(modeled_rw_count cap)) = n at h ⊢
  cases n with
  | true => simp only [↓reduceIte]
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  rw [bind_input_iff] at h
  generalize read_bytes_map i.in_wmem buf cap = w at h ⊢
  cases w with
  | none => rfl
  | some _ =>
  exfalso
  dsimp only at h
  generalize (!(w_is0 cap)) = c at h
  cases c with
  | true =>
    simp only [↓reduceIte] at h
    by_cases hsm : bv_unsigned cap ≤ getrandom_small_max
    · simp only [hsm, ↓reduceIte] at h
      rw [bind_choose_iff] at h
      obtain ⟨bs, -, hk⟩ := h
      rw [pure_iff] at hk
      cases hk
    · simp only [hsm, ↓reduceIte] at h
      rw [alt_iff] at h
      rcases h with h | h
      · rw [errno_from, bind_choose_iff] at h
        obtain ⟨e, -, hk⟩ := h
        rw [err_ret, ret_only, pure_iff] at hk
        cases hk
      · rw [bind_choose_iff] at h
        obtain ⟨bs, -, hk⟩ := h
        rw [pure_iff] at hk
        cases hk
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    generalize access_okb buf (bv_unsigned cap) = s at h
    cases s with
    | true =>
      simp only [↓reduceIte] at h
      exact zero_arm_never_unmodeled _ _ _ h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact zero_arm_never_unmodeled _ _ _ h

/-- An accepted `getrandom` leaves the VM ledger where it was: every
accepting arm hands back the model it was given.  Rocq keeps this in
`VmMapsDisjoint.v` under the same name (`VmMapsDisjoint.check_getrandom_frame`);
the header says why it is stated here. -/
theorem check_getrandom_frame (i : SyscallInput) (buf cap flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_getrandom i buf cap flags eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_getrandom at h
  generalize (!(bv_unsigned flags == 0 || bv_unsigned flags == GRND_NONBLOCK)) = f at h
  cases f with
  | true => simp only [↓reduceIte] at h; cases h
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  generalize (!(modeled_rw_count cap)) = n at h
  cases n with
  | true => simp only [↓reduceIte] at h; cases h
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  generalize read_bytes_map i.in_wmem buf cap = w at h
  cases w with
  | none => cases h
  | some _ =>
  dsimp only at h
  generalize (!(w_is0 cap)) = c at h
  cases c with
  | true =>
    simp only [↓reduceIte] at h
    by_cases hsm : bv_unsigned cap ≤ getrandom_small_max
    · simp only [hsm, ↓reduceIte] at h
      split at h
      · split at h
        · obtain ⟨rfl, -⟩ := check_result.CheckOk.inj h; rfl
        · cases h
      · cases h
    · simp only [hsm, ↓reduceIte] at h
      split at h
      · split at h
        · obtain ⟨rfl, -⟩ := check_result.CheckOk.inj h; rfl
        · cases h
      · split at h
        · obtain ⟨rfl, -⟩ := check_result.CheckOk.inj h; rfl
        · cases h
      · cases h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    generalize access_okb buf (bv_unsigned cap) = s at h
    cases s with
    | true =>
      simp only [↓reduceIte] at h
      obtain ⟨rfl, -, -⟩ := check_getrandom_zero_sound _ _ _ _ _ h; rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨rfl, -, -⟩ := check_getrandom_zero_sound _ _ _ _ _ h; rfl

/-! ## The witness — `Checks/Witness/Drivers/Char/Random.v` -/

/-- getrandom's witness.  A nonzero request of at most
`getrandom_small_max` bytes has ONE admissible shape — full delivery — so
the witness exhibits it with all-zero bytes: the bytes are the
environment's, and any list of the right length is admissible —
`get_random_bytes_user` (drivers/char/random.c, v6.18.46) copies the key
material for a request of at most 32 bytes (:455-458) and, for a longer
one, whatever `chacha20_block` produced in the loop (:460-476).  Every
other modeled request answers
-EINTR, the head of `getrandom_errnos`, which joins every range verdict
of the zero-byte arm and the delivery alternative of a large request:
`wait_for_random_bytes` (drivers/char/random.c:136-147, v6.18.46) can be
interrupted at :1403-1405 before the buffer is imported at :1408, so the
spec admits it there whatever the range says.  Rocq:
`Random.getrandom_witness`. -/
def getrandom_witness (buf buflen flags : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  if !(bv_unsigned flags == 0 || bv_unsigned flags == GRND_NONBLOCK) then Unmodeled
  else if !(modeled_rw_count buflen) then Unmodeled   -- see `Uaccess.rw_bytes_max`
  else match read_bytes_map i.in_wmem buf buflen with
       | none => Unmodeled                            -- unwritable destination
       | some _ =>
           if !(w_is0 buflen) && decide (bv_unsigned buflen ≤ getrandom_small_max)
           then -- the small request: delivered in full, and only that
             let bs := List.replicate (bv_unsigned buflen).toNat (Z_to_bv 8 0)
             Ok (mkEffect (len_word bs) [(buf, bs)] []) m []
           else ret_outcome (errno_ret EINTR) m   -- -EINTR joins every other verdict

/-- The witness is a run of the spec: `getrandom_spec` is receptive on
every input and model.  Rocq: `Random.getrandom_witness_ok`. -/
theorem getrandom_witness_ok (buf buflen flags : word) (i : SyscallInput) (m : Model) :
    getrandom_spec buf buflen flags i m (getrandom_witness buf buflen flags i m) := by
  unfold getrandom_spec getrandom_witness
  generalize (!(bv_unsigned flags == 0 || bv_unsigned flags == GRND_NONBLOCK)) = f
  cases f with
  | true => simp only [↓reduceIte]; exact unmodeled_intro i m
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  generalize (!(modeled_rw_count buflen)) = n
  cases n with
  | true => simp only [↓reduceIte]; exact unmodeled_intro i m
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [bind_input_iff]
  generalize read_bytes_map i.in_wmem buf buflen = w
  cases w with
  | none => exact unmodeled_intro i m
  | some _ =>
  dsimp only
  generalize (!(w_is0 buflen)) = c
  cases c with
  | true =>
    simp only [Bool.true_and, ↓reduceIte]
    by_cases hsm : bv_unsigned buflen ≤ getrandom_small_max
    · -- the small request: the chosen list has exactly `buflen` bytes
      simp only [hsm, decide_true, ↓reduceIte]
      rw [bind_choose_iff]
      refine ⟨_, ?_, rfl⟩
      rw [List.length_replicate]
      have hr := word_unsigned_range buflen
      omega
    · simp only [hsm, decide_false, ↓reduceIte]
      rw [alt_iff]; left
      rw [errno_from, bind_choose_iff]
      exact ⟨EINTR, List.Mem.head _, rfl⟩
  | false =>
    simp only [Bool.false_eq_true, Bool.false_and, ↓reduceIte]
    generalize access_okb buf (bv_unsigned buflen) = s
    cases s with
    | true =>
      simp only [↓reduceIte]
      rw [alt_iff]; left
      rw [errno_from, bind_choose_iff]
      exact ⟨EINTR, List.Mem.head _, rfl⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [alt_iff]; left
      rw [errno_from, bind_choose_iff]
      exact ⟨EINTR, List.Mem.head _, rfl⟩

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Drivers.Char.Random
