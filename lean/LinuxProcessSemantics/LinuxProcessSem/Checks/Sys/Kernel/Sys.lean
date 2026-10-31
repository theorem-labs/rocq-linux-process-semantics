import LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Sys
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Fork

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Checks.Sys.Kernel.Sys — the getpid (172), gettid (178), getuid/geteuid/getgid/getegid (174-177), setuid/setgid (146/144), setresuid/setresgid (147/149), setsid (157), uname (160), prlimit64 (261) and prctl (167) checkers and witnesses

Mirrors the whole of
`theories/LinuxProcessSem/Checks/Sys/Kernel/Sys.v` (the checkers and their
four proofs each) together with the whole of
`theories/LinuxProcessSem/Checks/Witness/Kernel/Sys.v` (the witnesses and
their receptivity proofs), and the arms' frame lemmas from
`theories/LinuxProcessSem/Checks/VmMapsDisjoint.v`.  Rocq keeps the
witness in its own file because each of its files holds every arm's share
of one obligation; the Lean tree keeps no `Checks/Witness/` mirror files,
so a witness lives beside its checker.  The file landed in two thirds:
the id and session arms first (ticket C-Kernel-Sys-ids), and uname,
prlimit64 and prctl appended below their frame lemmas (ticket
C-Kernel-Sys-uname-prlimit-prctl), with the earlier text and proofs left
as they landed.  What Rocq states about these
arms in `Checks/Sys/Dispatch.v` — their `CheckedArm`s and `arm_unfold`
lemmas — is each arm's REGISTRATION, which edits `Checks/Sys/Table.lean`
and appends to `Checks/VmMapsDisjoint/Arms.lean` the arm-level preserves
fact that file derives from the frame lemmas below through
`arm_preserves_of_frame`; that is the conformance tickets' step
(V-Kernel-Sys-ids for the first third, V-Kernel-Sys-uname-prlimit-prctl
for the second), not this file's: this file imports the two preludes,
the spec and the set_tid_address checker it shares, and nothing of the
checked table, so that it can land before the table has an arm
(`tools/lean_port_graph.py`, `derive_edges` rules 3 and 4).  The two
mirrored Rocq files are
byte-identical at a71fd38a and at the port's common baseline f44244ad,
which is an ancestor of no day branch; the header names the one
`Sys/Kernel/Sys.lean` names.  `Checks/VmMapsDisjoint.v` is held to no
commit — it gains a lemma with every arm that lands — and what this file
mirrors of it is the text of `check_uname_frame`, `check_prlimit64_frame`
and `check_prctl_frame` alone, identical at the same three commits.  No
guard holds a `Checks/` twin's header to the Rocq tree
(`tools/check_lean_spec_parity.py` sweeps `Sys/`), so the two sentences
before this one are held by readers, and stop being true the day either
Rocq file, or one of those three lemmas, changes after a71fd38a.  Not part
of the trusted
specification: what is trusted is `Sys/Kernel/Sys.lean`, and everything
here is proved against it.

WHAT THE CHECKERS DECIDE, and where each decision is the kernel's.

- `getpid` and `gettid` are `check_set_tid_address` under two more names,
  as `getpid_spec` and `gettid_spec` are `set_tid_address_spec`: the
  kernel returns `task_tgid_vnr(current)` from `SYSCALL_DEFINE0(getpid)`
  (kernel/sys.c:999-1002, Linux v6.18.46, commit 1f99e9ab748f) and
  `task_pid_vnr(current)` from `SYSCALL_DEFINE0(gettid)`
  (kernel/sys.c:1005-1008, Linux v6.18.46), and for the one-thread process
  this model carries the two numbers are one number; the argument for
  sharing the relation is on `Sys/Kernel/Sys.lean`, and sharing the
  checker keeps the executable model from drifting apart where the
  relational one cannot.  Their lemmas are the Fork checker's lemmas by
  application, as Rocq's are by `exact`.
- The four readers `SYSCALL_DEFINE0(getuid)` (kernel/sys.c:1027-1031,
  Linux v6.18.46), `geteuid` (:1033-1037), `getgid` (:1039-1043) and
  `getegid` (:1045-1049) return one field of `current_cred()` through an
  identity mapping and have no failing path.
- `setuid` and `setgid` are one checker over an `IdTriple`, as the spec
  is one relation.  `__sys_setuid` (kernel/sys.c:651-696, Linux v6.18.46)
  answers -EINVAL to an invalid id before it allocates anything (:659-661),
  then allocates (:663-665, the -ENOMEM), then takes one of three arms:
  a capable caller installs the id as all three (:670 writes the real and
  saved uid and the :680 both arms share writes the effective one; the
  `set_user` call at :672 and the `set_cred_ucounts` call at :686 are the
  two -EAGAINs, and both fail only when the real id moves); a caller naming
  its real or saved id installs it as the effective one (:676-678 falls
  through to :680); every other caller is -EPERM (:668 and :677).  The
  checker reads the same three arms in the same order, and reads the
  -EINVAL arm first, before the credentials are consulted, because the
  kernel does.  `__sys_setgid` (kernel/sys.c:479-513, Linux v6.18.46) has
  the same shape without the `set_user` call.  On the -EPERM arm
  `check_setid_result` is run with -EPERM as the "success" return and `m`
  as its model, which is exactly Rocq's reading of
  `alt (errno arm) (err_ret EPERM)`.
- `setresuid` and `setresgid` are one checker again.  `__sys_setresuid`
  (kernel/sys.c:708-781, Linux v6.18.46) resolves each `-1` to the current
  id, answers 0 to a call that changes nothing before it allocates
  (:732-737), refuses with -EPERM a caller without the capability that
  names an id it does not already hold (:739-747), and only then
  allocates and installs (:749-765), calling `set_user` (kernel/sys.c:523-534,
  Linux v6.18.46) when the real uid moves (:755-758).
  `__sys_setresgid` (kernel/sys.c:810-870, Linux v6.18.46) is the same
  without `set_user`.  The checker's two leading gates are the spec's own
  Boolean expressions, so that one `split` opens both sides together.
- `setsid` (`ksys_setsid`, kernel/sys.c:1268-1301, Linux v6.18.46): -EPERM
  is accepted on every model, since the process-group test at :1284
  depends on state this model does not carry; a session id is accepted
  only while no call has succeeded — the `leader` bit at :1278 is set at
  :1287 and never cleared — and only inside the envelope a tid is drawn
  from, equal to the recorded tid if there is one, since the session id
  is the caller's tgid (:1271-1273); a success moves the model with
  `with_tid` then `with_setsid_succeeded`, the spec's post-model.  The
  -EPERM test is read before the bit, and `setsid_id_not_eperm` is what
  keeps the two accepting arms apart: no return inside the envelope is
  the bit pattern of -EPERM.
- `uname` (`SYSCALL_DEFINE1(newuname)`, kernel/sys.c:1351-1366, Linux
  v6.18.46): one `copy_to_user` of the 390-byte `struct new_utsname`
  (include/uapi/linux/utsname.h:25-32, Linux v6.18.46), -EFAULT when it
  fails (:1358-1359) and 0 otherwise (:1365).  `copy_to_user` asks
  `access_ok` over the whole range before a byte moves
  (`_inline_copy_to_user`, include/linux/uaccess.h:189-200, Linux
  v6.18.46, the test at :195), so the checker's first gate is
  `access_okb`: -EFAULT with nothing written.  A destination the writable
  view does not wholly back is declined, since the kernel would land a
  prefix the model cannot state.  The bytes are the record when the model
  holds one and any member of `utsname_wf` when it does not, which then
  becomes the record; the two pinned members and the four free members'
  terminators are `Sys/Kernel/Sys.lean`'s argument, and an empty
  `domainname` is only `utsname_default`'s draw below.
- `prlimit64` (`SYSCALL_DEFINE4(prlimit64)`, kernel/sys.c:1729-1792, Linux
  v6.18.46, and `do_prlimit`, :1500-1561): the kernel lines behind the
  checker's answers are the `copy_from_user` of `new_rlim` at :1744-1745,
  taken before the pid is resolved at :1751, and the `copy_to_user` of
  `old_rlim` at :1784-1787, each -EFAULT through the `access_ok`
  (`__access_ok`, include/asm-generic/access_ok.h:31-41, Linux v6.18.46) that
  `_inline_copy_from_user` (include/linux/uaccess.h:159-185, Linux
  v6.18.46, at :168) and `_inline_copy_to_user` (:189-200, at :195) ask
  over the whole sixteen bytes before a byte moves; `do_prlimit`'s
  -EINVAL for soft > hard (:1511-1512), before any lock is taken; its
  `capable(CAP_SYS_RESOURCE)` test on a rising hard limit (:1526-1528),
  which is why a moving hard limit is declined rather than judged —
  whether the capability is held is not a fact of this model, and a
  falling one is admitted by no spec arm; and the store (:1535-1536).  The
  comparison at :1526 reads the task's standing hard limit, which is why a
  write needs a recorded pair.  `RLIMIT_CORE`
  is 4 (include/uapi/asm-generic/resource.h:20, Linux v6.18.46).
- `prctl` (`SYSCALL_DEFINE5(prctl)`, whose opening lines,
  kernel/sys.c:2518-2530, Linux v6.18.46, hand every option at :2525-2527
  to the LSM hook `security_task_prctl`, security/security.c:3871-3887,
  Linux v6.18.46): for `PR_CAPBSET_READ` (23, include/uapi/linux/prctl.h:71,
  Linux v6.18.46) `cap_task_prctl` (security/commoncap.c:1291-1431, Linux
  v6.18.46) answers -EINVAL unless `cap_valid(arg2)` (:1299-1300) and
  `!!cap_raised(old->cap_bset, arg2)` otherwise (:1301), 1 under the full
  bounding set `Sys/Kernel/Sys.lean` assumes.  `cap_valid` is
  `((x) >= 0 && (x) <= CAP_LAST_CAP)` (include/uapi/linux/capability.h:425,
  Linux v6.18.46), `CAP_LAST_CAP` being `CAP_CHECKPOINT_RESTORE`, 40
  (:421-423), over the whole `unsigned long`, so 2^32 is -EINVAL and not
  capability 0.  Every other option is declined.

THE ERRNO GATE IS READ FIRST, AND COMPLETENESS PAYS FOR IT.
`check_setid_result` tests the errno set before the success return, as
Rocq does, so an accepting checker answers `CheckOk m []` for an errno
and `CheckOk mR []` for the success return.  Completeness on the success
arm therefore needs the success return NOT to be in the errno set — else
the spec's success outcome, with post-model `mR`, would be answered with
`m`.  `errno_ret_in_setid_zero` and `errno_ret_in_setid_eperm` are that
fact for the two returns the id checkers ever pass as `r`: 0 and -EPERM
are in neither `setid_errnos` set.  They are Rocq's lemmas, and
`check_setid_result_complete_ok` takes the fact as a hypothesis so that
each leaf discharges it with the one that applies.

THE PROOFS keep Rocq's case structure.  Rocq walks the credential
checkers with four Ltacs — `creds_split`, which destructs every `if` on
both sides, and `creds_unmod_leaf`, `creds_sound_leaf` and
`creds_complete_leaf`, which close the leaves.  Here a checker's `if` is
opened by `split at h` on setuid/setgid, and by `ite_eq_elim`, outermost
first, on setresid and setsid (its section says why `split at h` is the
wrong tool on those two); either way the hypothesis handed back selects
the spec's arm through `ite_eq_left` / `ite_eq_right`; on the spec side
the applied `if` — `(if c then a else b) i m o`, which `split` does not
find — is opened by `ite_sys_elim`, and closed for a witness by
`ite_sys_intro`.
The leaves are `check_setid_result_sound_ok` (Rocq's lemma);
`check_setid_result_complete_ok` (Lean-only, standing where Rocq's
`creds_complete_leaf` re-derives it in place); `errno_arm_never_unmodeled`
(Lean-only, closing the spec-side `Unmodeled` leaf that Rocq's
`*_complete_unmodeled` proofs close by `creds_split; inv_ok`; the
checker-side leaf `creds_unmod_leaf` closes is `check_setid_no_unmodeled`
and `check_setresid_no_unmodeled` here); and `errno_arm_enomem_witness`
for the witnesses.  `check_setid_result_model` is the Lean-only lemma
behind the frame lemmas: an accepted call hands back `m` or `mR`, and
every `mR` a caller passes is `with_creds _ m`.  The setsid and
`check_setid_result` proofs take the effect apart by `split at h` on the
checker's own `match`, one goal per arm, as the getrandom checker does.

THE FRAME LEMMAS are Rocq's `VmMapsDisjoint.check_<name>_frame`, stated
here for the reason the set_tid_address checker states its own: each
depends on nothing but its checker, and the alternation that consumes
them lives in a file that imports the table, which imports this file.
Nothing else of the registration is here: no `CheckedArm`, no table row,
no `arm_unfold` lemma. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Sys

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork
open LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Sys
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Witness.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Fork

/-! ## Opening an `if`: Lean-only lemmas

A spec arm is a `Sys` value, and a hypothesis about it is
`(if c then a else b) i m o`: the `if` sits under three applications,
where `split` does not look (`Checks/Sys/Drivers/Char/Random.lean` says
the same of its gates and generalises them instead).  `ite_sys_pos`,
`ite_sys_neg` and `ite_sys_intro` build such an `if`, and `ite_sys_elim`
reads one, none of them naming the condition, which for the setresid
checker is a Boolean expression several `let`s deep.

`ite_eq_elim` reads a CHECKER's `if`, `(if c then a else b) = r`, and is
here instead of `split at h` for a reason worth keeping: `split` prefers
an `if` or `match` nested INSIDE a condition, and two of these checkers
have one — setresid's condition holds the three resolved `-1`s, each an
`if`, and setsid's holds the `match` on the recorded tid — so `split at
h` opened those first, one leaf per combination, and left the outer
`if` standing in every one.  `ite_eq_elim` always takes the outermost. -/

/-- Build an applied `if` whose condition holds.  Lean-only; the setresid
soundness proof and `ite_sys_intro` use it. -/
theorem ite_sys_pos {A : Type} {c : Prop} [Decidable c] {a b : Sys A} {i : SyscallInput}
    {m : Model} {o : outcome A} (hc : c) (ha : a i m o) : (if c then a else b) i m o := by
  rw [ite_eq_left hc]
  exact ha

/-- Build an applied `if` whose condition fails.  Lean-only; the setsid
and setresid soundness proofs and `ite_sys_intro` use it. -/
theorem ite_sys_neg {A : Type} {c : Prop} [Decidable c] {a b : Sys A} {i : SyscallInput}
    {m : Model} {o : outcome A} (hc : ¬ c) (hb : b i m o) : (if c then a else b) i m o := by
  rw [ite_eq_right hc]
  exact hb

/-- Build an applied `if`: give each branch under its condition.
Lean-only; the witness receptivity proofs and setsid's soundness proof use
it. -/
theorem ite_sys_intro {A : Type} {c : Prop} [Decidable c] {a b : Sys A} {i : SyscallInput}
    {m : Model} {o : outcome A} (ha : c → a i m o) (hb : ¬ c → b i m o) :
    (if c then a else b) i m o := by
  by_cases hc : c
  · exact ite_sys_pos hc (ha hc)
  · exact ite_sys_neg hc (hb hc)

/-- Read an applied `if`: whichever branch the condition selects holds,
and the condition says which.  Lean-only; the completeness proofs use it. -/
theorem ite_sys_elim {A : Type} {c : Prop} [Decidable c] {a b : Sys A} {i : SyscallInput}
    {m : Model} {o : outcome A} (h : (if c then a else b) i m o) :
    (c ∧ a i m o) ∨ (¬ c ∧ b i m o) := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h
    exact Or.inl ⟨hc, h⟩
  · rw [ite_eq_right hc] at h
    exact Or.inr ⟨hc, h⟩

/-- Read a checker's `if`, outermost first (the section header says why
not `split at h`).  Lean-only; the setsid and setresid proofs use it. -/
theorem ite_eq_elim {α : Type} {c : Prop} [Decidable c] {a b r : α} (h : (if c then a else b) = r) :
    (c ∧ a = r) ∨ (¬ c ∧ b = r) := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h
    exact Or.inl ⟨hc, h⟩
  · rw [ite_eq_right hc] at h
    exact Or.inr ⟨hc, h⟩

/-! ## getpid (172) and gettid (178): the set_tid_address checker -/

/-- Rocq: `Checks.Sys.Kernel.Sys.check_getpid`.  The SAME check as
`check_set_tid_address`, because `getpid_spec` is the same relation. -/
def check_getpid : SyscallEffect → Model → check_result := check_set_tid_address

/-- Rocq: `Checks.Sys.Kernel.Sys.check_gettid`.  The same check again. -/
def check_gettid : SyscallEffect → Model → check_result := check_set_tid_address

/-- Rocq: `check_getpid_sound_ok`. -/
theorem check_getpid_sound_ok (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_getpid eff m = CheckOk m' evs) :
    getpid_spec i m (Ok eff m' evs) :=
  check_set_tid_address_sound_ok i eff m m' evs h

/-- Rocq: `check_getpid_sound_unmodeled`. -/
theorem check_getpid_sound_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (h : check_getpid eff m = CheckUnmodeled) : getpid_spec i m Unmodeled :=
  check_set_tid_address_sound_unmodeled i eff m h

/-- Rocq: `check_getpid_complete_ok`. -/
theorem check_getpid_complete_ok (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : getpid_spec i m (Ok eff m' evs)) :
    check_getpid eff m = CheckOk m' evs :=
  check_set_tid_address_complete_ok i eff m m' evs h

/-- Rocq: `check_getpid_complete_unmodeled`. -/
theorem check_getpid_complete_unmodeled (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (h : getpid_spec i m Unmodeled) : check_getpid eff m = CheckUnmodeled :=
  check_set_tid_address_complete_unmodeled i m eff h

/-- Rocq: `check_gettid_sound_ok`. -/
theorem check_gettid_sound_ok (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_gettid eff m = CheckOk m' evs) :
    gettid_spec i m (Ok eff m' evs) :=
  check_set_tid_address_sound_ok i eff m m' evs h

/-- Rocq: `check_gettid_sound_unmodeled`. -/
theorem check_gettid_sound_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (h : check_gettid eff m = CheckUnmodeled) : gettid_spec i m Unmodeled :=
  check_set_tid_address_sound_unmodeled i eff m h

/-- Rocq: `check_gettid_complete_ok`. -/
theorem check_gettid_complete_ok (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : gettid_spec i m (Ok eff m' evs)) :
    check_gettid eff m = CheckOk m' evs :=
  check_set_tid_address_complete_ok i eff m m' evs h

/-- Rocq: `check_gettid_complete_unmodeled`. -/
theorem check_gettid_complete_unmodeled (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (h : gettid_spec i m Unmodeled) : check_gettid eff m = CheckUnmodeled :=
  check_set_tid_address_complete_unmodeled i m eff h

/-! ## setsid (157) -/

/-- Rocq: `Checks.Sys.Kernel.Sys.check_setsid`.  The
envelope-and-recorded-tid test is the spec's `choose` read as a Boolean:
Rocq's `(0 <? …)%Z && (… <? PID_MAX_ENVELOPE)%Z` is
`decide … && decide …`, and the `match` on `m_tid m` is the spec's match
with `True` read as `true` and `t = t0` as `bv_eqb`. -/
def check_setsid (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | SyscallEffect.mkEffectU ret [] [] [] [] [] =>
      if bv_eqb ret (errno_ret EPERM) then CheckOk m []
      else if m_setsid_succeeded m then CheckReject
      else if decide (0 < bv_unsigned ret) && decide (bv_unsigned ret < PID_MAX_ENVELOPE) &&
              (match m_tid m with
               | none => true
               | some t0 => bv_eqb ret t0)
      then CheckOk (with_setsid_succeeded (with_tid ret m)) []
      else CheckReject
  | _ => CheckReject

/-- A return inside the envelope is not the bit pattern of -EPERM: read
unsigned, -EPERM is `2^64 - 1`, above `PID_MAX_ENVELOPE`.  This is what
keeps the checker's first test from stealing a session id.  Rocq:
`setsid_id_not_eperm`. -/
theorem setsid_id_not_eperm (r : word) (h : bv_unsigned r < PID_MAX_ENVELOPE) :
    bv_eqb r (errno_ret EPERM) = false := by
  cases hr : bv_eqb r (errno_ret EPERM) with
  | false => rfl
  | true =>
    exfalso
    rw [(bv_eqb_eq r (errno_ret EPERM)).mp hr] at h
    exact absurd h (by decide)

/-- Accepting is sound.  Rocq: `check_setsid_sound_ok`.

The effect is taken apart by `split at h` on the checker's `match`; then
the three tests in order.  An accepted -EPERM is the spec's `err_ret
EPERM` on either side of the sticky bit; an accepted session id lands on
the spec's draw, whose three conjuncts are read off the accepted Boolean
(`of_decide_eq_true` for the bounds, `bv_eqb_eq` for the recorded tid),
and `set_tid` then `set_setsid_succeeded` are two `bind_modify_iff`s. -/
theorem check_setsid_sound_ok (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_setsid eff m = CheckOk m' evs) :
    setsid_spec i m (Ok eff m' evs) := by
  simp only [setsid_spec, bind_get_model_iff]
  unfold check_setsid at h
  split at h
  · rename_i ret
    rcases ite_eq_elim h with ⟨he, h⟩ | ⟨-, h⟩
    · obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj h
      obtain rfl := (bv_eqb_eq ret (errno_ret EPERM)).mp he
      exact ite_sys_intro (fun _ => pure_ok _ i _) (fun _ => alt_l _ _ i _ _ (pure_ok _ i _))
    · rcases ite_eq_elim h with ⟨-, h⟩ | ⟨hs, h⟩
      · cases h
      · rcases ite_eq_elim h with ⟨hv, h⟩ | ⟨-, h⟩
        · obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj h
          refine ite_sys_neg hs (alt_r _ _ i _ _ ?_)
          have hv' := (Bool.and_eq_true _ _).mp hv
          have hlo : 0 < bv_unsigned ret :=
            of_decide_eq_true ((Bool.and_eq_true _ _).mp hv'.1).1
          have hhi : bv_unsigned ret < PID_MAX_ENVELOPE :=
            of_decide_eq_true ((Bool.and_eq_true _ _).mp hv'.1).2
          have h2 := hv'.2
          rw [bind_choose_iff]
          refine ⟨ret, ⟨⟨hlo, hhi⟩, ?_⟩, ?_⟩
          · cases ht : m_tid m with
            | none => exact True.intro
            | some t0 =>
                simp only [ht] at h2
                exact (bv_eqb_eq ret t0).mp h2
          · rw [set_tid, bind_modify_iff, set_setsid_succeeded, bind_modify_iff]
            exact pure_ok _ i _
        · cases h
  · cases h

/-- The checker never declines: every arm is `CheckOk` or `CheckReject`.
Rocq: `check_setsid_no_unmodeled`. -/
theorem check_setsid_no_unmodeled (eff : SyscallEffect) (m : Model) :
    check_setsid eff m ≠ CheckUnmodeled := by
  intro h
  unfold check_setsid at h
  split at h
  · rcases ite_eq_elim h with ⟨-, h⟩ | ⟨-, h⟩
    · cases h
    · rcases ite_eq_elim h with ⟨-, h⟩ | ⟨-, h⟩
      · cases h
      · rcases ite_eq_elim h with ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
  · cases h

/-- Declining is sound, vacuously.  Rocq: `check_setsid_sound_unmodeled`. -/
theorem check_setsid_sound_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (h : check_setsid eff m = CheckUnmodeled) : setsid_spec i m Unmodeled :=
  absurd h (check_setsid_no_unmodeled eff m)

/-- Accepting is complete.  Rocq: `check_setsid_complete_ok`.

The spec's -EPERM, on either side of the sticky bit, lands on the
checker's first test by `bv_eqb_refl`.  The draw lands on the third:
`setsid_id_not_eperm` takes it past the first, the sticky-bit hypothesis
past the second, and the drawn tid's three facts make the Boolean `true`,
with the recorded-tid case split so that the checker's `match` reduces
under `ht`. -/
theorem check_setsid_complete_ok (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : setsid_spec i m (Ok eff m' evs)) :
    check_setsid eff m = CheckOk m' evs := by
  simp only [setsid_spec, bind_get_model_iff] at h
  rcases ite_sys_elim h with ⟨-, h⟩ | ⟨hs, h⟩
  · rw [err_ret, ret_only, pure_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    simp only [check_setsid, bv_eqb_refl, ↓reduceIte]
  · rw [alt_iff] at h
    rcases h with h | h
    · rw [err_ret, ret_only, pure_iff] at h
      obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
      simp only [check_setsid, bv_eqb_refl, ↓reduceIte]
    · rw [bind_choose_iff] at h
      obtain ⟨tid, ⟨⟨hlo, hhi⟩, htid⟩, h⟩ := h
      rw [set_tid, bind_modify_iff, set_setsid_succeeded, bind_modify_iff] at h
      unfold ret_only Monad.pure at h
      obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
      cases ht : m_tid m with
      | none =>
          simp only [check_setsid, setsid_id_not_eperm _ hhi, Bool.false_eq_true, ↓reduceIte, hs,
            decide_eq_true hlo, decide_eq_true hhi, ht, Bool.true_and]
      | some t0 =>
          simp only [ht] at htid
          subst htid
          simp only [check_setsid, setsid_id_not_eperm _ hhi, Bool.false_eq_true, ↓reduceIte, hs,
            decide_eq_true hlo, decide_eq_true hhi, ht, bv_eqb_refl, Bool.true_and]

/-- Declining is complete, vacuously: the spec never declines.  Rocq:
`check_setsid_complete_unmodeled`. -/
theorem check_setsid_complete_unmodeled (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (h : setsid_spec i m Unmodeled) : check_setsid eff m = CheckUnmodeled := by
  exfalso
  simp only [setsid_spec, bind_get_model_iff] at h
  rcases ite_sys_elim h with ⟨-, h⟩ | ⟨-, h⟩
  · rw [err_ret, ret_only, pure_iff] at h
    cases h
  · rw [alt_iff] at h
    rcases h with h | h
    · rw [err_ret, ret_only, pure_iff] at h
      cases h
    · rw [bind_choose_iff] at h
      obtain ⟨tid, -, h⟩ := h
      rw [set_tid, bind_modify_iff, set_setsid_succeeded, bind_modify_iff] at h
      unfold ret_only Monad.pure at h
      cases h

/-! ## The credential checkers: getuid family (174-177), setuid/setgid (146/144), setresuid/setresgid (147/149) -/

/-- 0 is in neither errno set: the success return of an installing arm
is never mistaken for an injected failure.  Rocq: `errno_ret_in_setid_zero`. -/
theorem errno_ret_in_setid_zero (b : Bool) :
    errno_ret_in (setid_errnos b) (Z_to_bv 64 0) = false := by
  cases b <;> decide

/-- Nor is -EPERM: the refusing arm's return is not in the set it is
paired with.  Rocq: `errno_ret_in_setid_eperm`. -/
theorem errno_ret_in_setid_eperm (b : Bool) :
    errno_ret_in (setid_errnos b) (errno_ret EPERM) = false := by
  cases b <;> decide

/-- Rocq: `Checks.Sys.Kernel.Sys.check_getid`.  A bare return of the
selected field, the model unmoved. -/
def check_getid (sel : Creds → word) (eff : SyscallEffect) (m : Model) : check_result :=
  check_ret_only eff (sel (m_creds m)) m []

/-- Rocq: `Checks.Sys.Kernel.Sys.check_setid_result`.  The acceptor for
one installing arm of the id setters.  The errno test is first, as in
Rocq; the file header says what that costs completeness and how the cost
is paid. -/
def check_setid_result (errs : List Int) (r : word) (mR : Model) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match eff with
  | SyscallEffect.mkEffectU ret [] [] [] [] [] =>
      if errno_ret_in errs ret then CheckOk m []
      else if bv_eqb ret r then CheckOk mR [] else CheckReject
  | _ => CheckReject

/-- Rocq: `Checks.Sys.Kernel.Sys.check_setid`.  The three arms of
`__sys_setuid` (kernel/sys.c:651-696, Linux v6.18.46) in the kernel's
order, behind its -EINVAL test; the file header walks them.  The `let`s
are the spec's, so that the two sides unfold to the same terms.  `v` is
the kernel's `uid_t` / `gid_t` (the parameter type of `setuid`,
kernel/sys.c:698, and `setgid`, :515, Linux v6.18.46) ALREADY narrowed:
the `ID_MINUS_ONE` test is a full-width `bv_eqb`, and the `uid32`
narrowing of the register is the registration's — `setuid_arm` /
`setgid_arm` in `Sys/Registry/Kernel/Sys.lean` apply it before
`setid_spec`, and Rocq's `arm_setuid` / `arm_setgid`
(`Checks/Sys/Dispatch.v`) before this checker — so a raw 0x1_FFFF_FFFF
is a valid id here and -1 only once the row narrows it; the pins that
read it through `check_syscall` go with V-Kernel-Sys-ids. -/
def check_setid (get : Creds → IdTriple) (put : IdTriple → Creds → Creds) (user : Bool)
    (v : word) (eff : SyscallEffect) (m : Model) : check_result :=
  let c := m_creds m
  let t := get c
  if bv_eqb v ID_MINUS_ONE then check_ret_only eff (errno_ret EINVAL) m []
  else if creds_privileged c then
    check_setid_result (setid_errnos (user && !(bv_eqb v t.id_real))) (Z_to_bv 64 0)
      (with_creds (put (IdTriple.mkIdTriple v v v) c) m) eff m
  else if bv_eqb v t.id_real || bv_eqb v t.id_saved then
    check_setid_result (setid_errnos false) (Z_to_bv 64 0)
      (with_creds (put (IdTriple.mkIdTriple t.id_real v t.id_saved) c) m) eff m
  else
    check_setid_result (setid_errnos false) (errno_ret EPERM) m eff m

/-- Rocq: `Checks.Sys.Kernel.Sys.check_setresid`.  The three answers of
`__sys_setresuid` (kernel/sys.c:708-781, Linux v6.18.46) in the kernel's
order — the no-op 0, the -EPERM, the installing arm — each `-1` resolved
to the current id first, as the file header walks them.  The `let`s are
the spec's.  `r`, `e` and `s` are the kernel's `uid_t` / `gid_t` (the
parameter types of `setresuid`, kernel/sys.c:783, and `setresgid`, :872,
Linux v6.18.46) ALREADY narrowed, as `check_setid`'s `v` is: `pick`
compares each word against `ID_MINUS_ONE` at full width, the `uid32`
narrowing is the registration's (`setresuid_arm` / `setresgid_arm` in
`Sys/Registry/Kernel/Sys.lean`; Rocq's `arm_setresuid` /
`arm_setresgid`), so a raw 0x1_FFFF_FFFF is an id to install here and
"leave this id alone" only once the row narrows it. -/
def check_setresid (get : Creds → IdTriple) (put : IdTriple → Creds → Creds) (user : Bool)
    (r e s : word) (eff : SyscallEffect) (m : Model) : check_result :=
  let c := m_creds m
  let t := get c
  let pick (a cur : word) : word := if bv_eqb a ID_MINUS_ONE then cur else a
  let nr := pick r t.id_real
  let ne := pick e t.id_eff
  let ns := pick s t.id_saved
  if bv_eqb nr t.id_real && bv_eqb ne t.id_eff && bv_eqb ns t.id_saved then
    check_ret_only eff (Z_to_bv 64 0) m []
  else
    let is_old (x : word) : Bool :=
      bv_eqb x t.id_real || bv_eqb x t.id_eff || bv_eqb x t.id_saved
    if !(is_old nr && is_old ne && is_old ns) && !(creds_privileged c) then
      check_ret_only eff (errno_ret EPERM) m []
    else
      check_setid_result (setid_errnos (user && !(bv_eqb nr t.id_real))) (Z_to_bv 64 0)
        (with_creds (put (IdTriple.mkIdTriple nr ne ns) c) m) eff m

/-- An accepted `check_setid_result` is one of the arm's two outcomes:
the errno alternative or whatever `c2` accepts, given that `c2` accepts
the success shape at `mR`.  Rocq: `check_setid_result_sound_ok`. -/
theorem check_setid_result_sound_ok (errs : List Int) (r : word) (mR : Model)
    (c2 : Sys SyscallEffect) (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (hc2 : c2 i m (Ok (mkEffect r [] []) mR []))
    (h : check_setid_result errs r mR eff m = CheckOk m' evs) :
    alt (e <- errno_from errs ;; err_ret e) c2 i m (Ok eff m' evs) := by
  unfold check_setid_result at h
  split at h
  · rename_i ret
    split at h
    · rename_i hg
      obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj h
      rw [errno_ret_in_true] at hg
      obtain ⟨e, he, rfl⟩ := hg
      rw [alt_iff]
      left
      rw [errno_from, bind_choose_iff]
      exact ⟨e, he, rfl⟩
    · split at h
      · rename_i hr
        obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj h
        obtain rfl := (bv_eqb_eq ret r).mp hr
        rw [alt_iff]
        right
        exact hc2
      · cases h
  · cases h

/-- The acceptor never declines.  Rocq: `check_setid_result_no_unmodeled`. -/
theorem check_setid_result_no_unmodeled (errs : List Int) (r : word) (mR : Model)
    (eff : SyscallEffect) (m : Model) : check_setid_result errs r mR eff m ≠ CheckUnmodeled := by
  intro h
  unfold check_setid_result at h
  split at h
  · split at h
    · cases h
    · split at h <;> cases h
  · cases h

/-- The arm's two outcomes are accepted, with the spec's post-model,
provided the success return is not in the errno set (`hnr`, the file
header's point) and `c2` accepts only the success shape at `mR`.
Lean-only: the leaf Rocq's `creds_complete_leaf` re-derives in place. -/
theorem check_setid_result_complete_ok (errs : List Int) (r : word) (mR : Model)
    (c2 : Sys SyscallEffect) (i : SyscallInput) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (hnr : errno_ret_in errs r = false)
    (hc2 : c2 i m (Ok eff m' evs) → eff = mkEffect r [] [] ∧ m' = mR ∧ evs = [])
    (h : alt (e <- errno_from errs ;; err_ret e) c2 i m (Ok eff m' evs)) :
    check_setid_result errs r mR eff m = CheckOk m' evs := by
  rw [alt_iff] at h
  rcases h with h | h
  · rw [errno_from, bind_choose_iff] at h
    obtain ⟨e, he, hk⟩ := h
    rw [err_ret, ret_only, pure_iff] at hk
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj hk
    simp only [check_setid_result, errno_ret_in_intro _ _ he, ↓reduceIte]
  · obtain ⟨rfl, rfl, rfl⟩ := hc2 h
    simp only [check_setid_result, hnr, Bool.false_eq_true, ↓reduceIte, bv_eqb_refl]

/-- An installing arm never runs `Unmodeled`: the errno alternative ends
in `pure`, and `c2` is given not to.  Lean-only: the spec-side leaf Rocq's
`check_setid_complete_unmodeled` and `check_setresid_complete_unmodeled`
close in place by `creds_split; inv_ok`. -/
theorem errno_arm_never_unmodeled (errs : List Int) (c2 : Sys SyscallEffect) (i : SyscallInput)
    (m : Model) (hc2 : ¬ c2 i m Unmodeled)
    (h : alt (e <- errno_from errs ;; err_ret e) c2 i m Unmodeled) : False := by
  rw [alt_iff] at h
  rcases h with h | h
  · rw [errno_from, bind_choose_iff] at h
    obtain ⟨e, -, hk⟩ := h
    rw [err_ret, ret_only, pure_iff] at hk
    cases hk
  · exact hc2 h

/-- Accepting is sound for a reader.  Rocq: `check_getid_sound_ok`. -/
theorem check_getid_sound_ok (sel : Creds → word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput) (h : check_getid sel eff m = CheckOk m' evs) :
    getid_spec sel i m (Ok eff m' evs) := by
  unfold check_getid at h
  rw [check_ret_only_ok_iff] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  simp only [getid_spec, bind_get_model_iff]
  exact pure_ok _ i _

/-- Declining is sound for a reader, vacuously.  Rocq: `check_getid_sound_unmodeled`. -/
theorem check_getid_sound_unmodeled (sel : Creds → word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (h : check_getid sel eff m = CheckUnmodeled) :
    getid_spec sel i m Unmodeled := by
  unfold check_getid at h
  exact absurd h (check_ret_only_no_unmodeled _ _ _ _)

/-- Accepting is complete for a reader.  Rocq: `check_getid_complete_ok`. -/
theorem check_getid_complete_ok (sel : Creds → word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput) (h : getid_spec sel i m (Ok eff m' evs)) :
    check_getid sel eff m = CheckOk m' evs := by
  simp only [getid_spec, bind_get_model_iff] at h
  rw [ret_only, pure_iff] at h
  obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
  unfold check_getid
  exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- Declining is complete for a reader, vacuously.  Rocq: `check_getid_complete_unmodeled`. -/
theorem check_getid_complete_unmodeled (sel : Creds → word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (h : getid_spec sel i m Unmodeled) :
    check_getid sel eff m = CheckUnmodeled := by
  exfalso
  simp only [getid_spec, bind_get_model_iff] at h
  rw [ret_only, pure_iff] at h
  cases h

/-- Accepting is sound for setuid/setgid.  Rocq: `check_setid_sound_ok`.
The checker's `if`s are opened by `split at h`, and each hypothesis
selects the spec's arm by `ite_eq_left` / `ite_eq_right`. -/
theorem check_setid_sound_ok (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (v : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (h : check_setid get put user v eff m = CheckOk m' evs) :
    setid_spec get put user v i m (Ok eff m' evs) := by
  simp only [check_setid] at h
  simp only [setid_spec, bind_get_model_iff]
  split at h
  · rename_i hv
    rw [ite_eq_left hv]
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact pure_ok _ i _
  · rename_i hv
    rw [ite_eq_right hv]
    split at h
    · rename_i hp
      rw [ite_eq_left hp]
      exact check_setid_result_sound_ok _ _ _ _ i eff m m' evs
        (by rw [set_creds, bind_modify_iff]; exact pure_ok _ i _) h
    · rename_i hp
      rw [ite_eq_right hp]
      split at h
      · rename_i ho
        rw [ite_eq_left ho]
        exact check_setid_result_sound_ok _ _ _ _ i eff m m' evs
          (by rw [set_creds, bind_modify_iff]; exact pure_ok _ i _) h
      · rename_i ho
        rw [ite_eq_right ho]
        exact check_setid_result_sound_ok _ _ _ _ i eff m m' evs (by exact pure_ok _ i _) h

/-- The setuid/setgid checker never declines: every leaf is
`check_ret_only` or `check_setid_result`.  Lean-only, the fact Rocq's
`creds_split; creds_unmod_leaf` proves inside `check_setid_sound_unmodeled`. -/
theorem check_setid_no_unmodeled (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (v : word) (eff : SyscallEffect) (m : Model) :
    check_setid get put user v eff m ≠ CheckUnmodeled := by
  intro h
  simp only [check_setid] at h
  split at h
  · exact check_ret_only_no_unmodeled _ _ _ _ h
  · split at h
    · exact check_setid_result_no_unmodeled _ _ _ _ _ h
    · split at h <;> exact check_setid_result_no_unmodeled _ _ _ _ _ h

/-- Declining is sound for setuid/setgid, vacuously.  Rocq: `check_setid_sound_unmodeled`. -/
theorem check_setid_sound_unmodeled (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (v : word) (eff : SyscallEffect) (m : Model) (i : SyscallInput)
    (h : check_setid get put user v eff m = CheckUnmodeled) :
    setid_spec get put user v i m Unmodeled :=
  absurd h (check_setid_no_unmodeled get put user v eff m)

/-- Accepting is complete for setuid/setgid.  Rocq: `check_setid_complete_ok`.
The spec's applied `if`s are opened by `ite_sys_elim`; each installing
leaf is `check_setid_result_complete_ok` with the errno-set fact for its
success return. -/
theorem check_setid_complete_ok (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (v : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (h : setid_spec get put user v i m (Ok eff m' evs)) :
    check_setid get put user v eff m = CheckOk m' evs := by
  simp only [setid_spec, bind_get_model_iff] at h
  simp only [check_setid]
  rcases ite_sys_elim h with ⟨hv, h⟩ | ⟨hv, h⟩
  · rw [ite_eq_left hv]
    rw [err_ret, ret_only, pure_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  · rw [ite_eq_right hv]
    rcases ite_sys_elim h with ⟨hp, h⟩ | ⟨hp, h⟩
    · rw [ite_eq_left hp]
      exact check_setid_result_complete_ok _ _ _ _ i eff m m' evs (errno_ret_in_setid_zero _)
        (fun h2 => by
          rw [set_creds, bind_modify_iff] at h2
          unfold ret_only Monad.pure at h2
          exact outcome.Ok.inj h2) h
    · rw [ite_eq_right hp]
      rcases ite_sys_elim h with ⟨ho, h⟩ | ⟨ho, h⟩
      · rw [ite_eq_left ho]
        exact check_setid_result_complete_ok _ _ _ _ i eff m m' evs (errno_ret_in_setid_zero _)
          (fun h2 => by
            rw [set_creds, bind_modify_iff] at h2
            unfold ret_only Monad.pure at h2
            exact outcome.Ok.inj h2) h
      · rw [ite_eq_right ho]
        exact check_setid_result_complete_ok _ _ _ _ i eff m m' evs (errno_ret_in_setid_eperm _)
          (fun h2 => by
            rw [err_ret, ret_only, pure_iff] at h2
            exact outcome.Ok.inj h2) h

/-- Declining is complete for setuid/setgid, vacuously: no arm of the
spec runs `Unmodeled`.  Rocq: `check_setid_complete_unmodeled`. -/
theorem check_setid_complete_unmodeled (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (v : word) (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (h : setid_spec get put user v i m Unmodeled) :
    check_setid get put user v eff m = CheckUnmodeled := by
  exfalso
  simp only [setid_spec, bind_get_model_iff] at h
  rcases ite_sys_elim h with ⟨-, h⟩ | ⟨-, h⟩
  · rw [err_ret, ret_only, pure_iff] at h
    cases h
  · rcases ite_sys_elim h with ⟨-, h⟩ | ⟨-, h⟩
    · exact errno_arm_never_unmodeled _ _ i m
        (fun h2 => by
          rw [set_creds, bind_modify_iff] at h2
          unfold ret_only Monad.pure at h2
          cases h2) h
    · rcases ite_sys_elim h with ⟨-, h⟩ | ⟨-, h⟩
      · exact errno_arm_never_unmodeled _ _ i m
          (fun h2 => by
            rw [set_creds, bind_modify_iff] at h2
            unfold ret_only Monad.pure at h2
            cases h2) h
      · exact errno_arm_never_unmodeled _ _ i m
          (fun h2 => by
            rw [err_ret, ret_only, pure_iff] at h2
            cases h2) h

/-- Accepting is sound for setresuid/setresgid.  Rocq: `check_setresid_sound_ok`. -/
theorem check_setresid_sound_ok (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (r e s : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (h : check_setresid get put user r e s eff m = CheckOk m' evs) :
    setresid_spec get put user r e s i m (Ok eff m' evs) := by
  simp only [check_setresid] at h
  simp only [setresid_spec, bind_get_model_iff]
  rcases ite_eq_elim h with ⟨hn, h⟩ | ⟨hn, h⟩
  · refine ite_sys_pos hn ?_
    rw [check_ret_only_ok_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact pure_ok _ i _
  · refine ite_sys_neg hn ?_
    rcases ite_eq_elim h with ⟨hp, h⟩ | ⟨hp, h⟩
    · refine ite_sys_pos hp ?_
      rw [check_ret_only_ok_iff] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact pure_ok _ i _
    · refine ite_sys_neg hp ?_
      exact check_setid_result_sound_ok _ _ _ _ i eff m m' evs
        (by rw [set_creds, bind_modify_iff]; exact pure_ok _ i _) h

/-- The setresuid/setresgid checker never declines.  Lean-only, as
`check_setid_no_unmodeled` is. -/
theorem check_setresid_no_unmodeled (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (r e s : word) (eff : SyscallEffect) (m : Model) :
    check_setresid get put user r e s eff m ≠ CheckUnmodeled := by
  intro h
  simp only [check_setresid] at h
  rcases ite_eq_elim h with ⟨-, h⟩ | ⟨-, h⟩
  · exact check_ret_only_no_unmodeled _ _ _ _ h
  · rcases ite_eq_elim h with ⟨-, h⟩ | ⟨-, h⟩
    · exact check_ret_only_no_unmodeled _ _ _ _ h
    · exact check_setid_result_no_unmodeled _ _ _ _ _ h

/-- Declining is sound for setresuid/setresgid, vacuously.  Rocq:
`check_setresid_sound_unmodeled`. -/
theorem check_setresid_sound_unmodeled (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (r e s : word) (eff : SyscallEffect) (m : Model) (i : SyscallInput)
    (h : check_setresid get put user r e s eff m = CheckUnmodeled) :
    setresid_spec get put user r e s i m Unmodeled :=
  absurd h (check_setresid_no_unmodeled get put user r e s eff m)

/-- Accepting is complete for setresuid/setresgid.  Rocq: `check_setresid_complete_ok`. -/
theorem check_setresid_complete_ok (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (r e s : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (h : setresid_spec get put user r e s i m (Ok eff m' evs)) :
    check_setresid get put user r e s eff m = CheckOk m' evs := by
  simp only [setresid_spec, bind_get_model_iff] at h
  simp only [check_setresid]
  rcases ite_sys_elim h with ⟨hn, h⟩ | ⟨hn, h⟩
  · rw [ite_eq_left hn]
    rw [ret_only, pure_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  · rw [ite_eq_right hn]
    rcases ite_sys_elim h with ⟨hp, h⟩ | ⟨hp, h⟩
    · rw [ite_eq_left hp]
      rw [err_ret, ret_only, pure_iff] at h
      obtain ⟨rfl, rfl, rfl⟩ := outcome.Ok.inj h
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    · rw [ite_eq_right hp]
      exact check_setid_result_complete_ok _ _ _ _ i eff m m' evs (errno_ret_in_setid_zero _)
        (fun h2 => by
          rw [set_creds, bind_modify_iff] at h2
          unfold ret_only Monad.pure at h2
          exact outcome.Ok.inj h2) h

/-- Declining is complete for setresuid/setresgid, vacuously.  Rocq:
`check_setresid_complete_unmodeled`. -/
theorem check_setresid_complete_unmodeled (get : Creds → IdTriple)
    (put : IdTriple → Creds → Creds) (user : Bool) (r e s : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (h : setresid_spec get put user r e s i m Unmodeled) :
    check_setresid get put user r e s eff m = CheckUnmodeled := by
  exfalso
  simp only [setresid_spec, bind_get_model_iff] at h
  rcases ite_sys_elim h with ⟨-, h⟩ | ⟨-, h⟩
  · rw [ret_only, pure_iff] at h
    cases h
  · rcases ite_sys_elim h with ⟨-, h⟩ | ⟨-, h⟩
    · rw [err_ret, ret_only, pure_iff] at h
      cases h
    · exact errno_arm_never_unmodeled _ _ i m
        (fun h2 => by
          rw [set_creds, bind_modify_iff] at h2
          unfold ret_only Monad.pure at h2
          cases h2) h

/-! ## The witnesses — `Checks/Witness/Kernel/Sys.v` -/

/-- Rocq: `Checks.Witness.Kernel.Sys.getpid_witness`: the set_tid_address
witness, as the spec is its spec. -/
def getpid_witness : Model → outcome SyscallEffect := set_tid_address_witness

/-- Rocq: `Checks.Witness.Kernel.Sys.gettid_witness`. -/
def gettid_witness : Model → outcome SyscallEffect := set_tid_address_witness

/-- Rocq: `getpid_witness_ok`. -/
theorem getpid_witness_ok (i : SyscallInput) (m : Model) : getpid_spec i m (getpid_witness m) :=
  set_tid_address_witness_ok i m

/-- Rocq: `gettid_witness_ok`. -/
theorem gettid_witness_ok (i : SyscallInput) (m : Model) : gettid_spec i m (gettid_witness m) :=
  set_tid_address_witness_ok i m

/-- Rocq: `Checks.Witness.Kernel.Sys.setsid_witness`: -EPERM, the answer
the spec accepts on every model, before and after a success. -/
def setsid_witness (m : Model) : outcome SyscallEffect := ret_outcome (errno_ret EPERM) m

/-- Rocq: `setsid_witness_ok`. -/
theorem setsid_witness_ok (i : SyscallInput) (m : Model) : setsid_spec i m (setsid_witness m) := by
  simp only [setsid_spec, setsid_witness, bind_get_model_iff]
  refine ite_sys_intro (fun _ => ?_) (fun _ => ?_)
  · exact pure_ok _ i _
  · exact alt_l _ _ i _ _ (pure_ok _ i _)

/-- -ENOMEM is in both errno sets: it is the failure every installing
arm can show, so the witnesses fail with it.  Rocq: `In_ENOMEM_setid_errnos`. -/
theorem In_ENOMEM_setid_errnos (b : Bool) : ENOMEM ∈ setid_errnos b := by
  cases b <;> decide

/-- The errno alternative of an installing arm accepts a bare -ENOMEM at
`m`, whichever `c2` stands beside it.  Lean-only, for the three
witnesses below; Rocq reaches it by `alt_l; bind_step errno_from_witness
In_ENOMEM_setid_errnos; pure_ok` at each leaf. -/
theorem errno_arm_enomem_witness (errs : List Int) (c2 : Sys SyscallEffect) (i : SyscallInput)
    (m : Model) (hin : ENOMEM ∈ errs) :
    alt (e <- errno_from errs ;; err_ret e) c2 i m (ret_outcome (errno_ret ENOMEM) m) := by
  refine alt_l _ _ i m _ ?_
  rw [errno_from, bind_choose_iff]
  exact ⟨ENOMEM, hin, rfl⟩

/-- Rocq: `Checks.Witness.Kernel.Sys.getid_witness`: the selected field. -/
def getid_witness (sel : Creds → word) (m : Model) : outcome SyscallEffect :=
  ret_outcome (sel (m_creds m)) m

/-- Rocq: `getid_witness_ok`. -/
theorem getid_witness_ok (sel : Creds → word) (i : SyscallInput) (m : Model) :
    getid_spec sel i m (getid_witness sel m) := by
  simp only [getid_spec, getid_witness, bind_get_model_iff]
  exact pure_ok _ i _

/-- Rocq: `Checks.Witness.Kernel.Sys.setid_witness`: -EINVAL for the id
`-1`, else -ENOMEM, which every remaining arm's errno set holds. -/
def setid_witness (v : word) (m : Model) : outcome SyscallEffect :=
  if bv_eqb v ID_MINUS_ONE then ret_outcome (errno_ret EINVAL) m
  else ret_outcome (errno_ret ENOMEM) m

/-- Rocq: `setid_witness_ok`. -/
theorem setid_witness_ok (get : Creds → IdTriple) (put : IdTriple → Creds → Creds) (user : Bool)
    (v : word) (i : SyscallInput) (m : Model) :
    setid_spec get put user v i m (setid_witness v m) := by
  simp only [setid_spec, setid_witness, bind_get_model_iff]
  refine ite_sys_intro (fun hv => ?_) (fun hv => ?_)
  · rw [ite_eq_left hv]
    exact pure_ok _ i _
  · rw [ite_eq_right hv]
    refine ite_sys_intro (fun _ => ?_) (fun _ => ite_sys_intro (fun _ => ?_) (fun _ => ?_))
    · exact errno_arm_enomem_witness _ _ i m (In_ENOMEM_setid_errnos _)
    · exact errno_arm_enomem_witness _ _ i m (In_ENOMEM_setid_errnos _)
    · exact errno_arm_enomem_witness _ _ i m (In_ENOMEM_setid_errnos _)

/-- Rocq: `Checks.Witness.Kernel.Sys.setresid_witness`: the spec's own
two leading gates select 0 or -EPERM, and the installing arm fails with
-ENOMEM. -/
def setresid_witness (get : Creds → IdTriple) (r e s : word) (m : Model) :
    outcome SyscallEffect :=
  let t := get (m_creds m)
  let pick (a cur : word) : word := if bv_eqb a ID_MINUS_ONE then cur else a
  let nr := pick r t.id_real
  let ne := pick e t.id_eff
  let ns := pick s t.id_saved
  if bv_eqb nr t.id_real && bv_eqb ne t.id_eff && bv_eqb ns t.id_saved then
    ret_outcome (Z_to_bv 64 0) m
  else
    let is_old (x : word) : Bool :=
      bv_eqb x t.id_real || bv_eqb x t.id_eff || bv_eqb x t.id_saved
    if !(is_old nr && is_old ne && is_old ns) && !(creds_privileged (m_creds m)) then
      ret_outcome (errno_ret EPERM) m
    else
      ret_outcome (errno_ret ENOMEM) m

/-- Rocq: `setresid_witness_ok`. -/
theorem setresid_witness_ok (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (r e s : word) (i : SyscallInput) (m : Model) :
    setresid_spec get put user r e s i m (setresid_witness get r e s m) := by
  simp only [setresid_spec, setresid_witness, bind_get_model_iff]
  refine ite_sys_intro (fun hn => ?_) (fun hn => ?_)
  · rw [ite_eq_left hn]
    exact pure_ok _ i _
  · rw [ite_eq_right hn]
    refine ite_sys_intro (fun hp => ?_) (fun hp => ?_)
    · rw [ite_eq_left hp]
      exact pure_ok _ i _
    · rw [ite_eq_right hp]
      exact errno_arm_enomem_witness _ _ i m (In_ENOMEM_setid_errnos _)

/-! ## The frame lemmas -/

/-- Rocq: `VmMapsDisjoint.check_getpid_frame`, the Fork checker's by
application. -/
theorem check_getpid_frame (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_getpid eff m = CheckOk m' evs) : m_vmmaps m' = m_vmmaps m :=
  check_set_tid_address_frame eff m m' evs h

/-- Rocq: `VmMapsDisjoint.check_gettid_frame`. -/
theorem check_gettid_frame (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_gettid eff m = CheckOk m' evs) : m_vmmaps m' = m_vmmaps m :=
  check_set_tid_address_frame eff m m' evs h

/-- An accepted setsid leaves the VM ledger as it found it: the model
handed back is `m` or `with_setsid_succeeded (with_tid ret m)`, and both
rebuilders touch the process state alone (`State/Model.lean`).  Rocq:
`VmMapsDisjoint.check_setsid_frame`. -/
theorem check_setsid_frame (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_setsid eff m = CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  unfold check_setsid at h
  split at h
  · rcases ite_eq_elim h with ⟨-, h⟩ | ⟨-, h⟩
    · obtain ⟨rfl, -⟩ := check_result.CheckOk.inj h
      rfl
    · rcases ite_eq_elim h with ⟨-, h⟩ | ⟨-, h⟩
      · cases h
      · rcases ite_eq_elim h with ⟨-, h⟩ | ⟨-, h⟩
        · obtain ⟨rfl, -⟩ := check_result.CheckOk.inj h
          rfl
        · cases h
  · cases h

/-- Rocq: `VmMapsDisjoint.check_getid_frame`: a reader hands back the model
it was given. -/
theorem check_getid_frame (sel : Creds → word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_getid sel eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_getid at h
  rw [check_ret_only_ok_iff] at h
  obtain ⟨-, rfl, -⟩ := h
  rfl

/-- An accepted `check_setid_result` hands back `m` or `mR`.  Lean-only:
the fact Rocq's `vm_frame2` finds by destructing the acceptor in place. -/
theorem check_setid_result_model (errs : List Int) (r : word) (mR : Model) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_setid_result errs r mR eff m = CheckOk m' evs) :
    m' = m ∨ m' = mR := by
  unfold check_setid_result at h
  split at h
  · split at h
    · exact Or.inl (check_result.CheckOk.inj h).1.symm
    · split at h
      · exact Or.inr (check_result.CheckOk.inj h).1.symm
      · cases h
  · cases h

/-- An accepted setuid/setgid leaves the VM ledger alone: every post-model
is `m` or `with_creds _ m`, which rebuilds the process state alone.  Rocq:
`VmMapsDisjoint.check_setid_frame`. -/
theorem check_setid_frame (get : Creds → IdTriple) (put : IdTriple → Creds → Creds) (user : Bool)
    (v : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_setid get put user v eff m = CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  simp only [check_setid] at h
  split at h
  · rw [check_ret_only_ok_iff] at h
    obtain ⟨-, rfl, -⟩ := h
    rfl
  · split at h
    · rcases check_setid_result_model _ _ _ _ _ _ _ h with rfl | rfl <;> rfl
    · split at h
      · rcases check_setid_result_model _ _ _ _ _ _ _ h with rfl | rfl <;> rfl
      · rcases check_setid_result_model _ _ _ _ _ _ _ h with rfl | rfl <;> rfl

/-- The same for setresuid/setresgid.  Rocq: `VmMapsDisjoint.check_setresid_frame`. -/
theorem check_setresid_frame (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (r e s : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_setresid get put user r e s eff m = CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  simp only [check_setresid] at h
  rcases ite_eq_elim h with ⟨-, h⟩ | ⟨-, h⟩
  · rw [check_ret_only_ok_iff] at h
    obtain ⟨-, rfl, -⟩ := h
    rfl
  · rcases ite_eq_elim h with ⟨-, h⟩ | ⟨-, h⟩
    · rw [check_ret_only_ok_iff] at h
      obtain ⟨-, rfl, -⟩ := h
      rfl
    · rcases check_setid_result_model _ _ _ _ _ _ _ h with rfl | rfl <;> rfl

/-! # The second third: uname (160), prlimit64 (261) and prctl (167)

Appended by ticket C-Kernel-Sys-uname-prlimit-prctl below the id and
session half's frame lemmas, so that the earlier text and proofs stand as
they landed.  The order inside is Rocq's for `Checks/Sys/Kernel/Sys.v`
(prctl, uname, prlimit64), then the three witnesses of
`Checks/Witness/Kernel/Sys.v`, then the three frame lemmas of
`Checks/VmMapsDisjoint.v`.

TWO ACCEPTORS OVER A RECORDED VALUE.  `check_uname_copy` and
`check_rlim64_read` are one shape twice: a single write of a byte list
at the caller's pointer with a return of 0, equal to the recorded list
if the model holds one, and inside the spec's envelope (`utsname_wf`,
`rlim64_wf`) if it does not, in which case the list becomes the record.
That is the executable reading of the spec's `match m_utsname m with |
some bs => pure … | none => bs <- choose …`: the FIRST call of a run is
where the environment's answer enters the model, and every later call
must repeat it.  Rocq's `check_uname_copy_ok` / `check_rlim64_read_ok`
read the disjunction back out of an acceptance, and the soundness proofs
below hand each disjunct to the spec's arm.

WHERE `access_ok` STANDS.  `uname_spec` asks `access_okb` before it
walks the destination, `prlimit64_spec` walks first and asks only when
the walk fails; both checkers keep their spec's order, and the reason
each order is the arm's — `copy_to_user` runs `access_ok` over the whole
range before a byte moves (`_inline_copy_to_user`,
include/linux/uaccess.h:189-200, Linux v6.18.46, the test at :195), so a
destination `access_ok` refuses is -EFAULT with nothing written, while a
destination it allows but memory does not wholly back would take a
PREFIX and then fail, which the model cannot state and declines — is on
the specs and not restated here.

THE PROOFS take the checkers apart the way `Checks/Sys/Kernel/Time/Hrtimer.lean`
takes `check_nanosleep` apart: each Boolean gate is `cases hc : c` and
then `simp only [hc, …, ↓reduceIte]` on both sides, each `read_bytes_map`
and each recorded value is `rcases hx : e with _ | v`, and the two
Prop-valued gates — `prlimit64`'s soft > hard and `prctl`'s
`CAP_LAST_CAP < arg2`, both `Int` comparisons — are `by_cases` and
`ite_eq_left`/`ite_eq_right`.  `split at h` is used only
where every alternative closes by `cases h` or a rewrite: the two
acceptors' effect `match`, their `if` gates and `match bs0` in the two
`_no_unmodeled` lemmas, and the gates of the frame lemmas. -/

/-! ## prctl (167) -/

/-- Rocq: `Checks.Sys.Kernel.Sys.check_prctl`.
`SYSCALL_DEFINE5(prctl)` opens (kernel/sys.c:2518-2530, Linux v6.18.46, commit
1f99e9ab748f) by handing every option, at :2525-2527, to the LSM hook
`security_task_prctl` (security/security.c:3871-3887, Linux v6.18.46) and
returns whatever that answers other than -ENOSYS; for `PR_CAPBSET_READ` (23,
include/uapi/linux/prctl.h:71, Linux v6.18.46) the answer comes from
`cap_task_prctl` (security/commoncap.c:1291-1431, Linux v6.18.46): -EINVAL
unless `cap_valid(arg2)` (:1299-1300), else `!!cap_raised(old->cap_bset, arg2)`
(:1301), which is 1 for the full bounding set this model assumes (the premise is
on `Sys/Kernel/Sys.lean`).  `cap_valid` is `((x) >= 0 && (x) <= CAP_LAST_CAP)`
over the whole `unsigned long` (include/uapi/linux/capability.h:425, Linux
v6.18.46), `CAP_LAST_CAP` being `CAP_CHECKPOINT_RESTORE`, 40 (:421-423).  Every
other option is the spec's decline, and the checker's. -/
def check_prctl (option_ arg2 : word) (eff : SyscallEffect) (m : Model) : check_result :=
  if !(bv_unsigned option_ == PR_CAPBSET_READ) then CheckUnmodeled
  else if CAP_LAST_CAP < bv_unsigned arg2 then check_ret_only eff (errno_ret EINVAL) m []
  else check_ret_only eff (Z_to_bv 64 1) m []

/-- Rocq: `check_prctl_sound_ok`. -/
theorem check_prctl_sound_ok (option_ arg2 : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_prctl option_ arg2 eff m = CheckOk m' evs) (i : SyscallInput) :
    prctl_spec option_ arg2 i m (Ok eff m' evs) := by
  unfold check_prctl at h
  unfold prctl_spec
  cases hopt : (bv_unsigned option_ == PR_CAPBSET_READ) with
  | false => simp only [hopt, Bool.not_false, ↓reduceIte, reduceCtorEq] at h
  | true =>
    simp only [hopt, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hc : CAP_LAST_CAP < bv_unsigned arg2
    · rw [ite_eq_left hc] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _
    · rw [ite_eq_right hc] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      exact pure_ok _ i _

/-- Rocq: `check_prctl_sound_unmodeled`: the checker's one decline is
the spec's option gate; neither `check_ret_only` arm can decline. -/
theorem check_prctl_sound_unmodeled (option_ arg2 : word) (eff : SyscallEffect) (m : Model)
    (h : check_prctl option_ arg2 eff m = CheckUnmodeled) (i : SyscallInput) :
    prctl_spec option_ arg2 i m Unmodeled := by
  unfold check_prctl at h
  unfold prctl_spec
  cases hopt : (bv_unsigned option_ == PR_CAPBSET_READ) with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
    simp only [hopt, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    exfalso
    by_cases hc : CAP_LAST_CAP < bv_unsigned arg2
    · rw [ite_eq_left hc] at h
      exact check_ret_only_no_unmodeled _ _ _ _ h
    · rw [ite_eq_right hc] at h
      exact check_ret_only_no_unmodeled _ _ _ _ h

/-- Rocq: `check_prctl_complete_ok`. -/
theorem check_prctl_complete_ok (option_ arg2 : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (h : prctl_spec option_ arg2 i m (Ok eff m' evs)) :
    check_prctl option_ arg2 eff m = CheckOk m' evs := by
  unfold prctl_spec at h
  unfold check_prctl
  cases hopt : (bv_unsigned option_ == PR_CAPBSET_READ) with
  | false => simp only [hopt, Bool.not_false, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h
  | true =>
    simp only [hopt, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hc : CAP_LAST_CAP < bv_unsigned arg2
    · rw [ite_eq_left hc] at h ⊢
      simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
    · rw [ite_eq_right hc] at h ⊢
      simp only [ret_only, pure_iff, outcome.Ok.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- Rocq: `check_prctl_complete_unmodeled`: the spec declines only at
the option gate, which reads no effect. -/
theorem check_prctl_complete_unmodeled (option_ arg2 : word) (i : SyscallInput) (m : Model)
    (h : prctl_spec option_ arg2 i m Unmodeled) (eff : SyscallEffect) :
    check_prctl option_ arg2 eff m = CheckUnmodeled := by
  unfold prctl_spec at h
  unfold check_prctl
  cases hopt : (bv_unsigned option_ == PR_CAPBSET_READ) with
  | false => simp only [Bool.not_false, ↓reduceIte]
  | true =>
    simp only [hopt, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    exfalso
    by_cases hc : CAP_LAST_CAP < bv_unsigned arg2
    · rw [ite_eq_left hc] at h
      simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
    · rw [ite_eq_right hc] at h
      simp only [ret_only, pure_iff, reduceCtorEq] at h

/-! ## uname (160) -/

/-- Rocq: `Checks.Sys.Kernel.Sys.check_uname_copy`.
The struct as delivered: one write at `name`, a return of 0
(`SYSCALL_DEFINE1(newuname)`, kernel/sys.c:1351-1366, Linux v6.18.46, commit
1f99e9ab748f, the `return 0` at :1365) and nothing else in the effect, its bytes
equal to the record `bs0` when there is one and inside `utsname_wf` when there
is not — in which case the model records them.  The `struct new_utsname` the
write must be is include/uapi/linux/utsname.h:25-32 (Linux v6.18.46): six
members of `__NEW_UTS_LEN + 1` bytes, 390 in all, which `utsname_wf`'s length
conjunct fixes. -/
def check_uname_copy (name : word) (bs0 : Option (List byte)) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match eff with
  | SyscallEffect.mkEffectU r [(a, bs)] [] [] [] [] =>
    if !(bv_eqb r (Z_to_bv 64 0) && bv_eqb a name) then CheckReject
    else
      match bs0 with
      | some b0 => if listN_eqb bs b0 then CheckOk m [] else CheckReject
      | none => if utsname_wf bs then CheckOk (with_utsname bs m) [] else CheckReject
  | _ => CheckReject

/-- Rocq: `check_uname_copy_no_unmodeled`: the acceptor answers
`CheckOk` or `CheckReject` and never declines. -/
theorem check_uname_copy_no_unmodeled (name : word) (bs0 : Option (List byte))
    (eff : SyscallEffect) (m : Model) : check_uname_copy name bs0 eff m ≠ CheckUnmodeled := by
  intro h
  unfold check_uname_copy at h
  split at h
  · split at h
    · cases h
    · split at h
      · split at h <;> cases h
      · split at h <;> cases h
  · cases h

/-- Rocq: `check_uname_copy_ok`.  What an acceptance says: the effect
is the one write of some `bs` at `name` returning 0 with no events, and
either `bs` is the record and the model stands, or there was no record,
`bs` is inside the envelope and the model now records it. -/
theorem check_uname_copy_ok (name : word) (bs0 : Option (List byte)) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_uname_copy name bs0 eff m = CheckOk m' evs) :
    ∃ bs, eff = mkEffect (Z_to_bv 64 0) [(name, bs)] [] ∧ evs = [] ∧
      ((bs0 = some bs ∧ m' = m) ∨ (bs0 = none ∧ utsname_wf bs = true ∧ m' = with_utsname bs m)) := by
  unfold check_uname_copy at h
  split at h
  next r a bs =>
    cases hg : (bv_eqb r (Z_to_bv 64 0) && bv_eqb a name) with
    | false => simp only [hg, Bool.not_false, ↓reduceIte, reduceCtorEq] at h
    | true =>
      simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      simp only [Bool.and_eq_true, bv_eqb_eq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      refine ⟨bs, rfl, ?_⟩
      cases bs0 with
      | some b0 =>
        cases hl : listN_eqb bs b0 with
        | false => simp only [hl, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
        | true =>
          simp only [hl, ↓reduceIte, check_result.CheckOk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [listN_eqb_eq] at hl
          subst hl
          exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
      | none =>
        cases hw : utsname_wf bs with
        | false => simp only [hw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
        | true =>
          simp only [hw, ↓reduceIte, check_result.CheckOk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨rfl, Or.inr ⟨rfl, rfl, rfl⟩⟩
  next => cases h

/-- Rocq: `Checks.Sys.Kernel.Sys.check_uname`.
`SYSCALL_DEFINE1(newuname)` (kernel/sys.c:1351-1366, Linux v6.18.46, commit
1f99e9ab748f) copies the 390 bytes out with one `copy_to_user` and answers
-EFAULT when it fails (:1358-1359); the `override_release` and
`override_architecture` calls after it (:1361-1364) fire for no process under
the launcher premise `Sys/Kernel/Sys.lean` states — on `uts_machine_chars` for
PER_LINUX32, on `uname_spec` for UNAME26: the launcher runs PER_LINUX with
neither flag.  A premise and not a fact of the image, because the `execve` that
started the process keeps both — `SET_PERSONALITY`
(arch/riscv/include/asm/elf.h:137-142, Linux v6.18.46) keeps an inherited
PER_LINUX32 under `CONFIG_COMPAT` and, in every configuration, every flag
outside `PER_MASK` (include/uapi/linux/personality.h:66), UNAME26 (:12) among
them — and `personality` (92) has no arm.  The checker's first gate is the
copy's own `access_ok` (riscv64's `#define` at
arch/riscv/include/asm/uaccess.h:42, Linux v6.18.46, over `__access_ok`,
include/asm-generic/access_ok.h:31-41, Linux v6.18.46; `Sys/Uaccess.lean`'s
header says why the two agree), which `_inline_copy_to_user` asks
(include/linux/uaccess.h:189-200, Linux v6.18.46, at :195): a destination it
refuses is -EFAULT with nothing written, whatever memory holds.  A destination
it allows but the writable view does not wholly back is declined, for the
partial-copy reason on `uname_spec`; one it wholly backs runs `check_uname_copy`
over the record. -/
def check_uname (i : SyscallInput) (name : word) (eff : SyscallEffect) (m : Model) :
    check_result :=
  if !(access_okb name NEW_UTSNAME_SIZE) then check_ret_only eff (errno_ret EFAULT) m []
  else
    match read_bytes_map i.in_wmem name (Z_to_bv 64 NEW_UTSNAME_SIZE) with
    | none => CheckUnmodeled
    | some _ => check_uname_copy name (m_utsname m) eff m

/-- Rocq: `check_uname_sound_ok`. -/
theorem check_uname_sound_ok (i : SyscallInput) (name : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_uname i name eff m = CheckOk m' evs) :
    uname_spec name i m (Ok eff m' evs) := by
  unfold check_uname at h
  unfold uname_spec
  refine bind_ok0 _ _ _ _ _ _ _ _ _ (input_ok i m) ?_
  refine bind_ok0 _ _ _ _ _ _ _ _ _ (get_model_ok i m) ?_
  cases hacc : access_okb name NEW_UTSNAME_SIZE with
  | false =>
    simp only [hacc, Bool.not_false, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    exact pure_ok _ i _
  | true =>
    simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    rcases hrd : read_bytes_map i.in_wmem name (Z_to_bv 64 NEW_UTSNAME_SIZE) with _ | _
    · simp only [hrd, reduceCtorEq] at h
    · simp only [hrd] at h ⊢
      obtain ⟨bs, rfl, rfl, hcase⟩ := check_uname_copy_ok _ _ _ _ _ _ h
      rcases hcase with ⟨hb, rfl⟩ | ⟨hb, hwf, rfl⟩
      · simp only [hb]
        exact pure_ok _ i _
      · simp only [hb]
        exact bind_ok0 _ _ _ _ _ _ _ _ _ (choose_ok _ bs i m hwf)
          (bind_ok0 _ _ _ _ _ _ _ _ _ (modify_ok _ i m) (pure_ok _ i _))

/-- Rocq: `check_uname_sound_unmodeled`: the one decline is a
destination `access_ok` allows and the walk does not wholly back. -/
theorem check_uname_sound_unmodeled (i : SyscallInput) (name : word) (eff : SyscallEffect)
    (m : Model) (h : check_uname i name eff m = CheckUnmodeled) : uname_spec name i m Unmodeled := by
  unfold check_uname at h
  unfold uname_spec
  refine bind_unmodeled2 _ _ _ _ _ _ _ (input_ok i m) ?_
  refine bind_unmodeled2 _ _ _ _ _ _ _ (get_model_ok i m) ?_
  cases hacc : access_okb name NEW_UTSNAME_SIZE with
  | false =>
    simp only [hacc, Bool.not_false, ↓reduceIte] at h
    exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
  | true =>
    simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    rcases hrd : read_bytes_map i.in_wmem name (Z_to_bv 64 NEW_UTSNAME_SIZE) with _ | _
    · exact unmodeled_intro i m
    · simp only [hrd] at h
      exact absurd h (check_uname_copy_no_unmodeled _ _ _ _)

/-- Rocq: `check_uname_complete_ok`. -/
theorem check_uname_complete_ok (i : SyscallInput) (name : word) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event) (h : uname_spec name i m (Ok eff m' evs)) :
    check_uname i name eff m = CheckOk m' evs := by
  simp only [uname_spec, bind_input_iff, bind_get_model_iff] at h
  unfold check_uname
  cases hacc : access_okb name NEW_UTSNAME_SIZE with
  | false =>
    simp only [hacc, Bool.not_false, ↓reduceIte, err_ret, ret_only, pure_iff,
      outcome.Ok.injEq] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  | true =>
    simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    rcases hrd : read_bytes_map i.in_wmem name (Z_to_bv 64 NEW_UTSNAME_SIZE) with _ | _
    · simp only [hrd, unmodeled_iff, reduceCtorEq] at h
    · simp only [hrd] at h ⊢
      unfold check_uname_copy
      rcases hu : m_utsname m with _ | bs0
      · simp only [hu, bind_choose_iff, set_utsname, bind_modify_iff, pure_iff,
          outcome.Ok.injEq] at h
        obtain ⟨bs, hwf, rfl, rfl, rfl⟩ := h
        simp only [bv_eqb_refl, Bool.and_self, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, hwf]
      · simp only [hu, pure_iff, outcome.Ok.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have hl : listN_eqb bs0 bs0 = true := (listN_eqb_eq _ _).mpr rfl
        simp only [bv_eqb_refl, Bool.and_self, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, hl]

/-- Rocq: `check_uname_complete_unmodeled`. -/
theorem check_uname_complete_unmodeled (i : SyscallInput) (name : word) (m : Model)
    (h : uname_spec name i m Unmodeled) (eff : SyscallEffect) :
    check_uname i name eff m = CheckUnmodeled := by
  simp only [uname_spec, bind_input_iff, bind_get_model_iff] at h
  unfold check_uname
  cases hacc : access_okb name NEW_UTSNAME_SIZE with
  | false =>
    simp only [hacc, Bool.not_false, ↓reduceIte, err_ret, ret_only, pure_iff, reduceCtorEq] at h
  | true =>
    simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
    rcases hrd : read_bytes_map i.in_wmem name (Z_to_bv 64 NEW_UTSNAME_SIZE) with _ | _
    · rfl
    · exfalso
      simp only [hrd] at h
      rcases hu : m_utsname m with _ | bs0
      · simp only [hu, bind_choose_iff, set_utsname, bind_modify_iff, pure_iff, reduceCtorEq,
          and_false, exists_false] at h
      · simp only [hu, pure_iff, reduceCtorEq] at h

/-! ## prlimit64 (261) -/

/-- Rocq: `Checks.Sys.Kernel.Sys.check_rlim64_read`.
`check_uname_copy`'s shape over the sixteen-byte `struct rlimit64`
(include/uapi/linux/resource.h:50-53, Linux v6.18.46, commit 1f99e9ab748f): one
write at `old_rlim` — the `copy_to_user` of `SYSCALL_DEFINE4(prlimit64)`,
kernel/sys.c:1784-1787, Linux v6.18.46 — returning 0, equal to the recorded pair
when there is one and inside `rlim64_wf` (sixteen bytes, soft ≤ hard, the
invariant `do_prlimit` keeps at kernel/sys.c:1511-1512, Linux v6.18.46) when
there is not, in which case the model records it. -/
def check_rlim64_read (old_rlim : word) (bs0 : Option (List byte)) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match eff with
  | SyscallEffect.mkEffectU r [(a, bs)] [] [] [] [] =>
    if !(bv_eqb r (Z_to_bv 64 0) && bv_eqb a old_rlim) then CheckReject
    else
      match bs0 with
      | some b0 => if listN_eqb bs b0 then CheckOk m [] else CheckReject
      | none => if rlim64_wf bs then CheckOk (with_rlimit_core bs m) [] else CheckReject
  | _ => CheckReject

/-- Rocq: `check_rlim64_read_no_unmodeled`. -/
theorem check_rlim64_read_no_unmodeled (old_rlim : word) (bs0 : Option (List byte))
    (eff : SyscallEffect) (m : Model) : check_rlim64_read old_rlim bs0 eff m ≠ CheckUnmodeled := by
  intro h
  unfold check_rlim64_read at h
  split at h
  · split at h
    · cases h
    · split at h
      · split at h <;> cases h
      · split at h <;> cases h
  · cases h

/-- Rocq: `check_rlim64_read_ok`, `check_uname_copy_ok`'s statement
over `rlim64_wf` and `with_rlimit_core`. -/
theorem check_rlim64_read_ok (old_rlim : word) (bs0 : Option (List byte)) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (h : check_rlim64_read old_rlim bs0 eff m = CheckOk m' evs) :
    ∃ bs, eff = mkEffect (Z_to_bv 64 0) [(old_rlim, bs)] [] ∧ evs = [] ∧
      ((bs0 = some bs ∧ m' = m) ∨
        (bs0 = none ∧ rlim64_wf bs = true ∧ m' = with_rlimit_core bs m)) := by
  unfold check_rlim64_read at h
  split at h
  next r a bs =>
    cases hg : (bv_eqb r (Z_to_bv 64 0) && bv_eqb a old_rlim) with
    | false => simp only [hg, Bool.not_false, ↓reduceIte, reduceCtorEq] at h
    | true =>
      simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      simp only [Bool.and_eq_true, bv_eqb_eq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      refine ⟨bs, rfl, ?_⟩
      cases bs0 with
      | some b0 =>
        cases hl : listN_eqb bs b0 with
        | false => simp only [hl, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
        | true =>
          simp only [hl, ↓reduceIte, check_result.CheckOk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [listN_eqb_eq] at hl
          subst hl
          exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
      | none =>
        cases hw : rlim64_wf bs with
        | false => simp only [hw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
        | true =>
          simp only [hw, ↓reduceIte, check_result.CheckOk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨rfl, Or.inr ⟨rfl, rfl, rfl⟩⟩
  next => cases h

/-- Rocq: `Checks.Sys.Kernel.Sys.check_prlimit64`.  `SYSCALL_DEFINE4(prlimit64)`
(kernel/sys.c:1729-1792, Linux v6.18.46, commit 1f99e9ab748f) and
`do_prlimit` (kernel/sys.c:1500-1561, Linux v6.18.46), gate for gate in the
spec's order; the kernel line behind each answer is in the module
header's `prlimit64` bullet.  What the definition does not say: the four
leading declines are the spec's — a pid other than 0 names a task this
one-process model does not carry, a resource other than `RLIMIT_CORE`
(4, include/uapi/asm-generic/resource.h:20, Linux v6.18.46) has no record
here, neither pointer is a call that reads and writes nothing
observable, both pointers a read-and-write whose two effects the ledger
cannot order — and the write arm's decline without a recorded pair is
the hard-limit comparison at :1526-1528, which has nothing to compare
against until a read has recorded the pair. -/
def check_prlimit64 (i : SyscallInput) (pid resource new_rlim old_rlim : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if !(w_is0 pid) then CheckUnmodeled
  else if !(bv_unsigned resource == RLIMIT_CORE) then CheckUnmodeled
  else if w_is0 new_rlim && w_is0 old_rlim then CheckUnmodeled
  else if !(w_is0 new_rlim) && !(w_is0 old_rlim) then CheckUnmodeled
  else if w_is0 new_rlim then
    match read_bytes_map i.in_wmem old_rlim (Z_to_bv 64 16) with
    | none =>
      if !(access_okb old_rlim 16) then check_ret_only eff (errno_ret EFAULT) m []
      else CheckUnmodeled
    | some _ => check_rlim64_read old_rlim (m_rlimit_core m) eff m
  else
    match m_rlimit_core m with
    | none => CheckUnmodeled
    | some bs0 =>
      match read_bytes_map i.in_mem new_rlim (Z_to_bv 64 16) with
      | none =>
        if !(access_okb new_rlim 16) then check_ret_only eff (errno_ret EFAULT) m []
        else CheckUnmodeled
      | some nb =>
        if bv_unsigned (rlim64_hard nb) < bv_unsigned (rlim64_soft nb) then
          check_ret_only_copyins [(new_rlim, 16)] eff (errno_ret EINVAL) m []
        else if !(bv_eqb (rlim64_hard nb) (rlim64_hard bs0)) then CheckUnmodeled
        else check_ret_only_copyins [(new_rlim, 16)] eff (Z_to_bv 64 0) (with_rlimit_core nb m) []

/-- Rocq: `check_prlimit64_sound_ok`. -/
theorem check_prlimit64_sound_ok (i : SyscallInput) (pid resource new_rlim old_rlim : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_prlimit64 i pid resource new_rlim old_rlim eff m = CheckOk m' evs) :
    prlimit64_spec pid resource new_rlim old_rlim i m (Ok eff m' evs) := by
  unfold check_prlimit64 at h
  unfold prlimit64_spec
  cases hp : w_is0 pid with
  | false => simp only [hp, Bool.not_false, ↓reduceIte, reduceCtorEq] at h
  | true =>
  simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hr : (bv_unsigned resource == RLIMIT_CORE) with
  | false => simp only [hr, Bool.not_false, ↓reduceIte, reduceCtorEq] at h
  | true =>
  simp only [hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hn : w_is0 new_rlim with
  | true =>
    cases ho : w_is0 old_rlim with
    | true => simp only [hn, ho, Bool.and_self, ↓reduceIte, reduceCtorEq] at h
    | false =>
      simp only [hn, ho, Bool.and_false, Bool.not_true, Bool.not_false, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte] at h ⊢
      refine bind_ok0 _ _ _ _ _ _ _ _ _ (input_ok i m) ?_
      refine bind_ok0 _ _ _ _ _ _ _ _ _ (get_model_ok i m) ?_
      rcases hrd : read_bytes_map i.in_wmem old_rlim (Z_to_bv 64 16) with _ | _
      · simp only [hrd] at h ⊢
        cases hacc : access_okb old_rlim 16 with
        | false =>
          simp only [hacc, Bool.not_false, ↓reduceIte] at h ⊢
          obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
          exact pure_ok _ i _
        | true => simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
      · simp only [hrd] at h ⊢
        obtain ⟨bs, rfl, rfl, hcase⟩ := check_rlim64_read_ok _ _ _ _ _ _ h
        rcases hcase with ⟨hb, rfl⟩ | ⟨hb, hwf, rfl⟩
        · simp only [hb]
          exact pure_ok _ i _
        · simp only [hb]
          exact bind_ok0 _ _ _ _ _ _ _ _ _ (choose_ok _ bs i m hwf)
            (bind_ok0 _ _ _ _ _ _ _ _ _ (modify_ok _ i m) (pure_ok _ i _))
  | false =>
    cases ho : w_is0 old_rlim with
    | false =>
      simp only [hn, ho, Bool.and_self, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
        reduceCtorEq] at h
    | true =>
      simp only [hn, ho, Bool.false_and, Bool.not_false, Bool.not_true, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte] at h ⊢
      refine bind_ok0 _ _ _ _ _ _ _ _ _ (input_ok i m) ?_
      refine bind_ok0 _ _ _ _ _ _ _ _ _ (get_model_ok i m) ?_
      rcases hl : m_rlimit_core m with _ | bs0
      · simp only [hl, reduceCtorEq] at h
      · simp only [hl] at h ⊢
        rcases hrd : read_bytes_map i.in_mem new_rlim (Z_to_bv 64 16) with _ | nb
        · simp only [hrd] at h ⊢
          cases hacc : access_okb new_rlim 16 with
          | false =>
            simp only [hacc, Bool.not_false, ↓reduceIte] at h ⊢
            obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
            exact pure_ok _ i _
          | true =>
            simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
        · simp only [hrd] at h ⊢
          by_cases hlt : bv_unsigned (rlim64_hard nb) < bv_unsigned (rlim64_soft nb)
          · rw [ite_eq_left hlt] at h ⊢
            obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
            exact record_copyins_ok_empty _ _ i _ _ _ [] rfl (pure_ok _ i _)
          · rw [ite_eq_right hlt] at h ⊢
            cases heq : bv_eqb (rlim64_hard nb) (rlim64_hard bs0) with
            | false => simp only [heq, Bool.not_false, ↓reduceIte, reduceCtorEq] at h
            | true =>
              simp only [heq, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
              obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
              exact record_copyins_ok_empty _ _ i _ _ _ [] rfl
                (bind_ok0 _ _ _ _ _ _ _ _ _ (modify_ok _ i m) (pure_ok _ i _))

/-- Rocq: `check_prlimit64_sound_unmodeled`: every decline of the
checker is one of the spec's — the four gates, a short mapping on either
side, a write with no record, a hard limit that moves. -/
theorem check_prlimit64_sound_unmodeled (i : SyscallInput) (pid resource new_rlim old_rlim : word)
    (eff : SyscallEffect) (m : Model)
    (h : check_prlimit64 i pid resource new_rlim old_rlim eff m = CheckUnmodeled) :
    prlimit64_spec pid resource new_rlim old_rlim i m Unmodeled := by
  unfold check_prlimit64 at h
  unfold prlimit64_spec
  cases hp : w_is0 pid with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
  simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hr : (bv_unsigned resource == RLIMIT_CORE) with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
  simp only [hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hn : w_is0 new_rlim with
  | true =>
    cases ho : w_is0 old_rlim with
    | true =>
      simp only [Bool.and_self, ↓reduceIte]
      exact unmodeled_intro i m
    | false =>
      simp only [hn, ho, Bool.and_false, Bool.not_true, Bool.not_false, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte] at h ⊢
      refine bind_unmodeled2 _ _ _ _ _ _ _ (input_ok i m) ?_
      refine bind_unmodeled2 _ _ _ _ _ _ _ (get_model_ok i m) ?_
      rcases hrd : read_bytes_map i.in_wmem old_rlim (Z_to_bv 64 16) with _ | _
      · simp only [hrd] at h
        cases hacc : access_okb old_rlim 16 with
        | false =>
          simp only [hacc, Bool.not_false, ↓reduceIte] at h
          exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact unmodeled_intro i m
      · simp only [hrd] at h
        exact absurd h (check_rlim64_read_no_unmodeled _ _ _ _)
  | false =>
    cases ho : w_is0 old_rlim with
    | false =>
      simp only [Bool.and_self, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      exact unmodeled_intro i m
    | true =>
      simp only [hn, ho, Bool.false_and, Bool.not_false, Bool.not_true, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte] at h ⊢
      refine bind_unmodeled2 _ _ _ _ _ _ _ (input_ok i m) ?_
      refine bind_unmodeled2 _ _ _ _ _ _ _ (get_model_ok i m) ?_
      rcases hl : m_rlimit_core m with _ | bs0
      · exact unmodeled_intro i m
      · simp only [hl] at h
        rcases hrd : read_bytes_map i.in_mem new_rlim (Z_to_bv 64 16) with _ | nb
        · simp only [hrd] at h
          cases hacc : access_okb new_rlim 16 with
          | false =>
            simp only [hacc, Bool.not_false, ↓reduceIte] at h
            exact absurd h (check_ret_only_no_unmodeled _ _ _ _)
          | true =>
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            exact unmodeled_intro i m
        · simp only [hrd] at h ⊢
          apply record_copyins_unmodeled
          by_cases hlt : bv_unsigned (rlim64_hard nb) < bv_unsigned (rlim64_soft nb)
          · rw [ite_eq_left hlt] at h
            exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)
          · rw [ite_eq_right hlt] at h ⊢
            cases heq : bv_eqb (rlim64_hard nb) (rlim64_hard bs0) with
            | false =>
              simp only [Bool.not_false, ↓reduceIte]
              exact unmodeled_intro i m
            | true =>
              simp only [heq, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
              exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)

/-- Rocq: `check_prlimit64_complete_ok`. -/
theorem check_prlimit64_complete_ok (i : SyscallInput) (pid resource new_rlim old_rlim : word)
    (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (h : prlimit64_spec pid resource new_rlim old_rlim i m (Ok eff m' evs)) :
    check_prlimit64 i pid resource new_rlim old_rlim eff m = CheckOk m' evs := by
  unfold prlimit64_spec at h
  unfold check_prlimit64
  cases hp : w_is0 pid with
  | false => simp only [hp, Bool.not_false, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h
  | true =>
  simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hr : (bv_unsigned resource == RLIMIT_CORE) with
  | false => simp only [hr, Bool.not_false, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h
  | true =>
  simp only [hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hn : w_is0 new_rlim with
  | true =>
    cases ho : w_is0 old_rlim with
    | true => simp only [hn, ho, Bool.and_self, ↓reduceIte, unmodeled_iff, reduceCtorEq] at h
    | false =>
      simp only [hn, ho, Bool.and_false, Bool.not_true, Bool.not_false, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte, bind_input_iff, bind_get_model_iff] at h ⊢
      rcases hrd : read_bytes_map i.in_wmem old_rlim (Z_to_bv 64 16) with _ | _
      · simp only [hrd] at h ⊢
        cases hacc : access_okb old_rlim 16 with
        | false =>
          simp only [hacc, Bool.not_false, ↓reduceIte, err_ret, ret_only, pure_iff,
            outcome.Ok.injEq] at h ⊢
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
        | true =>
          simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, unmodeled_iff,
            reduceCtorEq] at h
      · simp only [hrd] at h ⊢
        unfold check_rlim64_read
        rcases hl : m_rlimit_core m with _ | bs0
        · simp only [hl, bind_choose_iff, set_rlimit_core, bind_modify_iff, pure_iff,
            outcome.Ok.injEq] at h
          obtain ⟨bs, hwf, rfl, rfl, rfl⟩ := h
          simp only [bv_eqb_refl, Bool.and_self, Bool.not_true, Bool.false_eq_true,
            ↓reduceIte, hwf]
        · simp only [hl, pure_iff, outcome.Ok.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          have hl' : listN_eqb bs0 bs0 = true := (listN_eqb_eq _ _).mpr rfl
          simp only [bv_eqb_refl, Bool.and_self, Bool.not_true, Bool.false_eq_true,
            ↓reduceIte, hl']
  | false =>
    cases ho : w_is0 old_rlim with
    | false =>
      simp only [hn, ho, Bool.and_self, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
        unmodeled_iff, reduceCtorEq] at h
    | true =>
      simp only [hn, ho, Bool.false_and, Bool.not_false, Bool.not_true, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte, bind_input_iff, bind_get_model_iff] at h ⊢
      rcases hl : m_rlimit_core m with _ | bs0
      · simp only [hl, unmodeled_iff, reduceCtorEq] at h
      · simp only [hl] at h ⊢
        rcases hrd : read_bytes_map i.in_mem new_rlim (Z_to_bv 64 16) with _ | nb
        · simp only [hrd] at h ⊢
          cases hacc : access_okb new_rlim 16 with
          | false =>
            simp only [hacc, Bool.not_false, ↓reduceIte, err_ret, ret_only, pure_iff,
              outcome.Ok.injEq] at h ⊢
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
          | true =>
            simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, unmodeled_iff,
              reduceCtorEq] at h
        · simp only [hrd] at h ⊢
          obtain ⟨core, hcore, rfl⟩ := record_copyins_ok_inv _ _ i m eff m' evs h
          by_cases hlt : bv_unsigned (rlim64_hard nb) < bv_unsigned (rlim64_soft nb)
          · rw [ite_eq_left hlt] at hcore ⊢
            simp only [err_ret, ret_only, pure_iff, outcome.Ok.injEq] at hcore
            obtain ⟨rfl, rfl, rfl⟩ := hcore
            simp only [mkEffect, List.append_nil]
            exact check_ret_only_copyins_refl _ _ _ _
          · rw [ite_eq_right hlt] at hcore ⊢
            cases heq : bv_eqb (rlim64_hard nb) (rlim64_hard bs0) with
            | false => simp only [heq, Bool.not_false, ↓reduceIte, unmodeled_iff, reduceCtorEq] at hcore
            | true =>
              simp only [heq, Bool.not_true, Bool.false_eq_true, ↓reduceIte, set_rlimit_core,
                bind_modify_iff, ret_only, pure_iff, outcome.Ok.injEq] at hcore ⊢
              obtain ⟨rfl, rfl, rfl⟩ := hcore
              simp only [mkEffect, List.append_nil]
              exact check_ret_only_copyins_refl _ _ _ _

/-- Rocq: `check_prlimit64_complete_unmodeled`: the spec's declines
are exactly the checker's, and none of them reads the effect. -/
theorem check_prlimit64_complete_unmodeled (i : SyscallInput) (pid resource new_rlim old_rlim : word)
    (m : Model) (h : prlimit64_spec pid resource new_rlim old_rlim i m Unmodeled)
    (eff : SyscallEffect) : check_prlimit64 i pid resource new_rlim old_rlim eff m = CheckUnmodeled := by
  unfold prlimit64_spec at h
  unfold check_prlimit64
  cases hp : w_is0 pid with
  | false => simp only [Bool.not_false, ↓reduceIte]
  | true =>
  simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hr : (bv_unsigned resource == RLIMIT_CORE) with
  | false => simp only [Bool.not_false, ↓reduceIte]
  | true =>
  simp only [hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hn : w_is0 new_rlim with
  | true =>
    cases ho : w_is0 old_rlim with
    | true => simp only [Bool.and_self, ↓reduceIte]
    | false =>
      simp only [hn, ho, Bool.and_false, Bool.not_true, Bool.not_false, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte, bind_input_iff, bind_get_model_iff] at h ⊢
      rcases hrd : read_bytes_map i.in_wmem old_rlim (Z_to_bv 64 16) with _ | _
      · simp only [hrd] at h ⊢
        cases hacc : access_okb old_rlim 16 with
        | false =>
          simp only [hacc, Bool.not_false, ↓reduceIte, err_ret, ret_only, pure_iff,
            reduceCtorEq] at h
        | true => simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      · exfalso
        simp only [hrd] at h
        rcases hl : m_rlimit_core m with _ | bs0
        · simp only [hl, bind_choose_iff, set_rlimit_core, bind_modify_iff, pure_iff,
            reduceCtorEq, and_false, exists_false] at h
        · simp only [hl, pure_iff, reduceCtorEq] at h
  | false =>
    cases ho : w_is0 old_rlim with
    | false => simp only [Bool.and_self, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    | true =>
      simp only [hn, ho, Bool.false_and, Bool.not_false, Bool.not_true, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte, bind_input_iff, bind_get_model_iff] at h ⊢
      rcases hl : m_rlimit_core m with _ | bs0
      · rfl
      · simp only [hl] at h ⊢
        rcases hrd : read_bytes_map i.in_mem new_rlim (Z_to_bv 64 16) with _ | nb
        · simp only [hrd] at h ⊢
          cases hacc : access_okb new_rlim 16 with
          | false =>
            simp only [hacc, Bool.not_false, ↓reduceIte, err_ret, ret_only, pure_iff,
              reduceCtorEq] at h
          | true => simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        · simp only [hrd, record_copyins_unmodeled_iff] at h ⊢
          by_cases hlt : bv_unsigned (rlim64_hard nb) < bv_unsigned (rlim64_soft nb)
          · rw [ite_eq_left hlt] at h
            simp only [err_ret, ret_only, pure_iff, reduceCtorEq] at h
          · rw [ite_eq_right hlt] at h ⊢
            cases heq : bv_eqb (rlim64_hard nb) (rlim64_hard bs0) with
            | false => simp only [Bool.not_false, ↓reduceIte]
            | true =>
              simp only [heq, Bool.not_true, Bool.false_eq_true, ↓reduceIte, set_rlimit_core,
                bind_modify_iff, ret_only, pure_iff, reduceCtorEq] at h

/-! ## The witnesses — the second third of `Checks/Witness/Kernel/Sys.v`

Each is one outcome its spec accepts at every model.  Where the spec
draws a fresh record — the first `uname` or the first `prlimit64` read of
a run — the witness supplies a closed member of the envelope,
`utsname_default` or `rlim64_zero`, and its `_wf` lemma is what
`choose_ok` is handed; the lemma is decided, the way
`Checks/Cases/Kernel/Sys.lean` decides the same predicate on its
fixtures, with the recursion depth the 390-byte literal needs. -/

/-- Rocq: `Checks.Witness.Kernel.Sys.utsname_default`:
"Linux", three empty members, "riscv64", an empty domainname — the two pinned
members at their literals and every free member empty, so the whole struct is
inside `utsname_wf`. -/
def utsname_default : List byte :=
  uts_literal uts_sysname_chars ++ uts_literal [] ++ uts_literal [] ++ uts_literal []
  ++ uts_literal uts_machine_chars ++ uts_literal []

set_option maxRecDepth 8192 in
/-- Rocq: `utsname_default_wf`. -/
theorem utsname_default_wf : utsname_wf utsname_default = true := by decide

/-- Rocq: `Checks.Witness.Kernel.Sys.uname_witness`:
the spec's outcome with the record repeated when there is one and
`utsname_default` drawn when there is not. -/
def uname_witness (name : word) (i : SyscallInput) (m : Model) : outcome SyscallEffect :=
  if !(access_okb name NEW_UTSNAME_SIZE) then ret_outcome (errno_ret EFAULT) m
  else
    match read_bytes_map i.in_wmem name (Z_to_bv 64 NEW_UTSNAME_SIZE) with
    | none => Unmodeled
    | some _ =>
      match m_utsname m with
      | some bs => Ok (mkEffect (Z_to_bv 64 0) [(name, bs)] []) m []
      | none =>
        Ok (mkEffect (Z_to_bv 64 0) [(name, utsname_default)] []) (with_utsname utsname_default m) []

/-- Rocq: `uname_witness_ok`. -/
theorem uname_witness_ok (name : word) (i : SyscallInput) (m : Model) :
    uname_spec name i m (uname_witness name i m) := by
  unfold uname_spec uname_witness
  refine bind_step _ _ _ _ _ _ _ (input_ok i m) ?_
  refine bind_step _ _ _ _ _ _ _ (get_model_ok i m) ?_
  cases access_okb name NEW_UTSNAME_SIZE with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact pure_ok _ i m
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rcases read_bytes_map i.in_wmem name (Z_to_bv 64 NEW_UTSNAME_SIZE) with _ | _
    · exact unmodeled_intro i m
    · rcases m_utsname m with _ | bs
      · exact bind_step _ _ _ _ _ _ _ (choose_ok _ utsname_default i m utsname_default_wf)
          (bind_step _ _ _ _ _ _ _ (modify_ok _ i m) (pure_ok _ i _))
      · exact pure_ok _ i m

/-- Rocq: `Checks.Witness.Kernel.Sys.rlim64_zero`:
the pair {0, 0}, sixteen zero bytes. -/
def rlim64_zero : List byte := List.replicate 16 (Z_to_bv 8 0)

/-- Rocq: `rlim64_zero_wf`. -/
theorem rlim64_zero_wf : rlim64_wf rlim64_zero = true := by decide

/-- Rocq: `Checks.Witness.Kernel.Sys.prlimit64_witness`:
the spec's outcome, arm for arm, with the record repeated on a pinned read and
`rlim64_zero` drawn on the first. -/
def prlimit64_witness (pid resource new_rlim old_rlim : word) (i : SyscallInput) (m : Model) :
    outcome SyscallEffect :=
  if !(w_is0 pid) then Unmodeled
  else if !(bv_unsigned resource == RLIMIT_CORE) then Unmodeled
  else if w_is0 new_rlim && w_is0 old_rlim then Unmodeled
  else if !(w_is0 new_rlim) && !(w_is0 old_rlim) then Unmodeled
  else if w_is0 new_rlim then
    match read_bytes_map i.in_wmem old_rlim (Z_to_bv 64 16) with
    | none => if !(access_okb old_rlim 16) then ret_outcome (errno_ret EFAULT) m else Unmodeled
    | some _ =>
      match m_rlimit_core m with
      | some bs => Ok (mkEffect (Z_to_bv 64 0) [(old_rlim, bs)] []) m []
      | none =>
        Ok (mkEffect (Z_to_bv 64 0) [(old_rlim, rlim64_zero)] []) (with_rlimit_core rlim64_zero m) []
  else
    match m_rlimit_core m with
    | none => Unmodeled
    | some bs0 =>
      match read_bytes_map i.in_mem new_rlim (Z_to_bv 64 16) with
      | none => if !(access_okb new_rlim 16) then ret_outcome (errno_ret EFAULT) m else Unmodeled
      | some nb =>
        outcome_copyins [(new_rlim, 16)]
          (if bv_unsigned (rlim64_hard nb) < bv_unsigned (rlim64_soft nb) then
             ret_outcome (errno_ret EINVAL) m
           else if !(bv_eqb (rlim64_hard nb) (rlim64_hard bs0)) then Unmodeled
           else ret_outcome (Z_to_bv 64 0) (with_rlimit_core nb m))

/-- Rocq: `prlimit64_witness_ok`. -/
theorem prlimit64_witness_ok (pid resource new_rlim old_rlim : word) (i : SyscallInput) (m : Model) :
    prlimit64_spec pid resource new_rlim old_rlim i m
      (prlimit64_witness pid resource new_rlim old_rlim i m) := by
  unfold prlimit64_spec prlimit64_witness
  cases w_is0 pid with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases (bv_unsigned resource == RLIMIT_CORE) with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases w_is0 new_rlim with
  | true =>
    cases w_is0 old_rlim with
    | true =>
      simp only [Bool.and_self, ↓reduceIte]
      exact unmodeled_intro i m
    | false =>
      simp only [Bool.and_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.false_eq_true,
        ↓reduceIte]
      refine bind_step _ _ _ _ _ _ _ (input_ok i m) ?_
      refine bind_step _ _ _ _ _ _ _ (get_model_ok i m) ?_
      rcases read_bytes_map i.in_wmem old_rlim (Z_to_bv 64 16) with _ | _
      · cases access_okb old_rlim 16 with
        | false =>
          simp only [Bool.not_false, ↓reduceIte]
          exact pure_ok _ i m
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact unmodeled_intro i m
      · rcases m_rlimit_core m with _ | bs
        · exact bind_step _ _ _ _ _ _ _ (choose_ok _ rlim64_zero i m rlim64_zero_wf)
            (bind_step _ _ _ _ _ _ _ (modify_ok _ i m) (pure_ok _ i _))
        · exact pure_ok _ i m
  | false =>
    cases w_is0 old_rlim with
    | false =>
      simp only [Bool.and_self, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      exact unmodeled_intro i m
    | true =>
      simp only [Bool.false_and, Bool.not_false, Bool.not_true, Bool.and_false, Bool.false_eq_true,
        ↓reduceIte]
      refine bind_step _ _ _ _ _ _ _ (input_ok i m) ?_
      refine bind_step _ _ _ _ _ _ _ (get_model_ok i m) ?_
      rcases m_rlimit_core m with _ | bs0
      · exact unmodeled_intro i m
      · rcases read_bytes_map i.in_mem new_rlim (Z_to_bv 64 16) with _ | nb
        · cases access_okb new_rlim 16 with
          | false =>
            simp only [Bool.not_false, ↓reduceIte]
            exact pure_ok _ i m
          | true =>
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            exact unmodeled_intro i m
        · apply record_copyins_outcome
          by_cases hlt : bv_unsigned (rlim64_hard nb) < bv_unsigned (rlim64_soft nb)
          · simp only [hlt, ↓reduceIte]
            exact pure_ok _ i m
          · simp only [hlt, ↓reduceIte]
            cases bv_eqb (rlim64_hard nb) (rlim64_hard bs0) with
            | false =>
              simp only [Bool.not_false, ↓reduceIte]
              exact unmodeled_intro i m
            | true =>
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              exact bind_step _ _ _ _ _ _ _ (modify_ok _ i m) (pure_ok _ i _)

/-- Rocq: `Checks.Witness.Kernel.Sys.prctl_witness`:
the spec's answer, since the arm is deterministic. -/
def prctl_witness (option_ arg2 : word) (m : Model) : outcome SyscallEffect :=
  if !(bv_unsigned option_ == PR_CAPBSET_READ) then Unmodeled
  else if CAP_LAST_CAP < bv_unsigned arg2 then ret_outcome (errno_ret EINVAL) m
  else ret_outcome (Z_to_bv 64 1) m

/-- Rocq: `prctl_witness_ok`. -/
theorem prctl_witness_ok (option_ arg2 : word) (i : SyscallInput) (m : Model) :
    prctl_spec option_ arg2 i m (prctl_witness option_ arg2 m) := by
  unfold prctl_spec prctl_witness
  cases (bv_unsigned option_ == PR_CAPBSET_READ) with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact unmodeled_intro i m
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    by_cases hc : CAP_LAST_CAP < bv_unsigned arg2
    · simp only [hc, ↓reduceIte]
      exact pure_ok _ i m
    · simp only [hc, ↓reduceIte]
      exact pure_ok _ i m

/-! ## The frame lemmas of the second third -/

/-- Rocq: `VmMapsDisjoint.check_prctl_frame`: both accepting arms hand
back `m`. -/
theorem check_prctl_frame (option_ arg2 : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_prctl option_ arg2 eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_prctl at h
  split at h
  · cases h
  · split at h
    · obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      rfl
    · obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
      rfl

/-- Rocq: `VmMapsDisjoint.check_uname_frame`: an accepted uname hands back
`m` or `with_utsname bs m`, and the latter rebuilds the process state
alone (`State/Model.lean`). -/
theorem check_uname_frame (i : SyscallInput) (name : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (h : check_uname i name eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_uname at h
  split at h
  · obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
    rfl
  · split at h
    · cases h
    · obtain ⟨_, -, -, hcase⟩ := check_uname_copy_ok _ _ _ _ _ _ h
      rcases hcase with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> rfl

/-- Rocq: `VmMapsDisjoint.check_prlimit64_frame`: every accepted answer
hands back `m` or `with_rlimit_core bs m`, which rebuilds the limit state
alone (`State/Model.lean`). -/
theorem check_prlimit64_frame (i : SyscallInput) (pid resource new_rlim old_rlim : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_prlimit64 i pid resource new_rlim old_rlim eff m = CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_prlimit64 at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · split at h
    · split at h
      · obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
        rfl
      · cases h
    · obtain ⟨_, -, -, hcase⟩ := check_rlim64_read_ok _ _ _ _ _ _ h
      rcases hcase with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> rfl
  · split at h
    · cases h
    · split at h
      · split at h
        · obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp h
          rfl
        · cases h
      · split at h
        · obtain ⟨-, rfl, -⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
          rfl
        · split at h
          · cases h
          · obtain ⟨-, rfl, -⟩ := (check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp h
            rfl

end LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Sys
