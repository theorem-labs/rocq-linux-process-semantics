import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Kernel.Signal — rt_sigaction (134), rt_sigprocmask (135), sigaltstack (132), tkill (130), tgkill (131)

Mirrors `theories/LinuxProcessSem/Sys/Kernel/Signal.v`, which answers to
Linux `kernel/signal.c`: it holds what the kernel defines there, and
nothing else.

TRUST BOUNDARY: this file is part of the trusted specification.

The baseline is the squash that carried the 2026-09-11 work onto main,
the commit every other twin names, rather than the plan's f44244ad6b80:
`Sys/Kernel/Signal.v` is byte-identical at the two, and the definitions
of its closure that moved between them — `State.v`'s `FdEntry` and
`IoState`, which #712 gave a `/dev/urandom` arm and stream — are already
what the `State/` parts mirror, so reading at the squash is the same
reading of this file against the closure the Lean tree actually has.

Every definition keeps the Rocq name and shape.  The docstrings carry the
kernel citation each decision rests on — file, function and the line
numbers at Linux v6.18.46 (commit 1f99e9ab748f) — and point at the Rocq
definition for the argument in full, so there is one place to correct it.
The Rocq file cites `rt_sigprocmask` by function name across v6.1 - v6.17
and `rt_sigaction` across v6.10 - v6.15, cites the abort path by function
name at v6.18.46, and quotes line numbers only for the pipe path
(fs/pipe.c) at v6.18.46; every number here was read at v6.18.46.  Two arguments the Rocq file carries at length are not repeated:
WHY an `rt_sigaction` install may be a no-op at all — a disposition is
accepted only for a signal no modeled operation can cause reality to
raise, under the premise that the environment the theorem quantifies over
delivers no signals — and WHY the mask `rt_sigprocmask` keeps is the one
Linux would have, which rests on the same premise and on this spec being
the sole reader and writer of the mask (the Rocq header enumerates the
kernel's other readers and writers, and `Checks/Cases/Kernel/Signal.lean`
twins the machine-checked half of that enumeration).

Five spellings differ from Rocq without changing a value:

- the two bit tests are done on the `word` where Rocq does them in `Z`:
  `Z.ldiff (bv_unsigned fl) sa_flags_accepted` is
  `bv_and fl (bv_not (Z_to_bv 64 sa_flags_accepted))`, and the constant
  `Z.lxor (Z.ones 64) sig_kernel_only_mask` is
  `bv_not (Z_to_bv 64 sig_kernel_only_mask)`; both constants are below
  `2^64`, so the 64-bit values agree;
- Rocq's `Z.eqb`, `Z.leb` and `Nat.eqb` Bool tests are `==` / `≤` on
  `Int` and `Nat`, and `negb` is `!`;
- `bv_add act (Z_to_bv 64 8)` is `act + Z_to_bv 64 8`, the `BitVec`
  addition `State.read_bytes_map` steps its own address with;
- `Z.to_nat NSIG_BYTES` is `NSIG_BYTES.toNat`;
- `mask_launchable` is a `Prop`, as in Rocq, and its two lemmas and the
  four about `sigmask_deliver_model` are the twins of the Rocq lemmas
  beside these definitions, as `tkill_spec_off_unmodeled` and
  `tgkill_spec_off_unmodeled` are of theirs; every other check is in
  `Checks/Cases/Kernel/Signal.lean`.

Four more, for the three syscalls below, none changing a value:

- Rocq's `firstn` and `skipn` over the copied-in `stack_t` are `List.take`
  and `List.drop`, and `Z.to_nat SS_FLAGS_OFF` and `Z.to_nat SS_SIZE_OFF`
  are `SS_FLAGS_OFF.toNat` and `SS_SIZE_OFF.toNat`;
- `Z.ldiff (bv_unsigned fl) SS_AUTODISARM` is
  `bv_unsigned (bv_and fl (bv_not (Z_to_bv 64 SS_AUTODISARM)))`, the bit
  test on the `word`; both operands are below `2^64`, so the two agree for
  every `fl`;
- `(bv_unsigned sig <=? 64)%Z` and the `pid_positive` pair are `decide`
  over `Int`'s `≤` and `<`, with `2 ^ 31` computed in `Int`, and the
  `(… <? MINSIGSTKSZ)%Z` size test is the decidable `Int` `<` an `if`
  takes directly;
- `Z.eqb` on the mode is `==` on `Int`. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Signal

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi

/-! ## rt_sigaction (134) — dispositions no modeled operation can consult -/

/-- The signal number is an `int`: `SYSCALL_DEFINE4(rt_sigaction, int, sig,
...)` (kernel/signal.c:4638-4641, Linux v6.18.46, commit 1f99e9ab748f), so
the kernel sees only the low half of the register — the same ABI
truncation `fd32`, `cmd32` and `how32` apply, at the same boundary: the
table line that reads this syscall's arguments.  Rocq's table narrows the
signal of 130 and 131 through this definition too, which is why it lives
here and not in `Sys/Syscall.lean`. -/
def sig32 (sig : word) : word := abi_low32 sig

/-- The signals whose disposition no modeled operation can consult AND which
the theorem's signal-free environment therefore never delivers: SIGINT (2)
and SIGTERM (15) (include/uapi/asm-generic/signal.h:12 and :26, Linux
v6.18.46).  Both halves are load-bearing, and the second is a premise of
the theorem rather than a fact about `rt_sigaction`; the argument, the
excluded signals with the operation that excludes each (the four fault
signals at every `MachineFault` site, SIGPIPE and SIGXFSZ at a modeled
`write`, SIGCHLD ahead of the model acquiring a child), and the invariant
a later change must keep, are on the Rocq definition
`Signal.sigaction_accepted` and the header above it.  Every other signal
fails closed at an install. -/
def sigaction_accepted (sig : word) : Bool :=
  let s := bv_unsigned sig
  s == 2 || s == 15

/-- `do_sigaction`'s first test, `if (!valid_signal(sig) || sig < 1 || (act &&
sig_kernel_only(sig))) return -EINVAL;` (kernel/signal.c:4317-4318, Linux
v6.18.46, commit 1f99e9ab748f).  `valid_signal` is `sig <= _NSIG ? 1 : 0`
over an `unsigned long` (include/linux/signal.h:272-275), so a negative
`int` widens to a huge value and fails it, and the explicit `sig < 1`
catches 0.  `_NSIG` is 64 (include/uapi/asm-generic/signal.h:7, Linux v6.18.46; riscv
ships no uapi/asm/signal.h of its own) and the bound is INCLUSIVE: 64 is a
valid signal, 65 is -EINVAL.  Applied to the already-truncated low half,
an unsigned 1..64 test is exactly that predicate.  `kill` differs here,
accepting signal 0 as a permission probe; the argument is on the Rocq
definition `Signal.sig_valid`. -/
def sig_valid (sig : word) : Bool :=
  let s := bv_unsigned sig
  decide (1 ≤ s) && decide (s ≤ 64)

/-- `sig_kernel_only(sig)` is `siginmask(sig, SIG_KERNEL_ONLY_MASK)`
(include/linux/signal.h:445, Linux v6.18.46, commit 1f99e9ab748f) over
`rt_sigmask(SIGKILL) | rt_sigmask(SIGSTOP)` (:419-420), and `siginmask`
(:417) also requires `0 < sig < SIGRTMIN`: exactly SIGKILL (9) and SIGSTOP
(19) (include/uapi/asm-generic/signal.h:20 and :30).  `do_sigaction` tests
it only under `act &&` (kernel/signal.c:4317, Linux v6.18.46), so the two are refused with
something to install and answered 0 with `act` NULL. -/
def sig_kernel_only (sig : word) : Bool :=
  let s := bv_unsigned sig
  s == 9 || s == 19

/-- The `sa_flags` bits whose entire meaning is HOW a signal reaches a
handler, or how a child's stop is reported — neither can happen, so an
install carrying them is still a no-op: SA_NOCLDSTOP 0x1, SA_NOCLDWAIT 0x2,
SA_SIGINFO 0x4, SA_EXPOSE_TAGBITS 0x800, SA_ONSTACK 0x08000000, SA_NODEFER
0x40000000 and SA_RESETHAND 0x80000000 (include/uapi/asm-generic/signal-defs.h:30,
:33, :36, :46, :56, :62 and :65, Linux v6.18.46, commit 1f99e9ab748f).  That
is `UAPI_SA_FLAGS` (include/linux/signal_types.h:84-86), 0xD8000807 on an
architecture whose `__ARCH_UAPI_SA_FLAGS` is 0 (:76-82; riscv defines no
SA_RESTORER), minus SA_RESTART 0x10000000 (signal-defs.h:59).

SA_RESTART is left out because it is the one retained flag that changes a
SYSCALL's return value rather than a delivery, and the model has a syscall
that can return -EINTR; every bit outside `UAPI_SA_FLAGS` is left out
although `do_sigaction` silently masks such bits away
(`act->sa.sa_flags &= UAPI_SA_FLAGS`, kernel/signal.c:4341-4342, Linux v6.18.46) rather
than rejecting them, because fail-closed is the default for a shape
nothing needs.  Both arguments, and why SA_RESETHAND is unreachable from
musl's `sigaction` wrapper, are on the Rocq definition
`Signal.sa_flags_accepted`. -/
def sa_flags_accepted : Int := 0xC8000807

/-- No bit of the flags word outside `sa_flags_accepted`: Rocq's
`Z.ldiff (bv_unsigned fl) sa_flags_accepted = 0`, on the word. -/
def sa_flags_ok (fl : word) : Bool :=
  bv_unsigned (bv_and fl (bv_not (Z_to_bv 64 sa_flags_accepted))) == 0

/-- The flags word of the `struct sigaction` at `act`, if all 24 bytes of it
are readable.  The kernel's struct on riscv64 is `sa_handler` (8) at 0,
`sa_flags` (an `unsigned long`, 8) at 8 and `sa_mask` (8) at 16
(`struct sigaction`, include/linux/signal_types.h:37-49, Linux v6.18.46,
commit 1f99e9ab748f); its `sa_restorer` member sits under
`__ARCH_HAS_SA_RESTORER` (:45-47), which include/uapi/asm-generic/signal.h:70-72
defines only under an SA_RESTORER that asm-generic never defines, and
riscv ships no uapi/asm/signal.h to define one — so 24 bytes, NOT musl's
32-byte `struct k_sigaction`, and a spec that read 32 would answer -EFAULT
where Linux answers 0.

`SYSCALL_DEFINE4(rt_sigaction)` copies the whole struct in one call
(kernel/signal.c:4650-4651, Linux v6.18.46; the copy is `copy_from_user` of
include/linux/uaccess.h) before `do_sigaction` runs
(:4653), so readability is all-or-nothing and -EFAULT precedes every
-EINVAL `do_sigaction` raises; it follows the `sigsetsize` -EINVAL
(:4647-4648), and the `oact` copy-out runs after `do_sigaction`
(:4657-4658).  There is no `access_okb` guard here, and the reason — all
24 bytes must be mapped before anything is answered, and no model state
maps a byte within 24 of `2^64` — is on the Rocq definition
`Signal.sigaction_flags`, together with why the handler and `sa_mask` are
never consulted. -/
def sigaction_flags (mp : word → Option byte) (act : word) : Option word :=
  if (readable_bytes mp act (Z_to_bv 64 24)).length == 24
  then read_u64 mp (act + Z_to_bv 64 8)
  else none

/-- `rt_sigaction sig act oact sigsetsize`, with `sig` already truncated
(`sig32`).  The arms follow the kernel's own order —
`SYSCALL_DEFINE4(rt_sigaction)` (kernel/signal.c:4638-4661, Linux v6.18.46,
commit 1f99e9ab748f) then `do_sigaction` (:4311-4378):

1. `sigsetsize != sizeof(sigset_t)` is -EINVAL before anything else is
   looked at (:4647-4648), and `sizeof(sigset_t)` is 8 on riscv64
   (`Uapi.NSIG_BYTES`), so a bad size beats a wild `act` pointer.
2. a non-NULL `oact` is UNMODELED.  The kernel copies the PREVIOUS
   disposition out (`*oact = *k`, :4327-4328; `copy_to_user`, :4657-4658)
   and the model stores none — nor could it answer from a fixed initial
   state, since `begin_new_exec` resets dispositions through
   `flush_signal_handlers` (kernel/signal.c, Linux v6.18.46; the call is at
   fs/exec.c:1252), which preserves an inherited
   SIG_IGN, so the initial disposition is the launcher's choice.  Declining
   is the only sound arm.  It is taken BEFORE the copy-in, one step earlier
   than the kernel, which copies `act` first (:4650-4651): a decline where
   Linux answers -EFAULT, which fail-closed permits.
3. with `act` NULL nothing is installed: `do_sigaction`'s guard (:4317-4318)
   answers -EINVAL outside 1..64 and its `act &&` half is off, so every
   valid signal — fault signals and SIGKILL included — is a plain 0.
4. with `act` non-NULL: -EFAULT unless all 24 bytes are readable
   (:4650-4651); then -EINVAL outside 1..64 and for SIGKILL/SIGSTOP
   (:4317-4318); then fail closed on SA_RESTART and on any bit outside
   `sa_flags_accepted`; then 0 for a signal in `sigaction_accepted`,
   recording nothing, and UNMODELED for every other signal — the case the
   spec exists for, which keeps a SIGSEGV, SIGILL, SIGBUS or SIGTRAP
   handler out of the modeled surface.

Two things `do_sigaction` does are not reproduced, and the Rocq definition
`Signal.rt_sigaction_spec` argues each: its -EINVAL for an existing action
carrying SA_IMMUTABLE (:4323-4326), a bit only `force_sig_info_to_task`
sets under HANDLER_EXIT (:1308-1309) on a process that is ending; and its
two silent side effects on an install, clearing SIGKILL and SIGSTOP from
the stored `sa_mask` (:4351-4352) and flushing the pending signals a new
SIG_IGN discards (:4365-4370), both unobservable while the model has no
stored mask and no pending queue behind a NULL `oact`. -/
def rt_sigaction_spec (sig act oact ss : word) : Sys SyscallEffect :=
  if !(bv_eqb ss (Z_to_bv 64 8)) then err_ret EINVAL
  else if !(w_is0 oact) then unmodeled
  else if w_is0 act
  then (if sig_valid sig then ret_only (Z_to_bv 64 0) else err_ret EINVAL)
  else
    i <- input ;;
    match sigaction_flags i.in_mem act with
    | none => err_ret EFAULT
    | some fl =>
        if !(sig_valid sig) then err_ret EINVAL
        else if sig_kernel_only sig then err_ret EINVAL
        else if !(sa_flags_ok fl) then unmodeled
        else if sigaction_accepted sig then ret_only (Z_to_bv 64 0)
        else unmodeled

/-! ## rt_sigprocmask (135) — a mask this spec alone reads and writes -/

/-- `how` is an `int` (`SYSCALL_DEFINE4(rt_sigprocmask, int, how, ...)`,
kernel/signal.c:3327-3328, Linux v6.18.46, commit 1f99e9ab748f), so the
kernel sees only the low half of the register, and `sigprocmask`'s
`switch (how)` (:3253-3264) compares that half against SIG_BLOCK,
SIG_UNBLOCK and SIG_SETMASK (include/uapi/asm-generic/signal-defs.h:72-78, Linux v6.18.46)
with `default: return -EINVAL` (:3263-3264).  Signedness does not enter:
three equality tests against non-negative constants decide identically
under an unsigned reading.  The narrowing itself is `Syscall.how32`,
applied by the table as `fd32` is. -/
def how_valid (how : word) : Bool :=
  let h := bv_unsigned how
  h == SIG_BLOCK || h == SIG_UNBLOCK || h == SIG_SETMASK

/-- The `sigset_t` at `p`, or `none` if any of its bytes is unreadable.
`copy_from_user(&new_set, nset, sizeof(sigset_t))` (kernel/signal.c:3340-3341,
Linux v6.18.46, commit 1f99e9ab748f) is all-or-nothing at the syscall
boundary — any shortfall is -EFAULT and nothing is installed — and
`sizeof(sigset_t)` is `Uapi.NSIG_BYTES` = 8, so this reads eight bytes and
no more.  The contents are read, not merely tested, because the value
decides what is installed and what `oset` later reports.  There is no
`access_okb` guard, and the reason — a wholly readable range is below
`TASK_SIZE`, and the wrap the word addition could complete is excluded by
the image well-formedness the theorem is stated under, not by the syscall
layer — is on the Rocq definition `Signal.sigset_at`. -/
def sigset_at (mp : word → Option byte) (p : word) : Option word :=
  match read_bytes_map mp p (Z_to_bv 64 NSIG_BYTES) with
  | some bs => some (le_bytes_to_word bs)
  | none => none

/-- `sigdelsetmask(&new_set, sigmask(SIGKILL)|sigmask(SIGSTOP))`
(kernel/signal.c:3342, Linux v6.18.46, commit 1f99e9ab748f), where
`sigdelsetmask` is `set->sig[0] &= ~mask` (include/linux/signal.h:225-228)
and `sigmask(sig)` is `1UL << ((sig) - 1)` (:127): the two bits
`Uapi.sig_kernel_only_mask` names.  Applied to the set the caller supplied
and to nothing else — the `old_set` snapshot taken one line earlier
(:3337) goes out through `oset` unfiltered — which is why this is a
function on the new set and not a filter on the field.  Blocking SIGKILL
is not an error: `sigprocmask` returns 0 (:3268) and the call returns 0
(:3354) with the bits quietly gone, observable only at a later read-back
through `oset`.  The opposite of `rt_sigaction`, where `sig_kernel_only`
is -EINVAL. -/
def sigmask_strip (w : word) : word :=
  bv_and w (bv_not (Z_to_bv 64 sig_kernel_only_mask))

/-- `sigprocmask`'s `switch (how)` (kernel/signal.c:3253-3264, Linux
v6.18.46, commit 1f99e9ab748f): `sigorsets` for SIG_BLOCK (:3255),
`sigandnsets` for SIG_UNBLOCK (:3258), plain assignment for SIG_SETMASK
(:3261); the two set operations are `_SIG_SET_BINOP` instances
(include/linux/signal.h:131, :157 and :163, Linux v6.18.46), bitwise or and and-not on
the one word a riscv64 `sigset_t` is.  `how` has already been checked by
`how_valid`, so the default arm here is unreachable rather than a
fall-through: it repeats SIG_SETMASK's answer, and the guard is what makes
that choice inert.  A reader widening `how_valid` must fix this with it. -/
def sigmask_apply (how old new : word) : word :=
  if bv_unsigned how = SIG_BLOCK then bv_or old new
  else if bv_unsigned how = SIG_UNBLOCK then bv_and old (bv_not new)
  else new

/-- THE WHOLE-RUN HALF OF `Run.valid_sigmask`, AS A CHECK RATHER THAN A
SENTENCE.  That predicate constrains the mask a process is LAUNCHED with;
what makes it a property of the whole run is that nothing this spec does
can put either bit back, which is a claim about this file's contents and
is therefore stated here and proved.  It is what the second of the
development's three priorities rests on for this syscall: `oset` copies the
mask out verbatim, so a reachable state with SIGKILL or SIGSTOP set would
be a trace Linux cannot produce (`set_current_blocked` strips the two for
every in-kernel writer, kernel/signal.c:3214-3218, Linux v6.18.46).  Rocq:
`Signal.mask_launchable`. -/
def mask_launchable (w : word) : Prop :=
  bv_and w (Z_to_bv 64 sig_kernel_only_mask) = Z_to_bv 64 0

/-- The strip lands in the launchable set whatever it was handed.  Twin of
Rocq's `Signal.sigmask_strip_launchable`. -/
theorem sigmask_strip_launchable (w : word) : mask_launchable (sigmask_strip w) := by
  unfold mask_launchable sigmask_strip bv_and bv_not
  rw [BitVec.and_assoc, BitVec.not_and_self, Z_to_bv_64_zero]
  exact BitVec.and_zero

/-- Each of the three arithmetics preserves launchability of the entry
mask: `sigorsets` because neither operand carries the bits, `sigandnsets`
because it only clears, and assignment because the value installed is the
caller's already-stripped set.  Twin of Rocq's
`Signal.sigmask_apply_launchable`. -/
theorem sigmask_apply_launchable (how old new : word)
    (hold : mask_launchable old) (hnew : mask_launchable new) :
    mask_launchable (sigmask_apply how old new) := by
  unfold mask_launchable at hold hnew ⊢
  unfold sigmask_apply
  split
  · -- SIG_BLOCK: `sigorsets` — neither operand carries the bits
    unfold bv_and at hold hnew ⊢
    unfold bv_or
    rw [BitVec.and_or_distrib_right, hold, hnew, BitVec.or_self]
  · split
    · -- SIG_UNBLOCK: `sigandnsets` only CLEARS, so the second operand is
      -- irrelevant and the proof does not look at it
      unfold bv_and at hold ⊢
      unfold bv_not
      rw [BitVec.and_assoc, BitVec.and_comm (~~~new), ← BitVec.and_assoc, hold, Z_to_bv_64_zero]
      exact BitVec.zero_and
    · -- SIG_SETMASK: the value installed is the caller's, already stripped
      exact hnew

/-- The `oset` copy-out, the LAST thing the syscall does:
`if (oset) { if (copy_to_user(oset, &old_set, sizeof(sigset_t))) return
-EFAULT; } return 0;` (kernel/signal.c:3349-3354, Linux v6.18.46, commit
1f99e9ab748f).  `old` is the mask the process had ON ENTRY (:3337), so
this is called with the entry mask on every arm that reaches it,
including the one that has already changed the mask.

`access_ok` IS TESTED BEFORE THE MEMORY WALK, AND THE ORDER IS THE POINT.
`copy_to_user` is `access_ok` and then the raw copy
(`_inline_copy_to_user`, include/linux/uaccess.h:189-200, Linux v6.18.46:
the test at :195, the copy at :197), and `State.access_okb` is written as
a subtraction in `Int` as `__access_ok` is (include/asm-generic/access_ok.h:31-40,
Linux v6.18.46),
so it is the only thing here that sees a range wrapping the top of the
address space; `State.read_bytes_map` walks in word arithmetic and wraps.

THE THIRD CASE IS WHY THIS IS NOT JUST TWO ARMS.  A destination that
passes `access_ok` but is not wholly writable is DECLINED, not -EFAULT:
riscv's `raw_copy_to_user` (arch/riscv/include/asm/uaccess.h:430-433, Linux
v6.18.46) hands the range to an assembly copy that stores forward under exception
fixups, so an `oset` straddling a page boundary with only its first page
writable really does store those bytes before faulting.  The return is
-EFAULT either way; the memory is not, and a partial copy-out is
user-visible state this model does not represent.  Answering -EFAULT with
no write would be a plausible answer Linux need not give, so the arm fails
closed.  Why this spec takes on the failed-call-after-install obligation
that `Kernel.Sys.prlimit64_spec` declines is on the Rocq definition
`Signal.write_oset`. -/
def write_oset (oset old : word) : Sys SyscallEffect :=
  if !(access_okb oset NSIG_BYTES) then err_ret EFAULT
  else
    i <- input ;;
    match read_bytes_map i.in_wmem oset (Z_to_bv 64 NSIG_BYTES) with
    | some _ =>
        Monad.pure (mkEffect (Z_to_bv 64 0)
                      [(oset, Z_to_le_bytes NSIG_BYTES.toNat (bv_unsigned old))] [])
    | none => unmodeled

/-- Whether a mask blocks SIGABRT: bit 5, `Uapi.sigabrt_mask`.  The one bit
of the mask the abort path reads. -/
def sigabrt_blocked (mask : word) : Bool :=
  !(w_is0 (bv_and mask (Z_to_bv 64 sigabrt_mask)))

/-- WHERE THE ABORT ACTUALLY KILLS THE PROCESS, and it is not at the
`tkill`.  musl's `raise` blocks the application signals, sends SIGABRT to
its own tid, then restores the old mask; with SIGABRT blocked the send
only makes it pending (`__send_signal_locked` adds it to the pending set,
kernel/signal.c:1137, Linux v6.18.46, commit 1f99e9ab748f, and
`recalc_sigpending_tsk` leaves a blocked signal there, :159-175), so the
call the process does not come back from is the restore: `sigprocmask`
(:3267) reaches `__set_task_blocked`, which installs the new mask
(:3203) and then runs `recalc_sigpending()` (:3204); that finds the
now-unblocked pending SIGABRT, and on the way back to user space
`get_signal` takes the fatal path — `sig_kernel_coredump` (:3016),
`vfs_coredump` (:3028), `do_group_exit(signr)` (:3043).

So the fatal step belongs to THIS syscall, conditional on the mask the
call installs rather than the one it was handed: `Monad.set_sigmask` plus
that condition, and the two coincide whenever nothing is pending
(`set_sigmask_deliver_no_pending`), which is every state a run with the
abort declaration off can reach.  THE ORDER IS THE KERNEL'S: the mask is
installed first and the process dies afterwards, and the `oset` copy-out
still happens, because the syscall finishes (:3349-3354) before the return
path takes the signal; what it wrote is discarded with the rest of the
effect by `Run.sstep_killed`, as `Kernel.Exit.exit_spec`'s is by
`Run.sstep_exit`.  A launch mask that already blocks SIGABRT is a DECLINE
elsewhere rather than a death here (musl's `abort` then falls through to
an `rt_sigaction` on SIGABRT, which `rt_sigaction_spec` declines); the
argument is on the Rocq definition `Signal.sigmask_deliver_model`.

One `State` function and one `Monad.modify`, rather than a branch over
two monadic steps, because that is what a checker and a witness can
follow with the same `modify_ok` they use for a plain `set_sigmask`. -/
def sigmask_deliver_model (new : word) (m : Model) : Model :=
  if m_sigabrt_pending m && !(sigabrt_blocked new)
  then with_killed (Z_to_bv 64 SIGABRT) (with_sigmask new m)
  else with_sigmask new m

def set_sigmask_deliver (new : word) : Sys Unit :=
  modify (sigmask_deliver_model new)

/-- MEANING PRESERVED: with nothing pending — every state a run whose task
did not declare the abort path can reach, since the only writer of the
pending bit is the `tkill` arm, which declines with the declaration off —
installing a mask is what it always was.  Twin of Rocq's
`Signal.sigmask_deliver_model_no_pending`. -/
theorem sigmask_deliver_model_no_pending (new : word) (m : Model)
    (hp : m_sigabrt_pending m = false) :
    sigmask_deliver_model new m = with_sigmask new m := by
  simp only [sigmask_deliver_model, hp, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- The two projections a checker and a witness need through the delivery:
the mask installed is the mask asked for, and the address space is
untouched.  Both branches go through `State.with_sigmask`, and
`State.with_killed` on top of it rebuilds `ProcState` alone.  Twins of
Rocq's `Signal.m_sigmask_sigmask_deliver_model` and
`Signal.m_vmmaps_sigmask_deliver_model`. -/
theorem m_sigmask_sigmask_deliver_model (new : word) (m : Model) :
    m_sigmask (sigmask_deliver_model new m) = new := by
  unfold sigmask_deliver_model
  split <;> rfl

theorem m_vmmaps_sigmask_deliver_model (new : word) (m : Model) :
    m_vmmaps (sigmask_deliver_model new m) = m_vmmaps m := by
  unfold sigmask_deliver_model
  split <;> rfl

/-- Twin of Rocq's `Signal.set_sigmask_deliver_no_pending`. -/
theorem set_sigmask_deliver_no_pending (new : word) (i : SyscallInput) (m : Model)
    (o : outcome Unit) (hp : m_sigabrt_pending m = false) :
    set_sigmask_deliver new i m o ↔ set_sigmask new i m o := by
  simp only [set_sigmask_deliver, set_sigmask, Monad.modify,
    sigmask_deliver_model_no_pending new m hp]

/-- `rt_sigprocmask how nset oset sigsetsize`, with `how` already truncated
(`Syscall.how32`).  The arms follow the kernel's own order —
`SYSCALL_DEFINE4(rt_sigprocmask)` (kernel/signal.c:3327-3355, Linux
v6.18.46, commit 1f99e9ab748f) then `sigprocmask` (:3244-3269):

1. `sigsetsize != sizeof(sigset_t)` is -EINVAL before anything else is
   looked at (:3334-3335), so a bad size BEATS A WILD `nset` POINTER.
   `sigsetsize` is a `size_t` compared full-width: unlike `how` it does
   NOT truncate, so a register whose low half is 8 is still wrong.
2. `old_set = current->blocked` is snapshotted HERE (:3337), before
   anything is installed, and it is this value — not the mask the call
   leaves behind — that `oset` receives: the syscall passes NULL as
   `sigprocmask`'s own `oldset` (:3344) and never uses that copy.
3. with `nset` NULL nothing is installed, and because `sigprocmask` is
   reached only from inside `if (nset)` (:3339), `how` IS NEVER LOOKED AT:
   an out-of-range `how` with a NULL `nset` returns 0, not -EINVAL.  The
   call is not a no-op even so — arm 5 still runs, so a query WRITES.
4. with `nset` non-NULL: -EFAULT unless all 8 bytes are readable
   (:3340-3341), then SIGKILL and SIGSTOP are stripped from the new set
   (:3342, silently — the call succeeds), then -EINVAL for a `how` outside
   {0, 1, 2} (:3263-3264), then the install (:3255, :3258 or :3261, then
   :3267 and :3203), which is fatal when it uncovers a pending SIGABRT
   (`sigmask_deliver_model`).
5. with `oset` non-NULL the entry mask is copied out LAST (:3349-3351).  A
   bad `how` returns before this runs, so a rejected call leaves `oset`
   untouched; and a fault HERE returns -EFAULT with the new mask already
   installed and NOT rolled back, the corner `write_oset` says how it
   takes on.

Every arm past the copy records the copy-from-user range: arm 1's -EINVAL
is answered before `nset` is looked at, arm 4's is answered after eight
bytes have been copied, and `Syscall.record_copyins` exists to tell those
two apart — an empty ledger on the second would be a false claim that the
call read no user memory, and `State.materialize_model_accesses` charges
the range against the allocation budget.  The -EFAULT arm records
nothing because the copy FAILED; what that convention costs (one page of
budget, in the under-charging direction, when `nset` straddles a page
boundary) is argued on the Rocq definition `Signal.rt_sigprocmask_spec`,
which also carries the argument that this spec is the sole reader and
writer of the mask it keeps, and the invariant a second one must
respect. -/
def rt_sigprocmask_spec (how nset oset ss : word) : Sys SyscallEffect :=
  if !(bv_eqb ss (Z_to_bv 64 NSIG_BYTES)) then err_ret EINVAL
  else
    m <- get_model ;;
    let old := m_sigmask m
    if w_is0 nset then
      (if w_is0 oset then ret_only (Z_to_bv 64 0) else write_oset oset old)
    else
      i <- input ;;
      match sigset_at i.in_mem nset with
      | none => err_ret EFAULT
      | some raw =>
          record_copyins [(nset, NSIG_BYTES.toNat)]
          (if !(how_valid how) then err_ret EINVAL
           else
             set_sigmask_deliver (sigmask_apply how old (sigmask_strip raw)) ;;
             (if w_is0 oset then ret_only (Z_to_bv 64 0) else write_oset oset old))

/-! ## sigaltstack (132) — a stack that is recorded as installed and never used

Linux v6.18.46, commit 1f99e9ab748f: the whole call is
`SYSCALL_DEFINE2(sigaltstack)` (kernel/signal.c:4455-4467, Linux v6.18.46)
and `do_sigaltstack` (kernel/signal.c:4397-4453, Linux v6.18.46), over
`__on_sig_stack` (include/linux/sched/signal.h:573-582, Linux v6.18.46),
`on_sig_stack` (:587-602) and `sas_ss_flags` (:604-610), and over
`sigaltstack_size_valid` (arch/riscv/kernel/signal.c:479-482, Linux
v6.18.46, under CONFIG_DYNAMIC_SIGFRAME; include/linux/signal.h:468-472,
Linux v6.18.46, without it).

WHAT THE MODEL KEEPS IS ONE BIT, `State.m_sigaltstack_installed`: whether
a call has left the kernel's `sas_ss_size` non-zero.  It does not keep
the pointer or the size, because BOTH READERS OF THE RECORD TAKE THE USER
STACK POINTER — `on_sig_stack` decides the -EPERM (kernel/signal.c:4418-4419,
Linux v6.18.46) and `sas_ss_flags` is the `ss_flags` an `oss` answer
reports (:4408) — and `State.SyscallInput` carries a0..a5 and no sp.
While the size is zero both are constant in sp: `__on_sig_stack` reduces
to `sp > sas_ss_sp && sp - sas_ss_sp <= 0` (include/linux/sched/signal.h:579-580,
Linux v6.18.46), whose conjuncts contradict each other, and `sas_ss_flags`
returns SS_DISABLE on its first test (:606-607).  A size of at least `Uapi.MINSIGSTKSZ` ends that, which is
why the first arm below declines every call after an install.

THE STARTING RECORD IS execve's AND IS NOT WHOLLY KNOWN: `begin_new_exec`
clears `sas_ss_sp` and `sas_ss_size` (fs/exec.c:1211, Linux v6.18.46) and
leaves `sas_ss_flags` alone — the three-field `sas_ss_reset`
(include/linux/sched/signal.h:612-617) is called from `copy_process`
(kernel/fork.c:2242, for a CLONE_VM child), from `signal_delivered`
(kernel/signal.c:3080-3081, once a handler has run under SS_AUTODISARM),
and from nowhere on the exec path — so the flags word is inherited from
whatever called `execve`, and `State.ProcInput` does not quantify it.  That is why a non-NULL `uoss` and the all-zero struct
are declined (arms 2 and 7 below).  The invariant the answered arms rest
on, why the bit is set by the install and not by SS_DISABLE, and the ISA
premise the success arm carries — riscv's `sigaltstack_size_valid` is
`ss_size > get_rt_frame_size(false)` (arch/riscv/kernel/signal.c:479-482,
Linux v6.18.46), and `get_rt_frame_size` (:206-223) adds the vector
context only for a task whose vector state is on (:214-216);
`flush_thread` turns that state off at execve
(arch/riscv/kernel/process.c:168-191, Linux v6.18.46, at :182) and only
the first-use trap `riscv_v_first_use_handler` turns it back on
(arch/riscv/kernel/vector.c:183-226, Linux v6.18.46, at :222), which no
instruction of the modeled ISA can raise, so the frame is 1088 bytes and
below MINSIGSTKSZ — are on the Rocq definition
`Signal.sigaltstack_spec` and the header above it, and are not repeated
here. -/

/-- The three fields of the `stack_t` the kernel copied in, decoded from
its 24 bytes (`Uapi.SIGALTSTACK_BYTES`; the layout is `struct sigaltstack`
at include/uapi/asm-generic/signal.h:85-89, Linux v6.18.46, commit
1f99e9ab748f).  `ss_flags` is an `int`: `do_sigaltstack` reads it as
`unsigned ss_flags = ss->ss_flags` (kernel/signal.c:4415), four bytes at
offset 8, and the four padding bytes above it are copied and never looked
at — so a spec that read eight bytes there would call bit 32 a mode. -/
def ss_sp_of (bs : List byte) : word :=
  le_bytes_to_word (List.take 8 bs)
def ss_flags_of (bs : List byte) : word :=
  le_bytes_to_word (List.take 4 (List.drop SS_FLAGS_OFF.toNat bs))
def ss_size_of (bs : List byte) : word :=
  le_bytes_to_word (List.drop SS_SIZE_OFF.toNat bs)

/-- `ss_mode = ss_flags & ~SS_FLAG_BITS` (kernel/signal.c:4421, Linux
v6.18.46, commit 1f99e9ab748f): the flags word with the one bit that is
not a mode masked away.  `SS_FLAG_BITS` is `SS_AUTODISARM`
(include/uapi/linux/signal.h:14).  This is Rocq's mask and Linux's answer
alone: qemu-user's `target_restore_altstack` switches on the whole flags
word and answers -EINVAL when bit 31 is set (linux-user/signal.c:317-319,
QEMU v11.1.1), so the mode a set bit 31 yields here lies outside the
supported intersection; bugs/sigaltstack-autodisarm-mode-admits-linux-alone.md
records the shape, and the pins that reach it say so. -/
def ss_mode (fl : word) : Int :=
  bv_unsigned (bv_and fl (bv_not (Z_to_bv 64 SS_AUTODISARM)))

/-- `do_sigaltstack` answers -EINVAL for a mode outside {SS_DISABLE,
SS_ONSTACK, 0} (kernel/signal.c:4422-4424, Linux v6.18.46, commit
1f99e9ab748f).  SS_ONSTACK is ACCEPTED as an input mode — the kernel does
not refuse a caller that claims to be on the stack it is installing — and
is not the same thing as the SS_ONSTACK an `oss` reports back. -/
def ss_mode_ok (fl : word) : Bool :=
  let md := ss_mode fl
  md == 0 || md == SS_ONSTACK || md == SS_DISABLE

/-- The SS_DISABLE branch of `do_sigaltstack` (kernel/signal.c:4436-4438,
Linux v6.18.46, commit 1f99e9ab748f), decided on the mode. -/
def ss_disabling (fl : word) : Bool := ss_mode fl == SS_DISABLE

/-- The `stack_t` at `uss`, or `none` if any of its 24 bytes is
unreadable.  All-or-nothing because `SYSCALL_DEFINE2(sigaltstack)`
(kernel/signal.c:4455-4467, Linux v6.18.46, commit 1f99e9ab748f) fetches
the struct with ONE copy_from_user (:4459-4460) before `do_sigaltstack`
(:4397-4453) runs, so -EFAULT precedes every other answer this call has.  No `access_okb`
guard, for the reason `sigaction_flags` gives above and by the same
argument (on the Rocq definition `Signal.sigaltstack_at`). -/
def sigaltstack_at (mp : word → Option byte) (uss : word) : Option (List byte) :=
  read_bytes_map mp uss (Z_to_bv 64 SIGALTSTACK_BYTES)

/-- `sigaltstack uss uoss`.  The arms follow the kernel's own order —
`SYSCALL_DEFINE2(sigaltstack)` (kernel/signal.c:4455-4467, Linux v6.18.46,
commit 1f99e9ab748f) then `do_sigaltstack` (:4397-4453):

1. a stack is installed — the recorded `sas_ss_size` is non-zero — so
   nothing below can be decided from a stack pointer this model does not
   have: UNMODELED.  This is the arm that makes one bit enough.
2. a non-NULL `uoss` is UNMODELED: the answer carries
   `current->sas_ss_flags & SS_FLAG_BITS` (:4408-4409), the inherited bit.
3. with both pointers NULL `do_sigaltstack` runs and does nothing: 0
   (:4461 with both arguments NULL, :4452).
4. -EFAULT unless all 24 bytes at `uss` are readable (:4459-4460).
5. -EINVAL for a mode outside {0, SS_ONSTACK, SS_DISABLE} (:4421-4424),
   decided AFTER the copy and BEFORE the fast path, where the kernel
   decides it, and after an -EPERM that cannot fire — `on_sig_stack` is
   false for every sp while the recorded size is zero (:4418-4419), which
   arm 1 guarantees it is.
6. SS_DISABLE succeeds whatever `ss_sp` and `ss_size` say: the kernel
   zeroes both before storing (:4436-4438), so no size check applies and
   the record moves to (NULL, 0, ss_flags) — or the fast path (:4430-4433)
   returned first because all three fields already matched, which is the
   same record.  Either way 0, the size stays zero, and the bit is NOT
   set.
7. a zero `ss_sp` AND a zero `ss_size` under a non-disabling mode is
   UNMODELED, the only arm that is not a kernel answer: the fast path's
   shadow.  The kernel returns 0 when all three fields equal the stored
   ones (:4430-4433) and -ENOMEM otherwise (:4440-4441, the size being
   zero), and which it is turns on the stored flags word — execve's
   inherited one, or the one arm 6 wrote over it — which is not tracked.
8. -ENOMEM below `Uapi.MINSIGSTKSZ` (:4440-4441, `min_ss_size` being the
   MINSIGSTKSZ the syscall passes at :4463).  The fast path cannot have
   fired: it needs `ss_sp` and `ss_size` to equal the stored (NULL, 0),
   which is arm 7's shape.
9. otherwise the install succeeds: 0, and the bit is set (:4445-4448) —
   the only arm that raises `sas_ss_size` above zero, and the bound arm 8
   just applied is why (`sigaltstack_size_valid`, :4442-4443, never
   decides a case it has not: see the section header).

No arm writes user memory, and none records a copy-in: the 24 bytes are
read into a kernel local (`stack_t new`, :4457), the shape
`rt_sigaction_spec` has above. -/
def sigaltstack_spec (uss uoss : word) : Sys SyscallEffect :=
  m <- get_model ;;
  if m_sigaltstack_installed m then unmodeled
  else if !(w_is0 uoss) then unmodeled
  else if w_is0 uss then ret_only (Z_to_bv 64 0)
  else
    i <- input ;;
    match sigaltstack_at i.in_mem uss with
    | none => err_ret EFAULT
    | some bs =>
        let fl := ss_flags_of bs
        if !(ss_mode_ok fl) then err_ret EINVAL
        else if ss_disabling fl then ret_only (Z_to_bv 64 0)
        else if w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs) then unmodeled
        else if bv_unsigned (ss_size_of bs) < MINSIGSTKSZ then err_ret ENOMEM
        else set_sigaltstack_installed ;; ret_only (Z_to_bv 64 0)

/-! ## tkill (130) and tgkill (131) — the abort path, and only under a task's declaration

The stance is the task's, declared in the input as `State.in_abort_terminal`
(`Run.valid_input` pins it false, `Run.valid_input_abort` true): with the
declaration off both arms answer `unmodeled` for every argument shape,
which is what the dispatcher did when the numbers had no arm, and the
decline is the FIRST test — ahead of the -EINVAL a real kernel answers
first — because a coverage gate is not a kernel test.  Why the numbers have
an arm at all (issue #236 asked that they keep none), what musl's `abort`
issues (TKILL to its own tid between two `rt_sigprocmask` calls, so the
death is the restore's and not the send's), the modeled envelope, why
SIGABRT's disposition is SIG_DFL by construction (`rt_sigaction_spec`
declines every install for signal 6), and the LSM gap
(bugs/tkill-lsm-denial-not-admitted.md) are on the Rocq header above
`Signal.pid_positive`.

The kernel path, Linux v6.18.46, commit 1f99e9ab748f: `SYSCALL_DEFINE2(tkill)`
(kernel/signal.c:4192-4199) and `SYSCALL_DEFINE3(tgkill)` (:4176-4183)
refuse a non-positive pid (and tgid) and call `do_tkill` (:4157-4164),
which is `do_send_specific` (:4127-4155): the pid lookup (:4134) through
`find_task_by_vpid` (kernel/pid.c:438, Linux v6.18.46), the tgid test
(kernel/signal.c:4135, Linux v6.18.46), `check_kill_permission` (:4136,
defined at :799-833, whose first test at :805-806 is `valid_signal` of
include/linux/signal.h:272-275, Linux v6.18.46), and — for a non-zero
signal only (kernel/signal.c:4141, Linux v6.18.46) — `do_send_sig_info`
(:4142). -/

/-- `pid` and `tgid` arrive as `pid_t`, an `int` (`SYSCALL_DEFINE2(tkill,
pid_t, pid, int, sig)`, kernel/signal.c:4192, Linux v6.18.46, commit
1f99e9ab748f): `Syscall.pid32` has already truncated to 32 bits, so
"positive" is 1..2^31-1 and every negative value has become something at
or above 2^31.  `if (pid <= 0) return -EINVAL;` (:4195-4196) and
`if (pid <= 0 || tgid <= 0) return -EINVAL;` (:4179-4180) are this test. -/
def pid_positive (p : word) : Bool :=
  let v := bv_unsigned p
  decide (1 ≤ v) && decide (v < 2 ^ 31)

/-- `valid_signal(sig)` widens the `int` to `unsigned long` and tests
`sig <= _NSIG` (include/linux/signal.h:272-275, Linux v6.18.46, commit
1f99e9ab748f), with `_NSIG` 64 on riscv64 (include/uapi/asm-generic/signal.h:7).
A negative `int` widens to something enormous and fails; so does anything
above 64.  Applied to the already-truncated low half, an unsigned `≤ 64`
test is that predicate — and unlike `sig_valid`, which `rt_sigaction`
uses, 0 PASSES it: `rt_sigaction`'s `sig < 1` is its own test, and the
signal-sending paths keep 0 as the permission probe: `check_kill_permission`
(kernel/signal.c:799-833, Linux v6.18.46) tests only the `valid_signal`
half at :805-806. -/
def tkill_sig_valid (sig : word) : Bool :=
  decide (bv_unsigned sig ≤ 64)

/-- The delivery, once every check has passed and the target is the caller
itself.  BLOCKED means pending: `__send_signal_locked` adds the signal to
the pending set (`sigaddset(&pending->signal, sig)`, kernel/signal.c:1137,
Linux v6.18.46, commit 1f99e9ab748f) and `complete_signal` does not flag
the task, because `wants_signal` returns false for a signal the mask covers
(:946-949); it stays pending until a mask change lets
`recalc_sigpending_tsk` (:159-175) find it, so the syscall returns 0 and
the process runs on — `set_sigmask_deliver` above is where it is taken.
UNBLOCKED means the process does not come back: `get_signal` runs on the
return to user space, finds SIG_DFL (:2942), takes the fatal branch for a
coredumping signal (:3016-3043) and reaches `do_group_exit` (kernel/exit.c:1095,
Linux v6.18.46).  The 0 this returns on that branch is never
observed, for `Kernel.Exit.exit_spec`'s reason: `Run.sstep_killed` ends
the trace with a `State.KillEv` and discards the effect. -/
def send_sigabrt : Sys SyscallEffect :=
  m <- get_model ;;
  (if sigabrt_blocked (m_sigmask m)
   then set_sigabrt_pending
   else set_killed (Z_to_bv 64 SIGABRT)) ;;
  ret_only (Z_to_bv 64 0)

/-- Everything `tkill` and `tgkill` share once the caller has named a
positive `pid`: whether it is this process, and what signal it is.  The
declaration is tested here too, so the helper is closed with it off
whichever spec reaches it.  A `pid` that is not the caller's own tid is
UNMODELED — `do_send_specific` looks it up (kernel/signal.c:4134, Linux
v6.18.46, commit 1f99e9ab748f) with `find_task_by_vpid` (kernel/pid.c:438,
Linux v6.18.46), which searches the whole namespace, and -ESRCH would be
a guess about every other process — and so is a call before `State.m_tid`
is pinned.  With the task found, `check_kill_permission`'s `valid_signal`
is -EINVAL for a signal above 64 (:805-806); then SIGABRT is delivered
and every other signal in 0..64 is UNMODELED: 0 because
`do_send_specific` skips delivery under `if (!error && sig)` (:4141) and
the answer is `security_task_kill`'s (:832), the rest because the model
has a disposition for SIGABRT and for no other signal. -/
def tkill_self (pid sig : word) : Sys SyscallEffect :=
  m <- get_model ;;
  if !(m_abort_terminal m) then unmodeled
  else
    match m_tid m with
    | none => unmodeled
    | some t =>
        if !(bv_eqb pid t) then unmodeled
        else if !(tkill_sig_valid sig) then err_ret EINVAL
        else if bv_eqb sig (Z_to_bv 64 SIGABRT) then send_sigabrt
        else unmodeled

/-- `tkill pid sig`, both already truncated (`Syscall.pid32`, `sig32`):
the declaration first, then `SYSCALL_DEFINE2(tkill)`'s `pid <= 0`
(kernel/signal.c:4195-4196, Linux v6.18.46, commit 1f99e9ab748f), then
`tkill_self` for `do_tkill(0, pid, sig)` (:4198). -/
def tkill_spec (pid sig : word) : Sys SyscallEffect :=
  m <- get_model ;;
  if !(m_abort_terminal m) then unmodeled
  else if !(pid_positive pid) then err_ret EINVAL
  else tkill_self pid sig

/-- `tgkill tgid pid sig`, all three already truncated: the declaration
first, then `SYSCALL_DEFINE3(tgkill)`'s `pid <= 0 || tgid <= 0`
(kernel/signal.c:4179-4180, Linux v6.18.46, commit 1f99e9ab748f), then the
one test `tgkill` adds over `tkill`: `do_send_specific` finds the task and
requires `task_tgid_vnr(p) == tgid` before it delivers, leaving the seeded
-ESRCH when it does not match (:4131, :4135).  In this model the caller's
tgid IS its tid — one thread, one group, the fact `State.procst_tid`
rests on — so the mismatch is decidable for the caller's own tid, and
undecidable (UNMODELED) for any other pid, as in `tkill_self`. -/
def tgkill_spec (tgid pid sig : word) : Sys SyscallEffect :=
  m <- get_model ;;
  if !(m_abort_terminal m) then unmodeled
  else if !(pid_positive pid && pid_positive tgid) then err_ret EINVAL
  else
    match m_tid m with
    | none => unmodeled
    | some t =>
        if !(bv_eqb pid t) then unmodeled
        else if !(bv_eqb tgid t) then err_ret ESRCH
        else tkill_self pid sig

/-- THE DECLARATION OFF IS THE OLD SURFACE, per arm.  Both specs test it
first, so with it clear the only outcome either admits is `Unmodeled` —
which is what the dispatcher produced for 130 and 131 before they had
arms.  This is the half of the compatibility claim that lives at the spec;
the other half is `set_sigmask_deliver_no_pending`, and the step-level
half is `Run.sstep_off_no_kill`.  Twin of Rocq's
`Signal.tkill_spec_off_unmodeled`. -/
theorem tkill_spec_off_unmodeled (pid sig : word) (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) (hoff : m_abort_terminal m = false)
    (h : tkill_spec pid sig i m o) : o = Unmodeled := by
  simp only [tkill_spec, bind_get_model_iff, hoff, Bool.not_false, ↓reduceIte] at h
  exact h

/-- Twin of Rocq's `Signal.tgkill_spec_off_unmodeled`. -/
theorem tgkill_spec_off_unmodeled (tgid pid sig : word) (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) (hoff : m_abort_terminal m = false)
    (h : tgkill_spec tgid pid sig i m o) : o = Unmodeled := by
  simp only [tgkill_spec, bind_get_model_iff, hoff, Bool.not_false, ↓reduceIte] at h
  exact h

end LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Signal
