import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude

/-! # Checks.Cases.Checks.Sys.Prelude — the checkers' shared helpers, read off against Linux

Pins over `Checks.Sys.Prelude`, the twin of
`theories/LinuxProcessSem/Checks/Sys/Prelude.v`.  The Rocq tree has no
check file for its Prelude — its lemmas are stated in the file itself —
so this file mirrors nothing: these are the Lean tree's tests for what
the twin ports, placed where every pin in this tree lives
(`Checks/Cases/<mirror path>`) so that
`tools/check_lean_pins.py` reads them and the twin holds only definitions
and their Rocq-twin lemmas.  Not part of the trusted specification: this
file is QA on the definitions, written to be READ.

The helpers under test decide what a checker ADMITS from a trace: which
returns count as errnos, which effects are return-only, which copy-in
ledgers match the read a spec recorded, which ranges a `copy_to_user`
could have written.  Each pin states one such decision on a concrete
value and refutes the concrete lie a kernel cannot tell — a return
outside the errno window, a write on a syscall that writes nothing, a
ledger that omits a pathname read — with the kernel line beside it.  The
last section exercises the tactic macros and claims nothing about Linux;
it says so.

No probe under `testing/syscall-check/` reaches anything here, and none
can: the harness runs the EXTRACTED ROCQ model (`check.sh` extracts it;
`testing/syscall-check/dune` builds `syscall_model`), so no Lean
definition is ever evaluated against a trace.  Where a pin below has a
probe that states the same fact of the Rocq side — `errno_openat.c`'s
`--mutate openat#2:ret=-ENOMEM` / `ret=-EBADF` for the two `errno_ret_in`
pins, `faccessat2_spec.c`'s `smuggle-zeros`/`smuggle-unmap`/
`smuggle-copy` for the `check_ret_only` ledger pins,
`bind_listen_spec.c`'s `drop-copyins` for the ledger pins — the kernel
line is still the evidence the pin cites, because the probe's verdict is
about the Rocq checker and this file is about the Lean one. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Prelude

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude
open LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Prelude (bytes_at)

section ErrnoWindow

/-! ## The errno window: `MAX_ERRNO` and `IS_ERR_VALUE`

`IS_ERR_VALUE(x)` is `(unsigned long)(x) >= (unsigned long)-MAX_ERRNO`
with `MAX_ERRNO` 4095 (include/linux/err.h:18 and :28, Linux v6.18.46,
commit 1f99e9ab748f).  `err.h` is about error POINTERS; what carries
the window to a syscall's return register is `syscall_get_error`
(arch/riscv/include/asm/syscall.h:46-52, v6.18.46), which reads `a0` and
answers it as an error exactly when `IS_ERR_VALUE` holds of it.  So a
riscv64 syscall return is an error exactly when it encodes `-e` for `e`
in `[1, 4095]`.  `errnos_ok` is the checker's premise that an injectable
set draws only from that window, and `errno_ret_in` is its test of a
claimed return against that set. -/

/-- Both ends of the window are admitted.  The top is `MAX_ERRNO`, not
an errno Linux defines — the highest in the uapi headers is `EHWPOISON`
133 (include/uapi/asm-generic/errno.h) — so the window is wider than the
errno set on purpose: it is the band `IS_ERR_VALUE` reserves, and every
implementation's errno choice lies inside it.
kernel: include/linux/err.h:MAX_ERRNO,IS_ERR_VALUE@v6.18.46 -/
theorem errnos_ok_admits_the_window : errnos_ok [1, 4095] = true := by decide

/-- 4096 is not: `(unsigned long)-4096` is below `(unsigned long)-4095`,
so `IS_ERR_VALUE` is false on it and a checker drawing from a set that
named it would read a valid return as a failure.
kernel: include/linux/err.h:IS_ERR_VALUE@v6.18.46 -/
theorem errnos_ok_refuses_4096 : errnos_ok [4096] = false := by decide

/-- And it scans the whole set, not its head: a good first entry does not
excuse a bad second one.  An injectable set is a checker's premise about
every errno an arm may answer, so one out-of-window entry spoils it.
kernel: include/linux/err.h:IS_ERR_VALUE@v6.18.46 -/
theorem errnos_ok_refuses_a_bad_entry_behind_a_good_one :
    errnos_ok [1, 4096] = false := by decide

/-- 0 is success, not an errno.
kernel: include/linux/err.h:IS_ERR_VALUE@v6.18.46 -/
theorem errnos_ok_refuses_zero : errnos_ok [0] = false := by decide

/-- A negative entry is refused too: `errno_ret` negates, so a set naming
`-22` would have the checker accept the SUCCESS return 22 as an -EINVAL.
kernel: include/linux/err.h:IS_ERR_VALUE; include/uapi/asm-generic/errno-base.h:EINVAL@v6.18.46 -/
theorem errnos_ok_refuses_a_negative : errnos_ok [-EINVAL] = false := by decide

/-- The corollary a checker relies on: `errno_ret (-22)` really is the
success return 22, which is why the entry above must be refused.
kernel: include/uapi/asm-generic/errno-base.h:EINVAL@v6.18.46 -/
theorem errno_ret_of_negative_is_a_success : errno_ret (-EINVAL) = Z_to_bv 64 22 := by decide

/-- -ENOMEM is an answer an anonymous `mmap` really gives (`do_mmap`,
mm/mmap.c:368-378, v6.18.46), so a branch drawn from a set naming it
admits that return.
kernel: mm/mmap.c:do_mmap; include/uapi/asm-generic/errno-base.h:ENOMEM@v6.18.46 -/
theorem errno_ret_in_admits_a_listed_errno : errno_ret_in [ENOMEM] (errno_ret ENOMEM) = true := by
  decide

/-- The lie: -EBADF is a real `mmap` answer — `ksys_mmap_pgoff`'s `fget`
failing on a file-backed request (mm/mmap.c:573-577, v6.18.46) — but it
belongs to the path `Sys/Mm/Mmap.v` declines, and a branch drawn from a
set that does not name it may not accept it.
kernel: mm/mmap.c:ksys_mmap_pgoff; include/uapi/asm-generic/errno-base.h:ENOMEM,EBADF@v6.18.46 -/
theorem errno_ret_in_refuses_an_unlisted_errno :
    errno_ret_in [ENOMEM] (errno_ret EBADF) = false := by
  decide

/-- A success return matches no errno: 0, and an fd.
kernel: include/linux/err.h:IS_ERR_VALUE; include/uapi/asm-generic/errno-base.h:ENOMEM,EINVAL@v6.18.46 -/
theorem errno_ret_in_refuses_zero : errno_ret_in [ENOMEM, EINVAL] (Z_to_bv 64 0) = false := by
  decide

/-- An fd — 3, the kind of value `alloc_fd` hands out — is a success
return and matches no errno either.
kernel: include/linux/err.h:IS_ERR_VALUE; include/uapi/asm-generic/errno-base.h:ENOMEM,EINVAL@v6.18.46 -/
theorem errno_ret_in_refuses_an_fd : errno_ret_in [ENOMEM, EINVAL] (Z_to_bv 64 3) = false := by
  decide

/-- An empty injectable set admits no failure at all.
model: an empty injectable set is the checker's own premise, which no line of Linux decides -/
theorem errno_ret_in_empty_admits_nothing : errno_ret_in [] (errno_ret EINVAL) = false := by
  decide

/-- The last value below the window, `-4096`, matches no errno even when
both ends of the window are injectable: `errno_ret_in_below`'s bound is
tight.
kernel: include/linux/err.h:MAX_ERRNO,IS_ERR_VALUE@v6.18.46 -/
theorem errno_ret_in_refuses_minus_4096 :
    errno_ret_in [1, 4095] (Z_to_bv 64 (2 ^ 64 - 4096)) = false := by decide

/-- The same fact again, proved THROUGH `errno_ret_in_below` rather than by
evaluating `errno_ret_in`.  That is the point of it: the pin above closes
by `decide` whatever the lemma's hypothesis says, so only this one holds
the lemma's bound at `two_pow_64 - 4096`.  Tighten that hypothesis by a
page and this stops elaborating.
model: holds the hypothesis of the twin's `errno_ret_in_below` at the window bottom -/
theorem errno_ret_in_below_holds_at_the_window_bottom :
    errno_ret_in [1, 4095] (Z_to_bv 64 (2 ^ 64 - 4096)) = false :=
  errno_ret_in_below _ _ (by decide) (by decide)

/-- And the fd bound at ITS edge: the largest fd below `2 ^ 31` is still
no errno.  Routed through `errno_ret_in_fd` for the same reason, so a
narrowed `2 ^ 31` stops elaborating here.
model: holds the hypothesis of the twin's `errno_ret_in_fd` at the largest fd it covers -/
theorem errno_ret_in_fd_holds_at_the_top_fd :
    errno_ret_in [1, 4095] (Z_to_bv 64 (2 ^ 31 - 1)) = false :=
  errno_ret_in_fd _ _ (by decide) (by decide)

end ErrnoWindow

section ReturnOnly

/-! ## Return-only effects

`SYSCALL_DEFINE1(close, unsigned int, fd)` (fs/open.c:1574-1602, Linux
v6.18.46, commit 1f99e9ab748f) is the shape `check_ret_only` decides:
`file_close_fd`, `filp_flush`, `fput_close_sync` and a return — no
`copy_to_user` anywhere in the body, so the only thing a trace of it can
carry is the return.  The returns are 0 when `filp_flush` succeeded,
-EBADF for a fd the table did not hold, and otherwise the flush's own
error — except that the four restart codes are remapped to -EINTR before
they are returned, because the table entry is already cleared and the
call cannot be restarted (fs/open.c:1594-1599, v6.18.46). -/

variable (m : Model) (evs : List event) (a : word) (b : byte)

/-- The return the checker asked for, and nothing else, is admitted.
kernel: fs/open.c:close@v6.18.46 -/
theorem check_ret_only_admits_the_return :
    check_ret_only (mkEffect (Z_to_bv 64 0) [] []) (Z_to_bv 64 0) m evs = CheckOk m evs :=
  (check_ret_only_ok_iff _ _ m evs m evs).mpr ⟨rfl, rfl, rfl⟩

/-- Another return is refused: a `close` whose fd the table held and
whose `filp_flush` returned 0 returns 0 (fs/open.c:1591-1592, v6.18.46 —
the guard there is `retval == 0`, not the fd lookup), and a trace
claiming -EBADF there is a lie: -EBADF is reachable only from the
`file_close_fd` failure above it, which returns before the flush.
kernel: fs/open.c:close@v6.18.46 -/
theorem check_ret_only_rejects_another_return :
    check_ret_only (mkEffect (errno_ret EBADF) [] []) (Z_to_bv 64 0) m evs = CheckReject := by
  simp only [check_ret_only, show bv_eqb (errno_ret EBADF) (Z_to_bv 64 0) = false by decide,
    Bool.false_eq_true, ↓reduceIte]

/-- A write is refused even beside the right return: `close` has no
`copy_to_user`, so a trace reporting one byte written by it is a lie.
kernel: fs/open.c:close@v6.18.46 -/
theorem check_ret_only_rejects_a_write :
    check_ret_only (mkEffect (Z_to_bv 64 0) [(a, [b])] []) (Z_to_bv 64 0) m evs = CheckReject := rfl

/-- So is a copy-in ledger: the acceptor is for the shape that reads
nothing, and the ledgered shapes have `check_ret_only_copyins`.
kernel: fs/open.c:close@v6.18.46 -/
theorem check_ret_only_rejects_a_ledger :
    check_ret_only (with_copyins [(a, 1)] (mkEffect (Z_to_bv 64 0) [] [])) (Z_to_bv 64 0) m evs
      = CheckReject := rfl

/-- A zero-fill range is refused too.  The acceptor demands all FIVE of
the effect's ledgers empty, and a pin per ledger is what stops the
pattern being widened one field at a time: `close` zero-fills nothing.
kernel: fs/open.c:close@v6.18.46 -/
theorem check_ret_only_rejects_a_zero_range :
    check_ret_only (mkEffect (Z_to_bv 64 0) [] [(a, 4096#64)]) (Z_to_bv 64 0) m evs
      = CheckReject := rfl

/-- So is an unmap: nothing in `close` touches the address space.
kernel: fs/open.c:close@v6.18.46 -/
theorem check_ret_only_rejects_an_unmap :
    check_ret_only (SyscallEffect.mkEffectU (Z_to_bv 64 0) [] [] [(a, 4096#64)] [] [])
      (Z_to_bv 64 0) m evs = CheckReject := rfl

/-- And so is a pre-effect copy.
kernel: fs/open.c:close@v6.18.46 -/
theorem check_ret_only_rejects_a_copy :
    check_ret_only (SyscallEffect.mkEffectU (Z_to_bv 64 0) [] [] []
      [MemCopy.mkCopy 4096#64 8192#64 16#64] []) (Z_to_bv 64 0) m evs = CheckReject := rfl

/-- The acceptor never declines: a return-only syscall is inside the
modeled surface whatever its return is.
model: an acceptor over a Boolean equality has no declining arm; the modeled surface is the calling arm's question -/
theorem check_ret_only_never_declines :
    check_ret_only (mkEffect (errno_ret EBADF) [] []) (Z_to_bv 64 0) m evs ≠ CheckUnmodeled :=
  check_ret_only_no_unmodeled _ _ m evs

/-! ### `eff_is_errno`: an errno the kernel returned having moved no bytes

`_inline_copy_to_user` (include/linux/uaccess.h:190-200, v6.18.46) tests
`access_ok` over the whole range and, when it fails, returns `n` with
`raw_copy_to_user` never called: -EFAULT from THAT GATE comes with no
byte written.  The scope matters and is narrow.  -EFAULT in general does
not imply an untouched buffer: `raw_copy_to_user` stops at the first
unmapped byte and leaves the prefix written, and a caller that then
answers -EFAULT reports a fault over bytes it really did store —
`SYSCALL_DEFINE2(gettimeofday, …)` (kernel/time/time.c:140-156,
v6.18.46) returns -EFAULT from the second `put_user` with `tv_sec`
already in user memory.  `eff_is_errno` is the zero-byte shape alone, as
its twin's docstring says ("when the kernel moved no bytes"); an arm that
reaches for it where a partial copy is possible would refuse a real
trace. -/

/-- The bare errno, with no write, is that shape.
kernel: include/linux/uaccess.h:_inline_copy_to_user; include/uapi/asm-generic/errno-base.h:EFAULT@v6.18.46 -/
theorem eff_is_errno_admits_the_bare_errno :
    eff_is_errno EFAULT (mkEffect (errno_ret EFAULT) [] []) = true := by decide

/-- The lie, for an arm whose only user write is the one that faulted: a
write beside -EFAULT, when the gate that answered it called no copy.
This is not a claim that Linux never returns -EFAULT having written (see
the section note); it is the acceptor refusing a shape its own callers
have already excluded.
kernel: include/linux/uaccess.h:_inline_copy_to_user; include/uapi/asm-generic/errno-base.h:EFAULT@v6.18.46 -/
theorem eff_is_errno_refuses_a_write :
    eff_is_errno EFAULT (mkEffect (errno_ret EFAULT) [(a, [b])] []) = false := rfl

/-- Another errno is not this one.
kernel: include/linux/uaccess.h:_inline_copy_to_user; include/uapi/asm-generic/errno-base.h:EFAULT,EINVAL@v6.18.46 -/
theorem eff_is_errno_refuses_another_errno :
    eff_is_errno EFAULT (mkEffect (errno_ret EINVAL) [] []) = false := by decide

/-- Nor is a success return.
kernel: include/linux/uaccess.h:_inline_copy_to_user; include/uapi/asm-generic/errno-base.h:EFAULT@v6.18.46 -/
theorem eff_is_errno_refuses_a_success :
    eff_is_errno EFAULT (mkEffect (Z_to_bv 64 0) [] []) = false := by decide

/-- The remaining four ledgers are refused beside the errno as well.  The
acceptor is the shape that moved NOTHING, and each ledger is a separate
way for a trace to claim it moved something, so each gets its own pin
rather than resting on the write above.
kernel: include/linux/uaccess.h:_inline_copy_to_user; include/uapi/asm-generic/errno-base.h:EFAULT@v6.18.46 -/
theorem eff_is_errno_refuses_a_zero_range :
    eff_is_errno EFAULT (mkEffect (errno_ret EFAULT) [] [(a, 4096#64)]) = false := rfl

/-- An unmap beside the errno.
kernel: include/linux/uaccess.h:_inline_copy_to_user; include/uapi/asm-generic/errno-base.h:EFAULT@v6.18.46 -/
theorem eff_is_errno_refuses_an_unmap :
    eff_is_errno EFAULT
      (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] [(a, 4096#64)] [] []) = false := rfl

/-- A pre-effect copy beside the errno.
kernel: include/linux/uaccess.h:_inline_copy_to_user; include/uapi/asm-generic/errno-base.h:EFAULT@v6.18.46 -/
theorem eff_is_errno_refuses_a_copy :
    eff_is_errno EFAULT (SyscallEffect.mkEffectU (errno_ret EFAULT) [] [] []
      [MemCopy.mkCopy 4096#64 8192#64 16#64] []) = false := rfl

/-- And a copy-in ledger: the gate that refused the range before copying
read nothing in on this arm's behalf either.
kernel: include/linux/uaccess.h:_inline_copy_to_user; include/uapi/asm-generic/errno-base.h:EFAULT@v6.18.46 -/
theorem eff_is_errno_refuses_a_ledger :
    eff_is_errno EFAULT (with_copyins [(a, 1)] (mkEffect (errno_ret EFAULT) [] [])) = false := rfl

/-- The `code` really is a parameter: the acceptor answers for -EINVAL as
readily as for -EFAULT.  Every pin above passes `EFAULT`, so without this
one a body that ignored `code` and tested against a hardcoded -EFAULT
would pass them all.
kernel: include/uapi/asm-generic/errno-base.h:EINVAL@v6.18.46 -/
theorem eff_is_errno_admits_another_code :
    eff_is_errno EINVAL (mkEffect (errno_ret EINVAL) [] []) = true := by decide

end ReturnOnly

section Ledger

/-! ## The copy-in ledger

A syscall that resolves a pathname reads it out of user memory first:
`getname_flags` (fs/namei.c:135-157, Linux v6.18.46, commit
1f99e9ab748f) copies it in at line 157 by calling `strncpy_from_user`
(defined in lib/strncpy_from_user.c:113, v6.18.46) before any lookup, and
`Syscall.record_copyins` puts that range on the effect's ledger.  The
ledger is outcome data (`Sys/Syscall.lean` says why: the same errno can
come before or after the copy, and `State.materialize_model_accesses`
charges what was read), so a checker compares it exactly, in order, and
an empty ledger on a syscall that read is a lie. -/

/-! The pathname sits at 4096 and the body's own read at 8192: literal
addresses, because the reflection compares them with `bv_eqb`, which
reduces on literals and is stuck on a variable. -/

variable (m : Model) (evs : List event) (r : word)

/-- The ledger the spec recorded is admitted.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem check_copyins_after_admits_the_recorded_read :
    check_copyins_after [(4096#64, 5)]
      (with_copyins [(4096#64, 5)] (mkEffect r [] [])) (CheckOk m evs)
      = CheckOk m evs :=
  (check_copyins_after_ok_iff _ _ _ m evs).mpr ⟨rfl, rfl⟩

/-- The lie: a syscall that resolved a pathname and claims to have read
nothing.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem check_copyins_after_rejects_an_empty_ledger :
    check_copyins_after [(4096#64, 5)] (mkEffect r [] []) (CheckOk m evs) = CheckReject := rfl

/-- A wider ledger is refused too: the acceptor is for a spec whose body
performs ONE pathname read and no later copy-in, so a second range is
a read the spec did not make.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem check_copyins_after_rejects_a_wider_ledger :
    check_copyins_after [(4096#64, 5)]
      (with_copyins [(4096#64, 5), (8192#64, 2)] (mkEffect r [] [])) (CheckOk m evs)
      = CheckReject := rfl

/-- A shorter range at the same address is a different read.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem check_copyins_after_rejects_a_shorter_read :
    check_copyins_after [(4096#64, 5)]
      (with_copyins [(4096#64, 4)] (mkEffect r [] [])) (CheckOk m evs)
      = CheckReject := rfl

/-- A decline passes straight through: the model left its surface and
makes no claim about what was copied.
model: a decline is the model leaving its surface, and it claims nothing about what was copied -/
theorem check_copyins_after_passes_a_decline :
    check_copyins_after [(4096#64, 5)] (mkEffect r [] []) CheckUnmodeled = CheckUnmodeled := rfl

/-- ...and a decline is never manufactured from a ledger mismatch.
model: a ledger mismatch is a rejection by construction, never a decline -/
theorem check_copyins_after_never_declines_on_a_mismatch :
    check_copyins_after [(4096#64, 5)] (mkEffect r [] []) (CheckOk m evs) ≠ CheckUnmodeled := by
  rw [check_copyins_after_rejects_an_empty_ledger]
  exact nofun

/-- Nor is a rejection ever turned back into an admission by a ledger
that happens to match.
model: the ledger comparison cannot turn a rejection back into an admission -/
theorem check_copyins_after_keeps_a_rejection :
    check_copyins_after [(4096#64, 5)] (with_copyins [(4096#64, 5)] (mkEffect r [] [])) CheckReject
      = CheckReject := rfl

/-! ### `check_copyins`: the same ledger test WITHOUT the decline guard

`check_copyins_after` is `check_copyins` with a decline taken out of the
way first, and that is the whole difference between them: on a ledger
MISMATCH `check_copyins` answers `CheckReject` whatever it was handed, a
decline included, where `check_copyins_after` hands the decline back
untouched.  The arms that reach for the bare form pass a result already
known not to be a decline.  Pinned here because the two are one `match`
apart: a port that gave this one the guard too would leave every pin of
`check_copyins_after` closing unchanged. -/

/-- The recorded read is admitted and the body's own answer passes
through.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem check_copyins_admits_the_recorded_read :
    check_copyins [(4096#64, 5)] (with_copyins [(4096#64, 5)] (mkEffect r [] []))
      (CheckOk m evs) = CheckOk m evs := rfl

/-- The lie: an empty ledger on a syscall that resolved a pathname.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem check_copyins_rejects_an_empty_ledger :
    check_copyins [(4096#64, 5)] (mkEffect r [] []) (CheckOk m evs) = CheckReject := rfl

/-- A rejection is not turned back into an admission by a matching
ledger.
model: the ledger comparison cannot turn a rejection back into an admission -/
theorem check_copyins_keeps_a_rejection :
    check_copyins [(4096#64, 5)] (with_copyins [(4096#64, 5)] (mkEffect r [] [])) CheckReject
      = CheckReject := rfl

/-- A decline passes through when the ledger MATCHES.
model: on a matching ledger the acceptor is the identity on its result -/
theorem check_copyins_passes_a_decline_on_a_match :
    check_copyins [(4096#64, 5)] (with_copyins [(4096#64, 5)] (mkEffect r [] [])) CheckUnmodeled
      = CheckUnmodeled := rfl

/-- ...and is turned into a rejection when it does not.  This is the arm
that separates `check_copyins` from `check_copyins_after`.
model: the bare form has no decline guard; its callers pass a result already known not to be one -/
theorem check_copyins_rejects_a_decline_on_a_mismatch :
    check_copyins [(4096#64, 5)] (mkEffect r [] []) CheckUnmodeled = CheckReject := rfl

/-- The two acceptors really do differ there, stated as the inequality a
port that merged them would have to break.
model: the two acceptors differ exactly on a decline meeting a mismatched ledger -/
theorem check_copyins_differs_from_after_on_a_declined_mismatch :
    check_copyins [(4096#64, 5)] (mkEffect r [] []) CheckUnmodeled
      ≠ check_copyins_after [(4096#64, 5)] (mkEffect r [] []) CheckUnmodeled := by
  rw [check_copyins_rejects_a_decline_on_a_mismatch, check_copyins_after_passes_a_decline]
  exact nofun

/-! ### The prefix forms

`check_copyin_prefix` and `strip_copyin_prefix` are for a spec whose
recorded read is FOLLOWED by copy-ins of its own: the recorded range is
the ledger's prefix, in the order the kernel performed the copies —
`Sys/Syscall.lean`'s `record_copyins` says why that order is
load-bearing for the models a checker compares by equality. -/

/-- The recorded read at the head, the body's own read behind it.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem check_copyin_prefix_admits_the_prefix :
    check_copyin_prefix [(4096#64, 5)]
      (with_copyins [(4096#64, 5), (8192#64, 2)] (mkEffect r [] [])) (CheckOk m evs)
      = CheckOk m evs := rfl

/-- The lie: the same two ranges in the other order, which would have the
body's copy happen before the pathname was read.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem check_copyin_prefix_rejects_the_other_order :
    check_copyin_prefix [(4096#64, 5)]
      (with_copyins [(8192#64, 2), (4096#64, 5)] (mkEffect r [] [])) (CheckOk m evs)
      = CheckReject := rfl

/-- An empty ledger has no such prefix.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem check_copyin_prefix_rejects_an_empty_ledger :
    check_copyin_prefix [(4096#64, 5)] (mkEffect r [] []) (CheckOk m evs) = CheckReject := rfl

/-- A decline passes through here as well.
model: a decline is the model leaving its surface, and it claims nothing about what was copied -/
theorem check_copyin_prefix_passes_a_decline :
    check_copyin_prefix [(4096#64, 5)] (mkEffect r [] []) CheckUnmodeled = CheckUnmodeled := rfl

/-- A rejection stays a rejection, prefix or no prefix.  Only the DECLINE
gets the pass-through arm; a second arm sending `CheckReject` to
`CheckUnmodeled` would launder a refused trace into "outside the modeled
surface", and this is the pin that refuses it.  `check_copyins_after` has
the same guard one section above.
model: a rejection is a refused trace; only a decline leaves the modeled surface -/
theorem check_copyin_prefix_keeps_a_rejection :
    check_copyin_prefix [(4096#64, 5)]
      (with_copyins [(4096#64, 5), (8192#64, 2)] (mkEffect r [] [])) CheckReject
      = CheckReject := rfl

/-- Stripping the recorded prefix leaves exactly the body's own reads,
and touches nothing else on the effect.
model: a closed computation over the effect's ledger -/
theorem strip_copyin_prefix_drops_exactly_the_prefix :
    strip_copyin_prefix [(4096#64, 5)]
      (with_copyins [(4096#64, 5), (8192#64, 2)] (mkEffect r [] []))
      = with_copyins [(8192#64, 2)] (mkEffect r [] []) := rfl

/-- It strips by COUNT, not by value: what the prefix held is
`check_copyin_prefix`'s question, so a mismatched head is still dropped
here and refused there.
model: a closed computation over the effect's ledger -/
theorem strip_copyin_prefix_strips_by_count :
    strip_copyin_prefix [(4096#64, 5)]
      (with_copyins [(8192#64, 2), (4096#64, 5)] (mkEffect r [] []))
      = with_copyins [(4096#64, 5)] (mkEffect r [] []) := rfl

/-! Every pin above uses a ONE-range `reads` against a two-range ledger,
and at that length several different offsets agree: `take reads.length`,
`take 1`, and a count measured back from the ledger's end all pick the
same element.  The three below use a TWO-range `reads` against a
three-range ledger, which is the shortest shape that separates them. -/

/-- Two recorded ranges at the head, the body's own read behind them.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem check_copyin_prefix_admits_a_two_range_prefix :
    check_copyin_prefix [(4096#64, 5), (8192#64, 2)]
      (with_copyins [(4096#64, 5), (8192#64, 2), (12288#64, 3)] (mkEffect r [] []))
      (CheckOk m evs) = CheckOk m evs := rfl

/-- The lie at that length: the two recorded ranges present but swapped,
which would have the second copy happen before the first.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem check_copyin_prefix_rejects_a_two_range_prefix_out_of_order :
    check_copyin_prefix [(4096#64, 5), (8192#64, 2)]
      (with_copyins [(8192#64, 2), (4096#64, 5), (12288#64, 3)] (mkEffect r [] []))
      (CheckOk m evs) = CheckReject := rfl

/-- And the strip drops BOTH recorded ranges, not one: the offset is
`reads.length`, so a `drop` fixed at 1 leaves a range behind here.
model: a closed computation over the effect's ledger -/
theorem strip_copyin_prefix_drops_two_ranges :
    strip_copyin_prefix [(4096#64, 5), (8192#64, 2)]
      (with_copyins [(4096#64, 5), (8192#64, 2), (12288#64, 3)] (mkEffect r [] []))
      = with_copyins [(12288#64, 3)] (mkEffect r [] []) := rfl

/-- And it touches nothing but the ledger.  Quantified over the writes,
the zero-fills, the unmaps and the copies, because the pins above all use
an effect whose other four ledgers are empty, and an implementation that
dropped one of them would agree with every one of them.
model: a closed computation over the effect's ledger -/
theorem strip_copyin_prefix_keeps_the_rest (ws : List (word × List byte))
    (zs us : List (word × word)) (cs : List MemCopy) :
    strip_copyin_prefix [(4096#64, 5)]
      (SyscallEffect.mkEffectU r ws zs us cs [(4096#64, 5), (8192#64, 2)])
      = SyscallEffect.mkEffectU r ws zs us cs [(8192#64, 2)] := rfl

/-- Clearing the ledger clears only the ledger.
model: a closed computation over the effect's ledger -/
theorem clear_copyins_keeps_the_rest (ws : List (word × List byte))
    (zs us : List (word × word)) (cs : List MemCopy) :
    clear_copyins (SyscallEffect.mkEffectU r ws zs us cs [(4096#64, 5)])
      = SyscallEffect.mkEffectU r ws zs us cs [] := rfl

/-! ### `check_ret_only_copyins`: a return plus the recorded read -/

/-- The recorded read beside the asked-for return is admitted.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem check_ret_only_copyins_admits_the_read :
    check_ret_only_copyins [(4096#64, 5)]
      (with_copyins [(4096#64, 5)] (mkEffect (Z_to_bv 64 0) [] []))
      (Z_to_bv 64 0) m evs = CheckOk m evs :=
  check_ret_only_copyins_refl _ _ m evs

/-- The lie: the read dropped from the ledger.
kernel: fs/namei.c:getname_flags@v6.18.46 -/
theorem check_ret_only_copyins_rejects_an_empty_ledger :
    check_ret_only_copyins [(4096#64, 5)] (mkEffect (Z_to_bv 64 0) [] []) (Z_to_bv 64 0) m evs
      = CheckReject := rfl

/-- A write beside the right return and the right ledger is still refused:
the shape is return-only.
kernel: fs/namei.c:getname_flags; fs/open.c:close@v6.18.46 -/
theorem check_ret_only_copyins_rejects_a_write (b : byte) :
    check_ret_only_copyins [(4096#64, 5)]
      (with_copyins [(4096#64, 5)] (mkEffect (Z_to_bv 64 0) [(8192#64, [b])] []))
      (Z_to_bv 64 0) m evs = CheckReject := rfl

/-- And the ledger is checked only after the return: a wrong return with
the right ledger is a rejection, not an admission.
kernel: fs/namei.c:getname_flags; fs/open.c:close@v6.18.46 -/
theorem check_ret_only_copyins_rejects_a_wrong_return :
    check_ret_only_copyins [(4096#64, 5)]
      (with_copyins [(4096#64, 5)] (mkEffect (errno_ret EBADF) [] []))
      (Z_to_bv 64 0) m evs = CheckReject := by
  simp only [check_ret_only_copyins, clear_copyins, with_copyins, check_ret_only,
    show bv_eqb (errno_ret EBADF) (Z_to_bv 64 0) = false by decide, Bool.false_eq_true,
    ↓reduceIte]

end Ledger

section WritableRange

/-! ## `wmem_ok`: could `copy_to_user` have written the range?

`_inline_copy_to_user` (include/linux/uaccess.h:190-200, v6.18.46) is
`access_ok` over the whole range and then `raw_copy_to_user`, which
stops at the first unmapped byte: the fixup of
`fallback_scalar_usercopy_sum_enabled` reports the uncopied count as
the distance to the terminal address (arch/riscv/lib/uaccess.S:61
`add t5, a0, a2`, and :212-214 `10: sub a0, t5, a0; ret`, v6.18.46).
`wmem_ok` asks the writable view whether
every byte of the range is there; the MMU half (`access_ok`) is
`State.access_okb`'s, pinned in `Checks/Cases/State.lean`. -/

/-- A syscall input whose writable view is `bs` laid out from `base` and
nothing else.  The map is `Checks/Cases/Prelude.lean`'s `bytes_at`, the
tree's shared byte-map fixture, rather than a local copy: its lower
bound is load-bearing (without it every address below `base` subtracts
to a negative `Int`, which `Int.toNat` takes to 0, so the map would
answer the first byte for the whole space below it) and that argument is
already pinned there as `bytes_at_guard_is_load_bearing`. -/
def input_of (base : word) (bs : List byte) : SyscallInput :=
  SyscallInput.mkInput (Z_to_bv 64 0) [] (fun _ => none) (bytes_at base bs)

/-- Four writable bytes at 0x1000: a four-byte write there lands.
kernel: include/linux/uaccess.h:_inline_copy_to_user@v6.18.46 -/
theorem wmem_ok_admits_a_mapped_range :
    wmem_ok (input_of 0x1000 [0#8, 0#8, 0#8, 0#8]) (Z_to_bv 64 0x1000) (Z_to_bv 64 4) = true := by
  decide

/-- The same four bytes, and a five-byte write: the fifth byte is not
there, so the copy faults and the checker must not accept a full write.
kernel: include/linux/uaccess.h:_inline_copy_to_user@v6.18.46 -/
theorem wmem_ok_refuses_a_range_past_the_mapping :
    wmem_ok (input_of 0x1000 [0#8, 0#8, 0#8, 0#8]) (Z_to_bv 64 0x1000) (Z_to_bv 64 5) = false := by
  decide

/-- A range starting one byte before the mapping is refused as a whole:
`wmem_ok` is all-or-nothing, as `copy_to_user`'s full-count success is.
kernel: include/linux/uaccess.h:_inline_copy_to_user@v6.18.46 -/
theorem wmem_ok_refuses_a_range_before_the_mapping :
    wmem_ok (input_of 0x1000 [0#8, 0#8, 0#8, 0#8]) (Z_to_bv 64 0xfff) (Z_to_bv 64 2) = false := by
  decide

/-- A zero-length write lands at any address the MMU half admits:
`raw_copy_to_user` of no bytes copies nothing and reports nothing
uncopied.  (`access_ok` still bounds the address even at size 0 —
`include/asm-generic/access_ok.h:__access_ok` tests `addr <= limit -
size` — which is `State.access_okb`'s pin, not this one's.)
kernel: include/linux/uaccess.h:_inline_copy_to_user@v6.18.46 -/
theorem wmem_ok_admits_a_zero_length_range :
    wmem_ok (input_of 0x1000 []) (Z_to_bv 64 0x8000) (Z_to_bv 64 0) = true := by decide

/-- A prefix of an admitted range is admitted: the delivered prefix of a
short read is writable whenever the whole buffer was.
kernel: include/linux/uaccess.h:_inline_copy_to_user@v6.18.46 -/
theorem wmem_ok_admits_a_prefix :
    wmem_ok (input_of 0x1000 [0#8, 0#8, 0#8, 0#8]) (Z_to_bv 64 0x1000) (Z_to_bv 64 2) = true :=
  wmem_ok_of_full _ _ (Z_to_bv 64 4) [0#8, 0#8, 0#8, 0#8] (Z_to_bv 64 2) (by decide) (by decide)

end WritableRange

section ShortWrite

/-! ## The short-write bridges

A channel write that moves fewer bytes than asked returns the count it
moved, and the acceptor has to get from that return back to the prefix
it selected.  `vfs_write` (fs/read_write.c:666-696, Linux v6.18.46)
returns `ret` from `f_op->write` or `new_sync_write` unchanged whenever
it is positive, and clamps `count` to `MAX_RW_COUNT` before the call, so
a positive return may be anything up to that clamp and is not required
to be the requested count.  The two bridges are `len_word_firstn_ret`,
which says the delivered prefix's length word IS that return, and
`neq_einval_of_not_error`, which says a return that is not error-encoded
is not the -EINVAL an errno arm would claim. -/

/-- Three bytes offered, two written: the prefix's `len_word` is the
return that chose it.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem len_word_of_a_short_prefix :
    len_word (([1#8, 2#8, 3#8] : List byte).take (bv_unsigned (Z_to_bv 64 2)).toNat)
      = Z_to_bv 64 2 := by decide

/-- The full write is the same statement at the other end of the range.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem len_word_of_a_full_prefix :
    len_word (([1#8, 2#8, 3#8] : List byte).take (bv_unsigned (Z_to_bv 64 3)).toNat)
      = Z_to_bv 64 3 := by decide

/-- The lie the bridge refuses: a short return beside the WHOLE buffer.
A trace claiming it wrote two bytes and delivering three is not a short
write, and `len_word` of the three-byte list is 3, not the claimed 2.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem len_word_refuses_a_prefix_that_is_not_the_return :
    len_word ([1#8, 2#8, 3#8] : List byte) ≠ Z_to_bv 64 2 := by decide

/-- A success return is not the -EINVAL an errno arm would claim, and it
is not error-encoded: the two halves `neq_einval_of_not_error` relates.
kernel: include/linux/err.h:IS_ERR_VALUE; include/uapi/asm-generic/errno-base.h:EINVAL@v6.18.46 -/
theorem a_short_count_is_not_einval :
    addr_is_error_b (Z_to_bv 64 2) = false ∧ bv_eqb (errno_ret EINVAL) (Z_to_bv 64 2) = false := by
  decide

/-- ...while -EINVAL itself IS error-encoded, so the hypothesis the
bridge needs really does exclude it.
kernel: include/linux/err.h:IS_ERR_VALUE; include/uapi/asm-generic/errno-base.h:EINVAL@v6.18.46 -/
theorem einval_is_error_encoded : addr_is_error_b (errno_ret EINVAL) = true := by decide

/-- ...and the bridge really is about -EINVAL: applying the twin at that
errno is what fixes the constant in its statement, since a twin restated
over another errno would not have this type.
model: fixes the errno constant in the twin's `neq_einval_of_not_error` by applying it -/
theorem einval_is_not_a_non_error_return (r : word) (h : addr_is_error_b r = false) :
    bv_eqb (errno_ret EINVAL) r = false :=
  neq_einval_of_not_error r h

/-- The decimal `error_b_big` concludes with, spelled as what it is: the
bottom of the error window.  This does NOT catch a mistyped digit in the
lemma — a smaller bound is a weaker conclusion from the same hypothesis
and still proves — so it is here for the reader, who otherwise has no
checked way to read 18446744073709547520 as `two_pow_64 - 4096`, the
bottom of the band `MAX_ERRNO` reserves.
model: an identity between the twin's decimal and the model's `two_pow_64` -/
theorem the_error_b_big_bound_is_the_window_bottom :
    (18446744073709547520 : Int) = two_pow_64 - 4096 := by decide

/-- A shorter walk over a range that reads whole is that range's prefix,
AT FULL LENGTH — the `k = n` case, which is what the `MAX_RW_COUNT` clamp
leaves when the count is under the clamp.  Routed through the twin, so a
hypothesis narrowed to `k < n` stops elaborating here.
model: holds the hypothesis of the twin's `readable_bytes_aux_prefix` at k = n -/
theorem readable_bytes_aux_prefix_holds_at_full_length :
    readable_bytes_aux (bytes_at 4096 [1#8, 2#8]) 4096 2 = ([1#8, 2#8] : List byte).take 2 :=
  readable_bytes_aux_prefix (bytes_at 4096 [1#8, 2#8]) 2 2 4096 [1#8, 2#8]
    (by decide) (by decide)

end ShortWrite

section Reflections

/-! ## The equality reflections

No kernel claim here: `listN_eqb`, `listNN_eqb`, `copy_eqb`,
`listCopy_eqb`, `writes_eqb` and `access_ranges_eqb` decide equality
of the effect's components, and their `_eq` lemmas in the twin are their
specification and the guard against a reflection that compared one
field short.  The instances below are samples of that guard, so a reader
can see the comparison happening without unfolding the `_eq` proof.
Each reflection gets one instance that ADMITS an equal pair and
instances that tell it apart on each thing it can get wrong — a
component, a length, or the order of two entries.  The positive is not
decoration: without it a reflection mutated to a constant `false` passes
every negative here. -/

/-- `listN_eqb` tells a byte apart.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem listN_eqb_tells_a_byte_apart : listN_eqb [1#8, 2#8] [1#8, 3#8] = false := by decide
/-- `listN_eqb` tells a length apart.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem listN_eqb_tells_a_length_apart : listN_eqb [1#8, 2#8] [1#8] = false := by decide
/-- `listN_eqb` admits equal lists.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem listN_eqb_admits_equal_lists : listN_eqb [1#8, 2#8] [1#8, 2#8] = true := by decide

/-- `listNN_eqb` tells a size apart.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem listNN_eqb_tells_a_size_apart :
    listNN_eqb [(4096#64, 4096#64)] [(4096#64, 8192#64)] = false := by
  decide
/-- `listNN_eqb` tells a base apart.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem listNN_eqb_tells_a_base_apart :
    listNN_eqb [(4096#64, 4096#64)] [(8192#64, 4096#64)] = false := by
  decide
/-- `listNN_eqb` tells a tail apart.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem listNN_eqb_tells_a_tail_apart :
    listNN_eqb [(4096#64, 4096#64), (8192#64, 4096#64)]
      [(4096#64, 4096#64), (8192#64, 8192#64)] = false := by
  decide

/-- `listNN_eqb` tells a length apart: the catch-all arm, which the
per-component pins never reach.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem listNN_eqb_tells_a_length_apart :
    listNN_eqb [(4096#64, 4096#64)] [] = false := by decide
/-- `listNN_eqb` admits equal lists.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem listNN_eqb_admits_equal_lists :
    listNN_eqb [(4096#64, 4096#64), (8192#64, 8192#64)]
      [(4096#64, 4096#64), (8192#64, 8192#64)] = true := by
  decide

/-- `copy_eqb` tells a source apart.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem copy_eqb_tells_a_source_apart :
    copy_eqb (MemCopy.mkCopy 1#64 2#64 3#64) (MemCopy.mkCopy 9#64 2#64 3#64) = false := by decide
/-- `copy_eqb` tells a destination apart.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem copy_eqb_tells_a_destination_apart :
    copy_eqb (MemCopy.mkCopy 1#64 2#64 3#64) (MemCopy.mkCopy 1#64 5#64 3#64) = false := by decide
/-- `copy_eqb` tells a length apart.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem copy_eqb_tells_a_length_apart :
    copy_eqb (MemCopy.mkCopy 1#64 2#64 3#64) (MemCopy.mkCopy 1#64 2#64 4#64) = false := by decide
/-- `copy_eqb` admits an equal copy.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem copy_eqb_admits_an_equal_copy :
    copy_eqb (MemCopy.mkCopy 1#64 2#64 3#64) (MemCopy.mkCopy 1#64 2#64 3#64) = true := by decide

/-- `listCopy_eqb` tells a tail apart.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem listCopy_eqb_tells_a_tail_apart :
    listCopy_eqb [MemCopy.mkCopy 1#64 2#64 3#64, MemCopy.mkCopy 4#64 5#64 6#64]
      [MemCopy.mkCopy 1#64 2#64 3#64, MemCopy.mkCopy 4#64 5#64 7#64] = false := by decide
/-- `listCopy_eqb` tells a length apart.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem listCopy_eqb_tells_a_length_apart :
    listCopy_eqb [MemCopy.mkCopy 1#64 2#64 3#64] [] = false := by decide
/-- `listCopy_eqb` admits equal lists.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem listCopy_eqb_admits_equal_lists :
    listCopy_eqb [MemCopy.mkCopy 1#64 2#64 3#64] [MemCopy.mkCopy 1#64 2#64 3#64] = true := by
  decide

/-- `writes_eqb` tells the bytes apart.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem writes_eqb_tells_the_bytes_apart :
    writes_eqb [(4096#64, [1#8])] [(4096#64, [2#8])] = false := by decide
/-- `writes_eqb` tells the address apart.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem writes_eqb_tells_the_address_apart :
    writes_eqb [(4096#64, [1#8])] [(4097#64, [1#8])] = false := by decide
/-- `writes_eqb` tells a tail apart.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem writes_eqb_tells_a_tail_apart :
    writes_eqb [(4096#64, [1#8]), (8192#64, [2#8])] [(4096#64, [1#8]), (8192#64, [3#8])]
      = false := by
  decide

/-- `writes_eqb` tells a length apart.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem writes_eqb_tells_a_length_apart :
    writes_eqb [(4096#64, [1#8])] [] = false := by decide
/-- `writes_eqb` admits equal write lists.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem writes_eqb_admits_equal_lists :
    writes_eqb [(4096#64, [1#8]), (8192#64, [2#8])] [(4096#64, [1#8]), (8192#64, [2#8])]
      = true := by
  decide

/-- `access_ranges_eqb` tells a count apart.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem access_ranges_eqb_tells_a_count_apart :
    access_ranges_eqb [(4096#64, 5)] [(4096#64, 6)] = false := by decide
/-- `access_ranges_eqb` tells an address apart.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem access_ranges_eqb_tells_an_address_apart :
    access_ranges_eqb [(4096#64, 5)] [(8192#64, 5)] = false := by decide
/-- `access_ranges_eqb` tells an order apart.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem access_ranges_eqb_tells_an_order_apart :
    access_ranges_eqb [(4096#64, 5), (8192#64, 2)] [(8192#64, 2), (4096#64, 5)] = false := by decide
/-- `access_ranges_eqb` tells a tail apart.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem access_ranges_eqb_tells_a_tail_apart :
    access_ranges_eqb [(4096#64, 5), (8192#64, 2)] [(4096#64, 5), (8192#64, 3)] = false := by decide

/-- `access_ranges_eqb` tells a length apart.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem access_ranges_eqb_tells_a_length_apart :
    access_ranges_eqb [(4096#64, 5)] [] = false := by decide
/-- `access_ranges_eqb` admits equal ledgers.
model: a sample of an equality reflection; its `_eq` lemma in the twin is the specification -/
theorem access_ranges_eqb_admits_equal_lists :
    access_ranges_eqb [(4096#64, 5), (8192#64, 2)] [(4096#64, 5), (8192#64, 2)] = true := by decide

end Reflections

section Tactics

/-! ## The tactic macros, exercised

No kernel claim here either.  Each example is the goal shape a checker
proof hands the macro, so a macro whose Lean arms stopped matching the
Rocq ones would fail to build, here, rather than in the first checker
port that reaches for it. -/

/-- `srw`: rewrite, then re-reduce the beta-redex the rewrite exposed.
The second step is what the closing `rw` needs: `z + 1` is a subterm of
the goal only after the beta-reduction, so an `srw` that only rewrote
would leave `rw [hy]` nothing to find.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (x y z : Nat) (h : x = z) (hy : z + 1 = y) : (fun n => n + 1) x = y := by
  srw h
  rw [hy]

/-- `hrw … at h`: the same on a hypothesis.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (x y : Nat) (h : x = 3) (hx : (fun n => n + 1) x = y) : 3 + 1 = y := by
  hrw h at hx
  exact hx

/-- `srw` where the rewrite leaves nothing to re-reduce.  The `dsimp only`
is wrapped in `try` for exactly this case: Lean's `dsimp only` FAILS when
it changes nothing, where Rocq's `cbv beta iota zeta` merely does
nothing.  Drop the `try` and this example stops closing — which the
beta-redex example above cannot notice.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (x y : Nat) (h : x = y) (hy : y = 3) : x = 3 := by
  srw h
  exact hy

/-- The same no-op case for `hrw`, whose `try` is there for the same
reason.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (x y : Nat) (h : x = y) (hx : x = 3) : y = 3 := by
  hrw h at hx
  exact hx

/-- `hall`: everywhere at once.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (x y : Nat) (h : x = 3) (hx : (fun n => n + 1) x = y) : (fun n => n + 2) x = y + 1 := by
  hall h
  omega

/-- `bool_true`: a `bv_eqb` on equal words, an `Int` comparison a
hypothesis settles, and a boolean a hypothesis names, all at once.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (a b : Int) (x y : word) (c : Bool) (hab : a ≤ b) (hxy : x = y) (hc : c = true) :
    (bv_eqb x y && (if a ≤ b then c else false)) = true := by
  bool_true

/-- `bool_true` on a comparison a hypothesis settles: the `simp only [*]`
arm reads the hypothesis, so the `split` arm is never reached.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (a b : Int) (hab : a < b) : (if a < b then 1 else 2) = 1 := by
  bool_true

/-- `bool_true` on a comparison NO hypothesis settles but the context
implies: the `split` arm keeps the branch `omega` cannot refute and
closes the other.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (a b : Int) (hab : a + 1 ≤ b) : (if a < b then 1 else 2) = 1 := by
  bool_true

/-- `inv_ok`: an existential over a conjunction with an `Ok = Ok` inside,
taken apart down to the equations.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (x y : Nat) (m m' : Model) (e e' : List event)
    (h : ∃ n, n = x ∧ ((Ok n m e : outcome Nat) = Ok y m' e')) : x = y := by
  inv_ok

/-- `inv_ok` on an `Ok = Ok` whose components are not variables: the
component equations come out as hypotheses, as Rocq's `inversion` gives
them, and stay for the caller.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (f g : Nat → Nat) (x y : Nat) (m : Model) (e : List event)
    (h : ((Ok (f x) m e : outcome Nat) = Ok (g y) m e)) : f x = g y := by
  inv_ok
  assumption

/-- The `Some = Some` inversion.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (a b : Nat) (h : some a = some b) : a = b := by
  inv_ok

/-- The `CheckOk = CheckOk` inversion.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (m m' : Model) (evs evs' : List event) (h : CheckOk m evs = CheckOk m' evs') :
    evs = evs' := by
  inv_ok

/-- An `Option` constructor mismatch closes the goal.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (a : Nat) (h : some a = none) : 1 = 2 := by
  inv_ok

/-- `inv_ok` closes a goal whose hypotheses contradict.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (x : Nat) (m : Model) (e : List event)
    (h : ((Ok x m e : outcome Nat) = Unmodeled) ∨ False) : 1 = 2 := by
  inv_ok

/-- `sys_unfold`: a sugared spec, opened down to the primitives.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (h : ret_only (Z_to_bv 64 0) i m o) : o = Ok (mkEffect (Z_to_bv 64 0) [] []) m [] := by
  sys_unfold
  with_reducible exact h

/-- `sys_unfold` on a setter: `set_halted` opens through `modify` to
the post-model it builds.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (i : SyscallInput) (m : Model) (o : outcome Unit)
    (h : set_halted (Z_to_bv 64 3) i m o) : o = Ok () (with_halted (Z_to_bv 64 3) m) [] := by
  sys_unfold
  with_reducible exact h

/-- `sys_unfold` where nothing is DSL does nothing and does not fail,
as Rocq's `unfold … in *` does not.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (n : Nat) (h : n = 1) : n = 1 := by
  sys_unfold
  with_reducible exact h

/-! `sys_unfold`'s list is hand-written and nothing compares it to the
DSL: a name dropped from it, or an existing-but-wrong name, leaves
`simp -failIfUnchanged only` succeeding on the names it does have.  Each
example below is one more name the macro must open — every sugar and
every primitive — so that dropping any one of them fails here rather
than in the first checker proof to need it.

The closer is `with_reducible exact h`, not `exact h`, and the choice is
load-bearing: `exact` checks up to definitional equality at default
transparency, which unfolds `Monad.input` to `o = Ok i m []` by itself,
so a plain `exact h` closes whether or not `sys_unfold` opened the name
and the example tests nothing.  At reducible transparency the DSL's
definitions do not unfold, so the closer succeeds only when the
hypothesis already has the goal's shape — that is, only when the macro
did its work.  (`inv_ok` selects hypotheses by their syntactic head, so
the `bind` examples force their names without this.)

The `Monad.set_*` setters are not each exercised: they are all
`modify (with_* …)`, the pattern `set_halted` above shows, and a checker
proof that meets an unopened one sees `set_x` where it expected
`modify`, which is at least a failure at the right place. -/

/-- `err_ret`: sugar over `ret_only`, opened through it to the equation.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
    (h : err_ret EINVAL i m o) : o = Ok (mkEffect (errno_ret EINVAL) [] []) m [] := by
  sys_unfold
  with_reducible exact h

/-- `errno_from`: sugar over `choose`, opened to the existential.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (es : List Int) (i : SyscallInput) (m : Model) (o : outcome Int)
    (h : errno_from es i m o) : ∃ e, e ∈ es ∧ o = Ok e m [] := by
  sys_unfold
  with_reducible exact h

/-- `lowest_fd`: sugar over `choose` in `Sys/Fs/File.lean`, opened to
the existential over the free descriptor `alloc_fd` names.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (fds : List (word × FdEntry)) (i : SyscallInput) (m : Model) (o : outcome word)
    (h : Sys.Fs.File.lowest_fd fds i m o) :
    ∃ fd, (fd_lookup fds fd = none ∧ fd = alloc_fd fds) ∧ o = Ok fd m [] := by
  sys_unfold
  with_reducible exact h

/-- `set_urandom`: the setter #712 added, opened through `modify`.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (s : InputStream) (i : SyscallInput) (m : Model) (o : outcome Unit)
    (h : set_urandom s i m o) : o = Ok () (with_urandom s m) [] := by
  sys_unfold
  with_reducible exact h

/-- `set_sigmask_deliver`: the `Sys/Kernel/Signal.lean` sugar over `modify`,
opened to the post-model `sigmask_deliver_model` builds.  The last of
Rocq's `sys_unfold` entries to land; without it the macro was narrower
than its twin and this example does not close.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (new : word) (i : SyscallInput) (m : Model) (o : outcome Unit)
    (h : Sys.Kernel.Signal.set_sigmask_deliver new i m o) :
    o = Ok () (Sys.Kernel.Signal.sigmask_deliver_model new m) [] := by
  sys_unfold
  with_reducible exact h

/-- `record_copyins` over a `ret_only` body: `bind` and both `pure`s open,
`inv_ok` takes the shape apart, and the events are the two empty lists
appended.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (r : word) (i : SyscallInput) (m m' : Model) (eff : SyscallEffect) (evs : List event)
    (h : record_copyins [(4096#64, 5)] (ret_only r) i m (Ok eff m' evs)) : evs.length = 0 := by
  sys_unfold
  inv_ok
  rfl

/-- `choose`, on an arbitrary predicate.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (P : Int → Prop) (i : SyscallInput) (m : Model) (o : outcome Int)
    (h : Monad.choose P i m o) : ∃ x, P x ∧ o = Ok x m [] := by
  sys_unfold
  with_reducible exact h

/-- `alt`, on two arbitrary computations.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (c1 c2 : Sys Nat) (i : SyscallInput) (m : Model) (o : outcome Nat)
    (h : Monad.alt c1 c2 i m o) : c1 i m o ∨ c2 i m o := by
  sys_unfold
  with_reducible exact h

/-- `unmodeled`.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (i : SyscallInput) (m : Model) (o : outcome Unit)
    (h : (Monad.unmodeled : Sys Unit) i m o) : o = Unmodeled := by
  sys_unfold
  with_reducible exact h

/-- `emit`.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (evs : List event) (i : SyscallInput) (m : Model) (o : outcome Unit)
    (h : Monad.emit evs i m o) : o = Ok () m evs := by
  sys_unfold
  with_reducible exact h

/-- `input`.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (i : SyscallInput) (m : Model) (o : outcome SyscallInput)
    (h : Monad.input i m o) : o = Ok i m [] := by
  sys_unfold
  with_reducible exact h

/-- `sysno`.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (i : SyscallInput) (m : Model) (o : outcome word)
    (h : Monad.sysno i m o) : o = Ok i.in_sysno m [] := by
  sys_unfold
  with_reducible exact h

/-- `arg`.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (i : SyscallInput) (m : Model) (o : outcome word)
    (h : Monad.arg 1 i m o) : o = Ok (in_arg i 1) m [] := by
  sys_unfold
  with_reducible exact h

/-- `get_fds`.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (i : SyscallInput) (m : Model) (o : outcome (List (word × FdEntry)))
    (h : Monad.get_fds i m o) : o = Ok (m_fds m) m [] := by
  sys_unfold
  with_reducible exact h

/-- `get_vmmaps`.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (i : SyscallInput) (m : Model) (o : outcome VmMaps)
    (h : Monad.get_vmmaps i m o) : o = Ok (m_vmmaps m) m [] := by
  sys_unfold
  with_reducible exact h

/-- `sys_unfold` on a bound reader, then `inv_ok`: `bind` and `get_model`
both open, the existential and its equations are taken apart, and what
is left is the events, which a checker proof reads off.  The outcome is
stated in its `Ok` shape, as a Rocq caller `destruct`s it first: on a
variable outcome `sys_unfold` leaves `bind`'s `match`, which `inv_ok`
does not split.
model: exercises a tactic macro on a checker proof's goal shape; no kernel claim -/
example (i : SyscallInput) (m m' m'' : Model) (evs : List event)
    (h : (bind get_model (fun m0 => Monad.pure m0)) i m (Ok m' m'' evs)) : evs.length = 0 := by
  sys_unfold
  inv_ok
  rfl

end Tactics

section K1WriteSourceAndGather

/-! ## Ticket K1: `write_source_prefix`, `gather_prefix_full`, `gather_iovecs_length`

Appended as one delimited section before the file's closing `end`, the
anchor BRIEF §4 retires: a second ticket appending here asks for a
sentinel line first, since two insertions before the same `end` are one
hunk to git.  The three lemmas waited on
`Uaccess.write_source`, `State.rw_count_clamp`, `State.gather_iovecs`,
`State.gather_prefix` and `State.iovs_total`, which landed after #766;
the pins read each off against the kernel step it mirrors.  `vfs_write`
clamps `count` to `MAX_RW_COUNT` before the copy — `if (count >
MAX_RW_COUNT) count = MAX_RW_COUNT;` (fs/read_write.c, v6.18.46), the
macro being `INT_MAX & PAGE_MASK` (include/linux/fs.h, v6.18.46), which
is 0x7ffff000 on a 4 KiB page — and a `writev` consumes its iovec array
front to back, each segment contributing the `iov_len` `__import_iovec`
left it after its in-place `MAX_RW_COUNT` cap (lib/iov_iter.c, v6.18.46)
before the next is touched (`iterate_iovec`, include/linux/iov_iter.h,
v6.18.46). -/

open LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess (write_source)

/-- The clamp: a write of 2^31 bytes from a buffer that reads whole is
sourced from its first 0x7ffff000 bytes and no more.  A modeled write
does reach this count: the channel and file arms of `write_spec`
(theories/LinuxProcessSem/Sys/Fs/ReadWrite.v) gate on
`Uaccess.modeled_rw_range`, which admits any count whose range
`State.access_okb` accepts — `modeled_rw_range_admits_any_count_in_range`
in `Checks/Cases/Uaccess.lean` pins 2^31 at 0x10000 — and then hand the
named count to `write_source`, so this is the most such a write can
move, the value `vfs_write` clamps to.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_source_prefix_clamps_at_max_rw_count (mp : word → Option byte) (a : word)
    (w : List byte) (hw : read_bytes_map mp a (Z_to_bv 64 (2 ^ 31)) = some w) :
    write_source mp a (Z_to_bv 64 (2 ^ 31)) = w.take 0x7ffff000 := by
  rw [write_source_prefix mp a _ w hw]
  have hc : (rw_count_clamp (Z_to_bv 64 (2 ^ 31))).toNat = 0x7ffff000 := by decide
  rw [hc]

/-- Below the clamp the source is the whole read: 3 bytes asked, 3 read,
3 written.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_source_prefix_below_the_clamp_is_the_whole_read (mp : word → Option byte)
    (a : word) (w : List byte) (hw : read_bytes_map mp a (Z_to_bv 64 3) = some w) :
    write_source mp a (Z_to_bv 64 3) = w := by
  rw [write_source_prefix mp a _ w hw]
  have hl := read_bytes_map_length mp a _ w hw
  have h3 : bv_unsigned (Z_to_bv 64 3) = 3 := by decide
  have hc : (rw_count_clamp (Z_to_bv 64 3)).toNat = 3 := by decide
  apply List.take_of_length_le
  omega

/-- Exactly at the clamp nothing is dropped: `MAX_RW_COUNT` itself is
admitted whole, the strict `>` in `vfs_write`'s test.
kernel: fs/read_write.c:vfs_write@v6.18.46 -/
theorem write_source_prefix_at_the_clamp_is_the_whole_read (mp : word → Option byte)
    (a : word) (w : List byte) (hw : read_bytes_map mp a (Z_to_bv 64 0x7ffff000) = some w) :
    write_source mp a (Z_to_bv 64 0x7ffff000) = w := by
  rw [write_source_prefix mp a _ w hw]
  have hl := read_bytes_map_length mp a _ w hw
  have h3 : bv_unsigned (Z_to_bv 64 0x7ffff000) = 0x7ffff000 := by decide
  have hc : (rw_count_clamp (Z_to_bv 64 0x7ffff000)).toNat = 0x7ffff000 := by decide
  apply List.take_of_length_le
  omega

/-- Two segments that both read whole gather to their concatenation, in
iovec order.
kernel: include/linux/iov_iter.h:iterate_iovec@v6.18.46 -/
theorem gather_prefix_full_two_segments (mp : word → Option byte) (b0 b1 l0 l1 : word)
    (w0 w1 : List byte) (h0 : read_bytes_map mp b0 l0 = some w0)
    (h1 : read_bytes_map mp b1 l1 = some w1) :
    gather_prefix mp [(b0, l0), (b1, l1)] = w0 ++ w1 := by
  apply gather_prefix_full
  simp only [gather_iovecs, h0, h1, List.append_nil]

/-- ... and to the requested total, which is the sum of the two
`iov_len`s AS `__import_iovec` HANDS THEM ON: it caps each `iov_len` in
place at `MAX_RW_COUNT - total_len` before `iterate_iovec` sees any, so
the lengths here are those of the capped vector — `State.cap_iovecs`,
which `writev_gathered` applies first — and over that vector each
segment contributes exactly its own and no segment is dropped.  Stated
over raw `l0`, `l1` the lemma is a model fact alone: at (0x7ffff000, 1)
the kernel moves 0x7ffff000 and never sees the pair.
kernel: include/linux/iov_iter.h:iterate_iovec; lib/iov_iter.c:__import_iovec@v6.18.46 -/
theorem gather_iovecs_length_two_segments (mp : word → Option byte) (b0 b1 l0 l1 : word)
    (w0 w1 : List byte) (h0 : read_bytes_map mp b0 l0 = some w0)
    (h1 : read_bytes_map mp b1 l1 = some w1) :
    ((w0 ++ w1).length : Int) = iovs_total [(b0, l0), (b1, l1)]
      ∧ iovs_total [(b0, l0), (b1, l1)] = bv_unsigned l0 + bv_unsigned l1 :=
  ⟨gather_iovecs_length mp [(b0, l0), (b1, l1)] (w0 ++ w1)
      (by simp only [gather_iovecs, h0, h1, List.append_nil]),
   by simp only [iovs_total, Int.add_zero]⟩

/-- The empty array gathers to nothing of length 0.  This is the one
shape `iterate_iovec` never sees: with `iovcnt = 0`, `iovec_from_user`
returns before it reads the array (lib/iov_iter.c, v6.18.46 — "Linux
has traditionally returned zero for zero segments"), and `vfs_writev`
answers 0 on the zero total before any `write_iter` (fs/read_write.c,
v6.18.46).
kernel: lib/iov_iter.c:iovec_from_user; fs/read_write.c:vfs_writev@v6.18.46 -/
theorem gather_prefix_full_empty (mp : word → Option byte) :
    gather_prefix mp [] = [] ∧ (([] : List byte).length : Int) = iovs_total [] :=
  ⟨gather_prefix_full mp [] [] rfl, gather_iovecs_length mp [] [] rfl⟩

/-- A segment that does not read has no gather, so neither lemma's
hypothesis holds of it.
model: `gather_iovecs` is `none` at the first unreadable segment; the two lemmas are stated over the `some` case alone -/
theorem gather_iovecs_none_on_an_unreadable_segment (b : word) :
    gather_iovecs (fun _ => none) [(b, Z_to_bv 64 1)] = none := by
  simp only [gather_iovecs]
  rw [read_bytes_map_eq]
  rfl

/-- ... and the hypotheses are load-bearing: on that segment
`gather_iovecs_length`'s conclusion is FALSE — the prefix gathered is
empty, the requested total is 1 — which is the kernel's short write,
`iterate_iovec` stopping where `skip < p->iov_len` still holds.
kernel: include/linux/iov_iter.h:iterate_iovec@v6.18.46 -/
theorem gather_prefix_short_on_an_unreadable_segment (b : word) :
    ((gather_prefix (fun _ => none) [(b, Z_to_bv 64 1)]).length : Int)
      ≠ iovs_total [(b, Z_to_bv 64 1)] := by
  have h : readable_bytes (fun _ => none) b (Z_to_bv 64 1) = [] := by
    rw [readable_bytes_eq]; rfl
  simp only [gather_prefix, iovs_total, h]
  decide

end K1WriteSourceAndGather

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Checks.Sys.Prelude
