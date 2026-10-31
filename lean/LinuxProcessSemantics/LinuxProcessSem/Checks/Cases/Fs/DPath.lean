import LinuxProcessSemantics.LinuxProcessSem.Specs
import LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Tactic

/-! # Checks.Cases.Fs.DPath — what `getcwd` admits, read off against Linux

Pins over `Sys.Fs.DPath.getcwd_spec`.  Rocq keeps no worked-cases file for
this arm under `theories/LinuxProcessSem/Checks/Cases/` (its checks are the
probe `testing/syscall-check/tests/getcwd_spec.c`, the checker proofs of
`theories/LinuxProcessSem/Checks/Sys/Fs/DPath.v` and the progress witness
of `theories/LinuxProcessSem/Checks/Witness/Fs/DPath.v`), so this file
mirrors no Rocq source.  Not part of the trusted specification: this file is QA on the
definitions, written to be READ, and every claim in it is a claim about what
the kernel does, with the citation beside it.

Every line of `SYSCALL_DEFINE2(getcwd)` cited below is fs/d_path.c at Linux
v6.18.46 (commit 1f99e9ab748f), read at that version; the line numbers are
that file's.  The body runs, in order:

    416  page = __getname();            419  return -ENOMEM
    424  d_unlinked(pwd.dentry)         426  error = -ENOENT
    429  DECLARE_BUFFER(b, page, PATH_MAX)
    431  prepend_char(&b, 0)            432  prepend_path(&pwd, &root, &b)
    436  len = PATH_MAX - b.len
    437  len > PATH_MAX                 438  error = -ENAMETOOLONG
    439  len > size                     440  error = -ERANGE
    441  copy_to_user(buf, b.buf, len)  442  error = -EFAULT
    444  error = len
    446  __putname(page)                447  return error

`__getname` and `__putname` are the `names_cachep` macros of
include/linux/fs.h (Linux v6.18.46); `d_unlinked` is include/linux/dcache.h's
(same version); `PATH_MAX` is 4096 (include/uapi/linux/limits.h:13, same
version).

Each check is stated on the relation itself, as `Checks.Cases.Mm.Mmap`
explains: the positive shape is an `iff` over EVERY outcome, which fixes
what is admitted and what is refused in one statement, and the negative
shape is the refutation of one concrete lie a kernel could tell.  All are
closed by `sys_norm`/`sys_refute` (`Checks.Cases.Tactic`).

The spec's unfolding equations are registered for `sys_simp` here rather
than in `Checks/Cases/Tactic.lean`'s register, which this port does not
edit; the attribute is global either way, and the register's own
completeness check covers `State` and `Monad` alone. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.DPath

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad
open LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
open LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.DPath
open LinuxProcessSemantics.LinuxProcessSem.Specs

attribute [sys_simp low] getcwd_spec.eq_1 getcwd_errnos.eq_1

/-! ## The injectable set

`getcwd_errnos` is the three failures decided before the size comparison
(lines 416-438); what it must NOT contain is every answer decided after it
or never at all. -/

/-- `-EFAULT` (line 442) is decided AFTER `len > size` (line 439), so it
is not injectable in the band the spec models; `-EINVAL` is glibc's answer
for a zero size and appears nowhere in the syscall body (lines 412-448);
`-EACCES` would need a permission check the body and its callees —
`get_fs_root_and_pwd_rcu`, `d_unlinked`, `prepend_path`, `copy_to_user`,
`__putname` — do not make: no `inode_permission` (fs/namei.c) and no LSM
hook is reached from `SYSCALL_DEFINE2(getcwd)`.  `-ERANGE` is outside the
list for a different reason: it is the fall-through at line 440, decided
after everything the list stands for, and the spec answers it on its own
arm rather than as an injected failure.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem late_and_foreign_errnos_not_injectable :
    ¬ (EFAULT ∈ getcwd_errnos ∨ EINVAL ∈ getcwd_errnos ∨ EACCES ∈ getcwd_errnos
       ∨ ERANGE ∈ getcwd_errnos) := by decide

/-! ## The size gate: `len > size` at line 439, decided without a working directory

The kernel's `len` is at least 2 on every path that reaches line 439:
`DECLARE_BUFFER` (line 429) starts `b.len` at `PATH_MAX`, `prepend_char(&b, 0)`
(line 431; `prepend_char`, lines 26-35) spends one byte on the NUL, and
`prepend_path` (lines 156-197) either drives `b.len` to -1 — which line 437
catches as `-ENAMETOOLONG` before the size test — or spends at least one
more byte, since its tail (lines 192-193) prepends a "/" whenever nothing
else was prepended.  So `len ≥ 2`, and with `size` of 0 or 1 the comparison at
line 439 is true for EVERY working directory. -/

/-- `size = 0`: `-ERANGE`, or one of the three earlier failures, and
nothing else — no success, no `-EFAULT`, no decline.  The outcome set
below is the whole of what `getcwd(buf, 0)` can answer at lines 419, 426,
438 and 440, each a bare return that writes nothing (the one
`copy_to_user`, line 441, is never reached).  On Linux.  Stated over
every `i`, so over every buffer, and qemu-user under `-R` answers -EFAULT
for a `buf` above `reserved_va` at size 0 (`access_ok_untagged`,
linux-user/qemu.h:187-195, QEMU 11.1.1), which this `iff` refuses:
bugs/getcwd-erange-band-admits-linux-alone.md, shape 2.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem getcwd_size0_iff (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    getcwd_spec 0 i m o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) m []
        ∨ o = Ok (mkEffect (errno_ret ENOENT) [] []) m []
        ∨ o = Ok (mkEffect (errno_ret ENAMETOOLONG) [] []) m [])
       ∨ o = Ok (mkEffect (errno_ret ERANGE) [] []) m []) := by
  sys_norm

/-- `size = 1`: the same set.  One byte holds the NUL but never the "/"
lines 192-193 charge on top of it, so `len > 1` at line 439 whatever the
working directory.  On Linux: qemu-user answers -EFAULT at size 1 for a
`buf` that is not guest memory (`lock_user`, linux-user/uaccess.c:8-25,
QEMU 11.1.1, before the host call), which this `iff`, stated over every
buffer, refuses: bugs/getcwd-erange-band-admits-linux-alone.md, shape 1.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem getcwd_size1_iff (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    getcwd_spec 1 i m o ↔
      ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) m []
        ∨ o = Ok (mkEffect (errno_ret ENOENT) [] []) m []
        ∨ o = Ok (mkEffect (errno_ret ENAMETOOLONG) [] []) m [])
       ∨ o = Ok (mkEffect (errno_ret ERANGE) [] []) m []) := by
  sys_norm

/-- `getcwd(buf, 1)` is `-ERANGE` (line 440), and the answer leaves the
model and the event stream alone.
probe: testing/syscall-check/tests/getcwd_spec.c#conform -- range -/
theorem getcwd_size1_erange_admitted (i : SyscallInput) (m : Model) :
    getcwd_spec 1 i m (Ok (mkEffect (errno_ret ERANGE) [] []) m []) := by
  sys_norm

/-- Each of the three failures decided before line 439 is admitted at
size 0: `-ENOMEM` when `__getname()` fails (line 419), `-ENOENT` when the
working directory was unlinked (line 426), `-ENAMETOOLONG` when the path
overflowed the page (line 438).
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem getcwd_size0_injected_admitted (i : SyscallInput) (m : Model) :
    getcwd_spec 0 i m (Ok (mkEffect (errno_ret ENOMEM) [] []) m [])
    ∧ getcwd_spec 0 i m (Ok (mkEffect (errno_ret ENOENT) [] []) m [])
    ∧ getcwd_spec 0 i m (Ok (mkEffect (errno_ret ENAMETOOLONG) [] []) m []) := by
  refine ⟨?_, ?_, ?_⟩ <;> sys_norm

/-- The size gate is not a decline: a kernel is never allowed to leave the
band unanswered at size 1, since lines 419-440 give it four answers and
nothing reaches line 441.
trace: getcwd_spec/001 -/
theorem getcwd_size1_never_unmodeled (i : SyscallInput) (m : Model) :
    ¬ getcwd_spec 1 i m Unmodeled := by
  sys_refute

/-! ## What the band refuses

Each refutation is one concrete answer a lying kernel could give at
`size ≤ 1` that the body of `SYSCALL_DEFINE2(getcwd)` cannot produce. -/

/-- `-EFAULT` is unreachable at size 0 ON LINUX: line 441's `copy_to_user`
sits behind line 439, and nothing before it — no `access_ok`, no probe of
`buf` — can fault.  The probe's mutation forges it on a real, writable
buffer, where no supported implementation answers it.  But `buf` is not
an argument of `getcwd_spec`, so this statement refuses -EFAULT for EVERY
buffer at size 0, and qemu-user answers -EFAULT for two of them.  A `buf`
above `reserved_va` under `-R` fails `access_ok_untagged`
(linux-user/qemu.h:187-195, QEMU 11.1.1) by design, and refusing that is
Linux's answer proved certain where a supported implementation gives
another.  NULL when `guest_base` is 0 passes the check, and `lock_user`
(linux-user/uaccess.c:8-25) hands back host address 0, which the `!p`
test of `TARGET_NR_getcwd` (linux-user/syscall.c:12285-12286, QEMU 11.1.1)
misreads as a failed lock — a defect QEMU's own source calls one (its
`read`, `write`, `pread64` and `pwrite64` skip the lock for a NULL buffer
of zero length, "which should succeed", linux-user/syscall.c:12255, QEMU
11.1.1), so the model does not owe it.  bugs/getcwd-erange-band-admits-linux-alone.md has both, as
shapes 2 and 3.
probe: testing/syscall-check/tests/getcwd_spec.c#reject --mutate getcwd:ret=-EFAULT -- range -/
theorem getcwd_size0_efault_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ getcwd_spec 0 i m (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- `-EINVAL` is what glibc's wrapper (sysdeps/unix/sysv/linux/getcwd.c,
not pinned to a version: nothing rests on it) answers for a zero size
before issuing the call; syscall 17's body (lines 412-448) has no
`-EINVAL` arm.
probe: testing/syscall-check/tests/getcwd_spec.c#reject --mutate getcwd:ret=-EINVAL -- range -/
theorem getcwd_size0_einval_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ getcwd_spec 0 i m (Ok (mkEffect (errno_ret EINVAL) [] []) m' evs) := by
  sys_refute

/-- `-EACCES`: getcwd consults no permission and no LSM hook between
lines 412 and 448 (the callee list above the injectable set).
probe: testing/syscall-check/tests/getcwd_spec.c#reject --mutate getcwd:ret=-EACCES -- range -/
theorem getcwd_size0_eacces_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ getcwd_spec 0 i m (Ok (mkEffect (errno_ret EACCES) [] []) m' evs) := by
  sys_refute

/-- A success of 2 — the length of "/" with its NUL, the shortest string
line 444 can ever return — is refused at size 1: `2 > 1` at line 439.
No probe mutation sits on the size-1 call with this value (the `ret=2`
case below is the size-0 call's), so the kernel line is the evidence.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem getcwd_size1_success_two_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ getcwd_spec 1 i m (Ok (mkEffect 2 [] []) m' evs) := by
  sys_refute

/-- The same lie on the probe's registers: the `ret=2` mutation rewrites
the FIRST `getcwd` of `range`, which is `getcwd(buf, 0)`, and `2 > 0` at
line 439 refuses it there too.
probe: testing/syscall-check/tests/getcwd_spec.c#reject --mutate getcwd:ret=2 -- range -/
theorem getcwd_size0_success_two_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ getcwd_spec 0 i m (Ok (mkEffect 2 [] []) m' evs) := by
  sys_refute

/-- A success of 0 is not a legal `getcwd` return at ANY size — `len`
counts the NUL (line 431), so line 444 never returns less than 2 — and
it is the value an acceptor that forgot the comparison would most
plausibly let through.
probe: testing/syscall-check/tests/getcwd_spec.c#reject --mutate getcwd:ret=0 -- range -/
theorem getcwd_size0_success_zero_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ getcwd_spec 0 i m (Ok (mkEffect 0 [] []) m' evs) := by
  sys_refute

/-- `-ERANGE` writes nothing: line 440 is taken INSTEAD of line 441's
`copy_to_user`, so a kernel that reports the errno and a byte landed in
`buf` is refused on the write ledger — WHATEVER the byte.  The harness's
`smuggle-write` forges 0x41 (`testing/syscall-check/main.ml`); the byte is
symbolic here so that the refusal is of the entry, not of one value.
probe: testing/syscall-check/tests/getcwd_spec.c#reject --mutate getcwd:smuggle-write:a0:1 -- range -/
theorem getcwd_erange_with_write_rejected (buf : word) (b : byte) (i : SyscallInput) (m m' : Model)
    (evs : List event) :
    ¬ getcwd_spec 0 i m
        (Ok (SyscallEffect.mkEffectU (errno_ret ERANGE) [(buf, [b])] [] [] [] []) m' evs) := by
  sys_refute

/-- …and it zero-fills nothing either: the whole path is built into a
kernel page (line 429) and no user byte is touched before line 441.
Stated at size 1, which no probe mutation reaches with this lie.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem getcwd_erange_with_zeros_rejected (buf : word) (i : SyscallInput) (m m' : Model)
    (evs : List event) :
    ¬ getcwd_spec 1 i m (Ok (mkEffect (errno_ret ERANGE) [] [(buf, 1)]) m' evs) := by
  sys_refute

/-- The zero-fill lie on the probe's registers: `smuggle-zeros` rewrites
the first `getcwd` of `range`, the size-0 call.
probe: testing/syscall-check/tests/getcwd_spec.c#reject --mutate getcwd:smuggle-zeros:a0:1 -- range -/
theorem getcwd_size0_erange_with_zeros_rejected (buf : word) (i : SyscallInput) (m m' : Model)
    (evs : List event) :
    ¬ getcwd_spec 0 i m (Ok (mkEffect (errno_ret ERANGE) [] [(buf, 1)]) m' evs) := by
  sys_refute

/-- `buf` is a destination only: nothing between lines 412 and 441 reads
user memory, and line 441 is not reached in the band, so a kernel that
claimed to have read a byte of `buf` is refused on the copy-in ledger.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem getcwd_erange_with_copyin_rejected (buf : word) (i : SyscallInput) (m m' : Model)
    (evs : List event) :
    ¬ getcwd_spec 0 i m
        (Ok (SyscallEffect.mkEffectU (errno_ret ERANGE) [] [] [] [] [(buf, 1)]) m' evs) := by
  sys_refute

/-- …and it unmaps nothing: the page is a KERNEL page (line 429), freed
by `__putname` (include/linux/fs.h) at line 446; no user mapping is
touched.
kernel: fs/d_path.c:getcwd; include/linux/fs.h:__putname@v6.18.46 -/
theorem getcwd_erange_with_unmap_rejected (buf : word) (i : SyscallInput) (m m' : Model)
    (evs : List event) :
    ¬ getcwd_spec 1 i m
        (Ok (SyscallEffect.mkEffectU (errno_ret ERANGE) [] [] [(buf, 4096)] [] []) m' evs) := by
  sys_refute

/-- No success at all in the band, whatever the return and whatever the
five ledgers claim beside it: line 444 is reached only when line 439 is
false, and `len ≥ 2 > size` for every working directory when `size ≤ 1`.
The kernel's success return is `len`, an `unsigned` (line 428) bounded by
`PATH_MAX` at line 437, so the hypothesis names every value line 444 can
hand back and the four admitted errnos, all in the top 4095 of the word,
lie outside it.
probe: testing/syscall-check/tests/getcwd_spec.c#reject --mutate getcwd#2:ret=0 -- range -/
theorem getcwd_size1_no_success (r : word) (i : SyscallInput) (m m' : Model)
    (ws : List (word × List byte)) (zs : List (word × word)) (us : List (word × word))
    (cs : List MemCopy) (ins : List (word × Nat)) (evs : List event)
    (hr : bv_unsigned r ≤ 4096) :
    ¬ getcwd_spec 1 i m (Ok (SyscallEffect.mkEffectU r ws zs us cs ins) m' evs) := by
  sys_norm
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (rintro rfl; exact absurd hr (by decide))

/-- A bare return emits no event: `SYSCALL_DEFINE2(getcwd)` (lines
412-448) opens no file, touches no `struct file` and writes no stream;
its only user contact is line 441's `copy_to_user`, which the band never
reaches.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem getcwd_erange_with_event_rejected (i : SyscallInput) (m m' : Model) :
    ¬ getcwd_spec 0 i m (Ok (mkEffect (errno_ret ERANGE) [] []) m' [WriteEv 1 (Z_to_bv 8 65)]) := by
  sys_refute

/-- The model is left exactly as it was: lines 412-448 change no process
state (`__putname`, include/linux/fs.h, at line 446 frees the page the
call itself took at line 416), so
an `-ERANGE` reported against any OTHER model is refused.  Nothing
decides this for the tactic, so the check states the difference as a
hypothesis and reads the surviving conjunct.
kernel: fs/d_path.c:getcwd; include/linux/fs.h:__putname@v6.18.46 -/
theorem getcwd_erange_model_changed_rejected (i : SyscallInput) (m m' : Model)
    (hm : m' ≠ m) :
    ¬ getcwd_spec 0 i m (Ok (mkEffect (errno_ret ERANGE) [] []) m' []) := by
  sys_norm
  intro h
  exact hm h

/-! ## Above the band: the working directory decides, and the model has none

At `size ≥ 2` line 439 can go either way — a working directory of "/"
has `len = 2` and succeeds at line 444, a deeper one fails at line 440 —
and the success carries the directory's own path through line 441.
`State.Model` has no pwd and `Fs` no directories, so no supported
implementation's answer here is a function of any modeled state, and the
sound answer is `Unmodeled`: not because the implementations disagree,
but because the model cannot name what every one of them returns. -/

/-- `size = 2`, the first size outside the band: declined outright.
Neither `-ERANGE` nor a success is admitted, because both are reachable
and which one depends on the working directory.
probe: testing/syscall-check/tests/getcwd_spec.c#fail-closed --expect-unmodeled getcwd -- size2 -/
theorem getcwd_size2_unmodeled_iff (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    getcwd_spec 2 i m o ↔ o = Unmodeled := by
  sys_norm

/-- `size = PATH_MAX` (4096, include/uapi/linux/limits.h:13): a buffer
every path fits (line 437 bounds `len` by `PATH_MAX`), so the answer is
the working directory itself — declined.
kernel: fs/d_path.c:getcwd; include/uapi/linux/limits.h:PATH_MAX@v6.18.46 -/
theorem getcwd_size_path_max_unmodeled_iff (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    getcwd_spec 4096 i m o ↔ o = Unmodeled := by
  sys_norm

/-- `size` is `unsigned long` (line 412), so a register holding -1 is
2^64 - 1, a size every path fits, and not an invalid argument: the answer
is again the working directory, declined.  A model that read the size as
signed would put this call in the band.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem getcwd_size_minus_one_unmodeled_iff (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) :
    getcwd_spec (Z_to_bv 64 (-1)) i m o ↔ o = Unmodeled := by
  sys_norm

/-- The lie the decline exists to refuse: `-ERANGE` at size 2.  A working
directory of "/" has `len = 2`, line 439 is false, and the kernel copies
"/" out and returns 2 — so `-ERANGE` is not the answer for every working
directory, and the model, which cannot tell which it has, admits it for
none.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem getcwd_size2_erange_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ getcwd_spec 2 i m (Ok (mkEffect (errno_ret ERANGE) [] []) m' evs) := by
  sys_refute

/-- …and the matching success of 2 is refused too, for the mirror reason:
a deeper working directory answers `-ERANGE` at the same size.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem getcwd_size2_success_rejected (i : SyscallInput) (m m' : Model) (evs : List event) :
    ¬ getcwd_spec 2 i m (Ok (mkEffect 2 [] []) m' evs) := by
  sys_refute

/-! ## Through the dispatcher: `buf` is a0 and is not read

`SYSCALL_DEFINE2(getcwd, char __user *, buf, unsigned long, size)` (line
412): `size` is a1, and the table hands `getcwd_spec` a1 alone.  These
pins fix that a0 changes nothing — the same outcome set for a NULL buffer
and for a garbage pointer, both in a process whose memory maps nothing —
which is what lines 412-440 say: nothing reads `buf` before line 441.
That no memory is read at all is already the spec-level pins' statement,
whose `i` is symbolic and so carries any memory; the inputs here are
fully concrete because `sys_norm` evaluates the table's `in_arg` only on
a closed input. -/

/-- `getcwd(NULL, 0)` from a process whose memory maps nothing at all is
`-ERANGE` (line 440) or an earlier injected failure; never `-EFAULT`, since
line 441 is not reached.  This is the input the probe's third `getcwd`
issues (`testing/syscall-check/tests/getcwd_spec.c`), and qemu-user is the
supported implementation that can differ on it: when `guest_base` is 0,
`lock_user` (linux-user/uaccess.c:8-25, QEMU 11.1.1) hands back host
address 0 for guest address 0 and `TARGET_NR_getcwd`
(linux-user/syscall.c:12285-12286) reads that as a failed lock and answers
-EFAULT.  That is not a behavior this `iff` owes.  The access check
passes; QEMU skips the lock for a NULL buffer of zero length in `read`,
`write`, `pread64` and `pwrite64` ("Special-case NULL buffer and zero
length, which should succeed", linux-user/syscall.c:12255, QEMU 11.1.1);
an implementation contradicting its own source is a bug under AGENTS.md, and
a bug is not a real behavior.  With `guest_base` non-zero qemu-user
answers -ERANGE like Linux, so -ERANGE is inside the intersection here and
nothing outside it is proved.  The tree's stance — every emulator verdict
rederived against the kernel (testing/syscall-check/README.md), kept as
the probe's `getcwd#3:ret=-EFAULT` reject case — is right at this input;
bugs/getcwd-erange-band-admits-linux-alone.md records the shape (its
third) beside the two the band does get wrong.
trace: getcwd_spec/001 -/
theorem sysno_17_null_buf_size0_iff (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 17 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m o
      ↔ ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) m []
          ∨ o = Ok (mkEffect (errno_ret ENOENT) [] []) m []
          ∨ o = Ok (mkEffect (errno_ret ENAMETOOLONG) [] []) m [])
         ∨ o = Ok (mkEffect (errno_ret ERANGE) [] []) m []) := by
  sys_norm

/-- `getcwd((char *)0xdeadbeef, 1)` with nothing mapped there: the same
set.  Linux neither validates nor dereferences the pointer before line
441.  No probe reaches this shape — the probe's `-EFAULT` mutations sit on
a real buffer at size 0 and on the NULL call above — so the pin is what
holds it — and here qemu-user's other answer IS owed, unlike the
NULL-buffer pin's: `lock_user(VERIFY_WRITE, 0xdeadbeef, 1, 0)` fails
`access_ok_untagged` on an unmapped page (linux-user/qemu.h:187-195,
QEMU 11.1.1) whatever `guest_base` is, the design of every non-empty lock
and no defect, so qemu-user answers -EFAULT where this `iff` admits
-ERANGE alone: Linux's answer proved certain where the intersection is
empty, bugs/getcwd-erange-band-admits-linux-alone.md, shape 1.
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem sysno_17_garbage_buf_size1_iff (m : Model) (o : outcome SyscallEffect) :
    syscall_spec (SyscallInput.mkInput 17 [0xdeadbeef, 1, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m o
      ↔ ((o = Ok (mkEffect (errno_ret ENOMEM) [] []) m []
          ∨ o = Ok (mkEffect (errno_ret ENOENT) [] []) m []
          ∨ o = Ok (mkEffect (errno_ret ENAMETOOLONG) [] []) m [])
         ∨ o = Ok (mkEffect (errno_ret ERANGE) [] []) m []) := by
  sys_norm

/-- `getcwd(NULL, 0)` is not `-EFAULT` on Linux: a kernel that probed the
pointer first (the shape the probe's `getcwd#3:ret=-EFAULT` mutation
forges, and the answer qemu-user really gives when `guest_base` is 0, by
a defect its own source calls one — shape 3 of
bugs/getcwd-erange-band-admits-linux-alone.md, which the model does not
owe) is refused through the table as well as on the spec.
probe: testing/syscall-check/tests/getcwd_spec.c#reject --mutate getcwd#3:ret=-EFAULT -- range -/
theorem sysno_17_null_buf_efault_rejected (m m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 17 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m
        (Ok (mkEffect (errno_ret EFAULT) [] []) m' evs) := by
  sys_refute

/-- `size` is `unsigned long` (line 412), 64 bits on riscv64.  A size
whose low 32 bits are zero is still enormous, so line 439 is false for a
short working directory and `-ERANGE` is not its answer; a model that
truncated a1 to 32 bits would read this call as size 0 and allow
`-ERANGE` for it.  (`getcwd_size_minus_one_unmodeled_iff` cannot tell:
the low 32 bits of -1 are all ones too.)
kernel: fs/d_path.c:getcwd@v6.18.46 -/
theorem sysno_17_size_high_bits_erange_rejected (m m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 17 [0x10000, 0xffffffff00000000, 0, 0, 0, 0]
          (fun _ => none) (fun _ => none)) m
        (Ok (mkEffect (errno_ret ERANGE) [] []) m' evs) := by
  sys_refute

/-- `getcwd(buf, sizeof buf)` with a 4096-byte buffer: `-ERANGE` is
refused through the table as well, whatever a0 holds, because the
answer there is the working directory's (line 439 goes either way) and
`getcwd_size_path_max_unmodeled_iff` says the spec declines it outright;
a0 is the probe's `buf`, the .bss page at 0x11000 the `big` trace records
(`testing/syscall-check/traces/getcwd_spec/014.jsonl`), and is unread.
Stated as a refutation rather than as the decline itself so that
`tools/check_decline_registers.py`, which reads every `syscall_spec …
Unmodeled` statement beside a concrete number as a claim about the
NUMBER, does not take a per-argument decline for a decline of 17.
probe: testing/syscall-check/tests/getcwd_spec.c#fail-closed --expect-unmodeled getcwd -- big -/
theorem sysno_17_big_size_erange_rejected (m m' : Model) (evs : List event) :
    ¬ syscall_spec (SyscallInput.mkInput 17 [0x11000, 4096, 0, 0, 0, 0] (fun _ => none) (fun _ => none)) m
        (Ok (mkEffect (errno_ret ERANGE) [] []) m' evs) := by
  sys_refute

end LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Fs.DPath
