-- Ports rocq-linux-process-semantics f1006fe8:theories/LinuxProcessSem/Sys/Syscall.v
import LinuxProcessSemantics.LinuxProcessSem.Monad

/-! rocq-baseline: a71fd38a08571d519b9cfc5f66308db5c26da570 -/

/-! # LinuxProcessSem.Sys.Syscall — the syscall calling convention

Mirrors `theories/LinuxProcessSem/Sys/Syscall.v`: how a spec returns, how
it records the user memory it read, and how the ABI narrows an argument
(every `int`/`unsigned int` parameter is the LOW 32 BITS of the register;
the argument for each narrowing is on the Rocq definition of the same
name and cites the `SYSCALL_DEFINE`s).

This file answers to the kernel header `include/linux/syscalls.h` and
holds what the specs share rather than any one syscall's behaviour.  Its
pins are `Checks/Cases/Sys/Syscall.lean`.

TRUST BOUNDARY: this file is part of the trusted specification. -/

namespace LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall

open LinuxProcessSemantics.Riscv.Prelude
open LinuxProcessSemantics.LinuxProcessSem.BvBase
open LinuxProcessSemantics.LinuxProcessSem.State
open LinuxProcessSemantics.LinuxProcessSem.Monad

/-- Return `r` with no memory writes. -/
def ret_only (r : word) : Sys SyscallEffect := Monad.pure (mkEffect r [] [])

/-- Fail with errno `e` (a0 = -e). -/
def err_ret (e : Int) : Sys SyscallEffect := ret_only (errno_ret e)

/-! ## The copy-in ledger

`SyscallEffect.eff_copyins` records the user-memory ranges a syscall read
while selecting its outcome.  It is outcome data because the same errno
can be returned either before or after a `copy_from_user`, and
`State.materialize_model_accesses` charges what was read against the
lazy anonymous budget, so an empty ledger on a syscall that did read is
a false claim about Linux, not a missing convenience
(`tools/check_copyin_parity.py` carries that argument). -/

/-- Attach the copy-from-user ranges at the point where the syscall has
actually performed them.  The wrapper's `reads` are prepended to the
inner spec's own ledger, `reads ++ eff_copyins`, and the order is
load-bearing rather than cosmetic: `State.materialize_model_accesses`
folds the ledger left to right (`State.accesses_pages`), and
`State.page_insert` prepends each page it has not yet seen, so the order
of `m_vm_materialized` in the post-state depends on the order of the
ledger, and a model compared by equality tells `reads ++ eff_copyins`
from `eff_copyins ++ reads`.  Keeping the list literally Rocq's is what
lets a checker ported later compare ledgers, and the models they
produce, by equality.  Rocq: `Syscall.record_copyins`. -/
def record_copyins (reads : List (word × Nat)) (spec : Sys SyscallEffect) :
    Sys SyscallEffect :=
  Monad.bind spec (fun eff => Monad.pure (with_copyins (reads ++ eff.eff_copyins) eff))

theorem record_copyins_ok (reads : List (word × Nat)) (spec : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event) :
    spec i m (Ok eff m' evs) →
    record_copyins reads spec i m
      (Ok (with_copyins (reads ++ eff.eff_copyins) eff) m' evs) := by
  intro h
  have hb := Monad.bind_ok spec
    (fun eff => Monad.pure (with_copyins (reads ++ eff.eff_copyins) eff)) i m eff m' evs
    (with_copyins (reads ++ eff.eff_copyins) eff) m' [] h (Monad.pure_ok _ i m')
  rw [List.append_nil] at hb
  unfold record_copyins
  exact hb

theorem record_copyins_ok_empty (reads : List (word × Nat)) (spec : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event) :
    eff.eff_copyins = [] →
    spec i m (Ok eff m' evs) →
    record_copyins reads spec i m (Ok (with_copyins reads eff) m' evs) := by
  intro hempty h
  have hb := record_copyins_ok reads spec i m eff m' evs h
  rw [hempty, List.append_nil] at hb
  unfold record_copyins
  exact hb

theorem record_copyins_unmodeled (reads : List (word × Nat)) (spec : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) :
    spec i m Unmodeled → record_copyins reads spec i m Unmodeled :=
  fun h => Monad.bind_unmodeled1 spec _ i m h

/-- `record_copyins` as a function on outcomes: the ledger is prepended to
an `Ok` and a decline stays a decline.  Rocq: `Syscall.outcome_copyins`. -/
def outcome_copyins (reads : List (word × Nat)) (o : outcome SyscallEffect) :
    outcome SyscallEffect :=
  match o with
  | Ok eff m evs => Ok (with_copyins (reads ++ eff.eff_copyins) eff) m evs
  | Unmodeled => Unmodeled

theorem record_copyins_outcome (reads : List (word × Nat)) (spec : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    spec i m o → record_copyins reads spec i m (outcome_copyins reads o) := by
  intro h
  cases o with
  | Ok eff m' evs => exact record_copyins_ok reads spec i m eff m' evs h
  | Unmodeled => exact record_copyins_unmodeled reads spec i m h

/-- The reading of `record_copyins` at every outcome, the converse of
`record_copyins_outcome` folded into one `iff`: an outcome of the wrapper
is an outcome of the inner spec with the ledger attached by
`outcome_copyins`, and nothing else.  Stated continuation first — the
inner outcome bound, its equation on the right — which is the shape
`Checks/Cases/Tactic.lean`'s `sys_norm` reads, as it reads `emit`.  The
two halves Rocq's `Checks/Sys/Prelude.v` proves by hand,
`record_copyins_ok_inv` and `record_copyins_unmodeled_inv`, are the `→`
of `record_copyins_ok_iff` and `record_copyins_unmodeled_iff` below,
each this lemma at one constructor of `o`. -/
theorem record_copyins_iff (reads : List (word × Nat)) (spec : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) :
    record_copyins reads spec i m o ↔ ∃ o', spec i m o' ∧ o = outcome_copyins reads o' := by
  unfold record_copyins
  cases o with
  | Ok eff' m' evs =>
    constructor
    · rintro ⟨eff, m1, evs1, evs2, hs, hp, hevs⟩
      simp only [Monad.pure, outcome.Ok.injEq] at hp
      obtain ⟨rfl, rfl, rfl⟩ := hp
      subst hevs
      refine ⟨_, hs, ?_⟩
      rw [List.append_nil]
      rfl
    · rintro ⟨o', hs, ho⟩
      cases o' with
      | Ok eff m1 evs1 =>
        simp only [outcome_copyins, outcome.Ok.injEq] at ho
        obtain ⟨rfl, rfl, rfl⟩ := ho
        exact ⟨eff, _, _, [], hs, rfl, (List.append_nil _).symm⟩
      | Unmodeled =>
        simp only [outcome_copyins] at ho
        cases ho
  | Unmodeled =>
    constructor
    · rintro (h | ⟨eff, m1, evs1, -, hp⟩)
      · exact ⟨Unmodeled, h, rfl⟩
      · exact absurd hp (by simp only [Monad.pure, reduceCtorEq, not_false_eq_true])
    · rintro ⟨o', hs, ho⟩
      cases o' with
      | Ok eff m1 evs1 =>
        simp only [outcome_copyins] at ho
        cases ho
      | Unmodeled => exact Or.inl hs

/-- `record_copyins_iff` at an `Ok`: the inner spec produced the same
model and events, and the effect is the inner effect with the wrapper's
reads prepended.  Its `→` is the twin of `Checks/Sys/Prelude.v`'s
`record_copyins_ok_inv`. -/
theorem record_copyins_ok_iff (reads : List (word × Nat)) (spec : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) (eff' : SyscallEffect) (m' : Model) (evs : List event) :
    record_copyins reads spec i m (Ok eff' m' evs) ↔
      ∃ eff, spec i m (Ok eff m' evs) ∧ eff' = with_copyins (reads ++ eff.eff_copyins) eff := by
  rw [record_copyins_iff]
  constructor
  · rintro ⟨o', hs, ho⟩
    cases o' with
    | Ok eff m1 evs1 =>
      simp only [outcome_copyins, outcome.Ok.injEq] at ho
      obtain ⟨rfl, rfl, rfl⟩ := ho
      exact ⟨eff, hs, rfl⟩
    | Unmodeled =>
      simp only [outcome_copyins] at ho
      cases ho
  · rintro ⟨eff, hs, rfl⟩
    exact ⟨Ok eff m' evs, hs, rfl⟩

/-- `record_copyins_iff` at a decline: only the inner spec can have
declined, since the wrapper's own step is a `pure`.  Its `→` is the twin
of `Checks/Sys/Prelude.v`'s `record_copyins_unmodeled_inv`. -/
theorem record_copyins_unmodeled_iff (reads : List (word × Nat)) (spec : Sys SyscallEffect)
    (i : SyscallInput) (m : Model) :
    record_copyins reads spec i m Unmodeled ↔ spec i m Unmodeled := by
  rw [record_copyins_iff]
  constructor
  · rintro ⟨o', hs, ho⟩
    cases o' with
    | Ok eff m1 evs1 =>
      simp only [outcome_copyins] at ho
      cases ho
    | Unmodeled => exact hs
  · intro h
    exact ⟨Unmodeled, h, rfl⟩

/-- An errno drawn from a syscall's realistic injectable set.  Failure
injection is constrained PER SYSCALL: a failure branch may return only
an errno the kernel really produces on that call — each `*_errnos` list
is the model's per-syscall set, and whether a list is exactly the
kernel's is its arm's pins' business — never an arbitrary value in
1..4095.  Rocq's comment
illustrates this with "mmap can never fail with -EBADF", which is wrong
about Linux: `ksys_mmap_pgoff` (mm/mmap.c:566-577, Linux v6.18.46,
commit 1f99e9ab748f) answers -EBADF for a file-backed request whose fd
`fget` cannot resolve, as `Sys/Mm/Mmap.v` itself records.  What holds is
narrower — `Mmap.v`'s anonymous arms draw from `mmap_errnos`, and the
file-backed path is declined rather than injected — so no modeled
failure branch invents an -EBADF.  That description of the Rocq comment
holds at this file's rocq-baseline and stops being true when the
`comments:` fix to `Syscall.v` lands.  Rocq: `Syscall.errno_from`. -/
def errno_from (es : List Int) : Sys Int := choose (fun e => e ∈ es)

/-- Word-against-zero test, used all over the dispatcher. -/
def w_is0 (w : word) : Bool := bv_eqb w (Z_to_bv 64 0)

theorem w_is0_pos (w : word) : 0 < bv_unsigned w → w_is0 w = false := by
  intro h
  unfold w_is0 bv_eqb
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro hw
  subst hw
  simp [bv_unsigned, Z_to_bv] at h

/-- …and the converse, which is the direction an ARM reads it in: past a
`w_is0` gate the length is positive, and a spec that goes on to record a
range derived from it is recording real bytes.
Rocq: `Syscall.w_is0_false_pos`. -/
theorem w_is0_false_pos (w : word) (h : w_is0 w = false) : 0 < bv_unsigned w := by
  unfold w_is0 bv_eqb at h
  simp only [beq_eq_false_iff_ne, ne_eq] at h
  unfold bv_unsigned
  have hz : (Z_to_bv 64 0 : word).toNat = 0 := by decide
  have hne : w.toNat ≠ 0 := fun h0 => h (BitVec.eq_of_toNat_eq (by rw [h0, hz]))
  omega

/-- The low 32 bits of a register, zero-extended back into a `word` — the
C conversion an `int` / `unsigned int` parameter performs.  NOT
`Riscv.Sem.low32`, which has a different type. -/
def abi_low32 (w : word) : word := Z_to_bv 64 (bv_unsigned w % 2 ^ 32)

/-- THE FILE DESCRIPTOR ARGUMENT IS 32 BITS: every entry point declares it
`unsigned int` / `int` (fs/read_write.c, fs/open.c, fs/file.c,
fs/fcntl.c), so `write(2^32 + 1, buf, n)` really writes to STDOUT.  The
walk through each `SYSCALL_DEFINE`, and why zero-extension is faithful
for a signed `int` fd, is on Rocq's `Syscall.fd32`. -/
def fd32 (fd : word) : word := abi_low32 fd

/-- `fd32` is the identity on every fd the model can hold or hand out (all
of them below 2^32), which is what proofs about concrete fds need to see
through the dispatcher's truncation. -/
theorem fd32_id (fd : word) (h : bv_unsigned fd < 2 ^ 32) : fd32 fd = fd := by
  unfold fd32 abi_low32 Z_to_bv
  unfold bv_unsigned at h ⊢
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) h, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

/-- The bound the per-binary proofs already carry for the fds they hold
(below 2^31, so an fd is never an error-encoded return) is more than
enough. -/
theorem fd32_lt31 (fd : word) (h : bv_unsigned fd < 2 ^ 31) : fd32 fd = fd :=
  fd32_id fd (Int.lt_trans h (by decide))

/-- lseek's `whence` is `unsigned int` (`SYSCALL_DEFINE3(lseek, ...)`,
fs/read_write.c); argument on Rocq's `Syscall.whence32`. -/
def whence32 (whence : word) : word := abi_low32 whence
/-- ioctl's, fcntl's and flock's command words are `unsigned int`:
`SYSCALL_DEFINE3(ioctl, unsigned int, fd, unsigned int, cmd, ...)`
(fs/ioctl.c:583, Linux v6.18.46), `SYSCALL_DEFINE3(fcntl, unsigned int,
fd, unsigned int, cmd, ...)` (fs/fcntl.c:574) and `SYSCALL_DEFINE2(flock, unsigned
int, fd, unsigned int, cmd)` (fs/locks.c:2135), all three read at Linux
v6.18.46, commit 1f99e9ab748f — Rocq pins the version for flock alone
and cites the other two files unversioned.  Argument on Rocq's
`Syscall.cmd32`. -/
def cmd32 (cmd : word) : word := abi_low32 cmd
/-- `clockid_t` is an `int`: `typedef int __kernel_clockid_t`
(include/uapi/asm-generic/posix_types.h) reaching
`SYSCALL_DEFINE2(clock_gettime, const clockid_t, which_clock, ...)`
(kernel/time/posix-timers.c, v6.10-v6.15) through include/linux/types.h.
The argument, and why the negative half is a decline rather than an
-EINVAL, is on Rocq's `Syscall.clockid32`. -/
def clockid32 (clkid : word) : word := abi_low32 clkid
/-- setsockopt's/getsockopt's `level`, setsockopt's `optlen` and
shutdown's `how` are `int` (net/socket.c); argument on Rocq's
`Syscall.int32`. -/
def int32 (w : word) : word := abi_low32 w
/-- Credential ids are `uid_t` / `gid_t` (kernel/sys.c, Linux v6.18.46);
argument on Rocq's `Syscall.uid32`. -/
def uid32 (u : word) : word := abi_low32 u
/-- A flag word declared `int` — dup3's (fs/file.c), unlinkat's
(fs/namei.c), newfstatat's (fs/stat.c); argument on Rocq's
`Syscall.flag32`. -/
def flag32 (flag : word) : word := abi_low32 flag

/-- Linux's `int` parameter `n`, as the kernel reads it: the register is
64 bits wide but `SYSCALL_DEFINE6(pselect6, int, n, ...)`
(fs/select.c:793, Linux v6.18.46, commit 1f99e9ab748f) casts it to
`int` before any comparison, so the high half is discarded and the low
half is read as two's complement (`nfds_signed`). -/
def nfds32 (n : word) : word := abi_low32 n

/-- ppoll's `nfds` is `unsigned int` (`SYSCALL_DEFINE5(ppoll, struct
pollfd __user *, ufds, unsigned int, nfds, ...)`, fs/select.c:1095,
Linux v6.18.46, commit 1f99e9ab748f), so the same 32-bit truncation
applies and the result is read UNSIGNED.  Kept apart from `nfds32`
rather than shared with it: the two words are narrowed identically and
read OPPOSITELY, and `do_sys_poll`'s first test — `nfds` against
`rlimit(RLIMIT_NOFILE)`, fs/select.c:981, Linux v6.18.46 — is an unsigned
comparison, so
a register whose low half has bit 31 set is a huge count and not a
negative one. -/
def unfds32 (nfds : word) : word := abi_low32 nfds

/-- The two's-complement reading of an already-narrowed `nfds32` word:
what pselect6's `int n` is, once the C cast has happened.  Rocq:
`Syscall.nfds_signed`. -/
def nfds_signed (n32 : word) : Int :=
  let v := bv_unsigned n32
  if v < 2 ^ 31 then v else v - 2 ^ 32

/-- `socket`'s `family` and `protocol` and `bind`'s and `connect`'s
`addrlen` are `int` arguments whose range checks are SIGNED, each in the
function that makes it: `family < 0` in
`__sock_create` (net/socket.c:1545, Linux v6.18.46, commit 1f99e9ab748f;
the same test is at net/socket.c:1515 in v6.12, the version
`Sys/Net/Socket.v` reads — `__sock_create` tests only the family and the
type), `protocol < 0` in `inet_create` (net/ipv4/af_inet.c:265 at
v6.18.46, :263 at v6.12), and `addrlen < 0` as `ulen < 0` in
`move_addr_to_kernel` (net/socket.c:250 at v6.18.46, :248 at v6.12).
`listen`'s `int backlog` is the one `int` here that is NOT sign-checked:
`__sys_listen_socket` (net/socket.c:1924 at v6.18.46, :1888 at v6.12)
clamps it through an `(unsigned int)` cast against `somaxconn`, so a
negative backlog is a huge count clamped down and never a rejection —
`Sys/Net/Socket.v`'s `listen_spec` carries that argument.  Rocq's comment
names `accept4` in this list too, loosely: its only `int` besides the fd
is `flags`, tested BITWISE (`flags & ~(SOCK_CLOEXEC | SOCK_NONBLOCK)`,
`__sys_accept4_file`, net/socket.c:2019 at v6.18.46), and the `len < 0`
it does refuse is a value read from user memory in `move_addr_to_user`
(net/socket.c:302), not a register, so no narrowing implements it —
Rocq's `accept4_spec` reads `flags` through `abi_low32`.  `abi_low32`
gives the unsigned low 32 bits; this reads the same bits as a signed
`int`.  Rocq: `Syscall.sint32`. -/
def sint32 (w : word) : Int :=
  let u := bv_unsigned (abi_low32 w)
  if u < 2 ^ 31 then u else u - 2 ^ 32

/-- rt_sigprocmask's `how` is `int` (kernel/signal.c); its `sigsetsize`
is `size_t` and deliberately NOT narrowed; argument on Rocq's
`Syscall.how32`. -/
def how32 (how : word) : word := abi_low32 how
/-- wait4's `upid` is a `pid_t`, an `int` (kernel/exit.c); argument on
Rocq's `Syscall.pid32`. -/
def pid32 (upid : word) : word := abi_low32 upid
/-- wait4's `options` is an `int` in the same prototype; argument on
Rocq's `Syscall.waitopts32`. -/
def waitopts32 (options : word) : word := abi_low32 options
/-- pipe2's flag word is an `int` (fs/pipe.c); argument on Rocq's
`Syscall.pipe_flags32`. -/
def pipe_flags32 (flags : word) : word := abi_low32 flags

end LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall
